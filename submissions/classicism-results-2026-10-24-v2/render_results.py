#!/usr/bin/env python3
"""Render local research views from canonical JSON; never runs Lean or changes verdicts.

Default/--check is read-only. --write refreshes the generated Markdown.
--refresh-checksums requires --write and explicitly refreshes SHA256SUMS.
"""
import argparse
import hashlib
import json
import posixpath
import re
from pathlib import Path


def load(root, name):
    return json.loads((root / name).read_text())


def anchor(name):
    return '<a id="' + name.lower() + '"></a>'


def protect_markdown_math(body):
    """Keep LaTeX out of Markdown's escape and emphasis processing on GitHub.

    Display/inline choices and all formula contents are preserved. Math fences
    must be unindented for GitHub to render them. Other code stays unchanged.
    """
    lines = body.splitlines(keepends=True)
    out = []
    fence = None
    math_indent = ''
    display = False
    inline = re.compile(r'\$`[^`\n]*`\$|`[^`\n]*`|(?<![\\$])\$([^$\n]+)\$(?!\$)')
    for line in lines:
        marker = re.match(r'^\s*(`{3,}|~{3,})', line)
        if fence:
            out.append(line[len(math_indent):] if math_indent and line.startswith(math_indent) else line)
            if marker and marker[1][0] == fence[0] and len(marker[1]) >= len(fence):
                fence = None
                math_indent = ''
            continue
        if not display and marker:
            fence = marker[1]
            math_indent = re.match(r'^[ \t]*', line)[0] if line.strip() == '```math' else ''
            out.append(line[len(math_indent):])
        elif line.strip() == '$$':
            if not display:
                math_indent = re.match(r'^[ \t]*', line)[0]
            out.append(line.lstrip().replace('$$', '```' if display else '```math', 1))
            display = not display
            if not display:
                math_indent = ''
        elif display:
            out.append(line[len(math_indent):] if math_indent and line.startswith(math_indent) else line)
        else:
            out.append(inline.sub(lambda m: '$`' + m[1] + '`$' if m[1] is not None else m[0], line))
    assert not display, 'Unclosed display math'
    return ''.join(out)


def math_layout_issues(name, body):
    """Check editable pages; source snapshots retain their original formatting."""
    issues = []
    lines = body.splitlines()
    fence = None
    opening = None
    for i, line in enumerate(lines):
        marker = re.match(r'^\s*(`{3,}|~{3,})', line)
        if marker:
            if fence is None:
                fence = marker[1][0]
                if line.strip() == '```math' and i and lines[i - 1].strip():
                    issues.append(name + ':' + str(i + 1) + ': missing blank line before display')
            elif marker[1][0] == fence:
                fence = None
            continue
        if fence:
            continue
        visible = re.sub(r'\$`[^`\n]*`\$|`[^`]*`', '', line)
        if '$$' not in visible:
            continue
        location = name + ':' + str(i + 1)
        if visible.strip() != '$$':
            issues.append(location + ': use single dollars in prose or a separate display block')
        elif opening is None:
            opening = i
            if i and lines[i - 1].strip():
                issues.append(location + ': missing blank line before display')
        else:
            opening = None
            if i + 1 < len(lines) and lines[i + 1].strip():
                issues.append(location + ': missing blank line after display')
    if opening is not None:
        issues.append(name + ':' + str(opening + 1) + ': unclosed display')
    prose = re.sub(r'```[\s\S]*?```|~~~[\s\S]*?~~~|\$`[^`\n]*`\$|`[^`]*`|\$\$[\s\S]*?\$\$',
                   lambda match: re.sub(r'[^\n]', ' ', match[0]), body)
    for match in re.finditer(r'(?<![\\$])\$[^\n$]+\$(?!\$)', prose):
        before = prose[match.start() - 1:match.start()] if match.start() else ''
        after = prose[match.end():match.end() + 1]
        if re.match(r'[\w=]', before) or re.match(r'[\w(]', after):
            line = body.count('\n', 0, match.start()) + 1
            issues.append(name + ':' + str(line) + ': put the complete inline expression inside its delimiters')
    if protect_markdown_math(body) != body:
        issues.append(name + ': protect math from Markdown escapes and emphasis')
    return issues


def render(root):
    main = load(root, 'MAIN-RESULTS.json')
    catalog = load(root, 'CATALOG.json')
    questions = load(root, 'CONJECTURES.json')
    integration = load(root, 'DATABASE-INTEGRATION.json')
    proposals = load(root, 'CANDIDATES_DK.json')
    coverage = load(root, 'evidence/COVERAGE.json')
    rows = {r['id']: r for r in main['results']}
    integration_claims = {r.get('claim_id', r['catalog_id']): r for r in integration.get('supplementary_entries', [])}
    assert len(rows) == len(main['results']), 'Duplicate result ID'
    keys = {r['id'] for r in catalog['entries']}
    assert len(keys) == len(catalog['entries']), 'Duplicate catalog key'
    assert set(coverage['original_catalog_keys_retained']) <= keys, 'Original key lost'
    section_ids = [x for section in main['sections'] for x in section['results']]
    assert len(section_ids) == len(set(section_ids)), 'Repeated result in sections'
    assert set(section_ids) == set(rows), 'Section coverage is incomplete'
    assert coverage['result_entries'] == len(rows), 'Stale coverage result count'
    assert coverage['questions'] == len(questions['questions']), 'Stale coverage question count'
    assert coverage['subject_coverage'] == main['sections'], 'Stale subject coverage'
    overview = main['overview']
    overview_groups = [g for s in overview['sections'] for g in s['groups']]
    lengths = load(root, 'evidence/proof-lengths.json')
    result_lengths = {r['result_ref']: r for r in lengths['results']}
    group_lengths = {g['group_ref']: g for g in lengths['groups']}
    assert len(result_lengths) == len(lengths['results']) == len(rows), 'Incomplete proof-length coverage'
    assert len(group_lengths) == len(lengths['groups']) == len(overview_groups), 'Incomplete group proof-length coverage'
    for row in rows.values():
        assessment = result_lengths[row['id']]
        assert row['proof_length'] == {'rating': assessment['rating'], 'words': assessment['word_count']}, 'Stale result proof length'
    for group in overview_groups:
        assessment = group_lengths[group['id']]
        assert group['result_refs'] == assessment['result_refs'], 'Stale group source selection'
        assert group['proof_length'] == {'rating': assessment['rating'], 'words': assessment['word_count']}, 'Stale group proof length'
    overview_refs = [rid for g in overview_groups for rid in g['result_refs']]
    supplemental_refs = [r['result_ref'] for s in overview['sections'] for r in s['supplemental_results']]
    assert len(overview_refs) == len(set(overview_refs)), 'Repeated overview result'
    assert len(supplemental_refs) == len(set(supplemental_refs)), 'Repeated supplemental result'
    assert not set(overview_refs) & set(supplemental_refs), 'Overlapping presentation roles'
    assert set(overview_refs + supplemental_refs) == set(rows), 'Presentation omits a result'
    assert coverage['presentation'] == {
        'overview_groups': len(overview_groups), 'overview_result_refs': overview_refs,
        'supplemental_result_refs': supplemental_refs, 'complete_result_entries': len(rows)
    }, 'Stale presentation coverage'
    question_rows = {r['id']: r for r in questions['questions']}
    assert set(overview['open_question_refs']) <= set(question_rows), 'Missing open question'
    assert {r['result_id'] for r in integration['entries']} == set(rows), 'Integration coverage'
    assert len(integration['entries']) == len(rows), 'Duplicate integration entry'
    links = load(root, 'evidence/source-links.json')
    redirects = {}
    for item in load(root, 'ARCHIVED-ARTIFACTS.json')['artifacts']:
        dest = item.get('retained_copy') or item.get('retained_path')
        if dest:
            redirects[item['path']] = dest

    def resolve(origin):
        if origin in links:
            return links[origin]
        rel = origin if origin.startswith(('source/', 'proofs/', 'evidence/')) else 'source/' + origin
        return rel if (root / rel).is_file() else redirects.get(rel, rel)

    def filelink(origin, base='.', label=None):
        path = resolve(origin)
        assert (root / path).is_file(), 'Missing evidence: ' + path
        return '[' + (label or Path(path).name) + '](' + posixpath.relpath(path, base) + ')'

    def prooflinks(origins, base='.'):
        return ' · '.join(filelink(x, base) for x in dict.fromkeys(resolve(x) for x in origins))

    def resultlink(rid, base='.', label=None):
        assert rid in rows, 'Unknown result: ' + rid
        return '[' + (label or '`' + rid + '`') + '](' + posixpath.relpath('evidence/RESULT-INDEX.md', base) + '#' + rid.lower() + ')'

    def statusrefs(ids):
        return ' '.join(resultlink(rid) + ('.' if rows[rid]['certified_scope'] is True else ': ' + rows[rid]['certified_scope'].rstrip('.') + '.') for rid in ids if rows[rid].get('certified_scope'))

    def certified_line(row):
        scope = row.get('certified_scope')
        if scope is True:
            return '**Lean certified.**'
        return '**Lean certified:** ' + scope.rstrip('.') + '.' if scope else ''

    def done(lines):
        text = ('\n'.join(lines).rstrip() + '\n').replace(r'\operatorname', r'\mathrm')
        return re.sub(r'\n{3,}', '\n\n', text)

    def bullet(claim):
        # Indent continuation blocks so displayed mathematics stays in its list item.
        lines = claim.split('\n')
        body = '- ' + lines[0] + ''.join('\n' + ('  ' + line if line else '') for line in lines[1:])
        return body + ('\n' if lines[-1].strip() == '$$' else '')

    out = {}
    observers = load(root, 'OBSERVER-PRINCIPLES.json')
    observer_ids = {r['id'] for r in observers['principles']}
    assert len(observer_ids) == len(observers['principles']), 'Duplicate observer principle'
    for r in observers['principles']:
        assert all(k in observers['definitions'] for k in r['definitions']), 'Missing observer definition'
    family_rows = observers.get('family_principles', [])
    assert len({r['id'] for r in family_rows}) == len(family_rows), 'Duplicate family principle'
    assert not observer_ids & {r['id'] for r in family_rows}, 'Family principle reused as an individual restriction'
    for r in family_rows:
        assert r['formal'] and r['scope'] and r['sources'], 'Incomplete family principle'
        assert all((root / path).is_file() for path in r['sources']), 'Missing family proof'
    text = ['# ' + observers['title'], '',
        'Logical observers preserve logical structure while offering different perspectives on propositions. An observer can distinguish two propositions that are both true here by returning a truth for one and a falsehood for the other. A separating family makes every difference between relations detectable.', '',
        '**Boolean separation recovers Booleanism; logical separation recovers Classicism together with BF.** Over H, Boolean observers suffice to identify abstractions of Boolean-equivalent formulas. The richer qualification in [OS](#map-over-h) extends this to all H-provable equivalences and also entails BF: H + OS ⇒ C + BF (**Lean certified**). Both recovery claims use separation at every relational type. We begin over C, where the observer conditions have their simplest form, then give the additional clauses needed over H.', '',
        '[Main results](MAIN-RESULTS.md) · [Candidates](CANDIDATES_DK.md) · [Structured definitions](OBSERVER-PRINCIPLES.json) · [Full connection catalogue](proofs/h-observer-space/SUMMARY.md)', '',
        '[Logical observers](#logical-observers-over-c) · [Separation](#observer-separation) · [Principles](#observer-principles-at-a-glance) · [Simplifications](#simplifications-over-c-and-c5) · [C: familiar principles](#familiar-principles-over-c) · [C: observers](#observer-relations-over-c) · [C5](#c5-simplifications) · [Commuting families](#commuting-observer-families) · [Max(C)](#map-over-max-c) · [H: familiar principles](#familiar-principles-over-h) · [H: observers](#observer-relations-over-h) · [Mathematics](#mathematics-through-observers) · [Shift models](#shift-models) · [Lean evidence](#lean-evidence)', '']
    overview_symbols = {symbol for section in observers['guide_sections'] if section.get('kind') == 'observer_overview' for symbol in section['symbols']}
    for section in observers['guide_sections']:
        text += [anchor(section['id']), '## ' + section['title'], '', section['body'], '']
        if section.get('kind') == 'observer_overview':
            text += ['| Principle and meaning | Additional condition $K(E)$ |', '| --- | --- |']
            for symbol in section['symbols']:
                r = next(r for r in observers['principles'] if r['symbol'] == symbol)
                text += ['| ' + anchor(r['id']) + '**' + symbol + '.** ' + r.get('overview_intuition', r['intuition']) + ' | $' + r['overview_condition'] + '$ |']
            text += ['']
        if section.get('kind') in ('principal_table', 'further_table'):
            group = 'principal' if section['kind'] == 'principal_table' else 'further'
            for r in observers['principles']:
                if r['group'] == group and r['symbol'] in section.get('symbols', [r['symbol']]):
                    detail_id = ('details-' if r['symbol'] in overview_symbols else '') + r['id']
                    text += [anchor(detail_id), '### ' + r['symbol'], '']
                    if r['symbol'] not in overview_symbols:
                        text += [r['intuition'], '']
                    if r['symbol'] != 'OS':
                        text += ['$$', observers['definitions'][r['symbol']], '$$', '']
                    else:
                        text += ['OS uses the common separation formula with no additional observer condition.', '']
    out['LOGICAL-OBSERVERS.md'] = done(text)
    proposed = proposals['principles']
    infinitary = proposals.get('infinitary_principles', [])
    candidate_rows = [item for r in proposed for item in [r, *r.get('variants', [])]] + infinitary
    proposed_ids = [item['id'] for item in candidate_rows]
    candidates_by_id = {item['id']: item for item in candidate_rows}
    proposal_sections = proposals['presentation_sections']
    listed_ids = [pid for section in proposal_sections for pid in section['principles']]
    assert len(listed_ids) == len(set(listed_ids)), 'Repeated proposal in presentation'
    assert set(listed_ids) == {r['id'] for r in proposed + infinitary}, 'Proposal list omits an entry'
    assert len(proposed_ids) == len(set(proposed_ids)), 'Duplicate proposed principle'
    assert set(proposals['first_batch']) == {r['id'] for r in proposed if r['batch'] == 'first'}, 'Proposal priority mismatch'
    assert all(r['batch'] in ('first', 'further', 'exploratory') for r in proposed), 'Unknown proposal batch'
    def proposal_sources(item):
        assert item['sources'], 'Proposal needs a direct source'
        return ' · '.join(filelink(s['path']) + ' (' + s['locator'] + ')' for s in item['sources'])
    def proposal_status(item):
        refs = item.get('result_refs', [])
        evidence = ('**Evidence:** ' + ' · '.join(resultlink(rid, label=rows[rid]['title'] if len(refs) > 1 else 'Proofs and certificates') for rid in refs) + '.') if refs else ''
        return '\n\n'.join(x for x in [certified_line(item), evidence] if x)
    def full_proposal(r):
        lines = [anchor(r['id']), '### ' + r['name'], '', r['statement'], '', '$$', r['formal'], '$$', '']
        if r.get('scope'):
            lines += [r['scope'], '']
        for definition in r.get('definitions', []):
            lines += [definition, '']
        lines += [bullet(claim) for claim in r['connections']]
        for variant in r.get('variants', []):
            lines += ['', anchor(variant['id']), '#### ' + variant['name'], '', variant['statement'], '', '$$', variant['formal'], '$$', '']
            for definition in variant['definitions']:
                lines += [definition, '']
            lines += [bullet(claim) for claim in variant['connections']]
            extra_sources = [s for s in variant['sources'] if s not in r['sources']]
            if extra_sources:
                lines += ['', '**Additional sources:** ' + proposal_sources({'sources': extra_sources}) + '.']
            if variant['result_refs'] != r['result_refs']:
                lines += ['', proposal_status(variant)]
        lines += ['', '**Sources:** ' + proposal_sources(r) + '.', '', proposal_status(r), '']
        lines += r.get('questions', []) + ([''] if r.get('questions') else [])
        return lines
    text = ['# ' + proposals['title'], '',
        proposals['scope'], '',
        '[Main results](MAIN-RESULTS.md) · [Observer guide](LOGICAL-OBSERVERS.md) · [Integration review](DATABASE-INTEGRATION.md) · [Structured proposals](CANDIDATES_DK.json) · [Evaluation principles](#evaluation-principles) · [Infinitary extension](#infinitary-extension)', '',
        '## Proposed principles', '',
        '| Subject | Principle | Reason for inclusion |', '|---|---|---|']
    for section in proposal_sections:
        for pid in section['principles']:
            r = candidates_by_id[pid]
            assert r.get('rationale'), 'Candidate needs a substantive reason for inclusion'
            text += ['| ' + section['title'] + ' | [' + r['name'] + '](#' + r['id'] + ') | ' + r['rationale'].replace('|', '\\|') + ' |']
    for section in proposal_sections:
        text += ['', anchor(section['id']), '## ' + section['title'], '']
        for pid in section['principles']:
            r = candidates_by_id[pid]
            compact = r.get('presentation')
            if not compact:
                text += full_proposal(r)
                continue
            text += [anchor(r['id']), '### ' + r['name'], '', r['statement'], '', '$$', r['formal'], '$$', '']
            text += [compact['definitions'], ''] + [bullet(claim) for claim in compact['connections']]
            text += ['', '#### Observer restrictions', '', '| Variant | Additional qualification | Main consequence |', '|---|---|---|']
            assert {v['id'] for v in compact['variants']} == {v['id'] for v in r['variants']}, 'Missing observer variant'
            for variant in compact['variants']:
                label = anchor(variant['id']) + '[' + variant['label'] + '](' + compact.get('guide_reference', compact['reference']) + '#' + variant['id'] + ')'
                text += ['| ' + label + ' | ' + variant['qualification'] + ' | ' + variant['consequence'] + ' |']
            text += ['', compact['reference_intro'], '', proposal_status(r), '']

            reference_path = compact['reference']
            reference = (root / reference_path).read_text()
            begin, end = '<!-- BEGIN OBSERVER PRINCIPLE REFERENCE -->', '<!-- END OBSERVER PRINCIPLE REFERENCE -->'
            assert reference.count(begin) == reference.count(end) == 1, 'Observer reference markers missing'
            body = done(full_proposal(r))
            def rebase_link(match):
                target = match.group(1)
                if target.startswith(('#', 'https://', 'http://')):
                    return match.group(0)
                path, sep, fragment = target.partition('#')
                return '](' + posixpath.relpath(path, posixpath.dirname(reference_path)) + sep + fragment + ')'
            body = re.sub(r'\]\(([^)\s]+)\)', rebase_link, body)
            block = '\n\n' + anchor('logical-observer-principles') + '\n## Logical-observer principles and connections\n\n' + body + '\n'
            out[reference_path] = reference.split(begin)[0] + begin + block + end + reference.split(end)[1]
    evaluation = proposals['evaluation']
    text += [anchor('evaluation-principles'), '## Evaluation principles', '', evaluation['purpose'], '',
             'For $E^{tt}$, define', '', '$$', evaluation['definition'], '$$', '']
    for r in evaluation['entries']:
        text += ['### ' + r['name'], '', '$$', r['formal'], '$$', '', '**Equivalent over C:** ' + r['equivalent_to'] + '.', '']
    text += ['- ' + note for note in evaluation['notes']]
    text += ['', '**Sources:** ' + proposal_sources(evaluation) + '.', '', proposal_status(evaluation), '']
    text += ['## Further equivalent formulations', '']
    for r in proposals['alternative_formulations']:
        text += ['### ' + r['name'], '', r['statement'], '']
        for i, formula in enumerate(r.get('formulas', [])):
            if i and r.get('between_formulas'):
                text += [r['between_formulas'], '']
            text += ['$$', formula, '$$', '']
        text += ['**Sources:** ' + proposal_sources(r) + '.', '', proposal_status(r), '']
    out['CANDIDATES_DK.md'] = done(text)
    def established_formalizations():
        established = main['established_formalizations']
        lines = [anchor('previously-known-results-formalized'), '### ' + established['title'], '', established['intro'], '']
        for item in established['entries']:
            rid = item['result_ref']
            r = rows[rid]
            assert r.get('certified_scope'), 'Prior-result formalization needs a certificate'
            proof_idea = item.get('proof_idea', r.get('proof_idea'))
            assert proof_idea and r.get('proof_length'), 'Prior-result formalization needs a proof description and length'
            if not any(rid in group['result_refs'] for group in overview_groups):
                lines += [anchor(rid)]
            lines += ['#### ' + item['name'], '', '**Source:** ' + item['attribution'], '',
                      proof_idea, '', '**Lean certified:** ' + item['scope'], '']
            if item.get('note'):
                lines += [item['note'], '']
            lines += ['[Proof length](#proof-length): ' + r['proof_length']['rating'] + '. ' +
                      resultlink(rid, label='Proofs and certificates') + '.', '']
        return lines

    parts = {p['id']: p for p in overview['parts']}
    assert len(parts) == 3 and all(s['part'] in parts for s in overview['sections'])
    assert list(dict.fromkeys(s['part'] for s in overview['sections'])) == list(parts), 'Unordered presentation parts'
    groups_by_id = {g['id']: g for g in overview_groups}
    assert len(groups_by_id) == len(overview_groups)
    assert len({h['group_ref'] for h in overview['headlines']}) == len(overview['headlines'])
    text = ['# Main results — 24 October 2026 (v2)', '',
        'Draft. The background is finitary relational **Classicism C** unless stated otherwise.', '',
        '[Full statements, proofs and certificates](evidence/RESULT-INDEX.md) · [Previously known results formalized](#previously-known-results-formalized) · [Questions and negative results](CONJECTURES.md) · [Logical observers](LOGICAL-OBSERVERS.md) · [Notation](#notation)', '',
        anchor('central-results'), '## Headline results', '']
    for item in overview['headlines']:
        group = groups_by_id[item['group_ref']]
        text += ['- [' + item['label'] + '](#' + group['result_refs'][0].lower() + ')' +
                 ('. **' + item['certification'] + '**' if item.get('certification') else '.')]
    text += ['', anchor('categories'), '## Contents', '', '| Part | Sections |', '|---|---|']
    for pid, part in parts.items():
        entries = ['[' + section['title'] + '](#' + section['id'] + ')' for section in overview['sections'] if section['part'] == pid]
        if pid == 'database-connections':
            entries += ['[Previously known results formalized](#previously-known-results-formalized)']
        text += ['| [' + part['title'] + '](#' + pid + ') | ' + '; '.join(entries) + '. |']
    text += ['']
    current_part = None
    overview_anchors = ({rid.lower() for g in overview_groups for rid in g['result_refs']}
                        | {alias.lower() for g in overview_groups for alias in g.get('anchor_aliases', [])}
                        | {item['result_ref'].lower() for item in main['established_formalizations']['entries']})
    for section in overview['sections']:
        if section['part'] != current_part:
            if current_part == 'database-connections':
                text += established_formalizations()
            current_part = section['part']
            text += [anchor(current_part), '## ' + parts[current_part]['title'], '']
        text += [anchor(section['id']), '### ' + section['title'], '']
        for group in section['groups']:
            refs = group['result_refs']
            text += [anchor(alias) for alias in group.get('anchor_aliases', [])]
            text += [anchor(rid) for rid in refs]
            text += ['#### ' + group['title'], '']
            if group.get('principle_ref') or group.get('principle'):
                principle = group.get('principle') or candidates_by_id[group['principle_ref']]
                text += [principle['statement'], '', '$$', principle['formal'], '$$', '', principle['scope'], '']
            text += [group.get('summary', rows[refs[0]]['statement']), '']
            for rid in refs:
                if rows[rid].get('proof_idea'):
                    text += [rows[rid]['proof_idea'], '']
            certification = ''
            if all(rows[rid].get('certified_scope') is True for rid in refs):
                certification = '**Lean certified.**'
            elif any(rows[rid].get('certified_scope') for rid in refs):
                scopes = [rows[rid]['title'] if rows[rid]['certified_scope'] is True else rows[rid]['certified_scope'].rstrip('.') for rid in refs if rows[rid].get('certified_scope')]
                certification = '**Lean certified:** ' + group.get('certified_summary', '; '.join(scopes)).rstrip('.') + '.'
            rating = group['proof_length']['rating']
            certification += (' · ' if certification else '') + '[Proof length](#proof-length): ' + rating + '.'
            if certification:
                text += [certification, '']
            labels = group.get('evidence_labels', ['Proofs and certificates'] if len(refs) == 1 else [rows[rid]['title'] for rid in refs])
            assert len(labels) == len(refs), 'Wrong evidence label count'
            text += [' · '.join(resultlink(rid, label=label) for rid, label in zip(refs, labels)) + '.', '']
        if section['supplemental_results']:
            text += [anchor(r['result_ref']) for r in section['supplemental_results'] if r['result_ref'].lower() not in overview_anchors]
            text += ['[Supplemental results in this category](evidence/RESULT-INDEX.md#supplement-' + section['id'] + ') · [Back to contents](#categories)', '']
        else:
            text += ['[Back to contents](#categories)', '']
    text += ['', '## Remaining central questions', '']
    for qid in overview['open_question_refs']:
        q = question_rows[qid]
        text += ['- [' + q['question'] + '](CONJECTURES.md#' + qid.lower() + ') — ' + q['status'].rstrip('.') + '.']
    text += ['', 'Further reductions, failed constructions and incomplete formalizations are recorded in the [question register](CONJECTURES.md).', '']
    text += [anchor('proof-length'), '## Proof length', '',
        '**Short:** under 1,000 words. **Medium:** 1,000–3,000. **Long:** over 3,000. Every entry is rated by the selected mathematical exposition, including substantive supporting arguments. Grouped entries combine their source passages, counting overlapping lines once. Alternative proofs, Lean code and compiler logs are excluded; published background is cited rather than expanded. These are measures of exposition length, not difficulty or importance. [Source selections and counts](evidence/proof-lengths.json).', '']
    text += [anchor('notation'), '## Notation and scope', '',
        '| Notation | Meaning |', '|---|---|',
        '| C; C5 | Fixed Classicism; C + ☐ND. |',
        '| e; t; et; tt | Individuals; propositions; unary properties of individuals; unary properties of propositions. The fixed grammar admits no individual-valued function types. |',
        '| ☐; ◇ | Necessarily; possibly. |',
        '| ND; BF; BC | Necessity of Distinctness; Barcan; Boolean Completeness. |',
        '| FC; RC; TC | Functional, Relational and Transversal Choice. Rigid Comprehension is written out. |',
        '| TR; RP; WRP | Tame Rigidity; Rigid Power; Weakly Rigid Power. |',
        '| Max; SP; Σ | Maximalism; Strong Possibility; the specified nonlogical signature. Eligibility depends on the stated reference theory. |',
        '| PR | Profile Realization, a research proposal distinct from the database’s Actual Profile principle. |', '',
        'Axiom of Infinity is distinct from the Infinity schema. Quantification over properties ranges over those admitted by the model; the fullness result explicitly asks for more. The original C remains finitary.', '']
    out['MAIN-RESULTS.md'] = done(text)

    def section_results(section):
        return [rid for group in section['groups'] for rid in group['result_refs']] + [r['result_ref'] for r in section['supplemental_results']]

    presentation_order = [rid for section in overview['sections'] for rid in section_results(section)]
    assert len(presentation_order) == len(set(presentation_order)) == len(rows)
    assert set(presentation_order) == set(rows), 'Incomplete companion-page coverage'

    def part_navigation(target=''):
        lines = ['| Part | Sections |', '|---|---|']
        for pid, part in parts.items():
            links = ['[' + section['title'] + '](' + target + '#' + section['id'] + ')' for section in overview['sections'] if section['part'] == pid]
            if pid == 'database-connections':
                links += ['[Previously known results formalized](' + target + '#previously-known-results-formalized)']
            lines += ['| [' + part['title'] + '](' + target + '#' + pid + ') | ' + '; '.join(links) + '. |']
        return lines + ['']

    def known_formalizations(base='.', level=3, attribution=False):
        target = posixpath.relpath('MAIN-RESULTS.md', base)
        lines = [anchor('previously-known-results-formalized'), '#' * level + ' Previously known results formalized', '',
                 '[Original attribution and certified scope](' + target + '#previously-known-results-formalized).', '']
        for item in main['established_formalizations']['entries']:
            retained_anchor = anchor('analytic-rigidification-answer') if attribution and item['result_ref'] == 'ANALYTIC-RIGIDIFICATION' else ''
            line = '- ' + retained_anchor + resultlink(item['result_ref'], base=base, label=item['name'])
            if attribution:
                line += '. **Contribution: Lean formalization.** Existing mathematics: ' + item['attribution']
                if item.get('note'):
                    line += ' ' + item['note']
            lines += [line]
        return lines + ['']

    def full_result(r):
        lines = []
        lines += [anchor(r['id']), '#### ' + r['title'], '', '**ID:** `' + r['id'] + '`. Tracked keys: ' + ', '.join('`' + k + '`' for k in r['registry_ids']) + '.', '',
                 r['statement'], '', '**Scope:** ' + r['scope'], '', '**Significance:** ' + r['significance'], '',
                 certified_line(r), '']
        for field, title in [('notes', 'Notes'), ('attribution', 'Attribution')]:
            if r.get(field):
                lines += ['**' + title + ':** ' + r[field], '']
        if r.get('proof_idea'):
            lines += [r['proof_idea'], '']
        if r.get('proof_length'):
            length = r['proof_length']
            lines += ['**Proof length:** ' + length['rating'] + ' (' + format(length['words'], ',') + ' words in the [selected exposition](proof-lengths.json)).', '']
        if r.get('proof_locators'):
            lines += ['**Proof locators:** ' + '; '.join(r['proof_locators']), '']
        for field, title in [('proofs', 'Proofs'), ('lean_sources', 'Earlier Lean sources'), ('manifests', 'Earlier saved manifests'), ('evidence', 'Scope evidence'), ('certificates', 'Selected exact certificates')]:
            if r.get(field):
                lines += ['**' + title + ':** ' + prooflinks(r[field], 'evidence'), '']
        if r.get('declarations'):
            lines += ['**Principal declarations:**', '']
            lines += ['- `' + x + '`' for x in r['declarations']] + ['']
        return lines

    text = ['# Full results, supplements and certificates', '',
        '[Main results](../MAIN-RESULTS.md) · [Questions](../CONJECTURES.md) · [Catalog](../CATALOG.md) · [Database integration](../DATABASE-INTEGRATION.md)', '',
        'Full statements, supporting results, proofs and certificates.', '',
        anchor('browse-by-category'), '## Contents', '']
    text += part_navigation()
    current_part = None
    for section in overview['sections']:
        if section['part'] != current_part:
            if current_part == 'database-connections':
                text += known_formalizations('evidence')
            current_part = section['part']
            text += [anchor(current_part), '## ' + parts[current_part]['title'], '']
        text += [anchor(section['id']), '### ' + section['title'], '']
        for group in section['groups']:
            for rid in group['result_refs']:
                text += full_result(rows[rid])
        text += [anchor('supplement-' + alias) for alias in section.get('supplement_anchor_aliases', [])]
        text += [anchor('supplement-' + section['id'])]
        for item in section['supplemental_results']:
            text += full_result(rows[item['result_ref']])
    out['evidence/RESULT-INDEX.md'] = done(text)

    text = ['# Detailed result catalog', '',
        f'All {len(keys)} stable keys, including the original {len(coverage["original_catalog_keys_retained"])}, are retained. Keys may group several claims. Exact aliases resolve to MAIN-RESULTS.json; linked aggregate keys retain narrower evidence boundaries. Supporting module metadata remains in [CATALOG.json](CATALOG.json).', '',
        '[Main guide](MAIN-RESULTS.md) · [Questions](CONJECTURES.md) · [Integration review](DATABASE-INTEGRATION.md)', '']
    text += part_navigation('evidence/RESULT-INDEX.md')
    for item in catalog['entries']:
        r = dict(item)
        if 'result_ref' in r:
            assert set(('statement', 'proofs', 'lean_status', 'certificate_scope')).isdisjoint(r), 'Duplicated alias fields'
            source = rows[r['result_ref']]
            r.update(statement=source['statement'], proofs=source['proofs'], lean_status=source['lean_status'], certified_scope=source.get('certified_scope'))
        if r.get('lean_status_ref'):
            assert 'lean_status' not in r and 'lean_status_refs' not in r, 'Duplicated exact status reference'
            r['lean_status'] = rows[r['lean_status_ref']]['lean_status']
            r['certified_scope'] = rows[r['lean_status_ref']].get('certified_scope')
        text += [anchor(r['id']), '## ' + r['id'], '', r['statement'], '']
        if r.get('integration_status_refs') and not r.get('lean_status_ref') and not r.get('result_ref'):
            refs = r['integration_status_refs']
            assert all(ref in integration_claims for ref in refs), 'Missing claim-level assessment'
            text += ['**Evidence:** ' + ' · '.join('[' + integration_claims[ref].get('subclaim_id', ref) + '](DATABASE-INTEGRATION.md#' + ref.lower() + ')' for ref in refs) + '.', '']
        elif r.get('lean_status_refs'):
            assert 'lean_status' not in r, 'Duplicated aggregate status'
            for rid in r['lean_status_refs']:
                assert rid in rows
        if certified_line(r):
            text += [certified_line(r), '']
        elif r.get('lean_status_refs') and statusrefs(r['lean_status_refs']):
            text += ['**Lean certified:** ' + statusrefs(r['lean_status_refs']), '']
        if r.get('reconciliation_receipts'):
            text += ['**Exact reconciliation scope:** ' + r.get('certificate_scope', ''), '',
                     '**Scope assessment:** ' + prooflinks(r['reconciliation_receipts']), '']
        if r.get('proofs'):
            text += ['**Proofs:** ' + prooflinks(r['proofs']), '']
        if r.get('result_entries'):
            text += ['**Scoped evidence:** ' + ' · '.join(resultlink(x) for x in r['result_entries']), '']
        if r.get('integration_status_refs') and (r.get('lean_status_ref') or r.get('result_ref')):
            text += ['**Integration assessment:** ' + ' · '.join('[' + integration_claims[ref].get('subclaim_id', ref) + '](DATABASE-INTEGRATION.md#' + ref.lower() + ')' for ref in r['integration_status_refs']), '']
    out['CATALOG.md'] = done(text)

    database_questions = {r['id']: r for r in questions['database_questions']}
    question_order = [qid for s in questions['sections'] for qid in s['questions']]
    database_order = [qid for s in questions['sections'] for qid in s['database_questions']]
    assert len(question_order) == len(set(question_order)) == len(question_rows), 'Question section coverage'
    assert set(question_order) == set(question_rows), 'Missing question section'
    assert len(database_order) == len(set(database_order)) == len(database_questions), 'Database question section coverage'
    assert set(database_order) == set(database_questions), 'Missing database question section'
    model_rows = [m for family in questions['model_families'] for m in family['models']]
    assert len(model_rows) == questions['database_coverage']['model_construction_records'], 'Model family coverage'
    database_ids = [qid for r in [*questions['questions'], *database_questions.values(), *model_rows]
                    for qid in r.get('database_question_ids', [])]
    assert len(database_ids) == len(set(database_ids)) == questions['database_coverage']['recorded_questions'], 'Database question coverage'
    text = ['# ' + questions['title'], '',
        'The background is C unless stated otherwise. “Unresolved” refers to the cited evidence, not necessarily to the literature.', '',
        '[Main results](MAIN-RESULTS.md) · [Catalog](CATALOG.md) · [Evidence](evidence/RESULT-INDEX.md)', '',
        'The central open questions are listed below. Claims awaiting review are separate; resolved questions and established connections are grouped in expandable sections at the end.', '',
        '| Unresolved question | Scope |', '|---|---|']
    assert {r['question_ref'] for r in questions['open_overview']} == set(next(s for s in questions['sections'] if s['id'] == 'remaining-questions')['questions'])
    text += ['| [' + r['summary'] + '](#' + r['question_ref'].lower() + ') | ' + r['scope'] + ' |' for r in questions['open_overview']]
    text += ['', 'Further observer comparisons are listed in the [dedicated research frontier](proofs/h-observer-space/MAP.md#10-explicit-frontier).', '']
    text += ['- [' + part['title'] + '](#' + part['id'] + ')' for part in questions['parts']]
    text += ['']
    catalog_rows = {r['id']: r for r in catalog['entries']}

    def question_section(section):
        text = [anchor(section['id']), '### ' + section['title'], '']
        for qid in section['database_questions']:
            r = database_questions[qid]
            text += [anchor(r['id'])]
            text += [anchor(qid) for qid in r['database_question_ids'] if qid != r['id']]
            text += ['#### ' + r['question'], '', r['answer'], '', r['evidence'] + '.', '']
            if r.get('contribution'):
                text += [r['contribution'], '']
            if r.get('lean_certified'):
                text += ['**Lean certified.**', '']
            elif statusrefs(r['formalization_result_refs']):
                text += ['**Lean certified:** ' + statusrefs(r['formalization_result_refs']), '']
        for qid in section['questions']:
            r = question_rows[qid]
            assert 'lean_status' not in r, 'Duplicated question formalization status'
            text += [anchor(r['id']), '#### ' + r['question'], '', '**Position:** ' + r['status'] + '.', '', r['established'], '']
            if r.get('contribution'):
                text += [r['contribution'], '']
            if r.get('remaining'):
                text += [r['remaining'], '']
            if statusrefs(r['formalization_result_refs']):
                label = '**Lean-certified related results:** ' if section['part'] in ('open', 'review') else '**Lean certified:** '
                text += [label + statusrefs(r['formalization_result_refs']), '']
            for rid in r['result_entries']:
                assert rid in rows
        for r in section['connections']:
            text += [anchor(r['id']), '#### ' + r['title'], '', r['text'], '']
            if r.get('contribution'):
                text += [r['contribution'], '']
            refs = r['result_refs']
            evidence = [resultlink(rid, label=rows[rid]['title']) for rid in refs]
            for cid in r['catalog_refs']:
                assert cid in catalog_rows, 'Missing connection evidence'
                evidence.append('[' + cid + '](CATALOG.md#' + cid.lower() + ')')
            text += ['**Evidence:** ' + ' · '.join(evidence) + '.', '']
            if statusrefs(refs):
                text += ['**Lean certified:** ' + statusrefs(refs), '']
            for cid in r['catalog_refs']:
                cr = catalog_rows[cid]
                if cr.get('certified_scope'):
                    scope = '' if cr['certified_scope'] is True else ': ' + cr['certified_scope'].rstrip('.')
                    text += ['**Lean certified:** [' + cid + '](CATALOG.md#' + cid.lower() + ')' + scope + '.', '']
        return text

    resolved_started = False
    for part in questions['parts']:
        kind = part.get('kind', 'open')
        selected = [s for s in questions['sections'] if s['part'] == kind]
        resolved = kind not in ('open', 'review')
        if resolved and not resolved_started:
            text += ['---', '', '## Resolved questions and established connections', '',
                     'New proofs and countermodels are distinguished from formalizations of earlier results. Existing database answers retained for context are credited to their sources.', '']
            resolved_started = True
        text += [anchor(alias) for alias in part.get('anchor_aliases', [])]
        text += [anchor(part['id'])]
        if resolved:
            text += ['<details>', '<summary><strong>' + part['title'] + '</strong></summary>', '']
        else:
            text += ['## ' + part['title'], '']
        text += [' · '.join('[' + s['title'] + '](#' + s['id'] + ')' for s in selected), '']
        if kind == 'review':
            text += questions.get('review_notes', []) + ['']
        for section in selected:
            text += question_section(section)
        if kind == 'database':
            text += [anchor('resolved-model-questions'), '### Resolved model-construction questions', '',
                'These nineteen constructions and their recorded existence verdicts are existing database results, included for reference rather than claimed as new models or formalizations. Signature, individual-domain and metatheoretic variants are grouped with their construction; the linked records give the attribution and exact scope.', '']
            for family in questions['model_families']:
                text += [anchor(family['id']), '#### ' + family['title'], '']
                for r in family['models']:
                    text += ['- **' + r['name'] + '.** ' + r['answer'] + ' ' + r['evidence'] + '.']
                text += ['']
            text += known_formalizations(attribution=True)
        if resolved:
            text += ['</details>', '']
    out['CONJECTURES.md'] = done(text)

    records = integration['records']
    for rec in records.values():
        file = root / rec['snapshot_path']
        assert hashlib.sha256(file.read_bytes()).hexdigest() == rec['sha256'], 'Changed database snapshot'
    by_result = {r['result_id']: r for r in integration['entries']}
    text = ['# Database integration review', '',
        'Each detailed result is matched to existing database records or proposed additions. Related principles supply context; exact matches are identified separately. The displayed database states are captured snapshots, with research-certificate scope recorded separately.', '',
        'The research proof and Lean status come from [the evidence index](evidence/RESULT-INDEX.md). Record snapshots and hashes are preserved in [DATABASE-INTEGRATION.json](DATABASE-INTEGRATION.json). Official verified flags require the database’s generated-statement checking workflow. Independence belongs in model records.', '',
        '**Record review:** ' + integration['reviewed_at_utc'] + '. Later capture times and hashes are recorded per snapshot.', '',
        '**Latest reconciliation:** ' + integration.get('reconciled_at_utc', integration['reviewed_at_utc']) + '.', '',
        '[CANDIDATES_DK](CANDIDATES_DK.md) isolate new explorer entries from alternative presentations of existing strengths. The source is [CANDIDATES_DK.json](CANDIDATES_DK.json); proposed entries are not active database assumptions.', '']
    text += part_navigation()
    current_part = None
    for section in overview['sections']:
        if section['part'] != current_part:
            if current_part == 'database-connections':
                text += known_formalizations()
            current_part = section['part']
            text += [anchor(current_part), '## ' + parts[current_part]['title'], '']
            if current_part == 'database-connections':
                text += [anchor('headline-results')]
        for alias in {'h-observer-separation': ['observer-separation-over-h'], 'worlds-and-probability': ['worlds-and-model-structure']}.get(section['id'], []):
            text += [anchor(alias)]
        text += [anchor(section['id']), '### ' + section['title'], '', '| Research result and evidence | Existing record or context | Proposed action |', '|---|---|---|']
        for rid in section_results(section):
            entry = by_result[rid]
            contexts = []
            for target in entry['records']:
                rec = records[target['record']]
                status = rec.get('status_at_review')
                lean = rec.get('lean_at_review')
                if isinstance(lean, dict):
                    if 'status' in lean:
                        lean = lean['status']
                    elif 'verdicts' in lean:
                        counts = {}
                        for verdict in lean['verdicts']:
                            state = verdict.get('status', 'unspecified')
                            counts[state] = counts.get(state, 0) + 1
                        lean = ', '.join(str(n) + ' ' + state + ' verdicts' for state, n in sorted(counts.items()))
                    else:
                        lean = 'see captured record for scope'
                detail = target['role']
                if status:
                    detail += '; ' + str(status)
                if lean:
                    detail += '; Lean ' + str(lean)
                contexts.append(filelink(rec['snapshot_path'], label='`' + rec['id'] + '`') + ' (' + detail + ')')
            context = '<br>'.join(contexts) if contexts else 'New metatheorem; no exact existing record matched.'
            cells = [resultlink(rid, label=rows[rid]['title']) + ('<br>' + certified_line(rows[rid]) if certified_line(rows[rid]) else ''), context, '**' + entry['action'] + '.** ' + entry['proposal']]
            text += ['| ' + ' | '.join(x.replace('|', '\\|').replace('\n', ' ') for x in cells) + ' |']
        text += ['']
    if integration.get('closure_cross_references'):
        text += ['## Existing closure consequences', '',
                 'These routes use already proved database records. They are cross-references, not new result registrations or new combined Lean certificates.', '']
        if integration.get('closure_evidence'):
            receipt = integration['closure_evidence']
            receipt_bytes = (root / receipt['path']).read_bytes()
            assert hashlib.sha256(receipt_bytes).hexdigest() == receipt['sha256']
            used_sources = json.loads(receipt_bytes)['used_result_sha256']
            assert set(receipt['result_sources']) == set(used_sources), 'Incomplete closure source map'
            for source, sha in used_sources.items():
                saved = receipt['result_sources'][source]
                assert saved['sha256'] == sha, 'Closure source hash differs from receipt'
                assert hashlib.sha256((root / saved['path']).read_bytes()).hexdigest() == sha, 'Changed closure source'
            text += ['**Saved proved-only closure checks:** ' + filelink(receipt['path']) + '.', '']
            text += [receipt['scope_note'] + ' Exact paths and hashes are in [the source map](DATABASE-INTEGRATION.json).', '']
        for item in integration['closure_cross_references']:
            text += [anchor(item['id']), '### ' + item['title'], '', item['summary'], '', item['scope'], '',
                     '**Recorded route:** ' + ' · '.join(filelink(records[key]['snapshot_path'], label='`' + records[key]['id'] + '`') for key in item['records']), '',
                     '**Research connections:** ' + ' · '.join(resultlink(rid) for rid in item['result_entries']), '']
    if integration.get('scope_receipts'):
        text += ['## Exact scope assessments', '',
                 'These saved assessments reconcile accepted evidence with the catalog claims. They do not run Lean or turn supporting components into complete principal certificates.', '']
        for receipt in integration['scope_receipts']:
            assert hashlib.sha256((root / receipt['path']).read_bytes()).hexdigest() == receipt['sha256']
            text += ['- ' + filelink(receipt['path'])]
        text += ['']
    if integration.get('formulation_audits'):
        text += ['## Formulation audits', '']
        for item in integration['formulation_audits']:
            assert hashlib.sha256((root / item['proof_path']).read_bytes()).hexdigest() == item['source_sha256']
            text += [anchor(item['id']), '### ' + item['title'], '', '**Position:** ' + item['status'], '',
                     item['summary'], '', item['scope'], '', item['completeness'], '',
                     '**Lean:** ' + item['lean_status'], '',
                     '**Proof and source comparison:** ' + filelink(item['proof_path']) + '.', '',
                     '**Existing records:** ' + ' · '.join(filelink(records[key]['snapshot_path'], label='`' + records[key]['id'] + '`') for key in item['records']), '']
    if integration.get('registered_supplementary_results'):
        text += ['## Newly registered results matched in this review', '',
                 'These ordinary proved records preserve the original typed arguments. Their generated-record Lean status remains separate from the research certificates.', '']
        for item in integration['registered_supplementary_results']:
            rec = records[item['record']]
            writeup = ' · ' + filelink(item['writeup_path'], label='Proof and exact type scope') if item.get('writeup_path') else ''
            text += ['- ' + filelink(rec['snapshot_path'], label='`' + item['id'] + '`') + writeup + '. Database status: ' + item['status'] + '; Lean: ' + item['lean_at_receipt'] + '.']
        text += ['']
    supplementary = integration['coverage']['supplementary_review_keys']
    assert {r['id'] for r in catalog['entries'] if not r.get('result_entries')} <= set(supplementary)
    reconciled = integration.get('supplementary_entries', [])
    reconciled_keys = {r['catalog_id'] for r in reconciled}
    claim_ids = [r.get('claim_id', r['catalog_id']) for r in reconciled]
    assert len(set(claim_ids)) == len(claim_ids), 'Repeated supplementary claim'
    assert reconciled_keys <= set(supplementary), 'Unexpected supplementary key'
    pending = [k for k in supplementary if k not in reconciled_keys]
    text += ['## Supplementary catalog reconciliation', '',
        f'{len(reconciled_keys)} of the {len(supplementary)} supplementary review keys are covered below, in {len(reconciled)} claim-level rows. This is matching and scope review; a matched record, derived consequence or supporting certificate does not establish every stronger claim in the same family. Rows split compound claims for accuracy and are not a count of new theorems.', '']
    if integration.get('supplementary_intake'):
        receipt = integration['supplementary_intake']
        assert hashlib.sha256((root / receipt['path']).read_bytes()).hexdigest() == receipt['sha256']
        text += ['**Source assessment:** ' + filelink(receipt['path']) + '. Exact claims, source locators and remaining gaps are retained in the structured table.', '']
    unresolved = [r for r in reconciled if r.get('relationship') == 'unresolved']
    if unresolved:
        text += ['**Unresolved assessment rows:** ' + ' · '.join('[`' + r['catalog_id'] + '` — ' + r.get('subclaim_id', '') + '](#' + r.get('claim_id', r['catalog_id']).lower() + ')' for r in unresolved) + '. Registration and certificate follow-ups on other rows are separate from these unresolved assessments.', '']
    unresolved = [r for r in reconciled if r.get('relationship') == 'unresolved']
    if unresolved:
        text += ['**Unresolved assessment rows:** ' + ' · '.join('[`' + r['catalog_id'] + '` — ' + r.get('subclaim_id', '') + '](#' + r.get('claim_id', r['catalog_id']).lower() + ')' for r in unresolved) + '. Registration and certificate follow-ups on other rows are separate from these unresolved assessments.', '']
    unresolved = [r for r in reconciled if r.get('relationship') == 'unresolved']
    if unresolved:
        text += ['**Unresolved assessment rows:** ' + ' · '.join('[`' + r['catalog_id'] + '` — ' + r.get('subclaim_id', '') + '](#' + r.get('claim_id', r['catalog_id']).lower() + ')' for r in unresolved) + '. Registration and certificate follow-ups on other rows are separate from these unresolved assessments.', '']
    family = None
    for item in reconciled:
        current_family = item['catalog_id'].split('.')[0]
        if current_family != family:
            family = current_family
            text += ['### ' + family, '', '| Catalog key and scope | Existing match | Action and remaining limits | Proof and Lean scope |', '|---|---|---|---|']
        matches = []
        for match in item.get('matched_records', []):
            rec = records[match['record']]
            matches.append(filelink(rec['snapshot_path'], label='`' + rec['id'] + '`') + ' (' + match['relationship'] + ')')
        for rid in item.get('result_entries', []):
            matches.append(resultlink(rid))
        evidence = []
        for source in item.get('proofs', []):
            label = source.get('label') or Path(source.get('path', source.get('origin', 'source'))).name
            if source.get('path'):
                evidence.append(filelink(source['path'], label=label) + (' — ' + source['locator'] if source.get('locator') else ''))
            else:
                evidence.append(label + (' — ' + source['locator'] if source.get('locator') else '') + ' (source locator; bytes not retained)')
        status = rows[item['lean_status_ref']]['lean_status'] if item.get('lean_status_ref') else item['lean_status']
        action = item['action']
        if item.get('blockers'):
            action += ' **Remaining:** ' + ' '.join(item['blockers'])
        if item.get('follow_up'):
            action += ' **Follow-up:** ' + item['follow_up']
        claim_name = (' · `' + item['subclaim_id'] + '`') if item.get('subclaim_id') else ''
        claim_anchor = anchor(item.get('claim_id', item['catalog_id']))
        cells = [claim_anchor + '[`' + item['catalog_id'] + '`](CATALOG.md#' + item['catalog_id'].lower() + ')' + claim_name + '<br>' + item['scope'],
                 '<br>'.join(matches) or 'No exact existing record matched; see the proposed action.',
                 action, status.rstrip('.') + '.' + ('<br>' + '<br>'.join(evidence) if evidence else '')]
        text += ['| ' + ' | '.join(x.replace('|', '\\|').replace('\n', ' ') for x in cells) + ' |']
    if pending:
        text += ['', '**Awaiting individual reconciliation:** ' + ', '.join('[`' + k + '`](CATALOG.md#' + k.lower() + ')' for k in pending) + '.', '']
    else:
        text += ['', 'All supplementary review keys are reconciled. Any remaining mathematical, source or formalization obligations are stated in their rows; reconciliation does not mark them proved or fully formalized.', '']
    out['DATABASE-INTEGRATION.md'] = done(text)
    text = ['# Results and certificate scope', '',
        'Research submission: results, proofs and exact certificate scope.', '',
        '[Main guide](MAIN-RESULTS.md) · [Exact evidence](evidence/RESULT-INDEX.md) · [Database reconciliation](DATABASE-INTEGRATION.md) · [Questions](CONJECTURES.md)', '',
        '## Certified results', '']
    for pid, part in parts.items():
        text += [anchor(pid), '### ' + part['title'], '']
        for section in overview['sections']:
            if section['part'] != pid:
                continue
            for rid in section_results(section):
                r = rows[rid]
                if r.get('certified_scope'):
                    text += ['- **' + r['title'] + '.** ' + ('Lean certified.' if r['certified_scope'] is True else 'Lean certified: ' + r['certified_scope']) + ' ' + resultlink(rid, label='Proof and certificate') + '.']
        text += ['']
        if pid == 'database-connections':
            text += known_formalizations(level=4)
    text += ['',
        '## Sources and reproduction', '',
        'Source proofs and accepted certificate evidence are linked in [SOURCE-MANIFEST.json](SOURCE-MANIFEST.json) and [the certificate index](evidence/CERTIFICATES.json).', '',
        'The summaries and this scope note are generated from the canonical records. Follow [REPRODUCING.md](REPRODUCING.md) for drift checks, exact-source verification and intentional checksum refreshes.', '']
    out['RELEASE-NOTES.md'] = done(text)
    return {name: protect_markdown_math(body) for name, body in out.items()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--write', action='store_true')
    parser.add_argument('--refresh-checksums', action='store_true')
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    if args.refresh_checksums and not args.write:
        parser.error('--refresh-checksums requires --write')
    root = args.root.resolve()
    expected = render(root)
    layout_issues = []
    pages = sorted(set(root.glob('*.md')) | set((root / 'proofs').rglob('*.md')))
    for path in pages:
        name = path.relative_to(root).as_posix()
        layout_issues += math_layout_issues(name, expected.get(name, path.read_text()))
    if layout_issues:
        raise SystemExit('\n'.join(layout_issues))
    changed = []
    for name, body in expected.items():
        path = root / name
        if not path.is_file() or path.read_text() != body:
            changed.append(name)
            if args.write:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(body)
    if args.refresh_checksums:
        inventory = []
        for path in sorted(root.rglob('*')):
            if path.is_file() and path != root / 'SHA256SUMS':
                inventory.append(hashlib.sha256(path.read_bytes()).hexdigest() + '  ' + path.relative_to(root).as_posix())
        (root / 'SHA256SUMS').write_text('\n'.join(inventory) + '\n')
    print(json.dumps({'mode': 'write' if args.write else 'check', 'generated_files': len(expected),
                      'changed_or_stale': changed, 'checksums_refreshed': args.refresh_checksums,
                      'lean_invoked': False}))
    return 0 if args.write or not changed else 1


if __name__ == '__main__':
    raise SystemExit(main())
