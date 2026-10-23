# Classicism — working bundle

A self-contained copy of one logical map: the axioms of a subject, the implications between them, the countermodels that refute the remaining implications, and the proofs for all of it. Unzip anywhere and start working.

Contains 132 principles, 438 proved results, 9 conjectures and 162 models, with the source documents they were extracted from.

## Read in this order

1. **`MAP.md`** — everything, in one file: framework, principle statements, every proof, every model construction, and the derived verdicts. Start here.
2. **`OPEN-QUESTIONS.md`** — what the map does not settle, grouped so each entry is a concrete piece of work.
3. **`topics/classicism/extraction.md`** — how the records were read out of the sources, which transcription decisions were made, and what was deliberately left out.
4. **`topics/classicism/sources/`** — the original papers.

`data.json` and `derived.json` hold the same content structured, if you would rather compute over it than read it.

## Layout

```
MAP.md OPEN-QUESTIONS.md      the map as prose
data.json derived.json        records, and every derived verdict
topics/classicism/
  topic.yaml                  title, source catalog, categories, viewer packages
  background.md               the framework in full
  extraction.md               source inventory, transcription decisions, deferred items
  principles/<id>.yaml        one principle per file
  results/<id>.yaml           premises ⇒ conclusion, with its proof
  models/<id>.yaml            satisfies [...] / violates [...], or a definition and arguments
  provenance/<id>.yaml        provenance moved out of a model record, named by its arguments
  writeups/<id>.md            hand-written write-up, overrides the generated one
  checks/                     executable sanity checks for the models
  sources/                    original papers
scripts/pmap.py schema/ viewer/  the tooling, so validate and build work here
```

## Semantics

Everything is relative to the topic background B (see `MAP.md` §1).

- A **result** is a Horn clause, premises ⇒ principle or False. `cl(S)` is the closure of B ∪ S under all proved results.
- A **model** M records `sat(M)` and `viol(M)` and witnesses that `sat(M) ∪ {¬v : v ∈ viol(M)}` is consistent. Derived: `holds(M) = cl(sat(M))`, and `fails(M) = {c : cl(sat(M) ∪ {c}) meets viol(M) or contains False}`. Everything else is unknown in M.
- **P ⇒ c** iff `c ∈ cl(P)`. **P ⇏ c** iff some model has `P ⊆ holds(M)` and `c ∈ fails(M)`. **P ⇒ ¬c** when adjoining c reaches False. This is an exclusion, not a model witness. Inconsistent packages are reported separately, with no explosion. Otherwise the pair is **open**.
- Mutually derivable principles collapse to one node.
- Conjectures are displayed but never used as evidence.
- Deriving False or an explicitly violated principle from a model is a validation error.

**A missing arrow means nothing was recorded.** The map is curated, not exhaustive.

## Adding to it

```yaml
# topics/classicism/results/<id>.yaml   —   file name must equal the id
id: my-new-result
premises: [principle-a, principle-b]     # every assumption actually used
conclusion: principle-c                 # use false for incompatible premises
status: conjectured                       # promote only after supplying a proof
certificate:
  source_id: misc                         # a source_catalog id; misc for original work
  lean: none
  produced_by: "who proposed the claim"
  recorded_by: "who transcribed it"       # optional, kept separate
  checked_by: []                          # only actual checkers
  date: 'YYYY-MM-DD'
proof: ""
sources:
  - Full reference, with theorem or section and page.
source_names: [Short label]               # one per source, same order
notes: "State what would settle this proposal."
```

```yaml
# topics/classicism/models/<id>.yaml
id: my-new-model
name: 'Construction family: ordering rule'
satisfies: [principle-a, principle-b]     # only what you actually verified
violates: [principle-c]                   # the engine derives the rest
status: conjectured                      # promote only after checking the model
certificate: {source_id: misc, lean: none, produced_by: "...", checked_by: [], date: 'YYYY-MM-DD'}
description: |
  The construction, and why it has these properties.
sources: [Full reference or an identifiable original proof]
source_names: [Short label]
```

Give models short, systematic names describing their construction or ordering rule: family first, then the rule and any distinguishing variant. Match the write-up title. Keep authorship, conjecture status, and lists of satisfied/violated principles in their own fields. For a conjectured extension, name the proposed extension without inventing a construction. Keep existing record IDs unchanged.

For A ∧ B ⇒ ¬C, record `premises: [a, b, c]` and `conclusion: false`. False is a reserved conclusion, not a principle. The same constraint lets A and C rule out B.

Counterexamples to implications are recorded as models. A result concluding false instead proves incompatibility; it does not establish that any premise package has a model.

## Sourcing rules

These are what make the map worth anything. Follow them exactly.

- Every result and model needs a nonempty `sources`. Give the paper with theorem/section and page, or an identifiable original proof for new work.
- `certificate.source_id` names the **direct** source. Declared sources here:
  - `bacon-dorr-classicism` — Classicism (2024) (published-paper)
  - `dorr-bc-not-rc` — BC does not imply RC (draft) (misc)
  - `lewin-1991` — Lewin, A Simple Proof of Zorn's Lemma (published-paper)
  - `prior-1963` — Prior, Formal Logic (published-paper)
  - `prior-lemmon` — Prior / Lemmon on BF (published-paper)
  - `bacon-2020` — Logical Combinatorialism (published-paper)
  - `bacon-2024-book` — Philosophical Introduction to HOL (2024) (published-paper)
  - `bacon-mathematical-contingency` — Could the truths of mathematics have been different? (draft) (misc)
  - `barton-goodsell-continuum-contingency` — Continuum Contingency (draft) (misc)
  - `the-broadest-necessity` — The Broadest Necessity (published-paper)
  - `necessity-of-identity` — Necessity of identity (historical) (misc)
  - `goodsell-yli-vakkuri-unpublished` — Goodsell / Yli-Vakkuri (unpublished) (misc)
  - `goodsell-pc` — Goodsell (personal communication) (misc)
  - `goodsell-arithmetic-necessary` — Arithmetic is Necessary (2024 draft) (misc)
  - `sun-possible-worlds-without-atomicity` — Possible Worlds Without Atomicity (draft) (misc)
  - `bounds-of-possibility` — The Bounds of Possibility (2021) (published-paper)
  - `misc` — Misc. (misc)
- Use `misc` for original proofs, one-off prompts and user suggestions. Citing a paper's definitions does **not** make that paper the source of your new proof.
- `produced_by` credits the mathematics; `recorded_by` credits transcription only.
- Leave `checked_by: []` unless a named person actually checked it. A human-authored source does not mean a human checked this database's translation of it.
- Never invent an author, a date, a page or a submission label. If you are unsure of a reference, say so in `notes` rather than guessing.
- If you are unsure of the mathematics, record `status: conjectured` with an empty proof and write in `notes` what would settle it. That is a useful contribution; a wrong `proved` is not.
- Do not change the mathematical content of an existing published or human-authored proof. Add a note, or a new record, instead.
- File name equals `id`, kebab-case. Never rename an id that other files reference.
- When an existing record gains content after its certificate date (a newly verified property of a model, an added proof, a corrected statement), append an entry to its `changes` list: `{date, by, summary}` plus, for models, the newly verified `satisfies`/`violates` ids. The Changes tab lists each entry under its own date; leave `certificate.date` as the record's original date.
- Keep the framework fixed. A principle needing a different setting belongs to a different topic.

## Lean

If `topics/classicism/lean/` is present, the topic has a formalisation. The YAML is the
source of truth for statements: each principle names its Lean definition in `lean_def`,
and every result and model statement is generated from its premises and conclusion into
`Statements.lean`. To prove a record, inhabit its generated `Prop`. Never edit the
generated file, and never hand-set `lean: verified` -- `pmap lean-check` builds the
library, confirms the proof inhabits the generated statement, and rejects anything
still depending on `sorryAx`. `lean: stated` means the statement elaborates and the
proof is missing. See that folder's README for the modelling choices.

## Commands

```sh
pip install -r requirements.txt
python3 scripts/pmap.py validate            # schema, references, consistency. Must pass.
python3 scripts/pmap.py status              # counts, open pairs, redundancies
python3 scripts/pmap.py lynchpins           # open questions ranked by what each answer settles
python3 topics/classicism/checks/action_strong_worlds.py   # topic checks
python3 topics/classicism/checks/boolean_valued_choice.py   # topic checks
python3 topics/classicism/checks/finite_support_bounds.py   # topic checks
python3 topics/classicism/checks/henkin.py   # topic checks
python3 topics/classicism/checks/qualitative_contrast_choice.py   # topic checks
python3 scripts/pmap.py build               # regenerate build/<topic>/index.html, the map viewer
python3 scripts/pmap.py selftest            # the derivation engine's own tests
python3 scripts/check_falsity.py            # Python/browser semantics and False; needs Node
python3 scripts/pmap.py lean                # regenerate the Lean statements
python3 scripts/pmap.py lean-check          # build the Lean library and audit lean: claims
```

A `CONTRADICTION` from `validate` means the data is inconsistent and must be fixed before anything else. Rerun `validate` after every batch of edits.

## Sending work back

The whole of `topics/classicism/` is portable: copy it back over the same folder in the main repository, or send the individual new YAML files. Nothing outside that folder needs to change.

<p class="thanks">Thanks to <a class="prismatic" style="--prism-x: 47%; --prism-y: 58%" href="https://ciandorr.github.io/" target="_blank" rel="noopener">Cian Dorr</a> for major contributions to Classicism + Logical Maps!</p>

Email me (Zach) at [zacharyw.goodsell@gmail.com](mailto:zacharyw.goodsell@gmail.com?subject=%5BLogical%20Maps%5D%20Classicism) with further suggestions.

To contribute to Classicism, please include **[Logical Maps] Classicism** in the subject line of your email. You can suggest a new principle, establish a new result, or define a new model, along with supporting documents if necessary (e.g. a PDF or Markdown file). I will be sure to record your role in the contribution if I add it to this page. Thank you!

Worked on an open question without settling it? Feel free to send what you tried and I will put your work into the question’s notes and credit your contribution. This gives it a <span class="iridescent bronze">bronze</span> star in the Conjectures tab. Please also say whether you think the question is important or difficult enough to deserve a <span class="iridescent silver">silver</span> or <span class="iridescent gold">gold</span> star.

To contribute to the Logical Maps project in general, please include **[Logical Maps]** in the subject line.

## Tooling licence

The reusable scripts, schemas, viewer, and starter templates are supplied under [the MIT licence](starter/LICENSE). This does not grant rights to this topic's papers or other separately supplied content.
