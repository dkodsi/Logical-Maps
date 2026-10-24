"""Presentation spelling of principle names; source records and proofs are unchanged."""
import re


def database_notation(text):
    protected = []
    def protect(match):
        protected.append(match.group())
        return '\x00' + str(len(protected) - 1) + '\x00'
    text = re.sub(r'```[\s\S]*?```|`[^`\n]*`|(?<=\]\()[^\n]*?(?=\))', protect, text)
    # These replacements concern prose labels, never theorem identifiers or source paths.
    exact = {
        'necessary relational BF': '☐BF (type τ, τ ≠ e)',
        'necessary all-type Barcan': '☐BF',
        'boxed all-type BF': '☐BF',
        'propositional Atomicity': 'Atomicity (type t)',
        'Propositional Atomicity': 'Atomicity (type t)',
        'boxed-Rigid-Power': '☐Rigid Power',
        'Full Choice and boxed Plenitude have the same ordinary arithmetic': '☐Functional Choice and ☐Plenitude have the same ordinary arithmetic',
        'Full Choice contributes selection': '☐Functional Choice contributes selection',
        'Full Choice arithmetic conservativity': '☐Functional Choice arithmetic conservativity',
        'Does full Choice add ordinary arithmetic over boxed Plenitude?': 'Does ☐Functional Choice add ordinary arithmetic over ☐Plenitude?',
        'strong-section characterization of necessary Choice': 'strong-section characterization of ☐Functional Choice',
        'C; actual, unboxed premises.': 'C.',
        'Pure C; both initial premises unboxed;': 'Pure C;',
        'Pure C; ND and BC are unboxed.': 'Pure C + ND + Boolean Completeness.',
        'Atomicity is unboxed. ': '',
        'The premises are local, not boxed.': '',
        'Both premises are unboxed; ': '',
        '; the entire section schema is unboxed': '',
        'Commutation is unboxed pointwise identity.': 'Commutation is pointwise identity.',
        'All laws and quantifiers are local.': '',
        'Two local hypotheses force several necessary principles.': 'Strong Leibniz Biconditionals and Rigid Comprehension entail several principles under ☐.',
        'Completeness and local stability of identity': 'Completeness and ND',
        'corrected local BC proof': 'corrected BC proof',
        'weaker local version': 'weaker version',
        'The local R09 theorem': 'The R09 theorem',
        'optional local hypotheses': 'optional hypotheses',
        'convincing local counterexample': 'single-type counterexample',
        'type-local': 'type-specific',
        'necessary local existence': 'existence of an evaluator at each evaluation point',
        'C5 is boxed ND at every type; Atomicity is unboxed and only at t.': 'C5 is C + ☐ND; the Atomicity premise is Atomicity (type t).',
        'as full all-type schemas': 'as schemas',
        'as full schemas': 'as schemas',
        'the all-type requirement is essential': 'the type-schema requirement is essential',
        'The all-type requirement is essential': 'The type-schema requirement is essential',
        'Full schema': 'Schema',
        'full-schema': 'schema',
        'full schemas': 'schemas',
        'all-type schemas': 'schemas',
        'the full-schema question': 'the schema question',
    }
    for old, new in exact.items():
        text = text.replace(old, new)
    names = [
        'Strong Leibniz Biconditionals', 'Strong Leibniz', 'Inextensible Comprehension',
        'Rigid Comprehension', 'Weakly Rigid Power', 'Weak Rigid Comprehension',
        'Boolean Completeness', 'Countable Boolean Completeness', 'Tame Rigidity',
        'Rigid Power', 'Functional Choice', 'Relational Choice', 'Transversal Choice',
        'Intensionality', 'Functionality', 'Extensionality', 'Plenitude', 'Actuality',
        'Atomicity', 'Barcan', 'ND', 'BF', 'BC', 'FC', 'RC', 'TC', 'TR', 'RP', 'WRP',
    ]
    principle = '(?:' + '|'.join(re.escape(n) for n in names) + ')'
    for _ in range(3):
        text = re.sub(r'\b(?:[Ff]ull|[Aa]ll-type|[Ll]ocal|[Uu]nboxed)\s+(?=(?:(?:necessary|boxed|full|all-type)\s+){0,2}' + principle + r'\b)', '', text)
    text = re.sub(r'\b(?:[Nn]ecessary|[Bb]oxed)\s+(' + principle + r')\b', r'☐\1', text)
    text = re.sub(r'\bStrong Leibniz\b(?! Biconditionals)', 'Strong Leibniz Biconditionals', text)
    text = re.sub(r'\bBarcan\b', 'BF', text)
    text = re.sub(r'(' + principle + r')\s+at (\(et\)t|et|tt|e|t)\b', r'\1 (type \2)', text)
    text = text.replace('boxed quantified Infinity', '☐Axiom of Infinity')
    text = text.replace('quantified Infinity_e', 'Axiom of Infinity (type e)')
    text = text.replace('quantified Infinity at e and t', 'Axiom of Infinity (types e and t)')
    text = text.replace('quantified Infinity at e', 'Axiom of Infinity (type e)')
    text = text.replace('□', '☐')
    text = re.sub('\x00(\d+)\x00', lambda m: protected[int(m.group(1))], text)
    return text
