"""Generate finite SetFormula macros with checked lexical variable binding.

This is source preparation, not a proof checker. The serial Lean owner checks
the generated intrinsically indexed syntax and its generic purity/type proofs.
No compiler, package manager, or network operation is invoked here.
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
OUT = ROOT / "topics/classicism/lean/Classicism/Results/Research/MaxAtomicitySetLibrary.lean"

def eq(x, y): return ("eq", x, y)
def mem(x, y): return ("mem", x, y)
def neg(p): return ("neg", p)
def ne(x, y): return neg(eq(x, y))
def And(*ps): return ("and", list(ps))
def Or(*ps): return ("or", list(ps))
def Imp(p, q): return ("imp", p, q)
def Iff(p, q): return ("iff", p, q)
def call(name, *args): return ("call", name, list(args))
def bind(kind, names, body):
    for name in reversed(names.split()): body = (kind, name, body)
    return body
def All(names, body): return bind("all", names, body)
def Ex(names, body): return bind("ex", names, body)
def InAll(x, X, body): return All(x, Imp(mem(x, X), body))
def InEx(x, X, body): return Ex(x, And(mem(x, X), body))

defs = []
def D(name, params, body, doc): defs.append((name, params.split(), body, doc))

D("emptySet", "x", All("z", neg(mem("z", "x"))), "x is the empty set.")
D("subset", "x y", All("z", Imp(mem("z", "x"), mem("z", "y"))), "Literal subset.")
D("singleton", "s x", All("z", Iff(mem("z", "s"), eq("z", "x"))), "s = {x}.")
D("doubleton", "d x y", All("z", Iff(mem("z", "d"), Or(eq("z", "x"), eq("z", "y")))), "d = {x,y}.")
D("orderedPair", "p x y", Ex("s d", And(call("singleton", "s", "x"), call("doubleton", "d", "x", "y"), call("doubleton", "p", "s", "d"))), "Kuratowski ordered pair.")
D("app", "f x y", Ex("p", And(mem("p", "f"), call("orderedPair", "p", "x", "y"))), "Set-coded function application.")
D("app2", "f x y z", Ex("p", And(call("orderedPair", "p", "x", "y"), call("app", "f", "p", "z"))), "Application of a graph with an ordered-pair input.")
D("successor", "y x", All("z", Iff(mem("z", "y"), Or(mem("z", "x"), eq("z", "x")))), "Von Neumann successor y=x union {x}.")
D("tuple5", "c a b d e f", Ex("u v w", And(call("orderedPair", "w", "e", "f"), call("orderedPair", "v", "d", "w"), call("orderedPair", "u", "b", "v"), call("orderedPair", "c", "a", "u"))), "c=(a,(b,(d,(e,f)))).")
D("functionGraph", "f domain codomain", And(
    InAll("r", "f", Ex("x y", And(mem("x", "domain"), mem("y", "codomain"), call("orderedPair", "r", "x", "y")))),
    InAll("x", "domain", Ex("y", And(mem("y", "codomain"), call("app", "f", "x", "y"), All("z", Imp(call("app", "f", "x", "z"), eq("z", "y"))))))),
    "Exact graph, total on domain, single valued, with no extraneous entries.")
D("injective", "f domain", All("x y z", Imp(And(mem("x", "domain"), mem("y", "domain"), call("app", "f", "x", "z"), call("app", "f", "y", "z")), eq("x", "y"))), "Injective on the specified domain.")
D("bijective", "f domain codomain", And(call("functionGraph", "f", "domain", "codomain"), call("injective", "f", "domain"), InAll("y", "codomain", InEx("x", "domain", call("app", "f", "x", "y")))), "Bijection via its exact graph.")
D("inductiveSet", "v", And(Ex("z", And(call("emptySet", "z"), mem("z", "v"))), InAll("x", "v", InEx("y", "v", call("successor", "y", "x")))), "An inductive set, with the empty set bound locally.")
D("omega", "w", And(call("inductiveSet", "w"), All("v", Imp(call("inductiveSet", "v"), call("subset", "w", "v")))), "Least inductive set; its intended semantics still requires the Cover proof.")

def recurrence(step, initial, one=False):
    init = [call("emptySet", "zero")]
    names = "zero one length graph" if one else "zero length graph"
    if one: init.append(call("successor", "one", "zero"))
    return And(mem("a", "w"), mem("b", "w"), mem("c", "w"), Ex(names, And(*init,
        call("successor", "length", "b"), call("functionGraph", "graph", "length", "w"),
        call("app", "graph", "zero", initial), call("app", "graph", "b", "c"),
        InAll("i", "b", Ex("j u v", And(call("successor", "j", "i"), call("app", "graph", "i", "u"), call("app", "graph", "j", "v"), step))))))
D("addNat", "w a b c", recurrence(call("successor", "v", "u"), "a"), "Addition by one finite recursion graph.")
D("mulNat", "w a b c", recurrence(call("addNat", "w", "u", "a", "v"), "zero"), "Multiplication; only the earlier addition macro is used.")
D("powNat", "w a b c", recurrence(call("mulNat", "w", "u", "a", "v"), "one", True), "Exponentiation, including exponent zero with value one.")
D("sequence", "s length w", And(mem("length", "w"), call("functionGraph", "s", "length", "w")), "A finite natural sequence with its length.")
D("prefix", "w s t", Ex("a b", And(call("sequence", "s", "a", "w"), call("sequence", "t", "b", "w"), call("subset", "s", "t"))), "Initial segment as inclusion of finite function graphs.")
D("properPrefix", "w s t", And(call("prefix", "w", "s", "t"), ne("s", "t")), "Strict initial segment.")
D("concatenate", "w s i u", And(mem("i", "w"), Ex("length next", And(call("sequence", "s", "length", "w"), call("successor", "next", "length"), call("sequence", "u", "next", "w"), call("subset", "s", "u"), call("app", "u", "length", "i")))), "Append the single natural i to s.")
D("lexLess", "w s t", Ex("length j a b", And(call("sequence", "s", "length", "w"), call("sequence", "t", "length", "w"), mem("j", "length"), call("app", "s", "j", "a"), call("app", "t", "j", "b"), mem("a", "b"), InAll("i", "j", All("u v", Imp(And(call("app", "s", "i", "u"), call("app", "t", "i", "v")), eq("u", "v")))))), "Strict lexicographic comparison at equal finite lengths.")
D("shortlexLess", "w s t", Ex("a b", And(call("sequence", "s", "a", "w"), call("sequence", "t", "b", "w"), Or(mem("a", "b"), And(eq("a", "b"), call("lexLess", "w", "s", "t"))))), "Length first, then lexicographic order.")
D("tree", "w T", And(Ex("s", mem("s", "T")), InAll("s", "T", Ex("length", call("sequence", "s", "length", "w"))), InAll("s", "T", All("t", Imp(call("prefix", "w", "t", "s"), mem("t", "T"))))), "A nonempty downward-closed tree of finite natural sequences.")
D("growthSequences", "w d nu zero one two", And(call("functionGraph", "d", "w", "w"), call("functionGraph", "nu", "w", "w"), call("app", "d", "zero", "one"), call("app", "nu", "zero", "one"), InAll("k", "w", Ex("next a b c e", And(call("successor", "next", "k"), call("app", "d", "k", "a"), call("app", "nu", "k", "b"), call("app", "d", "next", "c"), call("app", "nu", "next", "e"), call("mulNat", "w", "a", "b", "c"), call("powNat", "w", "two", "c", "e"))))), "d(0)=nu(0)=1; d(k+1)=d(k)*nu(k); nu(k+1)=2^d(k+1).")
D("masterTree", "w d T I", Ex("nu zero one two", And(call("emptySet", "zero"), call("successor", "one", "zero"), call("successor", "two", "one"), call("growthSequences", "w", "d", "nu", "zero", "one", "two"), call("tree", "w", "T"), call("bijective", "I", "T", "w"), mem("zero", "T"), call("app", "I", "zero", "zero"),
    All("s t k l", Imp(And(mem("s", "T"), mem("t", "T"), call("app", "I", "s", "k"), call("app", "I", "t", "l"), call("shortlexLess", "w", "s", "t")), mem("k", "l"))),
    InAll("s", "T", All("k count", Imp(And(call("app", "I", "s", "k"), call("app", "nu", "k", "count")), InAll("i", "w", All("u", Imp(call("concatenate", "w", "s", "i", "u"), Iff(mem("u", "T"), mem("i", "count")))))))))),
    "The exact canonical breadth-first master tree and index map (source definitions (2)-(3)).")
D("atLeastChildren", "w T t count", Ex("f", And(call("functionGraph", "f", "count", "w"), call("injective", "f", "count"), InAll("j", "count", Ex("i u", And(call("app", "f", "j", "i"), call("concatenate", "w", "t", "i", "u"), mem("u", "T")))))), "An injection into the immediate-child indices.")
D("condition", "w d master I T", And(call("tree", "w", "T"), call("subset", "T", "master"), InAll("s", "T", InAll("m", "w", Ex("t k a count", And(mem("t", "T"), call("properPrefix", "w", "s", "t"), call("app", "I", "t", "k"), call("app", "d", "k", "a"), call("powNat", "w", "a", "m", "count"), call("atLeastChildren", "w", "T", "t", "count")))))), "Nonempty forcing conditions, with the source growth requirement (4).")
D("forcingPoset", "P", Ex("w d master I", And(call("omega", "w"), call("masterTree", "w", "d", "master", "I"), All("T", Iff(mem("T", "P"), call("condition", "w", "d", "master", "I", "T"))))), "Exact set of the canonical Jech-Shelah conditions; order is subset.")

D("openSet", "X P", And(call("subset", "X", "P"), InAll("T", "X", InAll("S", "P", Imp(call("subset", "S", "T"), mem("S", "X"))))), "Downward open in the forcing order.")
D("denseBelow", "X T P", InAll("S", "P", Imp(call("subset", "S", "T"), InEx("R", "P", And(call("subset", "R", "S"), mem("R", "X"))))), "Dense below a condition.")
D("regularOpen", "X P", And(call("openSet", "X", "P"), InAll("T", "P", Iff(mem("T", "X"), call("denseBelow", "X", "T", "P")))), "Regular open as a fixed point of regularization.")
D("regularization", "Y X P", And(call("openSet", "X", "P"), call("subset", "Y", "P"), InAll("T", "P", Iff(mem("T", "Y"), call("denseBelow", "X", "T", "P")))), "Y is the regularization of the open X.")
D("complement", "Y X P", And(call("subset", "Y", "P"), InAll("T", "P", Iff(mem("T", "Y"), InAll("S", "P", Imp(call("subset", "S", "T"), neg(mem("S", "X"))))))), "Regular-open Boolean complement.")
D("intersection", "Z X Y", All("T", Iff(mem("T", "Z"), And(mem("T", "X"), mem("T", "Y")))), "Exact intersection.")
D("regularCarrier", "A P", All("X", Iff(mem("X", "A"), call("regularOpen", "X", "P"))), "The carrier RO(P), specified by a membership biconditional.")
D("meetGraph", "M A", All("r", Iff(mem("r", "M"), Ex("x y z u", And(mem("x", "A"), mem("y", "A"), mem("z", "A"), call("orderedPair", "u", "x", "y"), call("orderedPair", "r", "u", "z"), call("intersection", "z", "x", "y")))))), "Exact binary meet graph, without extraneous entries.")
D("complementGraph", "N A P", All("r", Iff(mem("r", "N"), Ex("x z", And(mem("x", "A"), mem("z", "A"), call("orderedPair", "r", "x", "z"), call("complement", "z", "x", "P")))))), "Exact complement graph.")
D("coordinateEvent", "w V P n m", And(call("subset", "V", "P"), InAll("T", "P", Iff(mem("T", "V"), InAll("s", "T", All("length", Imp(And(call("sequence", "s", "length", "w"), mem("n", "length")), call("app", "s", "n", "m"))))))), "The open event that every node past n has coordinate m at n.")
D("cantorPair", "w k n m", And(mem("k", "w"), mem("n", "w"), mem("m", "w"), Ex("zero one two sum next product twiceK twiceM", And(call("emptySet", "zero"), call("successor", "one", "zero"), call("successor", "two", "one"), call("addNat", "w", "n", "m", "sum"), call("successor", "next", "sum"), call("mulNat", "w", "sum", "next", "product"), call("mulNat", "w", "two", "k", "twiceK"), call("mulNat", "w", "two", "m", "twiceM"), call("addNat", "w", "product", "twiceM", "twiceK")))), "2k=(n+m)(n+m+1)+2m; all numerals are locally bound sets.")
D("coordinateSequence", "G P A", Ex("w", And(call("omega", "w"), call("functionGraph", "G", "w", "A"), InAll("k", "w", Ex("n m V g", And(mem("n", "w"), mem("m", "w"), call("cantorPair", "w", "k", "n", "m"), call("coordinateEvent", "w", "V", "P", "n", "m"), call("regularization", "g", "V", "P"), call("app", "G", "k", "g")))))), "The set-coded sequence of regularized coordinate events.")
D("jsCode", "c G", Ex("P A zero M N", And(call("forcingPoset", "P"), call("regularCarrier", "A", "P"), call("emptySet", "zero"), call("meetGraph", "M", "A"), call("complementGraph", "N", "A", "P"), call("tuple5", "c", "A", "zero", "P", "M", "N"), call("coordinateSequence", "G", "P", "A"))), "The concrete atomless JSCode_A of audit section 9. No rigid-algebra axiom.")
D("splitIndex", "c G x k r", Ex("D zero top M N w g", And(call("tuple5", "c", "D", "zero", "top", "M", "N"), call("omega", "w"), mem("k", "w"), call("app", "G", "k", "g"), call("app2", "M", "x", "g", "r"), ne("r", "zero"), ne("r", "x"))), "A coordinate whose coded meet is a nonzero proper part.")
D("firstSplit", "c G x k r", And(call("splitIndex", "c", "G", "x", "k", "r"), InAll("j", "k", neg(Ex("s", call("splitIndex", "c", "G", "x", "j", "s"))))), "Least splitting index in the coded von Neumann natural order.")

known = {}
max_depth = 0
dependencies = {}

def emit(node, params, bound=(), indent=2):
    global max_depth
    max_depth = max(max_depth, len(bound))
    pad = " " * indent
    def var(x):
        if x in bound: return f"v{bound.index(x)}"
        if x not in params: raise ValueError(f"unbound variable {x!r}")
        return x if not bound else f"(up {len(bound)} {x})"
    tag = node[0]
    if tag in {"eq", "mem"}:
        return f"(SetFormula.{tag} {var(node[1])} {var(node[2])})"
    if tag == "call":
        name, args = node[1:]
        if name not in known: raise ValueError(f"forward or unknown macro {name}")
        if len(args) != len(known[name]): raise ValueError(f"arity mismatch {name}")
        return "(" + name + " " + " ".join(map(var, args)) + ")"
    if tag in {"all", "ex"}:
        name, body = node[1:]
        if name in params or name in bound: raise ValueError(f"shadowing binder {name}")
        return f"(SetFormula.{tag} -- {name}\n{pad}  {emit(body, params, (name,)+bound, indent+2)})"
    if tag == "neg": return f"(SetFormula.neg {emit(node[1],params,bound,indent)})"
    if tag in {"imp", "iff"}:
        return f"(SetFormula.{tag}\n{pad}  {emit(node[1],params,bound,indent+2)}\n{pad}  {emit(node[2],params,bound,indent+2)})"
    if tag in {"and", "or"}:
        op = "allOf" if tag == "and" else "anyOf"
        return f"({op} [\n" + ",\n".join(pad+"  "+emit(p,params,bound,indent+2) for p in node[1]) + "] )"
    raise ValueError(tag)

def refs(node):
    if node[0] == "call": return {node[1]}
    if node[0] in {"eq", "mem"}: return set()
    if node[0] in {"all", "ex"}: return refs(node[2])
    if node[0] == "neg": return refs(node[1])
    if node[0] in {"and", "or"}: return set().union(*(refs(x) for x in node[1]))
    return refs(node[1]) | refs(node[2])

chunks = []
for name, params, body, doc in defs:
    dependencies[name] = sorted(refs(body))
    text = emit(body, params)
    chunks.append(f"/-- {doc} -/\ndef {name} {{n : Nat}} ({' '.join(params)} : Fin n) : SetFormula n :=\n  {text}\n")
    known[name] = params

header = '''import Classicism.Results.Research.MaxAtomicitySetSyntax

/-!
# Concrete finite set-formula library for the rigid selector

Source: research/2026-10-22/followup/max-atomicity-selector-audit.md, sections 3-9.
Generated by research/2026-10-22/lean-formalization/max_set_library_gen.py.
The generator checks binding, macro arities, and backward-only dependencies.
Lean checks the resulting finite indexed AST and its typing/purity proofs.
These are definitions, not claims that the described sets exist or are rigid.
No semantics, soundness, Jech-Shelah theorem, or Max contradiction is postulated.
Do not evaluate or print the fully expanded AST during routine integration.
-/

namespace Classicism.Meta.Research.MaxAtomicitySetLibrary
open MaxAtomicitySetSyntax MaxAtomicitySyntax

def allOf {n : Nat} (ps : List (SetFormula n)) : SetFormula n :=
  ps.foldr SetFormula.conj SetFormula.top

def anyOf {n : Nat} (ps : List (SetFormula n)) : SetFormula n :=
  ps.foldr SetFormula.disj SetFormula.bot

/-- Shift a free variable under k new set binders; structural metarecursion. -/
def up {n : Nat} : (k : Nat) → Fin n → Fin (n + k)
  | 0, i => i
  | k + 1, i => (up k i).succ

def v0 {n : Nat} : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
'''
vs = "".join(f"def v{i} {{n : Nat}} : Fin (n + {i+1}) := (v{i-1} (n := n)).succ\n" for i in range(1,max_depth))
footer = '''
/-- An actual finite first-order formula with exactly the two permitted free
set variables c,G. Existential or semantic adequacy is not asserted. -/
def jsFormula : SetFormula 2 := jsCode (0 : Fin 2) (1 : Fin 2)

/-- The concrete closed pure C term lambda E c G. JSCode_A(E,c,G). -/
def jsCodeTerm : Term Signature.pure []
    ((ER : Ty) ⇒ (U : Ty) ⇒ (U : Ty) ⇒ RTy.t) := quoteBinary jsFormula

theorem jsCodeTerm_closedTypes : jsCodeTerm.closedTypes = true :=
  quoteBinary_closedTypes jsFormula

theorem jsCodeTerm_pure : jsCodeTerm.pure = true := quoteBinary_pure jsFormula

end Classicism.Meta.Research.MaxAtomicitySetLibrary

#print axioms Classicism.Meta.Research.MaxAtomicitySetLibrary.jsCodeTerm_closedTypes
#print axioms Classicism.Meta.Research.MaxAtomicitySetLibrary.jsCodeTerm_pure
'''
OUT.write_text(header + vs + "\n" + "\n".join(chunks) + footer)
manifest = ROOT / "research/2026-10-22/lean-formalization/max-set-dependencies.txt"
manifest.write_text("Finite macro order; every dependency precedes its user.\n" +
    "\n".join(f"{name}: {', '.join(dependencies[name]) or '(primitive syntax only)'}" for name, *_ in defs) + "\n")
print(f"Wrote {OUT.name}: {len(defs)} finite macros; maximum binder depth {max_depth}.")
