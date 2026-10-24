#!/usr/bin/env python3
"""Emit complete shallow-C proofs for an arbitrary finite sorted signature.

This is a proof-producing schema implementation, not a trusted proof oracle.
Every emitted instance must pass Lean, the Classicism gate/type audits, and
object-language translation. No compiler is invoked by this program.

Signature JSON: {"namespace": "Classicism.Research.Example", "sorts": 3,
 "operations": [{"inputs": [], "output": 0}, ...]}.
Nullary operations include all generators; input lists may have any finite
length and repeated sorts. The zero-sort/zero-operation case is vacuous.
Direct source: notes/c5-generated-algebra-transfer-20261022.md, sections 1–5,
unpaginated original research (misc).
"""

import argparse
import hashlib
import json
import re
from pathlib import Path


def app(f, *args):
    return f if not args else f"({f} {' '.join(args)})"


def chain(items, end):
    return " → ".join([*items, end])


def quantify(names_types, body):
    if not names_types:
        return body
    return "∀ " + " ".join(f"({n} : {t})" for n, t in names_types) + ", " + body


def validate(spec):
    if set(spec) != {"namespace", "sorts", "operations"}:
        raise ValueError("Expected exactly namespace, sorts and operations")
    if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*(\.[A-Za-z][A-Za-z0-9_]*)+", spec["namespace"]):
        raise ValueError("Invalid Lean namespace")
    n = spec["sorts"]
    if type(n) is not int or n < 0:
        raise ValueError("sorts must be a nonnegative integer")
    if not isinstance(spec["operations"], list):
        raise ValueError("operations must be a finite list")
    for op in spec["operations"]:
        if not isinstance(op, dict) or set(op) != {"inputs", "output"}:
            raise ValueError("Each operation has exactly inputs and output")
        if not isinstance(op["inputs"], list):
            raise ValueError("inputs must be a finite list")
        if any(type(i) is not int or not 0 <= i < n for i in [*op["inputs"], op["output"]]):
            raise ValueError("Operation sort index outside signature")


def generate(spec):
    validate(spec)
    n, ops, ns = spec["sorts"], spec["operations"], spec["namespace"]
    fs, gs = [f"f{k}" for k in range(len(ops))], [f"g{k}" for k in range(len(ops))]
    hs, qs, ls, vs = ([f"{p}{i}" for i in range(n)] for p in ("H", "q", "l", "V"))
    cs, ps = [f"c{k}" for k in range(len(ops))], [f"p{i}" for i in range(n)]
    hcs, hqs, hls = ([f"{p}{k}" for k in range(len(ops))] for p in ("hc", "hq", "hl"))
    typ = lambda p, i: f"{p}{i}"
    tyargs = lambda p: [f"({p}{i} := {p}{i})" for i in range(n)]
    both = [*tyargs("μ"), *tyargs("ν")]
    op_type = lambda p, op: chain([typ(p, i) for i in op["inputs"]], typ(p, op["output"]))
    src = [(f, op_type("μ", op)) for f, op in zip(fs, ops)]
    tgt = [(H, f"ν{i} → Prop") for i, H in enumerate(hs)] + [(g, op_type("ν", op)) for g, op in zip(gs, ops)]
    qparams = [(q, f"μ{i} → ν{i}") for i, q in enumerate(qs)]
    lparams = [(l, f"ν{i} → μ{i}") for i, l in enumerate(ls)]
    gcall = lambda i, x=None: app(f"G{i}", *tyargs("μ"), *fs, *([] if x is None else [x]))
    kcall = lambda i, x=None: app(f"K{i}", *tyargs("ν"), *hs, *gs, *([] if x is None else [x]))
    scall = lambda name, *args: app(name, *tyargs("μ"), *fs, *args)
    tcall = lambda name, *args: app(name, *tyargs("ν"), *hs, *gs, *args)
    common = [*fs, *hs, *gs, *qs]
    fullcall = lambda name, *args: app(name, *both, *common, *args)
    hnd = ("hnd", "□ (∀ p q : Prop, p ≠ q → □ (p ≠ q))")
    hp = [(f"hp{i}", f"Persistent H{i}") for i in range(n)]

    def variables(op, p="x", t="μ"):
        return [(f"{p}{r}", typ(t, i)) for r, i in enumerate(op["inputs"])]

    def source_clause(k, predicates):
        op = ops[k]
        xs = variables(op)
        names = [x for x, _ in xs]
        return quantify(xs, chain([app(predicates[i], x) for i, x in zip(op["inputs"], names)],
                                  app(predicates[op["output"]], app(fs[k], *names))))

    def target_clause(k, predicates, guard=True):
        op = ops[k]
        ys = variables(op, "y", "ν")
        names = [y for y, _ in ys]
        prem = [app(hs[i], y) for i, y in zip(op["inputs"], names)] if guard else []
        prem += [app(predicates[i], y) for i, y in zip(op["inputs"], names)]
        return quantify(ys, chain(prem, app(predicates[op["output"]], app(gs[k], *names))))

    hcparams, hqparams, hlparams = [], [], []
    for k, op in enumerate(ops):
        ys, xs = variables(op, "y", "ν"), variables(op)
        yy, xx = [x for x, _ in ys], [x for x, _ in xs]
        qx = [app(qs[i], x) for i, x in zip(op["inputs"], xx)]
        ly = [app(ls[i], y) for i, y in zip(op["inputs"], yy)]
        j = op["output"]
        hcparams.append((hcs[k], quantify(ys, chain([app(hs[i], y) for i, y in zip(op["inputs"], yy)], app(hs[j], app(gs[k], *yy))))))
        hqparams.append((hqs[k], quantify(xs, chain([app(hs[i], q) for i, q in zip(op["inputs"], qx)], f"{app(qs[j], app(fs[k], *xx))} = {app(gs[k], *qx)}"))))
        hlparams.append((hls[k], quantify(ys, chain([app(hs[i], y) for i, y in zip(op["inputs"], yy)], f"{app(ls[j], app(gs[k], *yy))} = {app(fs[k], *ly)}"))))

    lines = ["import Classicism.Results.Research.GeneratedAlgebraTransfer", "", "/-!",
        "# Finite-sorted generated-algebra schema instance", "",
        "Generated by generate_generated_algebra.py from a finite typed signature.",
        "Direct source: research/2026-10-22/notes/c5-generated-algebra-transfer-20261022.md,",
        "§§1–5 (unpaginated original research, misc). Every proof must be checked and",
        "translated into C; generation alone is not certification. The hypotheses are",
        "the source theorem's given maps and guarded commutation laws, not assumed",
        "generation, persistence, image rigidity, surjectivity or inverse laws.", "-/", "",
        f"namespace {ns}", "open Classicism.Paper", ""]
    for i in range(n):
        lines.append(f"variable {{μ{i} ν{i} : Type}} [Rel μ{i}] [Rel ν{i}]")
    lines.append("")

    def decl(kind, name, params, conclusion, proof):
        lines.append(f"{kind} {name}")
        lines.extend(f"    ({x} : {t})" for x, t in params)
        lines.append(f"    : {conclusion} := {proof[0]}")
        lines.extend(proof[1:])
        lines.append("")

    for i in range(n):
        body = quantify([(v, f"μ{j} → Prop") for j, v in enumerate(vs)],
            chain([f"({source_clause(k, vs)})" for k in range(len(ops))], app(vs[i], "x")))
        decl("def", f"G{i}", src + [("x", f"μ{i}")], "Prop", [body])
    for i in range(n):
        body = quantify([(v, f"ν{j} → Prop") for j, v in enumerate(vs)],
            chain([f"(Rigid {v} ∧ {v} ≤ {hs[j]})" for j, v in enumerate(vs)] +
                  [f"({target_clause(k, vs)})" for k in range(len(ops))], app(vs[i], "y")))
        decl("def", f"K{i}", tgt + [("y", f"ν{i}")], "Prop", [f"H{i} y ∧ {body}"])

    for k, op in enumerate(ops):
        xs = variables(op); xx = [x for x, _ in xs]
        hh = [f"h{r}" for r in range(len(xx))]
        conclusion = chain([gcall(i, x) for i, x in zip(op["inputs"], xx)], gcall(op["output"], app(fs[k], *xx)))
        proof = ["by"]
        if hh: proof.append("  intro " + " ".join(hh))
        proof.append("  intro " + " ".join([*vs, *cs]))
        proof.append("  exact " + app(cs[k], *xx, *[app(h, *vs, *cs) for h in hh]))
        decl("theorem", f"source_op{k}", src + xs, conclusion, proof)
    for i in range(n):
        boxpred = [f"(fun z : μ{j} => □ {gcall(j, 'z')})" for j in range(n)]
        proof = ["by", "  intro x hx", "  " + ("apply " if ops else "exact ") + app("hx", *boxpred)]
        for k, op in enumerate(ops):
            xx = [x for x, _ in variables(op)]; hh = [f"h{r}" for r in range(len(xx))]
            term = f"(nec% {scall(f'source_op{k}', *xx)})"
            for h in hh: term = app("modal_K", "_", "_", term, h)
            if xx: proof += ["  · intro " + " ".join([*xx, *hh]), "    exact " + term]
            else: proof += ["  · exact " + term]
        decl("theorem", f"point_persistent{i}", src, f"∀ x, {gcall(i, 'x')} → □ {gcall(i, 'x')}", proof)
        decl("theorem", f"persistent{i}", src, f"Persistent {gcall(i)}", [f"nec% {scall(f'point_persistent{i}')}"])
        pers = scall(f"persistent{i}")
        decl("theorem", f"rigid{i}", src + [hnd], f"Rigid {gcall(i)}",
             [f"⟨{pers}, Proofs.inextensible_of_persistent_c5 hnd _ {pers}⟩"])

    for k, op in enumerate(ops):
        ys = variables(op, "y", "ν"); yy = [y for y, _ in ys]
        hh = [f"h{r}" for r in range(len(yy))]
        params = tgt + [hcparams[k]] + ys + [(h, kcall(i, y)) for h, i, y in zip(hh, op["inputs"], yy)]
        proof = ["by", "  refine ⟨" + app(hcs[k], *yy, *[h+".1" for h in hh]) + ", ?_⟩",
                 "  intro " + " ".join([*vs, *ps, *cs]),
                 "  exact " + app(cs[k], *yy, *[h+".1" for h in hh], *[app(h+".2", *vs, *ps, *cs) for h in hh])]
        decl("theorem", f"target_op{k}", params, kcall(op["output"], app(gs[k], *yy)), proof)

    mapparams = src + tgt + qparams
    for i in range(n):
        proof = ["by", "  " + ("apply " if ops else "exact ") + app("hx", *[f"(fun z : μ{j} => {kcall(j, app(qs[j], 'z'))})" for j in range(n)])]
        for k, op in enumerate(ops):
            xx = [x for x, _ in variables(op)]; hh = [f"h{r}" for r in range(len(xx))]
            qq = [app(qs[j], x) for j, x in zip(op["inputs"], xx)]
            term = tcall(f"target_op{k}", hcs[k], *qq, *hh)
            eq = app(hqs[k], *xx, *[h+".1" for h in hh])
            if xx: proof += ["  · intro " + " ".join([*xx, *hh]), f"    exact {eq}.symm ▸ {term}"]
            else: proof += [f"  · exact {eq}.symm ▸ {term}"]
        decl("theorem", f"forward{i}", mapparams + hcparams + hqparams + [("x", f"μ{i}"), ("hx", gcall(i, "x"))], kcall(i, app(qs[i], "x")), proof)

    images = [app("GeneratedAlgebra.Image", hs[i], gcall(i), qs[i]) for i in range(n)]
    image_adm = ["⟨" + app("GeneratedAlgebra.image_rigid", "hnd", hs[i], gcall(i), qs[i], f"hp{i}", scall(f"persistent{i}")) + ", " +
                 app("GeneratedAlgebra.image_support", hs[i], gcall(i), qs[i]) + "⟩" for i in range(n)]
    for i in range(n):
        proof = ["by", f"  have himage : {app(images[i], 'y')} := by",
                 "    " + ("apply " if ops else "exact ") + app("hy.2", *images, *image_adm)]
        for k, op in enumerate(ops):
            yy = [y for y, _ in variables(op, "y", "ν")]
            xx = [x for x, _ in variables(op)]
            hh, hi = [f"h{r}" for r in range(len(yy))], [f"i{r}" for r in range(len(yy))]
            gg, ee = [f"a{r}" for r in range(len(yy))], [f"e{r}" for r in range(len(yy))]
            qq = [app(qs[j], x) for j, x in zip(op["inputs"], xx)]
            if yy:
                proof.append("    · intro " + " ".join([*yy, *hh, *hi]))
                for x, a, e, h in zip(xx, gg, ee, hi): proof.append(f"      obtain ⟨{x}, {a}, {e}⟩ := {h}.2")
                proof += [f"      have he : {app(gs[k], *qq)} = {app(gs[k], *yy)} := by", "        rw [" + ", ".join(ee) + "]"]
                eq = app(hqs[k], *xx, *[f"({e}.symm ▸ {h})" for e, h in zip(ee, hh)]) + ".trans he"
                proof.append("      exact ⟨" + ", ".join([app(hcs[k], *yy, *hh), app(fs[k], *xx), scall(f"source_op{k}", *xx, *gg), eq]) + "⟩")
            else:
                proof.append("    · exact ⟨" + ", ".join([hcs[k], fs[k], scall(f"source_op{k}"), hqs[k]]) + "⟩")
        proof.append("  exact himage.2")
        decl("theorem", f"onto{i}", mapparams + [hnd] + hp + hcparams + hqparams + [("y", f"ν{i}"), ("hy", kcall(i, "y"))], f"∃ x, {gcall(i, 'x')} ∧ {app(qs[i], 'x')} = y", proof)

    for i in range(n):
        predicates = [f"(fun z : μ{j} => H{j} {app(qs[j], 'z')} ∧ {app(ls[j], app(qs[j], 'z'))} = z)" for j in range(n)]
        proof = ["by", "  " + ("apply " if ops else "exact ") + app("hx", *predicates)]
        for k, op in enumerate(ops):
            xx = [x for x, _ in variables(op)]; hh = [f"h{r}" for r in range(len(xx))]
            qq = [app(qs[j], x) for j, x in zip(op["inputs"], xx)]
            lq = [app(ls[j], q) for j, q in zip(op["inputs"], qq)]
            eq = app(hqs[k], *xx, *[h+".1" for h in hh])
            rev = app(hls[k], *qq, *[h+".1" for h in hh])
            support = f"{eq}.symm ▸ {app(hcs[k], *qq, *[h+'.1' for h in hh])}"
            if xx:
                proof += ["  · intro " + " ".join([*xx, *hh]),
                          f"    have he : {app(fs[k], *lq)} = {app(fs[k], *xx)} := by",
                          "      rw [" + ", ".join(h+".2" for h in hh) + "]",
                          f"    exact ⟨{support}, (congrArg {ls[op['output']]} {eq}).trans ({rev}.trans he)⟩"]
            else:
                proof.append(f"  · exact ⟨{support}, (congrArg {ls[op['output']]} {eq}).trans {rev}⟩")
        invparams = mapparams + lparams + hcparams + hqparams + hlparams
        invargs = [*ls, *hcs, *hqs, *hls]
        decl("theorem", f"left_inverse{i}", invparams + [("x", f"μ{i}"), ("hx", gcall(i, "x"))],
             f"H{i} {app(qs[i], 'x')} ∧ {app(ls[i], app(qs[i], 'x'))} = x", proof)
        li = lambda x, h: fullcall(f"left_inverse{i}", *invargs, x, h)
        decl("theorem", f"injective{i}", invparams + [("x", f"μ{i}"), ("z", f"μ{i}"), ("hx", gcall(i, "x")), ("hz", gcall(i, "z")), ("he", f"{app(qs[i], 'x')} = {app(qs[i], 'z')}")], "x = z",
            [app("GeneratedAlgebra.injective_of_left_inverse", gcall(i), qs[i], ls[i], f"(fun a ha => {li('a', 'ha')}.2)", "x", "z", "hx", "hz", "he")])
        ontoargs = ["hnd", *[f"hp{j}" for j in range(n)], *hcs, *hqs]
        decl("theorem", f"right_inverse{i}", invparams + [hnd] + hp + [("y", f"ν{i}"), ("hy", kcall(i, "y"))],
            f"{gcall(i, app(ls[i], 'y'))} ∧ {app(qs[i], app(ls[i], 'y'))} = y",
            [app("GeneratedAlgebra.right_inverse_on_target", gcall(i), kcall(i), qs[i], ls[i],
                f"(fun a ha => {fullcall(f'onto{i}', *ontoargs, 'a', 'ha')})",
                f"(fun a ha => {li('a', 'ha')}.2)", "y", "hy")])

    lines += [f"end {ns}", ""]
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("signature", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--module", required=True, help="Lean module path for certificate imports")
    parser.add_argument("--certificates", type=Path, required=True)
    args = parser.parse_args()
    for path in (args.output, args.certificates):
        if path.exists():
            parser.error(f"Refusing to overwrite existing (possibly frozen) file: {path}")
    if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*(\.[A-Za-z][A-Za-z0-9_]*)+", args.module):
        parser.error("Invalid module name")
    spec = json.loads(args.signature.read_text())
    source = generate(spec)
    cert = f"""import {args.module}
import Classicism.Results.Research.GeneratedAlgebraTransferCertificates
import Classicism.Tools.Check
import Classicism.Tools.TypeSystem
import Classicism.Tools.Translate

#classicism_audit {args.module}
#classicism_types_audit {args.module}
#classicism_derive_audit {args.module}
"""
    for i in range(spec["sorts"]):
        for name in (f"onto{i}", f"left_inverse{i}", f"right_inverse{i}"):
            cert += f"\n#print axioms {spec['namespace']}.{name}.derivable"
    args.output.write_text(source)
    args.certificates.write_text(cert + "\n")
    print(json.dumps({"source": str(args.output), "sha256": hashlib.sha256(source.encode()).hexdigest(),
                      "sorts": spec["sorts"], "operations": len(spec["operations"])}))


if __name__ == "__main__":
    main()
