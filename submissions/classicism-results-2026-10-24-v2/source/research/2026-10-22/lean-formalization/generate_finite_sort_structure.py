#!/usr/bin/env python3
"""Emit fixed finite C proof candidates; never invokes Lean or changes records.

The external integer controls source generation, not a natural-number argument in
the C theorem. Certification still requires the generated certificate module.
Source: positive-effective.md sections 23.1-23.3 (original, unpaginated).
"""
from __future__ import annotations

import argparse
from pathlib import Path


def cover(i: int, x: str = "z") -> str:
    return "False" if i == 0 else f"({x} = a{i - 1} ∨ {cover(i - 1, x)})"


def declarations(k: int) -> str:
    names = ", ".join(f"a{i}" for i in range(k))
    witnesses = " ".join(f"a{i}" for i in range(k))
    lines = [
        f"/-- A {k}-entry exhaustive cover; entries may repeat. -/",
        f"def AtMost{k} (σ : Type) [Ty σ] : Prop :=",
        f"  ∃ {witnesses} : σ, ∀ z : σ, {cover(k)}",
        "",
        f"theorem atMost{k}_atomicity {{τ : Type}} [Rel τ] [Order τ] [Pointwise τ]",
        f"    (h : AtMost{k} τ) : Atomicity τ := by",
        f"  obtain ⟨{names}, hall⟩ := h",
        "  intro p",
        "  rcases em (p ≤ ¬ p) with hp | hp",
        "  · exact Or.inl hp",
        "  · have h0 : ∀ z : τ, False → ¬ z ≤ ¬ z → z ≤ p → p ≤ z :=",
        "      fun _ h => h.elim",
    ]
    for i in range(k):
        q = "p" if i == 0 else f"q{i}"
        hn = "hp" if i == 0 else f"hn{i}"
        lines += [
            f"    obtain ⟨q{i + 1}, hn{i + 1}, hle{i + 1}, h{i + 1}⟩ :=",
            f"      minimum_step (fun z : τ => {cover(i)}) {q} a{i} {hn} h{i}",
            f"    have hp{i + 1} : q{i + 1} ≤ p := " +
            (f"hle{i + 1}" if i == 0 else
             f"le_trans_rel q{i + 1} q{i} p hle{i + 1} hp{i}"),
        ]
    lines += [
        f"    exact Or.inr ⟨q{k}, atom_of_minimal q{k} hn{k}",
        f"      (fun z => h{k} z (hall z)), hp{k}⟩",
        "",
        f"theorem atMost{k}_booleanCompleteness {{τ : Type}} [Rel τ] [Order τ] [Pointwise τ]",
        f"    (h : AtMost{k} τ) : BooleanCompleteness τ := by",
        f"  obtain ⟨{names}, hall⟩ := h",
        "  intro X",
        "  have h0 := glb_empty X",
    ]
    for i in range(k):
        y = "(⊤ : τ)" if i == 0 else f"y{i}"
        lines += [f"  obtain ⟨y{i + 1}, h{i + 1}⟩ :=",
                  f"    glb_step X (fun z : τ => {cover(i)}) a{i} {y} h{i}"]
    lines += [
        f"  exact ⟨y{k}, glb_cover X (fun z : τ => {cover(k)}) y{k} hall h{k}⟩",
        "",
        f"theorem atMost{k}_actuality (h : AtMost{k} Prop) : Actuality := by",
        f"  obtain ⟨{names}, hall⟩ := h",
        "  have h0 : ∀ p : Prop, False → p → (True : Prop) ≤ p := fun _ h => h.elim",
    ]
    for i in range(k):
        w = "True" if i == 0 else f"w{i}"
        hw = "True.intro" if i == 0 else f"hw{i}"
        lines += [f"  obtain ⟨w{i + 1}, hw{i + 1}, h{i + 1}⟩ :=",
                  f"    truth_step (fun z : Prop => {cover(i)}) {w} a{i} {hw} h{i}"]
    lines += [
        f"  exact ⟨w{k}, hw{k}, fun p => h{k} p (hall p)⟩",
        "",
        f"theorem atMost{k}_relationalChoice {{σ τ : Type}} [Ty σ] [Ty τ]",
        f"    (h : AtMost{k} σ) : RelationalChoice σ τ := by",
        f"  obtain ⟨{names}, hall⟩ := h",
        "  intro U hu",
        "  have h0 := partial_empty U",
    ]
    for i in range(k):
        s = "(fun _ _ => False)" if i == 0 else f"S{i}"
        lines += [f"  obtain ⟨S{i + 1}, h{i + 1}⟩ :=",
                  f"    partial_step (fun z : σ => {cover(i)}) U {s} a{i} hu h{i}"]
    lines += [
        f"  exact ⟨S{k}, partial_cover (fun z : σ => {cover(k)}) U S{k} hall h{k}⟩",
        "",
    ]
    return "\n".join(lines)


def render(bounds: list[int]) -> str:
    return "\n".join([
        "import Classicism.Results.Research.FiniteSortStructure",
        "",
        "/-! Fixed finite C proof candidates. Generated externally; no internal Nat induction.",
        "Source: positive-effective.md §§23.1–23.3 (original research, unpaginated).",
        "The accompanying certificate driver must pass before any C certification claim. -/",
        "",
        "namespace Classicism.Research.FiniteSortStructure",
        "open Classicism.Paper Classicism.P",
        "",
        *(declarations(k) for k in bounds),
        "end Classicism.Research.FiniteSortStructure",
        "",
    ])


def certificates(bounds: list[int], module: str) -> str:
    names = [f"Classicism.Research.FiniteSortStructure.atMost{k}_{suffix}"
             for k in bounds for suffix in
             ("atomicity", "booleanCompleteness", "actuality", "relationalChoice")]
    return "\n".join([
        f"import {module}",
        "import Classicism.Tools.Check",
        "import Classicism.Tools.TypeSystem",
        "import Classicism.Tools.Schema",
        "",
        "#classicism_audit Classicism.Results.Research.FiniteSortStructure",
        "#classicism_types_audit Classicism.Results.Research.FiniteSortStructure",
        f"#classicism_audit {module}",
        f"#classicism_types_audit {module}",
        "",
        "#classicism_derive " + "\n  ".join(names),
        "",
        *(f"#print axioms {n}.derivable" for n in names),
        "",
    ])


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("bounds", type=int, nargs="+")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--certificates", type=Path, required=True)
    parser.add_argument("--module", required=True)
    args = parser.parse_args()
    if any(k < 1 for k in args.bounds) or len(set(args.bounds)) != len(args.bounds):
        parser.error("bounds must be distinct positive external integers")
    for path in (args.output, args.certificates):
        if path.exists():
            parser.error(f"refusing to overwrite {path}; use a fresh output path")
    args.output.write_text(render(args.bounds))
    args.certificates.write_text(certificates(args.bounds, args.module))


if __name__ == "__main__":
    main()
