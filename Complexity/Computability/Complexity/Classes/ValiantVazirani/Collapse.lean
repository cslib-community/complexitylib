/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.ValiantVazirani
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import Complexity.Computability.Complexity.Classes.Ladner.PolyTime
import Complexity.Computability.Complexity.Classes.Oracle.PolyTime

/-!
# If unique satisfiability is easy, then NP = RP

By the Valiant–Vazirani theorem [Valiant and Vazirani][ValiantVazirani1986], [Arora and Barak,
Section 17.4][AroraBarak09], every problem in `NP` is in `RP` relative to every language solving
`PromiseUSAT` (`Cslib.Complexity.NP_subset_RPWithPromiseOracle_PromiseUSAT`). An oracle decided
in polynomial time adds nothing to randomized polynomial time: its queries are answered by
running its decider (`Cslib.Complexity.ComputableInPolyTimeWithOracle.computableInPolyTime`),
so `RP^A = RP` for `A ∈ P` (`Cslib.Complexity.RPWithOracle_eq_RP`). Hence, if `PromiseUSAT` has a
polynomial-time solver, then `NP = RP`, for every encoding of instances
(`Cslib.Complexity.NP_eq_RP_of_PromiseUSAT_mem_PromiseP`). In particular `USAT ∈ P` implies
`NP = RP` (`Cslib.Complexity.NP_eq_RP_of_USAT_mem_P`); this form is weak, since `USAT` as a
language is `coNP`-hard.

A polynomial-time solver of a promise problem is a function on its instances; the oracle
algorithm asks about words. Under an encoding with a total decoder (`Turing.MultiTapeTM.Decoder`),
such as that of formulas, the solver composed with the decoder is an oracle language in `P` that
solves the promise problem (`Cslib.Complexity.exists_mem_P_solvedBy_of_mem_PromiseP`), and `RP`
relative to such a promise problem is `RP` (`Cslib.Complexity.RPWithPromiseOracle_eq_RP`).

## Main results

* `Cslib.Complexity.RPWithOracle_eq_RP`: `RP^A = RP` for `A ∈ P`.
* `Cslib.Complexity.exists_mem_P_solvedBy_of_mem_PromiseP`: a promise problem in `PromiseP`
  under a decodable encoding is solved by an oracle language in `P`.
* `Cslib.Complexity.RPWithPromiseOracle_eq_RP`: `RP` relative to a promise problem in
  `PromiseP`, under a decodable encoding, is `RP`.
* `Cslib.Complexity.NP_eq_RP_of_PromiseUSAT_mem_PromiseP`: if `PromiseUSAT ∈ PromiseP`, then
  `NP = RP`.
* `Cslib.Complexity.NP_eq_RP_of_USAT_mem_P`: if `USAT ∈ P`, then `NP = RP`.

## References

* [L. G. Valiant, V. V. Vazirani, *NP is as easy as detecting unique
  solutions*][ValiantVazirani1986]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α β : Type} {A : Set (List Bool)}

/-- **`RP` relative to an oracle in `P` is `RP`.** -/
theorem RPWithOracle_eq_RP (hA : A ∈ P encBits) (enc : α ↪ List Bool) :
    RPWithOracle A enc = RP enc :=
  Set.Subset.antisymm
    (fun _ ⟨p, V, hV, hL⟩ => ⟨p, V, hV.computableInPolyTime hA, hL⟩)
    (RP_subset_RPWithOracle A enc)

open Classical in
/-- **A promise problem in `PromiseP` is solved by an oracle language in `P`**, under an encoding
of its instances with a total decoder: the words whose decoding the polynomial-time solver
accepts. -/
theorem exists_mem_P_solvedBy_of_mem_PromiseP {Q : PromiseProblem β} {encQ : β ↪ List Bool}
    (D : Decoder encQ) (hQ : Q ∈ PromiseP encQ) :
    ∃ A ∈ P encBits, Q.SolvedBy fun b => decide (encQ b ∈ A) := by
  obtain ⟨f, hf, hsolve⟩ := mem_PromiseP_iff.1 hQ
  obtain ⟨_, _, hD⟩ := D.computable
  refine ⟨{w | f (D.decode w) = true}, ⟨_, hf.comp (.of_tidy hD.computableTidilyInPolyTime),
    fun _ => Iff.rfl⟩, ?_⟩
  simpa [D.decode_enc] using hsolve

/-- `RP` relative to a promise problem in `PromiseP` lies in `RP`, under an encoding of its
instances with a total decoder. -/
theorem RPWithPromiseOracle_subset_RP {Q : PromiseProblem β} {encQ : β ↪ List Bool}
    (D : Decoder encQ) (hQ : Q ∈ PromiseP encQ) (enc : α ↪ List Bool) :
    RPWithPromiseOracle Q encQ enc ⊆ RP enc :=
  let ⟨_, hA, hsolve⟩ := exists_mem_P_solvedBy_of_mem_PromiseP D hQ
  (RPWithPromiseOracle_subset_RPWithOracle hsolve enc).trans (RPWithOracle_eq_RP hA enc).subset

/-- **`RP` relative to a promise problem in `PromiseP` is `RP`**, under an encoding of its
instances with a total decoder. -/
theorem RPWithPromiseOracle_eq_RP {Q : PromiseProblem β} {encQ : β ↪ List Bool}
    (D : Decoder encQ) (hQ : Q ∈ PromiseP encQ) (enc : α ↪ List Bool) :
    RPWithPromiseOracle Q encQ enc = RP enc :=
  Set.Subset.antisymm (RPWithPromiseOracle_subset_RP D hQ enc)
    (RP_subset_RPWithPromiseOracle Q encQ enc)

/-- **Valiant–Vazirani: if `PromiseUSAT` has a polynomial-time solver, then `NP = RP`**, for every
encoding of instances. -/
theorem NP_eq_RP_of_PromiseUSAT_mem_PromiseP (h : PromiseUSAT ∈ PromiseP encCNF)
    (enc : α ↪ List Bool) : NP enc = RP enc :=
  Set.Subset.antisymm ((NP_subset_RPWithPromiseOracle_PromiseUSAT enc).trans
    (RPWithPromiseOracle_subset_RP cnfDecoder h enc)) RP_subset_NP

/-- **Valiant–Vazirani: if `USAT ∈ P`, then `NP = RP`**, for every encoding of instances. This
form is weak: `USAT` as a language is `coNP`-hard. -/
theorem NP_eq_RP_of_USAT_mem_P (h : USAT ∈ P encCNF) (enc : α ↪ List Bool) :
    NP enc = RP enc :=
  NP_eq_RP_of_PromiseUSAT_mem_PromiseP ⟨USAT, h, subset_rfl, disjoint_USAT_UNSAT⟩ enc

end Cslib.Complexity
