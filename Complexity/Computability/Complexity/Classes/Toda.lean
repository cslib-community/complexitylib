/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Oracle.Counting
public import Complexity.Computability.Complexity.Classes.Toda.Hierarchy
import Complexity.Computability.Complexity.Classes.Toda.Counting
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Toda's theorem

Toda's theorem [Toda][Toda1991], [Arora and Barak, Section 17.4][AroraBarak09]: the polynomial
hierarchy lies in `BP·⊕P` (`Cslib.Complexity.PH_subset_BPOp_ParityP`), which lies in polynomial
time with an oracle for a function in `#P`
(`Cslib.Complexity.BPOp_ParityP_subset_PWithSharpPOracle`), so `PH ⊆ P^#P`
(`Cslib.Complexity.PH_subset_PWithSharpPOracle`), for the class `P^#P` of
`Cslib.Complexity.PWithSharpPOracle`: one polynomial-time oracle program, correct against every
oracle language answering the bits of a function in `#P`.

## One bit of a `#P` value

For a problem in `BP·⊕P`, decided with bounded error by the parity of the number `f r` of
witnesses of a verifier on random strings `r` of length `R`,
`Complexity.Computability.Complexity.Classes.Toda.Counting` gives a function in `#P` on the same
instances whose bit `R + 1` says whether more than half of the random strings have `f r` odd
(`Cslib.Complexity.exists_SharpP_testBit_of_mem_BPOp_ParityP`). The program deciding the problem
in `P^#P` (`Cslib.Complexity.mem_PWithSharpPOracle_of_testBit`) asks for this bit with a single
query, as in Toda's `PH ⊆ P^#P[1]`; the class `PWithSharpPOracle` itself does not count queries.

## Main results

* `Cslib.Complexity.exists_SharpP_testBit_of_mem_BPOp_ParityP`: a problem in `BP·⊕P` is decided
  by a bit at a polynomial position of a function in `#P`.
* `Cslib.Complexity.BPOp_ParityP_subset_PWithSharpPOracle`: **`BP·⊕P ⊆ P^#P`**.
* `Cslib.Complexity.PH_subset_PWithSharpPOracle`: **Toda's theorem, `PH ⊆ P^#P`**.

## References

* [S. Toda, *PP is as hard as the polynomial-time hierarchy*][Toda1991]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Finset Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-! ### `BP·⊕P ⊆ P^#P` -/

open Toda Classical in
/-- **A problem in `BP·⊕P` is one bit of a `#P` value**: for a problem decided with bounded error,
using random strings of length `R = p (enc a).length`, by the parity of a verifier's number of
witnesses, some function in `#P` has bit `R + 1` set exactly at the members of the problem. -/
theorem exists_SharpP_testBit_of_mem_BPOp_ParityP {L : Set α}
    (hL : L ∈ BPOp enc (ParityP (encPair enc encBits))) :
    ∃ f ∈ SharpP enc, ∃ p : Polynomial ℕ, ∀ a, a ∈ L ↔ (f a).testBit (p.eval (enc a).length) := by
  obtain ⟨ρ, L', hL'P, hdec⟩ := hL
  obtain ⟨ζ, V, hV, hL'⟩ := mem_ParityP.1 hL'P
  -- the witnesses of a pair of an instance and a random string have length `Zp`
  set Zp : Polynomial ℕ := ζ.comp (2 * Polynomial.X + 1 + ρ) with hZp
  set pF : Polynomial ℕ := (ρ + 1) + ((ρ + 1) + (ρ + (ρ + 1) * Zp)) + 1 + 1 with hpF
  have hV' := hV.tidy
  refine ⟨fun a => acceptCount (fun x => sharpTest (fun r z => V ((x.1, r), z))
      (ρ.eval (enc x.1).length) (Zp.eval (enc x.1).length) x.2) a (pF.eval (enc a).length),
    ⟨pF, _, .of_tidy (by fun_prop), fun _ => rfl⟩, ρ + 1, fun a => ?_⟩
  have hpFn : pF.eval (enc a).length = (ρ.eval (enc a).length + 1) +
      ((ρ.eval (enc a).length + 1) + (ρ.eval (enc a).length +
        (ρ.eval (enc a).length + 1) * Zp.eval (enc a).length)) + 1 + 1 := by
    simp only [hpF, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one]
  have hZlen (r : List Bool) (hr : r.length = ρ.eval (enc a).length) :
      ζ.eval (encPair enc encBits (a, r)).length = Zp.eval (enc a).length := by
    rw [length_encPair, hZp, Polynomial.eval_comp]
    simp [hr]
  obtain ⟨hyes, hno⟩ := hdec a
  simp only [decide_eq_true_eq, decide_eq_false_iff_not, hL',
    hZlen _ List.length_ofFn] at hyes hno
  simp only
  rw [acceptCount_congr (W := fun x => sharpTest (fun r z => V ((a, r), z)) (ρ.eval (enc a).length)
    (Zp.eval (enc a).length) x.2) (fun w => rfl), hpFn, Polynomial.eval_add, Polynomial.eval_one]
  generalize ρ.eval (enc a).length = R at hyes hno ⊢
  generalize Zp.eval (enc a).length = Z at hyes hno ⊢
  unfold acceptCount
  rw [testBit_card_filter_sharpTest, decide_eq_true_iff]
  -- bounded error decides the majority
  have hsplit := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin R → Bool)))
    (fun r => Odd (acceptCount V (a, List.ofFn r) Z))
  simp only [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hsplit
  have hpos : 1 ≤ 2 ^ R := Nat.one_le_two_pow
  change a ∈ L ↔ 2 ^ R < 2 * (univ.filter fun r : Fin R → Bool =>
    Odd (acceptCount V (a, List.ofFn r) Z)).card
  constructor
  · intro ha
    have := hyes ha
    omega
  · intro hlt
    by_contra ha
    have := hno ha
    omega

/-- **`BP·⊕P ⊆ P^#P`**: a problem decided with bounded error by a problem in `⊕P` about pairs of
an instance and a random string is in `P^#P`, decided by a program asking for one bit of a
function in `#P`. -/
theorem BPOp_ParityP_subset_PWithSharpPOracle :
    BPOp enc (ParityP (encPair enc encBits)) ⊆ PWithSharpPOracle enc := fun _ hL =>
  let ⟨_, hf, _, h⟩ := exists_SharpP_testBit_of_mem_BPOp_ParityP hL
  mem_PWithSharpPOracle_of_testBit hf h

/-- **Toda's theorem: `PH ⊆ P^#P`.** Every problem in the polynomial hierarchy is decided by a
polynomial-time oracle program, asking for one bit of a function in `#P`, against every oracle
language answering the bits of that function. -/
theorem PH_subset_PWithSharpPOracle : PH enc ⊆ PWithSharpPOracle enc :=
  PH_subset_BPOp_ParityP.trans BPOp_ParityP_subset_PWithSharpPOracle

end Cslib.Complexity
