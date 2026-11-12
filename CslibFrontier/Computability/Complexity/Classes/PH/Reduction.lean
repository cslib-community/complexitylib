/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.PH.Collapse
public import CslibFrontier.Computability.Complexity.Reduction
import CslibFrontier.Computability.Complexity.Classes.PH.Projection
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Foundations.Data.List.TakeQuantifiers

/-!
# Reduction and bounded-quantifier closure of the polynomial hierarchy

Each level `Σₖ` and `Πₖ` of the polynomial hierarchy, and `PH` itself, is closed downward under
polynomial-time many-one reductions (`Cslib.Complexity.PolyTimeReducible.mem_SigmaP`,
`Cslib.Complexity.PolyTimeReducible.mem_PiP`, `Cslib.Complexity.PolyTimeReducible.mem_PH`). A
reduction `f` maps an instance `a` to `f a`, whose encoded length is bounded by a polynomial `q` in
`|enc a|`; the pull-back verifier quantifies over certificate blocks for length `q |enc a|` and cuts
each block to the length expected for `|encB (f a)|` (`Cslib.Complexity.truncateBlocks`).

Combining reduction closure with `Cslib.Complexity.mem_SigmaP_of_exists` closes `Σₖ` (`k ≥ 1`)
under existential quantification over words of any unary polynomial-time length `N a`
(`Cslib.Complexity.mem_SigmaP_of_exists_length`), and by quantifier duality closes `Πₖ` (`k ≥ 1`)
under universal quantification (`Cslib.Complexity.mem_PiP_of_forall_length`).

## Main results

* `Cslib.Complexity.PolyTimeReducible.mem_SigmaP`: `Σₖ` is closed under polynomial-time reductions.
* `Cslib.Complexity.PolyTimeReducible.mem_PiP`: `Πₖ` is closed under polynomial-time reductions.
* `Cslib.Complexity.PolyTimeReducible.mem_PH`: `PH` is closed under polynomial-time reductions.
* `Cslib.Complexity.mem_SigmaP_of_exists_length`: `Σₖ` (`k ≥ 1`) is closed under existential
  quantification of computed unary polynomial-time length.
* `Cslib.Complexity.mem_PiP_of_forall_length`: `Πₖ` (`k ≥ 1`) is closed under universal
  quantification of computed unary polynomial-time length.
* `Cslib.Complexity.mem_SigmaP_of_exists_append`, `Cslib.Complexity.mem_PiP_of_forall_append`: the
  same quantifiers on pairs `(a, s)`, extending the word `s` in place, so that nested quantifier
  blocks stay on one pair type.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [L. Stockmeyer, *The polynomial-time hierarchy*][Stockmeyer1976]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime

variable {α β : Type} {enc : α ↪ List Bool} {encB : β ↪ List Bool} {k : ℕ} {A : Set α} {B : Set β}

/-- **`Σₖ` is closed under polynomial-time reductions.** The verifier for `A` quantifies over
certificate blocks of length `p (q |enc a|)`, for a polynomial upper bound `q` on `|encB (f a)|`,
and cuts each block to `p |encB (f a)|` before running the verifier of `B`. -/
theorem PolyTimeReducible.mem_SigmaP (h : PolyTimeReducible enc encB A B) (hB : B ∈ SigmaP k encB) :
    A ∈ SigmaP k enc := by
  obtain ⟨f, hf, hAB⟩ := h
  obtain ⟨ps, V, hps, hV, hBV⟩ := hB
  obtain ⟨q, hq⟩ := ((encoding_length encB).comp hf).polyBounded.exists_polynomial
  refine ⟨ps.map (·.comp q),
    fun x => V (f x.1, truncateBlocks ps (encB (f x.1)).length (q.eval (enc x.1).length) x.2),
    by simp [hps], ?_, fun a => ?_⟩
  · have hfst : ComputableInPolyTime (fun x : α × List Bool => f x.1) (encPair enc encBits) encB :=
      hf.comp (fst enc encBits)
    exact hV.comp (hfst.prod (computableInPolyTime_truncateBlocks ps
      ((encoding_length encB).comp hfst)
      ((unary_eval q).comp ((encoding_length enc).comp (fst enc encBits)))
      (snd enc encBits)))
  · rw [hAB a, hBV (f a)]
    simp only [List.map_map, Function.comp_def, Polynomial.eval_comp]
    exact (alternation_truncateBlocks (hq a) (P := fun w => V (f a, w) = true)).symm

/-- **`Πₖ` is closed under polynomial-time reductions**, by quantifier duality. -/
theorem PolyTimeReducible.mem_PiP (h : PolyTimeReducible enc encB A B) (hB : B ∈ PiP k encB) :
    A ∈ PiP k enc :=
  compl_mem_SigmaP_iff.mp (h.compl.mem_SigmaP (compl_mem_SigmaP_iff.mpr hB))

/-- **`PH` is closed under polynomial-time reductions.** -/
theorem PolyTimeReducible.mem_PH (h : PolyTimeReducible enc encB A B) (hB : B ∈ PH encB) :
    A ∈ PH enc := by
  obtain ⟨k, hk⟩ := Complexity.mem_PH.1 hB
  exact SigmaP_subset_PH k (h.mem_SigmaP hk)

/-- **`Σₖ` is closed under existential quantification of computed unary polynomial-time length**,
for `k ≥ 1`. Cutting certificates to `N y.1` reduces to a fixed polynomial block length, where
`Cslib.Complexity.mem_SigmaP_of_exists` merges the quantifier with the first block of `B`. -/
theorem mem_SigmaP_of_exists_length (hk : 1 ≤ k) {N : α → ℕ}
    (hN : ComputableInPolyTime N enc encUnary) {C : Set (α × List Bool)}
    (hC : C ∈ SigmaP k (encPair enc encBits)) :
    {a | ∃ w : List Bool, w.length = N a ∧ (a, w) ∈ C} ∈ SigmaP k enc := by
  obtain ⟨p, hp⟩ := hN.polyBounded.exists_polynomial
  let C' : Set (α × List Bool) := {y | (y.1, y.2.take (N y.1)) ∈ C}
  have hred : PolyTimeReducible (encPair enc encBits) (encPair enc encBits) C' C :=
    ⟨fun y => (y.1, y.2.take (N y.1)),
      (fst enc encBits).prod (bitsTakeWithInput (snd enc encBits) (hN.comp (fst enc encBits))),
      fun _ => Iff.rfl⟩
  convert mem_SigmaP_of_exists hk (hred.mem_SigmaP hC) p using 1
  ext a
  exact (List.exists_length_eq_take_iff (P := fun u => (a, u) ∈ C) (hp a)).symm

/-- **`Πₖ` is closed under universal quantification of computed unary polynomial-time length**,
for `k ≥ 1`, by quantifier duality from `Cslib.Complexity.mem_SigmaP_of_exists_length`. -/
theorem mem_PiP_of_forall_length (hk : 1 ≤ k) {N : α → ℕ}
    (hN : ComputableInPolyTime N enc encUnary) {C : Set (α × List Bool)}
    (hC : C ∈ PiP k (encPair enc encBits)) :
    {a | ∀ w : List Bool, w.length = N a → (a, w) ∈ C} ∈ PiP k enc := by
  have hex := mem_SigmaP_of_exists_length hk hN (compl_mem_SigmaP_of_mem_PiP hC)
  convert compl_mem_PiP_of_mem_SigmaP hex using 1
  ext a
  simp

/-- Appending a word `u` to the word component of `(a, s)` is polynomial-time. -/
private theorem polyTimeReducible_append (C : Set (α × List Bool)) :
    PolyTimeReducible (encPair (encPair enc encBits) encBits) (encPair enc encBits)
      {x : (α × List Bool) × List Bool | (x.1.1, x.1.2 ++ x.2) ∈ C} C :=
  ⟨fun x => (x.1.1, x.1.2 ++ x.2), (fst _ _).fst'.prod (bitsAppend (fst _ _).snd' (snd _ _)),
    fun _ => Iff.rfl⟩

/-- **`Σₖ` on pairs is closed under existentially extending the word**, for `k ≥ 1`: if `C` is in
`Σₖ`, so is the set of `(a, s)` with some `u` of computed length `N (a, s)` and
`(a, s ++ u) ∈ C`. -/
theorem mem_SigmaP_of_exists_append (hk : 1 ≤ k) {N : α × List Bool → ℕ}
    (hN : ComputableInPolyTime N (encPair enc encBits) encUnary) {C : Set (α × List Bool)}
    (hC : C ∈ SigmaP k (encPair enc encBits)) :
    {x : α × List Bool | ∃ u : List Bool, u.length = N x ∧ (x.1, x.2 ++ u) ∈ C} ∈
      SigmaP k (encPair enc encBits) :=
  mem_SigmaP_of_exists_length hk hN ((polyTimeReducible_append C).mem_SigmaP hC)

/-- **`Πₖ` on pairs is closed under universally extending the word**, for `k ≥ 1`: if `C` is in
`Πₖ`, so is the set of `(a, s)` with `(a, s ++ u) ∈ C` for every `u` of computed length
`N (a, s)`. -/
theorem mem_PiP_of_forall_append (hk : 1 ≤ k) {N : α × List Bool → ℕ}
    (hN : ComputableInPolyTime N (encPair enc encBits) encUnary) {C : Set (α × List Bool)}
    (hC : C ∈ PiP k (encPair enc encBits)) :
    {x : α × List Bool | ∀ u : List Bool, u.length = N x → (x.1, x.2 ++ u) ∈ C} ∈
      PiP k (encPair enc encBits) :=
  mem_PiP_of_forall_length hk hN ((polyTimeReducible_append C).mem_PiP hC)

end Cslib.Complexity
