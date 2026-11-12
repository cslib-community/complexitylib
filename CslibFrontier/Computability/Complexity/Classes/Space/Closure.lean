/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Space
public import CslibFrontier.Computability.Complexity.Reduction
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolySpace
public import CslibFrontier.Foundations.Order.BooleanSubalgebra
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BoundedSearch
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain

/-!
# Characterizations and closure properties of `PSPACE`

A problem is in `PSPACE` exactly when a Boolean function deciding it is computable within
some time and space polynomial in the length of the encoded instance
(`Cslib.Complexity.mem_PSPACE_iff_computableInO`,
`Cslib.Complexity.mem_PSPACE_iff_computableInPolySpace`). `PSPACE` is closed under
complement, under polynomial-time reductions, and under polynomially bounded existential
quantification [Arora and Barak, Chapter 4][AroraBarak09]. The existential quantifier over words
`w` of length `ℓ` streams one candidate at a time and
reuses the space of the decider for each (`Turing.MultiTapeTM.ComputableInO.exists_bits`).

## Main results

* `Cslib.Complexity.mem_PSPACE_iff_computableInO`: `PSPACE` in the quantitative calculus.
* `Cslib.Complexity.mem_PSPACE_iff_computableInPolySpace`,
  `Cslib.Complexity.mem_PSPACE_of_computableInPolySpace`: `PSPACE` within polynomial space.
* `Cslib.Complexity.compl_mem_PSPACE`, `Cslib.Complexity.PSPACE_eq_preimage_compl_PSPACE`,
  `Cslib.Complexity.inter_mem_PSPACE`,
  `Cslib.Complexity.union_mem_PSPACE`, `Cslib.Complexity.diff_mem_PSPACE`,
  `Cslib.Complexity.symmDiff_mem_PSPACE`, `Cslib.Complexity.PSPACE.booleanSubalgebra`,
  `Cslib.Complexity.PolyTimeReducible.mem_PSPACE`, `Cslib.Complexity.setOf_exists_mem_PSPACE`:
  closure properties of `PSPACE`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM Filter

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}


/-- **`PSPACE` in the quantitative calculus**: a problem is in `PSPACE` exactly when a Boolean
function deciding it is computable within some time and within space polynomial in the length of
the encoded instance. -/
theorem mem_PSPACE_iff_computableInO : A ∈ PSPACE enc ↔ ∃ (f : α → Bool) (T S : α → ℕ),
    ComputableInO f enc encBool T S ∧ PolyBounded (fun a => (enc a).length) S ∧
      ∀ a, a ∈ A ↔ f a = true := by
  constructor
  · rintro ⟨f, ⟨t, s, hs, hf⟩, hA⟩
    exact ⟨f, t, s, ⟨1, hf.mono (fun _ => by omega) fun _ => by omega, fun _ => by simp⟩, hs, hA⟩
  · rintro ⟨f, T, S, ⟨c, hc, -⟩, hS, hA⟩
    exact ⟨f, ⟨_, _, (PolyBounded.const c).mul (hS.add (.const 1)), hc⟩, hA⟩

/-- **`PSPACE` within polynomial space**: a problem is in `PSPACE` exactly when a Boolean function
deciding it is computable within space polynomial in the length of the encoded instance
(`Turing.MultiTapeTM.ComputableInPolySpace`). -/
theorem mem_PSPACE_iff_computableInPolySpace : A ∈ PSPACE enc ↔
    ∃ f : α → Bool, ComputableInPolySpace f enc encBool ∧ ∀ a, a ∈ A ↔ f a = true := by
  constructor
  · rintro ⟨f, ⟨t, s, hs, hf⟩, hA⟩
    obtain ⟨c, d, hcd⟩ := hs.exists_le
    refine ⟨f, ⟨t, fun n => c * (n + 1) ^ d + 1, by fun_prop,
      hf.mono (fun _ => le_rfl) fun a => (hcd a).trans (Nat.le_succ _),
      fun _ => by simp⟩, hA⟩
  · rintro ⟨f, ⟨t, s, hs, hf, -⟩, hA⟩
    exact ⟨f, ⟨t, _, .of_polynomiallyBounded _ hs, hf⟩, hA⟩

/-- A Boolean function computable within polynomial space decides a problem in `PSPACE`. -/
theorem mem_PSPACE_of_computableInPolySpace {f : α → Bool}
    (hf : ComputableInPolySpace f enc encBool) (hA : ∀ a, a ∈ A ↔ f a = true) :
    A ∈ PSPACE enc :=
  mem_PSPACE_iff_computableInPolySpace.mpr ⟨f, hf, hA⟩

/-- **`PSPACE` is closed under complement**: negate the answer. -/
theorem compl_mem_PSPACE (hA : A ∈ PSPACE enc) : Aᶜ ∈ PSPACE enc := by
  obtain ⟨f, hf, hA⟩ := mem_PSPACE_iff_computableInPolySpace.mp hA
  exact mem_PSPACE_of_computableInPolySpace
    ((ComputableInPolySpace.of_polyTime ComputableInPolyTime.bool_not).comp hf)
    fun a => by simp [hA a]

/-- `PSPACE` equals its preimage under complement. -/
theorem PSPACE_eq_preimage_compl_PSPACE (enc : α ↪ List Bool) :
    PSPACE enc = compl ⁻¹' PSPACE enc :=
  Set.ext fun _ => ⟨compl_mem_PSPACE, fun h => by simpa using compl_mem_PSPACE h⟩

open scoped symmDiff

/-- **`PSPACE` is closed under intersection.** -/
theorem inter_mem_PSPACE {B : Set α} (hA : A ∈ PSPACE enc) (hB : B ∈ PSPACE enc) :
    A ∩ B ∈ PSPACE enc := by
  obtain ⟨f, hf, hA⟩ := mem_PSPACE_iff_computableInPolySpace.mp hA
  obtain ⟨g, hg, hB⟩ := mem_PSPACE_iff_computableInPolySpace.mp hB
  exact mem_PSPACE_of_computableInPolySpace
    ((ComputableInPolySpace.of_polyTime ComputableInPolyTime.bool_and).comp (hf.prod hg))
    fun a => by simp [hA a, hB a]

/-- `PSPACE` as a Boolean subalgebra of `Set α`. -/
def PSPACE.booleanSubalgebra (enc : α ↪ List Bool) : BooleanSubalgebra (Set α) :=
  .ofComplInf (PSPACE enc) (P_subset_PSPACE empty_mem_P) (fun _ => compl_mem_PSPACE)
    (fun _ _ => inter_mem_PSPACE)

@[simp]
theorem PSPACE.coe_booleanSubalgebra :
    (PSPACE.booleanSubalgebra enc : Set (Set α)) = PSPACE enc := rfl

@[simp]
theorem PSPACE.mem_booleanSubalgebra : A ∈ PSPACE.booleanSubalgebra enc ↔ A ∈ PSPACE enc :=
  Iff.rfl

/-- `PSPACE` is closed under union. -/
theorem union_mem_PSPACE {B : Set α} (hA : A ∈ PSPACE enc) (hB : B ∈ PSPACE enc) :
    A ∪ B ∈ PSPACE enc :=
  (PSPACE.booleanSubalgebra enc).sup_mem hA hB

/-- `PSPACE` is closed under set difference. -/
theorem diff_mem_PSPACE {B : Set α} (hA : A ∈ PSPACE enc) (hB : B ∈ PSPACE enc) :
    A \ B ∈ PSPACE enc :=
  (PSPACE.booleanSubalgebra enc).sdiff_mem hA hB

/-- `PSPACE` is closed under symmetric difference. -/
theorem symmDiff_mem_PSPACE {B : Set α} (hA : A ∈ PSPACE enc) (hB : B ∈ PSPACE enc) :
    A ∆ B ∈ PSPACE enc :=
  (PSPACE.booleanSubalgebra enc).symmDiff_mem hA hB

/-- **`PSPACE` is closed under polynomial-time reductions.** -/
theorem PolyTimeReducible.mem_PSPACE {β : Type} {encB : β ↪ List Bool} {B : Set β}
    (h : PolyTimeReducible enc encB A B) (hB : B ∈ PSPACE encB) : A ∈ PSPACE enc := by
  obtain ⟨g, hg, hAB⟩ := h
  obtain ⟨f, hf, hB⟩ := mem_PSPACE_iff_computableInPolySpace.mp hB
  exact mem_PSPACE_of_computableInPolySpace (hf.comp (.of_polyTime hg))
    fun a => (hAB a).trans (hB (g a))

/-- **`PSPACE` is closed under polynomially bounded existential quantification.** The candidates
are streamed in place by `ComputableInO.exists_bits`, reusing the decider's workspace without a
polynomial-time assumption on that decider. -/
theorem setOf_exists_mem_PSPACE {β : Type} {encB : β ↪ List Bool} {B : Set (β × List Bool)}
    {ℓ : β → ℕ} (hB : B ∈ PSPACE (encPair encB encBits))
    (hℓ : ComputableInPolyTime ℓ encB encUnary) :
    {x | ∃ w : List Bool, w.length = ℓ x ∧ (x, w) ∈ B} ∈ PSPACE encB := by
  obtain ⟨f, T, S, hf, hS, hB⟩ := mem_PSPACE_iff_computableInO.mp hB
  let size := fun p : β × ℕ => (encPair encB encUnary p).length
  let time := fun p : β × ℕ => listMax (fun w => T (p.1, w)) (BitString.enumList p.2)
  obtain ⟨c, d, hs⟩ := hS.exists_le
  let space := fun p : β × ℕ => c * (size p + 1) ^ d
  have hspace : PolyBounded size space := PolyBounded.of_forall_le c d fun _ => le_rfl
  obtain ⟨overhead, ho, h⟩ := hf.exists_bits (T := time) (S := space)
    (fun p w hw => le_listMax (f := fun w => T (p.1, w)) (BitString.mem_enumList.mpr hw))
    (fun p w hw => by
      apply (hs (p.1, w)).trans_eq
      simp only [space, size, length_encPair, encBits_apply, encUnary_apply,
        List.length_replicate, hw])
  have hin : ComputableInPolyTime (fun x => (x, ℓ x)) encB (encPair encB encUnary) :=
    ComputableInPolyTime.id'.prod hℓ
  obtain ⟨Ti, Si, -, hSi, hi⟩ := hin.exists_computableInO
  have hfinal := h.comp hi
  refine mem_PSPACE_iff_computableInO.mpr ⟨_, _, _, hfinal,
    hSi.add ((ho.add hspace).comp hin.polyBounded_length), fun x => ?_⟩
  simp only [Set.mem_ofPred_eq, Function.comp_apply, List.any_eq_true, BitString.mem_enumList, ← hB]

end Cslib.Complexity
