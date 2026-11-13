/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Ladner.PolyTime
public import CslibFrontier.Computability.Complexity.Classes.RecursivelyPresentable
public import CslibFrontier.Computability.Complexity.Reduction
import CslibFrontier.Computability.Complexity.Classes.P.Closure
import CslibFrontier.Computability.Complexity.Classes.P.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.TwoPow
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Partrec

/-!
# Recursive presentations of `P`, polynomial-time transducers, and lower `≤ₘᵖ`-cones

This module presents `P`, enumerates polynomial-time transducers `List Bool → List Bool`, and
establishes recursive presentability and finite-variation closure for lower `≤ₘᵖ`-cones and for any
`≤ₘᵖ`-closed class on bit words with a decidable `≤ₘᵖ`-complete problem, without importing the
delayed diagonalization construction of
`CslibFrontier.Computability.Complexity.Classes.UniformDiagonalization`.

## Main definitions

* `Cslib.Complexity.UniformDiagonalization.pIndexed`, `.pIndexedCap`: the clocked presentation of
  `P` on bit words and its budget-capped form.
* `Cslib.Complexity.Ladner.transducerIndexed`: the clocked enumeration of polynomial-time
  transducers `List Bool → List Bool`.

## Main results

* `Cslib.Complexity.Ladner.isComputable_clock`, `.isComputable_withClock`: `(i, l) ↦ clock i l` is
  computable on unary inputs via exponential padding.
* `Cslib.Complexity.UniformDiagonalization.setOf_pIndexed_mem_P`,
  `Cslib.Complexity.UniformDiagonalization.exists_setOf_pIndexed_eq`: every slice of `pIndexed`
  is in `P`, and every problem in `P` is a slice at arbitrarily large indices.
* `Cslib.Complexity.UniformDiagonalization.computableInPolyTime_pIndexedCap`,
  `Cslib.Complexity.UniformDiagonalization.pIndexedCap_eq_pIndexed_of_le`,
  `Cslib.Complexity.UniformDiagonalization.isComputable_pIndexed`: the budget-capped form is
  polynomial-time and agrees with `pIndexed` once the budget suffices, and `pIndexed` is computable.
* `Cslib.Complexity.recursivelyPresentable_P`: `P` on bit words is recursively presentable.
* `Cslib.Complexity.Ladner.computableInPolyTime_transducerIndexed`,
  `Cslib.Complexity.Ladner.exists_transducerIndexed_eq`,
  `Cslib.Complexity.Ladner.isComputable_transducerIndexed`: every fixed slice of
  `transducerIndexed` is polynomial-time, every polynomial-time function on bit words appears at
  arbitrarily large indices, and the two-argument family is computable.
* `Cslib.Complexity.polyTimeReducible_of_symmDiff_finite_left`,
  `Cslib.Complexity.polyTimeReducible_of_symmDiff_finite_right`,
  `Cslib.Complexity.closedUnderFiniteVariation_polyTimeReducible_le`: finite-variation patching of
  polynomial-time reductions and closure of lower `≤ₘᵖ`-cones.
* `Cslib.Complexity.recursivelyPresentable_polyTimeReducible_le`,
  `Cslib.Complexity.PolyTimeComplete.recursivelyPresentable`: recursive presentations of lower
  `≤ₘᵖ`-cones and of classes with a decidable `≤ₘᵖ`-complete problem.

## References

* [R. E. Ladner, *On the Structure of Polynomial Time Reducibility*][Ladner1975a]
* [U. Schöning, *A uniform approach to obtain diagonal sets in complexity
  classes*][Schoening1982]
-/

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal ComputableInPolyTime
open scoped symmDiff

public section

namespace Cslib.Complexity

/-! ### Computability of polynomial clocks -/

namespace Ladner

/-- **The polynomial clock `(i, l) ↦ clock i l` is computable** on unary inputs, by padding an
exponential unary budget with `exists_computableInO_unary_two_pow` and computing `capPow` within
that budget. -/
theorem isComputable_clock :
    IsComputable (fun p : ℕ × ℕ => clock p.1 p.2) (encPair encUnary encUnary) encUnary := by
  have hL : ComputableInPolyTime (fun p : ℕ × ℕ => (p.2 + 1) * p.1)
      (encPair encUnary encUnary) encUnary := by fun_prop
  obtain ⟨_, _, hpad, -⟩ := hL.exists_computableInO_unary_two_pow
  have hpair := (isComputable_id (encPair encUnary encUnary)).prod
    (enc := encPair (encPair encUnary encUnary) encUnary) hpad.isComputable
  have hcap : ComputableInPolyTime
      (fun q : (ℕ × ℕ) × ℕ => capPow (2 * q.1.2 + 2) q.1.1 q.2)
      (encPair (encPair encUnary encUnary) encUnary) encUnary := by fun_prop
  convert hcap.isComputable.comp hpair using 1
  funext p
  have hc := clock_le_two_pow p.1 p.2
  rw [clock] at hc
  simp only [Function.comp_apply, id_eq, capPow, clock, min_eq_left hc]

/-- Pairing `(i, w)` with its polynomial clock `clock i |w|` is computable. -/
theorem isComputable_withClock :
    IsComputable (fun p : ℕ × List Bool => (p, clock p.1 p.2.length))
      (encPair encUnary encBits) (encPair (encPair encUnary encBits) encUnary) := by
  have hargs : ComputableInPolyTime (fun p : ℕ × List Bool => (p.1, p.2.length))
      (encPair encUnary encBits) (encPair encUnary encUnary) := by fun_prop
  exact (isComputable_id (encPair encUnary encBits)).prod
    (enc := encPair (encPair encUnary encBits) encUnary)
    (isComputable_clock.comp hargs.isComputable)

end Ladner

/-! ### `P` is recursively presentable -/

namespace UniformDiagonalization

open Ladner (runIndexed clock exists_index_of_mem_P isComputable_withClock)

/-- The presentation of `P`: whether the machine with index `i` accepts `w` within its clock. -/
def pIndexed (p : ℕ × List Bool) : Bool :=
  decide (runIndexed p.1 p.2 (clock p.1 p.2.length) = ([eBit true], true))

/-- Every slice of `pIndexed` defines a problem in `P`. -/
theorem setOf_pIndexed_mem_P (i : ℕ) : {w | pIndexed (i, w) = true} ∈ P encBits := by
  have hc : ComputableInPolyTime (fun w : List Bool => clock i w.length) encBits encUnary :=
    (unary_pow i).comp (by fun_prop)
  have hd : ComputableInPolyTime (fun w : List Bool =>
      decide (runIndexed i w (clock i w.length) = ([eBit true], true))) encBits encBool := by
    fun_prop
  exact ⟨fun w => pIndexed (i, w), hd, fun _ => Iff.rfl⟩

/-- Every problem in `P` on bit words appears in `pIndexed` at arbitrarily large indices. -/
theorem exists_setOf_pIndexed_eq {A : Set (List Bool)} (h : A ∈ P encBits) (B : ℕ) :
    ∃ i, B ≤ i ∧ {w | pIndexed (i, w) = true} = A := by
  obtain ⟨f, hf, i, hi, hrun⟩ := exists_index_of_mem_P h B
  refine ⟨i, hi, Set.ext fun w => ?_⟩
  rw [Set.mem_ofPred_eq, pIndexed, hrun, hf]
  cases f w <;> decide

/-- The presentation of `P` with the clock capped at `c`. -/
def pIndexedCap : (ℕ × List Bool) × ℕ → Bool
  | ((i, w), c) =>
    decide (runIndexed i w (Ladner.capPow (2 * w.length + 2) i c) = ([eBit true], true))

/-- `pIndexedCap` is computable in polynomial time when the cap is given in unary. -/
theorem computableInPolyTime_pIndexedCap :
    ComputableInPolyTime pIndexedCap (encPair (encPair encUnary encBits) encUnary) encBool := by
  have heq : pIndexedCap = fun p =>
      decide (runIndexed p.1.1 p.1.2 (Ladner.capPow (2 * p.1.2.length + 2) p.1.1 p.2) =
        ([eBit true], true)) := by
    funext ⟨⟨_, _⟩, _⟩
    rfl
  rw [heq]
  fun_prop

/-- Once the cap `c` is at least `clock i |w|`, `pIndexedCap` agrees with `pIndexed`. -/
theorem pIndexedCap_eq_pIndexed_of_le {i : ℕ} {w : List Bool} {c : ℕ}
    (hc : clock i w.length ≤ c) :
    pIndexedCap ((i, w), c) = pIndexed (i, w) := by
  rw [clock] at hc
  simp only [pIndexedCap, pIndexed, Ladner.capPow, clock, min_eq_left hc]
  rfl

/-- **The presentation of `P` is computable**, by computing `clock` via `isComputable_withClock` and
running the universal simulator for that many steps. -/
theorem isComputable_pIndexed : IsComputable pIndexed (encPair encUnary encBits) encBool := by
  have hstep : ComputableInPolyTime
      (fun q : (ℕ × List Bool) × ℕ => decide (runIndexed q.1.1 q.1.2 q.2 = ([eBit true], true)))
      (encPair (encPair encUnary encBits) encUnary) encBool := by fun_prop
  have heq : pIndexed =
      (fun q : (ℕ × List Bool) × ℕ => decide (runIndexed q.1.1 q.1.2 q.2 = ([eBit true], true))) ∘
        fun p => (p, clock p.1 p.2.length) := rfl
  rw [heq]
  exact hstep.isComputable.comp isComputable_withClock

end UniformDiagonalization

/-- **`P` is recursively presentable**, by the machines run within polynomial clocks. -/
theorem recursivelyPresentable_P : RecursivelyPresentable encBits (P encBits) := by
  refine ⟨UniformDiagonalization.pIndexed, UniformDiagonalization.isComputable_pIndexed,
    Set.ext fun A => ⟨fun h => ?_, ?_⟩⟩
  · obtain ⟨i, -, hi⟩ := UniformDiagonalization.exists_setOf_pIndexed_eq h 0
    exact ⟨i, hi⟩
  · rintro ⟨i, rfl⟩
    exact UniformDiagonalization.setOf_pIndexed_mem_P i

/-! ### Enumerating polynomial-time transducers -/

namespace Ladner

private theorem map_ne_zero_map_eBit (w : List Bool) : (w.map eBit).map (· != 0) = w := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> exact congrArg (_ :: ·) ih

private def decodeRunOutput (r : List ℕ × Bool) : List Bool :=
  if r.2 then r.1.map (· != 0) else []

private theorem computableInPolyTime_decodeRunOutput :
    ComputableInPolyTime decodeRunOutput eOut encBits :=
  ComputableInPolyTime.ite (.snd (encList encUnary) encBool)
    (computableInPolyTime_map_ne_zero.comp (.fst (encList encUnary) encBool)) (.const [])

/-- The output of the `i`-th machine on `w` within its polynomial clock `clock i |w|`, decoded as a
bit word if the machine has halted, and `[]` otherwise. -/
def transducerIndexed (p : ℕ × List Bool) : List Bool :=
  decodeRunOutput (runIndexed p.1 p.2 (clock p.1 p.2.length))

/-- For each fixed index `i`, `w ↦ transducerIndexed (i, w)` is computable in polynomial time. -/
theorem computableInPolyTime_transducerIndexed (i : ℕ) :
    ComputableInPolyTime (fun w => transducerIndexed (i, w)) encBits encBits := by
  have hc : ComputableInPolyTime (fun w : List Bool => clock i w.length) encBits encUnary :=
    (unary_pow i).comp (by fun_prop)
  have hrun : ComputableInPolyTime (fun w : List Bool => runIndexed i w (clock i w.length))
      encBits eOut := by fun_prop
  exact computableInPolyTime_decodeRunOutput.comp hrun

/-- Every polynomial-time function `List Bool → List Bool` is realized by `transducerIndexed` at
arbitrarily large indices. -/
theorem exists_transducerIndexed_eq {f : List Bool → List Bool}
    (hf : ComputableInPolyTime f encBits encBits) (B : ℕ) :
    ∃ i, B ≤ i ∧ ∀ w, transducerIndexed (i, w) = f w := by
  obtain ⟨t, s, ht, -, k, State, hfinite, tm, htm⟩ := hf
  have := Fintype.ofFinite State
  let eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
  obtain ⟨c, e, hle⟩ := (PolyBounded.of_polynomiallyBounded List.length ht).exists_le
  obtain ⟨i, hi, hdesc⟩ := exists_index_ge (desc eS eBit tm) (B + c + e)
  refine ⟨i, by omega, fun w => ?_⟩
  have hrun : runIndexed i w (clock i w.length) = ((f w).map eBit, true) := by
    rw [runIndexed, hdesc]
    exact universal_desc_of_halted_map eS tm (fun x => (htm x).runFrom_of_le le_rfl)
      ((hle w).trans (le_clock (by omega) w.length))
  simp only [transducerIndexed, decodeRunOutput, hrun, ↓reduceIte, map_ne_zero_map_eBit]

/-- **The enumeration of polynomial-time transducers is computable**, with the index in unary. -/
theorem isComputable_transducerIndexed :
    IsComputable transducerIndexed (encPair encUnary encBits) encBits := by
  have hrun : ComputableInPolyTime
      (fun q : (ℕ × List Bool) × ℕ => runIndexed q.1.1 q.1.2 q.2)
      (encPair (encPair encUnary encBits) encUnary) eOut := by fun_prop
  have heq : transducerIndexed =
      (decodeRunOutput ∘ fun q : (ℕ × List Bool) × ℕ => runIndexed q.1.1 q.1.2 q.2) ∘
        fun p => (p, clock p.1 p.2.length) := rfl
  rw [heq]
  exact (computableInPolyTime_decodeRunOutput.comp hrun).isComputable.comp isComputable_withClock

end Ladner

open Ladner (transducerIndexed computableInPolyTime_transducerIndexed
  exists_transducerIndexed_eq isComputable_transducerIndexed)

/-! ### Finite-variation patching of reductions -/

/-- Patch a polynomial-time map `f : α → β` on two `P`-sets `S₁` (mapped to `b₁ ∈ B`) and `S₀`
(mapped to `b₀ ∉ B`). -/
private theorem polyTimeReducible_of_patch {α β : Type} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {A : Set α} {B : Set β} {f : α → β}
    (hf : ComputableInPolyTime f encA encB) {S₁ S₀ : Set α} (hS₁ : S₁ ∈ P encA)
    (hS₀ : S₀ ∈ P encA) {b₀ b₁ : β} (hb₀ : b₀ ∉ B) (hb₁ : b₁ ∈ B)
    (h₁ : ∀ x ∈ S₁, x ∈ A) (h₀ : ∀ x ∈ S₀, x ∉ A)
    (hrest : ∀ x, x ∉ S₁ → x ∉ S₀ → (x ∈ A ↔ f x ∈ B)) :
    PolyTimeReducible encA encB A B := by
  obtain ⟨g₁, hg₁, hG₁⟩ := hS₁
  obtain ⟨g₀, hg₀, hG₀⟩ := hS₀
  refine ⟨fun x => if g₁ x then b₁ else if g₀ x then b₀ else f x,
    hg₁.ite (.const b₁) (hg₀.ite (.const b₀) hf), fun x => ?_⟩
  by_cases hx₁ : x ∈ S₁
  · simp only [(hG₁ x).mp hx₁, ↓reduceIte, h₁ x hx₁, hb₁]
  · have hg₁x : g₁ x = false := Bool.eq_false_iff.mpr fun h => hx₁ ((hG₁ x).mpr h)
    by_cases hx₀ : x ∈ S₀
    · simp only [hg₁x, (hG₀ x).mp hx₀, Bool.false_eq_true, ↓reduceIte, h₀ x hx₀, hb₀]
    · have hg₀x : g₀ x = false := Bool.eq_false_iff.mpr fun h => hx₀ ((hG₀ x).mpr h)
      simp only [hg₁x, hg₀x, Bool.false_eq_true, ↓reduceIte, hrest x hx₁ hx₀]

/-- Modifying the source of a polynomial-time reduction on finitely many instances preserves
reducibility whenever the target has a non-member and a member. -/
theorem polyTimeReducible_of_symmDiff_finite_left {α β : Type} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {L L' : Set α} {B : Set β} (hLB : PolyTimeReducible encA encB L B)
    (hfin : (L ∆ L').Finite) {b₀ b₁ : β} (hb₀ : b₀ ∉ B) (hb₁ : b₁ ∈ B) :
    PolyTimeReducible encA encB L' B := by
  obtain ⟨f, hf, hL⟩ := hLB
  refine polyTimeReducible_of_patch hf
    ((hfin.subset (t := (L ∆ L') ∩ L') Set.inter_subset_left).mem_P (enc := encA))
    ((hfin.subset (t := (L ∆ L') \ L') Set.sdiff_subset).mem_P (enc := encA))
    hb₀ hb₁ (fun _ hx => hx.2) (fun _ hx => hx.2) fun x hx₁ hx₀ => ?_
  have hsame : x ∈ L' ↔ x ∈ L := by
    simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_symmDiff] at hx₁ hx₀
    tauto
  exact hsame.trans (hL x)

/-- The lower `≤ₘᵖ`-cone of a problem with a non-member and a member is closed under finite
variations. -/
theorem closedUnderFiniteVariation_polyTimeReducible_le {α β : Type} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {B : Set β} {b₀ b₁ : β} (hb₀ : b₀ ∉ B) (hb₁ : b₁ ∈ B) :
    ClosedUnderFiniteVariation {L : Set α | PolyTimeReducible encA encB L B} :=
  fun _ _ hLB hfin => polyTimeReducible_of_symmDiff_finite_left hLB hfin hb₀ hb₁

/-- Modifying the target of a polynomial-time reduction on finitely many instances preserves
reducibility whenever the modified target still has a non-member and a member. -/
theorem polyTimeReducible_of_symmDiff_finite_right {α β : Type} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {B : Set α} {L L' : Set β} (hBL : PolyTimeReducible encA encB B L)
    (hfin : (L ∆ L').Finite) {z₀ z₁ : β} (hz₀ : z₀ ∉ L') (hz₁ : z₁ ∈ L') :
    PolyTimeReducible encA encB B L' := by
  obtain ⟨r, hr, hB⟩ := hBL
  have hP₁ : r ⁻¹' ((L ∆ L') ∩ L) ∈ P encA :=
    PolyTimeReducible.mem_P ⟨r, hr, fun _ => Iff.rfl⟩
      ((hfin.subset Set.inter_subset_left).mem_P (enc := encB))
  have hP₀ : r ⁻¹' ((L ∆ L') \ L) ∈ P encA :=
    PolyTimeReducible.mem_P ⟨r, hr, fun _ => Iff.rfl⟩
      ((hfin.subset Set.sdiff_subset).mem_P (enc := encB))
  refine polyTimeReducible_of_patch hr hP₁ hP₀ hz₀ hz₁
    (fun x hx => (hB x).mpr hx.2) (fun x hx hBx => hx.2 ((hB x).mp hBx))
    fun x hx₁ hx₀ => (hB x).trans ?_
  simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_sdiff, Set.mem_symmDiff] at hx₁ hx₀
  tauto

/-! ### Presenting lower cones and classes with a complete problem -/

/-- **The lower `≤ₘᵖ`-cone of a decidable problem on bit words is recursively presentable.** -/
theorem recursivelyPresentable_polyTimeReducible_le {B : Set (List Bool)}
    (hB : IsDecidable B encBits) :
    RecursivelyPresentable encBits {L | PolyTimeReducible encBits encBits L B} := by
  obtain ⟨b, hb, hB'⟩ := hB.exists_isComputable
  refine ⟨b ∘ transducerIndexed, hb.comp isComputable_transducerIndexed, ?_⟩
  ext L
  simp only [Set.mem_ofPred_eq, Set.mem_range, Function.comp_apply]
  constructor
  · rintro ⟨f, hf, hLB⟩
    obtain ⟨i, -, hi⟩ := exists_transducerIndexed_eq hf 0
    refine ⟨i, Set.ext fun w => ?_⟩
    simp only [Set.mem_ofPred_eq, hi w, ← hB' (f w), ← hLB w]
  · rintro ⟨i, rfl⟩
    exact ⟨fun w => transducerIndexed (i, w), computableInPolyTime_transducerIndexed i,
      fun w => (hB' _).symm⟩

/-- **Any class on bit words closed under `≤ₘᵖ` that has a decidable `≤ₘᵖ`-complete problem is
recursively presentable.** -/
theorem PolyTimeComplete.recursivelyPresentable
    {𝒞 : ∀ {α : Type}, (α ↪ List Bool) → Set (Set α)} {B : Set (List Bool)}
    (hB : PolyTimeComplete 𝒞 encBits B) (hdec : IsDecidable B encBits)
    (hclosed : ∀ ⦃A : Set (List Bool)⦄, PolyTimeReducible encBits encBits A B → A ∈ 𝒞 encBits) :
    RecursivelyPresentable encBits (𝒞 encBits) := by
  have heq : 𝒞 encBits = {A | PolyTimeReducible encBits encBits A B} :=
    Set.ext fun A => ⟨fun hA => hB.2 encBits A hA, fun hAB => hclosed hAB⟩
  exact heq ▸ recursivelyPresentable_polyTimeReducible_le hdec

end Cslib.Complexity
