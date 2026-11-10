/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Ordered.TupleInterpretation
import CslibFrontier.Tactic.FirstOrder

/-!
# Successor on full tuple universes

A non-wrapping successor increments one coordinate, keeps earlier coordinates fixed and carries
all later coordinates from maximum to zero. This is equivalent to increasing the arbitrary-base
lexicographic rank by exactly one. The full tuple universe is essential to the interval argument.

The native carry compiler preserves quantifier-freeness when its supplied source successor is
quantifier-free, as in Immerman's Exercise 1.33(2) with source SUC available. In the library's
`≤`/BIT basis, the canonical source successor instead uses a universal adjacency formula. Its
compiled tuple formula is first-order, with one element quantifier in each carry alternative;
no unconditional quantifier-free claim is made for this basis. Native full-tuple BIT is supplied
in `Ordered.TupleBit`; numeric-preserving full-tuple composition is in
`Ordered.FullTuple.Composition`.

## Main definitions

* `Cslib.Logic.FO.Ordered.IsCarrySuccessor`: the coordinatewise carry condition.
* `Cslib.Logic.FO.Ordered.tupleSuccOf`: compile any supplied source successor using finite carries.
* `Cslib.Logic.FO.Ordered.successor`: canonical source adjacency, with one universal quantifier.
* `Cslib.Logic.FO.Ordered.tupleSucc`: the canonical full-tuple successor formula.

## Main results

* `Cslib.Logic.FO.Ordered.isCarrySuccessor_iff`: the carry condition is exact rank successor.
* `Cslib.Logic.FO.Ordered.isQF_tupleSuccOf`: conditional preservation of quantifier-freeness.
* `Cslib.Logic.FO.Ordered.realize_tupleSuccOf`, `Cslib.Logic.FO.Ordered.realize_tupleSucc`:
  the generic and canonical formulas hold exactly at consecutive ranks.
* `Cslib.Logic.FO.Ordered.not_realize_tupleSucc_zero`,
  `Cslib.Logic.FO.Ordered.not_realize_tupleSucc_of_max`: zero-dimension and maximum boundaries.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Remark 1.32 and Exercise 1.33(2).
-/

@[expose] public section

namespace Cslib.Logic.FO.Ordered

/-- Non-wrapping increment of a tuple: one digit increases, with a maximum-to-zero suffix. -/
def IsCarrySuccessor {n k : ℕ} (x y : Fin k → Fin n) : Prop :=
  ∃ i, (y i).val = (x i).val + 1 ∧ (∀ j, j < i → x j = y j) ∧
    ∀ j, i < j → (x j).val = n - 1 ∧ (y j).val = 0

/-- Consecutive ranks are exactly strict tuple intervals with no intermediate tuple. -/
theorem lexRank_succ_iff {n k : ℕ} (x y : Fin k → Fin n) :
    lexRank y = lexRank x + 1 ↔
      lexRank x < lexRank y ∧
        ∀ z : Fin k → Fin n, ¬(lexRank x < lexRank z ∧ lexRank z < lexRank y) := by
  constructor
  · intro h
    exact ⟨by lia, fun z hz => by lia⟩
  · rintro ⟨hxy, h⟩
    by_contra he
    have hr : lexRank x + 1 < n ^ k := by have := lexRank_lt y; lia
    let r : Fin (n ^ k) := ⟨lexRank x + 1, hr⟩
    have hz : lexRank (lexEquiv.symm r) = lexRank x + 1 :=
      congrArg Fin.val (lexEquiv.apply_symm_apply r)
    exact h (lexEquiv.symm r) ⟨by lia, by lia⟩

/-- A carry increment has no intermediate tuple in lexicographic order. -/
theorem IsCarrySuccessor.lexRank_succ {n k : ℕ} {x y : Fin k → Fin n}
    (h : IsCarrySuccessor x y) : lexRank y = lexRank x + 1 := by
  obtain ⟨i, hi, hpre, hpost⟩ := h
  apply (lexRank_succ_iff x y).mpr
  refine ⟨(lexRank_lt_iff x y).mpr ⟨i, by change (x i).val < (y i).val; lia, hpre⟩, ?_⟩
  intro z ⟨hxz, hzy⟩
  obtain ⟨a, ha, hxa⟩ := (lexRank_lt_iff x z).mp hxz
  obtain ⟨b, hb, hzb⟩ := (lexRank_lt_iff z y).mp hzy
  have hai : ¬a < i := by
    intro hai
    rcases lt_trichotomy a b with hab | rfl | hba
    · have := hzb a hab
      have := hpre a hai
      lia
    · have := hpre a hai
      lia
    · have := hxa b hba
      have := hpre b (lt_trans hba hai)
      lia
  have hbi : ¬b < i := by
    intro hbi
    have := hxa b (lt_of_lt_of_le hbi (le_of_not_gt hai))
    have := hpre b hbi
    lia
  have hai' : a = i := by
    by_contra hne
    have hia : i < a := lt_of_le_of_ne (le_of_not_gt hai) (Ne.symm hne)
    have := (hpost a hia).1
    have := (z a).isLt
    change (x a).val < (z a).val at ha
    lia
  have hbi' : b = i := by
    by_contra hne
    have hib : i < b := lt_of_le_of_ne (le_of_not_gt hbi) (Ne.symm hne)
    have := (hpost b hib).2
    change (z b).val < (y b).val at hb
    lia
  subst a b
  change (x i).val < (z i).val at ha
  change (z i).val < (y i).val at hb
  lia

/-- Consecutive ranks have precisely one increment coordinate and a carried suffix. -/
theorem isCarrySuccessor_of_lexRank_succ {n k : ℕ} {x y : Fin k → Fin n}
    (h : lexRank y = lexRank x + 1) : IsCarrySuccessor x y := by
  obtain ⟨hxy, hgap⟩ := (lexRank_succ_iff x y).mp h
  obtain ⟨i, hi, hpre⟩ := (lexRank_lt_iff x y).mp hxy
  have hi' : (x i).val < (y i).val := hi
  refine ⟨i, ?_, hpre, ?_⟩
  · by_contra he
    have hlt : (x i).val + 1 < (y i).val := by lia
    let c : Fin n := ⟨(x i).val + 1, lt_trans hlt (y i).isLt⟩
    let z := Function.update x i c
    apply hgap z
    constructor
    · apply (lexRank_lt_iff x z).mpr
      refine ⟨i, ?_, fun j hj => ?_⟩
      · simp [z, c, Fin.lt_def]
      · simp [z, ne_of_lt hj]
    · apply (lexRank_lt_iff z y).mpr
      refine ⟨i, ?_, fun j hj => ?_⟩
      · simpa [z, c, Fin.lt_def] using hlt
      · simpa [z, ne_of_lt hj] using hpre j hj
  · intro j hij
    constructor
    · by_contra he
      have hlt : (x j).val + 1 < n := by have := (x j).isLt; lia
      let c : Fin n := ⟨(x j).val + 1, hlt⟩
      let z := Function.update x j c
      apply hgap z
      constructor
      · apply (lexRank_lt_iff x z).mpr
        refine ⟨j, ?_, fun a ha => ?_⟩
        · simp [z, c, Fin.lt_def]
        · simp [z, ne_of_lt ha]
      · apply (lexRank_lt_iff z y).mpr
        refine ⟨i, ?_, fun a ha => ?_⟩
        · simpa [z, ne_of_lt hij] using hi
        · simpa [z, ne_of_lt (lt_trans ha hij)] using hpre a ha
    · by_contra he
      let c : Fin n := ⟨0, Nat.zero_lt_of_lt (y j).isLt⟩
      let z := Function.update y j c
      apply hgap z
      constructor
      · apply (lexRank_lt_iff x z).mpr
        refine ⟨i, ?_, fun a ha => ?_⟩
        · simpa [z, ne_of_lt hij] using hi
        · simpa [z, ne_of_lt (lt_trans ha hij)] using hpre a ha
      · apply (lexRank_lt_iff z y).mpr
        refine ⟨j, ?_, fun a ha => ?_⟩
        · simp only [z, Function.update_self, c, Fin.lt_def]
          lia
        · simp [z, ne_of_lt ha]

/-- The coordinatewise carry condition is exactly non-wrapping numerical successor. -/
theorem isCarrySuccessor_iff {n k : ℕ} (x y : Fin k → Fin n) :
    IsCarrySuccessor x y ↔ lexRank y = lexRank x + 1 :=
  ⟨IsCarrySuccessor.lexRank_succ, isCarrySuccessor_of_lexRank_succ⟩

open FirstOrder Language Structure

/-- Compile a supplied source successor formula into full-tuple successor by finite carries. -/
noncomputable def tupleSuccOf {L : Language} (σ : (language L).Formula (Fin 2)) (k : ℕ) :
    (language L).Formula (Fin 2 × Fin k) :=
  Formula.iSup fun i : Fin k =>
    σ.relabel (fun a => (a, i)) ⊓ Formula.iInf fun j : Fin k =>
      if j < i then Term.equal (.var (0, j)) (.var (1, j))
      else if i < j then
        Term.equal (.var (0, j)) (max L) ⊓ Term.equal (.var (1, j)) (zero L)
      else ⊤

/-- The carry compiler introduces no quantifiers beyond those of the supplied successor. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem isQF_tupleSuccOf {L : Language} {σ : (language L).Formula (Fin 2)}
    (hσ : σ.IsQF) (k : ℕ) : (tupleSuccOf σ k).IsQF := by
  unfold tupleSuccOf; fo_qf

/-- Source successor in the canonical `≤` language: strict order with no intermediate point.
The formula universally quantifies one element; it is not asserted quantifier-free. -/
noncomputable def successor (L : Language) : (language L).Formula (Fin 2) :=
  (le L (.var 1) (.var 0)).not ⊓ Formula.iAlls Unit
    ((le L (.var (.inr ())) (.var (.inl 0))).not.imp
      (le L (.var (.inl 1)) (.var (.inr ()))))

variable {L : Language} {n k : ℕ} [Fact (2 ≤ n)] [L.Structure (Fin n)]

/-- The canonical source formula defines ordinary, non-wrapping successor. -/
@[simp, fo_realize]
theorem realize_successor (v : Fin 2 → Fin n) :
    (successor L).Realize v ↔ (v 1).val = (v 0).val + 1 := by
  fo_simp [successor, not_le]
  constructor
  · rintro ⟨h, hi⟩
    have h' : (v 0).val < (v 1).val := h
    let c : Fin n := ⟨(v 0).val + 1, by have := (v 1).isLt; lia⟩
    have hc := hi (fun _ => c) (by change (v 0).val < (v 0).val + 1; lia)
    change (v 1).val ≤ (v 0).val + 1 at hc
    lia
  · intro h
    refine ⟨by change (v 0).val < (v 1).val; lia, fun z hz => ?_⟩
    change (v 0).val < (z ()).val at hz
    change (v 1).val ≤ (z ()).val
    lia

/-- Any correct source successor formula compiles to exact successor of lexicographic ranks. -/
theorem realize_tupleSuccOf {σ : (language L).Formula (Fin 2)}
    (hσ : ∀ v : Fin 2 → Fin n, σ.Realize v ↔ (v 1).val = (v 0).val + 1)
    (v : Fin 2 × Fin k → Fin n) :
    (tupleSuccOf σ k).Realize v ↔
      lexRank (fun i => v (1, i)) = lexRank (fun i => v (0, i)) + 1 := by
  rw [← isCarrySuccessor_iff]
  fo_simp [tupleSuccOf, hσ, IsCarrySuccessor]
  refine exists_congr fun i => and_congr_right fun _ =>
    ⟨fun h => ⟨fun j hj => by simpa [hj] using h j, fun j hj => ?_⟩, fun ⟨hpre, hpost⟩ j => ?_⟩
  · have hh := h j
    fo_simp [not_lt.mpr (le_of_lt hj), hj] at hh
    exact ⟨congrArg Fin.val hh.1, congrArg Fin.val hh.2⟩
  · split_ifs with hji hij
    · exact hpre j hji
    · fo_simp
      exact ⟨Fin.ext (hpost j hij).1, Fin.ext (hpost j hij).2⟩
    · exact Formula.realize_top.mpr trivial

/-- Canonical non-wrapping successor on the full arbitrary-base tuple universe. -/
noncomputable def tupleSucc (L : Language) (k : ℕ) :
    (language L).Formula (Fin 2 × Fin k) := tupleSuccOf (successor L) k

/-- The canonical tuple successor formula holds exactly at consecutive numerical ranks. -/
@[simp, fo_realize]
theorem realize_tupleSucc (v : Fin 2 × Fin k → Fin n) :
    (tupleSucc L k).Realize v ↔
      lexRank (fun i => v (1, i)) = lexRank (fun i => v (0, i)) + 1 :=
  realize_tupleSuccOf realize_successor v

/-- The zero-dimensional full tuple universe is a singleton, so it has no successor pair. -/
theorem not_realize_tupleSucc_zero (v : Fin 2 × Fin 0 → Fin n) :
    ¬(tupleSucc L 0).Realize v := by
  simp [realize_tupleSucc, lexRank_apply]

/-- The maximum tuple has no successor; in particular, the formula does not wrap to zero. -/
theorem not_realize_tupleSucc_of_max (v : Fin 2 × Fin k → Fin n)
    (hmax : (fun i => v (0, i)) = tupleMax) : ¬(tupleSucc L k).Realize v := by
  rw [realize_tupleSucc, hmax, lexRank_tupleMax]
  have := lexRank_lt (fun i => v (1, i))
  lia

end Cslib.Logic.FO.Ordered
