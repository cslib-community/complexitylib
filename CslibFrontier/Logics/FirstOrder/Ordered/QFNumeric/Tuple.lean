/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Ordered.QFNumeric
public import CslibFrontier.Logics.FirstOrder.Ordered.Tuple
import CslibFrontier.Logics.FirstOrder.Ordered.TupleSuccessor
import CslibFrontier.Logics.FirstOrder.QuantifierFree
import CslibFrontier.Tactic.FirstOrder

/-!
# Quantifier-free `BIT`-free numeric pullback to full tuple universes

To compose two quantifier-free projections without introducing quantifiers or `BIT`, numeric guards
over the intermediate power universe `Fin (n ^ k)` must be pulled back to quantifier-free formulas
over `k`-tuples in `Fin n` within `qfNumericLanguage` (`≤`, non-wrapping successor, `0`, `max`).

`QFNumeric.onFullTuple` performs this block translation on `qfNumericLanguage.Formula β`:
equality becomes coordinatewise equality, `≤` becomes first-difference lexicographic order, `succ`
becomes finite-carry successor, and `0` and `max` become constant all-`0` and all-`max` tuples;
quantifiers map to `⊥` and are excluded by the `IsQF` hypothesis on `realize_onFullTuple`.
Because `qfNumericLanguage` has no `BIT` symbol, `BIT` never enters quantifier-free projection
guards before or after composition.

The existing `Ordered.tupleLt` and `Ordered.tupleSuccOf` formulas live over `Ordered.language L`,
which includes the constant `1` and the predicate `BIT` absent from `qfNumericLanguage`, so they
cannot be unfolded into `qfNumericLanguage` without widening `Ordered.TupleInterpretation`. Instead,
this module states the short lexicographic-order and carry-successor formulas directly over
`qfNumericLanguage` and derives their semantics from the shared combinatorial characterizations
`lexRank_lt_iff`, `lexRank_tupleZero`, `lexRank_tupleMax`, and `isCarrySuccessor_iff`.

## Main definitions

* `Cslib.Logic.FO.Ordered.QFNumeric.onFullTuple`: quantifier-free block translation of
  `qfNumericLanguage` formulas from elements to `k`-tuples.

## Main results

* `Cslib.Logic.FO.Ordered.QFNumeric.isQF_onFullTuple`: `onFullTuple` preserves quantifier-freeness.
* `Cslib.Logic.FO.Ordered.QFNumeric.realize_onFullTuple`: for `2 ≤ n` and `0 < k`, a quantifier-free
  formula holds of the lexicographic ranks `lexEquiv (v b)` in `Fin (n ^ k)` iff `onFullTuple k φ`
  holds of the `k`-tuples `v` over `Fin n`.

## References

* [N. Immerman and S. Landau, *The Complexity of Iterated Multiplication*][ImmermanLandau1995],
  Definitions 3.3 and 3.6 and Proposition 3.7.
* [N. Immerman, *Descriptive Complexity*][Immerman1999], Remark 1.32 and Exercise 1.33(1)--(2).
-/

public section

namespace Cslib.Logic.FO.Ordered.QFNumeric

open FirstOrder Language Structure

/-- Coordinate `i` of the `k`-tuple translation of a `qfNumericLanguage` term: free variables
select their `i`-th coordinate, while `0` and `max` become constant `0` and `max` coordinates
(bound variables map to `zero` and do not occur in `Formula β`). -/
private def onTupleTerm {β : Type*} {k m : ℕ} (i : Fin k) :
    qfNumericLanguage.Term (β ⊕ Fin m) → qfNumericLanguage.Term (β × Fin k)
  | .var (.inl b) => .var (b, i)
  | .var (.inr _) => zero
  | .func (.inl .zero) _ => zero
  | .func (.inl .max) _ => max
  | .func (.inr f) _ => Empty.elim f

private theorem lexEquiv_realize_onTupleTerm {β : Type*} {k n : ℕ} [Fact (2 ≤ n)] (hk : 0 < k)
    (v : β → Fin k → Fin n) (t : qfNumericLanguage.Term (β ⊕ Fin 0)) :
    letI : Fact (2 ≤ n ^ k) := ⟨(Fact.out : 2 ≤ n).trans (Nat.le_pow hk)⟩
    lexEquiv (fun i : Fin k => (onTupleTerm i t).realize (fun p => v p.1 p.2)) =
      t.realize (Sum.elim (fun b => lexEquiv (v b)) default) := by
  let : Fact (2 ≤ n ^ k) := ⟨(Fact.out : 2 ≤ n).trans (Nat.le_pow hk)⟩
  cases t with
  | var s =>
    cases s with
    | inl b => rfl
    | inr x => exact Fin.elim0 x
  | func f ts =>
    rcases f with f | f
    · cases f with
      | zero =>
        have hts : ts = Fin.elim0 := Subsingleton.elim _ _
        subst hts
        apply Fin.ext
        have hzero :
            (fun i : Fin k => (zero : qfNumericLanguage.Term (β × Fin k)).realize
              (fun p => v p.1 p.2)) = tupleZero (n := n) (k := k) := by
          funext i
          apply Fin.ext
          exact realize_zero_val _
        have hrhs :
            ((Term.func (L := qfNumericLanguage) (.inl EndpointFunction.zero) Fin.elim0).realize
              (Sum.elim (fun b => lexEquiv (v b)) (default : Fin 0 → Fin (n ^ k)))).val = 0 := by
          rw [← zero_eq]
          exact realize_zero_val _
        refine Eq.trans ?_ hrhs.symm
        change lexRank (fun i : Fin k =>
          (zero : qfNumericLanguage.Term (β × Fin k)).realize (fun p => v p.1 p.2)) = 0
        rw [hzero, lexRank_tupleZero]
      | max =>
        have hts : ts = Fin.elim0 := Subsingleton.elim _ _
        subst hts
        apply Fin.ext
        have hmax :
            (fun i : Fin k => (max : qfNumericLanguage.Term (β × Fin k)).realize
              (fun p => v p.1 p.2)) = tupleMax (n := n) (k := k) := by
          funext i
          apply Fin.ext
          exact realize_max_val _
        have hrhs :
            ((Term.func (L := qfNumericLanguage) (.inl EndpointFunction.max) Fin.elim0).realize
              (Sum.elim (fun b => lexEquiv (v b)) (default : Fin 0 → Fin (n ^ k)))).val =
              n ^ k - 1 := by
          rw [← max_eq]
          exact realize_max_val _
        refine Eq.trans ?_ hrhs.symm
        change lexRank (fun i : Fin k =>
          (max : qfNumericLanguage.Term (β × Fin k)).realize (fun p => v p.1 p.2)) = n ^ k - 1
        rw [hmax, lexRank_tupleMax]
    · exact Empty.elim f

/-- Coordinatewise equality of `k`-tuples of terms. -/
private noncomputable def tupleEq {α : Type*} {k : ℕ}
    (s t : Fin k → qfNumericLanguage.Term α) : qfNumericLanguage.Formula α :=
  Formula.iInf fun i : Fin k => Term.equal (s i) (t i)

/-- Strict lexicographic order on `k`-tuples of terms in `qfNumericLanguage`. -/
private noncomputable def tupleLt {α : Type*} {k : ℕ}
    (s t : Fin k → qfNumericLanguage.Term α) : qfNumericLanguage.Formula α :=
  Formula.iSup fun i : Fin k =>
    (le (t i) (s i)).not ⊓
      Formula.iInf fun j : Fin k =>
        if j < i then Term.equal (s j) (t j) else ⊤

/-- Weak lexicographic order on `k`-tuples of terms in `qfNumericLanguage`. -/
private noncomputable def tupleLe {α : Type*} {k : ℕ}
    (s t : Fin k → qfNumericLanguage.Term α) : qfNumericLanguage.Formula α :=
  (tupleLt t s).not

/-- Non-wrapping carry successor on `k`-tuples of terms in `qfNumericLanguage`. -/
private noncomputable def tupleSucc {α : Type*} {k : ℕ}
    (s t : Fin k → qfNumericLanguage.Term α) : qfNumericLanguage.Formula α :=
  Formula.iSup fun i : Fin k =>
    succ (s i) (t i) ⊓ Formula.iInf fun j : Fin k =>
      if j < i then Term.equal (s j) (t j)
      else if i < j then
        Term.equal (s j) max ⊓ Term.equal (t j) zero
      else ⊤

private theorem isQF_tupleEq {α : Type*} {k : ℕ}
    (s t : Fin k → qfNumericLanguage.Term α) : (tupleEq s t).IsQF := by
  unfold tupleEq; fo_qf

private theorem isQF_tupleLt {α : Type*} {k : ℕ}
    (s t : Fin k → qfNumericLanguage.Term α) : (tupleLt s t).IsQF := by
  unfold tupleLt; fo_qf

private theorem isQF_tupleLe {α : Type*} {k : ℕ}
    (s t : Fin k → qfNumericLanguage.Term α) : (tupleLe s t).IsQF :=
  (isQF_tupleLt t s).not

private theorem isQF_tupleSucc {α : Type*} {k : ℕ}
    (s t : Fin k → qfNumericLanguage.Term α) : (tupleSucc s t).IsQF := by
  unfold tupleSucc; fo_qf

private theorem realize_tupleEq {α : Type*} {k n : ℕ} [Fact (2 ≤ n)]
    (s t : Fin k → qfNumericLanguage.Term α) (w : α → Fin n) :
    (tupleEq s t).Realize w ↔
      lexEquiv (fun i => (s i).realize w) = lexEquiv (fun i => (t i).realize w) := by
  fo_simp [tupleEq]
  rw [← funext_iff, lexEquiv.injective.eq_iff]

private theorem realize_tupleLt {α : Type*} {k n : ℕ} [Fact (2 ≤ n)]
    (s t : Fin k → qfNumericLanguage.Term α) (w : α → Fin n) :
    (tupleLt s t).Realize w ↔
      lexRank (fun i => (s i).realize w) < lexRank (fun i => (t i).realize w) := by
  fo_simp [tupleLt, not_le, lexRank_lt_iff]
  refine exists_congr fun i => and_congr_right fun _ => forall_congr' fun j => ?_
  by_cases hji : j < i <;> simp [hji]

private theorem realize_tupleLe {α : Type*} {k n : ℕ} [Fact (2 ≤ n)]
    (s t : Fin k → qfNumericLanguage.Term α) (w : α → Fin n) :
    (tupleLe s t).Realize w ↔
      lexEquiv (fun i => (s i).realize w) ≤ lexEquiv (fun i => (t i).realize w) := by
  rw [tupleLe, Formula.realize_not, realize_tupleLt, not_lt]
  rfl

private theorem realize_tupleSucc {α : Type*} {k n : ℕ} [Fact (2 ≤ n)]
    (s t : Fin k → qfNumericLanguage.Term α) (w : α → Fin n) :
    (tupleSucc s t).Realize w ↔
      (lexEquiv (fun i => (s i).realize w)).val + 1 =
        (lexEquiv (fun i => (t i).realize w)).val := by
  change (tupleSucc s t).Realize w ↔
    lexRank (fun i => (s i).realize w) + 1 = lexRank (fun i => (t i).realize w)
  rw [eq_comm, ← isCarrySuccessor_iff]
  fo_simp [tupleSucc, IsCarrySuccessor]
  refine exists_congr fun i => and_congr (eq_comm)
    ⟨fun h => ⟨fun j hj => by simpa [hj] using h j, fun j hj => ?_⟩,
     fun ⟨hpre, hpost⟩ j => ?_⟩
  · have hh := h j
    fo_simp [not_lt.mpr (le_of_lt hj), hj] at hh
    rcases hh with ⟨hmax, hzero⟩
    exact ⟨(congrArg Fin.val hmax).trans (realize_max_val w),
      (congrArg Fin.val hzero).trans (realize_zero_val w)⟩
  · split_ifs with hji hij
    · fo_simp
      exact hpre j hji
    · fo_simp
      rcases hpost j hij with ⟨hmax, hzero⟩
      exact ⟨Fin.ext (hmax.trans (realize_max_val w).symm),
        Fin.ext (hzero.trans (realize_zero_val w).symm)⟩
    · exact Formula.realize_top.mpr trivial

private noncomputable def onBoundedFullTuple {β : Type*} (k : ℕ) :
    ∀ {m : ℕ}, qfNumericLanguage.BoundedFormula β m → qfNumericLanguage.Formula (β × Fin k)
  | _, .falsum => ⊥
  | _, .equal t₁ t₂ => tupleEq (fun i => onTupleTerm i t₁) (fun i => onTupleTerm i t₂)
  | _, .rel (.inl .le) ts =>
    tupleLe (fun i => onTupleTerm i (ts 0)) (fun i => onTupleTerm i (ts 1))
  | _, .rel (.inr .succ) ts =>
    tupleSucc (fun i => onTupleTerm i (ts 0)) (fun i => onTupleTerm i (ts 1))
  | _, .imp f₁ f₂ => (onBoundedFullTuple k f₁).imp (onBoundedFullTuple k f₂)
  | _, .all _ => ⊥

/-- Quantifier-free block translation of a `qfNumericLanguage` formula from elements of
`Fin (n ^ k)` to `k`-tuples over `Fin n`: `=` maps to coordinatewise `=`, `≤` maps to
lexicographic `≤`, `succ` maps to carry successor, `0` and `max` map to constant tuples, and
quantifiers map to `⊥` (excluded by the `IsQF` hypothesis on `realize_onFullTuple`). -/
noncomputable def onFullTuple {β : Type*} (k : ℕ) (φ : qfNumericLanguage.Formula β) :
    qfNumericLanguage.Formula (β × Fin k) :=
  onBoundedFullTuple k φ

/-- `QFNumeric.onFullTuple` preserves quantifier-freeness. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem isQF_onFullTuple {β : Type*} {k : ℕ} {φ : qfNumericLanguage.Formula β}
    (h : φ.IsQF) : (onFullTuple k φ).IsQF := by
  rw [onFullTuple]
  induction h with
  | falsum =>
    rw [onBoundedFullTuple]
    exact BoundedFormula.isQF_bot
  | of_isAtomic ha =>
    cases ha with
    | equal t₁ t₂ =>
      change (onBoundedFullTuple k (.equal t₁ t₂)).IsQF
      rw [onBoundedFullTuple]
      exact isQF_tupleEq _ _
    | rel R ts =>
      change (onBoundedFullTuple k (.rel R ts)).IsQF
      rcases R with R | R <;> cases R <;> rw [onBoundedFullTuple]
      · exact isQF_tupleLe _ _
      · exact isQF_tupleSucc _ _
  | imp _ _ ih₁ ih₂ =>
    rw [onBoundedFullTuple]
    exact ih₁.imp ih₂

/-- **Quantifier-free `qfNumericLanguage` block translation preserves truth** on `Fin n` for `2 ≤ n`
and positive tuple dimension `0 < k`. -/
theorem realize_onFullTuple {β : Type*} {k n : ℕ} {φ : qfNumericLanguage.Formula β}
    (h : φ.IsQF) [Fact (2 ≤ n)] (v : β → Fin k → Fin n) (hk : 0 < k) :
    (onFullTuple k φ).Realize (fun p => v p.1 p.2) ↔
      letI : Fact (2 ≤ n ^ k) := ⟨(Fact.out : 2 ≤ n).trans (Nat.le_pow hk)⟩
      φ.Realize (fun b => lexEquiv (v b)) := by
  let : Fact (2 ≤ n ^ k) := ⟨(Fact.out : 2 ≤ n).trans (Nat.le_pow hk)⟩
  rw [onFullTuple]
  induction h with
  | falsum =>
    rw [onBoundedFullTuple]
    rfl
  | of_isAtomic ha =>
    cases ha with
    | equal t₁ t₂ =>
      change (onBoundedFullTuple k (.equal t₁ t₂)).Realize (fun p => v p.1 p.2) ↔
        t₁.realize (Sum.elim (fun b => lexEquiv (v b)) default) =
          t₂.realize (Sum.elim (fun b => lexEquiv (v b)) default)
      rw [onBoundedFullTuple, realize_tupleEq, lexEquiv_realize_onTupleTerm hk v t₁,
        lexEquiv_realize_onTupleTerm hk v t₂]
    | rel R ts =>
      rcases R with R | R <;> cases R
      · refine Iff.trans ?_ (realize_boundedFormula_le ts (fun b => lexEquiv (v b))).symm
        change (onBoundedFullTuple k (.rel (.inl .le) ts)).Realize (fun p => v p.1 p.2) ↔ _
        rw [onBoundedFullTuple, realize_tupleLe, lexEquiv_realize_onTupleTerm hk v (ts 0),
          lexEquiv_realize_onTupleTerm hk v (ts 1)]
      · refine Iff.trans ?_ (realize_boundedFormula_succ ts (fun b => lexEquiv (v b))).symm
        change (onBoundedFullTuple k (.rel (.inr .succ) ts)).Realize (fun p => v p.1 p.2) ↔ _
        rw [onBoundedFullTuple, realize_tupleSucc, lexEquiv_realize_onTupleTerm hk v (ts 0),
          lexEquiv_realize_onTupleTerm hk v (ts 1)]
  | imp _ _ ih₁ ih₂ =>
    rw [onBoundedFullTuple]
    simp only [Formula.realize_imp, ih₁, ih₂]

end Cslib.Logic.FO.Ordered.QFNumeric
