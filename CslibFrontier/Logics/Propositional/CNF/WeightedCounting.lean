/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.WeightedAffine
public import CslibFrontier.Logics.Propositional.CNF.WeightedGlobal

/-!
# All-cases mathematical weighted counting plan

The mathematical assembly in [ChenJiangZhu2027], Section 7.1, Theorem 7.1,
PDF pp. 23–24. Direct cases use no queries; positive deficient computed rank uses
exactly two ordinary CNFs on the selected original capped rows. The input count
retains all declared variables. Finite subset listing remains noncomputable and
no encoded construction-time, counting-time or space guarantee is asserted.
-/

public noncomputable section

namespace Cslib.Logic.PL.WeightedRow

open LinearSystem

variable {n d : ℕ}

open Classical in
/-- Count on the complete normalized input, including rejection and deleted true rows. -/
@[expose] def normalizedCount (ns : List (Normalized n d)) : ℕ :=
  Fintype.card {σ : Fin n → Bool // ∀ N ∈ ns, N.Holds σ}

/-- Uniform polynomial clause budget, independent of the original number of rows. -/
@[expose] def countingBudget (n d : ℕ) : ℕ :=
  (d + 2) * (2 * n + 1) ^ (d + 1) + 2 * (n * ((d + 1) * (n + 1) ^ d))

/-- Either a direct answer, or two ordinary queries with a certified variable/width/size budget. -/
inductive CountingPlan (n d : ℕ) where
  | direct (answer : ℕ)
  | queries (k : ℕ) (query : Bool → CNF (Fin n ⊕ Fin k))
      (variableBound : n + k ≤ 2 * n - 2)
      (width : ∀ β c, c ∈ query β → c.length ≤ d + 2)
      (clauses : ∀ β, (query β).length ≤ countingBudget n d)

open Classical in
/-- Interpret ordinary CNF counts; direct answers make zero oracle calls. -/
@[expose] def CountingPlan.count : CountingPlan n d → ℕ
  | .direct a => a
  | .queries _ q _ _ _ =>
      Fintype.card {σ // (q false).eval σ = true} -
        Fintype.card {σ // (q true).eval σ = true}

/-- Full computed rank makes the actual Boolean solution set a subsingleton. -/
theorem normalized_full_unique (ns : List (Normalized n d))
    (hf : (cappedBasis ns).length = n) (x y : Fin n → Bool)
    (hx : ∀ N ∈ ns, N.Holds x) (hy : ∀ N ∈ ns, N.Holds y) : x = y := by
  have hx' := (cappedMatrix_rat_iff ns x).mpr ((cappedRows_iff ns x).mp hx).2
  have hy' := (cappedMatrix_rat_iff ns y).mpr ((cappedRows_iff ns y).mp hy).2
  have he := rectangular_unique n (cappedMatrix ns) (cappedRhs ns) hf _ _ hx' hy'
  funext j
  have hj := congrFun he j
  cases hxj : x j <;> cases hyj : y j <;> simp_all

/-- The full-rank direct count is the computed candidate Booleanity test, with rejection. -/
theorem normalized_full_count (ns : List (Normalized n d))
    (hr : Normalized.reject ∉ ns) (hf : (cappedBasis ns).length = n) :
    normalizedCount ns =
      if rectangularBoolean n (cappedMatrix ns) (cappedRhs ns) then 1 else 0 := by
  classical
  let S := {σ : Fin n → Bool // ∀ N ∈ ns, N.Holds σ}
  have hs : Subsingleton S := ⟨fun x y => Subtype.ext
    (normalized_full_unique ns hf x y x.property y.property)⟩
  have he : rectangularBoolean n (cappedMatrix ns) (cappedRhs ns) = true ↔ Nonempty S := by
    rw [rectangularBoolean_correct n (cappedMatrix ns) (cappedRhs ns) hf]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨⟨x, (cappedRows_iff ns x).mpr ⟨hr, (cappedMatrix_iff ns x).mp hx⟩⟩⟩
    · rintro ⟨⟨x, hx⟩⟩
      exact ⟨x, (cappedMatrix_iff ns x).mpr ((cappedRows_iff ns x).mp hx).2⟩
  change Fintype.card S = _
  split_ifs with hb
  · have : Nonempty S := he.mp hb
    let : Unique S :=
      { default := Classical.choice inferInstance, uniq := fun _ => Subsingleton.elim _ _ }
    exact Fintype.card_unique
  · have : IsEmpty S := ⟨fun x => hb (he.mpr ⟨x⟩)⟩
    exact Fintype.card_eq_zero

/-- Dispatch all computed cases. No rank, basis, consistency or solution advice is supplied.
Small declared dimension is enumerated directly; every other direct answer follows the
source's rejection, empty, full-rank or rank-zero branch. -/
def countingPlan (ns : List (Normalized n d)) :
    {p : CountingPlan n d // p.count = normalizedCount ns} := by
  classical
  by_cases small : n ≤ 1
  · exact ⟨.direct (normalizedCount ns), rfl⟩
  by_cases reject : Normalized.reject ∈ ns
  · refine ⟨.direct 0, ?_⟩
    symm
    apply Fintype.card_eq_zero_iff.mpr
    exact ⟨fun x => x.property _ reject⟩
  by_cases empty : cappedRows ns = []
  · refine ⟨.direct (2 ^ n), ?_⟩
    change _ = Fintype.card _
    symm
    calc
      _ = Fintype.card (Fin n → Bool) := Fintype.card_congr
        (Equiv.subtypeUnivEquiv fun σ => (cappedRows_iff ns σ).mpr ⟨reject, by simp [empty]⟩)
      _ = _ := by simp [CountingPlan.count]
  by_cases consistent : rectangularConsistent n (cappedMatrix ns) (cappedRhs ns) = true
  · by_cases full : (cappedBasis ns).length = n
    · exact ⟨.direct (if rectangularBoolean n (cappedMatrix ns) (cappedRhs ns) then 1 else 0),
        (normalized_full_count ns reject full).symm⟩
    by_cases zero : (cappedBasis ns).length = 0
    · refine ⟨.direct (2 ^ n), ?_⟩
      change _ = Fintype.card _
      symm
      calc
        _ = Fintype.card (Fin n → Bool) := Fintype.card_congr
          (Equiv.subtypeUnivEquiv fun σ => (normalized_selected_iff ns σ).mpr
            ⟨reject, consistent, fun i => by have := i.isLt; omega⟩)
        _ = _ := by simp [CountingPlan.count]
    have bound := cappedBasis_length ns
    let k := (cappedBasis ns).length - 1
    have hk : k + 1 = (cappedBasis ns).length := by omega
    let R : Fin (k + 1) → Row (Fin n) d := fun i =>
      selectedCappedRow ns (Fin.cast hk i)
    have equiv (σ : Fin n → Bool) :
        (∀ N ∈ ns, N.Holds σ) ↔ ∀ j, (R j).value σ = (R j).demand := by
      rw [normalized_selected_iff]
      simp only [reject, consistent, not_false_eq_true, true_and]
      exact ⟨fun h j => h (Fin.cast hk j), fun h i => h (Fin.cast hk.symm i)⟩
    refine ⟨.queries k (globalQuery R) (by omega) (globalQuery_width R) ?_, ?_⟩
    · intro β
      have hp := globalQuery_polynomial R β
      simp only [Fintype.card_fin] at hp
      exact hp.trans (Nat.add_le_add_left
        (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ (by omega : k + 1 ≤ n))) _)
    · change _ = Fintype.card _
      simp only [CountingPlan.count]
      rw [← global_counting_identity R]
      exact Fintype.card_congr (Equiv.subtypeEquivRight fun σ => (equiv σ).symm)
  · refine ⟨.direct 0, ?_⟩
    symm
    apply Fintype.card_eq_zero_iff.mpr
    refine ⟨fun x => consistent ?_⟩
    exact ((normalized_selected_iff ns x.val).mp x.property).2.1

open Classical in
/-- Normalize the actual repeated-occurrence input before dispatching every case. -/
def originalCountingPlan {t : ℕ} {m : Fin t → ℕ} (R : (j : Fin t) → Occurrences n (m j))
    (hd : ∀ j, (R j).demand ≤ d) :
    {p : CountingPlan n d // p.count =
      Fintype.card {σ : Fin n → Bool // ∀ j, ((R j).value σ : ℤ) = (R j).target}} := by
  classical
  let ns := (List.finRange t).map fun j => (R j).normalize d (hd j)
  refine ⟨(countingPlan ns).val, (countingPlan ns).property.trans ?_⟩
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro σ
  simp [ns, Occurrences.normalize_iff]

end Cslib.Logic.PL.WeightedRow
