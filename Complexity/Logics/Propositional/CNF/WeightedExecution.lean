/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.WeightedCounting
public import Complexity.Logics.Propositional.CNF.WeightedExecutable
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Executable original-input weighted counting

Execution of the normalization and all-cases dispatch in [ChenJiangZhu2027],
Section 7.1, Theorem 7.1, PDF pp. 23–24. The existing integer Gram/rectangular
solver supplies every rank, consistency and candidate test. Only dimension at
most one is enumerated. No composed binary time or space bound is asserted.
-/

public section

namespace Cslib.Logic.PL.WeightedRow

open scoped BigOperators
open LinearSystem

private theorem upperList_ordered {n d : ℕ} (R : Row (Fin n) d)
    (c : Clause (Fin n)) (hc : c ∈ upperList R) :
    c.Pairwise (fun a b => a.1 < b.1) := by
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hc
  have hs := (mem_boundedLists.mp (List.mem_filter.mp ht).1).1
  exact List.Pairwise.map _ (fun _ _ h => h)
    (((List.sortedLT_finRange n).pairwise.sublist List.filter_sublist).sublist hs)

private theorem executableBase_width {n d h : ℕ} (R : Fin (h + 1) → Row (Fin n) d)
    (c : Clause (Fin n)) (hc : c ∈ executableBase R) : c.length ≤ d + 1 := by
  obtain ⟨j, _, hj⟩ := List.mem_flatMap.mp (List.mem_dedup.mp hc)
  exact upperList_width (R j) c hj

/-- Canonical variable ordering makes signed-set keys injective on the actual output. -/
theorem executableBase_keys_injective {n d h : ℕ} (R : Fin (h + 1) → Row (Fin n) d) :
    Set.InjOn List.toFinset (↑((executableBase R).toFinset) : Set (Clause (Fin n))) := by
  let rel := fun a b : Literal (Fin n) => a.1 < b.1
  let : Std.Antisymm rel := ⟨fun _ _ hab hba => False.elim (lt_asymm hab hba)⟩
  let : Std.Irrefl rel := ⟨fun _ => lt_irrefl _⟩
  intro a ha b hb he
  have ordered (c) (hc : c ∈ (executableBase R).toFinset) : c.Pairwise rel := by
    obtain ⟨j, _, hj⟩ := List.mem_flatMap.mp
      (List.mem_dedup.mp (List.mem_toFinset.mp hc))
    exact upperList_ordered (R j) c hj
  apply (ordered a ha).eq_of_mem_iff (ordered b hb)
  intro l
  simp only [← List.mem_toFinset, he]

/-- The sharp signed-subset global budget applies to executable deduplication too. -/
theorem executableBase_length {n d h : ℕ} (R : Fin (h + 1) → Row (Fin n) d) :
    (executableBase R).length ≤ ∑ k ∈ Finset.range (d + 2), (2 * n).choose k := by
  let K := (executableBase R).toFinset.image List.toFinset
  let U := (Finset.range (d + 2)).biUnion fun k =>
    (Finset.univ : Finset (Literal (Fin n))).powersetCard k
  have hs : K ⊆ U := by
    intro s hs
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hs
    have hw := (List.toFinset_card_le c).trans
      (executableBase_width R c (List.mem_toFinset.mp hc))
    exact Finset.mem_biUnion.mpr ⟨c.toFinset.card,
      Finset.mem_range.mpr (by omega),
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩⟩
  calc
    _ = (executableBase R).toFinset.card :=
      (List.toFinset_card_of_nodup (List.nodup_dedup _)).symm
    _ = K.card := (Finset.card_image_of_injOn (executableBase_keys_injective R)).symm
    _ ≤ U.card := Finset.card_le_card hs
    _ ≤ ∑ k ∈ Finset.range (d + 2),
        ((Finset.univ : Finset (Literal (Fin n))).powersetCard k).card :=
      Finset.card_biUnion_le
    _ = _ := by simp [Literal, Nat.mul_comm]

/-- Explicit row-independent polynomial for the emitted upper base. -/
theorem executableBase_polynomial {n d h : ℕ} (R : Fin (h + 1) → Row (Fin n) d) :
    (executableBase R).length ≤ (d + 2) * (2 * n + 1) ^ (d + 1) := by
  apply (executableBase_length R).trans
  calc
    _ ≤ ∑ _k ∈ Finset.range (d + 2), (2 * n + 1) ^ (d + 1) := by
      apply Finset.sum_le_sum
      intro k hk
      exact (Nat.choose_le_pow _ _).trans
        ((Nat.pow_le_pow_left (by omega : 2 * n ≤ 2 * n + 1) k).trans
          (Nat.pow_le_pow_right (by omega) (by have := Finset.mem_range.mp hk; omega)))
    _ = _ := by simp

/-- The executed query has the same sharp polynomial budget as the mathematical writer. -/
theorem executableQuery_polynomial {n d h : ℕ} (R : Fin (h + 1) → Row (Fin n) d)
    (β : Bool) : (executableQuery R β).length ≤
      (d + 2) * (2 * n + 1) ^ (d + 1) + 2 * ((h + 1) * ((d + 1) * (n + 1) ^ d)) := by
  have ht (j : Fin (h + 1)) :
      (attainmentList (R j)).length ≤ (d + 1) * (n + 1) ^ d := by
    apply (attainmentList_length (R j)).trans
    apply Nat.mul_le_mul_left
    exact Nat.pow_le_pow_left (by
      have := List.length_filter_le (fun i => decide (i ∈ (R j).support)) (List.finRange n)
      simpa only [supportList, List.length_finRange] using Nat.add_le_add_right this 1) d
  apply (TwoBoundary.query_length (executableBase R) (fun j => attainmentList (R j)) β).trans
  apply Nat.add_le_add (executableBase_polynomial R)
  apply Nat.mul_le_mul_left
  simpa using Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => ht j)

/-- Execute satisfaction testing on normalized rows, retaining rejection. -/
@[expose] def normalizedTest {n d : ℕ} (ns : List (Normalized n d))
    (σ : Fin n → Bool) : Bool :=
  ns.all fun N => match N with
    | .reject => false
    | .trivial => true
    | .row R => decide (R.value σ = R.demand)

/-- The executable test has exactly the reviewed normalized semantics. -/
theorem normalizedTest_iff {n d : ℕ} (ns : List (Normalized n d)) (σ : Fin n → Bool) :
    normalizedTest ns σ = true ↔ ∀ N ∈ ns, N.Holds σ := by
  simp only [normalizedTest, List.all_eq_true]
  apply forall_congr'
  intro N
  cases N <;> simp [Normalized.Holds]

/-- Explicit finite enumeration, used only when the declared dimension is at most one. -/
@[expose] def smallCount {n d : ℕ} (ns : List (Normalized n d)) : ℕ :=
  ((Finset.univ : Finset (Fin n → Bool)).filter fun σ => normalizedTest ns σ).card

/-- Small enumeration computes the count on every declared variable. -/
theorem smallCount_correct {n d : ℕ} (ns : List (Normalized n d)) :
    smallCount ns = normalizedCount ns := by
  classical
  simp only [smallCount, normalizedCount, Fintype.card_subtype, normalizedTest_iff]

/-- Detect rejection by constructor inspection, without comparing function-valued rows. -/
@[expose] def rejected {n d : ℕ} (ns : List (Normalized n d)) : Bool :=
  ns.any fun N => match N with | .reject => true | _ => false

/-- Constructor inspection agrees with rejection membership. -/
theorem rejected_iff {n d : ℕ} (ns : List (Normalized n d)) :
    rejected ns = true ↔ Normalized.reject ∈ ns := by
  induction ns with
  | nil => simp [rejected]
  | cons N ns ih => cases N <;> simp_all [rejected]

/-- Execute every branch from the actual normalized input and computed solver tests. -/
def executableCountingPlan {n d : ℕ} (ns : List (Normalized n d)) :
    {p : CountingPlan n d // p.count = normalizedCount ns} := by
  by_cases small : n ≤ 1
  · exact ⟨.direct (smallCount ns), smallCount_correct ns⟩
  by_cases hr : rejected ns = true
  · have reject := (rejected_iff ns).mp hr
    refine ⟨.direct 0, ?_⟩
    classical
    symm
    apply Fintype.card_eq_zero_iff.mpr
    exact ⟨fun x => x.property _ reject⟩
  have reject : Normalized.reject ∉ ns := fun h => hr ((rejected_iff ns).mpr h)
  by_cases he : (cappedRows ns).length = 0
  · have empty := List.length_eq_zero_iff.mp he
    refine ⟨.direct (2 ^ n), ?_⟩
    classical
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
      classical
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
    refine ⟨.queries k (executableQuery R) (by omega) (executableQuery_width R) ?_, ?_⟩
    · intro β
      have hp := executableQuery_polynomial R β
      exact hp.trans (Nat.add_le_add_left
        (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ (by omega : k + 1 ≤ n))) _)
    · classical
      change _ = Fintype.card _
      simp only [CountingPlan.count]
      rw [← executable_counting_identity R]
      exact Fintype.card_congr (Equiv.subtypeEquivRight fun σ => (equiv σ).symm)
  · refine ⟨.direct 0, ?_⟩
    classical
    symm
    apply Fintype.card_eq_zero_iff.mpr
    refine ⟨fun x => consistent ?_⟩
    exact ((normalized_selected_iff ns x.val).mp x.property).2.1


/-- Normalize actual repeated signed occurrences, then execute the entire counting plan.
The only supplied bound is on computed normalized demand; no rank/basis/output advice is used. -/
def executableOriginalCountingPlan {n d m t : ℕ} (R : Fin t → Occurrences n m)
    (hd : ∀ j, (R j).demand ≤ d) :
    {p : CountingPlan n d // p.count =
      Fintype.card {σ : Fin n → Bool // ∀ j, ((R j).value σ : ℤ) = (R j).target}} := by
  let ns := (List.finRange t).map fun j => (R j).normalize d (hd j)
  refine ⟨(executableCountingPlan ns).val, (executableCountingPlan ns).property.trans ?_⟩
  classical
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro σ
  simp [ns, Occurrences.normalize_iff]

/-- Execution and the reviewed mathematical dispatcher have the same full-input count.
Their query lists may differ in ordering; correspondence is semantic. -/
theorem executableOriginalCountingPlan_count {n d m t : ℕ}
    (R : Fin t → Occurrences n m) (hd : ∀ j, (R j).demand ≤ d) :
    (executableOriginalCountingPlan R hd).val.count = (originalCountingPlan R hd).val.count :=
  (executableOriginalCountingPlan R hd).property.trans (originalCountingPlan R hd).property.symm

end Cslib.Logic.PL.WeightedRow
