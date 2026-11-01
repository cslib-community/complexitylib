/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.Prefixes
import Complexity.Algorithms.MatrixMultiplication.Schonhage.Orders
import Mathlib.Data.List.OfFn

/-!
# Finite leaf partitions of sparse query prefixes

Every valid prefix has a compatible completion. Its possible full leaves partition
among its permitted children. The finite potential counts those leaves at each
remaining depth; no execution or time bound is assumed by this finite specification.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery

open Finset Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- All original full tensor leaves extending a prefix within the original order cap. -/
@[expose] def possibleLeaves {L : ℕ} (η : OutStr L) (t : ℕ)
    (xs : List Term) : Finset (Leaf L) :=
  univ.filter fun τ => Good η t (List.ofFn τ) ∧ xs.IsPrefix (List.ofFn τ)

@[simp] theorem mem_possibleLeaves {L t : ℕ} {η : OutStr L} {xs : List Term} {τ : Leaf L} :
    τ ∈ possibleLeaves η t xs ↔ Good η t (List.ofFn τ) ∧ xs.IsPrefix (List.ofFn τ) := by
  simp [possibleLeaves]

/-- Valid full tasks make every earlier prefix valid. -/
theorem Good.of_prefix {L t : ℕ} {η : OutStr L} {xs ys : List Term}
    (hy : Good η t ys) (hp : xs.IsPrefix ys) : Good η t xs := by
  obtain ⟨zs, rfl⟩ := hp
  obtain ⟨hlen, hcompat, hused⟩ := hy
  simp only [List.length_append] at hlen
  refine ⟨by omega,
    (compatible_append η 0 xs zs).mp hcompat |>.1, ?_⟩
  rw [usedFrom_append] at hused
  omega

private def privateTail {L : ℕ} (η : OutStr L) (k n : ℕ) : List Term :=
  List.ofFn fun i : Fin n => (outAt η (k + i.val)).privateTerm

private theorem privateTail_succ {L : ℕ} (η : OutStr L) (k n : ℕ) :
    privateTail η k (n + 1) = (outAt η k).privateTerm :: privateTail η (k + 1) n := by
  simp only [privateTail, List.ofFn_succ, Fin.val_zero, Nat.add_zero, Fin.val_succ]
  congr 2
  funext i
  congr 2
  omega

private theorem privateTail_compatible {L : ℕ} (η : OutStr L) (k n : ℕ) :
    Compatible η k (privateTail η k n) := by
  induction n generalizing k with
  | zero => simp [privateTail, Compatible]
  | succ n ih =>
    rw [privateTail_succ]
    exact ⟨(Term.contributes_iff _ _).mpr (Or.inr rfl), ih _⟩

private theorem privateTail_used {L : ℕ} (η : OutStr L) (k n : ℕ) :
    usedFrom η k (privateTail η k n) = 0 := by
  induction n generalizing k with
  | zero => simp [privateTail, usedFrom]
  | succ n ih =>
    rw [privateTail_succ, usedFrom, ih]
    have hp := OutVar.privateTerm_eq_P0_iff (outAt η k)
    by_cases hi : (outAt η k).IsInner
    · simp [hi, hp.mpr hi]
    · simp [hi]

/-- Filling unprocessed coordinates with their existing private term gives a real leaf. -/
theorem possibleLeaves_nonempty {L t : ℕ} {η : OutStr L} {xs : List Term}
    (hx : Good η t xs) : (possibleLeaves η t xs).Nonempty := by
  let ys := xs ++ privateTail η xs.length (L - xs.length)
  have hlen : ys.length = L := by
    simp only [ys, List.length_append, privateTail, List.length_ofFn]
    exact Nat.add_sub_of_le hx.1
  let τ : Leaf L := fun i => ys.get (Fin.cast hlen.symm i)
  have hτ : List.ofFn τ = ys :=
    (List.ofFn_congr hlen ys.get).symm.trans (List.ofFn_get ys)
  refine ⟨τ, mem_possibleLeaves.mpr ?_⟩
  rw [hτ]
  refine ⟨⟨hlen.le, ?_, ?_⟩, ⟨_, rfl⟩⟩
  · exact (compatible_append η 0 xs _).mpr ⟨hx.2.1, by
      simpa only [Nat.zero_add] using privateTail_compatible η xs.length (L - xs.length)⟩
  · dsimp only [ys]
    rw [usedFrom_append, Nat.zero_add, privateTail_used, Nat.add_zero]
    exact hx.2.2

/-- All valid full leaves are possible at the initial empty prefix. -/
@[simp] theorem possibleLeaves_nil {L : ℕ} (η : OutStr L) (t : ℕ) :
    possibleLeaves η t [] = univ.filter fun τ : Leaf L => Good η t (List.ofFn τ) := by
  ext τ
  simp

/-- A complete valid prefix has just its original full leaf. -/
theorem possibleLeaves_ofFn {L t : ℕ} {η : OutStr L} (τ : Leaf L)
    (hτ : Good η t (List.ofFn τ)) : possibleLeaves η t (List.ofFn τ) = {τ} := by
  ext σ
  rw [mem_possibleLeaves, mem_singleton]
  constructor
  · intro h
    apply List.ofFn_injective
    exact (h.2.eq_of_length (by simp)).symm
  · rintro rfl
    exact ⟨hτ, List.prefix_rfl⟩

/-- Different appended terms have disjoint possible-leaf sets. -/
theorem possibleLeaves_disjoint {L t : ℕ} {η : OutStr L} (xs : List Term)
    {a b : Term} (hab : a ≠ b) :
    Disjoint (possibleLeaves η t (xs ++ [a])) (possibleLeaves η t (xs ++ [b])) := by
  rw [disjoint_left]
  intro τ ha hb
  have heqa := List.prefix_iff_eq_take.mp (mem_possibleLeaves.mp ha).2
  have heqb := List.prefix_iff_eq_take.mp (mem_possibleLeaves.mp hb).2
  have heq : xs ++ [a] = xs ++ [b] := by
    simp only [List.length_append, List.length_singleton] at heqa heqb
    exact heqa.trans heqb.symm
  have htail := List.append_cancel_left heq
  exact hab (by simpa using htail)

/-- Every possible leaf extends the prefix by exactly one permitted child term. -/
theorem possibleLeaves_child_iff {L t : ℕ} {η : OutStr L} {xs : List Term}
    (hx : Good η t xs) (hk : xs.length < L) (τ : Leaf L) :
    τ ∈ possibleLeaves η t xs ↔
      ∃ lam ∈ allowedTerms η t xs, τ ∈ possibleLeaves η t (xs ++ [lam]) := by
  constructor
  · rintro h
    obtain ⟨hτ, zs, hzs⟩ := mem_possibleLeaves.mp h
    have hz : zs ≠ [] := by
      intro hh
      have hlength := congrArg List.length hzs
      simp only [hh, List.append_nil, List.length_ofFn] at hlength
      omega
    obtain ⟨lam, tail, rfl⟩ := List.exists_cons_of_ne_nil hz
    have hp : (xs ++ [lam]).IsPrefix (List.ofFn τ) :=
      ⟨tail, by simpa only [List.append_assoc, List.singleton_append] using hzs⟩
    exact ⟨lam, (good_append_iff hx hk lam).mp (hτ.of_prefix hp),
      mem_possibleLeaves.mpr ⟨hτ, hp⟩⟩
  · rintro ⟨lam, _, hτ⟩
    obtain ⟨hg, hp⟩ := mem_possibleLeaves.mp hτ
    exact mem_possibleLeaves.mpr ⟨hg, (List.prefix_append _ _).trans hp⟩

/-- The children partition exactly the original possible leaves. -/
theorem possibleLeaves_eq_biUnion {L t : ℕ} {η : OutStr L} {xs : List Term}
    (hx : Good η t xs) (hk : xs.length < L) :
    possibleLeaves η t xs = (allowedTerms η t xs).biUnion
      (fun lam => possibleLeaves η t (xs ++ [lam])) := by
  ext τ
  rw [possibleLeaves_child_iff hx hk, mem_biUnion]

/-- Partitioning preserves the number of actual possible full leaves. -/
theorem card_possibleLeaves_children {L t : ℕ} {η : OutStr L} {xs : List Term}
    (hx : Good η t xs) (hk : xs.length < L) :
    (possibleLeaves η t xs).card = ∑ lam ∈ allowedTerms η t xs,
      (possibleLeaves η t (xs ++ [lam])).card := by
  rw [possibleLeaves_eq_biUnion hx hk, card_biUnion]
  intro a _ b _ hab
  exact possibleLeaves_disjoint xs hab

/-- Partitioning preserves every additive semantic value of possible leaves. -/
theorem sum_possibleLeaves_children {G : Type*} [AddCommMonoid G] {L t : ℕ}
    {η : OutStr L} {xs : List Term} (hx : Good η t xs) (hk : xs.length < L)
    (f : Leaf L → G) :
    ∑ τ ∈ possibleLeaves η t xs, f τ = ∑ lam ∈ allowedTerms η t xs,
      ∑ τ ∈ possibleLeaves η t (xs ++ [lam]), f τ := by
  rw [possibleLeaves_eq_biUnion hx hk, sum_biUnion]
  intro a _ b _ hab
  exact possibleLeaves_disjoint xs hab

/-- A task's finite work potential counts all remaining levels of its possible full leaves. -/
@[expose] def potential {L : ℕ} (η : OutStr L) (t : ℕ) (xs : List Term) : ℕ :=
  (L - xs.length + 1) * (possibleLeaves η t xs).card

/-- The complete child family has strictly less finite work potential than its valid parent. -/
theorem sum_potential_children_lt {L t : ℕ} {η : OutStr L} {xs : List Term}
    (hx : Good η t xs) (hk : xs.length < L) :
    (∑ lam ∈ allowedTerms η t xs, potential η t (xs ++ [lam])) < potential η t xs := by
  have hc := card_possibleLeaves_children hx hk
  have hp := (possibleLeaves_nonempty hx).card_pos
  have hdepth : L - (xs.length + 1) + 1 = L - xs.length := by omega
  simp only [potential, List.length_append, List.length_singleton, hdepth,
    ← mul_sum, ← hc]
  exact Nat.mul_lt_mul_of_pos_right (by omega) hp

/-- Ordered native child sums agree with the duplicate-free finite label partition. -/
theorem sum_children_eq {G : Type*} [AddCommMonoid G] {L t : ℕ}
    {η : OutStr L} {xs : List Term} (hx : usedFrom η 0 xs ≤ t) (f : List Term → G) :
    ((children η t xs).map f).sum = ∑ lam ∈ allowedTerms η t xs, f (xs ++ [lam]) := by
  rw [← List.sum_toFinset f (children_nodup η t xs), children_toFinset hx, sum_image]
  intro a _ b _ hab
  simpa only [List.cons.injEq, and_true] using List.append_cancel_left hab

/-- Actual native child order preserves the count of possible full leaves. -/
theorem sum_card_possibleLeaves_children {L t : ℕ} {η : OutStr L} {xs : List Term}
    (hx : Good η t xs) (hk : xs.length < L) :
    ((children η t xs).map fun ys => (possibleLeaves η t ys).card).sum =
      (possibleLeaves η t xs).card := by
  rw [sum_children_eq hx.2.2]
  exact (card_possibleLeaves_children hx hk).symm

/-- Actual native child order preserves every additive value attached to full leaves. -/
theorem sum_values_children {G : Type*} [AddCommMonoid G] {L t : ℕ}
    {η : OutStr L} {xs : List Term} (hx : Good η t xs) (hk : xs.length < L)
    (f : Leaf L → G) :
    ((children η t xs).map fun ys => ∑ τ ∈ possibleLeaves η t ys, f τ).sum =
      ∑ τ ∈ possibleLeaves η t xs, f τ := by
  rw [sum_children_eq hx.2.2]
  exact (sum_possibleLeaves_children hx hk f).symm

/-- Replacing a task by its actual ordered child list strictly decreases finite work. -/
theorem sum_potential_children_list_lt {L t : ℕ} {η : OutStr L} {xs : List Term}
    (hx : Good η t xs) (hk : xs.length < L) :
    ((children η t xs).map (potential η t)).sum < potential η t xs := by
  rw [sum_children_eq hx.2.2]
  exact sum_potential_children_lt hx hk

/-- The actual empty root has the original full-depth leaf-count potential. -/
@[simp] theorem potential_nil {L : ℕ} (η : OutStr L) (t : ℕ) :
    potential η t [] = (L + 1) * (possibleLeaves η t []).card := by
  simp [potential]

/-- Every finite task has at least one potential unit, including an actual full leaf. -/
theorem potential_pos {L t : ℕ} {η : OutStr L} {xs : List Term}
    (hx : Good η t xs) : 0 < potential η t xs :=
  Nat.mul_pos (by omega) (possibleLeaves_nonempty hx).card_pos

/-- The finite work potential also bounds the number of actual pending task records. -/
theorem length_le_sum_potential {L t : ℕ} {η : OutStr L} (tasks : List (List Term))
    (hgood : ∀ xs ∈ tasks, Good η t xs) :
    tasks.length ≤ (tasks.map (potential η t)).sum := by
  induction tasks with
  | nil => simp
  | cons xs tasks ih =>
    have hp := potential_pos (hgood xs (by simp))
    have ht := ih (fun ys hy => hgood ys (by simp [hy]))
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery
