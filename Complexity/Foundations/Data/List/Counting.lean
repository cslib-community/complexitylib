/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger, Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.List.Basic

/-!
# List counts and scan bounds

## Main results

* `List.length_flatMap_le`: blocks of bounded length have bounded total length.
* `List.decide_mem_eq_any`: membership as a scan of the list.
* `List.countP_and_not_add_countP_and`: members satisfying one predicate split by whether
  they satisfy another.
* `List.existsUnique_fin_of_countP_eq_one`, `List.existsUnique_mem_of_countP_eq_one`: a Boolean
  predicate with `countP` equal to `1` holds at a unique list index and at a unique member.
-/

@[expose] public section

/-- Blocks of at most `k` elements each, one for each element of `l`, have at most `|l| k`
elements in total. -/
theorem List.length_flatMap_le {α β : Type*} {l : List α} {f : α → List β} {k : ℕ}
    (h : ∀ a ∈ l, (f a).length ≤ k) : (l.flatMap f).length ≤ l.length * k := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := h a List.mem_cons_self
    have hl := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    omega

/-- Membership in a list as a scan of the list, the form in which polynomial-time membership tests
are certified. -/
theorem List.decide_mem_eq_any {α : Type*} [DecidableEq α] (a : α) (l : List α) :
    decide (a ∈ l) = l.any fun u => decide (u = a) := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq, List.any_eq_true]
  simp

/-- Partitioning the elements of a list satisfying `p` by whether they satisfy `q`. -/
theorem List.countP_and_not_add_countP_and {α : Type*} (p q : α → Prop) [DecidablePred p]
    [DecidablePred q] (l : List α) :
    l.countP (fun a => ¬ q a ∧ p a) + l.countP (fun a => p a ∧ q a) = l.countP (fun a => p a) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.countP_cons, List.countP_cons, List.countP_cons]
    by_cases hp : p a <;> by_cases hq : q a <;>
      simp only [hp, hq, not_true_eq_false, not_false_eq_true, and_true, and_false,
        decide_true, decide_false, Bool.false_eq_true, ↓reduceIte] <;> omega

/-- If `l.countP p = 1`, there is a unique index `i : Fin l.length` with `p l[i] = true`. -/
theorem List.existsUnique_fin_of_countP_eq_one {α : Type*} {l : List α} {p : α → Bool}
    (h : l.countP p = 1) : ∃! i : Fin l.length, p l[i] = true := by
  induction l with
  | nil =>
    rw [List.countP_nil] at h
    omega
  | cons a tl ih =>
    cases hpa : p a with
    | true =>
      rw [List.countP_cons_of_pos hpa] at h
      have htl : tl.countP p = 0 := by omega
      refine Exists.intro (⟨0, Nat.succ_pos _⟩ : Fin (a :: tl).length)
        (And.intro ?_ fun i hi => ?_)
      · simpa only [Fin.getElem_fin, List.getElem_cons_zero] using hpa
      · rcases i with ⟨_ | k, hk⟩
        · rfl
        · simp only [Fin.getElem_fin, List.getElem_cons_succ] at hi
          have hk' : k < tl.length := by simp only [List.length_cons] at hk; omega
          exact absurd hi ((List.countP_eq_zero.mp htl) tl[k] (List.getElem_mem hk'))
    | false =>
      rw [List.countP_cons_of_neg (by rw [hpa]; decide)] at h
      obtain ⟨j, hj, hjuniq⟩ := ih h
      refine Exists.intro j.succ (And.intro ?_ fun i hi => ?_)
      · simpa only [Fin.getElem_fin, Fin.val_succ, List.getElem_cons_succ] using hj
      · rcases i with ⟨_ | k, hk⟩
        · simp only [Fin.getElem_fin, List.getElem_cons_zero] at hi
          exact absurd hi (by rw [hpa]; decide)
        · simp only [Fin.getElem_fin, List.getElem_cons_succ] at hi
          have hk' : k < tl.length := by simp only [List.length_cons] at hk; omega
          have heq := Fin.ext_iff.mp (hjuniq ⟨k, hk'⟩ (by simpa only [Fin.getElem_fin] using hi))
          exact Fin.ext (by simp only [Fin.val_succ]; exact congrArg (· + 1) heq)

/-- If `l.countP p = 1`, there is a unique element `a` satisfying `a ∈ l ∧ p a = true`. -/
theorem List.existsUnique_mem_of_countP_eq_one {α : Type*} {l : List α} {p : α → Bool}
    (h : l.countP p = 1) : ∃! a, a ∈ l ∧ p a = true := by
  induction l with
  | nil =>
    rw [List.countP_nil] at h
    omega
  | cons a tl ih =>
    cases hpa : p a with
    | true =>
      rw [List.countP_cons_of_pos hpa] at h
      have htl : tl.countP p = 0 := by omega
      refine Exists.intro a (And.intro ⟨List.mem_cons_self, hpa⟩ fun b ⟨hb, hpb⟩ => ?_)
      rcases List.mem_cons.mp hb with rfl | hbtl
      · rfl
      · exact absurd hpb ((List.countP_eq_zero.mp htl) b hbtl)
    | false =>
      rw [List.countP_cons_of_neg (by rw [hpa]; decide)] at h
      obtain ⟨b, ⟨hbtl, hpb⟩, hbuniq⟩ := ih h
      refine Exists.intro b (And.intro ⟨List.mem_cons_of_mem a hbtl, hpb⟩ fun c ⟨hc, hpc⟩ => ?_)
      rcases List.mem_cons.mp hc with rfl | hctl
      · exact absurd hpc (by rw [hpa]; decide)
      · exact hbuniq c ⟨hctl, hpc⟩
