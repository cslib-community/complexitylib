/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.PrefixPartition

/-!
# Finite frontier conservation for sparse native queries

Pending prefixes carry possible-leaf counts, additive values and the previously proved
finite depth potential. Expanding one prefix preserves counts and values and decreases
that potential; completing a full leaf transfers exactly one term to the finished list.
These are finite algebraic facts, not execution or cost contracts.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery

open Finset Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Number of possible full leaves represented by the pending task list. -/
@[expose] def leafMass {L : ℕ} (η : OutStr L) (t : ℕ) (tasks : List (List Term)) : ℕ :=
  (tasks.map fun xs => (possibleLeaves η t xs).card).sum

/-- Additive value of all full leaves represented by the pending task list. -/
@[expose] def frontierValue {G : Type*} [AddCommMonoid G] {L : ℕ}
    (η : OutStr L) (t : ℕ) (f : Leaf L → G) (tasks : List (List Term)) : G :=
  (tasks.map fun xs => ∑ τ ∈ possibleLeaves η t xs, f τ).sum

/-- Finite depth potential of all pending tasks. -/
@[expose] def frontierWork {L : ℕ} (η : OutStr L) (t : ℕ)
    (tasks : List (List Term)) : ℕ := (tasks.map (potential η t)).sum

/-- The initial frontier contains exactly the original allowed full leaves. -/
@[simp] theorem leafMass_root {L : ℕ} (η : OutStr L) (t : ℕ) :
    leafMass η t [[]] = (possibleLeaves η t []).card := by simp [leafMass]

/-- The initial frontier's value is the original allowed-leaf sum. -/
@[simp] theorem frontierValue_root {G : Type*} [AddCommMonoid G] {L : ℕ}
    (η : OutStr L) (t : ℕ) (f : Leaf L → G) :
    frontierValue η t f [[]] = ∑ τ ∈ possibleLeaves η t [], f τ := by
  simp [frontierValue]

/-- Initial finite depth potential charges at most one full-depth path per allowed leaf. -/
@[simp] theorem frontierWork_root {L : ℕ} (η : OutStr L) (t : ℕ) :
    frontierWork η t [[]] = (L + 1) * (possibleLeaves η t []).card := by
  simp [frontierWork]

/-- Each pending leaf contributes at least one unit of finite depth potential. -/
theorem leafMass_le_frontierWork {L : ℕ} (η : OutStr L) (t : ℕ)
    (tasks : List (List Term)) : leafMass η t tasks ≤ frontierWork η t tasks := by
  induction tasks with
  | nil => simp [leafMass, frontierWork]
  | cons xs tasks ih =>
    have hp : (possibleLeaves η t xs).card ≤ potential η t xs :=
      Nat.le_mul_of_pos_left _ (by omega)
    simpa only [leafMass, frontierWork, List.map_cons, List.sum_cons] using
      Nat.add_le_add hp ih

/-- Replacing a task with its real children preserves the represented leaf count. -/
theorem leafMass_expand {L t : ℕ} {η : OutStr L} {xs : List Term}
    (hx : Good η t xs) (hk : xs.length < L) (tasks : List (List Term)) :
    leafMass η t (children η t xs ++ tasks) = leafMass η t (xs :: tasks) := by
  simp only [leafMass, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
    sum_card_possibleLeaves_children hx hk]

/-- Replacing a task with its real children preserves every additive semantic sum. -/
theorem frontierValue_expand {G : Type*} [AddCommMonoid G] {L t : ℕ}
    {η : OutStr L} {xs : List Term} (hx : Good η t xs) (hk : xs.length < L)
    (f : Leaf L → G) (tasks : List (List Term)) :
    frontierValue η t f (children η t xs ++ tasks) = frontierValue η t f (xs :: tasks) := by
  simp only [frontierValue, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
    sum_values_children hx hk f]

/-- The actual ordered expansion strictly decreases the pending finite work potential. -/
theorem frontierWork_expand_lt {L t : ℕ} {η : OutStr L} {xs : List Term}
    (hx : Good η t xs) (hk : xs.length < L) (tasks : List (List Term)) :
    frontierWork η t (children η t xs ++ tasks) < frontierWork η t (xs :: tasks) := by
  simp only [frontierWork, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
  exact Nat.add_lt_add_right (sum_potential_children_list_lt hx hk) _

/-- Finishing a valid full leaf removes exactly one possible-leaf occurrence. -/
theorem leafMass_finish {L t : ℕ} {η : OutStr L} (τ : Leaf L)
    (hτ : Good η t (List.ofFn τ)) (tasks : List (List Term)) :
    leafMass η t (List.ofFn τ :: tasks) = 1 + leafMass η t tasks := by
  simp [leafMass, possibleLeaves_ofFn τ hτ]

/-- Finishing that leaf removes precisely its original additive value. -/
theorem frontierValue_finish {G : Type*} [AddCommMonoid G] {L t : ℕ}
    {η : OutStr L} (τ : Leaf L) (hτ : Good η t (List.ofFn τ))
    (f : Leaf L → G) (tasks : List (List Term)) :
    frontierValue η t f (List.ofFn τ :: tasks) = f τ + frontierValue η t f tasks := by
  simp [frontierValue, possibleLeaves_ofFn τ hτ]

/-- A completed leaf has exactly one unit of remaining depth potential. -/
theorem frontierWork_finish {L t : ℕ} {η : OutStr L} (τ : Leaf L)
    (hτ : Good η t (List.ofFn τ)) (tasks : List (List Term)) :
    frontierWork η t (List.ofFn τ :: tasks) = 1 + frontierWork η t tasks := by
  simp [frontierWork, potential, possibleLeaves_ofFn τ hτ]

/-- Finite conservation data used to relate native accumulator contents to the root sum.
There is no execution, charged-time, layout or intermediate-fitting field. -/
structure FrontierInvariant {G : Type*} [AddCommMonoid G] {L : ℕ}
    (η : OutStr L) (t : ℕ) (f : Leaf L → G)
    (finished : List (Leaf L)) (tasks : List (List Term)) : Prop where
  /-- Every pending prefix obeys the original query and order cap. -/
  good : ∀ xs ∈ tasks, Good η t xs
  /-- Completed and pending leaf occurrences account for the original finite leaf count. -/
  mass : finished.length + leafMass η t tasks = leafMass η t [[]]
  /-- Completed and pending values account for the original finite root sum. -/
  value : (finished.map f).sum + frontierValue η t f tasks = frontierValue η t f [[]]
  /-- Pending finite depth potential does not exceed the original root potential. -/
  work : frontierWork η t tasks ≤ frontierWork η t [[]]

/-- The actual initial empty prefix satisfies the finite conservation invariant. -/
theorem FrontierInvariant.initial {G : Type*} [AddCommMonoid G] {L : ℕ}
    (η : OutStr L) (t : ℕ) (f : Leaf L → G) : FrontierInvariant η t f [] [[]] := by
  constructor
  · intro xs hx
    have hxs : xs = [] := by simpa only [List.mem_singleton] using hx
    subst xs
    simp [Good, Compatible, usedFrom]
  · simp
  · simp
  · exact Nat.le_refl _

/-- Actual child expansion preserves conservation while advancing finite work. -/
theorem FrontierInvariant.expand {G : Type*} [AddCommMonoid G] {L t : ℕ}
    {η : OutStr L} {f : Leaf L → G} {finished : List (Leaf L)}
    {xs : List Term} {tasks : List (List Term)}
    (h : FrontierInvariant η t f finished (xs :: tasks)) (hk : xs.length < L) :
    FrontierInvariant η t f finished (children η t xs ++ tasks) := by
  have hx : Good η t xs := h.good xs (by simp)
  constructor
  · intro ys hy
    rcases List.mem_append.mp hy with hy | hy
    · exact good_of_mem_children hx hk hy
    · exact h.good ys (by simp [hy])
  · rw [leafMass_expand hx hk]
    exact h.mass
  · rw [frontierValue_expand hx hk]
    exact h.value
  · exact (frontierWork_expand_lt hx hk tasks).le.trans h.work

/-- Finishing one actual leaf transfers its occurrence and value to the completed prefix. -/
theorem FrontierInvariant.finish {G : Type*} [AddCommMonoid G] {L t : ℕ}
    {η : OutStr L} {f : Leaf L → G} {finished : List (Leaf L)} {τ : Leaf L}
    {tasks : List (List Term)}
    (h : FrontierInvariant η t f finished (List.ofFn τ :: tasks)) :
    FrontierInvariant η t f (finished ++ [τ]) tasks := by
  have hτ : Good η t (List.ofFn τ) := h.good _ (by simp)
  constructor
  · intro xs hx
    exact h.good xs (by simp [hx])
  · have hm := h.mass
    rw [leafMass_finish τ hτ] at hm
    simpa only [List.length_append, List.length_singleton, Nat.add_assoc] using hm
  · have hv := h.value
    rw [frontierValue_finish τ hτ] at hv
    simpa only [List.map_append, List.map_singleton, List.sum_append,
      List.sum_singleton, add_assoc] using hv
  · have hw := h.work
    rw [frontierWork_finish τ hτ] at hw
    omega

/-- At the empty frontier the accumulated original leaf values equal the exact root sum. -/
theorem FrontierInvariant.finished_value {G : Type*} [AddCommMonoid G] {L t : ℕ}
    {η : OutStr L} {f : Leaf L → G} {finished : List (Leaf L)}
    (h : FrontierInvariant η t f finished []) :
    (finished.map f).sum = ∑ τ ∈ possibleLeaves η t [], f τ := by
  simpa [frontierValue] using h.value

/-- The actual finished prefix cannot exceed the original number of allowed full leaves. -/
theorem FrontierInvariant.finished_length_le {G : Type*} [AddCommMonoid G] {L t : ℕ}
    {η : OutStr L} {f : Leaf L → G} {finished : List (Leaf L)}
    {tasks : List (List Term)} (h : FrontierInvariant η t f finished tasks) :
    finished.length ≤ (possibleLeaves η t []).card := by
  have hm := h.mass
  rw [leafMass_root] at hm
  omega

/-- The pending native record count fits below the same original finite root potential. -/
theorem FrontierInvariant.pending_length_le {G : Type*} [AddCommMonoid G] {L t : ℕ}
    {η : OutStr L} {f : Leaf L → G} {finished : List (Leaf L)}
    {tasks : List (List Term)} (h : FrontierInvariant η t f finished tasks) :
    tasks.length ≤ (L + 1) * (possibleLeaves η t []).card := by
  have hlen : tasks.length ≤ frontierWork η t tasks := length_le_sum_potential tasks h.good
  exact hlen.trans (by simpa only [frontierWork_root] using h.work)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery
