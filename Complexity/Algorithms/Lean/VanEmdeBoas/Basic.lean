/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.VanEmdeBoas.Layout
public import Mathlib.Data.Fin.Basic

/-!
# Recursive van Emde Boas sets

The universe at depth `d` is `[0, 2 ^ (2 ^ d))`. Each internal node stores its minimum
outside its clusters, caches its maximum, and records nonempty clusters in a recursive summary.
This is the recursive variant presented in [Demaine's lecture notes][Demaine2015VanEmdeBoas],
not the stratified-tree implementation of [van Emde Boas, Kaas and
Zijlstra][VanEmdeBoasKaasZijlstra1977].
The lecture notes credit Michael Bender for a 2001 personal communication.

The functions here are Lean algorithms. Immutable function updates, pattern matching and
recursive calls have no certified machine cost. The separate word-RAM realization must charge
instructions, initialization and memory before any machine running-time claim is made.

## Main definitions

* `Tree`: a fully allocated recursive shape, with a two-key base universe.
* `Tree.bounds`, `Tree.minimum`, `Tree.maximum`, `Tree.withBounds`: cached local extrema and
  header update.
* `Tree.empty`, `Tree.insert`, `Tree.member`, `Tree.successor`: set operations.
* `Tree.Contains`: mathematical interpretation of the stored keys.
* `Tree.Extrema`, `Tree.Valid`: local extrema specification and recursive tree invariant.

## References

* [P. van Emde Boas, R. Kaas and E. Zijlstra, *Design and implementation of an efficient
  priority queue*][VanEmdeBoasKaasZijlstra1977]
* [E. Demaine, *Divide and conquer: van Emde Boas trees*, Lecture 4][Demaine2015VanEmdeBoas]
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.VanEmdeBoas

/-- The extrema use one shared presence bit. A present pair stores minimum and maximum. -/
inductive Tree : ℕ → Type where
  /-- A node for the universe `{0, 1}`. -/
  | leaf (bounds : Option (ℕ × ℕ)) : Tree 0
  /-- A node with a recursive summary and a direct-indexed array of clusters. -/
  | node {d : ℕ} (bounds : Option (ℕ × ℕ)) (summary : Tree d)
      (cluster : Fin (universeSize d) → Tree d) : Tree (d + 1)

namespace Tree

variable {d : ℕ}

/-- Cached extrema; `none` denotes an empty node. -/
def bounds : Tree d → Option (ℕ × ℕ)
  | .leaf b => b
  | .node b _ _ => b

/-- Cached minimum, without a search through clusters. -/
def minimum (t : Tree d) : Option ℕ := t.bounds.map Prod.fst

/-- Cached maximum, without a search through clusters. -/
def maximum (t : Tree d) : Option ℕ := t.bounds.map Prod.snd

/-- Change only the local extrema. A caller must justify the children and summary invariant. -/
def withBounds : Tree d → Option (ℕ × ℕ) → Tree d
  | .leaf _, b => .leaf b
  | .node _ s c, b => .node b s c

/-- The fully allocated empty tree. Allocation cost is not measured in this Lean definition. -/
def empty : (d : ℕ) → Tree d
  | 0 => .leaf none
  | d + 1 => .node none (empty d) (fun _ => empty d)

/-- Set membership. On valid trees, arguments outside the universe are rejected. -/
def member : {d : ℕ} → Tree d → ℕ → Bool
  | 0, .leaf b, x => match b with
    | none => false
    | some (m, M) => x == m || x == M
  | d + 1, .node b _ c, x => match b with
    | none => false
    | some (m, _) =>
      if x = m then true
      else if h : x / universeSize d < universeSize d then
        member (c ⟨x / universeSize d, h⟩) (x % universeSize d)
      else false

/-- Insert a bounded key. Repeated insertion of the local minimum does no recursive work.
For an empty cluster, its first element is installed directly and only the summary recurses. -/
def insert : {d : ℕ} → Tree d → ℕ → Tree d
  | 0, .leaf b, x => match b with
    | none => .leaf (some (x, x))
    | some (m, M) => .leaf (some (min m x, max M x))
  | d + 1, .node b s c, x => match b with
    | none => .node (some (x, x)) s c
    | some (m, M) =>
      if x = m then .node b s c
      else
        let displaced := max m x
        if h : displaced / universeSize d < universeSize d then
          let i : Fin (universeSize d) := ⟨displaced / universeSize d, h⟩
          let low := displaced % universeSize d
          match (c i).bounds with
          | none => .node (some (min m x, max M x)) (insert s i.val)
              (Function.update c i ((c i).withBounds (some (low, low))))
          | some _ => .node (some (min m x, max M x)) s
              (Function.update c i (insert (c i) low))
        else .node b s c

/-- The least stored key strictly greater than the query, or `none` if it does not exist.
The cached maximum chooses between one cluster recursion and one summary recursion. -/
def successor : {d : ℕ} → Tree d → ℕ → Option ℕ
  | 0, .leaf b, x => match b with
    | none => none
    | some (m, M) => if x < m then some m else if x < M then some M else none
  | d + 1, .node b s c, x => match b with
    | none => none
    | some (m, M) =>
      if x < m then some m
      else if M ≤ x then none
      else if h : x / universeSize d < universeSize d then
        let i : Fin (universeSize d) := ⟨x / universeSize d, h⟩
        let low := x % universeSize d
        if (c i).maximum.any (low < ·) then
          (successor (c i) low).map (i.val * universeSize d + ·)
        else do
          let j ← successor s i.val
          if hj : j < universeSize d then
            (c ⟨j, hj⟩).minimum.map (j * universeSize d + ·)
          else none
      else none

/-- Mathematical interpretation. The minimum is absent from the cluster interpretation. -/
def Contains : {d : ℕ} → Tree d → ℕ → Prop
  | 0, .leaf b, x => ∃ m M, b = some (m, M) ∧ (x = m ∨ x = M)
  | d + 1, .node b _ c, x =>
    ∃ m M, b = some (m, M) ∧
      (x = m ∨ ∃ i : Fin (universeSize d), ∃ y,
        (c i).Contains y ∧ x = i.val * universeSize d + y)

/-- The local extrema correctly describe a bounded set of keys. -/
def Extrema (t : Tree d) : Prop :=
  match t.bounds with
  | none => ∀ x, ¬t.Contains x
  | some (m, M) => m ≤ M ∧ M < universeSize d ∧ t.Contains m ∧ t.Contains M ∧
      ∀ x, t.Contains x → m ≤ x ∧ x ≤ M

/-- Recursive invariant: bounded extrema, valid children and summary, exact summary occupancy,
and strict exclusion of the local minimum from every cluster. -/
def Valid : {d : ℕ} → Tree d → Prop
  | 0, t => t.Extrema
  | d + 1, .node b s c =>
    (Tree.node b s c).Extrema ∧ s.Valid ∧ (∀ i, (c i).Valid) ∧
      (∀ i, s.Contains i.val ↔ (c i).bounds.isSome = true) ∧
      match b with
      | none => s.bounds = none ∧ ∀ i, (c i).bounds = none
      | some (m, _) => ∀ i y, (c i).Contains y → m < i.val * universeSize d + y

/-- The empty tree at depth `d` has no cached bounds. -/
@[simp] theorem bounds_empty (d : ℕ) : (empty d).bounds = none := by
  cases d <;> rfl

/-- The empty tree at depth `d` has no cached minimum. -/
@[simp] theorem minimum_empty (d : ℕ) : (empty d).minimum = none := by
  simp [minimum]

/-- The empty tree at depth `d` has no cached maximum. -/
@[simp] theorem maximum_empty (d : ℕ) : (empty d).maximum = none := by
  simp [maximum]

/-- The empty tree at depth `d` contains no elements. -/
@[simp] theorem contains_empty (d x : ℕ) : ¬(empty d).Contains x := by
  cases d <;> simp [empty, Contains]

/-- The representation invariant has a concrete instance at every depth. -/
theorem valid_empty (d : ℕ) : (empty d).Valid := by
  induction d with
  | zero => simp [Valid, Extrema, empty, bounds, Contains]
  | succ d ih =>
    refine ⟨?_, ih, fun _ => ih, ?_, ?_⟩
    · simp [Extrema, bounds, Contains]
    · intro i
      simp
    · simp

/-- Membership lookup on the empty tree at depth `d` always returns `false`. -/
@[simp] theorem member_empty (d x : ℕ) : (empty d).member x = false := by
  cases d <;> rfl

/-- Successor lookup on the empty tree at depth `d` always returns `none`. -/
@[simp] theorem successor_empty (d x : ℕ) : (empty d).successor x = none := by
  cases d <;> rfl

/-- Every valid tree has correctly bounded extrema. -/
theorem Valid.extrema {t : Tree d} (h : t.Valid) : t.Extrema := by
  cases t with
  | leaf => exact h
  | node => exact h.1

/-- Stored keys lie in the advertised bounded universe. -/
theorem Valid.contains_lt {t : Tree d} (h : t.Valid) {x : ℕ} (hx : t.Contains x) :
    x < universeSize d := by
  have he := h.extrema
  unfold Extrema at he
  split at he
  · exact False.elim (he x hx)
  · exact Nat.lt_of_le_of_lt (he.2.2.2.2 x hx).2 he.2.1

/-- An empty local header has no represented elements. -/
theorem not_contains_of_bounds_none {t : Tree d} (hb : t.bounds = none) (x : ℕ) :
    ¬t.Contains x := by
  cases t with
  | leaf b => simp only [bounds] at hb; simp [Contains, hb]
  | node b s c => simp only [bounds] at hb; simp [Contains, hb]

/-- An occupied valid node has a represented cached minimum. -/
theorem Valid.contains_minimum {t : Tree d} (h : t.Valid) {m M : ℕ}
    (hb : t.bounds = some (m, M)) : t.Contains m := by
  have he := h.extrema
  simp only [Extrema, hb] at he
  exact he.2.2.1

/-- An occupied valid node has a represented cached maximum. -/
theorem Valid.contains_maximum {t : Tree d} (h : t.Valid) {m M : ℕ}
    (hb : t.bounds = some (m, M)) : t.Contains M := by
  have he := h.extrema
  simp only [Extrema, hb] at he
  exact he.2.2.2.1

/-- Division and remainder recover a cluster's coordinates for bounded low parts. -/
theorem cluster_coordinates {u i y : ℕ} (hu : 0 < u) (hy : y < u) :
    (i * u + y) / u = i ∧ (i * u + y) % u = y := by
  constructor
  · rw [Nat.mul_comm i u, Nat.mul_add_div hu, Nat.div_eq_of_lt hy, Nat.add_zero]
  · exact Nat.mul_add_mod_of_lt hy

/-- Boolean lookup agrees with the mathematical interpretation of every valid tree. -/
theorem member_iff_contains {t : Tree d} (ht : t.Valid) (x : ℕ) :
    t.member x = true ↔ t.Contains x := by
  induction d generalizing x with
  | zero =>
    cases t with
    | leaf b =>
      cases b with
      | none => simp [member, Contains]
      | some b => cases b; simp [member, Contains]
  | succ d ih =>
    cases t with
    | node b s c =>
      cases b with
      | none => simp [member, Contains]
      | some b =>
        obtain ⟨m, M⟩ := b
        by_cases hm : x = m
        · simp [member, Contains, hm]
        · by_cases hi : x / universeSize d < universeSize d
          · let i : Fin (universeSize d) := ⟨x / universeSize d, hi⟩
            rw [member, ite_eq_right hm, dite_eq_left hi, ih (ht.2.2.1 i)]
            constructor
            · intro hx
              refine ⟨m, M, rfl, Or.inr ⟨i, x % universeSize d, hx, ?_⟩⟩
              simpa only [i, Nat.mul_comm] using (Nat.div_add_mod x (universeSize d)).symm
            · rintro ⟨m', M', he, hm' | ⟨j, y, hy, hxy⟩⟩
              · cases he
                exact False.elim (hm hm')
              · have hylt := (ht.2.2.1 j).contains_lt hy
                have hcoord := cluster_coordinates (i := j.val) (universeSize_pos d) hylt
                have hhigh : x / universeSize d = j.val := by
                  rw [hxy]
                  exact hcoord.1
                have hlow : x % universeSize d = y := by
                  rw [hxy]
                  exact hcoord.2
                have hij : i = j := Fin.ext hhigh
                simpa only [hij, hlow] using hy
          · have hx : ¬(Tree.node (some (m, M)) s c).Contains x := by
              intro hx
              have hb := ht.contains_lt hx
              apply hi
              exact (Nat.div_lt_iff_lt_mul (universeSize_pos d)).mpr hb
            simp [member, hm, hi, hx]

end Tree

end Cslib.Algorithms.Lean.VanEmdeBoas
