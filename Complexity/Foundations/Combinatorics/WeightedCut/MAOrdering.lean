/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.WeightedCut.MinCutBetween
public import Mathlib.Data.List.MinMax
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Maximum adjacency orderings

For a weighted multigraph `W : V → V → ℕ` (`Cslib.WeightedCut.IsMultigraph`), the attachment
weight `w(A, x) = ∑_{a ∈ A} W a x` measures how strongly a vertex `x` is joined to a vertex set
`A`. A *maximum adjacency* (MA) ordering lists the vertices so that each vertex is attached to the
vertices before it at least as strongly as every later vertex is. Maximum adjacency search builds
one greedily: starting from the empty set, it repeatedly adds a vertex of largest attachment.

The basic property of these orderings, due to Nagamochi and Ibaraki [NagamochiIbaraki1992] and the
key lemma of the Stoer–Wagner minimum cut algorithm [StoerWagner1997] (the "cut-of-the-phase"
lemma), is that the cut `{t}` of the last vertex `t` is a minimum cut separating `t` from the
second to last vertex `s`: it weighs at most every vertex set containing exactly one of `s` and
`t`. The global minimum cut algorithm built on it is
`Complexity.Algorithms.Lean.StoerWagner.Basic`.

The proof is an induction along the ordering. Fix a cut `C`. For the set `A` of vertices listed so
far, the weight of `C` within `A` is the weight of the edges of `A` crossing `C`; whenever the
next listed vertex is on the other side of `C` from the last listed one, its attachment to its own
side of `A` is at most the weight of `C` within `A`. The last vertex `t` is such a vertex for
every `C` separating `s` and `t`, and its attachment to `A` = all other vertices is its degree,
the weight of `{t}`. This is the standard inductive argument for the lemma (as described in
secondary accounts of [StoerWagner1997]), phrased as an invariant of the prefixes.

## Main definitions

* `Cslib.WeightedCut.attachWeight`: the attachment weight `w(A, x)`.
* `Cslib.WeightedCut.IsMAOrderingFrom`, `Cslib.WeightedCut.IsMAOrdering`: maximum adjacency
  orderings after a set of already chosen vertices, and of all the vertices.
* `Cslib.WeightedCut.maSearch`: maximum adjacency search, ties broken by the order of the
  candidate list.

## Main results

* `Cslib.WeightedCut.cutWeight_singleton_le_of_isMAOrdering`: the MA-ordering lemma.
* `Cslib.WeightedCut.cutWeight_singleton_eq_minCutBetween_of_isMAOrdering`: the same, as
  `cutWeight W {t} = minCutBetween W s t`.
* `Cslib.WeightedCut.maSearch_spec`: maximum adjacency search lists its candidates in a maximum
  adjacency ordering.

## References

* [H. Nagamochi and T. Ibaraki, *Computing Edge-Connectivity in Multigraphs and Capacitated
  Graphs*][NagamochiIbaraki1992]
* [M. Stoer and F. Wagner, *A Simple Min-Cut Algorithm*][StoerWagner1997]
-/

public section

namespace Cslib.WeightedCut

variable {V : Type*} [DecidableEq V]

/-! ### Attachment weights and maximum adjacency orderings -/

/-- The attachment weight `w(A, x) = ∑_{a ∈ A} W a x` of a vertex `x` to a vertex set `A`. -/
def attachWeight (W : V → V → ℕ) (A : Finset V) (x : V) : ℕ :=
  ∑ a ∈ A, W a x

omit [DecidableEq V] in
theorem attachWeight_mono (W : V → V → ℕ) {A B : Finset V} (h : A ⊆ B) (x : V) :
    attachWeight W A x ≤ attachWeight W B x :=
  Finset.sum_le_sum_of_subset h

omit [DecidableEq V] in
@[simp]
theorem attachWeight_empty (W : V → V → ℕ) (x : V) : attachWeight W ∅ x = 0 :=
  Finset.sum_empty

theorem attachWeight_insert (W : V → V → ℕ) {A : Finset V} {a : V} (ha : a ∉ A) (x : V) :
    attachWeight W (insert a A) x = W a x + attachWeight W A x :=
  Finset.sum_insert ha

/-- `IsMAOrderingFrom W A l`: listing `l` after the already chosen vertices `A`, each vertex is
attached to the vertices chosen before it at least as strongly as every later vertex. -/
def IsMAOrderingFrom (W : V → V → ℕ) : Finset V → List V → Prop
  | _, [] => True
  | A, x :: l => (∀ y ∈ l, attachWeight W A y ≤ attachWeight W A x) ∧
      IsMAOrderingFrom W (insert x A) l

@[simp]
theorem isMAOrderingFrom_nil (W : V → V → ℕ) (A : Finset V) : IsMAOrderingFrom W A [] :=
  trivial

@[simp]
theorem isMAOrderingFrom_cons (W : V → V → ℕ) (A : Finset V) (x : V) (l : List V) :
    IsMAOrderingFrom W A (x :: l) ↔ (∀ y ∈ l, attachWeight W A y ≤ attachWeight W A x) ∧
      IsMAOrderingFrom W (insert x A) l :=
  Iff.rfl

instance decidableIsMAOrderingFrom (W : V → V → ℕ) :
    ∀ (A : Finset V) (l : List V), Decidable (IsMAOrderingFrom W A l)
  | A, [] => isTrue (isMAOrderingFrom_nil W A)
  | A, x :: l =>
    haveI := decidableIsMAOrderingFrom W (insert x A) l
    decidable_of_iff' _ (isMAOrderingFrom_cons W A x l)

/-- A maximum adjacency ordering of the vertices: a list of all the vertices, each once, in which
each vertex is attached to the vertices before it at least as strongly as every later vertex is.
The first vertex is arbitrary. -/
structure IsMAOrdering (W : V → V → ℕ) (l : List V) : Prop where
  /-- No vertex is listed twice. -/
  nodup : l.Nodup
  /-- Every vertex is listed. -/
  mem : ∀ v, v ∈ l
  /-- The maximum adjacency property. -/
  isMAOrderingFrom : IsMAOrderingFrom W ∅ l

theorem isMAOrdering_iff (W : V → V → ℕ) (l : List V) :
    IsMAOrdering W l ↔ l.Nodup ∧ (∀ v, v ∈ l) ∧ IsMAOrderingFrom W ∅ l :=
  ⟨fun h => ⟨h.nodup, h.mem, h.isMAOrderingFrom⟩, fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃⟩⟩

variable [Fintype V]

instance (W : V → V → ℕ) (l : List V) : Decidable (IsMAOrdering W l) :=
  decidable_of_iff' _ (isMAOrdering_iff W l)

/-! ### The MA-ordering lemma -/

section Lemma

variable (W : V → V → ℕ) (C : Finset V)

/-- The weight of `C` within `A`: of the edges between `A ∩ C` and `A \ C`. -/
private def crossIn (A : Finset V) : ℕ :=
  ∑ u ∈ A.filter (· ∈ C), ∑ v ∈ A.filter (· ∉ C), W u v

/-- The vertices of `A` on the same side of `C` as `x`. -/
private def sameSide (A : Finset V) (x : V) : Finset V :=
  A.filter fun a => (a ∈ C ↔ x ∈ C)

/-- The vertices of `A` on the other side of `C` from `x`. -/
private def otherSide (A : Finset V) (x : V) : Finset V :=
  A.filter fun a => ¬ (a ∈ C ↔ x ∈ C)

omit [Fintype V] in
private theorem attachWeight_sameSide_add_otherSide (A : Finset V) (x : V) :
    attachWeight W (sameSide C A x) x + attachWeight W (otherSide C A x) x =
      attachWeight W A x :=
  Finset.sum_filter_add_sum_filter_not A _ _

omit [Fintype V] in
/-- Adding `x` to `A` adds the attachment of `x` to the other side of `A`. -/
private theorem crossIn_insert {W : V → V → ℕ} (hW : IsMultigraph W) {A : Finset V} {x : V}
    (hx : x ∉ A) :
    crossIn W C (insert x A) = crossIn W C A + attachWeight W (otherSide C A x) x := by
  unfold crossIn otherSide attachWeight
  by_cases hxC : x ∈ C
  · rw [Finset.filter_insert, ite_eq_left hxC, Finset.filter_insert, ite_eq_right (not_not.mpr hxC),
      Finset.sum_insert (by simp [hx]), add_comm]
    congr 1
    exact Finset.sum_congr (by ext a; simp [hxC]) fun a _ => hW.1 x a
  · rw [Finset.filter_insert, ite_eq_right hxC, Finset.filter_insert, ite_eq_left hxC]
    have hfilter : (A.filter fun a => ¬ (a ∈ C ↔ x ∈ C)) = A.filter (· ∈ C) := by
      ext a
      simp [hxC]
    rw [hfilter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_insert (by simp [hx]), add_comm]

omit [Fintype V] in
private theorem crossIn_le_insert {W : V → V → ℕ} (hW : IsMultigraph W) {A : Finset V} {x : V}
    (hx : x ∉ A) : crossIn W C A ≤ crossIn W C (insert x A) := by
  rw [crossIn_insert C hW hx]
  exact Nat.le_add_right _ _

omit [Fintype V] in
/-- The key step: if `x` is attached to its own side of `A` by at most the weight of `C` within
`A`, it is attached to all of `A` by at most the weight of `C` within `A ∪ {x}`. -/
private theorem attachWeight_le_crossIn_insert {W : V → V → ℕ} (hW : IsMultigraph W)
    {A : Finset V} {x : V} (hx : x ∉ A)
    (h : attachWeight W (sameSide C A x) x ≤ crossIn W C A) :
    attachWeight W A x ≤ crossIn W C (insert x A) := by
  rw [crossIn_insert C hW hx, ← attachWeight_sameSide_add_otherSide W C A x]
  omega

/-- The invariant of the prefixes `A` of an MA ordering: every vertex `x` of the rest `R` on the
other side of `C` from the last listed vertex `last` is attached to its own side of `A` by at
most the weight of `C` within `A`. -/
private def Inv (A : Finset V) (last : V) (R : List V) : Prop :=
  ∀ x ∈ R, ¬ (x ∈ C ↔ last ∈ C) → attachWeight W (sameSide C A x) x ≤ crossIn W C A

omit [Fintype V] in
private theorem inv_cons {W : V → V → ℕ} (hW : IsMultigraph W) {A : Finset V} {last x : V}
    {l : List V} (hx : x ∉ A) (hma : ∀ y ∈ l, attachWeight W A y ≤ attachWeight W A x)
    (hinv : Inv W C A last (x :: l)) : Inv W C (insert x A) x l := by
  intro y hy hyx
  have hsame : sameSide C (insert x A) y = sameSide C A y := by
    unfold sameSide
    rw [Finset.filter_insert, ite_eq_right fun h => hyx h.symm]
  rw [hsame]
  by_cases hxl : x ∈ C ↔ last ∈ C
  · have hyl : ¬ (y ∈ C ↔ last ∈ C) := fun h => hyx (h.trans hxl.symm)
    exact (hinv y (List.mem_cons_of_mem x hy) hyl).trans (crossIn_le_insert C hW hx)
  · have hxx := attachWeight_le_crossIn_insert C hW hx (hinv x List.mem_cons_self hxl)
    exact (attachWeight_mono W (Finset.filter_subset _ _) y).trans ((hma y hy).trans hxx)

omit [Fintype V] in
private theorem inv_append {W : V → V → ℕ} (hW : IsMultigraph W) :
    ∀ (p : List V) {A : Finset V} {last : V} {R : List V},
      (∀ x ∈ p, x ∉ A) → p.Nodup → IsMAOrderingFrom W A (p ++ R) → Inv W C A last (p ++ R) →
      Inv W C (p.toFinset ∪ A) (p.getLastD last) R
  | [], A, last, R, _, _, _, hinv => by simpa using hinv
  | x :: p, A, last, R, hfresh, hnd, hma, hinv => by
    rw [List.cons_append, isMAOrderingFrom_cons] at hma
    rw [List.cons_append] at hinv
    have hx : x ∉ A := hfresh x List.mem_cons_self
    have hstep := inv_cons C hW hx hma.1 hinv
    have hfresh' : ∀ y ∈ p, y ∉ insert x A := by
      intro y hy hyA
      rcases Finset.mem_insert.mp hyA with rfl | hyA
      · exact (List.nodup_cons.mp hnd).1 hy
      · exact hfresh y (List.mem_cons_of_mem x hy) hyA
    have h := inv_append hW p hfresh' (List.nodup_cons.mp hnd).2 hma.2 hstep
    have hset : p.toFinset ∪ insert x A = (x :: p).toFinset ∪ A := by
      ext a
      simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_cons]
      tauto
    rwa [List.getLastD_cons, ← hset]

omit [Fintype V] in
private theorem inv_empty (last : V) (R : List V) : Inv W C ∅ last R := by
  intro x _ _
  simp [attachWeight, sameSide]

private theorem crossIn_univ : crossIn W C Finset.univ = cutWeight W C := by
  unfold crossIn cutWeight
  rw [Finset.sdiff_eq_filter]
  congr 1
  ext a
  simp

end Lemma

/-- **The MA-ordering lemma** ([NagamochiIbaraki1992]; the "cut-of-the-phase" lemma of
[StoerWagner1997]): if `s, t` are the last two vertices of a maximum adjacency ordering, the cut
`{t}` weighs at most every vertex set containing exactly one of `s` and `t`. -/
theorem cutWeight_singleton_le_of_isMAOrdering {W : V → V → ℕ} (hW : IsMultigraph W)
    {p : List V} {s t : V} (hl : IsMAOrdering W (p ++ [s, t])) {C : Finset V}
    (hsep : s ∈ C ↔ t ∉ C) :
    cutWeight W {t} ≤ cutWeight W C := by
  have hnd := hl.nodup
  have hinv := inv_append C hW (p ++ [s]) (A := ∅) (last := t) (R := [t])
    (fun _ _ => Finset.notMem_empty _) (List.Nodup.sublist (by simp) hnd)
    (by simpa using hl.isMAOrderingFrom) (inv_empty W C t _)
  rw [List.getLastD_concat, Finset.union_empty] at hinv
  set A := (p ++ [s]).toFinset with hA
  have htA : t ∉ A := by
    rw [hA, List.mem_toFinset]
    intro ht
    have h := List.nodup_append.mp hnd
    rcases List.mem_append.mp ht with ht | ht
    · exact h.2.2 t ht t (by simp) rfl
    · have hst : s ≠ t := by simpa using h.2.1
      exact hst (List.mem_singleton.mp ht).symm
  have hAt : A = Finset.univ \ {t} := by
    ext a
    by_cases hat : a = t
    · subst hat
      simp [htA]
    · have := hl.mem a
      simp only [hA, List.mem_toFinset, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton,
        hat, not_false_eq_true, and_true, iff_true]
      simpa [hat] using this
  have hts : ¬ (t ∈ C ↔ s ∈ C) := by tauto
  have hkey := attachWeight_le_crossIn_insert C hW htA (hinv t List.mem_cons_self hts)
  have huniv : insert t A = Finset.univ := by
    rw [hAt, Finset.insert_eq, Finset.union_sdiff_of_subset (Finset.subset_univ _)]
  rw [huniv, crossIn_univ] at hkey
  refine le_of_eq_of_le ?_ hkey
  unfold cutWeight attachWeight
  rw [Finset.sum_singleton, ← hAt]
  exact Finset.sum_congr rfl fun a _ => hW.1 t a

/-- The MA-ordering lemma in terms of the minimum `s`–`t` cut weight `λ(s, t)`
(`Cslib.WeightedCut.minCutBetween`): if `s, t` are the last two vertices of a maximum adjacency
ordering, the cut `{t}` weighs exactly `λ(s, t)`. -/
theorem cutWeight_singleton_eq_minCutBetween_of_isMAOrdering {W : V → V → ℕ}
    (hW : IsMultigraph W) {p : List V} {s t : V} (hl : IsMAOrdering W (p ++ [s, t])) :
    cutWeight W {t} = minCutBetween W s t := by
  have hst : s ≠ t := by simpa using (List.nodup_append.mp hl.nodup).2.1
  rw [minCutBetween_comm hW]
  exact (cutWeight_eq_minCutBetween_iff W (Finset.mem_singleton_self t) (by simpa using hst)).mpr
    fun Y htY hsY => cutWeight_singleton_le_of_isMAOrdering hW hl (by tauto)

omit [Fintype V]

/-! ### Maximum adjacency search -/

/-- Maximum adjacency search. With `key y = w(A, y)` for the vertices `A` chosen so far, it lists
a candidate of largest key (the first one in the list `R` of remaining candidates, by
`List.argmax`), adds its edge weights to the keys, and continues with the other candidates.
`fuel` bounds the number of steps, so that the recursion is structural and reduces in the
kernel. -/
@[expose] def maSearch (W : V → V → ℕ) : ℕ → (V → ℕ) → List V → List V
  | 0, _, _ => []
  | fuel + 1, key, R =>
    match R.argmax key with
    | none => []
    | some v => v :: maSearch W fuel (fun y => key y + W v y) (R.erase v)

/-- Maximum adjacency search from the chosen set `A`, with keys `w(A, ·)` and enough fuel, lists
its candidates in a maximum adjacency ordering after `A`. -/
theorem maSearch_spec (W : V → V → ℕ) :
    ∀ (fuel : ℕ) (key : V → ℕ) (A : Finset V) (R : List V), R.Nodup → R.length ≤ fuel →
      (∀ y, key y = attachWeight W A y) → (∀ y ∈ R, y ∉ A) →
      (maSearch W fuel key R).Perm R ∧ IsMAOrderingFrom W A (maSearch W fuel key R)
  | 0, key, A, R, _, hlen, _, _ => by
    rw [Nat.le_zero, List.length_eq_zero_iff] at hlen
    subst hlen
    exact ⟨List.Perm.refl _, trivial⟩
  | fuel + 1, key, A, R, hnd, hlen, hkey, hfresh => by
    rcases harg : R.argmax key with _ | v
    · rw [List.argmax_eq_none] at harg
      subst harg
      simp [maSearch]
    · simp only [maSearch, harg]
      have hvR : v ∈ R := List.argmax_mem harg
      have hvA : v ∉ A := hfresh v hvR
      have hlen' : (R.erase v).length ≤ fuel := by
        rw [List.length_erase_of_mem hvR]
        omega
      have hkey' : ∀ y, key y + W v y = attachWeight W (insert v A) y := by
        intro y
        rw [attachWeight_insert W hvA, hkey, add_comm]
      have hfresh' : ∀ y ∈ R.erase v, y ∉ insert v A := by
        intro y hy hyA
        rw [hnd.mem_erase_iff] at hy
        rcases Finset.mem_insert.mp hyA with rfl | hyA
        · exact hy.1 rfl
        · exact hfresh y hy.2 hyA
      obtain ⟨hperm, hma⟩ := maSearch_spec W fuel _ (insert v A) _ (hnd.erase v) hlen' hkey'
        hfresh'
      refine ⟨(hperm.cons v).trans (List.perm_cons_erase hvR).symm, ?_, hma⟩
      intro y hy
      rw [← hkey, ← hkey]
      exact List.le_of_mem_argmax (List.mem_of_mem_erase (hperm.subset hy)) harg

end Cslib.WeightedCut
