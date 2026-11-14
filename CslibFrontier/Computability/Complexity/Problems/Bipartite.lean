/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.StronglyConnected
public import CslibFrontier.Computability.Complexity.Problems.USTCON
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

/-!
# Bipartite graphs and odd cycles as undirected connectivity

An undirected graph instance (`Cslib.Complexity.UGraphInstance`) is a simple graph on `Fin n`,
given by a symmetric adjacency matrix with zero diagonal. It is encoded
(`Cslib.Complexity.encUGraph`) as its digraph (`Cslib.Complexity.encDigraph`): the unary header
`1^n 0` followed by the adjacency matrix row by row. It belongs to `Cslib.Complexity.Bipartite`
when its graph is 2-colourable (`SimpleGraph.IsBipartite`).

Non-bipartiteness becomes undirected `s`–`t` connectivity through the double cover `G′` of
[Goldreich, Exercise 5.16][Goldreich2008], whose vertices are the pairs `(v, b)` of a vertex and a
side, with an edge between `(u, b)` and `(v, !b)` for every edge `{u, v}`. A vertex `x` lies on an
odd closed walk exactly when `(x, 0)` and `(x, 1)` are connected in `G′`. The instance
`Cslib.Complexity.Bipartite.oddCycleInstance G` takes one copy of `G′` for every vertex `x`, a
source joined to `(x, 0)` in copy `x` and a target joined to `(x, 1)` in copy `x`. The copies are
disjoint, so the source reaches the target exactly when some vertex lies on an odd closed walk,
that is, when `G` is not bipartite (`Cslib.Complexity.Bipartite.oddCycleInstance_mem_iff`). This
turns the disjunction over `x` of Goldreich's guideline into a single query.

The vertices of the instance are numbered so that a counter program can decode them: the source
is `0`, the target `1`, and the vertex `(v, b)` of copy `x` is
`Cslib.Complexity.Bipartite.copyVertex n x v b = 2 + 2 n x + 2 v + b`.

## Main definitions

* `Cslib.Complexity.UGraphInstance`: undirected graphs given by adjacency matrices.
* `Cslib.Complexity.UGraphInstance.graph`: the simple graph of an instance.
* `Cslib.Complexity.encUGraph`: the encoding of instances.
* `Cslib.Complexity.Bipartite`: the bipartite instances.
* `Cslib.Complexity.Bipartite.oddCycleInstance`: the copies of the double cover, as an instance
  of undirected connectivity.

## Main results

* `Cslib.Complexity.UGraphInstance.encode_injective`: the encoding is injective.
* `Cslib.Complexity.Bipartite.oddCycleInstance_mem_iff`: the source reaches the target exactly
  when the graph is not bipartite.

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*][Goldreich2008]
-/

@[expose] public section

namespace Cslib.Complexity

/-- An **undirected graph** on `Fin n`, given by its adjacency matrix, symmetric and with zero
diagonal. -/
structure UGraphInstance where
  /-- The number of vertices. -/
  n : ℕ
  /-- The adjacency matrix. -/
  adj : Fin n → Fin n → Bool
  /-- The matrix is symmetric. -/
  symm : ∀ a b, adj a b = adj b a
  /-- The diagonal is zero. -/
  loopless : ∀ a, adj a a = false

namespace UGraphInstance

variable (G : UGraphInstance)

/-- The simple graph of an instance. -/
def graph : SimpleGraph (Fin G.n) where
  Adj a b := G.adj a b = true
  symm.symm a b h := (G.symm b a).trans h
  loopless.irrefl a h := by simp [G.loopless] at h

@[simp]
theorem graph_adj {a b : Fin G.n} : G.graph.Adj a b ↔ G.adj a b = true :=
  Iff.rfl

/-- The digraph of an instance, with an arc in each direction for every edge. -/
def toDigraph : DigraphInstance := ⟨G.n, G.adj⟩

theorem toDigraph_injective : Function.Injective toDigraph := by
  rintro ⟨n, adj, symm, loopless⟩ ⟨n', adj', symm', loopless'⟩ h
  simp only [toDigraph, DigraphInstance.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  simp only [heq_eq_eq] at h
  subst h
  rfl

/-- The encoding of an instance, that of its digraph (`Cslib.Complexity.encDigraph`): the unary
header `1^n 0`, then the adjacency matrix row by row. -/
def encode : List Bool := G.toDigraph.encode

/-- **The encoding is injective.** -/
theorem encode_injective : Function.Injective encode :=
  DigraphInstance.encode_injective.comp toDigraph_injective

/-- The entries of an instance on natural numbers, `false` outside the vertices. -/
def adjN (u v : ℕ) : Bool :=
  if h : u < G.n ∧ v < G.n then G.adj ⟨u, h.1⟩ ⟨v, h.2⟩ else false

theorem adjN_comm (u v : ℕ) : G.adjN u v = G.adjN v u := by
  unfold adjN
  by_cases h : u < G.n ∧ v < G.n
  · rw [dite_eq_left h, dite_eq_left ⟨h.2, h.1⟩]
    exact G.symm _ _
  · rw [dite_eq_right h, dite_eq_right fun h' => h ⟨h'.2, h'.1⟩]

end UGraphInstance

/-- The encoding of undirected graphs: the unary header `1^n 0`, then the adjacency matrix row by
row. -/
def encUGraph : UGraphInstance ↪ List Bool :=
  ⟨UGraphInstance.encode, UGraphInstance.encode_injective⟩

@[simp]
theorem encUGraph_apply (G : UGraphInstance) : encUGraph G = G.encode := rfl

/-- **Bipartite graphs**: the instances whose graph is 2-colourable. -/
def Bipartite : Set UGraphInstance :=
  {G | G.graph.IsBipartite}

theorem mem_Bipartite {G : UGraphInstance} : G ∈ Bipartite ↔ G.graph.IsBipartite :=
  Iff.rfl

namespace Bipartite

/-! ### The numbering of the copies of the double cover -/

variable (n : ℕ)

/-- The number of vertices: two copies of each of the `n` vertices in each of the `n` copies, a
source and a target. -/
def numVertices : ℕ := 2 * n * n + 2

theorem le_numVertices : n ≤ numVertices n := by
  have := Nat.le_mul_self n
  rw [numVertices, Nat.mul_assoc]
  omega

/-- The vertex `(v, b)` of the copy `x`. -/
def copyVertex (x v : ℕ) (b : Bool) : ℕ := 2 + 2 * n * x + 2 * v + b.toNat

/-- The copy of a vertex numbered at least `2`. -/
def copy (r : ℕ) : ℕ := (r - 2) / (2 * n)

/-- The vertex of the graph that a vertex numbered at least `2` stands for. -/
def vert (r : ℕ) : ℕ := (r - 2) % (2 * n) / 2

/-- The side of a vertex numbered at least `2`. -/
def side (r : ℕ) : ℕ := (r - 2) % 2

variable {n}

private theorem two_mul_add_lt {v : ℕ} (b : Bool) (hv : v < n) : 2 * v + b.toNat < 2 * n := by
  cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

theorem two_le_copyVertex (x v : ℕ) (b : Bool) : 2 ≤ copyVertex n x v b := by
  unfold copyVertex
  omega

theorem copy_copyVertex {x v : ℕ} (b : Bool) (hv : v < n) : copy n (copyVertex n x v b) = x := by
  have h := two_mul_add_lt b hv
  simp only [copy, copyVertex]
  rw [show 2 + 2 * n * x + 2 * v + b.toNat - 2 = (2 * v + b.toNat) + 2 * n * x by omega,
    Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt h, Nat.zero_add]

theorem vert_copyVertex (x : ℕ) {v : ℕ} (b : Bool) (hv : v < n) :
    vert n (copyVertex n x v b) = v := by
  have h := two_mul_add_lt b hv
  simp only [vert, copyVertex]
  rw [show 2 + 2 * n * x + 2 * v + b.toNat - 2 = (2 * v + b.toNat) + 2 * n * x by omega,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]
  cases b <;> simp; omega

theorem side_copyVertex (x v : ℕ) (b : Bool) : side (copyVertex n x v b) = b.toNat := by
  simp only [side, copyVertex]
  rw [show 2 + 2 * n * x + 2 * v + b.toNat - 2 = b.toNat + 2 * (n * x + v) by
    rw [Nat.mul_assoc]; omega, Nat.add_mul_mod_self_left]
  cases b <;> rfl

theorem copyVertex_lt {x v : ℕ} (b : Bool) (hx : x < n) (hv : v < n) :
    copyVertex n x v b < numVertices n := by
  have h := two_mul_add_lt b hv
  have : 2 * n * x + 2 * n ≤ 2 * n * n := by
    rw [← Nat.mul_succ]
    exact Nat.mul_le_mul_left _ hx
  simp only [copyVertex, numVertices]
  omega

/-- **Every vertex numbered at least `2` is a vertex of a copy.** -/
theorem eq_copyVertex {r : ℕ} (h₂ : 2 ≤ r) (hr : r < numVertices n) :
    copy n r < n ∧ vert n r < n ∧ side r < 2 ∧
      r = copyVertex n (copy n r) (vert n r) (decide (side r = 1)) := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp [numVertices] at hr
      omega
    · exact h
  have hq : r - 2 < 2 * n * n := by simp only [numVertices] at hr; omega
  have hdiv := Nat.div_add_mod (r - 2) (2 * n)
  have hmod := Nat.mod_lt (r - 2) (show 0 < 2 * n by omega)
  have hmod2 := Nat.div_add_mod ((r - 2) % (2 * n)) 2
  have hside : side r = (r - 2) % (2 * n) % 2 := by
    simp only [side]
    rw [Nat.mod_mod_of_dvd _ (Dvd.intro n rfl)]
  have hs : side r < 2 := Nat.mod_lt _ (by omega)
  refine ⟨Nat.div_lt_of_lt_mul (by rwa [Nat.mul_assoc, Nat.mul_comm n, ← Nat.mul_assoc]),
    by simp only [vert]; omega, hs, ?_⟩
  simp only [copyVertex, copy, vert]
  have hb : (decide (side r = 1)).toNat = side r := by
    rcases (show side r = 0 ∨ side r = 1 by omega) with h | h <;> simp [h]
  rw [hb, hside]
  omega

/-! ### The instance -/

variable (G : UGraphInstance)

/-- The edges of the copies of the double cover, the source and the target, on natural numbers:
within a copy, `(u, b)` and `(v, !b)` are joined when `u` and `v` are; the source `0` is joined to
`(x, 0)` and the target `1` to `(x, 1)` in the copy `x`. -/
def entry (r c : ℕ) : Bool :=
  if 2 ≤ r ∧ 2 ≤ c ∧ copy G.n r = copy G.n c ∧ side r ≠ side c then
    G.adjN (vert G.n r) (vert G.n c)
  else
    decide (r < 2 ∧ 2 ≤ c ∧ vert G.n c = copy G.n c ∧ side c = r) ||
      decide (2 ≤ r ∧ c < 2 ∧ vert G.n r = copy G.n r ∧ side r = c)

theorem entry_comm (r c : ℕ) : entry G r c = entry G c r := by
  unfold entry
  by_cases h : 2 ≤ r ∧ 2 ≤ c ∧ copy G.n r = copy G.n c ∧ side r ≠ side c
  · rw [ite_eq_left h, ite_eq_left ⟨h.2.1, h.1, h.2.2.1.symm, Ne.symm h.2.2.2⟩, G.adjN_comm]
  · rw [ite_eq_right h, ite_eq_right fun h' => h ⟨h'.2.1, h'.1, h'.2.2.1.symm, Ne.symm h'.2.2.2⟩,
      Bool.or_comm]
    congr 1 <;> simp only [decide_eq_decide] <;> tauto

theorem entry_self (r : ℕ) : entry G r r = false := by
  simp only [entry, ne_eq, not_true_eq_false, and_false, ↓reduceIte, Bool.or_eq_false_iff,
    decide_eq_false_iff_not, not_and]
  omega

/-- **The copies of the double cover**, with the source `0` and the target `1`, as an instance of
undirected connectivity. -/
def oddCycleInstance : USTCONInstance where
  n := numVertices G.n
  adj a b := entry G a b
  symm a b := entry_comm G a b
  loopless a := entry_self G a
  s := ⟨0, by simp [numVertices]⟩
  t := ⟨1, by simp [numVertices]⟩

/-- The vertex `(v, b)` of the copy `x`, as a vertex of the instance. -/
def cv {x v : ℕ} (hx : x < G.n) (hv : v < G.n) (b : Bool) : Fin (oddCycleInstance G).n :=
  ⟨copyVertex G.n x v b, copyVertex_lt b hx hv⟩

/-- An edge `{u, v}` of the graph joins `(u, b)` and `(v, !b)` in every copy. -/
theorem adj_cv {x : ℕ} (hx : x < G.n) {u v : Fin G.n} (h : G.graph.Adj u v) (b : Bool) :
    (oddCycleInstance G).graph.Adj (cv G hx u.isLt b) (cv G hx v.isLt (!b)) := by
  have key : entry G (copyVertex G.n x u b) (copyVertex G.n x v (!b)) = G.adj u v := by
    unfold entry
    rw [ite_eq_left ⟨by unfold copyVertex; omega, by unfold copyVertex; omega,
      by rw [copy_copyVertex _ u.isLt, copy_copyVertex _ v.isLt],
      by rw [side_copyVertex, side_copyVertex]; cases b <;> simp⟩,
      vert_copyVertex _ _ u.isLt, vert_copyVertex _ _ v.isLt, UGraphInstance.adjN,
      dite_eq_left ⟨u.isLt, v.isLt⟩]
  simpa [oddCycleInstance, cv, key] using h

/-- A walk of length `ℓ` from `v` to `w` gives a path from `(v, b)` to `(w, b xor parity ℓ)` in
every copy. -/
theorem reachable_cv_of_walk {x : ℕ} (hx : x < G.n) {v w : Fin G.n} (p : G.graph.Walk v w)
    (b : Bool) :
    (oddCycleInstance G).graph.Reachable (cv G hx v.isLt b)
      (cv G hx w.isLt (Bool.xor b p.length.bodd)) := by
  induction p generalizing b with
  | nil => simp
  | cons h p ih =>
    refine (adj_cv G hx h b).reachable.trans ?_
    have hb : (!b ^^ p.length.bodd) = (b ^^ (SimpleGraph.Walk.cons h p).length.bodd) := by
      cases b <;> simp [SimpleGraph.Walk.length_cons, Nat.bodd_succ]
    simpa only [hb] using ih (!b)

private theorem fin_two_aux {p q z : Fin 2} {s s' : ℕ} (hs : s < 2) (hs' : s' < 2) (hss : s ≠ s')
    (hpq : p ≠ q) (h : s = 0 ↔ p = z) : s' = 0 ↔ q = z := by
  have := p.isLt
  have := q.isLt
  have := z.isLt
  rw [Fin.ext_iff] at h ⊢
  rw [ne_eq, Fin.ext_iff] at hpq
  omega

/-- A set of vertices closed under adjacency contains everything reachable from its members. -/
private theorem mem_of_reachable {V : Type*} {H : SimpleGraph V} {S : Set V}
    (hS : ∀ a b, H.Adj a b → a ∈ S → b ∈ S) {a b : V} (h : H.Reachable a b) (ha : a ∈ S) :
    b ∈ S := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact ha
  | cons h _ ih => exact ih (hS _ _ h ha)

/-- **The source reaches the target exactly when the graph is not bipartite.** -/
theorem oddCycleInstance_mem_iff : oddCycleInstance G ∈ USTCON ↔ G ∉ Bipartite := by
  rw [mem_Bipartite, SimpleGraph.IsBipartite, SimpleGraph.two_colorable_iff_forall_loop_even]
  constructor
  · -- a 2-colouring `col` is respected by the copies: in the copy `x`, the side of `(v, b)` is
    -- `b` exactly when `v` has the colour of `x`
    rintro hst hall
    rw [← SimpleGraph.two_colorable_iff_forall_loop_even] at hall
    obtain ⟨col⟩ := hall
    let S : Set (Fin (oddCycleInstance G).n) := {a |
      a.val = 0 ∨ ∃ (_ : 2 ≤ a.val) (hx : copy G.n a.val < G.n) (hv : vert G.n a.val < G.n),
        (side a.val = 0 ↔ col ⟨vert G.n a.val, hv⟩ = col ⟨copy G.n a.val, hx⟩)}
    have hS : ∀ a b, (oddCycleInstance G).graph.Adj a b → a ∈ S → b ∈ S := by
      rintro ⟨a, ha⟩ ⟨b, hb⟩ hab haS
      simp only [USTCONInstance.graph_adj, oddCycleInstance] at hab
      simp only [S, Set.mem_ofPred_eq] at haS ⊢
      unfold entry at hab
      split_ifs at hab with hif
      · -- an edge within a copy changes both the side and the colour
        obtain ⟨ha2, hb2, hcopy, hside⟩ := hif
        rcases haS with h0 | ⟨-, hxa, hva, hiff⟩
        · omega
        obtain ⟨hxb, hvb, hsb, -⟩ := eq_copyVertex hb2 hb
        obtain ⟨-, -, hsa, -⟩ := eq_copyVertex ha2 ha
        rw [UGraphInstance.adjN, dite_eq_left ⟨hva, hvb⟩] at hab
        have hne := col.valid (show G.graph.Adj ⟨vert G.n a, hva⟩ ⟨vert G.n b, hvb⟩ from hab)
        have hx : (⟨copy G.n b, hxb⟩ : Fin G.n) = ⟨copy G.n a, hxa⟩ := Fin.ext hcopy.symm
        refine .inr ⟨hb2, hxb, hvb, ?_⟩
        rw [hx]
        exact fin_two_aux hsa hsb hside hne hiff
      · simp only [Bool.or_eq_true, decide_eq_true_eq] at hab
        rcases hab with ⟨ha2, hb2, hvc, hsb⟩ | ⟨ha2, hb2, hvc, hsa⟩
        · -- an edge from the source
          rcases haS with h0 | ⟨h₂, -⟩
          · obtain ⟨hxb, hvb, -, -⟩ := eq_copyVertex hb2 hb
            refine .inr ⟨hb2, hxb, hvb, ?_⟩
            have hx : (⟨vert G.n b, hvb⟩ : Fin G.n) = ⟨copy G.n b, hxb⟩ := Fin.ext hvc
            simp [hx, hsb, h0]
          · omega
        · -- an edge to the source or the target
          rcases haS with h0 | ⟨-, hxa, hva, hiff⟩
          · omega
          have hx : (⟨vert G.n a, hva⟩ : Fin G.n) = ⟨copy G.n a, hxa⟩ := Fin.ext hvc
          rw [hx] at hiff
          exact .inl (by simpa [← hsa] using hiff)
    have h1 : (oddCycleInstance G).t ∉ S := by
      simp only [S, Set.mem_ofPred_eq]
      rintro (h | ⟨h, -⟩) <;> simp [oddCycleInstance] at h
    exact h1 (mem_of_reachable hS hst (by simp only [S, Set.mem_ofPred_eq]; exact .inl rfl))
  · -- an odd closed walk at `x` joins `(x, 0)` and `(x, 1)` in the copy `x`
    intro h
    push Not at h
    obtain ⟨x, p, hp⟩ := h
    have hodd : p.length.bodd = true := by
      rw [Nat.not_even_iff_odd, Nat.odd_iff, Nat.mod_two_of_bodd] at hp
      cases h : p.length.bodd <;> simp_all
    have hreach := reachable_cv_of_walk G x.isLt p false
    rw [hodd] at hreach
    have hs : (oddCycleInstance G).graph.Adj (oddCycleInstance G).s (cv G x.isLt x.isLt false) := by
      simp [oddCycleInstance, cv, entry, two_le_copyVertex, copy_copyVertex _ x.isLt,
        vert_copyVertex _ _ x.isLt, side_copyVertex]
    have ht : (oddCycleInstance G).graph.Adj (cv G x.isLt x.isLt true) (oddCycleInstance G).t := by
      simp [oddCycleInstance, cv, entry, two_le_copyVertex, copy_copyVertex _ x.isLt,
        vert_copyVertex _ _ x.isLt, side_copyVertex]
    exact hs.reachable.trans (hreach.trans ht.reachable)

end Bipartite

end Cslib.Complexity
