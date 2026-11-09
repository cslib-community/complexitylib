/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TFNP
import CslibFrontier.Foundations.Data.BitString.List.Binary
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi

/-!
# Combinatorial principles for total search subclasses

The classical subclasses of `TFNP` introduced by Johnson, Papadimitriou and Yannakakis
[JohnsonPapadimitriouYannakakis1988] and by Papadimitriou [Papadimitriou1994PPAD] classify total
search problems by the finite combinatorial principle that guarantees a solution on the hypercube
`{0, 1} ^ n` (represented as bit strings `u : List Bool` of length `n`, with distinguished origin
`zeroVertex n = List.replicate n false`):

* **Local optimality (`PLS`)**: every finite directed graph with vertex costs has a local minimum
  (`localOptRel`, `isTotalSearch_localOptRel`).
* **Pigeonhole principle (`PPP`)**: every map `F : {0, 1} ^ n → {0, 1} ^ n` either hits `0 ^ n` or
  collides on two distinct vertices (`pigeonRel`, `isTotalSearch_pigeonRel`).
* **Directed parity / end-of-line (`PPAD`)**: in a directed graph where every vertex has in-degree
  and out-degree at most `1`, if `0 ^ n` has out-degree `1` (and in-degree `0`), there is another
  vertex that is either a sink or a proper source (`endOfLineRel`, `isTotalSearch_endOfLineRel`).
* **Undirected parity / handshaking (`PPA`)**: in a simple undirected graph of maximum degree `2`
  presented by two neighbor functions `N₁, N₂`, the number of odd-degree vertices is even; so either
  `0 ^ n` has even degree or another vertex has odd degree (`leafRel`, `isTotalSearch_leafRel`).

## Main definitions

* `Cslib.Complexity.zeroVertex`: the distinguished origin `0 ^ n = List.replicate n false`.
* `Cslib.Complexity.localOptRel`: the local-search relation for `PLS`.
* `Cslib.Complexity.pigeonRel`: the pigeonhole relation for `PPP`.
* `Cslib.Complexity.hasOut`, `Cslib.Complexity.hasIn`, `Cslib.Complexity.endOfLineRel`: active
  directed edges and the end-of-line relation for `PPAD`.
* `Cslib.Complexity.undirectedEdge`, `Cslib.Complexity.hasOddDegree`, `Cslib.Complexity.leafRel`:
  undirected edges, odd-degree test and the leaf relation for `PPA`.

## Main results

* `Cslib.Complexity.exists_localOpt`, `Cslib.Complexity.isTotalSearch_localOptRel`.
* `Cslib.Complexity.exists_pigeon`, `Cslib.Complexity.isTotalSearch_pigeonRel`.
* `Cslib.Complexity.exists_endOfLine`, `Cslib.Complexity.isTotalSearch_endOfLineRel`,
  `Cslib.Complexity.endOfLineRel_of_pigeonRel`: the directed end-of-line principle and its
  reduction to the pigeonhole principle.
* `Cslib.Complexity.exists_leaf`, `Cslib.Complexity.isTotalSearch_leafRel`,
  `Cslib.Complexity.endOfLineRel_tail_of_leafRel`: the finite parity principle and the reduction
  of directed end-of-line to undirected parity.

## References

* [D. S. Johnson, C. H. Papadimitriou, M. Yannakakis, *How easy is local
  search?*][JohnsonPapadimitriouYannakakis1988]
* [C. H. Papadimitriou, *On the complexity of the parity argument and other inefficient proofs of
  existence*][Papadimitriou1994PPAD]
* [P. Beame, S. Cook, J. Edmonds, R. Impagliazzo, T. Pitassi, *The relative complexity of NP
  search problems*][BeameEtAl1998]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.BitString

variable {α : Type}

/-! ### Fixed-length bit strings -/

/-- The distinguished origin vertex `0 ^ n` of `{0, 1} ^ n`. -/
def zeroVertex (n : ℕ) : List Bool := List.replicate n false

@[simp]
theorem length_zeroVertex (n : ℕ) : (zeroVertex n).length = n :=
  List.length_replicate

/-- Bit strings of length `n` as a subtype. -/
private abbrev Vertex (n : ℕ) : Type := {u : List Bool // u.length = n}

/-- Equivalence between bit strings of length `n` and functions `Fin n → Bool`. -/
private def vertexEquiv (n : ℕ) : Vertex n ≃ (Fin n → Bool) where
  toFun u i := u.1[i.val]'(i.isLt.trans_eq u.2.symm)
  invFun f := ⟨List.ofFn f, List.length_ofFn⟩
  left_inv u := Subtype.ext (List.ext_getElem (by simp [u.2]) fun i _ _ => by simp)
  right_inv f := funext fun i => by simp

private instance instFintypeVertex (n : ℕ) : Fintype (Vertex n) :=
  Fintype.ofEquiv (Fin n → Bool) (vertexEquiv n).symm

/-! ### Local optimality (`PLS`) -/

/-- The search relation of a local-search family (`PLS`): given bit-length `n a`, neighbor function
`N` and cost function `C`, a vertex `u` of length `n a` is a solution if its neighbor `N (a, u)`
does not have strictly smaller cost. -/
def localOptRel (n : α → ℕ) (N : α × List Bool → List Bool) (C : α × List Bool → ℕ)
    (a : α) (u : List Bool) : Prop :=
  u.length = n a ∧ C (a, u) ≤ C (a, N (a, u))

/-- **Finite local-optimum principle**: if `N (a, ·)` preserves length `n a`, some vertex of length
`n a` is a local minimum of `C (a, ·)`. -/
theorem exists_localOpt {n : α → ℕ} {N : α × List Bool → List Bool} {C : α × List Bool → ℕ}
    {a : α} (hN : ∀ u, u.length = n a → (N (a, u)).length = n a) :
    ∃ u, localOptRel n N C a u := by
  have hne : (Finset.univ : Finset (Vertex (n a))).Nonempty :=
    ⟨⟨zeroVertex (n a), length_zeroVertex (n a)⟩, Finset.mem_univ _⟩
  obtain ⟨u, -, hmin⟩ :=
    Finset.exists_min_image Finset.univ (fun u : Vertex (n a) => C (a, u.1)) hne
  exact ⟨u.1, u.2, hmin ⟨N (a, u.1), hN u.1 u.2⟩ (Finset.mem_univ _)⟩

/-- `localOptRel` is total whenever the neighbor map preserves the vertex bit-length. -/
theorem isTotalSearch_localOptRel {n : α → ℕ} {N : α × List Bool → List Bool}
    {C : α × List Bool → ℕ} (hN : ∀ a u, u.length = n a → (N (a, u)).length = n a) :
    IsTotalSearch (localOptRel n N C) :=
  fun a => exists_localOpt (hN a)

/-! ### Pigeonhole principle (`PPP`) -/

/-- The search relation of a pigeonhole family (`PPP`): a candidate `w` of length `2 * n a` encodes
the pair of `n a`-bit strings `u = w.take (n a)` and `v = w.drop (n a)`, and is a solution if
`F (a, u) = 0 ^ (n a)` or `u ≠ v` with `F (a, u) = F (a, v)`. -/
def pigeonRel (n : α → ℕ) (F : α × List Bool → List Bool) (a : α) (w : List Bool) : Prop :=
  w.length = 2 * n a ∧
    (F (a, w.take (n a)) = zeroVertex (n a) ∨
      w.take (n a) ≠ w.drop (n a) ∧ F (a, w.take (n a)) = F (a, w.drop (n a)))

/-- **Finite pigeonhole principle**: any length-preserving map `F (a, ·)` on `{0, 1} ^ (n a)` either
hits `0 ^ (n a)` or collides on two distinct strings of length `n a`. -/
theorem exists_pigeon {n : α → ℕ} {F : α × List Bool → List Bool} {a : α}
    (hF : ∀ u, u.length = n a → (F (a, u)).length = n a) :
    ∃ w, pigeonRel n F a w := by
  let f : Vertex (n a) → Vertex (n a) := fun u => ⟨F (a, u.1), hF u.1 u.2⟩
  by_cases hinj : Function.Injective f
  · obtain ⟨u, hu⟩ := Finite.surjective_of_injective hinj
      ⟨zeroVertex (n a), length_zeroVertex (n a)⟩
    refine ⟨u.1 ++ u.1, ?_, .inl ?_⟩
    · simp [u.2, Nat.two_mul]
    · rw [List.take_left' u.2]
      exact congrArg Subtype.val hu
  · simp only [Function.Injective, not_forall] at hinj
    obtain ⟨u, v, huv, hne⟩ := hinj
    refine ⟨u.1 ++ v.1, ?_, .inr ?_⟩
    · simp [u.2, v.2, Nat.two_mul]
    · rw [List.take_left' u.2, List.drop_left' u.2]
      exact ⟨fun h => hne (Subtype.ext h), congrArg Subtype.val huv⟩

/-- `pigeonRel` is total whenever `F` preserves the vertex bit-length. -/
theorem isTotalSearch_pigeonRel {n : α → ℕ} {F : α × List Bool → List Bool}
    (hF : ∀ a u, u.length = n a → (F (a, u)).length = n a) :
    IsTotalSearch (pigeonRel n F) :=
  fun a => exists_pigeon (hF a)

/-! ### Directed end-of-line principle (`PPAD`) -/

/-- Vertex `u` has an active outgoing edge to `S (a, u)` in the directed graph presented by
predecessor `P` and successor `S`: `P` points back from `S (a, u)` to `u`, and `S (a, u)` is neither
a self-loop nor the canonical source `0 ^ (n a)`. -/
def hasOut (n : α → ℕ) (P S : α × List Bool → List Bool) (a : α) (u : List Bool) : Bool :=
  decide (P (a, S (a, u)) = u ∧ S (a, u) ≠ u ∧ S (a, u) ≠ zeroVertex (n a))

/-- Vertex `u` has an active incoming edge from `P (a, u)` in the directed graph presented by `P`
and `S`: `S` points forward from `P (a, u)` to `u`, `P (a, u) ≠ u`, and `u` is not the canonical
source `0 ^ (n a)`. -/
def hasIn (n : α → ℕ) (P S : α × List Bool → List Bool) (a : α) (u : List Bool) : Bool :=
  decide (S (a, P (a, u)) = u ∧ P (a, u) ≠ u ∧ u ≠ zeroVertex (n a))

/-- If `u` has an active outgoing edge to `v = S (a, u)`, then `v` has an active incoming edge from
`u = P (a, v)`. -/
theorem hasIn_of_hasOut {n : α → ℕ} {P S : α × List Bool → List Bool} {a : α} {u : List Bool}
    (h : hasOut n P S a u = true) : hasIn n P S a (S (a, u)) = true := by
  simp only [hasOut, decide_eq_true_eq] at h
  simp only [hasIn, decide_eq_true_eq]
  exact ⟨by rw [h.1], by rw [h.1]; exact h.2.1.symm, h.2.2⟩

/-- If `u` has an active incoming edge from `v = P (a, u)`, then `v` has an active outgoing edge to
`u = S (a, v)`. -/
theorem hasOut_of_hasIn {n : α → ℕ} {P S : α × List Bool → List Bool} {a : α} {u : List Bool}
    (h : hasIn n P S a u = true) : hasOut n P S a (P (a, u)) = true := by
  simp only [hasIn, decide_eq_true_eq] at h
  simp only [hasOut, decide_eq_true_eq]
  exact ⟨by rw [h.1], by rw [h.1]; exact h.2.1.symm, by rw [h.1]; exact h.2.2⟩

/-- The canonical source `0 ^ (n a)` never has an active incoming edge. -/
@[simp]
theorem hasIn_zeroVertex (n : α → ℕ) (P S : α × List Bool → List Bool) (a : α) :
    hasIn n P S a (zeroVertex (n a)) = false := by
  simp [hasIn]

/-- The search relation of a directed end-of-line family (`PPAD`): a vertex `u` of length `n a` is a
solution if its incoming/outgoing parity is unbalanced relative to `0 ^ (n a)`: either
`u = 0 ^ (n a)` and `u` has no active outgoing edge (`!hasOut`), or `u ≠ 0 ^ (n a)` and `u` is a
sink (`hasIn ∧ !hasOut`) or proper source (`!hasIn ∧ hasOut`). -/
def endOfLineRel (n : α → ℕ) (P S : α × List Bool → List Bool) (a : α) (u : List Bool) : Prop :=
  u.length = n a ∧
    ((hasIn n P S a u != hasOut n P S a u) == decide (u ≠ zeroVertex (n a))) = true

/-- The canonical source `0 ^ (n a)` solves `endOfLineRel` whenever it lacks an active outgoing
edge. -/
theorem endOfLineRel_zeroVertex_of_hasOut_eq_false {n : α → ℕ} {P S : α × List Bool → List Bool}
    {a : α} (h : hasOut n P S a (zeroVertex (n a)) = false) :
    endOfLineRel n P S a (zeroVertex (n a)) := by
  simp [endOfLineRel, h]

/-- Any vertex `u` of length `n a` with an active incoming edge and no active outgoing edge solves
`endOfLineRel`. -/
theorem endOfLineRel_of_hasIn_of_hasOut_eq_false {n : α → ℕ} {P S : α × List Bool → List Bool}
    {a : α} {u : List Bool} (hlen : u.length = n a) (hin : hasIn n P S a u = true)
    (hout : hasOut n P S a u = false) :
    endOfLineRel n P S a u := by
  have hne : u ≠ zeroVertex (n a) := by
    rintro rfl
    simp [hasIn_zeroVertex] at hin
  simp [endOfLineRel, hlen, hin, hout, hne]

/-- The pigeonhole map used to reduce `endOfLineRel` to `pigeonRel`: follow active outgoing edges,
and fix every vertex that lacks an active outgoing edge. -/
def ppadToPppMap (n : α → ℕ) (P S : α × List Bool → List Bool) (p : α × List Bool) : List Bool :=
  if hasOut n P S p.1 p.2 then S p else p.2

theorem length_ppadToPppMap {n : α → ℕ} {P S : α × List Bool → List Bool} {a : α} {u : List Bool}
    (hS : ∀ u, u.length = n a → (S (a, u)).length = n a) (hu : u.length = n a) :
    (ppadToPppMap n P S (a, u)).length = n a := by
  unfold ppadToPppMap
  split_ifs
  · exact hS u hu
  · exact hu

/-- Any solution of `pigeonRel` for `ppadToPppMap n P S` yields a solution of `endOfLineRel n P S`
by selecting whichever of the two `n a`-bit halves lacks an active outgoing edge. -/
theorem endOfLineRel_of_pigeonRel {n : α → ℕ} {P S : α × List Bool → List Bool} {a : α}
    {w : List Bool} (h : pigeonRel n (ppadToPppMap n P S) a w) :
    endOfLineRel n P S a
      (if !hasOut n P S a (w.take (n a)) then w.take (n a) else w.drop (n a)) := by
  obtain ⟨hwlen, hsol⟩ := h
  have hu_len : (w.take (n a)).length = n a := by simp only [List.length_take, hwlen]; omega
  have hv_len : (w.drop (n a)).length = n a := by simp only [List.length_drop, hwlen]; omega
  rcases hsol with hz | ⟨hne, hcoll⟩
  · have hu : hasOut n P S a (w.take (n a)) = false := by
      by_contra hu'
      simp only [Bool.not_eq_false] at hu'
      have hFz : S (a, w.take (n a)) = zeroVertex (n a) := by
        simpa [ppadToPppMap, hu'] using hz
      simp only [hasOut, decide_eq_true_eq] at hu'
      exact hu'.2.2 hFz
    have huz : w.take (n a) = zeroVertex (n a) := by
      simpa [ppadToPppMap, hu] using hz
    simp only [hu, Bool.not_false, ↓reduceIte]
    rw [huz]
    exact endOfLineRel_zeroVertex_of_hasOut_eq_false (huz ▸ hu)
  · by_cases hu : hasOut n P S a (w.take (n a)) = false
    · simp only [hu, Bool.not_false, ↓reduceIte]
      have hv : hasOut n P S a (w.drop (n a)) = true := by
        by_contra hv'
        simp only [Bool.not_eq_true] at hv'
        have huv : w.take (n a) = w.drop (n a) := by
          simpa [ppadToPppMap, hu, hv'] using hcoll
        exact hne huv
      have hSv : w.take (n a) = S (a, w.drop (n a)) := by
        simpa [ppadToPppMap, hu, hv] using hcoll
      exact endOfLineRel_of_hasIn_of_hasOut_eq_false hu_len (hSv ▸ hasIn_of_hasOut hv) hu
    · simp only [Bool.not_eq_false] at hu
      simp only [hu, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      have hv : hasOut n P S a (w.drop (n a)) = false := by
        by_contra hv'
        simp only [Bool.not_eq_false] at hv'
        have hSuv : S (a, w.take (n a)) = S (a, w.drop (n a)) := by
          simpa [ppadToPppMap, hu, hv'] using hcoll
        simp only [hasOut, decide_eq_true_eq] at hu hv'
        exact hne (by rw [← hu.1, hSuv, hv'.1])
      have hSu : S (a, w.take (n a)) = w.drop (n a) := by
        simpa [ppadToPppMap, hu, hv] using hcoll
      exact endOfLineRel_of_hasIn_of_hasOut_eq_false hv_len (hSu ▸ hasIn_of_hasOut hu) hv

/-- **Directed end-of-line principle**: if `S (a, ·)` preserves length `n a`, some vertex of length
`n a` satisfies `endOfLineRel`. -/
theorem exists_endOfLine {n : α → ℕ} {P S : α × List Bool → List Bool} {a : α}
    (hS : ∀ u, u.length = n a → (S (a, u)).length = n a) :
    ∃ u, endOfLineRel n P S a u := by
  obtain ⟨w, hw⟩ := exists_pigeon (n := n) (F := ppadToPppMap n P S) (a := a)
    (fun u hu => length_ppadToPppMap hS hu)
  exact ⟨_, endOfLineRel_of_pigeonRel hw⟩

/-- `endOfLineRel` is total whenever the successor map preserves the vertex bit-length. -/
theorem isTotalSearch_endOfLineRel {n : α → ℕ} {P S : α × List Bool → List Bool}
    (hS : ∀ a u, u.length = n a → (S (a, u)).length = n a) :
    IsTotalSearch (endOfLineRel n P S) :=
  fun a => exists_endOfLine (hS a)

/-! ### Undirected parity / handshake principle (`PPA`) -/

/-- Undirected edge between `u` and `v` in the graph of maximum degree `2` presented by two neighbor
functions `N₁, N₂`: `u ≠ v`, `v` is listed by `u`, and `u` is listed by `v`. -/
def undirectedEdge (N₁ N₂ : α × List Bool → List Bool) (a : α) (u v : List Bool) : Bool :=
  decide (u ≠ v ∧ (N₁ (a, u) = v ∨ N₂ (a, u) = v) ∧ (N₁ (a, v) = u ∨ N₂ (a, v) = u))

theorem undirectedEdge_comm (N₁ N₂ : α × List Bool → List Bool) (a : α) (u v : List Bool) :
    undirectedEdge N₁ N₂ a u v = undirectedEdge N₁ N₂ a v u := by
  simp only [undirectedEdge, decide_eq_decide]
  exact ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨h₁.symm, h₃, h₂⟩, fun ⟨h₁, h₂, h₃⟩ => ⟨h₁.symm, h₃, h₂⟩⟩

@[simp]
theorem undirectedEdge_self (N₁ N₂ : α × List Bool → List Bool) (a : α) (u : List Bool) :
    undirectedEdge N₁ N₂ a u u = false := by
  simp [undirectedEdge]

theorem eq_or_eq_of_undirectedEdge {N₁ N₂ : α × List Bool → List Bool} {a : α} {u v : List Bool}
    (h : undirectedEdge N₁ N₂ a u v = true) : v = N₁ (a, u) ∨ v = N₂ (a, u) := by
  simp only [undirectedEdge, decide_eq_true_eq] at h
  exact h.2.1.imp Eq.symm Eq.symm

/-- Vertex `u` has odd degree (degree `1`) in the undirected graph presented by `N₁, N₂`. -/
def hasOddDegree (N₁ N₂ : α × List Bool → List Bool) (a : α) (u : List Bool) : Bool :=
  undirectedEdge N₁ N₂ a u (N₁ (a, u)) !=
    (undirectedEdge N₁ N₂ a u (N₂ (a, u)) && decide (N₂ (a, u) ≠ N₁ (a, u)))

/-- The search relation of an undirected parity family (`PPA`): a vertex `u` of length `n a` is a
solution if either `u = 0 ^ (n a)` has even degree or `u ≠ 0 ^ (n a)` has odd degree. -/
def leafRel (n : α → ℕ) (N₁ N₂ : α × List Bool → List Bool) (a : α) (u : List Bool) : Prop :=
  u.length = n a ∧ (hasOddDegree N₁ N₂ a u == decide (u ≠ zeroVertex (n a))) = true

/-- Sum of incident edges at `u` equals the sum of the two neighbor indicators. -/
private theorem sum_undirectedEdge_eq {n : α → ℕ} {N₁ N₂ : α × List Bool → List Bool} {a : α}
    (hN₁ : ∀ u, u.length = n a → (N₁ (a, u)).length = n a)
    (hN₂ : ∀ u, u.length = n a → (N₂ (a, u)).length = n a) (u : Vertex (n a)) :
    (∑ v : Vertex (n a), (undirectedEdge N₁ N₂ a u.1 v.1).toNat) =
      (undirectedEdge N₁ N₂ a u.1 (N₁ (a, u.1))).toNat +
        (undirectedEdge N₁ N₂ a u.1 (N₂ (a, u.1)) && decide (N₂ (a, u.1) ≠ N₁ (a, u.1))).toNat := by
  let v₁ : Vertex (n a) := ⟨N₁ (a, u.1), hN₁ u.1 u.2⟩
  let v₂ : Vertex (n a) := ⟨N₂ (a, u.1), hN₂ u.1 u.2⟩
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v₁)]
  by_cases h12 : v₂ = v₁
  · have h12_val : N₂ (a, u.1) = N₁ (a, u.1) := congrArg Subtype.val h12
    have hzero : ∑ v ∈ Finset.univ.erase v₁, (undirectedEdge N₁ N₂ a u.1 v.1).toNat = 0 := by
      refine Finset.sum_eq_zero fun v hv => ?_
      have hne : v.1 ≠ N₁ (a, u.1) := fun h => (Finset.mem_erase.1 hv).1 (Subtype.ext h)
      cases he : undirectedEdge N₁ N₂ a u.1 v.1
      · rfl
      · rcases eq_or_eq_of_undirectedEdge he with h | h
        · exact (hne h).elim
        · exact (hne (h.trans h12_val)).elim
    simp [hzero, h12_val, v₁]
  · have hv₂_mem : v₂ ∈ Finset.univ.erase v₁ :=
      Finset.mem_erase.2 ⟨h12, Finset.mem_univ v₂⟩
    rw [← Finset.add_sum_erase _ _ hv₂_mem]
    have hzero : ∑ v ∈ (Finset.univ.erase v₁).erase v₂,
        (undirectedEdge N₁ N₂ a u.1 v.1).toNat = 0 := by
      refine Finset.sum_eq_zero fun v hv => ?_
      have hne₂ : v.1 ≠ N₂ (a, u.1) := fun h => (Finset.mem_erase.1 hv).1 (Subtype.ext h)
      have hne₁ : v.1 ≠ N₁ (a, u.1) :=
        fun h => (Finset.mem_erase.1 (Finset.mem_erase.1 hv).2).1 (Subtype.ext h)
      cases he : undirectedEdge N₁ N₂ a u.1 v.1
      · rfl
      · rcases eq_or_eq_of_undirectedEdge he with h | h
        · exact (hne₁ h).elim
        · exact (hne₂ h).elim
    have h12_val : N₂ (a, u.1) ≠ N₁ (a, u.1) := fun h => h12 (Subtype.ext h)
    simp [hzero, h12_val, v₁, v₂]

/-- The double sum of undirected edges over all ordered pairs is even. -/
private theorem even_sum_undirectedEdge (n : α → ℕ) (N₁ N₂ : α × List Bool → List Bool) (a : α) :
    (∑ u : Vertex (n a), ∑ v : Vertex (n a), (undirectedEdge N₁ N₂ a u.1 v.1).toNat) % 2 = 0 := by
  let g (u v : Vertex (n a)) : ℕ :=
    if binaryValue u.1 < binaryValue v.1 then (undirectedEdge N₁ N₂ a u.1 v.1).toNat else 0
  have hpt (u v : Vertex (n a)) :
      (undirectedEdge N₁ N₂ a u.1 v.1).toNat = g u v + g v u := by
    by_cases huv : u = v
    · subst huv
      simp [g]
    · have hbv : binaryValue u.1 ≠ binaryValue v.1 := fun h =>
        huv (Subtype.ext (binaryValue_injective_of_length_eq (u.2.trans v.2.symm) h))
      have hcomm := undirectedEdge_comm N₁ N₂ a u.1 v.1
      rcases lt_or_gt_of_ne hbv with hlt | hgt
      · have hnot : ¬binaryValue v.1 < binaryValue u.1 := Nat.not_lt.2 hlt.le
        simp [g, hlt, hnot]
      · have hnot : ¬binaryValue u.1 < binaryValue v.1 := Nat.not_lt.2 hgt.le
        simp [g, hgt, hnot, hcomm]
  have hsum : (∑ u : Vertex (n a), ∑ v : Vertex (n a), (undirectedEdge N₁ N₂ a u.1 v.1).toNat) =
      2 * ∑ u : Vertex (n a), ∑ v : Vertex (n a), g u v := by
    simp_rw [hpt, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun u v => g v u), Nat.two_mul]
  rw [hsum, Nat.mul_mod_right]

private theorem bne_eq_true_iff_add_mod_two (b₁ b₂ : Bool) :
    (b₁ != b₂) = true ↔ (b₁.toNat + b₂.toNat) % 2 = 1 := by
  cases b₁ <;> cases b₂ <;> decide

private theorem bne_eq_false_iff_add_mod_two (b₁ b₂ : Bool) :
    (b₁ != b₂) = false ↔ (b₁.toNat + b₂.toNat) % 2 = 0 := by
  cases b₁ <;> cases b₂ <;> decide

/-- **Finite parity / handshake principle**: if `N₁ (a, ·)` and `N₂ (a, ·)` preserve length `n a`,
some vertex of length `n a` satisfies `leafRel`. -/
theorem exists_leaf {n : α → ℕ} {N₁ N₂ : α × List Bool → List Bool} {a : α}
    (hN₁ : ∀ u, u.length = n a → (N₁ (a, u)).length = n a)
    (hN₂ : ∀ u, u.length = n a → (N₂ (a, u)).length = n a) :
    ∃ u, leafRel n N₁ N₂ a u := by
  by_contra! hno
  let z : Vertex (n a) := ⟨zeroVertex (n a), length_zeroVertex (n a)⟩
  have hdeg (u : Vertex (n a)) :
      (∑ v : Vertex (n a), (undirectedEdge N₁ N₂ a u.1 v.1).toNat) % 2 =
        if u = z then 1 else 0 := by
    have hu := hno u.1
    rw [sum_undirectedEdge_eq hN₁ hN₂ u]
    by_cases huz : u = z
    · subst huz
      have hz_odd : hasOddDegree N₁ N₂ a z.1 = true := by
        simpa [leafRel, z, length_zeroVertex] using hu
      rw [ite_eq_left rfl]
      exact (bne_eq_true_iff_add_mod_two _ _).1 hz_odd
    · have huz_val : u.1 ≠ zeroVertex (n a) := fun h => huz (Subtype.ext h)
      have hu_even : hasOddDegree N₁ N₂ a u.1 = false := by
        simpa [leafRel, u.2, huz_val] using hu
      rw [ite_eq_right huz]
      exact (bne_eq_false_iff_add_mod_two _ _).1 hu_even
  have heven := even_sum_undirectedEdge n N₁ N₂ a
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ z)] at heven
  have herase : (∑ u ∈ Finset.univ.erase z,
      ∑ v : Vertex (n a), (undirectedEdge N₁ N₂ a u.1 v.1).toNat) % 2 = 0 := by
    refine Nat.dvd_iff_mod_eq_zero.1 (Finset.dvd_sum fun u hu => Nat.dvd_iff_mod_eq_zero.2 ?_)
    rw [hdeg u, ite_eq_right (Finset.mem_erase.1 hu).1]
  have hz_mod : (∑ v : Vertex (n a), (undirectedEdge N₁ N₂ a z.1 v.1).toNat) % 2 = 1 := by
    simpa using hdeg z
  omega

/-- `leafRel` is total whenever both neighbor maps preserve the vertex bit-length. -/
theorem isTotalSearch_leafRel {n : α → ℕ} {N₁ N₂ : α × List Bool → List Bool}
    (hN₁ : ∀ a u, u.length = n a → (N₁ (a, u)).length = n a)
    (hN₂ : ∀ a u, u.length = n a → (N₂ (a, u)).length = n a) :
    IsTotalSearch (leafRel n N₁ N₂) :=
  fun a => exists_leaf (hN₁ a) (hN₂ a)

/-! ### Reducing directed end-of-line (`PPAD`) to undirected parity (`PPA`) -/

/-- First neighbor map on `{0, 1} ^ (n a + 1)` for reducing `endOfLineRel` to `leafRel`:
`false :: u` is the outgoing port of `u`, matched with `true :: S (a, u)` when `hasOut n P S a u`
holds; `true :: u` is the incoming port of `u`, matched with `false :: P (a, u)` when
`hasIn n P S a u` holds. -/
def ppadToPpaN₁ (n : α → ℕ) (P S : α × List Bool → List Bool) (p : α × List Bool) : List Bool :=
  if !p.2.headD false then
    if hasOut n P S p.1 p.2.tail then true :: S (p.1, p.2.tail) else false :: p.2.tail
  else
    if hasIn n P S p.1 p.2.tail then false :: P (p.1, p.2.tail) else true :: p.2.tail

/-- Whether a vertex `u` is a non-source vertex (`u ≠ 0 ^ (n a)`) participating in at least one
active directed edge (`hasOut` or `hasIn`). -/
def isActiveNonZero (n : α → ℕ) (P S : α × List Bool → List Bool) (a : α) (u : List Bool) : Bool :=
  decide (u ≠ zeroVertex (n a)) && (hasOut n P S a u || hasIn n P S a u)

/-- Second neighbor map on `{0, 1} ^ (n a + 1)` for reducing `endOfLineRel` to `leafRel`:
internally pairs `false :: u` and `true :: u` for every vertex `u ≠ 0 ^ (n a)` that participates in
at least one active directed edge (`hasOut` or `hasIn`), leaving the ports of `0 ^ (n a)` and
isolated vertices unpaired. -/
def ppadToPpaN₂ (n : α → ℕ) (P S : α × List Bool → List Bool) (p : α × List Bool) : List Bool :=
  if isActiveNonZero n P S p.1 p.2.tail then
    (!p.2.headD false) :: p.2.tail
  else
    p.2.headD false :: p.2.tail

@[simp]
theorem ppadToPpaN₁_false_cons (n : α → ℕ) (P S : α × List Bool → List Bool) (a : α)
    (u : List Bool) :
    ppadToPpaN₁ n P S (a, false :: u) =
      if hasOut n P S a u then true :: S (a, u) else false :: u := rfl

@[simp]
theorem ppadToPpaN₁_true_cons (n : α → ℕ) (P S : α × List Bool → List Bool) (a : α)
    (u : List Bool) :
    ppadToPpaN₁ n P S (a, true :: u) =
      if hasIn n P S a u then false :: P (a, u) else true :: u := rfl

@[simp]
theorem ppadToPpaN₂_cons (n : α → ℕ) (P S : α × List Bool → List Bool) (a : α) (b : Bool)
    (u : List Bool) :
    ppadToPpaN₂ n P S (a, b :: u) =
      if isActiveNonZero n P S a u then (!b) :: u else b :: u := rfl

theorem length_ppadToPpaN₁ {n : α → ℕ} {P S : α × List Bool → List Bool} {a : α} {w : List Bool}
    (hP : ∀ u, u.length = n a → (P (a, u)).length = n a)
    (hS : ∀ u, u.length = n a → (S (a, u)).length = n a) (hw : w.length = n a + 1) :
    (ppadToPpaN₁ n P S (a, w)).length = n a + 1 := by
  have htail : w.tail.length = n a := by simp [hw]
  unfold ppadToPpaN₁
  split_ifs <;> simp [htail, hP _ htail, hS _ htail]

theorem length_ppadToPpaN₂ {n : α → ℕ} {P S : α × List Bool → List Bool} {a : α} {w : List Bool}
    (hw : w.length = n a + 1) :
    (ppadToPpaN₂ n P S (a, w)).length = n a + 1 := by
  have htail : w.tail.length = n a := by simp [hw]
  unfold ppadToPpaN₂
  split_ifs <;> simp [htail]

private theorem ppadToPpaN₁_invol (n : α → ℕ) (P S : α × List Bool → List Bool) (a : α)
    (b : Bool) (u : List Bool) :
    ppadToPpaN₁ n P S (a, ppadToPpaN₁ n P S (a, b :: u)) = b :: u := by
  cases b
  · rw [ppadToPpaN₁_false_cons]
    split_ifs with hout
    · have hin := hasIn_of_hasOut hout
      simp only [hasOut, decide_eq_true_eq] at hout
      simp [hin, hout.1]
    · simp [hout]
  · rw [ppadToPpaN₁_true_cons]
    split_ifs with hin
    · have hout := hasOut_of_hasIn hin
      simp only [hasIn, decide_eq_true_eq] at hin
      simp [hout, hin.1]
    · simp [hin]

private theorem ppadToPpaN₂_invol (n : α → ℕ) (P S : α × List Bool → List Bool) (a : α)
    (b : Bool) (u : List Bool) :
    ppadToPpaN₂ n P S (a, ppadToPpaN₂ n P S (a, b :: u)) = b :: u := by
  rw [ppadToPpaN₂_cons]
  split_ifs with hc <;> simp [hc]

private theorem undirectedEdge_left_of_invol {N₁ N₂ : α × List Bool → List Bool} {a : α}
    {w : List Bool} (h : N₁ (a, N₁ (a, w)) = w) :
    undirectedEdge N₁ N₂ a w (N₁ (a, w)) = decide (w ≠ N₁ (a, w)) := by
  simp [undirectedEdge, h]

private theorem undirectedEdge_right_of_invol {N₁ N₂ : α × List Bool → List Bool} {a : α}
    {w : List Bool} (h : N₂ (a, N₂ (a, w)) = w) :
    undirectedEdge N₁ N₂ a w (N₂ (a, w)) = decide (w ≠ N₂ (a, w)) := by
  simp [undirectedEdge, h]

private theorem decide_ne_ppadToPpaN₁ (n : α → ℕ) (P S : α × List Bool → List Bool)
    (a : α) (b : Bool) (u : List Bool) :
    decide (b :: u ≠ ppadToPpaN₁ n P S (a, b :: u)) =
      if b then hasIn n P S a u else hasOut n P S a u := by
  cases b
  · rw [ppadToPpaN₁_false_cons]
    cases hout : hasOut n P S a u <;> simp
  · rw [ppadToPpaN₁_true_cons]
    cases hin : hasIn n P S a u <;> simp

private theorem decide_ne_ppadToPpaN₂ (n : α → ℕ) (P S : α × List Bool → List Bool)
    (a : α) (b : Bool) (u : List Bool) :
    decide (b :: u ≠ ppadToPpaN₂ n P S (a, b :: u)) = isActiveNonZero n P S a u := by
  rw [ppadToPpaN₂_cons]
  cases hc : isActiveNonZero n P S a u <;> cases b <;> simp

private theorem ppadToPpaN₂_ne_ppadToPpaN₁ (n : α → ℕ) (P S : α × List Bool → List Bool)
    (a : α) (b : Bool) {u : List Bool} (hc : isActiveNonZero n P S a u = true) :
    ppadToPpaN₂ n P S (a, b :: u) ≠ ppadToPpaN₁ n P S (a, b :: u) := by
  rw [ppadToPpaN₂_cons, ite_eq_left hc]
  cases b
  · rw [ppadToPpaN₁_false_cons]
    split_ifs with hout
    · simp only [hasOut, decide_eq_true_eq] at hout
      intro h
      exact hout.2.1 (List.cons.inj h).2.symm
    · simp
  · rw [ppadToPpaN₁_true_cons]
    split_ifs with hin
    · simp only [hasIn, decide_eq_true_eq] at hin
      intro h
      exact hin.2.1 (List.cons.inj h).2.symm
    · simp

/-- Any solution `w` of `leafRel` for `(ppadToPpaN₁ n P S, ppadToPpaN₂ n P S)` has `w.tail` as a
solution of `endOfLineRel n P S`. -/
theorem endOfLineRel_tail_of_leafRel {n : α → ℕ} {P S : α × List Bool → List Bool} {a : α}
    {w : List Bool}
    (h : leafRel (fun a => n a + 1) (ppadToPpaN₁ n P S) (ppadToPpaN₂ n P S) a w) :
    endOfLineRel n P S a w.tail := by
  obtain ⟨hwlen, hleaf⟩ := h
  rcases w with _ | ⟨b, u⟩
  · simp at hwlen
  have hu_len : u.length = n a := by simpa using hwlen
  have he₁ :=
    undirectedEdge_left_of_invol (N₂ := ppadToPpaN₂ n P S) (ppadToPpaN₁_invol n P S a b u)
  have he₂ :=
    undirectedEdge_right_of_invol (N₁ := ppadToPpaN₁ n P S) (ppadToPpaN₂_invol n P S a b u)
  have hodd : hasOddDegree (ppadToPpaN₁ n P S) (ppadToPpaN₂ n P S) a (b :: u) =
      ((if b then hasIn n P S a u else hasOut n P S a u) != isActiveNonZero n P S a u) := by
    rw [hasOddDegree, he₁, he₂, decide_ne_ppadToPpaN₁, decide_ne_ppadToPpaN₂]
    by_cases hc : isActiveNonZero n P S a u = true
    · have hne := ppadToPpaN₂_ne_ppadToPpaN₁ n P S a b hc
      rw [ppadToPpaN₂_cons, ite_eq_left hc] at hne
      simp [hc, hne]
    · simp only [Bool.not_eq_true] at hc
      simp [hc]
  rw [hodd] at hleaf
  have hz_succ : zeroVertex (n a + 1) = false :: zeroVertex (n a) := rfl
  rw [hz_succ] at hleaf
  refine ⟨hu_len, ?_⟩
  unfold isActiveNonZero at hleaf
  by_cases hu : u = zeroVertex (n a)
  · subst hu
    have hin : hasIn n P S a (zeroVertex (n a)) = false := hasIn_zeroVertex n P S a
    cases b <;> cases hout : hasOut n P S a (zeroVertex (n a)) <;> simp_all
  · cases b <;> cases hout : hasOut n P S a u <;> cases hin : hasIn n P S a u <;> simp_all

end Cslib.Complexity
