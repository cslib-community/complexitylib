/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.WellFounded

/-!
# Min-max duality for required paths in in-forests

An in-forest is a finite type with a partial successor map `σ : α → Option α` and no cycles
(`Acyclic`). A directed path (`FPath`) is determined by its starting vertex and its number of
vertices: its vertices are the successive partial iterates of `σ` (`iter`). Given requirements
`r : α → ℕ`, a path is *required* (`FPath.Required`) when it is nonempty and its length is at least
`r v` at its final vertex `v`.

We prove that inside any finite vertex set `S : Finset α`, there exist a vertex set `H ⊆ S`
meeting every required path in `S` (`Covers`) and a family `P` of pairwise vertex-disjoint required
paths in `S` (`Packing`) of the same cardinality (`exists_cover_packing`), while every packing has
cardinality at most that of every cover (`packing_card_le_cover`). Consequently the minimum hitting
set and the maximum disjoint packing have equal size (`forest_duality`).

## Main definitions

* `Cslib.FunctionalGraph.ForestDuality.iter`: partial iteration of `σ : α → Option α`.
* `Cslib.FunctionalGraph.ForestDuality.FPath`: a directed path given by start vertex and length.
* `Cslib.FunctionalGraph.ForestDuality.FPath.Mem`: a vertex lies on a path.
* `Cslib.FunctionalGraph.ForestDuality.FPath.End`: a path is nonempty and ends at a vertex.
* `Cslib.FunctionalGraph.ForestDuality.FPath.Within`: every vertex of a path lies in `S`.
* `Cslib.FunctionalGraph.ForestDuality.Covers`: a vertex set hitting all required paths in `S`.
* `Cslib.FunctionalGraph.ForestDuality.Packing`: a pairwise vertex-disjoint family of required
  paths in `S`.
* `Cslib.FunctionalGraph.ForestDuality.Acyclic`: absence of directed cycles under `σ`.

## Main results

* `Cslib.FunctionalGraph.ForestDuality.packing_card_le_cover`: weak duality.
* `Cslib.FunctionalGraph.ForestDuality.exists_cover_packing`: strong duality on any finite vertex
  subset `S`.
* `Cslib.FunctionalGraph.ForestDuality.forest_duality`: combined min-max duality.

## References

* Adapted from lean/Proofs/ForestDuality.lean at revision `c4cfa198` of
  [S. Schlesinger, *Square-root circuit bounds for iterated functions*]
  [Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.FunctionalGraph.ForestDuality

universe u
variable {α : Type u} (σ : α → Option α)

/-- Partial iteration of the successor map: `iter σ k u` is the `k`-th successor of `u`. -/
def iter : ℕ → α → Option α
  | 0, u => some u
  | k + 1, u => (iter k u).bind σ

/-- Iterating `a + c` times is iterating `a` times and then, if defined, `c` more times. -/
theorem iter_add (a c : ℕ) (u : α) : iter σ (a + c) u = (iter σ a u).bind (iter σ c) := by
  induction c with
  | zero =>
    change iter σ a u = (iter σ a u).bind (fun x => some x)
    cases iter σ a u <;> rfl
  | succ c ih =>
    change (iter σ (a + c) u).bind σ = (iter σ a u).bind (fun x => (iter σ c x).bind σ)
    rw [ih]
    cases iter σ a u <;> rfl

private theorem iter_add_of_eq {a : ℕ} {u w : α} (h : iter σ a u = some w) (c : ℕ) :
    iter σ (a + c) u = iter σ c w := by
  rw [iter_add, h]
  rfl

/-- A directed path in an in-forest, specified by its starting vertex and its number of
vertices. -/
structure FPath (α : Type u) where
  /-- The first vertex of the path. -/
  start : α
  /-- The number of vertices on the path. -/
  len : ℕ
  deriving DecidableEq

variable {σ}

/-- Vertex membership: `v` is one of the first `len` partial iterates from `start`. -/
def FPath.Mem (p : FPath α) (v : α) : Prop :=
  ∃ k < p.len, iter σ k p.start = some v

/-- The path is nonempty and ends at `v`. -/
def FPath.End (p : FPath α) (v : α) : Prop :=
  0 < p.len ∧ iter σ (p.len - 1) p.start = some v

/-- The path is nonempty and its length is at least the requirement `r v` of its last vertex `v`. -/
def FPath.Required (r : α → ℕ) (p : FPath α) : Prop :=
  ∃ v, p.End (σ := σ) v ∧ r v ≤ p.len

/-- Every vertex of the path lies in `S`. -/
def FPath.Within (S : Finset α) (p : FPath α) : Prop :=
  ∀ v, p.Mem (σ := σ) v → v ∈ S

variable (σ)

/-- `H` meets every required path contained in `S`. -/
def Covers (r : α → ℕ) (S H : Finset α) : Prop :=
  ∀ p : FPath α, p.Required (σ := σ) r → p.Within (σ := σ) S → ∃ v ∈ H, p.Mem (σ := σ) v

/-- `P` is a family of pairwise vertex-disjoint required paths contained in `S`. -/
def Packing (r : α → ℕ) (S : Finset α) (P : Finset (FPath α)) : Prop :=
  (∀ p ∈ P, p.Required (σ := σ) r ∧ p.Within (σ := σ) S) ∧
    ∀ p ∈ P, ∀ q ∈ P, p ≠ q → ∀ v, p.Mem (σ := σ) v → ¬ q.Mem (σ := σ) v

/-- Acyclicity: no vertex is its own `k`-th successor for `k > 0`. -/
def Acyclic : Prop :=
  ∀ (v : α) (k : ℕ), 0 < k → iter σ k v ≠ some v

/-- **Weak duality.** Any family of pairwise disjoint required paths in `S` has cardinality at most
that of any hitting set for required paths in `S`. -/
theorem packing_card_le_cover {r : α → ℕ} {S H : Finset α}
    {P : Finset (FPath α)} (hP : Packing σ r S P) (hH : Covers σ r S H) :
    P.card ≤ H.card := by
  classical
  rcases P.eq_empty_or_nonempty with hPe | ⟨p0, -⟩
  · simp [hPe]
  have : Nonempty α := ⟨p0.start⟩
  have hit : ∀ p ∈ P, ∃ v ∈ H, p.Mem (σ := σ) v := fun p hp =>
    hH p (hP.1 p hp).1 (hP.1 p hp).2
  choose! g hgH hgM using hit
  refine Finset.card_le_card_of_injOn g (fun p hp => hgH p hp) ?_
  intro p hp q hq he
  by_contra hne
  exact hP.2 p hp q hq hne (g p) (hgM p hp) (he ▸ hgM q hq)

/-- `w` lies strictly before `v` along a directed path. -/
private def Before (w v : α) : Prop :=
  ∃ k, 0 < k ∧ iter σ k w = some v

private theorem before_wellFounded [Finite α] (hac : Acyclic σ) : WellFounded (Before σ) := by
  have : IsTrans α (Before σ) := ⟨fun a b c ⟨k, hk, hab⟩ ⟨l, hl, hbc⟩ =>
    ⟨k + l, by omega, by rw [iter_add_of_eq σ hab]; exact hbc⟩⟩
  have : Std.Irrefl (Before σ) := ⟨fun a ⟨k, hk, h⟩ => hac a k hk h⟩
  exact Finite.wellFounded_of_trans_of_irrefl _

/-- If a path `q` ending at `w` and a path `W` ending at `v` share a vertex `u`, then either `v`
belongs to `q` or `w` lies strictly before `v`. -/
private theorem shared_vertex {q W : FPath α} {u v w : α} (hqw : q.End (σ := σ) w)
    (hWv : W.End (σ := σ) v) (hqu : q.Mem (σ := σ) u) (hWu : W.Mem (σ := σ) u) :
    q.Mem (σ := σ) v ∨ Before σ w v := by
  obtain ⟨a, ha, hau⟩ := hqu
  obtain ⟨b, hb, hbu⟩ := hWu
  obtain ⟨hq0, hqe⟩ := hqw
  obtain ⟨hW0, hWe⟩ := hWv
  have hv : iter σ (W.len - 1 - b) u = some v := by
    rw [← iter_add_of_eq σ hbu, show b + (W.len - 1 - b) = W.len - 1 by omega]
    exact hWe
  have hw : iter σ (q.len - 1 - a) u = some w := by
    rw [← iter_add_of_eq σ hau, show a + (q.len - 1 - a) = q.len - 1 by omega]
    exact hqe
  by_cases hle : W.len - 1 - b ≤ q.len - 1 - a
  · left
    exact ⟨a + (W.len - 1 - b), by omega, by rw [iter_add_of_eq σ hau]; exact hv⟩
  · right
    refine ⟨W.len - 1 - b - (q.len - 1 - a), by omega, ?_⟩
    rw [← iter_add_of_eq σ hw, show q.len - 1 - a + (W.len - 1 - b - (q.len - 1 - a)) =
      W.len - 1 - b by omega]
    exact hv

/-- **Strong duality.** On every finite vertex subset `S`, there exist a hitting set `H ⊆ S` and a
disjoint packing `P` of required paths in `S` with equal cardinality. -/
theorem exists_cover_packing [Finite α] (hac : Acyclic σ) (r : α → ℕ) :
    ∀ S : Finset α, ∃ H ⊆ S, ∃ P : Finset (FPath α),
      Covers σ r S H ∧ Packing σ r S P ∧ P.card = H.card := by
  classical
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
  let E : Set α := {v | ∃ p : FPath α, p.Required (σ := σ) r ∧ p.Within (σ := σ) S ∧
    p.End (σ := σ) v}
  by_cases hE : E.Nonempty
  swap
  · refine ⟨∅, Finset.empty_subset _, ∅, ?_, ⟨by simp, by simp⟩, rfl⟩
    intro p hreq hin
    obtain ⟨v, hv, hr⟩ := hreq
    exact (hE ⟨v, p, ⟨v, hv, hr⟩, hin, hv⟩).elim
  obtain ⟨v, ⟨W, hWreq, hWin, hWv⟩, hmin⟩ := (before_wellFounded σ hac).has_min E hE
  have hvS : v ∈ S := hWin v ⟨W.len - 1, by have := hWv.1; omega, hWv.2⟩
  obtain ⟨H', hH'S, P', hcov, hpack, hcard⟩ := ih (S.erase v) (Finset.erase_ssubset hvS)
  have avoid : ∀ q : FPath α, q.Required (σ := σ) r → q.Within (σ := σ) (S.erase v) →
      ∀ u, q.Mem (σ := σ) u → ¬ W.Mem (σ := σ) u := by
    intro q hqreq hqin u hqu hWu
    obtain ⟨w, hqw, hrw⟩ := hqreq
    rcases shared_vertex σ hqw hWv hqu hWu with hqv | hbef
    · exact (Finset.notMem_erase v S) (hqin v hqv)
    · exact hmin w ⟨q, ⟨w, hqw, hrw⟩, fun x hx => Finset.mem_of_mem_erase (hqin x hx), hqw⟩
        hbef
  have hWv_mem : W.Mem (σ := σ) v := ⟨W.len - 1, by have := hWv.1; omega, hWv.2⟩
  have hWP' : W ∉ P' := by
    intro hW
    exact (Finset.notMem_erase v S) ((hpack.1 W hW).2 v hWv_mem)
  have hvH' : v ∉ H' := fun h => Finset.notMem_erase v S (hH'S h)
  refine ⟨insert v H', ?_, insert W P', ?_, ⟨?_, ?_⟩, ?_⟩
  · exact Finset.insert_subset hvS (hH'S.trans (Finset.erase_subset v S))
  · intro q hqreq hqin
    by_cases hqv : q.Mem (σ := σ) v
    · exact ⟨v, Finset.mem_insert_self v H', hqv⟩
    · have hin' : q.Within (σ := σ) (S.erase v) := by
        intro x hx
        refine Finset.mem_erase.2 ⟨?_, hqin x hx⟩
        rintro rfl
        exact hqv hx
      obtain ⟨x, hx, hqx⟩ := hcov q hqreq hin'
      exact ⟨x, Finset.mem_insert_of_mem hx, hqx⟩
  · intro p hp
    rcases Finset.mem_insert.1 hp with rfl | hp
    · exact ⟨hWreq, hWin⟩
    · exact ⟨(hpack.1 p hp).1, fun x hx => Finset.mem_of_mem_erase ((hpack.1 p hp).2 x hx)⟩
  · intro p hp q hq hne x hpx hqx
    have avoid' : ∀ p' ∈ P', ∀ y, p'.Mem (σ := σ) y → ¬ W.Mem (σ := σ) y := fun p' hp' =>
      avoid p' (hpack.1 p' hp').1 (hpack.1 p' hp').2
    rcases Finset.mem_insert.1 hp with hpW | hpP <;>
      rcases Finset.mem_insert.1 hq with hqW | hqP
    · exact hne (hpW.trans hqW.symm)
    · exact avoid' q hqP x hqx (hpW ▸ hpx)
    · exact avoid' p hpP x hpx (hqW ▸ hqx)
    · exact hpack.2 p hpP q hqP hne x hpx hqx
  · rw [Finset.card_insert_of_notMem hWP', Finset.card_insert_of_notMem hvH', hcard]

/-- **Min-max duality for required paths in an in-forest.** There exist a hitting set `H` and a
disjoint packing `P` of required paths in `S` with equal cardinality, every hitting set is at least
that large, and every disjoint packing is at most that large. -/
theorem forest_duality [Finite α] (hac : Acyclic σ) (r : α → ℕ)
    (S : Finset α) :
    ∃ H : Finset α, ∃ P : Finset (FPath α),
      Covers σ r S H ∧ Packing σ r S P ∧ P.card = H.card ∧
      (∀ H' : Finset α, Covers σ r S H' → H.card ≤ H'.card) ∧
      (∀ P' : Finset (FPath α), Packing σ r S P' → P'.card ≤ P.card) := by
  obtain ⟨H, -, P, hcov, hpack, hcard⟩ := exists_cover_packing σ hac r S
  refine ⟨H, P, hcov, hpack, hcard, fun H' hH' => ?_, fun P' hP' => ?_⟩
  · rw [← hcard]
    exact packing_card_le_cover σ hpack hH'
  · rw [hcard]
    exact packing_card_le_cover σ hP' hcov

end Cslib.FunctionalGraph.ForestDuality
