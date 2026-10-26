/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Hamiltonian
import Complexity.Computability.Complexity.Problems.Hamiltonian.Undirected
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Mathlib.Data.List.GetD

/-!
# The traveling salesman problem

`TSP` is the decision version of the traveling salesman problem
[Papadimitriou, Section 9.3][Papadimitriou94]: an instance is a distance matrix `D`, given as a list
of rows (row `i` lists the distances from city `i`), together with a budget `b`, and it belongs to
`TSP` when some closed tour visiting every city exactly once has length at most `b`. The
conventions are the following.

* The cities are the row indices `0, …, D.length - 1`. Rows may have any length: an entry missing
  from a ragged or short matrix reads `0` (`TSP.dist`).
* Distances need not be symmetric, and the diagonal entries are only used by the tour of a single
  city, which costs `TSP.dist D 0 0`. The matrix without rows is a yes-instance, through the empty
  tour of length `0`.
* A tour is a permutation `p` of the cities, and its length `TSP.tourLength D p` is the sum of the
  distances from each city of `p` to the next one, the last city returning to the first.
* Distances and the budget are binary (`encTSP`).

`TSP` is in `NP`. As for the Hamiltonian problems, a certificate names an ordering of the cities,
decoded by `Graph.decodeVertexList` from the list `0, …, D.length - 1` of cities; it has length
`m ^ 2` for instances of encoded length `m`. The verifier checks that the ordering lists every city
exactly once, and compares the length of its tour with the budget using the binary arithmetic of
`Complexity/Computability/Machines/Turing/MultiTape/Complexity/PolyTime/Nat/Binary.lean`, so
distances and budgets of any size are handled without unary
expansion.

The reduction `HamCycle.toTSP` from `HamCycle` takes the distinct declared vertices of a graph as
cities, at distance `1` when they are adjacent and `2` otherwise, with the number `n` of cities as
the budget. A closed tour has `n` steps of length at least `1`, so it has length at most `n`
exactly when every step joins adjacent vertices, that is, when it is a Hamiltonian cycle. Graphs
with fewer than three vertices have no Hamiltonian cycle and are mapped to a fixed no-instance.

## Main definitions

* `Cslib.Complexity.encTSP`, `Cslib.Complexity.TSP.dist`, `Cslib.Complexity.TSP.tourLength`,
  `Cslib.Complexity.TSP`.
* `Cslib.Complexity.TSP.verifier`.
* `Cslib.Complexity.HamCycle.toTSP`.

## Main results

* `Cslib.Complexity.TSP.tourLength_eq_sum`: the tour length as a sum over the positions of the
  tour.
* `Cslib.Complexity.TSP.computableInPolyTime_tourLength`: tour lengths are polynomial-time.
* `Cslib.Complexity.TSP.isVerifier`, `Cslib.Complexity.TSP.mem_NP`: `TSP ∈ NP encTSP`.
* `Cslib.Complexity.HamCycle.toTSP_mem_iff`: `toTSP G ∈ TSP ↔ G ∈ HamCycle`.
* `Cslib.Complexity.HamCycle.computableInPolyTime_toTSP`: the reduction is polynomial-time.
* `Cslib.Complexity.polyTimeReducible_HamCycle_TSP`, `Cslib.Complexity.TSP_npHard`: `HamCycle`
  reduces to `TSP` in polynomial time, so `TSP` is `NP`-hard.
* `Cslib.Complexity.TSP_npComplete`: `TSP` is `NP`-complete.

## References

* [M. R. Garey and D. S. Johnson, *Computers and Intractability*][GareyJohnson1979]
* [C. H. Papadimitriou, *Computational Complexity*][Papadimitriou94]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableTidilyInPolyTime

/-- Instances of the traveling salesman problem, a distance matrix given by its rows and a budget,
encoded by framed lists of binary distances and a binary budget. -/
def encTSP : List (List ℕ) × ℕ ↪ List Bool := encPair (encList (encList encNat)) encNat

namespace TSP

/-- The distance from city `i` to city `j` in the matrix `D`: entry `j` of row `i`. Entries missing
from a ragged or short matrix read `0`. -/
def dist (D : List (List ℕ)) (i j : ℕ) : ℕ := (D.getD i []).getD j 0

/-- The length of the closed tour visiting the cities of `p` in order: the sum of the distances
from each city of `p` to the next one, the last city returning to the first. A tour of one city
`c` has length `dist D c c`, and the empty tour has length `0`. -/
def tourLength (D : List (List ℕ)) (p : List ℕ) : ℕ :=
  (List.zipWith (dist D) p (p.rotate 1)).sum

end TSP

/-- The traveling salesman problem: the distance matrices `D` with a budget `b` such that some
closed tour visiting each city `0, …, D.length - 1` exactly once has length at most `b`
[Papadimitriou, Section 9.3][Papadimitriou94]. -/
def TSP : Set (List (List ℕ) × ℕ) :=
  {x | ∃ p : List ℕ, p.Perm (List.range x.1.length) ∧ TSP.tourLength x.1 p ≤ x.2}

namespace TSP

/-- The tour length as a sum over the positions of the tour: with `q = p ++ p.take 1`, the tour
with its first city repeated at the end, position `k` pays the distance from entry `k` of `q` to
entry `k + 1`. -/
theorem tourLength_eq_sum (D : List (List ℕ)) (p : List ℕ) :
    tourLength D p = ((List.range p.length).map fun k =>
      dist D ((p ++ p.take 1).getD k 0) ((p ++ p.take 1).getD (k + 1) 0)).sum := by
  rw [tourLength]
  congr 1
  apply List.ext_getElem (by simp)
  intro k hk hk'
  simp only [List.length_zipWith, List.length_rotate, Nat.min_self] at hk
  rw [List.getElem_zipWith, List.getElem_rotate, List.getElem_map, List.getElem_range,
    List.getD_append _ _ _ _ hk, List.getD_eq_getElem _ _ hk]
  congr 1
  by_cases h : k + 1 < p.length
  · rw [List.getD_append _ _ _ _ h, List.getD_eq_getElem _ _ h]
    simp only [Nat.mod_eq_of_lt h]
  · have hk1 : k + 1 = p.length := by omega
    simp only [hk1, Nat.mod_self, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
    cases p with
    | nil => simp at hk
    | cons a l => rfl

/-! ### Membership in `NP` -/

/-- The length of a tour is polynomial-time in the distance matrix and the tour, both with binary
entries: it is a binary sum over the positions of the tour, and a city beyond the matrix is looked
up at an index capped by the number of rows. -/
@[fun_prop]
theorem computableInPolyTime_tourLength :
    ComputableInPolyTime (fun x : List (List ℕ) × List ℕ => tourLength x.1 x.2)
      (encPair (encList (encList encNat)) (encList encNat)) encNat := by
  refine .of_tidy ?_
  have heq : (fun x : List (List ℕ) × List ℕ => tourLength x.1 x.2) = fun x =>
      ((List.range x.2.length).map fun k =>
        dist x.1 ((x.2 ++ [x.2.headD 0]).getD k 0)
          ((x.2 ++ [x.2.headD 0]).getD (k + 1) 0)).sum := by
    funext ⟨D, p⟩
    cases p <;> rw [tourLength_eq_sum] <;> rfl
  rw [heq]
  refine binary_sum.comp (mapWithInput (by fun_prop) ?_)
  have hq : ComputableTidilyInPolyTime
      (fun q : (List (List ℕ) × List ℕ) × ℕ => q.1.2 ++ [q.1.2.headD 0])
      (encPair (encPair (encList (encList encNat)) (encList encNat)) encUnary)
      (encList encNat) := by
    fun_prop
  have hrow : ComputableTidilyInPolyTime
      (fun q : (List (List ℕ) × List ℕ) × ℕ =>
        q.1.1.getD ((q.1.2 ++ [q.1.2.headD 0]).getD q.2 0) [])
      (encPair (encPair (encList (encList encNat)) (encList encNat)) encUnary)
      (encList encNat) :=
    listGetD_binary [] (by fun_prop) ((listGetD 0).comp (hq.prod (snd _ _)))
  exact listGetD_binary 0 hrow
    ((listGetD 0).comp (hq.prod (unary_add.comp ((snd _ _).prod (const 1)))))

/-- The verifier for `TSP`: decode a list of cities from the certificate (`Graph.decodeVertexList`
applied to the cities `0, …, n - 1`) and check that it lists every city exactly once and that the
closed tour visiting the cities in this order has length at most the budget. -/
def verifier : (List (List ℕ) × ℕ) × List Bool → Bool :=
  Graph.verifyOrdering (fun x => List.range x.1.length) fun x p => decide (tourLength x.1 p ≤ x.2)

/-- `TSP.verifier` verifies `TSP` with certificates of length `n ^ 2` for instances of encoded
length `n`. -/
theorem isVerifier : IsVerifier encTSP (Polynomial.X ^ 2) verifier TSP := by
  rintro ⟨D, b⟩
  have hmem : (D, b) ∈ TSP ↔ ∃ p : List ℕ, p.Nodup ∧ (∀ v, v ∈ p ↔ v ∈ List.range D.length) ∧
      tourLength D p ≤ b := by
    refine exists_congr fun p => ?_
    rw [← and_assoc]
    refine and_congr_left fun _ => ⟨fun h => ⟨h.nodup_iff.2 List.nodup_range, fun _ => h.mem_iff⟩,
      fun h => (List.perm_ext_iff_of_nodup h.1 List.nodup_range).2 h.2⟩
  rw [hmem]
  refine Graph.isVerifier_verifyOrdering (V := fun x : List (List ℕ) × ℕ => List.range x.1.length)
    (P := fun x p => tourLength x.1 p ≤ x.2) (fun x => ?_) (fun _ _ => decide_eq_true_iff) (D, b)
  rw [List.length_range]
  refine (length_le_length_encList (encList encNat) x.1).trans ?_
  simp only [encTSP, length_encPair]
  omega

/-- The `TSP` verifier is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_verifier :
    ComputableInPolyTime verifier (encPair encTSP encBits) encBool := by
  refine .of_tidy ?_
  have hV : ComputableTidilyInPolyTime (fun x : List (List ℕ) × ℕ => List.range x.1.length) encTSP
      (encList encNat) := by
    unfold encTSP
    simpa only [Function.comp_def, List.map_id'] using (map unary_to_binary).comp
      (range.comp ((length_list (encList encNat)).comp (fst (encList (encList encNat)) encNat)))
  have hD : ComputableTidilyInPolyTime (fun q : (List (List ℕ) × ℕ) × List ℕ => q.1.1)
      (encPair encTSP (encList encNat)) (encList (encList encNat)) := by
    unfold encTSP
    exact (fst _ _).comp (fst _ _)
  have hb : ComputableTidilyInPolyTime (fun q : (List (List ℕ) × ℕ) × List ℕ => q.1.2)
      (encPair encTSP (encList encNat)) encNat := by
    unfold encTSP
    exact (snd _ _).comp (fst _ _)
  have hlen := computableInPolyTime_tourLength.tidy.comp (hD.prod (snd _ (encList encNat)))
  exact (Graph.computableInPolyTime_verifyOrdering (.of_tidy hV)
    (.of_tidy (binary_le' hlen hb))).tidy

/-- `TSP` belongs to `NP`. -/
theorem mem_NP : TSP ∈ NP encTSP :=
  ⟨_, verifier, computableInPolyTime_verifier, isVerifier⟩

end TSP

namespace HamCycle

/-! ### The reduction from Hamiltonian cycles -/

/-- The reduction from `HamCycle` to `TSP` [Papadimitriou, Section 9.3][Papadimitriou94]: the
cities are the distinct declared vertices, at distance `1` when they are adjacent and `2`
otherwise, and the budget is the number `n` of cities. When `n < 3` the graph has no Hamiltonian
cycle, and the reduction returns the no-instance of one city at distance `1` from itself with
budget `0`. -/
def toTSP (G : Graph) : List (List ℕ) × ℕ :=
  if G.distinctVertices.length < 3 then ([[1]], 0)
  else
    (G.distinctVertices.map fun u =>
      G.distinctVertices.map fun v => if G.adjBool u v then 1 else 2,
    G.distinctVertices.length)

private theorem dist_map {V : List ℕ} {G : Graph} {i j : ℕ} (hi : i < V.length)
    (hj : j < V.length) :
    TSP.dist (V.map fun u => V.map fun v => if G.adjBool u v then 1 else 2) i j =
      if G.adjBool V[i] V[j] then 1 else 2 := by
  simp only [TSP.dist, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem hj, Option.map_some, Option.getD_some]

private theorem chain_iff {R : ℕ → ℕ → Prop} {q : List ℕ} :
    (q : Cycle ℕ).Chain R ↔
      ∀ k < q.length, R ((q ++ q.take 1).getD k 0) ((q ++ q.take 1).getD (k + 1) 0) := by
  rw [Cycle.chain_coe_iff_isChain_append_take_one, List.isChain_iff_getElem]
  by_cases hq : q = []
  · subst hq
    simp
  · have hlen : (q ++ q.take 1).length = q.length + 1 := by
      have := List.length_pos_iff.2 hq
      simp only [List.length_append, List.length_take]
      omega
    constructor
    · intro h k hk
      have := h k (by omega)
      rwa [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
    · intro h k hk
      have := h k (by omega)
      rwa [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at this

private theorem eq_one_of_sum_le {l : List ℕ} (h1 : ∀ a ∈ l, 1 ≤ a) (h : l.sum ≤ l.length) :
    ∀ a ∈ l, a = 1 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ht := List.length_le_sum_of_one_le t fun b hb => h1 b (List.mem_cons_of_mem _ hb)
    simp only [List.sum_cons, List.length_cons] at h
    have ha := h1 a List.mem_cons_self
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb
    · omega
    · exact ih (fun c hc => h1 c (List.mem_cons_of_mem _ hc)) (by omega) b hb

private theorem getD_map_of_lt {l : List ℕ} {f : ℕ → ℕ} {j : ℕ} (hj : j < l.length) :
    (l.map f).getD j 0 = f (l.getD j 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map,
    List.getD_eq_getElem _ _ hj]

private theorem getD_lt {l : List ℕ} {n : ℕ} (hn : 0 < n) (hl : ∀ a ∈ l, a < n) (j : ℕ) :
    l.getD j 0 < n := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[j]? with
  | none => exact hn
  | some a => exact hl a (List.mem_of_getElem? h)

/-- **Correctness of the reduction to `TSP`.** A graph has a Hamiltonian cycle exactly when its
distance matrix has a closed tour of length at most the number of cities. -/
theorem toTSP_mem_iff (G : Graph) : toTSP G ∈ TSP ↔ G ∈ HamCycle := by
  rw [mem_HamCycle_iff]
  have hVnd := G.nodup_distinctVertices
  have hmemV : ∀ v, v ∈ G.distinctVertices ↔ v ∈ G.1 := fun _ => Graph.mem_distinctVertices
  have hlenV :
      ∀ q : List ℕ, q.Nodup → (∀ v, v ∈ q ↔ v ∈ G.1) → q.length = G.distinctVertices.length :=
    fun q hq hcov =>
      ((List.perm_ext_iff_of_nodup hq hVnd).2 fun v => (hcov v).trans (hmemV v).symm).length_eq
  unfold toTSP
  generalize G.distinctVertices = V at hVnd hmemV hlenV ⊢
  split_ifs with hn
  · constructor
    · rintro ⟨p, hp, hlen⟩
      rw [show p = [0] by simpa using hp] at hlen
      simp [TSP.tourLength, TSP.dist] at hlen
    · rintro ⟨q, hq, hcov, h3, -⟩
      have := hlenV q hq hcov
      omega
  · push Not at hn
    simp only [TSP, Set.mem_ofPred_eq, List.length_map]
    constructor
    · rintro ⟨p, hp, hlen⟩
      have hn0 : 0 < V.length := by omega
      have hplen : p.length = V.length := by rw [hp.length_eq, List.length_range]
      have hplt : ∀ a ∈ p, a < V.length := fun a ha => List.mem_range.1 (hp.subset ha)
      have hget := getD_lt hn0 (l := p ++ p.take 1) fun a ha => by
        rcases List.mem_append.1 ha with ha | ha
        · exact hplt a ha
        · exact hplt a (List.mem_of_mem_take ha)
      -- Every step of the tour costs `1`, so it joins adjacent vertices.
      rw [TSP.tourLength_eq_sum] at hlen
      have hone : ∀ k < V.length, G.adjBool (V.getD ((p ++ p.take 1).getD k 0) 0)
          (V.getD ((p ++ p.take 1).getD (k + 1) 0) 0) = true := by
        intro k hk
        rw [List.getD_eq_getElem _ _ (hget k), List.getD_eq_getElem _ _ (hget (k + 1))]
        have h := eq_one_of_sum_le (l := (List.range p.length).map fun k =>
          TSP.dist (V.map fun u => V.map fun v => if G.adjBool u v then 1 else 2)
            ((p ++ p.take 1).getD k 0) ((p ++ p.take 1).getD (k + 1) 0)) ?_
          (by rw [List.length_map, List.length_range]; exact hlen.trans hplen.ge) _
          (List.mem_map.2 ⟨k, List.mem_range.2 (hplen ▸ hk), rfl⟩)
        · rw [dist_map (hget k) (hget (k + 1))] at h
          split_ifs at h with hadj
          · exact hadj
          · omega
        · intro a ha
          obtain ⟨j, -, rfl⟩ := List.mem_map.1 ha
          rw [dist_map (hget j) (hget (j + 1))]
          split_ifs <;> omega
      refine ⟨p.map fun i => V.getD i 0, ?_, fun v => ?_, by rw [List.length_map, hplen]; exact hn,
        ?_⟩
      · refine (hp.nodup_iff.2 List.nodup_range).map_on fun i hi j hj hij => ?_
        rw [List.getD_eq_getElem _ _ (hplt i hi), List.getD_eq_getElem _ _ (hplt j hj)] at hij
        exact hVnd.getElem_inj_iff.1 hij
      · rw [← hmemV, List.mem_map]
        constructor
        · rintro ⟨i, hi, rfl⟩
          rw [List.getD_eq_getElem _ _ (hplt i hi)]
          exact List.getElem_mem _
        · intro hv
          have hlt := List.idxOf_lt_length_iff.2 hv
          refine ⟨V.idxOf v, hp.mem_iff.2 (List.mem_range.2 hlt), ?_⟩
          rw [List.getD_eq_getElem _ _ hlt, List.getElem_idxOf]
      · have hp'len : (p ++ p.take 1).length = V.length + 1 := by
          simp only [List.length_append, List.length_take, hplen]
          omega
        rw [chain_iff]
        intro k hk
        rw [List.length_map, hplen] at hk
        rw [← List.map_take, ← List.map_append, getD_map_of_lt (by omega),
          getD_map_of_lt (by omega)]
        exact (Graph.adjBool_eq_true_iff _ _ _).1 (hone k hk)
    · rintro ⟨q, hq, hcov, h3, hch⟩
      have hqlen := hlenV q hq hcov
      have hqV : ∀ v ∈ q, v ∈ V := fun v hv => (hmemV v).2 ((hcov v).1 hv)
      refine ⟨q.map V.idxOf, ?_, ?_⟩
      · have hnd : (q.map V.idxOf).Nodup :=
          hq.map_on fun u hu v _ h => (List.idxOf_inj (hqV u hu)).1 h
        have hsub : q.map V.idxOf ⊆ List.range V.length := fun i hi => by
          obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hi
          exact List.mem_range.2 (List.idxOf_lt_length_iff.2 (hqV v hv))
        exact (hnd.subperm hsub).perm_of_length_le (by simp [hqlen])
      · rw [TSP.tourLength_eq_sum]
        refine (List.sum_le_length_nsmul _ 1 fun a ha => ?_).trans (by simp [hqlen])
        obtain ⟨k, hk, rfl⟩ := List.mem_map.1 ha
        rw [List.mem_range, List.length_map] at hk
        have hq'len : (q ++ q.take 1).length = q.length + 1 := by
          simp only [List.length_append, List.length_take]
          omega
        have hmem : ∀ j < q.length + 1, (q ++ q.take 1).getD j 0 ∈ V := fun j hj => by
          have hj' : j < (q ++ q.take 1).length := by omega
          rw [List.getD_eq_getElem _ _ hj']
          rcases List.mem_append.1 (List.getElem_mem hj') with h | h
          · exact hqV _ h
          · exact hqV _ (List.mem_of_mem_take h)
        rw [← List.map_take, ← List.map_append, getD_map_of_lt (by omega),
          getD_map_of_lt (by omega)]
        have h₁ := List.idxOf_lt_length_iff.2 (hmem k (by omega))
        have h₂ := List.idxOf_lt_length_iff.2 (hmem (k + 1) (by omega))
        rw [dist_map h₁ h₂, List.getElem_idxOf, List.getElem_idxOf,
          ite_eq_left ((Graph.adjBool_eq_true_iff _ _ _).2 (chain_iff.1 hch k hk))]

/-- The reduction `toTSP` is polynomial-time: the cities are selected from the declared vertices,
and the distances and the budget are written in binary. -/
@[fun_prop]
theorem computableInPolyTime_toTSP : ComputableInPolyTime toTSP encGraph encTSP := by
  refine .of_tidy ?_
  have hV : ComputableTidilyInPolyTime Graph.distinctVertices encGraph (encList encNat) :=
    Graph.computableInPolyTime_distinctVertices.tidy
  have hn : ComputableTidilyInPolyTime (fun G : Graph => G.distinctVertices.length) encGraph
      encUnary := (length_list _).comp hV
  have hrow : ComputableTidilyInPolyTime
      (fun p : Graph × ℕ => p.1.distinctVertices.map fun v => if p.1.adjBool p.2 v then 1 else 2)
      (encPair encGraph encNat) (encList encNat) :=
    mapWithInput (hV.comp (fst _ _))
      (cond Graph.computableInPolyTime_adjBool.tidy (const 1) (const 2))
  unfold toTSP encTSP
  exact ite_decide (unary_lt' hn (const 3)) (const _)
    ((mapWithInput hV hrow).prod (unary_to_binary.comp hn))

end HamCycle

/-- `HamCycle` reduces to `TSP` in polynomial time via `HamCycle.toTSP`. -/
theorem polyTimeReducible_HamCycle_TSP : PolyTimeReducible encGraph encTSP HamCycle TSP :=
  ⟨HamCycle.toTSP, HamCycle.computableInPolyTime_toTSP,
    fun G => (HamCycle.toTSP_mem_iff G).symm⟩

/-- `TSP` is `NP`-hard. -/
theorem TSP_npHard : NPHard encTSP TSP :=
  HamCycle_npHard.trans polyTimeReducible_HamCycle_TSP

/-- **`TSP` is NP-complete** [Papadimitriou, Section 9.3][Papadimitriou94]. -/
theorem TSP_npComplete : NPComplete encTSP TSP :=
  ⟨TSP.mem_NP, TSP_npHard⟩

end Cslib.Complexity
