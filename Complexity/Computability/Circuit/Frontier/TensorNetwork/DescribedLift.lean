/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.ReductionLift
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.VertexDesc
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.Recursion
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListLookup
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListMap
import Complexity.Computability.PolyTime.GaloisRingUnits
import Complexity.Foundations.NumberTheory.Padics.AdjoinRootDigitLift
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Sort

/-!
# A described network over `O`

The contraction recursion of [OpenAI2026ETH] (§D.4, pp. 57–64) is proved correct over the valuation
ring `O = ℤ_(2)[U] / (f)`, while the native algorithm carries networks of descriptors
(`DescribedNetwork (VertexDesc T)`) and computes with coefficient lists in
`A_p = (ℤ / 2 ^ p)[U] / (f)`. This file gives the network over `O` that a described network stands
for.

* **Lifts.** A coefficient list `c` lifts to `∑ i < e, c_i U ^ i` in `O` (`GaloisRingArith.liftO`),
  and reducing the lift modulo `2 ^ p` gives the value of `c` in `A_p`
  (`GaloisRingArith.reduction_liftO`). This is the canonical lifting of representatives of §D.4.1
  (p. 58): a retained vertex is read through the lift of its entry at every later precision.
  Lifts of distinct lists with binary coordinates differ by a unit
  (`GaloisRingArith.isUnit_liftO_sub`); in particular the binary digits of `0, …, n - 1` are
  interpolation points when `n ≤ 2 ^ e` (`GaloisRingArith.pairwise_isUnit_liftO_sub_digits`).
* **Rows first.** A described network is *rows-first bipartite* at `r`
  (`DescribedNetwork.IsRowsFirstBipartite`) when every port names an edge and every edge is a port
  of exactly one of the first `r` vertices, once, and of exactly one of the others, once. The ends
  of the edges are then computed by listing the vertices at each edge
  (`DescribedNetwork.incident`, `DescribedNetwork.edgeEnds`), in polynomial time
  (`DescribedNetwork.computableInPolyTime_edgeEnds`).
* **The network** (`DescribedNetwork.toNetwork`). A rows-first described network and an evaluator
  give a Boolean tensor network on `Fin k` vertices and `Fin m` edges with these ends, whose
  tensor at a vertex is the evaluator at its descriptor and the bits on its ports. It has the
  contraction of the described network (`DescribedNetwork.contraction_toNetwork`). Over `O`, with
  the lifts of the entries, its contraction reduces modulo `2 ^ p` to the contraction of the
  values in `A_p` (`DescribedNetwork.reduction_contraction_toNetwork`).

## Main definitions

* `Cslib.GaloisRingArith.liftO`: the lift of a coefficient list to `O`.
* `Cslib.Circuits.Frontier.DescribedNetwork.incident`,
  `Cslib.Circuits.Frontier.DescribedNetwork.edgeEnds`: the ends of the edges.
* `Cslib.Circuits.Frontier.DescribedNetwork.toNetwork`: the network of a described network.

## Main results

* `Cslib.GaloisRingArith.reduction_liftO`, `Cslib.GaloisRingArith.mk_liftO`: reducing a lift.
* `Cslib.GaloisRingArith.isUnit_liftO_sub`,
  `Cslib.GaloisRingArith.pairwise_isUnit_liftO_sub_digits`: binary lists as interpolation points.
* `Cslib.Circuits.Frontier.DescribedNetwork.rows_le_of_isRowsFirstBipartite`: row count bound.
* `Cslib.Circuits.Frontier.DescribedNetwork.incident_eq`: the vertices at an edge.
* `Cslib.Circuits.Frontier.DescribedNetwork.contraction_toNetwork`,
  `Cslib.Circuits.Frontier.DescribedNetwork.reduction_contraction_toNetwork`: the contraction.
* `Cslib.Circuits.Frontier.DescribedNetwork.computableInPolyTime_edgeEnds`: polynomial time.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §D.4.1 (pp. 57–58) and
  §D.4.6 (pp. 63–64).
-/

public section

open Polynomial AdjoinRoot Finset

/-! ### Lifts of coefficient lists -/

namespace AdjoinRoot

/-- `ℤ_(2)` lies in the valuation ring `O` of `ℚ[U] / (f)`. -/
theorem algebraMap_mem_integer_padicValuation {f : ℤ[X]} (hf : f.Monic)
    (hirr : Irreducible (f.map (Int.castRingHom (ZMod 2)))) :
    ∀ c ∈ Valuation.integer (Rat.padicValuation 2),
      algebraMap ℚ (AdjoinRoot (f.map (Int.castRingHom ℚ))) c ∈
        (padicValuation 2 hf hirr).integer := fun c hc => by
  rw [Valuation.mem_integer_iff, padicValuation_algebraMap]
  exact hc

end AdjoinRoot

namespace Cslib.GaloisRingArith

variable {fl : List ℕ} (hirr : Irreducible ((monicOf fl).map (Int.castRingHom (ZMod 2))))

/-- The class of `U` in the valuation ring `O = ℤ_(2)[U] / (f)`, `f = monicOf fl`. -/
noncomputable def rootO : (padicValuation 2 (monic_monicOf fl) hirr).integer :=
  ⟨map (Int.castRingHom ℚ) (monicOf fl) _ dvd_rfl (root _),
    (Valuation.mem_integer_iff _ _).mpr (padicValuation_map_le_one _ hirr _)⟩

/-- **The lift of a coefficient list to `O`**: `∑ i < e, c_i U ^ i`, with `e = fl.length`. -/
noncomputable def liftO (c : List ℕ) : (padicValuation 2 (monic_monicOf fl) hirr).integer :=
  ∑ i ∈ range fl.length, ((c.getD i 0 : ℕ) : (padicValuation 2 (monic_monicOf fl) hirr).integer) *
    rootO hirr ^ i

/-- Reduction sends `U` to `U`. -/
theorem reduction_rootO (p : ℕ) :
    reduction (monic_monicOf fl) hirr p (rootO hirr) = root _ := by
  rw [rootO, reduction_toRat, map_root]

/-- **Reducing a lift modulo `2 ^ p` gives the value in `A_p`.** -/
theorem reduction_liftO (p : ℕ) (c : List ℕ) :
    reduction (monic_monicOf fl) hirr p (liftO hirr c) = val p fl c := by
  simp only [liftO, val, map_sum, map_mul, map_natCast, map_pow, reduction_rootO]

/-- **The class of a lift modulo `2 ^ p`** is the image of the value in `A_p`. -/
theorem mk_liftO (p : ℕ) (c : List ℕ) :
    Ideal.Quotient.mk _ (liftO hirr c) =
      Cslib.Circuits.Frontier.reductionLift (monic_monicOf fl) hirr p (val p fl c) := by
  rw [← reduction_liftO hirr p, Cslib.Circuits.Frontier.reductionLift_reduction]

/-! ### Binary lists as interpolation points -/

/-- A lift of a list with binary coordinates is a digit lift. -/
private theorem liftO_eq_integerDigitLift {c : List ℕ} (hc : ∀ i < fl.length, c.getD i 0 < 2) :
    liftO hirr c = AdjoinRoot.integerDigitLift (monic_monicOf fl) hirr
      fun i => ((c.getD i 0 : ℕ) : ZMod 2) := by
  apply Subtype.ext
  rw [AdjoinRoot.coe_integerDigitLift, Fin.sum_univ_eq_sum_range
    (fun i => ((((c.getD i 0 : ℕ) : ZMod 2)).val : AdjoinRoot ((monicOf fl).map
      (Int.castRingHom ℚ))) * AdjoinRoot.root _ ^ i), natDegree_monicOf, liftO]
  push_cast
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (hc i (mem_range.mp hi))]
  exact congrArg (_ * · ^ i) (AdjoinRoot.map_root _ _ _ _)

/-- **Lifts of distinct binary lists differ by a unit.** If two lists have binary coordinates
below `e = fl.length` and differ at one of them, their lifts to `O` differ by a unit: they are
digit lifts (`AdjoinRoot.isUnit_integerDigitLift_sub`). -/
theorem isUnit_liftO_sub {c c' : List ℕ} (hc : ∀ i < fl.length, c.getD i 0 < 2)
    (hc' : ∀ i < fl.length, c'.getD i 0 < 2)
    (hne : ∃ i < fl.length, c.getD i 0 ≠ c'.getD i 0) :
    IsUnit (liftO hirr c - liftO hirr c') := by
  rw [liftO_eq_integerDigitLift hirr hc, liftO_eq_integerDigitLift hirr hc']
  refine AdjoinRoot.isUnit_integerDigitLift_sub _ hirr fun h => ?_
  obtain ⟨i, hi, hne⟩ := hne
  have h2 := congrArg ZMod.val (congrFun h ⟨i, by rwa [natDegree_monicOf]⟩)
  rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (hc i hi),
    Nat.mod_eq_of_lt (hc' i hi)] at h2
  exact hne h2

/-- Coordinate `i < e` of the binary digits of `k` below `e`. -/
theorem getD_map_testBit (e k i : ℕ) (hi : i < e) :
    ((List.range e).map fun j => if k.testBit j then 1 else 0).getD i 0 =
      if k.testBit i then 1 else 0 := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]

/-- **Binary-digit points are interpolation points.** The lists of the binary digits below
`e = fl.length` of `0, …, n - 1`, for `n ≤ 2 ^ e`, have lifts to `O` with unit differences. -/
theorem pairwise_isUnit_liftO_sub_digits {n : ℕ} (hn : n ≤ 2 ^ fl.length) :
    Pairwise fun i j : Fin ((List.range n).map fun k =>
        (List.range fl.length).map fun j => if k.testBit j then 1 else 0).length =>
      IsUnit (liftO hirr (((List.range n).map fun k =>
          (List.range fl.length).map fun j => if k.testBit j then 1 else 0).getD i []) -
        liftO hirr (((List.range n).map fun k =>
          (List.range fl.length).map fun j => if k.testBit j then 1 else 0).getD j [])) := by
  intro i j hij
  have hi : (i : ℕ) < n := by simpa using i.2
  have hj : (j : ℕ) < n := by simpa using j.2
  rw [List.getD_eq_getElem _ _ i.2, List.getD_eq_getElem _ _ j.2, List.getElem_map,
    List.getElem_map, List.getElem_range, List.getElem_range]
  have hbin (k : ℕ) : ∀ b < fl.length,
      ((List.range fl.length).map fun j => if k.testBit j then 1 else 0).getD b 0 < 2 := by
    intro b hb
    rw [getD_map_testBit _ _ _ hb]
    split <;> omega
  refine isUnit_liftO_sub hirr (hbin _) (hbin _) ?_
  by_contra hall
  simp only [not_exists, not_and, not_not] at hall
  refine hij (Fin.ext (Nat.eq_of_testBit_eq fun b => ?_))
  rcases lt_or_ge b fl.length with hb | hb
  · have := hall b hb
    rw [getD_map_testBit _ _ _ hb, getD_map_testBit _ _ _ hb] at this
    revert this
    cases (i : ℕ).testBit b <;> cases (j : ℕ).testBit b <;> simp
  · have h2 : 2 ^ fl.length ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
    rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]

end Cslib.GaloisRingArith

namespace Cslib.Circuits.Frontier

/-! ### Lists of lists with one occurrence -/

/-- **One occurrence among the lists.** If an element occurs once in total among a list of
lists, exactly one of the lists contains it, once. -/
theorem exists_unique_of_sum_count_eq_one {Ls : List (List ℕ)} {j : ℕ}
    (h : (Ls.map fun l => l.count j).sum = 1) :
    ∃ i, ∃ hi : i < Ls.length, Ls[i].count j = 1 ∧
      ∀ i' (hi' : i' < Ls.length), j ∈ Ls[i'] → i' = i := by
  induction Ls with
  | nil => simp at h
  | cons l Ls ih =>
    rw [List.map_cons, List.sum_cons] at h
    by_cases hj : j ∈ l
    · have hl : l.count j = 1 := by
        have := List.count_pos_iff.mpr hj
        omega
      have h0 : (Ls.map fun l => l.count j).sum = 0 := by omega
      refine ⟨0, by simp, by simpa using hl, fun i' hi' hm => ?_⟩
      rcases i' with _ | i'
      · rfl
      · exfalso
        have hi'' : i' < Ls.length := by simpa using hi'
        simp only [List.getElem_cons_succ] at hm
        have hpos := List.count_pos_iff.mpr hm
        have hle : Ls[i'].count j ≤ (Ls.map fun l => l.count j).sum :=
          List.le_sum_of_mem (List.mem_map.mpr ⟨_, List.getElem_mem _, rfl⟩)
        omega
    · have hl : l.count j = 0 := List.count_eq_zero.mpr hj
      obtain ⟨i, hi, hc, hu⟩ := ih (by omega)
      refine ⟨i + 1, by simpa using hi, by simpa using hc, fun i' hi' hm => ?_⟩
      rcases i' with _ | i'
      · exact absurd hm (by simpa using hj)
      · simp only [List.getElem_cons_succ] at hm
        rw [hu i' (by simpa using hi') hm]

namespace DescribedNetwork

variable {T : Type} (D : DescribedNetwork T)

/-! ### Rows first -/

/-- Being rows-first depends only on the ports, not on the descriptors. -/
theorem isRowsFirstBipartite_map {T' : Type} (f : T → T') (r : ℕ) :
    (⟨D.numEdges, D.vertices.map fun v => (v.1, f v.2)⟩ :
      DescribedNetwork T').IsRowsFirstBipartite r ↔
      D.IsRowsFirstBipartite r := by
  simp only [IsRowsFirstBipartite, List.forall_mem_map, ← List.map_take, ← List.map_drop,
    List.map_map, Function.comp_def]

/-- The vertices at the edge `j`: those having `j` among their ports, in increasing order. -/
@[expose] def incident (j : ℕ) : List ℕ :=
  (List.range D.vertices.length).filter fun v => j ∈ (D.vertices.map Prod.fst).getD v []

/-- **The ends of the edges**: for each edge, its first and its second vertex. -/
@[expose] def edgeEnds : List (ℕ × ℕ) :=
  (List.range D.numEdges).map fun j => ((D.incident j).getD 0 0, (D.incident j).getD 1 0)

variable {D}

/-- A rows-first network with an edge has at most as many rows as vertices. -/
theorem rows_le_of_isRowsFirstBipartite {D : DescribedNetwork T} {r : ℕ}
    (hD : D.IsRowsFirstBipartite r) (hM : 1 ≤ D.numEdges) : r ≤ D.vertices.length := by
  by_contra h
  have h1 := (hD.2 0 hM).2
  rw [List.drop_of_length_le (by omega)] at h1
  simp at h1

theorem getD_map_fst (v : ℕ) (hv : v < D.vertices.length) :
    (D.vertices.map Prod.fst).getD v [] = D.vertices[v].1 := by
  rw [List.getD_eq_getElem _ _ (by simpa using hv), List.getElem_map]

/-- **The two ends of an edge** of a rows-first network: a row `s < r` and a column `t ≥ r`, which
are the only vertices with the edge among their ports, each once. -/
theorem exists_ends {r : ℕ} (hD : D.IsRowsFirstBipartite r) {j : ℕ} (hj : j < D.numEdges) :
    ∃ s t, ∃ hs : s < D.vertices.length, ∃ ht : t < D.vertices.length, s < r ∧ r ≤ t ∧
      D.vertices[s].1.count j = 1 ∧ D.vertices[t].1.count j = 1 ∧
      ∀ v (hv : v < D.vertices.length), j ∈ D.vertices[v].1 → v = s ∨ v = t := by
  obtain ⟨hrow', hcol'⟩ := hD.2 j hj
  have hrow : (((D.vertices.map Prod.fst).take r).map fun l => l.count j).sum = 1 := by
    rw [← List.map_take, List.map_map]
    exact hrow'
  have hcol : (((D.vertices.map Prod.fst).drop r).map fun l => l.count j).sum = 1 := by
    rw [← List.map_drop, List.map_map]
    exact hcol'
  obtain ⟨s, hs, hsc, hsu⟩ := exists_unique_of_sum_count_eq_one hrow
  obtain ⟨t, ht, htc, htu⟩ := exists_unique_of_sum_count_eq_one hcol
  simp only [List.length_take, List.length_map, List.length_drop] at hs ht
  have hs' : s < D.vertices.length := by omega
  have hsr : s < r := by omega
  have ht' : r + t < D.vertices.length := by omega
  refine ⟨s, r + t, hs', ht', hsr, by omega, ?_, ?_, fun v hv hm => ?_⟩
  · simpa using hsc
  · simpa using htc
  · by_cases hvr : v < r
    · left
      refine hsu v (by simp; omega) ?_
      simpa [List.getElem_take] using hm
    · right
      have := htu (v - r) (by simp; omega) (by
        simp only [List.getElem_map, List.getElem_drop]
        convert hm using 3
        omega)
      omega

/-- **The vertices at an edge** of a rows-first network are its row and its column. -/
theorem incident_eq {r : ℕ} (hD : D.IsRowsFirstBipartite r) {j : ℕ} (hj : j < D.numEdges) :
    ∃ s t, ∃ hs : s < D.vertices.length, ∃ ht : t < D.vertices.length, s < r ∧ r ≤ t ∧
      D.vertices[s].1.count j = 1 ∧ D.vertices[t].1.count j = 1 ∧ D.incident j = [s, t] := by
  obtain ⟨s, t, hs, ht, hsr, hrt, hsc, htc, hu⟩ := exists_ends hD hj
  refine ⟨s, t, hs, ht, hsr, hrt, hsc, htc, ?_⟩
  have hsorted : (D.incident j).Pairwise (· < ·) :=
    (List.pairwise_lt_range).filter _
  have hmem : ∀ v, v ∈ D.incident j ↔ v ∈ [s, t] := by
    intro v
    simp only [incident, List.mem_filter, List.mem_range, decide_eq_true_eq, List.mem_cons,
      List.not_mem_nil, or_false]
    constructor
    · rintro ⟨hv, hm⟩
      rw [getD_map_fst v hv] at hm
      exact hu v hv hm
    · rintro (rfl | rfl)
      · refine ⟨hs, ?_⟩
        rw [getD_map_fst _ hs]
        exact List.count_pos_iff.mp (by omega)
      · refine ⟨ht, ?_⟩
        rw [getD_map_fst _ ht]
        exact List.count_pos_iff.mp (by omega)
  have hst : [s, t].Pairwise (· < ·) := by simp; omega
  exact hsorted.eq_of_mem_iff hst hmem

/-- The first vertex at an edge of a rows-first network is a vertex. -/
theorem getD_incident_zero_lt {r : ℕ} (hD : D.IsRowsFirstBipartite r) {j : ℕ}
    (hj : j < D.numEdges) : (D.incident j).getD 0 0 < D.vertices.length := by
  obtain ⟨s, t, hs, ht, -, -, -, -, h⟩ := incident_eq hD hj
  rw [h]
  exact hs

/-- The second vertex at an edge of a rows-first network is a vertex. -/
theorem getD_incident_one_lt {r : ℕ} (hD : D.IsRowsFirstBipartite r) {j : ℕ}
    (hj : j < D.numEdges) : (D.incident j).getD 1 0 < D.vertices.length := by
  obtain ⟨s, t, hs, ht, -, -, -, -, h⟩ := incident_eq hD hj
  rw [h]
  exact ht

/-! ### The network of a described network -/

/-- The row of an edge of a rows-first network. -/
@[expose] def srcFin {r : ℕ} (hD : D.IsRowsFirstBipartite r) (j : Fin D.numEdges) :
    Fin D.vertices.length :=
  ⟨(D.incident j).getD 0 0, getD_incident_zero_lt hD j.2⟩

/-- The column of an edge of a rows-first network. -/
@[expose] def tgtFin {r : ℕ} (hD : D.IsRowsFirstBipartite r) (j : Fin D.numEdges) :
    Fin D.vertices.length :=
  ⟨(D.incident j).getD 1 0, getD_incident_one_lt hD j.2⟩

/-- **The network of a rows-first described network**, on `Fin k` vertices and `Fin m` edges: the
edge `j` runs from its row to its column, and the tensor of a vertex is the evaluator at its
descriptor and the bits on its ports. -/
@[expose] noncomputable def toNetwork {r : ℕ} (hD : D.IsRowsFirstBipartite r) {R : Type*}
    (eval : T → List Bool → R) :
    TensorNetwork R Bool (Fin D.vertices.length) (Fin D.numEdges) where
  src := D.srcFin hD
  tgt := D.tgtFin hD
  tensor v x := eval D.vertices[v].2 (wordBits (List.ofFn x) D.vertices[v].1)
  tensor_congr v x y hxy := by
    congr 1
    refine List.map_congr_left fun i hi => ?_
    have hi' : i < D.numEdges := hD.1 _ (List.getElem_mem _) i hi
    obtain ⟨s, t, hs, ht, -, -, -, -, hinc⟩ := incident_eq hD hi'
    have hv : (v : ℕ) ∈ D.incident i := by
      simp only [incident, List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨v.2, by rw [getD_map_fst _ v.2]; exact hi⟩
    rw [List.getD_eq_getElem _ _ (by simpa using hi'),
      List.getD_eq_getElem _ _ (by simpa using hi'),
      List.getElem_ofFn, List.getElem_ofFn]
    refine hxy ⟨i, hi'⟩ ?_
    rw [hinc] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with hv | hv
    · left
      exact Fin.ext (by simp [srcFin, hinc, hv])
    · right
      exact Fin.ext (by simp [tgtFin, hinc, hv])

variable {r : ℕ} (hD : D.IsRowsFirstBipartite r)

@[simp] theorem toNetwork_src {R : Type*} (eval : T → List Bool → R) :
    (D.toNetwork hD eval).src = D.srcFin hD := rfl

@[simp] theorem toNetwork_tgt {R : Type*} (eval : T → List Bool → R) :
    (D.toNetwork hD eval).tgt = D.tgtFin hD := rfl

/-- The edges run from the rows. -/
theorem srcFin_lt (j : Fin D.numEdges) : (D.srcFin hD j : ℕ) < r := by
  obtain ⟨s, t, -, -, hsr, -, -, -, h⟩ := incident_eq hD j.2
  simp [srcFin, h, hsr]

/-- The edges end at the columns. -/
theorem le_tgtFin (j : Fin D.numEdges) : r ≤ (D.tgtFin hD j : ℕ) := by
  obtain ⟨s, t, -, -, -, hrt, -, -, h⟩ := incident_eq hD j.2
  simp [tgtFin, h, hrt]

/-- A vertex has an edge among its ports exactly when it is an end of the edge. -/
theorem mem_ports_iff (v : Fin D.vertices.length) (j : Fin D.numEdges) :
    (j : ℕ) ∈ D.vertices[v].1 ↔ D.srcFin hD j = v ∨ D.tgtFin hD j = v := by
  obtain ⟨s, t, hs, ht, -, -, hsc, htc, hinc⟩ := incident_eq hD j.2
  have hmem : (v : ℕ) ∈ D.incident j ↔ (j : ℕ) ∈ D.vertices[v].1 := by
    simp only [incident, List.mem_filter, List.mem_range, decide_eq_true_eq]
    rw [getD_map_fst _ v.2]
    exact ⟨fun h => h.2, fun h => ⟨v.2, h⟩⟩
  rw [← hmem, hinc]
  simp only [List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff, srcFin, tgtFin, hinc,
    List.getD_cons_zero, List.getD_cons_succ]
  exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩

/-- **The ends of the edges** are the native `edgeEnds`. -/
theorem edgeEnds_eq :
    D.edgeEnds = List.ofFn fun j => ((D.srcFin hD j : ℕ), (D.tgtFin hD j : ℕ)) := by
  rw [edgeEnds, ← List.map_coe_finRange_eq_range, List.map_map, List.ofFn_eq_map]
  rfl

/-- **The network has the contraction of the described network.** -/
theorem contraction_toNetwork {R : Type*} [CommSemiring R] (eval : T → List Bool → R) :
    (D.toNetwork hD eval).contraction = D.contraction eval := by
  simp only [TensorNetwork.contraction, contraction]
  refine sum_congr rfl fun x _ => ?_
  rw [← List.ofFn_getElem_eq_map, List.prod_ofFn]
  rfl

/-- The network of a described network commutes with maps of the entries. -/
theorem toNetwork_map {R S : Type*} [CommSemiring R] [CommSemiring S] (eval : T → List Bool → R)
    (ψ : R →+* S) : (D.toNetwork hD eval).map ψ = D.toNetwork hD fun t bs => ψ (eval t bs) :=
  rfl

/-- **Over `O`, the contraction reduces to the contraction in `A_p`.** For the network with the
lifts of the entries of the descriptors, reduction modulo `2 ^ p` of its contraction is the
contraction of the described network with the values of the entries in `A_p`. -/
theorem reduction_contraction_toNetwork {fl : List ℕ}
    (hirr : Irreducible ((GaloisRingArith.monicOf fl).map (Int.castRingHom (ZMod 2))))
    (eval : T → List Bool → List ℕ) (p : ℕ) :
    reduction (GaloisRingArith.monic_monicOf fl) hirr p
        (D.toNetwork hD fun t bs => GaloisRingArith.liftO hirr (eval t bs)).contraction =
      D.contraction fun t bs => GaloisRingArith.val p fl (eval t bs) := by
  rw [contraction_toNetwork, map_contraction]
  simp only [GaloisRingArith.reduction_liftO]

/-! ### Polynomial time -/

section PolyTime

open Turing.MultiTapeTM

variable {T : Type} (encT : T ↪ List Bool)

/-- **The vertices at an edge are polynomial-time**, with the edge in unary. -/
theorem computableInPolyTime_incident :
    ComputableInPolyTime (fun q : DescribedNetwork T × ℕ => q.1.incident q.2)
      (encPair (encDescribed encT) encUnary) (encList encUnary) := by
  have hV : ComputableInPolyTime (fun q : DescribedNetwork T × ℕ => q.1.vertices)
      (encPair (encDescribed encT) encUnary) (encList (encPair (encList encNat) encT)) :=
    vertices_polyTime.comp (ComputableInPolyTime.fst _ _)
  have hP : ComputableInPolyTime (fun q : DescribedNetwork T × ℕ => q.1.vertices.map Prod.fst)
      (encPair (encDescribed encT) encUnary) (encList (encList encNat)) :=
    ComputableInPolyTime.mapWithInput (f := fun _ v => v.1) hV
      ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.snd _ _))
  have hrange : ComputableInPolyTime (fun q : DescribedNetwork T × ℕ =>
      List.range q.1.vertices.length) (encPair (encDescribed encT) encUnary) (encList encUnary) :=
    ComputableInPolyTime.range.comp ((ComputableInPolyTime.length_list _).comp hV)
  have hports : ComputableInPolyTime (fun z : (DescribedNetwork T × ℕ) × ℕ =>
      (z.1.1.vertices.map Prod.fst).getD z.2 [])
      (encPair (encPair (encDescribed encT) encUnary) encUnary) (encList encNat) :=
    (ComputableInPolyTime.listGetD (encA := encList encNat) []).comp
      ((hP.comp (ComputableInPolyTime.fst _ _)).prod (ComputableInPolyTime.snd _ _))
  have hj : ComputableInPolyTime (fun z : (DescribedNetwork T × ℕ) × ℕ => z.1.2)
      (encPair (encPair (encDescribed encT) encUnary) encUnary) encNat :=
    ComputableInPolyTime.unary_to_binary.comp
      ((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.fst _ _))
  exact ComputableInPolyTime.filterWithInput
    (test := fun q v => decide (q.2 ∈ (q.1.vertices.map Prod.fst).getD v [])) hrange
    (ComputableInPolyTime.decide_mem hports hj)

/-- **The ends of the edges are polynomial-time.** -/
theorem computableInPolyTime_edgeEnds :
    ComputableInPolyTime (fun D : DescribedNetwork T => D.edgeEnds) (encDescribed encT)
      (encList (encPair encNat encNat)) := by
  have hinc : ComputableInPolyTime (fun q : DescribedNetwork T × ℕ => q.1.incident q.2)
      (encPair (encDescribed encT) encUnary) (encList encUnary) :=
    computableInPolyTime_incident encT
  have hget (i : ℕ) : ComputableInPolyTime (fun q : DescribedNetwork T × ℕ =>
      (q.1.incident q.2).getD i 0) (encPair (encDescribed encT) encUnary) encNat :=
    ComputableInPolyTime.unary_to_binary.comp
      ((ComputableInPolyTime.listGetD (encA := encUnary) 0).comp
        (hinc.prod (ComputableInPolyTime.const i)))
  exact ComputableInPolyTime.mapWithInput
    (f := fun D j => ((D.incident j).getD 0 0, (D.incident j).getD 1 0))
    (ComputableInPolyTime.range.comp numEdges_polyTime) ((hget 0).prod (hget 1))

end PolyTime

end DescribedNetwork

end Cslib.Circuits.Frontier
