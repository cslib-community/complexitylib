/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CMMSA
public import CslibFrontier.Computability.PCP.Approximation.LabelCover
import CslibFrontier.Computability.PCP.Approximation.LabelCover.SmallSoundness
import CslibFrontier.Foundations.Data.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Mathlib.Data.List.GetD

/-!
# Weighted Min-Rep: from Label Cover to CMMSA

A library reduction, adapting the Min-Rep problem [Kortsarz2001], turns a Label Cover instance into
an instance of CMMSA [Hirahara2022, Section II.B, p. 974] (`Cslib.Complexity.GapCMMSA`). For an
instance with `m` edges, left labels `β` and right labels `γ`:

* there is a variable `x_{u,a}` for each left end `u` of an edge and each label `a : β`, of weight
  the degree of `u`, and a variable `y_{v,b}` for each right end `v` and each `b : γ`, of weight
  the degree of `v` (with padding, described below);
* each edge `e` from `u` to `v` with projection `π` gives the monotone DNF
  `φ_e = ⋁_a (x_{u,a} ∧ y_{v,π a})`, with `2 |β|` literals;
* the threshold is `θ = 2m`.

A labelling satisfying every edge selects one variable per vertex, of total weight `2m`
(`minRep_mem_yes`). Conversely, let an assignment of weight at most `2gm` satisfy every `φ_e`, and
let `A_u` and `B_v` be the labels it selects at the vertices. Labelling every vertex uniformly at
random from its selected labels satisfies each edge `e` from `u` to `v` with probability at least
`1 / (|A_u| |B_v|)`. The degree weights make `∑_e (|A_u| + |B_v|)` at most the weight `2gm`, and
the tangent line of `t ↦ 4 / t²` at `t = 2g` turns this into an expected `m / g²` satisfied edges.
So a Label Cover instance of value at most `δ < 1 / g²` gives a no-instance (`minRep_mem_no`).

**Variable layout.** The left ends of the edges are listed with multiplicity (`srcs`), and so are
the right ends (`dsts`). Every entry of these lists gets a block of `nβ` (respectively `nγ`)
variables, so the instance has `m (nβ + nγ)` variables: a vertex of degree `d` gets `d` blocks.
The formulas use only the block at the vertex's first occurrence (`blockVar`). The other `d - 1`
blocks are padding: their variables weigh `d` like the used ones, appear in no formula and are
never needed. Only ends of edges get variables, so every weight is positive, as
`CMMSAInstance.WellFormed` requires. An instance with no edges maps to a fixed yes-instance with
threshold `1`. Labels are numbered through fixed equivalences `β ≃ Fin nβ` and `γ ≃ Fin nγ`.

The construction and the gap-preservation argument are library results adapting the Min-Rep idea
to CMMSA, with proportion `σ = 1` and a constant gap `g`. The paper's hardness of CMMSA, for
`g = Δ^ε` and `σ = Δ^{-ε}`, needs Label Cover with polynomially small soundness [Hirahara2022,
Section II.B] and is not proved here.

## Main definitions

* `Cslib.PCP.Encoded.LabelCoverMinRep.minRep`: the CMMSA instance of a Label Cover instance.

## Main results

* `Cslib.PCP.Encoded.LabelCoverMinRep.wellFormed_minRep`: the output is well formed, with at most
  `2 nβ` literals per formula.
* `Cslib.PCP.Encoded.LabelCoverMinRep.minRep_mem_yes`: satisfiable instances give yes-instances.
* `Cslib.PCP.Encoded.LabelCoverMinRep.minRep_mem_no`: instances of value at most `δ < 1 / g²`
  give no-instances for the gap `g` and the proportion `1`.
* `Cslib.PCP.Encoded.LabelCoverMinRep.isPolyTime_minRep`: the construction is polynomial-time.
* `Cslib.Complexity.polyTimeReducible_GapLabelCover_GapCMMSA`: the reduction.
* `Cslib.Complexity.exists_GapCMMSA_npHard`: for every constant gap `g ≥ 1` some literal bound `Δ`
  makes `GapCMMSA Δ g 1` NP-hard.

## References

* [G. Kortsarz, *On the hardness of approximating spanners*][Kortsarz2001]
* [S. Hirahara, *NP-Hardness of Learning Programs and Partial MCSP*][Hirahara2022]
-/

public section

namespace Cslib.PCP.Encoded.LabelCoverMinRep

open Cslib.Complexity Cslib.Logic.PL Finset Turing.MultiTapeTM

/-! ### The construction -/

/-- The variable of the label `a` of the vertex `u` in the block of the vertex list `L` starting
at `off`, with `n` labels per entry: the block at the first occurrence of `u` in `L`. -/
@[expose] def blockVar (L : List ℕ) (off n u a : ℕ) : ℕ :=
  off + L.idxOf u * n + a

/-- The weights of the blocks of the vertex list `L`, with `n` labels per entry: one block of `n`
variables for every entry of `L`, repeated vertices included, each weighing the number of
occurrences of its vertex in `L`. Only the block at a vertex's first occurrence is used by
`blockVar`. -/
@[expose] def blockWeights (L : List ℕ) (n : ℕ) : List ℕ :=
  (List.range (L.length * n)).map fun k => L.count (L.getD (k / n) 0)

section Ends

variable {C : Type}

/-- The left ends of the edges, with multiplicity. -/
@[expose] def srcs (G : Graph C) : List ℕ :=
  G.edges.map Edge.src

/-- The right ends of the edges, with multiplicity. -/
@[expose] def dsts (G : Graph C) : List ℕ :=
  G.edges.map Edge.dst

end Ends

variable {β γ : Type} {nβ nγ : ℕ} (eβ : β ≃ Fin nβ) (eγ : γ ≃ Fin nγ)

/-- The formula `⋁_a (x_{u,a} ∧ y_{v,π a})` of an edge from `u` to `v` with projection `π`. -/
@[expose] def formula (G : Graph (β → γ)) (d : Edge (β → γ)) : DNF ℕ :=
  (List.finRange nβ).map fun a : Fin nβ =>
    [(blockVar (srcs G) 0 nβ d.src a, true),
      (blockVar (dsts G) ((srcs G).length * nβ) nγ d.dst (eγ (d.constraint (eβ.symm a))), true)]

/-- The **weighted Min-Rep** instance of a Label Cover instance: one block of degree-weighted
variables per edge end (so `m (nβ + nγ)` variables, the blocks after a vertex's first occurrence
appearing in no formula), one formula per edge and the threshold `2m` (or `1` without edges). -/
@[expose] def minRep (G : Graph (β → γ)) : CMMSAInstance where
  weights := blockWeights (srcs G) nβ ++ blockWeights (dsts G) nγ
  threshold := max (2 * G.edges.length) 1
  formulas := G.edges.map (formula eβ eγ G)

/-! ### Variables and weights -/

theorem length_blockWeights (L : List ℕ) (n : ℕ) : (blockWeights L n).length = L.length * n := by
  simp [blockWeights]

theorem length_srcs {C : Type} (G : Graph C) : (srcs G).length = G.edges.length :=
  List.length_map _

theorem length_dsts {C : Type} (G : Graph C) : (dsts G).length = G.edges.length :=
  List.length_map _

private theorem mul_add_lt {i k n a : ℕ} (hi : i < k) (ha : a < n) : i * n + a < k * n :=
  calc i * n + a < i * n + n := by omega
    _ = (i + 1) * n := by ring
    _ ≤ k * n := Nat.mul_le_mul_right n hi

/-- The weight of the variable of the label `a` of the `k`-th vertex is that vertex's degree. -/
theorem getD_blockWeights {L : List ℕ} {n k a : ℕ} (hk : k < L.length) (ha : a < n) :
    (blockWeights L n).getD (k * n + a) 0 = L.count L[k] := by
  have hlt := mul_add_lt hk ha
  rw [List.getD_eq_getElem _ _ (by simpa [length_blockWeights] using hlt)]
  simp only [blockWeights, List.getElem_map, List.getElem_range, Nat.mul_add_div_of_lt _ ha,
    List.getD_eq_getElem _ _ hk]

theorem pos_of_mem_blockWeights {L : List ℕ} {n w : ℕ} (hw : w ∈ blockWeights L n) : 0 < w := by
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hw
  have hk' : k / n < L.length := Nat.div_lt_of_lt_mul (by
    simpa [Nat.mul_comm] using List.mem_range.1 hk)
  rw [List.getD_eq_getElem _ _ hk']
  exact List.count_pos_iff.2 (List.getElem_mem _)

theorem blockVar_lt {L : List ℕ} {off n u a : ℕ} (hu : u ∈ L) (ha : a < n) :
    blockVar L off n u a < off + L.length * n := by
  have := mul_add_lt (List.idxOf_lt_length_of_mem hu) ha
  unfold blockVar
  omega

private theorem blockVar_inj {L : List ℕ} {off n u v a b : ℕ} (hu : u ∈ L)
    (ha : a < n) (hb : b < n) (h : blockVar L off n u a = blockVar L off n v b) :
    u = v ∧ a = b := by
  unfold blockVar at h
  have h' : L.idxOf u * n + a = L.idxOf v * n + b := by omega
  have hidx : L.idxOf u = L.idxOf v := by
    rw [← Nat.mul_add_div_of_lt (L.idxOf u) ha, ← Nat.mul_add_div_of_lt (L.idxOf v) hb, h']
  exact ⟨(List.idxOf_inj hu).1 hidx, by rw [hidx] at h'; omega⟩

theorem mem_srcs {C : Type} {G : Graph C} {d : Edge C} (hd : d ∈ G.edges) : d.src ∈ srcs G :=
  List.mem_map_of_mem hd

theorem mem_dsts {C : Type} {G : Graph C} {d : Edge C} (hd : d ∈ G.edges) : d.dst ∈ dsts G :=
  List.mem_map_of_mem hd

/-- A left variable weighs the degree of its vertex. -/
theorem getD_weights_left {G : Graph (β → γ)} {u a : ℕ} (hu : u ∈ srcs G) (ha : a < nβ) :
    (minRep eβ eγ G).weights.getD (blockVar (srcs G) 0 nβ u a) 0 = (srcs G).count u := by
  have hlt := blockVar_lt (off := 0) hu ha
  rw [minRep, List.getD_append _ _ _ _ (by rw [length_blockWeights]; omega)]
  simp only [blockVar, zero_add]
  rw [getD_blockWeights (List.idxOf_lt_length_of_mem hu) ha, List.getElem_idxOf]

/-- A right variable weighs the degree of its vertex. -/
theorem getD_weights_right {G : Graph (β → γ)} {v b : ℕ} (hv : v ∈ dsts G) (hb : b < nγ) :
    (minRep eβ eγ G).weights.getD (blockVar (dsts G) ((srcs G).length * nβ) nγ v b) 0 =
      (dsts G).count v := by
  rw [minRep, List.getD_append_right _ _ _ _ (by rw [length_blockWeights]; unfold blockVar; omega)]
  simp only [length_blockWeights, blockVar, add_assoc, Nat.add_sub_cancel_left]
  rw [getD_blockWeights (List.idxOf_lt_length_of_mem hv) hb, List.getElem_idxOf]

/-- The formula of an edge holds exactly when some label of its left end and its projection at its
right end are both selected. -/
theorem eval_formula (G : Graph (β → γ)) (d : Edge (β → γ)) (T : Finset ℕ) :
    (formula eβ eγ G d).eval (fun i => decide (i ∈ T)) = true ↔ ∃ a : Fin nβ,
      blockVar (srcs G) 0 nβ d.src a ∈ T ∧
        blockVar (dsts G) ((srcs G).length * nβ) nγ d.dst (eγ (d.constraint (eβ.symm a))) ∈ T := by
  simp [formula, DNF.eval_eq_true_iff, Term.eval_eq_true_iff]

/-! ### Well-formedness and completeness -/

theorem length_flatten_formula (G : Graph (β → γ)) (d : Edge (β → γ)) :
    (formula eβ eγ G d).flatten.length = 2 * nβ := by
  simp [formula, List.length_flatten, Function.comp_def, List.sum_replicate, Nat.mul_comm]

/-- **The output is well formed**, with `2 nβ` literal occurrences per formula. -/
theorem wellFormed_minRep [Nonempty β] (G : Graph (β → γ)) :
    (minRep eβ eγ G).WellFormed (2 * nβ) where
  weight_pos w hw := by
    rcases List.mem_append.1 hw with hw | hw <;> exact pos_of_mem_blockWeights hw
  threshold_pos := by simp only [minRep]; omega
  formula_ne_nil φ hφ := by
    obtain ⟨d, -, rfl⟩ := List.mem_map.1 hφ
    have : 0 < nβ := Fin.pos_iff_nonempty.2 ⟨eβ (Classical.arbitrary β)⟩
    simp only [formula, ne_eq, List.map_eq_nil_iff, List.finRange_eq_nil_iff]
    omega
  term_ne_nil φ hφ t ht := by
    obtain ⟨d, -, rfl⟩ := List.mem_map.1 hφ
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 ht
    simp
  monotone φ hφ t ht l hl := by
    obtain ⟨d, -, rfl⟩ := List.mem_map.1 hφ
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> rfl
  var_lt φ hφ t ht l hl := by
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hφ
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    have hl₁ := blockVar_lt (off := 0) (mem_srcs hd) a.isLt
    have hl₂ := blockVar_lt (off := (srcs G).length * nβ) (mem_dsts hd)
      (eγ (d.constraint (eβ.symm a))).isLt
    simp only [minRep, List.length_append, length_blockWeights]
    rcases hl with rfl | rfl <;> dsimp only <;> omega
  length_flatten_le φ hφ := by
    obtain ⟨d, -, rfl⟩ := List.mem_map.1 hφ
    rw [length_flatten_formula]

/-- **Completeness.** A satisfiable Label Cover instance gives a yes-instance: selecting the
variable of the label of every end of an edge costs `2m`. -/
theorem minRep_mem_yes [Nonempty β] [DecidableEq γ] {G : Graph (β → γ)} {Δ : ℕ} {g σ : ℝ}
    (hG : (G.toGraph projectionEval).Satisfiable) (hΔ : 2 * nβ ≤ Δ) :
    minRep eβ eγ G ∈ (GapCMMSA Δ g σ).yes := by
  obtain ⟨ℓ, r, h⟩ := (satisfiable_toGraph_projectionEval_iff G).1 hG
  let left := (srcs G).toFinset.image fun u => blockVar (srcs G) 0 nβ u (eβ (ℓ u))
  let right := (dsts G).toFinset.image fun v =>
    blockVar (dsts G) ((srcs G).length * nβ) nγ v (eγ (r v))
  refine mem_yes_GapCMMSA.2 ⟨(wellFormed_minRep eβ eγ G).mono hΔ, left ∪ right, ?_, ?_, ?_⟩
  · intro x hx
    simp only [minRep, Finset.mem_range, List.length_append, length_blockWeights]
    rcases Finset.mem_union.1 hx with hx | hx <;> obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hx
    · have := blockVar_lt (off := 0) (List.mem_toFinset.1 hu) (eβ (ℓ u)).isLt
      omega
    · exact blockVar_lt (List.mem_toFinset.1 hu) (eγ (r u)).isLt
  · have hleft : ∑ x ∈ left, (minRep eβ eγ G).weights.getD x 0 ≤ G.edges.length := by
      refine (Finset.sum_image_le_of_nonneg fun _ _ => Nat.zero_le _).trans_eq ?_
      rw [Finset.sum_congr rfl fun u hu => getD_weights_left eβ eγ (List.mem_toFinset.1 hu)
        (eβ (ℓ u)).isLt, List.sum_toFinset_count_eq_length, length_srcs]
    have hright : ∑ x ∈ right, (minRep eβ eγ G).weights.getD x 0 ≤ G.edges.length := by
      refine (Finset.sum_image_le_of_nonneg fun _ _ => Nat.zero_le _).trans_eq ?_
      rw [Finset.sum_congr rfl fun v hv => getD_weights_right eβ eγ (List.mem_toFinset.1 hv)
        (eγ (r v)).isLt, List.sum_toFinset_count_eq_length, length_dsts]
    have hunion := Finset.sum_union_inter (s₁ := left) (s₂ := right)
      (f := fun x => (minRep eβ eγ G).weights.getD x 0)
    simp only [CMMSAInstance.weight]
    have hth : (minRep eβ eγ G).threshold = max (2 * G.edges.length) 1 := rfl
    rw [hth]
    omega
  · intro φ hφ
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hφ
    rw [eval_formula]
    refine ⟨eβ (ℓ d.src), Finset.mem_union_left _ (Finset.mem_image.2
      ⟨d.src, List.mem_toFinset.2 (mem_srcs hd), rfl⟩), Finset.mem_union_right _
        (Finset.mem_image.2 ⟨d.dst, List.mem_toFinset.2 (mem_dsts hd), ?_⟩)⟩
    rw [Equiv.symm_apply_apply, h d hd]

/-! ### Soundness -/

/-- The labels of the vertex `u` that the assignment `T` selects in a block. -/
private def labels (T : Finset ℕ) (L : List ℕ) (off n u : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun a => blockVar L off n u a ∈ T

/-- Summed with degree multiplicities, the selected labels of a block weigh at most the selected
variables of the block. -/
private theorem sum_count_mul_card_labels_le (T : Finset ℕ) (L : List ℕ) (off n : ℕ)
    (w : ℕ → ℕ) (hw : ∀ u ∈ L, ∀ a < n, w (blockVar L off n u a) = L.count u) :
    ∑ u ∈ L.toFinset, L.count u * #(labels T L off n u) ≤
      ∑ x ∈ T.filter fun x => off ≤ x ∧ x < off + L.length * n, w x := by
  have hinj : Set.InjOn (fun p : ℕ × Fin n => blockVar L off n p.1 p.2)
      ((L.toFinset ×ˢ (Finset.univ : Finset (Fin n)) : Finset (ℕ × Fin n)) : Set (ℕ × Fin n)) := by
    rintro ⟨u, a⟩ hua ⟨v, b⟩ - h
    simp only [Finset.mem_coe, Finset.mem_product, List.mem_toFinset, Finset.mem_univ,
      and_true] at hua
    obtain ⟨rfl, hab⟩ := blockVar_inj hua a.isLt b.isLt h
    exact Prod.ext rfl (Fin.ext hab)
  let P := (L.toFinset ×ˢ (Finset.univ : Finset (Fin n))).filter fun p =>
    blockVar L off n p.1 p.2 ∈ T
  calc ∑ u ∈ L.toFinset, L.count u * #(labels T L off n u)
      = ∑ p ∈ P, w (blockVar L off n p.1 p.2) := by
        rw [Finset.sum_filter, Finset.sum_product]
        refine Finset.sum_congr rfl fun u hu => ?_
        rw [labels, Finset.card_filter, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        dsimp only
        rw [hw u (List.mem_toFinset.1 hu) a a.isLt]
        split_ifs <;> simp
    _ = ∑ x ∈ P.image fun p => blockVar L off n p.1 p.2, w x :=
        (Finset.sum_image (hinj.mono (Finset.filter_subset _ _))).symm
    _ ≤ ∑ x ∈ T.filter fun x => off ≤ x ∧ x < off + L.length * n, w x := by
        refine Finset.sum_le_sum_of_subset fun x hx => ?_
        obtain ⟨⟨u, a⟩, hp, rfl⟩ := Finset.mem_image.1 hx
        simp only [P, Finset.mem_filter, Finset.mem_product, List.mem_toFinset] at hp
        refine Finset.mem_filter.2 ⟨hp.2, ?_, blockVar_lt hp.1.1 a.isLt⟩
        unfold blockVar
        omega

/-- A sum over the edges of a function of their left ends, grouped by vertex. -/
private theorem sum_edges_eq {C : Type} (G : Graph C) (p : Edge C → ℕ) (F : ℕ → ℕ) :
    ∑ i : Fin G.edges.length, F (p (G.edges.get i)) =
      ∑ u ∈ (G.edges.map p).toFinset, (G.edges.map p).count u * F u := by
  have h1 := Fin.sum_univ_fun_getElem G.edges fun d => F (p d)
  have h2 := Finset.sum_list_map_count (G.edges.map p) F
  rw [List.map_map] at h2
  simp only [smul_eq_mul] at h2
  exact h1.trans h2

/-- **The degree weights pay for the selected labels**: the selected labels at the two ends of
the edges, summed over the edges, weigh at most the assignment. -/
private theorem sum_card_labels_le (G : Graph (β → γ)) (T : Finset ℕ) :
    ∑ i : Fin G.edges.length, (#(labels T (srcs G) 0 nβ (G.edges.get i).src) +
      #(labels T (dsts G) ((srcs G).length * nβ) nγ (G.edges.get i).dst)) ≤
        (minRep eβ eγ G).weight T := by
  have hleft := sum_count_mul_card_labels_le T (srcs G) 0 nβ
    (fun x => (minRep eβ eγ G).weights.getD x 0) fun u hu a ha => getD_weights_left eβ eγ hu ha
  have hright := sum_count_mul_card_labels_le T (dsts G) ((srcs G).length * nβ) nγ
    (fun x => (minRep eβ eγ G).weights.getD x 0) fun v hv b hb => getD_weights_right eβ eγ hv hb
  rw [Finset.sum_add_distrib]
  refine (add_le_add
    ((sum_edges_eq G Edge.src fun u => #(labels T (srcs G) 0 nβ u)).trans_le hleft)
    ((sum_edges_eq G Edge.dst fun v => #(labels T (dsts G) ((srcs G).length * nβ) nγ v)).trans_le
      hright)).trans ?_
  unfold CMMSAInstance.weight
  rw [← Finset.sum_filter_add_sum_filter_not T fun x => 0 ≤ x ∧ x < 0 + (srcs G).length * nβ]
  refine add_le_add le_rfl (Finset.sum_le_sum_of_subset fun x hx => ?_)
  simp only [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, by omega⟩

/-- **Averaging over random labellings.** If every index `i` has a pair of labels in `A (s i)`
and `B (t i)` satisfying `P i`, some choice of a label in `A v` for every `v` and in `B w` for
every `w` satisfies at least `∑ 1 / (|A (s i)| |B (t i)|)` of the indices. -/
private theorem exists_labelling_ge {ι V W α α' : Type} [Fintype ι] [Finite V] [Finite W]
    (s : ι → V) (t : ι → W)
    (A : V → Finset α) (B : W → Finset α') (hA : ∀ v, (A v).Nonempty) (hB : ∀ w, (B w).Nonempty)
    (P : ι → α → α' → Prop) [∀ i a b, Decidable (P i a b)]
    (hP : ∀ i, ∃ a ∈ A (s i), ∃ b ∈ B (t i), P i a b) :
    ∃ (f : V → α) (h : W → α'), ∑ i, (1 / (#(A (s i)) * #(B (t i))) : ℝ) ≤
      #(Finset.univ.filter fun i => P i (f (s i)) (h (t i))) := by
  classical
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite W
  let Ω := Fintype.piFinset A ×ˢ Fintype.piFinset B
  have hΩ : Ω.Nonempty :=
    (Fintype.piFinset_nonempty.2 hA).product (Fintype.piFinset_nonempty.2 hB)
  have hfib (i : ι) : (#Ω : ℝ) / (#(A (s i)) * #(B (t i))) ≤
      #(Ω.filter fun p => P i (p.1 (s i)) (p.2 (t i))) := by
    obtain ⟨a, ha, b, hb, hab⟩ := hP i
    have hsub : (Fintype.piFinset A).filter (fun f => f (s i) = a) ×ˢ
        (Fintype.piFinset B).filter (fun h => h (t i) = b) ⊆
          Ω.filter fun p => P i (p.1 (s i)) (p.2 (t i)) := by
      intro p hp
      simp only [Finset.mem_product, Finset.mem_filter] at hp
      exact Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hp.1.1, hp.2.1⟩, hp.1.2 ▸ hp.2.2 ▸ hab⟩
    have hcardA : #((Fintype.piFinset A).filter fun f => f (s i) = a) * #(A (s i)) =
        #(Fintype.piFinset A) := by
      rw [Fintype.card_filter_piFinset_eq_of_mem _ _ ha, Fintype.card_piFinset, mul_comm]
      exact Finset.mul_prod_erase Finset.univ (fun j => #(A j)) (Finset.mem_univ _)
    have hcardB : #((Fintype.piFinset B).filter fun h => h (t i) = b) * #(B (t i)) =
        #(Fintype.piFinset B) := by
      rw [Fintype.card_filter_piFinset_eq_of_mem _ _ hb, Fintype.card_piFinset, mul_comm]
      exact Finset.mul_prod_erase Finset.univ (fun j => #(B j)) (Finset.mem_univ _)
    have hpos : (0 : ℝ) < #(A (s i)) * #(B (t i)) := by
      have := (hA (s i)).card_pos
      have := (hB (t i)).card_pos
      positivity
    rw [div_le_iff₀ hpos]
    have hle : (#((Fintype.piFinset A).filter fun f => f (s i) = a) : ℝ) *
        #((Fintype.piFinset B).filter fun h => h (t i) = b) ≤
          #(Ω.filter fun p => P i (p.1 (s i)) (p.2 (t i))) := by
      have := Finset.card_le_card hsub
      rw [Finset.card_product] at this
      exact_mod_cast this
    have hΩcard : (#Ω : ℝ) = #((Fintype.piFinset A).filter fun f => f (s i) = a) *
        #((Fintype.piFinset B).filter fun h => h (t i) = b) * (#(A (s i)) * #(B (t i))) := by
      simp only [Ω, Finset.card_product]
      rw [← hcardA, ← hcardB]
      push_cast
      ring
    rw [hΩcard]
    exact mul_le_mul_of_nonneg_right hle hpos.le
  have hsum : ∑ _p ∈ Ω, ∑ i, (1 / (#(A (s i)) * #(B (t i))) : ℝ) ≤
      ∑ p ∈ Ω, (#(Finset.univ.filter fun i => P i (p.1 (s i)) (p.2 (t i))) : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
    calc ∑ i, (#Ω : ℝ) * (1 / (#(A (s i)) * #(B (t i))))
        ≤ ∑ i, (#(Ω.filter fun p => P i (p.1 (s i)) (p.2 (t i))) : ℝ) :=
          Finset.sum_le_sum fun i _ => by rw [mul_one_div]; exact hfib i
      _ = ∑ p ∈ Ω, (#(Finset.univ.filter fun i => P i (p.1 (s i)) (p.2 (t i))) : ℝ) := by
          simp only [Finset.card_filter]
          push_cast
          exact Finset.sum_comm
  obtain ⟨⟨f, h⟩, -, hfh⟩ := Finset.exists_le_of_sum_le hΩ hsum
  exact ⟨f, h, hfh⟩

/-- The tangent line of `t ↦ 4 / t²` at `t = 2g`, below `1 / (ab) ≥ 4 / (a + b)²`. -/
private theorem three_div_sub_le_one_div_mul {a b g : ℝ} (ha : 0 < a) (hb : 0 < b) (hg : 0 < g) :
    3 / g ^ 2 - (a + b) / g ^ 3 ≤ 1 / (a * b) := by
  have ht : 0 < a + b := by positivity
  have h1 : 4 / (a + b) ^ 2 ≤ 1 / (a * b) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (a - b)]
  have h2 : 3 / g ^ 2 - (a + b) / g ^ 3 ≤ 4 / (a + b) ^ 2 := by
    have : 3 / g ^ 2 - (a + b) / g ^ 3 = (3 * g - (a + b)) / g ^ 3 := by field_simp
    rw [this, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (sq_nonneg (a + b - 2 * g)) (le_of_lt (add_pos ht hg))]
  linarith

/-- **Jensen's inequality for `1 / (ab)`, through its tangent line**: positive pairs whose sums
add up to at most `2gm` have `∑ 1 / (a_i b_i) ≥ m / g²`. -/
private theorem card_div_le_sum_one_div {ι : Type} [Fintype ι] {a b : ι → ℝ} {g : ℝ}
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hg : 0 < g)
    (hsum : ∑ i, (a i + b i) ≤ g * (2 * Fintype.card ι)) :
    Fintype.card ι / g ^ 2 ≤ ∑ i, 1 / (a i * b i) := by
  have hle := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    three_div_sub_le_one_div_mul (ha i) (hb i) hg
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Finset.sum_div] at hle
  have hdiv : (∑ i, (a i + b i)) / g ^ 3 ≤ g * (2 * Fintype.card ι) / g ^ 3 :=
    div_le_div_of_nonneg_right hsum (by positivity)
  have hcalc : g * (2 * Fintype.card ι) / g ^ 3 = 2 * (Fintype.card ι / g ^ 2) := by
    field_simp
  have hcalc' : (Fintype.card ι : ℝ) * (3 / g ^ 2) = 3 * (Fintype.card ι / g ^ 2) := by ring
  linarith

/-- An edge whose formula holds has a selected label at its left end whose projection is selected
at its right end. -/
private theorem exists_mem_labels {G : Graph (β → γ)} {T : Finset ℕ} {d : Edge (β → γ)}
    (hd : (formula eβ eγ G d).eval (fun i => decide (i ∈ T)) = true) :
    ∃ a ∈ labels T (srcs G) 0 nβ d.src,
      eγ (d.constraint (eβ.symm a)) ∈ labels T (dsts G) ((srcs G).length * nβ) nγ d.dst := by
  obtain ⟨a, ha, hb⟩ := (eval_formula eβ eγ G d T).1 hd
  exact ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ _, ha⟩,
    Finset.mem_filter.2 ⟨Finset.mem_univ _, hb⟩⟩

/-- **Soundness.** A Label Cover instance of value at most `δ < 1 / g²` gives a no-instance with
gap `g` and proportion `1`: every assignment of weight at most `2gm` falsifies some formula. -/
theorem minRep_mem_no [Nonempty β] [DecidableEq γ] {G : Graph (β → γ)} {Δ : ℕ} {g δ : ℝ}
    (hΔ : 2 * nβ ≤ Δ) (hg : 1 ≤ g) (hδ : δ < 1 / g ^ 2)
    (hG : 1 - (G.toGraph projectionEval).unsatVal ≤ δ) :
    minRep eβ eγ G ∈ (GapCMMSA Δ g 1).no := by
  refine mem_no_GapCMMSA_one.2 ⟨(wellFormed_minRep eβ eγ G).mono hΔ, hg, fun T _ hT => ?_⟩
  by_contra hall
  simp only [not_exists, not_and, Bool.not_eq_false] at hall
  have hsat (d : Edge (β → γ)) (hd : d ∈ G.edges) :
      (formula eβ eγ G d).eval (fun i => decide (i ∈ T)) = true :=
    hall _ (List.mem_map_of_mem hd)
  have hg0 : 0 < g := by linarith
  have hg1 : 1 / g ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  rcases Nat.eq_zero_or_pos G.edges.length with hm | hm
  · have : IsEmpty (Fin G.edges.length) := by rw [hm]; infer_instance
    rw [ConstraintGraph.unsatVal_of_isEmpty (G.toGraph projectionEval)] at hG
    linarith
  -- The weight bound.
  have hth : (minRep eβ eγ G).threshold = 2 * G.edges.length := by
    simp only [minRep]
    omega
  have hweight : ((minRep eβ eγ G).weight T : ℝ) ≤ g * (2 * G.edges.length) := by
    rw [hth] at hT
    exact_mod_cast hT
  have hcard := sum_card_labels_le eβ eγ G T
  -- The selected labels at every end of an edge.
  have hA : ∀ u : (srcs G).toFinset, (labels T (srcs G) 0 nβ u).Nonempty := by
    rintro ⟨u, hu⟩
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hu)
    obtain ⟨a, ha, -⟩ := exists_mem_labels eβ eγ (hsat d hd)
    exact ⟨a, ha⟩
  have hB : ∀ v : (dsts G).toFinset,
      (labels T (dsts G) ((srcs G).length * nβ) nγ v).Nonempty := by
    rintro ⟨v, hv⟩
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hv)
    obtain ⟨a, -, hb⟩ := exists_mem_labels eβ eγ (hsat d hd)
    exact ⟨_, hb⟩
  let s : Fin G.edges.length → (srcs G).toFinset := fun i =>
    ⟨(G.edges.get i).src, List.mem_toFinset.2 (mem_srcs (List.get_mem _ _))⟩
  let t : Fin G.edges.length → (dsts G).toFinset := fun i =>
    ⟨(G.edges.get i).dst, List.mem_toFinset.2 (mem_dsts (List.get_mem _ _))⟩
  obtain ⟨f, h, hfh⟩ := exists_labelling_ge s t
    (fun u => labels T (srcs G) 0 nβ u)
    (fun v => labels T (dsts G) ((srcs G).length * nβ) nγ v) hA hB
    (fun i a b => eγ ((G.edges.get i).constraint (eβ.symm a)) = b)
    fun i => by
      obtain ⟨a, ha, hb⟩ := exists_mem_labels eβ eγ (hsat _ (List.get_mem G.edges i))
      exact ⟨a, ha, _, hb, rfl⟩
  -- The labelling `f`, `h` satisfies the edges it is counted on.
  let σ : ℕ → β × γ := fun x =>
    (if hx : x ∈ (srcs G).toFinset then eβ.symm (f ⟨x, hx⟩) else Classical.arbitrary β,
      if hx : x ∈ (dsts G).toFinset then eγ.symm (h ⟨x, hx⟩) else
        (G.edges.get ⟨0, hm⟩).constraint (Classical.arbitrary β))
  have hσ (i : Fin G.edges.length)
      (hi : eγ ((G.edges.get i).constraint (eβ.symm (f (s i)))) = h (t i)) :
      (G.toGraph projectionEval).Satisfies σ i := by
    rw [satisfies_toGraph_projectionEval_iff]
    simp only [σ]
    rw [dite_eq_left_of_eq_true (eq_true (s i).2), dite_eq_left_of_eq_true (eq_true (t i).2)]
    exact (Equiv.eq_symm_apply eγ).2 hi
  have hdisj : Disjoint (Finset.univ.filter fun i : Fin G.edges.length =>
      eγ ((G.edges.get i).constraint (eβ.symm (f (s i)))) = h (t i))
        ((G.toGraph projectionEval).unsatEdges σ) := by
    refine Finset.disjoint_left.2 fun i hi hu => ?_
    exact ConstraintGraph.mem_unsatEdges.1 hu (hσ i (Finset.mem_filter.1 hi).2)
  have hcount := Finset.card_le_univ (Finset.disjUnion _ _ hdisj)
  rw [Finset.card_disjUnion, Fintype.card_fin] at hcount
  have hfrac := (G.toGraph projectionEval).card_mul_unsatFrac σ
  rw [Fintype.card_fin] at hfrac
  have hval := (G.toGraph projectionEval).unsatVal_le σ
  -- Jensen.
  have hjensen := card_div_le_sum_one_div (ι := Fin G.edges.length)
    (a := fun i => (#(labels T (srcs G) 0 nβ (G.edges.get i).src) : ℝ))
    (b := fun i => (#(labels T (dsts G) ((srcs G).length * nβ) nγ (G.edges.get i).dst) : ℝ))
    (fun i => by exact_mod_cast (hA (s i)).card_pos)
    (fun i => by exact_mod_cast (hB (t i)).card_pos) hg0 (by
      rw [Fintype.card_fin]
      calc ∑ i : Fin G.edges.length,
            ((#(labels T (srcs G) 0 nβ (G.edges.get i).src) : ℝ) +
              #(labels T (dsts G) ((srcs G).length * nβ) nγ (G.edges.get i).dst))
          ≤ ((minRep eβ eγ G).weight T : ℝ) := by exact_mod_cast hcard
        _ ≤ g * (2 * G.edges.length) := hweight)
  rw [Fintype.card_fin] at hjensen
  have hm' : (0 : ℝ) < G.edges.length := by exact_mod_cast hm
  have hcount' : (#(Finset.univ.filter fun i : Fin G.edges.length =>
      eγ ((G.edges.get i).constraint (eβ.symm (f (s i)))) = h (t i)) : ℝ) +
        #((G.toGraph projectionEval).unsatEdges σ) ≤ G.edges.length := by
    exact_mod_cast hcount
  have hmul : (G.edges.length : ℝ) * (1 - (G.toGraph projectionEval).unsatFrac σ) ≤
      G.edges.length * δ :=
    mul_le_mul_of_nonneg_left (by linarith) hm'.le
  have hδm : (G.edges.length : ℝ) * δ < G.edges.length / g ^ 2 := by
    rw [div_eq_mul_one_div]
    exact mul_lt_mul_of_pos_left hδ hm'
  nlinarith

/-! ### Running time -/

section Runtime

variable {Input : Type} {input : Input ↪ List Bool}

private theorem isPolyTime_blockWeights {L : Input → List ℕ} {n : ℕ}
    (hL : ComputableInPolyTime L input (encList encUnary)) :
    ComputableInPolyTime (fun x => blockWeights (L x) n) input (encList encUnary) := by
  have hrange : ComputableInPolyTime (fun x => List.range ((L x).length * n)) input
      (encList encUnary) :=
    ComputableInPolyTime.range.comp (ComputableInPolyTime.unary_mul'
      ((ComputableInPolyTime.length_list encUnary).comp hL) (.const n))
  have hL₁ : ComputableInPolyTime (fun p : Input × ℕ => L p.1) (encPair input encUnary)
      (encList encUnary) := hL.comp (.fst _ _)
  have hk : ComputableInPolyTime (fun p : Input × ℕ => p.2) (encPair input encUnary)
      encUnary := .snd _ _
  have hget : ComputableInPolyTime (fun p : Input × ℕ => (L p.1).getD (p.2 / n) 0)
      (encPair input encUnary) encUnary :=
    ComputableInPolyTime.listGetDWithInput hL₁ (ComputableInPolyTime.unary_div' hk (.const n)) 0
  have htest : ComputableInPolyTime
      (fun q : (Input × ℕ) × ℕ => q.2 == (L q.1.1).getD (q.1.2 / n) 0)
      (encPair (encPair input encUnary) encUnary) encBool :=
    ComputableInPolyTime.unary_beq' (.snd _ _) (hget.comp (.fst _ _))
  have hcount : ComputableInPolyTime (fun p : Input × ℕ => (L p.1).count ((L p.1).getD (p.2 / n) 0))
      (encPair input encUnary) encUnary :=
    ComputableInPolyTime.countPWithInput hL₁ htest
  exact ComputableInPolyTime.mapWithInput hrange hcount

variable [Finite β] [Finite γ] {encC : (β → γ) ↪ List Bool}

private theorem isPolyTime_formula {G : Input → Graph (β → γ)} {d : Input → Edge (β → γ)}
    (hG : ComputableInPolyTime G input (Graph.encoding encC))
    (hd : ComputableInPolyTime d input (Edge.encoding encC)) :
    ComputableInPolyTime (fun x => formula eβ eγ (G x) (d x)) input
      (encDNFOver encNat) := by
  have hedges := Graph.isPolyTime_edges hG
  have hsrcs : ComputableInPolyTime (fun x => srcs (G x)) input (encList encUnary) := by
    unfold srcs
    exact ComputableInPolyTime.mapWithInput (f := fun _ (e : Edge (β → γ)) => e.src) hedges
      (Edge.isPolyTime_src (.snd _ _))
  have hdsts : ComputableInPolyTime (fun x => dsts (G x)) input (encList encUnary) := by
    unfold dsts
    exact ComputableInPolyTime.mapWithInput (f := fun _ (e : Edge (β → γ)) => e.dst) hedges
      (Edge.isPolyTime_dst (.snd _ _))
  have hoff : ComputableInPolyTime (fun x => (srcs (G x)).length * nβ) input encUnary :=
    ComputableInPolyTime.unary_mul' ((ComputableInPolyTime.length_list encUnary).comp hsrcs)
      (.const nβ)
  have hconstraint := Edge.isPolyTime_constraint hd
  have hlit {v : Input → ℕ} (hv : ComputableInPolyTime v input encUnary) :
      ComputableInPolyTime (fun x => ((v x, true) : Literal ℕ)) input (encPair encNat encBool) :=
    (ComputableInPolyTime.unary_to_binary.comp hv).prod (.const true)
  unfold formula
  refine ComputableInPolyTime.mapConst _ fun a _ => ?_
  have hleft : ComputableInPolyTime (fun x => blockVar (srcs (G x)) 0 nβ (d x).src a) input
      encUnary :=
    ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_add' (.const 0)
      (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.idxOfWithInput hsrcs
        (Edge.isPolyTime_src hd)) (.const nβ))) (.const (a : ℕ))
  have hlabel : ComputableInPolyTime (fun x => ((eγ ((d x).constraint (eβ.symm a)) : ℕ)))
      input encUnary :=
    (ComputableInPolyTime.of_finite (fun π : β → γ => ((eγ (π (eβ.symm a)) : ℕ)))).comp
      hconstraint
  have hright : ComputableInPolyTime (fun x => blockVar (dsts (G x)) ((srcs (G x)).length * nβ) nγ
      (d x).dst (eγ ((d x).constraint (eβ.symm a)))) input encUnary :=
    ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_add' hoff
      (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.idxOfWithInput hdsts
        (Edge.isPolyTime_dst hd)) (.const nγ))) hlabel
  exact (hlit hleft).cons' ((hlit hright).cons' (.const []))

/-- **The Min-Rep construction is polynomial-time** for fixed finite label sets. The unary vertex
numbers of the input bound the variable numbers, and the input's edge list bounds the unary
weights and threshold. -/
theorem isPolyTime_minRep :
    ComputableInPolyTime (minRep eβ eγ) (Graph.encoding encC) CMMSAInstance.encoding := by
  have hG : ComputableInPolyTime (fun G : Graph (β → γ) => G) (Graph.encoding encC)
      (Graph.encoding encC) := .id'
  have hedges := Graph.isPolyTime_edges hG
  have hsrcs : ComputableInPolyTime (fun G : Graph (β → γ) => srcs G) (Graph.encoding encC)
      (encList encUnary) := by
    unfold srcs
    exact ComputableInPolyTime.mapWithInput (f := fun _ (e : Edge (β → γ)) => e.src) hedges
      (Edge.isPolyTime_src (.snd _ _))
  have hdsts : ComputableInPolyTime (fun G : Graph (β → γ) => dsts G) (Graph.encoding encC)
      (encList encUnary) := by
    unfold dsts
    exact ComputableInPolyTime.mapWithInput (f := fun _ (e : Edge (β → γ)) => e.dst) hedges
      (Edge.isPolyTime_dst (.snd _ _))
  have hlen : ComputableInPolyTime (fun G : Graph (β → γ) => G.edges.length) (Graph.encoding encC)
      encUnary := (ComputableInPolyTime.length_list _).comp hedges
  have hweights : ComputableInPolyTime
      (fun G : Graph (β → γ) => blockWeights (srcs G) nβ ++ blockWeights (dsts G) nγ)
      (Graph.encoding encC) (encList encUnary) :=
    ComputableInPolyTime.listAppend' (isPolyTime_blockWeights hsrcs)
      (isPolyTime_blockWeights hdsts)
  have hthreshold : ComputableInPolyTime (fun G : Graph (β → γ) => max (2 * G.edges.length) 1)
      (Graph.encoding encC) encUnary :=
    (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.unary_max).comp
      ((ComputableInPolyTime.unary_mul' (.const 2) hlen).prod (.const 1))
  have hformulas : ComputableInPolyTime (fun G : Graph (β → γ) => G.edges.map (formula eβ eγ G))
      (Graph.encoding encC) (encList (encDNFOver encNat)) :=
    ComputableInPolyTime.mapWithInput hedges
      (isPolyTime_formula eβ eγ (hG.comp (.fst _ _)) (.snd _ _))
  exact CMMSAInstance.isPolyTime_mk hweights hthreshold hformulas

end Runtime

end Cslib.PCP.Encoded.LabelCoverMinRep

namespace Cslib.Complexity

open Cslib.PCP Cslib.PCP.Encoded Turing.MultiTapeTM

/-- **Weighted Min-Rep reduction**, a library reduction adapting the Min-Rep problem
[Kortsarz2001]: perfect-completeness Label Cover of soundness
`δ < 1 / g²` reduces to CMMSA with at most `2 |β|` literals per formula, gap `g` and proportion
`1`. -/
theorem polyTimeReducible_GapLabelCover_GapCMMSA {β γ : Type} [Fintype β] [Finite γ]
    [Nonempty β] [Nonempty γ] [DecidableEq γ] (encC : (β → γ) ↪ List Bool) {g δ : ℝ}
    (hg : 1 ≤ g) (hδ : δ < 1 / g ^ 2) :
    PromiseProblem.PolyTimeReducible (Graph.encoding encC) CMMSAInstance.encoding
      (GapLabelCover β γ 1 δ) (GapCMMSA (2 * Fintype.card β) g 1) := by
  let eβ := Fintype.equivFin β
  let eγ := Finite.equivFin γ
  refine ⟨LabelCoverMinRep.minRep eβ eγ, LabelCoverMinRep.isPolyTime_minRep eβ eγ, ?_, ?_⟩
  · intro G hG
    rw [GapLabelCover, PromiseProblem.mem_yes_gapMax] at hG
    have h0 : (G.toGraph projectionEval).unsatVal = 0 :=
      le_antisymm (by linarith) (ConstraintGraph.unsatVal_nonneg _)
    exact LabelCoverMinRep.minRep_mem_yes eβ eγ
      ((ConstraintGraph.unsatVal_eq_zero_iff _).1 h0) le_rfl
  · intro G hG
    rw [GapLabelCover, PromiseProblem.mem_no_gapMax] at hG
    exact LabelCoverMinRep.minRep_mem_no eβ eγ le_rfl hg hδ hG.1

/-- **CMMSA is NP-hard for every constant gap**: for every `g ≥ 1` there is a bound `Δ` on the
literals of each formula for which `GapCMMSA Δ g 1` is NP-hard, by weighted Min-Rep from
small-soundness Label Cover (`exists_GapLabelCover_npHard`). -/
theorem exists_GapCMMSA_npHard {g : ℝ} (hg : 1 ≤ g) :
    ∃ Δ : ℕ, PromiseProblem.NPHard CMMSAInstance.encoding (GapCMMSA Δ g 1) := by
  have hg2 : 1 ≤ g ^ 2 := one_le_pow₀ hg
  obtain ⟨k, -, hk⟩ := exists_GapLabelCover_npHard (δ := 1 / (2 * g ^ 2)) (by positivity)
    (by rw [div_lt_one (by positivity)]; linarith)
  exact ⟨_, hk.trans (polyTimeReducible_GapLabelCover_GapCMMSA _ hg
    (by rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith))⟩

end Cslib.Complexity
