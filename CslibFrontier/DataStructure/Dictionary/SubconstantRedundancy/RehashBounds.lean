/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.StorageNode

/-!
# Expected Subtree Rehashing Bounds for the Multi-Level Dictionary Tree

This file formalizes the single-node look-ahead survival bound (`Claim 5.4`, PDF p. 35 / printed
p. 34) and the multi-level expected rehashing bound (`Lemma 5.3`, PDF pp. 34–35 / printed
pp. 33–34) of Tianxiao Li, Jingxun Liang, Huacheng Yu, and Renfei Zhou, *Dynamic Dictionary with
Subconstant Wasted Bits per Key* ([LiLiangYuZhou2024, Section 5.5];
[arXiv:2310.20536v1](https://arxiv.org/abs/2310.20536v1)).

## Proof structure and adaptations

1. **Single-window seed survival (`Claim 5.4`):** For any level `0 ≤ ℓ ≤ depth`, window length
   `rehashWindow ℓ = ⌈(nFloor ℓ) ^ 2 / 10⌉`, and valid oblivious primitive-ID trajectory `S_0, …,
   S_k` (`k ≤ rehashWindow ℓ`, each `|S_i| ∈ [nLow ℓ, nHigh ℓ]`), union-bounding the unified
   single-set failure density `3 / (nFloor ℓ) ^ 2` (`TreeSchedule.dens_not_isGoodNodeSeed_le`,
   covering both `DoubleTabulation` and small-node `trinomialPolyHash` routers) proves that a
   uniform seed survives the entire window with probability `≥ 1 / 2`, both unconditionally
   (`dens_goodNodeSeed_survives_window_ge_half`, `prob_goodNodeSeed_survives_window_ge_half`) and
   conditioned on passing the initial rejection check on `S_0` (`Algorithm 4` Lines 2–5,
   `condProb_goodNodeSeed_survives_window_ge_half`).
2. **Online stopping-time subsequence bound:** Modeling the exact online first-failure stopping
   process `expectedSubseqSuccesses` over an arbitrary valid subsequence of `T` updates at node `u`,
   strong induction on `T` proves the uniform linear bound
   `expectedSubseqSuccesses ≤ 1 + 20 * T / (nFloor ℓ) ^ 2` for all `T ≥ 0`
   (`expectedSubseqSuccesses_le`), while geometric rejection sampling at each `Rehash(u)` call takes
   at most `12 / 11 ≤ 2` expected seed trials (`expectedRejectionTrials_le_two`) without recursing
   to children on failed trials (`Algorithm 4` Lines 3–5).
3. **Multi-level telescoping (`Lemma 5.3` recurrence step):** Multiplying the level recurrence
   `a_{ℓ + 1} ≤ a_ℓ * B_ℓ + 20 * M / n_{ℓ + 1} ^ 2` by `n_{ℓ + 1}` and using `2 * n_{j + 1} ≤
   B_j * n_{j + 1} ≤ n_j` yields `O(n + M)` expected work per level and
   `≤ 42 * (n + M) * log* n` across `ValidRegime` given levelwise bounds `hbase` and `hstep`
   (`rehashWork_of_level_recurrence`, `canonicalSchedule_rehashWork_le_mul_logStar`). The online
   `OracleComp` execution model in `TreeExec.lean` instantiates `hbase` and `hstep` unconditionally
   across any admissible `Dynamic.spec` history (`expectedCost_execHistory_le`,
   `canonicalSchedule_expectedCost_execHistory_le`).

## Main definitions

* `TreeSchedule.rehashWindow`, `TreeSchedule.ValidPrimIdSeq`: look-ahead window `⌈n_ℓ ^ 2 / 10⌉` and
  valid primitive-ID trajectories.
* `TreeSchedule.expectedSubseqSuccesses`, `seqChanges`: exact expected successful rehashes of a node
  `u` across a valid oblivious subsequence of `T` steps and active-change count.
* `TreeSchedule.LevelSubseqBatch`: partition of `≤ M` oblivious updates across `K` maximal
  ancestor-rehash-free subsequences at level `ℓ`.

## Main results

* `TreeSchedule.dens_goodNodeSeed_survives_window_ge_half`,
  `TreeSchedule.prob_goodNodeSeed_survives_window_ge_half`,
  `TreeSchedule.condProb_goodNodeSeed_survives_window_ge_half`: `Claim 5.4` survival probability
  `≥ 1 / 2`.
* `TreeSchedule.expectedSubseqSuccesses_le`, `TreeSchedule.expectedSubseqSuccesses_le_of_changes`,
  `TreeSchedule.sum_expectedSubseqSuccesses_le`: `1 + 20 * T / n_ℓ ^ 2` and active-change bounds per
  maximal subsequence, and `K + 20 * M / n_ℓ ^ 2` summed over `K` subsequences.
* `TreeSchedule.rehashWork_of_level_recurrence`, `canonicalSchedule_rehashWork_le_mul_logStar`:
  multi-level recurrence-telescoping step of `Lemma 5.3` (completed end-to-end in `TreeExec.lean`).

## References

* [T. Li, J. Liang, H. Yu, and R. Zhou,
  *Dynamic Dictionary with Subconstant Wasted Bits per Key*][LiLiangYuZhou2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.SubconstantRedundancy

open Cslib.DataStructure.Dictionary
open Cslib.Probability
open Finset

namespace TreeSchedule

variable (P : TreeSchedule)

/-! ## Section 1: Single-node look-ahead survival (`Claim 5.4`) -/

/-- Look-ahead survival window `⌈(nFloor ℓ) ^ 2 / 10⌉` at level `ℓ`
([LiLiangYuZhou2024, Section 5.5, Claim 5.4];
[arXiv:2310.20536v1](https://arxiv.org/abs/2310.20536v1), PDF p. 35 / printed p. 34). -/
@[expose]
def rehashWindow (ℓ : ℕ) : ℕ :=
  ((P.nFloor ℓ) ^ 2 + 9) / 10

/-- Admissibility of a primitive-ID trajectory `seq : Fin (T + 1) → Finset (P.PrimId ℓ)` at node
`u` during a maximal subsequence where no ancestor of `u` is rehashed (`nLow ℓ ≤ #(seq i) ≤
nHigh ℓ`). -/
@[expose]
def ValidPrimIdSeq (ℓ T : ℕ) (seq : Fin (T + 1) → Finset (P.PrimId ℓ)) : Prop :=
  ∀ i : Fin (T + 1), P.nLow ℓ ≤ #(seq i) ∧ #(seq i) ≤ P.nHigh ℓ

/-- Suffix of a valid primitive-ID trajectory starting at step `s` (`s ≤ T`). -/
def suffixPrimIdSeq {ℓ T : ℕ} (seq : Fin (T + 1) → Finset (P.PrimId ℓ)) {s : ℕ} (hs : s ≤ T) :
    Fin ((T - s) + 1) → Finset (P.PrimId ℓ) :=
  fun j => seq ⟨s + j.val, by omega⟩

theorem validPrimIdSeq_suffix {ℓ T : ℕ} {seq : Fin (T + 1) → Finset (P.PrimId ℓ)}
    (hvalid : P.ValidPrimIdSeq ℓ T seq) {s : ℕ} (hs : s ≤ T) :
    P.ValidPrimIdSeq ℓ (T - s) (P.suffixPrimIdSeq seq hs) :=
  fun j => hvalid ⟨s + j.val, by omega⟩

open scoped Classical in
/-- Union bound on `NodeSeed ℓ` failing at any step `i ∈ Fin (k + 1)` of a valid trajectory. -/
theorem dens_exists_not_isGoodNodeSeed_le (hcr : P.ConcentrationReady) {ℓ k : ℕ}
    (hℓ : ℓ ≤ P.depth) {seq : Fin (k + 1) → Finset (P.PrimId ℓ)}
    (hvalid : P.ValidPrimIdSeq ℓ k seq) :
    (dens {g : P.NodeSeed ℓ | ∃ i : Fin (k + 1), ¬ P.IsGoodNodeSeed ℓ g (seq i)} : ℝ) ≤
      (3 * ((k + 1 : ℕ) : ℝ)) / (P.nFloor ℓ : ℝ) ^ 2 := by
  have hsub : (Finset.univ.filter fun g : P.NodeSeed ℓ =>
      ∃ i : Fin (k + 1), ¬ P.IsGoodNodeSeed ℓ g (seq i)) ⊆
      Finset.univ.biUnion fun i : Fin (k + 1) =>
        Finset.univ.filter fun g : P.NodeSeed ℓ => ¬ P.IsGoodNodeSeed ℓ g (seq i) := by
    intro g hg
    obtain ⟨i, hi⟩ := (mem_filter.mp hg).2
    exact mem_biUnion.mpr ⟨i, Finset.mem_univ i, mem_filter.mpr ⟨Finset.mem_univ g, hi⟩⟩
  have h1 : (dens {g : P.NodeSeed ℓ | ∃ i : Fin (k + 1), ¬ P.IsGoodNodeSeed ℓ g (seq i)} : ℝ) ≤
      ∑ i : Fin (k + 1),
        (dens {g : P.NodeSeed ℓ | ¬ P.IsGoodNodeSeed ℓ g (seq i)} : ℝ) :=
    (NNRat.cast_le.mpr ((dens_le_dens hsub).trans dens_biUnion_le)).trans_eq
      (map_sum (NNRat.castHom ℝ) _ _)
  refine h1.trans ((sum_le_sum fun i _ =>
    P.dens_not_isGoodNodeSeed_le hcr hℓ (seq i) (hvalid i).1 (hvalid i).2).trans_eq ?_)
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

open scoped Classical in
/-- **Unconditional single-node window survival (`Claim 5.4`, density form)**:
for `k ≤ rehashWindow ℓ`, at least `1 / 2` of all seeds in `P.NodeSeed ℓ` succeed across every set
`seq 0, …, seq k` ([LiLiangYuZhou2024, Section 5.5, Claim 5.4];
[arXiv:2310.20536v1](https://arxiv.org/abs/2310.20536v1), PDF p. 35 / printed p. 34). -/
theorem dens_goodNodeSeed_survives_window_ge_half (hcr : P.ConcentrationReady) {ℓ k : ℕ}
    (hℓ : ℓ ≤ P.depth) (hk : k ≤ P.rehashWindow ℓ)
    {seq : Fin (k + 1) → Finset (P.PrimId ℓ)} (hvalid : P.ValidPrimIdSeq ℓ k seq) :
    (1 : ℝ) / 2 ≤
      (dens {g : P.NodeSeed ℓ | ∀ i : Fin (k + 1), P.IsGoodNodeSeed ℓ g (seq i)} : ℝ) := by
  have hnF6 := hcr.six_le_nFloor ℓ hℓ
  have h36 : 36 ≤ (P.nFloor ℓ) ^ 2 := by nlinarith
  have hsq_pos : (0 : ℝ) < (P.nFloor ℓ : ℝ) ^ 2 := by positivity
  have hW : 6 * (k + 1) ≤ (P.nFloor ℓ) ^ 2 := by
    dsimp only [rehashWindow] at hk
    omega
  have hbad := P.dens_exists_not_isGoodNodeSeed_le hcr hℓ hvalid
  have hbad_half : (dens {g : P.NodeSeed ℓ |
      ∃ i : Fin (k + 1), ¬ P.IsGoodNodeSeed ℓ g (seq i)} : ℝ) ≤ (1 : ℝ) / 2 := by
    refine hbad.trans ?_
    rw [div_le_div_iff₀ hsq_pos (by positivity)]
    have hnat : 3 * (k + 1) * 2 ≤ 1 * (P.nFloor ℓ) ^ 2 := by omega
    exact_mod_cast hnat
  have hpart := card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (P.NodeSeed ℓ)))
    (p := fun g : P.NodeSeed ℓ => ∀ i : Fin (k + 1), P.IsGoodNodeSeed ℓ g (seq i))
  have hnot_eq : (Finset.univ.filter fun g : P.NodeSeed ℓ =>
      ¬ ∀ i : Fin (k + 1), P.IsGoodNodeSeed ℓ g (seq i)) =
      Finset.univ.filter fun g : P.NodeSeed ℓ =>
        ∃ i : Fin (k + 1), ¬ P.IsGoodNodeSeed ℓ g (seq i) := by
    ext g
    simp only [mem_filter, Finset.mem_univ, true_and, not_forall]
  rw [hnot_eq, card_univ] at hpart
  have hsum_dens : (dens {g : P.NodeSeed ℓ |
      ∀ i : Fin (k + 1), P.IsGoodNodeSeed ℓ g (seq i)} : ℝ) +
      (dens {g : P.NodeSeed ℓ |
        ∃ i : Fin (k + 1), ¬ P.IsGoodNodeSeed ℓ g (seq i)} : ℝ) = 1 := by
    have hC_pos : (0 : ℝ) < Fintype.card (P.NodeSeed ℓ) := Nat.cast_pos.mpr Fintype.card_pos
    rw [dens_eq_card_div_card, dens_eq_card_div_card, NNRat.cast_div, NNRat.cast_div,
      NNRat.cast_natCast, NNRat.cast_natCast, NNRat.cast_natCast, ← add_div]
    have hpr : (#(Finset.univ.filter fun g : P.NodeSeed ℓ =>
        ∀ i : Fin (k + 1), P.IsGoodNodeSeed ℓ g (seq i)) : ℝ) +
        (#(Finset.univ.filter fun g : P.NodeSeed ℓ =>
          ∃ i : Fin (k + 1), ¬ P.IsGoodNodeSeed ℓ g (seq i)) : ℝ) =
        Fintype.card (P.NodeSeed ℓ) := by exact_mod_cast hpart
    rw [hpr, div_self hC_pos.ne']
  linarith

/-- **`PMF.uniformOfFintype` probability form of `Claim 5.4`**. -/
theorem prob_goodNodeSeed_survives_window_ge_half (hcr : P.ConcentrationReady) {ℓ k : ℕ}
    (hℓ : ℓ ≤ P.depth) (hk : k ≤ P.rehashWindow ℓ)
    {seq : Fin (k + 1) → Finset (P.PrimId ℓ)} (hvalid : P.ValidPrimIdSeq ℓ k seq) :
    (1 : ℝ) / 2 ≤ ((PMF.uniformOfFintype (P.NodeSeed ℓ)).toOuterMeasure
      {g : P.NodeSeed ℓ | ∀ i : Fin (k + 1), P.IsGoodNodeSeed ℓ g (seq i)}).toReal := by
  classical
  rw [PMF.toOuterMeasure_uniformOfFintype_toReal]
  simpa only [Set.mem_ofPred_eq, dens_eq_card_div_card, NNRat.cast_div, NNRat.cast_natCast] using
    P.dens_goodNodeSeed_survives_window_ge_half hcr hℓ hk hvalid

open scoped Classical in
/-- Exact integer cardinality bound on good seeds in `seq 0` that fail within the next `m` steps:
`((nFloor ℓ) ^ 2 - 3) * #B_m ≤ 3 * m * #G₀`. -/
theorem card_goodNodeSeed_fails_after_le (hcr : P.ConcentrationReady) {ℓ T m : ℕ}
    (hℓ : ℓ ≤ P.depth) (hm : m ≤ T)
    {seq : Fin (T + 1) → Finset (P.PrimId ℓ)} (hvalid : P.ValidPrimIdSeq ℓ T seq) :
    let G₀ := Finset.univ.filter fun g : P.NodeSeed ℓ => P.IsGoodNodeSeed ℓ g (seq 0)
    let B := G₀.filter fun g =>
      ∃ j : Fin m, ¬ P.IsGoodNodeSeed ℓ g (seq ⟨j.val + 1, by omega⟩)
    ((P.nFloor ℓ) ^ 2 - 3) * #B ≤ 3 * m * #G₀ := by
  intro G₀ B
  set N := (P.nFloor ℓ) ^ 2
  have hnF6 := hcr.six_le_nFloor ℓ hℓ
  have hN_pos : 0 < N := by dsimp only [N]; positivity
  have hC_pos : 0 < Fintype.card (P.NodeSeed ℓ) := Fintype.card_pos
  have hG₀_ge := P.card_isGoodNodeSeed_ge hcr hℓ (seq 0) (hvalid 0).1 (hvalid 0).2
  have hB_sub : B ⊆ Finset.univ.biUnion fun j : Fin m =>
      Finset.univ.filter fun g : P.NodeSeed ℓ =>
        ¬ P.IsGoodNodeSeed ℓ g (seq ⟨j.val + 1, by omega⟩) := by
    intro g hg
    obtain ⟨_, j, hj⟩ := mem_filter.mp hg
    exact mem_biUnion.mpr ⟨j, Finset.mem_univ j, mem_filter.mpr ⟨Finset.mem_univ g, hj⟩⟩
  have hstep_card : ∀ j : Fin m,
      N * #(Finset.univ.filter fun g : P.NodeSeed ℓ =>
        ¬ P.IsGoodNodeSeed ℓ g (seq ⟨j.val + 1, by omega⟩)) ≤
        3 * Fintype.card (P.NodeSeed ℓ) := by
    intro j
    have hj_valid := hvalid ⟨j.val + 1, by omega⟩
    have hd := P.dens_not_isGoodNodeSeed_le hcr hℓ _ hj_valid.1 hj_valid.2
    rw [dens_eq_card_div_card, NNRat.cast_div, NNRat.cast_natCast, NNRat.cast_natCast,
      div_le_div_iff₀ (Nat.cast_pos.mpr hC_pos) (by dsimp only [N] at hN_pos; positivity)] at hd
    have hd_nat : #(Finset.univ.filter fun g : P.NodeSeed ℓ =>
        ¬ P.IsGoodNodeSeed ℓ g (seq ⟨j.val + 1, by omega⟩)) * N ≤
        3 * Fintype.card (P.NodeSeed ℓ) := by exact_mod_cast hd
    rwa [Nat.mul_comm]
  have hNB : N * #B ≤ 3 * m * Fintype.card (P.NodeSeed ℓ) := by
    calc N * #B
        ≤ N * ∑ j : Fin m, #(Finset.univ.filter fun g : P.NodeSeed ℓ =>
            ¬ P.IsGoodNodeSeed ℓ g (seq ⟨j.val + 1, by omega⟩)) :=
          Nat.mul_le_mul_left N ((card_le_card hB_sub).trans card_biUnion_le)
      _ = ∑ j : Fin m, N * #(Finset.univ.filter fun g : P.NodeSeed ℓ =>
            ¬ P.IsGoodNodeSeed ℓ g (seq ⟨j.val + 1, by omega⟩)) := Finset.mul_sum ..
      _ ≤ ∑ _j : Fin m, 3 * Fintype.card (P.NodeSeed ℓ) := sum_le_sum fun j _ => hstep_card j
      _ = 3 * m * Fintype.card (P.NodeSeed ℓ) := by
          rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]; ring
  have hmul : (N * Fintype.card (P.NodeSeed ℓ)) * ((N - 3) * #B) ≤
      (N * Fintype.card (P.NodeSeed ℓ)) * (3 * m * #G₀) := by
    calc (N * Fintype.card (P.NodeSeed ℓ)) * ((N - 3) * #B)
        = (N - 3) * Fintype.card (P.NodeSeed ℓ) * (N * #B) := by ring
      _ ≤ (N * #G₀) * (3 * m * Fintype.card (P.NodeSeed ℓ)) := Nat.mul_le_mul hG₀_ge hNB
      _ = (N * Fintype.card (P.NodeSeed ℓ)) * (3 * m * #G₀) := by ring
  exact Nat.le_of_mul_le_mul_left hmul (Nat.mul_pos hN_pos hC_pos)

open scoped Classical in
/-- **Conditional single-node window survival (`Claim 5.4` for rejection-sampled `g_u`)**:
conditioned on `IsGoodNodeSeed ℓ g (seq 0)` (`Algorithm 4` Lines 2–5), a resampled seed `g`
survives all `k ≤ rehashWindow ℓ` subsequent updates with probability `≥ 1 / 2`. -/
theorem condProb_goodNodeSeed_survives_window_ge_half (hcr : P.ConcentrationReady) {ℓ k : ℕ}
    (hℓ : ℓ ≤ P.depth) (hk : k ≤ P.rehashWindow ℓ)
    {seq : Fin (k + 1) → Finset (P.PrimId ℓ)} (hvalid : P.ValidPrimIdSeq ℓ k seq) :
    let G₀ := Finset.univ.filter fun g : P.NodeSeed ℓ => P.IsGoodNodeSeed ℓ g (seq 0)
    let G_all := G₀.filter fun g => ∀ i : Fin (k + 1), P.IsGoodNodeSeed ℓ g (seq i)
    (1 : ℝ) / 2 ≤ (#G_all : ℝ) / (#G₀ : ℝ) := by
  intro G₀ G_all
  have hnF6 := hcr.six_le_nFloor ℓ hℓ
  have h36 : 36 ≤ (P.nFloor ℓ) ^ 2 := by nlinarith
  obtain ⟨g₀, hg₀⟩ := P.exists_isGoodNodeSeed hcr hℓ (seq 0) (hvalid 0).1 (hvalid 0).2
  have hG₀_pos : 0 < #G₀ := card_pos.mpr ⟨g₀, mem_filter.mpr ⟨Finset.mem_univ g₀, hg₀⟩⟩
  let B := G₀.filter fun g => ∃ j : Fin k, ¬ P.IsGoodNodeSeed ℓ g (seq ⟨j.val + 1, by omega⟩)
  have hNB := P.card_goodNodeSeed_fails_after_le hcr hℓ le_rfl hvalid
  have h6k : 6 * k ≤ (P.nFloor ℓ) ^ 2 - 3 := by
    dsimp only [rehashWindow] at hk
    omega
  have h2B : 2 * #B ≤ #G₀ := by
    have hpos : 0 < (P.nFloor ℓ) ^ 2 - 3 := by omega
    have hmul : ((P.nFloor ℓ) ^ 2 - 3) * (2 * #B) ≤ ((P.nFloor ℓ) ^ 2 - 3) * #G₀ := by
      calc ((P.nFloor ℓ) ^ 2 - 3) * (2 * #B)
          = 2 * (((P.nFloor ℓ) ^ 2 - 3) * #B) := by ring
        _ ≤ 2 * (3 * k * #G₀) := Nat.mul_le_mul_left 2 hNB
        _ = (6 * k) * #G₀ := by ring
        _ ≤ ((P.nFloor ℓ) ^ 2 - 3) * #G₀ := Nat.mul_le_mul_right #G₀ h6k
    exact Nat.le_of_mul_le_mul_left hmul hpos
  have hpart : #G_all + #(G₀.filter fun g =>
      ¬ ∀ i : Fin (k + 1), P.IsGoodNodeSeed ℓ g (seq i)) = #G₀ :=
    card_filter_add_card_filter_not _
  have hB_eq : (G₀.filter fun g => ¬ ∀ i : Fin (k + 1), P.IsGoodNodeSeed ℓ g (seq i)) = B := by
    ext g
    simp only [G₀, B, mem_filter, Finset.mem_univ, true_and, not_forall]
    refine and_congr_right fun hg0 => ⟨?_, ?_⟩
    · rintro ⟨⟨i, hi_lt⟩, hi⟩
      cases i with
      | zero => exact False.elim (hi hg0)
      | succ j => exact ⟨⟨j, Nat.lt_of_succ_lt_succ hi_lt⟩, hi⟩
    · rintro ⟨j, hj⟩
      exact ⟨⟨j.val + 1, by omega⟩, hj⟩
  rw [hB_eq] at hpart
  rw [le_div_iff₀ (Nat.cast_pos.mpr hG₀_pos)]
  have hgoal_nat : #G₀ ≤ 2 * #G_all := by omega
  have hgoal_real : (#G₀ : ℝ) ≤ 2 * (#G_all : ℝ) := by exact_mod_cast hgoal_nat
  linarith

/-! ## Section 2: Online stopping-time subsequence bound and multi-level `Lemma 5.3` -/

open scoped Classical in
/-- Expected geometric rejection-sampling trials `(Fintype.card (NodeSeed ℓ) : ℝ) / #G₀` per
`Rehash(u)` invocation is at most `2` (`≤ 12 / 11`). -/
theorem expectedRejectionTrials_le_two (hcr : P.ConcentrationReady) {ℓ : ℕ} (hℓ : ℓ ≤ P.depth)
    (S : Finset (P.PrimId ℓ)) (hlo : P.nLow ℓ ≤ #S) (hhi : #S ≤ P.nHigh ℓ) :
    let G₀ := Finset.univ.filter fun g : P.NodeSeed ℓ => P.IsGoodNodeSeed ℓ g S
    (Fintype.card (P.NodeSeed ℓ) : ℝ) / (#G₀ : ℝ) ≤ 2 := by
  intro G₀
  have hnF6 := hcr.six_le_nFloor ℓ hℓ
  have h36 : 36 ≤ (P.nFloor ℓ) ^ 2 := by nlinarith
  obtain ⟨g₀, hg₀⟩ := P.exists_isGoodNodeSeed hcr hℓ S hlo hhi
  have hG₀_pos : 0 < #G₀ := card_pos.mpr ⟨g₀, mem_filter.mpr ⟨Finset.mem_univ g₀, hg₀⟩⟩
  have hge := P.card_isGoodNodeSeed_ge hcr hℓ S hlo hhi
  have hnat : Fintype.card (P.NodeSeed ℓ) ≤ 2 * #G₀ := by
    have h1 : (P.nFloor ℓ) ^ 2 * Fintype.card (P.NodeSeed ℓ) ≤
        2 * (((P.nFloor ℓ) ^ 2 - 3) * Fintype.card (P.NodeSeed ℓ)) := by
      have hcoeff : (P.nFloor ℓ) ^ 2 ≤ 2 * ((P.nFloor ℓ) ^ 2 - 3) := by omega
      calc (P.nFloor ℓ) ^ 2 * Fintype.card (P.NodeSeed ℓ)
          ≤ (2 * ((P.nFloor ℓ) ^ 2 - 3)) * Fintype.card (P.NodeSeed ℓ) :=
            Nat.mul_le_mul_right _ hcoeff
        _ = 2 * (((P.nFloor ℓ) ^ 2 - 3) * Fintype.card (P.NodeSeed ℓ)) := by ring
    have h2 : (P.nFloor ℓ) ^ 2 * Fintype.card (P.NodeSeed ℓ) ≤
        (P.nFloor ℓ) ^ 2 * (2 * #G₀) := by
      calc (P.nFloor ℓ) ^ 2 * Fintype.card (P.NodeSeed ℓ)
          ≤ 2 * (((P.nFloor ℓ) ^ 2 - 3) * Fintype.card (P.NodeSeed ℓ)) := h1
        _ ≤ 2 * ((P.nFloor ℓ) ^ 2 * #G₀) := Nat.mul_le_mul_left 2 hge
        _ = (P.nFloor ℓ) ^ 2 * (2 * #G₀) := by ring
    exact Nat.le_of_mul_le_mul_left h2 (by positivity)
  rw [div_le_iff₀ (Nat.cast_pos.mpr hG₀_pos)]
  exact_mod_cast hnat

/-- Exact expected number of successful `Rehash(u)` completions across a maximal subsequence `seq`
of `T` updates at a level-`ℓ` node `u`, starting from the initial `Rehash(u)` on `seq 0` and
stopping/restarting at the first step `j₀ + 1 ∈ {1, …, T}` where the accepted seed fails. -/
noncomputable def expectedSubseqSuccesses (ℓ : ℕ) :
    ∀ (T : ℕ), (Fin (T + 1) → Finset (P.PrimId ℓ)) → ℝ
  | T, seq =>
    open scoped Classical in
    let G₀ := Finset.univ.filter fun g : P.NodeSeed ℓ => P.IsGoodNodeSeed ℓ g (seq 0)
    1 + (∑ g ∈ G₀,
      if hfail : ∃ j : ℕ, ∃ hj : j < T, ¬ P.IsGoodNodeSeed ℓ g (seq ⟨j + 1, by omega⟩) then
        have hj₀ : Nat.find hfail < T := (Nat.find_spec hfail).1
        have hdec : T - (Nat.find hfail + 1) < T := by omega
        expectedSubseqSuccesses ℓ (T - (Nat.find hfail + 1))
          (P.suffixPrimIdSeq seq (Nat.succ_le_of_lt hj₀))
      else 0) / (#G₀ : ℝ)
termination_by T _ => T
decreasing_by exact hdec

theorem expectedSubseqSuccesses_nonneg (ℓ : ℕ) :
    ∀ (T : ℕ) (seq : Fin (T + 1) → Finset (P.PrimId ℓ)),
      0 ≤ P.expectedSubseqSuccesses ℓ T seq := by
  classical
  intro T
  induction T using Nat.strong_induction_on with
  | ind T ih =>
    intro seq
    rw [expectedSubseqSuccesses]
    refine add_nonneg zero_le_one (div_nonneg (sum_nonneg fun g _ => ?_) (Nat.cast_nonneg _))
    split_ifs with hfail
    · exact ih _ (by have := (Nat.find_spec hfail).1; omega) _
    · exact le_rfl

/-- **Online subsequence expected-rehash bound (`Section 5.5` consequence of `Claim 5.4`)**:
across any valid subsequence `seq` of `T` updates at a level-`ℓ` node `u`, expected successful
rehashes satisfy `expectedSubseqSuccesses ℓ T seq ≤ 1 + 20 * T / (nFloor ℓ) ^ 2` for all `T ≥ 0`
([LiLiangYuZhou2024, Section 5.5]; [arXiv:2310.20536v1](https://arxiv.org/abs/2310.20536v1),
PDF p. 35 / printed p. 34). -/
theorem expectedSubseqSuccesses_le (hcr : P.ConcentrationReady) {ℓ : ℕ} (hℓ : ℓ ≤ P.depth) :
    ∀ (T : ℕ) (seq : Fin (T + 1) → Finset (P.PrimId ℓ)),
      P.ValidPrimIdSeq ℓ T seq →
      P.expectedSubseqSuccesses ℓ T seq ≤ 1 + 20 * (T : ℝ) / (P.nFloor ℓ : ℝ) ^ 2 := by
  classical
  set W := P.rehashWindow ℓ
  set N : ℝ := (P.nFloor ℓ : ℝ) ^ 2
  have hnF6 := hcr.six_le_nFloor ℓ hℓ
  have hN36_nat : 36 ≤ (P.nFloor ℓ) ^ 2 := by nlinarith
  have hN36 : (36 : ℝ) ≤ N := by dsimp only [N]; exact_mod_cast hN36_nat
  have hN_pos : 0 < N := by linarith
  have hW_lo_nat : (P.nFloor ℓ) ^ 2 ≤ 10 * W := by dsimp only [W, rehashWindow]; omega
  have hW_hi_nat : 10 * W ≤ (P.nFloor ℓ) ^ 2 + 9 := by dsimp only [W, rehashWindow]; omega
  have hW_lo : N ≤ 10 * (W : ℝ) := by dsimp only [N]; exact_mod_cast hW_lo_nat
  have hW_hi : 10 * (W : ℝ) ≤ N + 9 := by dsimp only [N]; exact_mod_cast hW_hi_nat
  intro T
  induction T using Nat.strong_induction_on with
  | ind T ih =>
    intro seq hvalid
    rw [expectedSubseqSuccesses]
    let G₀ := Finset.univ.filter fun g : P.NodeSeed ℓ => P.IsGoodNodeSeed ℓ g (seq 0)
    obtain ⟨g₀, hg₀⟩ := P.exists_isGoodNodeSeed hcr hℓ (seq 0) (hvalid 0).1 (hvalid 0).2
    have hG₀_pos : 0 < #G₀ := card_pos.mpr ⟨g₀, mem_filter.mpr ⟨Finset.mem_univ g₀, hg₀⟩⟩
    have hG₀_real : (0 : ℝ) < (#G₀ : ℝ) := Nat.cast_pos.mpr hG₀_pos
    let term : P.NodeSeed ℓ → ℝ := fun g =>
      if hfail : ∃ j : ℕ, ∃ hj : j < T, ¬ P.IsGoodNodeSeed ℓ g (seq ⟨j + 1, by omega⟩) then
        P.expectedSubseqSuccesses ℓ (T - (Nat.find hfail + 1))
          (P.suffixPrimIdSeq seq (Nat.succ_le_of_lt (Nat.find_spec hfail).1))
      else 0
    change 1 + (∑ g ∈ G₀, term g) / (#G₀ : ℝ) ≤ 1 + 20 * (T : ℝ) / N
    rcases Nat.eq_zero_or_pos T with rfl | hT_pos
    · have hzero : ∑ g ∈ G₀, term g = 0 := sum_eq_zero fun g _ => by
        dsimp only [term]
        rw [dite_eq_right]
        rintro ⟨j, hj, _⟩; omega
      rw [hzero, zero_div, add_zero, Nat.cast_zero, mul_zero, zero_div, add_zero]
    · by_cases hTW : T ≤ W
      · let B := G₀.filter fun g =>
          ∃ j : Fin T, ¬ P.IsGoodNodeSeed ℓ g (seq ⟨j.val + 1, by omega⟩)
        have hNB := P.card_goodNodeSeed_fails_after_le hcr hℓ le_rfl hvalid
        have h4B_nat : (P.nFloor ℓ) ^ 2 * #B ≤ 4 * T * #G₀ := by
          have h3N : 3 * (P.nFloor ℓ) ^ 2 ≤ 4 * ((P.nFloor ℓ) ^ 2 - 3) := by omega
          have hmul : 3 * ((P.nFloor ℓ) ^ 2 * #B) ≤ 3 * (4 * T * #G₀) := by
            calc 3 * ((P.nFloor ℓ) ^ 2 * #B)
                = (3 * (P.nFloor ℓ) ^ 2) * #B := by ring
              _ ≤ (4 * ((P.nFloor ℓ) ^ 2 - 3)) * #B := Nat.mul_le_mul_right #B h3N
              _ = 4 * (((P.nFloor ℓ) ^ 2 - 3) * #B) := by ring
              _ ≤ 4 * (3 * T * #G₀) := Nat.mul_le_mul_left 4 hNB
              _ = 3 * (4 * T * #G₀) := by ring
          exact Nat.le_of_mul_le_mul_left hmul (by decide)
        have h4B : N * (#B : ℝ) ≤ 4 * (T : ℝ) * (#G₀ : ℝ) := by
          dsimp only [N]; exact_mod_cast h4B_nat
        have hpt : ∀ g ∈ G₀, term g ≤ if g ∈ B then (4 : ℝ) else 0 := by
          intro g hg
          dsimp only [term]
          split_ifs with hfail hgB
          · have hj0_lt : Nat.find hfail < T := (Nat.find_spec hfail).1
            have hrem_lt : T - (Nat.find hfail + 1) < T := by omega
            have hih := ih _ hrem_lt _
              (P.validPrimIdSeq_suffix hvalid (Nat.succ_le_of_lt hj0_lt))
            have hrem_le : ((T - (Nat.find hfail + 1) : ℕ) : ℝ) ≤ (W : ℝ) := by
              exact_mod_cast (Nat.sub_le T _).trans hTW
            have h20W : 20 * ((T - (Nat.find hfail + 1) : ℕ) : ℝ) / N ≤ 3 := by
              rw [div_le_iff₀ hN_pos]
              linarith
            linarith
          · obtain ⟨j, hj, hbad_j⟩ := hfail
            exact False.elim (hgB (mem_filter.mpr ⟨hg, ⟨⟨j, hj⟩, hbad_j⟩⟩))
          · norm_num
          · exact le_rfl
        have hsum_le : ∑ g ∈ G₀, term g ≤ 4 * (#B : ℝ) := by
          calc ∑ g ∈ G₀, term g
              ≤ ∑ g ∈ G₀, if g ∈ B then (4 : ℝ) else 0 := sum_le_sum hpt
            _ = ∑ _g ∈ G₀.filter (· ∈ B), (4 : ℝ) := by rw [sum_ite, sum_const_zero, add_zero]
            _ = 4 * (#B : ℝ) := by
                have hfilt : G₀.filter (· ∈ B) = B := by
                  ext g
                  simp only [mem_filter, and_iff_right_iff_imp]
                  exact fun hg => (mem_filter.mp hg).1
                rw [hfilt, sum_const, nsmul_eq_mul]; ring
        have hdiv : (∑ g ∈ G₀, term g) / (#G₀ : ℝ) ≤ 20 * (T : ℝ) / N := by
          rw [div_le_div_iff₀ hG₀_real hN_pos]
          nlinarith
        linarith
      · have hW_lt_T : W + 1 ≤ T := by omega
        let B_W := G₀.filter fun g =>
          ∃ j : Fin W, ¬ P.IsGoodNodeSeed ℓ g (seq ⟨j.val + 1, by omega⟩)
        have hNB := P.card_goodNodeSeed_fails_after_le hcr hℓ (Nat.le_of_succ_le hW_lt_T) hvalid
        have h6W : 6 * W ≤ (P.nFloor ℓ) ^ 2 - 3 := by dsimp only [W, rehashWindow]; omega
        have h2BW_nat : 2 * #B_W ≤ #G₀ := by
          have hpos : 0 < (P.nFloor ℓ) ^ 2 - 3 := by omega
          have hmul : ((P.nFloor ℓ) ^ 2 - 3) * (2 * #B_W) ≤
              ((P.nFloor ℓ) ^ 2 - 3) * #G₀ := by
            calc ((P.nFloor ℓ) ^ 2 - 3) * (2 * #B_W)
                = 2 * (((P.nFloor ℓ) ^ 2 - 3) * #B_W) := by ring
              _ ≤ 2 * (3 * W * #G₀) := Nat.mul_le_mul_left 2 hNB
              _ = (6 * W) * #G₀ := by ring
              _ ≤ ((P.nFloor ℓ) ^ 2 - 3) * #G₀ := Nat.mul_le_mul_right #G₀ h6W
          exact Nat.le_of_mul_le_mul_left hmul hpos
        have h2BW : 2 * (#B_W : ℝ) ≤ (#G₀ : ℝ) := by exact_mod_cast h2BW_nat
        have hBW_le : (#B_W : ℝ) ≤ (#G₀ : ℝ) := by
          exact_mod_cast card_le_card (filter_subset _ G₀)
        set hi_val : ℝ := 1 + 20 * (T : ℝ) / N
        set lo_val : ℝ := 1 + 20 * ((T - (W + 1) : ℕ) : ℝ) / N
        have hlo_nonneg : 0 ≤ lo_val := by dsimp only [lo_val]; positivity
        have hpt : ∀ g ∈ G₀, term g ≤ if g ∈ B_W then hi_val else lo_val := by
          intro g hg
          dsimp only [term]
          split_ifs with hfail hgBW
          · have hj0_lt : Nat.find hfail < T := (Nat.find_spec hfail).1
            have hih := ih _ (by omega) _
              (P.validPrimIdSeq_suffix hvalid (Nat.succ_le_of_lt hj0_lt))
            have hrem_le : ((T - (Nat.find hfail + 1) : ℕ) : ℝ) ≤ (T : ℝ) := by
              exact_mod_cast Nat.sub_le T _
            have hmono : 20 * ((T - (Nat.find hfail + 1) : ℕ) : ℝ) / N ≤ 20 * (T : ℝ) / N :=
              div_le_div_of_nonneg_right (by linarith) hN_pos.le
            dsimp only [hi_val]; linarith
          · have hj0_lt : Nat.find hfail < T := (Nat.find_spec hfail).1
            have hj0_ge_W : W ≤ Nat.find hfail := by
              by_contra hlt
              have hbad_j0 := (Nat.find_spec hfail).2
              exact hgBW (mem_filter.mpr ⟨hg, ⟨⟨Nat.find hfail, not_le.mp hlt⟩, hbad_j0⟩⟩)
            have hih := ih _ (by omega) _
              (P.validPrimIdSeq_suffix hvalid (Nat.succ_le_of_lt hj0_lt))
            have hrem_le : ((T - (Nat.find hfail + 1) : ℕ) : ℝ) ≤ ((T - (W + 1) : ℕ) : ℝ) := by
              exact_mod_cast (by omega : T - (Nat.find hfail + 1) ≤ T - (W + 1))
            have hmono : 20 * ((T - (Nat.find hfail + 1) : ℕ) : ℝ) / N ≤
                20 * ((T - (W + 1) : ℕ) : ℝ) / N :=
              div_le_div_of_nonneg_right (by linarith) hN_pos.le
            dsimp only [lo_val]; linarith
          · dsimp only [hi_val]; positivity
          · exact hlo_nonneg
        have hsum_split : ∑ g ∈ G₀, (if g ∈ B_W then hi_val else lo_val) =
            (#B_W : ℝ) * hi_val + ((#G₀ : ℝ) - (#B_W : ℝ)) * lo_val := by
          have hpart := card_filter_add_card_filter_not (s := G₀) (p := (· ∈ B_W))
          have hfilt : G₀.filter (· ∈ B_W) = B_W := by
            ext g
            simp only [mem_filter, and_iff_right_iff_imp]
            exact fun hg => (mem_filter.mp hg).1
          rw [hfilt] at hpart
          rw [sum_ite, hfilt, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]
          have hpr : (#B_W : ℝ) + (#(G₀.filter fun x => x ∉ B_W) : ℝ) = (#G₀ : ℝ) := by
            exact_mod_cast hpart
          rw [← hpr]; ring
        have hsum_le : ∑ g ∈ G₀, term g ≤
            (#B_W : ℝ) * hi_val + ((#G₀ : ℝ) - (#B_W : ℝ)) * lo_val :=
          (sum_le_sum hpt).trans_eq hsum_split
        have hgap : hi_val - lo_val = 20 * ((W + 1 : ℕ) : ℝ) / N := by
          dsimp only [hi_val, lo_val]
          rw [Nat.cast_sub hW_lt_T]
          ring
        have hgap_ge2 : 2 ≤ hi_val - lo_val := by
          rw [hgap, le_div_iff₀ hN_pos, Nat.cast_add, Nat.cast_one]
          linarith
        rw [ ← sub_nonneg ]
        have hcalc : (1 + 20 * (T : ℝ) / N) - (1 + (∑ g ∈ G₀, term g) / (#G₀ : ℝ)) ≥
            ((( #G₀ : ℝ) - (#B_W : ℝ)) * (hi_val - lo_val) - (#G₀ : ℝ)) / (#G₀ : ℝ) := by
          have hd : hi_val - (1 + (∑ g ∈ G₀, term g) / (#G₀ : ℝ)) =
              ((#G₀ : ℝ) * (hi_val - 1) - ∑ g ∈ G₀, term g) / (#G₀ : ℝ) := by
            field_simp
            ring
          change 1 + 20 * (T : ℝ) / N - (1 + (∑ g ∈ G₀, term g) / (#G₀ : ℝ)) ≥ _
          have hhi_def : 1 + 20 * (T : ℝ) / N = hi_val := rfl
          rw [hhi_def, hd]
          refine div_le_div_of_nonneg_right ?_ hG₀_real.le
          nlinarith [hsum_le]
        have hnum_nonneg : 0 ≤ ((#G₀ : ℝ) - (#B_W : ℝ)) * (hi_val - lo_val) - (#G₀ : ℝ) := by
          have hhalf : (#G₀ : ℝ) ≤ 2 * ((#G₀ : ℝ) - (#B_W : ℝ)) := by linarith
          nlinarith [hgap_ge2, hBW_le]
        exact le_trans (div_nonneg hnum_nonneg hG₀_real.le) hcalc

/-- Congruence helper for `expectedSubseqSuccesses` across equal lengths `T₁ = T₂`. -/
private theorem expectedSubseqSuccesses_congr (ℓ : ℕ) {T₁ T₂ : ℕ} (hT : T₁ = T₂)
    {s₁ : Fin (T₁ + 1) → Finset (P.PrimId ℓ)} {s₂ : Fin (T₂ + 1) → Finset (P.PrimId ℓ)}
    (hs : ∀ (k : ℕ) (hk₁ : k < T₁ + 1) (hk₂ : k < T₂ + 1), s₁ ⟨k, hk₁⟩ = s₂ ⟨k, hk₂⟩) :
    P.expectedSubseqSuccesses ℓ T₁ s₁ = P.expectedSubseqSuccesses ℓ T₂ s₂ := by
  subst hT
  congr 1
  exact funext fun ⟨k, hk⟩ => hs k hk hk

/-- Number of active transitions `i : Fin T` where `seq i.succ ≠ seq i.castSucc`. -/
def seqChanges {α : Type*} [DecidableEq α] {T : ℕ} (seq : Fin (T + 1) → α) : ℕ :=
  #(Finset.univ.filter fun i : Fin T => seq i.succ ≠ seq i.castSucc)

/-- Number of active transitions in `(s₀, ss)` where consecutive sets differ. -/
@[expose]
def listChanges {α : Type*} [DecidableEq α] : α → List α → ℕ
  | _, [] => 0
  | s₀, s₁ :: ss => (if s₁ = s₀ then 0 else 1) + listChanges s₁ ss

private def dedupAdj {α : Type*} [DecidableEq α] : α → List α → List α
  | _, [] => []
  | s₀, s₁ :: ss => if s₁ = s₀ then dedupAdj s₁ ss else s₁ :: dedupAdj s₁ ss

private theorem length_dedupAdj {α : Type*} [DecidableEq α] :
    ∀ (s₀ : α) (ss : List α), (dedupAdj s₀ ss).length = listChanges s₀ ss
  | _, [] => rfl
  | s₀, s₁ :: ss => by
    dsimp only [dedupAdj, listChanges]
    by_cases h : s₁ = s₀
    · rw [ite_eq_left h, ite_eq_left h, Nat.zero_add, length_dedupAdj]
    · rw [ite_eq_right h, ite_eq_right h, List.length_cons, length_dedupAdj, Nat.add_comm]

private theorem mem_dedupAdj {α : Type*} [DecidableEq α] :
    ∀ {s₀ x : α} {ss : List α}, x ∈ dedupAdj s₀ ss → x ∈ ss
  | _, _, [], h => h
  | s₀, _, s₁ :: ss, h => by
    dsimp only [dedupAdj] at h
    by_cases he : s₁ = s₀
    · rw [ite_eq_left he] at h
      exact List.mem_cons_of_mem s₁ (mem_dedupAdj h)
    · rw [ite_eq_right he] at h
      rcases List.mem_cons.mp h with rfl | hm
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem s₁ (mem_dedupAdj hm)

private theorem listChanges_ofFn {α : Type*} [DecidableEq α] :
    ∀ {T : ℕ} (seq : Fin (T + 1) → α),
      listChanges (seq 0) (List.ofFn fun i : Fin T => seq i.succ) = seqChanges seq
  | 0, _ => by simp [listChanges, seqChanges]
  | m + 1, seq => by
    rw [List.ofFn_succ]
    dsimp only [listChanges, Fin.succ_zero_eq_one]
    have hih := listChanges_ofFn (fun i : Fin (m + 1) => seq i.succ)
    rw [Fin.succ_zero_eq_one] at hih
    rw [hih]
    dsimp only [seqChanges]
    have hsplit : #(Finset.univ.filter fun i : Fin (m + 1) => seq i.succ ≠ seq i.castSucc) =
        (if seq 1 = seq 0 then 0 else 1) +
          #(Finset.univ.filter fun j : Fin m => (seq j.succ.succ) ≠ (seq j.castSucc.succ)) := by
      have hsum : ∀ {k : ℕ} (p : Fin k → Prop), [DecidablePred p] →
          #(Finset.univ.filter p) = ∑ i : Fin k, if p i then 1 else 0 := by
        intro _ p _; simp [Finset.sum_boole]
      rw [hsum, Fin.sum_univ_succ]
      congr 1
      · by_cases h10 : seq 1 = seq 0
        · have hf : ¬ (seq (0 : Fin (m + 1)).succ ≠ seq (0 : Fin (m + 1)).castSucc) := by
            simpa using h10
          rw [ite_eq_left h10, ite_eq_right hf]
        · have ht : seq (0 : Fin (m + 1)).succ ≠ seq (0 : Fin (m + 1)).castSucc := by
            simpa using h10
          rw [ite_eq_right h10, ite_eq_left ht]
      · rw [hsum fun j : Fin m => seq j.succ.succ ≠ seq j.castSucc.succ]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Fin.castSucc_succ]
    rw [hsplit]

/-- Step-by-step online expected remaining rehashes starting from seed `g` across `seq 1, …, seq T`:
keeps `g` while `IsGoodNodeSeed` holds (`0` cost) and restarts `expectedSubseqSuccesses` at the
first failing step. -/
@[expose]
noncomputable def expectedRemRehashes (ℓ : ℕ) :
    ∀ (T : ℕ), (Fin (T + 1) → Finset (P.PrimId ℓ)) → P.NodeSeed ℓ → ℝ
  | 0, _, _ => 0
  | m + 1, seq, g =>
    open scoped Classical in
    let tail : Fin (m + 1) → Finset (P.PrimId ℓ) := fun i => seq i.succ
    if P.IsGoodNodeSeed ℓ g (seq 1) then
      expectedRemRehashes ℓ m tail g
    else
      P.expectedSubseqSuccesses ℓ m tail

open scoped Classical in
/-- `expectedSubseqSuccesses` equals `1` plus the uniform average over `G₀` of
`expectedRemRehashes`. -/
theorem expectedSubseqSuccesses_eq_one_add_avg_rem (ℓ : ℕ) :
    ∀ (T : ℕ) (seq : Fin (T + 1) → Finset (P.PrimId ℓ)),
      P.expectedSubseqSuccesses ℓ T seq =
        let G₀ := Finset.univ.filter fun g : P.NodeSeed ℓ => P.IsGoodNodeSeed ℓ g (seq 0)
        1 + (∑ g ∈ G₀, P.expectedRemRehashes ℓ T seq g) / (#G₀ : ℝ) := by
  have hrem_eq : ∀ (T : ℕ) (seq : Fin (T + 1) → Finset (P.PrimId ℓ)) (g : P.NodeSeed ℓ),
      P.expectedRemRehashes ℓ T seq g =
        if hfail : ∃ j : ℕ, ∃ hj : j < T, ¬ P.IsGoodNodeSeed ℓ g (seq ⟨j + 1, by omega⟩) then
          P.expectedSubseqSuccesses ℓ (T - (Nat.find hfail + 1))
            (P.suffixPrimIdSeq seq (Nat.succ_le_of_lt (Nat.find_spec hfail).1))
        else 0 := by
    intro T
    induction T with
    | zero =>
      intro seq g
      dsimp only [expectedRemRehashes]
      rw [dite_eq_right]
      rintro ⟨_, hj, _⟩; omega
    | succ m ih =>
      intro seq g
      let tail : Fin (m + 1) → Finset (P.PrimId ℓ) := fun i => seq i.succ
      dsimp only [expectedRemRehashes]
      by_cases hg1 : P.IsGoodNodeSeed ℓ g (seq 1)
      · rw [ite_eq_left hg1, ih tail g]
        have hiff : (∃ j : ℕ, ∃ hj : j < m, ¬ P.IsGoodNodeSeed ℓ g (tail ⟨j + 1, by omega⟩)) ↔
            (∃ j : ℕ, ∃ hj : j < m + 1, ¬ P.IsGoodNodeSeed ℓ g (seq ⟨j + 1, by omega⟩)) := by
          constructor
          · rintro ⟨j, hj, hb⟩
            exact ⟨j + 1, by omega, hb⟩
          · rintro ⟨j, hj, hb⟩
            rcases j with _ | j'
            · exact False.elim (hb hg1)
            · exact ⟨j', by omega, hb⟩
        by_cases hft : ∃ j : ℕ, ∃ hj : j < m, ¬ P.IsGoodNodeSeed ℓ g (tail ⟨j + 1, by omega⟩)
        · have hf := hiff.mp hft
          rw [dite_eq_left hft, dite_eq_left hf]
          have hft_lt : Nat.find hft < m := (Nat.find_spec hft).1
          have hf_lt : Nat.find hf < m + 1 := (Nat.find_spec hf).1
          have hfind : Nat.find hf = Nat.find hft + 1 := by
            refine le_antisymm (Nat.find_min' hf ⟨by omega, (Nat.find_spec hft).2⟩) ?_
            rcases hfn : Nat.find hf with _ | k
            · have hb0 := (Nat.find_spec hf).2
              simp only [hfn, Nat.zero_add] at hb0
              exact False.elim (hb0 hg1)
            · refine Nat.succ_le_succ (Nat.find_min' hft ?_)
              have hspec := (Nat.find_spec hf).2
              exact ⟨by omega, by simpa only [hfn, tail, Fin.succ] using hspec⟩
          refine P.expectedSubseqSuccesses_congr ℓ (by omega) fun k hk₁ hk₂ => ?_
          dsimp only [suffixPrimIdSeq, tail, Fin.succ]
          exact congrArg seq (Fin.ext (by dsimp only; omega))
        · have hf : ¬ ∃ j : ℕ, ∃ hj : j < m + 1,
              ¬ P.IsGoodNodeSeed ℓ g (seq ⟨j + 1, by omega⟩) := mt hiff.mpr hft
          rw [dite_eq_right hft, dite_eq_right hf]
      · rw [ite_eq_right hg1]
        have hf : ∃ j : ℕ, ∃ hj : j < m + 1,
            ¬ P.IsGoodNodeSeed ℓ g (seq ⟨j + 1, by omega⟩) := ⟨0, Nat.zero_lt_succ m, hg1⟩
        rw [dite_eq_left hf]
        have hfind0 : Nat.find hf = 0 := Nat.eq_zero_of_le_zero (Nat.find_min' hf ⟨by omega, hg1⟩)
        refine P.expectedSubseqSuccesses_congr ℓ (by omega) fun k hk₁ hk₂ => ?_
        dsimp only [tail, suffixPrimIdSeq, Fin.succ]
        exact congrArg seq (Fin.ext (by dsimp only; omega))
  intro T seq
  rw [expectedSubseqSuccesses]
  simp only [hrem_eq]

/-- Convert `(s₀, ss)` into `Fin (ss.length + 1) → α`. -/
@[expose]
noncomputable def seqOfHeadList {α : Type*} (s₀ : α) (ss : List α) :
    Fin (ss.length + 1) → α :=
  Fin.cons s₀ ss.get

private theorem expectedRem_and_subseq_ofHeadList (ℓ : ℕ) :
    ∀ (ss : List (Finset (P.PrimId ℓ))) (s₀ : Finset (P.PrimId ℓ)),
      (∀ g : P.NodeSeed ℓ, P.IsGoodNodeSeed ℓ g s₀ →
        P.expectedRemRehashes ℓ ss.length (seqOfHeadList s₀ ss) g =
          P.expectedRemRehashes ℓ (dedupAdj s₀ ss).length
            (seqOfHeadList s₀ (dedupAdj s₀ ss)) g) ∧
      P.expectedSubseqSuccesses ℓ ss.length (seqOfHeadList s₀ ss) =
        P.expectedSubseqSuccesses ℓ (dedupAdj s₀ ss).length
          (seqOfHeadList s₀ (dedupAdj s₀ ss)) := by
  classical
  intro ss
  induction ss with
  | nil =>
    intro s₀
    exact ⟨fun _ _ => rfl, rfl⟩
  | cons s₁ tail ih =>
    intro s₀
    obtain ⟨ih_rem, ih_sub⟩ := ih s₁
    have htail_eq : (fun i : Fin tail.length.succ => (seqOfHeadList s₀ (s₁ :: tail)) i.succ) =
        seqOfHeadList s₁ tail := by
      ext i
      cases i using Fin.cases <;> rfl
    have hrem : ∀ g : P.NodeSeed ℓ, P.IsGoodNodeSeed ℓ g s₀ →
        P.expectedRemRehashes ℓ (s₁ :: tail).length (seqOfHeadList s₀ (s₁ :: tail)) g =
          P.expectedRemRehashes ℓ (dedupAdj s₀ (s₁ :: tail)).length
            (seqOfHeadList s₀ (dedupAdj s₀ (s₁ :: tail))) g := by
      intro g hg0
      dsimp only [dedupAdj]
      by_cases h10 : s₁ = s₀
      · subst h10
        rw [ite_eq_left rfl]
        dsimp only [List.length_cons, expectedRemRehashes]
        have hc1 : seqOfHeadList s₁ (s₁ :: tail) 1 = s₁ := rfl
        rw [hc1, ite_eq_left hg0, htail_eq]
        exact ih_rem g hg0
      · rw [ite_eq_right h10]
        dsimp only [List.length_cons, expectedRemRehashes]
        have hc1 : seqOfHeadList s₀ (s₁ :: tail) 1 = s₁ := rfl
        have hc2 : seqOfHeadList s₀ (s₁ :: dedupAdj s₁ tail) 1 = s₁ := rfl
        have hdtail : (fun i : Fin (dedupAdj s₁ tail).length.succ =>
            (seqOfHeadList s₀ (s₁ :: dedupAdj s₁ tail)) i.succ) =
            seqOfHeadList s₁ (dedupAdj s₁ tail) := by
          ext i
          cases i using Fin.cases <;> rfl
        rw [hc1, hc2, htail_eq, hdtail]
        by_cases hg1 : P.IsGoodNodeSeed ℓ g s₁
        · rw [ite_eq_left hg1, ite_eq_left hg1]; exact ih_rem g hg1
        · rw [ite_eq_right hg1, ite_eq_right hg1]; exact ih_sub
    refine ⟨hrem, ?_⟩
    rw [P.expectedSubseqSuccesses_eq_one_add_avg_rem ℓ (s₁ :: tail).length _,
      P.expectedSubseqSuccesses_eq_one_add_avg_rem ℓ (dedupAdj s₀ (s₁ :: tail)).length _]
    have h0₁ : seqOfHeadList s₀ (s₁ :: tail) 0 = s₀ := rfl
    have h0₂ : seqOfHeadList s₀ (dedupAdj s₀ (s₁ :: tail)) 0 = s₀ := rfl
    dsimp only
    rw [h0₁, h0₂]
    congr 2
    exact Finset.sum_congr rfl fun g hg => hrem g (mem_filter.mp hg).2

/-- `List`-form stutter-invariant subsequence bound on `(s₀, ss)`. -/
theorem expectedSubseqSuccesses_seqOfHeadList_le (hcr : P.ConcentrationReady) {ℓ : ℕ}
    (hℓ : ℓ ≤ P.depth) (s₀ : Finset (P.PrimId ℓ)) (ss : List (Finset (P.PrimId ℓ)))
    (h0 : P.nLow ℓ ≤ #s₀ ∧ #s₀ ≤ P.nHigh ℓ)
    (hss : ∀ s ∈ ss, P.nLow ℓ ≤ #s ∧ #s ≤ P.nHigh ℓ) :
    P.expectedSubseqSuccesses ℓ ss.length (seqOfHeadList s₀ ss) ≤
      1 + 20 * (listChanges s₀ ss : ℝ) / (P.nFloor ℓ : ℝ) ^ 2 := by
  rw [(P.expectedRem_and_subseq_ofHeadList ℓ ss s₀).2, ← length_dedupAdj s₀ ss]
  refine P.expectedSubseqSuccesses_le hcr hℓ _ _ fun j => ?_
  refine Fin.cases h0 (fun i => ?_) j
  dsimp only [seqOfHeadList]
  rw [Fin.cons_succ]
  exact hss _ (mem_dedupAdj (List.get_mem (dedupAdj s₀ ss) i))

/-- **Stutter-invariant subsequence bound**: unchanged steps `seq i.succ = seq i.castSucc` never
cause a good seed to fail, so `expectedSubseqSuccesses ℓ T seq` is bounded in terms of the number
`seqChanges seq` of actual set changes rather than raw step count `T`. -/
theorem expectedSubseqSuccesses_le_of_changes (hcr : P.ConcentrationReady) {ℓ : ℕ}
    (hℓ : ℓ ≤ P.depth) (T : ℕ) (seq : Fin (T + 1) → Finset (P.PrimId ℓ))
    (hvalid : P.ValidPrimIdSeq ℓ T seq) :
    P.expectedSubseqSuccesses ℓ T seq ≤
      1 + 20 * (seqChanges seq : ℝ) / (P.nFloor ℓ : ℝ) ^ 2 := by
  let ls := List.ofFn fun i : Fin T => seq i.succ
  have heq_seq : P.expectedSubseqSuccesses ℓ T seq =
      P.expectedSubseqSuccesses ℓ ls.length (seqOfHeadList (seq 0) ls) := by
    refine P.expectedSubseqSuccesses_congr ℓ (List.length_ofFn).symm fun k hk₁ hk₂ => ?_
    rcases k with _ | k'
    · rfl
    · dsimp only [seqOfHeadList]
      rw [show (⟨k' + 1, hk₂⟩ : Fin (ls.length + 1)) =
        (⟨k', Nat.lt_of_succ_lt_succ hk₂⟩ : Fin ls.length).succ from rfl,
        Fin.cons_succ, List.get_ofFn]
      exact congrArg seq (Fin.ext rfl)
  rw [heq_seq, ← listChanges_ofFn seq]
  refine P.expectedSubseqSuccesses_seqOfHeadList_le hcr hℓ (seq 0) ls (hvalid 0) fun s hs => ?_
  obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hs
  exact hvalid r.succ

/-- Batch of `K` maximal ancestor-rehash-free subsequences across level-`ℓ` nodes during `M`
oblivious updates (`∑ r, lengths r ≤ M`). -/
structure LevelSubseqBatch (ℓ K M : ℕ) where
  /-- Update count of each maximal ancestor-rehash-free subsequence. -/
  lengths : Fin K → ℕ
  /-- Oblivious `PrimId ℓ` set trajectory along each subsequence. -/
  trajectories : ∀ r : Fin K, Fin (lengths r + 1) → Finset (P.PrimId ℓ)
  valid : ∀ r : Fin K, P.ValidPrimIdSeq ℓ (lengths r) (trajectories r)
  sum_lengths_le : ∑ r : Fin K, lengths r ≤ M

/-- Summing `expectedSubseqSuccesses_le` across any `LevelSubseqBatch` of `K` subsequences with
total update count `≤ M` gives at most `K + 20 * M / (nFloor ℓ) ^ 2` expected successful rehashes.
-/
theorem sum_expectedSubseqSuccesses_le (hcr : P.ConcentrationReady) {ℓ K M : ℕ}
    (hℓ : ℓ ≤ P.depth) (batch : P.LevelSubseqBatch ℓ K M) :
    ∑ r : Fin K, P.expectedSubseqSuccesses ℓ (batch.lengths r) (batch.trajectories r) ≤
      (K : ℝ) + 20 * (M : ℝ) / (P.nFloor ℓ : ℝ) ^ 2 := by
  have hsq_pos : (0 : ℝ) < (P.nFloor ℓ : ℝ) ^ 2 :=
    sq_pos_of_pos (Nat.cast_pos.mpr (P.nFloor_pos ℓ hℓ))
  calc ∑ r : Fin K, P.expectedSubseqSuccesses ℓ (batch.lengths r) (batch.trajectories r)
      ≤ ∑ r : Fin K, (1 + 20 * (batch.lengths r : ℝ) / (P.nFloor ℓ : ℝ) ^ 2) :=
        sum_le_sum fun r _ => P.expectedSubseqSuccesses_le hcr hℓ _ _ (batch.valid r)
    _ = (K : ℝ) + 20 * (∑ r : Fin K, (batch.lengths r : ℝ)) / (P.nFloor ℓ : ℝ) ^ 2 := by
        rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
          ← sum_div, ← mul_sum]
    _ ≤ (K : ℝ) + 20 * (M : ℝ) / (P.nFloor ℓ : ℝ) ^ 2 := by
        have hsum_real : (∑ r : Fin K, (batch.lengths r : ℝ)) ≤ (M : ℝ) := by
          rw [← Nat.cast_sum]; exact_mod_cast batch.sum_lengths_le
        exact add_le_add_right
          (div_le_div_of_nonneg_right (by linarith) hsq_pos.le) _

private theorem sum_inv_nFloor_le_two_div {ℓ : ℕ} (hℓ : ℓ ≤ P.depth) :
    ∑ j ∈ Finset.range (ℓ + 1), (1 : ℝ) / (P.nFloor j : ℝ) ≤
      2 / (P.nFloor ℓ : ℝ) := by
  induction ℓ with
  | zero =>
    have hn0 : (0 : ℝ) < P.nFloor 0 := Nat.cast_pos.mpr (P.nFloor_pos 0 (Nat.zero_le _))
    rw [Nat.zero_add, Finset.range_one, sum_singleton]
    rw [div_le_div_iff_of_pos_right hn0]
    norm_num
  | succ m ih =>
    have hm_lt : m < P.depth := Nat.lt_of_succ_le hℓ
    have hstep := P.nFloor_step_le m hm_lt
    have hb1 := P.branchBits_pos m hm_lt
    have h2_le : 2 * P.nFloor (m + 1) ≤ P.nFloor m := by
      have h2pow : 2 ≤ 2 ^ P.branchBits m :=
        (show 2 = 2 ^ 1 by decide) ▸ Nat.pow_le_pow_right Nat.two_pos hb1
      exact (Nat.mul_le_mul_right _ h2pow).trans hstep
    have hnm : (0 : ℝ) < P.nFloor m := Nat.cast_pos.mpr (P.nFloor_pos m hm_lt.le)
    have hnm1 : (0 : ℝ) < P.nFloor (m + 1) := Nat.cast_pos.mpr (P.nFloor_pos (m + 1) hℓ)
    have h2_div : 2 / (P.nFloor m : ℝ) ≤ 1 / (P.nFloor (m + 1) : ℝ) := by
      rw [div_le_div_iff₀ hnm hnm1, one_mul]
      exact_mod_cast h2_le
    have h11 : (1 : ℝ) / (P.nFloor (m + 1) : ℝ) + 1 / (P.nFloor (m + 1) : ℝ) =
        2 / (P.nFloor (m + 1) : ℝ) := by ring
    rw [Finset.sum_range_succ]
    linarith [ih hm_lt.le]

/-- **Multi-level recurrence-telescoping bound (`Lemma 5.3` over abstract `TreeSchedule`)**:
for any nonneg level-wise expected successful-rehash counts `succRehashes : ℕ → ℝ` satisfying the
top-level initialization + update bound `succRehashes 0 ≤ 1 + 20 * M / (nFloor 0) ^ 2` and the
parent-to-child recurrence
`succRehashes (ℓ + 1) ≤ succRehashes ℓ * branchFactor ℓ + 20 * M / (nFloor (ℓ + 1)) ^ 2`,
the total expected rehashing work across all levels `0 ≤ ℓ ≤ depth` (charging `2 * nFloor ℓ` per
successful rehash to include `≤ 2` expected rejection-sampling seed trials) is at most
`14 * (depth + 1) * (cap + M)` ([LiLiangYuZhou2024, Section 5.5, Lemma 5.3];
[arXiv:2310.20536v1](https://arxiv.org/abs/2310.20536v1), PDF pp. 34–35 / printed pp. 33–34;
instantiated unconditionally for `OracleComp` tree histories in `TreeExec.lean`). -/
theorem rehashWork_of_level_recurrence (hcr : P.ConcentrationReady) {M : ℕ}
    {succRehashes : ℕ → ℝ}
    (hnonneg : ∀ ℓ ≤ P.depth, 0 ≤ succRehashes ℓ)
    (hbase : succRehashes 0 ≤ 1 + 20 * (M : ℝ) / (P.nFloor 0 : ℝ) ^ 2)
    (hstep : ∀ ℓ < P.depth,
      succRehashes (ℓ + 1) ≤
        succRehashes ℓ * (P.branchFactor ℓ : ℝ) +
          20 * (M : ℝ) / (P.nFloor (ℓ + 1) : ℝ) ^ 2) :
    ∑ ℓ ∈ Finset.range (P.depth + 1), 2 * succRehashes ℓ * (P.nFloor ℓ : ℝ) ≤
      14 * ((P.depth + 1 : ℕ) : ℝ) * ((P.cap + M : ℕ) : ℝ) := by
  have hlevel_tele : ∀ ℓ ≤ P.depth,
      succRehashes ℓ * (P.nFloor ℓ : ℝ) ≤
        (P.cap : ℝ) + 20 * (M : ℝ) * ∑ j ∈ Finset.range (ℓ + 1), (1 : ℝ) / (P.nFloor j : ℝ) := by
    intro ℓ hℓ
    induction ℓ with
    | zero =>
      have hn0_pos : (0 : ℝ) < P.nFloor 0 := Nat.cast_pos.mpr (P.nFloor_pos 0 (Nat.zero_le _))
      have hmul := mul_le_mul_of_nonneg_right hbase hn0_pos.le
      rw [Nat.zero_add, Finset.range_one, sum_singleton]
      have hcap0 : (P.nFloor 0 : ℝ) = (P.cap : ℝ) := by exact_mod_cast P.nFloor_zero
      have hsimp : (1 + 20 * (M : ℝ) / (P.nFloor 0 : ℝ) ^ 2) * (P.nFloor 0 : ℝ) =
          (P.cap : ℝ) + 20 * (M : ℝ) * ((1 : ℝ) / (P.nFloor 0 : ℝ)) := by
        rw [← hcap0]; field_simp
      linarith
    | succ m ih =>
      have hm_lt : m < P.depth := Nat.lt_of_succ_le hℓ
      have hnm1_pos : (0 : ℝ) < P.nFloor (m + 1) := Nat.cast_pos.mpr (P.nFloor_pos (m + 1) hℓ)
      have hbf_le : (P.branchFactor m : ℝ) * (P.nFloor (m + 1) : ℝ) ≤ (P.nFloor m : ℝ) := by
        dsimp only [branchFactor]; exact_mod_cast P.nFloor_step_le m hm_lt
      have hmul := mul_le_mul_of_nonneg_right (hstep m hm_lt) hnm1_pos.le
      have hprod_le : succRehashes m * (P.branchFactor m : ℝ) * (P.nFloor (m + 1) : ℝ) ≤
          succRehashes m * (P.nFloor m : ℝ) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hbf_le (hnonneg m hm_lt.le)
      have hdiv_simp : (20 * (M : ℝ) / (P.nFloor (m + 1) : ℝ) ^ 2) * (P.nFloor (m + 1) : ℝ) =
          20 * (M : ℝ) * ((1 : ℝ) / (P.nFloor (m + 1) : ℝ)) := by
        field_simp
      rw [Finset.sum_range_succ, mul_add]
      linarith [ih hm_lt.le]
  have hlevel_bound : ∀ ℓ ≤ P.depth,
      2 * succRehashes ℓ * (P.nFloor ℓ : ℝ) ≤ 14 * ((P.cap + M : ℕ) : ℝ) := by
    intro ℓ hℓ
    have h6 : (6 : ℝ) ≤ P.nFloor ℓ := by exact_mod_cast hcr.six_le_nFloor ℓ hℓ
    have hinv := P.sum_inv_nFloor_le_two_div hℓ
    have h2div : 2 / (P.nFloor ℓ : ℝ) ≤ (1 : ℝ) / 3 := by
      rw [div_le_div_iff₀ (by linarith) (by positivity)]
      linarith
    have htele := hlevel_tele ℓ hℓ
    have hM_nonneg : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    have hcap_nonneg : (0 : ℝ) ≤ P.cap := Nat.cast_nonneg P.cap
    rw [Nat.cast_add]
    nlinarith
  calc ∑ ℓ ∈ Finset.range (P.depth + 1), 2 * succRehashes ℓ * (P.nFloor ℓ : ℝ)
      ≤ ∑ _ℓ ∈ Finset.range (P.depth + 1), 14 * ((P.cap + M : ℕ) : ℝ) :=
        sum_le_sum fun ℓ hℓ => hlevel_bound ℓ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hℓ))
    _ = 14 * ((P.depth + 1 : ℕ) : ℝ) * ((P.cap + M : ℕ) : ℝ) := by
        rw [sum_const, Finset.card_range, nsmul_eq_mul]; ring

end TreeSchedule

/-- Under `ValidRegime`, `treeDepth U (redundancyRatio n R) + 1 ≤ 3 * Nat.logStar n`. -/
theorem ValidRegime.treeDepth_add_one_le_three_mul_logStar
    {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    treeDepth U (redundancyRatio n R) + 1 ≤ 3 * Nat.logStar n := by
  have hk := h.treeDepth_le_logStar_add_four
  have h3 := h.three_le_logStar
  omega

/-- **Recurrence-telescoping `Lemma 5.3` bound across `ValidRegime`**:
given level-wise expected successful-rehash counts `succRehashes : ℕ → ℝ` satisfying `hbase` and
`hstep` over `M` single-key padded updates, total expected rehashing work across all levels of
`canonicalSchedule h` is at most `42 * (n + M) * Nat.logStar n`
([LiLiangYuZhou2024, Section 5.5, Lemma 5.3];
[arXiv:2310.20536v1](https://arxiv.org/abs/2310.20536v1), PDF pp. 34–35 / printed pp. 33–34;
see `canonicalSchedule_expectedCost_execHistory_le` in `TreeExec.lean` for the unconditional
bound over `M` external `Dynamic.Op` updates). -/
theorem canonicalSchedule_rehashWork_le_mul_logStar
    {U V n R p_min q_min p_max q_max M : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max)
    {succRehashes : ℕ → ℝ}
    (hnonneg : ∀ ℓ ≤ (canonicalSchedule h).depth, 0 ≤ succRehashes ℓ)
    (hbase : succRehashes 0 ≤ 1 + 20 * (M : ℝ) / ((canonicalSchedule h).nFloor 0 : ℝ) ^ 2)
    (hstep : ∀ ℓ < (canonicalSchedule h).depth,
      succRehashes (ℓ + 1) ≤
        succRehashes ℓ * ((canonicalSchedule h).branchFactor ℓ : ℝ) +
          20 * (M : ℝ) / ((canonicalSchedule h).nFloor (ℓ + 1) : ℝ) ^ 2) :
    ∑ ℓ ∈ Finset.range ((canonicalSchedule h).depth + 1),
        2 * succRehashes ℓ * ((canonicalSchedule h).nFloor ℓ : ℝ) ≤
      42 * ((n + M : ℕ) : ℝ) * (Nat.logStar n : ℝ) := by
  have hgen := (canonicalSchedule h).rehashWork_of_level_recurrence
    (canonicalSchedule_concentrationReady h) hnonneg hbase hstep
  have hdepth : ((canonicalSchedule h).depth + 1 : ℕ) ≤ 3 * Nat.logStar n :=
    h.treeDepth_add_one_le_three_mul_logStar
  have hdepth_real : (((canonicalSchedule h).depth + 1 : ℕ) : ℝ) ≤ 3 * (Nat.logStar n : ℝ) := by
    exact_mod_cast hdepth
  have hcap : (canonicalSchedule h).cap = n := rfl
  rw [hcap] at hgen
  have hpos : (0 : ℝ) ≤ ((n + M : ℕ) : ℝ) := Nat.cast_nonneg _
  nlinarith

end Cslib.DataStructure.Dictionary.SubconstantRedundancy
