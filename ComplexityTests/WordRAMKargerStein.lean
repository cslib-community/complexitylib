/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.WordRAM.KargerStein

/-!
# Karger–Stein recursive `FastCut` tests on the randomized word RAM

Concrete non-vacuity and behavioral tests for `Cslib.Algorithms.WordRAM.Karger` (`FastCut.lean` and
`KargerStein.lean`):

1. Pure-integer threshold and recursion-depth checks (`fastCutThreshold` on `7, 8, 9, 16` and
   `fastCutDepth` on `6, 8, 16`).
2. Weighted 8-vertex imbalanced barbell (`barbell8W`, two `K_4` cliques of edge weight `10` joined
   by two unit-weight bridge edges `(0, 7)` and `(3, 4)`, `minCut = 2` strictly below every
   singleton degree `≥ 30`): exercises recursive branching (`8 → 6 → 2`) in `fastCutProgram_spec`,
   `fastCutHighProbProgram_spec`, and `fastCutHighProbProgram_failure_le_inv_n` at `w = 16`.
3. Disconnected and zero-weight 8-vertex multigraphs (`minCut = 0`): verifies fault-free halting
   across the recursive frame stack along the deterministic `totS = 0` contraction branch.
-/

@[expose] public section

namespace ComplexityTests.WordRAMKargerStein

open Cslib Cslib.WordRAM Cslib.Algorithms.WordRAM.Karger
open scoped ENNReal

/-! ## 1. Pure-integer threshold and recursion depth -/

theorem fastCutThreshold_values :
    fastCutThreshold 7 = 6 ∧
    fastCutThreshold 8 = 6 ∧
    fastCutThreshold 9 = 7 ∧
    fastCutThreshold 16 = 12 := by
  decide

theorem fastCutDepth_values :
    fastCutDepth 6 = 0 ∧
    fastCutDepth 8 = 1 ∧
    fastCutDepth 16 = 4 := by
  have h6 : fastCutDepth 6 = 0 := fastCutDepth_of_lt_seven (by decide)
  have h7 : fastCutDepth 7 = 1 := by
    rw [fastCutDepth_of_ge_seven (by decide), show fastCutThreshold 7 = 6 by decide, h6]
  have h8 : fastCutDepth 8 = 1 := by
    rw [fastCutDepth_of_ge_seven (by decide), show fastCutThreshold 8 = 6 by decide, h6]
  have h9 : fastCutDepth 9 = 2 := by
    rw [fastCutDepth_of_ge_seven (by decide), show fastCutThreshold 9 = 7 by decide, h7]
  have h12 : fastCutDepth 12 = 3 := by
    rw [fastCutDepth_of_ge_seven (by decide), show fastCutThreshold 12 = 9 by decide, h9]
  have h16 : fastCutDepth 16 = 4 := by
    rw [fastCutDepth_of_ge_seven (by decide), show fastCutThreshold 16 = 12 by decide, h12]
  exact ⟨h6, h8, h16⟩

/-! ## 2. Weighted 8-vertex barbell (`minCut = 2`, recursive branching `8 → 6 → 2`) -/

/-- Weighted 8-vertex barbell: two `K_4` cliques `{0, 1, 2, 3}` and `{4, 5, 6, 7}` of edge weight
`10`, joined by two unit-weight bridge edges `{0, 7}` and `{3, 4}`. Every singleton cut has weight
`30` or `31`, whereas `{0, 1, 2, 3}` achieves `minCut = 2`. -/
def barbell8W (u v : Fin 8) : ℕ :=
  if u = v then 0
  else if (u.val < 4 ∧ v.val < 4) ∨ (4 ≤ u.val ∧ 4 ≤ v.val) then 10
  else if (u.val = 0 ∧ v.val = 7) ∨ (u.val = 7 ∧ v.val = 0) ∨
      (u.val = 3 ∧ v.val = 4) ∨ (u.val = 4 ∧ v.val = 3) then 1
  else 0

theorem isMultigraph_barbell8W : IsMultigraph barbell8W := by
  refine ⟨fun u v => ?_, fun u => ?_⟩
  · unfold barbell8W
    by_cases huv : u = v
    · subst huv; simp
    · have hvu : v ≠ u := Ne.symm huv
      simp only [huv, hvu, ↓reduceIte]
      split_ifs <;> omega
  · simp [barbell8W]

private theorem single_edge_le_cutWeight {n : ℕ} (W : Fin n → Fin n → ℕ) {C : Finset (Fin n)}
    {u v : Fin n} (hu : u ∈ C) (hv : v ∉ C) :
    W u v ≤ cutWeight W C := by
  have hv' : v ∈ Finset.univ \ C := Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hv⟩
  unfold cutWeight
  exact (Finset.single_le_sum (fun b _ => Nat.zero_le (W u b)) hv').trans
    (Finset.single_le_sum (f := fun a => ∑ b ∈ Finset.univ \ C, W a b)
      (fun _ _ => Nat.zero_le _) hu)

private theorem two_sources_le_cutWeight {n : ℕ} (W : Fin n → Fin n → ℕ) {C : Finset (Fin n)}
    {u₁ u₂ v₁ v₂ : Fin n} (hne : u₁ ≠ u₂)
    (hu₁ : u₁ ∈ C) (hu₂ : u₂ ∈ C) (hv₁ : v₁ ∉ C) (hv₂ : v₂ ∉ C) :
    W u₁ v₁ + W u₂ v₂ ≤ cutWeight W C := by
  have hv₁' : v₁ ∈ Finset.univ \ C := Finset.mem_sdiff.mpr ⟨Finset.mem_univ v₁, hv₁⟩
  have hv₂' : v₂ ∈ Finset.univ \ C := Finset.mem_sdiff.mpr ⟨Finset.mem_univ v₂, hv₂⟩
  have hs₁ : W u₁ v₁ ≤ ∑ b ∈ Finset.univ \ C, W u₁ b :=
    Finset.single_le_sum (fun b _ => Nat.zero_le _) hv₁'
  have hs₂ : W u₂ v₂ ≤ ∑ b ∈ Finset.univ \ C, W u₂ b :=
    Finset.single_le_sum (fun b _ => Nat.zero_le _) hv₂'
  have hsub : ({u₁, u₂} : Finset (Fin n)) ⊆ C := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx'
    · exact hu₁
    · exact (Finset.mem_singleton.mp hx') ▸ hu₂
  have hpair : ∑ a ∈ ({u₁, u₂} : Finset (Fin n)), ∑ b ∈ Finset.univ \ C, W a b ≤ cutWeight W C := by
    unfold cutWeight
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.zero_le _
  rw [Finset.sum_pair hne] at hpair
  omega

theorem totalDoubledWeight_barbell8W_lt : totalDoubledWeight barbell8W < 2 ^ 16 := by
  have hentry : ∀ u v : Fin 8, barbell8W u v ≤ 10 := by
    intro u v
    unfold barbell8W
    split_ifs <;> omega
  have hrow : ∀ u : Fin 8, rowDeg barbell8W u ≤ 80 := fun u => by
    unfold rowDeg
    calc
      ∑ v : Fin 8, barbell8W u v ≤ ∑ _v : Fin 8, 10 := Finset.sum_le_sum fun v _ => hentry u v
      _ = 80 := by simp
  have htot : totalDoubledWeight barbell8W ≤ 640 := by
    unfold totalDoubledWeight
    calc
      ∑ u : Fin 8, rowDeg barbell8W u ≤ ∑ _u : Fin 8, 80 := Finset.sum_le_sum fun u _ => hrow u
      _ = 640 := by simp
  omega

theorem minCut_barbell8W : minCut barbell8W = 2 := by
  let L : Finset (Fin 8) := Finset.univ.filter (fun u : Fin 8 => u.val < 4)
  apply le_antisymm
  · have hnt : IsNonTrivialCut L := by
      refine ⟨⟨0, by simp [L]⟩, fun h => ?_⟩
      have h4 : (4 : Fin 8) ∈ L := h ▸ Finset.mem_univ 4
      simp [L] at h4
    let rowSum (u : Fin 8) : ℕ := ∑ v ∈ Finset.univ \ L, barbell8W u v
    have hrow0 : rowSum 0 = 1 := by
      change ∑ v ∈ Finset.univ \ L, barbell8W 0 v = 1
      rw [Finset.sum_eq_single (7 : Fin 8)]
      · decide
      · intro v hv hv7
        have hvL : 4 ≤ v.val := by simpa [L] using hv
        have hv7' : v.val ≠ 7 := fun h => hv7 (Fin.ext h)
        unfold barbell8W
        split_ifs <;> omega
      · intro h7
        exfalso
        exact h7 (by simp [L])
    have hrow3 : rowSum 3 = 1 := by
      change ∑ v ∈ Finset.univ \ L, barbell8W 3 v = 1
      rw [Finset.sum_eq_single (4 : Fin 8)]
      · decide
      · intro v hv hv4
        have hvL : 4 ≤ v.val := by simpa [L] using hv
        have hv4' : v.val ≠ 4 := fun h => hv4 (Fin.ext h)
        unfold barbell8W
        split_ifs <;> omega
      · intro h4
        exfalso
        exact h4 (by simp [L])
    have hrow_other : ∀ u ∈ L, u ≠ 0 → u ≠ 3 → rowSum u = 0 := by
      intro u hu hu0 hu3
      have huL : u.val < 4 := by simpa [L] using hu
      have hu0' : u.val ≠ 0 := fun h => hu0 (Fin.ext h)
      have hu3' : u.val ≠ 3 := fun h => hu3 (Fin.ext h)
      refine Finset.sum_eq_zero fun v hv => ?_
      have hvL : 4 ≤ v.val := by simpa [L] using hv
      unfold barbell8W
      split_ifs <;> omega
    have hcw : cutWeight barbell8W L = 2 := by
      change ∑ u ∈ L, rowSum u = 2
      rw [← Finset.add_sum_erase L rowSum (by simp [L] : (0 : Fin 8) ∈ L), hrow0]
      rw [← Finset.add_sum_erase (L.erase 0) rowSum (by simp [L] : (3 : Fin 8) ∈ L.erase 0), hrow3]
      have hrest : ∑ u ∈ (L.erase 0).erase 3, rowSum u = 0 := by
        refine Finset.sum_eq_zero fun u hu => ?_
        have hu3 : u ≠ 3 := (Finset.mem_erase.mp hu).1
        have hu' := (Finset.mem_erase.mp hu).2
        have hu0 : u ≠ 0 := (Finset.mem_erase.mp hu').1
        exact hrow_other u (Finset.mem_erase.mp hu').2 hu0 hu3
      omega
    exact hcw ▸ minCut_le_cutWeight barbell8W hnt
  · refine (le_minCut_iff (by decide) barbell8W 2).mpr fun C hC => ?_
    by_cases hsplitL : ∃ u : Fin 8, ∃ v : Fin 8, u.val < 4 ∧ v.val < 4 ∧ u ∈ C ∧ v ∉ C
    · obtain ⟨u, v, hu4, hv4, huC, hvC⟩ := hsplitL
      have huv : u ≠ v := fun h => hvC (h ▸ huC)
      have hw10 : barbell8W u v = 10 := by
        unfold barbell8W
        simp [huv, hu4, hv4]
      have hle := single_edge_le_cutWeight barbell8W huC hvC
      omega
    · by_cases hsplitR : ∃ u : Fin 8, ∃ v : Fin 8, 4 ≤ u.val ∧ 4 ≤ v.val ∧ u ∈ C ∧ v ∉ C
      · obtain ⟨u, v, hu4, hv4, huC, hvC⟩ := hsplitR
        have huv : u ≠ v := fun h => hvC (h ▸ huC)
        have hw10 : barbell8W u v = 10 := by
          unfold barbell8W
          simp [huv, hu4, hv4]
        have hle := single_edge_le_cutWeight barbell8W huC hvC
        omega
      · by_cases h0 : (0 : Fin 8) ∈ C
        · have hL_in : ∀ u : Fin 8, u.val < 4 → u ∈ C := fun u hu => by
            by_contra huC
            exact hsplitL ⟨0, u, by decide, hu, h0, huC⟩
          have hex_out : ∃ v : Fin 8, v ∉ C := by
            by_contra hall
            exact hC.2 (Finset.eq_univ_iff_forall.mpr fun v =>
              Classical.not_not.mp fun hv => hall ⟨v, hv⟩)
          obtain ⟨v₀, hv₀⟩ := hex_out
          have hv₀_ge : 4 ≤ v₀.val := by
            by_contra hlt
            exact hv₀ (hL_in v₀ (by omega))
          have hR_out : ∀ v : Fin 8, 4 ≤ v.val → v ∉ C := fun v hv => by
            intro hvC
            exact hsplitR ⟨v, v₀, hv, hv₀_ge, hvC, hv₀⟩
          have hle := two_sources_le_cutWeight barbell8W (u₁ := 0) (u₂ := 3) (v₁ := 7) (v₂ := 4)
            (by decide) h0 (hL_in 3 (by decide)) (hR_out 7 (by decide)) (hR_out 4 (by decide))
          have hw1 : barbell8W 0 7 + barbell8W 3 4 = 2 := by decide
          omega
        · have hL_out : ∀ v : Fin 8, v.val < 4 → v ∉ C := fun v hv hvC =>
            hsplitL ⟨v, 0, hv, by decide, hvC, h0⟩
          obtain ⟨u₀, hu₀⟩ := hC.1
          have hu₀_ge : 4 ≤ u₀.val := by
            by_contra hlt
            exact hL_out u₀ (by omega) hu₀
          have hR_in : ∀ u : Fin 8, 4 ≤ u.val → u ∈ C := fun u hu => by
            by_contra huC
            exact hsplitR ⟨u₀, u, hu₀_ge, hu, hu₀, huC⟩
          have hle := two_sources_le_cutWeight barbell8W (u₁ := 7) (u₂ := 4) (v₁ := 0) (v₂ := 3)
            (by decide) (hR_in 7 (by decide)) (hR_in 4 (by decide)) h0 (hL_out 3 (by decide))
          have hw1 : barbell8W 7 0 + barbell8W 4 3 = 2 := by decide
          omega

theorem fastCutProgram_barbell8 :
    RandHaltsWithin 16 fastCutProgram
      (.init (8 :: flattenMatrix barbell8W)) (fastCutTime 8) ∧
    RandCallsBounded 16 fastCutProgram
      (.init (8 :: flattenMatrix barbell8W)) (fastCutTime 8) 12 ∧
    (∀ cfg ∈ (runRand 16 fastCutProgram (fastCutTime 8)
        (.running (.init (8 :: flattenMatrix barbell8W)))).support,
      ∃ (y : Data 24) (C : Finset (Fin 8)),
        cfg = .halted (cutWeight barbell8W C) y ∧
        y.Bounded 16 ∧
        IsNonTrivialCut C ∧
        2 ≤ cutWeight barbell8W C ∧
        y.mem 1 = 8 ∧ y.mem 1730 = 0) ∧
    (1 : ℝ≥0∞) / 18 ≤
      (evalRand 16 fastCutProgram (fastCutTime 8)
        (.init (8 :: flattenMatrix barbell8W))).toOuterMeasure
        {cfg | ∃ y, cfg = .halted 2 y} := by
  have hw : logWidth 4 8 ≤ 16 := by decide
  have htot : Fits 16 (totalDoubledWeight barbell8W) := totalDoubledWeight_barbell8W_lt
  have hspec := fastCutProgram_spec (by decide : 2 ≤ 8) isMultigraph_barbell8W hw htot
  have hCalls := hspec.2.1
  have hq : fastCutNodeQueries 8 = 12 := by
    rw [fastCutNodeQueries_of_ge_seven (by decide), show fastCutThreshold 8 = 6 by decide,
      fastCutNodeQueries_of_lt_seven (by decide)]
  rw [hq] at hCalls
  refine ⟨hspec.1, hCalls, fun cfg hcfg => ?_, ?_⟩
  · obtain ⟨y, C, hcfg_eq, hbnd, hC, hge, hmod⟩ := hspec.2.2.1 cfg hcfg
    rw [minCut_barbell8W] at hge
    have hm1 : y.mem 1 = 8 := by
      rw [hmod 1 (by rw [Finset.mem_Ico]; omega)]
      exact Data.init_mem_succ (r := 24) (8 :: flattenMatrix barbell8W) 0
    have hm1730 : y.mem 1730 = 0 := by
      rw [hmod 1730 (by rw [Finset.mem_Ico]; omega),
        show (1730 : ℕ) = 1729 + 1 from rfl, Data.init_mem_succ,
        List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by rw [List.length_cons, length_flattenMatrix]; decide)]
      rfl
    exact ⟨y, C, hcfg_eq, hbnd, hC, hge, hm1, hm1730⟩
  · have hProb := hspec.2.2.2 (by rw [minCut_barbell8W]; decide)
    have hset : {cfg : RandCfg 24 | ∃ y, cfg = .halted (minCut barbell8W) y} =
        {cfg : RandCfg 24 | ∃ y, cfg = .halted 2 y} := by
      rw [minCut_barbell8W]
    have hlog : (Nat.log 2 8 + 15 : ℕ) = 18 := by decide
    rwa [hset, hlog, Nat.cast_ofNat] at hProb

theorem fastCutHighProbProgram_barbell8 :
    RandHaltsWithin 16 fastCutHighProbProgram
      (.init (8 :: flattenMatrix barbell8W)) (fastCutHighProbTime 8) ∧
    (evalRand 16 fastCutHighProbProgram (fastCutHighProbTime 8)
        (.init (8 :: flattenMatrix barbell8W))).toOuterMeasure
        {cfg | ∀ y, cfg ≠ .halted 2 y} ≤
      (1 : ℝ≥0∞) / 16 ∧
    (evalRand 16 fastCutHighProbProgram (fastCutHighProbTime 8)
        (.init (8 :: flattenMatrix barbell8W))).toOuterMeasure
        {cfg | ∀ y, cfg ≠ .halted 2 y} ≤
      (1 : ℝ≥0∞) / 8 := by
  have hw : logWidth 4 8 ≤ 16 := by decide
  have htot : Fits 16 (totalDoubledWeight barbell8W) := totalDoubledWeight_barbell8W_lt
  have hspec := fastCutHighProbProgram_spec (by decide : 2 ≤ 8) isMultigraph_barbell8W hw htot
  have hpos : 0 < minCut barbell8W := by rw [minCut_barbell8W]; decide
  have hFail := hspec.2.2.2 hpos
  have hInv :=
    fastCutHighProbProgram_failure_le_inv_n (by decide : 2 ≤ 8) isMultigraph_barbell8W hw htot hpos
  have hset : {cfg : RandCfg 24 | ∀ y, cfg ≠ .halted (minCut barbell8W) y} =
      {cfg : RandCfg 24 | ∀ y, cfg ≠ .halted 2 y} := by
    rw [minCut_barbell8W]
  rw [hset, show (2 * 8 : ℕ) = 16 by decide, Nat.cast_ofNat] at hFail
  rw [hset, Nat.cast_ofNat] at hInv
  exact ⟨hspec.1, hFail, hInv⟩

/-! ## 3. Disconnected and zero-weight 8-vertex multigraphs (`minCut = 0`) -/

/-- Positive-weight disconnected 8-vertex multigraph: edge `{0, 1}` of weight `4` and isolated
vertices `2..7`, exercising the transition from `totS > 0` (`rand` contraction) to `totS = 0`
(deterministic contraction) across the recursive `FastCut` frame stack. -/
def disconnected8W (u v : Fin 8) : ℕ :=
  if (u.val = 0 ∧ v.val = 1) ∨ (u.val = 1 ∧ v.val = 0) then 4 else 0

theorem isMultigraph_disconnected8W : IsMultigraph disconnected8W := by
  refine ⟨fun u v => ?_, fun u => ?_⟩ <;>
  · unfold disconnected8W
    split_ifs <;> omega

theorem minCut_disconnected8W : minCut disconnected8W = 0 := by
  apply Nat.eq_zero_of_le_zero
  have hnt : IsNonTrivialCut ({(2 : Fin 8)} : Finset (Fin 8)) :=
    isNonTrivialCut_singleton (by decide) 2
  have hcw : cutWeight disconnected8W ({(2 : Fin 8)} : Finset (Fin 8)) = 0 := by
    unfold cutWeight
    rw [Finset.sum_singleton]
    apply Finset.sum_eq_zero
    intro v _
    have h2 : ((2 : Fin 8).val) = 2 := rfl
    unfold disconnected8W
    split_ifs <;> omega
  exact hcw ▸ minCut_le_cutWeight disconnected8W hnt

theorem fastCutProgram_disconnected8 :
    RandHaltsWithin 16 fastCutProgram
      (.init (8 :: flattenMatrix disconnected8W)) (fastCutTime 8) ∧
    RandHaltsWithin 16 fastCutHighProbProgram
      (.init (8 :: flattenMatrix disconnected8W)) (fastCutHighProbTime 8) ∧
    (∀ cfg ∈ (runRand 16 fastCutProgram (fastCutTime 8)
        (.running (.init (8 :: flattenMatrix disconnected8W)))).support,
      ∃ (y : Data 24) (C : Finset (Fin 8)),
        cfg = .halted (cutWeight disconnected8W C) y ∧ IsNonTrivialCut C) := by
  have hw : logWidth 4 8 ≤ 16 := by decide
  have hentry : ∀ u v : Fin 8, disconnected8W u v ≤ 4 := fun u v => by
    unfold disconnected8W
    split_ifs <;> omega
  have hrow : ∀ u : Fin 8, rowDeg disconnected8W u ≤ 32 := fun u => by
    unfold rowDeg
    calc
      ∑ v : Fin 8, disconnected8W u v ≤ ∑ _v : Fin 8, 4 := Finset.sum_le_sum fun v _ => hentry u v
      _ = 32 := by simp
  have htot : Fits 16 (totalDoubledWeight disconnected8W) := by
    have hle : totalDoubledWeight disconnected8W ≤ 256 := by
      unfold totalDoubledWeight
      calc
        ∑ u : Fin 8, rowDeg disconnected8W u ≤ ∑ _u : Fin 8, 32 :=
          Finset.sum_le_sum fun u _ => hrow u
        _ = 256 := by simp
    exact (by decide : Fits 16 256).of_le hle
  have h1 := fastCutProgram_spec (by decide : 2 ≤ 8) isMultigraph_disconnected8W hw htot
  have h2 := fastCutHighProbProgram_spec (by decide : 2 ≤ 8) isMultigraph_disconnected8W hw htot
  refine ⟨h1.1, h2.1, fun cfg hcfg => ?_⟩
  obtain ⟨y, C, hcfg_eq, -, hC_nt, -⟩ := h1.2.2.1 cfg hcfg
  exact ⟨y, C, hcfg_eq, hC_nt⟩

/-- Empty 8-vertex multigraph (`totalDoubledWeight = 0`), exercising the `totS = 0` deterministic
contraction branch across the recursive `FastCut` frame stack. -/
def zero8W : Fin 8 → Fin 8 → ℕ := fun _ _ => 0

theorem isMultigraph_zero8W : IsMultigraph zero8W :=
  ⟨fun _ _ => rfl, fun _ => rfl⟩

theorem fastCutProgram_zero8 :
    RandHaltsWithin 16 fastCutProgram (.init (8 :: flattenMatrix zero8W)) (fastCutTime 8) ∧
    RandHaltsWithin 16 fastCutHighProbProgram
      (.init (8 :: flattenMatrix zero8W)) (fastCutHighProbTime 8) ∧
    (∀ cfg ∈ (runRand 16 fastCutProgram (fastCutTime 8)
        (.running (.init (8 :: flattenMatrix zero8W)))).support,
      ∃ y : Data 24, cfg = .halted 0 y) := by
  have hw : logWidth 4 8 ≤ 16 := by decide
  have htot0 : Fits 16 (totalDoubledWeight zero8W) := by
    have hz : totalDoubledWeight zero8W = 0 := by simp [totalDoubledWeight, rowDeg, zero8W]
    rw [hz]
    exact fits_zero 16
  have h1 := fastCutProgram_spec (by decide : 2 ≤ 8) isMultigraph_zero8W hw htot0
  have h2 := fastCutHighProbProgram_spec (by decide : 2 ≤ 8) isMultigraph_zero8W hw htot0
  refine ⟨h1.1, h2.1, fun cfg hcfg => ?_⟩
  obtain ⟨y, C, hcfg_eq, -⟩ := h1.2.2.1 cfg hcfg
  have hcw0 : cutWeight zero8W C = 0 := by simp [cutWeight, zero8W]
  exact ⟨y, hcw0 ▸ hcfg_eq⟩

end ComplexityTests.WordRAMKargerStein
