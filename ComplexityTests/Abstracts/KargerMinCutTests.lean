/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

-- upstream: local-only (formal abstract tests)

import ComplexityAbstracts.KargerMinCutAbstract

/-!
# Regression tests for `KargerMinCutAbstract`

Concrete non-vacuity and behavioral checks on `KargerMinCutAbstract`:

1. Weighted 3-vertex triangle (`minCut = 5`): instantiates `kargerSingleTrial` at `w = 16`,
   checking `HaltsWithin`, `RandCallsBounded ... 1`, cut-weight lower bound and memory preservation
   outside `[2, 14)`, and `2 / 6 ≤ toOuterMeasure` of hitting `minCut = 5`.
2. Weighted 4-vertex barbell (`minCut = 2` achieved strictly by `{0, 1}`, whereas every singleton
   cut has weight `11`): instantiates `kargerAmplified` (`R = 6`) and `kargerHighProb` at `w = 16`,
   checking preservation of the input matrix in memory and failure bounds `(1 - 2 / 12) ^ 6` and
   `1 / 8`.
3. Empty 3-vertex multigraph (`minCut = 0`, `totalDoubledWeight = 0`): instantiates
   `kargerSingleTrial`, verifying fault-free halting with output `0` on every branch.
4. Weighted 8-vertex barbell (`minCut = 2` across two unit bridges between `K_4` cliques of edge
   weight `10`, exercising recursive branching `8 → 6 → 2`): instantiates `kargerSteinFastCut` and
   `kargerSteinHighProb` at the tight word-width boundary `w = 16`, checking halting, `rand`-call
   bounds, input-matrix and post-stack memory preservation (`M[0], M[1], M[3], M[1730]`), hit
   probability `≥ 1 / 18`, and miss probability `≤ 1 / 16`.
-/

namespace ComplexityTests.Abstracts.KargerMinCutTests

open ComplexityAbstracts.KargerMinCutAbstract

private theorem isNonTrivialCut_iff_card {n : ℕ} (C : Finset (Fin n)) :
    IsNonTrivialCut C ↔ 0 < C.card ∧ C.card < n := by
  constructor
  · rintro ⟨hne, hnu⟩
    refine ⟨Finset.card_pos.mpr hne, Nat.lt_of_le_of_ne ?_ fun hc => hnu ?_⟩
    · simpa using Finset.card_le_univ C
    · exact Finset.eq_univ_of_card C (by simpa using hc)
  · rintro ⟨hpos, hlt⟩
    refine ⟨Finset.card_pos.mp hpos, fun hu => ?_⟩
    simp [hu] at hlt

/-- Weighted 3-vertex triangle with edge weights `w(0, 1) = 3`, `w(1, 2) = 5`, `w(0, 2) = 2`. -/
def triangleW : Fin 3 → Fin 3 → ℕ
  | 0, 1 | 1, 0 => 3
  | 1, 2 | 2, 1 => 5
  | 0, 2 | 2, 0 => 2
  | _, _ => 0

theorem isMultigraph_triangleW : IsMultigraph triangleW := by
  refine ⟨fun u v => ?_, fun u => ?_⟩
  · fin_cases u <;> fin_cases v <;> rfl
  · fin_cases u <;> rfl

theorem minCut_triangleW : minCut triangleW = 5 := by
  have hnt0 : IsNonTrivialCut ({(0 : Fin 3)} : Finset (Fin 3)) := by
    rw [isNonTrivialCut_iff_card]
    decide
  have hcw0 : cutWeight triangleW ({(0 : Fin 3)} : Finset (Fin 3)) = 5 := by decide
  unfold minCut
  apply le_antisymm
  · exact Nat.sInf_le ⟨{(0 : Fin 3)}, hnt0, hcw0⟩
  · obtain ⟨C, hC, hcw⟩ :=
      Nat.sInf_mem (s := {k | ∃ C : Finset (Fin 3), IsNonTrivialCut C ∧ cutWeight triangleW C = k})
        ⟨5, {(0 : Fin 3)}, hnt0, hcw0⟩
    rw [← hcw]
    clear hcw
    rw [isNonTrivialCut_iff_card] at hC
    revert C hC
    decide

/-- Non-vacuous instantiation of `kargerSingleTrial` on `triangleW` (`n = 3, minCut = 5, w = 16`):
halts within `435` steps and `1` `rand` call, preserves `M[0]` and `M[14]`, outputs a cut weight
`≥ 5` on every branch, and hits `5` with probability at least `2 / 6`. -/
theorem kargerSingleTrial_triangle :
    ∃ p : Program 16,
      let input := 3 :: flattenMatrix triangleW
      HaltsWithin 16 p (init input) 435 ∧
      RandCallsBounded 16 p (init input) 435 1 ∧
      (∀ cfg ∈ (evalRand 16 p 435 (init input)).support,
        ∃ (reg : Fin 16 → ℕ) (mem : ℕ → ℕ) (C : Finset (Fin 3)),
          cfg = .halted (cutWeight triangleW C) reg mem ∧
          5 ≤ cutWeight triangleW C ∧
          mem 0 = 10 ∧ mem 1 = 3 ∧ mem 14 = 0) ∧
      (2 : ENNReal) / 6 ≤
        (evalRand 16 p 435 (init input)).toOuterMeasure
          {cfg | ∃ reg mem, cfg = .halted 5 reg mem} := by
  obtain ⟨p, hp⟩ := kargerSingleTrial
  have hw : 3 * (Nat.log 2 3 + 1) ≤ 16 := by decide
  have htot : totalDoubledWeight triangleW < 2 ^ 16 := by decide
  obtain ⟨hHalts, hCalls, hPost, hProb⟩ := hp 3 16 triangleW (by decide) isMultigraph_triangleW
    hw htot
  rw [minCut_triangleW] at hPost hProb
  have hT : 42 * 3 ^ 2 + 12 * 3 + 21 = 435 := by decide
  refine ⟨p, ?_, ?_, ?_, ?_⟩
  · simpa [hT] using hHalts
  · simpa [hT] using hCalls
  · intro cfg hcfg
    rw [← hT] at hcfg
    obtain ⟨reg, mem, C, rfl, -, -, -, hge, hframe⟩ := hPost cfg hcfg
    have hm0 : mem 0 = 10 := (hframe 0 (Or.inl (by decide))).trans (by decide)
    have hm1 : mem 1 = 3 := (hframe 1 (Or.inl (by decide))).trans (by decide)
    have hm14 : mem 14 = 0 := (hframe 14 (Or.inr (by decide))).trans (by decide)
    exact ⟨reg, mem, C, rfl, hge, hm0, hm1, hm14⟩
  · simpa [hT] using hProb (by decide)

/-- Weighted 4-vertex barbell: heavy edges `{0, 1}` and `{2, 3}` of weight `10` connected by two
bridge edges `{1, 2}` and `{0, 3}` of weight `1` (`minCut = 2` achieved strictly by `{0, 1}`). -/
def barbellW : Fin 4 → Fin 4 → ℕ
  | 0, 1 | 1, 0 => 10
  | 2, 3 | 3, 2 => 10
  | 1, 2 | 2, 1 => 1
  | 0, 3 | 3, 0 => 1
  | _, _ => 0

theorem isMultigraph_barbellW : IsMultigraph barbellW := by
  refine ⟨fun u v => ?_, fun u => ?_⟩
  · fin_cases u <;> fin_cases v <;> rfl
  · fin_cases u <;> rfl

theorem minCut_barbellW : minCut barbellW = 2 := by
  have hnt0 : IsNonTrivialCut ({(0 : Fin 4), 1} : Finset (Fin 4)) := by
    rw [isNonTrivialCut_iff_card]
    decide
  have hcw0 : cutWeight barbellW ({(0 : Fin 4), 1} : Finset (Fin 4)) = 2 := by decide
  unfold minCut
  apply le_antisymm
  · exact Nat.sInf_le ⟨{(0 : Fin 4), 1}, hnt0, hcw0⟩
  · obtain ⟨C, hC, hcw⟩ :=
      Nat.sInf_mem (s := {k | ∃ C : Finset (Fin 4), IsNonTrivialCut C ∧ cutWeight barbellW C = k})
        ⟨2, {(0 : Fin 4), 1}, hnt0, hcw0⟩
    rw [← hcw]
    clear hcw
    rw [isNonTrivialCut_iff_card] at hC
    revert C hC
    decide

/-- Non-vacuous instantiation of `kargerAmplified` (`R = 6`) and `kargerHighProb` on `barbellW`
(`n = 4, minCut = 2, w = 16`). -/
theorem kargerAmplified_and_highProb_barbell :
    (∃ p : Program 22,
      let input := 6 :: 4 :: flattenMatrix barbellW
      HaltsWithin 16 p (init input) 5284 ∧
      RandCallsBounded 16 p (init input) 5284 12 ∧
      (∀ cfg ∈ (evalRand 16 p 5284 (init input)).support,
        ∃ reg mem C, cfg = .halted (cutWeight barbellW C) reg mem ∧ mem 4 = 10) ∧
      (evalRand 16 p 5284 (init input)).toOuterMeasure
          {cfg | ∀ reg mem, cfg ≠ .halted 2 reg mem} ≤
        ((1 : ENNReal) - (2 : ENNReal) / 12) ^ 6) ∧
    (∃ q : Program 22,
      let input := 4 :: flattenMatrix barbellW
      HaltsWithin 16 q (init input) 33792 ∧
      RandCallsBounded 16 q (init input) 33792 48 ∧
      (evalRand 16 q 33792 (init input)).toOuterMeasure
          {cfg | ∀ reg mem, cfg ≠ .halted 2 reg mem} ≤
        (1 : ENNReal) / 8) := by
  have hw : 3 * (Nat.log 2 4 + 1) ≤ 16 := by decide
  have htot : totalDoubledWeight barbellW < 2 ^ 16 := by decide
  constructor
  · obtain ⟨p, hp⟩ := kargerAmplified
    obtain ⟨hH, hC, hP, hF⟩ := hp 6 4 16 barbellW (by decide) (by decide) isMultigraph_barbellW
      hw (by decide) htot
    rw [minCut_barbellW] at hF
    have hT : 6 * (50 * 4 ^ 2 + 12 * 4 + 30) + 16 = 5284 := by decide
    refine ⟨p, by simpa [hT] using hH, by simpa [hT] using hC, fun cfg hcfg => ?_,
      by simpa [hT] using hF (by decide)⟩
    rw [← hT] at hcfg
    obtain ⟨reg, mem, C, rfl, -, -, -, -, hframe⟩ := hP cfg hcfg
    have hm4 : mem 4 = 10 := (hframe 4 (Or.inl (by decide))).trans (by decide)
    exact ⟨reg, mem, C, rfl, hm4⟩
  · obtain ⟨q, hq⟩ := kargerHighProb
    obtain ⟨hH, hC, -, hF⟩ := hq 4 16 barbellW (by decide) isMultigraph_barbellW hw htot
    rw [minCut_barbellW] at hF
    have hF' := hF (by decide)
    have hT : 33 * 4 ^ 4 * (Nat.log 2 4 + 2) = 33792 := by decide
    have hR : (4 * (4 - 1) / 2) * (Nat.log 2 4 + 2) * (4 - 2) = 48 := by decide
    rw [hT] at hH hC hF'
    rw [hR] at hC
    rw [show ((2 * 4 : ℕ) : ENNReal) = 8 by norm_num] at hF'
    exact ⟨q, hH, hC, hF'⟩

/-- Boundary check on the zero-weight 3-vertex multigraph (`totalDoubledWeight = 0`): halts without
faulting and outputs `0` on every branch. -/
theorem kargerSingleTrial_zero :
    ∃ p : Program 16,
      let zeroW : Fin 3 → Fin 3 → ℕ := fun _ _ => 0
      let input := 3 :: flattenMatrix zeroW
      HaltsWithin 16 p (init input) 435 ∧
      (∀ cfg ∈ (evalRand 16 p 435 (init input)).support,
        ∃ reg mem, cfg = .halted 0 reg mem) := by
  obtain ⟨p, hp⟩ := kargerSingleTrial
  let zeroW : Fin 3 → Fin 3 → ℕ := fun _ _ => 0
  have hmg : IsMultigraph zeroW := ⟨fun _ _ => rfl, fun _ => rfl⟩
  obtain ⟨hH, -, hP, -⟩ := hp 3 16 zeroW (by decide) hmg (by decide) (by decide)
  have hT : 42 * 3 ^ 2 + 12 * 3 + 21 = 435 := by decide
  refine ⟨p, by simpa [hT] using hH, fun cfg hcfg => ?_⟩
  rw [← hT] at hcfg
  obtain ⟨reg, mem, C, rfl, -⟩ := hP cfg hcfg
  have hcw : cutWeight zeroW C = 0 := by simp [cutWeight, zeroW]
  exact ⟨reg, mem, by rw [hcw]⟩

/-- Weighted 8-vertex barbell: two `K_4` cliques `{0, 1, 2, 3}` and `{4, 5, 6, 7}` of edge weight
`10`, joined by unit-weight bridge edges `{0, 7}` and `{3, 4}` (`minCut = 2`). -/
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
  have hrow : ∀ u : Fin 8, ∑ v : Fin 8, barbell8W u v ≤ 80 := fun u => by
    calc
      ∑ v : Fin 8, barbell8W u v ≤ ∑ _v : Fin 8, 10 := Finset.sum_le_sum fun v _ => hentry u v
      _ = 80 := by simp
  have htot : totalDoubledWeight barbell8W ≤ 640 := by
    unfold totalDoubledWeight
    calc
      ∑ u : Fin 8, ∑ v : Fin 8, barbell8W u v ≤ ∑ _u : Fin 8, 80 :=
        Finset.sum_le_sum fun u _ => hrow u
      _ = 640 := by simp
  omega

theorem minCut_barbell8W : minCut barbell8W = 2 := by
  let L : Finset (Fin 8) := Finset.univ.filter (fun u : Fin 8 => u.val < 4)
  have hntL : IsNonTrivialCut L := by
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
  have hcwL : cutWeight barbell8W L = 2 := by
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
  unfold minCut
  apply le_antisymm
  · exact Nat.sInf_le ⟨L, hntL, hcwL⟩
  · obtain ⟨C, hC, hcw⟩ :=
      Nat.sInf_mem (s := {k | ∃ C : Finset (Fin 8), IsNonTrivialCut C ∧ cutWeight barbell8W C = k})
        ⟨2, L, hntL, hcwL⟩
    rw [← hcw]
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
          have hR_out : ∀ v : Fin 8, 4 ≤ v.val → v ∉ C := fun v hv hvC =>
            hsplitR ⟨v, v₀, hv, hv₀_ge, hvC, hv₀⟩
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

/-- Non-vacuous instantiation of `kargerSteinFastCut` and `kargerSteinHighProb` on `barbell8W`
(`n = 8, minCut = 2`) at the tight word-width boundary `w = 16`. -/
theorem kargerStein_barbell8 :
    (∃ p : Program 24,
      HaltsWithin 16 p (init (8 :: flattenMatrix barbell8W)) 800000 ∧
      RandCallsBounded 16 p (init (8 :: flattenMatrix barbell8W)) 800000 384 ∧
      (∀ cfg ∈ (evalRand 16 p 800000 (init (8 :: flattenMatrix barbell8W))).support,
        ∃ reg mem C,
          cfg = .halted (cutWeight barbell8W C) reg mem ∧
          2 ≤ cutWeight barbell8W C ∧
          mem 0 = 65 ∧ mem 1 = 8 ∧ mem 3 = 10 ∧ mem 1730 = 0) ∧
      (1 : ENNReal) / 18 ≤
        (evalRand 16 p 800000 (init (8 :: flattenMatrix barbell8W))).toOuterMeasure
          {cfg | ∃ reg mem, cfg = .halted 2 reg mem}) ∧
    (∃ q : Program 24,
      HaltsWithin 16 q (init (8 :: flattenMatrix barbell8W)) 74880000 ∧
      RandCallsBounded 16 q (init (8 :: flattenMatrix barbell8W)) 74880000 34560 ∧
      (evalRand 16 q 74880000 (init (8 :: flattenMatrix barbell8W))).toOuterMeasure
          {cfg | ∀ reg mem, cfg ≠ .halted 2 reg mem} ≤
        (1 : ENNReal) / 16) := by
  have hw : 4 * (Nat.log 2 8 + 1) ≤ 16 := by decide
  have htot : totalDoubledWeight barbell8W < 2 ^ 16 := totalDoubledWeight_barbell8W_lt
  constructor
  · obtain ⟨p, hp⟩ := kargerSteinFastCut
    obtain ⟨hH, hC, hP, hProb⟩ := hp 8 16 barbell8W (by decide) isMultigraph_barbell8W hw htot
    rw [minCut_barbell8W] at hP hProb
    have hProb' := hProb (by decide)
    have hT : 2500 * 8 ^ 2 * (Nat.log 2 8 + 2) = 800000 := by decide
    have hR : 6 * (8 * 8) = 384 := by decide
    rw [hT] at hH hC hProb'
    rw [hR] at hC
    rw [show ((Nat.log 2 8 + 15 : ℕ) : ENNReal) = 18 by
      rw [show Nat.log 2 8 + 15 = 18 by decide]; norm_num] at hProb'
    refine ⟨p, hH, hC, fun cfg hcfg => ?_, hProb'⟩
    rw [← hT] at hcfg
    obtain ⟨reg, mem, C, rfl, -, -, -, hge, hframe⟩ := hP cfg hcfg
    have hm0 : mem 0 = 65 := (hframe 0 (Or.inl (by decide))).trans (by decide)
    have hm1 : mem 1 = 8 := (hframe 1 (Or.inl (by decide))).trans (by decide)
    have hm3 : mem 3 = 10 := (hframe 3 (Or.inl (by decide))).trans (by decide)
    have hm1730 : mem 1730 = 0 := (hframe 1730 (Or.inr (by decide))).trans (by decide)
    exact ⟨reg, mem, C, rfl, hge, hm0, hm1, hm3, hm1730⟩
  · obtain ⟨q, hq⟩ := kargerSteinHighProb
    obtain ⟨hH, hC, -, hFail⟩ := hq 8 16 barbell8W (by decide) isMultigraph_barbell8W hw htot
    rw [minCut_barbell8W] at hFail
    have hFail' := hFail (by decide)
    have hT : 2600 * 8 ^ 2 * (Nat.log 2 8 + 15) * (Nat.log 2 8 + 2) ^ 2 = 74880000 := by decide
    have hR : (Nat.log 2 8 + 15) * (Nat.log 2 8 + 2) * (6 * (8 * 8)) = 34560 := by decide
    rw [hT] at hH hC hFail'
    rw [hR] at hC
    rw [show ((2 * 8 : ℕ) : ENNReal) = 16 by norm_num] at hFail'
    exact ⟨q, hH, hC, hFail'⟩

end ComplexityTests.Abstracts.KargerMinCutTests
