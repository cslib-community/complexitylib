/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Analysis.RowCompression.Decoder
public import Complexity.Foundations.Analysis.RowCompression.FalseOverflow
public import Complexity.Foundations.Analysis.RowCompression.Stationary
import Complexity.Foundations.Analysis.RowCompression.PreloadedIteration

/-!
# Sharp comparison for saturated decoders

The stationary comparison charges only errors after executed increments. The final
common-loss coefficient is independent of the later dyadic floor. The displayed stationary
coefficient grows as the inverse floor scale; its weighted error sum must still be paid.
These deterministic comparisons impose no error hypothesis on prefix zero and allow a zero
initial row against nonzero truth. They do not derive errors from recursive evaluations.
-/

public section
universe u
namespace Cslib.RowCompression
open Finset
open scoped BigOperators

/-- The stationary coefficient has an inverse-δ term. In particular, reducing δ
alone does not prove that the weighted prefix contribution tends to zero. -/
lemma stationary_decoder_coefficient {δ : ℝ} (hδ : δ ≠ 0) (L : ℝ) :
    3 * L * (12 * (1 + δ / 2) / (δ / 2)) = 36 * L + 72 * L / δ := by
  field_simp
  ring

/-- The floor's factor δ cancels the inverse-δ coefficient. This exact scheduled
coefficient need not vanish as δ decreases; callers must pay the weighted errors. -/
lemma stationary_decoder_floor_coefficient {δ : ℝ} (hδ : δ ≠ 0) (L : ℝ) (m i : ℕ) :
    (3 * L * (12 * (1 + δ / 2) / (δ / 2))) * dyadicFloor δ m i =
      (36 * L * δ + 72 * L) * (1 / 1024 : ℝ) ^ dyadicSlack m i := by
  rw [stationary_decoder_coefficient hδ]
  dsimp only [dyadicFloor]
  field_simp

/-- Explicit stationary coefficient for a root-Lipschitz decoder, flat below the floor.
Only post-increment errors on truth entries at least half the floor are charged. -/
theorem stationary_decoder_bound (H : ℝ → ℝ → ℝ → ℝ) {L δ : ℝ}
    (hL : 0 ≤ L) (hδ : 0 < δ)
    (hentry : ∀ d v r, d ≤ δ → H d v r = 0)
    (hflat : ∀ d v q r, q ≤ δ → r ≤ δ → H d v q = H d v r)
    (hroot : ∀ d v r d' v' r',
      |H d v r ^ (4⁻¹ : ℝ) - H d' v' r' ^ (4⁻¹ : ℝ)| ≤
        L * (|d - d'| + |v - v'| + |r - r'|))
    {K : ℕ} (hK : 0 < K) {ι : Type*} (s : Finset ι) (n : ℕ → ℕ)
    (Δ : ℕ → ι → Fin 2 → ℝ) (raw truth : ι → Fin 2 → ℝ) (m j : ℕ) (hj : j ≤ m)
    (hno : ∀ i < j, stepThreshold s n (fun _ => K) (dyadicFloor δ m) Δ ⟨0, raw⟩ i ≤
      dyadicFloor δ m i) (ε : ℕ → ℝ) (hε : ∀ i < j, 0 ≤ ε i)
    (herr : ∀ i < j, ∀ y ∈ s, δ / 2 ≤ truth y 0 →
      clippedError (truth y 0) (truth y 1) (uncompressedRow Δ raw (i + 1) y) ≤ ε i)
    (y : ι) (hy : y ∈ s) :
    |stateRootError H s K
      (stationaryState s n (fun _ => K) (dyadicFloor δ m) Δ ⟨0, raw⟩ truth j)
      ⟨0, truth⟩ y| ≤
      (3 * L * (12 * (1 + δ / 2) / (δ / 2))) *
        ∑ i ∈ range j, dyadicFloor δ m i * ε i := by
  have h := abs_stationaryState_root_sub_le_weighted_dyadic
    (H := H) (p := (4⁻¹ : ℝ)) (C := L) hδ hK hL (by norm_num : (0 : ℝ) ≤ 0)
    (by linarith : (0 : ℝ) ≤ δ / 2) m j hj hno hε herr hentry
    (fun d v q r hq hr => hflat d v q r hq.2 hr.2)
    (fun d v r d' v' r' _ _ _ _ => hroot d v r d' v' r') y hy
  simpa only [stateRootError, mul_assoc] using h

/-- Sharp no-overflow comparison with explicit coefficients. The final coefficient
`4 R + L (2 (4 T + 5) + 1)` precedes δ, the schedule and all input rows.
There is no initial-prefix error charge, even for `raw = 0` and nonzero truth. -/
theorem sharp_noOverflow_decoder_bound (H : ℝ → ℝ → ℝ → ℝ) {T R L : ℝ}
    (hT : 0 < T) (hR : 0 ≤ R) (hL : 0 ≤ L)
    (hsat : ∀ d v r, H d v r = H (min T d) v (min T r))
    (hrange : ∀ d v r, 0 ≤ H d v r ^ (4⁻¹ : ℝ) ∧ H d v r ^ (4⁻¹ : ℝ) ≤ R)
    (hroot : ∀ d v r d' v' r',
      |H d v r ^ (4⁻¹ : ℝ) - H d' v' r' ^ (4⁻¹ : ℝ)| ≤
        L * (|d - d'| + |v - v'| + |r - r'|))
    {K : ℕ} (hK : 0 < K) {δ : ℝ} (hδ : 0 < δ) (hδT : δ / 100 ≤ T)
    (hentry : ∀ d v r, d ≤ δ → H d v r = 0)
    (hflat : ∀ d v q r, q ≤ δ → r ≤ δ → H d v q = H d v r)
    {ι : Type*} (s : Finset ι) (n : ℕ → ℕ) (Δ : ℕ → ι → Fin 2 → ℝ)
    (raw truth : ι → Fin 2 → ℝ) (m : ℕ)
    (hno : ∀ i < m, stepThreshold s n (fun _ => K) (dyadicFloor δ m) Δ ⟨0, raw⟩ i ≤
      dyadicFloor δ m i) (hfirst : ∀ y ∈ s, 0 ≤ truth y 0)
    (ε : ℕ → ℝ) (hε : ∀ i < m, 0 ≤ ε i)
    (herr : ∀ i < m, ∀ y ∈ s, δ / 2 ≤ truth y 0 →
      clippedError (truth y 0) (truth y 1) (uncompressedRow Δ raw (i + 1) y) ≤ ε i)
    (εfinal : ℝ) (hεfinal : 0 ≤ εfinal)
    (herrfinal : ∀ y ∈ s,
      clippedError (truth y 0) (truth y 1) (uncompressedRow Δ raw m y) ≤ εfinal)
    (y : ι) (hy : y ∈ s) :
    |stateRootError H s K (iterate s n (fun _ => K) (dyadicFloor δ m) Δ ⟨0, raw⟩ m)
      ⟨0, truth⟩ y| ≤
      (3 * L * (12 * (1 + δ / 2) / (δ / 2))) *
        ∑ i ∈ range m, dyadicFloor δ m i * ε i +
      (4 * R + L * (2 * (4 * T + 5) + 1)) * εfinal := by
  let actual := iterate s n (fun _ => K) (dyadicFloor δ m) Δ ⟨0, raw⟩ m
  let r := uncompressedRow Δ raw m
  let loss := fun y ν => actual.row y ν - r y ν
  let ref := stationaryState s n (fun _ => K) (dyadicFloor δ m) Δ ⟨0, raw⟩ truth m
  have hr : r + loss = actual.row := by funext y ν; simp [loss]
  have hloss (x : ι) (_hx : x ∈ s) : |loss x 0| ≤ T := by
    have h := abs_stationaryState_row_sub_le_dyadic (s := s) (n := n)
      (K := fun _ => K) (Δ := Δ) (a := ⟨0, raw⟩) (truth := truth)
      hδ.le m m le_rfl hno x 0
    rw [stationaryState_row_sub] at h
    exact h.trans hδT
  have hact := boundedLoss_decoder_bound H hT hR hsat hrange hL hroot hK
    s actual.defaultValue truth r loss hfirst hloss εfinal hεfinal herrfinal y hy
  rw [hr] at hact
  change |stateRootError H s K actual ref y| ≤ _ at hact
  have href := stationary_decoder_bound H hL hδ hentry hflat hroot hK
    s n Δ raw truth m m le_rfl hno ε hε herr y hy
  change |stateRootError H s K ref ⟨0, truth⟩ y| ≤ _ at href
  calc
    _ ≤ |stateRootError H s K actual ref y| +
      |stateRootError H s K ref ⟨0, truth⟩ y| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add hact href
    _ = _ := add_comm _ _

/-- Preloaded first-overflow comparison for any saturated decoder. The coefficient
is independent of the later floor δ. Local prefix zero is the already-added overflow input,
so no error at the initial global prefix is charged. -/
theorem firstOverflow_decoder_bound (H : ℝ → ℝ → ℝ → ℝ) {T R L scale : ℝ}
    (hT : 0 < T) (hR : 0 ≤ R) (hL : 0 ≤ L)
    (hsat : ∀ d d' v r, T ≤ d → T ≤ d' → H d v r = H d' v r)
    (hrange : ∀ d v r, 0 ≤ H d v r ^ (4⁻¹ : ℝ) ∧ H d v r ^ (4⁻¹ : ℝ) ≤ R)
    (hroot : ∀ d v r d' v' r',
      |H d v r ^ (4⁻¹ : ℝ) - H d' v' r' ^ (4⁻¹ : ℝ)| ≤
        L * (|d - d'| + |v - v'| + |r - r'|))
    (hgate : ∀ d v r, T ≤ r → H d v r = 0)
    {K : ℕ} (hK : 0 < K) (hs : 0 < scale) (hscale : scale ≤ T / 10000) :
    ∀ {ι : Type u} (s : Finset ι) (n : ℕ → ℕ)
      (Δ : ℕ → ι → Fin 2 → ℝ) (raw truth : ι → Fin 2 → ℝ) (δ : ℝ),
      0 < δ → δ ≤ scale → ∀ m j : ℕ, j < m →
      IsFirstOverflow s n (fun _ => K) (dyadicFloor δ m) Δ ⟨0, raw⟩ j →
      (∀ y ∈ s, 0 ≤ truth y 0) →
      (∀ y ∈ s, |truth y 1| ≤ scale / 2) →
      (∀ i, j ≤ i → i < m → K ≤ n i) →
      ∀ ε : ℕ → ℝ, (∀ i, j ≤ i → i < m → 0 ≤ ε i) →
      (∀ i, j ≤ i → i < m → ∀ y ∈ s,
        clippedError (truth y 0) (truth y 1) (uncompressedRow Δ raw (i + 1) y) ≤ ε i) →
      ∀ y ∈ s, |stateRootError (H) s K
        (iterate s n (fun _ => K) (dyadicFloor δ m) Δ ⟨0, raw⟩ m)
        (stationaryContinuation s n K (dyadicFloor δ m) Δ ⟨0, raw⟩ truth j (m - j)) y| ≤
        (4 * ((8 * R + 3 * L) * (1 + 16 * (16 * (T + 1) + 1)))) *
          ∑ i ∈ Ico j m, 28^(m - i) * ε i := by
  let C := (8 * R + 3 * L) * (1 + 16 * (16 * (T + 1) + 1))
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hrange' {ι : Type u} (s : Finset ι) (K : ℕ) (a b : State ι) (y : ι) :
      |stateRootError H s K a b y| ≤ R := by
    have ha := hrange (a.row y 0) (a.row y 1) (firstRank s K a.defaultValue a.row)
    have hb := hrange (b.row y 0) (b.row y 1) (firstRank s K b.defaultValue b.row)
    exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  intro ι s n Δ raw truth δ hδ hδs m j hj hover hfirst hsecond hn ε hε herr y hy
  have hbound := iterate_root_bound H hsat R hR @hrange' hgate hT hL hroot (ι := ι)
  let ρ := dyadicFloor δ m
  let run := iterate s n (fun _ => K) ρ Δ ⟨0, raw⟩
  let raw₀ := uncompressedRow Δ raw (j + 1)
  let loss := fun y ν => (run j).row y ν - uncompressedRow Δ raw j y ν
  let z := (run j).defaultValue
  have hr : 0 < m - j := Nat.sub_pos_of_lt hj
  have hjr : j + (m - j) = m := Nat.add_sub_of_le hj.le
  have hloss (y : ι) (_hy : y ∈ s) (ν : Fin 2) : |loss y ν| ≤ scale / 2 := by
    have h := abs_stationaryState_row_sub_le_dyadic (s := s) (n := n)
      (K := fun _ => K) (Δ := Δ) (a := ⟨0, raw⟩) (truth := truth)
      hδ.le m j hj.le hover.1 y ν
    rw [stationaryState_row_sub] at h
    change |loss y ν| ≤ δ / 100 at h
    linarith
  have hlocalε (i : ℕ) (hi : i ≤ m - j) : 0 ≤ preloadedError ε j i := by
    cases i with
    | zero => exact hε j le_rfl hj
    | succ i => exact hε (j + i) (Nat.le_add_right _ _) (by omega)
  have hlocalerr (i : ℕ) (hi : i ≤ m - j) (y : ι) (hy : y ∈ s) :
      clippedError (truth y 0) (truth y 1)
        (uncompressedRow (preloadedIncrement Δ j) raw₀ i y) ≤ preloadedError ε j i := by
    cases i with
    | zero =>
      simpa only [uncompressedRow_zero, preloadedError_zero, raw₀] using herr j le_rfl hj y hy
    | succ i =>
      dsimp only [raw₀]
      rw [uncompressedRow_preloadedIncrement j (Nat.succ_pos i), preloadedError_succ]
      simpa only [Nat.add_assoc] using herr (j + i) (Nat.le_add_right _ _) (by omega) y hy
  have hrow : raw₀ + loss = inputRow s n (fun _ => K) ρ Δ ⟨0, raw⟩ j := by
    funext y ν
    dsimp only [raw₀, loss, run, inputRow, Pi.add_apply]
    rw [uncompressedRow_succ]
    ring
  have hactual : iterate s (fun i => n (j + i)) (fun _ => K) (fun i => ρ (j + i))
      (preloadedIncrement Δ j) ⟨z, raw₀ + loss⟩ (m - j) = run m := by
    rw [hrow]
    simpa only [hjr] using iterate_preloadedIncrement (s := s) (n := n) (K := fun _ => K)
      (ρ := ρ) (Δ := Δ) (a := ⟨0, raw⟩) j hr
  have hz : z ≤ scale := by
    have h := stationaryState_defaultValue_le_dyadic (s := s) (n := n)
      (K := fun _ => K) (Δ := Δ) (a := ⟨0, raw⟩) (truth := truth)
      hδ.le (by norm_num) (by dsimp; positivity) m j hj.le hover.1
    exact h.trans hδs
  have hlocal := hbound s (fun i => n (j + i)) (fun i => ρ (j + i))
    (preloadedIncrement Δ j) truth raw₀ loss z scale K hs hscale hz hK (m - j) hr
    (fun i hi => hn (j + i) (Nat.le_add_right _ _) (by omega))
    (fun i _ => by have h := dyadicFloor_le_scale_div hδ.le m (j + i); dsimp only [ρ]; linarith)
    hfirst hsecond hloss (preloadedError ε j) hlocalε hlocalerr y hy
  rw [hactual] at hlocal
  have hbudget := prefixErrorBudget_preloadedError_le j hr
    (fun i hi => hε i (mem_Ico.mp hi).1 (by have := (mem_Ico.mp hi).2; omega))
  rw [hjr] at hbudget
  calc
    _ ≤ C * prefixErrorBudget (preloadedError ε j) (m - j) := hlocal
    _ ≤ C * (4*∑ i ∈ Ico j m, 28^(m - i) * ε i) := mul_le_mul_of_nonneg_left hbudget hC
    _ = _ := by ring


/-- The stationary decoder reference is preserved through the remaining zero-increment
schedule. Support and gate separation, rather than monotonicity, justify preservation. -/
theorem stationary_decoder_continuation (H : ℝ → ℝ → ℝ → ℝ) {scale e g : ℝ}
    (hs : 0 < scale) (hsg : scale < g) (hge : 3 * g < e)
    (hentry : ∀ d v r, d ≤ e → H d v r = 0)
    (hgate : ∀ d v r, g ≤ r → H d v r = 0)
    (hflat : ∀ d v q r, q ≤ scale → r ≤ scale → H d v q = H d v r)
    {K : ℕ} (hK : 0 < K) {ι : Type*} (s : Finset ι) (n : ℕ → ℕ)
    (Δ : ℕ → ι → Fin 2 → ℝ) (raw truth : ι → Fin 2 → ℝ)
    {δ : ℝ}
    (hδ : 0 < δ) (hδs : δ ≤ scale) (m j r : ℕ) (hr : j + r ≤ m)
    (hno : ∀ i < j, stepThreshold s n (fun _ => K) (dyadicFloor δ m) Δ ⟨0, raw⟩ i ≤
      dyadicFloor δ m i)
    (hfirst : ∀ y ∈ s, 0 ≤ truth y 0) (hsecond : ∀ y ∈ s, |truth y 1| ≤ scale / 2)
    (hn : ∀ i, j ≤ i → i < m → K ≤ n i) (y : ι) (hy : y ∈ s) :
    let b := stationaryState s n (fun _ => K) (dyadicFloor δ m) Δ ⟨0, raw⟩ truth j
    let c := stationaryContinuation s n K (dyadicFloor δ m) Δ ⟨0, raw⟩ truth j r
    H (c.row y 0) (c.row y 1) (firstRank s K
      c.defaultValue c.row) =
      H (b.row y 0) (b.row y 1) (firstRank s K
        b.defaultValue b.row) := by
  have hb (y : ι) (ν : Fin 2) := abs_stationaryState_row_sub_le_dyadic
    (s := s) (n := n) (K := fun _ => K) (Δ := Δ) (a := ⟨0, raw⟩) (truth := truth)
    hδ.le m j (by omega) hno y ν
  apply reference_iterate_output_eq (H := H) hs.le
    hK
    (fun y hy => by have hh := (abs_le.mp (hb y 0)).1; linarith [hfirst y hy])
    (fun y hy => by
      have hh := abs_le.mp (hb y 1)
      exact abs_le.mpr ⟨by linarith [(abs_le.mp (hsecond y hy)).1], by linarith [(abs_le.mp
        (hsecond y hy)).2]⟩)
    hsg hge
    hentry hgate
    (fun d v q r hq hr => hflat d v q r hq.2 hr.2) r
  · intro i hi; exact hn (j + i) (Nat.le_add_right _ _) (by omega)
  · intro i _; have h := dyadicFloor_le_scale_div hδ.le m (j + i); linarith
  · exact hy



open Classical in
/-- Assemble sharp no-overflow and first-overflow truth comparisons outside false events.
The event predicates may depend on the same inputs as the errors. -/
theorem sharp_compression_of_bounds (H : ℝ → ℝ → ℝ → ℝ) (K : ℕ)
    {scale η Cf Ct An At : ℝ} (hη : 0 < η)
    (hCf : 0 ≤ Cf) (hCt : 0 ≤ Ct) (_hAn : 0 ≤ An) (hAt : 0 ≤ At)
    (hn : ∀ {ι : Type u} (s : Finset ι) (n : ℕ → ℕ)
      (Δ : ℕ → ι → Fin 2 → ℝ) (raw truth : ι → Fin 2 → ℝ) (m : ℕ),
      (∀ i < m, stepThreshold s n (fun _ => K) (dyadicFloor η m) Δ ⟨0, raw⟩ i ≤ dyadicFloor η
        m i) →
      (∀ y ∈ s, 0 ≤ truth y 0) →
      ∀ ε : ℕ → ℝ, (∀ i < m, 0 ≤ ε i) →
      (∀ i < m, ∀ y ∈ s, η / 2 ≤ truth y 0 →
        clippedError (truth y 0) (truth y 1) (uncompressedRow Δ raw (i + 1) y) ≤ ε i) →
      ∀ εfinal : ℝ, 0 ≤ εfinal →
      (∀ y ∈ s, clippedError (truth y 0) (truth y 1) (uncompressedRow Δ raw m y) ≤ εfinal) →
        ∀ y ∈ s, |stateRootError H s K
        (iterate s n (fun _ => K) (dyadicFloor η m) Δ ⟨0, raw⟩ m) ⟨0, truth⟩ y| ≤
        An * ∑ i ∈ range m, dyadicFloor η m i * ε i + Cf * εfinal)
    (ht : ∀ {ι : Type u} (s : Finset ι) (n : ℕ → ℕ)
      (Δ : ℕ → ι → Fin 2 → ℝ) (raw truth : ι → Fin 2 → ℝ) (m j : ℕ), j < m →
      IsFirstOverflow s n (fun _ => K) (dyadicFloor η m) Δ ⟨0, raw⟩ j →
      (∀ y ∈ s, 0 ≤ truth y 0) →
      (∀ y ∈ s, |truth y 1| ≤ scale / 2) →
      (∀ i, j ≤ i → i < m → K ≤ n i) →
      ∀ ε : ℕ → ℝ, (∀ i < m, 0 ≤ ε i) →
      (∀ i < j, ∀ y ∈ s, η / 2 ≤ truth y 0 →
        clippedError (truth y 0) (truth y 1) (uncompressedRow Δ raw (i + 1) y) ≤ ε i) →
      (∀ i, j ≤ i → i < m → ∀ y ∈ s,
        clippedError (truth y 0) (truth y 1) (uncompressedRow Δ raw (i + 1) y) ≤ ε i) →
      ∀ y ∈ s, |stateRootError H s K
        (iterate s n (fun _ => K) (dyadicFloor η m) Δ ⟨0, raw⟩ m) ⟨0, truth⟩ y| ≤
        At*∑ i ∈ range j, dyadicFloor η m i * ε i + Ct*∑ i ∈ Ico j m, 28^(m - i) * ε i) :
    ∀ {ι : Type u} (S : Finset ι) (n : ℕ → ℕ)
        (Δ : ℕ → ι → Fin 2 → ℝ) (raw truth : ι → Fin 2 → ℝ)
        (m : ℕ) (heavy : ℕ → Prop),
        (∀ y ∈ S, 0 ≤ truth y 0) →
        (∀ y ∈ S, |truth y 1| ≤ scale / 2) →
        (∀ i < m, K ≤ n i) → ∀ (ε : ℕ → ℝ),
        (∀ i < m, 0 ≤ ε i) →
        (∀ i < m, ∀ y ∈ S,
          clippedError (truth y 0) (truth y 1) (uncompressedRow Δ raw (i + 1) y) ≤ ε i) →
        ∀ εfinal : ℝ, 0 ≤ εfinal →
        (∀ y ∈ S,
          clippedError (truth y 0) (truth y 1) (uncompressedRow Δ raw m y) ≤ εfinal) →
        (¬ ∃ j < m, IsFirstOverflow S n (fun _ => K) (dyadicFloor η m) Δ ⟨0, raw⟩ j ∧ ¬heavy j) →
        ∀ y ∈ S,
        |stateRootError H S K
          (iterate S n (fun _ => K) (dyadicFloor η m) Δ ⟨0, raw⟩ m) ⟨0, truth⟩ y| ≤
          (max An At) * (∑ i ∈ range m, dyadicFloor η m i * ε i) +
          (max Cf Ct) * (if ∀ i < m, stepThreshold S n (fun _ => K) (dyadicFloor η m) Δ ⟨0, raw⟩ i ≤
            dyadicFloor η m i then εfinal else 0) + (max Cf Ct) * (∑ j ∈ range m,
            if IsFirstOverflow S n (fun _ => K) (dyadicFloor η m) Δ ⟨0, raw⟩ j ∧ heavy j then
              ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * ε i else 0) := by
  classical
  intro ι S n Δ raw truth m heavy hfirst hsecond hcapacity ε hε herr
    εfinal hεfinal herrfinal hfalse y hy
  have hpre0 : 0 ≤ ∑ i ∈ range m, dyadicFloor η m i * ε i :=
    sum_nonneg fun i hi => mul_nonneg (dyadicFloor_nonneg hη.le _ _) (hε i (mem_range.mp hi))
  have htail0 : 0 ≤ ∑ j ∈ range m,
      if IsFirstOverflow S n (fun _ => K) (dyadicFloor η m) Δ ⟨0, raw⟩ j ∧ heavy j then
        ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * ε i else 0 := by
    refine sum_nonneg fun j _ => ?_
    split_ifs
    · exact sum_nonneg fun i hi => mul_nonneg (by positivity) (hε i (mem_Ico.mp hi).2)
    · exact le_rfl
  by_cases hnone : ∀ i < m, stepThreshold S n (fun _ => K) (dyadicFloor η m) Δ ⟨0, raw⟩ i ≤
      dyadicFloor η m i
  · rw [ite_eq_left hnone]
    have hbound := hn S n Δ raw truth m hnone hfirst ε hε
      (fun i hi z hz _ => herr i hi z hz) εfinal hεfinal herrfinal y hy
    have hp := mul_le_mul_of_nonneg_right (le_max_left An At) hpre0
    have hf := mul_le_mul_of_nonneg_right (le_max_left Cf Ct) hεfinal
    have htail := mul_nonneg (hCf.trans (le_max_left Cf Ct)) htail0
    linarith
  · have hex : ∃ j, j < m ∧ dyadicFloor η m j <
        stepThreshold S n (fun _ => K) (dyadicFloor η m) Δ ⟨0, raw⟩ j := by
      push Not at hnone
      exact hnone
    let j := Nat.find hex
    have hj := Nat.find_spec hex
    have hjm : j < m := hj.1
    have hjover : IsFirstOverflow S n (fun _ => K) (dyadicFloor η m) Δ ⟨0, raw⟩ j := by
      refine ⟨?_, hj.2⟩
      intro i hi
      exact le_of_not_gt fun h => Nat.find_min hex hi ⟨by omega, h⟩
    have hheavy : heavy j := by
      by_contra h
      exact hfalse ⟨j, hjm, hjover, h⟩
    have hbound := ht S n Δ raw truth m j hjm hjover hfirst hsecond
      (fun i _ hi => hcapacity i hi) ε hε
      (fun i hi z hz _ => herr i (hi.trans hjm) z hz)
      (fun i _ hi z hz => herr i hi z hz) y hy
    have hprefix : (∑ i ∈ range j, dyadicFloor η m i * ε i) ≤
        ∑ i ∈ range m, dyadicFloor η m i * ε i := by
      apply sum_le_sum_of_subset_of_nonneg (range_mono hjm.le)
      intro i hi _
      exact mul_nonneg (dyadicFloor_nonneg hη.le _ _) (hε i (mem_range.mp hi))
    have hselected : (∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * ε i) ≤
        ∑ j ∈ range m,
          if IsFirstOverflow S n (fun _ => K) (dyadicFloor η m) Δ ⟨0, raw⟩ j ∧ heavy j then
            ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * ε i else 0 := by
      have h := single_le_sum (s := range m)
        (f := fun j => if IsFirstOverflow S n (fun _ => K) (dyadicFloor η m) Δ ⟨0, raw⟩ j ∧
          heavy j then ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * ε i else 0)
        (fun i _ => by
          split_ifs
          · exact sum_nonneg fun z hz => mul_nonneg (by positivity) (hε z (mem_Ico.mp hz).2)
          · exact le_rfl) (mem_range.mpr hjm)
      simpa only [hjover, hheavy, and_self, ↓reduceIte] using h
    rw [ite_eq_right hnone, mul_zero, add_zero]
    have hp := (mul_le_mul_of_nonneg_left hprefix hAt).trans
      (mul_le_mul_of_nonneg_right (le_max_right An At) hpre0)
    have htail := (mul_le_mul_of_nonneg_left hselected hCt).trans
      (mul_le_mul_of_nonneg_right (le_max_right Cf Ct) htail0)
    linarith



end Cslib.RowCompression
