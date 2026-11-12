/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Lyubashevsky
public import CslibFrontier.Probability.HashFamily.IntegerBox
import CslibFrontier.Probability.StatisticalDistance.TotalVariation
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.UniformBound
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Option.Bind

/-!
# Average-key cache-hit bounds for box commitments

The matrix is sampled uniformly, then an arbitrary history depending on it is sampled before
the fresh mask. The history may select a message, cache and commitment shift. Bounds average
over that entire experiment; they do not condition on a realized history or public matrix.

## Main results

* `lyubashevsky_commit_lookup_le`: cache-hit bound for every attempted honest commitment.
* `lyubashevskySimulate_lookup_le`: the existing simulator's published-commitment bound,
  multiplied by its exact acceptance probability.

These original finite-probability bounds use ideal uniform sampling and prime moduli. They do
not give a native sampler, a full signing simulation, a paired-fork law or EUF-CMA security.
-/

public section

namespace Cslib.Crypto.Protocols.SigmaProtocol

open Probability Probability.PMF
open scoped _root_.Matrix ENNReal NNReal Cslib.Probability.PMF

private theorem uniform_shift_lookup_le {M D : Type} [DecidableEq M] {n q : ℕ} [NeZero q]
    (msg : M) (cache : List ((M × (Fin n → ZMod q)) × D)) (shift : Fin n → ZMod q) :
    ((PMF.uniformOfFintype (Fin n → ZMod q)).map
      (fun w => (cache.lookup (msg, w - shift)).isSome)) true ≤
      cache.length / (q : ℝ≥0∞) ^ n := by
  classical
  let targets := cache.map (fun p => p.1.2 + shift)
  have h := toOuterMeasure_uniformOfFintype_mem_list_le targets
  have hsub : {w : Fin n → ZMod q | (cache.lookup (msg, w - shift)).isSome} ⊆
      {w | w ∈ targets} := by
    intro w hw
    obtain ⟨p, hp, he⟩ := List.lookup_isSome_iff.mp hw
    have heq : (msg, w - shift) = p.1 := eq_of_beq he
    exact List.mem_map.mpr ⟨p, hp, (sub_eq_iff_eq_add.mp (congrArg Prod.snd heq)).symm⟩
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  exact ((PMF.uniformOfFintype (Fin n → ZMod q)).toOuterMeasure.mono hsub).trans (by
    simpa [targets, Fintype.card_fun, div_eq_mul_inv] using h)

private theorem intBox_shift_lookup_le {Ω M D : Type} [DecidableEq M]
    (n m q r Q : ℕ) [Fact q.Prime] (hr : 2 * r < q)
    (H : Matrix (Fin n) (Fin m) (ZMod q) → PMF Ω) (msg : Ω → M)
    (cache : Ω → List ((M × (Fin n → ZMod q)) × D))
    (shift : Matrix (Fin n) (Fin m) (ZMod q) → Ω → Fin n → ZMod q)
    (hcache : ∀ A h, h ∈ (H A).support → (cache h).length ≤ Q) :
    (do
      let A ← PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))
      let h ← H A
      let y ← uniformOfFinset (intBox (Fin m) r) (intBox_nonempty r)
      return (cache h).lookup (msg h, A *ᵥ (Int.cast ∘ y) - shift A h) |>.isSome) true ≤
        Q / (q : ℝ≥0∞) ^ n +
          ENNReal.ofReal (Real.sqrt ((q : ℝ) ^ n / ((2 * r + 1 : ℕ) : ℝ) ^ m) / 2) := by
  classical
  let real := (PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))).bind fun A =>
    (uniformOfFinset (intBox (Fin m) r) (intBox_nonempty r)).map
      (fun y => (A, A *ᵥ (Int.cast ∘ y)))
  let ideal := (PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))).bind fun A =>
    (PMF.uniformOfFintype (Fin n → ZMod q)).map (A, ·)
  let test := fun aw : Matrix (Fin n) (Fin m) (ZMod q) × (Fin n → ZMod q) =>
    (H aw.1).map (fun h => (cache h).lookup (msg h, aw.2 - shift aw.1 h) |>.isSome)
  have hc : CloseTo real ideal
      (ENNReal.ofReal (Real.sqrt ((q : ℝ) ^ n / ((2 * r + 1 : ℕ) : ℝ) ^ m) / 2)) :=
    closeTo_of_dist_le_ofReal (dist_intBox_mulVec_le n m q r hr)
  have hreal : real.bind test = (do
      let A ← PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))
      let h ← H A
      let y ← uniformOfFinset (intBox (Fin m) r) (intBox_nonempty r)
      return (cache h).lookup (msg h, A *ᵥ (Int.cast ∘ y) - shift A h) |>.isSome) := by
    simp only [pmf_norm, real, test, PMF.map]
    congr 1 with A : 1
    exact PMF.bind_comm _ _ _
  have hideal : ideal.bind test = (do
      let A ← PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))
      let h ← H A
      let w ← PMF.uniformOfFintype (Fin n → ZMod q)
      return (cache h).lookup (msg h, w - shift A h) |>.isSome) := by
    simp only [pmf_norm, ideal, test, PMF.map]
    congr 1 with A : 1
    exact PMF.bind_comm _ _ _
  have hi : (ideal.bind test) true ≤ Q / (q : ℝ≥0∞) ^ n := by
    rw [hideal]
    apply bind_apply_le_on_support
    intro A _
    apply bind_apply_le_on_support
    intro h hh
    exact (uniform_shift_lookup_le (msg h) (cache h) (shift A h)).trans (by
      gcongr
      exact_mod_cast hcache A h hh)
  have h := (hc.bind_left test) {true}
  rw [PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_apply_singleton, hreal] at h
  exact h.trans (add_le_add hi le_rfl)

/-- A fresh honest commitment hits a previously chosen cache with this average-key bound.
The event includes attempts whose later response aborts. The history may depend arbitrarily on
the public matrix, but it is sampled before the fresh commitment coins. -/
theorem lyubashevsky_commit_lookup_le {Ω M D : Type} [DecidableEq M]
    (n m k q γ β Q : ℕ) [Fact q.Prime] (hγ : 2 * γ < q)
    (H : Matrix (Fin n) (Fin m) (ZMod q) → PMF Ω)
    (S : Ω → Matrix (Fin m) (Fin k) ℤ)
    (T : Matrix (Fin n) (Fin m) (ZMod q) → Ω → Matrix (Fin n) (Fin k) (ZMod q))
    (msg : Ω → M) (cache : Ω → List ((M × (Fin n → ZMod q)) × D))
    (hcache : ∀ A h, h ∈ (H A).support → (cache h).length ≤ Q) :
    (do
      let A ← PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))
      let h ← H A
      let view ← (lyubashevsky n m k q γ β).commit (S h) (A, T A h)
      return (cache h).lookup (msg h, view.1) |>.isSome) true ≤
        Q / (q : ℝ≥0∞) ^ n +
          ENNReal.ofReal (Real.sqrt ((q : ℝ) ^ n / ((2 * γ + 1 : ℕ) : ℝ) ^ m) / 2) := by
  simpa only [pmf_norm, lyubashevsky, sub_zero] using
      intBox_shift_lookup_le n m q γ Q hγ H msg cache (fun _ _ => 0) hcache

/-- The existing simulator's published commitment hits a cache with the exact acceptance factor
times the inner-box bound. `none` contributes no published commitment. This does not justify
removing attempted queries from a real aborting signer's cache. -/
theorem lyubashevskySimulate_lookup_le {Ω M D : Type} [DecidableEq M]
    (n m k q γ β Q : ℕ) [Fact q.Prime] (hβ : β ≤ γ) (hγ : 2 * (γ - β) < q)
    (H : Matrix (Fin n) (Fin m) (ZMod q) → PMF Ω)
    (T : Matrix (Fin n) (Fin m) (ZMod q) → Ω → Matrix (Fin n) (Fin k) (ZMod q))
    (challenge : Ω → BitString k) (msg : Ω → M)
    (cache : Ω → List ((M × (Fin n → ZMod q)) × D))
    (hcache : ∀ A h, h ∈ (H A).support → (cache h).length ≤ Q) :
    (do
      let A ← PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))
      let h ← H A
      let view ← lyubashevskySimulate n m k q γ β (A, T A h) (challenge h)
      return view.any (fun wz : (Fin n → ZMod q) × (Fin m → ℤ) =>
        (cache h).lookup (msg h, wz.1) |>.isSome)) true ≤
        ((2 * (γ - β) + 1 : ℕ) / (2 * γ + 1 : ℝ≥0∞)) ^ m *
          (Q / (q : ℝ≥0∞) ^ n + ENNReal.ofReal
            (Real.sqrt ((q : ℝ) ^ n / ((2 * (γ - β) + 1 : ℕ) : ℝ) ^ m) / 2)) := by
  classical
  let mass : ℝ≥0∞ := ((2 * (γ - β) + 1 : ℕ) / (2 * γ + 1 : ℝ≥0∞)) ^ m
  let shift := fun A h => T A h *ᵥ (Int.cast ∘ lyubashevskyChallenge (challenge h))
  let inner := uniformOfFinset (intBox (Fin m) (γ - β)) (intBox_nonempty (γ - β))
  have hpoint (A : Matrix (Fin n) (Fin m) (ZMod q)) (h : Ω) :
      ((lyubashevskySimulate n m k q γ β (A, T A h) (challenge h)).map
        (fun view => view.any (fun wz => (cache h).lookup (msg h, wz.1) |>.isSome))) true =
      mass * (inner.map (fun z =>
        (cache h).lookup (msg h, A *ᵥ (Int.cast ∘ z) - shift A h) |>.isSome)) true := by
    rw [lyubashevskySimulate, PMF.map_comp]
    change ((boxReject (Fin m) γ β 0).bind _) true = _
    rw [bind_option_apply_of_some (boxReject (Fin m) γ β 0) inner mass (fun z => by
      simpa only [mass, inner, Fintype.card_fin] using
        boxReject_apply_some hβ (zero_mem_intBox β) z)]
    simp [PMF.map, shift]
  have hfactor :
      ((PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))).bind fun A =>
        (H A).bind fun h =>
          (lyubashevskySimulate n m k q γ β (A, T A h) (challenge h)).map
            (fun view => view.any (fun wz => (cache h).lookup (msg h, wz.1) |>.isSome))) true =
      mass * ((PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))).bind fun A =>
        (H A).bind fun h => inner.map (fun z =>
          (cache h).lookup (msg h, A *ᵥ (Int.cast ∘ z) - shift A h) |>.isSome)) true := by
    simp only [PMF.bind_apply, hpoint]
    simp_rw [mul_left_comm _ mass, ← ENNReal.tsum_mul_left]
    simp only [mul_left_comm]
  calc
    _ = mass * (do
        let A ← PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))
        let h ← H A
        let z ← inner
        return (cache h).lookup (msg h, A *ᵥ (Int.cast ∘ z) - shift A h) |>.isSome) true := hfactor
    _ ≤ _ := by
      gcongr
      exact intBox_shift_lookup_le n m q (γ - β) Q hγ H msg cache shift hcache

end Cslib.Crypto.Protocols.SigmaProtocol
