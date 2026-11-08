/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Protocols.SigmaProtocol.Lyubashevsky.Commitment
import Complexity.Probability.PMF.Uniform

/-!
# Average-key lattice commitment collision clients

The honest experiment uses modulus 17, one output row, eight mask coordinates and radius three.
Its cache-hit probability is positive and below 0.06. A supported zero matrix instead hits with
conditional probability one; a nonzero matrix also has positive hit probability. Empty caches,
zero inner radius and zero output dimension are checked separately.
-/

namespace ComplexityTests.Crypto.LyubashevskyCommitment

open Cslib.Probability Cslib.Probability.PMF Cslib.Crypto.Protocols.SigmaProtocol
open scoped Matrix ENNReal

instance : Fact (Nat.Prime 17) := ⟨by decide⟩

abbrev Mat := Matrix (Fin 1) (Fin 8) (ZMod 17)

def secret : Matrix (Fin 8) (Fin 1) ℤ := Matrix.of fun _ _ => 1

def publicPart (A : Mat) : Matrix (Fin 1) (Fin 1) (ZMod 17) := A * secret.map Int.cast

def cache : List ((Unit × (Fin 1 → ZMod 17)) × Bool) := [(((), 0), false)]

noncomputable def hitAt (A : Mat) : PMF Bool :=
  ((lyubashevsky 1 8 1 17 3 1).commit secret (A, publicPart A)).map
    (fun view => (cache.lookup ((), view.1)).isSome)

noncomputable def realHit : PMF Bool := do
  let A ← PMF.uniformOfFintype Mat
  hitAt A

theorem zero_matrix_hit : hitAt 0 = PMF.pure true := by
  simp only [hitAt, lyubashevsky, Matrix.zero_mulVec, PMF.map_comp, Function.comp_def,
    cache, List.lookup_cons_self, Option.isSome_some]
  exact PMF.map_const _ _

theorem hitAt_positive (A : Mat) : 0 < hitAt A true := by
  apply bot_lt_iff_ne_bot.mpr
  apply (PMF.mem_support_iff _ _).mp
  simp only [hitAt, lyubashevsky, PMF.map_comp, Function.comp_def]
  apply (PMF.mem_support_map_iff _ _ _).mpr
  refine ⟨0, (mem_support_uniformOfFinset_iff _ _).mpr (zero_mem_intBox 3), ?_⟩
  have hz : A *ᵥ (fun _ => (0 : ZMod 17)) = 0 := Matrix.mulVec_zero A
  simp only [Pi.zero_apply, Int.cast_zero, hz, cache, List.lookup_cons_self, Option.isSome_some]

theorem realHit_positive : 0 < realHit true := by
  apply bot_lt_iff_ne_bot.mpr
  apply (PMF.mem_support_iff _ _).mp
  change true ∈ ((PMF.uniformOfFintype Mat).bind hitAt).support
  apply (PMF.mem_support_bind_iff _ _ _).mpr
  refine ⟨0, mem_support_uniformOfFintype 0, ?_⟩
  rw [zero_matrix_hit]
  simp

def nonzeroMatrix : Mat := Matrix.of fun _ j => if j = 0 then 1 else 0

example : nonzeroMatrix ≠ 0 := by
  intro h
  have hentry := congrArg (fun A : Mat => A 0 0) h
  norm_num [nonzeroMatrix] at hentry

example : 0 < hitAt nonzeroMatrix true := hitAt_positive _

theorem realHit_le : (realHit true).toReal ≤ 3 / 50 := by
  have h := lyubashevsky_commit_lookup_le 1 8 1 17 3 1 1 (by decide)
    (fun _ => PMF.pure ()) (fun _ => secret) (fun A _ => publicPart A)
    (fun _ => ()) (fun _ => cache) (by intro A h hh; simp [cache])
  have hreal : realHit true ≤ (1 : ℝ≥0∞) / 17 +
      ENNReal.ofReal (Real.sqrt ((17 : ℝ) / 7 ^ 8) / 2) := by
    norm_num only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      PMF.pure_bind, Nat.reduceMul, Nat.reduceAdd, Nat.cast_ofNat, pow_one] at h
    simpa only [realHit, hitAt, PMF.map, PMF.monad_bind_eq_bind, Function.comp_def,
      show (7 : ℝ) ^ 8 = 5764801 by norm_num] using h
  have hs : Real.sqrt ((17 : ℝ) / 7 ^ 8) / 2 ≤ 1 / 1000 := by
    have ht : Real.sqrt ((17 : ℝ) / 7 ^ 8) ≤ 1 / 500 :=
      Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    linarith
  have hsmall : realHit true ≤ (1 : ℝ≥0∞) / 17 + ENNReal.ofReal (1 / 1000) :=
    hreal.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hs))
  have ht := ENNReal.toReal_mono (by finiteness) hsmall
  norm_num [ENNReal.toReal_add] at ht
  linarith

example :
    (do
      let A ← PMF.uniformOfFintype Mat
      let view ← (lyubashevsky 1 8 1 17 3 1).commit secret (A, publicPart A)
      return ([] : List ((Unit × (Fin 1 → ZMod 17)) × Bool)).lookup
        ((), view.1) |>.isSome) = PMF.pure false := by
  simp only [List.lookup_nil, Option.isSome_none, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.bind_const]

example :
    (do
      let A ← PMF.uniformOfFintype Mat
      let view ← lyubashevskySimulate 1 8 1 17 3 3 (A, publicPart A) (fun _ => true)
      return view.any (fun wz : (Fin 1 → ZMod 17) × (Fin 8 → ℤ) =>
        (cache.lookup ((), wz.1)).isSome)) true ≤
      ((1 : ℝ≥0∞) / 7) ^ 8 *
        (1 / 17 + ENNReal.ofReal (Real.sqrt (17 : ℝ) / 2)) := by
  have h := lyubashevskySimulate_lookup_le 1 8 1 17 3 3 1 (by decide) (by decide)
    (fun _ => PMF.pure ()) (fun A _ => publicPart A) (fun _ _ => true)
    (fun _ => ()) (fun _ => cache) (by intro A h hh; simp [cache])
  norm_num only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.pure_bind,
    Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd, Nat.cast_ofNat, pow_one, one_pow, div_one] at h
  exact h

-- The sampled history retains A and fresh public randomness. Both the cache target and the
-- simulator shift depend on that history; neither can depend on the later sampled response.
example :
    (do
      let A ← PMF.uniformOfFintype Mat
      let h ← (PMF.uniformOfFintype Bool).map (A, ·)
      let view ← lyubashevskySimulate 1 8 1 17 3 1
        (A, if h.2 then publicPart h.1 else 0) (fun _ => true)
      return view.any (fun wz : (Fin 1 → ZMod 17) × (Fin 8 → ℤ) =>
        ([((h.2, h.1 *ᵥ (fun _ => 1)), false)].lookup (h.2, wz.1)).isSome)) true ≤
      ((2 * (3 - 1) + 1 : ℕ) / (2 * 3 + 1 : ℝ≥0∞)) ^ 8 *
        (1 / (17 : ℝ≥0∞) ^ 1 + ENNReal.ofReal
          (Real.sqrt ((17 : ℝ) ^ 1 / ((2 * (3 - 1) + 1 : ℕ) : ℝ) ^ 8) / 2)) := by
  simpa only [Nat.cast_ofNat, Nat.cast_one] using
    lyubashevskySimulate_lookup_le 1 8 1 17 3 1 1 (by decide) (by decide)
    (fun A => (PMF.uniformOfFintype Bool).map (A, ·))
    (fun _ h => if h.2 then publicPart h.1 else 0) (fun _ _ => true) Prod.snd
    (fun h => [((h.2, h.1 *ᵥ (fun _ => 1)), false)]) (by intro A h hh; exact le_rfl)

example :
    (do
      let A ← PMF.uniformOfFintype (Matrix (Fin 0) (Fin 1) (ZMod 17))
      let view ← (lyubashevsky 0 1 1 17 3 1).commit 0 (A, 0)
      return ([(((), 0), false)] : List ((Unit × (Fin 0 → ZMod 17)) × Bool)).lookup
        ((), view.1) |>.isSome) = PMF.pure true := by
  have hw (w : Fin 0 → ZMod 17) : w = 0 := Subsingleton.elim _ _
  simp only [hw, List.lookup_cons_self, Option.isSome_some, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.bind_const]

end ComplexityTests.Crypto.LyubashevskyCommitment
