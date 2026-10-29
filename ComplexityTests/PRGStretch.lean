/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Stretch
import Complexity.Tactic.PPT

/-! Functional stretch, captured parameters, strict reductions and zero-count boundaries. -/

namespace ComplexityTests.PRGStretch

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM

-- A toy expander exercises seed retention and suffix order; no security is claimed for it.
private def expand (seed : List Bool) : List Bool := seed ++ [false]

example : PRGStretch.stretch expand (fun _ => 3) [true, false] =
    [true, false, false, false, false] := by decide

example : PRGStretch.stretch expand (fun _ => 2) [] = [false, false] := by decide

example (seed : List Bool) : PRGStretch.stretch expand (fun _ => 0) seed = seed := rfl

-- Efficiency works uniformly on arbitrary initial words, with the generator capturing a bit.
example : ComputableInPolyTime
    (fun p : (ℕ × Bool) × List Bool =>
      PRGStretch.iterate (fun seed => seed ++ [p.1.2]) p.1.1 (p.1.1 ^ 2 + 1) p.2)
    (encPair (encPair encUnary encBool) encBits) encBits := by polytime

-- The entire randomized hybrid test composes, including its captured randomized distinguisher.
example : IsPPTOn (encPair (encPair encUnary encBool) encBits) encBool
    (fun p : (ℕ × Bool) × List Bool =>
      PRGStretch.test (fun seed => seed ++ [p.1.2]) p.1.1 (p.1.1 ^ 2 + 1)
        (fun word => do
          let bit ← ProbComp.uniform Bool
          return bit && decide (word.length = p.1.1)) p.2) := by
  ppt

-- Zero hops still samples a fair bit, but every sampled branch rejects.
example (generator : List Bool → List Bool) (adversary : Distinguisher) (n : ℕ)
    (challenge : List Bool) :
    ProbComp.eval (PRGStretch.reduction generator (fun _ => 0) adversary n challenge) =
      PMF.pure false := by
  simp only [PRGStretch.reduction, PRGStretch.hop, Nat.not_lt_zero, ↓reduceIte,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_const]

-- Two hops use a four-element sampling range, including the padded rejecting outcomes.
example (generator : List Bool → List Bool) (adversary : Distinguisher) (n : ℕ) :
    Game.advantage
        (ProbComp.eval (prgRealGame (PRGStretch.stretch generator (fun _ => 2)) adversary n))
        (ProbComp.eval (prgIdealGame (fun n => n + 2) adversary n)) =
      4 * Game.advantage
        (ProbComp.eval
          (prgRealGame generator (PRGStretch.reduction generator (fun _ => 2) adversary) n))
        (ProbComp.eval (prgIdealGame (fun n => n + 1)
          (PRGStretch.reduction generator (fun _ => 2) adversary) n)) := by
  simpa only [show 2 ^ (Nat.log 2 2 + 1) = 4 by decide, Nat.cast_ofNat] using
    PRGStretch.advantage_eq generator (fun _ => 2) adversary n

-- A captured loop may add an input-dependent block at each iteration.
example : ComputableInPolyTime
    (fun word : List Bool => (fun state => state ++ word)^[word.length] []) encBits encBits := by
  apply ComputableInPolyTime.of_tidy
  apply ComputableTidilyInPolyTime.iterateWith_of_bounded_growth
    (par := id) (step := fun word state => state ++ word) (growth := List.length)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (by
      have h : ComputableInPolyTime id encBits encBits := by fun_prop
      simpa using h.polyBounded_length)
  intro word state
  simp

-- Arbitrary iteration is deliberately not inferred from the step's polynomial-time certificate.
example : True := by
  fail_if_success
    have : ComputableInPolyTime
        (fun word : List Bool => (fun state => state ++ state)^[word.length] [true])
        encBits encBits := by polytime
  trivial

/-! ### Quantitative cumulative-time, workspace and degree tests -/

private theorem length_expand (s : List Bool) : (expand s).length = s.length + 1 := by
  simp [expand]

-- Forward streaming representation emits bits in forward order followed by the reversed final seed,
-- and reversing it once recovers `PRGStretch.iterate` across zero rounds, empty seeds and
-- multi-round executions.
example : PRGStretch.forwardIterate expand 3 [true, false] =
    [false, false, false, false, true] := by decide

example : PRGStretch.forwardIterate expand 0 [true, false] = [false, true] := rfl

example : PRGStretch.forwardIterate expand 2 [] = [false, false] := by decide

example (seed : List Bool) (k : ℕ) :
    (PRGStretch.forwardIterate expand k seed).reverse =
      PRGStretch.iterate expand seed.length k seed :=
  PRGStretch.reverse_forwardIterate_eq_iterate_of_forall length_expand seed k

example (seed : List Bool) (k : ℕ) :
    (PRGStretch.forwardIterate expand k seed).length = seed.length + k :=
  PRGStretch.length_forwardIterate_of_forall length_expand seed k

example (seed : List Bool) (i : ℕ) :
    (PRGStretch.seedAt expand seed i).length = seed.length :=
  PRGStretch.length_seedAt_of_forall length_expand seed i

-- `expand` always emits `false`; `shiftIn` emits the last bit of its seed, so from
-- `[false, false, true]` its three rounds emit `true`, `false`, `false`, and the order of the
-- emitted bits is observable.
private def shiftIn (seed : List Bool) : List Bool := [true] ++ seed

private theorem length_shiftIn (s : List Bool) : (shiftIn s).length = s.length + 1 := by
  simp [shiftIn]

-- `forwardIterate` streams the emitted bits in generation order before the reversed final seed.
example : PRGStretch.forwardIterate shiftIn 3 [false, false, true] =
    [true, false, false, true, true, true] := by decide

-- `stretch` retains the final seed followed by the emitted bits in reverse generation order, not in
-- generation order.
example : PRGStretch.stretch shiftIn (fun _ => 3) [false, false, true] =
    [true, true, true, false, false, true] := by decide

example : PRGStretch.stretch shiftIn (fun _ => 3) [false, false, true] ≠
    [true, true, true, true, false, false] := by decide

example : (PRGStretch.forwardIterate shiftIn 3 [false, false, true]).reverse =
    PRGStretch.stretch shiftIn (fun _ => 3) [false, false, true] :=
  PRGStretch.reverse_forwardIterate_eq_iterate_of_forall length_shiftIn _ 3

private theorem expand_degree :
    ComputableInDegree expand encBits encBits 1 1 := by
  have hraw : ComputableTidilyInDegree expand encBits encBits 1 1 := by
    unfold expand
    fun_prop (disch := first | apply le_refl | lia)
  obtain ⟨⟨t, space, ht, hs, h⟩, hl⟩ := hraw
  exact ⟨⟨t, space, ht, hs, h.computableInTimeAndSpace⟩, hl⟩

private theorem shiftIn_degree :
    ComputableInDegree shiftIn encBits encBits 1 1 := by
  have hraw : ComputableTidilyInDegree shiftIn encBits encBits 1 1 := by
    unfold shiftIn
    fun_prop (disch := first | apply le_refl | lia)
  obtain ⟨⟨t, space, ht, hs, h⟩, hl⟩ := hraw
  exact ⟨⟨t, space, ht, hs, h.computableInTimeAndSpace⟩, hl⟩

-- Quantitative cumulative-time and round-independent workspace for `forwardIterate` on a concrete
-- length-expanding generator.
example : ∃ (tGen : List Bool → ℕ) (csG c : ℕ),
    ComputableInTimeAndSpace
      (fun p : List Bool × ℕ => PRGStretch.forwardIterate expand p.2 p.1)
      (encPair encBits encUnary) encBits
      (fun p => c * (p.1.length + p.2 +
        (∑ i ∈ Finset.range p.2, (tGen (PRGStretch.seedAt expand p.1 i) + p.1.length + 1)) + 1))
      (fun p => c * (csG * (p.1.length + 1) + p.1.length + 1)) := by
  obtain ⟨⟨tGen, sGen, _, ⟨csG, hcsG⟩, hgen⟩, -⟩ := expand_degree
  refine ⟨tGen, csG, ?_⟩
  exact PRGStretch.computableInTimeAndSpace_forwardIterate length_expand hgen
    (fun p i _ => by
      simpa [PRGStretch.length_seedAt_of_forall length_expand] using
        hcsG (PRGStretch.seedAt expand p.1 i))

-- Quantitative cumulative-time and workspace (charging the `(n + k)`-bit reversal buffer) for
-- `PRGStretch.iterate` on `(seed, count)`.
example : ∃ (tGen : List Bool → ℕ) (csG c : ℕ),
    ComputableInTimeAndSpace
      (fun p : List Bool × ℕ => PRGStretch.iterate expand p.1.length p.2 p.1)
      (encPair encBits encUnary) encBits
      (fun p => c * (p.1.length + p.2 +
        (∑ i ∈ Finset.range p.2, (tGen (PRGStretch.seedAt expand p.1 i) + p.1.length + 1)) + 1))
      (fun p => c * (csG * (p.1.length + 1) + p.1.length + p.2 + 1)) := by
  obtain ⟨⟨tGen, sGen, _, ⟨csG, hcsG⟩, hgen⟩, -⟩ := expand_degree
  refine ⟨tGen, csG, ?_⟩
  exact PRGStretch.computableInTimeAndSpace_iterate_pair length_expand hgen
    (fun p i _ => by
      simpa [PRGStretch.length_seedAt_of_forall length_expand] using
        hcsG (PRGStretch.seedAt expand p.1 i))

-- Quantitative cumulative-time and workspace for `PRGStretch.stretch` with a linear round count, on
-- the generator whose emitted bits vary.
example : ∃ (tGen : List Bool → ℕ) (tCount sCount : ℕ → ℕ) (csG c : ℕ),
    ComputableInTimeAndSpace (PRGStretch.stretch shiftIn (fun n => n + n + 1)) encBits encBits
      (fun seed => c * (tCount seed.length + seed.length + (seed.length + seed.length + 1) +
        (∑ i ∈ Finset.range (seed.length + seed.length + 1),
          (tGen (PRGStretch.seedAt shiftIn seed i) + seed.length + 1)) + 1))
      (fun seed => c * (sCount seed.length + csG * (seed.length + 1) + seed.length +
        (seed.length + seed.length + 1) + 1)) := by
  obtain ⟨⟨tGen, sGen, _, ⟨csG, hcsG⟩, hgen⟩, -⟩ := shiftIn_degree
  have hcount_deg : ComputableTidilyInDegree (fun n : ℕ => n + n + 1) encUnary encUnary 1 1 := by
    fun_prop (disch := first | apply le_refl | lia)
  obtain ⟨⟨tCount, sCount, _, _, hcount⟩, -⟩ := hcount_deg
  refine ⟨tGen, tCount, sCount, csG, ?_⟩
  exact PRGStretch.computableInTimeAndSpace_stretch length_shiftIn hgen
    hcount.computableInTimeAndSpace
    (fun seed i _ => by
      simpa [PRGStretch.length_seedAt_of_forall length_shiftIn] using
        hcsG (PRGStretch.seedAt shiftIn seed i))

-- Zero rounds through the quantitative certificate: the cumulative sum is empty and no generator
-- workspace is needed, so `stretch` costs `O(tCount n + n + 1)` time and `O(sCount n + n + 1)`
-- space.
example : ∃ (tCount sCount : ℕ → ℕ) (c : ℕ),
    ComputableInTimeAndSpace (PRGStretch.stretch shiftIn (fun _ => 0)) encBits encBits
      (fun seed => c * (tCount seed.length + seed.length + 1))
      (fun seed => c * (sCount seed.length + seed.length + 1)) := by
  obtain ⟨⟨tGen, sGen, _, _, hgen⟩, -⟩ := shiftIn_degree
  obtain ⟨⟨tCount, sCount, _, _, hcount⟩, -⟩ :=
    ComputableTidilyInDegree.const (encIn := encUnary) (encMid := encUnary) 0
  obtain ⟨c, h⟩ := PRGStretch.computableInTimeAndSpace_stretch length_shiftIn hgen
    hcount.computableInTimeAndSpace
    (Q := fun _ => 0) (fun _ i hi => absurd hi (Nat.not_lt_zero i))
  exact ⟨tCount, sCount, c, h.mono (fun seed => by simp) (fun seed => by simp)⟩

-- Degree-level quantitative certificate: a linear-time generator `(dGen = 1, eGen = 1)` stretched
-- for `n + n + 1` rounds `(dCount = 1, eCount = 1)` has time/space degree
-- `max 1 (1 + max 1 1) = 2` and output degree `max 1 1 = 1`.
example : ComputableInDegree
    (PRGStretch.stretch expand (fun n => n + n + 1)) encBits encBits 2 1 := by
  have hcount : ComputableInDegree (fun n : ℕ => n + n + 1) encUnary encUnary 1 1 := by
    have hraw : ComputableTidilyInDegree (fun n : ℕ => n + n + 1) encUnary encUnary 1 1 := by
      fun_prop (disch := first | apply le_refl | lia)
    obtain ⟨⟨t, space, ht, hs, h⟩, hl⟩ := hraw
    exact ⟨⟨t, space, ht, hs, h.computableInTimeAndSpace⟩, hl⟩
  have h := PRGStretch.computableInDegree_stretch length_expand expand_degree hcount
  fail_if_success
    have : ComputableInDegree
        (PRGStretch.stretch expand (fun n => n + n + 1)) encBits encBits 1 1 := h.mono
  exact h.mono

-- A linear-time generator stretched for a quadratic round count `(dCount = 2, eCount = 2)` has
-- time/space degree `max 2 (2 + max 1 1) = 3` and output degree `max 1 2 = 2`.
example (count : ℕ → ℕ) (hcount : ComputableInDegree count encUnary encUnary 2 2) :
    ComputableInDegree (PRGStretch.stretch expand count) encBits encBits 3 2 := by
  have h := PRGStretch.computableInDegree_stretch length_expand expand_degree hcount
  fail_if_success
    have : ComputableInDegree (PRGStretch.stretch expand count) encBits encBits 2 2 := h.mono
  fail_if_success
    have : ComputableInDegree (PRGStretch.stretch expand count) encBits encBits 3 1 := h.mono
  exact h.mono

-- Recover `ComputableInPolyTime` directly from the quantitative stretch theorem.
example : ComputableInPolyTime
    (PRGStretch.stretch expand (fun n => n * n + 1)) encBits encBits :=
  PRGStretch.polyTime_stretch_of_length_eq length_expand
    (by unfold expand; fun_prop) (by fun_prop)

-- Quantitative captured-parameter certificate for `PRGStretch.iterate`.
example : ∃ (tGen : Bool × List Bool → ℕ) (csG c : ℕ),
    ComputableInTimeAndSpace
      (fun x : (Bool × List Bool) × ℕ =>
        PRGStretch.iterate (fun s => s ++ [x.1.1]) x.1.2.length x.2 x.1.2)
      (encPair (encPair encBool encBits) encUnary) encBits
      (fun x => c * ((encBool x.1.1).length + x.1.2.length + x.2 +
        (∑ i ∈ Finset.range x.2,
          (tGen (x.1.1, PRGStretch.seedAt (fun s => s ++ [x.1.1]) x.1.2 i) +
            (encBool x.1.1).length + x.1.2.length + 1)) + 1))
      (fun x => c * (csG * ((encPair encBool encBits x.1).length + 1) +
        (encBool x.1.1).length + x.1.2.length + x.2 + 1)) := by
  have hgen_deg : ComputableTidilyInDegree
      (fun p : Bool × List Bool => p.2 ++ [p.1]) (encPair encBool encBits) encBits 1 1 := by
    have hsingleton : ComputableTidilyInDegree
        (fun p : Bool × List Bool => [p.1]) (encPair encBool encBits) encBits 1 0 :=
      (ComputableTidilyInDegree.of_finite (fun b : Bool => [b])).comp
        (ComputableTidilyInDegree.fst encBool encBits) |>.mono
    exact (ComputableTidilyInDegree.snd encBool encBits).append hsingleton (fun _ => rfl) |>.mono
  obtain ⟨⟨tGen, sGen, _, ⟨csG, hcsG⟩, hgen⟩, -⟩ := hgen_deg
  refine ⟨tGen, csG, ?_⟩
  refine PRGStretch.computableInTimeAndSpace_iterate_captured
    (generator := fun b s => s ++ [b]) (fun _ _ => by simp)
    hgen.computableInTimeAndSpace (fun x i _ => ?_)
  have hlen_seed : (PRGStretch.seedAt (fun s => s ++ [x.1.1]) x.1.2 i).length = x.1.2.length :=
    PRGStretch.length_seedAt_of_forall (fun _ => by simp) x.1.2 i
  have h := hcsG (x.1.1, PRGStretch.seedAt (fun s => s ++ [x.1.1]) x.1.2 i)
  simp only [length_encPair, encBits_apply, hlen_seed, pow_one] at h ⊢
  exact h

end ComplexityTests.PRGStretch
