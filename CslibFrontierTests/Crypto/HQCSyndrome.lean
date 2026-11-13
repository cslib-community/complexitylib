/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Game.Experiment
import CslibFrontier.Crypto.Primitives.HQC.Syndrome
import Mathlib.Data.Fin.VecNotation

/-! Finite checks for the HQC syndrome laws, continuation clients, and truncation semantics. -/

namespace CslibFrontierTests.HQCSyndrome

open Cslib Cslib.BitString Cslib.Crypto Cslib.Crypto.HQC Cslib.Probability Finset

-- The source's ideal support sampler supplies exactly the fixed-weight law used by the
-- distributions, including the boundary layers.
example :
    (ProbComp.eval (sampleSupportFrom (idealCandidate 4) 0 0)).map (indicatorVector 4) =
      PMF.uniformOfFinset (weightLayer 4 0) (weightLayer_nonempty (by decide)) :=
  eval_idealSupport_map_indicatorVector (by decide)

example :
    (ProbComp.eval (sampleSupportFrom (idealCandidate 4) 0 4)).map (indicatorVector 4) =
      PMF.uniformOfFinset (weightLayer 4 4) (weightLayer_nonempty (by decide)) :=
  eval_idealSupport_map_indicatorVector (by decide)

private def delta0 : BitString 4 := ![true, false, false, false]
private def e1 : BitString 4 := ![false, true, false, false]
private def e2 : BitString 4 := ![false, false, true, false]
private def e3 : BitString 4 := ![false, false, false, true]

-- Full uniform sampling is not a valid comparison baseline for a parity-constrained syndrome:
-- this odd word is supported by the former and excluded by the required even-parity law.
example : delta0 ∈ (PMF.uniformOfFintype (BitString 4)).support ∧
    delta0 ∉ (uniformParity 4 (syndromeParity 1 true)).support := by
  constructor
  · exact PMF.mem_support_uniformOfFintype delta0
  · rw [mem_support_uniformParity]
    decide

-- Both the real and comparison two-block laws expose the same deterministic parity test.
example :
    (realSyndromeLaw 4 1 (by decide) true).map (fun sample => parity 4 sample.value) =
      PMF.pure false := by
  simpa [syndromeParity] using map_parity_realSyndromeLaw (n := 4) (w := 1) (by decide) true

example :
    (uniformSyndromeLaw 4 1 true).map (fun sample => parity 4 sample.value) =
      PMF.pure false := by
  simpa [syndromeParity] using map_parity_uniformSyndromeLaw 4 1 true

private def parityContinuation (sample : SyndromeSample 4) : Experiment :=
  pure (parity 4 sample.value)

-- The distribution laws compose directly with the existing security-game continuation API.
example :
    Game.withSetup (realSyndromeLaw 4 1 (by decide) true) parityContinuation =
      PMF.pure false := by
  change (realSyndromeLaw 4 1 (by decide) true).bind
      (PMF.pure ∘ fun sample => parity 4 sample.value) = PMF.pure false
  rw [PMF.bind_pure_comp]
  simpa [syndromeParity] using map_parity_realSyndromeLaw (n := 4) (w := 1) (by decide) true

example :
    Game.withSetup (uniformSyndromeLaw 4 1 true) parityContinuation = PMF.pure false := by
  change (uniformSyndromeLaw 4 1 true).bind
      (PMF.pure ∘ fun sample => parity 4 sample.value) = PMF.pure false
  rw [PMF.bind_pure_comp]
  simpa [syndromeParity] using map_parity_uniformSyndromeLaw 4 1 true

-- Retaining no coordinates produces the unique empty second block.
example :
    (realTruncatedSyndromeLaw 4 0 1 (by decide) (by decide) true true).map
        (fun sample => sample.secondValue) = PMF.pure ![] := by
  apply PMF.map_eq_pure_iff.mpr
  intro sample _
  funext i
  exact Fin.elim0 i

-- Retaining all coordinates exposes the complete second syndrome from the shared witness.
example {sample : TruncatedSyndromeSample 4 4}
    (hs : sample ∈
      (realTruncatedSyndromeLaw 4 4 1 (by decide) (by decide) true true).support) :
    ∃ x y z : BitString 4,
      weight x = 1 ∧ weight y = 1 ∧ weight z = 1 ∧
        sample.firstValue = syndrome sample.firstBlock x z ∧
          sample.secondValue = syndrome sample.secondBlock y z := by
  rw [mem_support_realTruncatedSyndromeLaw_iff] at hs
  obtain ⟨_, _, x, y, z, hx, hy, hz, hfirst, hsecond⟩ := hs
  refine ⟨x, y, z, hx, hy, hz, hfirst, ?_⟩
  simpa using hsecond

private def sharedSecretCounterexample : TruncatedSyndromeSample 4 3 :=
  ⟨delta0, delta0, ![true, true, false, false], ![false, false, true]⟩

private theorem syndrome_delta0 (x z : BitString 4) : syndrome delta0 x z = x + z := by
  ext i
  fin_cases i <;>
    simp [syndrome, delta0, Matrix.mulVec, dotProduct, Matrix.circulant_apply, Fin.sum_univ_succ,
      Bool.mul_eq_and, Bool.add_eq_xor]

private theorem sharedSecretCounterexample_redrawn :
    sharedSecretCounterexample =
      ⟨delta0, delta0, syndrome delta0 e1 delta0,
        syndrome delta0 e3 e2 ∘ Fin.castLEEmb (by decide : 3 ≤ 4)⟩ := by
  rw [syndrome_delta0, syndrome_delta0]
  unfold sharedSecretCounterexample delta0 e1 e2 e3
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem no_shared_third :
    ¬∃ x y z : BitString 4,
      weight x = 1 ∧ weight y = 1 ∧ weight z = 1 ∧
        x + z = ![true, true, false, false] ∧
          (y + z) ∘ Fin.castLEEmb (by decide : 3 ≤ 4) =
            (![false, false, true] : BitString 3) := by
  decide

private theorem mem_weightOne {value : BitString 4} (hvalue : weight value = 1) :
    value ∈ (PMF.uniformOfFinset (weightLayer 4 1) (weightLayer_nonempty (by decide))).support :=
  (PMF.mem_support_uniformOfFinset_iff _ value).mpr (mem_weightLayer.mpr hvalue)

/-- An intentionally incorrect variant that redraws the third secret between components. -/
private noncomputable def redrawnTruncatedSyndromeLaw : PMF (TruncatedSyndromeSample 4 3) := do
  let h₁ ← uniformParity 4 true
  let h₂ ← uniformParity 4 true
  let x ← PMF.uniformOfFinset (weightLayer 4 1) (weightLayer_nonempty (by decide))
  let y ← PMF.uniformOfFinset (weightLayer 4 1) (weightLayer_nonempty (by decide))
  let z₁ ← PMF.uniformOfFinset (weightLayer 4 1) (weightLayer_nonempty (by decide))
  let z₂ ← PMF.uniformOfFinset (weightLayer 4 1) (weightLayer_nonempty (by decide))
  return ⟨h₁, h₂, syndrome h₁ x z₁, syndrome h₂ y z₂ ∘ Fin.castLEEmb (by decide : 3 ≤ 4)⟩

-- The displayed sample is possible with `z₁ = e0`, `z₂ = e2`, `x = e1`, and `y = e3`.
example : sharedSecretCounterexample ∈ redrawnTruncatedSyndromeLaw.support := by
  simp only [redrawnTruncatedSyndromeLaw, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff]
  refine ⟨delta0, ?_, delta0, ?_, e1, ?_, e3, ?_, delta0, ?_, e2, ?_, ?_⟩
  · exact (mem_support_uniformParity true delta0).mpr (by decide)
  · exact (mem_support_uniformParity true delta0).mpr (by decide)
  · exact mem_weightOne (by decide)
  · exact mem_weightOne (by decide)
  · exact mem_weightOne (by decide)
  · exact mem_weightOne (by decide)
  · exact sharedSecretCounterexample_redrawn

-- No single weight-one `z` can produce both displayed components, so the source law excludes it.
example : sharedSecretCounterexample ∉
    (realTruncatedSyndromeLaw 4 3 1 (by decide) (by decide) true true).support := by
  rw [mem_support_realTruncatedSyndromeLaw_iff]
  rintro ⟨_, _, x, y, z, hx, hy, hz, hfirst, hsecond⟩
  apply no_shared_third
  refine ⟨x, y, z, hx, hy, hz, ?_, ?_⟩
  · simpa only [sharedSecretCounterexample, syndrome_delta0] using hfirst.symm
  · simpa only [sharedSecretCounterexample, syndrome_delta0] using hsecond.symm

private def suffixThree (value : BitString 4) : BitString 3 :=
  fun i => value ⟨i.val + 1, by omega⟩

/-- An intentionally incorrect variant that retains the last three coordinates. -/
private noncomputable def suffixTruncatedSyndromeLaw : PMF (TruncatedSyndromeSample 4 3) := do
  let h₁ ← uniformParity 4 true
  let h₂ ← uniformParity 4 true
  let x ← PMF.uniformOfFinset (weightLayer 4 1) (weightLayer_nonempty (by decide))
  let y ← PMF.uniformOfFinset (weightLayer 4 1) (weightLayer_nonempty (by decide))
  let z ← PMF.uniformOfFinset (weightLayer 4 1) (weightLayer_nonempty (by decide))
  return ⟨h₁, h₂, syndrome h₁ x z, suffixThree (syndrome h₂ y z)⟩

private theorem sharedSecretCounterexample_suffix :
    sharedSecretCounterexample =
      ⟨delta0, delta0, syndrome delta0 e1 delta0,
        suffixThree (syndrome delta0 e3 delta0)⟩ := by
  rw [syndrome_delta0, syndrome_delta0]
  unfold sharedSecretCounterexample suffixThree delta0 e1 e3
  congr 1 <;> funext i <;> fin_cases i <;> rfl

-- Retaining a suffix instead of the source's designated prefix admits the displayed sample,
-- even though the actual source law above excludes it while using the same third secret.
example : sharedSecretCounterexample ∈ suffixTruncatedSyndromeLaw.support := by
  simp only [suffixTruncatedSyndromeLaw, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff]
  refine ⟨delta0, ?_, delta0, ?_, e1, ?_, e3, ?_, delta0, ?_, ?_⟩
  · exact (mem_support_uniformParity true delta0).mpr (by decide)
  · exact (mem_support_uniformParity true delta0).mpr (by decide)
  · exact mem_weightOne (by decide)
  · exact mem_weightOne (by decide)
  · exact mem_weightOne (by decide)
  · exact sharedSecretCounterexample_suffix

end CslibFrontierTests.HQCSyndrome
