/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

-- upstream: local-only (formal abstract tests)

import ComplexityAbstracts.SipserLautemannAbstract
import ComplexityTests.SipserLautemann

/-! # Concrete clients of the public Sipser–Lautemann abstract

The head-bit language has both yes- and no-instances. A two-bit randomized test has error
exactly one quarter on each input; its native polynomial-time certificate witnesses the public
BPP definition, and the public containment supplies both alternating descriptions. A deterministic
version also checks the boundary convention that zero random bits means one possible seed.
-/

namespace ComplexityTests.Abstracts.SipserLautemannTests

open ComplexityAbstracts.SipserLautemannAbstract
open Cslib.Complexity.Tests.SipserLautemann
  (noisyHeadVerifier noisyHeadVerifier_polyTime noisyHeadVerifier_decides)

/-- The language of strings whose first bit is true; the empty string is rejected. -/
def HeadLanguage : Set (List Bool) := {x | x.headD false = true}

example : [true] ∈ HeadLanguage := rfl
example : [] ∉ HeadLanguage := by
  change ¬ false = true
  decide

/-- Exactly one of the four fair two-bit seeds flips the answer, for either answer. -/
example (x : List Bool) :
    (Finset.univ.filter fun r : Fin 2 → Bool =>
      noisyHeadVerifier (x, List.ofFn r) ≠ x.headD false).card = 1 := by
  cases h : x.headD false <;> simp only [noisyHeadVerifier, h] <;> decide

/-- The existing total two-bit test satisfies the public native-machine predicate. -/
theorem noisyHead_polyTime : PolyTimePredicate noisyHeadVerifier :=
  CookLevinBridge.computableInPolyTime_iff_tidy.mpr noisyHeadVerifier_polyTime

/-- A genuinely randomized witness for the public BPP definition, on a nonconstant language. -/
theorem head_mem_BPP : HeadLanguage ∈ BPP := by
  refine ⟨Polynomial.C 2, noisyHeadVerifier, noisyHead_polyTime, ?_⟩
  exact noisyHeadVerifier_decides

/-- Both alternating descriptions follow from the abstract's public theorem. -/
example : HeadLanguage ∈ SigmaTwo ∩ PiTwo := sipserLautemann head_mem_BPP

/-- A deterministic test of the same nonconstant language. -/
def headVerifier (z : List Bool × List Bool) : Bool := z.1.headD false

private theorem headVerifier_polyTime : PolyTimePredicate headVerifier := by
  apply CookLevinBridge.computableInPolyTime_iff_tidy.mpr
  change Turing.MultiTapeTM.ComputableTidilyInPolyTime headVerifier
    (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits)
    Turing.MultiTapeTM.encBool
  unfold headVerifier
  fun_prop

-- There is exactly one random seed of length zero, rather than no seeds.
example : Fintype.card (Fin 0 → Bool) = 1 := by decide

/-- Zero random bits also give a valid public BPP witness: the unique empty seed is correct. -/
example : HeadLanguage ∈ BPP := by
  refine ⟨0, headVerifier, headVerifier_polyTime, ?_⟩
  intro x
  cases h : x.headD false <;>
    simp only [HeadLanguage, Set.mem_ofPred_eq, headVerifier, Polynomial.eval_zero, h] <;> simp

end ComplexityTests.Abstracts.SipserLautemannTests
