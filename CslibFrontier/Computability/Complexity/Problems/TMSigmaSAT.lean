/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.PH.Reduction
public import CslibFrontier.Computability.Complexity.Problems.TMSAT
import CslibFrontier.Computability.Complexity.Classes.Alternation.Game
import CslibFrontier.Computability.Complexity.Classes.PH.Projection
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Bounded-alternation machine satisfiability (`TMSigmaSAT`) is `Σₖ`-complete

`Cslib.Complexity.TMSigmaSAT k` is the level-`k` universal machine language on
`Cslib.Complexity.TMSATInstance`: an instance `⟨α, x, 1ⁿ, 1ᵗ⟩` belongs to `TMSigmaSAT k` when `k`
alternating quantifier blocks of length `n` (starting with `∃`) make the machine described by `α`
accept `⟨x, u₁ ++ ⋯ ++ uₖ⟩` within `t` steps (`Cslib.Complexity.TMSATInstance.Accepts`). For `k = 1`
this is `Cslib.Complexity.TMSAT` (`Cslib.Complexity.TMSigmaSAT.one_eq_TMSAT`).

* **Membership in `Σₖ`** (`Cslib.Complexity.TMSigmaSAT.mem_SigmaP`): the verifier cuts `k`
  certificate blocks of length `|enc a|` to `a.witnessLength ≤ |enc a|` bits each via
  `Cslib.Complexity.takeBlocks` and simulates the described machine for `a.steps` steps.
* **Hardness for `Σₖ`** (`Cslib.Complexity.TMSigmaSAT.sigmaPHard`): by
  `Cslib.Complexity.exists_replicate_of_mem_SigmaP`, every `A ∈ SigmaP k enc` has a verifier with a
  single polynomial bound `p` for all `k` blocks, which reduces to `TMSigmaSAT k` via
  `Cslib.Complexity.TMSATInstance.exists_polyTime_accepts`.

## Main definitions

* `Cslib.Complexity.TMSigmaSAT`: the level-`k` universal machine language on `TMSATInstance`.
* `Cslib.Complexity.TMSigmaSAT.verifier`: its alternating verifier.

## Main results

* `Cslib.Complexity.TMSigmaSAT.one_eq_TMSAT`: `TMSigmaSAT 1 = TMSAT`.
* `Cslib.Complexity.TMSigmaSAT.mem_SigmaP`: `TMSigmaSAT k ∈ SigmaP k encTMSATInstance`.
* `Cslib.Complexity.TMSigmaSAT.sigmaPHard`: `TMSigmaSAT k` is `Σₖ`-hard.
* `Cslib.Complexity.TMSigmaSAT.sigmaPComplete`: `TMSigmaSAT k` is `Σₖ`-complete.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, web draft 2007][AroraBarak07]
-/

public section

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal

/-- **Level-`k` machine satisfiability (`TMSigmaSAT k`)**: the instances `⟨α, x, 1ⁿ, 1ᵗ⟩`
(`Cslib.Complexity.TMSATInstance`) for which `k` alternating quantifier blocks of length `n`
(starting with `∃`) make the machine described by `α` accept `⟨x, u₁ ++ ⋯ ++ uₖ⟩` within `t` steps.
For `k = 1` this is `TMSAT`. -/
def TMSigmaSAT (k : ℕ) : Set TMSATInstance :=
  {a | Alternation true (List.replicate k a.witnessLength) a.Accepts}

namespace TMSigmaSAT

theorem mem_iff {k : ℕ} {a : TMSATInstance} :
    a ∈ TMSigmaSAT k ↔ Alternation true (List.replicate k a.witnessLength) a.Accepts :=
  Iff.rfl

@[simp]
theorem one_eq_TMSAT : TMSigmaSAT 1 = TMSAT := by
  ext a
  simp [TMSigmaSAT, TMSAT.mem_iff, alternation_singleton_true]

/-- The verifier of `TMSigmaSAT k`: cut `k` blocks of length `|enc a|` to `a.witnessLength` bits
each and run the described machine for `a.steps` steps. -/
noncomputable def verifier (k : ℕ) (q : TMSATInstance × List Bool) : Bool :=
  decide (q.1.Accepts
    (takeBlocks (List.replicate k (q.1.witnessLength, (encTMSATInstance q.1).length)) q.2))

theorem computableInPolyTime_verifier (k : ℕ) :
    ComputableInPolyTime (verifier k) (encPair encTMSATInstance encBits) encBool := by
  have htake : ComputableInPolyTime
      (fun q : TMSATInstance × List Bool =>
        takeBlocks (List.replicate k (q.1.witnessLength, (encTMSATInstance q.1).length)) q.2)
      (encPair encTMSATInstance encBits) encBits := by
    simpa only [List.map_replicate] using
      computableInPolyTime_takeBlocks
        (List.replicate k (fun q : TMSATInstance × List Bool => q.1.witnessLength,
          fun q => (encTMSATInstance q.1).length))
        (fun l hl => by
          obtain rfl := List.eq_of_mem_replicate hl
          exact ⟨by fun_prop,
            (ComputableInPolyTime.encoding_length encTMSATInstance).comp (.fst _ _)⟩)
        (.snd _ _)
  exact TMSATInstance.computableInPolyTime_decide_accepts (.fst _ _) htake

theorem isAlternatingVerifier (k : ℕ) :
    IsAlternatingVerifier encTMSATInstance true (List.replicate k Polynomial.X)
      (verifier k) (TMSigmaSAT k) := fun a => by
  rw [mem_iff]
  have htake := alternation_takeBlocks
    (ls := List.replicate k (a.witnessLength, (encTMSATInstance a).length))
    (q := true) (P := a.Accepts)
    (fun l hl => by
      obtain rfl := List.eq_of_mem_replicate hl
      exact TMSAT.witnessLength_le a)
  simpa only [List.map_replicate, Polynomial.eval_X, verifier, decide_eq_true_iff] using htake.symm

/-- **`TMSigmaSAT k` is in `Σₖ`.** -/
theorem mem_SigmaP (k : ℕ) : TMSigmaSAT k ∈ SigmaP k encTMSATInstance :=
  ⟨List.replicate k Polynomial.X, verifier k, List.length_replicate,
    computableInPolyTime_verifier k, isAlternatingVerifier k⟩

/-- **`TMSigmaSAT k` is `Σₖ`-hard**: every problem in `Σₖ` reduces to it in polynomial time via
the uniform-block verifier of `Cslib.Complexity.exists_replicate_of_mem_SigmaP`. -/
theorem sigmaPHard (k : ℕ) : SigmaPHard k encTMSATInstance (TMSigmaSAT k) := by
  intro α enc A hA
  obtain ⟨p, V, hV, hAV⟩ := exists_replicate_of_mem_SigmaP hA
  obtain ⟨f, hf, hlen, hacc⟩ := TMSATInstance.exists_polyTime_accepts hV p k
  refine ⟨f, hf, fun a => ?_⟩
  rw [hAV a, mem_iff, hlen a, List.map_replicate]
  refine alternation_congr_of_length fun w hw => ?_
  rw [List.sum_replicate, smul_eq_mul] at hw
  exact (hacc a w hw).symm

/-- **`TMSigmaSAT k` is `Σₖ`-complete.** -/
theorem sigmaPComplete (k : ℕ) : SigmaPComplete k encTMSATInstance (TMSigmaSAT k) :=
  ⟨mem_SigmaP k, sigmaPHard k⟩

end TMSigmaSAT

end Cslib.Complexity
