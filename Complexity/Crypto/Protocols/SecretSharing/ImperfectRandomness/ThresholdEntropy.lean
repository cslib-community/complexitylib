/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Crypto.Protocols.SecretSharing.ImperfectRandomness.TwoOutOfN
public import Complexity.Crypto.Protocols.SecretSharing.ImperfectRandomness.AllOutOfR

/-!
# Threshold sources lose at most log₂ 3 bits of entropy

Theorem 1.2 of [Aggarwal2026], PDF p. 3, states the key-relative entropy bound
for both threshold families. Their sharper bounds are already proved in the
construction modules; these corollaries give the advertised common statement
on the actual key alphabets and source laws, without padding the alphabet.

## Main results

* `TwoOutOfN.minEntropy_key_relative`: the two-out-of-n family.
* `AllOutOfR.minEntropy_key_relative`: the all-out-of-r family.
-/

public section

namespace Cslib.Crypto.Protocols.SecretSharing.ImperfectRandomness

open Finset Cslib.Probability

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- Theorem 1.2's entropy guarantee for every actual two-out-of-n source. -/
theorem TwoOutOfN.minEntropy_key_relative {n : ℕ} (hn : 2 ≤ n) (T : Finset V) :
    Real.logb 2 (Fintype.card (TwoOutOfN.Key n V)) - Real.logb 2 3 ≤
      PMF.minEntropy (TwoOutOfN.source hn T) := by
  have hc : (TwoOutOfN.central n).card = n - 1 ∧
      (univ \ TwoOutOfN.central n).card = (n - 1) + 1 := by
    rw [TwoOutOfN.card_central, TwoOutOfN.card_side]
    omega
  exact OddSources.log_key_sub_log_three_le_minEntropy (TwoOutOfN.central n)
    (TwoOutOfN.central_nonempty hn) (TwoOutOfN.side_nonempty hn) (n - 1) (Or.inl hc) T

/-- Theorem 1.2's entropy guarantee for every actual all-out-of-r source, with `r=n+1`. -/
theorem AllOutOfR.minEntropy_key_relative {n : ℕ} (hn : 1 ≤ n)
    (T : Finset (AllOutOfR.Index V n)) :
    Real.logb 2 (Fintype.card (AllOutOfR.Key V n)) - Real.logb 2 3 ≤
      PMF.minEntropy (AllOutOfR.source hn T) := by
  have hp : 0 < 2 ^ n := pow_pos (by decide) _
  have hc : (AllOutOfR.oddBranches n).card = (2 ^ n - 1) + 1 ∧
      (univ \ AllOutOfR.oddBranches n).card = 2 ^ n - 1 := by
    rw [AllOutOfR.card_oddBranches, AllOutOfR.card_evenBranches]
    omega
  exact OddSources.log_key_sub_log_three_le_minEntropy (AllOutOfR.oddBranches n)
    (AllOutOfR.oddBranches_nonempty n) (AllOutOfR.evenBranches_nonempty hn)
    (2 ^ n - 1) (Or.inr hc) T

end Cslib.Crypto.Protocols.SecretSharing.ImperfectRandomness
