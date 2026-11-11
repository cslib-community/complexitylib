/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.MCSP.AntiChecker.Efficient
import CslibFrontier.Computability.MCSP.Magnification.AntiChecker

/-!
# Tests for the efficient anti-checker and the Gap-MCSP oracle circuits

OPS Lemma 4.1 is instantiated at a fixed `β` under `NP ⊆ P/poly`. The oracle circuits for
Gap-MCSP accept a concrete yes-instance at `n = 1` and apply, for all large `n`, at the thresholds
of OPS Lemma 4.1.
-/

namespace CslibFrontierTests.AntiCheckerEfficient

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.MCSP Cslib.MCSP.AntiChecker
  Cslib.Complexity Turing.MultiTapeTM Filter

-- OPS Lemma 4.1 at `β = 1 / 100`: for all large `n`, a circuit with `2 ^ (n + k n / 100)` gates
-- outputs `⌊2 ^ (n / 10)⌋₊` strings that catch every small circuit on a hard function.
example (hNP : NP encBits ⊆ PPolyOn encBits) :
    ∃ k : ℕ, ∀ᶠ n : ℕ in atTop,
      ∃ C : Circuit signature (2 ^ n) (⌊(2 : ℝ) ^ (10 * (1 / 100 : ℝ) * n)⌋₊ * n),
        (C.size : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) + k * (1 / 100 : ℝ) * n) ∧
        ∀ f : BooleanFunction n,
          ⌊(2 : ℝ) ^ ((1 / 100 : ℝ) * n)⌋₊ < complexity interpretation (single f) →
          IsAntiChecker (computableFunctions n ⌊(2 : ℝ) ^ ((1 / 100 : ℝ) * n) / (10 * n)⌋₊) f
            (Set.range fun i =>
              BitString.block (C.eval interpretation (MCSP.truthTable n f)) i) := by
  obtain ⟨k, hk⟩ := exists_antiChecker_circuit_of_NP_subset_PPoly hNP
  exact ⟨k, hk _ (by norm_num)⟩

-- The explicit form: under `NP ⊆ P/poly`, one constant bounds the circuit for every `n`, `s` and
-- number of output blocks at least the number of rounds.
example (hNP : NP encBits ⊆ PPolyOn encBits) :
    ∃ c : ℕ, ∀ n s : ℕ, 0 < n →
      ∃ C : Circuit signature (2 ^ n) (antiCheckerRounds n s * n),
        C.size ≤ 2 ^ n * c * (n + s + 1) ^ c := by
  obtain ⟨c, hc⟩ := exists_antiChecker_circuit_le_of_NP_subset_PPoly hNP
  exact ⟨c, fun n s hn => (hc n s _ hn le_rfl).imp fun _ h => h.1⟩

-- Gap-MCSP oracle circuits at `n = 1` with thresholds `1` and `9`, the least `s₂` the gap allows:
-- the circuit accepts the truth table of a constant function, which has one gate. At `n = 1` every
-- function has fewer than `9` gates, so there are no no-instances to reject; the large-`n` example
-- below is the non-vacuous use.
example : ∃ E : Circuit oracleSignature (2 ^ 1) 1,
    E.size ≤ 5000 * 2 ^ 1 * 9 ^ 5 ∧
    E.eval (oracleInterpretation antiCheckerOracle) (MCSP.truthTable 1 fun _ => false) 0 =
      true := by
  obtain ⟨E, hsize, -, -, -, hyes, -⟩ :=
    exists_oracleCircuit_gapMCSP (s₁ := fun _ => 1) (s₂ := fun _ => 9) (n := 1) (by norm_num)
  refine ⟨E, hsize, hyes _ ?_⟩
  rw [GapMCSP.ofFn_mem_yesSet_iff, Equiv.symm_apply_apply, complexity_const]

-- The thresholds of OPS Lemma 4.1 meet the gap condition for all large `n`, so
-- `Gap-MCSP[⌊2 ^ (β n) / 10 n⌋₊, ⌊2 ^ (β n)⌋₊]` has the oracle circuits for all large `n`.
example {β : ℝ} (hβ : 0 < β) :
    ∀ᶠ n : ℕ in atTop, ∃ E : Circuit oracleSignature (2 ^ n) 1,
      E.size ≤ 5000 * 2 ^ n * ⌊(2 : ℝ) ^ (β * n)⌋₊ ^ 5 ∧
      (∀ T : BitString (2 ^ n),
        List.ofFn T ∈ GapMCSP.yesSet (fun n => ⌊(2 : ℝ) ^ (β * n) / (10 * n)⌋₊) →
        E.eval (oracleInterpretation antiCheckerOracle) T 0 = true) ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.noSet (fun n => ⌊(2 : ℝ) ^ (β * n)⌋₊) →
        E.eval (oracleInterpretation antiCheckerOracle) T 0 = false) := by
  filter_upwards [eventually_mul_floor_div_add_le_floor hβ] with n hn
  obtain ⟨E, hsize, -, -, -, hyes, hno⟩ :=
    exists_oracleCircuit_gapMCSP (s₁ := fun n => ⌊(2 : ℝ) ^ (β * n) / (10 * n)⌋₊)
      (s₂ := fun n => ⌊(2 : ℝ) ^ (β * n)⌋₊) hn
  exact ⟨E, hsize, hyes, hno⟩

end CslibFrontierTests.AntiCheckerEfficient
