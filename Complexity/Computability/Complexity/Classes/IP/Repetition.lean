/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.IP
import Complexity.Computability.Probabilistic.Oracle.Composition

/-!
# Sequential repetition of interactive proofs

`sequentialRepeat k round` runs the verifier `round` up to `k` times in sequence against the same
prover, stopping at the first rejection, and accepts when all `k` runs accept. The prover keeps its
state from one run to the next and may adapt to everything it has seen.

If every prover, from every state, is accepted by one run with probability at most `ε`, then every
prover is accepted by the repetition with probability at most `ε ^ k`
(`acceptProb_sequentialRepeat_le`): the bound on each run holds whatever happened in the earlier
runs. A prover accepted from each of its states with probability at least `c` is accepted by the
repetition with probability at least `c ^ k` (`le_acceptProb_sequentialRepeat`), so perfect
completeness is preserved. For a constant `k` the repetition of a strict oracle PPT verifier is
strict oracle PPT (`isOraclePPTOn_sequentialRepeat`). This is the amplification of
[Arora and Barak, Section 8.1][AroraBarak09] for sequential repetition.

## Main definitions

* `Cslib.Complexity.sequentialRepeat`: `k` runs in sequence, accepting when all accept.

## Main results

* `Cslib.Complexity.acceptProb_sequentialRepeat_le`: soundness error `ε ^ k`.
* `Cslib.Complexity.le_acceptProb_sequentialRepeat`: completeness `c ^ k`.
* `Cslib.Complexity.isOraclePPTOn_sequentialRepeat`: efficiency for a constant number of runs.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Probability Turing.MultiTapeTM

variable {Operation α : Type}

/-- Run `round` up to `k` times in sequence, stopping at the first rejection; accept when all `k`
runs accept. -/
def sequentialRepeat : ℕ → WordOracleComp Operation Bool → WordOracleComp Operation Bool
  | 0, _ => pure true
  | k + 1, round => do
    let ok ← round
    if ok then sequentialRepeat k round else pure false

/-- Running `rest` after an accepting run of `round` is accepted with the probability of `rest`
from each final prover state of an accepting run, averaged over those states. -/
private theorem acceptProb_bind_ite (P : Prover Operation)
    (round rest : WordOracleComp Operation Bool) :
    acceptProb (do let ok ← round; if ok then rest else pure false) P =
      ∑' s, P.run round P.init (true, s) * acceptProb rest { P with init := s } := by
  simp only [acceptProb, Prover.run_bind, PMF.map_bind]
  rw [PMF.bind_apply, tsum_prod', tsum_bool]
  simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, Prover.run_pure, PMF.pure_map,
    PMF.pure_apply, mul_zero, tsum_zero, zero_add]
  rfl

/-- **Soundness amplification.** If every prover is accepted by one run with probability at most
`ε`, every prover is accepted by `k` sequential runs with probability at most `ε ^ k`. -/
theorem acceptProb_sequentialRepeat_le {round : WordOracleComp Operation Bool} {ε : ENNReal}
    (h : ∀ P : Prover Operation, acceptProb round P ≤ ε) (k : ℕ) (P : Prover Operation) :
    acceptProb (sequentialRepeat k round) P ≤ ε ^ k := by
  induction k generalizing P with
  | zero => exact (PMF.coe_le_one _ _).trans (by simp)
  | succ k ih =>
    rw [sequentialRepeat, acceptProb_bind_ite, pow_succ]
    calc ∑' s, P.run round P.init (true, s) *
          acceptProb (sequentialRepeat k round) { P with init := s }
        ≤ ∑' s, P.run round P.init (true, s) * ε ^ k :=
          tsum_le_tsum fun s => mul_le_mul' le_rfl (ih _)
      _ = (∑' s, P.run round P.init (true, s)) * ε ^ k := ENNReal.tsum_mul_right
      _ ≤ ε * ε ^ k := by
          gcongr
          exact (acceptProb_eq_tsum round P).symm.trans_le (h P)
      _ = ε ^ k * ε := mul_comm _ _

/-- **Completeness under repetition.** A prover accepted by one run with probability at least `c`
from each of its states is accepted by `k` sequential runs with probability at least `c ^ k`. -/
theorem le_acceptProb_sequentialRepeat {round : WordOracleComp Operation Bool} {c : ENNReal}
    (P : Prover Operation) (h : ∀ s, c ≤ acceptProb round { P with init := s }) (k : ℕ) :
    c ^ k ≤ acceptProb (sequentialRepeat k round) P := by
  suffices ∀ s, c ^ k ≤ acceptProb (sequentialRepeat k round) { P with init := s } from this _
  induction k with
  | zero => intro s; simp [sequentialRepeat, acceptProb]
  | succ k ih =>
    intro s
    rw [sequentialRepeat, acceptProb_bind_ite, pow_succ, mul_comm]
    calc c * c ^ k ≤ (∑' s', P.run round s (true, s')) * c ^ k := by
          gcongr
          exact (h s).trans_eq (acceptProb_eq_tsum round _)
      _ = ∑' s', P.run round s (true, s') * c ^ k := ENNReal.tsum_mul_right.symm
      _ ≤ _ := tsum_le_tsum fun s' => mul_le_mul' le_rfl (ih s')

/-- A constant number of sequential runs of a strict oracle PPT verifier is strict oracle PPT. -/
theorem isOraclePPTOn_sequentialRepeat [DecidableEq Operation] [Finite Operation]
    {input : α ↪ List Bool} {round : α → WordOracleComp Operation Bool}
    (h : IsOraclePPTOn input encBool round) (k : ℕ) :
    IsOraclePPTOn input encBool (fun a => sequentialRepeat k (round a)) := by
  induction k with
  | zero => exact (ComputableInPolyTime.const true).isOraclePPTOn
  | succ k ih =>
    exact h.bind_with (IsOraclePPTOn.cond' (ComputableInPolyTime.snd input encBool)
      (ih.preprocess' (ComputableInPolyTime.fst input encBool))
      (ComputableInPolyTime.const false).isOraclePPTOn)

end Cslib.Complexity
