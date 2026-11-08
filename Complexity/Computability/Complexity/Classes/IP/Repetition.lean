/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.IP
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import Complexity.Languages.Probabilistic.Iteration
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
completeness is preserved. When the repetition count `k : α → ℕ` is computable in unary polynomial
time, the repetition of a strict oracle PPT verifier is strict oracle PPT
(`IsOraclePPTOn.sequentialRepeat_count`, with `isOraclePPTOn_sequentialRepeat` as the constant-`k`
specialization). This is the amplification of
[Arora and Barak, Section 8.1][AroraBarak09] for sequential repetition.

## Main definitions

* `Cslib.Complexity.sequentialRepeat`: `k` runs in sequence, accepting when all accept.

## Main results

* `Cslib.Complexity.sequentialRepeat_eq_iterate`: `sequentialRepeat` as a bounded
  `OracleComp.iterate` loop over a `Bool` accumulator.
* `Cslib.Complexity.acceptProb_sequentialRepeat_le`: soundness error `ε ^ k`.
* `Cslib.Complexity.le_acceptProb_sequentialRepeat`: completeness `c ^ k`.
* `Cslib.Probability.IsOraclePPTOn.sequentialRepeat_count`: efficiency for a unary polynomial-time
  number of runs.
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
theorem acceptProb_bind_ite (P : Prover Operation)
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

/-- `sequentialRepeat k round` is `k` iterations of the step that runs `round` while the
accumulator is `true` and stays at `false` once a run rejects, starting from `true`. -/
theorem sequentialRepeat_eq_iterate (k : ℕ) (round : WordOracleComp Operation Bool) :
    sequentialRepeat k round =
      OracleComp.iterate k (fun ok => if ok then round else pure false) true := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [sequentialRepeat, OracleComp.iterate_succ_bind]
    simp only [↓reduceIte]
    congr 1
    ext ok
    cases ok
    · exact (OracleComp.iterate_eq_pure k (fun ok => if ok then round else pure false) false
        rfl).symm
    · exact ih

/-- A polynomial number of sequential runs of a strict oracle PPT verifier is strict oracle
PPT. -/
theorem _root_.Cslib.Probability.IsOraclePPTOn.sequentialRepeat_count
    [DecidableEq Operation] [Finite Operation]
    {input : α ↪ List Bool} {k : α → ℕ} {round : α → WordOracleComp Operation Bool}
    (h : IsOraclePPTOn input encBool round)
    (hk : ComputableInPolyTime k input encUnary) :
    IsOraclePPTOn input encBool (fun a => sequentialRepeat (k a) (round a)) := by
  simp only [sequentialRepeat_eq_iterate]
  have hstep : IsOraclePPTOn (encPair input encBool) encBool
      (fun pair : α × Bool => if pair.2 then round pair.1 else pure false) :=
    IsOraclePPTOn.cond' (ComputableInPolyTime.snd input encBool)
      (h.preprocess' (ComputableInPolyTime.fst input encBool))
      (ComputableInPolyTime.const false).isOraclePPTOn
  exact (IsOraclePPTOn.iterateWith_spec' (stateEncoding := encBool)
    (step := fun a ok => if ok then round a else pure false)
    hk (ComputableInPolyTime.const true) hstep
    (fun _ _ _ => True) (fun _ => trivial) (fun _ _ _ _ _ _ _ => trivial)
    (PolyBounded.const 1) (fun _ _ s _ _ => by cases s <;> decide)).1

/-- A constant number of sequential runs of a strict oracle PPT verifier is strict oracle PPT. -/
theorem isOraclePPTOn_sequentialRepeat [DecidableEq Operation] [Finite Operation]
    {input : α ↪ List Bool} {round : α → WordOracleComp Operation Bool}
    (h : IsOraclePPTOn input encBool round) (k : ℕ) :
    IsOraclePPTOn input encBool (fun a => sequentialRepeat k (round a)) :=
  h.sequentialRepeat_count (ComputableInPolyTime.const k)

end Cslib.Complexity
