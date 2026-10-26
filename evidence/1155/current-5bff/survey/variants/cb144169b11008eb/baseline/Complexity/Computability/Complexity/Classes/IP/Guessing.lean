/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.IP
public import Complexity.Computability.Probabilistic.PPT
import Complexity.Probability.PMF.Bind
import Complexity.Computability.Probabilistic.Oracle.Composition
import Complexity.Computability.Probabilistic.Sampling

/-!
# Private-coin guessing rounds

In a guessing round the verifier draws a private fair bit `b`, sends the prover a message drawn
from `message b`, and accepts when the reply starts with `b`. The prover sees the message but
not `b`. This is the round of the private-coin protocol for graph non-isomorphism
[Goldreich, Micali and Wigderson][GoldreichMicaliWigderson1991].

If the two message distributions are `δ`-close, in the sense that the expectations of every
`[0, 1]`-valued function differ by at most `δ`, then every prover is accepted with probability at
most `(1 + δ) / 2` (`acceptProb_guessingRound_le`); identical distributions give soundness `1 / 2`
(`acceptProb_guessingRound_le_half`).
If they have disjoint supports, the prover answering `true` exactly on the possible messages for
`true` is always accepted (`acceptProb_guessingProver`). A round whose messages are sampled by a
strict PPT program is strict oracle PPT (`isOraclePPTOn_guessingRound`): the verifier reads only
one bit of the reply.

## Main definitions

* `Cslib.Complexity.guessingRound`: one guessing round.
* `Cslib.Complexity.Prover.guessProb`: the probability that a prover answers a message with a
  given bit.
* `Cslib.Complexity.guessingProver`: the prover separating the two supports.

## Main results

* `Cslib.Complexity.acceptProb_guessingRound`: acceptance averages the guessing probabilities.
* `Cslib.Complexity.acceptProb_guessingRound_le`: close message distributions give soundness.
* `Cslib.Complexity.acceptProb_guessingRound_le_half`: identical message distributions give
  soundness `1 / 2`.
* `Cslib.Complexity.acceptProb_guessingProver`: disjoint supports give perfect completeness.
* `Cslib.Complexity.isOraclePPTOn_guessingRound`: efficiency.

## References

* [O. Goldreich, S. Micali, A. Wigderson, *Proofs that yield nothing but their validity or all
  languages in NP have zero-knowledge proof systems*][GoldreichMicaliWigderson1991]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Probability Turing.MultiTapeTM

/-- One private-coin guessing round: draw a fair secret bit `b` and a message from `message b`,
send the message, and accept when the first bit of the reply is `b`. -/
noncomputable def guessingRound (message : Bool → ProbComp (List Bool)) :
    WordOracleComp Unit Bool := do
  let b ← ProbOracleComp.sample (ProbComp.uniform Bool)
  let m ← ProbOracleComp.sample (message b)
  let reply ← List.take 1 <$> ProbOracleComp.query ((), m)
  pure (decide (reply = [b]))

/-- The probability that `P`, in state `s`, answers the message `m` with a reply starting with
`b`. -/
noncomputable def Prover.guessProb (P : Prover Unit) (s : P.State) (m : List Bool) (b : Bool) :
    ENNReal :=
  ((P.respond ((), m)).run s).map (fun y => decide (List.take 1 y.1 = [b])) true

/-- A reply cannot start with both bits. -/
theorem Prover.guessProb_add_le_one (P : Prover Unit) (s : P.State) (m : List Bool) :
    P.guessProb s m false + P.guessProb s m true ≤ 1 := by
  simp only [Prover.guessProb, PMF.map_apply]
  rw [← ENNReal.tsum_add, ← PMF.tsum_coe ((P.respond ((), m)).run s)]
  refine ENNReal.tsum_le_tsum fun y => ?_
  by_cases h : List.take 1 y.1 = [false]
  · simp [h]
  · by_cases h' : List.take 1 y.1 = [true] <;> simp [h, h']

private theorem acceptProb_guessReply (P : Prover Unit) (m : List Bool) (b : Bool) :
    acceptProb (do
      let reply ← List.take 1 <$> ProbOracleComp.query ((), m)
      pure (decide (reply = [b]))) P = P.guessProb P.init m b := by
  rw [acceptProb, bind_pure_comp, Prover.run_map, Prover.run_map, Prover.run_query, PMF.map_comp,
    PMF.map_comp]
  rfl

/-- A guessing round accepts with the average, over the secret bit and the message, of the
probability that the prover guesses the bit. -/
theorem acceptProb_guessingRound (message : Bool → ProbComp (List Bool)) (P : Prover Unit) :
    acceptProb (guessingRound message) P =
      (∑' m, ProbComp.eval (message false) m * P.guessProb P.init m false +
        ∑' m, ProbComp.eval (message true) m * P.guessProb P.init m true) / 2 := by
  simp only [guessingRound, acceptProb_sample_bind, acceptProb_guessReply, ProbComp.eval_uniform,
    tsum_bool, PMF.uniformOfFintype_apply, Fintype.card_bool]
  rw [ENNReal.div_eq_inv_mul, mul_add]
  norm_num

/-- **Soundness of a guessing round.** If the expectation of every `[0, 1]`-valued function under
the messages for `true` exceeds that under the messages for `false` by at most `δ`, then every
prover is accepted with probability at most `(1 + δ) / 2`. -/
theorem acceptProb_guessingRound_le {message : Bool → ProbComp (List Bool)} {δ : ENNReal}
    (hclose : ∀ f : List Bool → ENNReal, (∀ m, f m ≤ 1) →
      ∑' m, ProbComp.eval (message true) m * f m ≤
        ∑' m, ProbComp.eval (message false) m * f m + δ)
    (P : Prover Unit) : acceptProb (guessingRound message) P ≤ (1 + δ) / 2 := by
  rw [acceptProb_guessingRound]
  refine ENNReal.div_le_div_right ?_ 2
  calc ∑' m, ProbComp.eval (message false) m * P.guessProb P.init m false +
        ∑' m, ProbComp.eval (message true) m * P.guessProb P.init m true
      ≤ ∑' m, ProbComp.eval (message false) m * P.guessProb P.init m false +
          (∑' m, ProbComp.eval (message false) m * P.guessProb P.init m true + δ) := by
        gcongr
        exact hclose _ fun m => PMF.coe_le_one _ _
    _ = ∑' m, ProbComp.eval (message false) m *
          (P.guessProb P.init m false + P.guessProb P.init m true) + δ := by
        rw [← add_assoc, ← ENNReal.tsum_add]
        simp only [mul_add]
    _ ≤ 1 + δ := by
        gcongr
        exact PMF.tsum_mul_le_of_forall_le _ fun m => P.guessProb_add_le_one _ m

/-- **Soundness one half.** If the messages for the two secret bits have the same law, every
prover is accepted with probability at most `1 / 2`. -/
theorem acceptProb_guessingRound_le_half {message : Bool → ProbComp (List Bool)}
    (h : ProbComp.eval (message true) = ProbComp.eval (message false)) (P : Prover Unit) :
    acceptProb (guessingRound message) P ≤ 1 / 2 :=
  (acceptProb_guessingRound_le (δ := 0) (fun _ _ => by rw [h, add_zero]) P).trans_eq
    (by rw [add_zero])

open scoped Classical in
/-- The prover of a guessing round answering `true` exactly on the possible messages for the
secret bit `true`. -/
noncomputable def guessingProver (message : Bool → ProbComp (List Bool)) : Prover Unit where
  State := Unit
  init := ()
  respond q s := PMF.pure ([decide (q.2 ∈ (ProbComp.eval (message true)).support)], s)

open scoped Classical in
/-- **Completeness of a guessing round.** If no message is possible for both secret bits, the
prover separating the supports is always accepted. -/
theorem acceptProb_guessingProver {message : Bool → ProbComp (List Bool)}
    (hdisjoint : ∀ m ∈ (ProbComp.eval (message false)).support,
      m ∉ (ProbComp.eval (message true)).support) :
    acceptProb (guessingRound message) (guessingProver message) = 1 := by
  rw [acceptProb_guessingRound]
  have hprob (m : List Bool) (b : Bool) :
      (guessingProver message).guessProb (guessingProver message).init m b =
        if decide (m ∈ (ProbComp.eval (message true)).support) = b then 1 else 0 := by
    simp [Prover.guessProb, guessingProver, StateT.run, eq_comm]
  have hfalse : ∑' m, ProbComp.eval (message false) m *
      (guessingProver message).guessProb (guessingProver message).init m false = 1 := by
    rw [← (ProbComp.eval (message false)).tsum_coe]
    refine tsum_congr fun m => ?_
    by_cases hm : m ∈ (ProbComp.eval (message false)).support
    · simp [hprob, hdisjoint m hm]
    · simp [(PMF.apply_eq_zero_iff _ _).2 hm]
  have htrue : ∑' m, ProbComp.eval (message true) m *
      (guessingProver message).guessProb (guessingProver message).init m true = 1 := by
    rw [← (ProbComp.eval (message true)).tsum_coe]
    refine tsum_congr fun m => ?_
    by_cases hm : m ∈ (ProbComp.eval (message true)).support
    · simp [hprob, hm]
    · simp [(PMF.apply_eq_zero_iff _ _).2 hm]
  rw [hfalse, htrue, one_add_one_eq_two, ENNReal.div_self two_ne_zero ENNReal.ofNat_ne_top]

/-- A guessing round whose messages are sampled by a strict PPT program is strict oracle PPT. -/
theorem isOraclePPTOn_guessingRound {α : Type} {input : α ↪ List Bool}
    {message : α → Bool → ProbComp (List Bool)}
    (h : IsPPTOn (encPair input encBool) encBits (fun p => message p.1 p.2)) :
    IsOraclePPTOn input encBool (fun a => guessingRound (message a)) := by
  have hbit := (isPPTOn_uniform_bool input).isOraclePPTOn (Operation := Unit)
  have hmessage := h.isOraclePPTOn (Operation := Unit)
  unfold guessingRound
  fun_prop

end Cslib.Complexity
