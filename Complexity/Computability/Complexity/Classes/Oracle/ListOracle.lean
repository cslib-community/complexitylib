/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Oracle
import Complexity.Computability.Complexity.Classes.Oracle.Deterministic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Replay.ListOracle

/-!
# Oracles given as finite lists

A computation in polynomial time relative to an oracle language `S` asks only words no longer
than its clock, a polynomial `q` in the encoded input length. So any finite list `ℓ` of words
that agrees with `S` on the words of length at most `q n` can replace the oracle, and the run
against `ℓ` is polynomial-time in the input and `ℓ` together
(`Cslib.Complexity.ComputableInPolyTimeWithOracle.exists_listOracle`). This is how a sparse oracle
is replaced by advice, or by a guessed list of its short members.

The proof replays the coin-fixed run of a machine certifying the computation
(`Cslib.Probability.IsOraclePPTOn.exists_fin_run_pure_false`) from its instruction-indexed
transcript of oracle replies, built against the list one bit at a time
(`Turing.MultiTapePTM.listReplyStep`, in
`Complexity/Computability/Machines/Turing/MultiTape/Probabilistic/Replay/ListOracle.lean`).
Oracles that agree on the words no longer than the clock give the same transcript
(`Turing.MultiTapePTM.oracleReplies_congr`).

## Main results

* `Cslib.Complexity.ComputableInPolyTimeWithOracle.exists_listOracle`,
  `Cslib.Complexity.ComputableInPolyTimeWithOracle.exists_listOracle_bool`: polynomial time
  relative to `S` is polynomial time with a list that agrees with `S` on short words.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Section 3.4.
-/

@[expose] public section

namespace Cslib.Complexity

open Probability Turing.MultiTapeTM

variable {α β : Type} {S : Set (List Bool)} {input : α ↪ List Bool}

open Classical in
/-- **A finite list can replace the oracle.** If `f` is computable in polynomial time relative to
`S`, there are a polynomial `q` and a function `F`, polynomial-time in an instance and a list of
words together, such that `F (a, ℓ)` is the encoded result `output (f a)` whenever `ℓ` agrees with
`S` on every word of length at most `q (input a).length`. -/
theorem ComputableInPolyTimeWithOracle.exists_listOracle {f : α → β} {output : β ↪ List Bool}
    (hf : ComputableInPolyTimeWithOracle S f input output) :
    ∃ (F : α × List (List Bool) → List Bool) (q : Polynomial ℕ),
      ComputableInPolyTime F (encPair input (encList encBits)) encBits ∧
        ∀ a ℓ, (∀ w : List Bool, w.length ≤ q.eval (input a).length → (w ∈ ℓ ↔ w ∈ S)) →
          F (a, ℓ) = output (f a) := by
  obtain ⟨program, hcert, hprogram⟩ := hf
  obtain ⟨k, m, machine, c, d, hrun⟩ := hcert.exists_fin_run_pure_false
  let T : α → ℕ := fun a => c * ((input a).length + 1) ^ d
  have hTa : ComputableInPolyTime T input encUnary :=
    ((ComputableInPolyTime.unary_eval (Polynomial.C c * (Polynomial.X + 1) ^ d)).comp
      (ComputableInPolyTime.encoding_length input)).of_enc_eq fun a => by simp [T]
  have hT : ComputableInPolyTime (fun x : α × List (List Bool) => T x.1)
      (encPair input (encList encBits)) encUnary :=
    hTa.comp (ComputableInPolyTime.fst _ _)
  have hinput : ComputableInPolyTime (fun a : α => input a) input encBits := .of_eq fun _ => rfl
  have hinput' : ComputableInPolyTime (fun x : α × List (List Bool) => input x.1)
      (encPair input (encList encBits)) encBits :=
    hinput.comp (g := fun x : α × List (List Bool) => x.1) (.fst _ _)
  have hpar : ComputableInPolyTime (fun x : α × List (List Bool) => (input x.1, x.2))
      (encPair input (encList encBits)) (encPair encBits (encList encBits)) :=
    hinput'.prod (.snd _ _)
  have hiter : ComputableInPolyTime
      (fun x : α × List (List Bool) => (machine.listReplyStep (input x.1, x.2))^[T x.1] [])
      (encPair input (encList encBits)) encBits :=
    ComputableInPolyTime.iterateWith_of_bounded_growth hpar hT (ComputableInPolyTime.const [])
      machine.computableInPolyTime_listReplyStep (.const 1) fun x answers => by
        simp [Turing.MultiTapePTM.listReplyStep]
  have hout : ComputableInPolyTime
      (fun x : α × List (List Bool) =>
        machine.replayOutput (input x.1) ((machine.listReplyStep (input x.1, x.2))^[T x.1] []))
      (encPair input (encList encBits)) encBits :=
    machine.computableInPolyTime_replayOutput.comp (g := fun x : α × List (List Bool) =>
      (input x.1, (machine.listReplyStep (input x.1, x.2))^[T x.1] [])) (hinput'.prod hiter)
  refine ⟨_, Polynomial.C c * (Polynomial.X + 1) ^ d, hout, fun a ℓ hℓ => ?_⟩
  dsimp only
  rw [machine.iterate_listReplyStep, machine.oracleReplies_congr (g' := fun w => decide (w ∈ S))
    _ fun w hw => ?_, machine.replayOutput_oracleReplies, ← hprogram a, ← hrun a]
  · rfl
  · refine decide_eq_decide.mpr (hℓ w ?_)
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_one]
    exact hw.le

/-- **A finite list can replace the oracle of a decision**: the Boolean form of
`Cslib.Complexity.ComputableInPolyTimeWithOracle.exists_listOracle`. -/
theorem ComputableInPolyTimeWithOracle.exists_listOracle_bool {f : α → Bool}
    (hf : ComputableInPolyTimeWithOracle S f input encBool) :
    ∃ (F : α × List (List Bool) → Bool) (q : Polynomial ℕ),
      ComputableInPolyTime F (encPair input (encList encBits)) encBool ∧
        ∀ a ℓ, (∀ w : List Bool, w.length ≤ q.eval (input a).length → (w ∈ ℓ ↔ w ∈ S)) →
          F (a, ℓ) = f a := by
  obtain ⟨F, q, hF, hFS⟩ := hf.exists_listOracle
  refine ⟨fun x => decide (F x = [true]), q,
    ComputableInPolyTime.decide_eq' hF (ComputableInPolyTime.const [true]), fun a ℓ hℓ => ?_⟩
  change decide (F (a, ℓ) = [true]) = f a
  rw [hFS a ℓ hℓ, encBool_apply]
  cases f a <;> rfl

end Cslib.Complexity
