/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.TwoStage

/-!
# Commitment schemes

A commitment scheme `Commitment.Scheme K M C O` has typed public keys, messages, commitments and
openings ([BonehShoup2023], Section 8.12, p. 344, and Definition 8.8). Key generation draws the
public parameter, `commit` produces a commitment together with its opening, and `verify` checks
an opening. Correctness is a separate property (`Scheme.Correct`).

Both security notions are stated as experiments for one fixed scheme:

* **Hiding** (`Scheme.hidingExperiment`): draw a key and run the left-or-right experiment
  `lrExperiment` on it, where the challenge is the commitment to the selected message without its
  opening. Every pair of typed messages is admissible.
* **Binding** (`Scheme.bindingExperiment`): draw a key, let the adversary output a
  `BindingCollision`, and accept when it opens one commitment to two different messages.

A scheme is perfectly hiding at a key (`Scheme.PerfectlyHidingAt`) when the commitment law does not
depend on the message. At such a key, every adversary has advantage zero
(`Scheme.advantage_lrExperiment_eq_zero`). In general, the hiding advantage is at most the
probability that key generation outputs a key that is not perfectly hiding
(`Scheme.advantage_hidingExperiment_le`). Asymptotic security over a family of schemes and the
efficiency of adversaries are stated on top of these experiments.

## Main definitions

* `Cslib.Crypto.Commitment.Scheme`: a commitment scheme with typed keys, messages, commitments and
  openings.
* `Cslib.Crypto.Commitment.Scheme.Correct`: every honest opening verifies.
* `Cslib.Crypto.Commitment.Scheme.commitment`: the commitment to a message, without its opening.
* `Cslib.Crypto.Commitment.Scheme.hidingExperiment`: the hiding experiment.
* `Cslib.Crypto.Commitment.BindingCollision`, `Cslib.Crypto.Commitment.Scheme.isBindingCollision`,
  `Cslib.Crypto.Commitment.Scheme.bindingExperiment`: the binding experiment and its winning
  condition.
* `Cslib.Crypto.Commitment.Scheme.PerfectlyHidingAt`: the commitment law is message-independent at
  a key.

## Main results

* `Cslib.Crypto.Commitment.Scheme.eval_hidingExperiment`: the hiding experiment is the
  left-or-right experiment averaged over key generation.
* `Cslib.Crypto.Commitment.Scheme.advantage_lrExperiment_eq_zero`: zero advantage at a perfectly
  hiding key.
* `Cslib.Crypto.Commitment.Scheme.advantage_hidingExperiment_le`: the hiding advantage is at most
  the probability of a key that is not perfectly hiding.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 8.12 (Definition 8.8, p. 344).
-/

@[expose] public section

namespace Cslib.Crypto.Commitment

open Probability

/-- A commitment scheme ([BonehShoup2023], Section 8.12, p. 344) with public keys `K`, messages
`M`, commitments `C` and openings `O`. -/
structure Scheme (K M C O : Type) where
  /-- Key generation: draw the public parameter. -/
  keyGen : ProbComp K
  /-- Commit to a message under a key, returning the commitment and its opening. -/
  commit : K → M → ProbComp (C × O)
  /-- Verify that an opening opens a commitment to a message under a key. -/
  verify : K → M → C → O → Bool

/-- An attempted double opening: one commitment together with two messages and their openings. -/
structure BindingCollision (M C O : Type) where
  /-- The commitment opened twice. -/
  commitment : C
  /-- The first message. -/
  msg₀ : M
  /-- The opening of `commitment` to `msg₀`. -/
  opening₀ : O
  /-- The second message. -/
  msg₁ : M
  /-- The opening of `commitment` to `msg₁`. -/
  opening₁ : O

namespace Scheme

variable {K M C O : Type}

/-- A scheme is correct when every honest opening verifies: for every key that key generation can
output, every message `m` and every commitment and opening that `commit` can output on `m`, `verify`
accepts ([BonehShoup2023], Section 8.12). -/
def Correct (S : Scheme K M C O) : Prop :=
  ∀ k ∈ (ProbComp.eval S.keyGen).support, ∀ m c o,
    (c, o) ∈ (ProbComp.eval (S.commit k m)).support → S.verify k m c o = true

/-- The commitment to `m` under `k`, without its opening. This is the challenge in the hiding
experiment. -/
def commitment (S : Scheme K M C O) (k : K) (m : M) : ProbComp C :=
  Prod.fst <$> S.commit k m

/-- The hiding experiment of the scheme `S` ([BonehShoup2023], Section 8.12, Definition 8.8): draw
a key and run the left-or-right experiment on it. The adversary chooses two messages from the key,
the challenger commits to the message selected by `b` and gives the adversary the commitment
without its opening, and the adversary's guess is the output. Every pair of messages is
admissible. -/
def hidingExperiment {σ : Type} (S : Scheme K M C O) (A : TwoStage K (MessagePair M) C Bool σ)
    (b : Bool) : Experiment := do
  let k ← S.keyGen
  lrExperiment (fun _ _ _ => true) S.commitment A b k

/-- The hiding experiment is the left-or-right experiment averaged over key generation. -/
theorem eval_hidingExperiment {σ : Type} (S : Scheme K M C O)
    (A : TwoStage K (MessagePair M) C Bool σ) (b : Bool) :
    ProbComp.eval (S.hidingExperiment A b) =
      Game.withSetup (ProbComp.eval S.keyGen)
        (lrExperiment (fun _ _ _ => true) S.commitment A b) := by
  simp only [hidingExperiment, Game.withSetup, ProbComp.eval_bind]

/-- The scheme is perfectly hiding at the key `k` when the law of the commitment does not depend on
the message. -/
def PerfectlyHidingAt (S : Scheme K M C O) (k : K) : Prop :=
  ∀ m₀ m₁, ProbComp.eval (S.commitment k m₀) = ProbComp.eval (S.commitment k m₁)

/-- At a perfectly hiding key, the left-or-right experiment has the same law for both bits. -/
theorem eval_lrExperiment_eq_of_perfectlyHidingAt {σ : Type} {S : Scheme K M C O} {k : K}
    (hk : S.PerfectlyHidingAt k) (A : TwoStage K (MessagePair M) C Bool σ) (b₀ b₁ : Bool) :
    ProbComp.eval (lrExperiment (fun _ _ _ => true) S.commitment A b₀ k) =
      ProbComp.eval (lrExperiment (fun _ _ _ => true) S.commitment A b₁ k) := by
  simp only [lrExperiment, ite_true, ProbComp.eval_bind]
  congr 1 with choice : 1
  rw [hk (choice.1.select b₀) (choice.1.select b₁)]

/-- **Perfect hiding at a key**: at a perfectly hiding key, every adversary, even a computationally
unbounded one, has advantage zero in the left-or-right experiment. -/
theorem advantage_lrExperiment_eq_zero {σ : Type} {S : Scheme K M C O} {k : K}
    (hk : S.PerfectlyHidingAt k) (A : TwoStage K (MessagePair M) C Bool σ) :
    Experiment.advantage (lrExperiment (fun _ _ _ => true) S.commitment A false k)
      (lrExperiment (fun _ _ _ => true) S.commitment A true k) = 0 := by
  rw [Experiment.advantage, eval_lrExperiment_eq_of_perfectlyHidingAt hk A false true,
    Game.advantage_self]

/-- **Hiding up to a bad key**: if the scheme is perfectly hiding at every key outside `bad`, then
every adversary, even a computationally unbounded one, has hiding advantage at most the probability
that key generation outputs a key in `bad`. -/
theorem advantage_hidingExperiment_le {σ : Type} (S : Scheme K M C O) (bad : K → Bool)
    (hbad : ∀ k, bad k = false → S.PerfectlyHidingAt k)
    (A : TwoStage K (MessagePair M) C Bool σ) :
    Experiment.advantage (S.hidingExperiment A false) (S.hidingExperiment A true) ≤
      Experiment.succProbability (bad <$> S.keyGen) := by
  rw [Experiment.advantage, Experiment.succProbability, eval_hidingExperiment,
    eval_hidingExperiment, ProbComp.eval_map, PMF.map, Function.comp_def]
  refine Game.advantage_bind_le_succProbability_bind _ _ _ _ fun k => ?_
  cases hk : bad k
  · rw [eval_lrExperiment_eq_of_perfectlyHidingAt (hbad k hk) A false true]
    exact ⟨le_self_add, le_self_add⟩
  · simp only [PMF.pure_apply, ite_true]
    exact ⟨le_add_of_le_right (PMF.coe_le_one _ _), le_add_of_le_right (PMF.coe_le_one _ _)⟩

/-- `c` opens to two different messages under `k`: the messages differ and both openings verify
([BonehShoup2023], Section 8.12, Definition 8.8). -/
def isBindingCollision [DecidableEq M] (S : Scheme K M C O) (k : K)
    (out : BindingCollision M C O) : Bool :=
  decide (out.msg₀ ≠ out.msg₁) && S.verify k out.msg₀ out.commitment out.opening₀ &&
    S.verify k out.msg₁ out.commitment out.opening₁

/-- The binding experiment of the scheme `S` ([BonehShoup2023], Section 8.12, Definition 8.8): draw
a key, give it to the adversary, and accept when the adversary opens one commitment to two
different messages. -/
def bindingExperiment [DecidableEq M] (S : Scheme K M C O)
    (A : K → ProbComp (BindingCollision M C O)) : Experiment := do
  let k ← S.keyGen
  let out ← A k
  return S.isBindingCollision k out

end Scheme

end Cslib.Crypto.Commitment
