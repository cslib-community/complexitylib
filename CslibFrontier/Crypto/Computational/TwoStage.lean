/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game.Experiment
public import CslibFrontier.Computability.Probabilistic.Parameter
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Two-stage adversaries and the left-or-right experiment

Many attack games run the adversary twice. It first receives the challenger's public input and
chooses a challenge request, then receives the challenge and answers. Between the two calls it
keeps a saved state. `TwoStage I₁ O₁ I₂ O σ` is such an adversary: `choose` maps the first input
to a request and a state of type `σ`, and `guess` maps the state and the challenge to the answer.
The state type is a parameter, so a saved state can be a typed record.

`TwoStage.IsPPT` states that a family of two-stage adversaries, one for each security parameter,
is uniform strict PPT: one finite machine for each stage, reading the unary security parameter
and the encoded stage input, including the full encoded saved state. Security definitions over
two-stage adversaries quantify over every state type and state encoding. The word-level
adversaries with state `List Bool` are the instance `σ := List Bool`, `encσ := encBits`.

`lrExperiment` is the left-or-right experiment. The adversary chooses two messages from the drawn
public input; the challenger checks the pair with an admissibility predicate, encrypts the message
selected by the bit and gives the challenge to the adversary, whose guess is the output. An
inadmissible pair outputs `false` on both sides. This is the challenge phase of single-challenge
IND-CPA ([BonehShoup2023], Section 11.2, Attack Game 11.1, p. 436); key generation belongs to the
scheme's own experiment, which draws the public input and then runs `lrExperiment`.

## Main definitions

* `Cslib.Crypto.TwoStage`: an adversary with a choice stage and a guessing stage.
* `Cslib.Crypto.TwoStage.IsPPT`: uniform strict PPT for a family of two-stage adversaries.
* `Cslib.Crypto.MessagePair`, `Cslib.Crypto.MessagePair.select`: a pair of challenge messages and
  the message selected by a bit.
* `Cslib.Crypto.encMessagePair`: the encoding of a message pair, laid out as `encPair encM encM`.
* `Cslib.Crypto.lrExperiment`: the left-or-right experiment on a drawn public input.

## Main results

* `Cslib.Crypto.encMessagePair_msg₀_polyTime`, `Cslib.Crypto.encMessagePair_msg₁_polyTime`,
  `Cslib.Crypto.encMessagePair_mk_polyTime`: polynomial-time projections and construction of an
  encoded message pair.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 11.2 (Attack Game 11.1, p. 436).
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

/-- A two-stage adversary. `choose` receives the first input, of type `I₁`, and returns a request
of type `O₁` together with a saved state of type `σ`; `guess` receives the saved state and the
second input, of type `I₂`, and returns its answer, of type `O`. The state is all that the
adversary retains between the stages. -/
structure TwoStage (I₁ O₁ I₂ O σ : Type) where
  /-- Receive the first input and return a request and a saved state. -/
  choose : I₁ → ProbComp (O₁ × σ)
  /-- Receive the saved state and the second input and return the answer. -/
  guess : σ → I₂ → ProbComp O

/-- A family of two-stage adversaries, one for each security parameter, is uniform strict PPT:
one finite machine runs each stage at every parameter. The choice stage reads the unary security
parameter and the encoded first input; the guessing stage reads the unary security parameter, the
encoded saved state and the encoded second input. Each clock charges the complete encoded input,
including the saved state. -/
structure TwoStage.IsPPT {I₁ O₁ I₂ O σ : Type} (encI₁ : I₁ ↪ List Bool) (encO₁ : O₁ ↪ List Bool)
    (encI₂ : I₂ ↪ List Bool) (encO : O ↪ List Bool) (encσ : σ ↪ List Bool)
    (A : ℕ → TwoStage I₁ O₁ I₂ O σ) : Prop where
  /-- The choice stage is uniform strict PPT on the parameter and the first input. -/
  choose : IsPPTOn (encPair encUnary encI₁) (encPair encO₁ encσ) fun x => (A x.1).choose x.2
  /-- The guessing stage is uniform strict PPT on the parameter, the state and the second
  input. -/
  guess : IsPPTOn (encPair encUnary (encPair encσ encI₂)) encO
    fun ⟨n, state, input⟩ => (A n).guess state input

/-- A pair of challenge messages. -/
structure MessagePair (M : Type) where
  /-- The message encrypted when the challenge bit is `false`. -/
  msg₀ : M
  /-- The message encrypted when the challenge bit is `true`. -/
  msg₁ : M

namespace MessagePair

variable {M : Type}

/-- The message selected by the challenge bit `b`: `msg₀` for `false` and `msg₁` for `true`. -/
def select (pair : MessagePair M) (b : Bool) : M := bif b then pair.msg₁ else pair.msg₀

@[simp] theorem select_false (pair : MessagePair M) : pair.select false = pair.msg₀ := rfl

@[simp] theorem select_true (pair : MessagePair M) : pair.select true = pair.msg₁ := rfl

end MessagePair

/-- The encoding of a message pair: `msg₀` framed, then `msg₁`, each encoded by `encM`. This is
the layout of `encPair encM encM` on `(msg₀, msg₁)`. -/
def encMessagePair {M : Type} (encM : M ↪ List Bool) : MessagePair M ↪ List Bool :=
  ⟨fun pair => encPair encM encM (pair.msg₀, pair.msg₁), fun ⟨a₀, a₁⟩ ⟨b₀, b₁⟩ h => by
    obtain ⟨h₀, h₁⟩ := Prod.mk.inj ((encPair encM encM).injective h)
    exact congrArg₂ MessagePair.mk h₀ h₁⟩

section Encoding

variable {M γ : Type} {encM : M ↪ List Bool} {encIn : γ ↪ List Bool}

@[simp] theorem encMessagePair_apply (pair : MessagePair M) :
    encMessagePair encM pair = encPair encM encM (pair.msg₀, pair.msg₁) := rfl

/-- The pair of components of a message pair is computed in polynomial time. -/
private theorem encMessagePair_toProd_polyTime :
    ComputableInPolyTime (fun pair : MessagePair M => (pair.msg₀, pair.msg₁))
      (encMessagePair encM) (encPair encM encM) :=
  .of_eq fun _ => rfl

/-- The first message of a computed message pair is computed in polynomial time. -/
@[fun_prop] theorem encMessagePair_msg₀_polyTime {g : γ → MessagePair M}
    (h : ComputableInPolyTime g encIn (encMessagePair encM)) :
    ComputableInPolyTime (fun a => (g a).msg₀) encIn encM :=
  (ComputableInPolyTime.fst' encMessagePair_toProd_polyTime).comp h

/-- The second message of a computed message pair is computed in polynomial time. -/
@[fun_prop] theorem encMessagePair_msg₁_polyTime {g : γ → MessagePair M}
    (h : ComputableInPolyTime g encIn (encMessagePair encM)) :
    ComputableInPolyTime (fun a => (g a).msg₁) encIn encM :=
  (ComputableInPolyTime.snd' encMessagePair_toProd_polyTime).comp h

/-- A message pair of two computed messages is computed in polynomial time. -/
@[fun_prop] theorem encMessagePair_mk_polyTime {x₀ x₁ : γ → M}
    (h₀ : ComputableInPolyTime x₀ encIn encM) (h₁ : ComputableInPolyTime x₁ encIn encM) :
    ComputableInPolyTime (fun a => MessagePair.mk (x₀ a) (x₁ a)) encIn (encMessagePair encM) :=
  ComputableInPolyTime.of_enc_eq (h₀.prod h₁) fun _ => rfl

end Encoding

/-- The left-or-right experiment ([BonehShoup2023], Attack Game 11.1, challenge phase) on the
drawn public input `x`. The adversary chooses a message pair and a state from `x`. If
`valid x msg₀ msg₁` holds, the challenger encrypts the message selected by `b` under `x` and
returns the adversary's guess on the state and the challenge; otherwise it returns `false`, on
both sides. -/
def lrExperiment {I₁ M C σ : Type} (valid : I₁ → M → M → Bool) (enc : I₁ → M → ProbComp C)
    (A : TwoStage I₁ (MessagePair M) C Bool σ) (b : Bool) (x : I₁) : Experiment := do
  let (pair, state) ← A.choose x
  if valid x pair.msg₀ pair.msg₁ then
    let challenge ← enc x (pair.select b)
    A.guess state challenge
  else
    return false

end Cslib.Crypto
