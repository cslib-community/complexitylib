/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.Oracle.Interaction
public import Complexity.Languages.Probabilistic.Sum

/-!
# Public-coin interactive oracle reductions

An interactive reduction from a relation `R₁` to a relation `R₂` is a public-coin protocol in which
a prover convinces a verifier, who holds a statement of `R₁`, to output a statement of `R₂`, and
whose prover outputs a witness for it [Ben-Sasson, Chiesa and Spooner][BenSassonChiesaSpooner2016].
Interactive proofs and interactive oracle proofs are the reductions to acceptance.

A protocol is described by its rounds (`Interactive.Spec`, a list of `Interactive.Round`s). In a
prover round the prover sends a message, which the verifier only accesses through the message's
`Interactive.OracleInterface` (reading the whole message is the interface `OracleInterface.full`);
in a verifier round the verifier sends a public random challenge, drawn from a sampler.

A prover is a strategy tree (`Interactive.ProverStrategy`) in the monad `ProbOracleComp oP`; it may
draw private coins and query its oracles `oP`. A public-coin verifier
(`Interactive.Verifier`) consists of one challenge sampler per verifier round and a decision: a
program that queries its oracles `oV` and the prover's messages, given the statement and the
challenges, and returns the output statement, or `none` to reject. A reduction from a relation
`R₁` to a relation `R₂` (`Interactive.Reduction`) pairs an honest prover with a verifier.

Runs live in `ProbOracleComp (oP ⊕ₒ oV)`; a `World` implements the joint oracles (the plain
model, a random oracle, an ideal functionality) as one stateful handler, and `World.eval` gives
the output law.

Shapes depend only on parameters fixed before the interaction (the *index*: field, sizes,
circuit), never on the statement or on earlier messages. Everything indexed by a shape is defined
by structural recursion on its list of rounds, so concatenated protocols compute without casts.

## Main definitions

* `Interactive.OracleInterface`, `Interactive.OracleInterface.full`,
  `Interactive.OracleInterface.coord`, `Interactive.Round`, `Interactive.Round.Message`,
  `Interactive.Spec`.
* `Interactive.Spec.Transcript`, `Interactive.Spec.PerChallenge`, `Interactive.Spec.Challenges`,
  `Interactive.Spec.Transcript.challenges`, `Interactive.Spec.MsgQuery`,
  `Interactive.Spec.MsgResponse`, `Interactive.Spec.msgSpec`, `Interactive.Spec.Transcript.answer`.
* `Interactive.ProverStrategy`, `Interactive.Prover`, `Interactive.Verifier`,
  `Interactive.Reduction`.
* `Interactive.liftProver`, `Interactive.runStrategy`, `Interactive.Verifier.output`,
  `Interactive.Verifier.execute`, `Interactive.Reduction.run`.
* `Interactive.World`, `Interactive.World.eval`, `Interactive.World.plain`.

## References

* [E. Ben-Sasson, A. Chiesa, N. Spooner, *Interactive Oracle Proofs*][BenSassonChiesaSpooner2016]
-/

@[expose] public section

namespace Cslib.Interactive

open scoped ENNReal

/-! ### Messages and rounds -/

/-- How the verifier accesses a prover message of type `M`: the queries it may ask and the
responses the message gives. -/
structure OracleInterface (M : Type) where
  /-- The queries the verifier may ask about a message. -/
  Query : Type
  /-- The type of the response to each query. -/
  Response : Query → Type
  /-- The message's response to each query. -/
  answer : M → (q : Query) → Response q

/-- Reading the whole message with a single query. -/
def OracleInterface.full (M : Type) : OracleInterface M where
  Query := Unit
  Response _ := M
  answer m _ := m

/-- Reading single coordinates of a vector message `ι → A` (as for a codeword or a PCP). -/
def OracleInterface.coord (ι A : Type) : OracleInterface (ι → A) where
  Query := ι
  Response _ := A
  answer f i := f i

/-- A round of a public-coin protocol. -/
inductive Round : Type 1 where
  /-- The prover sends a message of type `M`, which the verifier accesses through `I`. -/
  | prover (M : Type) (I : OracleInterface M)
  /-- The verifier sends a public random challenge of type `C`. -/
  | verifier (C : Type)

/-- The type of the message sent in a round. -/
abbrev Round.Message : Round → Type
  | .prover M _ => M
  | .verifier C => C

/-- A protocol specification: its rounds, in order. -/
abbrev Spec := List Round

namespace Spec

/-- A complete transcript: the message of every round. -/
@[reducible] def Transcript : Spec → Type
  | [] => Unit
  | r :: s => r.Message × Transcript s

/-- One value of `F C` for every verifier round with challenges in `C`: the challenges themselves
(`F = id`), their samplers (`F = ProbComp`) or per-round errors (`F = fun _ => ℝ≥0∞`). -/
@[reducible] def PerChallenge (F : Type → Type) : Spec → Type
  | [] => Unit
  | .prover _ _ :: s => PerChallenge F s
  | .verifier C :: s => F C × PerChallenge F s

/-- The verifier's challenges in a run. -/
abbrev Challenges (s : Spec) : Type := PerChallenge id s

/-- The challenges of a transcript. -/
def Transcript.challenges : (s : Spec) → Transcript s → Challenges s
  | [], _ => ()
  | .prover _ _ :: s, τ => Transcript.challenges s τ.2
  | .verifier _ :: s, τ => (τ.1, Transcript.challenges s τ.2)

/-- The queries the verifier may ask about the prover's messages. -/
@[reducible] def MsgQuery : Spec → Type
  | [] => Empty
  | .prover _ I :: s => I.Query ⊕ MsgQuery s
  | .verifier _ :: s => MsgQuery s

/-- The response types of the queries about the prover's messages. -/
@[reducible] def MsgResponse : (s : Spec) → MsgQuery s → Type
  | [], q => q.elim
  | .prover _ I :: _, .inl q => I.Response q
  | .prover _ _ :: s, .inr q => MsgResponse s q
  | .verifier _ :: s, q => MsgResponse s q

/-- The oracle interface of the prover's messages. -/
abbrev msgSpec (s : Spec) : OracleSpec (MsgQuery s) := MsgResponse s

/-- The prover's messages in a transcript answer the verifier's queries. -/
def Transcript.answer : (s : Spec) → Transcript s → (q : MsgQuery s) → MsgResponse s q
  | [], _, q => q.elim
  | .prover _ I :: _, τ, .inl q => I.answer τ.1 q
  | .prover _ _ :: s, τ, .inr q => Transcript.answer s τ.2 q
  | .verifier _ :: s, τ, q => Transcript.answer s τ.2 q

end Spec

open Spec

/-! ### Provers and verifiers -/

/-- A strategy of a party sending the prover's messages in the rounds `s`, in the monad `m`, ending
with a result of type `α`. In a prover round it computes a message and its continuation; in a
verifier round it awaits the challenge. -/
@[reducible] def ProverStrategy (m : Type → Type) : Spec → Type → Type
  | [], α => α
  | .prover M _ :: s, α => m (M × ProverStrategy m s α)
  | .verifier C :: s, α => C → m (ProverStrategy m s α)

/-- A prover from statements `StmtIn` with witnesses `WitIn` to statements `StmtOut` with witnesses
`WitOut`, using the oracles `oP`. -/
abbrev Prover {ιP : Type} (oP : OracleSpec ιP) (s : Spec) (StmtIn WitIn StmtOut WitOut : Type) :=
  StmtIn → WitIn → ProbOracleComp oP (ProverStrategy (ProbOracleComp oP) s (StmtOut × WitOut))

/-- A public-coin verifier from statements `StmtIn` to statements `StmtOut`, using the oracles
`oV`. Its challenges are drawn from `samplers`. Its decision sees the statement and the challenges,
queries the prover's messages and `oV`, and returns the output statement or rejects (`none`). -/
structure Verifier {ιV : Type} (oV : OracleSpec ιV) (s : Spec) (StmtIn StmtOut : Type) where
  /-- The distribution of each challenge. -/
  samplers : PerChallenge ProbComp s
  /-- The decision, with oracle access to the prover's messages. -/
  decide : StmtIn → Challenges s → OracleComp (oV ⊕ₒ msgSpec s) (Option StmtOut)

/-- An interactive reduction: an honest prover and a public-coin verifier. -/
structure Reduction {ιP ιV : Type} (oP : OracleSpec ιP) (oV : OracleSpec ιV) (s : Spec)
    (StmtIn WitIn StmtOut WitOut : Type) where
  /-- The honest prover. -/
  prover : Prover oP s StmtIn WitIn StmtOut WitOut
  /-- The verifier. -/
  verifier : Verifier oV s StmtIn StmtOut

/-! ### Execution -/

section Execution

variable {ιP ιV : Type} {oP : OracleSpec ιP} {oV : OracleSpec ιV}

/-- Lift a prover computation into the joint oracles. -/
def liftProver {α : Type} : ProbOracleComp oP α → ProbOracleComp (oP ⊕ₒ oV) α :=
  OracleComp.interpret (OracleComp.sumHandler
    (fun n => OracleComp.query (spec := probOracleSpec (oP ⊕ₒ oV)) (.inl n))
    (fun q => ProbOracleComp.query (spec := oP ⊕ₒ oV) (.inl q)))

/-- Run a prover strategy against public challenges drawn from `samplers`, returning the transcript
and the strategy's result. -/
def runStrategy {α : Type} :
    (s : Spec) → PerChallenge ProbComp s → ProverStrategy (ProbOracleComp oP) s α →
      ProbOracleComp oP (Transcript s × α)
  | [], _, a => pure ((), a)
  | .prover _ _ :: s, smp, st => do
    let (msg, st') ← st
    let (τ, a) ← runStrategy s smp st'
    return ((msg, τ), a)
  | .verifier _ :: s, smp, st => do
    let c ← ProbOracleComp.sample smp.1
    let st' ← st c
    let (τ, a) ← runStrategy s smp.2 st'
    return ((c, τ), a)

/-- Run the verifier's decision on a transcript, answering its queries about the prover's messages
from the transcript. -/
def Verifier.output {s : Spec} {StmtIn StmtOut : Type} (V : Verifier oV s StmtIn StmtOut)
    (x : StmtIn) (τ : Transcript s) : ProbOracleComp (oP ⊕ₒ oV) (Option StmtOut) :=
  OracleComp.interpret
    (OracleComp.sumHandler (fun q => ProbOracleComp.query (spec := oP ⊕ₒ oV) (.inr q))
      fun q => pure (Transcript.answer s τ q))
    (V.decide x (Transcript.challenges s τ))

/-- Run the verifier against any (possibly malicious) prover strategy with result type `α`: the
transcript, the verifier's output and the prover's result. -/
def Verifier.execute {s : Spec} {StmtIn StmtOut α : Type} (V : Verifier oV s StmtIn StmtOut)
    (x : StmtIn) (P : ProbOracleComp oP (ProverStrategy (ProbOracleComp oP) s α)) :
    ProbOracleComp (oP ⊕ₒ oV) (Transcript s × Option StmtOut × α) := do
  let st ← liftProver P
  let (τ, a) ← liftProver (runStrategy s V.samplers st)
  let out ← V.output (oP := oP) x τ
  return (τ, out, a)

/-- An honest run of a reduction on `x` with witness `w`. -/
def Reduction.run {s : Spec} {StmtIn WitIn StmtOut WitOut : Type}
    (R : Reduction oP oV s StmtIn WitIn StmtOut WitOut) (x : StmtIn) (w : WitIn) :
    ProbOracleComp (oP ⊕ₒ oV) (Transcript s × Option StmtOut × (StmtOut × WitOut)) :=
  R.verifier.execute x (R.prover x w)

/-- A model of the oracles: one stateful implementation of the prover's and verifier's oracles
(no oracles, a random oracle, an ideal functionality). -/
structure World {ιP ιV : Type} (oP : OracleSpec ιP) (oV : OracleSpec ιV) where
  /-- The private state of the oracles. -/
  State : Type
  /-- The initial state. -/
  init : State
  /-- The joint implementation. -/
  impl : (q : ιP ⊕ ιV) → StateT State PMF ((oP ⊕ₒ oV) q)

/-- The output law of a program in a world. -/
noncomputable def World.eval (W : World oP oV) {α : Type} (program : ProbOracleComp (oP ⊕ₒ oV) α) :
    PMF α :=
  (ProbOracleComp.runWith W.impl program W.init).map Prod.fst

/-- The plain model: no oracles. -/
def World.plain : World OracleSpec.empty OracleSpec.empty where
  State := Unit
  init := ()
  impl := OracleComp.sumHandler (fun e => e.elim) fun e => e.elim

end Execution

end Cslib.Interactive
