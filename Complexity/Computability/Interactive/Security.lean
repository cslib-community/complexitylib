/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Interactive.Basic

/-!
# Security of interactive reductions

Exact security notions for a reduction from a relation `relIn` to a relation `relOut`, in a world
`W` implementing the oracles. All errors are in `ℝ≥0∞`; a perfect notion is error `0`.

* `Reduction.Complete W R relIn relOut ε`: on every `(x, w)` in `relIn`, the honest run fails with
  probability at most `ε`, where success means that the verifier outputs the prover's statement
  and the prover's witness is valid for it.
* `Verifier.Sound W V langIn langOut ε`: on every `x ∉ langIn`, every prover strategy makes the
  verifier output a statement of `langOut` with probability at most `ε`.
* `Verifier.KnowledgeSound V relIn relOut E ε`: in the plain model, the straight-line extractor
  `E` recovers a valid input witness from the transcript and the prover's output witness, except
  with probability `ε`.
* `Verifier.RbrSound V langIn langOut ε`: round-by-round soundness in the plain model, with an
  error for every challenge round, through a state function on transcript prefixes.
* `Reduction.HVZK R relIn Sim ε`: in the plain model, the simulator's transcripts are `ε`-close
  in statistical distance to honest ones.

Interactive proofs and interactive oracle proofs are the reductions to the trivial relation
`Interactive.Accept`, with output language `Set.univ`. `Verifier.Sound` quantifies over all
prover strategies, with no query or time bound, so it is the information-theoretic notion in every
world; arguments and query-bounded soundness in oracle worlds are separate notions.
`Verifier.KnowledgeSound` is straight-line extraction from the transcript, as for interactive
oracle proofs; proofs of knowledge in the sense of Bellare and Goldreich, whose extractors rewind
the prover, are a different notion. Knowledge soundness and zero knowledge are stated in the plain
model: in an oracle world the extractor would need the prover's queries and the simulator the
oracle's view, which these definitions do not provide. Extractors and simulators are named
arguments, so a property cannot hold vacuously through an unconstrained existential. Their
efficiency is a separate layer: `Verifier.EfficientKnowledgeSound` and `Reduction.EfficientHVZK`
in `Complexity.Computability.Interactive.Efficient` add a polynomial-time extractor and a strict
PPT simulator over an indexed family of reductions.

## Main definitions

* `Interactive.language`, `Interactive.Accept`, `Interactive.CloseTo`.
* `Interactive.Reduction.Complete`, `Interactive.Verifier.Sound`,
  `Interactive.Verifier.KnowledgeSound`.
* `Interactive.Prefix`, `Interactive.Prefix.empty`, `Interactive.PerChallenge.sum`,
  `Interactive.RbrFrom`, `Interactive.Verifier.outputOn`, `Interactive.Verifier.RbrSound`.
* `Interactive.Reduction.HVZK`.

## References

* [R. Canetti, Y. Chen, J. Holmgren, A. Lombardi, G. N. Rothblum, R. D. Rothblum, D. Wichs,
  *Fiat–Shamir: from practice to theory*][CanettiCHLRRW2019]
-/

@[expose] public section

namespace Cslib.Interactive

open scoped ENNReal
open Spec

variable {ιP ιV : Type} {oP : OracleSpec ιP} {oV : OracleSpec ιV} {s : Spec}
  {StmtIn WitIn StmtOut WitOut : Type}

/-- The language of a relation: the statements with a witness. -/
def language {Stmt Wit : Type} (rel : Stmt → Wit → Prop) : Set Stmt := {x | ∃ w, rel x w}

/-- The trivial relation that proof systems reduce to: acceptance. -/
def Accept : Unit → Unit → Prop := fun _ _ => True

/-- `μ` is within statistical distance `ε` of `ν`: no event is more likely under `μ` than under
`ν` by more than `ε`. Quantifying over all events makes this symmetric, and it is the total
variation distance on any type, finite or not. -/
def CloseTo {α : Type} (μ ν : PMF α) (ε : ℝ≥0∞) : Prop :=
  ∀ event : Set α, μ.toOuterMeasure event ≤ ν.toOuterMeasure event + ε

/-- Statistical closeness is preserved by postprocessing. -/
theorem CloseTo.map {α β : Type} {μ ν : PMF α} {ε : ℝ≥0∞} (h : CloseTo μ ν ε) (f : α → β) :
    CloseTo (μ.map f) (ν.map f) ε := fun event => by
  simpa only [PMF.toOuterMeasure_map_apply] using h (f ⁻¹' event)

/-- Statistical closeness errors add along a chain. -/
theorem CloseTo.trans {α : Type} {μ ν ρ : PMF α} {ε δ : ℝ≥0∞} (h₁ : CloseTo μ ν ε)
    (h₂ : CloseTo ν ρ δ) : CloseTo μ ρ (ε + δ) := fun event =>
  (h₁ event).trans <| by
    rw [add_comm ε δ, ← add_assoc]
    exact add_le_add (h₂ event) le_rfl

/-! ### Completeness, soundness and knowledge soundness -/

/-- Completeness with error `ε`. -/
def Reduction.Complete (W : World oP oV) (R : Reduction oP oV s StmtIn WitIn StmtOut WitOut)
    (relIn : StmtIn → WitIn → Prop) (relOut : StmtOut → WitOut → Prop) (ε : ℝ≥0∞) : Prop :=
  ∀ x w, relIn x w →
    (W.eval (R.run x w)).toOuterMeasure
      {r | ¬ (r.2.1 = some r.2.2.1 ∧ relOut r.2.2.1 r.2.2.2)} ≤ ε

/-- Soundness with error `ε`, against every prover strategy. Provers are not bounded in time or
in oracle queries, so this is information-theoretic soundness in every world. -/
def Verifier.Sound (W : World oP oV) (V : Verifier oV s StmtIn StmtOut)
    (langIn : Set StmtIn) (langOut : Set StmtOut) (ε : ℝ≥0∞) : Prop :=
  ∀ x ∉ langIn, ∀ (α : Type) (P : ProbOracleComp oP (ProverStrategy (ProbOracleComp oP) s α)),
    (W.eval (V.execute x P)).toOuterMeasure {r | ∃ x' ∈ langOut, r.2.1 = some x'} ≤ ε

/-- Straight-line knowledge soundness with error `ε`, in the plain model: whenever a prover
strategy, ending with an output witness, makes the verifier output a statement for which that
witness is valid, the extractor `E` recovers a valid input witness from the statement, the
transcript and the output witness, except with probability `ε`. The extractor is an arbitrary
function; `Verifier.EfficientKnowledgeSound` adds the efficiency requirement. -/
def Verifier.KnowledgeSound (V : Verifier OracleSpec.empty s StmtIn StmtOut)
    (relIn : StmtIn → WitIn → Prop) (relOut : StmtOut → WitOut → Prop)
    (E : StmtIn → Transcript s → WitOut → WitIn) (ε : ℝ≥0∞) : Prop :=
  ∀ x (P : ProbOracleComp OracleSpec.empty
      (ProverStrategy (ProbOracleComp OracleSpec.empty) s WitOut)),
    (World.plain.eval (V.execute (oP := OracleSpec.empty) x P)).toOuterMeasure
      {r | (∃ x', r.2.1 = some x' ∧ relOut x' r.2.2) ∧ ¬ relIn x (E x r.1 r.2.2)} ≤ ε

/-! ### Round-by-round soundness -/

/-- The prefixes of transcripts: `none` is the empty prefix of a nonempty protocol, and a protocol
without rounds has only its complete (empty) transcript. -/
@[reducible] def Prefix : Spec → Type
  | [] => Unit
  | r :: s => Option (r.Message × Prefix s)

/-- The empty prefix. -/
def Prefix.empty : (s : Spec) → Prefix s
  | [] => ()
  | _ :: _ => none

/-- The total of per-round errors. -/
def PerChallenge.sum : (s : Spec) → PerChallenge (fun _ => ℝ≥0∞) s → ℝ≥0∞
  | [], _ => 0
  | .prover _ _ :: s, ε => PerChallenge.sum s ε
  | .verifier _ :: s, ε => ε.1 + PerChallenge.sum s ε.2

/-- The round-by-round condition on the rounds `s`, for the state function `S` on their prefixes
(false on doomed prefixes), per-round errors `ε` and the event `wins` on complete transcripts. A
prover message never leaves a doomed prefix; a challenge leaves one with probability at most its
error; and the verifier's output on a doomed complete transcript never wins. -/
def RbrFrom : (s : Spec) → PerChallenge ProbComp s → PerChallenge (fun _ => ℝ≥0∞) s →
    (Prefix s → Prop) → (Transcript s → Prop) → Prop
  | [], _, _, S, wins => ¬ S () → ¬ wins ()
  | .prover M _ :: s, smp, ε, S, wins =>
    (¬ S none → ∀ m : M, ¬ S (some (m, Prefix.empty s))) ∧
      ∀ m : M, RbrFrom s smp ε (fun p => S (some (m, p))) (fun τ => wins (m, τ))
  | .verifier C :: s, smp, ε, S, wins =>
    (¬ S none →
        (ProbComp.eval smp.1).toOuterMeasure {c : C | S (some (c, Prefix.empty s))} ≤ ε.1) ∧
      ∀ c : C, RbrFrom s smp.2 ε.2 (fun p => S (some (c, p))) (fun τ => wins (c, τ))

/-- The output of a verifier without oracles on a complete transcript. -/
noncomputable def Verifier.outputOn (V : Verifier OracleSpec.empty s StmtIn StmtOut) (x : StmtIn)
    (τ : Transcript s) : Option StmtOut :=
  OracleComp.interpret (m := Id)
    (OracleComp.sumHandler (fun e => e.elim) (Transcript.answer s τ))
    (V.decide x (Transcript.challenges s τ))

/-- Round-by-round soundness in the plain model with per-round errors `ε`: some state function is
false on the empty prefix of every `x ∉ langIn` and satisfies the round-by-round condition. -/
def Verifier.RbrSound (V : Verifier OracleSpec.empty s StmtIn StmtOut) (langIn : Set StmtIn)
    (langOut : Set StmtOut) (ε : PerChallenge (fun _ => ℝ≥0∞) s) : Prop :=
  ∃ S : StmtIn → Prefix s → Prop, (∀ x ∉ langIn, ¬ S x (Prefix.empty s)) ∧
    ∀ x, RbrFrom s V.samplers ε (S x) fun τ => ∃ x' ∈ langOut, V.outputOn x τ = some x'

/-! ### Zero knowledge -/

/-- Honest-verifier zero knowledge with statistical error `ε` (perfect for `ε = 0`), in the plain
model: on every `(x, w)` in `relIn`, the simulator's transcript law is `ε`-close to the honest
one. The simulator need not be efficient; `Reduction.EfficientHVZK` adds the efficiency
requirement. -/
def Reduction.HVZK (R : Reduction OracleSpec.empty OracleSpec.empty s StmtIn WitIn StmtOut WitOut)
    (relIn : StmtIn → WitIn → Prop) (Sim : StmtIn → ProbComp (Transcript s)) (ε : ℝ≥0∞) :
    Prop :=
  ∀ x w, relIn x w →
    CloseTo ((World.plain.eval (R.run x w)).map Prod.fst) (ProbComp.eval (Sim x)) ε

end Cslib.Interactive
