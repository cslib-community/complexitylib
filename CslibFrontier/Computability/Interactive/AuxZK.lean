/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Interactive.Efficient
public import CslibFrontier.Computability.Interactive.Sequential
public import CslibFrontier.Computability.Probabilistic.Parameter
public import CslibFrontier.Crypto.Game.CloseTo
import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.EventBind

/-!
# Auxiliary-input zero knowledge and product composition for interactive reductions

This module extends the public-coin interactive reduction core (`Cslib.Interactive`) in two
directions from the zero-knowledge roadmap:

1. **Auxiliary-input zero knowledge** ([Goldreich2001], §4.3.3, Definition 4.3.10;
   [AroraBarak09], Chapter 9):
   * `Reduction.PerfectHVZK`, `Reduction.AuxHVZK`, `Reduction.PerfectAuxHVZK`: exact and
     statistical (`CloseTo`) honest-verifier zero knowledge in the plain model when the simulator
     (and error bound) may depend on an auxiliary input `z : Aux`. Every `HVZK` / `PerfectHVZK`
     reduction is automatically `AuxHVZK` / `PerfectAuxHVZK` by ignoring `z`
     (`Reduction.HVZK.auxHVZK`, `Reduction.PerfectHVZK.perfectAuxHVZK`), and conversely
     instantiating at any `z₀ : Aux` recovers `HVZK` / `PerfectHVZK`.
   * `VerifierStrategy`, `runAgainst`, `Reduction.viewOf`, `Reduction.ZK`: statistical
     malicious-verifier auxiliary-input zero knowledge in the plain model, with unbounded
     verifiers and an unbounded simulator, where a strategy tree of the verifier's role adaptively
     chooses challenges and outputs an arbitrary view. It is not the computational definition of
     [Goldreich2001], whose verifiers and simulators are efficient. Embedding the honest
     verifier's challenge samplers (`honestVerifierStrategy`) proves that `Reduction.ZK` implies
     `Reduction.AuxHVZK` (`Reduction.ZK.auxHVZK`).
   * `AuxSimulatorRealizedBy`, `Reduction.EfficientAuxHVZK`: uniform strict-PPT realization of an
     auxiliary-input simulator family over encoded statements and auxiliary inputs up to
     statistical error `δ`, with `Reduction.EfficientHVZK.efficientAuxHVZK` lifting any
     `EfficientHVZK` certificate.
   * `Reduction.ComputationalHVZK`, `Reduction.ComputationalAuxHVZK`: computational
     honest-verifier zero knowledge over polynomially bounded families against uniform strict-PPT
     auxiliary-input distinguishers, with unconditional statistical-to-computational bridges
     (`AuxSimulatorRealizedBy.computationalAuxHVZK`,
     `Reduction.EfficientAuxHVZK.exists_computationalAuxHVZK`,
     `Reduction.EfficientHVZK.exists_computationalHVZK_zero`) and the lifting theorem
     `Reduction.ComputationalHVZK.computationalAuxHVZK`.
2. **Product (AND) composition of interactive reductions** (`Verifier.seqProd`,
   `Reduction.seqProd`) over `s₁ ++ s₂` for product relations `relProd` (alongside the disjunctive
   relation `relDisj`):
   * Completeness errors add (`Reduction.Complete.seqProd`), preserving perfect completeness.
   * Soundness error against `language (relProd relIn₁ relIn₂)` is `max ε₁ ε₂`
     (`Verifier.Sound.seqProd`), since a false product statement is false in at least one
     coordinate.
   * Straight-line knowledge soundness composes with the product extractor
     `Verifier.extractSeqProd` and error `κ₁ + κ₂` (`Verifier.KnowledgeSound.seqProd`).
   * `HVZK`, `PerfectHVZK`, `AuxHVZK`, and `PerfectAuxHVZK` compose via independent transcript
     simulation (`simSeqProd`, `auxSimSeqProd`) with additive statistical errors
     (`Reduction.HVZK.seqProd`, `Reduction.PerfectHVZK.seqProd`, `Reduction.AuxHVZK.seqProd`,
     `Reduction.PerfectAuxHVZK.seqProd`).

## Main definitions

* `Cslib.Interactive.Reduction.honestTranscript`, `Cslib.Interactive.Reduction.PerfectHVZK`,
  `Cslib.Interactive.Reduction.AuxHVZK`, `Cslib.Interactive.Reduction.PerfectAuxHVZK`.
* `Cslib.Interactive.VerifierStrategy`, `Cslib.Interactive.runAgainst`,
  `Cslib.Interactive.Reduction.viewOf`, `Cslib.Interactive.Reduction.ZK`,
  `Cslib.Interactive.honestVerifierStrategy`.
* `Cslib.Interactive.Encoding.encStatementAux`, `Cslib.Interactive.AuxSimulatorRealizedBy`,
  `Cslib.Interactive.Reduction.EfficientAuxHVZK`, `Cslib.Interactive.Reduction.ComputationalHVZK`,
  `Cslib.Interactive.Reduction.ComputationalAuxHVZK`.
* `Cslib.Interactive.relProd`, `Cslib.Interactive.relDisj`,
  `Cslib.Interactive.Verifier.liftFirst`, `Cslib.Interactive.Verifier.liftSecond`,
  `Cslib.Interactive.Verifier.seqProd`, `Cslib.Interactive.Reduction.liftFirst`,
  `Cslib.Interactive.Reduction.liftSecond`, `Cslib.Interactive.Reduction.seqProd`,
  `Cslib.Interactive.Verifier.extractSeqProd`, `Cslib.Interactive.simSeqProd`,
  `Cslib.Interactive.auxSimSeqProd`.

## Main results

* `Cslib.Interactive.Reduction.HVZK.auxHVZK`,
  `Cslib.Interactive.Reduction.PerfectHVZK.perfectAuxHVZK`,
  `Cslib.Interactive.Reduction.ZK.auxHVZK`,
  `Cslib.Interactive.Reduction.EfficientHVZK.efficientAuxHVZK`,
  `Cslib.Interactive.Reduction.ComputationalHVZK.computationalAuxHVZK`,
  `Cslib.Interactive.AuxSimulatorRealizedBy.computationalAuxHVZK`,
  `Cslib.Interactive.Reduction.EfficientAuxHVZK.exists_computationalAuxHVZK`,
  `Cslib.Interactive.Reduction.EfficientHVZK.exists_computationalHVZK_zero`.
* `Cslib.Interactive.Reduction.Complete.seqProd`,
  `Cslib.Interactive.Verifier.Sound.seqProd`,
  `Cslib.Interactive.Verifier.KnowledgeSound.seqProd`,
  `Cslib.Interactive.Reduction.HVZK.seqProd`,
  `Cslib.Interactive.Reduction.PerfectHVZK.seqProd`,
  `Cslib.Interactive.Reduction.AuxHVZK.seqProd`,
  `Cslib.Interactive.Reduction.PerfectAuxHVZK.seqProd`.

## References

* [O. Goldreich, *Foundations of Cryptography: Volume 1, Basic Tools*][Goldreich2001],
  Section 4.3.3 (Auxiliary-Input Zero-Knowledge, Definition 4.3.10).
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Chapter 9.
* [E. Ben-Sasson, A. Chiesa, N. Spooner, *Interactive Oracle Proofs*][BenSassonChiesaSpooner2016]
-/

@[expose] public section

namespace Cslib.Interactive

open scoped ENNReal NNReal
open Spec Probability Turing.MultiTapeTM Crypto

variable {s : Spec} {StmtIn WitIn StmtOut WitOut Aux View : Type}

/-! ### Part 1: Auxiliary-input zero knowledge -/

/-- The distribution of transcripts in an honest plain-model run of `R` on `(x, w)`. -/
noncomputable abbrev Reduction.honestTranscript
    (R : Reduction OracleSpec.empty OracleSpec.empty s StmtIn WitIn StmtOut WitOut)
    (x : StmtIn) (w : WitIn) : PMF (Transcript s) :=
  (World.plain.eval (R.run x w)).map Prod.fst

/-- In the plain model, `R.honestTranscript x w` is the first marginal of running `R.prover x w`
against `R.verifier.samplers`. -/
theorem Reduction.honestTranscript_eq_plainLaw
    (R : Reduction OracleSpec.empty OracleSpec.empty s StmtIn WitIn StmtOut WitOut)
    (x : StmtIn) (w : WitIn) :
    R.honestTranscript x w =
      (plainLaw (R.prover x w >>= runStrategy s R.verifier.samplers)).map Prod.fst := by
  rw [Reduction.honestTranscript, Reduction.run, World.plain_eval_execute, PMF.map_comp]
  rfl

/-- Perfect honest-verifier zero knowledge in the plain model: on every valid `(x, w)` in `relIn`,
the simulator's transcript law equals the honest transcript law. -/
def Reduction.PerfectHVZK
    (R : Reduction OracleSpec.empty OracleSpec.empty s StmtIn WitIn StmtOut WitOut)
    (relIn : StmtIn → WitIn → Prop) (Sim : StmtIn → ProbComp (Transcript s)) : Prop :=
  ∀ x w, relIn x w → R.honestTranscript x w = ProbComp.eval (Sim x)

/-- Perfect HVZK implies `0`-error statistical HVZK. -/
theorem Reduction.PerfectHVZK.hvzk
    {R : Reduction OracleSpec.empty OracleSpec.empty s StmtIn WitIn StmtOut WitOut}
    {relIn : StmtIn → WitIn → Prop} {Sim : StmtIn → ProbComp (Transcript s)}
    (h : R.PerfectHVZK relIn Sim) : R.HVZK relIn Sim 0 := by
  intro x w hxw
  rw [ ← Reduction.honestTranscript, h x w hxw]
  exact CloseTo.refl _

/-- Enlarging the statistical error preserves `Reduction.HVZK`. -/
theorem Reduction.HVZK.mono
    {R : Reduction OracleSpec.empty OracleSpec.empty s StmtIn WitIn StmtOut WitOut}
    {relIn : StmtIn → WitIn → Prop} {Sim : StmtIn → ProbComp (Transcript s)} {ε δ : ℝ≥0∞}
    (h : R.HVZK relIn Sim ε) (hle : ε ≤ δ) : R.HVZK relIn Sim δ :=
  fun x w hxw => (h x w hxw).mono hle

/-- **Auxiliary-input honest-verifier zero knowledge** ([Goldreich2001], §4.3.3, Definition 4.3.10
for an honest verifier) with statistical error `ε x z`, in the plain model: on every `(x, w)` in
`relIn` and every auxiliary input `z : Aux`, the simulator `Sim x z` produces transcripts within
statistical distance `ε x z` of the honest transcript distribution. -/
def Reduction.AuxHVZK
    (R : Reduction OracleSpec.empty OracleSpec.empty s StmtIn WitIn StmtOut WitOut)
    (relIn : StmtIn → WitIn → Prop)
    (Sim : StmtIn → Aux → ProbComp (Transcript s)) (ε : StmtIn → Aux → ℝ≥0∞) : Prop :=
  ∀ x w z, relIn x w → CloseTo (R.honestTranscript x w) (ProbComp.eval (Sim x z)) (ε x z)

/-- **Perfect auxiliary-input honest-verifier zero knowledge** in the plain model: on every
`(x, w)` in `relIn` and every auxiliary input `z : Aux`, the simulator `Sim x z` reproduces the
honest transcript distribution exactly. -/
def Reduction.PerfectAuxHVZK
    (R : Reduction OracleSpec.empty OracleSpec.empty s StmtIn WitIn StmtOut WitOut)
    (relIn : StmtIn → WitIn → Prop)
    (Sim : StmtIn → Aux → ProbComp (Transcript s)) : Prop :=
  ∀ x w z, relIn x w → R.honestTranscript x w = ProbComp.eval (Sim x z)

/-- Perfect auxiliary-input HVZK implies `0`-error statistical `AuxHVZK`. -/
theorem Reduction.PerfectAuxHVZK.auxHVZK
    {R : Reduction OracleSpec.empty OracleSpec.empty s StmtIn WitIn StmtOut WitOut}
    {relIn : StmtIn → WitIn → Prop} {Sim : StmtIn → Aux → ProbComp (Transcript s)}
    (h : R.PerfectAuxHVZK relIn Sim) : R.AuxHVZK relIn Sim (fun _ _ => 0) := by
  intro x w z hxw
  rw [h x w z hxw]
  exact CloseTo.refl _

/-- Enlarging the error bound pointwise preserves `Reduction.AuxHVZK`. -/
theorem Reduction.AuxHVZK.mono
    {R : Reduction OracleSpec.empty OracleSpec.empty s StmtIn WitIn StmtOut WitOut}
    {relIn : StmtIn → WitIn → Prop} {Sim : StmtIn → Aux → ProbComp (Transcript s)}
    {ε δ : StmtIn → Aux → ℝ≥0∞} (h : R.AuxHVZK relIn Sim ε) (hle : ∀ x z, ε x z ≤ δ x z) :
    R.AuxHVZK relIn Sim δ :=
  fun x w z hxw => (h x w z hxw).mono (hle x z)

/-- **Every `HVZK` reduction is automatically `AuxHVZK`**: an honest-verifier simulator only needs
the statement `x` and can ignore the auxiliary input `z`. -/
theorem Reduction.HVZK.auxHVZK
    {R : Reduction OracleSpec.empty OracleSpec.empty s StmtIn WitIn StmtOut WitOut}
    {relIn : StmtIn → WitIn → Prop} {Sim : StmtIn → ProbComp (Transcript s)} {ε : ℝ≥0∞}
    (h : R.HVZK relIn Sim ε) :
    R.AuxHVZK relIn (fun x (_ : Aux) => Sim x) (fun _ _ => ε) :=
  fun x w _ hxw => h x w hxw

/-- **Every `PerfectHVZK` reduction is automatically `PerfectAuxHVZK`** by ignoring the auxiliary
input `z`. -/
theorem Reduction.PerfectHVZK.perfectAuxHVZK
    {R : Reduction OracleSpec.empty OracleSpec.empty s StmtIn WitIn StmtOut WitOut}
    {relIn : StmtIn → WitIn → Prop} {Sim : StmtIn → ProbComp (Transcript s)}
    (h : R.PerfectHVZK relIn Sim) :
    R.PerfectAuxHVZK relIn (fun x (_ : Aux) => Sim x) :=
  fun x w _ hxw => h x w hxw

/-- Instantiating an `AuxHVZK` simulator at a fixed auxiliary input `z₀` yields `HVZK` when the
error bound at `z₀` is at most `ε`. -/
theorem Reduction.AuxHVZK.hvzk
    {R : Reduction OracleSpec.empty OracleSpec.empty s StmtIn WitIn StmtOut WitOut}
    {relIn : StmtIn → WitIn → Prop} {Sim : StmtIn → Aux → ProbComp (Transcript s)}
    {ε : StmtIn → Aux → ℝ≥0∞} {ε₀ : ℝ≥0∞}
    (h : R.AuxHVZK relIn Sim ε) (z₀ : Aux) (hle : ∀ x, ε x z₀ ≤ ε₀) :
    R.HVZK relIn (fun x => Sim x z₀) ε₀ :=
  fun x w hxw => (h x w z₀ hxw).mono (hle x)

/-- Instantiating a `PerfectAuxHVZK` simulator at any `z₀ : Aux` yields `PerfectHVZK`. -/
theorem Reduction.PerfectAuxHVZK.perfectHVZK
    {R : Reduction OracleSpec.empty OracleSpec.empty s StmtIn WitIn StmtOut WitOut}
    {relIn : StmtIn → WitIn → Prop} {Sim : StmtIn → Aux → ProbComp (Transcript s)}
    (h : R.PerfectAuxHVZK relIn Sim) (z₀ : Aux) :
    R.PerfectHVZK relIn (fun x => Sim x z₀) :=
  fun x w hxw => h x w z₀ hxw

/-- Under `AuxHVZK`, any randomized Boolean distinguisher `D : StmtIn → Aux → Transcript s → Game`
(receiving the statement, the auxiliary input, and the transcript) has distinguishing advantage at
most `ε x z` on every valid `(x, w)`. -/
theorem Reduction.AuxHVZK.coe_advantage_le
    {R : Reduction OracleSpec.empty OracleSpec.empty s StmtIn WitIn StmtOut WitOut}
    {relIn : StmtIn → WitIn → Prop} {Sim : StmtIn → Aux → ProbComp (Transcript s)}
    {ε : StmtIn → Aux → ℝ≥0∞} (h : R.AuxHVZK relIn Sim ε)
    (D : StmtIn → Aux → Transcript s → Game) {x : StmtIn} {w : WitIn} (z : Aux)
    (hxw : relIn x w) :
    (Game.advantage ((R.honestTranscript x w).bind (D x z))
      ((ProbComp.eval (Sim x z)).bind (D x z)) : ℝ≥0∞) ≤ ε x z :=
  Game.coe_advantage_bind_le_of_closeTo (h x w z hxw) (D x z)

/-! ### Malicious-verifier auxiliary-input zero knowledge in the plain model -/

/-- A strategy of the verifier's role over the rounds `s`, in the monad `m`, ending with an output
of type `α` (its view). It receives each prover message and chooses each challenge. -/
@[reducible] def VerifierStrategy (m : Type → Type) : Spec → Type → Type
  | [], α => m α
  | .prover M _ :: s, α => M → m (VerifierStrategy m s α)
  | .verifier C :: s, α => m (C × VerifierStrategy m s α)

/-- Run a prover strategy against a verifier strategy, returning the transcript and both outputs. -/
def runAgainst {m : Type → Type} [Monad m] {α β : Type} :
    (s : Spec) → ProverStrategy m s α → VerifierStrategy m s β → m (Transcript s × α × β)
  | [], a, v => do
    let v : m β := v
    let b ← v
    return ((), a, b)
  | .prover M _ :: s, p, v => do
    let p : m (M × ProverStrategy m s α) := p
    let v : M → m (VerifierStrategy m s β) := v
    let (msg, p') ← p
    let v' ← v msg
    let r ← runAgainst s p' v'
    return ((msg, r.1), r.2)
  | .verifier C :: s, p, v => do
    let p : C → m (ProverStrategy m s α) := p
    let v : m (C × VerifierStrategy m s β) := v
    let (c, v') ← v
    let p' ← p c
    let r ← runAgainst s p' v'
    return ((c, r.1), r.2)

/-- The law of a malicious verifier's view after interacting with the honest prover of `R` on
`(x, w)` and auxiliary input `z : Aux`. -/
noncomputable def Reduction.viewOf
    (R : Reduction OracleSpec.empty OracleSpec.empty s StmtIn WitIn StmtOut WitOut)
    (Vstar : StmtIn → Aux →
      ProbOracleComp OracleSpec.empty (VerifierStrategy (ProbOracleComp OracleSpec.empty) s View))
    (x : StmtIn) (w : WitIn) (z : Aux) : PMF View :=
  plainLaw do
    let p ← R.prover x w
    let v ← Vstar x z
    let (_, _, view) ← runAgainst s p v
    return view

/-- **Statistical malicious-verifier auxiliary-input zero knowledge, with an unbounded simulator
and verifier**, in the plain model: for every malicious verifier `Vstar`, every valid `(x, w)` in
`relIn`, and every auxiliary input `z : Aux`, the simulator `Sim Vstar x z` reproduces `Vstar`'s
view within statistical distance `ε x z`. Neither `Vstar` nor `Sim` is required to be efficient,
and closeness is statistical, so this is not the computational auxiliary-input definition of
[Goldreich2001], §4.3.3, Definition 4.3.10, whose verifiers and simulators are efficient. An
efficient variant is not formalized. -/
def Reduction.ZK
    (R : Reduction OracleSpec.empty OracleSpec.empty s StmtIn WitIn StmtOut WitOut)
    (relIn : StmtIn → WitIn → Prop)
    (Sim : (StmtIn → Aux →
        ProbOracleComp OracleSpec.empty
          (VerifierStrategy (ProbOracleComp OracleSpec.empty) s View)) →
      StmtIn → Aux → ProbComp View)
    (ε : StmtIn → Aux → ℝ≥0∞) : Prop :=
  ∀ Vstar x w z, relIn x w →
    CloseTo (R.viewOf Vstar x w z) (ProbComp.eval (Sim Vstar x z)) (ε x z)

/-- Map a function over the output view of a `VerifierStrategy`. -/
def VerifierStrategy.map {m : Type → Type} [Functor m] {α β : Type} :
    (s : Spec) → (α → β) → VerifierStrategy m s α → VerifierStrategy m s β
  | [], f, v => (f <$> (v : m α) : m β)
  | .prover M _ :: s, f, v => fun msg : M =>
    (VerifierStrategy.map s f <$> (v : M → m (VerifierStrategy m s α)) msg :
      m (VerifierStrategy m s β))
  | .verifier C :: s, f, v =>
    ((fun p => (p.1, VerifierStrategy.map s f p.2)) <$> (v : m (C × VerifierStrategy m s α)) :
      m (C × VerifierStrategy m s β))

/-- Running against a mapped `VerifierStrategy` maps the verifier's output in `plainLaw`. -/
theorem plainLaw_runAgainst_map : ∀ (s : Spec) {α β γ : Type} (f : β → γ)
    (p : ProverStrategy (ProbOracleComp OracleSpec.empty) s α)
    (v : VerifierStrategy (ProbOracleComp OracleSpec.empty) s β),
    plainLaw (runAgainst s p (VerifierStrategy.map s f v)) =
      (plainLaw (runAgainst s p v)).map fun (τ, a, b) => (τ, a, f b)
  | [], _, _, _, f, a, v => by
    simp [VerifierStrategy.map, runAgainst, PMF.map_comp, Function.comp_def]
  | .prover M _ :: s, _, _, _, f, p, v => by
    simp only [VerifierStrategy.map, runAgainst, plainLaw_bind, plainLaw_map, plainLaw_pure,
      PMF.bind_map, PMF.map_bind, PMF.pure_map, Function.comp_def]
    congr 1
    funext x
    congr 1
    funext v'
    rw [plainLaw_runAgainst_map s f x.2 v']
    simp [PMF.bind_map, Function.comp_def]
  | .verifier C :: s, _, _, _, f, p, v => by
    simp only [VerifierStrategy.map, runAgainst, plainLaw_bind, plainLaw_map, plainLaw_pure,
      PMF.bind_map, PMF.map_bind, PMF.pure_map, Function.comp_def]
    congr 1
    funext x
    congr 1
    funext p'
    rw [plainLaw_runAgainst_map s f p' x.2]
    simp [PMF.bind_map, Function.comp_def]

/-- The honest public-coin verifier's challenge samplers embedded as a `VerifierStrategy` whose
output view is the complete transcript `Transcript s`. -/
def honestVerifierStrategy :
    (s : Spec) → PerChallenge ProbComp s →
      VerifierStrategy (ProbOracleComp OracleSpec.empty) s (Transcript s)
  | [], _ => (pure () : ProbOracleComp OracleSpec.empty Unit)
  | .prover M _ :: s, smp => fun msg : M =>
    (pure (VerifierStrategy.map s (msg, ·) (honestVerifierStrategy s smp)) :
      ProbOracleComp OracleSpec.empty
        (VerifierStrategy (ProbOracleComp OracleSpec.empty) s (M × Transcript s)))
  | .verifier C :: s, smp =>
    ((fun c => (c, VerifierStrategy.map s (c, ·) (honestVerifierStrategy s smp.2))) <$>
      ProbOracleComp.sample smp.1 :
        ProbOracleComp OracleSpec.empty
          (C × VerifierStrategy (ProbOracleComp OracleSpec.empty) s (C × Transcript s)))

/-- Running a prover strategy against `honestVerifierStrategy` has the same law as `runStrategy`,
recording the transcript as the verifier's output view as well. -/
theorem plainLaw_runAgainst_honestVerifierStrategy :
    ∀ (s : Spec) (smp : PerChallenge ProbComp s) {α : Type}
      (p : ProverStrategy (ProbOracleComp OracleSpec.empty) s α),
      plainLaw (runAgainst s p (honestVerifierStrategy s smp)) =
        (plainLaw (runStrategy s smp p)).map fun r => (r.1, r.2, r.1)
  | [], _, _, a => by
    simp [honestVerifierStrategy, runAgainst, runStrategy]
  | .prover M _ :: s, smp, _, p => by
    simp only [honestVerifierStrategy, runAgainst, runStrategy, plainLaw_bind, plainLaw_pure,
      PMF.pure_bind, PMF.map_bind]
    congr 1
    funext x
    rw [plainLaw_runAgainst_map, plainLaw_runAgainst_honestVerifierStrategy s smp x.2]
    simp [PMF.bind_map, Function.comp_def]
  | .verifier C :: s, smp, _, p => by
    simp only [honestVerifierStrategy, runAgainst, runStrategy, plainLaw_bind, plainLaw_map,
      plainLaw_pure, plainLaw_sample, PMF.bind_map, PMF.map_bind, Function.comp_def]
    congr 1
    funext c
    congr 1
    funext p'
    rw [plainLaw_runAgainst_map, plainLaw_runAgainst_honestVerifierStrategy s smp.2 p']
    simp [PMF.bind_map, Function.comp_def]

/-- The view of `honestVerifierStrategy` on `(x, w)` is `R.honestTranscript x w`. -/
theorem Reduction.viewOf_honestVerifierStrategy
    (R : Reduction OracleSpec.empty OracleSpec.empty s StmtIn WitIn StmtOut WitOut)
    (x : StmtIn) (w : WitIn) (z : Aux) :
    R.viewOf (fun _ _ => pure (honestVerifierStrategy s R.verifier.samplers)) x w z =
      R.honestTranscript x w := by
  rw [Reduction.viewOf, Reduction.honestTranscript_eq_plainLaw]
  simp only [plainLaw_bind, plainLaw_pure, PMF.pure_bind, PMF.map_bind]
  congr 1
  funext p
  rw [plainLaw_runAgainst_honestVerifierStrategy, PMF.bind_map]
  rfl

/-- **Statistical malicious-verifier auxiliary-input zero knowledge (`Reduction.ZK`) implies
honest-verifier auxiliary-input zero knowledge (`Reduction.AuxHVZK`).** -/
theorem Reduction.ZK.auxHVZK
    {R : Reduction OracleSpec.empty OracleSpec.empty s StmtIn WitIn StmtOut WitOut}
    {relIn : StmtIn → WitIn → Prop}
    {Sim : (StmtIn → Aux →
        ProbOracleComp OracleSpec.empty
          (VerifierStrategy (ProbOracleComp OracleSpec.empty) s (Transcript s))) →
      StmtIn → Aux → ProbComp (Transcript s)}
    {ε : StmtIn → Aux → ℝ≥0∞}
    (h : R.ZK relIn Sim ε) :
    R.AuxHVZK relIn
      (Sim (fun _ _ => pure (honestVerifierStrategy s R.verifier.samplers))) ε := by
  intro x w z hxw
  rw [← R.viewOf_honestVerifierStrategy x w z]
  exact h _ x w z hxw

/-! ### Efficient and computational auxiliary-input HVZK -/

section Indexed

variable {I : Type} {sI : I → Spec} {StmtI WitI StmtOutI WitOutI AuxI : I → Type}

/-- Family index, encoded statement and auxiliary input word `(i, x, z)`: the index under
`enc.index`, then `x` and `z` as bit words (`enc.index` and `x` framed, `z` unframed). An
auxiliary-input simulator reads this triple; a transcript distinguisher reads it after the unary
parameter, paired with an encoded transcript, with an auxiliary input word in the `z` slot. -/
abbrev Encoding.encStatementAux (enc : Encoding I sI StmtI) :
    I × List Bool × List Bool ↪ List Bool :=
  encPair enc.index (encPair encBits encBits)

/-- The program `program` realizes the auxiliary-input simulator family `Sim` on encodings up to
statistical distance `δ`: on `(i, enc.statement i x, encAux i z)`, its output is within `δ i` of
the encoded transcript sampled by `Sim i x z`. -/
def AuxSimulatorRealizedBy (enc : Encoding I sI StmtI) (encAux : ∀ i, AuxI i ↪ List Bool)
    (Sim : ∀ i, StmtI i → AuxI i → ProbComp (Transcript (sI i)))
    (program : I × List Bool × List Bool → ProbComp (List Bool)) (δ : I → ℝ≥0∞) : Prop :=
  ∀ i x z, CloseTo ((ProbComp.eval (Sim i x z)).map (enc.transcript i))
    (ProbComp.eval (program (i, enc.statement i x, encAux i z))) (δ i)

/-- A program realizing an `AuxHVZK` simulator up to `δ` is `ε i + δ i`-close to the honest encoded
transcript for every valid `(x, w)` and auxiliary input `z`. -/
theorem AuxSimulatorRealizedBy.closeTo_run
    {R : ∀ i, Reduction OracleSpec.empty OracleSpec.empty (sI i) (StmtI i) (WitI i) (StmtOutI i)
      (WitOutI i)}
    {rel : ∀ i, StmtI i → WitI i → Prop} {enc : Encoding I sI StmtI}
    {encAux : ∀ i, AuxI i ↪ List Bool}
    {Sim : ∀ i, StmtI i → AuxI i → ProbComp (Transcript (sI i))}
    {program : I × List Bool × List Bool → ProbComp (List Bool)} {ε δ : I → ℝ≥0∞}
    (hzk : ∀ i, (R i).AuxHVZK (rel i) (Sim i) (fun _ _ => ε i))
    (h : AuxSimulatorRealizedBy enc encAux Sim program δ)
    {i : I} {x : StmtI i} {w : WitI i} (z : AuxI i) (hxw : rel i x w) :
    CloseTo (((R i).honestTranscript x w).map (enc.transcript i))
      (ProbComp.eval (program (i, enc.statement i x, encAux i z))) (ε i + δ i) :=
  ((hzk i x w z hxw).map (enc.transcript i)).trans (h i x z)

/-- A `SimulatorRealizedBy` witness lifts to `AuxSimulatorRealizedBy` by ignoring the encoded
auxiliary input. -/
theorem SimulatorRealizedBy.auxSimulatorRealizedBy
    {enc : Encoding I sI StmtI} (encAux : ∀ i, AuxI i ↪ List Bool)
    {Sim : ∀ i, StmtI i → ProbComp (Transcript (sI i))}
    {program : I × List Bool → ProbComp (List Bool)} {δ : I → ℝ≥0∞}
    (h : SimulatorRealizedBy enc Sim program δ) :
    AuxSimulatorRealizedBy enc encAux (fun i x _ => Sim i x)
      (fun (i, xw, _) => program (i, xw)) δ :=
  fun i x _ => h i x

/-- **Efficient auxiliary-input honest-verifier zero knowledge**, with simulation error `ε` and
realization error `δ`. At every index `i`, `Sim i` is an `ε i`-`AuxHVZK` simulator for `R i`, and
one uniform strict PPT program of `(i, enc.statement i x, encAux i z)` realizes the simulator
family on encoded transcripts up to `δ`. -/
structure Reduction.EfficientAuxHVZK
    (R : ∀ i, Reduction OracleSpec.empty OracleSpec.empty (sI i) (StmtI i) (WitI i) (StmtOutI i)
      (WitOutI i))
    (rel : ∀ i, StmtI i → WitI i → Prop) (enc : Encoding I sI StmtI)
    (encAux : ∀ i, AuxI i ↪ List Bool)
    (Sim : ∀ i, StmtI i → AuxI i → ProbComp (Transcript (sI i))) (ε δ : I → ℝ≥0∞) : Prop where
  /-- `Sim i` is an `ε i`-AuxHVZK simulator at every index. -/
  auxHVZK : ∀ i, (R i).AuxHVZK (rel i) (Sim i) (fun _ _ => ε i)
  /-- One uniform strict PPT program of the index, statement and auxiliary input realizes `Sim` up
  to `δ`. -/
  realized : ∃ program,
    IsPPTOn enc.encStatementAux encBits program ∧
      AuxSimulatorRealizedBy enc encAux Sim program δ

/-- **Every `EfficientHVZK` reduction is automatically `EfficientAuxHVZK`**: the simulator and its
strict PPT realizing program ignore the auxiliary input. -/
theorem Reduction.EfficientHVZK.efficientAuxHVZK
    {R : ∀ i, Reduction OracleSpec.empty OracleSpec.empty (sI i) (StmtI i) (WitI i) (StmtOutI i)
      (WitOutI i)}
    {rel : ∀ i, StmtI i → WitI i → Prop} {enc : Encoding I sI StmtI}
    (encAux : ∀ i, AuxI i ↪ List Bool)
    {Sim : ∀ i, StmtI i → ProbComp (Transcript (sI i))} {ε δ : I → ℝ≥0∞}
    (h : Reduction.EfficientHVZK R rel enc Sim ε δ) :
    Reduction.EfficientAuxHVZK R rel enc encAux (fun i x _ => Sim i x) ε δ where
  auxHVZK i := (h.hvzk i).auxHVZK
  realized := by
    obtain ⟨program, hppt, hreal⟩ := h.realized
    refine ⟨fun (i, xw, _) => program (i, xw), ?_, hreal.auxSimulatorRealizedBy encAux⟩
    exact hppt.preprocess (prepare := fun p : I × List Bool × List Bool => (p.1, p.2.1))
      (by fun_prop)

/-- **Computational honest-verifier zero knowledge** over an indexed family of reductions: one
uniform strict PPT simulator `program` on `(i, enc.statement i x)` produces encoded transcripts
that are computationally indistinguishable from honest encoded transcripts across all polynomially
bounded valid families `(i n, x n, w n)` and distinguisher auxiliary inputs `z n`, against every
uniform strict PPT distinguisher clocked on `((1^n, i n, enc.statement (i n) (x n), z n), τ)`. -/
structure Reduction.ComputationalHVZK
    (R : ∀ i, Reduction OracleSpec.empty OracleSpec.empty (sI i) (StmtI i) (WitI i) (StmtOutI i)
      (WitOutI i))
    (rel : ∀ i, StmtI i → WitI i → Prop) (enc : Encoding I sI StmtI)
    (program : I × List Bool → ProbComp (List Bool)) : Prop where
  /-- The simulator program is uniform strict PPT in `(i, enc.statement i x)`. -/
  ppt : IsPPTOn (encPair enc.index encBits) encBits program
  /-- Honest and simulated encoded transcripts have negligible distinguishing advantage across all
  polynomially bounded valid families and auxiliary inputs. -/
  indistinguishable :
    ∀ (idx : ℕ → I) (x : ∀ n, StmtI (idx n)) (w : ∀ n, WitI (idx n)) (z : ℕ → List Bool),
      PolynomiallyBounded (fun n => (enc.index (idx n)).length) →
      PolynomiallyBounded (fun n => (enc.statement (idx n) (x n)).length) →
      PolynomiallyBounded (fun n => (z n).length) →
      (∀ n, rel (idx n) (x n) (w n)) →
      ∀ D : ℕ → I → List Bool → List Bool → List Bool → ProbComp Bool,
        IsPPTOn
          (encPair (encPair encUnary enc.encStatementAux) encBits)
          encBool (fun ⟨⟨n, i, xw, zw⟩, τw⟩ => D n i xw zw τw) →
        Negligible (fun n => Game.advantage
          ((((R (idx n)).honestTranscript (x n) (w n)).map (enc.transcript (idx n))).bind
            fun τw => ProbComp.eval (D n (idx n) (enc.statement (idx n) (x n)) (z n) τw))
          ((ProbComp.eval (program (idx n, enc.statement (idx n) (x n)))).bind
            fun τw => ProbComp.eval (D n (idx n) (enc.statement (idx n) (x n)) (z n) τw)))

/-- **Computational auxiliary-input honest-verifier zero knowledge** ([Goldreich2001], §4.3.3,
Definition 4.3.10 for an honest verifier) over an indexed family of reductions: one uniform strict
PPT simulator `program` on `(i, enc.statement i x, encAux i z)` produces encoded transcripts that
are computationally indistinguishable from honest encoded transcripts across all polynomially
bounded valid families `(i n, x n, w n, z n)`, against every uniform strict PPT distinguisher
clocked on `((1^n, i n, enc.statement (i n) (x n), encAux (i n) (z n)), τ)`. -/
structure Reduction.ComputationalAuxHVZK
    (R : ∀ i, Reduction OracleSpec.empty OracleSpec.empty (sI i) (StmtI i) (WitI i) (StmtOutI i)
      (WitOutI i))
    (rel : ∀ i, StmtI i → WitI i → Prop) (enc : Encoding I sI StmtI)
    (encAux : ∀ i, AuxI i ↪ List Bool)
    (program : I × List Bool × List Bool → ProbComp (List Bool)) : Prop where
  /-- The simulator program is uniform strict PPT in `(i, enc.statement i x, encAux i z)`. -/
  ppt : IsPPTOn enc.encStatementAux encBits program
  /-- Honest and simulated encoded transcripts have negligible distinguishing advantage across all
  polynomially bounded valid families and auxiliary inputs. -/
  indistinguishable :
    ∀ (idx : ℕ → I) (x : ∀ n, StmtI (idx n)) (w : ∀ n, WitI (idx n)) (z : ∀ n, AuxI (idx n)),
      PolynomiallyBounded (fun n => (enc.index (idx n)).length) →
      PolynomiallyBounded (fun n => (enc.statement (idx n) (x n)).length) →
      PolynomiallyBounded (fun n => (encAux (idx n) (z n)).length) →
      (∀ n, rel (idx n) (x n) (w n)) →
      ∀ D : ℕ → I → List Bool → List Bool → List Bool → ProbComp Bool,
        IsPPTOn
          (encPair (encPair encUnary enc.encStatementAux) encBits)
          encBool (fun ⟨⟨n, i, xw, zw⟩, τw⟩ => D n i xw zw τw) →
        Negligible (fun n => Game.advantage
          ((((R (idx n)).honestTranscript (x n) (w n)).map (enc.transcript (idx n))).bind
            fun τw =>
              ProbComp.eval (D n (idx n) (enc.statement (idx n) (x n)) (encAux (idx n) (z n)) τw))
          ((ProbComp.eval (program (idx n, enc.statement (idx n) (x n), encAux (idx n) (z n)))).bind
            fun τw =>
              ProbComp.eval (D n (idx n) (enc.statement (idx n) (x n)) (encAux (idx n) (z n)) τw)))

/-- **Every `ComputationalHVZK` reduction is automatically `ComputationalAuxHVZK`**: the simulator
ignores the encoded auxiliary input while still handling auxiliary-input distinguishers. -/
theorem Reduction.ComputationalHVZK.computationalAuxHVZK
    {R : ∀ i, Reduction OracleSpec.empty OracleSpec.empty (sI i) (StmtI i) (WitI i) (StmtOutI i)
      (WitOutI i)}
    {rel : ∀ i, StmtI i → WitI i → Prop} {enc : Encoding I sI StmtI}
    (encAux : ∀ i, AuxI i ↪ List Bool)
    {program : I × List Bool → ProbComp (List Bool)}
    (h : Reduction.ComputationalHVZK R rel enc program) :
    Reduction.ComputationalAuxHVZK R rel enc encAux (fun (i, xw, _) => program (i, xw)) where
  ppt := h.ppt.preprocess (prepare := fun p : I × List Bool × List Bool => (p.1, p.2.1))
    (by fun_prop)
  indistinguishable idx x w z hidx hx hz hrel D hD :=
    h.indistinguishable idx x w (fun n => encAux (idx n) (z n)) hidx hx hz hrel D hD

/-- Statistical `AuxSimulatorRealizedBy` with negligible total error `ε i + δ i` implies
`Reduction.ComputationalAuxHVZK` (in fact against arbitrary, even unbounded distinguishers). -/
theorem AuxSimulatorRealizedBy.computationalAuxHVZK
    {R : ∀ i, Reduction OracleSpec.empty OracleSpec.empty (sI i) (StmtI i) (WitI i) (StmtOutI i)
      (WitOutI i)}
    {rel : ∀ i, StmtI i → WitI i → Prop} {enc : Encoding I sI StmtI}
    {encAux : ∀ i, AuxI i ↪ List Bool}
    {Sim : ∀ i, StmtI i → AuxI i → ProbComp (Transcript (sI i))}
    {program : I × List Bool × List Bool → ProbComp (List Bool)} {ε δ : I → ℝ≥0∞}
    (hzk : ∀ i, (R i).AuxHVZK (rel i) (Sim i) (fun _ _ => ε i))
    (hppt : IsPPTOn enc.encStatementAux encBits program)
    (hreal : AuxSimulatorRealizedBy enc encAux Sim program δ)
    {η : I → ℝ≥0} (hη : ∀ i, ε i + δ i ≤ η i)
    (hnegl : ∀ idx : ℕ → I, PolynomiallyBounded (fun n => (enc.index (idx n)).length) →
      Negligible (fun n => η (idx n))) :
    Reduction.ComputationalAuxHVZK R rel enc encAux program where
  ppt := hppt
  indistinguishable idx _ _ z hidx _ _ hrel _ _ :=
    negligible_of_le (hnegl idx hidx) fun n =>
      Game.advantage_bind_le_of_closeTo
        ((hreal.closeTo_run hzk (z n) (hrel n)).mono (hη (idx n))) _

/-- **Efficient statistical `EfficientAuxHVZK` implies `ComputationalAuxHVZK`** whenever `ε + δ` is
negligible along polynomially bounded index families (for instance when `ε = 0` and `δ = 0`). -/
theorem Reduction.EfficientAuxHVZK.exists_computationalAuxHVZK
    {R : ∀ i, Reduction OracleSpec.empty OracleSpec.empty (sI i) (StmtI i) (WitI i) (StmtOutI i)
      (WitOutI i)}
    {rel : ∀ i, StmtI i → WitI i → Prop} {enc : Encoding I sI StmtI}
    {encAux : ∀ i, AuxI i ↪ List Bool}
    {Sim : ∀ i, StmtI i → AuxI i → ProbComp (Transcript (sI i))} {ε δ : I → ℝ≥0∞}
    (h : Reduction.EfficientAuxHVZK R rel enc encAux Sim ε δ)
    {η : I → ℝ≥0} (hη : ∀ i, ε i + δ i ≤ η i)
    (hnegl : ∀ idx : ℕ → I, PolynomiallyBounded (fun n => (enc.index (idx n)).length) →
      Negligible (fun n => η (idx n))) :
    ∃ program, Reduction.ComputationalAuxHVZK R rel enc encAux program := by
  obtain ⟨program, hppt, hreal⟩ := h.realized
  exact ⟨program, hreal.computationalAuxHVZK h.auxHVZK hppt hη hnegl⟩

/-- **Efficient statistical `EfficientHVZK` with zero error (`ε = 0`, `δ = 0`) implies both
`ComputationalHVZK` and `ComputationalAuxHVZK`.** -/
theorem Reduction.EfficientHVZK.exists_computationalHVZK_zero
    {R : ∀ i, Reduction OracleSpec.empty OracleSpec.empty (sI i) (StmtI i) (WitI i) (StmtOutI i)
      (WitOutI i)}
    {rel : ∀ i, StmtI i → WitI i → Prop} {enc : Encoding I sI StmtI}
    {Sim : ∀ i, StmtI i → ProbComp (Transcript (sI i))}
    (h : Reduction.EfficientHVZK R rel enc Sim (fun _ => 0) (fun _ => 0)) :
    ∃ program, Reduction.ComputationalHVZK R rel enc program := by
  obtain ⟨program, hppt, hreal⟩ := h.realized
  refine ⟨program, hppt, fun idx x w _ _ _ _ hrel _ _ => ?_⟩
  refine negligible_of_le negligible_zero fun n => ?_
  have hclose : CloseTo (((R (idx n)).honestTranscript (x n) (w n)).map (enc.transcript (idx n)))
      (ProbComp.eval (program (idx n, enc.statement (idx n) (x n)))) (0 : ℝ≥0) := by
    simpa using hreal.closeTo_run h.hvzk (hrel n)
  exact Game.advantage_bind_le_of_closeTo hclose _

end Indexed

/-! ### Part 2: Product (AND) and disjunctive (OR) relations and product composition -/

variable {ιP ιV : Type} {oP : OracleSpec ιP} {oV : OracleSpec ιV}
  {s₁ s₂ : Spec} {S₁ W₁ S₁' W₁' S₂ W₂ S₂' W₂' : Type}

/-- The product (AND) of two relations: `(x₁, x₂)` is related to `(w₁, w₂)` when both components
are related. -/
def relProd (rel₁ : S₁ → W₁ → Prop) (rel₂ : S₂ → W₂ → Prop) :
    S₁ × S₂ → W₁ × W₂ → Prop :=
  fun x w => rel₁ x.1 w.1 ∧ rel₂ x.2 w.2

/-- The disjunctive (OR) relation on product statements `S₁ × S₂` with sum witnesses `W₁ ⊕ W₂`:
`Sum.inl w₁` witnesses `x.1` in `rel₁` and `Sum.inr w₂` witnesses `x.2` in `rel₂`. -/
def relDisj (rel₁ : S₁ → W₁ → Prop) (rel₂ : S₂ → W₂ → Prop) :
    S₁ × S₂ → W₁ ⊕ W₂ → Prop :=
  fun x w => match w with
    | .inl w₁ => rel₁ x.1 w₁
    | .inr w₂ => rel₂ x.2 w₂

/-- The language of a product relation is the Cartesian product of the component languages. -/
@[simp] theorem language_relProd (rel₁ : S₁ → W₁ → Prop) (rel₂ : S₂ → W₂ → Prop) :
    language (relProd rel₁ rel₂) = language rel₁ ×ˢ language rel₂ := by
  ext ⟨x₁, x₂⟩
  simp only [language, relProd, Set.mem_ofPred_eq, Set.mem_prod, Prod.exists]
  exact ⟨fun ⟨w₁, w₂, h₁, h₂⟩ => ⟨⟨w₁, h₁⟩, ⟨w₂, h₂⟩⟩,
    fun ⟨⟨w₁, h₁⟩, ⟨w₂, h₂⟩⟩ => ⟨w₁, w₂, h₁, h₂⟩⟩

/-- A pair `(x₁, x₂)` is outside `language (relProd rel₁ rel₂)` iff `x₁ ∉ language rel₁` or
`x₂ ∉ language rel₂`. -/
theorem notMem_language_relProd {rel₁ : S₁ → W₁ → Prop} {rel₂ : S₂ → W₂ → Prop}
    {x : S₁ × S₂} :
    x ∉ language (relProd rel₁ rel₂) ↔ x.1 ∉ language rel₁ ∨ x.2 ∉ language rel₂ := by
  rw [language_relProd, Set.mem_prod, not_and_or]

/-- A pair `(x₁, x₂)` belongs to `language (relDisj rel₁ rel₂)` iff `x₁ ∈ language rel₁` or
`x₂ ∈ language rel₂`. -/
@[simp] theorem mem_language_relDisj {rel₁ : S₁ → W₁ → Prop} {rel₂ : S₂ → W₂ → Prop}
    {x : S₁ × S₂} :
    x ∈ language (relDisj rel₁ rel₂) ↔ x.1 ∈ language rel₁ ∨ x.2 ∈ language rel₂ := by
  simp only [language, relDisj, Set.mem_ofPred_eq, Sum.exists]

/-- Lift a verifier `V₁` on the first coordinate to a verifier on `S₁ × S₂` that passes `x.2`
through unchanged. -/
def Verifier.liftFirst (V₁ : Verifier oV s₁ S₁ S₁') :
    Verifier oV s₁ (S₁ × S₂) (S₁' × S₂) where
  samplers := V₁.samplers
  decide x c := (fun o => o.map (·, x.2)) <$> V₁.decide x.1 c

/-- Lift a verifier `V₂` on the second coordinate to a verifier on `S₁' × S₂` that passes `y.1`
through unchanged. -/
def Verifier.liftSecond (V₂ : Verifier oV s₂ S₂ S₂') :
    Verifier oV s₂ (S₁' × S₂) (S₁' × S₂') where
  samplers := V₂.samplers
  decide y c := (fun o => o.map (y.1, ·)) <$> V₂.decide y.2 c

/-- **Product composition of verifiers** over `s₁ ++ s₂`: run `V₁` on `x.1` in the first phase and
`V₂` on `x.2` in the second phase, accepting with `some (y₁, y₂)` when both accept. -/
def Verifier.seqProd (V₁ : Verifier oV s₁ S₁ S₁') (V₂ : Verifier oV s₂ S₂ S₂') :
    Verifier oV (s₁ ++ s₂) (S₁ × S₂) (S₁' × S₂') :=
  (V₁.liftFirst (S₂ := S₂)).append (V₂.liftSecond (S₁' := S₁'))

/-- Lift a reduction `R₁` on the first coordinate to a reduction on `(S₁ × S₂, W₁ × W₂)` that
threads `(x.2, w.2)` through unchanged. -/
def Reduction.liftFirst (R₁ : Reduction oP oV s₁ S₁ W₁ S₁' W₁') :
    Reduction oP oV s₁ (S₁ × S₂) (W₁ × W₂) (S₁' × S₂) (W₁' × W₂) where
  prover x w := do
    let st ← R₁.prover x.1 w.1
    ProverStrategy.bindLeaf s₁ st fun _ yw => pure ((yw.1, x.2), (yw.2, w.2))
  verifier := R₁.verifier.liftFirst

/-- Lift a reduction `R₂` on the second coordinate to a reduction on `(S₁' × S₂, W₁' × W₂)` that
threads `(y.1, w.1)` through unchanged. -/
def Reduction.liftSecond (R₂ : Reduction oP oV s₂ S₂ W₂ S₂' W₂') :
    Reduction oP oV s₂ (S₁' × S₂) (W₁' × W₂) (S₁' × S₂') (W₁' × W₂') where
  prover y w := do
    let st ← R₂.prover y.2 w.2
    ProverStrategy.bindLeaf s₂ st fun _ yw => pure ((y.1, yw.1), (w.1, yw.2))
  verifier := R₂.verifier.liftSecond

/-- **Product (AND) composition of interactive reductions** over `s₁ ++ s₂`: run `R₁` on the first
coordinate and then `R₂` on the second coordinate. -/
def Reduction.seqProd (R₁ : Reduction oP oV s₁ S₁ W₁ S₁' W₁')
    (R₂ : Reduction oP oV s₂ S₂ W₂ S₂' W₂') :
    Reduction oP oV (s₁ ++ s₂) (S₁ × S₂) (W₁ × W₂) (S₁' × S₂') (W₁' × W₂') :=
  (R₁.liftFirst (S₂ := S₂) (W₂ := W₂)).append (R₂.liftSecond (S₁' := S₁') (W₁' := W₁'))

@[simp] theorem Reduction.verifier_seqProd (R₁ : Reduction oP oV s₁ S₁ W₁ S₁' W₁')
    (R₂ : Reduction oP oV s₂ S₂ W₂ S₂' W₂') :
    (R₁.seqProd R₂).verifier = R₁.verifier.seqProd R₂.verifier :=
  rfl

@[simp] theorem Verifier.outputOn_liftFirst (V₁ : Verifier OracleSpec.empty s₁ S₁ S₁')
    (x : S₁ × S₂) (τ₁ : Transcript s₁) :
    (V₁.liftFirst (S₂ := S₂)).outputOn x τ₁ = (V₁.outputOn x.1 τ₁).map (·, x.2) := by
  simp only [Verifier.outputOn, Verifier.liftFirst]
  exact OracleComp.interpret_map (m := Id) _ _ _

@[simp] theorem Verifier.outputOn_liftSecond (V₂ : Verifier OracleSpec.empty s₂ S₂ S₂')
    (y : S₁' × S₂) (τ₂ : Transcript s₂) :
    (V₂.liftSecond (S₁' := S₁')).outputOn y τ₂ = (V₂.outputOn y.2 τ₂).map (y.1, ·) := by
  simp only [Verifier.outputOn, Verifier.liftSecond]
  exact OracleComp.interpret_map (m := Id) _ _ _

/-- The output of `V₁.seqProd V₂` on a transcript `τ` pairs the outputs of `V₁` and `V₂` on the two
halves of `τ`. -/
theorem Verifier.outputOn_seqProd (V₁ : Verifier OracleSpec.empty s₁ S₁ S₁')
    (V₂ : Verifier OracleSpec.empty s₂ S₂ S₂') (x : S₁ × S₂) (τ : Transcript (s₁ ++ s₂)) :
    (V₁.seqProd V₂).outputOn x τ =
      (V₁.outputOn x.1 (Transcript.split s₁ s₂ τ).1).bind fun y₁ =>
        (V₂.outputOn x.2 (Transcript.split s₁ s₂ τ).2).map fun y₂ => (y₁, y₂) := by
  rw [Verifier.seqProd, outputOn_append, Verifier.outputOn_liftFirst]
  cases V₁.outputOn x.1 (Transcript.split s₁ s₂ τ).1 <;> simp

/-- `(V₁.seqProd V₂).outputOn x τ = some y` iff `V₁` outputs `some y.1` on the first half and `V₂`
outputs `some y.2` on the second half. -/
theorem Verifier.outputOn_seqProd_eq_some_iff (V₁ : Verifier OracleSpec.empty s₁ S₁ S₁')
    (V₂ : Verifier OracleSpec.empty s₂ S₂ S₂') (x : S₁ × S₂) (τ : Transcript (s₁ ++ s₂))
    (y : S₁' × S₂') :
    (V₁.seqProd V₂).outputOn x τ = some y ↔
      V₁.outputOn x.1 (Transcript.split s₁ s₂ τ).1 = some y.1 ∧
        V₂.outputOn x.2 (Transcript.split s₁ s₂ τ).2 = some y.2 := by
  rw [Verifier.outputOn_seqProd]
  cases h₁ : V₁.outputOn x.1 (Transcript.split s₁ s₂ τ).1 <;>
    cases h₂ : V₂.outputOn x.2 (Transcript.split s₁ s₂ τ).2 <;>
    simp [Prod.ext_iff]

/-- Plain-model execution law of `R₁.liftFirst`. -/
theorem Reduction.plainLaw_run_liftFirst
    (R₁ : Reduction OracleSpec.empty OracleSpec.empty s₁ S₁ W₁ S₁' W₁')
    (x : S₁ × S₂) (w : W₁ × W₂) :
    plainLaw ((R₁.liftFirst (S₂ := S₂) (W₂ := W₂)).prover x w >>=
        runStrategy s₁ (R₁.liftFirst (S₂ := S₂) (W₂ := W₂)).verifier.samplers) =
      (plainLaw (R₁.prover x.1 w.1 >>= runStrategy s₁ R₁.verifier.samplers)).map
        fun (τ, y₁, w₁) => (τ, ((y₁, x.2), (w₁, w.2))) := by
  simp only [Reduction.liftFirst, Verifier.liftFirst, bind_assoc, plainLaw_bind, PMF.map_bind]
  congr 1
  funext st
  rw [← plainLaw_bind]
  exact plainLaw_bindLeaf_pure_run _ _ _ _

/-- Plain-model execution law of `R₂.liftSecond`. -/
theorem Reduction.plainLaw_run_liftSecond
    (R₂ : Reduction OracleSpec.empty OracleSpec.empty s₂ S₂ W₂ S₂' W₂')
    (y : S₁' × S₂) (w : W₁' × W₂) :
    plainLaw ((R₂.liftSecond (S₁' := S₁') (W₁' := W₁')).prover y w >>=
        runStrategy s₂ (R₂.liftSecond (S₁' := S₁') (W₁' := W₁')).verifier.samplers) =
      (plainLaw (R₂.prover y.2 w.2 >>= runStrategy s₂ R₂.verifier.samplers)).map
        fun (τ, y₂, w₂) => (τ, ((y.1, y₂), (w.1, w₂))) := by
  simp only [Reduction.liftSecond, Verifier.liftSecond, bind_assoc, plainLaw_bind, PMF.map_bind]
  congr 1
  funext st
  rw [← plainLaw_bind]
  exact plainLaw_bindLeaf_pure_run _ _ _ _

/-- `R₁.liftFirst` preserves completeness with the same error. -/
theorem Reduction.Complete.liftFirst
    {R₁ : Reduction OracleSpec.empty OracleSpec.empty s₁ S₁ W₁ S₁' W₁'}
    {relIn₁ : S₁ → W₁ → Prop} {relOut₁ : S₁' → W₁' → Prop} {rel₂ : S₂ → W₂ → Prop} {ε₁ : ℝ≥0∞}
    (h₁ : R₁.Complete World.plain relIn₁ relOut₁ ε₁) :
    (R₁.liftFirst (S₂ := S₂) (W₂ := W₂)).Complete World.plain
      (relProd relIn₁ rel₂) (relProd relOut₁ rel₂) ε₁ := by
  rintro ⟨x₁, x₂⟩ ⟨w₁, w₂⟩ ⟨hx₁, hx₂⟩
  have hl := h₁ x₁ w₁ hx₁
  rw [Reduction.run, World.plain_eval_execute, PMF.toOuterMeasure_map_apply] at hl ⊢
  rw [Reduction.plainLaw_run_liftFirst, PMF.toOuterMeasure_map_apply]
  refine le_of_eq_of_le (congrArg _ ?_) hl
  ext r
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Reduction.liftFirst, Verifier.outputOn_liftFirst,
    relProd, hx₂, and_true]
  cases R₁.verifier.outputOn x₁ r.1 <;> simp

/-- `R₂.liftSecond` preserves completeness with the same error. -/
theorem Reduction.Complete.liftSecond
    {R₂ : Reduction OracleSpec.empty OracleSpec.empty s₂ S₂ W₂ S₂' W₂'}
    {rel₁ : S₁' → W₁' → Prop} {relIn₂ : S₂ → W₂ → Prop} {relOut₂ : S₂' → W₂' → Prop} {ε₂ : ℝ≥0∞}
    (h₂ : R₂.Complete World.plain relIn₂ relOut₂ ε₂) :
    (R₂.liftSecond (S₁' := S₁') (W₁' := W₁')).Complete World.plain
      (relProd rel₁ relIn₂) (relProd rel₁ relOut₂) ε₂ := by
  rintro ⟨y₁, x₂⟩ ⟨w₁, w₂⟩ ⟨hy₁, hx₂⟩
  have hl := h₂ x₂ w₂ hx₂
  rw [Reduction.run, World.plain_eval_execute, PMF.toOuterMeasure_map_apply] at hl ⊢
  rw [Reduction.plainLaw_run_liftSecond, PMF.toOuterMeasure_map_apply]
  refine le_of_eq_of_le (congrArg _ ?_) hl
  ext r
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Reduction.liftSecond,
    Verifier.outputOn_liftSecond, relProd, hy₁, true_and]
  cases R₂.verifier.outputOn x₂ r.1 <;> simp

/-- **Completeness of product composition (`Reduction.seqProd`)**: completeness errors add up. -/
theorem Reduction.Complete.seqProd
    {R₁ : Reduction OracleSpec.empty OracleSpec.empty s₁ S₁ W₁ S₁' W₁'}
    {R₂ : Reduction OracleSpec.empty OracleSpec.empty s₂ S₂ W₂ S₂' W₂'}
    {relIn₁ : S₁ → W₁ → Prop} {relOut₁ : S₁' → W₁' → Prop}
    {relIn₂ : S₂ → W₂ → Prop} {relOut₂ : S₂' → W₂' → Prop} {ε₁ ε₂ : ℝ≥0∞}
    (h₁ : R₁.Complete World.plain relIn₁ relOut₁ ε₁)
    (h₂ : R₂.Complete World.plain relIn₂ relOut₂ ε₂) :
    (R₁.seqProd R₂).Complete World.plain
      (relProd relIn₁ relIn₂) (relProd relOut₁ relOut₂) (ε₁ + ε₂) :=
  h₁.liftFirst.append h₂.liftSecond

/-- **Perfect completeness of product composition**: if both `R₁` and `R₂` are perfectly complete,
so is `R₁.seqProd R₂`. -/
theorem Reduction.Complete.seqProd_zero
    {R₁ : Reduction OracleSpec.empty OracleSpec.empty s₁ S₁ W₁ S₁' W₁'}
    {R₂ : Reduction OracleSpec.empty OracleSpec.empty s₂ S₂ W₂ S₂' W₂'}
    {relIn₁ : S₁ → W₁ → Prop} {relOut₁ : S₁' → W₁' → Prop}
    {relIn₂ : S₂ → W₂ → Prop} {relOut₂ : S₂' → W₂' → Prop}
    (h₁ : R₁.Complete World.plain relIn₁ relOut₁ 0)
    (h₂ : R₂.Complete World.plain relIn₂ relOut₂ 0) :
    (R₁.seqProd R₂).Complete World.plain (relProd relIn₁ relIn₂) (relProd relOut₁ relOut₂) 0 := by
  simpa using h₁.seqProd h₂

/-- **Soundness of product composition (`Verifier.seqProd`)**: on any pair `(x₁, x₂) ∉ L₁ ×ˢ L₂`,
either `x₁ ∉ L₁` (bounded by `ε₁`) or `x₂ ∉ L₂` (bounded by `ε₂`), so the soundness error of
`V₁.seqProd V₂` is at most `max ε₁ ε₂`. -/
theorem Verifier.Sound.seqProd
    {V₁ : Verifier OracleSpec.empty s₁ S₁ S₁'} {V₂ : Verifier OracleSpec.empty s₂ S₂ S₂'}
    {L₁ : Set S₁} {L₁' : Set S₁'} {L₂ : Set S₂} {L₂' : Set S₂'} {ε₁ ε₂ : ℝ≥0∞}
    (h₁ : V₁.Sound (oP := OracleSpec.empty) World.plain L₁ L₁' ε₁)
    (h₂ : V₂.Sound (oP := OracleSpec.empty) World.plain L₂ L₂' ε₂) :
    (V₁.seqProd V₂).Sound (oP := OracleSpec.empty) World.plain (L₁ ×ˢ L₂) (L₁' ×ˢ L₂')
      (max ε₁ ε₂) := by
  rintro ⟨x₁, x₂⟩ hx α P
  rw [Set.mem_prod, not_and_or] at hx
  rw [World.plain_eval_execute, PMF.toOuterMeasure_map_apply]
  have hsplit : plainLaw (P >>= runStrategy (s₁ ++ s₂) (V₁.seqProd V₂).samplers) =
      (plainLaw ((ProverStrategy.split s₁ s₂ ·) <$> P >>= runStrategy s₁ V₁.samplers)).bind
        fun r₁ => (plainLaw (runStrategy s₂ V₂.samplers r₁.2)).map
          fun r₂ => (Transcript.append s₁ s₂ r₁.1 r₂.1, r₂.2) := by
    simp only [Verifier.seqProd, Verifier.append, Verifier.liftFirst, Verifier.liftSecond,
      plainLaw_bind, plainLaw_map, PMF.bind_map, PMF.bind_bind]
    congr 1
    funext st
    exact plainLaw_run_split s₁ s₂ V₁.samplers V₂.samplers st
  rw [hsplit]
  rcases hx with hx₁ | hx₂
  · have hl₁ := h₁ x₁ hx₁ _ ((ProverStrategy.split s₁ s₂ ·) <$> P)
    rw [World.plain_eval_execute, PMF.toOuterMeasure_map_apply] at hl₁
    refine le_trans ?_ (hl₁.trans (le_max_left ε₁ ε₂))
    rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply]
    refine tsum_le_tsum fun r₁ => ?_
    by_cases hr₁ : ∃ y₁ ∈ L₁', V₁.outputOn x₁ r₁.1 = some y₁
    · have hmem : r₁ ∈ (fun r : Transcript s₁ × _ => (r.1, V₁.outputOn x₁ r.1, r.2)) ⁻¹'
          {r | ∃ x' ∈ L₁', r.2.1 = some x'} := hr₁
      rw [Set.indicator_of_mem hmem]
      exact (mul_le_mul_of_nonneg_left
        (Probability.PMF.toOuterMeasure_le_one _ _) zero_le).trans (mul_one _).le
    · rw [PMF.toOuterMeasure_map_apply]
      have hempty : (fun r₂ : Transcript s₂ × α => (Transcript.append s₁ s₂ r₁.1 r₂.1, r₂.2)) ⁻¹'
          ((fun r : Transcript (s₁ ++ s₂) × α =>
            (r.1, (V₁.seqProd V₂).outputOn (x₁, x₂) r.1, r.2)) ⁻¹'
              {r | ∃ y ∈ L₁' ×ˢ L₂', r.2.1 = some y}) = ∅ := by
        ext r₂
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
          not_exists, not_and]
        rintro ⟨y₁, y₂⟩ ⟨hy₁, _⟩ hout
        rw [Verifier.outputOn_seqProd_eq_some_iff] at hout
        rw [Spec.Transcript.split_append] at hout
        exact hr₁ ⟨y₁, hy₁, hout.1⟩
      rw [hempty, MeasureTheory.measure_empty, mul_zero]
      exact zero_le
  · refine le_trans (Probability.PMF.toOuterMeasure_bind_le _ _ _ fun r₁ => ?_) (le_max_right ε₁ ε₂)
    rw [PMF.toOuterMeasure_map_apply]
    have hl₂ := h₂ x₂ hx₂ α (pure r₁.2)
    rw [World.plain_eval_execute, PMF.toOuterMeasure_map_apply] at hl₂
    simp only [plainLaw_bind, plainLaw_pure, PMF.pure_bind] at hl₂
    refine le_trans (MeasureTheory.measure_mono ?_) hl₂
    rintro r₂ ⟨⟨y₁, y₂⟩, ⟨_, hy₂⟩, hout⟩
    rw [Verifier.outputOn_seqProd_eq_some_iff, Spec.Transcript.split_append] at hout
    exact ⟨y₂, hy₂, hout.2⟩

/-- Product straight-line extractor: extract the first witness from the first half of the
transcript and the second witness from the second half. -/
def Verifier.extractSeqProd (E₁ : S₁ → Transcript s₁ → W₁' → W₁)
    (E₂ : S₂ → Transcript s₂ → W₂' → W₂) :
    S₁ × S₂ → Transcript (s₁ ++ s₂) → W₁' × W₂' → W₁ × W₂ :=
  fun x τ wOut =>
    (E₁ x.1 (Transcript.split s₁ s₂ τ).1 wOut.1,
     E₂ x.2 (Transcript.split s₁ s₂ τ).2 wOut.2)

/-- **Straight-line knowledge soundness of product composition (`Verifier.seqProd`)**: running both
extractors recovers a valid witness pair `(w₁, w₂)` with error at most `κ₁ + κ₂`. -/
theorem Verifier.KnowledgeSound.seqProd
    {V₁ : Verifier OracleSpec.empty s₁ S₁ S₁'} {V₂ : Verifier OracleSpec.empty s₂ S₂ S₂'}
    {relIn₁ : S₁ → W₁ → Prop} {relOut₁ : S₁' → W₁' → Prop}
    {relIn₂ : S₂ → W₂ → Prop} {relOut₂ : S₂' → W₂' → Prop}
    {E₁ : S₁ → Transcript s₁ → W₁' → W₁} {E₂ : S₂ → Transcript s₂ → W₂' → W₂}
    {κ₁ κ₂ : ℝ≥0∞}
    (h₁ : V₁.KnowledgeSound relIn₁ relOut₁ E₁ κ₁)
    (h₂ : V₂.KnowledgeSound relIn₂ relOut₂ E₂ κ₂) :
    (V₁.seqProd V₂).KnowledgeSound (relProd relIn₁ relIn₂) (relProd relOut₁ relOut₂)
      (Verifier.extractSeqProd E₁ E₂) (κ₁ + κ₂) := by
  rintro ⟨x₁, x₂⟩ P
  rw [World.plain_eval_execute, PMF.toOuterMeasure_map_apply]
  have hsplit : plainLaw (P >>= runStrategy (s₁ ++ s₂) (V₁.seqProd V₂).samplers) =
      (plainLaw ((ProverStrategy.split s₁ s₂ ·) <$> P >>= runStrategy s₁ V₁.samplers)).bind
        fun r₁ => (plainLaw (runStrategy s₂ V₂.samplers r₁.2)).map
          fun r₂ => (Transcript.append s₁ s₂ r₁.1 r₂.1, r₂.2) := by
    simp only [Verifier.seqProd, Verifier.append, Verifier.liftFirst, Verifier.liftSecond,
      plainLaw_bind, plainLaw_map, PMF.bind_map, PMF.bind_bind]
    congr 1
    funext st
    exact plainLaw_run_split s₁ s₂ V₁.samplers V₂.samplers st
  rw [hsplit]
  let T₁ : Set (Transcript (s₁ ++ s₂) × (W₁' × W₂')) := {r |
    (∃ y₁, V₁.outputOn x₁ (Transcript.split s₁ s₂ r.1).1 = some y₁ ∧ relOut₁ y₁ r.2.1) ∧
      ¬ relIn₁ x₁ (E₁ x₁ (Transcript.split s₁ s₂ r.1).1 r.2.1)}
  let T₂ : Set (Transcript (s₁ ++ s₂) × (W₁' × W₂')) := {r |
    (∃ y₂, V₂.outputOn x₂ (Transcript.split s₁ s₂ r.1).2 = some y₂ ∧ relOut₂ y₂ r.2.2) ∧
      ¬ relIn₂ x₂ (E₂ x₂ (Transcript.split s₁ s₂ r.1).2 r.2.2)}
  have hsub : (fun r : Transcript (s₁ ++ s₂) × (W₁' × W₂') =>
        (r.1, (V₁.seqProd V₂).outputOn (x₁, x₂) r.1, r.2)) ⁻¹'
      {r : Execution (s₁ ++ s₂) (S₁' × S₂') (W₁' × W₂') |
        (∃ y, r.output = some y ∧ relProd relOut₁ relOut₂ y r.result) ∧
        ¬ relProd relIn₁ relIn₂ (x₁, x₂)
          (Verifier.extractSeqProd E₁ E₂ (x₁, x₂) r.transcript r.result)} ⊆
      T₁ ∪ T₂ := by
    rintro ⟨τ, w₁', w₂'⟩ ⟨⟨⟨y₁, y₂⟩, hout, hy₁, hy₂⟩, hnot⟩
    rw [Verifier.outputOn_seqProd_eq_some_iff] at hout
    simp only [relProd, Verifier.extractSeqProd, not_and_or] at hnot
    rcases hnot with hn₁ | hn₂
    · exact Or.inl ⟨⟨y₁, hout.1, hy₁⟩, hn₁⟩
    · exact Or.inr ⟨⟨y₂, hout.2, hy₂⟩, hn₂⟩
  refine le_trans (MeasureTheory.measure_mono hsub)
    (le_trans (MeasureTheory.measure_union_le _ _) (add_le_add ?_ ?_))
  · let P₁ : ProbOracleComp OracleSpec.empty
        (ProverStrategy (ProbOracleComp OracleSpec.empty) s₁ W₁') :=
      (ProverStrategy.split s₁ s₂ ·) <$> P >>= fun st₁ => ProverStrategy.bindLeaf s₁ st₁
        fun _ st₂ => (fun r₂ => r₂.2.1) <$> runStrategy s₂ V₂.samplers st₂
    have hl₁ := h₁ x₁ P₁
    rw [World.plain_eval_execute, PMF.toOuterMeasure_map_apply] at hl₁
    have hlaw₁ : plainLaw (P₁ >>= runStrategy s₁ V₁.samplers) =
        (plainLaw ((ProverStrategy.split s₁ s₂ ·) <$> P >>= runStrategy s₁ V₁.samplers)).bind
          fun r₁ => (plainLaw (runStrategy s₂ V₂.samplers r₁.2)).map
            fun r₂ => (r₁.1, r₂.2.1) :=
      plainLaw_split_bindLeaf_run s₁ s₂ V₁.samplers V₂.samplers P fun _ r₂ => r₂.2.1
    rw [hlaw₁] at hl₁
    refine le_trans (le_of_eq ?_) hl₁
    rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
    refine tsum_congr fun r₁ => ?_
    congr 1
    rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
    congr 1
    ext r₂
    simp [T₁, Spec.Transcript.split_append]
  · refine Probability.PMF.toOuterMeasure_bind_le _ _ _ fun r₁ => ?_
    rw [PMF.toOuterMeasure_map_apply]
    let P₂ : ProbOracleComp OracleSpec.empty
        (ProverStrategy (ProbOracleComp OracleSpec.empty) s₂ W₂') :=
      ProverStrategy.bindLeaf s₂ r₁.2 fun _ wOut => pure wOut.2
    have hl₂ := h₂ x₂ P₂
    rw [World.plain_eval_execute, PMF.toOuterMeasure_map_apply] at hl₂
    have hlaw₂ : plainLaw (P₂ >>= runStrategy s₂ V₂.samplers) =
        (plainLaw (runStrategy s₂ V₂.samplers r₁.2)).map fun r₂ => (r₂.1, r₂.2.2) :=
      plainLaw_bindLeaf_pure_run s₂ V₂.samplers r₁.2 fun _ wOut => wOut.2
    rw [hlaw₂, PMF.toOuterMeasure_map_apply] at hl₂
    convert hl₂ using 2
    ext r₂
    simp [T₂, Spec.Transcript.split_append]

/-- The honest transcript of `R₁.seqProd R₂` on `(x, w)` is the concatenation of independent
honest transcripts of `R₁` on `(x.1, w.1)` and `R₂` on `(x.2, w.2)`. -/
theorem Reduction.honestTranscript_seqProd
    (R₁ : Reduction OracleSpec.empty OracleSpec.empty s₁ S₁ W₁ S₁' W₁')
    (R₂ : Reduction OracleSpec.empty OracleSpec.empty s₂ S₂ W₂ S₂' W₂')
    (x : S₁ × S₂) (w : W₁ × W₂) :
    (R₁.seqProd R₂).honestTranscript x w =
      (R₁.honestTranscript x.1 w.1).bind fun τ₁ =>
        (R₂.honestTranscript x.2 w.2).map fun τ₂ =>
          Transcript.append s₁ s₂ τ₁ τ₂ := by
  rw [Reduction.honestTranscript_eq_plainLaw, Reduction.honestTranscript_eq_plainLaw,
    Reduction.honestTranscript_eq_plainLaw]
  simp only [Reduction.seqProd, Reduction.append, Verifier.append, bind_assoc]
  have hrun : plainLaw ((R₁.liftFirst (S₂ := S₂) (W₂ := W₂)).prover x w >>= fun st =>
        ProverStrategy.append s₁ s₂ st
          (fun xw => (R₂.liftSecond (S₁' := S₁') (W₁' := W₁')).prover xw.1 xw.2) >>=
        runStrategy (s₁ ++ s₂)
          (PerChallenge.append s₁ s₂ (R₁.liftFirst (S₂ := S₂) (W₂ := W₂)).verifier.samplers
            (R₂.liftSecond (S₁' := S₁') (W₁' := W₁')).verifier.samplers)) =
      (plainLaw ((R₁.liftFirst (S₂ := S₂) (W₂ := W₂)).prover x w >>=
          runStrategy s₁ (R₁.liftFirst (S₂ := S₂) (W₂ := W₂)).verifier.samplers)).bind fun r₁ =>
        (plainLaw ((R₂.liftSecond (S₁' := S₁') (W₁' := W₁')).prover r₁.2.1 r₁.2.2 >>=
          runStrategy s₂ (R₂.liftSecond (S₁' := S₁') (W₁' := W₁')).verifier.samplers)).map
            fun r₂ => (Transcript.append s₁ s₂ r₁.1 r₂.1, r₂.2) := by
    simp only [plainLaw_bind, PMF.bind_bind]
    congr 1
    funext st
    rw [← plainLaw_bind, plainLaw_run_append]
    simp only [plainLaw_bind]
  rw [hrun, Reduction.plainLaw_run_liftFirst, PMF.bind_map, PMF.map_bind, PMF.bind_map]
  congr 1
  funext r₁
  simp only [Function.comp_def, Reduction.plainLaw_run_liftSecond, PMF.map_comp]

/-- Product simulator for `Reduction.seqProd`: run `Sim₁` on `x.1` and `Sim₂` on `x.2`, and
concatenate their transcripts. -/
def simSeqProd (Sim₁ : S₁ → ProbComp (Transcript s₁))
    (Sim₂ : S₂ → ProbComp (Transcript s₂)) (x : S₁ × S₂) :
    ProbComp (Transcript (s₁ ++ s₂)) := do
  let τ₁ ← Sim₁ x.1
  let τ₂ ← Sim₂ x.2
  return Transcript.append s₁ s₂ τ₁ τ₂

/-- Product auxiliary-input simulator for `Reduction.seqProd`: run `Sim₁` on `(x.1, z)` and `Sim₂`
on `(x.2, z)`, and concatenate their transcripts. -/
def auxSimSeqProd (Sim₁ : S₁ → Aux → ProbComp (Transcript s₁))
    (Sim₂ : S₂ → Aux → ProbComp (Transcript s₂)) (x : S₁ × S₂) (z : Aux) :
    ProbComp (Transcript (s₁ ++ s₂)) := do
  let τ₁ ← Sim₁ x.1 z
  let τ₂ ← Sim₂ x.2 z
  return Transcript.append s₁ s₂ τ₁ τ₂

@[simp] theorem eval_simSeqProd (Sim₁ : S₁ → ProbComp (Transcript s₁))
    (Sim₂ : S₂ → ProbComp (Transcript s₂)) (x : S₁ × S₂) :
    ProbComp.eval (simSeqProd Sim₁ Sim₂ x) =
      (ProbComp.eval (Sim₁ x.1)).bind fun τ₁ =>
        (ProbComp.eval (Sim₂ x.2)).map fun τ₂ => Transcript.append s₁ s₂ τ₁ τ₂ := by
  simp [simSeqProd, ProbComp.eval_bind]

@[simp] theorem eval_auxSimSeqProd (Sim₁ : S₁ → Aux → ProbComp (Transcript s₁))
    (Sim₂ : S₂ → Aux → ProbComp (Transcript s₂)) (x : S₁ × S₂) (z : Aux) :
    ProbComp.eval (auxSimSeqProd Sim₁ Sim₂ x z) =
      (ProbComp.eval (Sim₁ x.1 z)).bind fun τ₁ =>
        (ProbComp.eval (Sim₂ x.2 z)).map fun τ₂ => Transcript.append s₁ s₂ τ₁ τ₂ := by
  simp [auxSimSeqProd, ProbComp.eval_bind]

/-- **HVZK of product composition (`Reduction.seqProd`)**: independent transcript simulation
preserves `HVZK` with the sum of the statistical errors. -/
theorem Reduction.HVZK.seqProd
    {R₁ : Reduction OracleSpec.empty OracleSpec.empty s₁ S₁ W₁ S₁' W₁'}
    {R₂ : Reduction OracleSpec.empty OracleSpec.empty s₂ S₂ W₂ S₂' W₂'}
    {relIn₁ : S₁ → W₁ → Prop} {relIn₂ : S₂ → W₂ → Prop}
    {Sim₁ : S₁ → ProbComp (Transcript s₁)} {Sim₂ : S₂ → ProbComp (Transcript s₂)}
    {ε₁ ε₂ : ℝ≥0∞}
    (h₁ : R₁.HVZK relIn₁ Sim₁ ε₁) (h₂ : R₂.HVZK relIn₂ Sim₂ ε₂) :
    (R₁.seqProd R₂).HVZK (relProd relIn₁ relIn₂) (simSeqProd Sim₁ Sim₂) (ε₁ + ε₂) := by
  rintro ⟨x₁, x₂⟩ ⟨w₁, w₂⟩ ⟨hx₁, hx₂⟩
  change CloseTo ((R₁.seqProd R₂).honestTranscript (x₁, x₂) (w₁, w₂))
    (ProbComp.eval (simSeqProd Sim₁ Sim₂ (x₁, x₂))) (ε₁ + ε₂)
  rw [Reduction.honestTranscript_seqProd, eval_simSeqProd]
  exact CloseTo.bind (h₁ x₁ w₁ hx₁) fun τ₁ _ => (h₂ x₂ w₂ hx₂).map (Transcript.append s₁ s₂ τ₁)

/-- **Perfect HVZK of product composition (`Reduction.seqProd`)**. -/
theorem Reduction.PerfectHVZK.seqProd
    {R₁ : Reduction OracleSpec.empty OracleSpec.empty s₁ S₁ W₁ S₁' W₁'}
    {R₂ : Reduction OracleSpec.empty OracleSpec.empty s₂ S₂ W₂ S₂' W₂'}
    {relIn₁ : S₁ → W₁ → Prop} {relIn₂ : S₂ → W₂ → Prop}
    {Sim₁ : S₁ → ProbComp (Transcript s₁)} {Sim₂ : S₂ → ProbComp (Transcript s₂)}
    (h₁ : R₁.PerfectHVZK relIn₁ Sim₁) (h₂ : R₂.PerfectHVZK relIn₂ Sim₂) :
    (R₁.seqProd R₂).PerfectHVZK (relProd relIn₁ relIn₂) (simSeqProd Sim₁ Sim₂) := by
  rintro ⟨x₁, x₂⟩ ⟨w₁, w₂⟩ ⟨hx₁, hx₂⟩
  rw [Reduction.honestTranscript_seqProd, eval_simSeqProd, h₁ x₁ w₁ hx₁, h₂ x₂ w₂ hx₂]

/-- **Auxiliary-input HVZK of product composition (`Reduction.seqProd`)**: independent
auxiliary-input simulation preserves `AuxHVZK` with error `ε₁ x.1 z + ε₂ x.2 z`. -/
theorem Reduction.AuxHVZK.seqProd
    {R₁ : Reduction OracleSpec.empty OracleSpec.empty s₁ S₁ W₁ S₁' W₁'}
    {R₂ : Reduction OracleSpec.empty OracleSpec.empty s₂ S₂ W₂ S₂' W₂'}
    {relIn₁ : S₁ → W₁ → Prop} {relIn₂ : S₂ → W₂ → Prop}
    {Sim₁ : S₁ → Aux → ProbComp (Transcript s₁)} {Sim₂ : S₂ → Aux → ProbComp (Transcript s₂)}
    {ε₁ : S₁ → Aux → ℝ≥0∞} {ε₂ : S₂ → Aux → ℝ≥0∞}
    (h₁ : R₁.AuxHVZK relIn₁ Sim₁ ε₁) (h₂ : R₂.AuxHVZK relIn₂ Sim₂ ε₂) :
    (R₁.seqProd R₂).AuxHVZK (relProd relIn₁ relIn₂) (auxSimSeqProd Sim₁ Sim₂)
      (fun x z => ε₁ x.1 z + ε₂ x.2 z) := by
  rintro ⟨x₁, x₂⟩ ⟨w₁, w₂⟩ z ⟨hx₁, hx₂⟩
  rw [Reduction.honestTranscript_seqProd, eval_auxSimSeqProd]
  exact CloseTo.bind (h₁ x₁ w₁ z hx₁) fun τ₁ _ =>
    (h₂ x₂ w₂ z hx₂).map (Transcript.append s₁ s₂ τ₁)

/-- **Perfect auxiliary-input HVZK of product composition (`Reduction.seqProd`)**. -/
theorem Reduction.PerfectAuxHVZK.seqProd
    {R₁ : Reduction OracleSpec.empty OracleSpec.empty s₁ S₁ W₁ S₁' W₁'}
    {R₂ : Reduction OracleSpec.empty OracleSpec.empty s₂ S₂ W₂ S₂' W₂'}
    {relIn₁ : S₁ → W₁ → Prop} {relIn₂ : S₂ → W₂ → Prop}
    {Sim₁ : S₁ → Aux → ProbComp (Transcript s₁)} {Sim₂ : S₂ → Aux → ProbComp (Transcript s₂)}
    (h₁ : R₁.PerfectAuxHVZK relIn₁ Sim₁) (h₂ : R₂.PerfectAuxHVZK relIn₂ Sim₂) :
    (R₁.seqProd R₂).PerfectAuxHVZK (relProd relIn₁ relIn₂) (auxSimSeqProd Sim₁ Sim₂) := by
  rintro ⟨x₁, x₂⟩ ⟨w₁, w₂⟩ z ⟨hx₁, hx₂⟩
  rw [Reduction.honestTranscript_seqProd, eval_auxSimSeqProd, h₁ x₁ w₁ z hx₁, h₂ x₂ w₂ z hx₂]

end Cslib.Interactive
