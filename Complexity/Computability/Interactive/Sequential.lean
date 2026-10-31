/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Interactive.Plain
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF.Event

/-!
# Sequential composition of interactive reductions

`Reduction.append` runs a reduction from `rel₁` to `rel₂` and then one from `rel₂` to `rel₃`; its
rounds are the concatenation `s₁ ++ s₂`. Every construction is by structural recursion on `s₁`,
so for a concrete protocol the transcripts, challenges and message queries of the composition
compute to those of the components without casts.

The composition theorems are stated in the plain model, where every security notion holds from
every state of the (trivial) world; in oracle models one composes interactive protocols first and
compiles them once (Fiat–Shamir, BCS). All errors add up. Straight-line knowledge soundness
composes with the named extractor `Verifier.extractAppend`. Its default intermediate statement is
used only when the first verifier rejects; without one, the composed extractor need not exist
when the intermediate statement type is empty.

## Main definitions

* `Interactive.Spec.Transcript.append`, `Interactive.Spec.Transcript.split`,
  `Interactive.Spec.PerChallenge.append`, `Interactive.Spec.PerChallenge.split`,
  `Interactive.Spec.liftMsgLeft`, `Interactive.Spec.liftMsgRight`.
* `Interactive.liftDecisionLeft`, `Interactive.liftDecisionRight`,
  `Interactive.Verifier.append`, `Interactive.Reduction.append`,
  `Interactive.iterSpec`, `Interactive.Reduction.id`, `Interactive.Reduction.iterate`,
  `Interactive.PerChallenge.iterate`.
* `Interactive.ProverStrategy.append`, `Interactive.ProverStrategy.split`,
  `Interactive.ProverStrategy.bindLeaf`.
* `Interactive.Verifier.extractAppend`.

## Main results

* `Interactive.Reduction.Complete.append`, `Interactive.Verifier.Sound.append`,
  `Interactive.Verifier.KnowledgeSound.append`, `Interactive.Verifier.RbrSound.append`.
* `Interactive.Reduction.Complete.iterate`, `Interactive.Verifier.RbrSound.iterate`.
* `Interactive.plainLaw_run_append`, `Interactive.plainLaw_run_split`: execution laws of composed
  and split strategies.
-/

@[expose] public section

namespace Cslib.Interactive

open scoped ENNReal
open Spec

namespace Spec

variable {F : Type → Type}

/-- Concatenate transcripts. -/
def Transcript.append : (s₁ s₂ : Spec) → Transcript s₁ → Transcript s₂ → Transcript (s₁ ++ s₂)
  | [], _, _, τ₂ => τ₂
  | _ :: s₁, s₂, τ₁, τ₂ => (τ₁.1, Transcript.append s₁ s₂ τ₁.2 τ₂)

/-- Split a transcript of a composition. -/
def Transcript.split : (s₁ s₂ : Spec) → Transcript (s₁ ++ s₂) → Transcript s₁ × Transcript s₂
  | [], _, τ => ((), τ)
  | _ :: s₁, s₂, τ => ((τ.1, (Transcript.split s₁ s₂ τ.2).1), (Transcript.split s₁ s₂ τ.2).2)

/-- Concatenate per-challenge data. -/
def PerChallenge.append : (s₁ s₂ : Spec) → PerChallenge F s₁ → PerChallenge F s₂ →
    PerChallenge F (s₁ ++ s₂)
  | [], _, _, b => b
  | .prover _ _ :: s₁, s₂, a, b => PerChallenge.append s₁ s₂ a b
  | .verifier _ :: s₁, s₂, a, b => (a.1, PerChallenge.append s₁ s₂ a.2 b)

/-- Split per-challenge data of a composition. -/
def PerChallenge.split : (s₁ s₂ : Spec) → PerChallenge F (s₁ ++ s₂) →
    PerChallenge F s₁ × PerChallenge F s₂
  | [], _, b => ((), b)
  | .prover _ _ :: s₁, s₂, a => PerChallenge.split s₁ s₂ a
  | .verifier _ :: s₁, s₂, a =>
    ((a.1, (PerChallenge.split s₁ s₂ a.2).1), (PerChallenge.split s₁ s₂ a.2).2)

/-- Queries about the messages of `s₁` are queries about those of `s₁ ++ s₂`. -/
def liftMsgLeft : (s₁ s₂ : Spec) → (q : MsgQuery s₁) →
    OracleComp (msgSpec (s₁ ++ s₂)) (MsgResponse s₁ q)
  | [], _, q => q.elim
  | .prover M I :: s₁, s₂, .inl q =>
    OracleComp.query (spec := msgSpec (.prover M I :: (s₁ ++ s₂))) (.inl q)
  | .prover M I :: s₁, s₂, .inr q =>
    OracleComp.interpret
      (fun q' => OracleComp.query (spec := msgSpec (.prover M I :: (s₁ ++ s₂))) (.inr q'))
      (liftMsgLeft s₁ s₂ q)
  | .verifier C :: s₁, s₂, q =>
    OracleComp.interpret
      (fun q' => OracleComp.query (spec := msgSpec (.verifier C :: (s₁ ++ s₂))) q')
      (liftMsgLeft s₁ s₂ q)

/-- Queries about the messages of `s₂` are queries about those of `s₁ ++ s₂`. -/
def liftMsgRight : (s₁ s₂ : Spec) → (q : MsgQuery s₂) →
    OracleComp (msgSpec (s₁ ++ s₂)) (MsgResponse s₂ q)
  | [], s₂, q => OracleComp.query (spec := msgSpec s₂) q
  | .prover M I :: s₁, s₂, q =>
    OracleComp.interpret
      (fun q' => OracleComp.query (spec := msgSpec (.prover M I :: (s₁ ++ s₂))) (.inr q'))
      (liftMsgRight s₁ s₂ q)
  | .verifier C :: s₁, s₂, q =>
    OracleComp.interpret
      (fun q' => OracleComp.query (spec := msgSpec (.verifier C :: (s₁ ++ s₂))) q')
      (liftMsgRight s₁ s₂ q)

end Spec

/-- Continue a strategy with another one once it ends. -/
def ProverStrategy.append {m : Type → Type} [Monad m] {α β : Type} :
    (s₁ s₂ : Spec) → ProverStrategy m s₁ α → (α → m (ProverStrategy m s₂ β)) →
      m (ProverStrategy m (s₁ ++ s₂) β)
  | [], _, a, next => next a
  | .prover M _ :: s₁, s₂, st, next =>
    let st : m (M × ProverStrategy m s₁ α) := st
    pure (show m (M × ProverStrategy m (s₁ ++ s₂) β) from do
      let (msg, st') ← st
      let rest ← ProverStrategy.append s₁ s₂ st' next
      return (msg, rest))
  | .verifier C :: s₁, s₂, st, next =>
    let st : C → m (ProverStrategy m s₁ α) := st
    pure (show C → m (ProverStrategy m (s₁ ++ s₂) β) from fun c => do
      let st' ← st c
      ProverStrategy.append s₁ s₂ st' next)

variable {ιP ιV : Type} {oP : OracleSpec ιP} {oV : OracleSpec ιV} {s₁ s₂ : Spec}
  {S₁ W₁ S₂ W₂ S₃ W₃ : Type}

/-- Lift a decision on `s₁` to the composition. -/
def liftDecisionLeft {α : Type} (s₁ s₂ : Spec) :
    OracleComp (oV ⊕ₒ msgSpec s₁) α → OracleComp (oV ⊕ₒ msgSpec (s₁ ++ s₂)) α :=
  OracleComp.interpret <| OracleComp.sumHandler
    (fun q => OracleComp.query (spec := oV ⊕ₒ msgSpec (s₁ ++ s₂)) (.inl q))
    fun q => OracleComp.liftRight (liftMsgLeft s₁ s₂ q)

/-- Lift a decision on `s₂` to the composition. -/
def liftDecisionRight {α : Type} (s₁ s₂ : Spec) :
    OracleComp (oV ⊕ₒ msgSpec s₂) α → OracleComp (oV ⊕ₒ msgSpec (s₁ ++ s₂)) α :=
  OracleComp.interpret <| OracleComp.sumHandler
    (fun q => OracleComp.query (spec := oV ⊕ₒ msgSpec (s₁ ++ s₂)) (.inl q))
    fun q => OracleComp.liftRight (liftMsgRight s₁ s₂ q)

/-- Sequential composition of verifiers: the second decides on the first one's output. -/
def Verifier.append (V₁ : Verifier oV s₁ S₁ S₂) (V₂ : Verifier oV s₂ S₂ S₃) :
    Verifier oV (s₁ ++ s₂) S₁ S₃ where
  samplers := PerChallenge.append s₁ s₂ V₁.samplers V₂.samplers
  decide x c := do
    let cs := PerChallenge.split s₁ s₂ c
    match ← liftDecisionLeft s₁ s₂ (V₁.decide x cs.1) with
    | none => return none
    | some x' => liftDecisionRight s₁ s₂ (V₂.decide x' cs.2)

/-- Sequential composition of reductions. -/
def Reduction.append (R₁ : Reduction oP oV s₁ S₁ W₁ S₂ W₂)
    (R₂ : Reduction oP oV s₂ S₂ W₂ S₃ W₃) : Reduction oP oV (s₁ ++ s₂) S₁ W₁ S₃ W₃ where
  prover x w := do
    let st ← R₁.prover x w
    ProverStrategy.append s₁ s₂ st fun xw => R₂.prover xw.1 xw.2
  verifier := R₁.verifier.append R₂.verifier

/-! ### Round-by-round composition (proved) -/

section Rbr

/-- The challenges of a composed transcript split into those of its halves. -/
private theorem challenges_split : ∀ (s₁ s₂ : Spec) (τ : Transcript (s₁ ++ s₂)),
    PerChallenge.split s₁ s₂ (Transcript.challenges (s₁ ++ s₂) τ) =
      (Transcript.challenges s₁ (Transcript.split s₁ s₂ τ).1,
        Transcript.challenges s₂ (Transcript.split s₁ s₂ τ).2)
  | [], _, _ => rfl
  | .prover _ _ :: s₁, s₂, τ => challenges_split s₁ s₂ τ.2
  | .verifier _ :: s₁, s₂, τ => by
    change ((τ.1, (PerChallenge.split s₁ s₂ (Transcript.challenges (s₁ ++ s₂) τ.2)).1),
      (PerChallenge.split s₁ s₂ (Transcript.challenges (s₁ ++ s₂) τ.2)).2) = _
    rw [challenges_split s₁ s₂ τ.2]
    rfl

/-- Lifted message queries of the first half are answered by the first half of the transcript. -/
private theorem interpret_liftMsgLeft : ∀ (s₁ s₂ : Spec) (τ : Transcript (s₁ ++ s₂))
    (q : MsgQuery s₁),
    OracleComp.interpret (m := Id) (Transcript.answer (s₁ ++ s₂) τ) (liftMsgLeft s₁ s₂ q) =
      Transcript.answer s₁ (Transcript.split s₁ s₂ τ).1 q
  | [], _, _, q => q.elim
  | .prover M I :: s₁, s₂, τ, .inl q => rfl
  | .prover M I :: s₁, s₂, τ, .inr q => by
    rw [liftMsgLeft, OracleComp.interpret_interpret]
    exact interpret_liftMsgLeft s₁ s₂ τ.2 q
  | .verifier C :: s₁, s₂, τ, q => by
    rw [liftMsgLeft, OracleComp.interpret_interpret]
    exact interpret_liftMsgLeft s₁ s₂ τ.2 q

/-- Lifted message queries of the second half are answered by the second half of the transcript. -/
private theorem interpret_liftMsgRight : ∀ (s₁ s₂ : Spec) (τ : Transcript (s₁ ++ s₂))
    (q : MsgQuery s₂),
    OracleComp.interpret (m := Id) (Transcript.answer (s₁ ++ s₂) τ) (liftMsgRight s₁ s₂ q) =
      Transcript.answer s₂ (Transcript.split s₁ s₂ τ).2 q
  | [], _, _, q => rfl
  | .prover M I :: s₁, s₂, τ, q => by
    rw [liftMsgRight, OracleComp.interpret_interpret]
    exact interpret_liftMsgRight s₁ s₂ τ.2 q
  | .verifier C :: s₁, s₂, τ, q => by
    rw [liftMsgRight, OracleComp.interpret_interpret]
    exact interpret_liftMsgRight s₁ s₂ τ.2 q



/-- The answers to the verifier's queries from a transcript, in the plain model. -/
private abbrev answerAll (s : Spec) (τ : Transcript s) :
    (q : Empty ⊕ MsgQuery s) → (OracleSpec.empty ⊕ₒ msgSpec s) q :=
  OracleComp.sumHandler (m := Id) (fun e : Empty => e.elim) (Transcript.answer s τ)

private theorem outputOn_eq (V : Verifier OracleSpec.empty s₁ S₁ S₂) (x : S₁) (τ : Transcript s₁) :
    V.outputOn x τ = OracleComp.interpret (m := Id) (answerAll s₁ τ)
      (V.decide x (Transcript.challenges s₁ τ)) :=
  rfl

private theorem interpret_liftDecisionLeft {α : Type} (τ : Transcript (s₁ ++ s₂))
    (p : OracleComp (OracleSpec.empty ⊕ₒ msgSpec s₁) α) :
    OracleComp.interpret (m := Id) (answerAll (s₁ ++ s₂) τ) (liftDecisionLeft s₁ s₂ p) =
      OracleComp.interpret (m := Id) (answerAll s₁ (Transcript.split s₁ s₂ τ).1) p := by
  rw [liftDecisionLeft]
  refine (OracleComp.interpret_interpret (m := Id) _ _ _).trans ?_
  congr 1
  funext q
  rcases q with e | q
  · exact e.elim
  · refine (OracleComp.interpret_interpret (m := Id) _ _ _).trans ?_
    exact interpret_liftMsgLeft s₁ s₂ τ q

private theorem interpret_liftDecisionRight {α : Type} (τ : Transcript (s₁ ++ s₂))
    (p : OracleComp (OracleSpec.empty ⊕ₒ msgSpec s₂) α) :
    OracleComp.interpret (m := Id) (answerAll (s₁ ++ s₂) τ) (liftDecisionRight s₁ s₂ p) =
      OracleComp.interpret (m := Id) (answerAll s₂ (Transcript.split s₁ s₂ τ).2) p := by
  rw [liftDecisionRight]
  refine (OracleComp.interpret_interpret (m := Id) _ _ _).trans ?_
  congr 1
  funext q
  rcases q with e | q
  · exact e.elim
  · refine (OracleComp.interpret_interpret (m := Id) _ _ _).trans ?_
    exact interpret_liftMsgRight s₁ s₂ τ q

/-- The composed verifier's output is the second verifier's output on the first one's. -/
theorem outputOn_append (V₁ : Verifier OracleSpec.empty s₁ S₁ S₂)
    (V₂ : Verifier OracleSpec.empty s₂ S₂ S₃)
    (x : S₁) (τ : Transcript (s₁ ++ s₂)) :
    (V₁.append V₂).outputOn x τ =
      (V₁.outputOn x (Transcript.split s₁ s₂ τ).1).bind
        fun x' => V₂.outputOn x' (Transcript.split s₁ s₂ τ).2 := by
  rw [outputOn_eq, outputOn_eq]
  simp only [Verifier.append, challenges_split]
  refine (OracleComp.interpret_bind (m := Id) _ _ _).trans ?_
  erw [interpret_liftDecisionLeft]
  cases h : OracleComp.interpret (m := Id) (answerAll s₁ (Transcript.split s₁ s₂ τ).1)
      (V₁.decide x (Transcript.challenges s₁ (Transcript.split s₁ s₂ τ).1)) with
  | none => rfl
  | some x' =>
    refine (interpret_liftDecisionRight τ _).trans ?_
    exact (outputOn_eq V₂ x' _).symm


/-- The state function of a composition: that of the first half, then, once the first half is
complete, the second half's state function for that first half. -/
private def compState :
    (s₁ s₂ : Spec) → (Prefix s₁ → Prop) → (Transcript s₁ → Prefix s₂ → Prop) →
    Prefix (s₁ ++ s₂) → Prop
  | [], _, _, next, p => next () p
  | _ :: _, _, S, _, none => S none
  | _ :: s₁, s₂, S, next, some (m, p) =>
    compState s₁ s₂ (fun q => S (some (m, q))) (fun τ => next (m, τ)) p

/-- A doomed start of the first half is a doomed start of the composition. -/
private theorem not_compState_empty {s₁ s₂ : Spec} {smp : PerChallenge ProbComp s₁}
    {ε : PerChallenge (fun _ => ℝ≥0∞) s₁} {S : Prefix s₁ → Prop} {wins : Transcript s₁ → Prop}
    {next : Transcript s₁ → Prefix s₂ → Prop} (h : RbrFrom s₁ smp ε S wins)
    (hjunc : ∀ τ, ¬ wins τ → ¬ next τ (Prefix.empty s₂)) (hS : ¬ S (Prefix.empty s₁)) :
    ¬ compState s₁ s₂ S next (Prefix.empty (s₁ ++ s₂)) := by
  cases s₁ with
  | nil => exact hjunc () (h hS)
  | cons r s₁ => exact hS

/-- The round-by-round condition holds trivially when nothing is ever alive. -/
private theorem rbrFrom_false : ∀ (s : Spec) (smp : PerChallenge ProbComp s)
    (ε : PerChallenge (fun _ => ℝ≥0∞) s), RbrFrom s smp ε (fun _ => False) (fun _ => False)
  | [], _, _ => fun _ h => h
  | .prover _ _ :: s, smp, ε => ⟨fun _ _ h => h, fun _ => rbrFrom_false s smp ε⟩
  | .verifier _ :: s, smp, ε => ⟨fun _ => by simp, fun _ => rbrFrom_false s smp.2 ε.2⟩

/-- The round-by-round condition is invariant under equivalent state functions and events. -/
theorem RbrFrom.congr : ∀ {s : Spec} {smp : PerChallenge ProbComp s}
    {ε : PerChallenge (fun _ => ℝ≥0∞) s} {S S' : Prefix s → Prop}
    {wins wins' : Transcript s → Prop},
    (∀ p, S p ↔ S' p) → (∀ τ, wins τ ↔ wins' τ) → RbrFrom s smp ε S wins →
      RbrFrom s smp ε S' wins'
  | [], _, _, _, _, _, _, hS, hw, h => fun h' hw' => h (mt (hS ()).1 h') ((hw ()).2 hw')
  | .prover _ _ :: s, _, _, _, _, _, _, hS, hw, h =>
    ⟨fun h0 m h1 => h.1 (mt (hS none).1 h0) m ((hS _).2 h1),
      fun m => RbrFrom.congr (fun p => hS _) (fun τ => hw _) (h.2 m)⟩
  | .verifier _ :: s, smp, _, S, S', _, _, hS, hw, h =>
    ⟨fun h0 => by
        have hset : {c | S' (some (c, Prefix.empty s))} = {c | S (some (c, Prefix.empty s))} :=
          Set.ext fun c => (hS _).symm
        rw [hset]
        exact h.1 (mt (hS none).1 h0),
      fun c => RbrFrom.congr (fun p => hS _) (fun τ => hw _) (h.2 c)⟩

/-- **Round-by-round composition, per prefix.** -/
private theorem rbrFrom_append : ∀ (s₁ s₂ : Spec) (smp₁ : PerChallenge ProbComp s₁)
    (smp₂ : PerChallenge ProbComp s₂) (ε₁ : PerChallenge (fun _ => ℝ≥0∞) s₁)
    (ε₂ : PerChallenge (fun _ => ℝ≥0∞) s₂) (S : Prefix s₁ → Prop) (wins₁ : Transcript s₁ → Prop)
    (next : Transcript s₁ → Prefix s₂ → Prop) (wins₂ : Transcript s₁ → Transcript s₂ → Prop),
    RbrFrom s₁ smp₁ ε₁ S wins₁ → (∀ τ, ¬ wins₁ τ → ¬ next τ (Prefix.empty s₂)) →
    (∀ τ, RbrFrom s₂ smp₂ ε₂ (next τ) (wins₂ τ)) →
    RbrFrom (s₁ ++ s₂) (PerChallenge.append s₁ s₂ smp₁ smp₂) (PerChallenge.append s₁ s₂ ε₁ ε₂)
      (compState s₁ s₂ S next)
      (fun τ => wins₂ (Transcript.split s₁ s₂ τ).1 (Transcript.split s₁ s₂ τ).2)
  | [], _, _, _, _, _, _, _, _, _, _, _, h₂ => h₂ ()
  | .prover M I :: s₁, s₂, smp₁, smp₂, ε₁, ε₂, S, wins₁, next, wins₂, h₁, hjunc, h₂ =>
    ⟨fun h0 m => not_compState_empty (h₁.2 m) (fun τ => hjunc (m, τ)) (h₁.1 h0 m),
      fun m => rbrFrom_append s₁ s₂ smp₁ smp₂ ε₁ ε₂ _ _ (fun τ => next (m, τ))
        (fun τ => wins₂ (m, τ)) (h₁.2 m) (fun τ => hjunc (m, τ)) (fun τ => h₂ (m, τ))⟩
  | .verifier C :: s₁, s₂, smp₁, smp₂, ε₁, ε₂, S, wins₁, next, wins₂, h₁, hjunc, h₂ =>
    ⟨fun h0 => by
        refine le_trans (MeasureTheory.measure_mono fun c hc => ?_) (h₁.1 h0)
        by_contra hS
        exact not_compState_empty (h₁.2 c) (fun τ => hjunc (c, τ)) hS hc,
      fun c => rbrFrom_append s₁ s₂ smp₁.2 smp₂ ε₁.2 ε₂ _ _ (fun τ => next (c, τ))
        (fun τ => wins₂ (c, τ)) (h₁.2 c) (fun τ => hjunc (c, τ)) (fun τ => h₂ (c, τ))⟩


/-- **Round-by-round soundness composes**, with the concatenated per-round errors. -/
theorem Verifier.RbrSound.append {V₁ : Verifier OracleSpec.empty s₁ S₁ S₂}
    {V₂ : Verifier OracleSpec.empty s₂ S₂ S₃} {L₁ : Set S₁} {L₂ : Set S₂} {L₃ : Set S₃}
    {ε₁ : PerChallenge (fun _ => ℝ≥0∞) s₁} {ε₂ : PerChallenge (fun _ => ℝ≥0∞) s₂}
    (h₁ : V₁.RbrSound L₁ L₂ ε₁) (h₂ : V₂.RbrSound L₂ L₃ ε₂) :
    (V₁.append V₂).RbrSound L₁ L₃ (PerChallenge.append s₁ s₂ ε₁ ε₂) := by
  obtain ⟨T₁, hinit₁, hr₁⟩ := h₁
  obtain ⟨T₂, hinit₂, hr₂⟩ := h₂
  let next : S₁ → Transcript s₁ → Prefix s₂ → Prop :=
    fun x τ₁ p => ∃ x', V₁.outputOn x τ₁ = some x' ∧ T₂ x' p
  have hjunc : ∀ x τ₁, ¬ (∃ x' ∈ L₂, V₁.outputOn x τ₁ = some x') →
      ¬ next x τ₁ (Prefix.empty s₂) := by
    rintro x τ₁ hw ⟨x', hout, hT⟩
    by_cases hx' : x' ∈ L₂
    · exact hw ⟨x', hx', hout⟩
    · exact hinit₂ x' hx' hT
  have hsecond : ∀ x τ₁, RbrFrom s₂ V₂.samplers ε₂ (next x τ₁)
      (fun τ₂ => ∃ x'' ∈ L₃, (V₁.outputOn x τ₁).bind (fun x' => V₂.outputOn x' τ₂) = some x'') := by
    intro x τ₁
    cases hout : V₁.outputOn x τ₁ with
    | none =>
      refine RbrFrom.congr (fun p => ?_) (fun τ => ?_) (rbrFrom_false s₂ V₂.samplers ε₂)
      · simp [next, hout]
      · simp
    | some x' =>
      refine RbrFrom.congr (fun p => ?_) (fun τ => ?_) (hr₂ x')
      · simp [next, hout]
      · simp
  refine ⟨fun x => compState s₁ s₂ (T₁ x) (next x),
    fun x hx => not_compState_empty (hr₁ x) (hjunc x) (hinit₁ x hx), fun x => ?_⟩
  refine RbrFrom.congr (fun p => Iff.rfl) (fun τ => ?_)
    (rbrFrom_append s₁ s₂ V₁.samplers V₂.samplers ε₁ ε₂ (T₁ x) _ (next x) _ (hr₁ x) (hjunc x)
      (hsecond x))
  rw [outputOn_append]

end Rbr

/-! ### Composition of completeness, soundness and knowledge soundness -/

section Plain

variable {R₁ : Reduction OracleSpec.empty OracleSpec.empty s₁ S₁ W₁ S₂ W₂}
  {R₂ : Reduction OracleSpec.empty OracleSpec.empty s₂ S₂ W₂ S₃ W₃}
  {V₁ : Verifier OracleSpec.empty s₁ S₁ S₂} {V₂ : Verifier OracleSpec.empty s₂ S₂ S₃}
  {rel₁ : S₁ → W₁ → Prop} {rel₂ : S₂ → W₂ → Prop} {rel₃ : S₃ → W₃ → Prop}
  {L₁ : Set S₁} {L₂ : Set S₂} {L₃ : Set S₃} {ε₁ ε₂ : ℝ≥0∞}

/-- The composed straight-line extractor: extract the intermediate witness from the second half of
the transcript, at the statement the first verifier outputs, then the input witness from the first
half. The default intermediate statement `y₀` is used only when the first verifier rejects, when
the composed verifier rejects too. -/
noncomputable def Verifier.extractAppend (V₁ : Verifier OracleSpec.empty s₁ S₁ S₂)
    (E₁ : S₁ → Transcript s₁ → W₂ → W₁) (E₂ : S₂ → Transcript s₂ → W₃ → W₂) (y₀ : S₂) :
    S₁ → Transcript (s₁ ++ s₂) → W₃ → W₁ := fun x τ w₃ =>
  E₁ x (Transcript.split s₁ s₂ τ).1
    (E₂ ((V₁.outputOn x (Transcript.split s₁ s₂ τ).1).getD y₀) (Transcript.split s₁ s₂ τ).2 w₃)

/-- The total error of concatenated per-round errors. -/
theorem PerChallenge.sum_append (ε₁ : PerChallenge (fun _ => ℝ≥0∞) s₁)
    (ε₂ : PerChallenge (fun _ => ℝ≥0∞) s₂) :
    PerChallenge.sum (s₁ ++ s₂) (PerChallenge.append s₁ s₂ ε₁ ε₂) =
      PerChallenge.sum s₁ ε₁ + PerChallenge.sum s₂ ε₂ := by
  induction s₁ with
  | nil => simp [PerChallenge.append, PerChallenge.sum]
  | cons r s₁ ih =>
    cases r with
    | prover M I => exact ih ε₁
    | verifier C =>
      change ε₁.1 + PerChallenge.sum (s₁ ++ s₂) (PerChallenge.append s₁ s₂ ε₁.2 ε₂) = _
      rw [ih, PerChallenge.sum, add_assoc]

end Plain

/-- Continue a strategy with an effect at its end that sees the transcript. -/
def ProverStrategy.bindLeaf {m : Type → Type} [Monad m] {α β : Type} :
    (s : Spec) → ProverStrategy m s α → (Transcript s → α → m β) → m (ProverStrategy m s β)
  | [], a, f => f () a
  | .prover M _ :: s, st, f =>
    let st : m (M × ProverStrategy m s α) := st
    pure (show m (M × ProverStrategy m s β) from do
      let (msg, st') ← st
      let rest ← ProverStrategy.bindLeaf s st' fun τ a => f (msg, τ) a
      return (msg, rest))
  | .verifier C :: s, st, f =>
    let st : C → m (ProverStrategy m s α) := st
    pure (show C → m (ProverStrategy m s β) from fun c => do
      let st' ← st c
      ProverStrategy.bindLeaf s st' fun τ a => f (c, τ) a)

/-- Running a strategy continued by an effect at its end: the effect sees the transcript. -/
theorem plainLaw_bindLeaf_run : ∀ (s : Spec) (smp : PerChallenge ProbComp s) {α β : Type}
    (st : ProverStrategy (ProbOracleComp OracleSpec.empty) s α)
    (f : Transcript s → α → ProbOracleComp OracleSpec.empty β),
    plainLaw (ProverStrategy.bindLeaf s st f >>= runStrategy s smp) =
      (plainLaw (runStrategy s smp st)).bind fun r => (plainLaw (f r.1 r.2)).map fun b => (r.1, b)
  | [], _, _, _, a, f => by
    simp [ProverStrategy.bindLeaf, runStrategy]
  | .prover M I :: s, smp, _, _, st, f => by
    simp only [ProverStrategy.bindLeaf, runStrategy, plainLaw_bind, plainLaw_pure, PMF.pure_bind,
      PMF.bind_bind]
    congr 1
    funext a
    have ih := plainLaw_bindLeaf_run s smp a.2 (fun τ b => f (a.1, τ) b)
    rw [plainLaw_bind] at ih
    rw [← PMF.bind_bind, ih, PMF.bind_bind]
    congr 1
    funext r
    rw [PMF.bind_map]
    rfl
  | .verifier C :: s, smp, _, _, st, f => by
    simp only [ProverStrategy.bindLeaf, runStrategy, plainLaw_bind, plainLaw_pure, plainLaw_sample,
      PMF.pure_bind, PMF.bind_bind]
    congr 1
    funext c
    congr 1
    funext st'
    have ih := plainLaw_bindLeaf_run s smp.2 st' (fun τ b => f (c, τ) b)
    rw [plainLaw_bind] at ih
    rw [← PMF.bind_bind, ih, PMF.bind_bind]
    congr 1
    funext r
    rw [PMF.bind_map]
    rfl


/-- Split a strategy for `s₁ ++ s₂` into a strategy for `s₁` ending with one for `s₂`. -/
def ProverStrategy.split {m : Type → Type} [Monad m] {α : Type} :
    (s₁ s₂ : Spec) → ProverStrategy m (s₁ ++ s₂) α → ProverStrategy m s₁ (ProverStrategy m s₂ α)
  | [], _, st => st
  | .prover M _ :: s₁, s₂, st =>
    let st : m (M × ProverStrategy m (s₁ ++ s₂) α) := st
    show m (M × ProverStrategy m s₁ (ProverStrategy m s₂ α)) from
      (fun p => (p.1, ProverStrategy.split s₁ s₂ p.2)) <$> st
  | .verifier C :: s₁, s₂, st =>
    let st : C → m (ProverStrategy m (s₁ ++ s₂) α) := st
    show C → m (ProverStrategy m s₁ (ProverStrategy m s₂ α)) from
      fun c => ProverStrategy.split s₁ s₂ <$> st c

/-- Running a composed strategy runs the first part, then the continuation on its result. -/
theorem plainLaw_run_append : ∀ (s₁ s₂ : Spec) (smp₁ : PerChallenge ProbComp s₁)
    (smp₂ : PerChallenge ProbComp s₂) {α β : Type}
    (st : ProverStrategy (ProbOracleComp OracleSpec.empty) s₁ α)
    (next : α → ProbOracleComp OracleSpec.empty
      (ProverStrategy (ProbOracleComp OracleSpec.empty) s₂ β)),
    plainLaw (ProverStrategy.append s₁ s₂ st next >>=
        runStrategy (s₁ ++ s₂) (PerChallenge.append s₁ s₂ smp₁ smp₂)) =
      (plainLaw (runStrategy s₁ smp₁ st)).bind fun r₁ =>
        (plainLaw (next r₁.2 >>= runStrategy s₂ smp₂)).map
          fun r₂ => (Transcript.append s₁ s₂ r₁.1 r₂.1, r₂.2)
  | [], s₂, _, smp₂, _, _, a, next => by
    simp only [ProverStrategy.append, runStrategy, plainLaw_pure, PMF.pure_bind,
      PerChallenge.append, Transcript.append]
    exact (PMF.map_id _).symm
  | .prover M I :: s₁, s₂, smp₁, smp₂, _, _, st, next => by
    simp only [ProverStrategy.append, List.cons_append, runStrategy, plainLaw_bind, plainLaw_pure,
      PMF.pure_bind, PMF.bind_bind, PerChallenge.append]
    congr 1
    funext a
    have ih := plainLaw_run_append s₁ s₂ smp₁ smp₂ a.2 next
    rw [plainLaw_bind] at ih
    rw [← PMF.bind_bind, ih, PMF.bind_bind]
    congr 1
    funext r
    rw [PMF.bind_map, plainLaw_bind]
    rfl
  | .verifier C :: s₁, s₂, smp₁, smp₂, _, _, st, next => by
    simp only [ProverStrategy.append, List.cons_append, runStrategy, plainLaw_bind, plainLaw_pure,
      plainLaw_sample, PMF.pure_bind, PMF.bind_bind, PerChallenge.append]
    congr 1
    funext c
    congr 1
    funext st'
    have ih := plainLaw_run_append s₁ s₂ smp₁.2 smp₂ st' next
    rw [plainLaw_bind] at ih
    rw [← PMF.bind_bind, ih, PMF.bind_bind]
    congr 1
    funext r
    rw [PMF.bind_map, plainLaw_bind]
    rfl

/-- Running any strategy for `s₁ ++ s₂` runs its split: the first part, then the rest. -/
theorem plainLaw_run_split : ∀ (s₁ s₂ : Spec) (smp₁ : PerChallenge ProbComp s₁)
    (smp₂ : PerChallenge ProbComp s₂) {α : Type}
    (st : ProverStrategy (ProbOracleComp OracleSpec.empty) (s₁ ++ s₂) α),
    plainLaw (runStrategy (s₁ ++ s₂) (PerChallenge.append s₁ s₂ smp₁ smp₂) st) =
      (plainLaw (runStrategy s₁ smp₁ (ProverStrategy.split s₁ s₂ st))).bind fun r₁ =>
        (plainLaw (runStrategy s₂ smp₂ r₁.2)).map
          fun r₂ => (Transcript.append s₁ s₂ r₁.1 r₂.1, r₂.2)
  | [], s₂, _, smp₂, _, st => by
    simp only [ProverStrategy.split, runStrategy, plainLaw_pure, PMF.pure_bind, PerChallenge.append,
      Transcript.append]
    exact (PMF.map_id _).symm
  | .prover M I :: s₁, s₂, smp₁, smp₂, _, st => by
    simp only [ProverStrategy.split, List.cons_append, runStrategy, plainLaw_bind, plainLaw_pure,
      plainLaw_map, PMF.pure_bind, PMF.bind_bind, PMF.bind_map, PerChallenge.append,
      Function.comp_apply]
    congr 1
    funext a
    rw [plainLaw_run_split s₁ s₂ smp₁ smp₂ a.2, PMF.bind_bind]
    congr 1
    funext r
    rw [PMF.bind_map]
    rfl
  | .verifier C :: s₁, s₂, smp₁, smp₂, _, st => by
    simp only [ProverStrategy.split, List.cons_append, runStrategy, plainLaw_bind, plainLaw_pure,
      plainLaw_map, plainLaw_sample, PMF.pure_bind, PMF.bind_bind, PMF.bind_map,
      PerChallenge.append, Function.comp_apply]
    congr 1
    funext c
    congr 1
    funext st'
    rw [plainLaw_run_split s₁ s₂ smp₁.2 smp₂ st', PMF.bind_bind]
    congr 1
    funext r
    rw [PMF.bind_map]
    rfl


/-- Splitting a concatenated transcript recovers its halves. -/
theorem Spec.Transcript.split_append : ∀ (s₁ s₂ : Spec) (τ₁ : Transcript s₁)
    (τ₂ : Transcript s₂), Transcript.split s₁ s₂ (Transcript.append s₁ s₂ τ₁ τ₂) = (τ₁, τ₂)
  | [], _, _, _ => rfl
  | _ :: s₁, s₂, τ₁, τ₂ => by
    simp only [Transcript.split, Transcript.append, Spec.Transcript.split_append s₁ s₂ τ₁.2 τ₂]

private theorem toOuterMeasure_bind_le_add {α β : Type} (μ : PMF α) (f : α → PMF β)
    (t : Set β) (A : Set α) {K : ℝ≥0∞} (h : ∀ a ∉ A, (f a).toOuterMeasure t ≤ K) :
    (μ.bind f).toOuterMeasure t ≤ μ.toOuterMeasure A + K := by
  simpa only [compl_compl] using
    Probability.PMF.toOuterMeasure_bind_failure_le μ f Aᶜ t K fun a _ ha => h a ha

section Compose

/-- The honest run of a composed reduction runs the first reduction, then the second on the
first prover's output. -/
private theorem plainLaw_run_reductionAppend
    (R₁ : Reduction OracleSpec.empty OracleSpec.empty s₁ S₁ W₁ S₂ W₂)
    (R₂ : Reduction OracleSpec.empty OracleSpec.empty s₂ S₂ W₂ S₃ W₃) (x : S₁) (w : W₁) :
    plainLaw ((R₁.append R₂).prover x w >>=
        runStrategy (s₁ ++ s₂) (R₁.append R₂).verifier.samplers) =
      (plainLaw (R₁.prover x w >>= runStrategy s₁ R₁.verifier.samplers)).bind fun r₁ =>
        (plainLaw (R₂.prover r₁.2.1 r₁.2.2 >>= runStrategy s₂ R₂.verifier.samplers)).map
          fun r₂ => (Transcript.append s₁ s₂ r₁.1 r₂.1, r₂.2) := by
  simp only [Reduction.append, Verifier.append, bind_assoc, plainLaw_bind, PMF.bind_bind]
  congr 1
  funext st
  rw [← plainLaw_bind, plainLaw_run_append]
  simp only [plainLaw_bind]

/-- **Completeness errors add up under sequential composition.** -/
theorem Reduction.Complete.append {R₁ : Reduction OracleSpec.empty OracleSpec.empty s₁ S₁ W₁ S₂ W₂}
    {R₂ : Reduction OracleSpec.empty OracleSpec.empty s₂ S₂ W₂ S₃ W₃}
    {rel₁ : S₁ → W₁ → Prop} {rel₂ : S₂ → W₂ → Prop} {rel₃ : S₃ → W₃ → Prop} {ε₁ ε₂ : ℝ≥0∞}
    (h₁ : R₁.Complete World.plain rel₁ rel₂ ε₁) (h₂ : R₂.Complete World.plain rel₂ rel₃ ε₂) :
    (R₁.append R₂).Complete World.plain rel₁ rel₃ (ε₁ + ε₂) := by
  intro x w hxw
  have hl₁ := h₁ x w hxw
  rw [Reduction.run, World.plain_eval_execute, PMF.toOuterMeasure_map_apply] at hl₁ ⊢
  rw [plainLaw_run_reductionAppend]
  refine le_trans (toOuterMeasure_bind_le_add _ _ _ _ fun r₁ hr₁ => ?_) (add_le_add hl₁ le_rfl)
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, not_not] at hr₁
  obtain ⟨hout, hrel⟩ := hr₁
  have hl₂ := h₂ r₁.2.1 r₁.2.2 hrel
  rw [Reduction.run, World.plain_eval_execute, PMF.toOuterMeasure_map_apply] at hl₂
  rw [PMF.toOuterMeasure_map_apply]
  convert hl₂ using 2
  ext r₂
  simp [Reduction.append, outputOn_append, Spec.Transcript.split_append, hout]


/-- A run against a composed verifier is a run of the split strategy against the first, then
of its continuation against the second. -/
private theorem plainLaw_run_verifierAppend (V₁ : Verifier OracleSpec.empty s₁ S₁ S₂)
    (V₂ : Verifier OracleSpec.empty s₂ S₂ S₃) {α : Type}
    (P : ProbOracleComp OracleSpec.empty
      (ProverStrategy (ProbOracleComp OracleSpec.empty) (s₁ ++ s₂) α)) :
    plainLaw (P >>= runStrategy (s₁ ++ s₂) (V₁.append V₂).samplers) =
      (plainLaw ((ProverStrategy.split s₁ s₂ ·) <$> P >>= runStrategy s₁ V₁.samplers)).bind
        fun r₁ => (plainLaw (runStrategy s₂ V₂.samplers r₁.2)).map
          fun r₂ => (Transcript.append s₁ s₂ r₁.1 r₂.1, r₂.2) := by
  simp only [plainLaw_bind, plainLaw_map, PMF.bind_map, PMF.bind_bind]
  congr 1
  funext st
  exact plainLaw_run_split s₁ s₂ V₁.samplers V₂.samplers st

/-- **Soundness errors add up under sequential composition**, through the intermediate
language. -/
theorem Verifier.Sound.append {V₁ : Verifier OracleSpec.empty s₁ S₁ S₂}
    {V₂ : Verifier OracleSpec.empty s₂ S₂ S₃} {L₁ : Set S₁} {L₂ : Set S₂} {L₃ : Set S₃}
    {ε₁ ε₂ : ℝ≥0∞} (h₁ : V₁.Sound (oP := OracleSpec.empty) World.plain L₁ L₂ ε₁)
    (h₂ : V₂.Sound (oP := OracleSpec.empty) World.plain L₂ L₃ ε₂) :
    (V₁.append V₂).Sound (oP := OracleSpec.empty) World.plain L₁ L₃ (ε₁ + ε₂) := by
  intro x hx α P
  have hl₁ := h₁ x hx _ ((ProverStrategy.split s₁ s₂ ·) <$> P)
  rw [World.plain_eval_execute, PMF.toOuterMeasure_map_apply] at hl₁ ⊢
  rw [plainLaw_run_verifierAppend]
  refine le_trans (toOuterMeasure_bind_le_add _ _ _ _ fun r₁ hr₁ => ?_) (add_le_add hl₁ le_rfl)
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, not_exists, not_and] at hr₁
  rw [PMF.toOuterMeasure_map_apply]
  cases hout : V₁.outputOn x r₁.1 with
  | none =>
    have hset : (fun r₂ : Transcript s₂ × α => (Transcript.append s₁ s₂ r₁.1 r₂.1, r₂.2)) ⁻¹'
        ((fun r : Transcript (s₁ ++ s₂) × α => (r.1, (V₁.append V₂).outputOn x r.1, r.2)) ⁻¹'
          {r | ∃ x' ∈ L₃, r.2.1 = some x'}) = ∅ := by
      ext r₂
      simp [outputOn_append, Spec.Transcript.split_append, hout]
    rw [hset, MeasureTheory.measure_empty]
    exact zero_le
  | some y =>
    have hy : y ∉ L₂ := fun hy => hr₁ y hy hout
    have hl₂ := h₂ y hy _ (pure r₁.2)
    rw [World.plain_eval_execute, PMF.toOuterMeasure_map_apply] at hl₂
    simp only [plainLaw_bind, plainLaw_pure, PMF.pure_bind] at hl₂
    convert hl₂ using 2
    ext r₂
    simp [outputOn_append, Spec.Transcript.split_append, hout]


/-- **Straight-line extractors compose**, with the sum of the knowledge errors. The first
verifier's knowledge soundness is applied to a prover that simulates the second phase with the
public samplers. -/
theorem Verifier.KnowledgeSound.append {V₁ : Verifier OracleSpec.empty s₁ S₁ S₂}
    {V₂ : Verifier OracleSpec.empty s₂ S₂ S₃}
    {rel₁ : S₁ → W₁ → Prop} {rel₂ : S₂ → W₂ → Prop} {rel₃ : S₃ → W₃ → Prop} {ε₁ ε₂ : ℝ≥0∞}
    {E₁ : S₁ → Transcript s₁ → W₂ → W₁} {E₂ : S₂ → Transcript s₂ → W₃ → W₂}
    (h₁ : V₁.KnowledgeSound rel₁ rel₂ E₁ ε₁)
    (h₂ : V₂.KnowledgeSound rel₂ rel₃ E₂ ε₂) (y₀ : S₂) :
    (V₁.append V₂).KnowledgeSound rel₁ rel₃
      (V₁.extractAppend E₁ E₂ y₀) (ε₁ + ε₂) := by
  intro x P
  rw [World.plain_eval_execute, PMF.toOuterMeasure_map_apply, plainLaw_run_verifierAppend]
  let T₁ : Set (Transcript (s₁ ++ s₂) × W₃) := {r | ∃ y,
    V₁.outputOn x (Transcript.split s₁ s₂ r.1).1 = some y ∧
      rel₂ y (E₂ y (Transcript.split s₁ s₂ r.1).2 r.2) ∧
      ¬ rel₁ x (E₁ x (Transcript.split s₁ s₂ r.1).1 (E₂ y (Transcript.split s₁ s₂ r.1).2 r.2))}
  let T₂ : Set (Transcript (s₁ ++ s₂) × W₃) := {r | ∃ y,
    V₁.outputOn x (Transcript.split s₁ s₂ r.1).1 = some y ∧
      (∃ x'', V₂.outputOn y (Transcript.split s₁ s₂ r.1).2 = some x'' ∧ rel₃ x'' r.2) ∧
      ¬ rel₂ y (E₂ y (Transcript.split s₁ s₂ r.1).2 r.2)}
  have hsub : (fun r : Transcript (s₁ ++ s₂) × W₃ => (r.1, (V₁.append V₂).outputOn x r.1, r.2)) ⁻¹'
      {r | (∃ x', r.2.1 = some x' ∧ rel₃ x' r.2.2) ∧
        ¬ rel₁ x (V₁.extractAppend E₁ E₂ y₀ x r.1 r.2.2)} ⊆ T₁ ∪ T₂ := by
    rintro ⟨τ, w₃⟩ ⟨⟨x'', hout, hrel⟩, hnot⟩
    simp only [outputOn_append] at hout
    obtain ⟨y, hy, hy₂⟩ := Option.bind_eq_some_iff.mp hout
    by_cases h : rel₂ y (E₂ y (Transcript.split s₁ s₂ τ).2 w₃)
    · left
      refine ⟨y, hy, h, ?_⟩
      simpa [Verifier.extractAppend, hy] using hnot
    · exact Or.inr ⟨y, hy, ⟨x'', hy₂, hrel⟩, h⟩
  refine le_trans (MeasureTheory.measure_mono hsub)
    (le_trans (MeasureTheory.measure_union_le _ _) (add_le_add ?_ ?_))
  · let P₁ : ProbOracleComp OracleSpec.empty
        (ProverStrategy (ProbOracleComp OracleSpec.empty) s₁ W₂) :=
      (ProverStrategy.split s₁ s₂ ·) <$> P >>= fun st₁ => ProverStrategy.bindLeaf s₁ st₁
        fun τ₁ st₂ => (fun r₂ => E₂ ((V₁.outputOn x τ₁).getD y₀) r₂.1 r₂.2) <$>
          runStrategy s₂ V₂.samplers st₂
    have hl₁ := h₁ x P₁
    rw [World.plain_eval_execute, PMF.toOuterMeasure_map_apply] at hl₁
    have hlaw₁ : plainLaw (P₁ >>= runStrategy s₁ V₁.samplers) =
        (plainLaw ((ProverStrategy.split s₁ s₂ ·) <$> P >>= runStrategy s₁ V₁.samplers)).bind
          fun r₁ => (plainLaw (runStrategy s₂ V₂.samplers r₁.2)).map
            fun r₂ => (r₁.1, E₂ ((V₁.outputOn x r₁.1).getD y₀) r₂.1 r₂.2) := by
      simp only [P₁, bind_assoc, plainLaw_bind, PMF.bind_bind]
      congr 1
      funext st₁
      rw [← plainLaw_bind, plainLaw_bindLeaf_run]
      congr 1
      funext r₁
      rw [plainLaw_map, PMF.map_comp]
      rfl
    rw [hlaw₁] at hl₁
    refine le_trans (le_of_eq ?_) hl₁
    rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
    refine tsum_congr fun r₁ => ?_
    congr 1
    rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
    congr 1
    ext r₂
    cases hout : V₁.outputOn x r₁.1 <;> simp [T₁, Spec.Transcript.split_append, hout]
  · refine Probability.PMF.toOuterMeasure_bind_le _ _ _ fun r₁ => ?_
    rw [PMF.toOuterMeasure_map_apply]
    cases hout : V₁.outputOn x r₁.1 with
    | none =>
      have hset : (fun r₂ : Transcript s₂ × W₃ => (Transcript.append s₁ s₂ r₁.1 r₂.1, r₂.2)) ⁻¹'
          T₂ = ∅ := by
        ext r₂
        simp [T₂, Spec.Transcript.split_append, hout]
      rw [hset, MeasureTheory.measure_empty]
      exact zero_le
    | some y =>
      have hl₂ := h₂ y (pure r₁.2)
      rw [World.plain_eval_execute, PMF.toOuterMeasure_map_apply] at hl₂
      simp only [plainLaw_bind, plainLaw_pure, PMF.pure_bind] at hl₂
      convert hl₂ using 2
      ext r₂
      simp [T₂, Spec.Transcript.split_append, hout]

end Compose

/-! ### Iteration -/

/-- The rounds of the stages `s 0`, …, `s (k - 1)`, in order. -/
def iterSpec (s : ℕ → Spec) : ℕ → Spec
  | 0 => []
  | k + 1 => iterSpec s k ++ s k

/-- The reduction without rounds that keeps the statement and the witness. -/
def Reduction.id {S W : Type} : Reduction oP oV [] S W S W where
  prover x w := pure (x, w)
  verifier := { samplers := (), decide := fun x _ => pure (some x) }

/-- Run the stages `R 0`, …, `R (k - 1)` in sequence. Stage `i` has its own rounds `s i` and
reduces statements of type `S i` with witnesses `W i` to those of stage `i + 1`. -/
def Reduction.iterate {s : ℕ → Spec} {S W : ℕ → Type}
    (R : (i : ℕ) → Reduction oP oV (s i) (S i) (W i) (S (i + 1)) (W (i + 1))) :
    (k : ℕ) → Reduction oP oV (iterSpec s k) (S 0) (W 0) (S k) (W k)
  | 0 => Reduction.id
  | k + 1 => (Reduction.iterate R k).append (R k)

/-- Concatenate per-round errors of the stages. -/
def PerChallenge.iterate {s : ℕ → Spec} (ε : (i : ℕ) → PerChallenge (fun _ => ℝ≥0∞) (s i)) :
    (k : ℕ) → PerChallenge (fun _ => ℝ≥0∞) (iterSpec s k)
  | 0 => ()
  | k + 1 => PerChallenge.append (iterSpec s k) (s k) (PerChallenge.iterate ε k) (ε k)

section Identity

variable {T U : Type}

/-- The reduction without rounds is perfectly complete. -/
theorem Reduction.id_complete (rel : T → U → Prop) :
    (Reduction.id (oP := OracleSpec.empty) (oV := OracleSpec.empty)).Complete World.plain rel rel
      0 := by
  intro x w hxw
  rw [Reduction.run, World.plain_eval_execute, PMF.toOuterMeasure_map_apply]
  simp only [Reduction.id, runStrategy, bind_pure_comp, map_pure, plainLaw_pure,
    Verifier.outputOn, OracleComp.interpret_pure, not_and, Set.preimage_ofPred_eq,
    PMF.toOuterMeasure_pure_apply, Set.mem_ofPred_eq, hxw, not_true_eq_false, imp_false,
    nonpos_iff_eq_zero, ite_eq_right_iff, one_ne_zero, not_not]
  rfl

/-- The reduction without rounds is round-by-round sound without error. -/
theorem Reduction.id_rbrSound (L : Set T) :
    (Reduction.id (oP := OracleSpec.empty) (oV := OracleSpec.empty) (W := U)).verifier.RbrSound
      L L () := by
  refine ⟨fun x _ => x ∈ L, fun x hx => hx, fun x hS ⟨x', hx', hout⟩ => hS ?_⟩
  have : x = x' := Option.some.inj hout
  exact this ▸ hx'

end Identity

section Plain

variable {s : ℕ → Spec} {S W : ℕ → Type}
  {R : (i : ℕ) →
    Reduction OracleSpec.empty OracleSpec.empty (s i) (S i) (W i) (S (i + 1)) (W (i + 1))}

/-- **Iterated completeness**: if every stage `R i` with `i < k` is complete from `rel i` to
`rel (i + 1)` with error `ε i`, the first `k` stages are complete from `rel 0` to `rel k` with
the sum of the errors. -/
theorem Reduction.Complete.iterate {rel : (i : ℕ) → S i → W i → Prop} {ε : ℕ → ℝ≥0∞} (k : ℕ)
    (h : ∀ i < k, (R i).Complete World.plain (rel i) (rel (i + 1)) (ε i)) :
    (Reduction.iterate R k).Complete World.plain (rel 0) (rel k) (∑ i ∈ Finset.range k, ε i) := by
  induction k with
  | zero =>
    rw [Finset.sum_range_zero]
    exact Reduction.id_complete (rel 0)
  | succ k ih =>
    rw [Finset.sum_range_succ]
    exact (ih fun i hi => h i (by omega)).append (h k (by omega))

/-- **Iterated round-by-round soundness**, with the per-round errors of the stages in order. -/
theorem Verifier.RbrSound.iterate {L : (i : ℕ) → Set (S i)}
    {ε : (i : ℕ) → PerChallenge (fun _ => ℝ≥0∞) (s i)} (k : ℕ)
    (h : ∀ i < k, (R i).verifier.RbrSound (L i) (L (i + 1)) (ε i)) :
    (Reduction.iterate R k).verifier.RbrSound (L 0) (L k) (PerChallenge.iterate ε k) := by
  induction k with
  | zero => exact Reduction.id_rbrSound (L 0)
  | succ k ih => exact (ih fun i hi => h i (by omega)).append (h k (by omega))

/-- The total error of the stages' concatenated per-round errors. -/
theorem PerChallenge.sum_iterate (ε : (i : ℕ) → PerChallenge (fun _ => ℝ≥0∞) (s i)) (k : ℕ) :
    PerChallenge.sum (iterSpec s k) (PerChallenge.iterate ε k) =
      ∑ i ∈ Finset.range k, PerChallenge.sum (s i) (ε i) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih]
    exact PerChallenge.sum_append _ _

end Plain

end Cslib.Interactive
