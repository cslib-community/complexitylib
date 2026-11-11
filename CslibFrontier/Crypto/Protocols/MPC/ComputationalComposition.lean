/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.Composition
public import CslibFrontier.Crypto.Protocols.MPC.Advantage
import CslibFrontier.Languages.Probabilistic.Norm

/-!
# Computational composition of semi-honest privacy

`Cslib.Crypto.Protocols.MPC.PerfectSemiHonestPrivate.compose` composes perfectly private protocols.
This module proves the quantitative version for distinguishing advantages: if the outer protocol
`P` is private against the outer distinguisher induced by `D` up to `ε_out`, and every subprotocol
`Sub op` is private against every distinguisher up to `ε_sub`, then `P.compose Sub` is private
against `D` up to `ε_out + sc₁.length * ε_sub`.

The proof is the hybrid argument behind Goldreich's composition theorem. The outer hop compares
the ideal world of `P.compose Sub` with the real execution of `P` in which the coalition's inner
views are simulated by `S₂`; the remaining hops replace the inner simulator by the real
subprotocol one oracle round at a time. Each round of `sc₁` contributes at most `ε_sub`;
message rounds contribute nothing, so the bound is crude when `sc₁` has many message rounds.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.composeDistinguisher`: the outer distinguisher induced by a
  distinguisher for the composed protocol, which expands the coalition's simulated inner views with
  `S₂` before running it.

## Main results

* `Cslib.Crypto.Protocols.MPC.semiHonestAdvantage_compose_le`: the semi-honest advantage of
  `P.compose Sub` against `D` is at most `ε_out + sc₁.length * ε_sub`.

## References

* [O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*][Goldreich2004],
  Section 7.3.1 (Theorem 7.3.3, pp. 637–638) and Section 7.5.2.1 (Theorem 7.5.7, pp. 702–703).
-/

public section

namespace Cslib.Crypto.Protocols.MPC

open Cslib.Probability Cslib.ProbComp
open scoped NNReal
open _root_.Cslib.Crypto.Protocols.MPC.Composition

variable {m : ℕ} {spec₁ spec₂ : MultiOracleSpec}
    {sc₂ : (op : spec₁.Op) → Schedule (spec₁.arity op) spec₂}
    {Coins₂ : (op : spec₁.Op) → Fin (spec₁.arity op) → Type}

/-- Running `steps` in `W` as a closed probabilistic program has law `steps.evalWith W st`. -/
private theorem eval_interpret_run {spec : MultiOracleSpec} {State Out : Fin m → Type}
    {sc : Schedule m spec} (W : MultiOracleWorld spec) (steps : Steps State Out sc)
    (st : (i : Fin m) → State i) :
    ProbComp.eval (OracleComp.interpret
        (OracleComp.sumHandler ProbComp.unifFin
          fun q : (Σ op : spec.Op, (s : Fin (spec.arity op)) → spec.Query op s) => W q.1 q.2)
        (steps.run st)) =
      steps.evalWith W st := by
  rw [ProbOracleComp.eval_interpret]
  rfl

/-- Triangle inequality through the hybrid that keeps the first continuation and the second
mixing distribution. -/
private theorem advantage_bind_bind_le {α : Type*} (μ ν : PMF α) (f g : α → Game) :
    Game.advantage (μ.bind f) (ν.bind g) ≤
      Game.advantage (μ.bind f) (ν.bind f) + Game.advantage (ν.bind f) (ν.bind g) :=
  Game.advantage_triangle _ _ _

/-- Hybrid bound for one execution of `steps`: replacing every subprotocol call of
`Steps.compose Sub steps` in `W₂`, together with the coalition's inner views, by an ideal call
to `W₁` and the inner simulator `S₂` changes the advantage of any distinguisher by at most
`ε_sub` per round of `sc`. -/
private theorem advantage_compose_steps_le {State Out : Fin m → Type} {sc : Schedule m spec₁}
    {W₁ : MultiOracleWorld spec₁} {W₂ : MultiOracleWorld spec₂}
    {Sub : (op : spec₁.Op) →
      Protocol (spec₁.arity op) spec₂ (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op)}
    {S₂ : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      CoalitionSimulator (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op) J}
    {ε_sub : ℝ≥0}
    (hsub : ∀ op J q D, semiHonestAdvantage (Sub op) W₂ (W₁ op) J (S₂ op J) q D ≤ ε_sub)
    (I : Finset (Fin m)) (steps : Steps State Out sc) (st : (i : Fin m) → State i)
    (D : ((i : I) → Schedule.SubCoins Coins₂ sc i.1 ×
        Schedule.Received (Schedule.compose sc₂ sc) i.1) × ((i : Fin m) → Out i) →
      ProbComp Bool) :
    Game.advantage
      (((ProbComp.eval (OracleComp.pi (sampleSubCoins Sub sc))).bind fun c_sub =>
        ((Steps.compose Sub steps).evalWith W₂ (fun i => (st i, c_sub i))).map fun recv₂ =>
          (fun i : I => (c_sub i.1, recv₂ i.1),
            fun i => (Steps.compose Sub steps).outputAt i (st i, c_sub i) (recv₂ i))).bind
        fun r => ProbComp.eval (D r))
      (((steps.evalWith W₁ st).bind fun recv₁ =>
        (ProbComp.eval (expandSimSteps S₂ I steps (I.restrict st) (I.restrict recv₁))).map
          fun sub => (sub, fun i => steps.outputAt i (st i) (recv₁ i))).bind
        fun r => ProbComp.eval (D r)) ≤
      sc.length * ε_sub := by
  induction steps with
  | done output =>
    simp [Steps.compose, expandSimSteps, sampleSubCoins, eval_pi_pure, Steps.outputAt]
  | @message _ _ s₀ r₀ _ _ send next ih =>
    have hih := ih (fun i => (st i, Round.deliverMessage (send (st s₀)) i))
      (fun res => D (fun i : I => ((res.1 i).1,
        (Round.deliverMessage (spec := spec₂) (sender := s₀) (receiver := r₀)
          (send (st s₀)) i.1, (res.1 i).2)), res.2))
    simp only [pmf_norm, Finset.restrict_def] at hih
    simp only [pmf_norm, Steps.compose, expandSimSteps, sampleSubCoins, Steps.evalWith_message,
      Steps.evalWith_mapState, bind_pure_comp, Finset.restrict_def, Steps.outputAt,
      Steps.outputAt_mapState]
    refine hih.trans ?_
    gcongr
    simp
  | @oracle _ _ op parties rest query next ih =>
    rw [sampleSubCoins_bind_evalWith_compose_oracle, evalWith_oracle_bind_expandSimSteps]
    simp only [PMF.bind_bind]
    refine (advantage_bind_bind_le _ _ _ _).trans ?_
    have hlen : ((Round.oracle op parties :: rest).length : ℝ≥0) * ε_sub =
        ε_sub + rest.length * ε_sub := by
      simp [add_mul, add_comm]
    rw [hlen]
    refine add_le_add ?_ (Game.advantage_bind_le_nnreal _ _ _ fun va => ?_)
    · -- The hop at this round is a distinguisher for `Sub op` on the induced sub-coalition.
      rw [Game.advantage_comm]
      refine le_of_eq_of_le ?_
        (hsub op (subCoalition parties I) (fun s => query s (st (parties s))) fun va => do
          let c_sub ← OracleComp.pi (sampleSubCoins Sub rest)
          let recv₂ ← OracleComp.interpret
            (OracleComp.sumHandler ProbComp.unifFin
              fun q : (Σ op : spec₂.Op, (s : Fin (spec₂.arity op)) → spec₂.Query op s) =>
                W₂ q.1 q.2)
            ((Steps.compose Sub next).run
              (fun i => ((st i, Round.deliverOracle parties va.2 i), c_sub i)))
          D (fun i : I =>
              ((pushTupleRestrict parties I (fun s => (va.1 s).coins) i, c_sub i.1),
                Schedule.Received.append
                  (pushScheduleReceivedRestrict parties I (sc₂ op)
                    (fun s => (va.1 s).received) i)
                  (recv₂ i.1)),
            fun i => (Steps.compose Sub next).outputAt i
              ((st i, Round.deliverOracle parties va.2 i), c_sub i) (recv₂ i)))
      simp only [semiHonestAdvantage, pmf_norm, eval_interpret_run]
    · -- The remaining hops are the induction hypothesis on `next`.
      simp only [PMF.bind_map, Function.comp_def]
      exact ih _ _

/-- The outer distinguisher induced by a distinguisher `D` for `P.compose Sub`: from an outer
view of the coalition `I`, expand the simulated inner views of each oracle round with `S₂`, then
run `D` on the resulting composed views. -/
@[expose] def composeDistinguisher {sc₁ : Schedule m spec₁} {In Coins₁ Out : Fin m → Type}
    (P : Protocol m spec₁ sc₁ In Coins₁ Out)
    (S₂ : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      CoalitionSimulator (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op) J)
    (I : Finset (Fin m)) (x : (i : Fin m) → In i)
    (D : ((i : I) → PartyView In (Schedule.ComposedCoins Coins₂ Coins₁ sc₁)
        (Schedule.compose sc₂ sc₁) i) × ((i : Fin m) → Out i) → ProbComp Bool) :
    ((i : I) → PartyView In Coins₁ sc₁ i) × ((i : Fin m) → Out i) → ProbComp Bool :=
  fun r => do
    let sub ← expandSimSteps S₂ I P.steps (fun i => (x i.1, (r.1 i).coins))
      (fun i => (r.1 i).received)
    D (fun i => ⟨x i.1, ((r.1 i).coins, (sub i).1), (sub i).2⟩, r.2)

/-- Computational composition of semi-honest privacy (the hybrid argument behind Goldreich
Theorem 7.5.7, pp. 702–703, and Theorem 7.3.3, pp. 637–638): if `P` is private against the
induced outer distinguisher `composeDistinguisher P S₂ I x D` up to `ε_out`, and every
subprotocol `Sub op` is private against every distinguisher up to `ε_sub`, then `P.compose Sub`
with the composed simulator `composeSim P S₁ S₂ I` is private against `D` up to
`ε_out + sc₁.length * ε_sub`. -/
theorem semiHonestAdvantage_compose_le {sc₁ : Schedule m spec₁} {In Coins₁ Out : Fin m → Type}
    (P : Protocol m spec₁ sc₁ In Coins₁ Out)
    (W₁ : MultiOracleWorld spec₁) (W₂ : MultiOracleWorld spec₂)
    (f : Functionality m In Out)
    (S₁ : (I : Finset (Fin m)) → CoalitionSimulator sc₁ In Coins₁ Out I)
    (Sub : (op : spec₁.Op) →
      Protocol (spec₁.arity op) spec₂ (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op))
    (S₂ : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      CoalitionSimulator (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op) J)
    (I : Finset (Fin m)) (x : (i : Fin m) → In i)
    (D : ((i : I) → PartyView In (Schedule.ComposedCoins Coins₂ Coins₁ sc₁)
        (Schedule.compose sc₂ sc₁) i) × ((i : Fin m) → Out i) → ProbComp Bool)
    (ε_out ε_sub : ℝ≥0)
    (hout : semiHonestAdvantage P W₁ f I (S₁ I) x (composeDistinguisher P S₂ I x D) ≤ ε_out)
    (hsub : ∀ op J q D_sub, semiHonestAdvantage (Sub op) W₂ (W₁ op) J (S₂ op J) q D_sub ≤ ε_sub) :
    semiHonestAdvantage (P.compose Sub) W₂ f I (composeSim P S₁ S₂ I) x D ≤
      ε_out + sc₁.length * ε_sub := by
  have hideal : ProbComp.eval (idealJoint f I (composeSim P S₁ S₂ I) x >>= D) =
      ProbComp.eval (idealJoint f I (S₁ I) x >>= composeDistinguisher P S₂ I x D) := by
    simp only [idealJoint, composeSim, composeDistinguisher, pmf_norm, bind_pure_comp,
      Finset.restrict_def]
  simp only [semiHonestAdvantage] at hout ⊢
  rw [hideal]
  refine (Game.advantage_triangle _
    ((P.realJoint W₁ I x).bind fun r => ProbComp.eval (composeDistinguisher P S₂ I x D r)) _).trans
    (add_le_add hout ?_)
  rw [Game.advantage_comm]
  simp only [pmf_norm, Protocol.realJoint, Protocol.evalWith_eq, Protocol.outputOfView,
    Protocol.compose, eval_pi_pair, Steps.evalWith_mapState, Steps.outputAt_mapState,
    Prod.map_apply, Finset.restrict_def, id_eq, composeDistinguisher]
  refine Game.advantage_bind_le_nnreal _ _ _ fun c₁ => ?_
  have h := advantage_compose_steps_le hsub I P.steps (fun i => (x i, c₁ i))
    (fun res => D (fun i => ⟨x i.1, (c₁ i.1, (res.1 i).1), (res.1 i).2⟩, res.2))
  simp only [pmf_norm, Finset.restrict_def] at h
  exact h

end Cslib.Crypto.Protocols.MPC
