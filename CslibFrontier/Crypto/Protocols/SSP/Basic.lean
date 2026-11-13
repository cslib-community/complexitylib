/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game.Experiment
public import CslibFrontier.Crypto.Game.Hybrid
public import CslibFrontier.Crypto.Protocols.UC.Linking
public import CslibFrontier.Languages.Probabilistic.Vector
import CslibFrontier.Languages.Probabilistic.Simulation

/-!
# State-separating proofs: parallel sessions and distinguishing advantage

State-separating proofs organize a game-based security argument as an algebra of *packages*:
stateful programs with an exported and an imported interface, which are composed sequentially and
placed side by side. Here a package is an interactive machine `Cslib.Crypto.Protocols.UC.Machine`:
sequential composition is `Machine.comp`, and its linking laws (`Machine.link_comp`,
`Machine.run_comp`) are the associativity laws of the package algebra. This file adds

* `parFin M`, the `m` packages `M j` run side by side as independent sessions, each on its own
  state, with the queries of the exported interface tagged by their session (`sessionSpec m E`);
* `par M₁ M₂`, two packages run side by side behind the sum of their interfaces;
* `advantage A M₀ M₁`, the advantage of the adversary `A` in distinguishing two closed packages,
  with the reduction law `advantage_comp` and the hybrid bound `advantage_le_sum_range`;
* `eval_run_eq_of_represent`, the state-simulation principle: two closed packages give every
  adversary the same output distribution when each state of the first is represented by a state of
  the second, compatibly with initialization and with every activation.

## Main definitions

* `Cslib.Crypto.Protocols.SSP.sessionSpec`: the interface of `m` tagged sessions.
* `Cslib.Crypto.Protocols.SSP.parFin`: `m` packages run side by side.
* `Cslib.Crypto.Protocols.SSP.par`: two packages run side by side.
* `Cslib.Crypto.Protocols.SSP.advantage`: the distinguishing advantage between closed packages.

## Main results

* `Cslib.Crypto.Protocols.SSP.advantage_comp`: a reduction package moves into the adversary.
* `Cslib.Crypto.Protocols.SSP.advantage_le_sum_range`: the hybrid bound along a sequence of
  closed packages.
* `Cslib.Crypto.Protocols.SSP.eval_run_eq_of_represent`: state simulation between closed packages.

## References

* [C. Brzuska, A. Delignat-Lavaud, C. Fournet, K. Kohbrok, M. Kohlweiss, *State Separation for
  Code-Based Game-Playing Proofs*][BrzuskaDFKK2018]
-/

public section

namespace Cslib.Crypto.Protocols.SSP

open UC
open OracleComp (sumHandler)
open scoped NNReal

variable {ιI ιJ ιE ιE₁ ιE₂ : Type} {I : ιI → Type} {J : ιJ → Type} {E : ιE → Type}
  {E₁ : ιE₁ → Type} {E₂ : ιE₂ → Type} {α : Type}

/-! ### Packages side by side -/

/-- The interface of `m` sessions of the interface `E`: a query is a session index together with a
query of `E`, and it is answered as in `E`. -/
abbrev sessionSpec (m : ℕ) (E : ιE → Type) : Fin m × ιE → Type := fun q => E q.2

/-- The packages `M j` run side by side as `m` independent sessions: the state is the tuple of the
session states, initialized session by session, and the query `(j, q)` runs the activation of the
`j`-th package on its own state, leaving the other sessions untouched. -/
@[expose] def parFin {m : ℕ} (M : Fin m → Machine I E) : Machine I (sessionSpec m E) where
  State := (j : Fin m) → (M j).State
  init := OracleComp.pi fun j => (M j).init
  handle q s := (fun x => (x.1, Function.update s q.1 x.2)) <$> ((M q.1).handle q.2).run (s q.1)

/-- On the session `j`, `parFin M` runs an activation of `M j` on the state of that session. -/
theorem parFin_handle {m : ℕ} (M : Fin m → Machine I E) (j : Fin m) (e : ιE)
    (s : (parFin M).State) :
    ((parFin M).handle (j, e)).run s =
      (fun x => ((x.1, Function.update s j x.2) : sessionSpec m E (j, e) × (parFin M).State)) <$>
        ((M j).handle e).run (s j) :=
  rfl

/-- Two packages importing the same interface, run side by side behind the sum of their exported
interfaces: each query is answered by the corresponding package, on its own state. -/
@[expose] def par (M₁ : Machine I E₁) (M₂ : Machine I E₂) : Machine I (E₁ ⊕ₒ E₂) where
  State := M₁.State × M₂.State
  init := do
    let s₁ ← M₁.init
    let s₂ ← M₂.init
    return (s₁, s₂)
  handle
    | .inl q, s => (fun x => (x.1, (x.2, s.2))) <$> (M₁.handle q).run s.1
    | .inr q, s => (fun x => (x.1, (s.1, x.2))) <$> (M₂.handle q).run s.2

/-- On the left interface, `par M₁ M₂` runs an activation of `M₁` on its own state. -/
theorem par_handle_inl (M₁ : Machine I E₁) (M₂ : Machine I E₂) (q : ιE₁)
    (s : (par M₁ M₂).State) :
    ((par M₁ M₂).handle (.inl q)).run s =
      (fun x => ((x.1, (x.2, s.2)) : (E₁ ⊕ₒ E₂) (.inl q) × (par M₁ M₂).State)) <$>
        (M₁.handle q).run s.1 :=
  rfl

/-- On the right interface, `par M₁ M₂` runs an activation of `M₂` on its own state. -/
theorem par_handle_inr (M₁ : Machine I E₁) (M₂ : Machine I E₂) (q : ιE₂)
    (s : (par M₁ M₂).State) :
    ((par M₁ M₂).handle (.inr q)).run s =
      (fun x => ((x.1, (s.1, x.2)) : (E₁ ⊕ₒ E₂) (.inr q) × (par M₁ M₂).State)) <$>
        (M₂.handle q).run s.2 :=
  rfl

/-! ### Distinguishing advantage -/

section Advantage

/-- The advantage of the adversary `A` in distinguishing the closed packages `M₀` and `M₁`: the
advantage between the experiments of running `A` against each of them. -/
@[expose] noncomputable def advantage (A : ProbOracleComp E Bool)
    (M₀ M₁ : Machine OracleSpec.empty E) : ℝ≥0 :=
  Experiment.advantage (M₀.run A) (M₁.run A)

@[simp] theorem advantage_self (A : ProbOracleComp E Bool) (M : Machine OracleSpec.empty E) :
    advantage A M M = 0 :=
  Game.advantage_self _

theorem advantage_comm (A : ProbOracleComp E Bool) (M₀ M₁ : Machine OracleSpec.empty E) :
    advantage A M₀ M₁ = advantage A M₁ M₀ :=
  Game.advantage_comm _ _

theorem advantage_le_one (A : ProbOracleComp E Bool) (M₀ M₁ : Machine OracleSpec.empty E) :
    advantage A M₀ M₁ ≤ 1 :=
  Game.advantage_le_one _ _

theorem advantage_triangle (A : ProbOracleComp E Bool) (M₀ M₁ M₂ : Machine OracleSpec.empty E) :
    advantage A M₀ M₂ ≤ advantage A M₀ M₁ + advantage A M₁ M₂ :=
  Game.advantage_triangle _ _ _

/-- The advantage depends on the two packages only through the output distributions that they give
the adversary. -/
theorem advantage_congr {A : ProbOracleComp E Bool} {M₀ M₀' M₁ M₁' : Machine OracleSpec.empty E}
    (h₀ : (M₀.run A).eval = (M₀'.run A).eval) (h₁ : (M₁.run A).eval = (M₁'.run A).eval) :
    advantage A M₀ M₁ = advantage A M₀' M₁' := by
  simp only [advantage, Experiment.advantage, h₀, h₁]

/-- **Reduction.** Distinguishing `R.comp M₀` from `R.comp M₁` is distinguishing `M₀` from `M₁`
by the adversary `R.link A`, which runs `A` against the reduction package `R`. -/
theorem advantage_comp (A : ProbOracleComp E Bool) (R : Machine J E)
    (M₀ M₁ : Machine OracleSpec.empty J) :
    advantage A (R.comp M₀) (R.comp M₁) = advantage (R.link A) M₀ M₁ := by
  simp only [advantage, Machine.run_comp]

/-- **Hybrid argument.** The advantage between the first and the last of a sequence of closed
packages is at most the sum of the advantages between consecutive ones. -/
theorem advantage_le_sum_range (A : ProbOracleComp E Bool) (H : ℕ → Machine OracleSpec.empty E)
    (n : ℕ) :
    advantage A (H 0) (H n) ≤ ∑ i ∈ Finset.range n, advantage A (H i) (H (i + 1)) :=
  Game.advantage_hybrid_le_sum (fun i => ((H i).run A).eval) n

end Advantage

/-! ### State simulation -/

section Simulation

/-- Closing a program interprets it, so closing is a monad morphism. -/
private theorem isMonadHom_closeProgram :
    IsMonadHom (ProbOracleComp OracleSpec.empty) ProbComp @Machine.closeProgram :=
  PFunctor.FreeM.isMonadHom_liftM (P := ⟨ℕ ⊕ Empty, probOracleSpec OracleSpec.empty⟩)
    (sumHandler ProbComp.unifFin fun q => q.elim)

/-- The output distribution of a program run against a closed package: sample the initial state,
then interpret the program with each activation read as a distribution. -/
private theorem eval_run (N : Machine OracleSpec.empty E) (program : ProbOracleComp E α) :
    (N.run program).eval = N.init.eval.bind fun s =>
      ((OracleComp.interpret (m := StateT N.State PMF)
        (fun q state => (Machine.closeProgram (N.handler q state)).eval) program).run s).map
          Prod.fst := by
  simp only [Machine.run, Machine.link, Machine.closeProgram_bind, Machine.closeProgram_sample,
    Machine.closeProgram_map, ProbComp.eval_bind, ProbComp.eval_map, Machine.runFrom]
  refine congrArg N.init.eval.bind (funext fun s => ?_)
  rw [OracleComp.map_run_interpret isMonadHom_closeProgram,
    OracleComp.map_run_interpret ProbComp.isMonadHom_eval]

/-- **State simulation.** Let every state of the closed package `M` be represented by a state of
the closed package `M'`, so that the initial distribution of `M` maps to that of `M'`, and every
activation of `M` maps to the activation of `M'` from the represented state. Then every program has
the same output distribution against `M` and against `M'`. -/
theorem eval_run_eq_of_represent (M M' : Machine OracleSpec.empty E)
    (represent : M.State → M'.State) (init : M.init.eval.map represent = M'.init.eval)
    (step : ∀ q s, (Machine.closeProgram ((M.handle q).run s)).eval.map
        (fun (a, s') => (a, represent s')) =
      (Machine.closeProgram ((M'.handle q).run (represent s))).eval)
    (program : ProbOracleComp E α) : (M.run program).eval = (M'.run program).eval := by
  have hstep : ∀ q s, (Machine.closeProgram (M.handler q s)).eval.map
      (fun (a, s') => (a, represent s')) =
        (Machine.closeProgram (M'.handler q (represent s))).eval := by
    rintro (n | q) s
    · simp only [Machine.handler, StateT.lift,
        Machine.closeProgram_bind, Machine.closeProgram_sample, Machine.closeProgram_pure,
        ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_bind, PMF.pure_map]
    · exact step q s
  rw [eval_run M, eval_run M', ← init, PMF.bind_map]
  refine congrArg M.init.eval.bind (funext fun s => ?_)
  simp only [Function.comp_apply]
  rw [← OracleComp.run_interpret_map_state
    (fun q state => (Machine.closeProgram (M.handler q state)).eval)
    (fun q state => (Machine.closeProgram (M'.handler q state)).eval) represent hstep,
    PMF.map_comp]
  exact congrArg (PMF.map · _) (funext fun ⟨_, _⟩ => rfl)

end Simulation

end Cslib.Crypto.Protocols.SSP
