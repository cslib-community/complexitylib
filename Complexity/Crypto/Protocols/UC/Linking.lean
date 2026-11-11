/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Crypto.Protocols.UC.Machine
import Complexity.Languages.Probabilistic.Simulation

/-!
# Laws of linking and composing interactive machines

Running a program against a composed machine `A.comp P` is running it against `A` and running the
result against `P` (`Machine.runFrom_comp`). Since `A.comp P` initializes `P` first, linking is
associative as an equation of programs, without any appeal to probabilities
(`Machine.link_comp`): `(A.comp P).link Z = P.link (A.link Z)`. The forwarding machine is a unit
for linking (`Machine.link_id`). These are the package-algebra laws of state-separating proofs,
which turn reductions into a regrouping of the same program.

Call budgets compose: a machine making at most `u` calls per activation, on top of a machine making
at most `t`, makes at most `u * (t + 1) + t` (`Machine.IsBounded.comp`), and a program making at
most `m` calls, linked against a machine making at most `t` per activation, makes at most
`t + m * (t + 1)` (`Machine.isQueryBounded_link`).

## Main results

* `Cslib.Crypto.Protocols.UC.Machine.runFrom_comp`: running against a composition.
* `Cslib.Crypto.Protocols.UC.Machine.link_comp`, `Cslib.Crypto.Protocols.UC.Machine.run_comp`:
  linking is associative.
* `Cslib.Crypto.Protocols.UC.Machine.runFrom_id`, `Cslib.Crypto.Protocols.UC.Machine.link_id`: the
  forwarding machine is a unit.
* `Cslib.Crypto.Protocols.UC.Machine.IsBounded.comp`,
  `Cslib.Crypto.Protocols.UC.Machine.isQueryBounded_link`: budgets of compositions and links.

## References

* [C. Brzuska, A. Delignat-Lavaud, C. Fournet, K. Kohbrok, M. Kohlweiss, *State Separation for
  Code-Based Game-Playing Proofs*][BrzuskaDFKK2018]: linking and its associativity.
-/

public section

namespace Cslib.Crypto.Protocols.UC.Machine

open OracleComp (sumHandler)

variable {ιI ιJ ιE : Type} {I : ιI → Type} {J : ιJ → Type} {E : ιE → Type} {α : Type}

/-- A single call of the combined interface is answered by the machine's handler. -/
theorem runFrom_call (M : Machine I E) (q : ℕ ⊕ ιE) (s : M.State) :
    M.runFrom (OracleComp.query q) s = (M.handler q).run s :=
  OracleComp.run_interpret_query _ _ _

/-- Running against a composition runs against the outer machine, and runs the result against the
inner machine. -/
theorem runFrom_comp (A : Machine J E) (P : Machine I J) (program : ProbOracleComp E α)
    (sA : A.State) (sP : P.State) :
    (A.comp P).runFrom program (sA, sP) =
      Equiv.prodAssoc _ _ _ <$> P.runFrom (A.runFrom program sA) sP := by
  simp only [runFrom]
  rw [OracleComp.run_interpret_run_interpret, Functor.map_map]
  have hhandler : (fun q (state : A.State × P.State) =>
      (fun x : (probOracleSpec E q × A.State) × P.State => (x.1.1, x.1.2, x.2)) <$>
        (OracleComp.interpret P.handler ((A.handler q).run state.1)).run state.2) =
      (A.comp P).handler := by
    funext q state
    cases q with
    | inl n =>
      change (fun x : (Fin (n + 1) × A.State) × P.State => (x.1.1, x.1.2, x.2)) <$>
          P.runFrom ((StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n))).run state.1)
            state.2 =
        (StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n))).run state
      simp only [StateT.run_lift, bind_pure_comp, runFrom_map, runFrom_sample, Functor.map_map]
      rfl
    | inr e => rfl
  rw [hhandler]
  refine (id_map _).symm.trans ?_
  congr 1

/-- The composition samples the inner machine's state first. -/
theorem comp_init (A : Machine J E) (P : Machine I J) :
    (A.comp P).init = (do
      let sP ← P.init
      let sA ← A.init
      return (sA, sP)) := rfl

/-- Sampling the composition's initial state inside a program samples the inner machine's state,
then the outer one's. -/
theorem sample_comp_init {ιK : Type} {K : ιK → Type} (A : Machine J E) (P : Machine I J) :
    ProbOracleComp.sample (spec := K) (α := A.State × P.State) (A.comp P).init = (do
      let sP ← ProbOracleComp.sample P.init
      let sA ← ProbOracleComp.sample A.init
      return (sA, sP)) := by
  rw [comp_init, ProbOracleComp.sample_bind]
  simp only [ProbOracleComp.sample_bind, ProbOracleComp.sample_pure]

/-- Linking is associative: a program linked against a composition is the program linked against
the outer machine and then against the inner one. -/
theorem link_comp (A : Machine J E) (P : Machine I J) (program : ProbOracleComp E α) :
    (A.comp P).link program = P.link (A.link program) := by
  simp only [link, runFrom_bind, runFrom_sample, bind_map_left, map_bind]
  erw [sample_comp_init, bind_assoc]
  refine congrArg _ (funext fun sP => ?_)
  erw [bind_assoc]
  refine congrArg _ (funext fun sA => ?_)
  erw [pure_bind]
  rw [runFrom_comp]
  change (Prod.fst : α × A.State × P.State → α) <$>
    (Equiv.prodAssoc α A.State P.State <$> P.runFrom (A.runFrom program sA) sP) = _
  rw [Functor.map_map, runFrom_map, Functor.map_map]
  rfl

/-- Running a program against a closed composition is running its link against the inner machine. -/
theorem run_comp (A : Machine J E) (P : Machine OracleSpec.empty J) (program : ProbOracleComp E α) :
    (A.comp P).run program = P.run (A.link program) := by
  rw [run, run, link_comp]

/-- The forwarding machine passes every call through and never changes its state. -/
theorem runFrom_id (program : ProbOracleComp E α) (s : (Machine.id E).State) :
    (Machine.id E).runFrom program s = (fun a => (a, s)) <$> program := by
  have hhandler : (Machine.id E).handler = fun q => StateT.lift (OracleComp.query q) := by
    funext q
    cases q with
    | inl n => simp only [handler, Machine.id, ProbOracleComp.sample, ProbComp.unifFin,
        OracleComp.interpret_query]
    | inr e => rfl
  rw [runFrom, hhandler, OracleComp.run_interpret_lift, OracleComp.interpret_query_eq_self]

/-- Linking against the forwarding machine leaves a program unchanged. -/
@[simp] theorem link_id (program : ProbOracleComp E α) : (Machine.id E).link program = program := by
  simp only [link, runFrom_id, Functor.map_map, id_map']
  exact pure_bind _ _

/-! ### Budgets of compositions and links -/

/-- Embedded sampling makes as many calls as the closed program. -/
theorem isQueryBounded_sample {program : ProbComp α} {n : ℕ} (h : program.IsQueryBounded n) :
    (ProbOracleComp.sample (spec := I) program).IsQueryBounded n :=
  OracleComp.IsCostBounded.interpret (fun _ => OracleComp.IsCostBounded.query _) h

/-- A unit-cost budget `n` gives a budget `n * c` when every call costs `c`. -/
private theorem isCostBounded_const_of_isQueryBounded {ι : Type} {spec : ι → Type} {β : Type}
    {program : OracleComp spec β} {n : ℕ} (c : ℕ) (h : program.IsQueryBounded n) :
    OracleComp.IsCostBounded (fun _ => c) program (n * c) := by
  induction h with
  | pure a n => exact .pure a _
  | liftBind q cont n _ ih =>
    rw [Nat.succ_mul]
    exact .liftBind q cont _ ih

/-- Every call of a program run against `P` costs at most `t + 1` calls of `P`'s imports. -/
private theorem isQueryBounded_handler {P : Machine I J} {t : ℕ} (hP : P.IsBounded t)
    (q : ℕ ⊕ ιJ) (s : P.State) : ((P.handler q).run s).IsQueryBounded (t + 1) := by
  cases q with
  | inl n =>
    change ((StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n))).run s).IsQueryBounded _
    rw [StateT.run_lift, bind_pure_comp]
    exact (OracleComp.isCostBounded_map_iff _ _ _).mpr
      ((isQueryBounded_sample (OracleComp.IsCostBounded.query n)).mono (by omega))
  | inr j => exact (hP.2 j s).mono (Nat.le_succ t)

/-- A program with at most `m` calls, run against a machine with at most `t` calls per activation,
makes at most `m * (t + 1)` calls. -/
theorem isQueryBounded_runFrom {P : Machine I J} {t m : ℕ} (hP : P.IsBounded t)
    {program : ProbOracleComp J α} (h : program.IsQueryBounded m) (s : P.State) :
    (P.runFrom program s).IsQueryBounded (m * (t + 1)) :=
  OracleComp.IsCostBounded.run_interpret (isQueryBounded_handler hP)
    (isCostBounded_const_of_isQueryBounded (t + 1) h) s

/-- A program with at most `m` calls, linked against a machine with at most `t` calls per
activation and at initialization, makes at most `t + m * (t + 1)` calls. -/
theorem isQueryBounded_link {M : Machine I J} {t m : ℕ} (hM : M.IsBounded t)
    {program : ProbOracleComp J α} (h : program.IsQueryBounded m) :
    (M.link program).IsQueryBounded (t + m * (t + 1)) :=
  (isQueryBounded_sample hM.1).bind fun s =>
    (OracleComp.isCostBounded_map_iff _ _ _).mpr (isQueryBounded_runFrom hM h s)

/-- A machine with at most `u` calls per activation on top of a machine with at most `t` makes at
most `u * (t + 1) + t` calls per activation. -/
theorem IsBounded.comp {A : Machine J E} {P : Machine I J} {u t : ℕ} (hA : A.IsBounded u)
    (hP : P.IsBounded t) : (A.comp P).IsBounded (u * (t + 1) + t) := by
  refine ⟨?_, fun q s => ?_⟩
  · refine (hP.1.bind fun _ => hA.1.bind fun _ => .pure _ 0).mono ?_
    rw [Nat.mul_succ]
    omega
  · refine ((OracleComp.isCostBounded_map_iff _ _ _).mpr
      (isQueryBounded_runFrom hP (hA.2 q s.1) s.2)).mono (Nat.le_add_right _ _)

end Cslib.Crypto.Protocols.UC.Machine
