/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.DeterministicTransitiveClosure.Converse

/-! # L ⊆ FO(DTC) clients -/

@[expose] public section

open FirstOrder Language Turing Cslib.Turing Cslib.Logic Cslib.Logic.FO Cslib.Logic.FO.Ordered
open Cslib.Complexity Cslib.Complexity.ConfigurationGraph Turing.MultiTapeNTM.ConfigurationGraph

namespace Cslib.Tests.DeterministicClosureLConverse

/-! ### The capture theorem -/

/-- Every native `L` query has an FO(DTC) sentence. -/
example {L : Language} [L.IsRelational] (v : Vocabulary L) {K : Ordered.Query L}
    (hK : K.encodedLanguage v ∈ Complexity.L encStructure) : DTCDefinable K :=
  DTCDefinable.of_encodedLanguage_mem_L v hK

/-! ### The step formula of a deterministic machine -/

section Formulas

variable {L : Language} {k : ℕ} {State : Type} [Fintype State] {N : ℕ} [Fact (2 ≤ N)]
  [L.Structure (Fin N)] {inputFormula : Option Bool → (language L).Formula (Fin 1)}
  {lengthFormula : (language L).Formula (Fin 1)} {w : List Bool}
  (hinput : ∀ s (a : Fin N), (inputFormula s).Realize ![a] ↔ inputAt w a.val = s)
  (hlen : ∀ a : Fin N, lengthFormula.Realize ![a] ↔ w.length = a.val) (hn : w.length < N)
include hinput hlen hn

/-- **The step formula of a deterministic machine is functional on `Fin N`**, at every tuple:
reachable or not, canonical or not. -/
example (tm : MultiTapeTM k Bool State) :
    Relator.RightUnique fun x y : Register k → Fin N =>
      (stepFormula L inputFormula lengthFormula tm.toMultiTapeNTM (fun i => .var (Sum.inl i))
        (fun i => .var (Sum.inr i))).Realize (Sum.elim x y) := by
  intro x y z hy hz
  rw [realize_stepFormula hinput hlen hn] at hy hz
  exact rightUnique_registerStep_fin tm.deterministic hy hz

/-- For a deterministic machine, the acceptance sentence means the same under deterministic
closure and under closure. -/
example (tm : MultiTapeTM k Bool State)
    (hfit : ∀ v, Relation.ReflTransGen tm.toMultiTapeNTM.ViewStep
      (tm.toMultiTapeNTM.initView w) v → Fits N (registers v)) :
    (acceptanceSentence L inputFormula lengthFormula tm.toMultiTapeNTM).Realize (M := Fin N)
        DTC.interpretation Operator.RelEnv.empty Empty.elim ↔
      (acceptanceSentence L inputFormula lengthFormula tm.toMultiTapeNTM).Realize (M := Fin N)
        TC.interpretation Operator.RelEnv.empty Empty.elim :=
  (realize_acceptanceSentence_dtc hinput hlen hn tm hfit).trans
    (realize_acceptanceSentence hinput hlen hn _ hfit).symm

/-- A halted register tuple keeps its self-loop in the deterministic reduct of the step formula,
for every machine: halting configurations stay reachable under deterministic closure. -/
example (ntm : MultiTapeNTM k Bool State) (x : Register k → Fin N)
    (hx : (x .control).val = stateCode (none : Option State)) :
    DTC.deterministicReduct (fun x y : Register k → Fin N =>
      (stepFormula L inputFormula lengthFormula ntm (fun i => .var (Sum.inl i))
        (fun i => .var (Sum.inr i))).Realize (Sum.elim x y)) x x := by
  simp only [DTC.deterministicReduct, realize_stepFormula hinput hlen hn]
  refine ⟨.inl ⟨hx, rfl⟩, fun z hz => ?_⟩
  rcases hz with ⟨_, h⟩ | ⟨q, _, _, _, _, hc, _⟩
  · exact funext fun i => Fin.ext (congrFun h i)
  · exact absurd (stateCode_injective (hc.symm.trans hx)) (Option.some_ne_none q)

end Formulas

/-! ### Divergence control: a nondeterministic fork

Deterministic closure and closure differ on the step formula of a nondeterministic machine. The
machine `fork` has no work tapes; in state `false` it may halt or move to state `true`. The
register tuple in state `false` has two step-formula successors on `Fin N`, so it has none in the
deterministic reduct: deterministic closure reaches only the tuple itself, while closure reaches
the continuing successor. -/

section Divergence

/-- From state `false`, halt or move to state `true`; no head moves and no output. -/
def fork : MultiTapeNTM 0 Bool Bool where
  q₀ := false
  Tr q _ _ a := q = false ∧ a.inputTape = 0 ∧ a.output = none ∧
    (a.state = none ∨ a.state = some true)

/-- The `fork` action that halts. -/
def haltAction : Action 0 Bool Bool := ⟨0, Fin.elim0, none, none⟩

/-- The `fork` action that moves to state `true`. -/
def continueAction : Action 0 Bool Bool := ⟨0, Fin.elim0, none, some true⟩

/-- The register tuple of `fork` with the input head on the first cell, no output and
control `q`. -/
noncomputable def forkTuple {N : ℕ} (hN : 3 ≤ N) (q : Option Bool) : Register 0 → Fin N
  | .inputPos => ⟨1, by omega⟩
  | .control => ⟨stateCode q, (Fintype.equivFin (Option Bool) q).isLt.trans_le
      (by simp only [Fintype.card_option, Fintype.card_bool]; omega)⟩
  | .output => ⟨0, by omega⟩
  | .head i => i.elim0
  | .left i => i.elim0
  | .right i => i.elim0

/-- Distinct controls give distinct tuples. -/
theorem forkTuple_injective {N : ℕ} (hN : 3 ≤ N) : Function.Injective (forkTuple hN) :=
  fun _ _ h => by
    have hc := congrArg Fin.val (congrFun h .control)
    exact stateCode_injective hc

variable {L : Language} {N : ℕ} [Fact (2 ≤ N)] [L.Structure (Fin N)]
  {inputFormula : Option Bool → (language L).Formula (Fin 1)}
  {lengthFormula : (language L).Formula (Fin 1)} {w : List Bool}
  (hinput : ∀ s (a : Fin N), (inputFormula s).Realize ![a] ↔ inputAt w a.val = s)
  (hlen : ∀ a : Fin N, lengthFormula.Realize ![a] ↔ w.length = a.val) (hn : w.length < N)

variable (L inputFormula lengthFormula) in
/-- The relation the step formula of `fork` defines on register tuples of `Fin N`. -/
def forkStep (x y : Register 0 → Fin N) : Prop :=
  (stepFormula L inputFormula lengthFormula fork (fun i => .var (Sum.inl i))
    (fun i => .var (Sum.inr i))).Realize (Sum.elim x y)

include hinput hlen hn

/-- The step formula follows a `fork` action from state `false`. -/
theorem forkStep_of_action (hN : 3 ≤ N) {a : Action 0 Bool Bool}
    (ha : fork.Tr false (inputAt w 1) Fin.elim0 a)
    (hy : ∀ i, ((forkTuple hN a.state) i).val =
      nextRegisters w.length (fun i => (forkTuple hN (some false) i).val) a i) :
    forkStep L inputFormula lengthFormula (forkTuple hN (some false)) (forkTuple hN a.state) := by
  rw [forkStep, realize_stepFormula hinput hlen hn]
  exact .inr ⟨false, _, Fin.elim0, a, ha, rfl, rfl, fun i => i.elim0, funext hy⟩

/-- In state `false`, the step formula reaches the halted tuple. -/
theorem forkStep_halt (hN : 3 ≤ N) :
    forkStep L inputFormula lengthFormula (forkTuple hN (some false)) (forkTuple hN none) :=
  forkStep_of_action hinput hlen hn hN (a := haltAction) ⟨rfl, rfl, rfl, .inl rfl⟩ fun i => by
    cases i <;> first | rfl | exact (‹Fin 0›).elim0

/-- In state `false`, the step formula reaches the tuple in state `true`. -/
theorem forkStep_continue (hN : 3 ≤ N) :
    forkStep L inputFormula lengthFormula (forkTuple hN (some false)) (forkTuple hN (some true)) :=
  forkStep_of_action hinput hlen hn hN (a := continueAction) ⟨rfl, rfl, rfl, .inr rfl⟩ fun i => by
    cases i <;> first | rfl | exact (‹Fin 0›).elim0

/-- **The step formula of `fork` is not functional on `Fin N`.** -/
example (hN : 3 ≤ N) : ¬ Relator.RightUnique (forkStep (N := N) L inputFormula lengthFormula) :=
  fun h => absurd (forkTuple_injective hN (h (forkStep_halt hinput hlen hn hN)
    (forkStep_continue hinput hlen hn hN))) (by simp)

/-- **Deterministic closure stays put at the fork**: the tuple in state `false` has no
successor in the deterministic reduct of the step formula. -/
theorem not_deterministicReduct_forkStep (hN : 3 ≤ N) (y : Register 0 → Fin N) :
    ¬ DTC.deterministicReduct (forkStep L inputFormula lengthFormula)
      (forkTuple hN (some false)) y := fun ⟨_, hu⟩ =>
  absurd (forkTuple_injective hN ((hu _ (forkStep_halt hinput hlen hn hN)).trans
    (hu _ (forkStep_continue hinput hlen hn hN)).symm)) (by simp)

/-- **Closure and deterministic closure diverge on `fork`**: closure reaches the tuple in state
`true` from the tuple in state `false`, and deterministic closure does not. -/
example (hN : 3 ≤ N) :
    Relation.ReflTransGen (forkStep L inputFormula lengthFormula)
        (forkTuple hN (some false)) (forkTuple hN (some true)) ∧
      ¬ Relation.ReflTransGen (DTC.deterministicReduct (forkStep L inputFormula lengthFormula))
        (forkTuple hN (some false)) (forkTuple hN (some true)) := by
  refine ⟨.single (forkStep_continue hinput hlen hn hN), fun h => ?_⟩
  rcases Relation.ReflTransGen.cases_head h with h | ⟨y, hy, -⟩
  · exact absurd (forkTuple_injective hN h) (by simp)
  · exact not_deterministicReduct_forkStep hinput hlen hn hN y hy

/-- On ℕ-valued tuples too, `fork` has two register successors in state `false`. -/
example (hN : 3 ≤ N) : ¬ Relator.RightUnique (RegisterStep fork w) := fun h => by
  have hy := (realize_stepFormula hinput hlen hn fork _ _ _).mp (forkStep_halt hinput hlen hn hN)
  have hz := (realize_stepFormula hinput hlen hn fork _ _ _).mp
    (forkStep_continue hinput hlen hn hN)
  exact absurd (forkTuple_injective hN (funext fun i => Fin.ext (congrFun (h hy hz) i)))
    (by simp)

end Divergence

end Cslib.Tests.DeterministicClosureLConverse
