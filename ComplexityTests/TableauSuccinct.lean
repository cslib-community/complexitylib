/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.Tableau.Succinct

/-!
# The tableau formula on bit-field labels

Both sides of `Tableau.satisfiable_succinctCNF_iff` occur. A machine that writes `true` in its
first step gives a satisfiable formula for one step on one input, whatever the input is fixed to.
A machine that never writes gives an unsatisfiable one. The size results apply to any machine.
-/

namespace ComplexityTests.TableauSuccinct

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Logic.PL Turing Turing.MultiTapeTM

/-- Write `true` in the first step, then run forever without writing. -/
private def emitLoop : MultiTapeTM 0 Bool Bool :=
  MultiTapeTM.ofTr false fun q _ _ =>
    { inputTape := 0, workTapes := Fin.elim0, output := if q then none else some true,
      state := some true }

private theorem output_emitLoop (y : List Bool) :
    (emitLoop.runFrom (emitLoop.initCfg y) 1).output = [true] := by
  change (emitLoop.step (emitLoop.initCfg y)).output = _
  rw [MultiTapeTM.step_of_state (q := false) rfl]
  simp [emitLoop, Action.apply]

-- One step on one input fixed to `b`: the machine has written `[true]`.
example (b : Bool) : (Tableau.succinctCNF emitLoop [b] 1 1).Satisfiable :=
  (Tableau.satisfiable_succinctCNF_iff emitLoop (by norm_num) (by simp)).2
    ⟨[b], rfl, List.prefix_refl _, by rw [output_emitLoop]; rfl⟩

/-- Never write. -/
private def silent : MultiTapeTM 0 Bool Bool :=
  MultiTapeTM.ofTr false fun _ _ _ =>
    { inputTape := 0, workTapes := Fin.elim0, output := none, state := some false }

-- The silent machine has written nothing after one step, so no input is accepted.
example : ¬ (Tableau.succinctCNF silent [] 1 1).Satisfiable := by
  rw [Tableau.satisfiable_succinctCNF_iff silent (by norm_num) (by simp)]
  rintro ⟨y, -, -, h⟩
  have hout : (silent.runFrom (silent.initCfg y) 1).output = [] := by
    change (silent.step (silent.initCfg y)).output = _
    rw [MultiTapeTM.step_of_state (q := false) rfl]
    simp [silent, Action.apply]
  rw [hout] at h
  exact absurd h (by decide)

variable {k : ℕ} {State : Type} [Fintype State] [DecidableEq State]
  (tm : MultiTapeTM k Bool State)

-- The formula has `2 ^ clauseBits` clauses of three literals, on labels of `labelBits` bits.
example (x : List Bool) (n T : ℕ) (hn : n < 2 * T) (hx : x.length ≤ n) :
    (Tableau.succinctCNF tm x n T).length = 2 ^ Tableau.clauseBits k State T ∧
      (∀ C ∈ Tableau.succinctCNF tm x n T, C.length = 3) ∧
      ∀ v ∈ (Tableau.succinctCNF tm x n T).vars, v < 2 ^ Tableau.labelBits k State T :=
  ⟨Tableau.length_succinctCNF tm x n T, fun _ hC => Tableau.length_of_mem_succinctCNF tm hC,
    fun _ hv => Tableau.lt_two_pow_labelBits_of_mem_vars tm hn hx hv⟩

-- The clause numbered `j + 4 * (2 + 4 * payload)` is clause `j` of the position in the payload.
example (x : List Bool) (n T t c : ℕ) (l : Tableau.Loc k State) (j : Fin 3) (ht : t ≤ T)
    (hl : l.ColOK T c) :
    Tableau.clauseAt tm x n T (j + 4 * (2 + 4 *
        (l.slot + 2 ^ Tableau.slotBits k State * (c + 2 ^ Tableau.colBits T * t)))) =
      Tableau.posClause tm n T t c l j := by
  rw [Tableau.clauseAt_fields tm x n T _ (by omega) (by omega), Tableau.clauseOf_pos tm x j ht hl]

end ComplexityTests.TableauSuccinct
