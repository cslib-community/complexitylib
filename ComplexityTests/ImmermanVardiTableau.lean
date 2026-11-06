import Complexity.Computability.Complexity.ImmermanVardi.Tableau.Acceptance
import Complexity.Tactic.FOOperator

/-! Behavioral regression clients for native positive tableaux and uniform LFP synthesis. -/

open FirstOrder Language Turing Turing.MultiTapeTM
open Cslib.Logic.FO Cslib.Complexity.ImmermanVardi.Tableau

local instance {M : Type} : Language.empty.Structure M := Language.emptyStructure

private def answer (b : Bool) : MultiTapeTM 0 Bool Unit :=
  ofTr () fun _ _ _ => ⟨0, Fin.elim0, some b, none⟩

private theorem answer_one (b : Bool) (input : List Bool) :
    ((answer b).runFrom ((answer b).initCfg input) 1).Halted ∧
      ((answer b).runFrom ((answer b).initCfg input) 1).output = [b] := by
  rw [runFrom_one, step_of_state (q := ()) rfl]
  simp [answer, tr_ofTr, Cfg.Halted, Action.apply_state, Action.apply_output]

-- The positive tableau records the actual output of a native machine, for either answer.
example (b : Bool) :
    traceRow (m := 0) (State := Unit) (traceStep (B := 8) (answer b) []).lfp
      1 (.out (.one true)) 0 ↔ b = true := by
  rw [traceRow_lfp (answer b) [] (by decide) (by decide)]
  change OutView.ofList ((answer b).runFrom ((answer b).initCfg []) 1).output = .one true ↔ _
  rw [(answer_one b []).2]
  simp [OutView.ofList]

-- Initial configurations are not confused with the halted configurations reached one step later.
example (b : Bool) :
    ¬ traceRow (m := 0) (State := Unit) (traceStep (B := 8) (answer b) []).lfp
      0 (.state none) 0 := by
  rw [traceRow_lfp (answer b) [] (by decide) (by decide)]
  simp [row, Tag.feature, Feature.Holds, runFrom]

-- The two signed representations of zero are the same cell, not an "elsewhere" witness.
example : ¬ elsewhere (B := 3) (State := Unit)
    (fun q b => q = Tag.head (m := 1) 0 false ∧ b = 0) 0 true 0 := by
  simp [elsewhere]

private def emptyInputFormula : Option Bool →
    (Ordered.language Language.empty).Formula (Fin 1)
  | none => ⊤
  | some _ => ⊥

private abbrev LargeSize := {n : ℕ // 8 ≤ n}

local instance (i : LargeSize) : Fact (2 ≤ i.val) := ⟨by have := i.property; omega⟩

-- A single checked sentence works simultaneously in every sufficiently large domain.
example (b : Bool) :
    ∃ φ : LFP.Formula (Ordered.language Language.empty) [] Empty,
      ∀ i : LargeSize, φ.Realize (M := Fin i.val) Operator.RelEnv.empty
        (fun e => nomatch e) ↔ b = true := by
  obtain ⟨φ, hφ⟩ := exists_acceptance_sentence (size := fun i : LargeSize => i.val)
    (answer b) (fun _ => []) emptyInputFormula
    (by intro i s a; cases s <;> simp [emptyInputFormula, inputAt])
    (by intro i; have := i.property; simp only [List.length_nil]; omega)
    (by intro i; exact (by decide : Fintype.card (Tag 0 Unit) ≤ 8).trans i.property)
  refine ⟨φ, fun i => (hφ i).trans ?_⟩
  have hrun := runFrom_eq_of_halt (answer b) ((answer b).initCfg [])
    (show 1 ≤ i.val - 1 by have := i.property; omega) (answer_one b []).1
  rw [hrun]
  rw [(answer_one b []).2]
  simp only [List.cons.injEq, and_true]
  exact ⟨And.right, fun hb => ⟨(answer_one b []).1, hb⟩⟩

-- Finite transition-table choices synthesize without enumerating a model's domain.
example : Operator.PolarityDefinable (L := Language.empty) LFP.policy
    (Γ := []) (fun r => nomatch r) true (fun i : LargeSize => Fin i.val)
    (fun _ => LFP.interpretation) (fun _ => Operator.RelEnv.empty)
    (fun _ (v : Bool → _) => ∃ q : Fin 3, q = 1 ∧ v false = v true) := by
  fo_definable
