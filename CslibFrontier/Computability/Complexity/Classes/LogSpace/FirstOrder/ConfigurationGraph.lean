/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Registers
public import CslibFrontier.Logics.FirstOrder.Ordered.Division

/-!
# First-order configuration graphs

A configuration of a nondeterministic machine with `k` binary work tapes is a fixed tuple of
registers (`Turing.MultiTapeNTM.ConfigurationGraph.Register k`): the input head position, the
control tag, the output tag and, for each work tape, the head symbol and the ternary codes of the
two stacks beside it. This file defines that graph by first-order formulas over the canonical
numeric vocabulary (order, BIT, zero, one and maximum, with exact addition) on a universe
`Fin N`: one universe element per register.

The input is read through two caller-supplied formulas: `inputFormula s` holds of a position
exactly when the input symbol there is `s` (including both endmarkers), and `lengthFormula`
holds exactly of the input length. Every formula has its exact semantics on every universe
`Fin N` with `w.length < N`. A step whose successor registers would exceed the universe is not
defined: no universe element denotes the successor, which is exactly the behaviour of
`RegisterStep` restricted to tuples of `Fin N`.

## Main definitions

* `Cslib.Complexity.ConfigurationGraph.stepFormula`: one step on register tuples.
* `Cslib.Complexity.ConfigurationGraph.startFormula`: the start registers.
* `Cslib.Complexity.ConfigurationGraph.acceptFormula`: halted registers with output tag `1`.

## Main results

* `Cslib.Complexity.ConfigurationGraph.realize_stepFormula`: the step formula defines
  `RegisterStep` exactly.
* `Cslib.Complexity.ConfigurationGraph.realize_startFormula`,
  `Cslib.Complexity.ConfigurationGraph.realize_acceptFormula`: start and acceptance.

## References

* [N. Immerman, *Languages That Capture Complexity Classes*][Immerman1987], proof of Theorem 3.1:
  an instantaneous description of a logarithmic-space machine is coded by a fixed tuple of
  variables, and its successor relation is first-order. Here each register is one universe element
  and the arithmetic is the exact addition of the canonical numeric vocabulary; the formulas are
  original.
* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.4][Sipser2013]
-/

public section

open FirstOrder Language Turing Cslib.Turing Cslib.Logic.FO.Ordered
open Turing.MultiTapeNTM.ConfigurationGraph

namespace Cslib.Complexity.ConfigurationGraph

variable {L : Language} {α : Type*} {k : ℕ} {State : Type} [Fintype State]

section Formulas

variable (L)

/-- The input head position after a move by `d` from `x`, clamped to the endmarkers `0` and
`n + 1`, where `lengthFormula` holds exactly of the input length `n`. -/
noncomputable def inputMoveFormula (lengthFormula : (language L).Formula (Fin 1))
    (d : SignType) (x y : (language L).Term α) : (language L).Formula α :=
  match d with
  | .neg => (x.equal (zero L) ⊓ y.equal (zero L)) ⊔ addEq L y (one L) x
  | .zero => y.equal x
  | .pos => Formula.iExs Unit
      (lengthFormula.relabel (fun _ => .inr ()) ⊓
        ((le L (.var (.inr ())) (x.relabel Sum.inl) ⊓
            addEq L (.var (.inr ())) (one L) (y.relabel Sum.inl)) ⊔
          (∼(le L (.var (.inr ())) (x.relabel Sum.inl)) ⊓
            addEq L (x.relabel Sum.inl) (one L) (y.relabel Sum.inl))))

/-- The head symbol after an optional write: unchanged by `none`, the written symbol's code
otherwise. -/
noncomputable def writeFormula (o : Option (Option Bool)) (h h' : (language L).Term α) :
    (language L).Formula α :=
  match o with
  | none => h'.equal h
  | some b => natEq L (symbolCode b) h'

/-- The three registers of one work tape after the action `a`: head `h`, left stack `l` and right
stack `r` become `h'`, `l'` and `r'`. The written head symbol is bound to a fresh variable. -/
noncomputable def tapeFormula (a : Option (Option Bool) × SignType)
    (h l r h' l' r' : (language L).Term α) : (language L).Formula α :=
  Formula.iExs Unit (writeFormula L a.1 (h.relabel Sum.inl) (.var (.inr ())) ⊓
    match a.2 with
    | .neg => modNatEq L 3 (l.relabel Sum.inl) (h'.relabel Sum.inl) ⊓
        divNatEq L 3 (l.relabel Sum.inl) (l'.relabel Sum.inl) ⊓
        scaleAddEq L 3 (r.relabel Sum.inl) (.var (.inr ())) (r'.relabel Sum.inl)
    | .zero => (h'.relabel Sum.inl).equal (.var (.inr ())) ⊓
        (l'.relabel Sum.inl).equal (l.relabel Sum.inl) ⊓
        (r'.relabel Sum.inl).equal (r.relabel Sum.inl)
    | .pos => modNatEq L 3 (r.relabel Sum.inl) (h'.relabel Sum.inl) ⊓
        scaleAddEq L 3 (l.relabel Sum.inl) (.var (.inr ())) (l'.relabel Sum.inl) ⊓
        divNatEq L 3 (r.relabel Sum.inl) (r'.relabel Sum.inl))

/-- The output tag after an optional emission (`outputStep`). -/
noncomputable def outputFormula (b : Option Bool) (o o' : (language L).Term α) :
    (language L).Formula α :=
  match b with
  | none => o'.equal o
  | some b => (o.equal (zero L) ⊓ natEq L (if b then 1 else 2) o') ⊔
      (∼(o.equal (zero L)) ⊓ natEq L 2 o')

/-- The registers `Y` are the successor registers `nextRegisters` of `X` under the action `a`. -/
noncomputable def nextFormula (lengthFormula : (language L).Formula (Fin 1))
    (a : Action k Bool State) (X Y : Register k → (language L).Term α) :
    (language L).Formula α :=
  inputMoveFormula L lengthFormula a.inputTape (X .inputPos) (Y .inputPos) ⊓
    natEq L (stateCode a.state) (Y .control) ⊓
    outputFormula L a.output (X .output) (Y .output) ⊓
    Formula.iInf fun i : Fin k => tapeFormula L (a.workTapes i)
      (X (.head i)) (X (.left i)) (X (.right i)) (Y (.head i)) (Y (.left i)) (Y (.right i))

/-- The registers `X` have the observations of the transition table entry `t`: its control
state, the input symbol under the input head and the work-tape head symbols. -/
noncomputable def matchFormula (inputFormula : Option Bool → (language L).Formula (Fin 1))
    (t : Instruction k State) (X : Register k → (language L).Term α) :
    (language L).Formula α :=
  natEq L (stateCode (some t.1)) (X .control) ⊓
    (inputFormula t.2.1).subst (fun _ => X .inputPos) ⊓
    Formula.iInf fun i : Fin k => natEq L (symbolCode (t.2.2.1 i)) (X (.head i))

/-- **One step of the configuration graph on register tuples**: either `X` is halted and
`Y = X`, or `X` has the observations of some transition table entry and `Y` is its successor. -/
noncomputable def stepFormula (inputFormula : Option Bool → (language L).Formula (Fin 1))
    (lengthFormula : (language L).Formula (Fin 1)) (ntm : MultiTapeNTM k Bool State)
    (X Y : Register k → (language L).Term α) : (language L).Formula α :=
  (natEq L (stateCode (none : Option State)) (X .control) ⊓
      Formula.iInf fun i => (Y i).equal (X i)) ⊔
    Formula.iSup fun j : Fin (instructions ntm).length =>
      matchFormula L inputFormula ((instructions ntm).get j) X ⊓
        nextFormula L lengthFormula ((instructions ntm).get j).2.2.2 X Y

/-- The registers `X` are the start registers of `ntm`. -/
noncomputable def startFormula (ntm : MultiTapeNTM k Bool State)
    (X : Register k → (language L).Term α) : (language L).Formula α :=
  Formula.iInf fun i => natEq L (startRegisters ntm i) (X i)

variable (State) in
/-- The registers `X` are halted with output tag `1`. -/
noncomputable def acceptFormula (X : Register k → (language L).Term α) :
    (language L).Formula α :=
  natEq L (stateCode (none : Option State)) (X .control) ⊓ natEq L 1 (X .output)

end Formulas

variable {N : ℕ} [Fact (2 ≤ N)] [L.Structure (Fin N)]

/-- The input-move formula has the exact semantics of `inputMove`, given a length formula that
holds exactly of the input length `n`. -/
theorem realize_inputMoveFormula {lengthFormula : (language L).Formula (Fin 1)} {n : ℕ}
    (hlen : ∀ a : Fin N, lengthFormula.Realize ![a] ↔ n = a.val) (hn : n < N) (d : SignType)
    (x y : (language L).Term α) (v : α → Fin N) :
    (inputMoveFormula L lengthFormula d x y).Realize v ↔
      (y.realize v).val = inputMove n (x.realize v).val d := by
  have hx := (x.realize v).isLt
  have hy := (y.realize v).isLt
  cases d with
  | neg =>
    simp only [inputMoveFormula, inputMove, Formula.realize_sup, Formula.realize_inf,
      Formula.realize_equal, realize_addEq, realize_one_val, Fin.ext_iff, realize_zero_val]
    omega
  | zero =>
    simp only [inputMoveFormula, inputMove, Formula.realize_equal, Fin.ext_iff]
  | pos =>
    have hl (l : Unit → Fin N) :
        (lengthFormula.relabel fun _ => (Sum.inr () : α ⊕ Unit)).Realize (Sum.elim v l) ↔
          n = (l ()).val := by
      rw [Formula.realize_relabel, ← hlen]
      exact iff_of_eq (congrArg _ (funext fun i => by rw [Fin.fin_one_eq_zero i]; rfl))
    simp only [inputMoveFormula, inputMove, Formula.realize_iExs, Formula.realize_inf,
      Formula.realize_sup, Formula.realize_not, hl, realize_le, realize_addEq, realize_one_val,
      Term.realize_var, Term.realize_relabel, Sum.elim_comp_inl, Sum.elim_inr, Fin.le_def,
      Nat.min_def]
    constructor
    · rintro ⟨l, hl, h⟩
      split_ifs <;> omega
    · intro h
      refine ⟨fun _ => ⟨n, hn⟩, rfl, ?_⟩
      dsimp only
      split_ifs at h <;> omega

/-- The tape formula has the exact semantics of `tapeStep`. -/
theorem realize_tapeFormula (a : Option (Option Bool) × SignType)
    (h l r h' l' r' : (language L).Term α) (v : α → Fin N) :
    (tapeFormula L a h l r h' l' r').Realize v ↔
      tapeStep a ((h.realize v).val, (l.realize v).val, (r.realize v).val) =
        ((h'.realize v).val, (l'.realize v).val, (r'.realize v).val) := by
  obtain ⟨o, d⟩ := a
  have hh := (h.realize v).isLt
  have hh' := (h'.realize v).isLt
  have hl := (l.realize v).isLt
  have hl' := (l'.realize v).isLt
  have hr := (r.realize v).isLt
  have hr' := (r'.realize v).isLt
  -- the written head symbol, as a natural number
  have hwrite (c : Unit → Fin N) : (writeFormula L o (h.relabel Sum.inl) (.var (.inr ()))).Realize
      (Sum.elim v c) ↔ (c ()).val = o.elim (h.realize v).val symbolCode := by
    cases o with
    | none =>
      simp only [writeFormula, Formula.realize_equal, Term.realize_var, Term.realize_relabel,
        Sum.elim_comp_inl, Sum.elim_inr, Fin.ext_iff, Option.elim_none]
    | some b =>
      simp only [writeFormula, realize_natEq, Term.realize_var, Sum.elim_inr, Option.elim_some]
  have h3 : (0 : ℕ) < 3 := by decide
  -- the witness is the written symbol; it fits because some successor register contains it
  cases d <;>
  simp only [tapeFormula, tapeStep, Formula.realize_iExs, Formula.realize_inf, hwrite,
    realize_modNatEq h3, realize_divNatEq h3, realize_scaleAddEq, Formula.realize_equal,
    Term.realize_relabel, Term.realize_var, Sum.elim_comp_inl, Sum.elim_inr, Fin.ext_iff,
    Prod.mk.injEq] <;>
  generalize o.elim (h.realize v).val symbolCode = w <;>
  exact ⟨fun ⟨c, hc, hrest⟩ => by omega,
    fun hs => ⟨fun _ => ⟨w, by omega⟩, rfl, by dsimp only; omega⟩⟩

/-- The output formula has the exact semantics of `outputStep`. -/
theorem realize_outputFormula (b : Option Bool) (o o' : (language L).Term α) (v : α → Fin N) :
    (outputFormula L b o o').Realize v ↔ (o'.realize v).val = outputStep (o.realize v).val b := by
  cases b with
  | none => simp only [outputFormula, outputStep, Formula.realize_equal, Fin.ext_iff]
  | some b =>
    simp only [outputFormula, outputStep, Formula.realize_sup, Formula.realize_inf,
      Formula.realize_not, Formula.realize_equal, realize_natEq, Fin.ext_iff, realize_zero_val]
    split_ifs <;> simp_all

/-- The successor formula has the exact semantics of `nextRegisters`. -/
theorem realize_nextFormula {lengthFormula : (language L).Formula (Fin 1)} {n : ℕ}
    (hlen : ∀ a : Fin N, lengthFormula.Realize ![a] ↔ n = a.val) (hn : n < N)
    (a : Action k Bool State) (X Y : Register k → (language L).Term α) (v : α → Fin N) :
    (nextFormula L lengthFormula a X Y).Realize v ↔
      (fun i => (Y i).realize v |>.val) = nextRegisters n (fun i => (X i).realize v |>.val) a := by
  simp only [nextFormula, Formula.realize_inf, Formula.realize_iInf,
    realize_inputMoveFormula hlen hn, realize_natEq, realize_outputFormula, realize_tapeFormula]
  constructor
  · rintro ⟨⟨⟨hi, hc⟩, ho⟩, ht⟩
    funext r
    cases r with
    | inputPos => exact hi
    | control => exact hc
    | output => exact ho
    | head i => exact (congrArg Prod.fst (ht i)).symm
    | left i => exact (congrArg (fun t => t.2.1) (ht i)).symm
    | right i => exact (congrArg (fun t => t.2.2) (ht i)).symm
  · intro h
    exact ⟨⟨⟨congrFun h .inputPos, congrFun h .control⟩, congrFun h .output⟩, fun i =>
      Prod.ext (congrFun h (.head i)).symm
        (Prod.ext (congrFun h (.left i)).symm (congrFun h (.right i)).symm)⟩

/-- The matching formula has the exact semantics of a transition table lookup. -/
theorem realize_matchFormula {inputFormula : Option Bool → (language L).Formula (Fin 1)}
    {w : List Bool} (hinput : ∀ s (a : Fin N), (inputFormula s).Realize ![a] ↔ inputAt w a.val = s)
    (t : Instruction k State) (X : Register k → (language L).Term α) (v : α → Fin N) :
    (matchFormula L inputFormula t X).Realize v ↔
      ((X .control).realize v).val = stateCode (some t.1) ∧
        inputAt w ((X .inputPos).realize v).val = t.2.1 ∧
        ∀ i, ((X (.head i)).realize v).val = symbolCode (t.2.2.1 i) := by
  have hsubst : Formula.Realize ((inputFormula t.2.1).subst fun _ => X .inputPos) v ↔
      (inputFormula t.2.1).Realize ![(X .inputPos).realize v] := by
    change BoundedFormula.Realize _ _ _ ↔ _
    rw [BoundedFormula.realize_subst]
    exact iff_of_eq (congrArg (fun f => BoundedFormula.Realize _ f default)
      (funext fun i => by rw [Fin.fin_one_eq_zero i]; rfl))
  simp only [matchFormula, Formula.realize_inf, Formula.realize_iInf, realize_natEq, hsubst,
    hinput, and_assoc]

/-- **The step formula defines the configuration graph on register tuples**: on every universe
`Fin N` with `w.length < N`, it holds exactly of `RegisterStep` between the values of its tuples. -/
theorem realize_stepFormula {inputFormula : Option Bool → (language L).Formula (Fin 1)}
    {lengthFormula : (language L).Formula (Fin 1)} {w : List Bool}
    (hinput : ∀ s (a : Fin N), (inputFormula s).Realize ![a] ↔ inputAt w a.val = s)
    (hlen : ∀ a : Fin N, lengthFormula.Realize ![a] ↔ w.length = a.val) (hn : w.length < N)
    (ntm : MultiTapeNTM k Bool State) (X Y : Register k → (language L).Term α)
    (v : α → Fin N) :
    (stepFormula L inputFormula lengthFormula ntm X Y).Realize v ↔
      RegisterStep ntm w (fun i => (X i).realize v |>.val) (fun i => (Y i).realize v |>.val) := by
  simp only [stepFormula, Formula.realize_sup, Formula.realize_inf, Formula.realize_iInf,
    Formula.realize_iSup, Formula.realize_equal, realize_natEq, realize_matchFormula hinput,
    realize_nextFormula hlen hn, RegisterStep]
  refine or_congr ⟨fun ⟨hc, hy⟩ => ⟨hc, funext fun i => congrArg Fin.val (hy i)⟩,
    fun ⟨hc, hy⟩ => ⟨hc, fun i => Fin.ext (congrFun hy i)⟩⟩ ⟨?_, ?_⟩
  · rintro ⟨j, ⟨hc, hs, hh⟩, hY⟩
    exact ⟨_, _, _, _, (mem_instructions ntm _).mp (List.get_mem _ j), hc, hs, hh, hY⟩
  · rintro ⟨q, s, heads, a, ha, hc, hs, hh, hY⟩
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp ((mem_instructions ntm (q, s, heads, a)).mpr ha)
    exact ⟨j, by rw [hj]; exact ⟨⟨hc, hs, hh⟩, hY⟩⟩

/-- The start formula holds exactly of the start registers. -/
theorem realize_startFormula (ntm : MultiTapeNTM k Bool State)
    (X : Register k → (language L).Term α) (v : α → Fin N) :
    (startFormula L ntm X).Realize v ↔ ∀ i, ((X i).realize v).val = startRegisters ntm i := by
  simp only [startFormula, Formula.realize_iInf, realize_natEq]

/-- The acceptance formula holds exactly of halted registers with output tag `1`. -/
theorem realize_acceptFormula (X : Register k → (language L).Term α) (v : α → Fin N) :
    (acceptFormula L State X).Realize v ↔
      ((X .control).realize v).val = stateCode (none : Option State) ∧
        ((X .output).realize v).val = 1 := by
  simp only [acceptFormula, Formula.realize_inf, realize_natEq]

end Cslib.Complexity.ConfigurationGraph
