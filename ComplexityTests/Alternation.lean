/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.Alternation.NP
import Complexity.Computability.Complexity.Classes.Alternation.Savitch
import Complexity.Computability.Complexity.Classes.Alternation.TQBF
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Tests: alternating machines and `AP = PSPACE`

A one-state machine that emits its move and halts: existential, it accepts every input, and
universal, it accepts none, so both labels matter; both decide their problems within one step,
which puts `Set.univ` and `∅` in `AP` with explicit machines, and their games of moves are won and
lost. Two game verifiers, one won by the existential player's first move and one lost to the
universal player's, put `Set.univ` and `∅` in `AP` through the guess-then-verify machine.
Single-bit moves on concrete predicates, rounds of quantifiers on a concrete formula, and
Savitch's midpoint game on a two-word graph.
-/

namespace ComplexityTests.Alternation

open Cslib Cslib.Complexity Cslib.Logic.PL Turing
open Turing.MultiTapeTM (encBits PolyBounded)

/-! ### A machine emitting its move -/

/-- The machine with one state that emits its move and halts; its state is universal when `u`
is `true`. -/
private def emitMove (u : Bool) : MultiTapeATM 0 Bool Unit where
  toPTM :=
    { initial := ()
      tr := fun _ _ _ _ b => .step ⟨0, Fin.elim0, some b, none⟩ Empty.elim Empty.elim }
  universal _ := u

/-- The move `b` halts with output `[b]`. -/
private theorem next_emitMove (u b : Bool) (input : List Bool) :
    ((emitMove u).next b ((emitMove u).toPTM.toNTM.initCfg input)).state = none ∧
      ((emitMove u).next b ((emitMove u).toPTM.toNTM.initCfg input)).output = [b] := by
  rw [MultiTapeATM.next_of_state _ (q := ()) rfl]
  exact ⟨rfl, rfl⟩

/-- Every list of one move halts. -/
private theorem runsInTime_emitMove (u : Bool) (input : List Bool) :
    (emitMove u).toPTM.toNTM.RunsInTime input 1 := by
  refine MultiTapeATM.runsInTime_iff_stepCoins.mpr fun coins hlen => ?_
  obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp hlen
  exact (next_emitMove u b input).1

/-- Existential, the machine accepts by the move `true`. -/
example (input : List Bool) : (emitMove false).Accepts input := by
  refine ⟨1, ((emitMove false).acceptsWithin_succ_of_existential (q := ()) rfl rfl).mpr
    ⟨true, ?_⟩⟩
  exact ⟨(next_emitMove false true input).1, (next_emitMove false true input).2⟩

/-- Universal, the machine rejects: the move `false` emits `[false]`. -/
example (input : List Bool) : ¬(emitMove true).Accepts input := by
  rw [MultiTapeATM.accepts_iff_acceptsWithin (runsInTime_emitMove true input),
    (emitMove true).acceptsWithin_succ_of_universal (q := ()) rfl rfl]
  intro h
  have := (h false).2
  rw [(next_emitMove true false input).2] at this
  simp at this

/-- The existential machine decides `Set.univ` within one step. -/
private theorem decidesInTime_univ :
    (emitMove false).DecidesInTime encBits Set.univ fun _ => 1 := fun a =>
  ⟨runsInTime_emitMove false a, iff_of_true trivial
    ⟨1, ((emitMove false).acceptsWithin_succ_of_existential (q := ()) rfl rfl).mpr
      ⟨true, (next_emitMove false true a).1, (next_emitMove false true a).2⟩⟩⟩

/-- The universal machine decides `∅` within one step. -/
private theorem decidesInTime_empty :
    (emitMove true).DecidesInTime encBits ∅ fun _ => 1 := fun a => by
  refine ⟨runsInTime_emitMove true a, iff_of_false (Set.notMem_empty a) ?_⟩
  rw [MultiTapeATM.accepts_iff_acceptsWithin (runsInTime_emitMove true (encBits a)),
    (emitMove true).acceptsWithin_succ_of_universal (q := ()) rfl rfl]
  intro h
  have := (h false).2
  rw [(next_emitMove true false (encBits a)).2] at this
  simp at this

/-- `Set.univ ∈ AP` and `∅ ∈ AP` by explicit machines and time bounds, transferring to `PSPACE`
and game verifiers. -/
example (a : List Bool) (u : Bool) :
    ((Set.univ : Set (List Bool)) ∈ AP encBits ∧ (∅ : Set (List Bool)) ∈ AP encBits) ∧
    ¬(emitMove true).AcceptsWithin 1 ((emitMove true).toPTM.toNTM.initCfg a) ∧
    (Set.univ : Set (List Bool)) ∈ PSPACE encBits ∧
    (∃ (p : Polynomial ℕ) (V : List Bool × List Bool → Bool),
      MultiTapeTM.ComputableInPolyTime V (MultiTapeTM.encPair encBits encBits)
        MultiTapeTM.encBool ∧ IsGameVerifier encBits p V (∅ : Set (List Bool))) ∧
    (emitMove u).HaltsWithin 1 ((emitMove u).toPTM.toNTM.initCfg a) :=
  have huniv : (Set.univ : Set (List Bool)) ∈ AP encBits :=
    ⟨_, PolyBounded.const 1, 0, Unit, inferInstance, emitMove false, decidesInTime_univ⟩
  have hempty : (∅ : Set (List Bool)) ∈ AP encBits :=
    ⟨_, PolyBounded.const 1, 0, Unit, inferInstance, emitMove true, decidesInTime_empty⟩
  ⟨⟨huniv, hempty⟩,
   (decidesInTime_empty.mem_iff a).not.mp (Set.notMem_empty a),
   AP_subset_PSPACE huniv,
   exists_isGameVerifier_of_mem_AP hempty,
   MultiTapeATM.runsInTime_iff_haltsWithin.mp (runsInTime_emitMove u a)⟩

/-- The existential machine wins its game of moves on every input. -/
example (input : List Bool) : Alternation true (List.replicate (2 * 1) 1)
    fun w => (emitMove false).strict.runClosedCoins w input = [true] :=
  (MultiTapeATM.accepts_iff_alternation _ (runsInTime_emitMove false input)).mp
    ⟨1, ((emitMove false).acceptsWithin_succ_of_existential (q := ()) rfl rfl).mpr
      ⟨true, (next_emitMove false true input).1, (next_emitMove false true input).2⟩⟩

/-- The universal machine loses its game of moves on every input. -/
example (input : List Bool) : ¬Alternation true (List.replicate (2 * 1) 1)
    fun w => (emitMove true).strict.runClosedCoins w input = [true] := by
  rw [← MultiTapeATM.accepts_iff_alternation _ (runsInTime_emitMove true input),
    MultiTapeATM.accepts_iff_acceptsWithin (runsInTime_emitMove true input),
    (emitMove true).acceptsWithin_succ_of_universal (q := ()) rfl rfl]
  intro h
  have := (h false).2
  rw [(next_emitMove true false input).2] at this
  simp at this

/-! ### Games won by the first or the second move -/

/-- The game won when the first move is `true`. -/
private def firstMove (x : List Bool × List Bool) : Bool := x.2.getD 0 false

/-- The game won when the second move is `true`. -/
private def secondMove (x : List Bool × List Bool) : Bool := x.2.getD 1 false

private theorem computableInPolyTime_firstMove :
    MultiTapeTM.ComputableInPolyTime firstMove (MultiTapeTM.encPair encBits encBits)
      MultiTapeTM.encBool := by
  unfold firstMove
  fun_prop

private theorem computableInPolyTime_secondMove :
    MultiTapeTM.ComputableInPolyTime secondMove (MultiTapeTM.encPair encBits encBits)
      MultiTapeTM.encBool := by
  unfold secondMove
  fun_prop

/-- The existential player wins the game of one round by moving `true`. -/
private theorem isGameVerifier_firstMove :
    IsGameVerifier encBits 1 firstMove (Set.univ : Set (List Bool)) := fun a => by
  rw [Polynomial.eval_one, show 2 * 1 = 2 * 0 + 1 + 1 from rfl, List.replicate_succ,
    alternation_true_one_cons]
  simp only [List.replicate_succ, alternation_false_one_cons, List.replicate_zero,
    alternation_nil, firstMove, List.getD_cons_zero, Set.mem_univ, true_iff]
  exact ⟨true, fun _ => rfl⟩

/-- The universal player wins the game of one round by moving `false`. -/
private theorem isGameVerifier_secondMove :
    IsGameVerifier encBits 1 secondMove (∅ : Set (List Bool)) := fun a => by
  rw [Polynomial.eval_one, show 2 * 1 = 2 * 0 + 1 + 1 from rfl, List.replicate_succ,
    alternation_true_one_cons]
  simp only [List.replicate_succ, alternation_false_one_cons, List.replicate_zero,
    alternation_nil, secondMove, List.getD_cons_succ, List.getD_cons_zero, Set.mem_empty_iff_false,
    false_iff, not_exists, not_forall]
  exact fun _ => ⟨false, Bool.false_ne_true⟩

/-- `Set.univ ∈ AP` and `∅ ∈ AP` through the guess-then-verify machine, and `AP = PSPACE`
moves problems and game verifiers between the two classes. -/
example :
    ((Set.univ : Set (List Bool)) ∈ AP encBits ∧ (∅ : Set (List Bool)) ∈ AP encBits) ∧
    ((∅ : Set (List Bool)) ∈ PSPACE encBits ∧ (Set.univ : Set (List Bool)) ∈ PSPACE encBits) ∧
    ∃ (p : Polynomial ℕ) (V : List Bool × List Bool → Bool),
      MultiTapeTM.ComputableInPolyTime V (MultiTapeTM.encPair encBits encBits)
        MultiTapeTM.encBool ∧ IsGameVerifier encBits p V (Set.univ : Set (List Bool)) :=
  have huniv_pspace : (Set.univ : Set (List Bool)) ∈ PSPACE encBits :=
    AP_eq_PSPACE ▸ isGameVerifier_firstMove.mem_AP computableInPolyTime_firstMove
  ⟨⟨isGameVerifier_firstMove.mem_AP computableInPolyTime_firstMove,
    isGameVerifier_secondMove.mem_AP computableInPolyTime_secondMove⟩,
   ⟨mem_PSPACE_iff_exists_isGameVerifier.mpr
      ⟨1, secondMove, computableInPolyTime_secondMove, isGameVerifier_secondMove⟩,
    huniv_pspace⟩,
   exists_isGameVerifier_of_mem_PSPACE huniv_pspace⟩

/-! ### Single-bit moves -/

/-- The existential player chooses the first move. -/
example : Alternation true (List.replicate 2 1) fun w => w.head? = some true := by
  rw [show 2 = 2 * 1 from rfl, alternation_replicate_succ]
  exact ⟨true, fun _ => by simp⟩

/-- The universal player chooses the second move. -/
example : ¬Alternation true (List.replicate 2 1) fun w => w[1]? = some true := by
  rw [show 2 = 2 * 1 from rfl, alternation_replicate_succ]
  rintro ⟨x, h⟩
  have := h false
  simp at this

/-- A predicate ignoring the moves. -/
example : Alternation false (List.replicate 3 1) fun _ => True :=
  alternation_const.mpr trivial

/-! ### Rounds of quantifiers -/

/-- `∃ x, ∀ y, x ∨ ¬y` holds: take `x` true. -/
example : (QBF.rounds [(0, 1)] ((QBF.var 0).or (QBF.var 1).not)).eval (fun _ => false) = true := by
  decide

/-- `∃ x, ∀ y, x ↔ y` fails. -/
example : (QBF.rounds [(0, 1)] (QBF.iff (.var 0) (.var 1))).eval (fun _ => false) = false := by
  decide

/-- The same formula as a game of two moves. -/
example : ¬Alternation true (List.replicate 2 1) fun z =>
    (QBF.iff (.var 0) (.var 1)).eval (QBF.updates (fun _ => false) [0, 1] z) = true := by
  have h := QBF.eval_rounds_eq_true_iff [(0, 1)] (QBF.iff (.var 0) (.var 1)) (fun _ => false)
  simp only [QBF.roundVars, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.length_singleton, mul_one] at h
  rw [← h]
  decide

/-! ### Savitch's midpoint game -/

/-- The graph with one edge, from `[false]` to `[true]`. -/
private def oneEdge (u v : List Bool) : Bool := decide (u = [false] ∧ v = [true])

/-- The midpoint `[true]` and either half win the game at level `1`. -/
example : Cslib.Reachability.midpointGame oneEdge 1 1 [false] [true] [true, false, false, true] =
    true := by
  decide

/-- The existential player wins the midpoint game from `[false]` to `[true]`. -/
example : Alternation true (List.replicate (2 * ((1 + 1) * 1)) 1)
    fun z => Cslib.Reachability.midpointGame oneEdge 1 1 [false] [true] z = true :=
  (Cslib.Reachability.alternation_midpointGame_iff 1 [false] [true]).mpr (by decide)

/-- The existential player loses the midpoint game from `[true]` to `[false]`. -/
example : ¬Alternation true (List.replicate (2 * ((1 + 1) * 1)) 1)
    fun z => Cslib.Reachability.midpointGame oneEdge 1 1 [true] [false] z = true := by
  rw [Cslib.Reachability.alternation_midpointGame_iff]
  decide

/-- Trailing moves do not change a game that reads only its first move. -/
example : Alternation true ([1] ++ [1, 1]) (fun z => z.take 1 = [true]) :=
  (alternation_append_iff fun z => by
    simp only [List.sum_cons, List.sum_nil, List.take_take]; rfl).mpr ⟨[true], rfl, rfl⟩

end ComplexityTests.Alternation
