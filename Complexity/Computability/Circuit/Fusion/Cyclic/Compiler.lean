/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Fusion.Cyclic.Closure
public import Complexity.Computability.Circuit.Monotone.Formula
public import Complexity.Computability.Circuit.Cyclic.Feedback
import Complexity.Computability.Circuit.Fusion.Cyclic
import Complexity.Computability.Circuit.Simulation

/-!
# Compiling semifilter covers to binary cyclic circuits

The generated closure of a finite pair list can be reconstructed from the input sets and the
listed pair intersections. Compile their update equations as ordinary native formulas, then
close the state inputs with `Circuit.feedback`. Each pair occurrence contributes exactly one
AND gate; all other operations are free binary ORs and constants. The final output reconstructs
the empty-index closure, hence the target of an unrestricted cover.

This finite presentation works on arbitrary carriers, including infinite ones. It does not
enumerate the subsets of the target complement or require the input sets to cover the carrier:
the monotone basis already supplies a free top constant. Selecting the active seeds uses
classical subset tests, so this is a noncomputable construction with least-fixed-point semantics,
not an efficient compiler or an iteration bound. The converse concerns unrestricted semifilters;
the forward lower bound also allows restricted witness classes.

## Main definitions

* `Cslib.Circuits.Fusion.PairClosureCompiler.readState`,
  `Cslib.Circuits.Fusion.PairClosureCompiler.pairValues`: reconstruct a closure coordinate from
  finitely many input and pair values.
* `Cslib.Circuits.Fusion.PairClosureCompiler.joinFormula`,
  `Cslib.Circuits.Fusion.PairClosureCompiler.readFormula`,
  `Cslib.Circuits.Fusion.PairClosureCompiler.updateFormula`: monotone formulas for union trees,
  coordinate reads, and pair updates.
* `Cslib.Circuits.Fusion.PairClosureCompiler.updateCircuit`,
  `Cslib.Circuits.Fusion.PairClosureCompiler.circuit`: the straight-line update circuit and its
  feedback closure.
* `Cslib.Circuits.Fusion.PairCover.toCyclic`: a finite binary circuit realizing a pair cover.

## Main results

* `Cslib.Circuits.Fusion.PairCover.eval_toCyclic`: the circuit's least solution is its target.
* `Cslib.Circuits.Fusion.PairCover.cost_toCyclic`: its AND cost is exactly the pair-list length.
* `Cslib.Circuits.Fusion.pairCoverComplexity_eq_cyclic_ecomplexityFrom`: unrestricted pair-cover
  complexity equals cyclic AND complexity from the supplied inputs, with free ORs and constants.

## References

* Reworks the finite compiler, binary lowering and completeness argument in
  LowerBound/Fusion/Cyclic/{Compiler,LowerJoinMeet,Complete}.lean of
  [S. Schlesinger, *Algebraic circuit formalizations in Complexitylib*][Schlesinger2026Algebraic].
  The finite presentation here uses only pair values, instead of all complement subsets.
-/

@[expose] public section

namespace Cslib.Circuits.Fusion.PairClosureCompiler

universe u

variable {U : Type u} {n : ℕ}

/-- Reconstruct a closure state from the finite input seeds and listed pair intersections. -/
def readState (target : Set U) (input : Fin n → Set U)
    (pairs : List (Set ↥(targetᶜ) × Set ↥(targetᶜ))) (state : Fin pairs.length → Set U) :
    Set ↥(targetᶜ) →o Set U where
  toFun s := {point | s = Set.univ ∨
    (∃ i, Subtype.val ⁻¹' input i ⊆ s ∧ point ∈ input i) ∨
    ∃ j, (pairs.get j).1 ∩ (pairs.get j).2 ⊆ s ∧ point ∈ state j}
  monotone' s t h point hp := by
    rcases hp with hs | ⟨i, hi, hx⟩ | ⟨j, hj, hx⟩
    · exact Or.inl (Set.eq_univ_of_univ_subset (hs ▸ h))
    · exact Or.inr (Or.inl ⟨i, hi.trans h, hx⟩)
    · exact Or.inr (Or.inr ⟨j, hj.trans h, hx⟩)

variable (target : Set U) (input : Fin n → Set U)
  (pairs : List (Set ↥(targetᶜ) × Set ↥(targetᶜ)))

/-- The intended pair values are intersections in the generated closure. -/
def pairValues : Fin pairs.length → Set U :=
  fun j => pairClosure target input pairs (pairs.get j).1 ∩
    pairClosure target input pairs (pairs.get j).2

/-- A pair state closed under its reconstructed intersections contains all derivations. -/
theorem pairClosure_le_readState (state : Fin pairs.length → Set U)
    (hstate : ∀ j, readState target input pairs state (pairs.get j).1 ∩
      readState target input pairs state (pairs.get j).2 ⊆ state j) :
    pairClosure target input pairs ≤ readState target input pairs state :=
  pairClosure_le _ (fun _ _ => Or.inl rfl)
    (fun i _ hx => Or.inr (Or.inl ⟨i, Set.Subset.rfl, hx⟩))
    (fun p hp _ hx => by
      obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hp
      exact Or.inr (Or.inr ⟨j, Set.Subset.rfl, hstate j hx⟩))

/-- Only the listed pair values are needed to reconstruct the whole generated closure. -/
theorem readState_pairValues :
    readState target input pairs (pairValues target input pairs) =
      pairClosure target input pairs := by
  have hread : readState target input pairs (pairValues target input pairs) ≤
      pairClosure target input pairs := by
    intro s point
    rintro (rfl | ⟨i, hi, hx⟩ | ⟨j, hj, hx, hy⟩)
    · exact .univ
    · exact (PairDerivation.input i hx).mono hi
    · exact (PairDerivation.inter (pairs.get j) (List.get_mem pairs j) hx hy).mono hj
  exact le_antisymm hread (pairClosure_le_readState target input pairs _
    (fun j => Set.inter_subset_inter (hread _) (hread _)))

/-- A binary union tree with a constant seed; it contains no charged conjunctions of its own. -/
def joinFormula {r : ℕ} (seed : Bool) : List (Formula Monotone.signature r) →
    Formula Monotone.signature r
  | [] => Monotone.const seed
  | f :: fs => Monotone.or f (joinFormula seed fs)

/-- The union tree charges exactly the conjunctions in its arguments. -/
private theorem cost_joinFormula {r : ℕ} (seed : Bool) (fs : List (Formula Monotone.signature r)) :
    (joinFormula seed fs).cost Monotone.andCost = (fs.map (·.cost Monotone.andCost)).sum := by
  induction fs with
  | nil => simp [joinFormula, Monotone.const]
  | cons f fs ih => simp [joinFormula, Monotone.or, Fin.sum_univ_two, ih]

/-- Membership in a union tree is membership in its seed or one of its arguments. -/
theorem mem_eval_joinFormula {r : ℕ} (seed : Bool) (fs : List (Formula Monotone.signature r))
    (values : Fin r → Set U) (point : U) :
    point ∈ (joinFormula seed fs).eval (Monotone.setInterpretation U) values ↔
      seed = true ∨ ∃ f ∈ fs, point ∈ f.eval (Monotone.setInterpretation U) values := by
  induction fs with
  | nil => cases seed <;> simp [joinFormula, Monotone.const]
  | cons f fs ih =>
    simp [joinFormula, Monotone.or, ih, or_left_comm]

/-- Every union tree has an operation at its root, including the empty tree. -/
private theorem joinFormula_isGate {r : ℕ} (seed : Bool)
    (fs : List (Formula Monotone.signature r)) :
    ∃ op args, joinFormula seed fs = .gate op args := by
  cases fs <;> exact ⟨_, _, rfl⟩

open scoped Classical in
/-- A free union of the active input seeds and pair values at a requested complement subset. -/
noncomputable def readFormula (s : Set ↥(targetᶜ)) :
    Formula Monotone.signature (n + (pairs.length + 1)) :=
  joinFormula (decide (s = Set.univ))
    (List.ofFn (fun i : Fin n =>
      if Subtype.val ⁻¹' input i ⊆ s then .input (Fin.castAdd (pairs.length + 1) i)
      else Monotone.const false) ++
    List.ofFn (fun j : Fin pairs.length =>
      if (pairs.get j).1 ∩ (pairs.get j).2 ⊆ s then .input (Fin.natAdd n j.castSucc)
      else Monotone.const false))

/-- Reading a closure coordinate needs only free union and constant gates. -/
theorem cost_readFormula (s : Set ↥(targetᶜ)) :
    (readFormula target input pairs s).cost Monotone.andCost = 0 := by
  classical
  simp [readFormula, cost_joinFormula, Monotone.const, Function.comp_def, apply_ite]

/-- The ordinary formula evaluates to the finite presentation of the closure state. -/
theorem eval_readFormula (s : Set ↥(targetᶜ)) (state : Fin (pairs.length + 1) → Set U) :
    (readFormula target input pairs s).eval (Monotone.setInterpretation U)
      (Fin.append input state) = readState target input pairs (state ∘ Fin.castSucc) s := by
  classical
  ext point
  have hite (p : Prop) (i : Fin (n + (pairs.length + 1))) :
      point ∈ (if p then Formula.input i else Monotone.const false).eval
        (Monotone.setInterpretation U) (Fin.append input state) ↔
          p ∧ point ∈ Fin.append input state i := by
    by_cases hp : p <;> simp [hp, Monotone.const]
  simp only [readFormula, mem_eval_joinFormula, List.mem_append, or_and_right, exists_or,
    List.mem_ofFn]
  simp [readState, hite]

/-- One conjunction for each pair, followed by the reconstructed empty-index output. -/
noncomputable def updateFormula : Fin (pairs.length + 1) →
    Formula Monotone.signature (n + (pairs.length + 1)) :=
  Fin.lastCases (readFormula target input pairs ∅)
    (fun j => Monotone.and (readFormula target input pairs (pairs.get j).1)
      (readFormula target input pairs (pairs.get j).2))

/-- Compile each update formula using the existing native formula compiler. -/
noncomputable def updateCircuit : Circuit Monotone.signature
    (n + (pairs.length + 1)) (pairs.length + 1) :=
  Circuit.pi (fun j => (updateFormula target input pairs j).toCircuit)

private theorem outputGate_pi {r m : ℕ} (cs : Fin m → Circuit Monotone.signature r 1)
    (h : ∀ i, ∃ j, (cs i).outputs 0 = .gate j) (i : Fin m) :
    ∃ j, (Circuit.pi cs).outputs i = .gate j := by
  induction m with
  | zero => exact i.elim0
  | succ m ih =>
    induction i using Fin.lastCases with
    | last =>
      obtain ⟨j, hj⟩ := h (Fin.last m)
      refine ⟨Fin.natAdd _ j, ?_⟩
      change ((Circuit.pi _).append _).outputs (Fin.natAdd m 0) = _
      rw [Circuit.outputs_append_natAdd, hj]
      rfl
    | cast i =>
      obtain ⟨j, hj⟩ := ih (fun i => cs i.castSucc) (fun i => h i.castSucc) i
      refine ⟨Fin.castAdd _ j, ?_⟩
      change ((Circuit.pi _).append _).outputs (Fin.castAdd 1 i) = _
      rw [Circuit.outputs_append_castAdd, hj]
      rfl

/-- Every compiled update output is an internal gate, so closing feedback adds no operations. -/
theorem updateCircuit_outputs (i : Fin (pairs.length + 1)) :
    ∃ j, (updateCircuit target input pairs).outputs i = .gate j := by
  apply outputGate_pi
  intro j
  have h : ∃ op args, updateFormula target input pairs j = .gate op args := by
    induction j using Fin.lastCases with
    | last =>
      simpa only [updateFormula, Fin.lastCases_last, readFormula] using joinFormula_isGate _ _
    | cast j =>
      rw [updateFormula, Fin.lastCases_castSucc]
      exact ⟨_, _, rfl⟩
  obtain ⟨op, args, h⟩ := h
  rw [h]
  exact ⟨Fin.natAdd _ (0 : Fin 1), rfl⟩

/-- The update uses exactly one charged conjunction per listed pair occurrence. -/
theorem cost_updateCircuit :
    (updateCircuit target input pairs).program.cost Monotone.andCost = pairs.length := by
  rw [updateCircuit, Circuit.cost_program_pi, Fin.sum_univ_castSucc]
  simp [Formula.cost_toCircuit, updateFormula, Monotone.and, Fin.sum_univ_two, cost_readFormula]

/-- The native update program computes the finite closure equations. -/
theorem eval_updateCircuit (state : Fin (pairs.length + 1) → Set U) :
    (updateCircuit target input pairs).eval (Monotone.setInterpretation U)
      (Fin.append input state) =
        Fin.lastCases (readState target input pairs (state ∘ Fin.castSucc) ∅)
          (fun j => readState target input pairs (state ∘ Fin.castSucc) (pairs.get j).1 ∩
            readState target input pairs (state ∘ Fin.castSucc) (pairs.get j).2) := by
  funext j
  simp only [updateCircuit, Circuit.eval_pi, Formula.eval_toCircuit]
  induction j using Fin.lastCases with
  | last =>
    simpa only [updateFormula, Fin.lastCases_last] using
      eval_readFormula target input pairs ∅ state
  | cast j =>
    simp [updateFormula, Monotone.and, eval_readFormula]

/-- Close the finite update program by feeding its outputs back into its state inputs. -/
noncomputable def circuit : CyclicCircuit Monotone.signature n (pairs.length + 1) :=
  (updateCircuit target input pairs).feedback (updateCircuit_outputs target input pairs)

/-- Closing feedback preserves the exact number of listed pair occurrences. -/
@[simp] theorem cost_circuit :
    (circuit target input pairs).cost Monotone.andCost = pairs.length := by
  rw [circuit, Circuit.cost_feedback, cost_updateCircuit]

/-- The finite circuit reconstructs every listed pair value and the empty-index closure. -/
theorem eval_circuit :
    (circuit target input pairs).eval (Monotone.setInterpretation U)
      Monotone.setInterpretation_mono input =
        Fin.lastCases (pairClosure target input pairs ∅) (pairValues target input pairs) := by
  let values : Fin (pairs.length + 1) → Set U :=
    Fin.lastCases (pairClosure target input pairs ∅) (pairValues target input pairs)
  have hvalues : values ∘ Fin.castSucc = pairValues target input pairs := by
    funext j
    simp only [Function.comp_apply, values, Fin.lastCases_castSucc]
  have hfixed : (updateCircuit target input pairs).eval (Monotone.setInterpretation U)
      (Fin.append input values) = values := by
    rw [eval_updateCircuit, hvalues, readState_pairValues]
    rfl
  apply le_antisymm
  · exact (updateCircuit target input pairs).eval_feedback_le _ _
      Monotone.setInterpretation_mono input hfixed.le
  · let state := (circuit target input pairs).eval (Monotone.setInterpretation U)
      Monotone.setInterpretation_mono input
    have hstate : (updateCircuit target input pairs).eval (Monotone.setInterpretation U)
        (Fin.append input state) = state :=
      (updateCircuit target input pairs).eval_feedback_fixed _ _
        Monotone.setInterpretation_mono input
    rw [eval_updateCircuit] at hstate
    have hpair (j : Fin pairs.length) :
        readState target input pairs (state ∘ Fin.castSucc) (pairs.get j).1 ∩
          readState target input pairs (state ∘ Fin.castSucc) (pairs.get j).2 =
            state j.castSucc := by
      simpa only [Fin.lastCases_castSucc] using congrFun hstate j.castSucc
    have hlast : readState target input pairs (state ∘ Fin.castSucc) ∅ =
        state (Fin.last pairs.length) := by
      simpa only [Fin.lastCases_last] using congrFun hstate (Fin.last pairs.length)
    have hclosure := pairClosure_le_readState target input pairs (state ∘ Fin.castSucc)
      (fun j => (hpair j).le)
    intro j
    induction j using Fin.lastCases with
    | last => simpa only [Fin.lastCases_last] using (hclosure ∅).trans_eq hlast
    | cast j =>
      simpa only [Fin.lastCases_castSucc, pairValues] using
        (Set.inter_subset_inter (hclosure _) (hclosure _)).trans_eq (hpair j)

end Cslib.Circuits.Fusion.PairClosureCompiler

namespace Cslib.Circuits.Fusion

universe u

variable {U : Type u} {n : ℕ} {target : Set U} {input : Fin n → Set U}

/-- Realize an unrestricted pair cover by a finite binary cyclic circuit.
The subset tests selecting its free unions are noncomputable on arbitrary carriers. -/
noncomputable def PairCover.toCyclic (c : PairCover target input) :
    CyclicCircuit Monotone.signature n 1 where
  lines := (PairClosureCompiler.circuit target input c.pairs).lines
  outputs _ := (PairClosureCompiler.circuit target input c.pairs).outputs (Fin.last c.pairs.length)

/-- The compiled cover charges exactly one conjunction per pair occurrence. -/
@[simp] theorem PairCover.cost_toCyclic (c : PairCover target input) :
    c.toCyclic.cost Monotone.andCost = c.pairs.length :=
  PairClosureCompiler.cost_circuit target input c.pairs

/-- The least solution of the compiled unrestricted cover is exactly its target. -/
@[simp] theorem PairCover.eval_toCyclic (c : PairCover target input) :
    c.toCyclic.eval (Monotone.setInterpretation U) Monotone.setInterpretation_mono input =
      fun _ => target := by
  funext i
  change (PairClosureCompiler.circuit target input c.pairs).eval (Monotone.setInterpretation U)
    Monotone.setInterpretation_mono input (Fin.last c.pairs.length) = target
  rw [PairClosureCompiler.eval_circuit]
  simp only [Fin.lastCases_last, c.pairClosure_empty]

/-- Unrestricted semifilter cover complexity is exactly binary cyclic AND complexity,
with free unions and constants, on arbitrary carriers and supplied input sets. -/
theorem pairCoverComplexity_eq_cyclic_ecomplexityFrom (target : Set U) (input : Fin n → Set U) :
    pairCoverComplexity target input =
      CyclicCircuit.ecomplexityFrom (Monotone.setInterpretation U)
        Monotone.setInterpretation_mono Monotone.andCost
        (fun _ : Unit => fun _ : Fin 1 => target) (fun _ => input) := by
  apply le_antisymm
  · exact pairCoverComplexity_le_cyclic_ecomplexityFrom (fun _ => input)
      (fun _ : Unit => fun _ : Fin 1 => target) () 0
  · apply le_pairCoverComplexity_iff.mpr
    intro c
    simpa only [PairCover.cost_toCyclic] using
      CyclicCircuit.ecomplexityFrom_le_of_computesFrom (weight := Monotone.andCost)
        c.toCyclic (fun _ => c.eval_toCyclic)

end Cslib.Circuits.Fusion
