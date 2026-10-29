/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Fusion.Boolean
import Mathlib.Tactic.FinCases

/-!
# Boolean clients of semifilter covers

Explicit witnesses give exact one-AND bounds for conjunction and for a conjunction using a
negative supplied literal. Raw positive inputs cannot compute negation, while supplying that
literal makes it free. Set/Boolean transport retains arbitrary costs and shared outputs, and an
empty assignment domain still requires a syntactic circuit with the requested output.
-/

namespace ComplexityTests.FusionBoolean

open Cslib.Circuits Fusion

private def nonemptySets {U : Type*} [Nonempty U] : Semifilter U where
  toFun s := s.Nonempty
  monotone' _ _ h hs := hs.mono h
  map_top' := by simp
  map_bot' := by simp

private theorem positive_cover {U : Type*} {n : ℕ} {target : Set U}
    {input : Fin n → Set U} (w : SemifilterWitness target input) (c : PairCover target input) :
    1 ≤ c.pairs.length := by
  by_contra h
  have hempty : c.pairs = [] := List.length_eq_zero_iff.mp (by lia)
  exact c.isCover w (by simp [hempty])

private abbrev conjunction (x : Fin 2 → Bool) : Fin 3 → Bool := ![x 0 && x 1, x 0, x 0 && x 1]

private instance : Nonempty ↥({x : Fin 2 → Bool | conjunction x 0 = true}ᶜ) :=
  ⟨⟨![false, true], by decide⟩⟩

private def conjunctionWitness : SemifilterWitness {x | conjunction x 0 = true}
    (fun i : Fin 2 => {x | x i = true}) where
  point := ⟨![true, true], by decide⟩
  filter := nonemptySets
  admissible_filter := trivial
  above i _ := by
    fin_cases i
    · exact ⟨⟨![true, false], by decide⟩, rfl⟩
    · exact ⟨⟨![false, true], by decide⟩, rfl⟩

private def andInputs : Circuit Monotone.signature 2 3 :=
  ⟨(Program.empty : Program Monotone.signature 2 0).gate ⟨.and, ![.input 0, .input 1]⟩,
    ![.gate 0, .input 0, .gate 0]⟩

private theorem andInputs_computes :
    andInputs.ComputesFrom Monotone.interpretation conjunction id :=
  fun _ => by funext i; fin_cases i <;> rfl

example : ecomplexityFrom Monotone.interpretation Monotone.andCost conjunction id = 1 := by
  apply le_antisymm (ecomplexityFrom_le_of_computesFrom andInputs andInputs_computes)
  refine le_ecomplexityFrom_iff.mpr fun c hc => ?_
  exact_mod_cast pairCover_lowerBound_of_computesFrom id conjunction 0
    (positive_cover conjunctionWitness) c hc

-- Literal sources are ordinary functions; negative literals are supplied for free.
private abbrev literals (x : Fin 2 → Bool) : Fin (2 + 2) → Bool :=
  Fin.append x (fun i => !x i)

private abbrev difference (x : Fin 2 → Bool) : Fin 3 → Bool :=
  ![x 0 && !x 1, x 1, x 0 && !x 1]

private instance : Nonempty ↥({x : Fin 2 → Bool | difference x 0 = true}ᶜ) :=
  ⟨⟨![false, false], by decide⟩⟩

private def literalWitness : SemifilterWitness {x | difference x 0 = true}
    (fun i => {x | literals x i = true}) where
  point := ⟨![true, false], by decide⟩
  filter := nonemptySets
  admissible_filter := trivial
  above i h := by
    fin_cases i
    · exact ⟨⟨![true, true], by decide⟩, rfl⟩
    · exact Bool.false_ne_true h |>.elim
    · exact Bool.false_ne_true h |>.elim
    · exact ⟨⟨![false, false], by decide⟩, rfl⟩

private def andLiterals : Circuit Monotone.signature 4 3 :=
  ⟨(Program.empty : Program Monotone.signature 4 0).gate ⟨.and, ![.input 0, .input 3]⟩,
    ![.gate 0, .input 1, .gate 0]⟩

private theorem andLiterals_computes :
    andLiterals.ComputesFrom Monotone.interpretation difference literals :=
  fun _ => by funext i; fin_cases i <;> rfl

private theorem literal_lower_bound : (1 : ℕ∞) ≤
    ecomplexityFrom Monotone.interpretation Monotone.andCost difference literals := by
  apply le_trans _ (pairCoverComplexity_le_ecomplexityFrom_bool literals difference 0)
  exact le_pairCoverComplexity_iff.mpr fun c => by
    exact_mod_cast positive_cover literalWitness c

private theorem difference_complexity :
    ecomplexityFrom Monotone.interpretation Monotone.andCost difference literals = 1 :=
  le_antisymm (ecomplexityFrom_le_of_computesFrom andLiterals andLiterals_computes)
    literal_lower_bound

-- Both spellings of the literal family use the same computation certificate and set generators.
example :
    andLiterals.ComputesFrom Monotone.interpretation difference
        (fun x i => Fin.addCases x (Bool.not ∘ x) i) ∧
      andLiterals.eval (Monotone.setInterpretation (Fin 2 → Bool))
        (Fin.append (fun i => {x : Fin 2 → Bool | x i = true}) (fun i => {x | x i = false})) =
          (fun o => {x | difference x o = true}) := by
  refine ⟨andLiterals_computes, ?_⟩
  have h : (fun i => {x : Fin 2 → Bool | literals x i = true}) =
      Fin.append (fun i => {x | x i = true}) (fun i => {x | x i = false}) := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [literals, Fin.append_left]
    · simp only [literals, Fin.append_right]
      ext x
      simp
  rw [← h]
  exact (Monotone.eval_setOf_iff_computesFrom andLiterals literals difference).mpr
    andLiterals_computes

private def pointFilter {U : Type*} (x : U) : Semifilter U where
  toFun s := x ∈ s
  monotone' _ _ h hx := h hx
  map_top' := rfl
  map_bot' := rfl

private def negationWitness : SemifilterWitness {x : Bool | (!x) = true}
    (fun _ : Fin 1 => {x | x = true}) where
  point := ⟨false, rfl⟩
  filter := pointFilter ⟨true, by decide⟩
  admissible_filter := trivial
  above _ h := (Bool.false_ne_true h).elim

private theorem negation_cover_top :
    pairCoverComplexity {x : Bool | (!x) = true} (fun _ : Fin 1 => {x | x = true}) = ⊤ := by
  apply top_le_iff.mp
  refine le_pairCoverComplexity_iff.mpr fun c => (c.isCover negationWitness ?_).elim
  exact fun _ _ ha hb => ⟨ha, hb⟩

-- Positive supplied inputs cannot compute negation in the monotone basis.
private theorem negation_raw_top : ecomplexityFrom Monotone.interpretation Monotone.andCost
    (fun x : Bool => ![!x]) (fun x => ![x]) = ⊤ := by
  apply top_le_iff.mp
  rw [← negation_cover_top]
  simpa using
    pairCoverComplexity_le_ecomplexityFrom_bool (fun x : Bool => ![x]) (fun x => ![!x]) 0

-- Supplying the negative literal changes that same target into a free projection.
example : ecomplexityFrom Monotone.interpretation Monotone.andCost
    (fun x : Bool => ![!x]) (fun x => ![x, !x]) = 0 := by
  simpa only [Function.comp_def, Matrix.cons_fin_one, Matrix.cons_val_one] using
    ecomplexityFrom_wiring (I := Monotone.interpretation) (cost := Monotone.andCost)
      (fun x : Bool => ![x, !x]) (fun _ : Fin 1 => 1)

-- Equality of minimum complexities includes the unrepresentable case.
example : ecomplexityFrom (Monotone.setInterpretation Bool) Monotone.andCost
    (fun _ : Unit => ![{x | (!x) = true}]) (fun _ => ![{x | x = true}]) = ⊤ := by
  rw [← Monotone.ecomplexityFrom_boolIndicator]
  simpa [Set.boolIndicator, Matrix.cons_fin_one] using negation_raw_top

private def shared : Circuit Monotone.signature 4 4 :=
  ⟨((((((Program.empty : Program Monotone.signature 4 0).gate
    ⟨.const false, Fin.elim0⟩).gate ⟨.const true, Fin.elim0⟩).gate
    ⟨.or, ![.input 0, .gate 0]⟩).gate ⟨.and, ![.gate 2, .input 3]⟩).gate
    ⟨.or, ![.gate 3, .gate 0]⟩).gate ⟨.and, ![.gate 2, .input 3]⟩,
    ![.gate 4, .gate 4, .gate 3, .input 1]⟩

private def mixedWeight : Monotone.Op → ℕ
  | .const false => 2
  | .const true => 3
  | .or => 5
  | .and => 7

example : shared.eval (Monotone.setInterpretation (Fin 2 → Bool))
    (fun i => {x | literals x i = true}) =
      (fun o => {x | (![x 0 && !x 1, x 0 && !x 1, x 0 && !x 1, x 1] : Fin 4 → Bool) o = true}) := by
  apply (Monotone.eval_setOf_iff_computesFrom shared literals _).mpr
  intro x
  funext i
  fin_cases i
  · change (((x 0 || false) && !x 1) || false) = (x 0 && !x 1)
    simp
  · change (((x 0 || false) && !x 1) || false) = (x 0 && !x 1)
    simp
  · change ((x 0 || false) && !x 1) = (x 0 && !x 1)
    simp
  · rfl

/-- info: ([[false, false, false, false], [false, false, false, true],
 [true, true, true, false], [false, false, false, true]], 6, 2, 29) -/
#guard_msgs (whitespace := lax) in
#eval (([![false, false], ![false, true], ![true, false], ![true, true]] :
    List (Fin 2 → Bool)).map
      (fun x => List.ofFn (shared.eval Monotone.interpretation (literals x))),
  shared.size, shared.program.cost Monotone.andCost, shared.program.cost mixedWeight)

example : ecomplexityFrom (Monotone.setInterpretation (Fin 2 → Bool)) Monotone.andCost
    (fun _ : Unit => fun o => {x | difference x o = true})
      (fun _ => fun i => {x | literals x i = true}) = 1 := by
  rw [← Monotone.ecomplexityFrom_boolIndicator]
  simpa [Set.boolIndicator] using difference_complexity

private def zero : Circuit Monotone.signature 0 1 :=
  Circuit.oneGate (.const false) Fin.elim0

-- Empty assignment domains still require a circuit that has an output wire.
private theorem empty_complexity : ecomplexityFrom Monotone.interpretation (fun _ => 1)
    (fun x : Empty => (x.elim : Fin 1 → Bool)) (fun x => (x.elim : Fin 0 → Bool)) = 1 := by
  apply le_antisymm (ecomplexityFrom_le_of_computesFrom zero (fun x => x.elim))
  refine le_ecomplexityFrom_iff.mpr fun ⟨p, outputs⟩ _ => ?_
  cases p with
  | empty => cases outputs 0 with
    | input i => exact i.elim0
    | gate i => exact i.elim0
  | gate p line => exact_mod_cast Nat.le_add_left 1 (p.cost fun _ => 1)

example : ecomplexityFrom (Monotone.setInterpretation Empty) (fun _ => 1)
    (fun _ : Unit => fun _ : Fin 1 => ∅) (fun _ => Fin.elim0) = 1 := by
  rw [← Monotone.ecomplexityFrom_boolIndicator]
  convert empty_complexity using 1
  congr 1 <;> funext x <;> exact x.elim

end ComplexityTests.FusionBoolean
