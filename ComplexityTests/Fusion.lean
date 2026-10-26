/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.SumOfTerms.Coverage
import Mathlib.Tactic.FinCases
import Mathlib.Data.Finset.Sort

/-!
# Fusion and support-coverage clients

The clients distinguish actual-gate bounds from global ones, preserve repeated gates and
outputs, and use finite targets in an infinite support type. They also check zero costs,
empty witnesses, empty outputs and the source-complexity bridge. A four-witness example obtains
an attained lower bound of three dictionary gates from nonuniform masses; union gates have zero
cost. With one capacity valid for every dictionary term, unweighted counting on any subset of
the same witnesses gives a lower bound of at most two.
-/

namespace ComplexityTests.Fusion

open Cslib.Circuits SumOfTerms

private def pairs (t : ℕ) : Finset ℕ := {2 * t, 2 * t + 1}

private def shared : Circuit (signature ℕ) 1 4 :=
  ⟨(((((Program.empty : Program (signature ℕ) 1 0).gate ⟨.term 0, Fin.elim0⟩).gate
      ⟨.term 1, Fin.elim0⟩).gate ⟨.add, ![.gate 0, .gate 1]⟩).gate
      ⟨.add, ![.gate 2, .gate 0]⟩).gate ⟨.term 0, Fin.elim0⟩,
    ![.gate 3, .gate 0, .gate 3, .input 0]⟩

-- The final term is unused, while the first term and a designated output are reused.
example : shared.program.cost termCost = 3 ∧ shared.program.cost addCost = 2 := by decide

example : shared.eval (supportInterpretation pairs) ![{99}] =
    ![{0, 1, 2, 3}, {0, 1}, {0, 1, 2, 3}, {99}] := by decide

/-- info: ([[0, 1, 2, 3], [0, 1], [0, 1, 2, 3], [99]], 5, 3) -/
#guard_msgs in
#eval (List.ofFn (fun i => (shared.eval (supportInterpretation pairs) ![{99}] i).sort (· ≤ ·)),
  shared.size,
  shared.program.cost termCost)

private theorem pair_bound (target : Finset ℕ) (t : ℕ) : (target ∩ pairs t).card ≤ 2 :=
  (Finset.card_le_card Finset.inter_subset_right).trans Finset.card_le_two

-- A theorem for arbitrary circuits, rather than just computation of one example's cost.
example (c : Circuit (signature ℕ) 0 1)
    (hc : {0, 1, 2, 3} ⊆ c.eval (supportInterpretation pairs) Fin.elim0 0) :
    2 ≤ c.program.cost termCost := by
  have h := ceilDiv_card_le_termCost c pairs Fin.elim0 {0, 1, 2, 3}
    (fun i => i.elim0) 0 hc two_pos (pair_bound _)
  change 2 ≤ _ at h
  exact h

example : 2 ≤ shared.program.cost termCost := by
  have h := ceilDiv_card_le_termCost shared pairs ![{99}] {0, 1, 2, 3}
    (by decide) 0 (by decide) two_pos (pair_bound _)
  change 2 ≤ _ at h
  exact h

-- Singleton dictionaries give the separated bound over the infinite ambient type ℕ.
example (c : Circuit (signature ℕ) 0 1) (target : Finset ℕ)
    (hc : target ⊆ c.eval (supportInterpretation fun t => {t}) Fin.elim0 0) :
    target.card ≤ c.program.cost termCost := by
  refine card_le_termCost_of_separated c (fun t => {t}) Fin.elim0 target
    (fun i => i.elim0) 0 hc fun t => ?_
  exact (Finset.card_le_card Finset.inter_subset_right).trans_eq (Finset.card_singleton t)

-- The weight of a range term is its cardinality; term zero is a legitimate free nullary gate.
example (c : Circuit (signature ℕ) 0 1)
    (hc : Finset.range 6 ⊆ c.eval (supportInterpretation Finset.range) Fin.elim0 0) :
    6 ≤ c.program.cost (dictionaryCost id) := by
  have h := card_le_mul_dictionaryCost c.program Finset.range Fin.elim0 (Finset.range 6)
    (fun i => i.elim0) (c.outputs 0) hc id 1 (fun t => ?_)
  · simpa using h
  · exact (Finset.card_le_card Finset.inter_subset_right).trans_eq (by simp)

private def freeEmpty : Circuit (signature ℕ) 0 1 :=
  ⟨Program.empty.gate ⟨.term 0, Fin.elim0⟩, fun _ => .gate 0⟩

example : freeEmpty.size = 1 ∧ freeEmpty.program.cost (dictionaryCost id) = 0 ∧
    freeEmpty.eval (supportInterpretation Finset.range) Fin.elim0 0 = ∅ := by decide

-- Supplied target elements invalidate the necessary disjointness condition.
example : (Circuit.id (signature ℕ) 1).eval (supportInterpretation pairs) ![{0}] 0 = {0} ∧
    (Circuit.id (signature ℕ) 1).program.cost termCost = 0 ∧
    ¬ Disjoint ({0} : Finset ℕ) ({0} : Finset ℕ) := by decide

private def localSupports (t : Fin 3) : Finset ℕ :=
  if t = 2 then {0, 1} else {t.val}

private def localOnly : Circuit (signature (Fin 3)) 0 2 :=
  ⟨((Program.empty : Program (signature (Fin 3)) 0 0).gate ⟨.term 0, Fin.elim0⟩).gate
      ⟨.term 1, Fin.elim0⟩,
    ![.gate 0, .gate 1]⟩

-- Preservation can fail on both witnesses for a semantic atom outside the circuit.
example : ((⟨.term 2, Fin.elim0⟩ : Fusion.Atom (signature (Fin 3)) (Finset ℕ)).failures
    (supportInterpretation localSupports) (fun t s => t ∉ s) {0, 1}).card = 2 := by
  rw [failures_support_term]
  decide

-- The actual gate bound is one on the SAME sample {0,1}; the unused dictionary term violates it.
-- Each witness needs a different designated output.
example : 2 ≤ localOnly.program.cost termCost := by
  apply Fusion.ceilDiv_card_le_circuit_cost localOnly (supportInterpretation localSupports)
    (fun t s => t ∉ s) {0, 1} Fin.elim0 (fun _ _ i => i.elim0) ?_
    termCost (by decide : 0 < 1) ?_
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact ⟨0, by decide⟩
    · exact ⟨1, by decide⟩
  · have hlocal (a : Fusion.Atom (signature (Fin 3)) (Finset ℕ))
        (h : a.op = .term 0 ∨ a.op = .term 1) :
        (a.failures (supportInterpretation localSupports) (fun t s => t ∉ s) {0, 1}).card ≤ 1 := by
      rcases a with ⟨op, args⟩
      rcases h with rfl | rfl <;> rw [failures_support_term] <;> decide
    intro k
    dsimp only [localOnly] at k ⊢
    fin_cases k <;> apply hlocal <;> decide

private def sharedCover : Fusion.Cover (supportInterpretation pairs)
    (fun t : Fin 4 => fun s => t.val ∉ s) :=
  Fusion.Cover.ofProgram shared.program (supportInterpretation pairs)
    (fun t : Fin 4 => fun s => t.val ∉ s) ![{99}] (by decide)
    (fun t => ⟨.gate (3 : Fin 5), by fin_cases t <;> decide⟩)

-- All five gates are retained, including the repeated unused term.
example : sharedCover.size = 5 ∧ sharedCover.atoms (0 : Fin 5) =
    sharedCover.atoms (4 : Fin 5) := by
  constructor
  · rfl
  · apply congrArg (fun args => (⟨.term 0, args⟩ : Fusion.Atom (signature ℕ) (Finset ℕ)))
    exact Subsingleton.elim _ _

private def mixedWeight : Op ℕ → ℕ
  | .add => 17
  | .term t => t + 2

example : sharedCover.cost mixedWeight = 41 := by
  rw [sharedCover, Fusion.Cover.cost_ofProgram]
  decide

private def singles : Bool → Finset Bool := fun b => {b}
private def avoids : Bool → Finset Bool → Prop := fun b s => b ∉ s

private theorem two_le_cover_cost (c : Fusion.Cover (supportInterpretation singles) avoids) :
    2 ≤ c.cost termCost := by
  have h := c.card_le_mul_cost Finset.univ termCost 1 (fun i => ?_)
  · simpa using h
  · rcases c.atoms i with ⟨op, args⟩
    change ((⟨op, args⟩ : Fusion.Atom (signature Bool) (Finset Bool)).failures
      (supportInterpretation singles) (fun t s => t ∉ s) Finset.univ).card ≤ 1 * termCost op
    cases op with
    | add => rw [failures_support_add]; simp
    | term t => rw [failures_support_term]; simp [singles]

-- The minimum-cover bound transfers to a finite, inhabited native construction problem.
example : (2 : ℕ∞) ≤ ecomplexityFrom (supportInterpretation singles) termCost
    (fun _ : Unit => fun _ : Fin 1 => Finset.univ) (fun _ : Unit => Fin.elim0) := by
  have hcover : (2 : ℕ∞) ≤ Fusion.coverComplexity (supportInterpretation singles) avoids
      termCost := Fusion.le_coverComplexity_iff.mpr fun c => by
    exact_mod_cast two_le_cover_cost c
  exact hcover.trans (Fusion.coverComplexity_le_ecomplexityFrom
    (supportInterpretation singles) avoids termCost _ _ () (fun _ i => i.elim0)
    (fun t => ⟨0, by simp [avoids]⟩))

private def twoSingles : Circuit (signature Bool) 0 1 :=
  ⟨((Program.empty : Program (signature Bool) 0 0).gate ⟨.term false, Fin.elim0⟩ |>.gate
    ⟨.term true, Fin.elim0⟩ |>.gate ⟨.add, ![.gate 0, .gate 1]⟩), fun _ => .gate 2⟩

example : ecomplexityFrom (supportInterpretation singles) termCost
    (fun _ : Unit => fun _ : Fin 1 => Finset.univ) (fun _ : Unit => Fin.elim0) ≤ 2 :=
  ecomplexityFrom_le_of_computesFrom twoSingles (fun _ => by decide)

private def weightedSupports : Fin 4 → Finset (Fin 4) := ![{0, 1}, {2}, {0, 3}, {1, 3}]

private def witnessMass (t : Fin 4) : ℕ := if t = 2 then 2 else 1

-- Total mass is five, but every available dictionary term has mass at most two.
example : ∑ t : Fin 4, witnessMass t = 5 := by decide

private theorem weighted_support_bound (t : Fin 4) :
    ∑ x ∈ Finset.univ ∩ weightedSupports t, witnessMass x ≤ 2 := by
  revert t
  decide

-- The lower bound applies to every circuit producing the full target from no free inputs.
example (c : Circuit (signature (Fin 4)) 0 1)
    (hc : Finset.univ ⊆ c.eval (supportInterpretation weightedSupports) Fin.elim0 0) :
    3 ≤ c.program.cost termCost := by
  have h := ceilDiv_sum_le_termCost c weightedSupports Fin.elim0 Finset.univ witnessMass
    (fun i => i.elim0) 0 hc two_pos weighted_support_bound
  change 3 ≤ _ at h
  exact h

-- No unweighted subset gives a global dictionary-capacity bound above two: some dictionary
-- term covers at least half of it. This checks all sixteen subsets, including the empty one.
example : ∀ samples : Finset (Fin 4), ∃ t : Fin 4,
    samples.card ≤ 2 * (samples ∩ weightedSupports t).card := by decide

private def threeTerms : Circuit (signature (Fin 4)) 0 1 :=
  ⟨(((((Program.empty : Program (signature (Fin 4)) 0 0).gate ⟨.term 0, Fin.elim0⟩).gate
      ⟨.term 1, Fin.elim0⟩).gate ⟨.term 2, Fin.elim0⟩).gate
      ⟨.add, ![.gate 0, .gate 1]⟩).gate ⟨.add, ![.gate 3, .gate 2]⟩,
    fun _ => .gate 4⟩

-- The lower bound is nonvacuous and sharp: three dictionary gates suffice.
example : threeTerms.eval (supportInterpretation weightedSupports) Fin.elim0 0 = Finset.univ ∧
    threeTerms.program.cost termCost = 3 := by decide

-- Zero mass allows zero capacity even for a nonempty, covered target.
example : (∑ _t ∈ (Finset.univ : Finset (Fin 4)), (0 : ℕ)) ≤
    0 * threeTerms.program.cost termCost := by
  exact sum_le_mul_dictionaryCost threeTerms.program weightedSupports Fin.elim0 Finset.univ
    (fun _ => 0) (fun i => i.elim0) (threeTerms.outputs 0) (by decide) (fun _ => 1) 0
    (by simp)

-- Empty witness types admit an empty cover and hence zero complexity.
example : Fusion.coverComplexity (supportInterpretation pairs)
    (fun t : Empty => t.elim) termCost = 0 := by
  apply nonpos_iff_eq_zero.mp
  exact Fusion.coverComplexity_le
    (⟨0, Fin.elim0, fun t => t.elim⟩ : Fusion.Cover (supportInterpretation pairs)
      (fun t : Empty => t.elim)) termCost

example : Fusion.coverComplexity (supportInterpretation pairs)
    (fun t : Empty => t.elim) termCost ≤
      (Circuit.wiring (signature ℕ) (Fin.elim0 : Fin 0 → Fin 0)).program.cost termCost :=
  Fusion.coverComplexity_le_circuit_cost
    (Circuit.wiring (signature ℕ) (Fin.elim0 : Fin 0 → Fin 0)) (supportInterpretation pairs)
    (fun t : Empty => t.elim) Fin.elim0 (fun t => t.elim) (fun t => t.elim) termCost

-- A universally true predicate has no cover, even though the signature has many circuits.
example : Fusion.coverComplexity (supportInterpretation pairs)
    (fun _ : Unit => fun _ => True) termCost = ⊤ := by
  apply top_le_iff.mp
  refine Fusion.le_coverComplexity_iff.mpr fun c => ?_
  exact (c.isCover () (fun _ _ => trivial)).elim

-- Zero capacity is supported by the multiplicative theorem when the sampled target is empty.
example : (∅ : Finset ℕ).card ≤ 0 * freeEmpty.program.cost (dictionaryCost id) :=
  card_le_mul_dictionaryCost freeEmpty.program Finset.range Fin.elim0 ∅ (fun i => i.elim0)
    (freeEmpty.outputs 0) (Finset.empty_subset _) id 0 (fun _ => by simp)

-- All four relevant universes remain independent, including the supplied-source domain.
universe u v w z
example {σ : Signature.{u}} {U : Type v} {W : Type w} {X : Type z}
    (I : Interpretation σ U) (P : W → U → Prop) (weight : σ.Op → ℕ)
    (sources : X → Fin 2 → U) (target : X → Fin 3 → U) (x : X)
    (hin : ∀ t i, P t (sources x i)) (hout : ∀ t, ∃ o, ¬ P t (target x o)) :
    Fusion.coverComplexity I P weight ≤ ecomplexityFrom I weight target sources :=
  Fusion.coverComplexity_le_ecomplexityFrom I P weight target sources x hin hout

end ComplexityTests.Fusion
