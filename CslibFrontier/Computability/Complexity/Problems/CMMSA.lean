/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Promise.Reduction
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Logics.Propositional.DNF.Encoding

/-!
# Collective Minimum Monotone Satisfying Assignment

An instance of **CMMSA** [Hirahara2022, Section II.B, p. 974] is a list of weights `w(i)` of
variables `i < n`, a threshold `θ` and a list of monotone DNF formulas `φ₁, …, φₘ` over those
variables. An assignment is the set `S` of variables it sets to true, and its weight is
`∑_{i ∈ S} w(i)`. The gap problem `GapCMMSA Δ g σ` separates

* the yes-instances, where some assignment of weight at most `θ` satisfies every formula, from
* the no-instances, where every assignment of weight at most `g θ` satisfies fewer than a
  proportion `σ` of the formulas, counted with multiplicity: the paper's index `j` is uniform over
  the list.

Both sides require the instance to be well formed for the bound `Δ` (`CMMSAInstance.WellFormed`).
In the paper the gap and the proportion are `g = Δ^ε` and `σ = Δ^{-ε}`, with `Δ` bounding the
number of literals of each formula. Here `g` and `σ` are arbitrary parameters, and the
no-instances also require `1 ≤ g` and `σ ≤ 1`, so that the two sides are disjoint. The library's
own hardness result is for constant `g` and `σ = 1`, where a no-instance is one in which every
light assignment falsifies some formula (`mem_no_GapCMMSA_one`); see
`CslibFrontier.Computability.PCP.Approximation.LabelCover.MinRep`.

**Instance shape.** The paper leaves the shape of an instance implicit. `WellFormed` asks for
positive weights and threshold, nonempty formulas and terms, positive literals, variables below
`n`, and at most `Δ` literal occurrences per formula. These are the conditions that the planned
reduction from CMMSA to partial MCSP, issue #4362, uses. A zero threshold or a zero weight
breaks its size accounting, and an empty term or formula leaves its secret sharing undefined.

**Encoding.** Weights and threshold are written in unary (`CMMSAInstance.encoding`): a reduction
out of CMMSA may build tables whose size is polynomial in the weights and the threshold, which is
polynomial in the input length only when these are unary. Variable numbers inside the formulas are
binary (`encDNFOver encNat`).

## Main definitions

* `Cslib.Complexity.CMMSAInstance`: an instance, with `weight` and `satCount` of an assignment.
* `Cslib.Complexity.CMMSAInstance.WellFormed`: the instance shape, for a bound `Δ`.
* `Cslib.Complexity.CMMSAInstance.encoding`: unary weights and threshold, binary variables.
* `Cslib.Complexity.GapCMMSA`: the gap problem.

## Main results

* `Cslib.Complexity.mem_no_GapCMMSA_one`: at `σ = 1`, a no-instance is one in which every light
  assignment falsifies some formula.
* `Cslib.Complexity.CMMSAInstance.isPolyTime_mk` and the field accessors: the encoding is a
  record of its fields.

## References

* [S. Hirahara, *NP-Hardness of Learning Programs and Partial MCSP*][Hirahara2022]
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-- An instance of **CMMSA**: weights of the variables `i < weights.length`, a threshold and a
list of DNF formulas over the variables. -/
@[ext]
structure CMMSAInstance where
  /-- The weight of each variable; the variables are the indices below `weights.length`. -/
  weights : List ℕ
  /-- The weight `θ` allowed to a satisfying assignment of a yes-instance. -/
  threshold : ℕ
  /-- The formulas, read with multiplicity. -/
  formulas : List (DNF ℕ)
  deriving DecidableEq, Repr

namespace CMMSAInstance

variable (I : CMMSAInstance)

/-- The weight `∑_{i ∈ S} w(i)` of the assignment setting exactly the variables in `S` to true. -/
@[expose] def weight (S : Finset ℕ) : ℕ := ∑ i ∈ S, I.weights.getD i 0

/-- The number of formulas, counted with multiplicity, that the assignment setting exactly the
variables in `S` to true satisfies. -/
@[expose] def satCount (S : Finset ℕ) : ℕ :=
  I.formulas.countP fun φ => φ.eval fun i => decide (i ∈ S)

/-- The shape of a CMMSA instance whose formulas have at most `Δ` literal occurrences each. -/
structure WellFormed (Δ : ℕ) : Prop where
  /-- Every weight is positive. -/
  weight_pos : ∀ w ∈ I.weights, 0 < w
  /-- The threshold is positive. -/
  threshold_pos : 0 < I.threshold
  /-- Every formula has a term. -/
  formula_ne_nil : ∀ φ ∈ I.formulas, φ ≠ []
  /-- Every term has a literal. -/
  term_ne_nil : ∀ φ ∈ I.formulas, ∀ t ∈ φ, t ≠ []
  /-- Every literal is positive: the formulas are monotone. -/
  monotone : ∀ φ ∈ I.formulas, ∀ t ∈ φ, ∀ l ∈ t, l.2 = true
  /-- Every literal is a variable of the instance. -/
  var_lt : ∀ φ ∈ I.formulas, ∀ t ∈ φ, ∀ l ∈ t, l.1 < I.weights.length
  /-- Every formula has at most `Δ` literal occurrences. -/
  length_flatten_le : ∀ φ ∈ I.formulas, φ.flatten.length ≤ Δ

/-- A bound on the literals of each formula is also a bound for every larger `Δ`. -/
theorem WellFormed.mono {I : CMMSAInstance} {Δ Δ' : ℕ} (h : I.WellFormed Δ) (hΔ : Δ ≤ Δ') :
    I.WellFormed Δ' :=
  { h with length_flatten_le := fun φ hφ => (h.length_flatten_le φ hφ).trans hΔ }

/-- **Unary weights and threshold**, binary variables: an instance is encoded as the framed list of
its unary weights, its framed unary threshold and the list of its formulas over binary variable
numbers (`encDNFOver encNat`). -/
enc_structure encoding : CMMSAInstance where
  weights : (encList encUnary), threshold : encUnary, formulas : (encList (encDNFOver encNat))

section PolyTime

variable {Input : Type} {input : Input ↪ List Bool}

/-- Reading the weights is polynomial-time. -/
@[fun_prop]
theorem isPolyTime_weights {inst : Input → CMMSAInstance}
    (h : ComputableInPolyTime inst input encoding) :
    ComputableInPolyTime (fun x => (inst x).weights) input (encList encUnary) :=
  encoding_weights_deg.computableInPolyTime.comp h

/-- Reading the threshold is polynomial-time. -/
@[fun_prop]
theorem isPolyTime_threshold {inst : Input → CMMSAInstance}
    (h : ComputableInPolyTime inst input encoding) :
    ComputableInPolyTime (fun x => (inst x).threshold) input encUnary :=
  encoding_threshold_deg.computableInPolyTime.comp h

/-- Reading the formulas is polynomial-time. -/
@[fun_prop]
theorem isPolyTime_formulas {inst : Input → CMMSAInstance}
    (h : ComputableInPolyTime inst input encoding) :
    ComputableInPolyTime (fun x => (inst x).formulas) input (encList (encDNFOver encNat)) :=
  encoding_formulas_deg.computableInPolyTime.comp h

/-- Assembling computed weights, threshold and formulas into an instance is polynomial-time. -/
@[fun_prop]
theorem isPolyTime_mk {weights : Input → List ℕ} {threshold : Input → ℕ}
    {formulas : Input → List (DNF ℕ)}
    (hweights : ComputableInPolyTime weights input (encList encUnary))
    (hthreshold : ComputableInPolyTime threshold input encUnary)
    (hformulas : ComputableInPolyTime formulas input (encList (encDNFOver encNat))) :
    ComputableInPolyTime (fun x => CMMSAInstance.mk (weights x) (threshold x) (formulas x))
      input encoding :=
  encoding_mk_deg.computableInPolyTime.comp (hweights.prod (hthreshold.prod hformulas))

end PolyTime

end CMMSAInstance

open CMMSAInstance

/-- **Gap CMMSA** [Hirahara2022, Section II.B, p. 974] with at most `Δ` literal occurrences per
formula, gap `g` and proportion `σ`. The yes-instances have an assignment of weight at most `θ`
satisfying every formula. The no-instances have `1 ≤ g` and `σ ≤ 1`, and every assignment of
weight at most `g θ` satisfies fewer than `σ m` of the `m` formulas. Both are well formed
(`CMMSAInstance.WellFormed`), and assignments set only variables of the instance. -/
def GapCMMSA (Δ : ℕ) (g σ : ℝ) : PromiseProblem CMMSAInstance where
  yes := {I | I.WellFormed Δ ∧ ∃ S ⊆ Finset.range I.weights.length,
    I.weight S ≤ I.threshold ∧ ∀ φ ∈ I.formulas, φ.eval (fun i => decide (i ∈ S)) = true}
  no := {I | I.WellFormed Δ ∧ 1 ≤ g ∧ σ ≤ 1 ∧ ∀ S ⊆ Finset.range I.weights.length,
    (I.weight S : ℝ) ≤ g * I.threshold → (I.satCount S : ℝ) < σ * I.formulas.length}
  disjoint := Set.disjoint_left.2 fun I ⟨_, S, hS, hw, hsat⟩ ⟨_, hg, hσ, hno⟩ => by
    have hcount : I.satCount S = I.formulas.length := List.countP_eq_length.2 hsat
    have hw' : (I.weight S : ℝ) ≤ I.threshold := by exact_mod_cast hw
    have hlt := hno S hS (hw'.trans (le_mul_of_one_le_left (Nat.cast_nonneg _) hg))
    rw [hcount] at hlt
    have := mul_le_mul_of_nonneg_right hσ (Nat.cast_nonneg (α := ℝ) I.formulas.length)
    linarith

variable {Δ : ℕ} {g σ : ℝ} {I : CMMSAInstance}

theorem mem_yes_GapCMMSA :
    I ∈ (GapCMMSA Δ g σ).yes ↔ I.WellFormed Δ ∧ ∃ S ⊆ Finset.range I.weights.length,
      I.weight S ≤ I.threshold ∧ ∀ φ ∈ I.formulas, φ.eval (fun i => decide (i ∈ S)) = true :=
  Iff.rfl

theorem mem_no_GapCMMSA :
    I ∈ (GapCMMSA Δ g σ).no ↔ I.WellFormed Δ ∧ 1 ≤ g ∧ σ ≤ 1 ∧
      ∀ S ⊆ Finset.range I.weights.length,
        (I.weight S : ℝ) ≤ g * I.threshold → (I.satCount S : ℝ) < σ * I.formulas.length :=
  Iff.rfl

/-- **At `σ = 1`, a no-instance is one in which every assignment of weight at most `g θ` falsifies
some formula.** -/
theorem mem_no_GapCMMSA_one :
    I ∈ (GapCMMSA Δ g 1).no ↔ I.WellFormed Δ ∧ 1 ≤ g ∧
      ∀ S ⊆ Finset.range I.weights.length, (I.weight S : ℝ) ≤ g * I.threshold →
        ∃ φ ∈ I.formulas, φ.eval (fun i => decide (i ∈ S)) = false := by
  simp only [mem_no_GapCMMSA, le_refl, true_and, one_mul, Nat.cast_lt]
  refine and_congr_right fun _ => and_congr_right fun _ =>
    forall₂_congr fun S _ => imp_congr_right fun _ => ?_
  constructor
  · intro h
    by_contra hall
    simp only [not_exists, not_and, Bool.not_eq_false] at hall
    exact h.ne (List.countP_eq_length.2 hall)
  · rintro ⟨φ, hφ, hfalse⟩
    refine lt_of_le_of_ne List.countP_le_length fun h => ?_
    have := List.countP_eq_length.1 h φ hφ
    simp only [hfalse, Bool.false_eq_true] at this

end Cslib.Complexity
