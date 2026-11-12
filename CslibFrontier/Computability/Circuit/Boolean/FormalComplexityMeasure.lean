/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Formula
import Mathlib.Data.Finset.Card

/-!
# Formal complexity measures

A `FormalComplexityMeasure` bounds literals by one and is subadditive under conjunction and
disjunction. Complement invariance is not assumed. The formula lower bound applies to
`Formula.IsConstantFree`: nullary constants have zero input-leaf cost in the library, whereas
the source axioms do not force their measure to vanish.

The source is [Arora–Barak, web draft 2007-01-08, §22.1, printed pp. 437–438,
PDF pp. 453–454][AroraBarak07]. `le_leafSize` is Theorem 22.1 for constant-free De Morgan
formulas, allowing negations anywhere. `card_le_four_mul_card` is Lemma 22.2, with all Boolean
functions on a fixed number of inputs and integer inequalities clearing both denominators.
The stronger near-total-density statement of Theorem 22.3 is not included.

## Main definitions

* `Cslib.Circuits.Boolean.FormalComplexityMeasure`: the source's measure axioms.
* `Cslib.Circuits.Formula.IsConstantFree`: De Morgan formulas without nullary constants.

## Main results

* `Cslib.Circuits.Boolean.FormalComplexityMeasure.le_leafSize`: the formula lower bound.
* `Cslib.Circuits.Boolean.FormalComplexityMeasure.card_le_four_mul_card`: at least a quarter
  of all Boolean functions have measure at least one quarter of a given function's measure.
-/

public section

namespace Cslib.Circuits

/-- A De Morgan formula contains no constant gates. Negation is permitted anywhere. -/
@[expose] def Formula.IsConstantFree {n : ℕ} : Formula Boolean.signature n → Prop
  | .input _ => True
  | .gate (.const _) _ => False
  | .gate .not args => (args 0).IsConstantFree
  | .gate .and args => (args 0).IsConstantFree ∧ (args 1).IsConstantFree
  | .gate .or args => (args 0).IsConstantFree ∧ (args 1).IsConstantFree

namespace Boolean

/-- A nonnegative integer measure on truth tables satisfying the literal and subadditivity
axioms of [Arora–Barak, draft §22.1][AroraBarak07]. No complement-invariance axiom is imposed. -/
structure FormalComplexityMeasure (n : ℕ) where
  /-- The measure of a Boolean function. -/
  measure : BooleanFunction n → ℕ
  /-- Positive literals have measure at most one. -/
  input_le (i : Fin n) : measure (fun x => x i) ≤ 1
  /-- Negative literals have measure at most one. -/
  not_input_le (i : Fin n) : measure (fun x => !(x i)) ≤ 1
  /-- Conjunction is subadditive. -/
  and_le (f g : BooleanFunction n) :
    measure (fun x => f x && g x) ≤ measure f + measure g
  /-- Disjunction is subadditive. -/
  or_le (f g : BooleanFunction n) :
    measure (fun x => f x || g x) ≤ measure f + measure g

namespace FormalComplexityMeasure

variable {n : ℕ} (μ : FormalComplexityMeasure n)

/-- Both polarities of a constant-free formula are bounded by its input-leaf count. -/
theorem eval_le_leafSize (F : Formula signature n) (hF : F.IsConstantFree) :
    μ.measure (F.eval interpretation) ≤ F.leafSize ∧
      μ.measure (fun x => !(F.eval interpretation x)) ≤ F.leafSize := by
  induction F with
  | input i => exact ⟨μ.input_le i, μ.not_input_le i⟩
  | gate op args ih =>
    cases op with
    | const c => exact hF.elim
    | not =>
      obtain ⟨hp, hn⟩ := ih 0 hF
      simpa [Formula.eval, interpretation, Formula.leafSize, Fin.sum_univ_one] using
        And.intro hn hp
    | and =>
      obtain ⟨hp₀, hn₀⟩ := ih 0 hF.1
      obtain ⟨hp₁, hn₁⟩ := ih 1 hF.2
      have hp := μ.and_le ((args 0).eval interpretation) ((args 1).eval interpretation)
      have hn := μ.or_le (fun x => !((args 0).eval interpretation x))
        (fun x => !((args 1).eval interpretation x))
      constructor
      · simpa [Formula.eval, interpretation, Formula.leafSize, Fin.sum_univ_two] using
          hp.trans (Nat.add_le_add hp₀ hp₁)
      · simpa [Formula.eval, interpretation, Formula.leafSize, Fin.sum_univ_two,
          Bool.not_and] using hn.trans (Nat.add_le_add hn₀ hn₁)
    | or =>
      obtain ⟨hp₀, hn₀⟩ := ih 0 hF.1
      obtain ⟨hp₁, hn₁⟩ := ih 1 hF.2
      have hp := μ.or_le ((args 0).eval interpretation) ((args 1).eval interpretation)
      have hn := μ.and_le (fun x => !((args 0).eval interpretation x))
        (fun x => !((args 1).eval interpretation x))
      constructor
      · simpa [Formula.eval, interpretation, Formula.leafSize, Fin.sum_univ_two] using
          hp.trans (Nat.add_le_add hp₀ hp₁)
      · simpa [Formula.eval, interpretation, Formula.leafSize, Fin.sum_univ_two,
          Bool.not_or] using hn.trans (Nat.add_le_add hn₀ hn₁)

/-- **Arora–Barak, draft Theorem 22.1:** a formal complexity measure lower-bounds the leaf size
of a constant-free formula computing the function. -/
theorem le_leafSize {f : BooleanFunction n} {F : Formula signature n}
    (hF : F.IsConstantFree) (hf : F.Computes interpretation f) :
    μ.measure f ≤ F.leafSize := by
  have he : F.eval interpretation = f := funext hf
  rw [← he]
  exact (μ.eval_le_leafSize F hF).1

/-- Decomposing a function as an exclusive or gives a four-term measure bound. -/
theorem le_four_terms (f g : BooleanFunction n) :
    μ.measure f ≤ μ.measure g + μ.measure (fun x => !(g x)) +
      μ.measure (fun x => f x ^^ g x) + μ.measure (fun x => !(f x ^^ g x)) := by
  have he : f = fun x => (!(f x ^^ g x) && g x) || ((f x ^^ g x) && !(g x)) := by
    funext x
    cases f x <;> cases g x <;> rfl
  have h := μ.or_le (fun x => !(f x ^^ g x) && g x)
    (fun x => (f x ^^ g x) && !(g x))
  have h₀ := μ.and_le (fun x => !(f x ^^ g x)) g
  have h₁ := μ.and_le (fun x => f x ^^ g x) (fun x => !(g x))
  rw [← he] at h
  omega

private theorem card_filter_involution {α : Type*} [Fintype α]
    (p : α → Prop) [DecidablePred p] (e : α → α) (he : Function.Involutive e) :
    (Finset.univ.filter fun x => p (e x)).card = (Finset.univ.filter p).card := by
  classical
  apply Finset.card_bijective e he.bijective
  intro x
  simp

/-- **Arora–Barak, draft Lemma 22.2:** if one function has measure at least `c`, at least a
quarter of all truth tables have measure at least `c / 4`. The inequalities clear denominators,
so no rounding or probability conventions are implicit. -/
theorem card_le_four_mul_card (f : BooleanFunction n) {c : ℕ} (hc : c ≤ μ.measure f) :
    Fintype.card (BooleanFunction n) ≤
      4 * (Finset.univ.filter fun g : BooleanFunction n => c ≤ 4 * μ.measure g).card := by
  classical
  let good : Finset (BooleanFunction n) := Finset.univ.filter fun g => c ≤ 4 * μ.measure g
  let neg : BooleanFunction n → BooleanFunction n := fun g x => !(g x)
  let shift : BooleanFunction n → BooleanFunction n := fun g x => f x ^^ g x
  have hn : Function.Involutive neg := by intro g; funext x; simp [neg]
  have hs : Function.Involutive shift := by
    intro g; funext x; dsimp [shift]; cases f x <;> cases g x <;> rfl
  have hns : Function.Involutive (fun g => neg (shift g)) := by
    intro g; funext x; dsimp [neg, shift]; cases f x <;> cases g x <;> rfl
  have cover : Finset.univ ⊆ good ∪ (Finset.univ.filter fun g => neg g ∈ good) ∪
      (Finset.univ.filter fun g => shift g ∈ good) ∪
      (Finset.univ.filter fun g => neg (shift g) ∈ good) := by
    intro g _
    have h := μ.le_four_terms f g
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, good]
    dsimp [neg, shift] at *
    omega
  have h₀ := card_filter_involution (fun g => c ≤ 4 * μ.measure g) neg hn
  have h₁ := card_filter_involution (fun g => c ≤ 4 * μ.measure g) shift hs
  have h₂ := card_filter_involution (fun g => c ≤ 4 * μ.measure g)
    (fun g => neg (shift g)) hns
  have hcard := Finset.card_le_card cover
  have hbound := Finset.card_union_le
    (good ∪ (Finset.univ.filter fun g => neg g ∈ good) ∪
      (Finset.univ.filter fun g => shift g ∈ good))
    (Finset.univ.filter fun g => neg (shift g) ∈ good)
  have hb₁ := Finset.card_union_le (good ∪ (Finset.univ.filter fun g => neg g ∈ good))
    (Finset.univ.filter fun g => shift g ∈ good)
  have hb₀ := Finset.card_union_le good (Finset.univ.filter fun g => neg g ∈ good)
  change _ = good.card at h₀ h₁ h₂
  simp only [good, Finset.mem_filter, Finset.mem_univ, true_and, Finset.card_univ]
    at hcard hbound hb₁ hb₀ h₀ h₁ h₂ ⊢
  omega

end FormalComplexityMeasure
end Boolean
end Cslib.Circuits
