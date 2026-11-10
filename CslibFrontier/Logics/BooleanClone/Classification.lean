/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.BooleanClone.Basic
public import CslibFrontier.Foundations.Data.BitString.Threshold
public import CslibFrontier.Foundations.Data.BitString.Parity
import Mathlib.Tactic.FinCases

/-!
# The four-generator Boolean clone classification

Every positive-arity Boolean clone consists of essentially unary operations or contains AND,
OR, majority or minority: [Chen2006CSP], Theorem 5.1, arXiv v1, printed pp. 17–18.
The arbitrary-arity proof is original: ternary partition minors detect a singleton coordinate.
This shared algebraic theorem supports both Schaefer's dichotomy and Post's criterion.

## Main definitions

* `Cslib.Logic.EssentiallyUnary`: dependence on at most one coordinate.

## Main results

* `Cslib.Logic.BooleanClone.classification`: the four-generator classification at all arities.
* `Cslib.Logic.BooleanClone.exists_projection_of_ternaryMinors`: ternary minors detect projections.

## References

* [H. Chen, *A Rendezvous of Logic, Complexity, and Algebra*][Chen2006CSP], Theorem 5.1,
  arXiv v1, printed pp. 17–18.
-/

public section

namespace Cslib.Logic

/-- An operation depends on at most one coordinate, including constant operations. Positive
arity is essential: the witnessing coordinate cannot exist at arity zero. -/
@[expose] def EssentiallyUnary {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ i : Fin n, ∃ u : Bool → Bool, ∀ a, f a = u (a i)

/-- For an idempotent operation, essential unarity means being a projection. -/
theorem EssentiallyUnary.exists_projection {n : ℕ} {f : (Fin n → Bool) → Bool}
    (hf : EssentiallyUnary f) (hid : ∀ b, f (fun _ => b) = b) :
    ∃ i, ∀ a, f a = a i := by
  obtain ⟨i, u, hu⟩ := hf
  refine ⟨i, fun a => ?_⟩
  rw [hu]
  exact (hu (fun _ => a i)).symm.trans (hid (a i))

namespace BooleanClone

variable (C : BooleanClone)

/-- Without AND, OR and minority, every binary operation is essentially unary.
The ten non-unary binary truth tables generate AND, OR or minority by the displayed
superpositions; the remaining six tables depend on at most one input. -/
theorem binary_essentiallyUnary
    (hand : andOp ∉ C.operations 2) (hor : orOp ∉ C.operations 2)
    (hminority : (Cslib.parity 3) ∉ C.operations 3)
    {f : (Fin 2 → Bool) → Bool} (hf : f ∈ C.operations 2) : EssentiallyUnary f := by
  have h₁ := C.comp (by decide) (by decide) hf (fun _ : Fin 2 => hf)
  have h₂ := C.comp (by decide) (by decide) hf
    (show ∀ i : Fin 2, ![(fun a : Fin 2 → Bool => a 0), f] i ∈ C.operations 2 by
      intro i
      fin_cases i
      · exact C.projection 0
      · exact hf)
  have h₃ := C.comp (by decide) (by decide) hf
    (show ∀ i : Fin 2, ![f, (fun a : Fin 2 → Bool => a 1)] i ∈ C.operations 2 by
      intro i
      fin_cases i
      · exact hf
      · exact C.projection 1)
  have htail := C.minor (n := 3) (by decide) (by decide) hf ![1, 2]
  have h₄ := C.comp (by decide) (by decide) hf
    (show ∀ i : Fin 2, ![(fun a : Fin 3 → Bool => a 0),
        (fun a : Fin 3 → Bool => f (a ∘ (![1, 2] : Fin 2 → Fin 3)))] i ∈ C.operations 3 by
      intro i
      fin_cases i
      · exact C.projection 0
      · exact htail)
  rw [binaryTable_eq f] at hf h₁ h₂ h₃ h₄ ⊢
  generalize f ![false, false] = b00 at *
  generalize f ![false, true] = b01 at *
  generalize f ![true, false] = b10 at *
  generalize f ![true, true] = b11 at *
  cases b00 <;> cases b01 <;> cases b10 <;> cases b11
  · exact ⟨0, fun _ => false, by decide⟩
  · exact False.elim (hand (by convert hf using 1; decide))
  · exact False.elim (hand (by convert h₂ using 1; decide))
  · exact ⟨0, id, by decide⟩
  · exact False.elim (hand (by convert h₃ using 1; decide))
  · exact ⟨1, id, by decide⟩
  · exact False.elim (hminority (by convert h₄ using 1; decide))
  · exact False.elim (hor (by convert hf using 1; decide))
  · exact False.elim (hor (by convert h₁ using 1; decide))
  · exact False.elim (hminority (by convert h₄ using 1; decide))
  · exact ⟨1, Bool.not, by decide⟩
  · exact False.elim (hor (by convert h₂ using 1; decide))
  · exact ⟨0, Bool.not, by decide⟩
  · exact False.elim (hor (by convert h₃ using 1; decide))
  · exact False.elim (hand (by convert h₁ using 1; decide))
  · exact ⟨0, fun _ => true, by decide⟩

private theorem selfDual_of_binaryMinors {n : ℕ} {f : (Fin n → Bool) → Bool}
    (h : ∀ p : Fin n → Fin 2, ∃ j, ∀ a, f (a ∘ p) = a j) :
    ∀ a, f (fun i => !(a i)) = !(f a) := by
  intro a
  obtain ⟨j, hj⟩ := h (fun i => if a i then 1 else 0)
  have h₀ := hj ![false, true]
  have h₁ := hj ![true, false]
  have he₀ : (![false, true] : Fin 2 → Bool) ∘ (fun i => if a i then 1 else 0) = a := by
    funext i
    cases ha : a i <;> simp [ha]
  have he₁ : (![true, false] : Fin 2 → Bool) ∘ (fun i => if a i then 1 else 0) =
      (fun i => !(a i)) := by
    funext i
    cases ha : a i <;> simp [ha]
  rw [he₀] at h₀
  rw [he₁] at h₁
  rw [h₀, h₁]
  fin_cases j <;> rfl

private def ternaryTable (b0 b1 b2 : Bool) (a : Fin 3 → Bool) : Bool :=
  if a 0 then
    if a 1 then if a 2 then true else !b2 else if a 2 then !b1 else b0
  else
    if a 1 then if a 2 then !b0 else b1 else if a 2 then b2 else false

private theorem ternaryTable_eq {f : (Fin 3 → Bool) → Bool}
    (hid : ∀ b, f (fun _ => b) = b)
    (hself : ∀ a, f (fun i => !(a i)) = !(f a)) :
    f = ternaryTable (f ![true, false, false]) (f ![false, true, false])
      (f ![false, false, true]) := by
  have h000 : f ![false, false, false] = false := by
    exact (congrArg f (show ![false, false, false] = (fun _ => false) by decide)).trans
      (hid false)
  have h111 : f ![true, true, true] = true := by
    exact (congrArg f (show ![true, true, true] = (fun _ => true) by decide)).trans
      (hid true)
  have h011 : f ![false, true, true] = !(f ![true, false, false]) := by
    have he : (fun i : Fin 3 => !(![true, false, false] i)) = ![false, true, true] := by decide
    simpa only [he] using hself ![true, false, false]
  have h101 : f ![true, false, true] = !(f ![false, true, false]) := by
    have he : (fun i : Fin 3 => !(![false, true, false] i)) = ![true, false, true] := by decide
    simpa only [he] using hself ![false, true, false]
  have h110 : f ![true, true, false] = !(f ![false, false, true]) := by
    have he : (fun i : Fin 3 => !(![false, false, true] i)) = ![true, true, false] := by decide
    simpa only [he] using hself ![false, false, true]
  funext a
  have ha : a = ![a 0, a 1, a 2] := by ext i; fin_cases i <;> rfl
  conv_lhs => rw [ha]
  cases h₀ : a 0 <;> cases h₁ : a 1 <;> cases h₂ : a 2 <;>
    simp [ternaryTable, h₀, h₁, h₂, h000, h111, h011, h101, h110]

/-- An idempotent ternary operation in a clone missing the four generators is a projection.
The eight self-dual idempotent tables are the three projections, majority, minority, and three
skew majorities; each skew majority generates majority by self-composition. -/
theorem ternary_idempotent_projection
    (hand : andOp ∉ C.operations 2) (hor : orOp ∉ C.operations 2)
    (hmajority : Cslib.majority 3 ∉ C.operations 3)
    (hminority : Cslib.parity 3 ∉ C.operations 3)
    {f : (Fin 3 → Bool) → Bool} (hf : f ∈ C.operations 3)
    (hid : ∀ b, f (fun _ => b) = b) : ∃ i, ∀ a, f a = a i := by
  have hself := selfDual_of_binaryMinors fun p =>
    (C.binary_essentiallyUnary hand hor hminority
      (C.minor (by decide) (by decide) hf p)).exists_projection (fun b => hid b)
  have h₀ := C.comp (by decide) (by decide) hf
    (show ∀ i : Fin 3, ![f, (fun a : Fin 3 → Bool => a 1),
        (fun a : Fin 3 → Bool => a 2)] i ∈ C.operations 3 by
      intro i
      fin_cases i
      · exact hf
      · exact C.projection 1
      · exact C.projection 2)
  have h₁ := C.comp (by decide) (by decide) hf
    (show ∀ i : Fin 3, ![(fun a : Fin 3 → Bool => a 0), f,
        (fun a : Fin 3 → Bool => a 2)] i ∈ C.operations 3 by
      intro i
      fin_cases i
      · exact C.projection 0
      · exact hf
      · exact C.projection 2)
  have h₂ := C.comp (by decide) (by decide) hf
    (show ∀ i : Fin 3, ![(fun a : Fin 3 → Bool => a 0),
        (fun a : Fin 3 → Bool => a 1), f] i ∈ C.operations 3 by
      intro i
      fin_cases i
      · exact C.projection 0
      · exact C.projection 1
      · exact hf)
  rw [ternaryTable_eq hid hself] at hf h₀ h₁ h₂ ⊢
  generalize f ![true, false, false] = b0 at *
  generalize f ![false, true, false] = b1 at *
  generalize f ![false, false, true] = b2 at *
  cases b0 <;> cases b1 <;> cases b2
  · exact False.elim (hmajority (by convert hf using 1; decide))
  · exact ⟨2, by decide⟩
  · exact ⟨1, by decide⟩
  · exact False.elim (hmajority (by convert h₀ using 1; decide))
  · exact ⟨0, by decide⟩
  · exact False.elim (hmajority (by convert h₁ using 1; decide))
  · exact False.elim (hmajority (by convert h₂ using 1; decide))
  · exact False.elim (hminority (by convert hf using 1; decide))

/-- Ternary identification minors detect every finite Boolean operation that is not a
projection. This statement covers arbitrary finite arity, including arity zero: its hypotheses
are then inconsistent, since a nullary operation cannot be idempotent. -/
theorem exists_projection_of_ternaryMinors {n : ℕ} {f : (Fin n → Bool) → Bool}
    (hid : ∀ b, f (fun _ => b) = b)
    (h : ∀ p : Fin n → Fin 3, ∃ k, ∀ a, f (a ∘ p) = a k) :
    ∃ i, ∀ a, f a = a i := by
  classical
  let χ : Finset (Fin n) → Fin n → Bool := fun s i => decide (i ∈ s)
  have hsingle : ∃ i, f (χ {i}) = true := by
    by_contra hn
    have hz (i : Fin n) : f (χ {i}) = false := by
      cases he : f (χ {i})
      · rfl
      · exact False.elim (hn ⟨i, he⟩)
    have hall (s : Finset (Fin n)) : f (χ s) = false := by
      induction s using Finset.induction_on with
      | empty => exact hid false
      | @insert i s hi ih =>
        let p : Fin n → Fin 3 := fun j => if j = i then 0 else if j ∈ s then 1 else 2
        obtain ⟨k, hk⟩ := h p
        have hp₀ : (![true, false, false] : Fin 3 → Bool) ∘ p = χ {i} := by
          funext j
          by_cases hj : j = i <;> by_cases hjs : j ∈ s <;> simp [p, χ, hj, hjs]
        have hp₁ : (![false, true, false] : Fin 3 → Bool) ∘ p = χ s := by
          funext j
          by_cases hj : j = i
          · subst j; simp [p, χ, hi]
          · by_cases hjs : j ∈ s <;> simp [p, χ, hj, hjs]
        have hpu : (![true, true, false] : Fin 3 → Bool) ∘ p = χ (insert i s) := by
          funext j
          by_cases hj : j = i <;> by_cases hjs : j ∈ s <;> simp [p, χ, hj, hjs]
        have h₀ := hk ![true, false, false]
        have h₁ := hk ![false, true, false]
        have hu := hk ![true, true, false]
        rw [hp₀, hz] at h₀
        rw [hp₁, ih] at h₁
        rw [hpu] at hu
        fin_cases k
        · cases h₀
        · cases h₁
        · exact hu
    have hc : χ Finset.univ = fun _ => true := by ext j; simp [χ]
    have hb := hall Finset.univ
    rw [hc, hid] at hb
    cases hb
  obtain ⟨i, hi⟩ := hsingle
  refine ⟨i, fun a => ?_⟩
  let p : Fin n → Fin 3 := fun j => if j = i then 0 else if a j then 1 else 2
  obtain ⟨k, hk⟩ := h p
  have hp₀ : (![true, false, false] : Fin 3 → Bool) ∘ p = χ {i} := by
    funext j
    by_cases hj : j = i <;> cases ha : a j <;> simp [p, χ, hj, ha]
  have h₀ := hk ![true, false, false]
  rw [hp₀, hi] at h₀
  have hk₀ : k = 0 := by
    fin_cases k
    · rfl
    · cases h₀
    · cases h₀
  have hpa : (![a i, true, false] : Fin 3 → Bool) ∘ p = a := by
    funext j
    by_cases hj : j = i
    · subst j; simp [p]
    · cases ha : a j <;> simp [p, hj, ha]
  have hresult := hk ![a i, true, false]
  simpa only [hpa, hk₀, Matrix.cons_val_zero] using hresult

/-- An arbitrary positive-arity idempotent operation in a clone missing the four generators
is a projection. There is no upper bound on its arity. -/
theorem idempotent_projection
    (hand : andOp ∉ C.operations 2) (hor : orOp ∉ C.operations 2)
    (hmajority : Cslib.majority 3 ∉ C.operations 3)
    (hminority : Cslib.parity 3 ∉ C.operations 3)
    {n : ℕ} (hn : 0 < n) {f : (Fin n → Bool) → Bool} (hf : f ∈ C.operations n)
    (hid : ∀ b, f (fun _ => b) = b) : ∃ i, ∀ a, f a = a i :=
  exists_projection_of_ternaryMinors hid fun p =>
    C.ternary_idempotent_projection hand hor hmajority hminority
      (C.minor hn (by decide) hf p) (fun b => hid b)

private theorem constant_of_binaryMinors {n : ℕ} {f : (Fin n → Bool) → Bool} {b : Bool}
    (hdiag : ∀ c, f (fun _ => c) = b)
    (h : ∀ p : Fin n → Fin 2, EssentiallyUnary (fun a => f (a ∘ p))) :
    ∀ a, f a = b := by
  intro a
  let p : Fin n → Fin 2 := fun i => if a i then 1 else 0
  obtain ⟨j, u, hu⟩ := h p
  have huv (c : Bool) : u c = b := (hu (fun _ => c)).symm.trans (hdiag c)
  have hp : (![false, true] : Fin 2 → Bool) ∘ p = a := by
    funext i
    cases ha : a i <;> simp [p, ha]
  have he := hu ![false, true]
  change f (![false, true] ∘ p) = u (![false, true] j) at he
  rw [hp, huv] at he
  exact he

/-- Chen's Boolean clone classification, Theorem 5.1 (arXiv v1, printed pp. 17–18), in
contrapositive form. All positive arities are quantified, and constants count as essentially
unary operations. -/
theorem essentiallyUnary_of_missing_generators
    (hand : andOp ∉ C.operations 2) (hor : orOp ∉ C.operations 2)
    (hmajority : Cslib.majority 3 ∉ C.operations 3)
    (hminority : Cslib.parity 3 ∉ C.operations 3)
    {n : ℕ} (hn : 0 < n) {f : (Fin n → Bool) → Bool} (hf : f ∈ C.operations n) :
    EssentiallyUnary f := by
  have hb : ∀ p : Fin n → Fin 2, EssentiallyUnary (fun a => f (a ∘ p)) :=
    fun p => C.binary_essentiallyUnary hand hor hminority (C.minor hn (by decide) hf p)
  cases h₀ : f (fun _ => false) <;> cases h₁ : f (fun _ => true)
  · exact ⟨⟨0, hn⟩, fun _ => false,
      constant_of_binaryMinors (fun c => by cases c <;> assumption) hb⟩
  · obtain ⟨i, hi⟩ := C.idempotent_projection hand hor hmajority hminority hn hf
      (fun b => by cases b <;> assumption)
    exact ⟨i, id, hi⟩
  · have hd (b : Bool) : f (fun _ => b) = !b := by cases b <;> assumption
    have hcomp := C.comp (by decide) hn (C.diagonal hn hf) (fun _ : Fin 1 => hf)
    have hneg : (fun a => !(f a)) ∈ C.operations n := by
      simpa only [hd] using hcomp
    have hnegid (b : Bool) : (!(f (fun _ => b))) = b := by rw [hd]; cases b <;> rfl
    obtain ⟨i, hi⟩ := C.idempotent_projection hand hor hmajority hminority hn hneg hnegid
    refine ⟨i, Bool.not, fun a => ?_⟩
    have he := congrArg Bool.not (hi a)
    simpa only [Bool.not_not] using he
  · exact ⟨⟨0, hn⟩, fun _ => true,
      constant_of_binaryMinors (fun c => by cases c <;> assumption) hb⟩

/-- A positive-arity Boolean clone either has only essentially unary operations or contains
AND, OR, majority or minority. This does not assume Post's or a minimal-clone classification. -/
theorem classification :
    (∀ n, 0 < n → ∀ f ∈ C.operations n, EssentiallyUnary f) ∨
      andOp ∈ C.operations 2 ∨ orOp ∈ C.operations 2 ∨
      Cslib.majority 3 ∈ C.operations 3 ∨ Cslib.parity 3 ∈ C.operations 3 := by
  classical
  by_cases hand : andOp ∈ C.operations 2
  · exact Or.inr (Or.inl hand)
  by_cases hor : orOp ∈ C.operations 2
  · exact Or.inr (Or.inr (Or.inl hor))
  by_cases hmajority : Cslib.majority 3 ∈ C.operations 3
  · exact Or.inr (Or.inr (Or.inr (Or.inl hmajority)))
  by_cases hminority : Cslib.parity 3 ∈ C.operations 3
  · exact Or.inr (Or.inr (Or.inr (Or.inr hminority)))
  exact Or.inl fun _ hn _ hf =>
    C.essentiallyUnary_of_missing_generators hand hor hmajority hminority hn hf

end BooleanClone
end Cslib.Logic
