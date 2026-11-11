/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser.State
public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperserCore.Operations

/-!
# Restrictions on `3.5n` gate-elimination states

Specialization of `Cslib.Circuits.Boolean.AffineDisperserCore` restrictions `(UF)` and `(PF)`
to `3.5n` states with `PairTame` parameter-map invariants (`State.RestrictOK`,
`State.Valid.restrict`).

## Main definitions

* `Cslib.Circuits.Boolean.AffineDisperser.State.RestrictOK`: hypotheses for restrictions preserving
  `PairTame` affinity.

## Main results

* `Cslib.Circuits.Boolean.AffineDisperser.State.Valid.restrict`: restrictions preserve validity.
-/

public section

namespace Cslib.Circuits.Boolean.AffineDisperser

open Finset Cslib.BitString SemiCircuit AffineDisperserCore

namespace State

open AffineDisperserCore.State

variable {n : ℕ} {f : BooleanFunction n}

/-! ### Restrictions -/

/-- The hypotheses of a restriction: `x` is a parameter, `ℓ` reads at most another parameter,
kept pairs avoid `x`, and every dropped pair contains `x` together with the parameter (if any) read
by `ℓ`. -/
structure RestrictOK (S : State n) (x : ℕ) (ℓ : Lit) (P : Finset (ℕ × ℕ)) : Prop where
  /-- `x` is a parameter of `S`. -/
  mem : x ∈ S.params
  /-- Every variable read by `ℓ` is a parameter other than `x`. -/
  reads : ∀ y, ℓ.Reads y → y ∈ S.params ∧ y ≠ x
  /-- Kept pairs come from `S.pairs`. -/
  subset : P ⊆ S.pairs
  /-- Kept pairs do not contain `x`. -/
  avoid : ∀ pr ∈ P, pr.1 ≠ x ∧ pr.2 ≠ x
  /-- Dropped pairs contain `x` and any variable read by `ℓ`. -/
  drop : ∀ pr ∈ S.pairs, pr ∉ P → (pr.1 = x ∨ pr.2 = x) ∧ ∀ y, ℓ.Reads y → y = pr.1 ∨ y = pr.2

/-- Along an affine family on which the kept pairs are tame, the restricted family is affine
and every pair is tame: a dropped pair has a constant member, or a constant sum when `x` is
restricted to a literal of its partner. -/
theorem RestrictOK.pairTame {S : State n} {x : ℕ} {ℓ : Lit} {P : Finset (ℕ × ℕ)}
    (h : S.RestrictOK x ℓ P) {k : ℕ} {τ : BitString k → ℕ → Bool}
    (htame : ∀ pr ∈ P, PairTame τ pr) :
    ∀ pr ∈ S.pairs, PairTame (fun u => Function.update (τ u) x (ℓ.eval (τ u))) pr := by
  intro pr hpr
  by_cases hP : pr ∈ P
  · have hav := h.avoid pr hP
    rcases htame pr hP with ht | ht | ht
    · exact Or.inl fun u v => by simpa only [Function.update_of_ne hav.1] using ht u v
    · exact Or.inr (Or.inl fun u v => by simpa only [Function.update_of_ne hav.2] using ht u v)
    · exact Or.inr (Or.inr fun u v => by
        simpa only [Function.update_of_ne hav.1, Function.update_of_ne hav.2] using ht u v)
  · obtain ⟨hx, hy⟩ := h.drop pr hpr hP
    obtain ⟨p1, p2⟩ := pr
    obtain ⟨_ | t, c⟩ := ℓ
    · simp only at hx
      rcases hx with rfl | rfl
      · exact Or.inl fun u v => by simp only [Function.update_self, Lit.eval, Arg.eval_const]
      · exact Or.inr (Or.inl fun u v => by
          simp only [Function.update_self, Lit.eval, Arg.eval_const])
    · have ht := hy t rfl
      have htx : t ≠ x := (h.reads t rfl).2
      refine Or.inr (Or.inr fun u v => ?_)
      simp only at hx ht ⊢
      rcases hx with rfl | rfl <;> rcases ht with rfl | rfl
      · exact absurd rfl htx
      · simp only [Function.update_self, Function.update_of_ne htx, Lit.eval, Arg.eval_node]
        cases τ u t <;> cases τ v t <;> cases c <;> rfl
      · simp only [Function.update_self, Function.update_of_ne htx, Lit.eval, Arg.eval_node]
        cases τ u t <;> cases τ v t <;> cases c <;> rfl
      · exact absurd rfl htx

/-- Restrictions preserve validity. -/
theorem Valid.restrict {S : State n} (hS : S.Valid f) {x : ℕ} {ℓ : Lit} {P : Finset (ℕ × ℕ)}
    (h : S.RestrictOK x ℓ P) : (S.restrict x ℓ P).Valid f :=
  Valid.restrict_of hS h.mem h.reads h.subset
    (fun pr hpr hc => by
      have hav := h.avoid pr hpr
      rcases hc with hc | hc
      · exact hav.1 hc
      · exact hav.2 hc)
    (fun k τ hτ htame =>
      hS.phi_affine k (fun u => Function.update (τ u) x (ℓ.eval (τ u)))
        (isAffine_update hτ x (isAffine_lit_eval hτ ℓ)) (h.pairTame htame))
    fun _ _ => trivial

end State

end Cslib.Circuits.Boolean.AffineDisperser
