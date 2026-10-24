/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Arithmetic.VP
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure

/-!
# Valiant's class VNP and VNP-completeness

Valiant's algebraic analogue of `NP` [Valiant1979Algebra], in the form of
[Bürgisser, Chapter 2][Burgisser2000]. A family `f` is in `VNP K` when it is *p-definable*: there
are a polynomially bounded `m` and a family `g` in `VP K` such that

`f n (X) = ∑ e ∈ {0, 1} ^ m n, g n (X, e)`,

the `m n` variables of `g n` after the first `f.vars n` being replaced by `0` or `1`
(`Cslib.Circuits.Arithmetic.booleanSum`). The number of variables and the degree of `g`, and
hence of `f`, are polynomially bounded, and `g` has polynomial-size circuits; as for `VP`, nothing
relates different `n`, so `VNP` is nonuniform. The definition makes sense over every commutative
semiring `K`.

A family is *VNP-complete* when it lies in `VNP K` and every family in `VNP K` is a p-projection of
it. A VNP-complete family is in `VP` exactly when `VNP ⊆ VP`. Valiant's theorem that the permanent
is VNP-complete over fields of characteristic other than two is not proved here.

## Main definitions

* `Cslib.Circuits.Arithmetic.booleanAssignment`, `Cslib.Circuits.Arithmetic.booleanSum`: Boolean
  values for the last variables, and the sum over all of them.
* `Cslib.Circuits.Arithmetic.VNP`: Valiant's class `VNP`.
* `Cslib.Circuits.Arithmetic.IsVNPComplete`: VNP-completeness under p-projections.

## Main results

* `Cslib.Circuits.Arithmetic.VP_subset_VNP`: `VP ⊆ VNP`.
* `Cslib.Circuits.Arithmetic.VNP.isPFamily`: members of `VNP` are p-families.
* `Cslib.Circuits.Arithmetic.VNP.of_isPProjection`: `VNP` is closed under p-projections.
* `Cslib.Circuits.Arithmetic.IsVNPComplete.mem_VP_iff`: a VNP-complete family is in `VP` exactly
  when `VNP ⊆ VP`.

## References

* [L. G. Valiant, *Completeness classes in algebra*][Valiant1979Algebra]
* [P. Bürgisser, *Completeness and Reduction in Algebraic Complexity Theory*][Burgisser2000],
  Chapter 2
-/

@[expose] public section

namespace Cslib.Circuits.Arithmetic

open MvPolynomial

universe u

variable {K : Type u} [CommSemiring K] {n m k : ℕ}

/-- Keep the first `n` variables and substitute the Boolean value `e i`, as `0` or `1`, for
variable `n + i`. -/
def booleanAssignment (e : Fin m → Bool) : Fin (n + m) → Fin n ⊕ K :=
  Fin.append Sum.inl fun i => Sum.inr (bif e i then 1 else 0)

/-- The Boolean sum `∑ e ∈ {0, 1} ^ m, P (X, e)`: the sum, over all Boolean values for the last
`m` variables, of the polynomial in the first `n` variables obtained by substituting them. -/
noncomputable def booleanSum (m : ℕ) (P : MvPolynomial (Fin (n + m)) K) :
    MvPolynomial (Fin n) K :=
  ∑ e : Fin m → Bool, projection (booleanAssignment e) P

/-- A Boolean sum over no variables is the polynomial itself. -/
@[simp] theorem booleanSum_zero (P : MvPolynomial (Fin (n + 0)) K) : booleanSum 0 P = P := by
  have h (e : Fin 0 → Bool) : (booleanAssignment e : Fin (n + 0) → Fin n ⊕ K) = Sum.inl := by
    rw [booleanAssignment, Fin.append_right_nil _ _ rfl]
    rfl
  rw [booleanSum, Fintype.sum_unique, h, projection_inl]
  rfl

/-- Lift a projection of the first `k` of `k + m` variables to all of them, keeping the last `m`
variables. -/
private def liftProjection (ρ : Fin k → Fin n ⊕ K) : Fin (k + m) → Fin (n + m) ⊕ K :=
  Fin.append (fun i => (ρ i).map (Fin.castAdd m) id) fun i => Sum.inl (Fin.natAdd n i)

/-- A projection of a Boolean sum is the Boolean sum of a projection: substitution for the first
variables commutes with summing over the last. -/
private theorem projection_booleanSum (ρ : Fin k → Fin n ⊕ K) (P : MvPolynomial (Fin (k + m)) K) :
    projection ρ (booleanSum m P) = booleanSum m (projection (liftProjection ρ) P) := by
  rw [booleanSum, booleanSum, map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [projection_projection, projection_projection]
  congr 2
  funext i
  induction i using Fin.addCases with
  | left i =>
    rcases h : ρ i with j | a <;>
      simp [booleanAssignment, liftProjection, h]
  | right i => cases e i <;> simp [booleanAssignment, liftProjection]

/-- A Boolean sum has no larger degree than the summed polynomial. -/
private theorem totalDegree_booleanSum_le (P : MvPolynomial (Fin (n + m)) K) :
    (booleanSum m P).totalDegree ≤ P.totalDegree :=
  totalDegree_finsetSum_le fun _ _ => totalDegree_projection_le _ _

/-- Valiant's class `VNP` over `K` [Valiant1979Algebra; Bürgisser, Chapter 2][Burgisser2000]: the
families `f` with `f n = booleanSum (m n) (g n)` for a family `g` in `VP K` whose members have
`f.vars n + m n` variables. The class is nonuniform, like `VP`. -/
def VNP (K : Type u) [CommSemiring K] : Set (PolynomialFamily K) :=
  {f | ∃ (m : ℕ → ℕ) (g : ∀ n, MvPolynomial (Fin (f.vars n + m n)) K),
    (⟨fun n => f.vars n + m n, g⟩ : PolynomialFamily K) ∈ VP K ∧
      ∀ n, f.poly n = booleanSum (m n) (g n)}

/-- Every family in `VP` is in `VNP`, summing over no variables. -/
theorem VP_subset_VNP : VP K ⊆ VNP K := fun f hf =>
  ⟨fun _ => 0, f.poly, hf, fun n => (booleanSum_zero (f.poly n)).symm⟩

/-- The members of `VNP` are p-families. -/
theorem VNP.isPFamily {f : PolynomialFamily K} (hf : f ∈ VNP K) : f.IsPFamily := by
  obtain ⟨m, g, ⟨⟨hvars, hdeg⟩, -⟩, hfg⟩ := hf
  refine ⟨hvars.mono_of_le fun n => Nat.le_add_right _ _, hdeg.mono_of_le fun n => ?_⟩
  rw [hfg n]
  exact totalDegree_booleanSum_le _

/-- `VNP` is closed under p-projections [Bürgisser, Chapter 2][Burgisser2000]. As for `VP`, the
number of variables is required to be polynomially bounded. -/
theorem VNP.of_isPProjection {f g : PolynomialFamily K} (hg : g ∈ VNP K)
    (hfg : f.IsPProjection g) (hvars : PolynomiallyBounded f.vars) : f ∈ VNP K := by
  obtain ⟨m, h, hh, hgh⟩ := hg
  obtain ⟨t, ht, hproj⟩ := hfg
  choose ρ hρ using hproj
  have hm : PolynomiallyBounded m := (VP.isPFamily hh).1.mono_of_le fun n => Nat.le_add_left _ _
  refine ⟨fun n => m (t n), fun n => projection (liftProjection (ρ n)) (h (t n)),
    VP.of_isPProjection hh ⟨t, ht, fun n => ⟨_, rfl⟩⟩ (hvars.add (hm.comp ht)), fun n => ?_⟩
  rw [← hρ n, hgh, projection_booleanSum]

/-- A family is *VNP-complete* over `K` [Valiant1979Algebra; Bürgisser, Chapter 2][Burgisser2000]
when it is in `VNP K` and every family in `VNP K` is a p-projection of it. -/
def IsVNPComplete (f : PolynomialFamily K) : Prop :=
  f ∈ VNP K ∧ ∀ g ∈ VNP K, g.IsPProjection f

/-- If a VNP-complete family is in `VP`, then `VNP ⊆ VP`. -/
theorem IsVNPComplete.VNP_subset_VP {f : PolynomialFamily K} (hf : IsVNPComplete f)
    (hVP : f ∈ VP K) : VNP K ⊆ VP K := fun g hg =>
  VP.of_isPProjection hVP (hf.2 g hg) (VNP.isPFamily hg).1

/-- A VNP-complete family is in `VP` exactly when `VNP ⊆ VP`: Valiant's hypothesis `VP ≠ VNP`
says that no VNP-complete family has polynomial-size circuits. -/
theorem IsVNPComplete.mem_VP_iff {f : PolynomialFamily K} (hf : IsVNPComplete f) :
    f ∈ VP K ↔ VNP K ⊆ VP K :=
  ⟨hf.VNP_subset_VP, fun h => h hf.1⟩

end Cslib.Circuits.Arithmetic
