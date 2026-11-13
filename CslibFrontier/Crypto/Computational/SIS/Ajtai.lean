/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SIS.Basic
import CslibFrontier.Probability.PMF.Bind

/-!
# Ajtai's hash function and collision finding

Ajtai's function `ajtaiHash A x = A x mod q` ([Ajtai1996]) on integer vectors is linear, so two
distinct inputs with the same hash differ by a nonzero kernel vector of `A`. When both inputs lie
in `[0, β]^m` the difference is a short integer solution with bound `β`
(`IsAjtaiCollision.isSolution_sub`); when both lie in `[-β, β]^m` it is one with bound `2 * β`
(`isSolution_sub_of_abs_le`). No primality assumption on `q` is needed.

`ajtaiCollisionExperiment q β F` draws a uniform `A ∈ ℤ_q^{n×m}`, and the finder `F` wins when it
returns a collision in `[0, β]^m`. The SIS solver `collisionToSIS F` returns the difference of
`F`'s pair, and `ajtaiAdvantage_le_sisAdvantage` bounds the collision-finding advantage by its SIS
advantage for every modulus, dimension, bound and finder. The reduction adds one vector
subtraction, so it preserves efficiency; this module states no asymptotic form.

## Main definitions

* `Cslib.Crypto.ajtaiHash`: Ajtai's linear hash function.
* `Cslib.Crypto.IsAjtaiCollision`: a collision in `[0, β]^m`.
* `Cslib.Crypto.ajtaiCollisionExperiment`, `Cslib.Crypto.ajtaiAdvantage`: the collision-finding
  experiment and its success probability.
* `Cslib.Crypto.collisionToSIS`: the SIS solver built from a collision finder.

## Main results

* `Cslib.Crypto.IsAjtaiCollision.isSolution_sub`, `Cslib.Crypto.isSolution_sub_of_abs_le`:
  collisions give short integer solutions.
* `Cslib.Crypto.ajtaiAdvantage_le_sisAdvantage`: collision finding reduces to SIS.

## References

* [M. Ajtai, *Generating Hard Instances of Lattice Problems*][Ajtai1996]
-/

@[expose] public section

namespace Cslib.Crypto

open Probability
open scoped _root_.Matrix NNReal

variable {n m q : ℕ}

/-- Ajtai's linear hash function `x ↦ A x mod q` on integer vectors ([Ajtai1996]). -/
def ajtaiHash (A : Matrix (Fin n) (Fin m) (ZMod q)) (x : Fin m → ℤ) : Fin n → ZMod q :=
  A *ᵥ (Int.cast ∘ x)

/-- Ajtai's hash function is additive. -/
theorem ajtaiHash_sub (A : Matrix (Fin n) (Fin m) (ZMod q)) (x y : Fin m → ℤ) :
    ajtaiHash A (x - y) = ajtaiHash A x - ajtaiHash A y := by
  rw [ajtaiHash, ajtaiHash, ajtaiHash, ← Matrix.mulVec_sub]
  congr 1
  funext i
  exact Int.cast_sub (x i) (y i)

/-- Distinct inputs in `[-β, β]^m` with the same Ajtai hash differ by a short integer solution
with bound `2 * β`. -/
theorem isSolution_sub_of_abs_le {A : Matrix (Fin n) (Fin m) (ZMod q)} {β : ℕ}
    {x y : Fin m → ℤ} (hxy : x ≠ y) (hx : ∀ i, |x i| ≤ β) (hy : ∀ i, |y i| ≤ β)
    (h : ajtaiHash A x = ajtaiHash A y) :
    SIS.IsSolution A (2 * β) (x - y) := by
  refine ⟨sub_ne_zero.mpr hxy, fun i => ?_, ?_⟩
  · have hxi := abs_le.mp (hx i)
    have hyi := abs_le.mp (hy i)
    simp only [Pi.sub_apply, Nat.cast_mul, Nat.cast_ofNat, abs_le]
    omega
  · change ajtaiHash A (x - y) = 0
    rw [ajtaiHash_sub, h, sub_self]

/-- `(x, y)` is a collision of Ajtai's hash function for `A` in `[0, β]^m`: distinct inputs in
`[0, β]^m` with the same hash. -/
def IsAjtaiCollision (A : Matrix (Fin n) (Fin m) (ZMod q)) (β : ℕ) (x y : Fin m → ℤ) : Prop :=
  x ≠ y ∧ (∀ i, 0 ≤ x i ∧ x i ≤ β) ∧ (∀ i, 0 ≤ y i ∧ y i ≤ β) ∧
    ajtaiHash A x = ajtaiHash A y

instance (A : Matrix (Fin n) (Fin m) (ZMod q)) (β : ℕ) (x y : Fin m → ℤ) :
    Decidable (IsAjtaiCollision A β x y) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- A collision in `[0, β]^m` differs by a short integer solution with bound `β`. -/
theorem IsAjtaiCollision.isSolution_sub {A : Matrix (Fin n) (Fin m) (ZMod q)} {β : ℕ}
    {x y : Fin m → ℤ} (h : IsAjtaiCollision A β x y) : SIS.IsSolution A β (x - y) := by
  obtain ⟨hxy, hx, hy, hxy'⟩ := h
  refine ⟨sub_ne_zero.mpr hxy, fun i => ?_, ?_⟩
  · have hxi := hx i
    have hyi := hy i
    simp only [Pi.sub_apply, abs_le]
    omega
  · change ajtaiHash A (x - y) = 0
    rw [ajtaiHash_sub, hxy', sub_self]

/-- The SIS solver built from a collision finder: run the finder and return the difference of
its pair. -/
def collisionToSIS (F : Matrix (Fin n) (Fin m) (ZMod q) → ProbComp ((Fin m → ℤ) × (Fin m → ℤ)))
    (A : Matrix (Fin n) (Fin m) (ZMod q)) : ProbComp (Fin m → ℤ) := do
  let (x, y) ← F A
  return x - y

section Experiment

variable (q) [NeZero q]

/-- The Ajtai collision-finding experiment for modulus `q`, dimensions `n × m` and box
`[0, β]^m`: the challenger draws a uniform `A ∈ ℤ_q^{n×m}`; the finder wins when it returns a
collision of `ajtaiHash A` in the box. -/
noncomputable def ajtaiCollisionExperiment (β : ℕ)
    (F : Matrix (Fin n) (Fin m) (ZMod q) → ProbComp ((Fin m → ℤ) × (Fin m → ℤ))) :
    ProbComp Bool := do
  let A ← ProbComp.uniform (Matrix (Fin n) (Fin m) (ZMod q))
  let (x, y) ← F A
  return decide (IsAjtaiCollision A β x y)

/-- The collision-finding advantage of `F`: its success probability in
`ajtaiCollisionExperiment`. -/
noncomputable def ajtaiAdvantage (β : ℕ)
    (F : Matrix (Fin n) (Fin m) (ZMod q) → ProbComp ((Fin m → ℤ) × (Fin m → ℤ))) : ℝ≥0 :=
  Game.succProbability (ProbComp.eval (ajtaiCollisionExperiment q β F))

/-- **Collision finding reduces to SIS** ([Ajtai1996]): every collision finder's advantage is at
most the SIS advantage of `collisionToSIS`, for every nonzero modulus. -/
theorem ajtaiAdvantage_le_sisAdvantage (β : ℕ)
    (F : Matrix (Fin n) (Fin m) (ZMod q) → ProbComp ((Fin m → ℤ) × (Fin m → ℤ))) :
    ajtaiAdvantage q β F ≤ sisAdvantage q β (collisionToSIS F) := by
  refine ENNReal.toNNReal_mono (PMF.apply_ne_top _ _) ?_
  simp only [ajtaiCollisionExperiment, sisExperiment, collisionToSIS, bind_assoc,
    ProbComp.eval_bind]
  refine PMF.bind_apply_mono_on_support _ _ fun A _ => ?_
  refine PMF.bind_apply_mono_on_support _ _ fun ⟨x, y⟩ _ => ?_
  by_cases h : IsAjtaiCollision A β x y
  · simp [h, h.isSolution_sub]
  · simp [h]

end Experiment

end Cslib.Crypto
