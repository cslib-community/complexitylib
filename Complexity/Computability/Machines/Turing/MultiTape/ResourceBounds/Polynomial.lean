/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate (independent polynomial-growth algebra)
-- Moved unchanged from Complexity/PolyTime; retain this home when resynchronizing vendored rules.

public import Complexity.Foundations.Data.Nat.PolynomialBound.Closure

/-! Polynomial growth relative to an arbitrary input-size function, without machine predicates. -/

namespace Turing.MultiTapeTM

/-! ### Polynomial bounds -/

-- vendored: express size-dependent bounds through cslib's `PolynomiallyBounded` and reuse
-- its closure rules; `exists_le` and `of_forall_le` preserve the original explicit-bound contract.
/-- `u` is bounded by a polynomially bounded function of `size`. This adapts
`Cslib.PolynomiallyBounded` to arbitrary inputs; it does not assert computability. -/
@[expose] public def PolyBounded {α : Type*} (size u : α → ℕ) : Prop :=
  ∃ bound : ℕ → ℕ, Cslib.PolynomiallyBounded bound ∧ ∀ a, u a ≤ bound (size a)

namespace PolyBounded

variable {α β : Type*} {size : α → ℕ} {u v : α → ℕ}

/-- Recover an explicit polynomial bound valid at every input, including size zero. -/
public theorem exists_le (h : PolyBounded size u) :
    ∃ c d, ∀ a, u a ≤ c * (size a + 1) ^ d := by
  obtain ⟨bound, hbound, h⟩ := h
  obtain ⟨c, d, hp⟩ := Cslib.polynomiallyBounded_iff_le.mp hbound
  exact ⟨c, d, fun a => (h a).trans (hp (size a))⟩

/-- Supply an explicit polynomial bound in the input size. -/
public theorem of_forall_le (c d : ℕ) (h : ∀ a, u a ≤ c * (size a + 1) ^ d) :
    PolyBounded size u :=
  ⟨_, Cslib.PolynomiallyBounded.of_forall_le c d (fun _ => le_rfl), h⟩

/-- Apply a polynomial bound to any input-size function. -/
public theorem of_polynomiallyBounded (size : α → ℕ) {bound : ℕ → ℕ}
    (hbound : Cslib.PolynomiallyBounded bound) : PolyBounded size (fun a => bound (size a)) :=
  ⟨bound, hbound, fun _ => le_rfl⟩

/-- With the identity size, the adapter gives CSLib's polynomial-growth predicate. -/
public theorem polynomiallyBounded {f : ℕ → ℕ} (h : PolyBounded id f) :
    Cslib.PolynomiallyBounded f :=
  let ⟨_, hbound, h⟩ := h
  hbound.mono_of_le h

public theorem mono (h : PolyBounded size v) (huv : ∀ a, u a ≤ v a) : PolyBounded size u :=
  let ⟨bound, hbound, hv⟩ := h
  ⟨bound, hbound, fun a => (huv a).trans (hv a)⟩

public theorem const (k : ℕ) : PolyBounded size fun _ => k :=
  of_polynomiallyBounded size (.const k)

public theorem self : PolyBounded size size :=
  of_polynomiallyBounded size .id

public theorem add (hu : PolyBounded size u) (hv : PolyBounded size v) :
    PolyBounded size fun a => u a + v a :=
  let ⟨_, hp, hu⟩ := hu
  let ⟨_, hq, hv⟩ := hv
  ⟨_, hp.add hq, fun a => Nat.add_le_add (hu a) (hv a)⟩

public theorem mul (hu : PolyBounded size u) (hv : PolyBounded size v) :
    PolyBounded size fun a => u a * v a :=
  let ⟨_, hp, hu⟩ := hu
  let ⟨_, hq, hv⟩ := hv
  ⟨_, hp.mul hq, fun a => Nat.mul_le_mul (hu a) (hv a)⟩

public theorem pow (hu : PolyBounded size u) (d : ℕ) :
    PolyBounded size fun a => u a ^ d :=
  let ⟨_, hp, hu⟩ := hu
  ⟨_, hp.pow d, fun a => Nat.pow_le_pow_left (hu a) d⟩

/-- Substitution: if `v` is bounded by a polynomial in `size'` and `size' ∘ g` by a polynomial in
`size`, then `v ∘ g` is bounded by a polynomial in `size`. -/
public theorem comp {size' : β → ℕ} {v : β → ℕ} {g : α → β} (hv : PolyBounded size' v)
    (hg : PolyBounded size fun a => size' (g a)) : PolyBounded size fun a => v (g a) := by
  obtain ⟨c, d, hv⟩ := hv.exists_le
  obtain ⟨bound, hbound, hg⟩ := hg
  refine ⟨fun n => c * (bound n + 1) ^ d, by fun_prop, fun a => ?_⟩
  exact (hv (g a)).trans (Nat.mul_le_mul_left c
    (Nat.pow_le_pow_left (Nat.add_le_add_right (hg a) 1) d))

end PolyBounded

end Turing.MultiTapeTM
