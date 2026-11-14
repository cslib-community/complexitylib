/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Realization.Basic

/-!
# Work bounds under the entry contract

A requested entry domain, fitting input words, well-formed memory and the client's valid history
may justify both its safety conditions and its local-work bound. These consequence rules keep
the original emitter, scratch bank and exchange factor. They change neither the program nor its
whole-memory and register-frame guarantees, and introduce no new execution model.

## Main results

* `Realizes.SpecWith.consequence_work`, `Realizes.With.consequence_work`: compare work under the
  requested entry contract for any monotonic execution judgment.
* `Realizes.consequence_work`: compare work under the requested entry contract.
* `RealizesBounded.consequence_work`: the same rule retaining frontier-bounded accesses.

The rules are original infrastructure over the existing realization contracts.
-/

public section

namespace Cslib.WordRAM.Realization

open Cslib.DataStructure

variable {B : Basis} {δ α : Type} {k l : ℕ}
  {p : δ → Memory.Prog α} {input : δ ↪ (Fin k → ℕ)} {output : α ↪ (Fin l → ℕ)}
  {safe safe' : ℕ → δ → Memory.State → Prop} {work work' : δ → Memory.State → ℕ}

/-- Strengthen safety and compare local work under the requested entry domain and admissible client
history for a `Realizes.SpecWith` contract over a monotonic execution judgment. -/
theorem Realizes.SpecWith.consequence_work
    {exec : ∀ {r : ℕ}, ℕ → Fin r → Code B r → Data r → Data r → ℕ → Prop}
    {n C : ℕ} {emit : ∀ {r : ℕ}, (frontier : Fin r) → (Fin k → Fin r) →
      (Fin (l + n + 1) → Fin r) → Code B r}
    (he : Realizes.SpecWith B exec p input output safe work n C emit)
    (hmono : ∀ {r : ℕ} {w : ℕ} {frontier : Fin r} {c : Code B r} {x y : Data r} {T₁ T₂ : ℕ},
      T₁ ≤ T₂ → exec w frontier c x y T₁ → exec w frontier c x y T₂)
    (hsafe : ∀ w d s, (∀ i, Fits w (input d i)) → Memory.WellFormed w s →
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p d)) →
      safe' w d s → safe w d s)
    (hwork : ∀ w d s, (∀ i, Fits w (input d i)) → Memory.WellFormed w s →
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p d)) →
      safe' w d s → work d s ≤ work' d s) :
    Realizes.SpecWith B exec p input output safe' work' n C emit :=
  he.consequence_of hsafe fun {_ _ frontier _ x _ d} hwords hmem hv hs' hy =>
    hmono (Nat.mul_le_mul_left C (by have := hwork _ d _ hwords hmem hv hs'; omega)) hy

/-- Strengthen safety and compare local work under the requested entry domain and admissible client
history for a `Realizes.With` certificate over a monotonic execution judgment. -/
theorem Realizes.With.consequence_work
    {exec : ∀ {r : ℕ}, ℕ → Fin r → Code B r → Data r → Data r → ℕ → Prop}
    (h : Realizes.With B exec p input output safe work)
    (hmono : ∀ {r : ℕ} {w : ℕ} {frontier : Fin r} {c : Code B r} {x y : Data r} {T₁ T₂ : ℕ},
      T₁ ≤ T₂ → exec w frontier c x y T₁ → exec w frontier c x y T₂)
    (hsafe : ∀ w d s, (∀ i, Fits w (input d i)) → Memory.WellFormed w s →
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p d)) →
      safe' w d s → safe w d s)
    (hwork : ∀ w d s, (∀ i, Fits w (input d i)) → Memory.WellFormed w s →
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p d)) →
      safe' w d s → work d s ≤ work' d s) :
    Realizes.With B exec p input output safe' work' :=
  let ⟨n, C, emit, he⟩ := h
  ⟨n, C, emit, he.consequence_work hmono hsafe hwork⟩

/-- Strengthen safety and compare local work under the requested entry domain and the client's
valid history. The emitter, scratch size, exchange factor and width freedom are unchanged. -/
theorem Realizes.consequence_work (h : Realizes B p input output safe work)
    (hsafe : ∀ w d s, (∀ i, Fits w (input d i)) → Memory.WellFormed w s →
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p d)) →
      safe' w d s → safe w d s)
    (hwork : ∀ w d s, (∀ i, Fits w (input d i)) → Memory.WellFormed w s →
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p d)) →
      safe' w d s → work d s ≤ work' d s) : Realizes B p input output safe' work' :=
  Realizes.With.consequence_work h (fun hT h => h.mono hT) hsafe hwork

/-- Strengthen safety and compare local work under the requested entry domain and valid history,
retaining frontier-bounded accesses and all of the original witness resources. -/
theorem RealizesBounded.consequence_work (h : RealizesBounded B p input output safe work)
    (hsafe : ∀ w d s, (∀ i, Fits w (input d i)) → Memory.WellFormed w s →
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p d)) →
      safe' w d s → safe w d s)
    (hwork : ∀ w d s, (∀ i, Fits w (input d i)) → Memory.WellFormed w s →
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p d)) →
      safe' w d s → work d s ≤ work' d s) : RealizesBounded B p input output safe' work' :=
  Realizes.With.consequence_work h (fun hT h => h.mono hT) hsafe hwork

end Cslib.WordRAM.Realization
