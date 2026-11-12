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

/-- Strengthen safety and compare local work under the requested entry domain and the client's
valid history. The emitter, scratch size, exchange factor and width freedom are unchanged. -/
theorem Realizes.consequence_work (h : Realizes B p input output safe work)
    (hsafe : ∀ w d s, (∀ i, Fits w (input d i)) → Memory.WellFormed w s →
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p d)) →
      safe' w d s → safe w d s)
    (hwork : ∀ w d s, (∀ i, Fits w (input d i)) → Memory.WellFormed w s →
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p d)) →
      safe' w d s → work d s ≤ work' d s) : Realizes B p input output safe' work' := by
  obtain ⟨n, C, emit, he⟩ := h
  refine ⟨n, C, emit, fun frontier src tmp hi hd hf hs => ?_⟩
  obtain ⟨hnw, hrun⟩ := he frontier src tmp hi hd hf hs
  refine ⟨hnw, fun w d x hx hin hsafe' hv => ?_⟩
  have hwords (i : Fin k) : Fits w (input d i) := congrFun hin i ▸ hx.1 (src i)
  have hmem := wellFormed_memoryState (frontier := frontier) hx
  obtain ⟨y, hy, hm, hout, hframe⟩ :=
    hrun w d x hx hin (hsafe w d _ hwords hmem hv hsafe') hv
  have hw := hwork w d _ hwords hmem hv hsafe'
  exact ⟨y, hy.mono (Nat.mul_le_mul_left C (by omega)), hm, hout, hframe⟩

/-- Strengthen safety and compare local work under the requested entry domain and valid history,
retaining frontier-bounded accesses and all of the original witness resources. -/
theorem RealizesBounded.consequence_work (h : RealizesBounded B p input output safe work)
    (hsafe : ∀ w d s, (∀ i, Fits w (input d i)) → Memory.WellFormed w s →
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p d)) →
      safe' w d s → safe w d s)
    (hwork : ∀ w d s, (∀ i, Fits w (input d i)) → Memory.WellFormed w s →
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p d)) →
      safe' w d s → work d s ≤ work' d s) : RealizesBounded B p input output safe' work' := by
  obtain ⟨n, C, emit, he⟩ := h
  refine ⟨n, C, emit, fun frontier src tmp hi hd hf hs => ?_⟩
  obtain ⟨hnw, hrun⟩ := he frontier src tmp hi hd hf hs
  refine ⟨hnw, fun w d x hx hin hsafe' hv => ?_⟩
  have hwords (i : Fin k) : Fits w (input d i) := congrFun hin i ▸ hx.1 (src i)
  have hmem := wellFormed_memoryState (frontier := frontier) hx
  obtain ⟨y, hy, hm, hout, hframe⟩ :=
    hrun w d x hx hin (hsafe w d _ hwords hmem hv hsafe') hv
  have hw := hwork w d _ hwords hmem hv hsafe'
  exact ⟨y, hy.mono (Nat.mul_le_mul_left C (by omega)), hm, hout, hframe⟩

end Cslib.WordRAM.Realization
