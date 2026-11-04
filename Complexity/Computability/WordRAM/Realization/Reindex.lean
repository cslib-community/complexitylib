/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Realization.Basic

/-!
# Static live-register wiring

A realization may consume selected words of a larger faithful environment without executing
any computation. The equality of encoded inputs is explicit, and the register selection is
fixed before runtime. This supplies layout arguments and query replies to existing method
certificates while keeping other live words framed.

## Main results

* `Realizes.reindex`: pull a certificate back along a fixed register-index map.
-/

@[expose] public section

namespace Cslib.WordRAM.Realization.Realizes

open Cslib.DataStructure

variable {B : Basis} {ε δ α : Type} {k m l : ℕ}

/-- A fixed input-index map merely rewires registers. The semantic map must agree with that
wiring on every encoded input; no host computation or runtime choice of code is granted. -/
theorem reindex {p : δ → Memory.Prog α} {input : δ ↪ (Fin k → ℕ)}
    {output : α ↪ (Fin l → ℕ)} {safe : ℕ → δ → Memory.State → Prop}
    {work : δ → Memory.State → ℕ} (h : Realizes B p input output safe work)
    (f : ε → δ) (env : ε ↪ (Fin m → ℕ)) (ix : Fin k → Fin m)
    (hw : ∀ e i, input (f e) i = env e (ix i)) :
    Realizes B (fun e => p (f e)) env output
      (fun w e s => safe w (f e) s) (fun e s => work (f e) s) := by
  obtain ⟨n, C, emit, he⟩ := h
  refine ⟨n, C, fun frontier src tmp => emit frontier (src ∘ ix) tmp, ?_⟩
  intro r frontier src tmp hi hd hf hs
  obtain ⟨hnw, hrun⟩ := he frontier (src ∘ ix) tmp hi
    (fun i j => hd (ix i) j) hf (fun i => hs (ix i))
  refine ⟨hnw, ?_⟩
  intro w e x hx hin hsafe hv
  have hin' : x.regs ∘ (src ∘ ix) = input (f e) := by
    funext i
    exact (congrFun hin (ix i)).trans (hw e i).symm
  exact hrun w (f e) x hx hin' hsafe hv

end Cslib.WordRAM.Realization.Realizes
