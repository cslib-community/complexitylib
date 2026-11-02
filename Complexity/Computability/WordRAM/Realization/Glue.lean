/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Realization.Basic
public import Complexity.Computability.WordRAM.Glue

/-!
# Certified local computation in memory clients

The source computation is an ordinary `pure` in `Memory.Prog`, but its native cost is the
certified word-glue budget. The input domain and top-level fit envelope remain visible.
Uniform emitter witnesses are chosen before the runtime environment, width or memory, including
when this rule supplies the continuation of a previous memory read.

## Main results

* `Realizes.glue`: reuse a `GlueComputes` emitter, preserving the entire memory and frontier.
-/

@[expose] public section

namespace Cslib.WordRAM.Realization.Realizes

open Cslib.DataStructure

variable {B : Basis} {δ : Type} {k : ℕ} {P : (Fin k → ℕ) → Prop}
  {f bound : (Fin k → ℕ) → ℕ} {time : ℕ}

private def glueSlot {n : ℕ} (j : Fin (n + 1)) : Fin (1 + n + 1) := ⟨j.val, by omega⟩

/-- Certified scalar computation returns its word, frames memory/frontier/live registers, and
charges its instruction budget even though its source memory-operation history is empty. -/
theorem glue (input : δ ↪ (Fin k → ℕ)) (h : GlueComputes B P f bound time) :
    Realizes B (fun d => pure (f (input d))) input
      (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding
      (fun w d _ => P (input d) ∧ Fits w (bound (input d))) (fun _ _ => time) := by
  obtain ⟨_, n, emit, he⟩ := h
  refine ⟨n, 1, fun _ src tmp => emit src (fun j => tmp (glueSlot j)), ?_⟩
  intro r frontier src tmp hi hd hf hs
  have htmp : Function.Injective (fun j : Fin (n + 1) => tmp (glueSlot j)) := by
    intro a b h
    apply Fin.ext
    exact congrArg (fun z : Fin (1 + n + 1) => z.val) (hi h)
  obtain ⟨hg, hrun⟩ := he src (fun j => tmp (glueSlot j)) htmp
    (fun i j => hd i (glueSlot j))
  refine ⟨hg.not_readsWidth, ?_⟩
  intro w d x hx hin hsafe hv
  obtain ⟨y, hy, hout, hm, hframe⟩ := hrun w x (hin.symm ▸ hsafe.1) (hin.symm ▸ hsafe.2)
  refine ⟨y, hy.mono (by change time ≤ 1 * (0 + time + 1); omega), ?_, ?_, ?_⟩
  · apply Memory.State.ext
    · exact hm
    · exact hframe frontier (fun j => hf (glueSlot j))
  · intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    change y.regs (tmp 0) = f (input d)
    have hzero : glueSlot (0 : Fin (n + 1)) = 0 := by
      apply Fin.ext
      simp [glueSlot]
    simpa only [hzero, hin] using hout
  · intro i hif htmp
    exact hframe i (fun j => htmp (glueSlot j))

end Cslib.WordRAM.Realization.Realizes
