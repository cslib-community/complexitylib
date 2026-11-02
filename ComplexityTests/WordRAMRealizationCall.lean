/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (realize certificate-call regression tests)

public import Complexity.Tactic.Realize

/-!
# Calls to separately certified memory methods

The methods are parameters, so their implementations cannot be unfolded. Calls select existing
live words, may alias inputs, and carry their method domain to the reached memory. Argument
computation requires an explicit, charged glue step.
-/

public section

namespace Cslib.WordRAM.Realization.Tests.Call

open Cslib.DataStructure

private abbrev word : ℕ ↪ (Fin 1 → ℕ) := (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding
private abbrev pairWords : ℕ × ℕ ↪ (Fin 2 → ℕ) := appendWords word word
private abbrev unitWords : Unit ↪ (Fin 0 → ℕ) := (Equiv.ofUnique Unit (Fin 0 → ℕ)).toEmbedding

-- A separately certified method consumes a projection of a larger live environment.
theorem projection_call (m : ℕ → Memory.Prog ℕ) (P : ℕ → ℕ → Memory.State → Prop)
    (hm : Realizes .exact m (WordEncoding.encode (α := ℕ)) (WordEncoding.encode (α := ℕ))
      P (fun _ _ => 0)) :
    Realizes .exact (fun d : ℕ × ℕ => m d.2) (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ)) (fun w d s => P w d.2 s) (fun _ _ => 0) := by
  realize
  exact h

-- Input registers need not be distinct: the existing reindex rule permits aliasing.
example (m : ℕ × ℕ → Memory.Prog ℕ) (P : ℕ → ℕ × ℕ → Memory.State → Prop)
    (hm : Realizes .exact m pairWords word P (fun _ _ => 0)) :
    Realizes .exact (fun d : ℕ => m (d, d)) word word
      (fun w d s => P w (d, d) s) (fun _ _ => 0) := by
  realize
  exact h

-- The returned word is live in the continuation, without revealing the method body.
example (m : ℕ → Memory.Prog ℕ) (P : ℕ → ℕ → Memory.State → Prop)
    (hm : Realizes .exact m word word P (fun _ _ => 0)) :
    Realizes .exact (fun d : ℕ × ℕ => do
      let a ← m d.1
      Memory.write d.2 a) pairWords unitWords
      (fun w d s => P w d.1 s) (fun _ _ => 0) := by
  realize
  exact h

-- A call's domain is required at the actual state reached after a write.
example (m : ℕ → Memory.Prog ℕ) (P : ℕ → ℕ → Memory.State → Prop)
    (hm : Realizes .exact m word word P (fun _ _ => 0)) :
    Realizes .exact (fun d : ℕ × ℕ => do
      Memory.write d.1 d.2
      m d.2) pairWords word
      (fun w d s => P w d.2 ⟨Function.update s.mem d.1 d.2, s.frontier⟩)
      (fun _ _ => 0) := by
  realize
  exact h

-- An arithmetic argument cannot be passed by free static rewiring.
example (m : ℕ → Memory.Prog ℕ)
    (_hm : Realizes .exact m word word (fun _ _ _ => True) (fun _ _ => 0)) : True := by
  fail_if_success
    have _ : Realizes .exact (fun d : ℕ => m (d + 1)) word word
        (fun _ _ _ => True) (fun _ _ => 0) := by realize
  trivial

-- Its explicit pure step is certified glue; the fitting arithmetic result stays visible.
example (m : ℕ → Memory.Prog ℕ) (P : ℕ → ℕ → Memory.State → Prop)
    (hm : Realizes .exact m word word P (fun _ _ => 0)) :
    Realizes .exact (fun d : ℕ => do
      let a ← pure (d + 1)
      m a) word word
      (fun w d s => Fits w (d + 1) ∧ P w (d + 1) s) (fun _ _ => 0) := by
  realize <;> first | exact h.1 | exact h.2

end Cslib.WordRAM.Realization.Tests.Call
