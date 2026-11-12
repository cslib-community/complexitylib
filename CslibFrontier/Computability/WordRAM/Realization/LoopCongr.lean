/-
Copyright (c) 2026 Samuel Schlesinger, Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Realization.Loop

/-!
# Fixed-environment transport for bounded memory-client loops

Equal body programs at two fixed environments give equal bounded iterations. Pointwise equal
body-work charges and equivalent body domains likewise transport the iteration's work and safety
conditions along its actual reached memory states. These are semantic laws of the existing free
programs: they need no fit, history or resource assumptions.

## Main results

* `iterate_comap`: pull a loop body back along a map of its environment.
* `iterate_congr`: equal bodies at fixed environments give equal iterations.
* `iterationSafe_congr`: transport iteration domains between agreeing bodies and environments.
* `iterationWork_congr`: transport local work between agreeing bodies and environments.

The transport rules are original infrastructure over the existing memory-client loops.
-/

public section

namespace Cslib.WordRAM.Realization

open Cslib.DataStructure

variable {δ σ : Type}

/-- A loop may receive any function of its environment: it is the loop over the whole
environment whose body applies that function. -/
theorem iterate_comap {ε σ : Type} (g : ε → δ) (body : δ × σ → Memory.Prog σ) (e : ε) (n : ℕ)
    (a : σ) : iterate body (g e) n a = iterate (fun x : ε × σ => body (g x.1, x.2)) e n a := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => exact congrArg (fun k => (body (g e, a)).bind k) (funext ih)

/-- Equal body programs at fixed environments give equal bounded iterations, including their
complete memory histories. -/
theorem iterate_congr {δ' : Type}
    {body : δ × σ → Memory.Prog σ} {body' : δ' × σ → Memory.Prog σ}
    {d : δ} {d' : δ'} (hbody : ∀ a, body (d, a) = body' (d', a)) (n : ℕ) (a : σ) :
    iterate body d n a = iterate body' d' n a := by
  calc
    _ = iterate (fun x : Unit × σ => body (d, x.2)) () n a :=
      iterate_comap (fun _ : Unit => d) body () n a
    _ = iterate (fun x : Unit × σ => body' (d', x.2)) () n a :=
      congrArg (fun b : Unit × σ → Memory.Prog σ => iterate b () n a)
        (funext fun x => hbody x.2)
    _ = _ := (iterate_comap (fun _ : Unit => d') body' () n a).symm

/-- Iteration domains agree when the bodies and their domains agree at fixed environments. -/
theorem iterationSafe_congr {δ' : Type}
    {body : δ × σ → Memory.Prog σ} {body' : δ' × σ → Memory.Prog σ}
    {safe : ℕ → δ × σ → Memory.State → Prop} {safe' : ℕ → δ' × σ → Memory.State → Prop}
    {w : ℕ} {d : δ} {d' : δ'} (hbody : ∀ a, body (d, a) = body' (d', a))
    (hsafe : ∀ a s, safe w (d, a) s ↔ safe' w (d', a) s) (n : ℕ) (a : σ) (s : Memory.State) :
    iterationSafe body safe w d n a s ↔ iterationSafe body' safe' w d' n a s := by
  induction n generalizing a s with
  | zero => rfl
  | succ n ih => simp only [iterationSafe, hsafe, ← hbody, ih]

/-- The local work is invariant under agreeing bodies and body charges at their environments. -/
theorem iterationWork_congr {δ' : Type}
    {body : δ × σ → Memory.Prog σ} {body' : δ' × σ → Memory.Prog σ}
    {work : δ × σ → Memory.State → ℕ} {work' : δ' × σ → Memory.State → ℕ}
    {d : δ} {d' : δ'} (hbody : ∀ a, body (d, a) = body' (d', a))
    (hwork : ∀ a s, work (d, a) s = work' (d', a) s) (n : ℕ) (a : σ) (s : Memory.State) :
    iterationWork body work d n a s = iterationWork body' work' d' n a s := by
  induction n generalizing a s with
  | zero => rfl
  | succ n ih => simp only [iterationWork, hwork, ← hbody, ih]

end Cslib.WordRAM.Realization
