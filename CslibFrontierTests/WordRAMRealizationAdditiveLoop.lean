/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (regression tests for additive realization accounting)

public import CslibFrontierTests.WordRAMRealizationLoop
public import CslibFrontier.Computability.WordRAM.Realization.GlueVector
public import CslibFrontier.Computability.WordRAM.Realization.Backend
public import CslibFrontier.Computability.WordRAM.Realization.Absorb

/-!
The existing query-free identity body is realized by fixed-time vector glue and retained through
the same Backend. Actual loop overhead is additive: `9*q+6`, instead of using the loop's coarse
factor again. Scratch selected from scalar `GlueComputes` remains symbolic. Installation and
halt are separate; both the full memory/frontier and the live-register frame are retained.
-/

@[expose] public section

namespace CslibFrontierTests.WordRAMRealizationAdditiveLoop

open Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization
  Cslib.WordRAM.Realization.Tests

/-- The existing source's one coordinate has a one-instruction scalar allowance, with its
result and neutral copies paid by vector glue. -/
noncomputable def bodyWitness :
    Realizes.Witness .exact identityBody WordEncoding.encode WordEncoding.encode
      (fun w d _ => Fits w d.2) (fun _ _ => 2) :=
  let g : Fin 1 → (Fin 1 → ℕ) → ℕ := fun _ v => v 0
  let h := Realizes.Witness.glueVector WordEncoding.encode WordEncoding.encode
    (fun d : Unit × ℕ => d.2) g g (fun _ => 1) (P := fun _ => True)
    (by intro d i; fin_cases i; rfl) (fun _ => GlueComputes.proj 0 (fun _ _ => le_rfl))
  h.consequence (by intro w d s _ _ hsafe; exact ⟨trivial, fun _ => hsafe⟩)
    (by intros; rfl)

noncomputable def loopWitness :=
  Realizes.Witness.iterateRuntime (WordEncoding.encode (α := Unit)) WordEncoding.encode
    bodyWitness

noncomputable def certificates : Unit → Certificate .exact := fun _ => ⟨loopWitness⟩

noncomputable def initial (s : Memory.State) (a q : ℕ) :=
  Backend.install certificates () (((), a), q) (Backend.data certificates s)

-- The retained code and factor, rather than a reselected existential witness, reach Backend.
example : Backend.code certificates () = loopEmit bodyWitness.code
    (Backend.frontier certificates) (Backend.src certificates ())
    (Backend.tmp certificates ()) := rfl

example : bodyWitness.factor = 1 ∧ loopWitness.factor = 11 := ⟨rfl, rfl⟩

-- The bank formula is concrete in the supplied data; scalar scratch is not assigned a numeral.
example : loopWitness.scratchSize = 1 + bodyWitness.scratchSize + 3 := rfl

-- The data adapters keep the supplied scratch, factor and emitter rather than reselecting them.
example {r : ℕ} (frontier : Fin r) src tmp :
    let h := bodyWitness.consequenceValid (safe' := fun w d _ => Fits w d.2 ∧ d.1 = ())
      (fun _ _ _ _ _ _ hs => hs.1)
    h.scratchSize = bodyWitness.scratchSize ∧ h.factor = 1 ∧
      h.code frontier src tmp = bodyWitness.code frontier src tmp :=
  ⟨rfl, rfl, rfl⟩

example {r : ℕ} (frontier : Fin r) src tmp :
    let h := bodyWitness.congr (p' := fun d => pure d.2) (fun _ => rfl)
    h.scratchSize = bodyWitness.scratchSize ∧ h.factor = 1 ∧
      h.code frontier src tmp = bodyWitness.code frontier src tmp :=
  ⟨rfl, rfl, rfl⟩

example {r : ℕ} (frontier : Fin r) src tmp :
    let h := bodyWitness.reindex id WordEncoding.encode id (fun _ _ => rfl)
    h.scratchSize = bodyWitness.scratchSize ∧ h.factor = 1 ∧
      h.code frontier src tmp = bodyWitness.code frontier src tmp :=
  ⟨rfl, rfl, rfl⟩

/-- A uniform native body with its tighter clock and full original semantic/frame result. -/
theorem identity_native {w : ℕ} (a q : ℕ) (s : Memory.State)
    (hs : Memory.WellFormed w s) (ha : Fits w a) (hq : Fits w q) :
    ∃ y, ExecWithin w (Backend.code certificates ()) (initial s a q) y (9 * q + 6) ∧
      memoryState (Backend.frontier certificates) y = s ∧
      y.regs (Backend.tmp certificates () 0) = a ∧
      ∀ i, i ≠ Backend.frontier certificates →
        (∀ j, Backend.tmp certificates () j ≠ i) → y.regs i = (initial s a q).regs i := by
  have harg (i : Fin 2) : Fits w (WordEncoding.encode (((), a), q) i) := by
    fin_cases i
    · exact ha
    · exact hq
  have hx : (initial s a q).Bounded w :=
    Backend.install_bounded certificates () (((), a), q)
      (Backend.bounded_data certificates hs) harg
  have hin := Backend.install_src certificates () (((), a), q) (Backend.data certificates s)
  have hm : memoryState (Backend.frontier certificates) (initial s a q) = s :=
    (Backend.memoryState_install certificates () (((), a), q) (Backend.data certificates s)).trans
      (Backend.memoryState_data certificates s)
  have hsafe : ∀ n, iterationSafe identityBody (fun w d _ => Fits w d.2) w () n a s := by
    intro n
    induction n with
    | zero => trivial
    | succ n ih => exact ⟨ha, ih⟩
  have hcharge : ∀ n, memoryCost (iterate identityBody () n a) s +
      iterationWork identityBody (fun _ _ => 2) () n a s = 3 * n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      change memoryCost (iterate identityBody () n a) s +
        (2 + iterationWork identityBody (fun _ _ => 2) () n a s + 1) = 3 * (n + 1)
      omega
  obtain ⟨y, hy, hmem, hout, hframe⟩ :=
    (bodyWitness.loopEmit_spec (WordEncoding.encode (α := Unit)) WordEncoding.encode
      (Backend.frontier certificates) (Backend.src certificates ())
      (Backend.tmp certificates ()) (Backend.tmp_injective certificates ())
      (Backend.src_ne_tmp certificates () ()) (Backend.tmp_ne_frontier certificates ())
      (Backend.src_ne_frontier certificates ())).2 w (((), a), q) (initial s a q) hx hin
        (by rw [hm]; exact hsafe q) (by rw [hm, identity_iterate]; trivial)
  rw [hm, hcharge] at hy
  refine ⟨y, hy.mono ?_, ?_, ?_, hframe⟩
  · change 1 * (3 * q) + 6 * (q + 1) ≤ 9 * q + 6
    omega
  · rw [hm, identity_iterate] at hmem
    exact hmem
  · have hr := hout 0
    rw [hm, identity_iterate] at hr
    exact hr

def dirty : Memory.State := ⟨fun _ => 7, 3⟩

-- Same selected code, nonzero runtime fuel, maximum width-three value and dirty whole memory.
example : ∃ y, ExecWithin 3 (Backend.code certificates ()) (initial dirty 7 2) y 24 ∧
    memoryState (Backend.frontier certificates) y = dirty ∧
    y.regs (Backend.tmp certificates () 0) = 7 ∧
    ∀ i, i ≠ Backend.frontier certificates →
      (∀ j, Backend.tmp certificates () j ≠ i) → y.regs i = (initial dirty 7 2).regs i :=
  identity_native 7 2 dirty ⟨by decide, fun _ => by change Fits 3 7; decide⟩
    (by decide) (by decide)

def zero : Memory.State := ⟨fun _ => 0, 0⟩

-- Zero width/fuel does not execute the decrement-constant body or assume Fits0 1.
example : ∃ y, ExecWithin 0 (Backend.code certificates ()) (initial zero 0 0) y 6 ∧
    memoryState (Backend.frontier certificates) y = zero ∧
    y.regs (Backend.tmp certificates () 0) = 0 ∧
    ∀ i, i ≠ Backend.frontier certificates →
      (∀ j, Backend.tmp certificates () j ≠ i) → y.regs i = (initial zero 0 0).regs i :=
  identity_native 0 0 zero ⟨fits_zero 0, fun _ => fits_zero 0⟩ (fits_zero 0) (fits_zero 0)

end CslibFrontierTests.WordRAMRealizationAdditiveLoop
