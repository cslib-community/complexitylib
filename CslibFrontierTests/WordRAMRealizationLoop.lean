/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (regression tests for realization loop infrastructure)

public import CslibFrontier.Computability.WordRAM.Realization.Loop
import CslibFrontier.Computability.WordRAM.Realization.Glue
import CslibFrontier.Computability.WordRAM.Realization.Primitive

/-!
# Runtime-loop regression clients

A query-free identity loop has zero memory charge but a local-work charge growing with runtime
fuel. Its uniform native witness also executes at zero word width when the state and fuel are
zero, so materializing the decrement constant in the positive body cannot break the empty case.
-/

public section

namespace Cslib.WordRAM.Realization.Tests

open Cslib.DataStructure

private def unitInput : Unit ↪ (Fin 0 → ℕ) :=
  (Equiv.ofUnique Unit (Fin 0 → ℕ)).toEmbedding

private def wordOutput : ℕ ↪ (Fin 1 → ℕ) :=
  (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding

private def bodyInput : Unit × ℕ ↪ (Fin (0 + 1) → ℕ) :=
  (unitInput.prodMap wordOutput).trans (Fin.appendEquiv 0 1).toEmbedding

/-- A certified word copy performs local work without any memory query. -/
@[expose] def identityBody (d : Unit × ℕ) : Memory.Prog ℕ := pure d.2

private theorem identityBody_realizes :
    Realizes .exact identityBody bodyInput wordOutput
      (fun w d _ => Fits w d.2) (fun _ _ => 1) := by
  unfold identityBody
  have h : GlueComputes .exact (fun _ : Fin 1 → ℕ => True)
      (fun v => v 0) (fun v => v 0) 1 := GlueComputes.proj 0 (fun _ _ => le_rfl)
  simpa [identityBody, bodyInput, unitInput, wordOutput, Fin.appendEquiv,
    Fin.append, Fin.addCases] using Realizes.glue bodyInput h

/-- A single body certificate is reused before all runtime fuel and data choices. -/
private theorem identityLoop_realizes :
    Realizes .exact (fun d : (Unit × ℕ) × ℕ => iterate identityBody d.1.1 d.2 d.1.2)
      ((bodyInput.prodMap wordOutput).trans (Fin.appendEquiv (0 + 1) 1).toEmbedding)
      wordOutput (fun w d s => iterationSafe identityBody (fun w d _ => Fits w d.2)
        w d.1.1 d.2 d.1.2 s)
      (fun d s => iterationWork identityBody (fun _ _ => 1) d.1.1 d.2 d.1.2 s) :=
  Realizes.iterateRuntime unitInput wordOutput identityBody_realizes

/-- Iterating the existing query-free identity source retains its value. -/
theorem identity_iterate (n a : ℕ) : iterate identityBody () n a = pure a := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [iterate, identityBody, pure_bind] using ih

example (n a : ℕ) (s : Memory.State) : memoryCost (iterate identityBody () n a) s = 0 := by
  rw [identity_iterate]
  rfl

private theorem identity_work (n a : ℕ) (s : Memory.State) :
    iterationWork identityBody (fun _ _ => 1) () n a s = 2 * n := by
  induction n generalizing a s with
  | zero => rfl
  | succ n ih =>
    simp only [iterationWork, ih]
    omega

/-- Query-free iteration still has increasing certified local work. -/
theorem queryFree_work_grows (n m a : ℕ) (s : Memory.State) (h : n < m) :
    iterationWork identityBody (fun _ _ => 1) () n a s <
      iterationWork identityBody (fun _ _ => 1) () m a s := by
  rw [identity_work, identity_work]
  omega

/-- The uniform loop witness has a genuine zero-width, zero-fuel flat execution. -/
example : ∃ r, ∃ p : Program .exact r, ∃ steps,
    Executes 0 p ⟨0, ⟨fun _ => 0, fun _ => 0⟩⟩ 0 steps := by
  obtain ⟨n, C, emit, he⟩ := identityLoop_realizes
  let r := 2 + (1 + n + 1) + 1
  let frontier : Fin r := ⟨r - 1, by omega⟩
  let src : Fin 2 → Fin r := fun i => ⟨i.val, by omega⟩
  let tmp : Fin (1 + n + 1) → Fin r := fun i => ⟨2 + i.val, by omega⟩
  have hi : Function.Injective tmp := by
    intro i j h
    apply Fin.ext
    have hh := congrArg (fun a : Fin r => a.val) h
    dsimp only [tmp] at hh
    omega
  have hd (i : Fin 2) (j : Fin (1 + n + 1)) : src i ≠ tmp j := by
    intro h
    have hh := congrArg (fun a : Fin r => a.val) h
    dsimp only [src, tmp] at hh
    omega
  have hf (j : Fin (1 + n + 1)) : tmp j ≠ frontier := by
    intro h
    have hh := congrArg (fun a : Fin r => a.val) h
    dsimp only [tmp, frontier, r] at hh
    omega
  have hs (i : Fin 2) : src i ≠ frontier := by
    intro h
    have hh := congrArg (fun a : Fin r => a.val) h
    dsimp only [src, frontier, r] at hh
    omega
  let x : Data r := ⟨fun _ => 0, fun _ => 0⟩
  have hx : x.Bounded 0 := ⟨fun _ => fits_zero 0, fun _ => fits_zero 0⟩
  have hin : x.regs ∘ src =
      ((bodyInput.prodMap wordOutput).trans (Fin.appendEquiv (0 + 1) 1).toEmbedding)
        (((), 0), 0) := by
    funext i
    fin_cases i <;> rfl
  obtain ⟨y, ⟨steps, _, hy⟩, _, hout, _⟩ :=
    (he frontier src tmp hi hd hf hs).2 0 (((), 0), 0) x hx hin trivial trivial
  have ho : y.regs (tmp 0) = 0 := hout 0
  refine ⟨r, (emit frontier src tmp).program (tmp 0), steps + 1, ?_⟩
  simpa only [ho] using hy.executes (tmp 0)

private def decrementBody (d : Unit × ℕ) : Memory.Prog ℕ := pure (d.2 - 1)

private theorem decrementBody_realizes :
    Realizes .exact decrementBody bodyInput wordOutput
      (fun w d _ => 1 ≤ d.2 ∧ Fits w d.2) (fun _ _ => 3) := by
  unfold decrementBody
  have hp : GlueComputes .exact (fun v : Fin 1 → ℕ => 1 ≤ v 0)
      (fun v => v 0) (fun v => v 0) 1 := GlueComputes.proj 0 (fun _ _ => le_rfl)
  have hc : GlueComputes .exact (fun v : Fin 1 → ℕ => 1 ≤ v 0)
      (fun _ => 1) (fun v => v 0) 1 := GlueComputes.const 1 (fun _ h => h)
  have h := GlueComputes.bin_exact hp hc .sub
    (fun v hv => by simp [BinOp.evalExact, hv, BinOp.eval])
    (fun v _ => Nat.sub_le (v 0) 1)
  simpa [bodyInput, unitInput, wordOutput, Fin.appendEquiv,
    Fin.append, Fin.addCases, BinOp.eval] using Realizes.glue bodyInput h

private theorem decrementLoop_realizes :
    Realizes .exact (fun d : (Unit × ℕ) × ℕ => iterate decrementBody d.1.1 d.2 d.1.2)
      ((bodyInput.prodMap wordOutput).trans (Fin.appendEquiv (0 + 1) 1).toEmbedding)
      wordOutput (fun w d s => iterationSafe decrementBody
        (fun w d _ => 1 ≤ d.2 ∧ Fits w d.2) w d.1.1 d.2 d.1.2 s)
      (fun d s => iterationWork decrementBody (fun _ _ => 3) d.1.1 d.2 d.1.2 s) :=
  Realizes.iterateRuntime unitInput wordOutput decrementBody_realizes

example (s : Memory.State) : (Memory.spec 4).clientResult s
    (iterate decrementBody () 3 7) = 4 := rfl

example (s : Memory.State) : iterationSafe decrementBody
    (fun w d _ => 1 ≤ d.2 ∧ Fits w d.2) 4 () 3 7 s := by
  change (1 ≤ 7 ∧ Fits 4 7) ∧ (1 ≤ 6 ∧ Fits 4 6) ∧ (1 ≤ 5 ∧ Fits 4 5) ∧ True
  decide

example (s : Memory.State) : iterationSafe decrementBody
    (fun w d _ => 1 ≤ d.2 ∧ Fits w d.2) 0 () 0 0 s := trivial

private def pointerBody (d : Unit × ℕ) : Memory.Prog ℕ := Memory.read d.2

private theorem pointerBody_realizes :
    Realizes .exact pointerBody bodyInput wordOutput
      (fun _ _ _ => True) (fun _ _ => 0) := by
  unfold pointerBody
  simpa [bodyInput, unitInput, wordOutput, Fin.appendEquiv, Fin.append, Fin.addCases] using
    Realizes.read (B := .exact) bodyInput (0 : Fin 1)

/-- The mutable state supplies each next address; the loop is not repeated at its first address. -/
private theorem pointerLoop_realizes :
    Realizes .exact (fun d : (Unit × ℕ) × ℕ => iterate pointerBody d.1.1 d.2 d.1.2)
      ((bodyInput.prodMap wordOutput).trans (Fin.appendEquiv (0 + 1) 1).toEmbedding)
      wordOutput (fun w d s => iterationSafe pointerBody (fun _ _ _ => True)
        w d.1.1 d.2 d.1.2 s)
      (fun d s => iterationWork pointerBody (fun _ _ => 0) d.1.1 d.2 d.1.2 s) :=
  Realizes.iterateRuntime unitInput wordOutput pointerBody_realizes

private def linkedMemory : Memory.State :=
  ⟨fun a => if a = 0 then 1 else if a = 1 then 2 else 0, 3⟩

example : (Memory.spec 2).clientResult linkedMemory (iterate pointerBody () 2 0) = 2 := rfl

example : (Memory.spec 2).clientHistory linkedMemory (iterate pointerBody () 2 0) =
    [.read 0, .read 1] := rfl

example : (Memory.spec 2).ValidHistory linkedMemory
    ((Memory.spec 2).clientHistory linkedMemory (iterate pointerBody () 2 0)) := by decide

example : Memory.WellFormed 2 linkedMemory := by
  refine ⟨by decide, fun a => ?_⟩
  change Fits 2 (if a = 0 then 1 else if a = 1 then 2 else 0)
  split_ifs <;> decide

/-- Direct native register-bank copy at zero length and width zero charges one instruction. -/
example (x : Data 3) :
    ∃ y, ExecWithin 0
      (Cslib.WordRAM.copyBank (B := .exact) (Fin.elim0 : Fin 0 → Fin 3) Fin.elim0 0) x y 1 ∧
      y.mem = x.mem ∧ ∀ j, y.regs j = x.regs j := by
  obtain ⟨y, hy, hm, _, hf⟩ := Cslib.WordRAM.copyBank_exec (B := .exact)
    (Fin.elim0 : Fin 0 → Fin 3) Fin.elim0 0 (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) 0 x
  exact ⟨y, hy, hm, fun j => hf j (fun i => Fin.elim0 i)⟩

/-- Direct two-register copy charges `k + 1 = 3` instructions, copies both slots, and frames memory
and outside registers without reading the word width. -/
example (x : Data 5) :
    ¬(Cslib.WordRAM.copyBank (B := .exact) ![0, 1] ![2, 3] (4 : Fin 5)).ReadsWidth ∧
    ∃ y, ExecWithin 0 (Cslib.WordRAM.copyBank (B := .exact) ![0, 1] ![2, 3] (4 : Fin 5)) x y 3 ∧
      y.mem = x.mem ∧ y.regs 2 = x.regs 0 ∧ y.regs 3 = x.regs 1 ∧ y.regs 4 = x.regs 4 := by
  refine ⟨Cslib.WordRAM.copyBank_not_readsWidth ![0, 1] ![2, 3] 4, ?_⟩
  have hdst : Function.Injective (![2, 3] : Fin 2 → Fin 5) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> revert h <;> decide
  have hdis : ∀ i j : Fin 2, (![0, 1] : Fin 2 → Fin 5) i ≠ (![2, 3] : Fin 2 → Fin 5) j := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  obtain ⟨y, hy, hm, hout, hf⟩ :=
    Cslib.WordRAM.copyBank_exec (B := .exact) ![0, 1] ![2, 3] 4 hdst hdis 0 x
  exact ⟨y, hy, hm, hout 0, hout 1, hf 4 (by intro i; fin_cases i <;> decide)⟩

/-- Direct ghost-state varying-charge loop rule sums state-dependent charges along transitions. -/
example : Cslib.WordRAM.iterationSum (fun s : ℕ => s + 2) (fun s => 3 * s) 3 1 = 27 := rfl

example (x : Data 2) (hx0 : x.regs 0 = 0) (hx1 : x.regs 1 = 0) :
    ∃ y, ExecWithin 0 (.loop (.lt 0 1) (.op (.copy (B := .exact) 0 0))) x y 4 ∧
      y.regs 0 = 0 ∧ y.regs 1 = 0 := by
  let I : ℕ → ℕ → Data 2 → Prop := fun n s z => n = 0 ∧ z.regs 0 = 0 ∧ z.regs 1 = 0 ∧ s = 5
  obtain ⟨y, hy, hIy⟩ := Cslib.WordRAM.ExecWithin.loop_invariant_state_charged
    (B := .exact) (cond := .lt 0 1) (code := .op (.copy (B := .exact) 0 0))
    (w := 0) (C := 1) (D := 1) I (fun s => s + 1) (fun s => s)
    (fun _ z hI => by simp [Cond.Holds, hI.2.1, hI.2.2.1])
    (fun n _ _ hI => absurd hI.1 (Nat.succ_ne_zero n))
    (n := 0) (s := 5) (x := x) ⟨rfl, hx0, hx1, rfl⟩
  exact ⟨y, hy, hIy.2.1, hIy.2.2.1⟩

/-- Positive-fuel execution of `ExecWithin.loop_invariant_state_charged` with a state-varying
charge and semantic ghost-state transition `(· + 2)^[n]`. -/
example (w n s₀ : ℕ) (x : Data 3) (hfit : Fits w n)
    (hx0 : x.regs 0 = 0) (hx1 : x.regs 1 = n) (hx2 : x.regs 2 = 1) :
    ∃ y, ExecWithin w (.loop (.lt 0 1) (.op (.exactBin .sub 1 1 2))) x y
        (3 * (Cslib.WordRAM.iterationSum (fun s => s + 2) (fun s => s) n s₀ + n + 1)) ∧
      y.regs 0 = 0 ∧ y.regs 1 = 0 ∧ y.regs 2 = 1 ∧
      ((fun s => s + 2)^[n]) s₀ = s₀ + 2 * n := by
  let I : ℕ → ℕ → Data 3 → Prop := fun k s z =>
    Fits w k ∧ z.regs 0 = 0 ∧ z.regs 1 = k ∧ z.regs 2 = 1 ∧
      s + 2 * k = s₀ + 2 * n
  obtain ⟨y, hy, hIy⟩ := Cslib.WordRAM.ExecWithin.loop_invariant_state_charged
    (B := .exact) (cond := .lt 0 1) (code := .op (.exactBin .sub 1 1 2))
    (w := w) (C := 1) (D := 0) I (fun s => s + 2) (fun s => s)
    (fun _ z hI => by simp [Cond.Holds, hI.2.1, hI.2.2.1])
    (fun k s z ⟨hfk, hz0, hz1, hz2, hinv⟩ => by
      refine ⟨by simp [Cond.Holds, hz0, hz1], z.set 1 k, ?_, ?_⟩
      · have hstep : ExecWithin w (.op (.exactBin .sub 1 1 2)) z (z.set 1 k) 1 := by
          apply ExecWithin.op
          rw [Op.eval_exactBin, hz1, hz2]
          simp only [BinOp.evalExact, Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel,
            Option.bind_some]
          exact Data.put_of_fits (hfk.of_le (by omega))
        exact hstep.mono (by omega)
      · refine ⟨hfk.of_le (by omega), ?_, by simp [Data.set], ?_, by omega⟩
        · simpa [Data.set] using hz0
        · simpa [Data.set] using hz2)
    (n := n) (s := s₀) (x := x) ⟨hfit, hx0, hx1, hx2, rfl⟩
  exact ⟨y, hy, hIy.2.1, hIy.2.2.1, hIy.2.2.2.1, by simpa using hIy.2.2.2.2⟩

end Cslib.WordRAM.Realization.Tests
