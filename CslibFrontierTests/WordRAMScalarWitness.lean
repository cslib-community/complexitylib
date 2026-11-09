/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (retained scalar code and maximum-bank Backend regressions)

public import CslibFrontier.Computability.WordRAM.Realization.GlueVector
public import CslibFrontier.Computability.WordRAM.Realization.Backend

/-!
# Specified scalar code through a real Backend

The same supplied scalar additions compute `(cursor + 1, accumulator + value)`. Their
sequential vector emitter shares one auxiliary bank: the original sum placement would use
eleven registers; the maximum placement uses nine. The body allowance is nine instructions,
including two output copies and the final neutral copy. Input delivery and a flat-program halt
are separate calling conventions, not instructions included in this body bound.
-/

@[expose] public section

namespace Cslib.WordRAM.Realization.Tests.ScalarWitness

open Cslib.DataStructure

def coordinates : Fin 2 → (Fin 3 → ℕ) → ℕ :=
  ![fun v => v 0 + 1, fun v => v 1 + v 2]

def step (v : Fin 3 → ℕ) : Fin 2 → ℕ := fun i => coordinates i v

def incrementScalar : GlueComputes.Witness .exact (fun _ : Fin 3 → ℕ => True)
    (coordinates 0) (coordinates 0) 3 :=
  (GlueComputes.Witness.proj 0 (fun _ _ => Nat.le_add_right _ _)).binExact
    (GlueComputes.Witness.const 1 (fun _ _ => by omega)) .add (fun _ _ => rfl)
    (fun _ _ => le_rfl)

def addScalar : GlueComputes.Witness .exact (fun _ : Fin 3 → ℕ => True)
    (coordinates 1) (coordinates 1) 3 :=
  (GlueComputes.Witness.proj 1 (fun _ _ => Nat.le_add_right _ _)).binExact
    (GlueComputes.Witness.proj 2 (fun _ _ => Nat.le_add_left _ _)) .add
    (fun _ _ => rfl) (fun _ _ => le_rfl)

def scalars (i : Fin 2) :
    GlueComputes.Witness .exact (fun _ : Fin 3 → ℕ => True)
      (coordinates i) (coordinates i) 3 :=
  Fin.cases incrementScalar (fun j => Fin.cases addScalar (fun z => Fin.elim0 z) j) i

theorem scalar_scratch (i : Fin 2) : (scalars i).scratchSize = 2 := by
  fin_cases i
  · change incrementScalar.scratchSize = 2
    unfold incrementScalar
    erw [GlueComputes.Witness.binExact_scratchSize]
    rfl
  · change addScalar.scratchSize = 2
    unfold addScalar
    erw [GlueComputes.Witness.binExact_scratchSize]
    rfl

def vectorWitness := Realizes.Witness.glueVectorOfScalars
  (.refl (Fin 3 → ℕ)) (.refl (Fin 2 → ℕ)) step coordinates coordinates (fun _ => 3)
  (fun _ _ => rfl) scalars

def certificates : Unit → Certificate .exact := fun _ => ⟨vectorWitness⟩

-- These equalities inspect the supplied data, not an existentially selected proof witness.
theorem vector_scratch : vectorWitness.scratchSize = 2 := by
  simp [vectorWitness, Realizes.Witness.glueVectorOfScalars, scalar_scratch,
    Finset.sup_const Finset.univ_nonempty]

example : Backend.registers certificates = 9 := by
  simp [Backend.registers, Backend.argWords, Backend.scratchWords, certificates,
    vectorWitness, Realizes.Witness.glueVectorOfScalars, scalar_scratch,
    Finset.sup_const Finset.univ_nonempty]

example : 3 + (2 + (∑ i : Fin 2, (scalars i).scratchSize) + 1) + 1 = 11 := by
  simp [scalar_scratch]

example : vectorWitness.factor = 1 := rfl

/-- Actual native execution retains the whole memory/frontier and live-register frame. The
single code and register file precede every input, width and initial memory. -/
theorem run {w : ℕ} (v : Fin 3 → ℕ) (x : Data (Backend.registers certificates))
    (hx : x.Bounded w) (hin : x.regs ∘ Backend.src certificates () = v)
    (hfit : ∀ i, Fits w (coordinates i v)) :
    ∃ y n, Exec w (Backend.code certificates ()) x y n ∧ n ≤ 9 ∧
      memoryState (Backend.frontier certificates) y =
        memoryState (Backend.frontier certificates) x ∧
      (∀ i : Fin 2, y.regs (Backend.tmp certificates ()
        (Fin.castAdd (vectorWitness.scratchSize + 1) i)) = step v i) ∧
      y.Bounded w ∧ ∀ j, j ≠ Backend.frontier certificates →
        (∀ a, Backend.tmp certificates () a ≠ j) → y.regs j = x.regs j := by
  obtain ⟨y, n, he, hn, hm, ho, hy, hf⟩ :=
    Backend.exists_exec_live certificates () v hx hin ⟨trivial, hfit⟩ (by trivial)
  refine ⟨y, n, he, ?_, hm, ho, hy, hf⟩
  simpa [Backend.factor, certificates, vectorWitness, Realizes.Witness.glueVectorOfScalars,
    memoryCost, StateTransitionSpec.clientHistory, StateTransitionSpec.runClient] using hn

def dirty : ℕ → ℕ := fun a => if a = 100 then 6 else 3

noncomputable def initial (v : Fin 3 → ℕ) : Data (Backend.registers certificates) :=
  Backend.install certificates () v ⟨fun _ => 2, dirty⟩

theorem initial_bounded (v : Fin 3 → ℕ) (hv : ∀ i, Fits 3 (v i)) :
    (initial v).Bounded 3 :=
  Backend.install_bounded certificates () v
    ⟨fun _ => by change Fits 3 2; decide, fun a => by
      dsimp only [dirty]
      split_ifs <;> decide⟩ hv

/-- The largest three-bit output is retained by the same body, with dirty exterior memory. -/
example : ∃ y n, Exec 3 (Backend.code certificates ()) (initial ![0, 7, 0]) y n ∧ n ≤ 9 ∧
    y.mem = dirty ∧ y.regs (Backend.frontier certificates) = 2 ∧
    (∀ i : Fin 2, y.regs (Backend.tmp certificates ()
      (Fin.castAdd (vectorWitness.scratchSize + 1) i)) = ![1, 7] i) := by
  obtain ⟨y, n, he, hn, hm, ho, -, -⟩ := run ![0, 7, 0] (initial ![0, 7, 0])
    (initial_bounded _ (by intro i; fin_cases i <;> decide))
    (Backend.install_src certificates () _ _) (by intro i; fin_cases i <;> decide)
  have hm' : memoryState (Backend.frontier certificates) y = ⟨dirty, 2⟩ := by
    exact hm.trans (Backend.memoryState_install certificates () ![0, 7, 0]
      ⟨fun _ => 2, dirty⟩)
  refine ⟨y, n, he, hn, congrArg Memory.State.mem hm',
    congrArg Memory.State.frontier hm', ?_⟩
  intro i
  fin_cases i
  · simpa [step, coordinates] using ho 0
  · simpa [step, coordinates] using ho 1

/-- A genuinely aliased source placement: both sum operands name register one. -/
def aliasSource : Fin 3 → Fin 8 := ![0, 1, 1]

def aliasTmp (j : Fin (2 + vectorWitness.scratchSize + 1)) : Fin 8 :=
  ⟨2 + j.val, by have := j.isLt; have := vector_scratch; omega⟩

/-- The same retained emitter admits repeated input registers, not only repeated values in
different registers. It retains the two live inputs and all dirty memory. -/
example : ∃ y, ExecWithin 3 (vectorWitness.code (7 : Fin 8) aliasSource aliasTmp)
    ⟨fun i => if i = 1 then 3 else 0, dirty⟩ y 9 ∧ y.mem = dirty ∧
    y.regs 0 = 0 ∧ y.regs 1 = 3 ∧
    (∀ i : Fin 2, y.regs (aliasTmp (Fin.castAdd (vectorWitness.scratchSize + 1) i)) =
      ![1, 6] i) := by
  have hi : Function.Injective aliasTmp := by
    intro a b h
    apply Fin.ext
    have := congrArg Fin.val h
    dsimp only [aliasTmp] at this
    omega
  have hs (i : Fin 3) : (aliasSource i).val ≤ 1 := by fin_cases i <;> decide
  have hd (i : Fin 3) (j : Fin (2 + vectorWitness.scratchSize + 1)) :
      aliasSource i ≠ aliasTmp j := by
    intro h
    have hh : (aliasSource i).val = 2 + j.val := congrArg Fin.val h
    have := hs i
    omega
  have hf (j : Fin (2 + vectorWitness.scratchSize + 1)) : aliasTmp j ≠ 7 := by
    intro h
    have hh := congrArg Fin.val h
    have hj := j.isLt
    have := vector_scratch
    dsimp only [aliasTmp] at hh
    omega
  have hsf (i : Fin 3) : aliasSource i ≠ 7 := by
    intro h
    have hh := congrArg Fin.val h
    have := hs i
    change (aliasSource i).val = 7 at hh
    omega
  let x : Data 8 := ⟨fun i => if i = 1 then 3 else 0, dirty⟩
  have hx : x.Bounded 3 := by
    constructor
    · intro i
      change Fits 3 (if i = 1 then 3 else 0)
      split_ifs <;> decide
    · intro a
      dsimp only [x, dirty]
      split_ifs <;> decide
  have hin : x.regs ∘ aliasSource = ![0, 3, 3] := by
    ext i
    fin_cases i <;> rfl
  obtain ⟨y, he, hm, ho, hframe⟩ :=
    (vectorWitness.code_spec 7 aliasSource aliasTmp hi hd hf hsf).2
      3 ![0, 3, 3] x hx hin ⟨trivial, by intro i; fin_cases i <;> decide⟩ (by trivial)
  change (∀ i : Fin 2, y.regs
    (aliasTmp (Fin.castAdd (vectorWitness.scratchSize + 1) i)) = step ![0, 3, 3] i) at ho
  refine ⟨y, ?_, congrArg Memory.State.mem hm, ?_, ?_, ?_⟩
  · simpa [vectorWitness, Realizes.Witness.glueVectorOfScalars] using he
  · exact hframe 0 (by decide) (by
      intro j h
      have hh := congrArg Fin.val h
      change 2 + j.val = 0 at hh
      omega)
  · exact hframe 1 (by decide) (by
      intro j h
      have hh := congrArg Fin.val h
      change 2 + j.val = 1 at hh
      omega)
  · intro i
    fin_cases i
    · simpa [step, coordinates] using ho 0
    · simpa [step, coordinates] using ho 1

/-- A supplied projection needs no positive literal and really runs at width zero. -/
example : ∃ y, ExecWithin 0
    ((GlueComputes.Witness.proj (B := .exact) (P := fun _ : Fin 1 → ℕ => True)
      (bound := fun v => v 0) 0 (fun _ _ => le_rfl)).code
        (fun _ => (0 : Fin 2)) (fun _ => (1 : Fin 2)))
    ⟨fun _ => 0, fun _ => 0⟩ y 1 ∧ y.regs 1 = 0 ∧ y.mem = fun _ => 0 := by
  let h := GlueComputes.Witness.proj (B := .exact) (P := fun _ : Fin 1 → ℕ => True)
    (bound := fun v => v 0) 0 (fun _ _ => le_rfl)
  exact h.code_spec (fun _ => (0 : Fin 2)) (fun _ => (1 : Fin 2))
    (show Function.Injective (fun _ : Fin 1 => (1 : Fin 2)) from
      fun i j _ => Subsingleton.elim i j) (by decide) |>.2 0
      ⟨fun _ => 0, fun _ => 0⟩ trivial (fits_zero 0) |>.imp fun y hy =>
        ⟨hy.1, hy.2.1, hy.2.2.1⟩

-- The input fits but its sum does not: no execution is promised by the certificate here.
example : (∀ i : Fin 3, Fits 3 (![0, 7, 1] i)) ∧
    ¬(∀ i : Fin 2, Fits 3 (coordinates i ![0, 7, 1])) := by decide

-- Exact subtraction retains its definedness premise; fitting zero is not enough for 0 - 1.
example : Fits 0 (0 - 1) ∧ BinOp.sub.evalExact 0 1 = none := by decide

end Cslib.WordRAM.Realization.Tests.ScalarWitness
