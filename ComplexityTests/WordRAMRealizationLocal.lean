/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.WordRAM.Realization.Primitive
import Complexity.Computability.WordRAM.Realization.Result
import Complexity.Computability.WordRAM.Realization.Module

/-!
# A concrete local ADT realized through the memory kernel

A read-only cell has natural-number state and one unit-indexed operation returning its state.
Its local representation owns exactly address zero. This client supplies the existing
`SubroutineBase` initialization, boundedness, locality and ABI obligations, then obtains the
native method execution from `Realizes.toStateTransitionImpl`. It does not supply an independent
execution proof for the method.
-/

namespace ComplexityTests.WordRAMRealizationLocal

open Cslib Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure

private abbrev cell : StateTransitionSpec :=
  StateTransitionSpec.ofFn (State := ℕ) (Op := Unit) (Result := fun _ => ℕ)
    (fun s _ => (s, s)) (fun _ _ => True)

private def cellModule (w : ℕ) : Module cell (Memory.spec w) :=
  Module.ofFn (methods := fun _ => Memory.read 0)
    (rep := fun s e => e.mem 0 = s ∧ e.frontier = 1)
    (valid := by
      intro s e o hr _
      change 0 < e.frontier ∧ True
      exact ⟨by omega, trivial⟩)
    (correct := by
      intro s e o hr _
      change e.mem 0 = s ∧ (e.mem 0 = s ∧ e.frontier = 1)
      exact ⟨hr.1, hr⟩)

private def input : Unit ↪ (Fin 1 → ℕ) where
  toFun _ _ := 0
  inj' := fun _ _ _ => Subsingleton.elim _ _

private abbrev word : ℕ ↪ (Fin 1 → ℕ) :=
  Equiv.toEmbedding (Equiv.symm (Equiv.funUnique (Fin 1) ℕ))

private def output : cell.Label ↪ (Fin 1 → ℕ) where
  toFun a := word a.2
  inj' := by
    rintro ⟨o, a⟩ ⟨o', a'⟩ h
    cases o
    cases o'
    have ha := congrFun h 0
    change a = a' at ha
    cases ha
    rfl

private def method (o : Unit) : Memory.Prog cell.Label := do
  let a ← Memory.read 0
  pure ⟨o, a⟩

private theorem realized :
    Realizes .exact method input output (fun _ _ _ => True) (fun _ _ => 0) :=
  (Realizes.read (B := .exact) input 0).result (fun o a => (⟨o, a⟩ : cell.Label))
    (fun _ _ => rfl)

private noncomputable def registers : ℕ := realized.scratchSize + 8

private noncomputable def reg (i : Fin 8) : Fin registers :=
  ⟨i.val, by have := i.isLt; unfold registers; omega⟩

private noncomputable def src : Fin 1 → Fin registers := fun _ => reg 0

private noncomputable def scratch : Fin (1 + realized.scratchSize + 1) → Fin registers :=
  fun i => ⟨6 + i.val, by have := i.isLt; unfold registers; omega⟩

private theorem scratch_injective : Function.Injective scratch := by
  intro i j hij
  apply Fin.ext
  have hval := congrArg Fin.val hij
  change 6 + i.val = 6 + j.val at hval
  omega

private theorem src_scratch (i : Fin 1) (j : Fin (1 + realized.scratchSize + 1)) :
    src i ≠ scratch j := by
  intro hij
  have hval := congrArg Fin.val hij
  change 0 = 6 + j.val at hval
  omega

private theorem scratch_frontier (j : Fin (1 + realized.scratchSize + 1)) :
    scratch j ≠ reg 1 := by
  intro hj
  have hval := congrArg Fin.val hj
  change 6 + j.val = 1 at hval
  omega

private theorem src_frontier (i : Fin 1) : src i ≠ reg 1 := by
  intro hi
  have hval := congrArg Fin.val hi
  change 0 = 1 at hval
  omega

private noncomputable def program : SubroutineCode .exact registers 0 where
  allocSpan := .seq (.op (.copy (reg 2) (reg 1))) (.op (.const (reg 1) 1))
  initSetup := .op (.copy (reg 2) (reg 2))
  code := realized.code (reg 1) src scratch
  frontierReg := reg 1
  baseReg := reg 2
  initParams := Fin.elim0
  curReg := reg 3
  zeroReg := reg 4
  oneReg := reg 5
  incCur := .exactBin .add (reg 3) (reg 3) (reg 5)
  input := fun i => decide (i = reg 0)
  output := scratch 0

private noncomputable def cellBase (w : ℕ) (h1 : Fits w 1) :
    SubroutineBase program cell.Result cell.valid w 0 Fin.elim0 0 where
  space := 1
  spanTime := 2
  setupTime := 1
  initPotential := 0
  charge _ _ := 2 * realized.factor
  rep s x := x.Bounded w ∧ x.mem 0 = s ∧ x.regs (reg 1) = 1
  potential _ := 0
  encode _ _ := 0
  argMatch _ regs := regs (reg 0) = 0
  decode _ regs := some (regs (scratch 0))
  bounded hr := hr.1
  arguments_fit _ _ _ _ := fits_zero w
  encode_matches _ _ := by simp [program]
  rep_supported := by
    intro s x x' hregs hmem hx' hr
    refine ⟨hx', ?_, ?_⟩
    · exact (hmem 0 (by simp [Block.mem_footprint, Block.Owns])).trans hr.2.1
    · exact (hregs (reg 1) (by simp [program, reg])).trans hr.2.2
  potential_supported _ _ _ := rfl
  clear_nodup := by simp [program, reg]
  params_not_clear j := Fin.elim0 j
  incCur_eval := by
    intro x ho hfit
    change x.regs (reg 5) = 1 at ho
    change Fits w (x.regs (reg 3) + 1) at hfit
    change (Op.exactBin .add (reg 3) (reg 3) (reg 5)).eval w x =
      some (x.set (reg 3) (x.regs (reg 3) + 1))
    rw [Op.eval_exactBin, ho]
    exact Data.put_of_fits hfit
  span_exec := by
    intro x hx hfront _
    change x.regs (reg 1) = 0 at hfront
    let a := x.set (reg 2) (x.regs (reg 1))
    let y := a.set (reg 1) 1
    have hcopy : ExecWithin (B := .exact) w (.op (.copy (reg 2) (reg 1))) x a 1 :=
      ExecWithin.copy
    have hconst : ExecWithin (B := .exact) w (.op (.const (reg 1) 1)) a y 1 :=
      ExecWithin.const h1
    refine ⟨y, hcopy.seq hconst, rfl, ?_, ?_, fun j => Fin.elim0 j⟩
    · simpa [program, y, a, Data.set, reg] using hfront
    · simp [program, y, Data.set]
  setup_exec := by
    intro x hx _ hfront _ hzero
    have hself : x.set (reg 2) (x.regs (reg 2)) = x := by
      apply Data.ext
      · exact Function.update_eq_self _ _
      · rfl
    have he : ExecWithin (B := .exact) w (.op (.copy (reg 2) (reg 2))) x x 1 := by
      simpa only [hself] using
        (ExecWithin.copy (B := .exact) (w := w) (d := reg 2) (s := reg 2) (x := x))
    exact ⟨x, he, hfront, ⟨hx, hzero 0 (by simp [Block.mem_footprint, Block.Owns]), hfront⟩,
      le_rfl, Modifies.refl _ _⟩

private noncomputable def implementation (w : ℕ) (h1 : Fits w 1) :
    DataStructure.WordRAM.StateTransitionImpl program cell w 0 Fin.elim0 0 := by
  refine Realizes.toStateTransitionImpl (cellModule w) realized (reg 1) src scratch
    scratch_injective src_scratch scratch_frontier src_frontier (cellBase w h1) rfl
    ?_ ?_ ?_ ?_ ?_
  · intro s x o hr _ ha
    refine ⟨?_, trivial, hr.2⟩
    funext i
    exact ha
  · intro o a regs hout
    have h0 := hout 0
    change regs (scratch 0) = a at h0
    exact congrArg some h0
  · intro s s' x y o a _ _ _ _ hrep hy _
    exact ⟨hy, hrep⟩
  · intro s e o _ _
    exact Modifies.refl _ _
  · intro s s' x y o a _ _ _ _ _ _ _
    change realized.factor * (1 + 0 + 1) + 0 ≤ 2 * realized.factor + 0
    omega

private noncomputable def fixture : Data registers :=
  ⟨fun i => if i = reg 1 then 1 else 0, fun a => if a = 0 then 7 else 9⟩

-- The resulting native ADT returns a nonzero stored word and preserves unowned dirty memory.
example :
    ∃ y n, Exec 4 program.code fixture y n ∧
      y.regs (scratch 0) = 7 ∧ y.mem 0 = 7 ∧ y.mem 100 = 9 ∧
      n ≤ 2 * realized.factor := by
  let I := implementation 4 (by norm_num [Fits])
  have hb : fixture.Bounded 4 := by
    constructor
    · intro i
      change Fits 4 (if i = reg 1 then 1 else 0)
      split_ifs <;> norm_num [Fits]
    · intro a
      change Fits 4 (if a = 0 then 7 else 9)
      split_ifs <;> norm_num [Fits]
  have hr : I.rep 7 fixture := by
    refine ⟨hb, rfl, ?_⟩
    simp [fixture]
  have ha : I.argMatch () fixture.regs := by
    change fixture.regs (reg 0) = 0
    simp [fixture, reg]
  obtain ⟨y, s', a, n, he, hs, hd, hy, hm, hn⟩ := I.step_exec () hr trivial ha
  have hstep := (cell.step_iff_stepFn 7 () s' a).mp hs
  change (s', a) = (7, 7) at hstep
  have hstate : s' = 7 := congrArg Prod.fst hstep
  have hanswer : a = 7 := congrArg Prod.snd hstep
  subst s'
  subst a
  change some (y.regs (scratch 0)) = some 7 at hd
  change y.Bounded 4 ∧ y.mem 0 = 7 ∧ y.regs (reg 1) = 1 at hy
  change n + 0 ≤ 2 * realized.factor + 0 at hn
  have hout : y.regs (scratch 0) = 7 := Option.some.inj hd
  have houtside := hm 100 (by
    change 100 ∉ (Block.mk 0 1).footprint
    simp [Block.mem_footprint, Block.Owns])
  exact ⟨y, n, he, hout, hy.2.1, houtside, hn⟩

-- The full existing initialization API is inhabited, including clearing an initially dirty cell.
example :
    ∃ y, ExecWithin 4 program.initClear
      (⟨fun _ => 0, fun _ => 9⟩ : Data registers) y 13 ∧
      (implementation 4 (by norm_num [Fits])).rep 0 y ∧ y.mem 100 = 9 := by
  let I := implementation 4 (by norm_num [Fits])
  let x : Data registers := ⟨fun _ => 0, fun _ => 9⟩
  have hx : x.Bounded 4 := ⟨fun _ => fits_zero 4, fun _ => by norm_num [Fits]⟩
  obtain ⟨y, he, _, hr, _, hm⟩ := I.initClear_exec hx rfl (fun j => Fin.elim0 j)
  exact ⟨y, he, hr, hm 100 (by
    change 100 ∉ (Block.mk 0 1).footprint
    simp [Block.mem_footprint, Block.Owns])⟩

end ComplexityTests.WordRAMRealizationLocal
