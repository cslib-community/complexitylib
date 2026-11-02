/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.WordRAM.Realization.Client.MemoryQueueAdapter

/-!
The framed queue is initialized after a nonempty five-cell prefix. Its actual flat programs
execute two enqueues and a transfer-triggering dequeue, including each operation's trailing
halt. Register argument delivery follows the existing `prepareRegs` ABI and is outside this
clock. The fresh owned block is zero; the separate literal M1a allocation path may keep dirty
unused item cells and is not replaced by this initializer.
-/

namespace ComplexityTests.WordRAMRealizationQueueAdapter

open Cslib Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.WordRAM.Realization.MemoryQueueAdapter

private abbrev spec := Queue.WordRAM.spec 4 2
private def ops : List spec.Op := [.enqueue 7, .enqueue 15, .dequeue]
private def expected : spec.Transcript :=
  [⟨.enqueue 7, (), [7]⟩, ⟨.enqueue 15, (), [7, 15]⟩, ⟨.dequeue, some 7, [15]⟩]

private noncomputable def fresh (C : ℕ) : Data registers where
  regs i := if i = register 3 then C else if i = register 11 then 5 else 0
  mem a := if a < 5 then 7 else if a < 11 then 0 else 9

private theorem valid : spec.ValidOpSeq [] ops := by
  apply (spec.validOpSeq_iff_validHistory [] ops).mpr
  change (0 < 2 ∧ Fits 4 7) ∧ (1 < 2 ∧ Fits 4 15) ∧ True ∧ True
  norm_num [Fits]

private theorem runsOps_modifies {capacity : ℕ}
    {C : DataStructure.WordRAM.StateTransitionImpl program (Queue.WordRAM.spec 4 capacity)
      4 5 (fun _ => capacity) []}
    {q q' : (Queue.WordRAM.spec 4 capacity).State} {x y : Data registers} {os tr t}
    (h : C.RunsOps C.prepareRegs q x os tr q' y t) :
    Modifies (Block.mk 5 C.space).footprint x.mem y.mem := by
  induction h with
  | nil => exact Modifies.refl _ _
  | cons _ _ _ _ hm _ ih => exact fun a ha => (ih a ha).trans (hm a ha)

-- The concrete framed target is inhabited and its flat native FIFO trace has the right answer.
example :
    let I := implementation 4 5 2 (by norm_num [space, Fits])
    ∃ pc x₀ t_init z t_ops,
      Runs 4 program.initFreshProg ⟨0, fresh 2⟩ ⟨pc, x₀⟩ t_init ∧
      (∃ out, step 4 program.initFreshProg ⟨pc, x₀⟩ = .halt out) ∧
      I.RunsOps I.prepareRegs [] x₀ ops expected [15] z t_ops ∧
      I.rep [15] z ∧ z.mem 100 = 9 ∧ z.mem 0 = 7 ∧ t_init ≤ 13 ∧
      t_ops ≤ 3 * (153 * MemoryQueueMethod.realizes_method.factor + 1) := by
  let I := implementation 4 5 2 (by norm_num [space, Fits])
  have hb : (fresh 2).Bounded 4 := by
    constructor
    · intro i
      change Fits 4 (if i = register 3 then 2 else if i = register 11 then 5 else 0)
      split_ifs <;> norm_num [Fits]
    · intro a
      change Fits 4 (if a < 5 then 7 else if a < 11 then 0 else 9)
      split_ifs <;> norm_num [Fits]
  have hfr : (fresh 2).regs program.frontierReg = 5 := by simp [fresh, program, register]
  have hpar : ∀ j, (fresh 2).regs (program.initParams j) = (2 : ℕ) := by
    intro j
    simp [fresh, program]
  have hspace : I.space = space 2 := implementation_space 4 5 2 _
  have hz : ∀ a ∈ (Block.mk 5 I.space).footprint, (fresh 2).mem a = 0 := by
    intro a ha
    rw [hspace] at ha
    simp only [Block.mem_footprint, Block.Owns, space] at ha
    simp [fresh, show ¬a < 5 by omega, show a < 11 by omega]
  obtain ⟨pc, x₀, ti, tr, q, z, nativeSteps, hri, hhalt, hm, hro, hops, htr, hr, hti, hto⟩ :=
    I.run_ops_exact_fresh hb hfr hpar hz ops valid
  have hcanonical := (spec.validTranscript_iff_run [] tr q).mp htr
  rw [hops] at hcanonical
  have hq : q = [15] := hcanonical.2.1
  have ht : tr = expected := hcanonical.2.2
  subst q
  subst tr
  have hOutside : 100 ∉ (Block.mk 5 I.space).footprint := by
    rw [hspace]
    norm_num [Block.mem_footprint, Block.Owns, space]
  have hmem := (runsOps_modifies (capacity := 2) hro) 100 hOutside
  have hinitmem := hm 100 hOutside
  have hfinal : z.mem 100 = 9 := hmem.trans (hinitmem.trans (by rfl))
  have hPrefixOutside : 0 ∉ (Block.mk 5 I.space).footprint := by
    simp [Block.mem_footprint, Block.Owns]
  have hprefix : z.mem 0 = 7 := ((runsOps_modifies (capacity := 2) hro) 0 hPrefixOutside).trans
    ((hm 0 hPrefixOutside).trans (by rfl))
  have htime : nativeSteps ≤ 3 * (153 * MemoryQueueMethod.realizes_method.factor + 1) := by
    have hbound := hto
    have hc : ∀ q o, I.charge q o = 153 * MemoryQueueMethod.realizes_method.factor :=
      fun q o => implementation_charge 4 5 2 _ q o
    have hp : I.initPotential = 0 := implementation_initPotential 4 5 2 _
    simp only [hc, hp, StateTransitionSpec.totalCostTranscript_const] at hbound
    change nativeSteps + _ ≤ 3 * (153 * MemoryQueueMethod.realizes_method.factor + 1) + 0 at hbound
    omega
  have hiTime : I.initTime = 13 := implementation_initTime 4 5 2 _
  rw [hiTime] at hti
  exact ⟨pc, x₀, ti, z, nativeSteps, hri, hhalt, hro, hr, hfinal, hprefix, hti, htime⟩

-- Capacity zero uses the SAME program and initializes a valid empty queue at a nonzero base.
-- An empty dequeue returns none through an actual flat call, with no transfer iterations.
example :
    let I := implementation 4 5 0 (by norm_num [space, Fits])
    ∃ pc x₀ ti z t,
      Runs 4 program.initFreshProg ⟨0, fresh 0⟩ ⟨pc, x₀⟩ ti ∧
      I.RunsOps I.prepareRegs [] x₀ [.dequeue] [⟨.dequeue, none, []⟩] [] z t ∧
      I.rep [] z ∧ z.mem 100 = 9 ∧ ti ≤ 13 ∧
      t ≤ 153 * MemoryQueueMethod.realizes_method.factor + 1 := by
  let I := implementation 4 5 0 (by norm_num [space, Fits])
  have hb : (fresh 0).Bounded 4 := by
    constructor
    · intro i
      change Fits 4 (if i = register 3 then 0 else if i = register 11 then 5 else 0)
      split_ifs <;> norm_num [Fits]
    · intro a
      change Fits 4 (if a < 5 then 7 else if a < 11 then 0 else 9)
      split_ifs <;> norm_num [Fits]
  have hfr : (fresh 0).regs program.frontierReg = 5 := by simp [fresh, program, register]
  have hpar : ∀ j, (fresh 0).regs (program.initParams j) = (0 : ℕ) := by
    intro j
    simp [fresh, program]
  have hspace : I.space = space 0 := implementation_space 4 5 0 _
  have hz : ∀ a ∈ (Block.mk 5 I.space).footprint, (fresh 0).mem a = 0 := by
    intro a ha
    rw [hspace] at ha
    simp only [Block.mem_footprint, Block.Owns, space] at ha
    simp [fresh, show ¬a < 5 by omega, show a < 11 by omega]
  have hv : (Queue.WordRAM.spec 4 0).ValidOpSeq [] [.dequeue] := by
    apply ((Queue.WordRAM.spec 4 0).validOpSeq_iff_validHistory [] [.dequeue]).mpr
    exact ⟨trivial, trivial⟩
  obtain ⟨pc, x₀, ti, tr, q, z, t, hri, _, hm, hro, hops, htr, hr, hti, hto⟩ :=
    I.run_ops_exact_fresh hb hfr hpar hz [.dequeue] hv
  have hcanonical := ((Queue.WordRAM.spec 4 0).validTranscript_iff_run [] tr q).mp htr
  rw [hops] at hcanonical
  have hq : q = [] := hcanonical.2.1
  have ht : tr = [⟨.dequeue, none, []⟩] := hcanonical.2.2
  subst q
  subst tr
  have hOutside : 100 ∉ (Block.mk 5 I.space).footprint := by
    rw [hspace]
    norm_num [Block.mem_footprint, Block.Owns, space]
  have hfinal : z.mem 100 = 9 := ((runsOps_modifies (capacity := 0) hro) 100 hOutside).trans
    ((hm 100 hOutside).trans (by rfl))
  have htime : t ≤ 153 * MemoryQueueMethod.realizes_method.factor + 1 := by
    have hc : ∀ q o, I.charge q o = 153 * MemoryQueueMethod.realizes_method.factor :=
      fun q o => implementation_charge 4 5 0 _ q o
    have hp : I.initPotential = 0 := implementation_initPotential 4 5 0 _
    simp only [hc, hp, StateTransitionSpec.totalCostTranscript_const] at hto
    change t + _ ≤ 1 * (153 * MemoryQueueMethod.realizes_method.factor + 1) + 0 at hto
    omega
  have hiTime : I.initTime = 13 := implementation_initTime 4 5 0 _
  rw [hiTime] at hti
  exact ⟨pc, x₀, ti, z, t, hri, hro, hr, hfinal, hti, htime⟩

-- The existing dirty-clear API has a LINEAR initialization allowance. It inhabits the local
-- framed target and preserves unowned memory; it is separate from literal source allocLayout.
example :
    let I := implementation 4 5 2 (by norm_num [space, Fits])
    ∃ y, ExecWithin 4 program.initClear (⟨(fresh 2).regs, fun _ => 7⟩ : Data registers) y 43 ∧
      I.rep [] y ∧ y.mem 100 = 7 := by
  let I := implementation 4 5 2 (by norm_num [space, Fits])
  let x : Data registers := ⟨(fresh 2).regs, fun _ => 7⟩
  have hb : x.Bounded 4 := by
    constructor
    · intro i
      change Fits 4 (if i = register 3 then 2 else if i = register 11 then 5 else 0)
      split_ifs <;> norm_num [Fits]
    · exact fun _ => by norm_num [Fits]
  have hfr : x.regs program.frontierReg = 5 := by simp [x, fresh, program, register]
  have hpar : ∀ j, x.regs (program.initParams j) = (2 : ℕ) := by
    intro j
    simp [x, fresh, program]
  obtain ⟨y, he, _, hr, _, hm⟩ := I.initClear_exec hb hfr hpar
  have hs : I.space = space 2 := implementation_space 4 5 2 _
  have ht : I.initTime = 13 := implementation_initTime 4 5 2 _
  rw [hs, ht] at he
  have hout : 100 ∉ (Block.mk 5 I.space).footprint := by
    rw [hs]
    norm_num [space, Block.mem_footprint, Block.Owns]
  exact ⟨y, he, hr, hm 100 hout⟩

end ComplexityTests.WordRAMRealizationQueueAdapter
