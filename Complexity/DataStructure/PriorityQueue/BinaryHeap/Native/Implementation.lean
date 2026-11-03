/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.PriorityQueue.BinaryHeap.Native.Base
public import Complexity.DataStructure.PriorityQueue.WordRAM.Decode

/-!
# Raw native execution of the memory heap

The single global heap program is certified through its existing operation realizations and
Backend. Arguments must already match the raw calling convention; argument delivery is not
executed for free. Zero staging, dispatch and the lookup key copy are actual charged code.

The representation and initialization are inherited from `subroutineBase`. Typed extraction
uses the exact erased original source result, not an unchecked natural-handle observation.

## Main results

* `subroutineImpl`: the existing raw heap `StateTransitionImpl`, including actual method execution.
* `subroutineImpl_exec_memoryState`: every matching actual raw execution leaves the original
  memory program's complete state.

Complete allocated clients and native Dijkstra have their separate contracts; no old exact
clock or register count is inherited.
-/

public section

namespace Cslib.DataStructure.PriorityQueue.BinaryHeap.Native

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure
open Cslib.DataStructure.PriorityQueue.WordRAM
open Cslib.DataStructure.PriorityQueue.BinaryHeap (space)

private theorem decode_body {w n K : ℕ} (L : Memory.Layout n) (e : Memory.State)
    (o : IndexedMinPQ.Op n) (y z : Data Program.registers)
    (hout : ∀ j, y.regs (Backend.tmp Program.family (.inl ((backend n K L).tag o))
        (Fin.castAdd ((certificates ((backend n K L).tag o)).realizes.scratchSize + 1) j)) =
      (certificates ((backend n K L).tag o)).output
        ((Memory.spec w).clientResult e
          ((certificates ((backend n K L).tag o)).prog ((backend n K L).arg o))) j)
    (hflag : z.regs Program.code.outFlag = y.regs Program.code.outFlag)
    (hvalue : z.regs Program.code.outV = y.regs Program.code.outV)
    (hkey : z.regs Program.code.outK =
      (match o with | .getKey _ => y.regs Program.code.outV | _ => y.regs Program.code.outK)) :
    Program.code.decode (K_max := K) o z.regs =
      some ((Memory.spec w).clientResult e (Memory.ops L o)) := by
  cases o with
  | isEmpty =>
    have h0 := hout (0 : Fin 2)
    dsimp only [backend] at h0
    rw [Program.output_bank 0 (0 : Fin 2) 0 rfl] at h0
    change y.regs (Program.bank 0) =
      ((Memory.spec w).clientResult e (Memory.isEmpty L)).toNat at h0
    apply PQCode.decode_isEmpty
    exact hflag.trans (by simpa only [Program.code_outFlag, Memory.ops] using h0)
  | getKey v =>
    have h0 := hout (0 : Fin 2)
    have h1 := hout (1 : Fin 2)
    dsimp only [backend] at h0 h1
    rw [Program.output_bank 1 (0 : Fin 2) 0 rfl] at h0
    rw [Program.output_bank 1 (1 : Fin 2) 1 rfl] at h1
    change y.regs (Program.bank 0) =
      optionWords ((Memory.spec w).clientResult e (Memory.getKey L v)) 0 at h0
    change y.regs (Program.bank 1) =
      optionWords ((Memory.spec w).clientResult e (Memory.getKey L v)) 1 at h1
    cases ha : (Memory.spec w).clientResult e (Memory.getKey L v) with
    | none =>
      have hf : z.regs Program.code.outFlag = 0 := hflag.trans (by
        simpa only [Program.code_outFlag, ha, optionWords_none, Matrix.cons_val_zero] using h0)
      simpa only [Memory.ops, ha] using PQCode.decode_getKey_none Program.code z.regs v hf
    | some k =>
      have hf : z.regs Program.code.outFlag = 1 := hflag.trans (by
        simpa only [Program.code_outFlag, ha, optionWords_some, Matrix.cons_val_zero] using h0)
      have hk : z.regs Program.code.outK = k := hkey.trans (by
        simpa only [Program.code_outV, ha, optionWords_some, Matrix.cons_val_one,
          Matrix.cons_val_zero] using h1)
      simpa only [Memory.ops, ha] using
        PQCode.decode_getKey_some Program.code z.regs v (by rw [hf]; decide) hk
  | insert v k =>
    exact congrArg some (Subsingleton.elim _ _)
  | decreaseKey v k =>
    exact congrArg some (Subsingleton.elim _ _)
  | extractMin =>
    have h0 := hout (0 : Fin 3)
    have h1 := hout (1 : Fin 3)
    have h2 := hout (2 : Fin 3)
    dsimp only [backend] at h0 h1 h2
    rw [Program.output_bank 4 (0 : Fin 3) 0 rfl] at h0
    rw [Program.output_bank 4 (1 : Fin 3) 1 rfl] at h1
    rw [Program.output_bank 4 (2 : Fin 3) 2 rfl] at h2
    change y.regs (Program.bank 0) = WordEncoding.encode (α := Option (ℕ × ℕ))
      ((Memory.spec w).clientResult e
        ((Memory.extractMin L).map (Option.map fun a => (a.1.val, a.2)))) 0 at h0
    change y.regs (Program.bank 1) = WordEncoding.encode (α := Option (ℕ × ℕ))
      ((Memory.spec w).clientResult e
        ((Memory.extractMin L).map (Option.map fun a => (a.1.val, a.2)))) 1 at h1
    change y.regs (Program.bank 2) = WordEncoding.encode (α := Option (ℕ × ℕ))
      ((Memory.spec w).clientResult e
        ((Memory.extractMin L).map (Option.map fun a => (a.1.val, a.2)))) 2 at h2
    rw [extractMin_result w ⟨n, L⟩ e] at h0 h1 h2
    cases ha : (Memory.spec w).clientResult e (Memory.extractMin L) with
    | none =>
      rw [ha] at h0
      change y.regs (Program.bank 0) = 0 at h0
      have hf : z.regs Program.code.outFlag = 0 := hflag.trans (by
        simpa only [Program.code_outFlag] using h0)
      simpa only [Memory.ops, ha] using PQCode.decode_extractMin_none Program.code z.regs hf
    | some a =>
      rcases a with ⟨v, k⟩
      rw [ha] at h0 h1 h2
      change y.regs (Program.bank 0) = 1 at h0
      change y.regs (Program.bank 1) = v.val at h1
      change y.regs (Program.bank 2) = k at h2
      have hf : z.regs Program.code.outFlag = 1 := hflag.trans (by
        simpa only [Program.code_outFlag] using h0)
      have hv : z.regs Program.code.outV = v.val := hvalue.trans (by
        simpa only [Program.code_outV] using h1)
      have hk : z.regs Program.code.outK = k := hkey.trans (by
        simpa only [Program.code_outK] using h2)
      simpa only [Memory.ops, ha] using
        PQCode.decode_extractMin_some Program.code z.regs v (by rw [hf]; decide) hv hk

private theorem raw_exec
    {w n K base : ℕ} (hn : Fits w n) (hK : Fits w K)
    {s : (indexedMinPQSpec n K).State} {x : Data Program.registers} (o : IndexedMinPQ.Op n)
    (hr : Representation.Rep base hn hK s x) (hv : IndexedMinPQ.valid K s o)
    (ha : Program.code.argMatch o x.regs) :
    ∃ z s' a steps, Exec w Program.code.code x z steps ∧
      (indexedMinPQSpec n K).step s o s' a ∧ Program.code.decode (K_max := K) o z.regs = some a ∧
      Representation.Rep base hn hK s' z ∧
      Modifies (Block.mk base (space n)).footprint x.mem z.mem ∧
      steps ≤ Backend.factor Program.family * (memoryBound o + 1) + 8 ∧
      memoryState (Backend.frontier Program.family) z = (Memory.spec w).clientState
        (memoryState (Backend.frontier Program.family) x)
        (Memory.ops (Memory.compactLayout n base) o) := by
  let L := Memory.compactLayout n base
  let hL := Memory.valid_compactLayout (base := base) hn hK
  let S : Backend (indexedMinPQSpec n K) Program.family :=
    (backend n K L).extend Program.initialization
  have hI : S.Implements (Memory.refinement hL) := (implements L hL).extend Program.initialization
  let x₀ := x.set (Program.bank 3) 0
  obtain ⟨hbx₀, hm₀, hl₀⟩ := Program.stage_zero x hr.bounded
  have hr₀ : Representation.Rep base hn hK s x₀ := hr.congr
    (fun _ _ => rfl) (le_of_eq (congrArg Memory.State.frontier hm₀).symm) hl₀ hbx₀
  obtain ⟨hi, habs, _⟩ := (Backend.rep_iff hI s x₀).mp hr₀.1
  have hv₀ : (indexedMinPQSpec n K).valid
      ((Memory.refinement hL).abs (memoryState (Backend.frontier Program.family) x₀)) o := by
    rwa [habs]
  let e := memoryState (Backend.frontier Program.family) x₀
  have hrun := hI.run o e
  have hvalid := ((Memory.spec w).demonicValid_iff_validHistory_runClient _ _).mp
    ((Memory.refinement hL).valid o hi hv₀)
  have hhist : (Memory.spec w).clientHistory e ((Memory.refinement hL).methods o) =
      (Memory.spec w).clientHistory e ((Program.family (S.tag o)).prog (S.arg o)) :=
    congrArg (fun t => t.2.2) hrun
  obtain ⟨_, hsafe⟩ := hI.entry o (wellFormed_memoryState hbx₀) hi hv₀
  have hlive : x₀.regs ∘ Backend.src Program.family (S.tag o) =
      (Program.family (S.tag o)).input (S.arg o) :=
    (Program.stage_zero_input ((backend n K L).tag o) x).trans
      (Program.method_arguments L x o hr.2 ha)
  obtain ⟨y, N, he, _, hstate, hout, hby, hframe⟩ :=
    Backend.exists_exec_live Program.family (S.tag o) (S.arg o) hbx₀ hlive hsafe
      (hhist ▸ hvalid)
  let a := S.answer o ((Memory.spec w).clientResult e
    ((Program.family (S.tag o)).prog (S.arg o)))
  have hinstall := Backend.install_eq_self Program.family (S.tag o) (S.arg o) x₀ hlive
  have hbe : S.exec w x₀ o a y N := (Backend.exec_iff S w x₀ y o a N).mpr
    ⟨by simpa only [Backend.prepare, hinstall] using he, _, rfl, hout⟩
  have hN : N ≤ Backend.factor Program.family * (memoryBound o + 1) :=
    bound_extend Program.initialization L hL hr₀.1 hv hbe
  obtain ⟨s', hstep, hrepY⟩ := (Backend.implementation hI).correct hr₀.1 hv hbe
  have hlY : ∀ i : Fin 4,
      y.regs (Program.argument (i.castAdd 2)) = layoutWords ⟨n, L⟩ i := by
    intro i
    calc
      y.regs (Program.argument (i.castAdd 2)) = x₀.regs (Program.argument (i.castAdd 2)) :=
        hframe _ (by rw [Program.argument_source]; exact Backend.src_ne_frontier _ _ _)
          (fun j => by rw [Program.argument_source]; exact (Backend.src_ne_tmp _ _ _ _ _).symm)
      _ = layoutWords ⟨n, L⟩ i := hr₀.2 i
  have hrY : Representation.Rep base hn hK s' y := ⟨hrepY, hlY⟩
  have hmodY := Backend.modifies (M := Memory.framed hL) hI hr₀.1 hv hbe
  obtain ⟨z, hez, hbz, hmz, hfz, hlz, hflag, hvalue, hkey⟩ :=
    Program.wrap_body L x o ha (N := N) ⟨N, le_rfl, he⟩ hby
  have hzstate : memoryState (Backend.frontier Program.family) z =
      memoryState (Backend.frontier Program.family) y := by
    apply Memory.State.ext
    · exact hmz
    · change z.regs (Backend.frontier Program.family) = y.regs (Backend.frontier Program.family)
      rwa [← Program.code_frontier]
  have hrZ : Representation.Rep base hn hK s' z := hrY.congr
    (fun c _ => congrFun hmz c) (le_of_eq (congrArg Memory.State.frontier hzstate).symm) hlz hbz
  have hdecode : Program.code.decode (K_max := K) o z.regs =
      some ((Memory.spec w).clientResult e (Memory.ops L o)) := by
    cases o <;> exact decode_body L e _ y z hout hflag hvalue hkey
  have hanswer : (Memory.spec w).clientResult e (Memory.ops L o) = a := congrArg Prod.fst hrun
  have hstateY : memoryState (Backend.frontier Program.family) y =
      (Memory.spec w).clientState e (Memory.ops L o) :=
    hstate.trans (congrArg (fun t => t.2.1) hrun).symm
  obtain ⟨steps, hsteps, hez⟩ := hez
  refine ⟨z, s', a, steps, hez, hstep, hdecode.trans (congrArg some hanswer), hrZ, ?_,
    by omega, ?_⟩
  · intro c hc
    have hc' : c ∉ L.footprint := by
      change c ∉ (Memory.compactLayout n base).footprint
      rwa [Memory.compactLayout_footprint]
    have hm := hmodY c (by
      simpa only [Memory.Framed.region_eq_footprint (Memory.framed hL) rfl,
        Memory.framed_footprint] using hc')
    exact (congrFun hmz c).trans hm
  · rw [hzstate, hstateY]
    exact congrArg (fun e => (Memory.spec w).clientState e (Memory.ops L o)) hm₀

private noncomputable def implementationImpl {w n K base : ℕ}
    (hS : Fits w (base + space n)) (hK : Fits w K) :
    Cslib.DataStructure.WordRAM.StateTransitionImpl Program.code.toSubroutineCode
      (indexedMinPQSpec n K) w base ![n] (IndexedMinPQ.empty n) where
  toSubroutineBase := subroutineBase hS hK
  step_exec {s x} o hr hv ha := by
    have hn : Fits w n := hS.of_le (by unfold space; omega)
    have hrep : Representation.Rep base hn hK s x :=
      (subroutineBase_rep_iff hS hK s x).mp hr
    rw [subroutineBase_argMatch] at ha
    obtain ⟨y, s', a, N, he, hstep, hd, hr', hm, hb, _⟩ := raw_exec hn hK o hrep hv ha
    refine ⟨y, s', a, N, he, hstep, ?_, (subroutineBase_rep_iff hS hK s' y).mpr hr', ?_, ?_⟩
    · rwa [subroutineBase_decode]
    · rwa [subroutineBase_space]
    · simpa only [subroutineBase_potential, subroutineBase_charge, Nat.add_zero] using hb

/-- The single global raw heap program implements the indexed priority queue under the original
end-fit and key-fit assumptions. Argument matching is an explicit calling-convention premise;
the charged method code includes zero staging, dispatch and the lookup result copy. -/
noncomputable def subroutineImpl {w n K base : ℕ}
    (hS : Fits w (base + space n)) (hK : Fits w K) :
    Cslib.DataStructure.WordRAM.StateTransitionImpl Program.code.toSubroutineCode
      (indexedMinPQSpec n K) w base ![n] (IndexedMinPQ.empty n) := implementationImpl hS hK

private theorem subroutineImpl_toBase_aux {w n K base : ℕ}
    (hS : Fits w (base + space n)) (hK : Fits w K) :
    (subroutineImpl hS hK).toSubroutineBase = subroutineBase hS hK := rfl

/-- Raw initialization, representation, charge and argument metadata are inherited unchanged. -/
theorem subroutineImpl_toBase {w n K base : ℕ}
    (hS : Fits w (base + space n)) (hK : Fits w K) :
    (subroutineImpl hS hK).toSubroutineBase = subroutineBase hS hK :=
  subroutineImpl_toBase_aux hS hK

/-- An arbitrary actual raw execution leaves the complete state of the original source method,
not merely a state with the same typed answer. Determinism transfers the certified execution's
literal memory/frontier equality to the supplied execution. -/
theorem subroutineImpl_exec_memoryState {w n K base : ℕ}
    (hS : Fits w (base + space n)) (hK : Fits w K)
    {s : (indexedMinPQSpec n K).State} {x y : Data Program.registers} {N : ℕ}
    (o : IndexedMinPQ.Op n) (hr : (subroutineImpl hS hK).rep s x)
    (hv : IndexedMinPQ.valid K s o) (ha : (subroutineImpl hS hK).argMatch o x.regs)
    (he : Exec w Program.code.code x y N) :
    memoryState (Backend.frontier Program.family) y = (Memory.spec w).clientState
      (memoryState (Backend.frontier Program.family) x)
      (Memory.ops (Memory.compactLayout n base) o) := by
  rw [subroutineImpl_toBase] at hr ha
  have hn : Fits w n := hS.of_le (by unfold space; omega)
  have hrep : Representation.Rep base hn hK s x :=
    (subroutineBase_rep_iff hS hK s x).mp hr
  rw [subroutineBase_argMatch] at ha
  obtain ⟨z, _, _, _, hez, _, _, _, _, _, hstate⟩ := raw_exec hn hK o hrep hv ha
  have hy : y = z := (he.unique hez).1
  rwa [hy]

end Cslib.DataStructure.PriorityQueue.BinaryHeap.Native
