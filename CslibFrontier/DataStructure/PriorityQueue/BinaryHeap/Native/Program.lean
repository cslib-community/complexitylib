/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.PriorityQueue.BinaryHeap.Native.Backend
public import CslibFrontier.DataStructure.PriorityQueue.BinaryHeap.Native.Initialize
public import CslibFrontier.DataStructure.PriorityQueue.WordRAM.Basic

/-!
# The binary heap's uniform native register interface

The existing `PQCode` interface keeps its three independent nonzero tag bits. It does not encode
five operation tags as a single word, so a one-bit heap domain is not strengthened by dispatch.
Operation bodies are the existing Backend family. Its bank also includes the two certified
initialization routines before the register count is chosen.

## Main definitions

* `family`: the five operation bodies and two existing initialization certificates.
* `code`: the existing priority-queue ABI, with a paid native dispatcher and result-key copy.

## Main results

* `span_exec`, `setup_registers`: actual reservation and metadata computation on this register ABI.
* `initFresh_exec`: the compact local-zero fresh initializer, with whole-memory identity.

Method correctness still requires live argument delivery, persistent layout fields and the source
heap invariant. No old clock or register count is inherited by this interface.
-/

public section

namespace Cslib.DataStructure.PriorityQueue.BinaryHeap.Native.Program

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure
open Cslib.DataStructure.PriorityQueue.WordRAM

/-- The two initialization routines, fixed before every runtime dimension and base. -/
@[expose] noncomputable def initialization : Fin 2 → Certificate .exact :=
  ![Certificate.ofRealizes Initialize.realizes_reserve,
    Certificate.ofRealizes Initialize.realizes_metadata]

/-- One static register family for all methods and both initialization routines. -/
@[expose] noncomputable def family : Fin 5 ⊕ Fin 2 → Certificate .exact :=
  Sum.elim certificates initialization

/-- The runtime parameter-independent register count. -/
noncomputable abbrev registers := Backend.registers family

/-- The common method-argument positions: n, count address, count length, base, handle and key. -/
noncomputable def argument (i : Fin 6) : Fin registers := Backend.src family (.inl 2) i

/-- Four common result/scratch slots, also used for three tag bits and a staged zero. -/
noncomputable def bank (i : Fin 4) : Fin registers :=
  Backend.tmp family (.inr 1) ⟨i.val, by have := i.isLt; change i.val < 3 + _ + 1; omega⟩

private theorem argument_source_aux (i : Fin 6) :
    argument i = Backend.src family (.inl 2) i := rfl

/-- The persistent/payload ABI uses the existing common Backend source positions. -/
theorem argument_source (i : Fin 6) : argument i = Backend.src family (.inl 2) i :=
  argument_source_aux i

private theorem argument_injective : Function.Injective argument := by
  intro i j h
  exact Backend.src_injective family (.inl 2) h

private theorem bank_injective : Function.Injective bank := by
  intro i j h
  have he := Backend.tmp_injective family (.inr 1) h
  apply Fin.ext
  exact congrArg (fun z : Fin (3 + Initialize.realizes_metadata.scratchSize + 1) => z.val) he

private theorem bank_ne_argument (i : Fin 4) (j : Fin 6) : bank i ≠ argument j :=
  (Backend.src_ne_tmp family (.inl 2) (.inr 1) j _).symm

private theorem argument_ne_frontier (i : Fin 6) :
    argument i ≠ Backend.frontier family := Backend.src_ne_frontier _ _ _

private theorem bank_ne_frontier (i : Fin 4) :
    bank i ≠ Backend.frontier family := Backend.tmp_ne_frontier _ _ _

private noncomputable def reserveScratch
    (i : Fin (1 + Initialize.realizes_reserve.scratchSize + 1)) : Fin registers :=
  if i.val = 0 then argument 3 else
    Backend.tmp family (.inr 0) ⟨i.val - 1, by
      have := i.isLt
      change i.val - 1 < 1 + Initialize.realizes_reserve.scratchSize + 1
      omega⟩

private noncomputable def metadataScratch
    (i : Fin (3 + Initialize.realizes_metadata.scratchSize + 1)) : Fin registers :=
  if i.val = 0 then bank 0 else if i.val = 1 then argument 1 else
    if i.val = 2 then argument 2 else
      Backend.tmp family (.inr 1) ⟨i.val - 2, by
        have := i.isLt
        change i.val - 2 < 3 + Initialize.realizes_metadata.scratchSize + 1
        omega⟩

/-- Reserve the compact 3n+1 span, returning its old frontier in the persistent base slot. -/
private noncomputable def reserve : Code .exact registers :=
  Initialize.realizes_reserve.code (Backend.frontier family) (fun _ => argument 0) reserveScratch

/-- Stage the count address and length while retaining the live dimension and base inputs. -/
private noncomputable def setup : Code .exact registers :=
  Initialize.realizes_metadata.code (Backend.frontier family)
    ![argument 0, argument 3] metadataScratch

/-- A key lookup returns an OptionNat pair; the established PQ ABI places its key in slot two. -/
private noncomputable def get : Code .exact registers :=
  .seq (Backend.code family (.inl 1)) (.op (.copy (bank 2) (bank 1)))

/-- One paid zero staging and three tests dispatch the independent flag bits. -/
private noncomputable def dispatch : Code .exact registers :=
  .seq (.op (.const (bank 3) 0)) <|
    .branch (.eq (bank 0) (bank 3))
      (.branch (.eq (bank 1) (bank 3))
        (.branch (.eq (bank 2) (bank 3)) (Backend.code family (.inl 0)) get)
        (.branch (.eq (bank 2) (bank 3))
          (Backend.code family (.inl 2)) (Backend.code family (.inl 3))))
      (Backend.code family (.inl 4))

/-- The existing uniform priority-queue ABI, with no runtime-sized native tag. -/
noncomputable def code : PQCode .exact registers where
  allocSpan := reserve
  initSetup := setup
  code := dispatch
  frontierReg := Backend.frontier family
  baseReg := argument 3
  initParams := ![argument 0]
  curReg := bank 0
  zeroReg := bank 1
  oneReg := bank 2
  incCur := .exactBin .add (bank 0) (bank 0) (bank 2)
  input r := decide (r = bank 0 ∨ r = bank 1 ∨ r = bank 2 ∨
    r = argument 4 ∨ r = argument 5)
  output := bank 0
  nReg := argument 0
  tag2 := bank 0
  tag1 := bank 1
  tag0 := bank 2
  argV := argument 4
  argK := argument 5
  outFlag := bank 0
  outV := bank 1
  outK := bank 2
  initParams_eq := rfl
  nReg_ne_frontier := argument_ne_frontier 0
  args_nodup := by
    have h01 : bank 0 ≠ bank 1 := bank_injective.ne (by decide)
    have h02 : bank 0 ≠ bank 2 := bank_injective.ne (by decide)
    have h12 : bank 1 ≠ bank 2 := bank_injective.ne (by decide)
    have h45 : argument 4 ≠ argument 5 := argument_injective.ne (by decide)
    simp only [List.nodup_cons, List.mem_cons, not_or,
      List.not_mem_nil, List.nodup_nil, not_false_eq_true, and_true]
    exact ⟨⟨h01, h02, bank_ne_argument 0 4, bank_ne_argument 0 5⟩,
      ⟨⟨h12, bank_ne_argument 1 4, bank_ne_argument 1 5⟩,
        ⟨⟨bank_ne_argument 2 4, bank_ne_argument 2 5⟩, h45⟩⟩⟩
  tag2_input := by simp
  tag1_input := by simp
  tag0_input := by simp
  argV_input := by simp
  argK_input := by simp
  output_eq := rfl

private theorem code_frontier_aux : code.frontierReg = Backend.frontier family := rfl

/-- The ABI uses the common native frontier register. -/
theorem code_frontier : code.frontierReg = Backend.frontier family := code_frontier_aux

private theorem code_nReg_aux : code.nReg = argument 0 := rfl

/-- The runtime dimension occupies the first method-argument position. -/
theorem code_nReg : code.nReg = argument 0 := code_nReg_aux

private theorem code_baseReg_aux : code.baseReg = argument 3 := rfl

/-- The persistent compact base occupies the fourth method-argument position. -/
theorem code_baseReg : code.baseReg = argument 3 := code_baseReg_aux

/-- Operation argument delivery preserves the frontier. -/
theorem code_input_frontier : code.input (Backend.frontier family) = false := by
  change decide (_ ∨ _ ∨ _ ∨ _ ∨ _) = false
  simp only [decide_eq_false_iff_not, not_or]
  exact ⟨(bank_ne_frontier 0).symm, (bank_ne_frontier 1).symm,
    (bank_ne_frontier 2).symm, (argument_ne_frontier 4).symm,
    (argument_ne_frontier 5).symm⟩

/-- Operation argument delivery preserves all four persistent layout words. -/
theorem code_input_argument (i : Fin 4) : code.input (argument (i.castAdd 2)) = false := by
  change decide (_ ∨ _ ∨ _ ∨ _ ∨ _) = false
  simp only [decide_eq_false_iff_not, not_or]
  refine ⟨(bank_ne_argument 0 (i.castAdd 2)).symm,
    (bank_ne_argument 1 (i.castAdd 2)).symm, (bank_ne_argument 2 (i.castAdd 2)).symm,
    argument_injective.ne ?_, argument_injective.ne ?_⟩
  · intro he
    have hh : i.val = 4 := congrArg (fun z : Fin 6 => z.val) he
    have hi := i.isLt
    omega
  · intro he
    have hh : i.val = 5 := congrArg (fun z : Fin 6 => z.val) he
    have hi := i.isLt
    omega

private theorem code_outFlag_aux : code.outFlag = bank 0 := rfl
private theorem code_outV_aux : code.outV = bank 1 := rfl
private theorem code_outK_aux : code.outK = bank 2 := rfl

/-- The optional-result presence flag uses the first common output slot. -/
theorem code_outFlag : code.outFlag = bank 0 := code_outFlag_aux

/-- An extracted handle uses the second common output slot. -/
theorem code_outV : code.outV = bank 1 := code_outV_aux

/-- The established PQ key output uses the third common output slot. -/
theorem code_outK : code.outK = bank 2 := code_outK_aux

private theorem output_bank_aux (i : Fin 5) (j : Fin (certificates i).l) (a : Fin 4)
    (he : j.val = a.val) :
    Backend.tmp family (.inl i) (Fin.castAdd ((certificates i).realizes.scratchSize + 1) j) =
      bank a := Backend.tmp_eq_of_val_eq family (.inl i) (.inr 1) he

/-- Each selected body's output position is the same position in the common ABI bank. -/
theorem output_bank (i : Fin 5) (j : Fin (certificates i).l) (a : Fin 4)
    (he : j.val = a.val) :
    Backend.tmp family (.inl i) (Fin.castAdd ((certificates i).realizes.scratchSize + 1) j) =
      bank a := output_bank_aux i j a he

private theorem clear_nodup_aux :
    [code.curReg, code.zeroReg, code.oneReg, code.baseReg, code.frontierReg].Nodup := by
  change [bank 0, bank 1, bank 2, argument 3, Backend.frontier family].Nodup
  have h01 : bank 0 ≠ bank 1 := bank_injective.ne (by decide)
  have h02 : bank 0 ≠ bank 2 := bank_injective.ne (by decide)
  have h12 : bank 1 ≠ bank 2 := bank_injective.ne (by decide)
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, List.nodup_nil,
    not_false_eq_true, and_true]
  exact ⟨⟨h01, h02, bank_ne_argument 0 3, bank_ne_frontier 0⟩,
    ⟨⟨h12, bank_ne_argument 1 3, bank_ne_frontier 1⟩,
      ⟨⟨bank_ne_argument 2 3, bank_ne_frontier 2⟩, argument_ne_frontier 3⟩⟩⟩

/-- The existing generic zero-fill routine has five distinct registers on this ABI. -/
theorem clear_nodup :
    [code.curReg, code.zeroReg, code.oneReg, code.baseReg, code.frontierReg].Nodup :=
  clear_nodup_aux

private theorem params_not_clear_aux (i : Fin 1) :
    code.initParams i ∉ [code.curReg, code.zeroReg, code.oneReg] := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  change argument 0 ∉ [bank 0, bank 1, bank 2]
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨(bank_ne_argument 0 0).symm, (bank_ne_argument 1 0).symm,
    (bank_ne_argument 2 0).symm⟩

/-- Generic zero-fill retains the runtime dimension parameter. -/
theorem params_not_clear (i : Fin 1) :
    code.initParams i ∉ [code.curReg, code.zeroReg, code.oneReg] := params_not_clear_aux i

private theorem incCur_eval_aux {w : ℕ} {x : Data registers}
    (hone : x.regs code.oneReg = 1) (hfit : Fits w (x.regs code.curReg + 1)) :
    code.incCur.eval w x = some (x.set code.curReg (x.regs code.curReg + 1)) := by
  dsimp only [code] at hone hfit ⊢
  simp only [Op.eval_exactBin, BinOp.evalExact, hone, Option.bind_some, Data.put_of_fits hfit]

/-- The generic clear loop's increment is the original exact addition, under its visible fit. -/
theorem incCur_eval {w : ℕ} {x : Data registers} (hone : x.regs code.oneReg = 1)
    (hfit : Fits w (x.regs code.curReg + 1)) :
    code.incCur.eval w x = some (x.set code.curReg (x.regs code.curReg + 1)) :=
  incCur_eval_aux hone hfit

private theorem method_src_eq_argument (i : Fin 5) (j : Fin (certificates i).k) (a : Fin 6)
    (he : j.val = a.val) : Backend.src family (.inl i) j = argument a :=
  Backend.src_eq_of_val_eq family (.inl i) (.inl 2) he

/-- The existing PQ calling convention delivers the actual selected body's live words; layouts
and operation payloads are runtime values in the same fixed bank. No prepare step is assumed. -/
theorem method_arguments {n K : ℕ} (L : Memory.Layout n) (x : Data registers)
    (o : IndexedMinPQ.Op n)
    (hl : ∀ i : Fin 4, x.regs (argument (i.castAdd 2)) = layoutWords ⟨n, L⟩ i)
    (ha : PQCode.argMatch code o x.regs) :
    x.regs ∘ Backend.src family (.inl ((backend n K L).tag o)) =
      (certificates ((backend n K L).tag o)).input ((backend n K L).arg o) := by
  cases o with
  | isEmpty =>
    change x.regs ∘ Backend.src family (.inl 0) = layoutWords ⟨n, L⟩
    funext j
    change Fin 4 at j
    fin_cases j <;>
      first
      | exact (congrArg x.regs (method_src_eq_argument 0 _ (0 : Fin 6) rfl)).trans (hl 0)
      | exact (congrArg x.regs (method_src_eq_argument 0 _ (1 : Fin 6) rfl)).trans (hl 1)
      | exact (congrArg x.regs (method_src_eq_argument 0 _ (2 : Fin 6) rfl)).trans (hl 2)
      | exact (congrArg x.regs (method_src_eq_argument 0 _ (3 : Fin 6) rfl)).trans (hl 3)
  | getKey v =>
    rcases ha with ⟨_, _, _, hv⟩
    change x.regs ∘ Backend.src family (.inl 1) = indexWords (⟨n, L⟩, v.val)
    funext j
    change Fin 5 at j
    fin_cases j <;>
      first
      | exact (congrArg x.regs (method_src_eq_argument 1 _ (0 : Fin 6) rfl)).trans (hl 0)
      | exact (congrArg x.regs (method_src_eq_argument 1 _ (1 : Fin 6) rfl)).trans (hl 1)
      | exact (congrArg x.regs (method_src_eq_argument 1 _ (2 : Fin 6) rfl)).trans (hl 2)
      | exact (congrArg x.regs (method_src_eq_argument 1 _ (3 : Fin 6) rfl)).trans (hl 3)
      | exact (congrArg x.regs (method_src_eq_argument 1 _ (4 : Fin 6) rfl)).trans (hv)
  | insert v k =>
    rcases ha with ⟨_, _, _, hv, hk⟩
    change x.regs ∘ Backend.src family (.inl 2) = updateWords ((⟨n, L⟩, v.val), k)
    funext j
    change Fin 6 at j
    fin_cases j <;>
      first
      | exact (congrArg x.regs (method_src_eq_argument 2 _ (0 : Fin 6) rfl)).trans (hl 0)
      | exact (congrArg x.regs (method_src_eq_argument 2 _ (1 : Fin 6) rfl)).trans (hl 1)
      | exact (congrArg x.regs (method_src_eq_argument 2 _ (2 : Fin 6) rfl)).trans (hl 2)
      | exact (congrArg x.regs (method_src_eq_argument 2 _ (3 : Fin 6) rfl)).trans (hl 3)
      | exact (congrArg x.regs (method_src_eq_argument 2 _ (4 : Fin 6) rfl)).trans (hv)
      | exact (congrArg x.regs (method_src_eq_argument 2 _ (5 : Fin 6) rfl)).trans (hk)
  | decreaseKey v k =>
    rcases ha with ⟨_, _, _, hv, hk⟩
    change x.regs ∘ Backend.src family (.inl 3) = updateWords ((⟨n, L⟩, v.val), k)
    funext j
    change Fin 6 at j
    fin_cases j <;>
      first
      | exact (congrArg x.regs (method_src_eq_argument 3 _ (0 : Fin 6) rfl)).trans (hl 0)
      | exact (congrArg x.regs (method_src_eq_argument 3 _ (1 : Fin 6) rfl)).trans (hl 1)
      | exact (congrArg x.regs (method_src_eq_argument 3 _ (2 : Fin 6) rfl)).trans (hl 2)
      | exact (congrArg x.regs (method_src_eq_argument 3 _ (3 : Fin 6) rfl)).trans (hl 3)
      | exact (congrArg x.regs (method_src_eq_argument 3 _ (4 : Fin 6) rfl)).trans (hv)
      | exact (congrArg x.regs (method_src_eq_argument 3 _ (5 : Fin 6) rfl)).trans (hk)
  | extractMin =>
    change x.regs ∘ Backend.src family (.inl 4) = layoutWords ⟨n, L⟩
    funext j
    change Fin 4 at j
    fin_cases j <;>
      first
      | exact (congrArg x.regs (method_src_eq_argument 4 _ (0 : Fin 6) rfl)).trans (hl 0)
      | exact (congrArg x.regs (method_src_eq_argument 4 _ (1 : Fin 6) rfl)).trans (hl 1)
      | exact (congrArg x.regs (method_src_eq_argument 4 _ (2 : Fin 6) rfl)).trans (hl 2)
      | exact (congrArg x.regs (method_src_eq_argument 4 _ (3 : Fin 6) rfl)).trans (hl 3)

private noncomputable def finish {n : ℕ} (o : IndexedMinPQ.Op n)
    (y : Data registers) : Data registers :=
  match o with
  | .getKey _ => y.set (bank 2) (y.regs (bank 1))
  | _ => y

private theorem staged_zero_cond (x : Data registers) (i : Fin 4) (hi : i ≠ 3) :
    (.eq (bank i) (bank 3) : Cond registers).Holds (x.set (bank 3) 0) ↔
      x.regs (bank i) = 0 := by
  have hn := bank_injective.ne hi
  simp [Cond.Holds, Data.set_regs, hn]

/-- Only the ABI wrapper is charged here: the actual zero staging, existing conditional rules,
and lookup key copy. The supplied body execution is not replaced or hand-stepped. -/
private theorem dispatch_exec {w n K : ℕ} (L : Memory.Layout n) (x : Data registers)
    (o : IndexedMinPQ.Op n) (ha : PQCode.argMatch code o x.regs)
    {y : Data registers} {N : ℕ}
    (he : ExecWithin w (Backend.code family (.inl ((backend n K L).tag o)))
      (x.set (bank 3) 0) y N) :
    ExecWithin w code.code x (finish o y) (N + 6) := by
  have hc := ExecWithin.const (B := Basis.exact) (x := x) (d := bank 3) (fits_zero w)
  have hp0 := (staged_zero_cond x 0 (by decide))
  have hp1 := (staged_zero_cond x 1 (by decide))
  have hp2 := (staged_zero_cond x 2 (by decide))
  cases o with
  | isEmpty =>
    rcases ha with ⟨h2, h1, h0⟩
    have h : ExecWithin w code.code x y (1 + (N + 1 + 1 + 1)) :=
      hc.seq (ExecWithin.branch_pos (hp0.mpr h2)
        (ExecWithin.branch_pos (hp1.mpr h1) (ExecWithin.branch_pos (hp2.mpr h0) he)))
    exact h.mono (by omega)
  | getKey v =>
    rcases ha with ⟨h2, h1, h0, _⟩
    have hget := he.seq (ExecWithin.copy (x := y) (d := bank 2) (s := bank 1))
    have h : ExecWithin w code.code x (finish (.getKey v) y) (1 + (N + 1 + 2 + 1 + 1)) :=
      hc.seq (ExecWithin.branch_pos (hp0.mpr h2)
        (ExecWithin.branch_pos (hp1.mpr h1)
          (ExecWithin.branch_neg (fun h => h0 (hp2.mp h)) hget)))
    exact h.mono (by omega)
  | insert v k =>
    rcases ha with ⟨h2, h1, h0, _, _⟩
    have h : ExecWithin w code.code x y (1 + (N + 1 + 2 + 1)) :=
      hc.seq (ExecWithin.branch_pos (hp0.mpr h2)
        (ExecWithin.branch_neg (fun h => h1 (hp1.mp h))
          (ExecWithin.branch_pos (hp2.mpr h0) he)))
    exact h.mono (by omega)
  | decreaseKey v k =>
    rcases ha with ⟨h2, h1, h0, _, _⟩
    have h : ExecWithin w code.code x y (1 + (N + 2 + 2 + 1)) :=
      hc.seq (ExecWithin.branch_pos (hp0.mpr h2)
        (ExecWithin.branch_neg (fun h => h1 (hp1.mp h))
          (ExecWithin.branch_neg (fun h => h0 (hp2.mp h)) he)))
    exact h.mono (by omega)
  | extractMin =>
    have h : ExecWithin w code.code x y (1 + (N + 2)) :=
      hc.seq (ExecWithin.branch_neg (fun h => ha (hp0.mp h)) he)
    exact h.mono (by omega)

/-- The paid zero staging preserves the source memory and all persistent layout words. -/
theorem stage_zero {w : ℕ} (x : Data registers) (hx : x.Bounded w) :
    (x.set (bank 3) 0).Bounded w ∧
      memoryState (Backend.frontier family) (x.set (bank 3) 0) =
        memoryState (Backend.frontier family) x ∧
      ∀ i : Fin 4, (x.set (bank 3) 0).regs (argument (i.castAdd 2)) =
        x.regs (argument (i.castAdd 2)) := by
  refine ⟨(Exec.const (B := Basis.exact) (d := bank 3) (fits_zero w)).bounded hx, ?_, ?_⟩
  · refine @Memory.State.ext (memoryState (Backend.frontier family) (x.set (bank 3) 0))
      (memoryState (Backend.frontier family) x) rfl ?_
    change Function.update x.regs (bank 3) 0 (Backend.frontier family) = _
    exact Function.update_of_ne (bank_ne_frontier 3).symm _ _
  · intro i
    change Function.update x.regs (bank 3) 0 (argument (i.castAdd 2)) = _
    exact Function.update_of_ne (bank_ne_argument 3 (i.castAdd 2)).symm _ _

/-- Every selected method's live input words survive the actual zero staging. -/
theorem stage_zero_input (i : Fin 5) (x : Data registers) :
    (x.set (bank 3) 0).regs ∘ Backend.src family (.inl i) =
      x.regs ∘ Backend.src family (.inl i) := by
  funext j
  change Function.update x.regs (bank 3) 0 (Backend.src family (.inl i) j) = _
  exact Function.update_of_ne (Backend.src_ne_tmp family (.inl i) (.inr 1) j _) _ _

/-- Lift a selected body's actual native execution through the paid raw ABI dispatcher. Only
lookup copies the body key from its OptionNat slot into the established PQ output-key slot. -/
theorem wrap_body {w n K : ℕ} (L : Memory.Layout n) (x : Data registers)
    (o : IndexedMinPQ.Op n) (ha : PQCode.argMatch code o x.regs)
    {y : Data registers} {N : ℕ}
    (he : ExecWithin w (Backend.code family (.inl ((backend n K L).tag o)))
      (x.set (bank 3) 0) y N) (hy : y.Bounded w) :
    ∃ z, ExecWithin w code.code x z (N + 6) ∧ z.Bounded w ∧ z.mem = y.mem ∧
      z.regs code.frontierReg = y.regs code.frontierReg ∧
      (∀ i : Fin 4, z.regs (argument (i.castAdd 2)) = y.regs (argument (i.castAdd 2))) ∧
      z.regs code.outFlag = y.regs code.outFlag ∧ z.regs code.outV = y.regs code.outV ∧
      z.regs code.outK =
        (match o with | .getKey _ => y.regs code.outV | _ => y.regs code.outK) := by
  refine ⟨finish o y, dispatch_exec L x o ha he, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases o <;> first
    | exact hy
    | exact (Exec.copy (B := Basis.exact) (d := bank 2) (s := bank 1)).bounded hy
  · cases o <;> rfl
  · cases o <;> rfl
  · intro i
    cases o <;> try rfl
    change (y.set (bank 2) (y.regs (bank 1))).regs (argument (i.castAdd 2)) = _
    simp only [Data.set_regs, Function.update_of_ne (bank_ne_argument 2 (i.castAdd 2)).symm]
  · cases o <;> rfl
  · cases o <;> rfl
  · cases o <;> rfl

private theorem reserve_layout :
    Function.Injective reserveScratch ∧
      (∀ (_i : Fin 1) j, argument 0 ≠ reserveScratch j) ∧
      (∀ j, reserveScratch j ≠ Backend.frontier family) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j he
    dsimp only [reserveScratch] at he
    split_ifs at he with hi hj
    · apply Fin.ext; omega
    · exact False.elim (Backend.src_ne_tmp family (.inl 2) (.inr 0) (3 : Fin 6) _ he)
    · exact False.elim (Backend.src_ne_tmp family (.inl 2) (.inr 0) (3 : Fin 6) _ he.symm)
    · have hh := Backend.tmp_injective family (.inr 0) he
      have hv : i.val - 1 = j.val - 1 := congrArg (fun z => z.val) hh
      apply Fin.ext
      omega
  · intro i j
    dsimp only [reserveScratch]
    split
    · exact argument_injective.ne (by decide)
    · exact Backend.src_ne_tmp family (.inl 2) (.inr 0) (0 : Fin 6) _
  · intro j
    dsimp only [reserveScratch]
    split
    · exact argument_ne_frontier 3
    · exact Backend.tmp_ne_frontier family (.inr 0) _

/-- Actual compact reservation from arbitrary bounded native data. It preserves every cell and
its live dimension parameter; no host argument installation or zeroing is substituted. -/
theorem span_exec {w n base : ℕ} (x : Data registers) (hx : x.Bounded w)
    (hfront : x.regs code.frontierReg = base) (hn : x.regs code.nReg = n)
    (hfit : Fits w (base + PriorityQueue.BinaryHeap.space n)) :
    ∃ y, ExecWithin w code.allocSpan x y (2 * Initialize.realizes_reserve.factor) ∧
      y.Bounded w ∧ y.mem = x.mem ∧ y.regs code.baseReg = base ∧
      y.regs code.frontierReg = base + PriorityQueue.BinaryHeap.space n ∧
      y.regs code.nReg = n := by
  change x.regs (Backend.frontier family) = base at hfront
  change x.regs (argument 0) = n at hn
  have hin : x.regs ∘ (fun _ : Fin 1 => argument 0) =
      WordEncoding.encode (α := ℕ) n := by
    funext i
    exact hn
  obtain ⟨y, hy, hb, hm, hf, ho, hframe⟩ := Initialize.reserve_exec
    (Backend.frontier family) (fun _ => argument 0) reserveScratch reserve_layout.1
    reserve_layout.2.1 reserve_layout.2.2 (fun _ => argument_ne_frontier 0) x hx hin
    (by rw [hfront]; exact hfit)
  refine ⟨y, hy, hb, hm, ?_, ?_, ?_⟩
  · change y.regs (argument 3) = base
    change y.regs (argument 3) = x.regs (Backend.frontier family) at ho
    exact ho.trans hfront
  · change y.regs (Backend.frontier family) = _
    rw [hfront] at hf
    exact hf
  · change y.regs (argument 0) = n
    rw [hframe (argument 0) (argument_ne_frontier 0)
      (fun j => (reserve_layout.2.1 0 j).symm)]
    exact hn

private theorem metadataScratch_injective : Function.Injective metadataScratch := by
  intro i j he
  dsimp only [metadataScratch, bank] at he
  split_ifs at he
  all_goals first
  | apply Fin.ext; omega
  | have hh := Backend.tmp_injective family (.inr 1) he
    have hv := congrArg (fun z => z.val) hh
    dsimp only at hv
    apply Fin.ext
    omega
  | have hh := argument_injective he
    have hv := congrArg Fin.val hh
    omega
  | exact False.elim (Backend.src_ne_tmp family (.inl 2) (.inr 1) (1 : Fin 6) _ he)
  | exact False.elim (Backend.src_ne_tmp family (.inl 2) (.inr 1) (2 : Fin 6) _ he)
  | exact False.elim (Backend.src_ne_tmp family (.inl 2) (.inr 1) (1 : Fin 6) _ he.symm)
  | exact False.elim (Backend.src_ne_tmp family (.inl 2) (.inr 1) (2 : Fin 6) _ he.symm)

private theorem metadataScratch_ne_argument
    (i : Fin (3 + Initialize.realizes_metadata.scratchSize + 1)) (j : Fin 6)
    (hj1 : j ≠ 1) (hj2 : j ≠ 2) : metadataScratch i ≠ argument j := by
  dsimp only [metadataScratch, bank]
  split_ifs
  · exact (Backend.src_ne_tmp family (.inl 2) (.inr 1) j _).symm
  · exact argument_injective.ne hj1.symm
  · exact argument_injective.ne hj2.symm
  · exact (Backend.src_ne_tmp family (.inl 2) (.inr 1) j _).symm

private theorem metadataScratch_ne_frontier
    (i : Fin (3 + Initialize.realizes_metadata.scratchSize + 1)) :
    metadataScratch i ≠ Backend.frontier family := by
  dsimp only [metadataScratch]
  split_ifs
  · exact bank_ne_frontier 0
  · exact argument_ne_frontier 1
  · exact argument_ne_frontier 2
  · exact Backend.tmp_ne_frontier family (.inr 1) _

/-- Charged metadata setup on the actual native register ABI, preserving every memory cell.
Only the count address/length and private scratch are written. -/
theorem setup_registers {w n base : ℕ} (x : Data registers) (hx : x.Bounded w)
    (hn : x.regs code.nReg = n) (hb : x.regs code.baseReg = base)
    (hfit : Fits w (base + PriorityQueue.BinaryHeap.space n)) :
    ∃ y, ExecWithin w code.initSetup x y Initialize.realizes_metadata.factor ∧
      y.Bounded w ∧ y.mem = x.mem ∧ y.regs code.frontierReg = x.regs code.frontierReg ∧
      y.regs code.nReg = n ∧ y.regs code.baseReg = base ∧
      y.regs (argument 1) = base + n ∧ y.regs (argument 2) = 1 := by
  change x.regs (argument 0) = n at hn
  change x.regs (argument 3) = base at hb
  have hin : x.regs ∘ ![argument 0, argument 3] =
      WordEncoding.encode (α := ℕ × ℕ) (n, base) := by
    funext i
    fin_cases i
    · exact hn
    · exact hb
  have hd : ∀ (i : Fin 2) j, ![argument 0, argument 3] i ≠ metadataScratch j := by
    intro i j
    fin_cases i
    · exact (metadataScratch_ne_argument j 0 (by decide) (by decide)).symm
    · exact (metadataScratch_ne_argument j 3 (by decide) (by decide)).symm
  have hs : ∀ i : Fin 2, ![argument 0, argument 3] i ≠ Backend.frontier family := by
    intro i
    fin_cases i
    · exact argument_ne_frontier 0
    · exact argument_ne_frontier 3
  obtain ⟨y, hy, hbounded, hm, ho, _, hframe⟩ := Initialize.metadata_exec
    (Backend.frontier family) ![argument 0, argument 3] metadataScratch
    metadataScratch_injective hd metadataScratch_ne_frontier hs (n, base) x hx hin hfit
  refine ⟨y, hy, hbounded, congrArg Memory.State.mem hm,
    congrArg Memory.State.frontier hm, ?_, ?_, ?_, ?_⟩
  · change y.regs (argument 0) = n
    rw [hframe _ (argument_ne_frontier 0)
      (fun i => metadataScratch_ne_argument i 0 (by decide) (by decide))]
    exact hn
  · change y.regs (argument 3) = base
    rw [hframe _ (argument_ne_frontier 3)
      (fun i => metadataScratch_ne_argument i 3 (by decide) (by decide))]
    exact hb
  · have h := ho 1
    change y.regs (argument 1) = base + n at h
    exact h
  · have h := ho 2
    change y.regs (argument 2) = 1 at h
    exact h

/-- The actual compact fresh initializer preserves the entire old memory. Its local-zero domain
is exactly the original 3n+1 block, and its code and constant clock precede all runtime values.
This one-run statement is not a globally composable allocator with a local precondition. -/
theorem initFresh_exec {w n base : ℕ} (x : Data registers) (hx : x.Bounded w)
    (hfront : x.regs code.frontierReg = base) (hn : x.regs code.nReg = n)
    (hfit : Fits w (base + PriorityQueue.BinaryHeap.space n))
    (hz : ∀ a, (Block.mk base (PriorityQueue.BinaryHeap.space n)).Owns a →
      x.mem a = 0) :
    ∃ y, ExecWithin w code.initFresh x y
        (2 * Initialize.realizes_reserve.factor + Initialize.realizes_metadata.factor) ∧
      y.Bounded w ∧ y.mem = x.mem ∧
      y.regs code.frontierReg = base + PriorityQueue.BinaryHeap.space n ∧
      y.regs code.nReg = n ∧ y.regs code.baseReg = base ∧
      y.regs (argument 1) = base + n ∧ y.regs (argument 2) = 1 ∧
      Memory.Inv (Memory.compactLayout n base) (memoryState code.frontierReg y) ∧
      Memory.abs (Memory.compactLayout n base) (memoryState code.frontierReg y) =
        IndexedMinPQ.empty n := by
  obtain ⟨z, hzrun, hzbounded, hzmem, hzbase, hzfront, hzn⟩ := span_exec x hx hfront hn hfit
  obtain ⟨y, hyrun, hybounded, hymem, hyfront, hyn, hybase, hysize, hylen⟩ :=
    setup_registers z hzbounded hzn hzbase hfit
  have hmem : y.mem = x.mem := hymem.trans hzmem
  have hf : y.regs code.frontierReg = base + PriorityQueue.BinaryHeap.space n :=
    hyfront.trans hzfront
  have hi := Memory.inv_compactLayout (n := n) (base := base)
    (s := memoryState code.frontierReg y) (by
      change base + PriorityQueue.BinaryHeap.space n ≤ y.regs code.frontierReg
      rw [hf])
    (by intro a ha; change y.mem a = 0; rw [hmem]; exact hz a ha)
  exact ⟨y, hzrun.seq hyrun, hybounded, hmem, hf, hyn, hybase, hysize, hylen, hi⟩

end Cslib.DataStructure.PriorityQueue.BinaryHeap.Native.Program
