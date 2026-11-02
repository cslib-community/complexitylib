/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.PriorityQueue.BinaryHeap.Native.Backend
public import Complexity.DataStructure.PriorityQueue.BinaryHeap.Native.Initialize
public import Complexity.DataStructure.PriorityQueue.WordRAM.Basic

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
@[expose] def initialization : Fin 2 → Certificate .exact :=
  ![⟨Initialize.realizes_reserve⟩, ⟨Initialize.realizes_metadata⟩]

/-- One static register family for all methods and both initialization routines. -/
@[expose] def family : Fin 5 ⊕ Fin 2 → Certificate .exact := Sum.elim certificates initialization

/-- The runtime parameter-independent register count. -/
noncomputable abbrev registers := Backend.registers family

/-- The common method-argument positions: n, count address, count length, base, handle and key. -/
def argument (i : Fin 6) : Fin registers := Backend.src family (.inl 2) i

/-- Four common result/scratch slots, also used for three tag bits and a staged zero. -/
noncomputable def bank (i : Fin 4) : Fin registers :=
  Backend.tmp family (.inr 1) ⟨i.val, by have := i.isLt; change i.val < 3 + _ + 1; omega⟩

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
    (hfit : Fits w (base + PriorityQueue.WordRAM.BinaryHeap.space n)) :
    ∃ y, ExecWithin w code.allocSpan x y (2 * Initialize.realizes_reserve.factor) ∧
      y.Bounded w ∧ y.mem = x.mem ∧ y.regs code.baseReg = base ∧
      y.regs code.frontierReg = base + PriorityQueue.WordRAM.BinaryHeap.space n ∧
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
    (hfit : Fits w (base + PriorityQueue.WordRAM.BinaryHeap.space n)) :
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
    (hfit : Fits w (base + PriorityQueue.WordRAM.BinaryHeap.space n))
    (hz : ∀ a, (Block.mk base (PriorityQueue.WordRAM.BinaryHeap.space n)).Owns a →
      x.mem a = 0) :
    ∃ y, ExecWithin w code.initFresh x y
        (2 * Initialize.realizes_reserve.factor + Initialize.realizes_metadata.factor) ∧
      y.Bounded w ∧ y.mem = x.mem ∧
      y.regs code.frontierReg = base + PriorityQueue.WordRAM.BinaryHeap.space n ∧
      y.regs code.nReg = n ∧ y.regs code.baseReg = base ∧
      y.regs (argument 1) = base + n ∧ y.regs (argument 2) = 1 ∧
      Memory.Inv (Memory.compactLayout n base) (memoryState code.frontierReg y) ∧
      Memory.abs (Memory.compactLayout n base) (memoryState code.frontierReg y) =
        IndexedMinPQ.empty n := by
  obtain ⟨z, hzrun, hzbounded, hzmem, hzbase, hzfront, hzn⟩ := span_exec x hx hfront hn hfit
  obtain ⟨y, hyrun, hybounded, hymem, hyfront, hyn, hybase, hysize, hylen⟩ :=
    setup_registers z hzbounded hzn hzbase hfit
  have hmem : y.mem = x.mem := hymem.trans hzmem
  have hf : y.regs code.frontierReg = base + PriorityQueue.WordRAM.BinaryHeap.space n :=
    hyfront.trans hzfront
  have hi := Memory.inv_compactLayout (n := n) (base := base)
    (s := memoryState code.frontierReg y) (by
      change base + PriorityQueue.WordRAM.BinaryHeap.space n ≤ y.regs code.frontierReg
      rw [hf])
    (by intro a ha; change y.mem a = 0; rw [hmem]; exact hz a ha)
  exact ⟨y, hzrun.seq hyrun, hybounded, hmem, hf, hyn, hybase, hysize, hylen, hi⟩

end Cslib.DataStructure.PriorityQueue.BinaryHeap.Native.Program
