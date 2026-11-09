/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.PriorityQueue.BinaryHeap.Native.Representation

/-!
# The compact heap's initialization and calling-convention certificate

This is the existing `SubroutineBase` over the single global heap program. It supplies the
representation, raw initialization and ABI fields; its operation charge is metadata awaiting
the separate method-execution proof. It is not a `StateTransitionImpl` certificate.

The domain is the original end-fit and key-fit domain. Fresh initialization needs zero only in
the compact `space n` block. The generic dirty initializer instead pays its existing linear
clear, preserving memory outside that block. No local-zero generic allocator or old exact
instruction/register count is claimed.

## Main definitions

* `subroutineBase`: the existing raw initialization/representation/ABI certificate.

## Main results

* `subroutineBase_rep_iff`: its representation is exactly `Representation.Rep`.
* `subroutineBase_initTime`: the actual reservation and metadata-setup bound.
-/

public section

namespace Cslib.DataStructure.PriorityQueue.BinaryHeap.Native

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure
open Cslib.DataStructure.PriorityQueue.BinaryHeap (space)

private theorem dimension_fits {w n base : ℕ} (hS : Fits w (base + space n)) : Fits w n :=
  hS.of_le (by unfold space; omega)

private theorem parameter_live {n : ℕ} {x : Data Program.registers}
    (hpar : ∀ i, x.regs (Program.code.initParams i) = (![n] : Fin 1 → ℕ) i) :
    x.regs Program.code.nReg = n := by
  simpa only [Program.code.initParams_eq, Matrix.cons_val_zero] using hpar 0

private theorem setup_rep {w n K base : ℕ} (hn : Fits w n) (hK : Fits w K)
    (x : Data Program.registers) (hx : x.Bounded w)
    (hb : x.regs Program.code.baseReg = base)
    (hf : x.regs Program.code.frontierReg = base + space n)
    (hpar : ∀ i, x.regs (Program.code.initParams i) = (![n] : Fin 1 → ℕ) i)
    (hz : ∀ a ∈ (Block.mk base (space n)).footprint, x.mem a = 0)
    (hS : Fits w (base + space n)) :
    ∃ y, ExecWithin w Program.code.initSetup x y Initialize.realizes_metadata.factor ∧
      y.regs Program.code.frontierReg = base + space n ∧
      Representation.Rep base hn hK (IndexedMinPQ.empty n) y ∧
      Modifies (Block.mk base (space n)).footprint x.mem y.mem := by
  obtain ⟨y, he, hy, hm, hyf, hyn, hyb, hcount, hlen⟩ :=
    Program.setup_registers x hx (parameter_live hpar) hb hS
  have hfront : y.regs Program.code.frontierReg = base + space n := hyf.trans hf
  obtain ⟨hi, ha⟩ := Memory.inv_compactLayout (n := n) (base := base)
    (s := memoryState Program.code.frontierReg y) (by
      change base + space n ≤ y.regs Program.code.frontierReg
      rw [hfront]) (by
      intro a ha
      change y.mem a = 0
      rw [hm]
      exact hz a (Block.mem_footprint.mpr ha))
  rw [Program.code_frontier] at hi ha
  refine ⟨y, he, hfront, ⟨(Backend.rep_iff _ _ _).mpr ⟨hi, ha, hy⟩, ?_⟩,
    fun a _ => congrFun hm a⟩
  intro i
  fin_cases i
  · change y.regs (Program.argument 0) = n
    rwa [Program.code_nReg] at hyn
  · change y.regs (Program.argument 1) = base + n
    exact hcount
  · change y.regs (Program.argument 2) = 1
    exact hlen
  · change y.regs (Program.argument 3) = base
    rwa [Program.code_baseReg] at hyb

private noncomputable def baseImpl {w n K base : ℕ}
    (hS : Fits w (base + space n)) (hK : Fits w K) :
    SubroutineBase Program.code.toSubroutineCode (indexedMinPQSpec n K).Result
      (indexedMinPQSpec n K).valid w base ![n] (IndexedMinPQ.empty n) where
  space := space n
  spanTime := 2 * Initialize.realizes_reserve.factor
  setupTime := Initialize.realizes_metadata.factor
  initPotential := 0
  charge _ o := Backend.factor Program.family * (memoryBound o + 1) + 8
  rep := Representation.Rep base (dimension_fits hS) hK
  potential _ := 0
  encode := Program.code.encode
  argMatch := Program.code.argMatch
  decode := Program.code.decode
  bounded := Representation.Rep.bounded
  arguments_fit o hv i _ := Program.code.arguments_fit (by unfold space; omega) hS hK o hv i
  encode_matches := Program.code.encode_matches
  rep_supported := Representation.Rep.supported
  potential_supported _ _ _ := rfl
  clear_nodup := Program.clear_nodup
  params_not_clear := Program.params_not_clear
  incCur_eval := Program.incCur_eval
  span_exec {x} hx hf hpar := by
    obtain ⟨y, he, _, hm, hb, hyf, hyn⟩ :=
      Program.span_exec x hx hf (parameter_live hpar) hS
    refine ⟨y, he, hm, hb, hyf, fun i => ?_⟩
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simpa only [Program.code.initParams_eq, Matrix.cons_val_zero] using hyn
  setup_exec {x} hx hb hf hpar hz := by
    obtain ⟨y, he, hyf, hr, hm⟩ := setup_rep (dimension_fits hS) hK x hx hb hf hpar hz hS
    exact ⟨y, he, hyf, hr, le_rfl, hm⟩

/-- The compact raw heap's existing `SubroutineBase`, on only the original end-fit and key-fit
domain. This packages initialization and ABI metadata; method execution remains separate. -/
noncomputable def subroutineBase {w n K base : ℕ}
    (hS : Fits w (base + space n)) (hK : Fits w K) :
    SubroutineBase Program.code.toSubroutineCode (indexedMinPQSpec n K).Result
      (indexedMinPQSpec n K).valid w base ![n] (IndexedMinPQ.empty n) := baseImpl hS hK

variable {w n K base : ℕ} (hS : Fits w (base + space n)) (hK : Fits w K)

private theorem subroutineBase_space_aux : (subroutineBase hS hK).space = space n := rfl

/-- The footprint is the original compact block. -/
theorem subroutineBase_space : (subroutineBase hS hK).space = space n :=
  subroutineBase_space_aux hS hK

private theorem subroutineBase_initTime_aux : (subroutineBase hS hK).initTime =
    2 * Initialize.realizes_reserve.factor + Initialize.realizes_metadata.factor := rfl

/-- Fresh initialization pays the actual reservation and metadata setup. -/
theorem subroutineBase_initTime : (subroutineBase hS hK).initTime =
    2 * Initialize.realizes_reserve.factor + Initialize.realizes_metadata.factor :=
  subroutineBase_initTime_aux hS hK

/-- The inherited representation is not replaced by an independent heap model. -/
theorem subroutineBase_rep_iff {hn : Fits w n} (s : (indexedMinPQSpec n K).State)
    (x : Data Program.registers) :
    (subroutineBase hS hK).rep s x ↔ Representation.Rep base hn hK s x := Iff.rfl

private theorem subroutineBase_charge_aux (s : (indexedMinPQSpec n K).State)
    (o : IndexedMinPQ.Op n) :
    (subroutineBase hS hK).charge s o = Backend.factor Program.family * (memoryBound o + 1) + 8 :=
  rfl

/-- The declared operation charge is metadata until the method-execution obligation is proved. -/
theorem subroutineBase_charge (s : (indexedMinPQSpec n K).State) (o : IndexedMinPQ.Op n) :
    (subroutineBase hS hK).charge s o = Backend.factor Program.family * (memoryBound o + 1) + 8 :=
  subroutineBase_charge_aux hS hK s o

private theorem subroutineBase_potential_aux (x : Data Program.registers) :
    (subroutineBase hS hK).potential x = 0 := rfl

/-- The heap uses no amortized potential in this certificate. -/
theorem subroutineBase_potential (x : Data Program.registers) :
    (subroutineBase hS hK).potential x = 0 := subroutineBase_potential_aux hS hK x

private theorem subroutineBase_initPotential_aux : (subroutineBase hS hK).initPotential = 0 := rfl

/-- The initial potential is zero. -/
theorem subroutineBase_initPotential : (subroutineBase hS hK).initPotential = 0 :=
  subroutineBase_initPotential_aux hS hK

private theorem subroutineBase_encode_aux (o : IndexedMinPQ.Op n) :
    (subroutineBase hS hK).encode o = Program.code.encode o := rfl

/-- The standard argument encoding is the existing priority-queue encoding. -/
theorem subroutineBase_encode (o : IndexedMinPQ.Op n) :
    (subroutineBase hS hK).encode o = Program.code.encode o := subroutineBase_encode_aux hS hK o

private theorem subroutineBase_argMatch_aux (o : IndexedMinPQ.Op n) :
    (subroutineBase hS hK).argMatch o = Program.code.argMatch o := rfl

/-- Inline argument matching retains the existing priority-queue convention. -/
theorem subroutineBase_argMatch (o : IndexedMinPQ.Op n) :
    (subroutineBase hS hK).argMatch o = Program.code.argMatch o :=
  subroutineBase_argMatch_aux hS hK o

private theorem subroutineBase_decode_aux (o : IndexedMinPQ.Op n) :
    (subroutineBase hS hK).decode o = Program.code.decode o := rfl

/-- The result decoder is the existing priority-queue decoder. -/
theorem subroutineBase_decode (o : IndexedMinPQ.Op n) :
    (subroutineBase hS hK).decode o = Program.code.decode o := subroutineBase_decode_aux hS hK o

end Cslib.DataStructure.PriorityQueue.BinaryHeap.Native
