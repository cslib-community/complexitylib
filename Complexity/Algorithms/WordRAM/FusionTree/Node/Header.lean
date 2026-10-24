/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.FusionTree.Node.Registers
public import Complexity.Algorithms.WordRAM.FusionTree.Model

/-!
# Loading concrete fusion-node parameters

The representation below consists entirely of literal memory equalities. It supplies no
query result or execution assumption. The complete eighteen-word header load is charged.

## Main definitions

* `NodeProgram.Rep`: actual parameter words and interleaved full keys in RAM.
* `NodeProgram.Ready`: loaded header, original query and address, and unchanged key table.
* `NodeProgram.readHeader`: structured program loading the 18-word node header into registers.

## Main results

* `NodeProgram.exec_readHeader`: all header words are loaded in 55 instructions.

## References

* [FredmanWillard1993]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.FusionTree.NodeProgram

open Cslib.WordRAM

/-- Literal representation of an internal node's occupancy, fifteen parameters and full-key
minima. The unused tag, cached minimum and child pointers are read or skipped as appropriate;
they carry no query oracle. This is a projection of the contiguous tree representation. -/
structure Rep {w n : ℕ} {keys : Fin n → ℕ} (p : NodeParameters w keys)
    (a : ℕ) (mem : ℕ → ℕ) : Prop where
  /-- Actual occupancy at header offset one. -/
  count_eq : mem (a + 1) = n
  /-- Actual fifteen preprocessing words at offsets three through seventeen. -/
  words_eq : ∀ j : Fin 15, mem (a + 3 + j.val) = p.words j
  /-- Full-key minima in the interleaved child table. -/
  keys_eq : ∀ i : Fin n, mem (a + 18 + i.val * 2) = keys i

/-- The node contract is a literal projection of the contiguous tree representation.
Only equality with the actual stored parameter words is required. -/
theorem rep_of_tree {w a m : ℕ} {cs : List Lean.FusionTree.Tree}
    {parameters : Parameters} {mem : ℕ → ℕ}
    (p : NodeParameters w (fun i : Fin cs.length => cs[i].minimum))
    (hr : FusionTree.Rep parameters (.node m cs) a mem)
    (hp : parameters (.node m cs) = p.words) : Rep p a mem := by
  have hh := hr.node_header
  refine ⟨hh.2.1, fun j => (hh.2.2.2 j).trans (congrFun hp j), ?_⟩
  intro i
  simpa only [headerWords, Nat.mul_comm] using (hr.child i).1

/-- Loaded parameters and original inputs, with the actual full-key table. -/
structure Ready {w n : ℕ} {keys : Fin n → ℕ} (p : NodeParameters w keys)
    (q a : ℕ) (x : Data registers) : Prop where
  /-- Actual loaded header. -/
  prepared : Prepared p x
  /-- Original query. -/
  query_eq : x.regs query = q
  /-- Original record base. -/
  pointer_eq : x.regs pointer = a
  /-- Actual stride-two full-key table. -/
  keys_eq : ∀ i : Fin n, x.mem (a + 18 + i.val * 2) = keys i

/-- Framing memory and the first 40 registers preserves `Ready`. -/
theorem Ready.frame {w n q a : ℕ} {keys : Fin n → ℕ} {p : NodeParameters w keys}
    {x y : Data registers} (hx : Ready p q a x) (hf : Frame x y) : Ready p q a y :=
  ⟨hx.prepared.frame hf, (hf.2 query (by decide)).trans hx.query_eq,
    (hf.2 pointer (by decide)).trans hx.pointer_eq,
    fun i => (congrFun hf.1 _).trans (hx.keys_eq i)⟩

/-- Scratch register updates preserve the original inputs and loaded node data. -/
theorem Ready.set_scratch {w n q a : ℕ} {keys : Fin n → ℕ} {p : NodeParameters w keys}
    {x : Data registers} (hx : Ready p q a x) (i : Fin registers) (v : ℕ)
    (hlo : 2 ≤ i.val) (hhi : i.val < 10) : Ready p q a (x.set i v) := by
  have hq : query ≠ i := by intro h; have := congrArg Fin.val h; change 0 = i.val at this; omega
  have hp : pointer ≠ i := by intro h; have := congrArg Fin.val h; change 1 = i.val at this; omega
  exact ⟨hx.prepared.set_low i v hhi, (Function.update_of_ne hq _ _).trans hx.query_eq,
    (Function.update_of_ne hp _ _).trans hx.pointer_eq, hx.keys_eq⟩

/-- A subroutine may return through one caller scratch register while framing the rest. -/
theorem Ready.except_scratch {w n q a : ℕ} {keys : Fin n → ℕ} {p : NodeParameters w keys}
    {x y : Data registers} (hx : Ready p q a x) (i : Fin registers)
    (hlo : 2 ≤ i.val) (hhi : i.val < 10) (hm : y.mem = x.mem)
    (hp : ∀ j : Fin registers, j.val < 40 → j ≠ i → y.regs j = x.regs j) :
    Ready p q a y := by
  apply (hx.set_scratch i (y.regs i) hlo hhi).frame
  refine ⟨hm, ?_⟩
  intro j hj
  by_cases he : j = i
  · subst j
    simp only [Data.set_regs, Function.update_self]
  · exact (hp j hj he).trans (Function.update_of_ne he _ _).symm

/-- Copy the base pointer, then perform the actual eighteen-word header load. -/
def readHeader : Code .standard registers :=
  .seq (.op (.copy (headerBank 0) pointer)) (ReadHeaderProgram.code.rename headerBank)

/-- Header loading takes 55 actual instructions and preserves memory and both inputs. -/
theorem exec_readHeader {w n q a : ℕ} {keys : Fin n → ℕ} (p : NodeParameters w keys)
    (x : Data registers) (hr : Rep p a x.mem) (ha : Fits w (a + 17))
    (hxq : x.regs query = q) (hxa : x.regs pointer = a) :
    ∃ y, Exec w readHeader x y 55 ∧ Ready p q a y ∧ y.mem = x.mem := by
  let u := x.set (headerBank 0) a
  have hxu : Exec (B := .standard) w (.op (.copy (headerBank 0) pointer)) x u 1 := by
    simpa only [hxa] using (Exec.copy (B := .standard) (w := w)
      (d := headerBank 0) (s := pointer) (x := x))
  have hup : (u.comap headerBank).regs ReadHeaderProgram.pointer = a := by
    simp [u, ReadHeaderProgram.pointer]
  have hu : Fits w ((u.comap headerBank).regs ReadHeaderProgram.pointer + 17) := hup ▸ ha
  have he := ReadHeaderProgram.exec (u.comap headerBank) hu
  have hv := ReadHeaderProgram.result_spec (u.comap headerBank)
  generalize ReadHeaderProgram.result (u.comap headerBank) = v at he hv
  let y := v.extend headerBank u
  have hyword (i : Fin 18) :
      y.regs (headerBank ⟨i.val + 1, by omega⟩) = x.mem (a + i.val) := by
    change Function.extend headerBank v.regs u.regs (headerBank _) = _
    rw [(bank_injective _).extend_apply, hv.2.2 i, hup]
    rfl
  have hyinput (i : Fin registers) (hi : i.val < 10) : y.regs i = x.regs i := by
    have hn : ¬∃ j, headerBank j = i := by
      rintro ⟨j, heq⟩
      have := congrArg Fin.val heq
      dsimp only [headerBank, bank] at this
      omega
    change Function.extend headerBank v.regs u.regs i = _
    rw [Function.extend_apply' _ _ _ hn]
    have hni : i ≠ headerBank 0 := by
      intro heq
      exact hn ⟨0, heq.symm⟩
    exact Function.update_of_ne hni _ _
  refine ⟨y, hxu.seq (he.rename (bank_injective _)), ?_, hv.2.1⟩
  refine ⟨⟨(hyword 1).trans hr.count_eq, ?_⟩,
    (hyinput query (by decide)).trans hxq, (hyinput pointer (by decide)).trans hxa,
    fun i => (congrFun hv.2.1 _).trans (hr.keys_eq i)⟩
  intro j
  have hh := hyword ⟨j.val + 3, by omega⟩
  have hm : x.mem (a + (j.val + 3)) = p.words j := by
    rw [show a + (j.val + 3) = a + 3 + j.val by omega]
    exact hr.words_eq j
  simpa only [parameter, Nat.add_assoc] using hh.trans hm

end Cslib.Algorithms.WordRAM.FusionTree.NodeProgram
