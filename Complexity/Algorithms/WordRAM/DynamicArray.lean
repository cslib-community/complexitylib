/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Copy
public import Complexity.Computability.WordRAM.Dynamic
public import Complexity.Foundations.Semantics.Stateful.Amortized

/-!
# Doubling arrays on the word RAM

A fixed twelve-register append routine uses the charged zeroing allocator and a charged
copy loop. Old blocks are retained: the space theorem concerns total allocated words over
append-only histories, rather than reclamation. The abstract state exposes only the list.
A companion two-instruction indexed read routine and a fixed operation dispatcher connect
the doubling array to `Cslib.Stateful` and `Cslib.Stateful.Amortized`.

## Main definitions

* `Cslib.Algorithms.WordRAM.DynamicArray.program`: the fixed twelve-register append procedure.
* `Cslib.Algorithms.WordRAM.DynamicArray.getProgram`: the two-instruction indexed read procedure.
* `Cslib.Algorithms.WordRAM.DynamicArray.initProgram`: charged fifteen-instruction initializer.
* `Cslib.Algorithms.WordRAM.DynamicArray.dispatch`: fixed append/get operation dispatcher.
* `Cslib.Algorithms.WordRAM.DynamicArray.Rep`: the live array and allocator frontier invariant.
* `Cslib.Algorithms.WordRAM.DynamicArray.potential`: natural-valued credit `15 * (2 * |vs| - cap)`.

## Main results

* `Cslib.Algorithms.WordRAM.DynamicArray.Rep.space`: total allocated words `< 4 * vs.length` for
  nonempty arrays.
* `Cslib.Algorithms.WordRAM.DynamicArray.grow_exec`: capacity doubling within `15 * cap + 14`
  instructions.
* `Cslib.Algorithms.WordRAM.DynamicArray.append_exec`: append correctness, memory preservation,
  and the `49`-instruction potential inequality.
* `Cslib.Algorithms.WordRAM.DynamicArray.get_exec`: two-instruction indexed read correctness.
* `Cslib.Algorithms.WordRAM.DynamicArray.init_exec`: charged initialization of the empty array.
* `Cslib.Algorithms.WordRAM.DynamicArray.amortized`: `Stateful.Amortized` certificate for adaptive
  histories.
* `Cslib.Algorithms.WordRAM.DynamicArray.run_initialized`: end-to-end adaptive execution from
  charged initialization with linear total instruction bound and `< 4 * m` space.
* `Cslib.Algorithms.WordRAM.DynamicArray.run_appendAll`: appending `m` words from an initialized
  empty array in at most `15 + 52 * m` total instructions and `< 4 * m` total allocated words.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*, Chapter 17][CLRS2009].
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.DynamicArray

open Cslib.WordRAM

/-- Pointer to the live block. -/
abbrev ptr : Fin 12 := 0
/-- New block pointer and operation dispatch tag. -/
abbrev dest : Fin 12 := 1
/-- Logical length. -/
abbrev len : Fin 12 := 2
/-- Copy/allocation loop cursor. -/
abbrev idx : Fin 12 := 3
/-- Temporary address. -/
abbrev addr : Fin 12 := 4
/-- Temporary copied value and read output register. -/
abbrev temp : Fin 12 := 5
/-- Constant one. -/
abbrev one : Fin 12 := 6
/-- Current capacity. -/
abbrev cap : Fin 12 := 7
/-- Bump allocator frontier. -/
abbrev frontier : Fin 12 := 8
/-- Caller-supplied value to append or index to read. -/
abbrev arg : Fin 12 := 9
/-- Requested allocation size. -/
abbrev count : Fin 12 := 10
/-- Constant zero. -/
abbrev zero : Fin 12 := 11

/-- The copy routine embedded in the first seven registers. -/
def copy : Code .standard 12 := ArrayCopy.program.rename (Fin.castLE (by decide))

/-- Allocate twice the capacity, copy the live prefix, and switch the pointer. -/
def grow : Code .standard 12 := ram[
  count ← cap + cap; ⟪alloc frontier count dest idx zero one⟫; ⟪copy⟫;
  ptr ← dest; cap ← count ]

/-- Append a word, growing precisely when the array is full. -/
def program : Code .standard 12 := ram[
  if len = cap then [ ⟪grow⟫ ] else [ temp ← temp ];
  one ← #1;
  ⟪writeAt addr ptr len arg⟫; len ← len + one ]

/-- Read the word at the index in `arg` into `temp`. -/
def getProgram : Code .standard 12 := readAt addr temp ptr arg

/-- Allocate the initial one-word block at address zero and install the empty representation. -/
def initProgram : Code .standard 12 := ram[
  frontier ← #0; count ← #1; len ← #0;
  ⟪alloc frontier count ptr idx zero one⟫;
  cap ← count ]

/-- The live prefix, capacity and total allocation. The equalities express the geometric
allocation series starting with a single cell at address zero. -/
structure Rep (vs : List ℕ) (x : Data 12) : Prop where
  length_eq : x.regs len = vs.length
  capacity_pos : 0 < x.regs cap
  length_le : vs.length ≤ x.regs cap
  capacity_le : x.regs cap ≤ max 1 (2 * vs.length)
  pointer_eq : x.regs ptr + 1 = x.regs cap
  frontier_eq : x.regs frontier + 1 = 2 * x.regs cap
  contents : ∀ i : Fin vs.length, x.mem (x.regs ptr + i.val) = vs[i]

/-- Capacity and all historically allocated blocks occupy fewer than four words per live
element once the array is nonempty. -/
theorem Rep.space {vs : List ℕ} {x : Data 12} (h : Rep vs x) (hne : vs ≠ []) :
    x.regs frontier < 4 * vs.length := by
  have hn : 0 < vs.length := List.length_pos_iff.mpr hne
  have := h.capacity_le
  have := h.frontier_eq
  omega

/-- The doubled frontier bound `x.regs frontier + 2 * x.regs cap` is bounded by `8 * vs.length + 3`
for every represented state. -/
private theorem Rep.frontier_add_two_cap_le {vs : List ℕ} {x : Data 12} (h : Rep vs x) :
    x.regs frontier + 2 * x.regs cap ≤ 8 * vs.length + 3 := by
  have := h.capacity_le
  have := h.frontier_eq
  omega

/-- The natural-valued credit used to pay for allocation and copying. -/
def potential (vs : List ℕ) (x : Data 12) : ℕ := 15 * (2 * vs.length - x.regs cap)

/-- The exact copy contract lifts to a larger register file without charging a meta-level call. -/
private theorem copy_exec {w : ℕ} (x : Data 12) (h1 : Fits w 1)
    (hs : Fits w (x.regs ptr + x.regs len))
    (hd : Fits w (x.regs dest + x.regs len))
    (hdisj : x.regs ptr + x.regs len ≤ x.regs dest) :
    ∃ y, ExecWithin w copy x y (7 * x.regs len + 4) ∧
      y.mem = ArrayCopy.copyPrefix x.mem (x.regs ptr) (x.regs dest) (x.regs len) := by
  let f : Fin 7 → Fin 12 := Fin.castLE (by decide)
  obtain ⟨y, he, hm, _⟩ := ArrayCopy.exec (x.comap f) h1 hs hd hdisj
  exact ⟨y.extend f x, he.rename (Fin.castLE_injective _), hm⟩

/-- A growth phase preserves the live values and sets aside a zeroed block, charging both
allocation and copying. The resulting capacity, frontier, and frame are explicit. -/
theorem grow_exec {w : ℕ} (x : Data 12) (h1 : Fits w 1)
    (hn : x.regs len = x.regs cap) (hp : x.regs ptr + x.regs len ≤ x.regs frontier)
    (hw : Fits w (x.regs frontier + 2 * x.regs cap)) :
    ∃ y, ExecWithin w grow x y (15 * x.regs cap + 14) ∧
      y.regs ptr = x.regs frontier ∧ y.regs cap = 2 * x.regs cap ∧
      y.regs frontier = x.regs frontier + 2 * x.regs cap ∧
      (∀ i < x.regs len, y.mem (y.regs ptr + i) = x.mem (x.regs ptr + i)) ∧
      (∀ a, a < x.regs frontier ∨ x.regs frontier + 2 * x.regs cap ≤ a → y.mem a = x.mem a) := by
  let b := x.set count (2 * x.regs cap)
  have hb : ExecWithin w (.op (.bin .add count cap cap)) x b 1 := by
    have := ExecWithin.bin (x := x) (f := .add) (d := count) (i := cap) (j := cap)
      (hw.of_le (by simp only [BinOp.eval]; omega))
    simpa [b, two_mul] using this
  have ha := alloc_exec (x := b) (frontier := frontier) (count := count)
    (result := dest) (cur := idx) (zero := zero) (one := one) (by decide) h1
    (by simpa +decide [b, Function.update_apply] using hw)
  let a : Data 12 :=
    ⟨Function.update (Function.update (Function.update (Function.update (Function.update
        b.regs zero 0) one 1) dest (b.regs frontier)) frontier
          (b.regs frontier + b.regs count)) idx (b.regs frontier + b.regs count),
      clear b.mem (b.regs frontier) (b.regs count)⟩
  have has : a.regs ptr = x.regs ptr := by simp +decide [a, b]
  have had : a.regs dest = x.regs frontier := by simp +decide [a, b]
  have hal : a.regs len = x.regs len := by simp +decide [a, b]
  have hac : a.regs count = 2 * x.regs cap := by simp +decide [a, b]
  have haf : a.regs frontier = x.regs frontier + 2 * x.regs cap := by
    simp +decide [a, b]
  obtain ⟨z, hz, hzm⟩ := copy_exec a h1
    (hw.of_le (by rw [has, hal]; omega))
    (hw.of_le (by rw [had, hal]; omega)) (by rw [has, hal, had]; exact hp)
  have hzd : z.regs dest = x.regs frontier :=
    (hz.regs_eq (by decide)).trans had
  have hzc : z.regs count = 2 * x.regs cap :=
    (hz.regs_eq (by decide)).trans hac
  have hzf : z.regs frontier = x.regs frontier + 2 * x.regs cap :=
    (hz.regs_eq (by decide)).trans haf
  let y := (z.set ptr (z.regs dest)).set cap (z.regs count)
  have hfinish : ExecWithin (B := .standard) w (ram[ptr ← dest; cap ← count]) z y 2 := by
    simpa +decide [y, Function.update_apply] using
      (ExecWithin.copy (B := .standard) (x := z) (d := ptr) (s := dest)).seq
        (ExecWithin.copy (B := .standard) (d := cap) (s := count))
  refine ⟨y, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have he := hb.seq (ha.within.seq (hz.seq hfinish))
    convert he using 1
    · rfl
    · simp only [hal]
      simp +decide only [b, Data.set_regs, Function.update_apply, ↓reduceIte]
      omega
  · simp +decide [y, hzd]
  · simp [y, hzc]
  · simpa +decide [y, Function.update_apply] using hzf
  · intro i hi
    have hread := ArrayCopy.copyPrefix_read (mem := a.mem) (src := a.regs ptr)
      (dst := a.regs dest) (by simpa [hal] using hi)
    have hclear : a.mem (x.regs ptr + i) = x.mem (x.regs ptr + i) := by
      apply clear_of_not_owns
      simp only [Block.Owns, b, Data.set_regs, Function.update_apply]
      simp +decide only [↓reduceIte]
      omega
    simpa +decide [y, Function.update_apply, hzd, hzm, has, had, hal] using hread.trans hclear
  · intro addr haddr
    have hout : z.mem addr = a.mem addr := by
      rw [hzm]
      apply ArrayCopy.copyPrefix_outside
      rw [had, hal]
      omega
    have hclear : a.mem addr = x.mem addr := by
      apply clear_of_not_owns
      simp only [Block.Owns, b, Data.set_regs, Function.update_apply]
      simp +decide only [↓reduceIte]
      omega
    simpa [y] using hout.trans hclear

/-- Four-instruction suffix of `program`: set `one ← #1`, write `arg` at `ptr + len`, and
increment `len`. -/
private theorem appendTail_exec {w : ℕ} (z : Data 12) (h1 : Fits w 1)
    (haddr : Fits w (z.regs ptr + z.regs len)) (hlen : Fits w (z.regs len + 1)) :
    let y := (((z.set one 1).set addr (z.regs ptr + z.regs len)).write
      (z.regs ptr + z.regs len) (z.regs arg)).set len (z.regs len + 1)
    Exec w (ram[one ← #1; ⟪writeAt addr ptr len arg⟫; len ← len + one]) z y 4 := by
  intro y
  let z₁ := z.set one 1
  let z₂ := (z₁.set addr (z.regs ptr + z.regs len)).write (z.regs ptr + z.regs len) (z.regs arg)
  have e₁ : Exec (B := .standard) w (.op (.const one 1)) z z₁ 1 := Exec.const h1
  have e₂ : Exec w (writeAt addr ptr len arg) z₁ z₂ 2 := by
    simpa +decide [z₁, z₂, Data.set, Data.write, Function.update_apply] using
      writeAt_exec (x := z₁) (tmp := addr) (ptr := ptr) (idx := len) (src := arg)
        (by decide) (by simpa +decide [z₁, Data.set] using haddr)
  have e₃ : Exec w (.op (.bin .add len len one)) z₂ y 1 := by
    have hbin := Exec.bin (x := z₂) (f := .add) (d := len) (i := len) (j := one)
      (by simpa +decide [z₂, z₁, Data.set, Data.write, BinOp.eval] using hlen)
    simpa +decide [y, z₂, z₁, Data.set, Data.write, BinOp.eval] using hbin
  exact e₁.seq (e₂.seq e₃)

/-- Appending a word preserves the doubling-array invariant, modifies only cells in
`[x.regs ptr, y.regs frontier)` (hence only within `[0, y.regs frontier)`), and satisfies the
potential-method amortized bound with constant `49`. -/
theorem append_exec {w : ℕ} {vs : List ℕ} {x : Data 12} (hr : Rep vs x)
    (hw : Fits w (x.regs frontier + 2 * x.regs cap)) :
    ∃ y n, Exec w program x y n ∧
      Rep (vs ++ [x.regs arg]) y ∧
      (∀ a, a < x.regs ptr ∨ y.regs frontier ≤ a → y.mem a = x.mem a) ∧
      n + potential (vs ++ [x.regs arg]) y ≤ 49 + potential vs x ∧
      n + potential (vs ++ [x.regs arg]) y - potential vs x ≤ 49 := by
  have hcap_pos := hr.capacity_pos
  have hlen_eq := hr.length_eq
  have hlen_le := hr.length_le
  have hcap_le := hr.capacity_le
  have hptr_eq := hr.pointer_eq
  have hfront_eq := hr.frontier_eq
  have h1 : Fits w 1 := hw.of_le (by omega)
  by_cases hc : (Cond.eq len cap).Holds x
  · have hfull : x.regs len = x.regs cap := hc
    have hp : x.regs ptr + x.regs len ≤ x.regs frontier := by omega
    obtain ⟨z, hz, hz_ptr, hz_cap, hz_front, hz_copy, hz_frame⟩ :=
      grow_exec x h1 hfull hp hw
    have hz_len : z.regs len = x.regs len := hz.regs_eq (by decide)
    have hz_arg : z.regs arg = x.regs arg := hz.regs_eq (by decide)
    have hif : ExecWithin w (ram[if len = cap then [ ⟪grow⟫ ] else [ temp ← temp ]])
        x z (15 * x.regs cap + 15) := hz.branch_pos hc
    have haddr : Fits w (z.regs ptr + z.regs len) := hw.of_le (by omega)
    have hlen : Fits w (z.regs len + 1) := hw.of_le (by omega)
    let y := (((z.set one 1).set addr (z.regs ptr + z.regs len)).write
      (z.regs ptr + z.regs len) (z.regs arg)).set len (z.regs len + 1)
    have htail : Exec w (ram[one ← #1; ⟪writeAt addr ptr len arg⟫; len ← len + one]) z y 4 :=
      appendTail_exec z h1 haddr hlen
    obtain ⟨n, hn, he⟩ := hif.seq htail.within
    have hy_len : y.regs len = vs.length + 1 := by
      simp +decide [y, Data.set, Data.write, hz_len, hlen_eq]
    have hy_cap : y.regs cap = 2 * x.regs cap := by
      simpa +decide [y, Data.set, Data.write] using hz_cap
    have hy_ptr : y.regs ptr = x.regs frontier := by
      simpa +decide [y, Data.set, Data.write] using hz_ptr
    have hy_front : y.regs frontier = x.regs frontier + 2 * x.regs cap := by
      simpa +decide [y, Data.set, Data.write] using hz_front
    have hy_mem : y.mem = Function.update z.mem (z.regs ptr + z.regs len) (z.regs arg) := rfl
    refine ⟨y, n, he, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [List.length_append] using hy_len
      · omega
      · simp only [List.length_append, List.length_singleton]
        omega
      · simp only [List.length_append, List.length_singleton]
        omega
      · omega
      · omega
      · intro i
        by_cases hi : i.val < vs.length
        · have hne : z.regs ptr + i.val ≠ z.regs ptr + z.regs len := by omega
          have hmem : y.mem (y.regs ptr + i.val) = z.mem (z.regs ptr + i.val) := by
            rw [hy_mem, hy_ptr, ← hz_ptr, Function.update_of_ne hne]
          have hcopy := hz_copy i.val (by omega)
          have horig := hr.contents ⟨i.val, hi⟩
          change y.mem (y.regs ptr + i.val) = (vs ++ [x.regs arg])[i.val]
          rw [hmem, hcopy, List.getElem_append_left hi]
          exact horig
        · have hi_eq : i.val = vs.length := by
            have := i.isLt
            simp only [List.length_append, List.length_singleton] at this
            omega
          have hmem : y.mem (y.regs ptr + i.val) = x.regs arg := by
            rw [hy_mem, hy_ptr, ← hz_ptr, hi_eq, ← hlen_eq, ← hz_len, Function.update_self, hz_arg]
          change y.mem (y.regs ptr + i.val) = (vs ++ [x.regs arg])[i.val]
          rw [hmem]
          simp [hi_eq]
    · intro a ha
      have hne : a ≠ z.regs ptr + z.regs len := by omega
      have hmem : y.mem a = z.mem a := by
        rw [hy_mem, Function.update_of_ne hne]
      rw [hmem]
      exact hz_frame a (by omega)
    · simp only [potential, List.length_append, List.length_singleton, hy_cap]
      omega
    · simp only [potential, List.length_append, List.length_singleton, hy_cap]
      omega
  · have hlt : vs.length < x.regs cap := by
      change ¬x.regs len = x.regs cap at hc
      omega
    have hcopy_temp : Exec (B := .standard) w (.op (.copy temp temp)) x x 1 := by
      simpa [Data.set] using (Exec.copy (w := w) (x := x) (d := temp) (s := temp))
    have hif : Exec w (ram[if len = cap then [ ⟪grow⟫ ] else [ temp ← temp ]]) x x 3 :=
      Exec.branch_neg hc hcopy_temp
    have haddr : Fits w (x.regs ptr + x.regs len) := hw.of_le (by omega)
    have hlen : Fits w (x.regs len + 1) := hw.of_le (by omega)
    let y := (((x.set one 1).set addr (x.regs ptr + x.regs len)).write
      (x.regs ptr + x.regs len) (x.regs arg)).set len (x.regs len + 1)
    have htail : Exec w (ram[one ← #1; ⟪writeAt addr ptr len arg⟫; len ← len + one]) x y 4 :=
      appendTail_exec x h1 haddr hlen
    have he : Exec w program x y 7 := hif.seq htail
    have hy_len : y.regs len = vs.length + 1 := by
      simp +decide [y, Data.set, Data.write, hlen_eq]
    have hy_cap : y.regs cap = x.regs cap := by
      simp +decide [y, Data.set, Data.write]
    have hy_ptr : y.regs ptr = x.regs ptr := by
      simp +decide [y, Data.set, Data.write]
    have hy_front : y.regs frontier = x.regs frontier := by
      simp +decide [y, Data.set, Data.write]
    have hy_mem : y.mem = Function.update x.mem (x.regs ptr + x.regs len) (x.regs arg) := rfl
    refine ⟨y, 7, he, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [List.length_append] using hy_len
      · omega
      · simp only [List.length_append, List.length_singleton]
        omega
      · simp only [List.length_append, List.length_singleton]
        omega
      · omega
      · omega
      · intro i
        by_cases hi : i.val < vs.length
        · have hne : x.regs ptr + i.val ≠ x.regs ptr + x.regs len := by omega
          have hmem : y.mem (y.regs ptr + i.val) = x.mem (x.regs ptr + i.val) := by
            rw [hy_mem, hy_ptr, Function.update_of_ne hne]
          change y.mem (y.regs ptr + i.val) = (vs ++ [x.regs arg])[i.val]
          rw [hmem, List.getElem_append_left hi]
          exact hr.contents ⟨i.val, hi⟩
        · have hi_eq : i.val = vs.length := by
            have := i.isLt
            simp only [List.length_append, List.length_singleton] at this
            omega
          have hmem : y.mem (y.regs ptr + i.val) = x.regs arg := by
            rw [hy_mem, hy_ptr, hi_eq, ← hlen_eq, Function.update_self]
          change y.mem (y.regs ptr + i.val) = (vs ++ [x.regs arg])[i.val]
          rw [hmem]
          simp [hi_eq]
    · intro a ha
      have hne : a ≠ x.regs ptr + x.regs len := by omega
      rw [hy_mem, Function.update_of_ne hne]
    · simp only [potential, List.length_append, List.length_singleton, hy_cap]
      omega
    · simp only [potential, List.length_append, List.length_singleton, hy_cap]
      omega

/-- Indexed read returns `vs[x.regs arg]` in `temp` in two instructions without changing the
representation, memory, or potential. -/
theorem get_exec {w : ℕ} {vs : List ℕ} {x : Data 12} (hr : Rep vs x)
    (hi : x.regs arg < vs.length) (hw : Fits w (x.regs frontier)) :
    ∃ y, Exec w getProgram x y 2 ∧
      y.regs temp = vs.getD (x.regs arg) 0 ∧
      Rep vs y ∧ y.mem = x.mem ∧ potential vs y = potential vs x := by
  let y := (x.set addr (x.regs ptr + x.regs arg)).set temp (x.mem (x.regs ptr + x.regs arg))
  have hlen_le := hr.length_le
  have hptr_eq := hr.pointer_eq
  have hfront_eq := hr.frontier_eq
  have haddr : Fits w (x.regs ptr + x.regs arg) := hw.of_le (by omega)
  have he : Exec w getProgram x y 2 := readAt_exec haddr
  refine ⟨y, he, ?_, ?_, rfl, ?_⟩
  · have hmem := hr.contents ⟨x.regs arg, hi⟩
    simpa +decide [y, Data.set, List.getD_eq_getElem?_getD, hi] using hmem
  · refine ⟨?_, ?_, hr.length_le, hr.capacity_le, ?_, ?_, ?_⟩
    · simpa +decide [y, Data.set] using hr.length_eq
    · simpa +decide [y, Data.set] using hr.capacity_pos
    · simpa +decide [y, Data.set] using hr.pointer_eq
    · simpa +decide [y, Data.set] using hr.frontier_eq
    · intro i
      simpa +decide [y, Data.set] using hr.contents i
  · simp +decide [potential, y, Data.set]

/-- Charged initialization allocates the initial one-word block at address zero in fifteen
instructions, establishing `Rep []` with zero potential and frontier `1`. -/
theorem init_exec {w : ℕ} (x : Data 12) (h1 : Fits w 1) :
    ∃ y, Exec w initProgram x y 15 ∧
      Rep [] y ∧ y.regs frontier = 1 ∧ potential [] y = 0 ∧
      y.mem 0 = 0 ∧ (∀ a, 1 ≤ a → y.mem a = x.mem a) := by
  let x₁ := x.set frontier 0
  let x₂ := x₁.set count 1
  let x₃ := x₂.set len 0
  have e₁ : Exec (B := .standard) w (.op (.const frontier 0)) x x₁ 1 :=
    Exec.const (fits_zero w)
  have e₂ : Exec (B := .standard) w (.op (.const count 1)) x₁ x₂ 1 :=
    Exec.const h1
  have e₃ : Exec (B := .standard) w (.op (.const len 0)) x₂ x₃ 1 :=
    Exec.const (fits_zero w)
  have ha := alloc_exec (x := x₃) (frontier := frontier) (count := count)
    (result := ptr) (cur := idx) (zero := zero) (one := one) (by decide) h1
    (by simpa +decide [x₃, x₂, x₁, Data.set] using h1)
  let x₄ : Data 12 :=
    ⟨Function.update (Function.update (Function.update (Function.update (Function.update
        x₃.regs zero 0) one 1) ptr (x₃.regs frontier)) frontier
          (x₃.regs frontier + x₃.regs count)) idx (x₃.regs frontier + x₃.regs count),
      clear x₃.mem (x₃.regs frontier) (x₃.regs count)⟩
  let y := x₄.set cap (x₄.regs count)
  have e₅ : Exec (B := .standard) w (.op (.copy cap count)) x₄ y 1 := Exec.copy
  have he : Exec w initProgram x y 15 := by
    have hseq := e₁.seq (e₂.seq (e₃.seq (ha.seq e₅)))
    convert hseq using 1
    · rfl
    · simp +decide [x₃, x₂, x₁, Data.set]
  refine ⟨y, he, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun i => Fin.elim0 i⟩
    · simp +decide [y, x₄, x₃, x₂, x₁, Data.set]
    · simp +decide [y, x₄, x₃, x₂, x₁, Data.set]
    · simp +decide [y, x₄, x₃, x₂, x₁, Data.set]
    · simp +decide [y, x₄, x₃, x₂, x₁, Data.set]
    · simp +decide [y, x₄, x₃, x₂, x₁, Data.set]
    · simp +decide [y, x₄, x₃, x₂, x₁, Data.set]
  · simp +decide [y, x₄, x₃, x₂, x₁, Data.set]
  · simp +decide [potential, y, x₄, x₃, x₂, x₁, Data.set]
  · simp +decide [y, x₄, x₃, x₂, x₁, Data.set, clear]
  · intro a ha'
    have hno : ¬(Block.mk 0 1).Owns a := by
      simp only [Block.Owns]
      omega
    simpa +decide [y, x₄, x₃, x₂, x₁, Data.set] using
      clear_of_not_owns (m := x.mem) hno

/-! ## Connection to `Cslib.Stateful` and `Cslib.Stateful.Amortized` -/

/-- Doubling-array operations: append a word at the end or read an existing index. -/
inductive Op where
  /-- Append a word to the array. -/
  | append (value : ℕ)
  /-- Read the word at a zero-based index. -/
  | get (index : ℕ)
  deriving DecidableEq, Repr

/-- Mathematical specification of a bounded-word dynamic array.
Appending requires the value and the worst-case doubled frontier bound `8 * vs.length + 4`
to fit in a machine word; indexed reads require a valid index fitting a machine word. -/
abbrev spec (w : ℕ) : Stateful.Spec where
  State := List ℕ
  Op := Op
  Result
    | .append _ => Unit
    | .get _ => ℕ
  step vs
    | .append v => (vs ++ [v], ())
    | .get i => (vs, vs.getD i 0)
  valid vs
    | .append v => Fits w v ∧ Fits w (8 * vs.length + 4)
    | .get i => i < vs.length ∧ Fits w i

/-- Fixed operation dispatcher: `dest = 0` runs `program` (append), `dest = 1` runs `getProgram`. -/
def dispatch : Code .standard 12 := ram[
  zero ← #0;
  if dest = zero then [ ⟪program⟫ ] else [ ⟪getProgram⟫ ] ]

/-- Register calling convention for `dispatch`. -/
def implementation (w : ℕ) : DynamicProgram (spec w) 12 where
  code := dispatch
  output := temp
  input i := i == dest || i == arg
  encode o i := if i = dest then
      match o with | .append _ => 0 | .get _ => 1
    else
      match o with | .append v => v | .get idx => idx
  decode o regs := match o with
    | .append _ => some ()
    | .get _ => some (regs temp)

/-- Bounded-word doubling-array representation for `DynamicCertificate`. -/
structure BoundedRep (w : ℕ) (vs : List ℕ) (x : Data 12) : Prop where
  bounded : x.Bounded w
  rep : Rep vs x

/-- Amortized instruction charge per operation, including dispatch and final halt. -/
def charge : Op → ℕ
  | .append _ => 52
  | .get _ => 6

/-- Encoded arguments fit the word width whenever `1` fits and the operation is valid. -/
theorem arguments_fit {w : ℕ} (h1 : Fits w 1) {vs : List ℕ} (o : Op)
    (hv : (spec w).valid vs o) (i : Fin 12) : Fits w ((implementation w).encode o i) := by
  cases o with
  | append v =>
    change Fits w (if i = dest then 0 else v)
    split
    · exact fits_zero w
    · exact hv.1
  | get idx =>
    change Fits w (if i = dest then 1 else idx)
    split
    · exact h1
    · exact hv.2

/-- Argument delivery preserves `Rep` because `dest` and `arg` are not persistent representation
registers. -/
private theorem prepare_rep {vs : List ℕ} {x : Data 12} (hr : Rep vs x) (w : ℕ) (o : Op) :
    Rep vs ((implementation w).prepare o x) where
  length_eq := by simpa +decide [implementation, DynamicProgram.prepare] using hr.length_eq
  capacity_pos := by simpa +decide [implementation, DynamicProgram.prepare] using hr.capacity_pos
  length_le := hr.length_le
  capacity_le := hr.capacity_le
  pointer_eq := by simpa +decide [implementation, DynamicProgram.prepare] using hr.pointer_eq
  frontier_eq := by simpa +decide [implementation, DynamicProgram.prepare] using hr.frontier_eq
  contents i := by simpa +decide [implementation, DynamicProgram.prepare] using hr.contents i

/-- Every admissible operation executes `dispatch`, preserves `BoundedRep`, modifies only
cells below `y.regs frontier`, and satisfies the potential inequality with `charge o`
(counting the final halt). -/
theorem dispatch_exec {w : ℕ} (h1 : Fits w 1) {vs : List ℕ} {x : Data 12}
    (hr : BoundedRep w vs x) (o : Op) (hv : (spec w).valid vs o) :
    ∃ y n, Exec w dispatch ((implementation w).prepare o x) y n ∧
      (implementation w).decode o y.regs = some ((spec w).step vs o).2 ∧
      BoundedRep w ((spec w).step vs o).1 y ∧
      (∀ a, y.regs frontier ≤ a → y.mem a = x.mem a) ∧
      (n + 1) + potential ((spec w).step vs o).1 y ≤ charge o + potential vs x := by
  let x₀ := (implementation w).prepare o x
  have hx₀_bounded : x₀.Bounded w :=
    (implementation w).prepare_bounded hr.bounded (fun i _ => arguments_fit h1 o hv i)
  have hx₀_rep : Rep vs x₀ := prepare_rep hr.rep w o
  let x₁ := x₀.set zero 0
  have e₀ : Exec (B := .standard) w (.op (.const zero 0)) x₀ x₁ 1 :=
    Exec.const (fits_zero w)
  have hx₁_rep : Rep vs x₁ := by
    refine ⟨?_, ?_, hx₀_rep.length_le, hx₀_rep.capacity_le, ?_, ?_, ?_⟩
    · simpa +decide [x₁, Data.set] using hx₀_rep.length_eq
    · simpa +decide [x₁, Data.set] using hx₀_rep.capacity_pos
    · simpa +decide [x₁, Data.set] using hx₀_rep.pointer_eq
    · simpa +decide [x₁, Data.set] using hx₀_rep.frontier_eq
    · intro i
      simpa +decide [x₁, Data.set] using hx₀_rep.contents i
  have hpot₁ : potential vs x₁ = potential vs x := by
    simp +decide [potential, x₁, x₀, Data.set, implementation, DynamicProgram.prepare]
  cases o with
  | append v =>
    have hcond : (Cond.eq dest zero).Holds x₁ := by
      change x₁.regs dest = x₁.regs zero
      simp +decide [x₁, x₀, Data.set, implementation, DynamicProgram.prepare]
    have harg : x₁.regs arg = v := by
      simp +decide [x₁, x₀, Data.set, implementation, DynamicProgram.prepare]
    have hw : Fits w (x₁.regs frontier + 2 * x₁.regs cap) := by
      have hle := hx₁_rep.frontier_add_two_cap_le
      exact hv.2.of_le (by omega)
    obtain ⟨y, n, he, hy_rep, hy_frame, hy_pot, _⟩ := append_exec hx₁_rep hw
    have hrun : Exec w dispatch x₀ y (1 + (n + 1)) :=
      e₀.seq (Exec.branch_pos hcond he)
    rw [harg] at hy_rep hy_pot
    refine ⟨y, 1 + (n + 1), hrun, rfl, ⟨hrun.bounded hx₀_bounded, hy_rep⟩, ?_, ?_⟩
    · intro a ha
      exact hy_frame a (.inr ha)
    · simp only [charge]
      omega
  | get idx =>
    have hfront : Fits w (x₁.regs frontier) := by
      simpa +decide [x₁, x₀, Data.set, implementation, DynamicProgram.prepare] using
        hr.bounded.1 frontier
    have hcond : ¬(Cond.eq dest zero).Holds x₁ := by
      change ¬x₁.regs dest = x₁.regs zero
      simp +decide [x₁, x₀, Data.set, implementation, DynamicProgram.prepare]
    have harg : x₁.regs arg = idx := by
      simp +decide [x₁, x₀, Data.set, implementation, DynamicProgram.prepare]
    obtain ⟨y, he, htemp, hy_rep, hy_mem, hy_pot⟩ :=
      get_exec hx₁_rep (by rw [harg]; exact hv.1) hfront
    have hrun : Exec w dispatch x₀ y (1 + (2 + 2)) :=
      e₀.seq (Exec.branch_neg hcond he)
    refine ⟨y, 5, hrun, ?_, ⟨hrun.bounded hx₀_bounded, hy_rep⟩, ?_, ?_⟩
    · simp [implementation, htemp, harg, spec]
    · intro a _
      exact congrFun hy_mem a
    · simp only [charge]
      omega

/-- Semantic realization certificate for the bounded-word dynamic array. -/
def certificate {w : ℕ} (h1 : Fits w 1) : DynamicCertificate (implementation w) w where
  rep := BoundedRep w
  bounded h := h.bounded
  arguments_fit o hv i _ := arguments_fit h1 o hv i
  execute o hr hv := by
    obtain ⟨y, n, he, ha, hy, _⟩ := dispatch_exec h1 hr o hv
    exact ⟨y, n, he, ha, hy⟩

/-- Amortized instruction-cost certificate for the dynamic array (`52` per append, `6` per get,
including dispatch and final halt). -/
theorem amortized {w : ℕ} (h1 : Fits w 1) :
    Stateful.Amortized (certificate h1).realization
      DynamicProgram.OperationTrace.instructions potential (fun _ o => charge o) where
  step hr hv he := by
    obtain ⟨z, n, hz, _, _, _, hpot⟩ := dispatch_exec h1 hr _ hv
    obtain ⟨rfl, hk⟩ := he.eq_of_exec hz
    rw [hk]
    exact hpot

/-- Uniform amortized instruction-cost certificate (`52` instructions per operation). -/
theorem amortized_uniform {w : ℕ} (h1 : Fits w 1) :
    Stateful.Amortized (certificate h1).realization
      DynamicProgram.OperationTrace.instructions potential (fun _ _ => 52) where
  step {vs c o a c' trace} hr hv he := by
    have h := (amortized h1).step hr hv he
    cases o <;> simp only [charge] at h ⊢ <;> omega

/-- Every concrete call modifies only cells below `y.regs frontier`. -/
theorem modifies {w : ℕ} (h1 : Fits w 1) {vs : List ℕ} {x y : Data 12} {o : Op}
    {a : (spec w).Result o} {trace : DynamicProgram.OperationTrace}
    (hr : BoundedRep w vs x) (hv : (spec w).valid vs o)
    (he : (implementation w).ExecOp w x o a y trace) :
    Modifies (Finset.range (y.regs frontier)) x.mem y.mem := by
  obtain ⟨z, n, hz, _, _, hf, _⟩ := dispatch_exec h1 hr o hv
  obtain ⟨rfl, _⟩ := he.eq_of_exec hz
  intro addr haddr
  exact hf addr (Nat.le_of_not_lt (Finset.mem_range.not.mp haddr))

/-- Disjoint heap assertions above `y.regs frontier` survive every dynamic-array call. -/
theorem frame {w : ℕ} (h1 : Fits w 1) {vs : List ℕ} {x y : Data 12} {o : Op}
    {a : (spec w).Result o} {trace : DynamicProgram.OperationTrace}
    (hr : BoundedRep w vs x) (hv : (spec w).valid vs o)
    (he : (implementation w).ExecOp w x o a y trace)
    {Q : HeapAssertion} (hQ : Q.holds x.mem)
    (hd : Disjoint Q.footprint (Finset.range (y.regs frontier))) : Q.holds y.mem :=
  HeapAssertion.frame hQ hd (modifies h1 hr hv he)

/-- Every admissible adaptive client executes with total instructions bounded by `52` per
operation plus initial credit, retaining final credit and the `< 4 * m` space invariant. -/
theorem run_client {w : ℕ} (h1 : Fits w 1) {α : Type} (p : (spec w).Client α)
    {vs : List ℕ} {x : Data 12} (hr : BoundedRep w vs x)
    (hv : (spec w).ValidHistory vs ((spec w).runClient vs p).2.2) :
    ∃ y traces, Stateful.Executes ((implementation w).ExecOp w) p x
        ((spec w).runClient vs p).1 y traces ∧
      BoundedRep w ((spec w).runClient vs p).2.1 y ∧
      Stateful.total DynamicProgram.OperationTrace.instructions traces +
        potential ((spec w).runClient vs p).2.1 y ≤
          ((spec w).runClient vs p).2.2.length * 52 + potential vs x ∧
      (((spec w).runClient vs p).2.1 ≠ [] →
        y.regs frontier < 4 * ((spec w).runClient vs p).2.1.length) := by
  obtain ⟨y, traces, he, hy, hb⟩ := (amortized_uniform h1).exists_executes_const p hr hv
  exact ⟨y, traces, he, hy, hb, fun hne => hy.rep.space hne⟩

/-- Starting from arbitrary bounded machine data, run `initProgram` (15 instructions) followed
by any admissible adaptive client `p`. Total instructions across initialization and `m` operations
are at most `15 + 52 * m`, and the allocator frontier is `< 4 * n` whenever the final list of
length `n` is nonempty. -/
theorem run_initialized {w : ℕ} (h1 : Fits w 1) {α : Type} (p : (spec w).Client α)
    {x : Data 12} (hx : x.Bounded w)
    (hv : (spec w).ValidHistory [] ((spec w).runClient [] p).2.2) :
    ∃ ready y traces, Exec w initProgram x ready 15 ∧
      Stateful.Executes ((implementation w).ExecOp w) p ready
        ((spec w).runClient [] p).1 y traces ∧
      BoundedRep w ((spec w).runClient [] p).2.1 y ∧
      15 + Stateful.total DynamicProgram.OperationTrace.instructions traces +
        potential ((spec w).runClient [] p).2.1 y ≤
          15 + ((spec w).runClient [] p).2.2.length * 52 ∧
      (((spec w).runClient [] p).2.1 ≠ [] →
        y.regs frontier < 4 * ((spec w).runClient [] p).2.1.length) := by
  obtain ⟨ready, hi, hr_init, _, hpot_init, _, _⟩ := init_exec x h1
  have hready : BoundedRep w [] ready := ⟨hi.bounded hx, hr_init⟩
  obtain ⟨y, traces, he, hy, hb, hspace⟩ := run_client h1 p hready hv
  refine ⟨ready, y, traces, hi, he, hy, ?_, hspace⟩
  omega

/-- Client that appends each element of `us` in order. -/
def appendAll {w : ℕ} : List ℕ → (spec w).Client Unit
  | [] => .pure ()
  | v :: us => .liftBind (.append v) fun _ => appendAll us

/-- Mathematical execution of `appendAll` appends `us` to `vs` and records `us.map Op.append`. -/
@[simp]
theorem runClient_appendAll (w : ℕ) (vs us : List ℕ) :
    (spec w).runClient vs (appendAll us) = ((), vs ++ us, us.map Op.append) := by
  induction us generalizing vs with
  | nil => simp [appendAll]
  | cons v us ih =>
    simp [appendAll, spec, ih, List.append_assoc]

/-- `appendAll us` is admissible from `vs` whenever every element of `us` fits `w` and
`8 * (vs.length + us.length) + 4` fits `w`. -/
theorem validHistory_appendAll {w : ℕ} {vs us : List ℕ}
    (hvals : ∀ v ∈ us, Fits w v) (hlen : Fits w (8 * (vs.length + us.length) + 4)) :
    (spec w).ValidHistory vs ((spec w).runClient vs (appendAll us)).2.2 := by
  induction us generalizing vs with
  | nil => trivial
  | cons v us ih =>
    simp only [appendAll, Stateful.Spec.runClient_liftBind, Stateful.Spec.validHistory_cons, spec]
    refine ⟨⟨hvals v (List.mem_cons_self ..), hlen.of_le (by simp)⟩, ?_⟩
    exact ih (fun u hu => hvals u (List.mem_cons_of_mem v hu))
      (hlen.of_le (by simp only [List.length_append, List.length_cons, List.length_nil]; omega))

/-- Any sequence of `m = vs.length` appends starting from the charged initializer executes in at
most `15 + 52 * m` total charged instructions and uses fewer than `4 * m` total allocated words
whenever `vs ≠ []`. -/
theorem run_appendAll {w : ℕ} (h1 : Fits w 1) {vs : List ℕ} {x : Data 12}
    (hx : x.Bounded w) (hvals : ∀ v ∈ vs, Fits w v)
    (hlen : Fits w (8 * vs.length + 4)) :
    ∃ ready y traces, Exec w initProgram x ready 15 ∧
      Stateful.Executes ((implementation w).ExecOp w) (appendAll vs) ready () y traces ∧
      BoundedRep w vs y ∧
      15 + Stateful.total DynamicProgram.OperationTrace.instructions traces +
        potential vs y ≤ 15 + vs.length * 52 ∧
      (vs ≠ [] → y.regs frontier < 4 * vs.length) := by
  have hv : (spec w).ValidHistory [] ((spec w).runClient [] (appendAll vs)).2.2 :=
    validHistory_appendAll hvals (by simpa using hlen)
  simpa [runClient_appendAll] using run_initialized h1 (appendAll vs) hx hv

end Cslib.Algorithms.WordRAM.DynamicArray

end
