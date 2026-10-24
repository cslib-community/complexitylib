/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Multiword.Workspace
import Mathlib.Data.Nat.Choose.Basic

/-!
# Schoolbook multiplication on the checked word RAM

The code is unrolled for fixed operand lengths. Each row adds one shifted digit product
to the accumulator and appends its final carry. Leading zero updates make the active
accumulator and shifted operand have the same length.

## Main definitions

* `Cslib.WordRAM.Multiword.Schoolbook.cell`, `Cslib.WordRAM.Multiword.Schoolbook.row`: one
  multiply-add cell and one complete multiply-add row.
* `Cslib.WordRAM.Multiword.Schoolbook.rows`, `Cslib.WordRAM.Multiword.Schoolbook.rowCost`,
  `Cslib.WordRAM.Multiword.Schoolbook.clear`, `Cslib.WordRAM.Multiword.Schoolbook.program`:
  the unrolled schoolbook rows, their instruction cost, accumulator clearing, and full
  multiplication routine.
* `Cslib.WordRAM.Multiword.Schoolbook.registers`,
  `Cslib.WordRAM.Multiword.Schoolbook.leftRegs`,
  `Cslib.WordRAM.Multiword.Schoolbook.rightRegs`,
  `Cslib.WordRAM.Multiword.Schoolbook.outputRegs`,
  `Cslib.WordRAM.Multiword.Schoolbook.lowRegs`,
  `Cslib.WordRAM.Multiword.Schoolbook.highRegs`,
  `Cslib.WordRAM.Multiword.Schoolbook.fixedProgram`,
  `Cslib.WordRAM.Multiword.Schoolbook.input`: a concrete register allocation and input
  encoding for arbitrary fixed operand lengths.

## Main results

* `Cslib.WordRAM.Multiword.Schoolbook.exec_fixedProgram`: exact multiplication, bounded digits,
  preservation of operands and memory, and an exact width-independent instruction count.
* `Cslib.WordRAM.Multiword.Schoolbook.exec_eighteen`: 18-digit operands, 36 result digits,
  76 registers, and 2465 instructions for every physical word width at least two.

Inputs and outputs use little-endian half-word digits. Conversion from other representations
is not part of the routine. Odd widths use the same floor-half radix. Widths zero and one
are excluded: their floor-half radix is one and cannot represent a nonzero integer.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009].
-/

@[expose] public section

namespace Cslib.WordRAM.Multiword.Schoolbook

open Workspace

variable {r : ℕ}

private theorem value_cons (β : ℕ) (x : Data (r + 4)) (d : Fin (r + 4))
    (ds : List (Fin (r + 4))) :
    value β x (d :: ds) = x.regs d + β * value β x ds := rfl

private theorem value_eq_of_frame {β : ℕ} {x y : Data (r + 4)}
    {ds es : List (Fin (r + 4))}
    (hf : Frame x y ds) (he : ∀ i ∈ es, i ∉ ds ∧ i ≠ total ∧ i ≠ carry) :
    value β y es = value β x es := by
  unfold value
  congr 1
  exact List.map_congr_left fun i hi => hf.2 i (he i hi).1 (he i hi).2.1 (he i hi).2.2

/-- The in-place form of `LimbUpdate.program`: five ordinary instructions for one multiply-add,
overwriting the destination digit after reading it. -/
def cell (a b d : Fin (r + 4)) : Code .standard (r + 4) := ram[
  total ← a * b;
  total ← total + d;
  total ← total + carry;
  d ← total % base;
  carry ← total / base ]

/-- All workspace is included in the exact result of a cell. -/
private def cellResult (x : Data (r + 4)) (a b d : Fin (r + 4)) : Data (r + 4) :=
  let s := x.regs a * x.regs b + x.regs d + x.regs carry
  ((x.set total s).set d (s % x.regs base)).set carry (s / x.regs base)

private theorem exec_cell {w : ℕ} (x : Data (r + 4)) (a b d : Fin (r + 4))
    (hd : IsDigit d) (hw : 2 ≤ w) (hbase : x.regs base = radix w)
    (ha : x.regs a < radix w) (hb : x.regs b < radix w)
    (hx : x.regs d < radix w) (hc : x.regs carry < radix w) :
    Exec w (cell a b d) x (cellResult x a b d) 5 ∧
      (cellResult x a b d).regs d < radix w ∧
      (cellResult x a b d).regs carry < radix w ∧
      (cellResult x a b d).regs d + radix w * (cellResult x a b d).regs carry =
        x.regs a * x.regs b + x.regs d + x.regs carry ∧
      Frame x (cellResult x a b d) [d] := by
  obtain ⟨hdt, hdc, hdb, _⟩ := digit_ne hd
  have hs := limb_update_fits ha hb hx hc
  have hp := hs.of_le (show x.regs a * x.regs b ≤
      x.regs a * x.regs b + x.regs d + x.regs carry by omega)
  have hpd := hs.of_le (show x.regs a * x.regs b + x.regs d ≤
      x.regs a * x.regs b + x.regs d + x.regs carry by omega)
  have hm := hs.of_le (Nat.mod_le
    (x.regs a * x.regs b + x.regs d + x.regs carry) (x.regs base))
  have hq := hs.of_le (Nat.div_le_self
    (x.regs a * x.regs b + x.regs d + x.regs carry) (x.regs base))
  have hβ : 0 < radix w := by have := one_lt_radix hw; omega
  have hcl : (x.regs a * x.regs b + x.regs d + x.regs carry) / radix w < radix w :=
    (Nat.div_lt_iff_lt_mul hβ).mpr (by
      simpa only [pow_two] using limb_update_lt_sq ha hb hx hc)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ram_eval [cell, cellResult, hdt, hdc, hdb, Ne.symm hdt, Ne.symm hdb,
      total, carry, base, Fin.mk.injEq, hp, hpd, hs, hm, hq]
    simp only [Data.set, Function.update_idem]
  · simpa only [cellResult, Data.set_regs, Function.update_apply, hdc, ↓reduceIte,
      hbase] using
      Nat.mod_lt (x.regs a * x.regs b + x.regs d + x.regs carry) hβ
  · simpa only [cellResult, Data.set_regs, Function.update_self, hbase] using hcl
  · simpa only [cellResult, Data.set_regs, Function.update_apply, hdc, ↓reduceIte,
      hbase] using
      Nat.mod_add_div (x.regs a * x.regs b + x.regs d + x.regs carry) (radix w)
  · refine ⟨rfl, ?_⟩
    intro i hi hit hic
    simp only [List.mem_singleton] at hi
    simp only [cellResult, Data.set_regs, Function.update_apply, hi, hit, hic, ↓reduceIte]

/-- Update a full row. The final self-copy gives the empty row a one-instruction execution. -/
def row (a : Fin (r + 4)) : List (Fin (r + 4)) → List (Fin (r + 4)) →
    Code .standard (r + 4)
  | b :: bs, d :: ds => .seq (cell a b d) (row a bs ds)
  | _, _ => .op (.copy carry carry)

/-- A row has one five-instruction cell per digit and one final self-copy. -/
theorem size_row (a : Fin (r + 4)) (bs ds : List (Fin (r + 4)))
    (hlen : bs.length = ds.length) : (row a bs ds).size = 5 * ds.length + 1 := by
  induction bs generalizing ds with
  | nil => cases ds <;> simp_all [row]
  | cons b bs ih =>
    cases ds with
    | nil => simp_all
    | cons d ds => simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
                   simp only [row, Code.size, cell, ih ds hlen, List.length_cons]
                   omega

/-- Execute an entire row, with exact reconstruction including its final carry.
`I` is any set of preserved input registers, disjoint from the destination registers. -/
private theorem exec_row {w : ℕ} (hw : 2 ≤ w) (I : Set (Fin (r + 4)))
    (hI : ∀ i ∈ I, i ≠ total ∧ i ≠ carry) (a : Fin (r + 4)) (haI : a ∈ I)
    (bs ds : List (Fin (r + 4))) (hlen : bs.length = ds.length)
    (hbs : ∀ b ∈ bs, b ∈ I) (hds : ∀ d ∈ ds, IsDigit d ∧ d ∉ I)
    (hnd : ds.Nodup) (x : Data (r + 4)) (hbase : x.regs base = radix w)
    (ha : x.regs a < radix w) (hb : Bounded (radix w) x bs)
    (hd : Bounded (radix w) x ds) (hc : x.regs carry < radix w) :
    ∃ y, Exec w (row a bs ds) x y (5 * ds.length + 1) ∧
      Bounded (radix w) y ds ∧ y.regs carry < radix w ∧
      value (radix w) y ds + radix w ^ ds.length * y.regs carry =
        x.regs a * value (radix w) x bs + value (radix w) x ds + x.regs carry ∧
      Frame x y ds := by
  induction bs generalizing ds x with
  | nil =>
    cases ds with
    | nil =>
      refine ⟨x.set carry (x.regs carry), ?_, ?_, ?_, ?_, ?_⟩
      · ram_eval [row]
      · simp [Bounded]
      · simpa using hc
      · simp [value]
      · exact ⟨rfl, fun i _ _ hi => by
          simp only [Data.set_regs, Function.update_apply, hi, ↓reduceIte]⟩
    | cons => simp_all
  | cons b bs ih =>
    cases ds with
    | nil => simp_all
    | cons d ds =>
      have hlen' : bs.length = ds.length := by simpa using hlen
      have hd0 := hds d (by simp)
      obtain ⟨he, hzd, hzc, hzeq, hzf⟩ :=
        exec_cell x a b d hd0.1 hw hbase ha (hb b (by simp))
          (hd d (by simp)) hc
      let z := cellResult x a b d
      have hzI (i : Fin (r + 4)) (hi : i ∈ I) : z.regs i = x.regs i :=
        hzf.2 i (by simp only [List.mem_singleton]; rintro rfl; exact hd0.2 hi)
          (hI i hi).1 (hI i hi).2
      have hzds (i : Fin (r + 4)) (hi : i ∈ ds) : z.regs i = x.regs i :=
        hzf.2 i (by
          simp only [List.mem_singleton]
          rintro rfl
          exact (List.nodup_cons.mp hnd).1 hi)
          (digit_ne (hds i (by simp [hi])).1).1
          (digit_ne (hds i (by simp [hi])).1).2.1
      have hzb : z.regs base = radix w := by
        rw [hzf.2 base (by simp [Ne.symm (digit_ne hd0.1).2.2.1])
          (by simp [base, total]) (by simp [base, carry])]
        exact hbase
      obtain ⟨y, hey, hyd, hyc, hyeq, hyf⟩ := ih ds hlen'
        (fun i hi => hbs i (by simp [hi])) (fun i hi => hds i (by simp [hi]))
        (List.nodup_cons.mp hnd).2 z hzb (by rw [hzI a haI]; exact ha)
        (fun i hi => by rw [hzI i (hbs i (by simp [hi]))]; exact hb i (by simp [hi]))
        (fun i hi => by rw [hzds i hi]; exact hd i (by simp [hi])) hzc
      have hyd0 : y.regs d = z.regs d :=
        hyf.2 d (List.nodup_cons.mp hnd).1 (digit_ne hd0.1).1 (digit_ne hd0.1).2.1
      have hvalbs : value (radix w) z bs = value (radix w) x bs :=
        value_eq_of_frame (es := bs) hzf (fun i hi =>
          ⟨by
            simp only [List.mem_singleton]
            rintro rfl
            exact hd0.2 (hbs i (by simp [hi])), hI i (hbs i (by simp [hi]))⟩)
      have hvalds : value (radix w) z ds = value (radix w) x ds := by
        unfold value
        congr 1
        exact List.map_congr_left hzds
      refine ⟨y, ?_, ?_, hyc, ?_, ?_⟩
      · simpa only [row, List.length_cons, Nat.mul_add, Nat.mul_one,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he.seq hey
      · intro i hi
        rcases List.mem_cons.mp hi with rfl | hi
        · rw [hyd0]; exact hzd
        · exact hyd i hi
      · simp only [value_cons, List.length_cons,
          pow_succ] at ⊢
        rw [hyd0]
        rw [hzI a haI, hvalbs, hvalds] at hyeq
        change z.regs d + radix w * z.regs carry = _ at hzeq
        nlinarith [congrArg (radix w * ·) hyeq]
      · refine ⟨hyf.1.trans hzf.1, ?_⟩
        intro i hi hit hic
        exact (hyf.2 i (fun hm => hi (by simp [hm])) hit hic).trans
          (hzf.2 i (by simpa using fun h => hi (by simp [h])) hit hic)

/-- Unrolled schoolbook rows. `ds` is the current accumulator and `os` supplies one fresh
high digit per remaining multiplicand digit. The multiplier gains a leading zero each row. -/
def rows : List (Fin (r + 4)) → List (Fin (r + 4)) → List (Fin (r + 4)) →
    List (Fin (r + 4)) → Code .standard (r + 4)
  | a :: as, bs, ds, d :: os =>
    .seq (.op (.const carry 0)) (.seq (row a bs ds)
      (.seq (.op (.copy d carry)) (rows as (zero :: bs) (ds ++ [d]) os)))
  | _, _, _, _ => .op (.const carry 0)

/-- Exact instruction count of the unrolled rows, including empty-row self-copies. -/
def rowCost : ℕ → ℕ → ℕ
  | 0, _ => 1
  | m + 1, n => 5 * n + 3 + rowCost m (n + 1)

/-- The extra cells are the leading-zero updates in successive shifted rows. -/
theorem rowCost_eq (m n : ℕ) :
    rowCost m n = 5 * (m * n + m * (m - 1) / 2) + 3 * m + 1 := by
  have h : rowCost m n = 5 * (m * n + m.choose 2) + 3 * m + 1 := by
    induction m generalizing n with
    | zero => simp [rowCost]
    | succ m ih =>
      have hs : (m + 1).choose 2 = m + m.choose 2 := by
        rw [Nat.choose_succ_succ', Nat.choose_one_right]
      rw [rowCost, ih, hs]
      ring
  simpa only [Nat.choose_two_right] using h

/-- The instruction count of `rows` equals `rowCost` on the operand lengths. -/
theorem size_rows (as bs ds os : List (Fin (r + 4)))
    (hlen : bs.length = ds.length) (hos : os.length = as.length) :
    (rows as bs ds os).size = rowCost as.length bs.length := by
  induction as generalizing bs ds os with
  | nil => cases os <;> simp_all [rows, rowCost]
  | cons a as ih =>
    cases os with
    | nil => simp_all
    | cons d os =>
      have hos' : os.length = as.length := by simpa using hos
      simp only [rows, Code.size, size_row a bs ds hlen,
        ih (zero :: bs) (ds ++ [d]) os (by simp [hlen]) hos',
        List.length_cons, rowCost]
      omega

/-- The runtime is constant for fixed operand lengths, independently of the physical width. -/
theorem rowCost_le (m n : ℕ) : rowCost m n ≤ 5 * m * (n + m) + 3 * m + 1 := by
  induction m generalizing n with
  | zero => simp [rowCost]
  | succ m ih =>
    have := ih (n + 1)
    simp only [rowCost]
    nlinarith

private theorem frame_carry (x : Data (r + 4)) (v : ℕ) (ds : List (Fin (r + 4))) :
    Frame x (x.set carry v) ds := by
  refine ⟨rfl, fun i _ _ hi => ?_⟩
  simp only [Data.set_regs, Function.update_apply, hi, ↓reduceIte]

private theorem frame_digit (x : Data (r + 4)) (d : Fin (r + 4)) (v : ℕ) :
    Frame x (x.set d v) [d] := by
  refine ⟨rfl, fun i hi _ _ => ?_⟩
  simp only [List.mem_singleton] at hi
  simp only [Data.set_regs, Function.update_apply, hi, ↓reduceIte]

private theorem frame_input {x y : Data (r + 4)} {I : Set (Fin (r + 4))}
    {ds : List (Fin (r + 4))} (hf : Frame x y ds)
    (hI : ∀ i ∈ I, i ≠ total ∧ i ≠ carry) (hd : ∀ d ∈ ds, d ∉ I)
    {i : Fin (r + 4)} (hi : i ∈ I) : y.regs i = x.regs i :=
  hf.2 i (fun hm => hd i hm hi) (hI i hi).1 (hI i hi).2

/-- Complete schoolbook multiplication with an arbitrary initial accumulator. The theorem
constructs an execution and proves its product equation; no multiplication specification is
assumed. The accumulator grows by one carry digit per row. -/
private theorem exec_rows {w : ℕ} (hw : 2 ≤ w) (I : Set (Fin (r + 4)))
    (hI : ∀ i ∈ I, i ≠ total ∧ i ≠ carry) (hzI : zero ∈ I)
    (as bs ds os : List (Fin (r + 4)))
    (hlen : bs.length = ds.length) (hos : os.length = as.length)
    (has : ∀ a ∈ as, a ∈ I) (hbs : ∀ b ∈ bs, b ∈ I)
    (hds : ∀ d ∈ ds ++ os, IsDigit d ∧ d ∉ I) (hnd : (ds ++ os).Nodup)
    (x : Data (r + 4)) (hbase : x.regs base = radix w) (hz : x.regs zero = 0)
    (ha : Bounded (radix w) x as) (hb : Bounded (radix w) x bs)
    (hd : Bounded (radix w) x ds) :
    ∃ y, Exec w (rows as bs ds os) x y (rowCost as.length bs.length) ∧
      Bounded (radix w) y (ds ++ os) ∧
      value (radix w) y (ds ++ os) =
        value (radix w) x ds + value (radix w) x as * value (radix w) x bs ∧
      Frame x y (ds ++ os) := by
  induction as generalizing bs ds os x with
  | nil =>
    have hos' : os = [] := by simpa using hos
    subst os
    let y := x.set carry 0
    have hf := frame_carry x 0 ds
    have hy (i : Fin (r + 4)) (hi : i ∈ ds) : y.regs i = x.regs i := by
      simp only [y, Data.set_regs, Function.update_apply,
        (digit_ne (hds i (by simpa using hi)).1).2.1, ↓reduceIte]
    refine ⟨y, ?_, ?_, ?_, ?_⟩
    · ram_eval [rows, rowCost, y]
    · simpa only [List.append_nil, Bounded] using fun i hi => (hy i hi) ▸ hd i hi
    · simp only [List.append_nil, value, List.map_nil, Nat.ofDigits_nil, zero_mul,
        add_zero]
      congr 1
      exact List.map_congr_left hy
    · simpa only [List.append_nil] using hf
  | cons a as ih =>
    cases os with
    | nil => simp_all
    | cons d os =>
      have hos' : os.length = as.length := by simpa using hos
      have hdd := hds d (by simp)
      have hds' : ∀ i ∈ ds, IsDigit i ∧ i ∉ I := fun i hi => hds i (by simp [hi])
      have hndds : ds.Nodup := (List.nodup_append.mp hnd).1
      have hdnot : d ∉ ds := by
        intro hm
        exact (List.nodup_append.mp hnd).2.2 d hm d (by simp) rfl
      let x₀ := x.set carry 0
      have hx₀ : Frame x x₀ ds := frame_carry x 0 ds
      have hx₀i (i : Fin (r + 4)) (hi : i ≠ carry) : x₀.regs i = x.regs i := by
        simp only [x₀, Data.set_regs, Function.update_apply, hi, ↓reduceIte]
      obtain ⟨z, hez, hzd, hzc, hzeq, hzf⟩ := exec_row hw I hI a (has a (by simp))
        bs ds hlen hbs hds' hndds x₀
        (by rw [hx₀i base (by simp [base, carry])]; exact hbase)
        (by rw [hx₀i a (hI a (has a (by simp))).2]; exact ha a (by simp))
        (fun i hi => by rw [hx₀i i (hI i (hbs i hi)).2]; exact hb i hi)
        (fun i hi => by rw [hx₀i i (digit_ne (hds' i hi).1).2.1]; exact hd i hi)
        (by
          simp only [x₀, Data.set_regs, Function.update_self]
          have := one_lt_radix hw
          omega)
      have hfxz : Frame x z ds := frame_trans hx₀ hzf
      let u := z.set d (z.regs carry)
      have hfzu : Frame z u [d] := frame_digit z d (z.regs carry)
      have hfxu : Frame x u (ds ++ [d]) := frame_trans
        (frame_mono hfxz (by intro i hi; simp [hi]))
        (frame_mono hfzu (by intro i hi; simp [hi]))
      have huI (i : Fin (r + 4)) (hi : i ∈ I) : u.regs i = x.regs i :=
        frame_input hfxu hI (by
          intro j hj
          rcases List.mem_append.mp hj with hj | hj
          · exact (hds' j hj).2
          · obtain rfl := List.mem_singleton.mp hj
            exact hdd.2) hi
      have huBase : u.regs base = radix w := by
        rw [hfxu.2 base (by
          simp only [List.mem_append, List.mem_singleton, not_or]
          exact ⟨fun hm => (digit_ne (hds' base hm).1).2.2.1 rfl,
            Ne.symm (digit_ne hdd.1).2.2.1⟩)
          (by simp [base, total]) (by simp [base, carry])]
        exact hbase
      have huDs : Bounded (radix w) u (ds ++ [d]) := by
        intro i hi
        rcases List.mem_append.mp hi with hids | hid
        · rw [hfzu.2 i (by
            simp only [List.mem_singleton]
            rintro rfl
            exact hdnot hids)
            (digit_ne (hds' i hids).1).1 (digit_ne (hds' i hids).1).2.1]
          exact hzd i hids
        · obtain rfl := List.mem_singleton.mp hid
          simpa [u] using hzc
      have hnext : (ds ++ [d]) ++ os = ds ++ d :: os := by simp
      obtain ⟨y, hey, hyd, hyeq, hyf⟩ := ih (zero :: bs) (ds ++ [d]) os
        (by simp [hlen]) hos' (fun i hi => has i (by simp [hi]))
        (fun i hi => by
          rcases List.mem_cons.mp hi with rfl | hi
          · exact hzI
          · exact hbs i hi)
        (by rw [hnext]; exact hds) (by rw [hnext]; exact hnd)
        u huBase (by rw [huI zero hzI]; exact hz)
        (fun i hi => by rw [huI i (has i (by simp [hi]))]; exact ha i (by simp [hi]))
        (by
          intro i hi
          rcases List.mem_cons.mp hi with rfl | hi
          · rw [huI zero hzI, hz]; have := one_lt_radix hw; omega
          · rw [huI i (hbs i hi)]; exact hb i hi) huDs
      have huValDs : value (radix w) u (ds ++ [d]) =
          value (radix w) x ds + x.regs a * value (radix w) x bs := by
        have hvds := value_eq_of_frame (β := radix w) (es := ds) hfzu (fun i hi =>
          ⟨by
            simp only [List.mem_singleton]
            rintro rfl
            exact hdnot hi,
            (digit_ne (hds' i hi).1).1, (digit_ne (hds' i hi).1).2.1⟩)
        simp only [value, List.map_append, Nat.ofDigits_append, List.length_map,
          List.map_singleton, Nat.ofDigits_singleton] at ⊢
        change value (radix w) u ds + radix w ^ ds.length * u.regs d = _
        rw [hvds]
        have hud : u.regs d = z.regs carry := by simp [u]
        rw [hud, hzeq]
        have h₀ (i : Fin (r + 4)) (hi : i ≠ carry) : x₀.regs i = x.regs i := hx₀i i hi
        have hva := h₀ a (hI a (has a (by simp))).2
        have hvb := value_eq_of_frame (β := radix w) (es := bs) hx₀ (fun i hi =>
          ⟨fun hm => (hds' i hm).2 (hbs i hi), hI i (hbs i hi)⟩)
        have hvd : value (radix w) x₀ ds = value (radix w) x ds := by
          unfold value
          congr 1
          exact List.map_congr_left fun i hi => h₀ i (digit_ne (hds' i hi).1).2.1
        rw [hva, hvb, hvd]
        simp only [x₀, Data.set_regs, Function.update_self, add_zero]
        exact Nat.add_comm _ _
      have huValAs : value (radix w) u as = value (radix w) x as := by
        unfold value
        congr 1
        exact List.map_congr_left fun i hi => huI i (has i (by simp [hi]))
      have huValBs : value (radix w) u (zero :: bs) =
          radix w * value (radix w) x bs := by
        rw [value_cons, huI zero hzI, hz, zero_add]
        congr 1
        unfold value
        congr 1
        exact List.map_congr_left fun i hi => huI i (hbs i hi)
      refine ⟨y, ?_, ?_, ?_, ?_⟩
      · have he₀ : Exec w (.op (.const (B := .standard) carry 0)) x x₀ 1 := by
          ram_eval [x₀]
        have hed : Exec w (.op (.copy (B := .standard) d carry)) z u 1 := by
          ram_eval [u]
        simp only [List.length_cons] at hey
        simp only [rows, List.length_cons, rowCost]
        convert he₀.seq (hez.seq (hed.seq hey)) using 1
        omega
      · simpa only [hnext] using hyd
      · rw [hnext, huValDs, huValAs, huValBs] at hyeq
        rw [hyeq, value_cons]
        ring
      · rw [hnext] at hyf
        exact frame_trans (frame_mono hfxu (by
          intro i hi
          simpa only [List.mem_append, List.mem_singleton, List.mem_cons] using
            (show i ∈ ds ∨ i = d ∨ i ∈ os from by
              rcases List.mem_append.mp hi with hi | hi
              · exact Or.inl hi
              · exact Or.inr (Or.inl (List.mem_singleton.mp hi))))) hyf

/-- Clear the initial accumulator; the empty clear uses one carry self-copy. -/
def clear : List (Fin (r + 4)) → Code .standard (r + 4)
  | [] => .op (.copy carry carry)
  | d :: ds => .seq (.op (.const d 0)) (clear ds)

/-- Clearing `ds` takes one constant instruction per digit plus one final self-copy. -/
theorem size_clear (ds : List (Fin (r + 4))) : (clear ds).size = ds.length + 1 := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp only [clear, Code.size, ih, List.length_cons]; omega

private theorem exec_clear {w : ℕ} (ds : List (Fin (r + 4)))
    (hds : ∀ i ∈ ds, IsDigit i) (hnd : ds.Nodup) (x : Data (r + 4)) :
    ∃ y, Exec w (clear ds) x y (ds.length + 1) ∧
      (∀ i ∈ ds, y.regs i = 0) ∧ Frame x y ds := by
  induction ds generalizing x with
  | nil =>
    refine ⟨x.set carry (x.regs carry), ?_, by simp, frame_carry _ _ _⟩
    ram_eval [clear]
  | cons d ds ih =>
    let z := x.set d 0
    obtain ⟨y, hey, hy, hyf⟩ := ih (fun i hi => hds i (by simp [hi]))
      (List.nodup_cons.mp hnd).2 z
    have hez : Exec w (.op (.const (B := .standard) d 0)) x z 1 := by ram_eval [z]
    refine ⟨y, ?_, ?_, ?_⟩
    · simpa only [clear, List.length_cons, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using hez.seq hey
    · intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · rw [hyf.2 i (List.nodup_cons.mp hnd).1 (digit_ne (hds i (by simp))).1
          (digit_ne (hds i (by simp))).2.1]
        simp [z]
      · exact hy i hi
    · exact frame_trans
        (frame_mono (frame_digit x d 0) (by simp))
        (frame_mono hyf (by intro i hi; simp [hi]))

/-- Complete multiplication: initialize the radix and zero, clear the initial accumulator,
and execute all rows. Operand and output register lists are fixed at code construction time. -/
def program (as bs ds os : List (Fin (r + 4))) : Code .standard (r + 4) :=
  .seq setup (.seq (clear ds) (rows as bs ds os))

/-- Exact code size, which is also the exact execution time on valid inputs. -/
theorem size_program (as bs ds os : List (Fin (r + 4)))
    (hlen : bs.length = ds.length) (hos : os.length = as.length) :
    (program as bs ds os).size = 7 + bs.length + rowCost as.length bs.length := by
  simp only [program, Code.size, setup, size_clear, size_rows as bs ds os hlen hos]
  omega

/-- Multiplication of two arbitrary fixed-length little-endian digit lists. All outputs
start arbitrary: initialization is part of the charged code. Every arithmetic operation uses
the original physical width and checked overflow. The complete product occupies `ds ++ os`.
The layout assumptions express only nonaliasing and reserved-register separation. -/
theorem exec {w : ℕ} (hw : 2 ≤ w) (as bs ds os : List (Fin (r + 4)))
    (hlen : bs.length = ds.length) (hos : os.length = as.length)
    (hin : ∀ i ∈ as ++ bs, IsDigit i) (hout : ∀ i ∈ ds ++ os, IsDigit i)
    (hnd : (ds ++ os).Nodup) (hdis : List.Disjoint (ds ++ os) (as ++ bs))
    (x : Data (r + 4)) (ha : Bounded (radix w) x as) (hb : Bounded (radix w) x bs) :
    ∃ y, Exec w (program as bs ds os) x y
        (7 + bs.length + rowCost as.length bs.length) ∧
      Bounded (radix w) y (ds ++ os) ∧
      value (radix w) y (ds ++ os) = value (radix w) x as * value (radix w) x bs ∧
      y.mem = x.mem ∧ ∀ i ∈ as ++ bs, y.regs i = x.regs i := by
  let I : Set (Fin (r + 4)) := {i | i = zero ∨ i ∈ as ++ bs}
  have hI : ∀ i ∈ I, i ≠ total ∧ i ≠ carry := by
    intro i hi
    rcases hi with rfl | hi
    · simp [zero, total, carry]
    · exact ⟨(digit_ne (hin i hi)).1, (digit_ne (hin i hi)).2.1⟩
  have houtI : ∀ i ∈ ds ++ os, IsDigit i ∧ i ∉ I := by
    intro i hi
    refine ⟨hout i hi, ?_⟩
    rintro (hz | hin')
    · exact (digit_ne (hout i hi)).2.2.2 hz
    · exact List.disjoint_left.mp hdis hi hin'
  let z := setupResult w x
  obtain ⟨u, heu, hu, huf⟩ := exec_clear (w := w) ds
    (fun i hi => hout i (by simp [hi])) (List.nodup_append.mp hnd).1 z
  have huz (i : Fin (r + 4)) (hi : i ∉ ds) (ht : i ≠ total) (hc : i ≠ carry) :
      u.regs i = z.regs i := huf.2 i hi ht hc
  have hui (i : Fin (r + 4)) (hi : i ∈ as ++ bs) : u.regs i = x.regs i := by
    rw [huz i (fun hm => List.disjoint_left.mp hdis (by simp [hm]) hi)
      (digit_ne (hin i hi)).1 (digit_ne (hin i hi)).2.1]
    exact setup_digit w x (hin i hi)
  have hub : u.regs base = radix w := by
    rw [huz base (fun hm => (digit_ne (hout base (by simp [hm]))).2.2.1 rfl)
      (by simp [base, total]) (by simp [base, carry])]
    simp [z, setupResult, base, zero]
  have huzero : u.regs zero = 0 := by
    rw [huz zero (fun hm => (digit_ne (hout zero (by simp [hm]))).2.2.2 rfl)
      (by simp [zero, total]) (by simp [zero, carry])]
    simp [z, setupResult]
  obtain ⟨y, hey, hyb, hyval, hyf⟩ := exec_rows hw I hI (Or.inl rfl)
    as bs ds os hlen hos (fun i hi => Or.inr (by simp [hi]))
    (fun i hi => Or.inr (by simp [hi])) houtI hnd u hub huzero
    (fun i hi => by rw [hui i (by simp [hi])]; exact ha i hi)
    (fun i hi => by rw [hui i (by simp [hi])]; exact hb i hi)
    (fun i hi => by rw [hu i hi]; have := one_lt_radix hw; omega)
  have huval : value (radix w) u ds = 0 := by
    unfold value
    have hm : ds.map u.regs = List.replicate ds.length 0 := by
      simpa only [List.map_const'] using List.map_congr_left hu
    rw [hm, Nat.ofDigits_replicate_zero]
  have hvals (es : List (Fin (r + 4))) (hes : es ⊆ as ++ bs) :
      value (radix w) u es = value (radix w) x es := by
    unfold value
    congr 1
    exact List.map_congr_left fun i hi => hui i (hes hi)
  refine ⟨y, ?_, hyb, ?_, ?_, ?_⟩
  · unfold program
    convert (exec_setup hw x).seq (heu.seq hey) using 1
    omega
  · rw [huval, zero_add, hvals as (by simp), hvals bs (by simp)] at hyval
    exact hyval
  · exact hyf.1.trans (huf.1.trans rfl)
  · intro i hi
    exact (frame_input hyf hI (fun j hj => (houtI j hj).2) (Or.inr hi)).trans (hui i hi)

/-- A contiguous list of digit registers, after the four reserved workspace registers. -/
def registers (start len : ℕ) (h : start + len ≤ r) : List (Fin (r + 4)) :=
  List.ofFn fun i : Fin len => ⟨4 + start + i.val, by omega⟩

private theorem registers_bounds {start len : ℕ} {h : start + len ≤ r}
    {i : Fin (r + 4)} (hi : i ∈ registers start len h) :
    4 + start ≤ i.val ∧ i.val < 4 + start + len := by
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hi
  dsimp
  omega

private theorem nodup_registers (start len : ℕ) (h : start + len ≤ r) :
    (registers start len h).Nodup := by
  apply List.nodup_ofFn_ofInjective
  intro i j hij
  apply Fin.ext
  have := congrArg Fin.val hij
  dsimp at this
  omega

/-- The first operand occupies the first `m` digit registers. -/
def leftRegs (m n : ℕ) : List (Fin (2 * (m + n) + 4)) :=
  registers 0 m (by omega)

/-- The second operand follows the first. -/
def rightRegs (m n : ℕ) : List (Fin (2 * (m + n) + 4)) :=
  registers m n (by omega)

/-- The `m + n` result digits follow both operands. -/
def outputRegs (m n : ℕ) : List (Fin (2 * (m + n) + 4)) :=
  registers (m + n) (n + m) (by omega)

/-- Initial zero accumulator, with the second operand's length. -/
def lowRegs (m n : ℕ) : List (Fin (2 * (m + n) + 4)) :=
  (outputRegs m n).take n

/-- One fresh high digit for each schoolbook row. -/
def highRegs (m n : ℕ) : List (Fin (2 * (m + n) + 4)) :=
  (outputRegs m n).drop n

private theorem lengths (m n : ℕ) :
    (leftRegs m n).length = m ∧ (rightRegs m n).length = n ∧
      (lowRegs m n).length = n ∧ (highRegs m n).length = m := by
  simp [leftRegs, rightRegs, lowRegs, highRegs, outputRegs, registers]

private theorem output_split (m n : ℕ) :
    lowRegs m n ++ highRegs m n = outputRegs m n := List.take_append_drop _ _

private theorem layout (m n : ℕ) :
    (∀ i ∈ leftRegs m n ++ rightRegs m n, IsDigit i) ∧
      (∀ i ∈ lowRegs m n ++ highRegs m n, IsDigit i) ∧
      (lowRegs m n ++ highRegs m n).Nodup ∧
      List.Disjoint (lowRegs m n ++ highRegs m n) (leftRegs m n ++ rightRegs m n) := by
  have hin (i : Fin (2 * (m + n) + 4)) (hi : i ∈ leftRegs m n ++ rightRegs m n) :
      4 ≤ i.val ∧ i.val < 4 + m + n := by
    rcases List.mem_append.mp hi with hi | hi
    · have := registers_bounds hi
      omega
    · have := registers_bounds hi
      omega
  have hout (i : Fin (2 * (m + n) + 4))
      (hi : i ∈ lowRegs m n ++ highRegs m n) :
      4 + m + n ≤ i.val := by
    rw [output_split] at hi
    have := registers_bounds hi
    omega
  refine ⟨fun i hi => (hin i hi).1, fun i hi => ?_, ?_, ?_⟩
  · exact le_trans (by omega) (hout i hi)
  · rw [output_split]
    exact nodup_registers _ _ _
  · apply List.disjoint_left.mpr
    intro i ho hi
    have := hin i hi
    have := hout i ho
    omega

/-- A concrete schoolbook program with `2 * (m + n) + 4` registers and no address words.
The code and register count depend only on the limb counts, not on the physical word width. -/
def fixedProgram (m n : ℕ) : Code .standard (2 * (m + n) + 4) :=
  program (leftRegs m n) (rightRegs m n) (lowRegs m n) (highRegs m n)

/-- Exact code size of the fixed-register schoolbook multiplication program. -/
theorem size_fixedProgram (m n : ℕ) :
    (fixedProgram m n).size = 7 + n + rowCost m n := by
  obtain ⟨hl, hr, hd, ho⟩ := lengths m n
  simpa only [fixedProgram, hl, hr] using size_program
    (leftRegs m n) (rightRegs m n) (lowRegs m n) (highRegs m n)
    (hr.trans hd.symm) (ho.trans hl.symm)

/-- Closed form of the exact instruction count, including setup and initialization. -/
theorem size_fixedProgram_eq (m n : ℕ) :
    (fixedProgram m n).size = 5 * (m * n + m * (m - 1) / 2) + 3 * m + n + 8 := by
  rw [size_fixedProgram, rowCost_eq]
  omega

/-- The same constant bounds every choice of operand lengths up to eighteen digits. -/
theorem size_fixedProgram_le {m n : ℕ} (hm : m ≤ 18) (hn : n ≤ 18) :
    (fixedProgram m n).size ≤ 2465 := by
  have hmn : m * n ≤ 324 := Nat.mul_le_mul hm hn
  have hpred : m * (m - 1) ≤ 306 := Nat.mul_le_mul hm (show m - 1 ≤ 17 by omega)
  have hhalf : m * (m - 1) / 2 ≤ 153 := by omega
  rw [size_fixedProgram_eq]
  omega

/-- The concrete fixed-register schoolbook program multiplies all bounded operands, including
zero-length operands, at every physical width at least two. The output has `m + n` bounded
digits, reconstructs the exact product, and preserves memory and both operands. -/
theorem exec_fixedProgram {w : ℕ} (hw : 2 ≤ w) (m n : ℕ)
    (x : Data (2 * (m + n) + 4))
    (ha : Bounded (radix w) x (leftRegs m n))
    (hb : Bounded (radix w) x (rightRegs m n)) :
    ∃ y, Exec w (fixedProgram m n) x y (7 + n + rowCost m n) ∧
      Bounded (radix w) y (outputRegs m n) ∧
      value (radix w) y (outputRegs m n) =
        value (radix w) x (leftRegs m n) * value (radix w) x (rightRegs m n) ∧
      y.mem = x.mem ∧ ∀ i ∈ leftRegs m n ++ rightRegs m n, y.regs i = x.regs i := by
  obtain ⟨hl, hr, hd, ho⟩ := lengths m n
  obtain ⟨hi, hout, hnd, hdis⟩ := layout m n
  simpa only [fixedProgram, output_split, hl, hr] using exec hw
    (leftRegs m n) (rightRegs m n) (lowRegs m n) (highRegs m n)
    (hr.trans hd.symm) (ho.trans hl.symm) hi hout hnd hdis x ha hb

/-- Eighteen digits per operand give a fixed 76-register, 2465-instruction program.
This accommodates six physical words per operand even at odd widths, including width three. -/
theorem exec_eighteen {w : ℕ} (hw : 2 ≤ w) (x : Data 76)
    (ha : Bounded (radix w) x (leftRegs 18 18))
    (hb : Bounded (radix w) x (rightRegs 18 18)) :
    ∃ y, Exec w (fixedProgram 18 18) x y 2465 ∧
      Bounded (radix w) y (outputRegs 18 18) ∧
      value (radix w) y (outputRegs 18 18) =
        value (radix w) x (leftRegs 18 18) * value (radix w) x (rightRegs 18 18) ∧
      y.mem = x.mem ∧ ∀ i ∈ leftRegs 18 18 ++ rightRegs 18 18, y.regs i = x.regs i :=
  exec_fixedProgram hw 18 18 x ha hb

/-- Encode two fixed digit tuples into the concrete layout, with zero workspace and memory.
This is an input encoding, not a RAM conversion routine. -/
def input (m n : ℕ) (a : Fin m → ℕ) (b : Fin n → ℕ) : Data (2 * (m + n) + 4) :=
  ⟨fun i =>
    if h : 4 ≤ i.val ∧ i.val < 4 + m then a ⟨i.val - 4, by omega⟩
    else if h : 4 + m ≤ i.val ∧ i.val < 4 + m + n then
      b ⟨i.val - (4 + m), by omega⟩
    else 0, fun _ => 0⟩

private theorem input_left (m n : ℕ) (a : Fin m → ℕ) (b : Fin n → ℕ) (i : Fin m) :
    (input m n a b).regs ⟨4 + i.val, by omega⟩ = a i := by
  simp [input, i.isLt]

private theorem input_right (m n : ℕ) (a : Fin m → ℕ) (b : Fin n → ℕ) (i : Fin n) :
    (input m n a b).regs ⟨4 + m + i.val, by omega⟩ = b i := by
  have hy : 4 + m ≤ 4 + m + i.val ∧ 4 + m + i.val < 4 + m + n := by omega
  simp [input, hy]

private theorem value_input_left (β m n : ℕ) (a : Fin m → ℕ) (b : Fin n → ℕ) :
    value β (input m n a b) (leftRegs m n) = Nat.ofDigits β (List.ofFn a) := by
  simp only [value, leftRegs, registers, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  exact input_left m n a b i

private theorem value_input_right (β m n : ℕ) (a : Fin m → ℕ) (b : Fin n → ℕ) :
    value β (input m n a b) (rightRegs m n) = Nat.ofDigits β (List.ofFn b) := by
  simp only [value, rightRegs, registers, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  exact input_right m n a b i

private theorem bounded_input_left {β : ℕ} (m n : ℕ) (a : Fin m → ℕ) (b : Fin n → ℕ)
    (ha : ∀ i, a i < β) : Bounded β (input m n a b) (leftRegs m n) := by
  intro j hj
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hj
  rw [input_left]
  exact ha i

private theorem bounded_input_right {β : ℕ} (m n : ℕ) (a : Fin m → ℕ) (b : Fin n → ℕ)
    (hb : ∀ i, b i < β) : Bounded β (input m n a b) (rightRegs m n) := by
  intro j hj
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hj
  rw [input_right]
  exact hb i

/-- Bounded digit tuples encode globally bounded RAM data. -/
private theorem input_bounded {w : ℕ} (hw : 2 ≤ w) (m n : ℕ) (a : Fin m → ℕ) (b : Fin n → ℕ)
    (ha : ∀ i, a i < radix w) (hb : ∀ i, b i < radix w) :
    (input m n a b).Bounded w := by
  refine ⟨fun i => ?_, fun _ => fits_zero _⟩
  dsimp [input]
  split
  · exact (ha _).trans (radix_fits hw)
  · split
    · exact (hb _).trans (radix_fits hw)
    · exact fits_zero _

/-- Any two values smaller than six physical words have a globally bounded digit encoding
on which the concrete checked program computes their full product in 2465 instructions.
The encoding is specified separately; the runtime starts with the encoded operands. -/
theorem six_word_product {w a b : ℕ} (hw : 2 ≤ w)
    (ha : a < 2 ^ (6 * w)) (hb : b < 2 ^ (6 * w)) :
    ∃ x y : Data 76, x.Bounded w ∧ y.Bounded w ∧
      Exec w (fixedProgram 18 18) x y 2465 ∧
      value (radix w) x (leftRegs 18 18) = a ∧
      value (radix w) x (rightRegs 18 18) = b ∧
      Bounded (radix w) y (outputRegs 18 18) ∧
      value (radix w) y (outputRegs 18 18) = a * b := by
  obtain ⟨as, has, hvalas⟩ := exists_six_word_digits hw ha
  obtain ⟨bs, hbs, hvalbs⟩ := exists_six_word_digits hw hb
  let x := input 18 18 as bs
  have hx := input_bounded hw 18 18 as bs has hbs
  obtain ⟨y, he, hyb, hyval, _⟩ := exec_eighteen hw x
    (bounded_input_left 18 18 as bs has) (bounded_input_right 18 18 as bs hbs)
  have hxa : value (radix w) x (leftRegs 18 18) = a :=
    (value_input_left _ _ _ _ _).trans hvalas
  have hxb : value (radix w) x (rightRegs 18 18) = b :=
    (value_input_right _ _ _ _ _).trans hvalbs
  exact ⟨x, y, hx, he.bounded hx, he, hxa, hxb, hyb, by rwa [hxa, hxb] at hyval⟩

end Cslib.WordRAM.Multiword.Schoolbook

end
