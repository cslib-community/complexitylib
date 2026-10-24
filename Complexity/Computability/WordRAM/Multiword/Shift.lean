/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Multiword.Workspace

/-!
# Checked multiword right shifts

Whole half-word digits are skipped by subtracting the half width from a physical scalar.
The remaining shift is division by a power of two, performed from high digits to low digits
with a remainder carry. Each intermediate is strictly below the square of the digit radix.

## Main definitions

* `Cslib.WordRAM.Multiword.Shift.cell`, `Cslib.WordRAM.Multiword.Shift.digits`,
  `Cslib.WordRAM.Multiword.Shift.finish`: single-digit division, high-to-low digit division, and
  residual power-of-two shift completion.
* `Cslib.WordRAM.Multiword.Shift.dispatch`, `Cslib.WordRAM.Multiword.Shift.codeSize`: whole-digit
  shift dispatch and its static instruction count.
* `Cslib.WordRAM.Multiword.Shift.program`: variable right shift with fixed register lists.

## Main results

* `Cslib.WordRAM.Multiword.Shift.exec`: bounded digits, exact reconstruction and a frame.
* `Cslib.WordRAM.Multiword.Shift.exec_eighteen`: the eighteen-digit bank interface.

The code may depend on the physical width through constants. Its size and runtime bounds
depend only on the digit counts. Inputs and outputs are disjoint little-endian digit lists;
the scalar is a separate physical word. All four reserved registers may change.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009].
-/

@[expose] public section

namespace Cslib.WordRAM.Multiword.Shift

open Workspace

variable {r : ℕ}

private theorem value_frame {β : ℕ} {x y : Data (r + 4)}
    {ds as : List (Fin (r + 4))} (hf : Frame x y ds)
    (ha : ∀ i ∈ as, i ∉ ds ∧ IsDigit i) : value β y as = value β x as := by
  unfold value
  congr 1
  exact List.map_congr_left fun i hi =>
    hf.2 i (ha i hi).1 (digit_ne (ha i hi).2).1 (digit_ne (ha i hi).2).2.1

/-- One division digit. `base` is the radix, `zero` the divisor, and `total` the shift. -/
def cell (a d : Fin (r + 4)) : Code .standard (r + 4) := ram[
  carry ← carry * base;
  carry ← carry + a;
  d ← carry >>> total;
  carry ← carry % zero ]

/-- Full result of a division digit, including the remainder workspace. -/
private def cellResult (x : Data (r + 4)) (a d : Fin (r + 4)) : Data (r + 4) :=
  let t := x.regs carry * x.regs base + x.regs a
  ((x.set carry t).set d (t >>> x.regs total)).set carry (t % x.regs zero)

private theorem exec_cell {w : ℕ} (_hw : 2 ≤ w) (x : Data (r + 4))
    (a d : Fin (r + 4)) (ha : IsDigit a) (hd : IsDigit d)
    (hb : x.regs base = radix w) (hz : x.regs zero = 2 ^ x.regs total)
    (hs : x.regs total < w / 2) (had : x.regs a < radix w)
    (hc : x.regs carry < 2 ^ x.regs total) :
    Exec w (cell a d) x (cellResult x a d) 4 ∧
      (cellResult x a d).regs d < radix w ∧
      (cellResult x a d).regs carry < 2 ^ x.regs total ∧
      (cellResult x a d).regs d * 2 ^ x.regs total +
        (cellResult x a d).regs carry = x.regs carry * radix w + x.regs a ∧
      (cellResult x a d).regs total = x.regs total ∧ Frame x (cellResult x a d) [d] := by
  obtain ⟨hat, hac, hab, haz⟩ := digit_ne ha
  obtain ⟨hdt, hdc, hdb, hdz⟩ := digit_ne hd
  have hp : 0 < 2 ^ x.regs total := Nat.two_pow_pos _
  have hple : 2 ^ x.regs total ≤ radix w :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hlt : x.regs carry * radix w + x.regs a < radix w * 2 ^ x.regs total := by
    nlinarith
  have hf : Fits w (x.regs carry * radix w + x.regs a) := by
    have hsq := radix_sq_le w
    unfold Fits
    nlinarith
  have hm := hf.of_le (show x.regs carry * radix w ≤
    x.regs carry * radix w + x.regs a by omega)
  have hq : Fits w ((x.regs carry * radix w + x.regs a) >>> x.regs total) := by
    rw [Nat.shiftRight_eq_div_pow]
    exact hf.of_le (Nat.div_le_self _ _)
  have hr := hf.of_le (Nat.mod_le (x.regs carry * radix w + x.regs a) (2 ^ x.regs total))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ram_eval [cell, cellResult, hat, hac, hdt, hdc, hdb, hdz, Ne.symm hdc, Ne.symm hdz, hb, hz,
      total, carry, base, zero, Fin.mk.injEq, hf, hm, hq, hr]
    simp only [Data.set, Function.update_idem]
  · simp only [cellResult, Data.set_regs, Function.update_apply, hdc, ↓reduceIte,
      hb, Nat.shiftRight_eq_div_pow]
    exact (Nat.div_lt_iff_lt_mul hp).mpr hlt
  · simpa only [cellResult, Data.set_regs, Function.update_self, hb, hz] using
      Nat.mod_lt (x.regs carry * radix w + x.regs a) hp
  · simpa only [cellResult, Data.set_regs, Function.update_apply, hdc, ↓reduceIte,
      hb, hz, Nat.shiftRight_eq_div_pow, Nat.mul_comm, Nat.add_comm] using
      Nat.mod_add_div (x.regs carry * radix w + x.regs a) (2 ^ x.regs total)
  · simp only [cellResult, Data.set_regs, Function.update_apply, Ne.symm hdt,
      show (total : Fin (r + 4)) ≠ carry by simp [total, carry], ↓reduceIte]
  · refine ⟨rfl, ?_⟩
    intro i hi ht hic
    simp only [List.mem_singleton] at hi
    simp only [cellResult, Data.set_regs, Function.update_apply, hi, hic, ↓reduceIte]

/-- Divide from high to low, padding the high output digits with zeros. -/
def digits : List (Fin (r + 4)) → List (Fin (r + 4)) → Code .standard (r + 4)
  | a :: as, d :: ds => .seq (digits as ds) (cell a d)
  | [], d :: ds => .seq (digits [] ds) (.op (.const d 0))
  | _, [] => .op (.const carry 0)

/-- The static instruction size of `digits as ds` when `as.length ≤ ds.length`. -/
theorem size_digits (as ds : List (Fin (r + 4))) (hlen : as.length ≤ ds.length) :
    (digits as ds).size = ds.length + 3 * as.length + 1 := by
  induction ds generalizing as with
  | nil => cases as <;> simp_all [digits]
  | cons d ds ih =>
    cases as with
    | nil => simp only [digits, Code.size, ih [] (by simp), List.length_nil,
        List.length_cons]
    | cons a as => simp only [digits, Code.size, cell,
        ih as (by simpa using hlen), List.length_cons]; omega

private theorem exec_digits {w : ℕ} (hw : 2 ≤ w)
    (as ds : List (Fin (r + 4))) (hlen : as.length ≤ ds.length)
    (hin : ∀ i ∈ as, IsDigit i) (hout : ∀ i ∈ ds, IsDigit i)
    (hnd : ds.Nodup) (hdis : List.Disjoint ds as)
    (x : Data (r + 4)) (hb : x.regs base = radix w)
    (hz : x.regs zero = 2 ^ x.regs total) (hs : x.regs total < w / 2)
    (ha : Bounded (radix w) x as) :
    ∃ y, Exec w (digits as ds) x y (ds.length + 3 * as.length + 1) ∧
      Bounded (radix w) y ds ∧ y.regs carry < 2 ^ x.regs total ∧
      value (radix w) y ds * 2 ^ x.regs total + y.regs carry =
        value (radix w) x as ∧ y.regs total = x.regs total ∧ Frame x y ds := by
  induction ds generalizing as x with
  | nil =>
    cases as with
    | cons => simp_all
    | nil =>
      refine ⟨x.set carry 0, ?_, by simp [Bounded], ?_, ?_, ?_, ?_⟩
      · ram_eval [digits]
      · simp only [Data.set_regs, Function.update_self]; exact Nat.two_pow_pos _
      · simp [value]
      · simp [total, carry]
      · exact ⟨rfl, fun i _ _ hc => by
          simp only [Data.set_regs, Function.update_apply, hc, ↓reduceIte]⟩
  | cons d ds ih =>
    have hd := digit_ne (hout d (by simp))
    have hds : ∀ i ∈ ds, IsDigit i := fun i hi => hout i (by simp [hi])
    have hnd' := (List.nodup_cons.mp hnd).2
    have hdnot := (List.nodup_cons.mp hnd).1
    cases as with
    | nil =>
      obtain ⟨z, he, hzb, hzc, hzv, hzt, hzf⟩ := ih [] (by simp)
        (by simp) hds hnd' (by simp) x hb hz hs (by simp [Bounded])
      let y := z.set d 0
      have hyf : Frame z y [d] := ⟨rfl, fun i hi _ _ => by
        simp only [List.mem_singleton] at hi; simp [y, hi]⟩
      have hyv : value (radix w) y ds = value (radix w) z ds :=
        value_frame hyf (fun i hi => ⟨by
          simp only [List.mem_singleton]; rintro rfl; exact hdnot hi, hds i hi⟩)
      refine ⟨y, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [digits, List.length_cons, List.length_nil, Nat.mul_zero,
          Nat.add_zero, Nat.add_assoc] using he.seq (Exec.const (d := d) (fits_zero w))
      · intro i hi
        rcases List.mem_cons.mp hi with rfl | hi
        · simp only [y, Data.set_regs, Function.update_self]
          exact lt_trans (by decide) (one_lt_radix hw)
        · have hid : i ≠ d := fun heq => hdnot (heq ▸ hi)
          rw [hyf.2 i (by simpa only [List.mem_singleton] using hid)
            (digit_ne (hds i hi)).1 (digit_ne (hds i hi)).2.1]
          exact hzb i hi
      · simpa only [y, Data.set_regs, Function.update_apply, Ne.symm hd.2.1,
          ↓reduceIte] using hzc
      · change (y.regs d + radix w * value (radix w) y ds) * _ + _ = _
        rw [hyv]
        simp only [y, Data.set_regs, Function.update_self, Function.update_apply,
          Ne.symm hd.2.1, ↓reduceIte, zero_add]
        simp only [value, List.map_nil, Nat.ofDigits_nil] at hzv ⊢
        have hv0 : Nat.ofDigits (radix w) (List.map z.regs ds) * 2 ^ x.regs total = 0 := by omega
        have hc0 : z.regs carry = 0 := by omega
        rw [mul_assoc, hv0, mul_zero, hc0, zero_add]
      · simpa only [y, Data.set_regs, Function.update_apply, Ne.symm hd.1,
          ↓reduceIte] using hzt
      · exact frame_trans (frame_mono hzf (by simp)) (frame_mono hyf (by simp))
    | cons a as =>
      have hat := digit_ne (hin a (by simp))
      have hdis' : List.Disjoint ds as := List.disjoint_left.mpr fun i hi hj =>
        List.disjoint_left.mp hdis (List.mem_cons_of_mem d hi) (List.mem_cons_of_mem a hj)
      obtain ⟨z, he, hzb, hzc, hzv, hzt, hzf⟩ := ih as (by simpa using hlen)
        (fun i hi => hin i (by simp [hi])) hds hnd' hdis' x hb hz hs
        (fun i hi => ha i (by simp [hi]))
      have hza : z.regs a = x.regs a := hzf.2 a
        (fun hi => List.disjoint_left.mp hdis (List.mem_cons_of_mem d hi)
          List.mem_cons_self) hat.1 hat.2.1
      have hbase : z.regs base = radix w := by
        rw [hzf.2 base (fun hi => (digit_ne (hds base hi)).2.2.1 rfl)
          (by simp [base, total]) (by simp [base, carry])]; exact hb
      have hzero : z.regs zero = 2 ^ z.regs total := by
        rw [hzf.2 zero (fun hi => (digit_ne (hds zero hi)).2.2.2 rfl)
          (by simp [zero, total]) (by simp [zero, carry]), hzt]; exact hz
      obtain ⟨hec, hyb, hyc, hyv, hyt, hyf⟩ := exec_cell hw z a d
        (hin a (by simp)) (hout d (by simp)) hbase hzero (by rwa [hzt])
        (by rw [hza]; exact ha a (by simp)) (by rwa [hzt])
      let y := cellResult z a d
      have hyval : value (radix w) y ds = value (radix w) z ds :=
        value_frame hyf (fun i hi => ⟨by
          simp only [List.mem_singleton]; rintro rfl; exact hdnot hi, hds i hi⟩)
      refine ⟨y, ?_, ?_, ?_, ?_, hyt.trans hzt, ?_⟩
      · simp only [digits, List.length_cons]
        convert he.seq hec using 1; omega
      · intro i hi
        rcases List.mem_cons.mp hi with rfl | hi
        · exact hyb
        · have hid : i ≠ d := fun heq => hdnot (heq ▸ hi)
          rw [hyf.2 i (by simpa only [List.mem_singleton] using hid)
            (digit_ne (hds i hi)).1 (digit_ne (hds i hi)).2.1]
          exact hzb i hi
      · rwa [hzt] at hyc
      · change (y.regs d + radix w * value (radix w) y ds) * _ + _ =
          x.regs a + radix w * value (radix w) x as
        rw [hzt, hza] at hyv
        rw [hyval]
        nlinarith [congrArg (radix w * ·) hzv]
      · exact frame_trans (frame_mono hzf (by simp)) (frame_mono hyf (by simp))

/-- Set up the residual power-of-two divisor and divide the remaining digits. -/
def finish (as ds : List (Fin (r + 4))) : Code .standard (r + 4) :=
  .seq (ram[ zero ← #1; zero ← zero <<< total ]) (digits as ds)

private theorem exec_finish {w : ℕ} (hw : 2 ≤ w)
    (as ds : List (Fin (r + 4))) (hlen : as.length ≤ ds.length)
    (hin : ∀ i ∈ as, IsDigit i) (hout : ∀ i ∈ ds, IsDigit i)
    (hnd : ds.Nodup) (hdis : List.Disjoint ds as)
    (x : Data (r + 4)) (hb : x.regs base = radix w)
    (hs : x.regs total < w / 2) (ha : Bounded (radix w) x as) :
    ∃ y, Exec w (finish as ds) x y (ds.length + 3 * as.length + 3) ∧
      Bounded (radix w) y ds ∧
      value (radix w) y ds = value (radix w) x as >>> x.regs total ∧
      Frame x y (zero :: ds) := by
  let z := (x.set zero 1).set zero (2 ^ x.regs total)
  have h1 := fits_one (w := w) (by omega)
  have hpow : Fits w (2 ^ x.regs total) :=
    (radix_fits hw).of_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hshift : 1 <<< x.regs total = 2 ^ x.regs total := by
    rw [Nat.shiftLeft_eq, one_mul]
  have hez : Exec w (ram[ zero ← #1; zero ← zero <<< total ]) x z 2 := by
    ram_eval [z, zero, total, Fin.mk.injEq, h1, hpow, hshift]
  have hzf : Frame x z [zero] := ⟨rfl, fun i hi _ _ => by
    simp only [List.mem_singleton] at hi
    simp only [z, Data.set_regs, Function.update_apply, hi, ↓reduceIte]⟩
  have hzt : z.regs total = x.regs total := by simp [z, total, zero]
  have hzb : z.regs base = radix w := by simpa [z, base, zero] using hb
  have hza (i : Fin (r + 4)) (hi : i ∈ as) : z.regs i = x.regs i :=
    hzf.2 i (by simpa only [List.mem_singleton] using (digit_ne (hin i hi)).2.2.2)
      (digit_ne (hin i hi)).1 (digit_ne (hin i hi)).2.1
  obtain ⟨y, he, hyb, hyc, hyv, _, hyf⟩ := exec_digits hw as ds hlen hin hout hnd hdis
    z hzb (by simp [z]) (by rwa [hzt])
    (fun i hi => by rw [hza i hi]; exact ha i hi)
  have hzv : value (radix w) z as = value (radix w) x as :=
    value_frame hzf (fun i hi => ⟨by
      simpa only [List.mem_singleton] using (digit_ne (hin i hi)).2.2.2, hin i hi⟩)
  rw [hzt, hzv] at hyv
  rw [hzt] at hyc
  refine ⟨y, ?_, hyb, ?_, ?_⟩
  · unfold finish
    convert hez.seq he using 1; omega
  · rw [Nat.shiftRight_eq_div_pow]
    exact (Nat.div_eq_of_lt_le (by omega) (by nlinarith)).symm
  · exact frame_trans (frame_mono hzf (by simp)) (frame_mono hyf (by simp))

/-- Branch through the possible whole-digit shifts. Exhausting the input clears the output. -/
def dispatch : List (Fin (r + 4)) → List (Fin (r + 4)) → Code .standard (r + 4)
  | [], ds => .seq (.op (.const total 0)) (finish [] ds)
  | a :: as, ds => .branch (.lt total zero) (finish (a :: as) ds)
      (.seq (.op (.bin .sub total total zero)) (dispatch as ds))

/-- Exact instruction-list size before the three-instruction initialization. -/
def codeSize : ℕ → ℕ → ℕ
  | 0, n => n + 4
  | m + 1, n => codeSize m n + n + 3 * (m + 1) + 6

/-- The static instruction size of `dispatch as ds` equals `codeSize as.length ds.length`. -/
theorem size_dispatch (as ds : List (Fin (r + 4))) (hlen : as.length ≤ ds.length) :
    (dispatch as ds).size = codeSize as.length ds.length := by
  induction as with
  | nil => simp only [dispatch, Code.size, finish, size_digits [] ds (by simp),
      List.length_nil, codeSize]; omega
  | cons a as ih =>
    have hlen' : as.length ≤ ds.length := by simp only [List.length_cons] at hlen; omega
    simp only [dispatch, Code.size, finish, size_digits _ _ hlen,
      ih hlen', List.length_cons, codeSize]
    omega

private theorem exec_dispatch {w : ℕ} (hw : 2 ≤ w)
    (as ds : List (Fin (r + 4))) (hlen : as.length ≤ ds.length)
    (hin : ∀ i ∈ as, IsDigit i) (hout : ∀ i ∈ ds, IsDigit i)
    (hnd : ds.Nodup) (hdis : List.Disjoint ds as)
    (x : Data (r + 4)) (hb : x.regs base = radix w) (hz : x.regs zero = w / 2)
    (hs : Fits w (x.regs total)) (ha : Bounded (radix w) x as) :
    ∃ y, ExecWithin w (dispatch as ds) x y (ds.length + 3 * as.length + 4) ∧
      Bounded (radix w) y ds ∧
      value (radix w) y ds = value (radix w) x as >>> x.regs total ∧
      Frame x y (base :: zero :: ds) := by
  induction as generalizing x with
  | nil =>
    let z := x.set total 0
    obtain ⟨y, he, hyb, hyv, hyf⟩ := exec_finish hw [] ds (by simp) (by simp) hout hnd
      (by simp) z (by simpa [z, base, total] using hb) (by simp [z]; omega)
      (by simp [Bounded])
    refine ⟨y, ?_, hyb, ?_, ?_⟩
    · simp only [dispatch, List.length_nil, Nat.mul_zero, Nat.add_zero]
      convert (Exec.const (d := total) (x := x) (B := .standard)
        (fits_zero w)).within.seq he.within using 1
      simp only [List.length_nil]; omega
    · simpa [value] using hyv
    · exact frame_trans
        (show Frame x z (base :: zero :: ds) from ⟨rfl, fun i _ ht _ => by
          simp only [z, Data.set_regs, Function.update_apply, ht, ↓reduceIte]⟩)
        (frame_mono hyf (by simp))
  | cons a as ih =>
    have hlen' : as.length ≤ ds.length := by simp only [List.length_cons] at hlen; omega
    have hin' : ∀ i ∈ as, IsDigit i := fun i hi => hin i (by simp [hi])
    have hdis' : List.Disjoint ds as := List.disjoint_left.mpr fun i hi hj =>
      List.disjoint_left.mp hdis hi (List.mem_cons_of_mem a hj)
    by_cases hsmall : x.regs total < w / 2
    · obtain ⟨y, he, hyb, hyv, hyf⟩ :=
        exec_finish hw (a :: as) ds hlen hin hout hnd hdis x hb hsmall ha
      refine ⟨y, ?_, hyb, hyv, frame_mono hyf (by simp)⟩
      simpa only [dispatch] using he.within.branch_pos
        (show (Cond.lt total zero).Holds x by simpa [Cond.Holds, hz] using hsmall)
    · let z := x.set total (x.regs total - w / 2)
      have hez : Exec w (.op (.bin .sub total total zero)) x z 1 := by
        have hf := hs.of_le (Nat.sub_le (x.regs total) (w / 2))
        ram_eval [z, hz, hf]
      have hzf : Frame x z (base :: zero :: ds) := ⟨rfl, fun i _ ht _ => by
        simp only [z, Data.set_regs, Function.update_apply, ht, ↓reduceIte]⟩
      have hza (i : Fin (r + 4)) (hi : i ∈ as) : z.regs i = x.regs i := by
        simp only [z, Data.set_regs, Function.update_apply, (digit_ne (hin' i hi)).1,
          ↓reduceIte]
      obtain ⟨y, he, hyb, hyv, hyf⟩ := ih hlen' hin' hdis' z
        (by simpa [z, base, total] using hb) (by simpa [z, zero, total] using hz)
        (by simpa [z] using hs.of_le (Nat.sub_le (x.regs total) (w / 2)))
        (fun i hi => by rw [hza i hi]; exact ha i (by simp [hi]))
      have hzv : value (radix w) z as = value (radix w) x as := by
        unfold value
        congr 1
        exact List.map_congr_left hza
      have hdrop : value (radix w) x (a :: as) >>> (w / 2) = value (radix w) x as := by
        rw [Nat.shiftRight_eq_div_pow]
        change (x.regs a + radix w * value (radix w) x as) / radix w = _
        rw [Nat.add_mul_div_left _ _ (by have := one_lt_radix hw; omega),
          Nat.div_eq_of_lt (ha a (by simp)), zero_add]
      refine ⟨y, ?_, hyb, ?_, frame_trans hzf hyf⟩
      · have hbranch := (hez.within.seq he).branch_neg (pos := finish (a :: as) ds)
          (show ¬(Cond.lt total zero).Holds x by simpa [Cond.Holds, hz] using hsmall)
        simp only [dispatch]
        convert hbranch using 1
        simp only [List.length_cons]; omega
      · rw [show x.regs total = w / 2 + (x.regs total - w / 2) by omega,
          Nat.shiftRight_add, hdrop]
        simpa only [z, Data.set_regs, Function.update_self, hzv] using hyv

/-- Initialize the radix, half width and scalar shift, then execute checked division. -/
def program (w : ℕ) (as ds : List (Fin (r + 4))) (s : Fin (r + 4)) :
    Code .standard (r + 4) :=
  .seq (ram[ base ← #(radix w); zero ← #(w / 2); total ← s ]) (dispatch as ds)

/-- The static instruction size of `program w as ds s` is `3 + codeSize as.length ds.length`. -/
theorem size_program (w : ℕ) (as ds : List (Fin (r + 4))) (s : Fin (r + 4))
    (hlen : as.length ≤ ds.length) :
    (program w as ds s).size = 3 + codeSize as.length ds.length := by
  simp [program, size_dispatch as ds hlen]

/-- Variable right shift from a physical scalar word. The output is padded to its fixed length.
All arithmetic, including construction of the residual power of two, is checked at width `w`.
The frame preserves memory and every register outside the output and reserved workspace. -/
theorem exec {w : ℕ} (hw : 2 ≤ w)
    (as ds : List (Fin (r + 4))) (s : Fin (r + 4)) (hlen : as.length ≤ ds.length)
    (hin : ∀ i ∈ as, IsDigit i) (hout : ∀ i ∈ ds, IsDigit i) (hsdigit : IsDigit s)
    (hnd : ds.Nodup) (hdis : List.Disjoint ds as) (hsout : s ∉ ds)
    (x : Data (r + 4)) (ha : Bounded (radix w) x as) (hs : Fits w (x.regs s)) :
    ∃ y, ExecWithin w (program w as ds s) x y (ds.length + 3 * as.length + 7) ∧
      Bounded (radix w) y ds ∧
      value (radix w) y ds = value (radix w) x as >>> x.regs s ∧
      Frame x y (base :: zero :: ds) ∧ y.regs s = x.regs s := by
  let z := ((x.set base (radix w)).set zero (w / 2)).set total (x.regs s)
  obtain ⟨hst, hsc, hsb, hsz⟩ := digit_ne hsdigit
  have hez : Exec (B := .standard) w
      (ram[ base ← #(radix w); zero ← #(w / 2); total ← s ]) x z 3 := by
    have hhalf := (fits_self w).of_le (Nat.div_le_self w 2)
    have hβ := radix_fits hw
    ram_eval [z, hsb, hsz, hhalf, hβ, base, zero, total, Fin.mk.injEq]
  have hzf : Frame x z (base :: zero :: ds) := ⟨rfl, fun i hi ht _ => by
    have hb : i ≠ base := fun h => hi (by simp [h])
    have hz : i ≠ zero := fun h => hi (by simp [h])
    simp only [z, Data.set_regs, Function.update_apply, ht, hb, hz, ↓reduceIte]⟩
  have hzi (i : Fin (r + 4)) (hi : IsDigit i) : z.regs i = x.regs i := by
    obtain ⟨ht, _, hb, hz⟩ := digit_ne hi
    simp only [z, Data.set_regs, Function.update_apply, ht, hb, hz, ↓reduceIte]
  obtain ⟨y, he, hyb, hyv, hyf⟩ := exec_dispatch hw as ds hlen hin hout hnd hdis z
    (by simp [z, base, total, zero]) (by simp [z, zero, total]) (by simpa [z] using hs)
    (fun i hi => by rw [hzi i (hin i hi)]; exact ha i hi)
  have hzv : value (radix w) z as = value (radix w) x as := by
    unfold value
    congr 1
    exact List.map_congr_left fun i hi => hzi i (hin i hi)
  have hf := frame_trans hzf hyf
  refine ⟨y, ?_, hyb, ?_, hf, ?_⟩
  · unfold program
    convert hez.within.seq he using 1; omega
  · simpa only [z, Data.set_regs, Function.update_self, hzv] using hyv
  · exact hf.2 s (by simp [hsb, hsz, hsout]) hst hsc

/-- Extract the outside-output register guarantee from the complete four-register frame. -/
private theorem regs_eq_of_frame {x y : Data (r + 4)} {ds : List (Fin (r + 4))}
    (hf : Frame x y (base :: zero :: ds)) {i : Fin (r + 4)}
    (hi : IsDigit i) (hnot : i ∉ ds) : y.regs i = x.regs i := by
  obtain ⟨ht, hc, hb, hz⟩ := digit_ne hi
  exact hf.2 i (by simp only [List.mem_cons, not_or]; exact ⟨hb, hz, hnot⟩) ht hc

/-- A shift beyond the full digit capacity is zero. Combined with `exec`, this also describes
the runtime's large-shift branch, without requiring its scalar to fit the digit radix. -/
theorem shiftRight_eq_zero {w s : ℕ} (hw : 2 ≤ w) (x : Data (r + 4))
    (as : List (Fin (r + 4))) (ha : Bounded (radix w) x as)
    (hs : (w / 2) * as.length ≤ s) : value (radix w) x as >>> s = 0 := by
  have hv : value (radix w) x as < radix w ^ as.length := by
    unfold value
    have hd : ∀ d ∈ as.map x.regs, d < radix w := by
      intro d hd
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hd
      exact ha i hi
    simpa only [List.length_map] using Nat.ofDigits_lt_base_pow_length (one_lt_radix hw) hd
  rw [radix, ← pow_mul] at hv
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_eq_of_lt (hv.trans_le (Nat.pow_le_pow_right (by decide) hs))

/-- A quadratic instruction-list bound, independent of the physical word width. -/
theorem codeSize_le (m n : ℕ) : codeSize m n ≤ (m + 1) * (n + 3 * m + 6) := by
  induction m with
  | zero => simp [codeSize]
  | succ m ih => simp only [codeSize]; nlinarith

/-- Eighteen input and output digits have exactly 970 compiled instructions. -/
theorem size_program_eighteen (w : ℕ) (as ds : List (Fin (r + 4))) (s : Fin (r + 4))
    (has : as.length = 18) (hds : ds.length = 18) :
    (program w as ds s).size = 970 := by
  rw [size_program w as ds s (by omega), has, hds]
  decide

/-- The MSB bank's eighteen-digit shift takes at most 79 instructions, including initialization.
Every non-output register numbered at least four is preserved, including the scalar. -/
theorem exec_eighteen {w : ℕ} (hw : 2 ≤ w)
    (as ds : List (Fin (r + 4))) (s : Fin (r + 4))
    (has : as.length = 18) (hds : ds.length = 18)
    (hin : ∀ i ∈ as, IsDigit i) (hout : ∀ i ∈ ds, IsDigit i) (hsdigit : IsDigit s)
    (hnd : ds.Nodup) (hdis : List.Disjoint ds as) (hsout : s ∉ ds)
    (x : Data (r + 4)) (ha : Bounded (radix w) x as) (hs : Fits w (x.regs s)) :
    ∃ y, ExecWithin w (program w as ds s) x y 79 ∧
      Bounded (radix w) y ds ∧
      value (radix w) y ds = value (radix w) x as >>> x.regs s ∧
      Frame x y (base :: zero :: ds) ∧
      (∀ i, IsDigit i → i ∉ ds → y.regs i = x.regs i) := by
  obtain ⟨y, he, hyb, hyv, hyf, _⟩ := exec hw as ds s (by omega) hin hout hsdigit
    hnd hdis hsout x ha hs
  exact ⟨y, by simpa only [has, hds] using he, hyb, hyv, hyf,
    fun _ hi hnot => regs_eq_of_frame hyf hi hnot⟩

end Cslib.WordRAM.Multiword.Shift

end
