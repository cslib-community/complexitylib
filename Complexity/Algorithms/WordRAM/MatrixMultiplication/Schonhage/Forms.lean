/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Encoding
public import Complexity.Foundations.Algebra.FiniteMagnitude
import Mathlib.Tactic.Ring

/-!
# Native execution of the encoding forms

The form code reads seven strided entries and uses only the existing native signed arithmetic
blocks. These results account for those blocks' actual instructions and their scratch registers.

## Main results

* `Encoding.exec_summand`: a coefficient in `{0, 1, -1}` takes at most 23 instructions.

## References

The linear forms are from [AlmanWilliams2026, Section 2.4.1]; see `Encoding` for provenance.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Encoding

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- Registers outside the signed workspace and the form's three local registers. -/
def FormFrame (x y : Data 32) : Prop :=
  y.mem = x.mem ∧ ∀ i, 9 ≤ i.val → i ≠ address → i ≠ accumulator → i ≠ temporary →
    y.regs i = x.regs i

/-- Form frames compose without changing any memory cell. -/
theorem FormFrame.trans {x y z : Data 32} (hxy : FormFrame x y) (hyz : FormFrame y z) :
    FormFrame x z :=
  ⟨hyz.1.trans hxy.1, fun i hi ha hc ht =>
    (hyz.2 i hi ha hc ht).trans (hxy.2 i hi ha hc ht)⟩

private theorem fits_of_abs_lt {w : ℕ} (hw : 0 < w) {a : ℤ}
    (ha : |a| < (2 : ℤ) ^ (w - 1)) : GenericRAM.Signed.Fits w a := by
  have h := abs_lt.mp ha
  exact ⟨hw, h.1.le, h.2⟩

/-- A single coefficient is executed by real loads and signed arithmetic. The seven address
computations fit whenever the one-past-end address fits. The two operands must fit the signed
source range; the sum itself may use the two extra target bits supplied by the arithmetic block. -/
theorem exec_summand {w : ℕ} (x : Data 32) (s : Fin 7) (c a v : ℤ) (base n : ℕ)
    (hc : c = 0 ∨ c = 1 ∨ c = -1)
    (hacc : x.regs accumulator = encode a) (hbase : x.regs group = base)
    (hn : x.regs stride = n) (hmem : x.mem (base + s.val * n) = encode v)
    (ha : GenericRAM.Signed.Fits w a) (hv : GenericRAM.Signed.Fits w v)
    (haddr : Fits (w + 2) (base + 7 * n)) (hseven : Fits (w + 2) 7) :
    ∃ y, ExecWithin (w + 2) (summand s c) x y 23 ∧
      y.regs accumulator = encode (a + c * v) ∧ FormFrame x y := by
  rcases hc with rfl | rfl | rfl
  · refine ⟨x.set accumulator (x.regs accumulator), (ExecWithin.copy).mono (by decide), ?_, ?_⟩
    · simp [hacc]
    · refine ⟨rfl, ?_⟩
      intro i _ _ hi _
      simp only [Data.set_regs, Function.update_of_ne hi]
  all_goals
    have hs : Fits (w + 2) s.val := hseven.of_le (by omega)
    have hmul : Fits (w + 2) (s.val * n) := haddr.of_le (by nlinarith [s.isLt])
    have hsum : Fits (w + 2) (base + s.val * n) := haddr.of_le (by nlinarith [s.isLt])
    let z := ((((x.set temporary s.val).set address (s.val * n)).set address
      (base + s.val * n)).set right (encode v)).set left (encode a)
    have hz : ExecWithin (w + 2)
        (ram[ temporary ← #s.val; address ← temporary * stride;
          address ← group + address; right ← *address; left ← accumulator ]) x z 5 := by
      ram_eval [z, hs, hmul, hsum, hn, hbase, hacc, hmem,
        temporary, address, group, stride, right, left, accumulator, Fin.mk.injEq]
    have hza : z.regs left = encode a := by simp [z]
    have hzv : z.regs right = encode v := by
      simp [z, left, right]
    have hzframe : FormFrame x z := by
      refine ⟨rfl, ?_⟩
      intro i hi hia hic hit
      have hil : i ≠ left := by intro h; subst i; simp at hi
      have hir : i ≠ right := by intro h; subst i; simp at hi
      simp only [z, Data.set_regs, Function.update_of_ne hil, Function.update_of_ne hir,
        Function.update_of_ne hia, Function.update_of_ne hit]
  · obtain ⟨y, he, hyr, hym, hyreg⟩ := exec_add ha hv z hza hzv
    refine ⟨y.set accumulator (y.regs result), ?_, ?_, ?_⟩
    · simpa only [summand, show ¬(1 : ℤ) = 0 by decide, ↓reduceIte] using
        (hz.seq (he.seq (ExecWithin.copy (d := accumulator) (s := result)))).mono
          (by decide : 5 + (15 + 1) ≤ 23)
    · simp [GenericRAM.Signed.Arithmetic.eval, hyr]
    · refine ⟨hym.trans hzframe.1, ?_⟩
      intro i hi hia hic hit
      simpa only [Data.set_regs, Function.update_of_ne hic] using
        (hyreg i (Or.inr hi)).trans (hzframe.2 i hi hia hic hit)
  · obtain ⟨y, he, hyr, hym, hyreg⟩ := exec_subtract ha hv z hza hzv
    refine ⟨y.set accumulator (y.regs result), ?_, ?_, ?_⟩
    · simpa only [summand, show ¬(-1 : ℤ) = 0 by decide,
        show ¬(-1 : ℤ) = 1 by decide, ↓reduceIte] using
        (hz.seq (he.seq (ExecWithin.copy (d := accumulator) (s := result)))).mono
          (by decide : 5 + (17 + 1) ≤ 23)
    · simp [GenericRAM.Signed.Arithmetic.eval, hyr, sub_eq_add_neg]
    · refine ⟨hym.trans hzframe.1, ?_⟩
      intro i hi hia hic hit
      simpa only [Data.set_regs, Function.update_of_ne hic] using
        (hyreg i (Or.inr hi)).trans (hzframe.2 i hi hia hic hit)

/-- Execute any finite list of the fixed digit/coefficients. Partial sums are bounded by
`|a| + length * B`; the theorem derives each arithmetic operand's fit from that inequality. -/
theorem exec_sumCode {w : ℕ} (hw : 0 < w) (pairs : List (Fin 7 × ℤ))
    (x : Data 32) (a B : ℤ) (base n : ℕ) (v : Fin 7 → ℤ)
    (hc : ∀ sc ∈ pairs, sc.2 = 0 ∨ sc.2 = 1 ∨ sc.2 = -1)
    (hacc : x.regs accumulator = encode a) (hbase : x.regs group = base)
    (hn : x.regs stride = n) (hmem : ∀ s, x.mem (base + s.val * n) = encode (v s))
    (hB : 0 ≤ B) (hv : ∀ s, |v s| ≤ B) (hfitB : B < (2 : ℤ) ^ (w - 1))
    (hfit : |a| + pairs.length * B < (2 : ℤ) ^ (w - 1))
    (haddr : Fits (w + 2) (base + 7 * n)) (hseven : Fits (w + 2) 7) :
    ∃ y, ExecWithin (w + 2) (sumCode pairs) x y (23 * pairs.length + 1) ∧
      y.regs accumulator = encode (a + (pairs.map fun sc => sc.2 * v sc.1).sum) ∧
      FormFrame x y := by
  induction pairs generalizing x a with
  | nil =>
    refine ⟨x.set accumulator (x.regs accumulator), ExecWithin.copy, ?_, ?_⟩
    · simpa using hacc
    · refine ⟨rfl, ?_⟩
      intro i _ _ hi _
      simp only [Data.set_regs, Function.update_of_ne hi]
  | cons sc rest ih =>
    obtain ⟨s, c⟩ := sc
    have hc0 := hc (s, c) (by simp)
    have hcv : |c * v s| ≤ B := by
      rcases hc0 with rfl | rfl | rfl
      · simpa using hB
      · simpa using hv s
      · simpa using hv s
    have ha : GenericRAM.Signed.Fits w a :=
      fits_of_abs_lt hw (by have := abs_nonneg a; simp only [List.length_cons,
        Nat.cast_add, Nat.cast_one] at hfit; nlinarith [Nat.cast_nonneg (α := ℤ) rest.length])
    have hvs := fits_of_abs_lt hw ((hv s).trans_lt hfitB)
    obtain ⟨y, he, hyacc, hyframe⟩ := exec_summand x s c a (v s) base n hc0 hacc
      hbase hn (hmem s) ha hvs haddr hseven
    have hybase : y.regs group = base := (hyframe.2 group (by decide) (by decide)
      (by decide) (by decide)).trans hbase
    have hyn : y.regs stride = n := (hyframe.2 stride (by decide) (by decide)
      (by decide) (by decide)).trans hn
    have hfit' : |a + c * v s| + rest.length * B < (2 : ℤ) ^ (w - 1) := by
      have ht := abs_add_le a (c * v s)
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hfit
      nlinarith
    obtain ⟨z, hz, hzacc, hzframe⟩ := ih y (a + c * v s)
      (fun sc hsc => hc sc (by simp [hsc])) hyacc hybase hyn
      (fun s => by rw [hyframe.1]; exact hmem s) hfit'
    refine ⟨z, ?_, ?_, hyframe.trans hzframe⟩
    · simpa only [sumCode, List.length_cons, Nat.mul_add, Nat.mul_one,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he.seq hz
    · simpa only [List.map_cons, List.sum_cons, add_assoc] using hzacc

/-- A complete coefficient row, including initialization, costs at most 163 instructions.
All seven entries have absolute value at most `B`, so every partial sum has magnitude at
most `7B`; this ordinary explicit width condition is sufficient for every signed operation. -/
theorem exec_form {w : ℕ} (hw : 0 < w) (side : Bool) (t : Fin 10)
    (x : Data 32) (B : ℤ) (base n : ℕ) (v : Fin 7 → ℤ)
    (hbase : x.regs group = base) (hn : x.regs stride = n)
    (hmem : ∀ s, x.mem (base + s.val * n) = encode (v s))
    (hB : 0 ≤ B) (hv : ∀ s, |v s| ≤ B) (hfit : 7 * B < (2 : ℤ) ^ (w - 1))
    (haddr : Fits (w + 2) (base + 7 * n)) (hseven : Fits (w + 2) 7) :
    ∃ y, ExecWithin (w + 2) (form side t) x y 163 ∧
      y.regs accumulator = encode (∑ s, coefficients side t s * v s) ∧ FormFrame x y := by
  let z := x.set accumulator 0
  have hz : FormFrame x z := by
    refine ⟨rfl, ?_⟩
    intro i _ _ hi _
    simp only [z, Data.set_regs, Function.update_of_ne hi]
  obtain ⟨y, he, hacc, hf⟩ := exec_sumCode hw
    (List.ofFn fun s => (s, coefficients side t s)) z 0 B base n v
    (by intro sc hsc; obtain ⟨s, rfl⟩ := List.mem_ofFn.mp hsc; exact coefficients_values side t s)
    (by simp [z, encode])
    ((hz.2 group (by decide) (by decide) (by decide) (by decide)).trans hbase)
    ((hz.2 stride (by decide) (by decide) (by decide) (by decide)).trans hn)
    (by simpa only [z, Data.set_mem] using hmem) hB hv (by linarith)
    (by simpa using hfit) haddr hseven
  refine ⟨y, ?_, ?_, hz.trans hf⟩
  · simpa only [form, List.length_ofFn] using
      (ExecWithin.const (fits_zero (w := w + 2))).seq he
  · simpa only [List.map_ofFn, List.sum_ofFn, Function.comp_apply, zero_add] using hacc

/-- The finite term dispatch costs at most three instructions per inspected row in addition
to the row's 163-instruction bound. All ten forms share the same native register file. -/
theorem exec_dispatch {w : ℕ} (hw : 0 < w) (side : Bool) (rows : List (Fin 10))
    (t : Fin 10) (ht : t ∈ rows) (x : Data 32) (B : ℤ) (base n : ℕ) (v : Fin 7 → ℤ)
    (hterm : x.regs term = t.val) (hbase : x.regs group = base) (hn : x.regs stride = n)
    (hmem : ∀ s, x.mem (base + s.val * n) = encode (v s))
    (hB : 0 ≤ B) (hv : ∀ s, |v s| ≤ B) (hfit : 7 * B < (2 : ℤ) ^ (w - 1))
    (haddr : Fits (w + 2) (base + 7 * n)) (hten : Fits (w + 2) 10) :
    ∃ y, ExecWithin (w + 2) (dispatch side rows) x y (3 * rows.length + 163) ∧
      y.regs accumulator = encode (∑ s, coefficients side t s * v s) ∧ FormFrame x y := by
  induction rows generalizing x with
  | nil => simp at ht
  | cons q rest ih =>
    let z := x.set temporary q.val
    have hz : ExecWithin (B := .standard) (w + 2) (ram[ temporary ← #q.val ]) x z 1 :=
      ExecWithin.const (hten.of_le (by omega))
    have hzf : FormFrame x z := by
      refine ⟨rfl, ?_⟩
      intro i _ _ _ hi
      simp only [z, Data.set_regs, Function.update_of_ne hi]
    have hzt : z.regs term = t.val := by
      simpa [z, term, temporary, Fin.mk.injEq] using hterm
    have hzb : z.regs group = base := by
      simpa [z, group, temporary, Fin.mk.injEq] using hbase
    have hzn : z.regs stride = n := by
      simpa [z, stride, temporary, Fin.mk.injEq] using hn
    have hzm : ∀ s, z.mem (base + s.val * n) = encode (v s) := hmem
    by_cases hqt : t = q
    · subst t
      obtain ⟨y, he, hacc, hf⟩ := exec_form hw side q z B base n v hzb hzn hzm hB hv
        hfit haddr (hten.of_le (by decide))
      refine ⟨y, ?_, hacc, hzf.trans hf⟩
      apply (hz.seq (ExecWithin.branch_pos ?_ he)).mono
      · simp only [List.length_cons]
        omega
      · simp only [Cond.holds_eq, hzt, z, Data.set_regs, Function.update_self]
    · have htrest : t ∈ rest := (List.mem_cons.mp ht).resolve_left hqt
      obtain ⟨y, he, hacc, hf⟩ := ih htrest z hzt hzb hzn hzm
      refine ⟨y, ?_, hacc, hzf.trans hf⟩
      apply (hz.seq (ExecWithin.branch_neg ?_ he)).mono
      · simp only [List.length_cons]
        omega
      · simp only [Cond.holds_eq, hzt, z, Data.set_regs, Function.update_self]
        exact fun h => hqt (Fin.ext h)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Encoding
