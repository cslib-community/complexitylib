/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Forms
import Mathlib.Tactic.Ring

/-!
# A native mixed-radix encoding cell

## Main results

* `Encoding.exec_cell`: charged index arithmetic, coefficient dispatch, signed linear form,
  output store and counter increment for one cell of a shared coordinate transform.

## References

The linear forms are from [AlmanWilliams2026, Section 2.4.1]; see `Encoding` for provenance.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Encoding

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- The registers modified by a cell, apart from the nine signed-arithmetic scratch registers. -/
def CellLocal (i : Fin 32) : Prop :=
  i = cell ∨ i = block ∨ i = term ∨ i = suffix ∨ i = address ∨
    i = accumulator ∨ i = group ∨ i = temporary

instance (i : Fin 32) : Decidable (CellLocal i) :=
  inferInstanceAs (Decidable (i = cell ∨ i = block ∨ i = term ∨ i = suffix ∨
    i = address ∨ i = accumulator ∨ i = group ∨ i = temporary))

private theorem cell_preserves (side : Bool) (i : Fin 32) :
    9 ≤ i.val → ¬CellLocal i → (cellBody side).Preserves i := by
  decide +kernel +revert

/-- One output entry, with all index arithmetic and the counter increment charged. A single
ordinary explicit natural-number bound covers the addresses and index products; no fit
condition is imposed on an unspecified intermediate machine state. -/
theorem exec_cell {w : ℕ} (hw : 0 < w) (side : Bool) (x : Data 32)
    (P n s d i : ℕ) (hP : 0 < P) (hnpos : 0 < n) (hi : i < 10 * P * n)
    (hsrc : x.regs src = s) (hdst : x.regs dst = d) (hcell : x.regs cell = i)
    (hn : x.regs stride = n) (hseven : x.regs seven = 7)
    (hten : x.regs ten = 10) (hone : x.regs one = 1)
    (v : Fin 7 → ℤ) (B : ℤ) (hB : 0 ≤ B) (hv : ∀ a, |v a| ≤ B)
    (hmem : ∀ a, x.mem (s + (i / (10 * n) * 7 + a.val) * n + i % n) = encode (v a))
    (hval : 7 * B < (2 : ℤ) ^ (w - 1))
    (haddr : Fits (w + 2) (s + d + 64 + 64 * P * n)) :
    ∃ y, ExecWithin (w + 2) (cellBody side) x y 205 ∧
      y.mem = Function.update x.mem (d + i)
        (encode (∑ a, coefficients side ⟨i / n % 10, Nat.mod_lt _ (by decide)⟩ a * v a)) ∧
      y.regs cell = i + 1 ∧
      (∀ a, 9 ≤ a.val → ¬CellLocal a → y.regs a = x.regs a) := by
  let p := i / (10 * n)
  let t : Fin 10 := ⟨i / n % 10, Nat.mod_lt _ (by decide)⟩
  let r := i % n
  -- Keep nonlinear arithmetic focused on index bounds, rather than the execution context.
  have hp : p < P := by
    apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < 10 * n)).mpr
    nlinarith only [hi]
  have hr : r < n := Nat.mod_lt _ hnpos
  have hn1 : 1 ≤ n := hnpos
  have hPn : n ≤ P * n := Nat.le_mul_of_pos_left n hP
  have hmul : p * n < P * n := Nat.mul_lt_mul_of_pos_right hp hnpos
  have h10n : Fits (w + 2) (10 * n) := haddr.of_le (by nlinarith only [hPn])
  have hpfit : Fits (w + 2) p := haddr.of_le (by nlinarith only [hp, hn1])
  have hdiv : i / n ≤ i := Nat.div_le_self _ _
  have hdivfit : Fits (w + 2) (i / n) := haddr.of_le (by nlinarith only [hdiv, hi])
  have htfit : Fits (w + 2) t.val := haddr.of_le (by have := t.isLt; omega)
  have hrfit : Fits (w + 2) r := haddr.of_le (by nlinarith only [hr, hPn])
  have hp7 : Fits (w + 2) (p * 7) := haddr.of_le (by nlinarith only [hp, hn1])
  have hp7n : Fits (w + 2) (p * 7 * n) := haddr.of_le (by nlinarith only [hmul])
  have hp7nr : Fits (w + 2) (p * 7 * n + r) :=
    haddr.of_le (by nlinarith only [hmul, hr, hPn])
  have hgroup : Fits (w + 2) (s + (p * 7 * n + r)) :=
    haddr.of_le (by nlinarith only [hmul, hr, hPn])
  let z := ((((((((x.set temporary (10 * n)).set block p).set term (i / n)).set term t.val).set
    suffix r).set group (p * 7)).set group (p * 7 * n)).set group (p * 7 * n + r)).set
      group (s + (p * 7 * n + r))
  have hz : ExecWithin (w + 2) cellSetup x z 9 := by
    ram_eval [cellSetup, z, p, t, r, hsrc, hcell, hn, hseven, hten,
      h10n, hpfit, hdivfit, htfit, hrfit, hp7, hp7n, hp7nr, hgroup,
      temporary, block, term, suffix, group, src, cell, stride, seven, ten, Fin.mk.injEq]
  have hzterm : z.regs term = t.val := by
    simp [z, temporary, block, term, suffix, group]
  have hzgroup : z.regs group = s + (p * 7 * n + r) := by simp [z]
  have hzn : z.regs stride = n := by
    simpa [z, temporary, block, term, suffix, group, stride, Fin.mk.injEq] using hn
  have hzmem : ∀ a, z.mem (s + (p * 7 * n + r) + a.val * n) = encode (v a) := by
    intro a
    have hidx : s + (p * 7 * n + r) + a.val * n = s + (p * 7 + a.val) * n + r := by ring
    simpa only [z, Data.set_mem, hidx] using hmem a
  have hspan : Fits (w + 2) (s + (p * 7 * n + r) + 7 * n) :=
    haddr.of_le (by nlinarith only [hmul, hr, hPn])
  obtain ⟨u, hu, huacc, humem, hureg⟩ := exec_dispatch hw side (List.finRange 10) t
    (List.mem_finRange _) z B (s + (p * 7 * n + r)) n v hzterm hzgroup hzn hzmem
    hB hv hval hspan (haddr.of_le (by omega))
  have zucell : u.regs cell = i := by
    rw [hureg cell (by decide) (by decide) (by decide) (by decide)]
    simpa [z, temporary, block, term, suffix, group, cell, Fin.mk.injEq] using hcell
  have zudst : u.regs dst = d := by
    rw [hureg dst (by decide) (by decide) (by decide) (by decide)]
    simpa [z, temporary, block, term, suffix, group, dst, Fin.mk.injEq] using hdst
  have zuone : u.regs one = 1 := by
    rw [hureg one (by decide) (by decide) (by decide) (by decide)]
    simpa [z, temporary, block, term, suffix, group, one, Fin.mk.injEq] using hone
  have hdfit : Fits (w + 2) (d + i) := haddr.of_le (by nlinarith only [hi])
  have hinc : Fits (w + 2) (i + 1) := haddr.of_le (by nlinarith only [hi])
  let y := ((u.set address (d + i)).write (d + i) (u.regs accumulator)).set cell (i + 1)
  have hy : ExecWithin (w + 2) cellFinish u y 3 := by
    ram_eval [cellFinish, y, zucell, zudst, zuone, hdfit, hinc,
      address, cell, accumulator, dst, one, Fin.mk.injEq]
  have he : ExecWithin (w + 2) (cellBody side) x y 205 := by
    simpa only [cellBody, List.length_finRange] using (hz.seq (hu.seq hy)).mono
      (by decide : 9 + ((3 * 10 + 163) + 3) ≤ 205)
  refine ⟨y, he, ?_, ?_, fun a ha hl => he.regs_eq (cell_preserves side a ha hl)⟩
  · simp only [y, Data.set_mem, Data.write_mem, humem, z, huacc]
    rfl
  · simp [y]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Encoding
