/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CountPrime.Program

/-!
# Actual canonical signed monomial writes

Each of the p coefficients is stored, so dirty destination words do not become implicit
padding. An out-of-range key (in particular the native padding sentinel p) writes a zero
block. The raw unsigned word two is exactly `Signed.encode 1`; there is no extra conversion
or free ring-coefficient operation. This is an internal counter-stage execution API.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime

open Cslib.WordRAM

private theorem writeCoefficient_preserves (i : Fin 128) :
    i ≠ Reg.coefficient → i ≠ Reg.address → writeCoefficient.Preserves i := by
  decide +kernel +revert

/-- A whole dirty p-word destination becomes the canonical coefficient block, with every
test, address calculation and store charged. The key may be any unsigned word. -/
theorem exec_writeCoefficients {w : ℕ} (x : Data 128)
    (h0 : x.regs Reg.zero = 0) (h1 : x.regs Reg.one = 1) (h2 : x.regs Reg.two = 2)
    (hw : Fits w (x.regs Reg.block + x.regs Reg.modulus + 4)) :
    ∃ y, ExecWithin w writeCoefficients x y (7 * x.regs Reg.modulus + 3) ∧
      (∀ j < x.regs Reg.modulus, y.mem (x.regs Reg.block + j) =
        if j = x.regs Reg.residue then 2 else 0) ∧
      (∀ a, a < x.regs Reg.block ∨ x.regs Reg.block + x.regs Reg.modulus ≤ a →
        y.mem a = x.mem a) ∧
      ∀ i, i ≠ Reg.coefficient → i ≠ Reg.address → y.regs i = x.regs i := by
  let I (y : Data 128) : Prop :=
    (∀ i, i ≠ Reg.coefficient → i ≠ Reg.address → y.regs i = x.regs i) ∧
    y.regs Reg.coefficient ≤ x.regs Reg.modulus ∧
    (∀ j < y.regs Reg.coefficient, y.mem (x.regs Reg.block + j) =
      if j = x.regs Reg.residue then 2 else 0) ∧
    ∀ a, ¬(x.regs Reg.block ≤ a ∧ a < x.regs Reg.block + y.regs Reg.coefficient) →
      y.mem a = x.mem a
  have hbody (y : Data 128) (hy : I y)
      (hc : (Cond.lt Reg.coefficient Reg.modulus).Holds y) :
      ∃ z, ExecWithin w writeCoefficient y z 5 ∧ I z ∧
        x.regs Reg.modulus - z.regs Reg.coefficient <
          x.regs Reg.modulus - y.regs Reg.coefficient := by
    obtain ⟨hr, hi, hv, hf⟩ := hy
    have hmod := hr Reg.modulus (by decide) (by decide)
    have hbase := hr Reg.block (by decide) (by decide)
    have hres := hr Reg.residue (by decide) (by decide)
    have hy0 := (hr Reg.zero (by decide) (by decide)).trans h0
    have hy1 := (hr Reg.one (by decide) (by decide)).trans h1
    have hy2 := (hr Reg.two (by decide) (by decide)).trans h2
    have hlt : y.regs Reg.coefficient < x.regs Reg.modulus := by
      simpa only [Cond.holds_lt, hmod] using hc
    have ha : Fits w (y.regs Reg.block + y.regs Reg.coefficient) := hw.of_le (by
      rw [hbase]; omega)
    have hn : Fits w (y.regs Reg.coefficient + 1) := hw.of_le (by omega)
    let z := ((y.set Reg.address (y.regs Reg.block + y.regs Reg.coefficient)).write
      (y.regs Reg.block + y.regs Reg.coefficient)
      (if y.regs Reg.coefficient = y.regs Reg.residue then 2 else 0)).set
      Reg.coefficient (y.regs Reg.coefficient + 1)
    have he : ExecWithin w writeCoefficient y z 5 := by
      let before := y.set Reg.address (y.regs Reg.block + y.regs Reg.coefficient)
      let middle := before.write (y.regs Reg.block + y.regs Reg.coefficient)
        (if y.regs Reg.coefficient = y.regs Reg.residue then 2 else 0)
      have hfirst : ExecWithin (B := .standard) w
          (ram[ Reg.address ← Reg.block + Reg.coefficient ]) y before 1 := .bin ha
      have hcase : ExecWithin (B := .standard) w
          (.branch (.eq Reg.coefficient Reg.residue)
            (ram[ *Reg.address ← Reg.two ]) (ram[ *Reg.address ← Reg.zero ])) before middle 3 := by
        apply ExecWithin.branch
        · intro hc'
          have h : y.regs Reg.coefficient = y.regs Reg.residue := by
            simpa +decide [before, Cond.holds_eq, Reg.address, Reg.coefficient,
              Reg.residue] using hc'
          simpa +decide [middle, before, h, hy2, Reg.address, Reg.two] using
            (ExecWithin.store (B := .standard) (w := w) (a := Reg.address) (s := Reg.two)
              (x := before))
        · intro hc'
          have h : y.regs Reg.coefficient ≠ y.regs Reg.residue := by
            simpa +decide [before, Cond.holds_eq, Reg.address, Reg.coefficient,
              Reg.residue] using hc'
          simpa +decide [middle, before, h, hy0, Reg.address, Reg.zero] using
            (ExecWithin.store (B := .standard) (w := w) (a := Reg.address) (s := Reg.zero)
              (x := before))
      have hlast : ExecWithin (B := .standard) w
          (ram[ Reg.coefficient ← Reg.coefficient + Reg.one ]) middle z 1 := by
        ram_eval [middle, before, z, hy1, hn, Reg.address, Reg.coefficient, Reg.one]
      exact hfirst.seq (hcase.seq hlast)
    refine ⟨z, he, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · intro i hc ha
      exact (he.regs_eq (writeCoefficient_preserves i hc ha)).trans (hr i hc ha)
    · change y.regs Reg.coefficient + 1 ≤ x.regs Reg.modulus
      omega
    · intro j hj
      change j < y.regs Reg.coefficient + 1 at hj
      change Function.update y.mem (y.regs Reg.block + y.regs Reg.coefficient)
        (if y.regs Reg.coefficient = y.regs Reg.residue then 2 else 0)
        (x.regs Reg.block + j) = _
      by_cases heq : j = y.regs Reg.coefficient
      · subst j
        rw [hbase, Function.update_self, hres]
      · rw [Function.update_of_ne (by rw [hbase]; omega)]
        exact hv j (by omega)
    · intro a ha
      change ¬(x.regs Reg.block ≤ a ∧ a < x.regs Reg.block + (y.regs Reg.coefficient + 1)) at ha
      change Function.update y.mem (y.regs Reg.block + y.regs Reg.coefficient)
        (if y.regs Reg.coefficient = y.regs Reg.residue then 2 else 0) a = x.mem a
      rw [Function.update_of_ne (by rw [hbase]; omega)]
      exact hf a (by omega)
    · change x.regs Reg.modulus - (y.regs Reg.coefficient + 1) <
        x.regs Reg.modulus - y.regs Reg.coefficient
      omega
  let y := x.set Reg.coefficient 0
  have hinit : ExecWithin (B := .standard) w (ram[ Reg.coefficient ← #0 ]) x y 1 :=
    .const (fits_zero w)
  have hI : I y := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i hc ha
      exact Function.update_of_ne hc _ _
    · change 0 ≤ x.regs Reg.modulus
      omega
    · intro j hj
      change j < 0 at hj
      omega
    · intro a ha
      rfl
  obtain ⟨z, hz, hIz, hstop⟩ := ExecWithin.loop_invariant I
    (fun y => x.regs Reg.modulus - y.regs Reg.coefficient) hbody hI
  obtain ⟨hr, hi, hv, hf⟩ := hIz
  have hi' : z.regs Reg.coefficient = x.regs Reg.modulus := by
    have hm := hr Reg.modulus (by decide) (by decide)
    simp only [Cond.holds_lt, hm] at hstop
    omega
  refine ⟨z, (hinit.seq hz).mono (by change 1 +
    ((x.regs Reg.modulus - 0) * (5 + 2) + 2) ≤ _; omega), ?_, ?_, hr⟩
  · simpa only [hi'] using hv
  · intro a ha
    exact hf a (by omega)

end Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime
