/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordWitness.Pair

/-!
# Charged query-controller steps

An accepted step reads the actual answer word and invokes the actual original-weight verifier.
The separate skipped-step rule accounts for both zero answers and the already-successful
short circuit. These are internal execution rules, not additional algorithm inputs.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness

open Cslib.WordRAM

/-- A nonzero actual product word, while still searching, causes exactly one native scan.
The six additional instructions include both branches, answer access and cursor advancement. -/
theorem exec_step_scan {w U n first length out queries count i scans a b : ℕ}
    (AB BC AC : ℕ → ℕ → ℤ) (x : Data 400)
    (hx : Fixed n first length out queries count x)
    (hi : x.regs Reg.index = i) (hs : x.regs Reg.scans = scans)
    (hf : x.regs Reg.found = 0) (hanswer : x.mem (out + i) ≠ 0)
    (haWord : x.mem (queries + 2 * i) = a)
    (hbWord : x.mem (queries + 2 * i + 1) = b)
    (ha : a < n) (hb : b < n) (hc : first + length ≤ n)
    (hmem : ∀ u < n, ∀ v < n,
      x.mem (5 + (u * n + v)) = Signed.encode (AB u v) ∧
      x.mem (5 + n * n + (u * n + v)) = Signed.encode (BC u v) ∧
      x.mem (5 + n * n + n * n + (u * n + v)) = Signed.encode (AC u v))
    (hmag : ∀ u < n, ∀ v < n,
      (AB u v).natAbs ≤ U ∧ (BC u v).natAbs ≤ U ∧ (AC u v).natAbs ≤ U)
    (hU : GenericRAM.Signed.Fits w (2 * U : ℕ))
    (hfit : Fits (w + 2)
      (out + queries + 3 * i + scans + 6 * (n * n) + n + first + length + 40)) :
    ∃ y, ExecWithin (w + 2) step x y (42 * length + 34) ∧
      Fixed n first length out queries count y ∧ y.mem = x.mem ∧
      y.regs Reg.index = i + 1 ∧ y.regs Reg.scans = scans + 1 ∧
      (y.regs Reg.found = 0 ∨ y.regs Reg.found = 1) ∧
      (y.regs Reg.found = 1 ↔
        ∃ c, first ≤ c ∧ c < first + length ∧ AB a b + BC b c + AC a c = 0) ∧
      (y.regs Reg.found = 1 →
        y.regs Reg.witnessA = a ∧ y.regs Reg.witnessB = b ∧
        first ≤ y.regs Reg.witnessC ∧ y.regs Reg.witnessC < first + length ∧
        AB a b + BC b (y.regs Reg.witnessC) + AC a (y.regs Reg.witnessC) = 0) := by
  let d := x.set Reg.address (out + i) |>.set Reg.answer (x.mem (out + i))
  have hd : ExecWithin (w + 2)
      (ram[ Reg.address ← Reg.output + Reg.index; Reg.answer ← *Reg.address ]) x d 2 := by
    ram_eval [d, hx.output, hi, Reg.address, Reg.output, Reg.index, Reg.answer,
      hfit.of_le (by omega : out + i ≤
        out + queries + 3 * i + scans + 6 * (n * n) + n + first + length + 40)]
  have dFixed : Fixed n first length out queries count d := hx.of_frame (by
    intro j hj
    have haddr : j ≠ Reg.address := by
      intro he
      subst j
      norm_num [Reg.address, Reg.one, Reg.zero] at hj
    have hans : j ≠ Reg.answer := by
      intro he
      subst j
      norm_num [Reg.answer, Reg.one, Reg.zero] at hj
    simp [d, haddr, hans])
  obtain ⟨s, he, sFixed, sm, si, ss, sf, sh, sw⟩ := exec_scanPair AB BC AC d dFixed
    (by simpa +decide [d, Reg.address, Reg.answer, Reg.index] using hi)
    (by simpa +decide [d, Reg.address, Reg.answer, Reg.scans] using hs)
    (by simpa +decide [d, Reg.address, Reg.answer, Reg.found] using hf)
    haWord hbWord ha hb hc hmem hmag hU
    (hfit.of_le (by omega))
  have hb : ExecWithin (w + 2)
      (.branch (.eq Reg.found Reg.zero)
        (.seq (ram[ Reg.address ← Reg.output + Reg.index; Reg.answer ← *Reg.address ])
          (.branch (.eq Reg.answer Reg.zero) (.op (.copy Reg.answer Reg.answer)) scanPair))
        (.op (.copy Reg.answer Reg.answer))) x s (42 * length + 33) := by
    apply ExecWithin.branch_pos (by simp only [Cond.holds_eq, hf, hx.zero])
    exact (hd.seq (ExecWithin.branch_neg (cond := .eq Reg.answer Reg.zero) (by
      simpa +decide [Cond.holds_eq, d, Reg.answer, Reg.address, Reg.zero,
        show x.regs 399 = 0 from hx.zero] using hanswer) he)).mono (by omega)
  let y := s.set Reg.index (i + 1)
  have hy : ExecWithin (w + 2) (.op (.bin .add Reg.index Reg.index Reg.one)) s y 1 := by
    ram_eval [y, si, sFixed.one, Reg.index, Reg.one,
      hfit.of_le (by omega : i + 1 ≤
        out + queries + 3 * i + scans + 6 * (n * n) + n + first + length + 40)]
  have yFixed : Fixed n first length out queries count y := sFixed.of_frame (by
    intro j hj
    have hne : j ≠ Reg.index := by
      intro he
      subst j
      norm_num [Reg.index, Reg.one, Reg.zero] at hj
    simp [y, hne])
  refine ⟨y, hb.seq hy, yFixed, sm, rfl, ?_, ?_, ?_, ?_⟩
  · simpa +decide [y, Reg.index, Reg.scans] using ss
  · simpa +decide [y, Reg.index, Reg.found] using sf
  · simpa +decide [y, Reg.index, Reg.found] using sh
  · simpa +decide [y, Reg.index, Reg.found, Reg.witnessA, Reg.witnessB,
      Reg.witnessC] using sw

/-- Zero answers and an already successful flag incur no verifier call. In particular the
actual scan counter and all returned witness coordinates are preserved. -/
theorem exec_step_skip {W n first length out queries count i : ℕ} (x : Data 400)
    (hx : Fixed n first length out queries count x) (hi : x.regs Reg.index = i)
    (hskip : x.regs Reg.found ≠ 0 ∨ x.mem (out + i) = 0)
    (hfit : Fits W (out + i + 2)) :
    ∃ y, ExecWithin W step x y 6 ∧ Fixed n first length out queries count y ∧
      y.mem = x.mem ∧ y.regs Reg.index = i + 1 ∧
      ∀ j : Fin 400, j ≠ Reg.index → j ≠ Reg.address → j ≠ Reg.answer →
        y.regs j = x.regs j := by
  let y := if x.regs Reg.found = 0 then
      (x.set Reg.address (out + i) |>.set Reg.answer 0 |>.set Reg.answer 0)
        |>.set Reg.index (i + 1)
    else (x.set Reg.answer (x.regs Reg.answer)).set Reg.index (i + 1)
  have ha : Fits W (out + i) := hfit.of_le (by omega)
  have ht : Fits W (i + 1) := hfit.of_le (by omega)
  have he : ExecWithin W step x y 6 := by
    by_cases hf : x.regs Reg.found = 0
    · have hz : x.mem (out + i) = 0 := hskip.resolve_left (not_not_intro hf)
      ram_eval [step, y, hf, hz, hi, hx.output, hx.zero, hx.one, ha, ht,
        Reg.found, Reg.zero, Reg.address, Reg.output, Reg.index, Reg.answer, Reg.one]
    · ram_eval [step, y, hf, hi, hx.zero, hx.one, ht,
        Reg.found, Reg.zero, Reg.answer, Reg.index, Reg.one]
  have frame (j : Fin 400) (hj : j ≠ Reg.index) (ha : j ≠ Reg.address)
      (hb : j ≠ Reg.answer) : y.regs j = x.regs j := by
    by_cases hf : x.regs Reg.found = 0 <;> simp [y, hf, hj, ha, hb]
  have yFixed : Fixed n first length out queries count y := hx.of_frame (by
    intro j hj
    have hindex : j ≠ Reg.index := by
      intro he; subst j; norm_num [Reg.index, Reg.one, Reg.zero] at hj
    have haddr : j ≠ Reg.address := by
      intro he; subst j; norm_num [Reg.address, Reg.one, Reg.zero] at hj
    have hans : j ≠ Reg.answer := by
      intro he; subst j; norm_num [Reg.answer, Reg.one, Reg.zero] at hj
    exact frame j hindex haddr hans)
  refine ⟨y, he, yFixed, ?_, ?_, frame⟩
  · by_cases hf : x.regs Reg.found = 0 <;> simp [y, hf]
  · by_cases hf : x.regs Reg.found = 0 <;> simp [y, hf]

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness
