/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime.Loop
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime.Cost
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordProduct.First
import CslibFrontier.Foundations.Data.List.GetD

/-!
# Complete box-backed fixed-prime execution with dirty source memory

The actual catalogue/setup prefix feeds the one-slot loop on arbitrary old registers and
dirty remaining memory. A derived all-record reference supplies finite mathematical indices
and the conservative time envelope. It describes no reused physical slot and is not an
algorithm input. Every constructed slot is read through its smaller physical boundary.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

private theorem prefix_not_readsWidth :
    ¬(Code.seq Instances.catalogue Instances.setup).ReadsWidth := by
  have h := Instances.program_fixed.2
  change ¬(Instances.catalogue.ReadsWidth ∨ Instances.setup.ReadsWidth ∨
    Instances.visit.ReadsWidth) at h
  change ¬(Instances.catalogue.ReadsWidth ∨ Instances.setup.ReadsWidth)
  intro hh
  exact h (hh.elim Or.inl (fun hs => Or.inr (Or.inl hs)))

/-- Execute the actual stream from original input words and arbitrary dirty remaining data.
The standalone output is only a derived mathematical reference for existing finite charges;
the native execution runs the catalogue/setup prefix and then the single-slot loop. The
allowance excludes one instruction reserved for the final halt. -/
theorem exec_source {w m n g p A : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hD : 16 ≤ D m)
    (hg : 1 ≤ g) (hp : p ∈ Nat.sqrtPrimeWindow (D m)) (hN : D m ^ 18 ≤ n)
    (hv : ∀ z ∈ values, z.natAbs ≤ A)
    (hW : FixedPrime.admissionWidth n (D m) g p A ≤ w + 2)
    (initial : Data 416)
    (hinput : ∀ q < 5 + 3 * (n * n), initial.mem q =
      (Data.init (PreparationInput.input n (D m) g p values) : Data 64).mem q) :
    let V := fun q => values.getD q 0
    let wAB := fun u v : Fin n => V (pairIndex (u, v))
    let wBC := fun b c : Fin n => V (n * n + pairIndex (b, c))
    let wAC := fun u c : Fin n => V (2 * (n * n) + pairIndex (u, c))
    let hn : 0 < n := lt_of_lt_of_le (by omega : 0 < D m)
      ((Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN)
    ∃ a : Data 64,
      Instances.Output n (D m) g p V
        (.init (PreparationInput.input n (D m) g p values)) a ∧
      ∃ y, ExecWithin (w + 2) program initial y
          (FixedPrime.timeBound (m := m) hn g p values a.mem - 1) ∧
        (y.regs FixedPrime.Reg.found = 0 ∨ y.regs FixedPrime.Reg.found = 1) ∧
        y.regs FixedPrime.Reg.scans ≤ falsePositiveCount wAB wBC wAC p +
          y.regs FixedPrime.Reg.found ∧
        (y.regs FixedPrime.Reg.found = 1 ↔ HasZeroTriangle wAB wBC wAC) ∧
        (y.regs FixedPrime.Reg.found = 1 →
          y.regs (FixedPrime.recordBank RecordWitness.Reg.witnessA) < n ∧
          y.regs (FixedPrime.recordBank RecordWitness.Reg.witnessB) < n ∧
          y.regs (FixedPrime.recordBank RecordWitness.Reg.witnessC) < n ∧
          V (y.regs (FixedPrime.recordBank RecordWitness.Reg.witnessA) * n +
              y.regs (FixedPrime.recordBank RecordWitness.Reg.witnessB)) +
            V (n * n + (y.regs (FixedPrime.recordBank RecordWitness.Reg.witnessB) * n +
              y.regs (FixedPrime.recordBank RecordWitness.Reg.witnessC))) +
            V (2 * (n * n) + (y.regs (FixedPrime.recordBank RecordWitness.Reg.witnessA) * n +
              y.regs (FixedPrime.recordBank RecordWitness.Reg.witnessC))) = 0) ∧
        ∀ q, q < 5 + 3 * (n * n) ∨
          a.regs Instances.heap + CallableProduct.windowSize n (n * n) ≤ q →
          y.mem q = initial.mem q := by
  let V := fun q => values.getD q 0
  let canonical : Data 64 := .init (PreparationInput.input n (D m) g p values)
  let a₀ := initial.comap producerBank
  have hDn : D m ≤ n := (Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN
  have hp0 := (Nat.mem_sqrtPrimeWindow_iff_sq.mp hp).1.pos
  have hw : PreparationInput.width n (D m) g p A ≤ w + 2 := by
    have hr := FixedPrime.record_admitted hW
    unfold RecordWitness.admissionWidth RecordProduct.admissionWidth at hr
    omega
  have header (q : ℕ) (hq : q < 5 + 3 * (n * n)) : initial.mem q = canonical.mem q := hinput q hq
  obtain ⟨hmag, hbudget⟩ := PreparationInput.fits_at_width n (D m) g p A
  have hmod := hmag.of_natAbs_le (show (p : ℤ).natAbs ≤ A + p + 1 by
    simp only [Int.natAbs_natCast]; omega)
  have hvalues (q : ℕ) (hq : q < 3 * (n * n)) : GenericRAM.Signed.Fits
      (Nat.clog 2 (PreparationInput.envelope n (D m) g p A) + 1) (V q) :=
    hmag.of_natAbs_le ((hv (values.getD q 0) (List.getD_mem 0 (by omega))).trans
      (by omega : A ≤ A + p + 1))
  obtain ⟨a, _, hout, b, hb, bn, bD, bp, bB, bH, bK, bd, bo, bz, bt, bh, bs, b1, b3,
      bL, bR, bmem, bframe⟩ := Instances.exec_at_with_prefix n (D m) g p V a₀
    (by simpa [a₀, canonical, PreparationInput.input, Data.init] using header 1 (by omega))
    (by simpa [a₀, canonical, PreparationInput.input, Data.init] using header 2 (by omega))
    (by simpa [a₀, canonical, PreparationInput.input, Data.init] using header 3 (by omega))
    (by simpa [a₀, canonical, PreparationInput.input, Data.init] using header 4 (by omega))
    (fun q hq => (header (5 + q) (by omega)).trans
      (PreparationInput.input_word n (D m) g p values q))
    (by omega) hDn hg hp0 hmod hvalues hbudget
  have hb' : ExecWithin (w + 2) (Code.seq Instances.catalogue Instances.setup) a₀ b
      (Catalogue.cost n (D m) p + 26) := by
    apply ExecWithin.mono_width prefix_not_readsWidth hb
    simpa only [PreparationInput.width, Nat.add_assoc] using hw
  have haEnd := hout.inputEnd_le_heap
  have haframe (q : ℕ) (hq : q < 5 + 3 * (n * n) ∨ a.regs Instances.heap ≤ q) :
      a.mem q = initial.mem q := by
    obtain ⟨_, _, _, _, _, hh, _, _, _, _, _, hf⟩ := hout
    exact hf q (by simpa only [hh] using hq)
  let reference : Data 64 := ⟨a.regs,
    fun q => if q < a.regs Instances.heap then a.mem q else canonical.mem q⟩
  have reference_mem (q : ℕ) (hq : q < a.regs Instances.heap) : reference.mem q = a.mem q :=
    ite_eq_left hq
  have reference_out : Instances.Output n (D m) g p V canonical reference :=
    hout.transfer V rfl (fun q hq => reference_mem q hq) (by
      intro q hq
      change (if q < a.regs Instances.heap then a.mem q else canonical.mem q) = canonical.mem q
      by_cases hh : q < a.regs Instances.heap
      · rw [ite_eq_left hh]
        have hin : q < 5 + 3 * (n * n) := by
          change _ ∨ a.regs Instances.heap ≤ q at hq
          omega
        exact (haframe q (Or.inl hin)).trans (header q hin)
      · rw [ite_eq_right hh])
  have heap : reference.regs Instances.heap ≤ PreparationInput.wordBound n (D m) g p A := by
    have hh := hout.heap_le_budget V (by omega) hDn hg
    change a.regs Instances.heap ≤ _
    unfold PreparationInput.wordBound PreparationInput.envelope
    omega
  have slot_end : a.regs Instances.output + (6 + 2 * (n * D m)) ≤ a.regs Instances.heap := by
    obtain ⟨idx, hidx, _⟩ := RecordProduct.first_index V hD hDn hg (Nat.ne_of_gt hp0)
    have hcard := PreparationSpec.count_eq_card V
      (fun u v : Fin n => V (pairIndex (u, v))) (Nat.ne_of_gt hp0) (by intro u v; rfl) hout
    have hpos : 1 ≤ a.regs Instances.produced := by
      rw [hcard]
      exact Finset.card_pos.mpr ⟨idx, hidx⟩
    have hs := Nat.mul_le_mul_right (6 + 2 * (n * D m)) hpos
    rw [Nat.one_mul] at hs
    have hh := hout.2.2.2.2.2.1
    rw [hh, ← hout.2.2.2.1, ← hout.2.2.2.2.1]
    omega
  let x := b.extend producerBank initial
  have hf : Function.Injective producerBank := Fin.castLE_injective (by decide)
  have hx : ExecWithin (w + 2) prepare initial x (Catalogue.cost n (D m) p + 26) := hb'.rename hf
  have xr (j : Fin 64) : x.regs (producerBank j) = b.regs j := hf.extend_apply _ _ j
  have cursor : Cursor n (D m) g p V (x.comap producerBank) := by
    have bc : Cursor n (D m) g p V b :=
      ⟨bn, bD, bp, bB, bH, bK, bd, bo.trans (by rw [hout.2.2.2.1, ← bK]),
        bt.trans (by rw [hout.2.2.2.2.1, ← bK, ← bH]), bs, b1, b3, bL, bR⟩
    simpa only [x, Data.comap_extend hf] using bc
  have hmem : Set.EqOn x.mem reference.mem (Set.Iio (reference.regs Instances.output)) := by
    intro q hq
    have hq' : q < b.regs Instances.output := by simpa only [bo, reference, Set.mem_Iio] using hq
    have hqa : q < a.regs Instances.heap := by
      have hq0 : q < a.regs Instances.output := by simpa only [bo] using hq'
      omega
    exact (bmem hq').trans (reference_mem q hqa).symm
  obtain ⟨y, hy, yf, ys, yiff, yw, frame, _⟩ := exec_traverse values hlen hD hg hp hN hv hW
    reference x reference_out cursor ((xr _).trans bz)
    (by rw [xr, xr]; exact bh) hmem heap
  have domination := streamingCharge_le_timeBound
    (lt_of_lt_of_le (by omega : 0 < D m) hDn) values canonical reference
      (Nat.ne_of_gt hp0) reference_out
  refine ⟨reference, reference_out, y, (hx.seq hy).mono ?_, yf, ys, yiff, yw, ?_⟩
  · dsimp only [V] at domination ⊢
    omega
  · intro q hq
    have hinputEnd : 5 + 3 * (n * n) ≤ a.regs Instances.output := by
      rw [hout.2.2.2.1]
      omega
    have houtside : q < reference.regs Instances.output ∨
        reference.regs Instances.output + (6 + 2 * (n * D m)) +
          CallableProduct.windowSize n (n * n) ≤ q := by
      change q < a.regs Instances.output ∨
        a.regs Instances.output + (6 + 2 * (n * D m)) +
          CallableProduct.windowSize n (n * n) ≤ q
      rcases hq with hh | hh
      · exact Or.inl (hh.trans_le hinputEnd)
      · exact Or.inr (by change a.regs Instances.heap + _ ≤ q at hh; omega)
    exact (frame q houtside).trans (bframe q (by
      rw [bo]
      rcases hq with hh | hh
      · exact Or.inl hh
      · exact Or.inr (by change a.regs Instances.heap + _ ≤ q at hh; omega)))

end Cslib.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime
