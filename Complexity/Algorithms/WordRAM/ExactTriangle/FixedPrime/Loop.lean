/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.FixedPrime.Step
public import Complexity.Algorithms.WordRAM.ExactTriangle.FixedPrime.Potential

/-!
# Complete traversal of the actual prepared catalogue

Every guarded iteration delivers the next occupied ordinal to the concrete record program.
The invariant counts only the visited prefix: distinct failures share one global budget and
the actual successful-return flags sum to at most one. Scratch is reused above the producer
heap; protected readback and the genuine original producer execution are kept separate.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.FixedPrime

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

attribute [local instance] Classical.propDecidable

private structure Invariant {m n g p : ℕ} (V : ℕ → ℤ) (a : Data 64)
    (start : Data 416) (order : ℕ → InstanceIndex p) (hn : 0 < n) (x : Data 416) : Prop where
  bank : ∀ j : Fin 64, x.regs
    (recordBank (RecordWitness.productBank (RecordProduct.producerBank j))) = a.regs j
  protected_mem : Set.EqOn x.mem a.mem (Set.Iio (a.regs Instances.heap))
  frame : ∀ u, u < a.regs Instances.heap ∨
    a.regs Instances.heap + CallableProduct.windowSize n (n * n) ≤ u → x.mem u = start.mem u
  index_le : x.regs Reg.index ≤ a.regs Instances.produced
  one : x.regs Reg.one = 1
  flag : x.regs Reg.found = 0 ∨ x.regs Reg.found = 1
  limit : x.regs Reg.limit =
    (if x.regs Reg.found = 1 then x.regs Reg.index else a.regs Instances.produced)
  scans_failed : x.regs Reg.scans ≤
    (∑ j ∈ Finset.range (x.regs Reg.index),
      recordFailures (m := m) (g := g) hn V a.mem (order j)) + x.regs Reg.found
  scans_coarse : x.regs Reg.scans ≤ x.regs Reg.index * (n * n + 1)
  searched : Nat.count (fun j => recordHit (m := m) (n := n) (g := g) V (order j))
    (x.regs Reg.index) = x.regs Reg.found
  witness : x.regs Reg.found = 1 →
    x.regs (recordBank RecordWitness.Reg.witnessA) < n ∧
    x.regs (recordBank RecordWitness.Reg.witnessB) < n ∧
    x.regs (recordBank RecordWitness.Reg.witnessC) < n ∧
    V (x.regs (recordBank RecordWitness.Reg.witnessA) * n +
        x.regs (recordBank RecordWitness.Reg.witnessB)) +
      V (n * n + (x.regs (recordBank RecordWitness.Reg.witnessB) * n +
        x.regs (recordBank RecordWitness.Reg.witnessC))) +
      V (2 * (n * n) + (x.regs (recordBank RecordWitness.Reg.witnessA) * n +
        x.regs (recordBank RecordWitness.Reg.witnessC))) = 0

private theorem window_mono {n Q : ℕ} (hQ : Q ≤ n * n) :
    CallableProduct.windowSize n Q ≤ CallableProduct.windowSize n (n * n) := by
  unfold CallableProduct.windowSize CallableProduct.sourceWidth
  exact Nat.pow_le_pow_right (by decide)
    (Nat.mul_le_mul_left 128 (Nat.clog_mono_right 2 (by omega)))

/-- Run all occupied records, stopping at the first original witness. The original producer
readback is a caller premise; the initialized theorem constructs it by running the producer
once. No intermediate layout, answer, scan order or execution contract is an algorithm input. -/
theorem exec_traverse {w m n g p A : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hD : 16 ≤ D m)
    (hg : 1 ≤ g) (hp : p ∈ Nat.sqrtPrimeWindow (D m)) (hN : D m ^ 18 ≤ n)
    (hv : ∀ z ∈ values, z.natAbs ≤ A)
    (hW : admissionWidth n (D m) g p A ≤ w + 2)
    (a : Data 64) (x : Data 416)
    (hout : Instances.Output n (D m) g p (fun q => values.getD q 0)
      (.init (PreparationInput.input n (D m) g p values)) a)
    (hbank : ∀ j : Fin 64,
      x.regs (recordBank (RecordWitness.productBank (RecordProduct.producerBank j))) = a.regs j)
    (hmem : Set.EqOn x.mem a.mem (Set.Iio (a.regs Instances.heap)))
    (hheap : a.regs Instances.heap ≤ PreparationInput.wordBound n (D m) g p A) :
    let V := fun q => values.getD q 0
    let wAB := fun u v : Fin n => V (pairIndex (u, v))
    let wBC := fun b c : Fin n => V (n * n + pairIndex (b, c))
    let wAC := fun u c : Fin n => V (2 * (n * n) + pairIndex (u, c))
    let hn : 0 < n := lt_of_lt_of_le (by omega : 0 < D m)
      ((Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN)
    ∃ y, ExecWithin (w + 2) traverse x y
        ((∑ idx ∈ instanceIndices wAB (D m) g p, recordBase (m := m) hn V a.mem idx) +
          (42 * pieceSize (D m) g + 28) * (falsePositiveCount wAB wBC wAC p + 1) + 7) ∧
      (y.regs Reg.found = 0 ∨ y.regs Reg.found = 1) ∧
      y.regs Reg.scans ≤ falsePositiveCount wAB wBC wAC p + y.regs Reg.found ∧
      (y.regs Reg.found = 1 ↔ HasZeroTriangle wAB wBC wAC) ∧
      (y.regs Reg.found = 1 →
        y.regs (recordBank RecordWitness.Reg.witnessA) < n ∧
        y.regs (recordBank RecordWitness.Reg.witnessB) < n ∧
        y.regs (recordBank RecordWitness.Reg.witnessC) < n ∧
        V (y.regs (recordBank RecordWitness.Reg.witnessA) * n +
            y.regs (recordBank RecordWitness.Reg.witnessB)) +
          V (n * n + (y.regs (recordBank RecordWitness.Reg.witnessB) * n +
            y.regs (recordBank RecordWitness.Reg.witnessC))) +
          V (2 * (n * n) + (y.regs (recordBank RecordWitness.Reg.witnessA) * n +
            y.regs (recordBank RecordWitness.Reg.witnessC))) = 0) ∧
      (∀ u, u < a.regs Instances.heap ∨
        a.regs Instances.heap + CallableProduct.windowSize n (n * n) ≤ u → y.mem u = x.mem u) ∧
      ∀ j : Fin 64, y.regs
        (recordBank (RecordWitness.productBank (RecordProduct.producerBank j))) = a.regs j := by
  classical
  let V := fun q => values.getD q 0
  let wAB := fun u v : Fin n => V (pairIndex (u, v))
  let wBC := fun b c : Fin n => V (n * n + pairIndex (b, c))
  let wAC := fun u c : Fin n => V (2 * (n * n) + pairIndex (u, c))
  have hDn : D m ≤ n := (Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN
  have hn : 0 < n := lt_of_lt_of_le (by omega) hDn
  have hp0 := (Nat.mem_sqrtPrimeWindow_iff_sq.mp hp).1.ne_zero
  let M := a.regs Instances.produced
  let I := instanceIndices wAB (D m) g p
  obtain ⟨f, -, hf, fsurj⟩ := exists_occupied_order V hout hD hDn hg hp0
  let order : ℕ → InstanceIndex p := fun i =>
    if hi : i < M then f ⟨i, hi⟩ else (⟨0, Nat.pos_of_ne_zero hp0⟩, 0, 0)
  have order_at (i : ℕ) (hi : i < M) : order i = f ⟨i, hi⟩ := dite_eq_left hi
  have order_mem (i : ℕ) (hi : i < M) : order i ∈ I := by
    rw [order_at i hi]
    exact (hf _).1
  have order_ord (i : ℕ) (hi : i < M) :
      RecordProduct.recordOrdinal n (D m) g p V (order i) = i := by
    rw [order_at i hi]
    exact (hf _).2
  have order_inj : Set.InjOn order (Finset.range M) := by
    intro i hi j hj hij
    exact (order_ord i (Finset.mem_range.mp hi)).symm.trans
      ((congrArg (RecordProduct.recordOrdinal n (D m) g p V) hij).trans
        (order_ord j (Finset.mem_range.mp hj)))
  have image_eq : (Finset.range M).image order = I := by
    ext idx
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact order_mem i hi
    · intro hi
      obtain ⟨i, hi⟩ := fsurj idx hi
      exact ⟨i.val, i.isLt, (order_at i.val i.isLt).trans hi⟩
  have sum_eq (charge : InstanceIndex p → ℕ) :
      (∑ j ∈ Finset.range M, charge (order j)) = ∑ idx ∈ I, charge idx := by
    rw [← image_eq, Finset.sum_image order_inj]
  let B := fun i => recordBase (m := m) hn V a.mem (order i)
  let F := fun i => recordFailures (m := m) (g := g) hn V a.mem (order i)
  let C := 42 * pieceSize (D m) g + 28
  have hF : (∑ j ∈ Finset.range M, F j) ≤ falsePositiveCount wAB wBC wAC p := by
    rw [show (∑ j ∈ Finset.range M, F j) =
      ∑ idx ∈ I, recordFailures (m := m) (g := g) hn V a.mem idx from
        sum_eq (recordFailures (m := m) (g := g) hn V a.mem)]
    exact sum_recordFailures_le hn V hout hD hDn hg hp I (fun _ hi => hi)
  let Inv := Invariant (m := m) (g := g) V a x order hn
  let Φ := fun z : Data 416 => remainingCharge B F C M (z.regs Reg.index) (z.regs Reg.found)
  have body : ∀ z, Inv z → (Cond.lt Reg.index Reg.limit).Holds z →
      ∃ y T, ExecWithin (w + 2) step z y T ∧ Inv y ∧ T + 2 + Φ y ≤ Φ z := by
    intro z hz hc
    have hguard : z.regs Reg.index < z.regs Reg.limit := hc
    have before : z.regs Reg.found = 0 := by
      rcases hz.flag with h | h
      · exact h
      · have hlim := hz.limit
        rw [h, ite_eq_left rfl] at hlim
        omega
    have lim : z.regs Reg.limit = M := by
      simpa only [before, zero_ne_one, ite_false] using hz.limit
    have hi : z.regs Reg.index < M := by omega
    obtain ⟨y, S, T, he, hT, yi, yl, yo, ys, yf, hS, hcoarse, yhit, yw, ym, ybank⟩ :=
      exec_step values hlen hD hg hp hN hv hW a z hout hz.bank hz.protected_mem hheap rfl hi lim
        hz.one hz.scans_coarse (order (z.regs Reg.index)) (order_mem _ hi) (order_ord _ hi)
    have newflag : y.regs Reg.found ≤ 1 := by rcases yf with h | h <;> omega
    have yInv : Inv y := by
      refine ⟨ybank, ?_, ?_, ?_, yo, yf, ?_, ?_, ?_, ?_, yw⟩
      · intro u hu
        exact (ym u (Or.inl hu)).trans (hz.protected_mem hu)
      · intro u hu
        have houtside : u < a.regs Instances.heap ∨ a.regs Instances.heap +
            CallableProduct.windowSize n
              (RecordProduct.recordQueryCount n (D m) p V (order (z.regs Reg.index))) ≤ u := by
          rcases hu with h | h
          · exact Or.inl h
          · exact Or.inr (le_trans (Nat.add_le_add_left
              (window_mono (recordQueryCount_le n (D m) p V _)) _) h)
        exact (ym u houtside).trans (hz.frame u hu)
      · rw [yi]
        exact Nat.succ_le_of_lt hi
      · simpa only [yi] using yl
      · have hs := hz.scans_failed
        rw [before, Nat.add_zero] at hs
        rw [ys, yi, Finset.sum_range_succ]
        change z.regs Reg.scans + S ≤
          (∑ j ∈ Finset.range (z.regs Reg.index), F j) + F (z.regs Reg.index) + y.regs Reg.found
        change S ≤ F (z.regs Reg.index) + y.regs Reg.found at hS
        change z.regs Reg.scans ≤ ∑ j ∈ Finset.range (z.regs Reg.index), F j at hs
        omega
      · rw [ys, yi, Nat.add_mul, Nat.one_mul]
        exact Nat.add_le_add hz.scans_coarse hcoarse
      · rw [yi, Nat.count_succ]
        have searched := hz.searched
        rw [before] at searched
        rw [searched, Nat.zero_add]
        rcases yf with h | h
        · rw [ite_eq_right (by intro hh; have := yhit.mpr hh; omega), h]
        · rw [ite_eq_left (yhit.mp h), h]
    refine ⟨y, T, he, yInv, ?_⟩
    have paid := remainingCharge_step (base := B) (failures := F) (C := C) hi hT hS newflag
    simpa only [Φ, yi, before] using paid
  have h1 : Fits (w + 2) 1 := (counter_fits hW).of_le (by unfold counterEnvelope; omega)
  obtain ⟨s, hs, sm, si, sl, sf, ss, so, sbank⟩ := exec_setup x h1
  have sInv : Inv s := by
    refine ⟨fun j => (sbank _ (by change j.val < 400; omega)).trans (hbank j), ?_, ?_, ?_,
      so, Or.inl sf, ?_, ?_, ?_, ?_, ?_⟩
    · intro u hu
      exact (congrFun sm u).trans (hmem hu)
    · intro u _
      exact congrFun sm u
    · rw [si]
      exact Nat.zero_le _
    · rw [sf, ite_eq_right (by decide : ¬(0 : ℕ) = 1), sl, hbank]
    · simp only [si, ss, sf, Finset.range_zero, Finset.sum_empty, Nat.zero_add, le_refl]
    · simp only [ss, si, Nat.zero_mul, le_refl]
    · simp only [si, sf, Nat.count_zero]
    · intro h
      omega
  obtain ⟨y, hy, hIy, hcy⟩ := ExecWithin.loop_potential Inv Φ body sInv
  have hbudget : 5 + (Φ s + 2) ≤
      (∑ idx ∈ I, recordBase (m := m) hn V a.mem idx) +
        C * (falsePositiveCount wAB wBC wAC p + 1) + 7 := by
    dsimp only [Φ, remainingCharge]
    rw [si, sf]
    simp only [Finset.range_zero, Finset.sum_empty, Nat.sub_zero]
    have hmul := Nat.mul_le_mul_left C (Nat.add_le_add_right hF 1)
    rw [sum_eq (recordBase (m := m) hn V a.mem)]
    omega
  have hex : ExecWithin (w + 2) traverse x y
      ((∑ idx ∈ I, recordBase (m := m) hn V a.mem idx) +
        C * (falsePositiveCount wAB wBC wAC p + 1) + 7) := (hs.seq hy).mono hbudget
  refine ⟨y, hex, hIy.flag, ?_, ?_, hIy.witness, hIy.frame, hIy.bank⟩
  · exact hIy.scans_failed.trans (Nat.add_le_add_right
      ((sum_prefix_le F hIy.index_le).trans hF) _)
  · constructor
    · intro hf
      obtain ⟨ha, hb, hc, hw⟩ := hIy.witness hf
      exact ⟨⟨_, ha⟩, ⟨_, hb⟩, ⟨_, hc⟩, hw⟩
    · intro hzero
      by_contra hnot
      have hf : y.regs Reg.found = 0 := by rcases hIy.flag with h | h <;> omega
      have hlim : y.regs Reg.limit = M := by
        simpa only [hf, zero_ne_one, ite_false] using hIy.limit
      have hi : y.regs Reg.index = M := by
        change ¬ y.regs Reg.index < y.regs Reg.limit at hcy
        have := hIy.index_le
        omega
      obtain ⟨u, v, c, hw⟩ := hzero
      have hans := RecordProduct.product_answers_correct V wAB wBC wAC hD hg hp
        (by intro b c; rfl) (by intro u c; rfl)
      obtain ⟨rho, k, piece, hacc, hc⟩ := exists_mem_acceptedPairs hD hDn hg hp0 hans hw
      obtain ⟨hidx, hquery, -⟩ := mem_acceptedPairs.mp hacc
      obtain ⟨j, hj⟩ := fsurj (rho, k, piece) hidx
      have hh : recordHit (m := m) (n := n) (g := g) V (order j.val) := by
        rw [order_at j.val j.isLt, hj]
        exact ⟨(u, v), hquery, c, hc, hw⟩
      have hpositive := Nat.count_strict_mono (p := fun j =>
        recordHit (m := m) (n := n) (g := g) V (order j)) hh j.isLt
      have searched := hIy.searched
      rw [hf, hi] at searched
      rw [searched] at hpositive
      exact Nat.not_lt_zero _ hpositive

end Cslib.Algorithms.WordRAM.ExactTriangle.FixedPrime
