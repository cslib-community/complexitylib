/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Frontend.Arrays

/-!
# Complete descriptor-table execution

The invariant retains every completed descriptor and compact payload, both full radix arrays,
and all memory outside the allocated frontend region.

## Main results

The enumeration loop charges each native array scan, descriptor store and allocation advance.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Frontend.Arrays

open Cslib.WordRAM Select Scan

/-- Immutable registers of the complete enumeration loop. -/
structure Registers (l : Layout) (U k : ℕ) (x : Data 48) : Prop where
  /-- Original magnitude promise. -/
  magnitude : x.regs Select.magnitude = U
  /-- Original input length and explicit bit budget. -/
  inputLen : x.regs Arrays.inputLen = l.n
  digits : x.regs Arrays.digits = l.digits
  /-- Exact radix key/count pointers and distinct-key length. -/
  keys : x.regs Scan.keys = 1 + 2 * l.n
  counts : x.regs Scan.counts = 1 + 3 * l.n
  len : x.regs Scan.len = k
  /-- Computed layout values. -/
  splits : x.regs Arrays.splits = l.splits
  triples : x.regs Arrays.triples = l.count
  arrays : x.regs Arrays.arrays = l.arrays
  capacity : x.regs Arrays.capacity = l.capacity
  descriptors : x.regs Arrays.descriptors = l.descriptors
  heapEnd : x.regs Arrays.heapEnd = l.endpoint
  /-- All small constants are real native registers. -/
  constants : x.regs zero = 0 ∧ x.regs one = 1 ∧ x.regs two = 2 ∧
    x.regs three = 3 ∧ x.regs four = 4 ∧ x.regs five = 5

/-- The body preserves every immutable layout and source register. -/
theorem Registers.transfer {l : Layout} {U k : ℕ} {x y : Data 48}
    (h : Registers l U k x) (hr : ∀ i, body.Preserves i → y.regs i = x.regs i) :
    Registers l U k y := by
  constructor
  · exact (hr _ (by decide)).trans h.magnitude
  · exact (hr _ (by decide)).trans h.inputLen
  · exact (hr _ (by decide)).trans h.digits
  · exact (hr _ (by decide)).trans h.keys
  · exact (hr _ (by decide)).trans h.counts
  · exact (hr _ (by decide)).trans h.len
  · exact (hr _ (by decide)).trans h.splits
  · exact (hr _ (by decide)).trans h.triples
  · exact (hr _ (by decide)).trans h.arrays
  · exact (hr _ (by decide)).trans h.capacity
  · exact (hr _ (by decide)).trans h.descriptors
  · exact (hr _ (by decide)).trans h.heapEnd
  · obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h.constants
    exact ⟨(hr _ (by decide)).trans h0, (hr _ (by decide)).trans h1,
      (hr _ (by decide)).trans h2, (hr _ (by decide)).trans h3,
      (hr _ (by decide)).trans h4, (hr _ (by decide)).trans h5⟩

/-- Every layout scalar and partial allocation is below the explicit arithmetic budget. -/
theorem layout_bounds (l : Layout) (U : ℕ) :
    l.n + 1 ≤ budget l U ∧ l.digits * l.digits ≤ budget l U ∧
    l.splits ≤ budget l U ∧ l.count ≤ budget l U ∧ l.arrays ≤ budget l U ∧
    2 * l.arrays ≤ budget l U ∧ l.payloads ≤ budget l U ∧
    l.arrays * l.capacity ≤ budget l U ∧ l.endpoint ≤ budget l U ∧
    4 * U + 2 ≤ budget l U ∧ 5 ≤ budget l U := by
  have hb : budget l U = l.endpoint + 8 * U + 8 * l.digits + 64 := rfl
  have he : l.endpoint = l.payloads + l.capacity * l.arrays := rfl
  have hp : l.payloads = l.descriptors + 2 * l.arrays := rfl
  have hd : l.descriptors = 1 + 4 * l.n := rfl
  have hs : l.splits = 2 * l.digits ^ 2 := rfl
  have hc : l.count = l.splits + 2 := rfl
  have ha : l.arrays = 3 * l.count := rfl
  have hmul : l.arrays * l.capacity = l.capacity * l.arrays := Nat.mul_comm _ _
  have hsq : l.digits * l.digits = l.digits ^ 2 := (pow_two _).symm
  omega

/-- Setup computes all constants and addresses with actual instructions, preserving all memory. -/
theorem setup_exec {w U : ℕ} (l : Layout) (k : ℕ) (x : Data 48)
    (hU : x.regs Select.magnitude = U) (hn : x.regs inputLen = l.n)
    (hΛ : x.regs digits = l.digits) (hk : x.regs Scan.keys = 1 + 2 * l.n)
    (hc : x.regs Scan.counts = 1 + 3 * l.n) (hlen : x.regs len = k)
    (hd : x.regs descriptors = l.descriptors) (hfit : Fits w (budget l U)) :
    ∃ y, ExecWithin w setup x y 19 ∧ Registers l U k y ∧
      y.regs current = 0 ∧ y.regs heap = l.pointer 0 ∧ y.mem = x.mem := by
  obtain ⟨fN, fSq, fS, fD, fA, f2A, fP, fAC, fE, _, f5⟩ := layout_bounds l U
  have f0 : Fits w 0 := fits_zero w
  have f1 : Fits w 1 := hfit.of_le (by omega)
  have f2 : Fits w 2 := hfit.of_le (by omega)
  have f3 : Fits w 3 := hfit.of_le (by omega)
  have f4 : Fits w 4 := hfit.of_le (by omega)
  have f5' : Fits w 5 := hfit.of_le f5
  have fn := hfit.of_le fN
  have fsq := hfit.of_le fSq
  have fs : Fits w (l.digits * l.digits * 2) := by
    simpa only [Layout.splits, pow_two, Nat.mul_comm] using hfit.of_le fS
  have fd : Fits w (l.digits * l.digits * 2 + 2) := by
    simpa only [Layout.count, Layout.splits, pow_two, Nat.mul_comm] using hfit.of_le fD
  have fa : Fits w ((l.digits * l.digits * 2 + 2) * 3) := by
    simpa only [Layout.arrays, Layout.count, Layout.splits, pow_two, Nat.mul_comm]
      using hfit.of_le fA
  have f2a : Fits w ((l.digits * l.digits * 2 + 2) * 3 * 2) := by
    simpa only [Layout.arrays, Layout.count, Layout.splits, pow_two, Nat.mul_comm,
      Nat.mul_left_comm, Nat.mul_assoc] using hfit.of_le f2A
  have fp : Fits w (l.descriptors + (l.digits * l.digits * 2 + 2) * 3 * 2) := by
    simpa only [Layout.payloads, Layout.arrays, Layout.count, Layout.splits, pow_two,
      Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hfit.of_le fP
  have fac : Fits w ((l.digits * l.digits * 2 + 2) * 3 * (l.n + 1)) := by
    simpa only [Layout.capacity, Layout.arrays, Layout.count, Layout.splits, pow_two,
      Nat.mul_comm] using hfit.of_le fAC
  have fe : Fits w (l.descriptors + (l.digits * l.digits * 2 + 2) * 3 * 2 +
      (l.digits * l.digits * 2 + 2) * 3 * (l.n + 1)) := by
    simpa only [Layout.endpoint, Layout.pointer, Layout.payloads, Layout.capacity,
      Layout.arrays, Layout.count, Layout.splits, pow_two, Nat.mul_comm,
      Nat.mul_left_comm, Nat.mul_assoc] using hfit.of_le fE
  refine ⟨?y, ?run, ?_, ?_, ?_, ?_⟩
  case run => ram_eval [setup, hn, hΛ, hd, f0, f1, f2, f3, f4, f5', fn, fsq,
    fs, fd, fa, f2a, fp, fac, fe]
  · constructor
    all_goals simp +decide [Data.set_regs, hU, hn, hΛ, hk, hc, hlen, hd,
      Layout.splits, Layout.count, Layout.arrays, Layout.capacity, Layout.endpoint,
      Layout.pointer, Layout.payloads, pow_two, Nat.mul_comm, Nat.mul_assoc]
  · simp
  · simp +decide [Data.set_regs, Layout.pointer, Layout.payloads, Layout.arrays,
      Layout.count, Layout.splits, pow_two, Nat.mul_comm, Nat.mul_assoc]
  · rfl

/-- All compact arrays and six-word descriptors are produced by the complete native loop. -/
theorem loop_exec {w U : ℕ} (l : Layout) (rs : List (ℕ × ℕ)) (x : Data 48)
    (hr : Registers l U rs.length x) (hidx : x.regs current = 0)
    (hheap : x.regs heap = l.pointer 0) (hlen : rs.length ≤ l.n)
    (hk : Block.HoldsList (1 + 2 * l.n) (rs.map Prod.fst) x.mem)
    (hc : Block.HoldsList (1 + 3 * l.n) (rs.map Prod.snd) x.mem)
    (hkeys : ∀ p ∈ rs, p.1 ≤ 2 * U + 1 ∧ p.1 / 2 ≤ U)
    (hfit : Fits w (budget l U)) :
    ∃ y, ExecWithin w (.loop (.lt current arrays) body) x y
        (l.arrays * (43 * rs.length + 32) + 2) ∧
      Output l U rs y.mem ∧ y.regs current = l.arrays ∧ y.regs heap = l.endpoint ∧
      Registers l U rs.length y ∧
      Block.HoldsList (1 + 2 * l.n) (rs.map Prod.fst) y.mem ∧
      Block.HoldsList (1 + 3 * l.n) (rs.map Prod.snd) y.mem ∧
      Modifies (Block.mk l.descriptors (l.endpoint - l.descriptors)).footprint x.mem y.mem := by
  have hb := layout_bounds l U
  have he := hb.2.2.2.2.2.2.2.2.1
  have hlabel := hb.2.2.2.2.2.2.2.2.2.1
  have hsmall := hb.2.2.2.2.2.2.2.2.2.2
  have hbase : l.descriptors ≤ l.pointer 0 := by dsimp [Layout.pointer, Layout.payloads]; omega
  have hN : 1 + 4 * l.n ≤ l.endpoint := by
    dsimp only [Layout.endpoint, Layout.pointer, Layout.payloads, Layout.descriptors]
    omega
  let I (y : Data 48) : Prop :=
    Registers l U rs.length y ∧ y.regs current ≤ l.arrays ∧
    y.regs heap = l.pointer (y.regs current) ∧
    (∀ i < y.regs current,
      y.mem (l.descriptors + 2 * i) = (Math.array U l.digits rs i).length ∧
      y.mem (l.descriptors + 2 * i + 1) = l.pointer i ∧
      Block.HoldsList (l.pointer i) (Math.array U l.digits rs i) y.mem) ∧
    Block.HoldsList (1 + 2 * l.n) (rs.map Prod.fst) y.mem ∧
    Block.HoldsList (1 + 3 * l.n) (rs.map Prod.snd) y.mem ∧
    Modifies (Block.mk l.descriptors (l.endpoint - l.descriptors)).footprint x.mem y.mem
  have hbody (y : Data 48) (hy : I y) (ht : (Cond.lt current arrays).Holds y) :
      ∃ z, ExecWithin w body y z (43 * rs.length + 30) ∧ I z ∧
        l.arrays - z.regs current < l.arrays - y.regs current := by
    obtain ⟨hyr, hyidx, hyheap, hyout, hykeys, hycounts, hyframe⟩ := hy
    have hj : y.regs current < l.arrays := by
      simpa only [Cond.holds_lt, hyr.arrays] using ht
    have hnext : l.pointer (y.regs current + 1) ≤ l.endpoint :=
      l.pointer_mono (by omega)
    have hcur : l.pointer (y.regs current) ≤ l.endpoint := l.pointer_mono (by omega)
    have hcappos : 0 < l.capacity := by dsimp [Layout.capacity]; omega
    have hsource : 1 + 4 * l.n ≤ l.pointer (y.regs current) := by
      have := l.pointer_mono (i := 0) (j := y.regs current) (by omega)
      change l.descriptors ≤ _
      omega
    have hready : ScanReady w rs (y.set dst (y.regs heap)) := by
      constructor
      · simpa +decide using hyr.len
      · simpa +decide using hyr.constants
      · simpa +decide [hyr.keys] using hykeys
      · simpa +decide [hyr.counts] using hycounts
      · intro p hp
        exact hfit.of_le ((hkeys p hp).1.trans (by omega))
      · intro p hp
        simpa +decide [hyr.magnitude] using (hkeys p hp).2.trans (show U ≤ 2 * U by omega)
      · intro p hp
        exact hfit.of_le (show 2 * p.1 ≤ budget l U by have := (hkeys p hp).1; omega)
      · simpa +decide [hyr.magnitude] using hfit.of_le hlabel
      · exact hfit.of_le hsmall
      · simpa +decide [hyr.keys] using hfit.of_le
          (show 1 + 2 * l.n + rs.length ≤ budget l U by omega)
      · simpa +decide [hyr.counts] using hfit.of_le
          (show 1 + 3 * l.n + rs.length ≤ budget l U by omega)
      · simpa +decide [hyheap] using hfit.of_le
          (show l.pointer (y.regs current) + rs.length + 1 ≤ budget l U by
            rw [Layout.pointer_succ] at hnext
            dsimp only [Layout.capacity] at hnext
            omega)
      · simpa +decide [hyr.keys, hyheap] using
          (show 1 + 2 * l.n + rs.length ≤ l.pointer (y.regs current) by omega)
      · simpa +decide [hyr.counts, hyheap] using
          (show 1 + 3 * l.n + rs.length ≤ l.pointer (y.regs current) by omega)
    obtain ⟨z, hz, hzi, hzh, hzd0, hzd1, hzp, hzf⟩ := body_exec
      (j := y.regs current) y rs hready hyr.magnitude hyr.digits
      (by simpa only [Layout.splits] using hyr.splits) rfl
      (by rw [hyr.capacity]; dsimp [Layout.capacity]; omega)
      (by rw [hyr.descriptors, hyheap]; exact l.descriptor_before hj _)
      (hfit.of_le (by
        rw [hyr.descriptors]
        have := l.descriptor_before hj 0
        have hp0 : l.pointer 0 ≤ l.endpoint := l.pointer_mono (i := 0) (j := l.arrays) (by omega)
        omega))
      (by rw [hyheap, hyr.capacity, ← Layout.pointer_succ]; exact hfit.of_le (hnext.trans he))
      (hfit.of_le (by have := hb.2.2.2.2.1; omega))
    simp only [hyr.descriptors, hyheap, hyr.capacity] at hzd0 hzd1 hzp hzf hzh
    have hf (b : ℕ) (houtside : b < l.pointer (y.regs current) ∨
        l.pointer (y.regs current + 1) ≤ b)
        (hb0 : b ≠ l.descriptors + 2 * y.regs current)
        (hb1 : b ≠ l.descriptors + 2 * y.regs current + 1) : z.mem b = y.mem b := by
      apply hzf b _ hb0 hb1
      simpa only [Layout.pointer_succ] using houtside
    refine ⟨z, hz, ?_, by omega⟩
    refine ⟨hyr.transfer (fun i hi => hz.regs_eq hi), by omega, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hzi, Layout.pointer_succ]
      exact hzh
    · intro i hi
      by_cases hij : i = y.regs current
      · subst i
        exact ⟨hzd0, hzd1, hzp⟩
      · have hi' : i < y.regs current := by omega
        obtain ⟨h0, h1, hp⟩ := hyout i hi'
        have hbefore := l.descriptor_before (hi'.trans hj) (y.regs current)
        refine ⟨(hf _ (.inl (by omega)) (by omega) (by omega)).trans h0,
          (hf _ (.inl (by omega)) (by omega) (by omega)).trans h1, ?_⟩
        apply hp.frame
        intro b hlo hhi
        have hlen' := (Math.length_array_le U l.digits rs i).trans
          (show rs.length + 1 ≤ l.capacity by dsimp [Layout.capacity]; omega)
        have hptr := l.pointer_mono (show i + 1 ≤ y.regs current by omega)
        rw [Layout.pointer_succ] at hptr
        have htable := l.descriptor_before hj i
        exact hf b (.inl (by omega)) (by omega) (by omega)
    · apply hykeys.frame
      intro b hlo hhi
      simp only [List.length_map] at hhi
      exact hf b (.inl (by omega)) (by dsimp [Layout.descriptors]; omega)
        (by dsimp [Layout.descriptors]; omega)
    · apply hycounts.frame
      intro b hlo hhi
      simp only [List.length_map] at hhi
      exact hf b (.inl (by omega)) (by dsimp [Layout.descriptors]; omega)
        (by dsimp [Layout.descriptors]; omega)
    · intro b hnot
      have hb : b < l.descriptors ∨ l.endpoint ≤ b := by
        rw [Block.mem_footprint] at hnot
        dsimp only [Block.Owns] at hnot
        have := hbase.trans (l.pointer_mono (show 0 ≤ l.arrays by omega))
        omega
      have htable := l.descriptor_before hj (y.regs current)
      have hb0 : b ≠ l.descriptors + 2 * y.regs current := by omega
      have hb1 : b ≠ l.descriptors + 2 * y.regs current + 1 := by omega
      exact (hf b (by rcases hb with hb | hb <;> omega) hb0 hb1).trans (hyframe b hnot)
  have hx : I x := by
    refine ⟨hr, by rw [hidx]; omega, by simpa only [hidx] using hheap, ?_, hk, hc,
      Modifies.refl _ _⟩
    intro i hi
    rw [hidx] at hi
    omega
  obtain ⟨y, hy, hI, ht⟩ := ExecWithin.loop_invariant I
    (fun y => l.arrays - y.regs current) hbody hx
  obtain ⟨hyr, hyidx, hyheap, hyout, hykeys, hycounts, hyframe⟩ := hI
  have hend : y.regs current = l.arrays := by
    simp only [Cond.holds_lt, hyr.arrays] at ht
    omega
  refine ⟨y, ?_, ?_, hend, ?_, hyr, hykeys, hycounts, hyframe⟩
  · simpa only [hidx, Nat.sub_zero, Nat.mul_comm] using hy
  · intro j hj
    exact hyout j (by omega)
  · simpa only [hend, Layout.endpoint] using hyheap

/-- Complete array/descriptor construction, including all native constant and layout setup. -/
theorem exec {w U : ℕ} (l : Layout) (rs : List (ℕ × ℕ)) (x : Data 48)
    (hU : x.regs Select.magnitude = U) (hn : x.regs inputLen = l.n)
    (hΛ : x.regs digits = l.digits) (hkreg : x.regs Scan.keys = 1 + 2 * l.n)
    (hcreg : x.regs Scan.counts = 1 + 3 * l.n) (hlenreg : x.regs len = rs.length)
    (hd : x.regs descriptors = l.descriptors) (hlen : rs.length ≤ l.n)
    (hk : Block.HoldsList (1 + 2 * l.n) (rs.map Prod.fst) x.mem)
    (hc : Block.HoldsList (1 + 3 * l.n) (rs.map Prod.snd) x.mem)
    (hkeys : ∀ p ∈ rs, p.1 ≤ 2 * U + 1 ∧ p.1 / 2 ≤ U)
    (hfit : Fits w (budget l U)) :
    ∃ y, ExecWithin w program x y (l.arrays * (43 * rs.length + 32) + 21) ∧
      Output l U rs y.mem ∧ Registers l U rs.length y ∧ y.regs heap = l.endpoint ∧
      Block.HoldsList (1 + 2 * l.n) (rs.map Prod.fst) y.mem ∧
      Block.HoldsList (1 + 3 * l.n) (rs.map Prod.snd) y.mem ∧
      Modifies (Block.mk l.descriptors (l.endpoint - l.descriptors)).footprint x.mem y.mem := by
  obtain ⟨a, ha, har, hai, hah, ham⟩ := setup_exec l rs.length x hU hn hΛ hkreg hcreg
    hlenreg hd hfit
  obtain ⟨y, hy, hout, _, hyh, hyr, hykeys, hycounts, hyframe⟩ := loop_exec l rs a har hai hah
    hlen (by simpa only [ham] using hk) (by simpa only [ham] using hc) hkeys hfit
  exact ⟨y, (ha.seq hy).mono (by omega), hout, hyr, hyh, hykeys, hycounts,
    by simpa only [ham] using hyframe⟩

end Cslib.Algorithms.WordRAM.ThreeSum.Frontend.Arrays
