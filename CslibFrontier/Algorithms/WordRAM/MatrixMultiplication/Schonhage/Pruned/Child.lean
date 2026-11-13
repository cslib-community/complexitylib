/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Node
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Scan
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Push

/-!
# Computed nonempty-child transitions of the native controller

## Main results

* `PrunedQuery.exec_node_child`: read the actual frame and requests, construct the child by
  native digit tests/division/deduplication, and push its computed frame.

The nonemptiness premise selects a case of the proof. The machine itself tests the count
that it has just computed; no query-selection or layout certificate is input to its code.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM

/-- Only the next query row, timestamps and the next four-word frame may change during a
nonempty-child transition. In particular, parent queries, accumulators and frame survive. -/
def childWrites (L f d : ℕ) : Finset ℕ :=
  (Block.mk (f + 4 * (L + 1) + (d + 1) * 10 ^ L) (10 ^ L)).footprint ∪
  (Block.mk (f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L) (10 ^ L)).footprint ∪
  (Block.mk (f + 4 * (d + 1)) 4).footprint

/-- Load the current frame, execute the native child scan, and package the post-scan state `v`
together with the branch-dispatch wrapper that turns a `push`/`advance` branch execution on `v`
into a full `step` execution on `x`. -/
theorem exec_loadScanChild {w L f a0 b0 d N k : ℕ} (x : Data registers)
    (hregs : KernelRegs L f a0 b0 x) (hd : x.regs level = d) (hdL : d < L)
    (hm : x.regs mode = 1)
    (hN : x.mem (f + 4 * d) = N) (hcap : N ≤ 10 ^ L)
    (hterm : x.mem (f + 4 * d + 3) = k) (hk : k < 10)
    (input : ℕ → ℕ)
    (hinput : ∀ i < N, x.mem (f + 4 * (L + 1) + d * 10 ^ L + i) = input i)
    (hcodes : ∀ i < N, input i < 10 ^ L)
    (hmarks : ∀ q < 10 ^ L,
      x.mem (f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L + q) ≤ x.regs epoch)
    (hw : Fits w (8 * f + 64 * (L + 1) * 10 ^ L + x.regs epoch + 128)) :
    ∃ v,
      (∀ {y T}, ExecWithin w
          (ram[ if nil < childCount then [ ⟪push⟫ ] else [ ⟪advance⟫ ] ]) v y T →
        ExecWithin w step x y (20 * N + T + 26)) ∧
      v.regs frames = f ∧ v.regs frame = f + 4 * d ∧ v.regs level = d ∧
      v.regs nextLevel = d + 1 ∧ v.regs leafPrefix = x.mem (f + 4 * d + 1) ∧
      v.regs stride = x.mem (f + 4 * d + 2) ∧ v.regs term = k ∧
      v.regs active = x.regs active ∧ v.regs epoch = x.regs epoch + 1 ∧
      v.regs nil = 0 ∧ v.regs one = 1 ∧ v.regs frameWidth = 4 ∧ v.regs ten = 10 ∧
      v.regs childCount = (scanSet true k input N).card ∧
      ScanMemory v.mem (f + 4 * (L + 1) + (d + 1) * 10 ^ L)
        (f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L) (x.regs epoch + 1) (10 ^ L)
        (scanSet true k input N) ∧
      Modifies ((Block.mk (f + 4 * (L + 1) + (d + 1) * 10 ^ L) (10 ^ L)).footprint ∪
        (Block.mk (f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L) (10 ^ L)).footprint)
        x.mem v.mem := by
  have hpow : 1 ≤ (10 : ℕ) ^ L := Nat.one_le_pow L _ (by decide)
  have hL : L + 1 ≤ (L + 1) * 10 ^ L := by nlinarith only [hpow]
  have hmul : (d + 1) * 10 ^ L ≤ (L + 1) * 10 ^ L :=
    Nat.mul_le_mul_right _ (by omega)
  obtain ⟨u, hu, humem, huf', huc, hup', hstride', hut, hul', _, hun', huch', _, hureg⟩ :=
    hregs.exec_loadFrame hd hdL.le (hw.of_le (by omega))
  have fixed (i : Fin registers) (hi : ¬LoadFrameLocal i) : u.regs i = x.regs i :=
    hureg i hi
  have hus' : u.regs stamps = f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L :=
    (fixed stamps (by decide)).trans hregs.stamps_eq
  have huc' : u.regs count = N := huc.trans hN
  have hut' : u.regs term = k := hut.trans hterm
  have hue : u.regs epoch = x.regs epoch := fixed epoch (by decide)
  obtain ⟨v, hv, _, hve, hvc, htable, _, hscanFrame, hvreg⟩ :=
    exec_scan (N := N) (capacity := 10 ^ L) true u input huc'
      (by simpa only [hul', humem] using hinput)
      (fun i hi => (Nat.div_le_self _ _).trans_lt (hcodes i hi))
      (Or.inl (by rw [huch', hus']; nlinarith only [hmul, hpow]))
      (Or.inl (by rw [hul', huch']; nlinarith only [hcap]))
      (Or.inl (by rw [hul', hus']; nlinarith only [hcap, hmul, hpow]))
      (by simpa only [hus', humem, hue] using hmarks)
      ((fixed one (by decide)).trans hregs.one_eq)
      ((fixed ten (by decide)).trans hregs.ten_eq)
      ((fixed nine (by decide)).trans hregs.nine_eq)
      (hw.of_le (by
        rw [hul', huch', hus', hue]
        nlinarith only [hcap, hmul, hpow, hL]))
  have scanFixed (i : Fin registers) (hi : ¬ScanLocal i) : v.regs i = u.regs i := hvreg i hi
  refine ⟨v, ?_,
    (scanFixed frames (by decide)).trans ((fixed frames (by decide)).trans hregs.frames_eq),
    (scanFixed frame (by decide)).trans huf',
    (scanFixed level (by decide)).trans ((fixed level (by decide)).trans hd),
    (scanFixed nextLevel (by decide)).trans hun',
    (scanFixed leafPrefix (by decide)).trans hup',
    (scanFixed stride (by decide)).trans hstride',
    (scanFixed term (by decide)).trans hut',
    (scanFixed active (by decide)).trans (fixed active (by decide)),
    by simpa only [hue] using hve,
    (scanFixed nil (by decide)).trans ((fixed nil (by decide)).trans hregs.nil_eq),
    (scanFixed one (by decide)).trans ((fixed one (by decide)).trans hregs.one_eq),
    (scanFixed frameWidth (by decide)).trans
      ((fixed frameWidth (by decide)).trans hregs.frameWidth_eq),
    (scanFixed ten (by decide)).trans ((fixed ten (by decide)).trans hregs.ten_eq),
    by simpa only [hut'] using hvc,
    by simpa only [huch', hus', hue, hut'] using htable, ?_⟩
  · intro y T htail
    have hcall : ExecWithin w dispatch u y (20 * N + 5 + T + 1) :=
      (hv.seq htail).branch_pos
        (by simpa only [Cond.holds_lt, hut', (fixed ten (by decide)).trans hregs.ten_eq] using hk)
    have hum : u.regs mode = 1 := (fixed mode (by decide)).trans hm
    have hu0 := (fixed nil (by decide)).trans hregs.nil_eq
    have hu1 := (fixed one (by decide)).trans hregs.one_eq
    have hbranch : ExecWithin w
        (ram[ if mode = nil then [ ⟪enter⟫ ] else [
          if mode = one then [ ⟪dispatch⟫ ] else [ ⟪accumulate⟫ ] ] ]) u y (20 * N + 5 + T + 4) :=
      (hcall.branch_pos (by simp only [Cond.holds_eq, hum, hu1])).branch_neg
        (by simp only [Cond.holds_eq, hum, hu0]; decide)
    exact (hu.seq hbranch).mono (by omega)
  · intro c hc
    obtain ⟨h1, h2⟩ := Finset.notMem_union.mp hc
    rw [hscanFrame c (by simpa only [Block.mem_footprint, huch'] using h1)
      (by simpa only [Block.mem_footprint, hus'] using h2)]
    exact congrFun humem c

/-- Any four-word frame write below `f + 4 * (L + 1)` preserves the scanned child-list and stamp
blocks and composes with the scan footprint. -/
theorem postScan_memory {L f d E g : ℕ} {S : Finset ℕ} {μ₀ μ ν : ℕ → ℕ}
    (htable : ScanMemory μ (f + 4 * (L + 1) + (d + 1) * 10 ^ L)
      (f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L) E (10 ^ L) S)
    (hscan : Modifies ((Block.mk (f + 4 * (L + 1) + (d + 1) * 10 ^ L) (10 ^ L)).footprint ∪
      (Block.mk (f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L) (10 ^ L)).footprint) μ₀ μ)
    (hframe : Modifies (Block.mk g 4).footprint μ ν)
    (hg : g + 4 ≤ f + 4 * (L + 1)) :
    ScanMemory ν (f + 4 * (L + 1) + (d + 1) * 10 ^ L)
      (f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L) E (10 ^ L) S ∧
    Modifies ((Block.mk (f + 4 * (L + 1) + (d + 1) * 10 ^ L) (10 ^ L)).footprint ∪
      (Block.mk (f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L) (10 ^ L)).footprint ∪
      (Block.mk g 4).footprint) μ₀ ν ∧
    ∀ a < f + 4 * (L + 1), μ a = μ₀ a := by
  have hlistAway (q : ℕ) : ¬(Block.mk g 4).Owns
      (f + 4 * (L + 1) + (d + 1) * 10 ^ L + q) := by
    change ¬(g ≤ _ ∧ _ < g + 4)
    omega
  have hstampAway (q : ℕ) : ¬(Block.mk g 4).Owns
      (f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L + q) := by
    change ¬(g ≤ _ ∧ _ < g + 4)
    omega
  refine ⟨htable.congr
      (fun i _ => hframe _ (by simpa only [Block.mem_footprint] using hlistAway i))
      (fun q _ => hframe _ (by simpa only [Block.mem_footprint] using hstampAway q)),
    fun c hc => ?_, fun a ha => hscan a ?_⟩
  · have hn := Finset.notMem_union.mp hc
    exact (hframe c hn.2).trans (hscan c hn.1)
  · simp only [Finset.mem_union, Block.mem_footprint, Block.Owns]
    omega

/-- This is the actual full controller transition, not a callee execution assumption. All
three controller comparisons, the complete native scan, four frame stores and index work
fit in `20 N + 42` instructions. The produced directory describes the same final memory. -/
theorem exec_node_child {w L f a0 b0 d N p k : ℕ} (x : Data registers)
    (hregs : KernelRegs L f a0 b0 x) (hd : x.regs level = d) (hdL : d < L)
    (hm : x.regs mode = 1)
    (hN : x.mem (f + 4 * d) = N) (hcap : N ≤ 10 ^ L)
    (hpref : x.mem (f + 4 * d + 1) = p) (hp : p < 10 ^ d)
    (hstride : x.mem (f + 4 * d + 2) = 10 ^ d)
    (hterm : x.mem (f + 4 * d + 3) = k) (hk : k < 10)
    (input : ℕ → ℕ)
    (hinput : ∀ i < N, x.mem (f + 4 * (L + 1) + d * 10 ^ L + i) = input i)
    (hcodes : ∀ i < N, input i < 10 ^ L)
    (hmarks : ∀ q < 10 ^ L,
      x.mem (f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L + q) ≤ x.regs epoch)
    (hne : (scanSet true k input N).Nonempty)
    (hw : Fits w (8 * f + 64 * (L + 1) * 10 ^ L + x.regs epoch + 128)) :
    ∃ y, ExecWithin w step x y (20 * N + 42) ∧ KernelRegs L f a0 b0 y ∧
      y.regs level = d + 1 ∧ y.regs mode = 0 ∧ y.regs active = x.regs active ∧
      y.regs epoch = x.regs epoch + 1 ∧
      ScanMemory y.mem (f + 4 * (L + 1) + (d + 1) * 10 ^ L)
        (f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L) (x.regs epoch + 1) (10 ^ L)
        (scanSet true k input N) ∧
      y.mem (f + 4 * (d + 1)) = (scanSet true k input N).card ∧
      y.mem (f + 4 * (d + 1) + 1) = p + k * 10 ^ d ∧
      y.mem (f + 4 * (d + 1) + 2) = 10 ^ (d + 1) ∧
      y.mem (f + 4 * (d + 1) + 3) = 0 ∧
      Modifies (childWrites L f d) x.mem y.mem := by
  have hpow : 1 ≤ (10 : ℕ) ^ L := Nat.one_le_pow L _ (by decide)
  have hL : L + 1 ≤ (L + 1) * 10 ^ L := by nlinarith only [hpow]
  have hmul : (d + 1) * 10 ^ L ≤ (L + 1) * 10 ^ L :=
    Nat.mul_le_mul_right _ (by omega)
  have hnext : (10 : ℕ) ^ d * 10 ≤ 10 ^ L := by
    simpa only [← pow_succ] using
      Nat.pow_le_pow_right (by decide : 1 ≤ (10 : ℕ)) (by omega : d + 1 ≤ L)
  have hnewp : p + k * 10 ^ d < 10 ^ L := by nlinarith only [hp, hk, hnext]
  obtain ⟨v, hstep, hvf, _, _, hvn, hvp, hvst, hvt, hva, hve,
      hv0, hv1, hv4, hv10, hvc', htable', hscanMod⟩ :=
    exec_loadScanChild x hregs hd hdL hm hN hcap hterm hk input hinput hcodes hmarks hw
  rw [hpref] at hvp
  rw [hstride] at hvst
  obtain ⟨y, hy, hyl, hym, _, _, _, hmem, hpushFrame, _⟩ := exec_push v hv0 hv1 hv4 hv10
    (hw.of_le (by
      rw [hvf, hvn, hvp, hvst, hvt]
      nlinarith only [hcap, hpow, hL, hmul, hnext, hnewp]))
  have hnonempty : (Cond.lt nil childCount).Holds v := by
    simpa only [Cond.holds_lt, hv0, hvc'] using Finset.card_pos.mpr hne
  have he : ExecWithin w step x y (20 * N + 42) :=
    (hstep (hy.branch_pos hnonempty)).mono (by omega)
  have hfbase : v.regs frames + v.regs nextLevel * 4 = f + 4 * (d + 1) := by
    rw [hvf, hvn]
    omega
  have hchildFrame : Modifies (Block.mk (f + 4 * (d + 1)) 4).footprint v.mem y.mem := by
    simpa only [hfbase] using hpushFrame
  obtain ⟨hymem, hymod, _⟩ := postScan_memory htable' hscanMod hchildFrame (by omega)
  refine ⟨y, he, hregs.of_step he, hyl.trans hvn, hym,
    (hy.regs_eq (by decide : push.Preserves active)).trans hva,
    (hy.regs_eq (by decide : push.Preserves epoch)).trans hve,
    hymem, ?_, ?_, ?_, ?_, hymod⟩
  · rw [hmem, hfbase, hvc']
    simp
  · rw [hmem, hfbase, hvp, hvt, hvst]
    simp
  · rw [hmem, hfbase, hvst]
    simp [pow_succ]
  · rw [hmem, hfbase]
    simp

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
