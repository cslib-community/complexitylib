/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Child

/-!
# Actual empty-child transitions

## Main results

* `PrunedQuery.exec_node_emptyChild`: compute an empty child by real native scanning,
  advance the parent term, and preserve its request list and partial values.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM

/-- An empty-child transition may change the temporary child list, shared stamps and the
parent frame. Its first three frame words are also explicitly preserved below. -/
def emptyChildWrites (L f d : ℕ) : Finset ℕ :=
  (Block.mk (f + 4 * (L + 1) + (d + 1) * 10 ^ L) (10 ^ L)).footprint ∪
  (Block.mk (f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L) (10 ^ L)).footprint ∪
  (Block.mk (f + 4 * d) 4).footprint

/-- The program itself observes its computed zero child count and skips the recursive push.
Every scan, comparison, increment and stored counter is charged. -/
theorem exec_node_emptyChild {w L f a0 b0 d N k : ℕ} (x : Data registers)
    (hregs : KernelRegs L f a0 b0 x) (hd : x.regs level = d) (hdL : d < L)
    (hm : x.regs mode = 1)
    (hN : x.mem (f + 4 * d) = N) (hcap : N ≤ 10 ^ L)
    (hterm : x.mem (f + 4 * d + 3) = k) (hk : k < 10)
    (input : ℕ → ℕ)
    (hinput : ∀ i < N, x.mem (f + 4 * (L + 1) + d * 10 ^ L + i) = input i)
    (hcodes : ∀ i < N, input i < 10 ^ L)
    (hmarks : ∀ q < 10 ^ L,
      x.mem (f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L + q) ≤ x.regs epoch)
    (hempty : scanSet true k input N = ∅)
    (hw : Fits w (8 * f + 64 * (L + 1) * 10 ^ L + x.regs epoch + 128)) :
    ∃ y, ExecWithin w step x y (20 * N + 33) ∧ KernelRegs L f a0 b0 y ∧
      y.regs level = d ∧ y.regs mode = 1 ∧ y.regs active = x.regs active ∧
      y.regs epoch = x.regs epoch + 1 ∧
      ScanMemory y.mem (f + 4 * (L + 1) + (d + 1) * 10 ^ L)
        (f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L) (x.regs epoch + 1) (10 ^ L) ∅ ∧
      (∀ j < 3, y.mem (f + 4 * d + j) = x.mem (f + 4 * d + j)) ∧
      y.mem (f + 4 * d + 3) = k + 1 ∧
      Modifies (emptyChildWrites L f d) x.mem y.mem := by
  have hpow : 1 ≤ (10 : ℕ) ^ L := Nat.one_le_pow L _ (by decide)
  have hL : L + 1 ≤ (L + 1) * 10 ^ L := by nlinarith only [hpow]
  have hmul : (d + 1) * 10 ^ L ≤ (L + 1) * 10 ^ L :=
    Nat.mul_le_mul_right _ (by omega)
  obtain ⟨u, hu, humem, huf, huc, _, _, hut, hul, _, hun, huch, _, hureg⟩ :=
    exec_loadFrame x hregs.one_eq hregs.frameWidth_eq (hw.of_le (by
      rw [hregs.frames_eq, hregs.lists_eq, hregs.values_eq, hregs.span_eq, hd]
      nlinarith only [hpow, hL, hmul]))
  have fixed (i : Fin registers) (hi : ¬LoadFrameLocal i) : u.regs i = x.regs i :=
    hureg i hi
  have hul' : u.regs listBase = f + 4 * (L + 1) + d * 10 ^ L := by
    simpa only [hregs.lists_eq, hregs.span_eq, hd] using hul
  have huch' : u.regs childList = f + 4 * (L + 1) + (d + 1) * 10 ^ L := by
    simpa only [hregs.lists_eq, hregs.span_eq, hd] using huch
  have hus' : u.regs stamps = f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L :=
    (fixed stamps (by decide)).trans hregs.stamps_eq
  have huc' : u.regs count = N := by simpa only [hregs.frames_eq, hd, hN] using huc
  have hut' : u.regs term = k := by simpa only [hregs.frames_eq, hd, hterm] using hut
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
  have huf' : u.regs frame = f + 4 * d := by
    simpa only [hregs.frames_eq, hd] using huf
  have hvf : v.regs frame = f + 4 * d := (scanFixed frame (by decide)).trans huf'
  have hvt : v.regs term = k := (scanFixed term (by decide)).trans hut'
  have hv0 := (scanFixed nil (by decide)).trans ((fixed nil (by decide)).trans hregs.nil_eq)
  have hv1 := (scanFixed one (by decide)).trans ((fixed one (by decide)).trans hregs.one_eq)
  have hv4 := (scanFixed frameWidth (by decide)).trans
    ((fixed frameWidth (by decide)).trans hregs.frameWidth_eq)
  have hvc' : v.regs childCount = 0 := by
    simpa only [hut', hempty, Finset.card_empty] using hvc
  obtain ⟨y, hy, _, hym, hmem, _⟩ := exec_advance v hv1 hv4
    (hw.of_le (by rw [hvt]; omega)) (hw.of_le (by rw [hvf]; nlinarith only [hL, hdL]))
  have hcall : ExecWithin w dispatch u y (20 * N + 13) := by
    have hskip : ExecWithin w
        (ram[ if nil < childCount then [ ⟪push⟫ ] else [ ⟪advance⟫ ] ]) v y 7 :=
      hy.branch_neg (by simp only [Cond.holds_lt, hv0, hvc', lt_self_iff_false,
        not_false_eq_true])
    exact (hv.seq hskip).branch_pos
      (by simpa only [Cond.holds_lt, hut', (fixed ten (by decide)).trans hregs.ten_eq] using hk)
  have hum : u.regs mode = 1 := (fixed mode (by decide)).trans hm
  have hu0 := (fixed nil (by decide)).trans hregs.nil_eq
  have hu1 := (fixed one (by decide)).trans hregs.one_eq
  have hbranch : ExecWithin w
      (ram[ if mode = nil then [ ⟪enter⟫ ] else [
        if mode = one then [ ⟪dispatch⟫ ] else [ ⟪accumulate⟫ ] ] ]) u y (20 * N + 16) :=
    (hcall.branch_pos (by simp only [Cond.holds_eq, hum, hu1])).branch_neg
      (by simp only [Cond.holds_eq, hum, hu0]; decide)
  have he : ExecWithin w step x y (20 * N + 33) := (hu.seq hbranch).mono (by omega)
  have hmem' : y.mem = Function.update v.mem (f + 4 * d + 3) (k + 1) := by
    simpa only [hvf, hvt] using hmem
  have hframe : Modifies (Block.mk (f + 4 * d) 4).footprint v.mem y.mem := by
    rw [hmem']
    exact Modifies.write_of_owns (by constructor <;> omega) _
  have hlistAway (q : ℕ) : ¬(Block.mk (f + 4 * d) 4).Owns
      (f + 4 * (L + 1) + (d + 1) * 10 ^ L + q) := by
    change ¬(_ ≤ _ ∧ _ < f + 4 * d + 4)
    omega
  have hstampAway (q : ℕ) : ¬(Block.mk (f + 4 * d) 4).Owns
      (f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L + q) := by
    change ¬(_ ≤ _ ∧ _ < f + 4 * d + 4)
    omega
  have htable' : ScanMemory v.mem (f + 4 * (L + 1) + (d + 1) * 10 ^ L)
      (f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L) (x.regs epoch + 1) (10 ^ L) ∅ := by
    simpa only [huch', hus', hue, hut', hempty] using htable
  refine ⟨y, he, hregs.of_step he, ?_, hym, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hy.regs_eq (by decide : advance.Preserves level)).trans
      ((scanFixed level (by decide)).trans ((fixed level (by decide)).trans hd))
  · exact (hy.regs_eq (by decide : advance.Preserves active)).trans
      ((scanFixed active (by decide)).trans (fixed active (by decide)))
  · exact (hy.regs_eq (by decide : advance.Preserves epoch)).trans (by
      simpa only [hue] using hve)
  · exact htable'.congr
      (fun i _ => hframe _ (by simpa only [Block.mem_footprint] using hlistAway i))
      (fun q _ => hframe _ (by simpa only [Block.mem_footprint] using hstampAway q))
  · intro j hj
    rw [hmem', Function.update_of_ne (by omega : f + 4 * d + j ≠ f + 4 * d + 3),
      hscanFrame]
    · exact congrFun humem _
    · rw [huch']
      change ¬(f + 4 * (L + 1) + (d + 1) * 10 ^ L ≤ f + 4 * d + j ∧
        f + 4 * d + j < f + 4 * (L + 1) + (d + 1) * 10 ^ L + 10 ^ L)
      omega
    · rw [hus']
      change ¬(f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L ≤ f + 4 * d + j ∧
        f + 4 * d + j < f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L + 10 ^ L)
      omega
  · simp only [hmem', Function.update_self]
  · intro c hc
    have hn := Finset.notMem_union.mp hc
    have hs := Finset.notMem_union.mp hn.1
    rw [hframe c hn.2, hscanFrame]
    · exact congrFun humem c
    · simpa only [Block.mem_footprint, huch'] using hs.1
    · simpa only [Block.mem_footprint, hus'] using hs.2

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
