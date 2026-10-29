/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Node
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Accumulate

/-!
# The actual controller phase after a child returns

## Main results

* `PrunedQuery.exec_node_return`: load the parent frame, add the returned child only at
  contributing requests, and advance the stored term counter.

The value-directory hypotheses describe ordinary memory established by the child proof.
They do not assume a child execution or its cost. All native accumulation and controller
instructions are proved and charged here.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM Cslib.WordRAM.Signed Finset

/-- The complete parent-return phase, including its real frame loads, two mode comparisons,
signed indexed-add loop and stored counter increment. Unselected child cells are not read. -/
theorem exec_node_return {w L f a0 b0 d N k : ℕ} (x : Data registers)
    (hregs : KernelRegs L f a0 b0 x) (hd : x.regs level = d) (hdL : d < L)
    (hm : x.regs mode = 2) (hN : x.mem (f + 4 * d) = N) (hcap : N ≤ 10 ^ L)
    (hterm : x.mem (f + 4 * d + 3) = k) (hk : k < 10)
    (input : ℕ → ℕ) (V B : ℕ → ℤ)
    (hinput : ∀ i < N, x.mem (f + 4 * (L + 1) + d * 10 ^ L + i) = input i)
    (hcodes : ∀ i < N, input i < 10 ^ L) (hinj : Set.InjOn input {i | i < N})
    (hparent : ∀ i < N,
      x.mem (f + 4 * (L + 1) + (L + 1) * 10 ^ L + d * 10 ^ L + input i) =
        encode (V (input i)))
    (hchild : ∀ i < N, selected true k (input i) →
      x.mem (f + 4 * (L + 1) + (L + 1) * 10 ^ L + (d + 1) * 10 ^ L + input i / 10) =
        encode (B (input i / 10)))
    (hV : ∀ i < N, GenericRAM.Signed.Fits w (V (input i)))
    (hB : ∀ i < N, GenericRAM.Signed.Fits w (B (input i / 10)))
    (hw : Fits (w + 2) (8 * f + 64 * (L + 1) * 10 ^ L + 128)) :
    ∃ y, ExecWithin (w + 2) step x y (31 * N + 29) ∧ KernelRegs L f a0 b0 y ∧
      y.regs level = d ∧ y.regs mode = 1 ∧ y.regs active = x.regs active ∧
      y.regs epoch = x.regs epoch ∧
      (∀ i < N,
        y.mem (f + 4 * (L + 1) + (L + 1) * 10 ^ L + d * 10 ^ L + input i) =
          encode (V (input i) + if selected true k (input i) then B (input i / 10) else 0)) ∧
      (∀ j < 3, y.mem (f + 4 * d + j) = x.mem (f + 4 * d + j)) ∧
      y.mem (f + 4 * d + 3) = k + 1 ∧
      (∀ q < 10 ^ L,
        y.mem (f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L + q) =
          x.mem (f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L + q)) ∧
      Modifies (nodeWrites L f d) x.mem y.mem := by
  have hpow : 1 ≤ (10 : ℕ) ^ L := Nat.one_le_pow L _ (by decide)
  have hL : L + 1 ≤ (L + 1) * 10 ^ L := by nlinarith only [hpow]
  have hmul : (d + 1) * 10 ^ L ≤ (L + 1) * 10 ^ L :=
    Nat.mul_le_mul_right _ (by omega)
  obtain ⟨u, hu, humem, huf, huc, _, _, hut, hul, huv, _, _, huch, hureg⟩ :=
    exec_loadFrame x hregs.one_eq hregs.frameWidth_eq (hw.of_le (by
      rw [hregs.frames_eq, hregs.lists_eq, hregs.values_eq, hregs.span_eq, hd]
      nlinarith only [hpow, hL, hmul]))
  have fixed (i : Fin registers) (hi : ¬LoadFrameLocal i) : u.regs i = x.regs i :=
    hureg i hi
  have huf' : u.regs frame = f + 4 * d := by simpa only [hregs.frames_eq, hd] using huf
  have hul' : u.regs listBase = f + 4 * (L + 1) + d * 10 ^ L := by
    simpa only [hregs.lists_eq, hregs.span_eq, hd] using hul
  let vb := f + 4 * (L + 1) + (L + 1) * 10 ^ L + d * 10 ^ L
  have huv' : u.regs valueBase = vb := by
    simpa only [hregs.values_eq, hregs.span_eq, hd] using huv
  have huch' : u.regs childValues = f + 4 * (L + 1) + (L + 1) * 10 ^ L +
      (d + 1) * 10 ^ L := by
    simpa only [hregs.values_eq, hregs.span_eq, hd] using huch
  have huc' : u.regs count = N := by simpa only [hregs.frames_eq, hd, hN] using huc
  have hut' : u.regs term = k := by simpa only [hregs.frames_eq, hd, hterm] using hut
  obtain ⟨v, hv, _, hvmem, hvFrame, _, hvreg⟩ := exec_accumulateLoop u input V B huc'
    (by simpa only [hul', humem] using hinput) hcodes hinj
    (by simpa only [huv', humem] using hparent)
    (by simpa only [huch', humem, hut'] using hchild) hV hB
    (Or.inl (by rw [hul', huv']; dsimp [vb]; nlinarith only [hcap, hpow]))
    (Or.inl (by rw [huv', huch']; dsimp [vb]; nlinarith only []))
    ((fixed one (by decide)).trans hregs.one_eq)
    ((fixed nine (by decide)).trans hregs.nine_eq)
    ((fixed ten (by decide)).trans hregs.ten_eq)
    (hw.of_le (by
      rw [hul', huv', huch']
      dsimp [vb]
      nlinarith only [hcap, hpow, hmul, hL]))
  have hvf : v.regs frame = f + 4 * d := (hvreg frame (by decide)).trans huf'
  have hvt : v.regs term = k := (hvreg term (by decide)).trans hut'
  obtain ⟨y, hy, _, hym, hymem, _⟩ := exec_advance v
    ((hvreg one (by decide)).trans ((fixed one (by decide)).trans hregs.one_eq))
    ((hvreg frameWidth (by decide)).trans
      ((fixed frameWidth (by decide)).trans hregs.frameWidth_eq))
    (hw.of_le (by rw [hvt]; omega)) (hw.of_le (by rw [hvf]; nlinarith only [hL, hdL]))
  have hacc : ExecWithin (w + 2) accumulate u y (31 * N + 8) := (hv.seq hy).mono (by omega)
  have hum : u.regs mode = 2 := (fixed mode (by decide)).trans hm
  have hu0 := (fixed nil (by decide)).trans hregs.nil_eq
  have hu1 := (fixed one (by decide)).trans hregs.one_eq
  have hbranch : ExecWithin (w + 2)
      (ram[ if mode = nil then [ ⟪enter⟫ ] else [
        if mode = one then [ ⟪dispatch⟫ ] else [ ⟪accumulate⟫ ] ] ]) u y (31 * N + 12) :=
    (hacc.branch_neg (by simp only [Cond.holds_eq, hum, hu1]; decide)).branch_neg
      (by simp only [Cond.holds_eq, hum, hu0]; decide)
  have he : ExecWithin (w + 2) step x y (31 * N + 29) := (hu.seq hbranch).mono (by omega)
  let written := ((range N).filter fun i => selected true k (input i)).image
    fun i => vb + input i
  have hvmem' : v.mem = written.piecewise
      (fun a => encode (V (a - vb) + B ((a - vb) / 10))) x.mem := by
    rw [huv', hut', humem] at hvmem
    exact hvmem
  have hyframe : Modifies (Block.mk (f + 4 * d) 4).footprint v.mem y.mem := by
    rw [hymem, hvf]
    exact Modifies.write_of_owns (by constructor <;> omega) _
  have hvframe : Modifies (Block.mk vb (10 ^ L)).footprint x.mem v.mem := by
    simpa only [huv', humem] using hvFrame
  have frameBeforeValue : f + 4 * d + 4 ≤ vb := by dsimp [vb]; omega
  refine ⟨y, he, hregs.of_step he, ?_, hym, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hy.regs_eq (by decide : advance.Preserves level)).trans
      ((hvreg level (by decide)).trans ((fixed level (by decide)).trans hd))
  · exact (hy.regs_eq (by decide : advance.Preserves active)).trans
      ((hvreg active (by decide)).trans (fixed active (by decide)))
  · exact (hy.regs_eq (by decide : advance.Preserves epoch)).trans
      ((hvreg epoch (by decide)).trans (fixed epoch (by decide)))
  · intro i hi
    change y.mem (vb + input i) = _
    have haway : ¬(Block.mk (f + 4 * d) 4).Owns (vb + input i) := by
      change ¬(_ ≤ _ ∧ _ < f + 4 * d + 4)
      omega
    rw [hyframe _ (by simpa only [Block.mem_footprint] using haway), hvmem']
    by_cases hsel : selected true k (input i)
    · have hmem : vb + input i ∈ written := mem_image.mpr
        ⟨i, mem_filter.mpr ⟨mem_range.mpr hi, hsel⟩, rfl⟩
      simp only [piecewise, hmem, hsel, ↓reduceIte, Nat.add_sub_cancel_left]
    · have hmem : vb + input i ∉ written := by
        rintro h
        obtain ⟨j, hj, hji⟩ := mem_image.mp h
        have heq : input j = input i := Nat.add_left_cancel hji
        exact hsel (heq ▸ (mem_filter.mp hj).2)
      simpa only [piecewise, hmem, hsel, ↓reduceIte, add_zero] using hparent i hi
  · intro j hj
    rw [hymem, hvf, Function.update_of_ne (by omega : f + 4 * d + j ≠ f + 4 * d + 3)]
    apply hvframe
    rw [Block.mem_footprint]
    change ¬(vb ≤ f + 4 * d + j ∧ _)
    omega
  · simp only [hymem, hvf, hvt, Function.update_self]
  · intro q _
    have hafter : vb + 10 ^ L ≤
        f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L + q := by
      dsimp only [vb]
      nlinarith only [hmul]
    have hf : f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L + q ∉
        (Block.mk (f + 4 * d) 4).footprint := by
      rw [Block.mem_footprint]
      dsimp only [Block.Owns]
      omega
    have hvf : f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L + q ∉
        (Block.mk vb (10 ^ L)).footprint := by
      rw [Block.mem_footprint]
      dsimp only [Block.Owns]
      omega
    exact (hyframe _ hf).trans (hvframe _ hvf)
  · intro c hc
    have hnotFrame : c ∉ (Block.mk (f + 4 * d) 4).footprint := by
      intro hf
      apply hc
      apply mem_union_left
      apply mem_union_left
      apply mem_union_left
      rw [Block.mem_footprint] at hf ⊢
      change f + 4 * d ≤ c ∧ c < f + 4 * d + 4 * (L + 1 - d)
      change f + 4 * d ≤ c ∧ c < f + 4 * d + 4 at hf
      have hrem : 1 ≤ L + 1 - d := by omega
      omega
    have hnotValue : c ∉ (Block.mk vb (10 ^ L)).footprint := by
      intro hc'
      apply hc
      apply mem_union_left
      apply mem_union_right
      rw [Block.mem_footprint] at hc' ⊢
      change vb ≤ c ∧ c < vb + (L + 1 - d) * 10 ^ L
      change vb ≤ c ∧ c < vb + 10 ^ L at hc'
      have hrem : 1 ≤ L + 1 - d := by omega
      have hlen := Nat.mul_le_mul_right (10 ^ L) hrem
      exact ⟨hc'.1, by omega⟩
    exact (hyframe c hnotFrame).trans (hvframe c hnotValue)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
