/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.RadixSort.Scan
public import Complexity.Computability.WordRAM.Compile

/-!
# Fixed-code native unsigned radix sorter

Two stable scans per bit partition the source into zeros followed by ones in scratch. Swapping
the pointers avoids a copy-back scan. Code and registers are independent of length and key width.
The source pointer on exit identifies the sorted array; the other block is scratch.

## Main definitions

* `pass`: two digit scans and pointer swap.
* `code`: the complete radix sorter with a register-supplied bit bound.
* `timeBound`: explicit instruction bound, excluding halt.

## Main results

* `exec`: complete charged sorting, with permutation, sortedness and a two-array frame.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.RadixSort

open Cslib.WordRAM

/-- Exchange source and scratch, then advance to the next bit. -/
def advance : Code .standard 16 := ram[
  swap ← src; src ← dst; dst ← swap; bit ← bit + one ]

/-- Exactly two stable scans per bit. -/
def pass : Code .standard 16 :=
  .seq (ram[ out ← #0; tag ← #0 ])
    (ram[ ⟪Scan.code⟫; tag ← #1; ⟪Scan.code⟫; ⟪advance⟫ ])

/-- Complete unsigned radix sorter. Parameters are length, two disjoint array bases, and bits.
The returned source register identifies the sorted block. -/
def code : Code .standard 16 :=
  .seq (ram[ one ← #1; two ← #2; bit ← #0 ]) (.loop (.lt bit bits) pass)

/-- All instructions of radix sorting, excluding a final halt. -/
def timeBound (n keyBits : ℕ) : ℕ := keyBits * (22 * n + 15) + 5

private theorem pass_exec {w b s d : ℕ} (xs : List ℕ) (x : Data 16)
    (hn : x.regs len = xs.length) (hs : x.regs src = s) (hd : x.regs dst = d)
    (hb : x.regs bit = b) (ho : x.regs one = 1) (h2 : x.regs two = 2)
    (hmem : Block.HoldsList s xs x.mem) (hwords : ∀ v ∈ xs, Fits w v)
    (hdisj : s + xs.length ≤ d ∨ d + xs.length ≤ s)
    (hsfit : Fits w (s + xs.length)) (hdfit : Fits w (d + xs.length))
    (hbit : Fits w (b + 1)) (h1 : Fits w 1) :
    ∃ y, ExecWithin w pass x y (22 * xs.length + 13) ∧
      Block.HoldsList d (partition b xs) y.mem ∧
      y.regs src = d ∧ y.regs dst = s ∧ y.regs bit = b + 1 ∧
      Modifies (Block.mk d xs.length).footprint x.mem y.mem := by
  let x₀ := (x.set out 0).set tag 0
  have hinit : ExecWithin (B := .standard) w (ram[ out ← #0; tag ← #0 ]) x x₀ 2 := by
    ram_eval [x₀]
  obtain ⟨y, hy, hym, hysrc, hyout, hyf⟩ := Scan.exec (t := 0) xs [] x₀
    (by simpa +decide [x₀] using hn) (by simpa +decide [x₀] using hs)
    (by simpa +decide [x₀] using hd) (by simpa +decide [x₀] using hb)
    (by simp [x₀]) (by simpa +decide [x₀] using ho)
    (by simpa +decide [x₀] using h2) (by simp +decide [x₀])
    hmem (Block.holdsList_nil _ _) hwords
    (by simpa using length_select_le b 0 xs) hdisj hsfit hdfit
  have hyr (j : Fin 16) (hj : Scan.code.Preserves j) : y.regs j = x₀.regs j :=
    hy.regs_eq hj
  let y₀ := y.set tag 1
  have hn₀ : y₀.regs len = xs.length := by
    simpa +decide [y₀, hyr len (by decide), x₀] using hn
  have hs₀ : y₀.regs src = s := by
    simpa +decide [y₀, hyr src (by decide), x₀] using hs
  have hd₀ : y₀.regs dst = d := by
    simpa +decide [y₀, hyr dst (by decide), x₀] using hd
  have hb₀ : y₀.regs bit = b := by
    simpa +decide [y₀, hyr bit (by decide), x₀] using hb
  have ho₀ : y₀.regs one = 1 := by
    simpa +decide [y₀, hyr one (by decide), x₀] using ho
  have h2₀ : y₀.regs two = 2 := by
    simpa +decide [y₀, hyr two (by decide), x₀] using h2
  obtain ⟨z, hz, hzm, _, _, hzf⟩ := Scan.exec (t := 1) xs (select b 0 xs) y₀
    hn₀ hs₀ hd₀ hb₀ (by simp [y₀]) ho₀ h2₀
    (by simpa +decide [y₀] using hyout) hysrc
    (by simpa only [y₀, Data.set_mem, List.nil_append] using hym) hwords
    (by rw [← partition, length_partition]) hdisj hsfit hdfit
  have hzs : z.regs src = s := (hz.regs_eq (by decide)).trans hs₀
  have hzd : z.regs dst = d := (hz.regs_eq (by decide)).trans hd₀
  have hzb : z.regs bit = b := (hz.regs_eq (by decide)).trans hb₀
  have hzo : z.regs one = 1 := (hz.regs_eq (by decide)).trans ho₀
  refine ⟨?u, ?run, ?_, ?_, ?_, ?_, ?_⟩
  case run =>
    have ha : ExecWithin w advance z ?u 4 := by
      ram_eval [advance, hzs, hzd, hzb, hzo, hbit]
    have hall := hinit.seq (hy.seq ((ExecWithin.const (d := tag) (x := y) h1).seq (hz.seq ha)))
    exact hall.mono (by omega)
  · exact hzm
  · simp +decide [Data.set_regs]
  · simp +decide [Data.set_regs]
  · simp +decide [Data.set_regs]
  · intro a hnot
    exact (hzf a hnot).trans (hyf a hnot)

/-- Sort all keys below `2^keyBits` in `keyBits * (22n+15)+5` instructions. The two arrays
have length `n`, are adjacent, and start at caller-supplied `base`. Only these `2n` cells may
change. The sorted block is returned in `src`; it is one of the two original blocks. This
includes empty lists and zero bit bounds. The key-bit bound and both one-past-end addresses
must fit; constant two must fit. No ordering contract is assumed. -/
theorem exec {w base keyBits : ℕ} (xs : List ℕ) (x : Data 16)
    (hn : x.regs len = xs.length) (hs : x.regs src = base)
    (hd : x.regs dst = base + xs.length) (hb : x.regs bits = keyBits)
    (hmem : Block.HoldsList base xs x.mem)
    (hkeys : ∀ v ∈ xs, v < 2 ^ keyBits)
    (hwords : ∀ v ∈ xs, Fits w v)
    (hfit : Fits w (base + 2 * xs.length)) (hbits : Fits w keyBits) (h2 : Fits w 2) :
    ∃ y, ExecWithin w code x y (timeBound xs.length keyBits) ∧
      Block.HoldsList (y.regs src) (passes keyBits xs) y.mem ∧
      (passes keyBits xs).Perm xs ∧ (passes keyBits xs).Pairwise (· ≤ ·) ∧
      (y.regs src = base ∨ y.regs src = base + xs.length) ∧
      Modifies (Block.mk base (2 * xs.length)).footprint x.mem y.mem := by
  let n := xs.length
  let I (y : Data 16) : Prop :=
    y.regs len = n ∧ y.regs bits = keyBits ∧ y.regs one = 1 ∧ y.regs two = 2 ∧
    y.regs bit ≤ keyBits ∧
    ((y.regs src = base ∧ y.regs dst = base + n) ∨
      (y.regs src = base + n ∧ y.regs dst = base)) ∧
    Block.HoldsList (y.regs src) (passes (y.regs bit) xs) y.mem ∧
    Modifies (Block.mk base (2 * n)).footprint x.mem y.mem
  have hbody (y : Data 16) (hy : I y) (hc : (Cond.lt bit bits).Holds y) :
      ∃ z, ExecWithin w pass y z (22 * n + 13) ∧ I z ∧
        keyBits - z.regs bit < keyBits - y.regs bit := by
    obtain ⟨hyn, hyB, hyo, hy2, hyb, hyp, hym, hyf⟩ := hy
    have hlt : y.regs bit < keyBits := by simpa only [Cond.holds_lt, hyB] using hc
    have hl : (passes (y.regs bit) xs).length = n := (passes_perm _ _).length_eq
    have hdis : y.regs src + n ≤ y.regs dst ∨ y.regs dst + n ≤ y.regs src := by
      rcases hyp with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> omega
    have hsf : Fits w (y.regs src + n) := hfit.of_le (by
      rcases hyp with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> omega)
    have hdf : Fits w (y.regs dst + n) := hfit.of_le (by
      rcases hyp with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> omega)
    have hwds : ∀ v ∈ passes (y.regs bit) xs, Fits w v := fun v hv =>
      hwords v ((passes_perm _ _).mem_iff.mp hv)
    obtain ⟨z, he, hzm, hzs, hzd, hzb, hzf⟩ := pass_exec (passes (y.regs bit) xs) y
      (hyn.trans hl.symm) rfl rfl rfl hyo hy2 hym hwds
      (by simpa only [hl] using hdis) (by simpa only [hl] using hsf)
      (by simpa only [hl] using hdf) (hbits.of_le (by omega)) (h2.of_le (by omega))
    refine ⟨z, by simpa only [hl] using he, ?_, by omega⟩
    refine ⟨(he.regs_eq (by decide)).trans hyn, (he.regs_eq (by decide)).trans hyB,
      (he.regs_eq (by decide)).trans hyo, (he.regs_eq (by decide)).trans hy2,
      by omega, ?_, ?_, ?_⟩
    · rw [hzs, hzd]
      rcases hyp with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact Or.inr ⟨hb, ha⟩
      · exact Or.inl ⟨hb, ha⟩
    · rw [hzs, hzb, passes]
      exact hzm
    · intro a hnot
      have hnot' : a ∉ (Block.mk (y.regs dst) (passes (y.regs bit) xs).length).footprint := by
        intro ha
        apply hnot
        rw [Block.mem_footprint] at ha ⊢
        change y.regs dst ≤ a ∧
          a < y.regs dst + (passes (y.regs bit) xs).length at ha
        change base ≤ a ∧ a < base + 2 * n
        rw [hl] at ha
        rcases hyp with ⟨ha', hb'⟩ | ⟨ha', hb'⟩ <;> omega
      exact (hzf a hnot').trans (hyf a hnot)
  let x₀ := ((x.set one 1).set two 2).set bit 0
  have hx₀ : I x₀ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, Modifies.refl _ _⟩
    · simpa +decide [x₀] using hn
    · simpa +decide [x₀] using hb
    · simp +decide [x₀]
    · simp +decide [x₀]
    · simp [x₀]
    · left; simpa +decide [x₀, n] using And.intro hs hd
    · simpa +decide [x₀, passes, hs] using hmem
  obtain ⟨y, he, hy, hc⟩ := ExecWithin.loop_invariant I
    (fun y => keyBits - y.regs bit) hbody hx₀
  obtain ⟨hyn, hyB, hyo, hy2, hyb, hyp, hym, hyf⟩ := hy
  have hend : y.regs bit = keyBits := by
    simp only [Cond.holds_lt, hyB] at hc
    omega
  have hinit : ExecWithin (B := .standard) w (ram[ one ← #1; two ← #2; bit ← #0 ]) x x₀ 3 := by
    ram_eval [x₀, h2, h2.of_le (show 1 ≤ 2 by omega)]
  refine ⟨y, ?_, by simpa only [hend] using hym,
    (passes_correct keyBits xs hkeys).1, (passes_correct keyBits xs hkeys).2,
    hyp.imp And.left And.left, hyf⟩
  have hall := hinit.seq he
  convert hall using 1
  · rfl
  · simp +decide only [timeBound, n, x₀, Data.set_regs, Function.update_apply,
      ↓reduceIte, Nat.sub_zero, Nat.add_assoc, Nat.reduceAdd]
    omega

end Cslib.Algorithms.WordRAM.RadixSort
