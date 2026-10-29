/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.RadixSort.Model
public import Complexity.Computability.WordRAM.ListArray

/-!
# Native stable digit-selection scan

The scan appends a stable digit-selected subsequence to a disjoint destination array. Both
orders of the two disjoint blocks are allowed, so consecutive radix passes can swap pointers.
All loads, address calculations, stores and loop control are native instructions.

## Main definitions

* `Scan.body`: read, test, conditionally append, and advance.
* `Scan.code`: reset the input cursor and scan the array.

## Main results

* `Scan.exec`: stable selection with a linear instruction bound and memory frame.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.RadixSort

open Cslib.WordRAM

/-- Array length. -/
abbrev len : Fin 16 := 0
/-- Source pointer; the sorter returns the final sorted pointer here. -/
abbrev src : Fin 16 := 1
/-- Scratch pointer. -/
abbrev dst : Fin 16 := 2
/-- Current bit index. -/
abbrev bit : Fin 16 := 3
/-- Digit selected by the current scan. -/
abbrev tag : Fin 16 := 4
/-- Constant one. -/
abbrev one : Fin 16 := 5
/-- Constant two. -/
abbrev two : Fin 16 := 6
/-- Input cursor. -/
abbrev idx : Fin 16 := 7
/-- Output cursor. -/
abbrev out : Fin 16 := 8
/-- Address temporary. -/
abbrev addr : Fin 16 := 9
/-- Loaded key. -/
abbrev value : Fin 16 := 10
/-- Current key digit. -/
abbrev keyDigit : Fin 16 := 11
/-- Number of key bits, supplied by the caller. -/
abbrev bits : Fin 16 := 12
/-- Temporary used to swap the two pointers. -/
abbrev swap : Fin 16 := 13

namespace Scan

/-- One stable-selection iteration, with every address and counter operation charged. -/
def body : Code .standard 16 := ram[
  addr ← src + idx; value ← *addr;
  keyDigit ← value >>> bit; keyDigit ← keyDigit % two;
  if keyDigit = tag then [ addr ← dst + out; *addr ← value; out ← out + one ]
    else [ addr ← addr ];
  idx ← idx + one ]

/-- Reset the input cursor, then perform one stable-selection scan. -/
def code : Code .standard 16 := ram[ idx ← #0; while idx < len do [ ⟪body⟫ ] ]

private theorem preserves_low (j : Fin 16) (hj : j.val ≤ 6) : body.Preserves j := by
  have hne (k : Fin 16) (hk : 7 ≤ k.val) : (some k : Option (Fin 16)) ≠ some j := by
    intro h
    have hv := congrArg Fin.val (Option.some.inj h)
    omega
  change (some addr ≠ some j) ∧ (some value ≠ some j) ∧
    (some keyDigit ≠ some j) ∧ (some keyDigit ≠ some j) ∧
    (((some addr ≠ some j) ∧ (none ≠ some j) ∧ (some out ≠ some j)) ∧
      (some addr ≠ some j)) ∧ (some idx ≠ some j)
  have hnone : (none : Option (Fin 16)) ≠ some j := by intro h; cases h
  exact ⟨hne addr (by decide), hne value (by decide), hne keyDigit (by decide),
    hne keyDigit (by decide),
    ⟨⟨hne addr (by decide), hnone, hne out (by decide)⟩,
      hne addr (by decide)⟩,
    hne idx (by decide)⟩

private theorem step {w : ℕ} (x : Data 16)
    (ho : x.regs one = 1) (ht : x.regs two = 2)
    (hs : Fits w (x.regs src + x.regs idx))
    (hd : Fits w (x.regs dst + x.regs out))
    (hi : Fits w (x.regs idx + 1))
    (hu : digit (x.regs bit) (x.mem (x.regs src + x.regs idx)) = x.regs tag →
      Fits w (x.regs out + 1))
    (hv : Fits w (x.mem (x.regs src + x.regs idx))) :
    ∃ y, ExecWithin w body x y 9 ∧
      y.regs idx = x.regs idx + 1 ∧
      y.regs out = x.regs out +
        (if digit (x.regs bit) (x.mem (x.regs src + x.regs idx)) = x.regs tag then 1 else 0) ∧
      y.mem = (if digit (x.regs bit) (x.mem (x.regs src + x.regs idx)) = x.regs tag then
        Function.update x.mem (x.regs dst + x.regs out) (x.mem (x.regs src + x.regs idx))
        else x.mem) := by
  have hshift := hv.of_le (Nat.shiftRight_le _ (x.regs bit))
  have hmod := hshift.of_le (Nat.mod_le _ 2)
  by_cases h : digit (x.regs bit) (x.mem (x.regs src + x.regs idx)) = x.regs tag
  · have heq : (x.mem (x.regs src + x.regs idx) >>> x.regs bit) % 2 = x.regs tag :=
      (digit_eq_shift _ _).symm.trans h
    have hinc := hu h
    have htagfit : Fits w (x.regs tag) := heq ▸ hmod
    refine ⟨?_, ?run, ?_, ?_, ?_⟩
    case run => ram_eval [body, ho, ht, hs, hd, hi, hinc, hshift, hmod, heq, htagfit]
    all_goals simp +decide [Data.set_regs, h]
  · have hne : (x.mem (x.regs src + x.regs idx) >>> x.regs bit) % 2 ≠ x.regs tag := by
      simpa only [← digit_eq_shift] using h
    refine ⟨?_, ?run, ?_, ?_, ?_⟩
    case run => ram_eval [body, ho, ht, hs, hd, hi, hshift, hmod, hne]
    all_goals simp +decide [Data.set_regs, h]

/-- Append a stable digit-selected subsequence in `11n+3` instructions. The destination has
capacity `n`; source and destination blocks are disjoint, in either order. The caller's existing
destination prefix is retained. Only destination cells may change. -/
theorem exec {w s d b t : ℕ} (xs acc : List ℕ) (x : Data 16)
    (hn : x.regs len = xs.length) (hs : x.regs src = s) (hd : x.regs dst = d)
    (hb : x.regs bit = b) (ht : x.regs tag = t)
    (ho : x.regs one = 1) (h2 : x.regs two = 2) (hout : x.regs out = acc.length)
    (hsrc : Block.HoldsList s xs x.mem) (hacc : Block.HoldsList d acc x.mem)
    (hwords : ∀ v ∈ xs, Fits w v)
    (hcap : (acc ++ select b t xs).length ≤ xs.length)
    (hdisj : s + xs.length ≤ d ∨ d + xs.length ≤ s)
    (hsfit : Fits w (s + xs.length)) (hdfit : Fits w (d + xs.length)) :
    ∃ y, ExecWithin w code x y (11 * xs.length + 3) ∧
      Block.HoldsList d (acc ++ select b t xs) y.mem ∧
      Block.HoldsList s xs y.mem ∧
      y.regs out = (acc ++ select b t xs).length ∧
      Modifies (Block.mk d xs.length).footprint x.mem y.mem := by
  let selected (i : ℕ) := acc ++ select b t (xs.take i)
  have hselected (i : ℕ) : (selected i).length ≤ xs.length := by
    have hsub : (select b t (xs.take i)).Sublist (select b t xs) :=
      (List.take_sublist i xs).filter _
    simp only [selected, List.length_append] at hcap ⊢
    have := hsub.length_le
    omega
  let I (y : Data 16) : Prop :=
    (∀ j : Fin 16, j.val ≤ 6 → y.regs j = x.regs j) ∧
    y.regs idx ≤ xs.length ∧ y.regs out = (selected (y.regs idx)).length ∧
    Block.HoldsList s xs y.mem ∧ Block.HoldsList d (selected (y.regs idx)) y.mem ∧
    Modifies (Block.mk d xs.length).footprint x.mem y.mem
  have hbody (y : Data 16) (hy : I y) (hc : (Cond.lt idx len).Holds y) :
      ∃ z, ExecWithin w body y z 9 ∧ I z ∧
        xs.length - z.regs idx < xs.length - y.regs idx := by
    obtain ⟨hr, hle, hu, hm, ha, hf⟩ := hy
    have hyl : y.regs len = xs.length := (hr len (by decide)).trans hn
    have hys : y.regs src = s := (hr src (by decide)).trans hs
    have hyd : y.regs dst = d := (hr dst (by decide)).trans hd
    have hyb : y.regs bit = b := (hr bit (by decide)).trans hb
    have hyt : y.regs tag = t := (hr tag (by decide)).trans ht
    have hyo : y.regs one = 1 := (hr one (by decide)).trans ho
    have hy2 : y.regs two = 2 := (hr two (by decide)).trans h2
    have hi : y.regs idx < xs.length := by simpa only [Cond.holds_lt, hyl] using hc
    have hread : y.mem (y.regs src + y.regs idx) = xs[y.regs idx] := by
      rw [hys]; exact hm.get _ hi
    have hv : Fits w (y.mem (y.regs src + y.regs idx)) := by
      rw [hread]; exact hwords _ (List.getElem_mem hi)
    have hsa : Fits w (y.regs src + y.regs idx) := by
      rw [hys]; exact hsfit.of_le (by omega)
    have hda : Fits w (y.regs dst + y.regs out) := by
      rw [hyd, hu]; exact hdfit.of_le (by have := hselected (y.regs idx); omega)
    have hic : Fits w (y.regs idx + 1) := hsfit.of_le (by omega)
    have hsuc : selected (y.regs idx + 1) = selected (y.regs idx) ++
        (if digit b xs[y.regs idx] = t then [xs[y.regs idx]] else []) := by
      dsimp only [selected]
      rw [List.take_succ_eq_append_getElem hi, select_append]
      simp only [select, List.filter_cons, List.filter_nil, decide_eq_true_eq]
      split_ifs <;> simp only [List.append_assoc, List.append_nil]
    by_cases heq : digit b xs[y.regs idx] = t
    · have hlt : y.regs out < xs.length := by
        have hlim := hselected (y.regs idx + 1)
        rw [hsuc, ite_eq_left heq, List.length_append, List.length_singleton] at hlim
        omega
      obtain ⟨z, he, hzi, hzu, hzm⟩ := step y hyo hy2 hsa hda hic
        (fun _ => hdfit.of_le (by omega)) hv
      rw [hyb, hread, hyt, ite_eq_left heq] at hzu hzm
      refine ⟨z, he, ?_, by omega⟩
      refine ⟨?_, by omega, ?_, ?_, ?_, ?_⟩
      · intro j hj
        exact (he.regs_eq (preserves_low j hj)).trans (hr j hj)
      · rw [hzi, hsuc, ite_eq_left heq, List.length_append, List.length_singleton]
        omega
      · apply hm.frame
        intro a hlo hhi
        rw [hzm, hyd, Function.update_of_ne (by rcases hdisj with h | h <;> omega)]
      · rw [hzi, hsuc, ite_eq_left heq, hzm, hyd, hu]
        exact ha.append_one _
      · intro a hnot
        have hne : a ≠ d + y.regs out := by
          intro heqa
          apply hnot
          apply Block.mem_footprint.mpr
          change d ≤ a ∧ a < d + xs.length
          omega
        rw [hzm, hyd, Function.update_of_ne hne]
        exact hf a hnot
    · obtain ⟨z, he, hzi, hzu, hzm⟩ := step y hyo hy2 hsa hda hic
        (by simpa only [hyb, hread, hyt] using fun h => (heq h).elim) hv
      rw [hyb, hread, hyt, ite_eq_right heq] at hzu hzm
      have hsel : selected (y.regs idx + 1) = selected (y.regs idx) := by
        rw [hsuc, ite_eq_right heq, List.append_nil]
      refine ⟨z, he, ?_, by omega⟩
      refine ⟨?_, by omega, ?_, ?_, ?_, ?_⟩
      · intro j hj
        exact (he.regs_eq (preserves_low j hj)).trans (hr j hj)
      · rw [hzi, hsel, hzu, Nat.add_zero, hu]
      · simpa only [hzm] using hm
      · simpa only [hzi, hsel, hzm] using ha
      · simpa only [hzm] using hf
  let x₀ := x.set idx 0
  have hx₀ : I x₀ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j hj
      have hne : j ≠ idx := by
        intro h
        have hv := congrArg Fin.val h
        change j.val = 7 at hv
        omega
      exact Function.update_of_ne hne _ _
    · simp [x₀]
    · simpa +decide [x₀, selected, select] using hout
    · exact hsrc
    · simpa [x₀, selected, select] using hacc
    · exact Modifies.refl _ _
  obtain ⟨y, he, hy, hc⟩ := ExecWithin.loop_invariant I
    (fun y => xs.length - y.regs idx) hbody hx₀
  obtain ⟨hr, hle, hu, hm, ha, hf⟩ := hy
  have hend : y.regs idx = xs.length := by
    have hyl : y.regs len = xs.length := (hr len (by decide)).trans hn
    simp only [Cond.holds_lt, hyl] at hc
    omega
  have hi := (ExecWithin.const (d := idx) (x := x) (fits_zero w)).seq he
  refine ⟨y, ?_, ?_, hm, ?_, hf⟩
  · convert hi using 1
    · rfl
    · simp only [x₀, Data.set_regs, Function.update_self, Nat.sub_zero]
      omega
  · simpa only [hend, selected, List.take_length] using ha
  · simpa only [hend, selected, List.take_length] using hu

end Scan
end Cslib.Algorithms.WordRAM.RadixSort
