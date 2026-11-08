/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORNativeQuerySelection
import all Complexity.Cryptanalysis.AddXNORNativeDualPreparation

/-!
# Original-input projected selection and bounded native witness search

For [WangLvShenZhang2027], Lemma 8/Theorem 7, PDF pp. 21–22, project the
original middle quarters, compute both low-bit queries natively, and transfer
their saved addresses into forward retention, separate inverse fourth-quarter
preparation and inverse third-quarter probing. Every reported hit solves the
original chain. No projected array, selected key, dictionary, execution or witness
correctness conclusion is a premise. The class value and two middle-quarter
words are parameters. For the source low-bit class interpretation take `p ≤ m`;
hit soundness itself does not need that restriction. This does not prove whole-class
completeness, orientation,
global computed-balance resources or the source multitape bit model.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.Native.Quarter

open Cslib.WordRAM

/-- Native projected selection feeds register-selected construction and scanning. -/
@[expose] def projectedProbe (b n₁ c n₂ b₃ n₃ b₄ n₄ q₂ q₃ N M g s t v₂ v₃ h f h₄ f₄ D : ℕ) :
    Code .standard 32 :=
  .seq (selectQueries c n₂ b₃ n₃ q₂ q₃ N g v₂ v₃ h h₄)
    (.seq (inverseSetup b n₁ M s h f N)
      (selectedProbe c n₂ v₂ D b₄ n₄ M t h₄ f₄ N b₃ n₃ v₃))

/-- A native search for one pair of middle-quarter words in a given low-bit
class. All arrays are original operands. Word and layout conditions are physical
prerequisites; the selected buckets and all semantic execution conclusions are derived. -/
theorem projectedProbe_exec {W m p b c b₃ b₄ q₂ q₃ h f h₄ f₄ D v₂ v₃ : ℕ}
    (as bs cs ds : List (BitVec m)) (s t : BitVec m) (g : BitVec p) (x : Data 32)
    (hfirst : ∀ i (hi : i < as.length), x.mem (b + i) = as[i].toNat)
    (hsecond : ∀ i (hi : i < bs.length), x.mem (c + i) = bs[i].toNat)
    (hthird : ∀ i (hi : i < cs.reverse.length), x.mem (b₃ + i) = cs.reverse[i].toNat)
    (hfourth : ∀ i (hi : i < ds.reverse.length), x.mem (b₄ + i) = ds.reverse[i].toNat)
    (hend₁ : b + as.length ≤ q₂) (hend₂ : c + bs.length ≤ q₂)
    (hend₃ : b₃ + cs.length ≤ q₂) (hend₄ : b₄ + ds.length ≤ q₂)
    (hproj : q₂ + bs.length ≤ q₃) (hprojEnd : q₃ + cs.length ≤ h)
    (hfpos : 0 < f) (hheads : h + 2 ^ p ≤ f)
    (harenas : f + 3 * 2 ^ as.length ≤ h₄) (hheads₄ : h₄ + 2 ^ p ≤ f₄)
    (hboundary : f₄ + 3 * 2 ^ ds.length ≤ D)
    (hzero : ∀ a, D ≤ a → x.mem a = 0)
    (hqueryFit : Fits W (h + h₄ + q₂ + q₃ + bs.length + cs.length +
      2 * 2 ^ p + 2 ^ bs.length + 2 ^ cs.length + v₂ + v₃ + 16))
    (hfit : Fits W ((b + as.length + c + bs.length + b₄ + ds.length + h + f +
      h₄ + f₄ + D + 4 * 2 ^ p + 10 * 2 ^ m + 5 * 2 ^ as.length +
      5 * 2 ^ ds.length + v₂ + 32) +
      (D + f₄ + 3 * 2 ^ ds.length + b₃ + cs.length + 8 * 2 ^ m +
        2 ^ cs.length + v₃ + 16))) :
    let fk := backward ((decode bs.length v₂).zip (bs.map (BitVec.setWidth p))) g
    let bk := eval ((decode cs.length v₃).zip (cs.map (BitVec.setWidth p))) g
    let ws := Backward.bucketIndices ds t (2 ^ p) bk.toNat (2 ^ ds.length)
    ∃ y, ExecWithin W (projectedProbe b as.length c bs.length b₃ cs.length b₄ ds.length
        q₂ q₃ (2 ^ p) (2 ^ m) g.toNat s.toNat t.toNat v₂ v₃ h f h₄ f₄ D) x y
        (((10 * bs.length + 8) + ((10 * cs.length + 8) +
          ((18 * bs.length + 28) + ((11 * cs.length + 14) + 5)))) +
          (7 + (4 * 2 ^ p + 2 ^ as.length * (11 * as.length + 22) + 10 +
            (9 + ((Forward.records as s p fk.toNat).length * (11 * bs.length + 30) + 2)) +
            (7 + (4 * 2 ^ p + 2 ^ ds.length * (18 * ds.length + 37) + 10)) +
            (10 + (ws.length * (18 * cs.length + 39) + 2))))) ∧
      (y.regs operand ≠ 0 →
        eval (((decode as.length (y.regs operand - 1)).zip as) ++
          ((decode bs.length (y.regs bits)).zip bs) ++
          ((decode cs.length (y.regs operators)).zip cs) ++
          ((decode ds.length (y.regs firstOperators)).zip ds)) s = t) := by
  dsimp only
  let fk := backward ((decode bs.length v₂).zip (bs.map (BitVec.setWidth p))) g
  let bk := eval ((decode cs.length v₃).zip (cs.map (BitVec.setWidth p))) g
  obtain ⟨z, hz, zf, zb, _, _, _, _, zmem⟩ := selectQueries_exec bs cs g x hsecond hthird
    hend₂ hend₃ hproj hqueryFit
  let u := z.set base b |>.set count as.length |>.set modulus (2 ^ m)
    |>.set initial s.toNat |>.set heads h |>.set frontier f |>.set keyModulus (2 ^ p)
  have setup : ExecWithin W (inverseSetup b as.length (2 ^ m) s.toNat h f (2 ^ p)) z u 7 := by
    have hb' : Fits W b := hfit.of_le (by have := Nat.two_pow_pos cs.length; omega)
    have hc' : Fits W as.length := hfit.of_le (by have := Nat.two_pow_pos cs.length; omega)
    have hm' : Fits W (2 ^ m) := hfit.of_le (by have := Nat.two_pow_pos cs.length; omega)
    have hs' : Fits W s.toNat := hfit.of_le (by
      have := s.isLt; have := Nat.two_pow_pos cs.length; omega)
    have hh' : Fits W h := hfit.of_le (by have := Nat.two_pow_pos cs.length; omega)
    have hf' : Fits W f := hfit.of_le (by have := Nat.two_pow_pos cs.length; omega)
    have hn' : Fits W (2 ^ p) := hfit.of_le (by have := Nat.two_pow_pos cs.length; omega)
    ram_eval [inverseSetup, u, hb', hc', hm', hs', hh', hf', hn',
      base, count, modulus, initial, heads, frontier, keyModulus, Fin.mk.injEq]
  have frame (a : ℕ) (ha : a < q₂ ∨ q₃ + cs.length ≤ a) : u.mem a = x.mem a := zmem a ha
  obtain ⟨y, he, hw⟩ := dualProbe_exec
    (W := W) (b := b) (c := c) (b₃ := b₃) (b₄ := b₄) (h := h) (f := f)
    (h₄ := h₄) (f₄ := f₄) (p := p) (D := D) (v := v₂) (v₃ := v₃)
    as bs cs ds s t u ⟨fk.toNat, fk.isLt⟩
    (by simp +decide [u, base, count, modulus, initial, heads, frontier, keyModulus])
    (by simp +decide [u, count, modulus, initial, heads, frontier, keyModulus])
    (by simp +decide [u, modulus, initial, heads, frontier, keyModulus])
    (by simp +decide [u, initial, heads, frontier, keyModulus])
    (by simp +decide [u, heads, frontier, keyModulus])
    (by simp +decide [u, frontier, keyModulus]) (by simp [u]) hfpos hheads
    (by intro i hi; rw [frame _ (Or.inl (by omega))]; exact hfirst i hi)
    (by intro i hi; constructor <;> omega)
    (by intro i hi; rw [frame _ (Or.inl (by omega))]; exact hsecond i hi)
    (by intro i hi; constructor <;> omega) (by omega)
    (by intro i hi; rw [frame _ (Or.inl (by simp only [List.length_reverse] at hi; omega))];
        exact hfourth i hi)
    (by omega)
    (by intro i hi; exact ⟨by omega, by omega, by omega, by omega⟩)
    harenas hheads₄ hboundary
    (by intro a ha; rw [frame _ (Or.inr (by omega))]; exact hzero a ha)
    (by intro i hi; rw [frame _ (Or.inl (by simp only [List.length_reverse] at hi; omega))];
        exact hthird i hi)
    (by omega) (by intro i hi; exact ⟨by omega, by omega, by omega, by omega⟩)
    ⟨bk.toNat, bk.isLt⟩ hfit
  have hf' : u.regs selectedForward = h + fk.toNat := by
    simpa +decide [u, selectedForward, base, count, modulus, initial, heads, frontier,
      keyModulus, fk] using zf
  have hb' : u.regs selectedBackward = h₄ + bk.toNat := by
    simpa +decide [u, selectedBackward, base, count, modulus, initial, heads, frontier,
      keyModulus, bk] using zb
  exact ⟨y, hz.seq (setup.seq (selectedProbe_exec hf' hb' he)), hw⟩

end Cslib.Cryptanalysis.AddXNOR.Native.Quarter
