/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORNativeDualPreparation
public import CslibFrontier.Cryptanalysis.AddXNORNativeProbe
import all CslibFrontier.Cryptanalysis.AddXNORNativeBackward
import all CslibFrontier.Cryptanalysis.AddXNORNativeForwardRetain
import all CslibFrontier.Cryptanalysis.AddXNORNativeBuckets

/-!
# Original-chain reconstruction after native construction

A bounded connection for [WangLvShenZhang2027], Lemma 8 and Theorem 7,
PDF pp. 21–22: execute forward preparation and retention, separate inverse
fourth-quarter preparation, native bucket-head loading and inverse third-quarter
scanning. Any returned witness solves the original four-quarter chain. Both
lists and the dictionary are constructed, not supplied as semantic premises.
The two bucket indices and second/third-quarter words are parameters; projected
query selection, full-class completeness, orientation and global resources remain
open. This is sparse word RAM, not the source sorted-list multitape bit model.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.Native.Quarter

open Cslib.WordRAM

/-- Load a constructed inverse bucket and transfer the full-width probe registers. -/
@[expose] def probeSetup (b n M v D h k : ℕ) : Code .standard 32 :=
  ram[ base ← #b; count ← #n; modulus ← #M; operators ← #v;
    Dictionary.table ← #D; one ← #1; zero ← #0; operand ← #0;
    address ← #(h + k); link ← *address ]

/-- Native construction followed by a scan of one actual inverse bucket. -/
@[expose] def dualProbe (c n v D h g b₄ n₄ M t h₄ f₄ N b₃ n₃ v₃ k : ℕ) : Code .standard 32 :=
  .seq (dualPrepare c n v D h g b₄ n₄ M t h₄ f₄ N)
    (.seq (probeSetup b₃ n₃ M v₃ D h₄ k) probeScan)

/-- Every reported native hit reconstructs the original chain, for arbitrary
admitted widths and operand lists. All construction, register transfers, loads
and scanning instructions are included. Absence of a hit is not a global no-instance
claim: this run selects only one bucket on each side and one word per middle quarter. -/
theorem dualProbe_exec {W m b c b₄ h f h₄ f₄ p D v b₃ v₃ : ℕ}
    (as bs cs ds : List (BitVec m)) (s t : BitVec m) (x : Data 32) (g : Fin (2 ^ p))
    (hb : x.regs base = b) (hc : x.regs count = as.length)
    (hn : x.regs modulus = 2 ^ m) (hs : x.regs initial = s.toNat)
    (hh : x.regs heads = h) (hf : x.regs frontier = f)
    (hp : x.regs keyModulus = 2 ^ p) (hfpos : 0 < f) (hheads : h + 2 ^ p ≤ f)
    (hinput : ∀ i (hi : i < as.length), x.mem (b + i) = as[i].toNat)
    (hsep : ∀ i < as.length, ¬(h ≤ b + i ∧ b + i < h + 2 ^ p) ∧
      ¬(f ≤ b + i ∧ b + i < f + 3 * 2 ^ as.length))
    (hother : ∀ i (hi : i < bs.length), x.mem (c + i) = bs[i].toNat)
    (hotherSep : ∀ i < bs.length, ¬(h ≤ c + i ∧ c + i < h + 2 ^ p) ∧
      ¬(f ≤ c + i ∧ c + i < f + 3 * 2 ^ as.length))
    (hotherEnd : c + bs.length ≤ D)
    (hfourth : ∀ i (hi : i < ds.reverse.length), x.mem (b₄ + i) = ds.reverse[i].toNat)
    (hfourthEnd : b₄ + ds.length ≤ D)
    (hfourthSep : ∀ i < ds.length,
      ¬(h ≤ b₄ + i ∧ b₄ + i < h + 2 ^ p) ∧
      ¬(f ≤ b₄ + i ∧ b₄ + i < f + 3 * 2 ^ as.length) ∧
      ¬(h₄ ≤ b₄ + i ∧ b₄ + i < h₄ + 2 ^ p) ∧
      ¬(f₄ ≤ b₄ + i ∧ b₄ + i < f₄ + 3 * 2 ^ ds.length))
    (harenas : f + 3 * 2 ^ as.length ≤ h₄) (hheads₄ : h₄ + 2 ^ p ≤ f₄)
    (hboundary : f₄ + 3 * 2 ^ ds.length ≤ D)
    (hzero : ∀ a, D ≤ a → x.mem a = 0)
    (hthird : ∀ i (hi : i < cs.reverse.length), x.mem (b₃ + i) = cs.reverse[i].toNat)
    (hthirdEnd : b₃ + cs.length ≤ D)
    (hthirdSep : ∀ i < cs.length,
      ¬(h ≤ b₃ + i ∧ b₃ + i < h + 2 ^ p) ∧
      ¬(f ≤ b₃ + i ∧ b₃ + i < f + 3 * 2 ^ as.length) ∧
      ¬(h₄ ≤ b₃ + i ∧ b₃ + i < h₄ + 2 ^ p) ∧
      ¬(f₄ ≤ b₃ + i ∧ b₃ + i < f₄ + 3 * 2 ^ ds.length))
    (k : Fin (2 ^ p))
    (hfit : Fits W ((b + as.length + c + bs.length + b₄ + ds.length + h + f +
      h₄ + f₄ + D + 4 * 2 ^ p + 10 * 2 ^ m + 5 * 2 ^ as.length +
      5 * 2 ^ ds.length + v + 32) +
      (D + f₄ + 3 * 2 ^ ds.length + b₃ + cs.length + 8 * 2 ^ m +
        2 ^ cs.length + v₃ + 16))) :
    let ws := Backward.bucketIndices ds t (2 ^ p) k.val (2 ^ ds.length)
    ∃ y, ExecWithin W
        (dualProbe c bs.length v D h g.val b₄ ds.length (2 ^ m) t.toNat h₄ f₄ (2 ^ p)
          b₃ cs.length v₃ k.val) x y
        (4 * 2 ^ p + 2 ^ as.length * (11 * as.length + 22) + 10 +
          (9 + ((Forward.records as s p g.val).length * (11 * bs.length + 30) + 2)) +
          (7 + (4 * 2 ^ p + 2 ^ ds.length * (18 * ds.length + 37) + 10)) +
          (10 + (ws.length * (18 * cs.length + 39) + 2))) ∧
      (y.regs operand ≠ 0 →
        eval (((decode as.length (y.regs operand - 1)).zip as) ++
          ((decode bs.length (y.regs bits)).zip bs) ++
          ((decode cs.length (y.regs operators)).zip cs) ++
          ((decode ds.length (y.regs firstOperators)).zip ds)) s = t) := by
  dsimp only
  have tailFit : Fits W (D + f₄ + 3 * 2 ^ ds.length + b₃ + cs.length + 8 * 2 ^ m +
      2 ^ cs.length + v₃ + 16) := hfit.of_le (Nat.le_add_left _ _)
  have hN := Nat.two_pow_pos cs.length
  obtain ⟨z, he, _, zm, zz, _, zl, zframe, _⟩ := dualPrepare_exec
    (W := W) (b := b) (c := c) (b₄ := b₄) (h := h) (f := f) (h₄ := h₄) (f₄ := f₄)
    (p := p) (D := D) (v := v) as bs ds s t x g
    hb hc hn hs hh hf hp hfpos hheads hinput hsep hother hotherSep hotherEnd
    hfourth hfourthEnd hfourthSep harenas hheads₄ hboundary hzero
    (hfit.of_le (Nat.le_add_right _ _))
  let u := z.set base b₃ |>.set count cs.length |>.set modulus (2 ^ m)
    |>.set operators v₃ |>.set Dictionary.table D |>.set one 1 |>.set zero 0
    |>.set operand 0 |>.set address (h₄ + k.val) |>.set link (z.mem (h₄ + k.val))
  have setup : ExecWithin W (probeSetup b₃ cs.length (2 ^ m) v₃ D h₄ k.val) z u 10 := by
    have hb' : Fits W b₃ := tailFit.of_le (by omega)
    have hc' : Fits W cs.length := tailFit.of_le (by omega)
    have hn' : Fits W (2 ^ m) := tailFit.of_le (by omega)
    have hv' : Fits W v₃ := tailFit.of_le (by omega)
    have hd' : Fits W D := tailFit.of_le (by omega)
    have h1 : Fits W 1 := tailFit.of_le (by omega)
    have h0 : Fits W 0 := tailFit.of_le (by omega)
    have ha : Fits W (h₄ + k.val) := tailFit.of_le (by
      have hk := k.isLt
      omega)
    ram_eval [probeSetup, u, hb', hc', hn', hv', hd', h1, h0, ha,
      base, count, modulus, operators, Dictionary.table, one, zero, operand, address, link,
      Fin.mk.injEq]
  obtain ⟨y, hy, _, _, hw⟩ := probeScan_original_exec
    (W := W) (b := b₃) (boundary := f₄ + 3 * 2 ^ ds.length)
    (ptr := z.mem (h₄ + k.val)) (D := D) (v := v₃)
    as bs cs ds s t (bucketIndices as s (2 ^ p) g.val (2 ^ as.length))
    (Backward.bucketIndices ds t (2 ^ p) k.val (2 ^ ds.length)) v _ 0 u
    (by simp +decide [u, base, count, modulus, operators, Dictionary.table,
      one, zero, operand, address, link])
    (by simp +decide [u, count, modulus, operators, Dictionary.table,
      one, zero, operand, address, link])
    (by simp +decide [u, modulus, operators, Dictionary.table, one, zero, operand, address, link])
    (by simp +decide [u, operators, Dictionary.table, one, zero, operand, address, link])
    (tailFit.of_le (by omega)) (by simp [u])
    (by simp +decide [u, Dictionary.table, one, zero, operand, address, link])
    (by simp +decide [u, one, zero, operand, address, link])
    (by simp +decide [u, zero, operand, address, link])
    (by simp +decide [u, operand, address, link])
    (by simpa only [u, Data.set_mem, Backward.indexedState] using zl k)
    (by simpa only [u, Data.set_mem, Forward.records, indexedState] using zm) zz
    (by
      intro i hi
      have hi' : i < cs.length := by simpa only [List.length_reverse] using hi
      change z.mem _ = _
      rw [zframe _ (by omega) (hthirdSep i hi').1 (hthirdSep i hi').2.1
        (hthirdSep i hi').2.2.1 (hthirdSep i hi').2.2.2]
      exact hthird i hi)
    (tailFit.of_le (by omega))
  exact ⟨y, he.seq (setup.seq hy), hw⟩

end Cslib.Cryptanalysis.AddXNOR.Native.Quarter
