/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORNativeForwardRetain
public import CslibFrontier.Cryptanalysis.AddXNORNativeBackward
public import CslibFrontier.Cryptanalysis.AddXNORNativeDictionaryFrame

/-!
# Forward retention followed by separate inverse preparation

A construction connection for [WangLvShenZhang2027], Lemma 8 and Theorem 7,
PDF pp. 21–22. The retained states are forward evaluations of the first two
quarters. A separate fourth-quarter inverse preparation preserves that dictionary
and the forward buckets. Both lists and the exact dictionary equation are derived
from consecutive native execution on raw operands. Only one forward bucket and
one second-quarter word are retained. Full-class search, orientation, global
resources and the source sorted-list multitape bit model remain open.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.Native.Quarter

open Cslib.WordRAM

/-- All inverse-stage layout and target registers are transferred by instructions. -/
@[expose] def inverseSetup (b n M t h f N : ℕ) : Code .standard 32 :=
  ram[ base ← #b; count ← #n; modulus ← #M; initial ← #t;
    heads ← #h; frontier ← #f; keyModulus ← #N ]

/-- Forward construction/retention, then independent inverse construction. -/
@[expose] def dualPrepare (c n v D h g b₄ n₄ M t h₄ f₄ N : ℕ) : Code .standard 32 :=
  .seq (Forward.prepareRetain c n v D h g)
    (.seq (inverseSetup b₄ n₄ M t h₄ f₄ N) Backward.prepare)

/-- Preserve exactly the executed low memory and restore the unfilled dictionary
region. This is proof bookkeeping, never a RAM instruction or input oracle. -/
def dictionaryBase (D : ℕ) (low original : ℕ → ℕ) : ℕ → ℕ :=
  fun a => if a < D then low a else original a

/-- Consecutive native stages derive both orientations of bucket lists and the
forward dictionary required by original-chain probing. The inverse arena follows
the forward arena and lies below the dictionary; operands avoid both arenas.
No linked-list, dictionary or execution conclusion is supplied as a premise. -/
theorem dualPrepare_exec {W m b c b₄ h f h₄ f₄ p D v : ℕ}
    (as bs ds : List (BitVec m)) (s t : BitVec m) (x : Data 32) (g : Fin (2 ^ p))
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
    (hfit : Fits W (b + as.length + c + bs.length + b₄ + ds.length + h + f +
      h₄ + f₄ + D + 4 * 2 ^ p + 10 * 2 ^ m + 5 * 2 ^ as.length +
      5 * 2 ^ ds.length + v + 32)) :
    let prepared := preparedMemory as s (clear x.mem h (2 ^ p)) h f (2 ^ p)
      (2 ^ as.length)
    let es := retainedEntries bs v (Forward.records as s p g.val)
    let retained := Dictionary.filledMemory D es prepared 0
    let inverse := Backward.preparedMemory ds t (clear retained h₄ (2 ^ p)) h₄ f₄
      (2 ^ p) (2 ^ ds.length)
    ∃ y, ExecWithin W
        (dualPrepare c bs.length v D h g.val b₄ ds.length (2 ^ m) t.toNat h₄ f₄ (2 ^ p)) x y
        (4 * 2 ^ p + 2 ^ as.length * (11 * as.length + 22) + 10 +
          (9 + ((Forward.records as s p g.val).length * (11 * bs.length + 30) + 2)) +
          (7 + (4 * 2 ^ p + 2 ^ ds.length * (18 * ds.length + 37) + 10))) ∧
      y.mem = inverse ∧
      y.mem = Dictionary.filledMemory D es (dictionaryBase D inverse prepared) 0 ∧
      (∀ q, dictionaryBase D inverse prepared (Dictionary.slot D q) = 0) ∧
      (∀ k : Fin (2 ^ p), Linked y.mem (f + 3 * 2 ^ as.length) (y.mem (h + k.val))
        (Forward.records as s p k.val)) ∧
      (∀ k : Fin (2 ^ p), Linked y.mem (f₄ + 3 * 2 ^ ds.length) (y.mem (h₄ + k.val))
        ((Backward.bucketIndices ds t (2 ^ p) k.val (2 ^ ds.length)).map
          fun u => ((Backward.indexedState ds t u).toNat, u))) ∧
      (∀ a, a < D → ¬(h ≤ a ∧ a < h + 2 ^ p) →
        ¬(f ≤ a ∧ a < f + 3 * 2 ^ as.length) →
        ¬(h₄ ≤ a ∧ a < h₄ + 2 ^ p) →
        ¬(f₄ ≤ a ∧ a < f₄ + 3 * 2 ^ ds.length) → y.mem a = x.mem a) ∧
      (∀ r, (dualPrepare c bs.length v D h g.val b₄ ds.length (2 ^ m) t.toNat
        h₄ f₄ (2 ^ p)).Preserves r → y.regs r = x.regs r) := by
  dsimp only
  let P := preparedMemory as s (clear x.mem h (2 ^ p)) h f (2 ^ p) (2 ^ as.length)
  let es := retainedEntries bs v (Forward.records as s p g.val)
  let R := Dictionary.filledMemory D es P 0
  obtain ⟨z, he, zm, _, zframe, _, _⟩ := Forward.prepareRetain_exec (W := W) (b := b)
    (c := c) (h := h) (f := f) (p := p) (D := D) (v := v) as bs s x g
    hb hc hn hs hh hf hp hfpos hheads hinput hsep hother hotherSep
    (by omega) hotherEnd hzero (hfit.of_le (by omega))
  change z.mem = R at zm
  let u := z.set base b₄ |>.set count ds.length |>.set modulus (2 ^ m)
    |>.set initial t.toNat |>.set heads h₄ |>.set frontier f₄ |>.set keyModulus (2 ^ p)
  have setup : ExecWithin W
      (inverseSetup b₄ ds.length (2 ^ m) t.toNat h₄ f₄ (2 ^ p)) z u 7 := by
    have hb' : Fits W b₄ := hfit.of_le (by omega)
    have hc' : Fits W ds.length := hfit.of_le (by omega)
    have hn' : Fits W (2 ^ m) := hfit.of_le (by omega)
    have ht' : Fits W t.toNat := hfit.of_le (by have := t.isLt; omega)
    have hh' : Fits W h₄ := hfit.of_le (by omega)
    have hf' : Fits W f₄ := hfit.of_le (by omega)
    have hp' : Fits W (2 ^ p) := hfit.of_le (by omega)
    ram_eval [inverseSetup, u, hb', hc', hn', ht', hh', hf', hp',
      base, count, modulus, initial, heads, frontier, keyModulus, Fin.mk.injEq]
  obtain ⟨y, hy, ym, _, _⟩ := Backward.prepare_exec ds t u (b := b₄) (h := h₄) (f := f₄) (p := p)
    (by simp +decide [u, base, count, modulus, initial, heads, frontier, keyModulus])
    (by simp +decide [u, count, modulus, initial, heads, frontier, keyModulus])
    (by simp +decide [u, modulus, initial, heads, frontier, keyModulus])
    (by simp +decide [u, initial, heads, frontier, keyModulus])
    (by simp +decide [u, heads, frontier, keyModulus])
    (by simp +decide [u, frontier, keyModulus]) (by simp [u])
    (by
      intro i hi
      change z.mem _ = _
      rw [zframe _ (by omega) (hfourthSep i hi).1 (hfourthSep i hi).2.1]
      exact hfourth i (by simpa only [List.length_reverse] using hi))
    (by intro i hi; exact (hfourthSep i hi).2.2)
    (hfit.of_le (by omega))
  simp only [u, Data.set_mem, zm] at ym
  have iframe (a : ℕ) (ha : ¬(h₄ ≤ a ∧ a < h₄ + 2 ^ p))
      (ha' : ¬(f₄ ≤ a ∧ a < f₄ + 3 * 2 ^ ds.length)) : y.mem a = R a := by
    rw [ym, Backward.preparedMemory_outside ds t _ _ _ _ _ _ (Nat.two_pow_pos p) ha ha',
      clear_of_not_owns ha]
  have above (a : ℕ) (ha : D ≤ a) : y.mem a = R a :=
    iframe a (by omega) (by omega)
  have dict : y.mem = Dictionary.filledMemory D es (dictionaryBase D y.mem P) 0 := by
    funext a
    by_cases ha : a < D
    · rw [Dictionary.filledMemory_below _ _ _ _ _ ha]
      simp [dictionaryBase, ha]
    · rw [above a (by omega)]
      exact Dictionary.filledMemory_congr_above D es P (dictionaryBase D y.mem P) 0
        (by intro q hq; simp [dictionaryBase, show ¬q < D by omega]) a (by omega)
  have exec := he.seq (setup.seq hy)
  refine ⟨y, exec, ym, ?_, ?_, ?_, ?_, ?_, fun r hr => exec.regs_eq hr⟩
  · simpa only [ym] using dict
  · intro q
    have hq : D ≤ Dictionary.slot D q := by simp only [Dictionary.slot]; omega
    simp only [dictionaryBase, show ¬Dictionary.slot D q < D by omega, ↓reduceIte]
    have hq₁ : ¬(h ≤ Dictionary.slot D q ∧ Dictionary.slot D q < h + 2 ^ p) := by omega
    have hq₂ : ¬(f ≤ Dictionary.slot D q ∧
        Dictionary.slot D q < f + 3 * 2 ^ as.length) := by omega
    rw [preparedMemory_outside as s _ h f (2 ^ p) (2 ^ as.length) _
      (Nat.two_pow_pos p) hq₁ hq₂, clear_of_not_owns hq₁]
    exact hzero _ hq
  · intro k
    have fr (a : ℕ) (ha : a < f + 3 * 2 ^ as.length) : y.mem a = R a :=
      iframe a (by omega) (by omega)
    rw [fr (h + k.val) (by have := k.isLt; omega)]
    exact (Forward.retainedMemory_linked as bs s x.mem v g k hfpos hheads (by omega)).frame fr
  · intro k
    rw [ym]
    exact Backward.preparedMemory_linked ds t _ h₄ f₄ (2 ^ p) (2 ^ ds.length)
      k.val k.isLt (by omega) hheads₄
      (clear_of_owns ⟨Nat.le_add_right _ _, Nat.add_lt_add_left k.isLt _⟩)
  · intro a ha ha₁ ha₂ ha₃ ha₄
    rw [iframe a ha₃ ha₄]
    exact zm ▸ zframe a ha ha₁ ha₂

end Cslib.Cryptanalysis.AddXNOR.Native.Quarter
