/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORNativeBuckets
public import CslibFrontier.Cryptanalysis.AddXNORNativeRetain

/-!
# Forward preparation followed by native retention

A retained-side construction component for [WangLvShenZhang2027], Lemma 8
and Theorem 7, PDF pp. 21–22. Native first-quarter preparation stores forward
states and indexed witnesses; native second-quarter retention evaluates these
states forward and inserts the results into the sparse full-state dictionary.
This is one bucket and one fixed second-quarter word, not a complete low-bit
class. No semantic dictionary or execution conclusion is assumed. The source
uses sorted lists and multitape bit operations; global search and resources
and the source bit model remain open.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.Native.Quarter.Forward

open Cslib.WordRAM

/-- Register transfer between the two actual programs, including a native head load. -/
@[expose] def retainSetup (b n v D h g : ℕ) : Code .standard 32 :=
  ram[ base ← #b; count ← #n; operators ← #v; Dictionary.table ← #D;
    Dictionary.top ← #0; one ← #1; zero ← #0; address ← #(h + g); link ← *address ]

/-- Consecutive execution; no host records are passed to the machine. -/
@[expose] def prepareRetain (b n v D h g : ℕ) : Code .standard 32 :=
  .seq prepare (.seq (retainSetup b n v D h g) retainLoop)

/-- The proof-observed list in precisely the order read by the native consumer. -/
def records {m : ℕ} (as : List (BitVec m)) (t : BitVec m) (p g : ℕ) : List (ℕ × ℕ) :=
  (bucketIndices as t (2 ^ p) g (2 ^ as.length)).map
    fun u => ((indexedState as t u).toNat, u)

/-- Actual preparation and retention derive the final dictionary from computed
forward records. Only raw operand memory, registers and physical layout are
premises. Duplicate states and index zero require no special assumptions.
Memory below the dictionary and outside the preparation regions is framed;
registers preserved by the composite are framed as well. -/
theorem prepareRetain_exec {W m b c h f p D v : ℕ}
    (as bs : List (BitVec m)) (t : BitVec m) (x : Data 32) (g : Fin (2 ^ p))
    (hb : x.regs base = b) (hc : x.regs count = as.length)
    (hn : x.regs modulus = 2 ^ m) (ht : x.regs initial = t.toNat)
    (hh : x.regs heads = h) (hf : x.regs frontier = f)
    (hp : x.regs keyModulus = 2 ^ p) (hfpos : 0 < f) (hheads : h + 2 ^ p ≤ f)
    (hinput : ∀ i (hi : i < as.length), x.mem (b + i) = as[i].toNat)
    (hsep : ∀ i < as.length, ¬(h ≤ b + i ∧ b + i < h + 2 ^ p) ∧
      ¬(f ≤ b + i ∧ b + i < f + 3 * 2 ^ as.length))
    (hother : ∀ i (hi : i < bs.length), x.mem (c + i) = bs[i].toNat)
    (hotherSep : ∀ i < bs.length, ¬(h ≤ c + i ∧ c + i < h + 2 ^ p) ∧
      ¬(f ≤ c + i ∧ c + i < f + 3 * 2 ^ as.length))
    (hboundary : f + 3 * 2 ^ as.length ≤ D) (hotherEnd : c + bs.length ≤ D)
    (hzero : ∀ q, D ≤ q → x.mem q = 0)
    (hfit : Fits W (b + as.length + 2 * 2 ^ m + h + 2 ^ p + f +
      5 * 2 ^ as.length + D + c + bs.length + 8 * 2 ^ m + v + 16)) :
    ∃ y, ExecWithin W (prepareRetain c bs.length v D h g.val) x y
        (4 * 2 ^ p + 2 ^ as.length * (11 * as.length + 22) + 10 +
          (9 + ((records as t p g.val).length * (11 * bs.length + 30) + 2))) ∧
      y.mem = Dictionary.filledMemory D (retainedEntries bs v (records as t p g.val))
        (preparedMemory as t (clear x.mem h (2 ^ p)) h f (2 ^ p) (2 ^ as.length)) 0 ∧
      y.regs Dictionary.top = Dictionary.filledTop D
        (retainedEntries bs v (records as t p g.val))
        (preparedMemory as t (clear x.mem h (2 ^ p)) h f (2 ^ p) (2 ^ as.length)) 0 ∧
      (∀ a, a < D → ¬(h ≤ a ∧ a < h + 2 ^ p) →
        ¬(f ≤ a ∧ a < f + 3 * 2 ^ as.length) → y.mem a = x.mem a) ∧
      (∀ q, y.mem (Dictionary.slot D q) ≠ 0 → ∃ r ∈ records as t p g.val,
        (eval ((decode bs.length v).zip bs) (BitVec.ofNat m r.1)).toNat = q ∧
        y.mem (Dictionary.slot D q) = r.2 + 1 ∧
        y.mem (Dictionary.slot D q + 1) = v) ∧
      (∀ r, (prepareRetain c bs.length v D h g.val).Preserves r → y.regs r = x.regs r) := by
  obtain ⟨z, he, zm, _, _⟩ := prepare_exec as t x hb hc hn ht hh hf hp
    hinput hsep (hfit.of_le (by omega))
  have frame (a : ℕ) (ha : ¬(h ≤ a ∧ a < h + 2 ^ p))
      (ha' : ¬(f ≤ a ∧ a < f + 3 * 2 ^ as.length)) : z.mem a = x.mem a := by
    rw [zm, preparedMemory_outside as t _ _ _ _ _ _ (Nat.two_pow_pos p) ha ha',
      clear_of_not_owns ha]
  let u := z.set base c |>.set count bs.length |>.set operators v
    |>.set Dictionary.table D |>.set Dictionary.top 0 |>.set one 1 |>.set zero 0
    |>.set address (h + g.val) |>.set link (z.mem (h + g.val))
  have setup : ExecWithin W (retainSetup c bs.length v D h g.val) z u 9 := by
    have hg := g.isLt
    have hC : Fits W c := hfit.of_le (by omega)
    have hn' : Fits W bs.length := hfit.of_le (by omega)
    have hv' : Fits W v := hfit.of_le (by omega)
    have hd' : Fits W D := hfit.of_le (by omega)
    have hz' : Fits W 0 := hfit.of_le (by omega)
    have ho' : Fits W 1 := hfit.of_le (by omega)
    have ha' : Fits W (h + g.val) := hfit.of_le (by omega)
    ram_eval [retainSetup, u, hC, hn', hv', hd', hz', ho', ha', base, count,
      operators, Dictionary.table, Dictionary.top, one, zero, address, link, Fin.mk.injEq]
  have linked : Linked u.mem (f + 3 * 2 ^ as.length) (u.regs link)
      (records as t p g.val) := by
    change Linked z.mem _ (z.mem _) _
    rw [zm]
    exact preparedMemory_linked as t _ h f (2 ^ p) (2 ^ as.length) g.val g.isLt
      hfpos hheads (clear_of_owns (by
        change h ≤ h + g.val ∧ h + g.val < h + 2 ^ p
        exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left g.isLt _⟩))
  obtain ⟨y, hy, ym, yt, _⟩ :=
    retainLoop_exec (a := as.length) (b := c) (v := v) (D := D) (t := 0) bs
    (records as t p g.val) u
    (by simp +decide [u, base, count, operators, Dictionary.table,
      Dictionary.top, one, zero, address, link])
    (by simp +decide [u, count, base, operators, Dictionary.table,
      Dictionary.top, one, zero, address, link])
    (by simpa +decide [u, modulus, base, count, operators, Dictionary.table,
      Dictionary.top, one, zero, address, link] using (he.regs_eq (by decide)).trans hn)
    (by simp +decide [u, operators, Dictionary.table, Dictionary.top, one, zero, address, link])
    (hfit.of_le (by omega)) rfl
    (by simp +decide [u, Dictionary.table, Dictionary.top, one, zero, address, link])
    (by simp +decide [u, Dictionary.top, one, zero, address, link])
    (by simp +decide [u, one, zero, address, link]) (by simp +decide [u, zero, address, link])
    linked hboundary hotherEnd
    (by intro i hi; change z.mem _ = _; rw [frame _ (hotherSep i hi).1 (hotherSep i hi).2];
        exact hother i hi)
    (by intro r hr; obtain ⟨k, _, rfl⟩ := List.mem_map.mp hr; exact (indexedState as t k).isLt)
    (by
      intro r hr
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hr
      rw [bucketIndices_eq] at hk
      exact List.mem_range.mp (List.mem_filter.mp (List.mem_reverse.mp hk)).1)
    (hfit.of_le (by omega))
  have exec := he.seq (setup.seq hy)
  refine ⟨y, exec, ?_, ?_, ?_, ?_, fun r hr => exec.regs_eq hr⟩
  · simpa only [u, Data.set_mem, zm] using ym
  · simpa only [u, Data.set_mem, zm] using yt
  · intro a ha ha' ha''
    rw [ym, Dictionary.filledMemory_below _ _ _ _ _ ha]
    exact frame a ha' ha''
  · intro q hq
    rw [ym] at hq ⊢
    apply retained_provenance D 0 q u.mem bs v (records as t p g.val) _ hq
    change z.mem (Dictionary.slot D q) = 0
    rw [frame]
    · exact hzero _ (by simp only [Dictionary.slot]; omega)
    · simp only [Dictionary.slot]; omega
    · simp only [Dictionary.slot]; omega

/-- Retention preserves every computed forward bucket, not only the bucket it
consumed. No linked-record or dictionary-validity premise is required. This
layout connection applies to arbitrary widths, collisions and zero witnesses. -/
theorem retainedMemory_linked {m h f p D : ℕ}
    (as bs : List (BitVec m)) (t : BitVec m) (mem : ℕ → ℕ)
    (v : ℕ) (g k : Fin (2 ^ p))
    (hf : 0 < f) (hh : h + 2 ^ p ≤ f) (hD : f + 3 * 2 ^ as.length ≤ D) :
    let prepared := preparedMemory as t (clear mem h (2 ^ p)) h f (2 ^ p) (2 ^ as.length)
    let retained := Dictionary.filledMemory D (retainedEntries bs v (records as t p g.val))
      prepared 0
    Linked retained (f + 3 * 2 ^ as.length) (retained (h + k.val)) (records as t p k.val) := by
  dsimp only
  have frame (a : ℕ) (ha : a < D) := Dictionary.filledMemory_below D
    (retainedEntries bs v (records as t p g.val))
    (preparedMemory as t (clear mem h (2 ^ p)) h f (2 ^ p) (2 ^ as.length)) 0 a ha
  rw [frame (h + k.val) (by have := k.isLt; omega)]
  exact (preparedMemory_linked as t _ h f (2 ^ p) (2 ^ as.length) k.val k.isLt hf hh
    (clear_of_owns ⟨Nat.le_add_right _ _, Nat.add_lt_add_left k.isLt _⟩)).frame
    (fun a ha => frame a (by omega))


end Cslib.Cryptanalysis.AddXNOR.Native.Quarter.Forward
