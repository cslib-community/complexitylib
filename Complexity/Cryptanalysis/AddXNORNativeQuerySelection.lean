/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORNativeQuarterProjection
public import Complexity.Cryptanalysis.AddXNORNativeSelectedProbe
import all Complexity.Cryptanalysis.AddXNORNativeProjection

/-!
# Native projected query selection from original middle quarters

For [WangLvShenZhang2027], Lemma 8, PDF pp. 21–22, the retained-side
bucket is selected by an inverse second-quarter query, and the inverse-side
bucket by a forward third-quarter query. The program constructs both projected
arrays from original operands, evaluates the actual queries and saves physical
bucket addresses for `selectedProbe`. No projected input or correct-query premise
is supplied. Class iteration, counter-selected orientation and global resources
remain separate.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.Native.Quarter

open Cslib.WordRAM

/-- Evaluate a projected word and save its actual bucket address. -/
@[expose] def selectAddress (back : Bool) (dst : Fin 32) (b n N g v h : ℕ) :
    Code .standard 32 :=
  .seq (ram[ base ← #b; count ← #n; modulus ← #N; state ← #g;
    operators ← #v; heads ← #h ])
    (.seq (if back then backwardEvaluate else evaluate) (ram[ dst ← heads + state ]))

/-- Query execution and saved address, with all transfers and memory preservation. -/
theorem selectAddress_exec {W p b v h : ℕ} (back : Bool) (dst : Fin 32)
    (as : List (BitVec p)) (g : BitVec p) (x : Data 32)
    (hinput : ∀ i (hi : i < (if back then as.reverse else as).length),
      x.mem (b + i) = (if back then as.reverse else as)[i].toNat)
    (hfit : Fits W (h + b + as.length + 2 * 2 ^ p + 2 ^ as.length + v + 8)) :
    ∃ y, ExecWithin W (selectAddress back dst b as.length (2 ^ p) g.toNat v h) x y
        (if back then 18 * as.length + 28 else 11 * as.length + 14) ∧
      y.regs dst = h + (if back then backward ((decode as.length v).zip as) g
        else eval ((decode as.length v).zip as) g).toNat ∧ y.mem = x.mem ∧
      (∀ r, (selectAddress back dst b as.length (2 ^ p) g.toNat v h).Preserves r →
        y.regs r = x.regs r) := by
  have hpos := Nat.two_pow_pos as.length
  have hN := Nat.two_pow_pos p
  let u := x.set base b |>.set count as.length |>.set modulus (2 ^ p)
    |>.set state g.toNat |>.set operators v |>.set heads h
  have setup : ExecWithin (B := .standard) W
      (ram[ base ← #b; count ← #as.length; modulus ← #(2 ^ p); state ← #g.toNat;
        operators ← #v; heads ← #h ]) x u 6 := by
    have hb : Fits W b := hfit.of_le (by omega)
    have hc : Fits W as.length := hfit.of_le (by omega)
    have hn : Fits W (2 ^ p) := hfit.of_le (by omega)
    have hg : Fits W g.toNat := hfit.of_le (by have := g.isLt; omega)
    have hv : Fits W v := hfit.of_le (by omega)
    have hh : Fits W h := hfit.of_le (by omega)
    ram_eval [u, hb, hc, hn, hg, hv, hh, base, count, modulus, state, operators, heads,
      Fin.mk.injEq]
  have run : ∃ z, ExecWithin W (if back then backwardEvaluate else evaluate) u z
        (if back then 18 * as.length + 21 else 11 * as.length + 7) ∧
      z.regs state = (if back then backward ((decode as.length v).zip as) g
        else eval ((decode as.length v).zip as) g).toNat ∧ z.mem = x.mem := by
    cases back
    · obtain ⟨z, he, zs, _, _, zm, _, _⟩ := evaluate_exec (W := W) (b := b) (v := v) as g u
        (by simp +decide [u, base, count, modulus, state, operators, heads])
        (by simp +decide [u, count, modulus, state, operators, heads])
        (by simp +decide [u, modulus, state, operators, heads])
        (by simp +decide [u, state, operators, heads]) (by simp +decide [u, operators, heads])
        (hfit.of_le (by omega)) (by simpa [u] using hinput)
        (hfit.of_le (by omega))
      exact ⟨z, he, zs, by simpa only [u, Data.set_mem] using zm⟩
    · obtain ⟨z, he, zs, _, zm⟩ := backwardEvaluate_exec (W := W) (b := b) (v := v) as g u
        (by simp +decide [u, base, count, modulus, state, operators, heads])
        (by simp +decide [u, count, modulus, state, operators, heads])
        (by simp +decide [u, modulus, state, operators, heads])
        (by simp +decide [u, state, operators, heads]) (by simp +decide [u, operators, heads])
        (hfit.of_le (by omega)) (by simpa [u] using hinput)
        (hfit.of_le (by omega))
      exact ⟨z, he, zs, by simpa only [u, Data.set_mem] using zm⟩
  obtain ⟨z, he, zs, zm⟩ := run
  let q := if back then backward ((decode as.length v).zip as) g
    else eval ((decode as.length v).zip as) g
  have zh : z.regs heads = h := by
    have hp : (if back then backwardEvaluate else evaluate).Preserves heads := by
      cases back <;> decide
    exact (he.regs_eq hp).trans (by simp [u])
  have ha : Fits W (h + q.toNat) := hfit.of_le (by have := q.isLt; omega)
  let y := z.set dst (h + q.toNat)
  have save : ExecWithin (B := .standard) W (ram[ dst ← heads + state ]) z y 1 := by
    ram_eval [y, zh, zs, ha, q, Fin.mk.injEq]
  have exec := setup.seq (he.seq save)
  refine ⟨y, ?_, by simp [y, q], by simpa only [y, Data.set_mem] using zm, ?_⟩
  · cases back <;> exact exec.mono (by simp; omega)
  · intro r hr
    exact exec.regs_eq hr

/-- Complemented state index used by the existing backward counter kernel. -/
abbrev backwardCounterIndex : Fin 32 := 31

/-- Compute both counter indices from the original class value. No count is read here. -/
@[expose] def selectCounterIndices (N g : ℕ) : Code .standard 32 :=
  ram[ mask ← #N; one ← #1; mask ← mask - one; state ← #g;
    backwardCounterIndex ← mask - state ]

/-- The actual forward class index and backward complemented index. These are
exactly the indices in `Counters.projectedEntry_exec`; counter contents and
orientation are not asserted by this scalar computation. -/
theorem selectCounterIndices_exec {W p : ℕ} (g : BitVec p) (x : Data 32)
    (hfit : Fits W (2 ^ p + 1)) :
    ∃ y, ExecWithin W (selectCounterIndices (2 ^ p) g.toNat) x y 5 ∧
      y.regs state = g.toNat ∧ y.regs backwardCounterIndex = (~~~g).toNat ∧
      y.mem = x.mem ∧ (∀ r, (selectCounterIndices (2 ^ p) g.toNat).Preserves r →
        y.regs r = x.regs r) := by
  have hpos := Nat.two_pow_pos p
  have hN : Fits W (2 ^ p) := hfit.of_le (by omega)
  have h1 : Fits W 1 := hfit.of_le (by omega)
  have hm : Fits W (2 ^ p - 1) := hfit.of_le (by omega)
  have hg : Fits W g.toNat := hfit.of_le (by have := g.isLt; omega)
  have hc : Fits W (2 ^ p - 1 - g.toNat) := hfit.of_le (by omega)
  let y := x.set mask (2 ^ p) |>.set one 1 |>.set mask (2 ^ p - 1)
    |>.set state g.toNat |>.set backwardCounterIndex (2 ^ p - 1 - g.toNat)
  have he : ExecWithin W (selectCounterIndices (2 ^ p) g.toNat) x y 5 := by
    ram_eval [selectCounterIndices, y, hN, h1, hm, hg, hc, mask, one, state,
      backwardCounterIndex, Fin.mk.injEq]
  exact ⟨y, he, by simp +decide [y, state, backwardCounterIndex],
    by simp [y, BitVec.toNat_not], rfl, fun r hr => he.regs_eq hr⟩

/-- Project both original middle quarters, then save both selected bucket addresses. -/
@[expose] def selectQueries (c n₂ b₃ n₃ q₂ q₃ N g v₂ v₃ h h₄ : ℕ) : Code .standard 32 :=
  .seq (projectQuarter c q₂ n₂ N true)
    (.seq (projectQuarter b₃ q₃ n₃ N true)
      (.seq (selectAddress true selectedForward q₂ n₂ N g v₂ h)
        (.seq (selectAddress false selectedBackward q₃ n₃ N g v₃ h₄)
          (selectCounterIndices N g))))

/-- Both native queries are derived from raw original arrays. The third-quarter
input is reversed, as required by the later full-width inverse probe. Scratch
writes frame all original data below `q₂` and all preparation/dictionary memory
after the second scratch array. -/
theorem selectQueries_exec {W m p c b₃ q₂ q₃ v₂ v₃ h h₄ : ℕ}
    (bs cs : List (BitVec m)) (g : BitVec p) (x : Data 32)
    (hsecond : ∀ i (hi : i < bs.length), x.mem (c + i) = bs[i].toNat)
    (hthird : ∀ i (hi : i < cs.reverse.length), x.mem (b₃ + i) = cs.reverse[i].toNat)
    (hsecondEnd : c + bs.length ≤ q₂) (hthirdEnd : b₃ + cs.length ≤ q₂)
    (hscratch : q₂ + bs.length ≤ q₃)
    (hfit : Fits W (h + h₄ + q₂ + q₃ + bs.length + cs.length +
      2 * 2 ^ p + 2 ^ bs.length + 2 ^ cs.length + v₂ + v₃ + 16)) :
    ∃ y, ExecWithin W (selectQueries c bs.length b₃ cs.length q₂ q₃ (2 ^ p)
        g.toNat v₂ v₃ h h₄) x y
        ((10 * bs.length + 8) + ((10 * cs.length + 8) +
          ((18 * bs.length + 28) + ((11 * cs.length + 14) + 5)))) ∧
      y.regs selectedForward = h +
        (backward ((decode bs.length v₂).zip (bs.map (BitVec.setWidth p))) g).toNat ∧
      y.regs selectedBackward = h₄ +
        (eval ((decode cs.length v₃).zip (cs.map (BitVec.setWidth p))) g).toNat ∧
      y.regs state = g.toNat ∧ y.regs backwardCounterIndex = (~~~g).toNat ∧
      (∀ i (hi : i < (bs.map (BitVec.setWidth p)).reverse.length),
        y.mem (q₂ + i) = (bs.map (BitVec.setWidth p)).reverse[i].toNat) ∧
      (∀ i (hi : i < (cs.map (BitVec.setWidth p)).length),
        y.mem (q₃ + i) = (cs.map (BitVec.setWidth p))[i].toNat) ∧
      (∀ a, a < q₂ ∨ q₃ + cs.length ≤ a → y.mem a = x.mem a) := by
  have hB := Nat.two_pow_pos bs.length
  have hC := Nat.two_pow_pos cs.length
  obtain ⟨z₂, he₂, zm₂, zf₂⟩ := projectQuarter_exec (p := p) (a := c) (b := q₂) true bs x hsecond
    hsecondEnd (hfit.of_le (by omega))
  obtain ⟨z₃, he₃, zm₃, zf₃⟩ := projectQuarter_exec (p := p) (a := b₃) (b := q₃) true cs.reverse z₂
    (by
      intro i hi
      rw [zf₂ _ (by have := hthirdEnd; simp only [List.length_reverse] at hi; omega)]
      exact hthird i hi)
    (by simpa only [List.length_reverse] using hthirdEnd.trans (by omega))
    (hfit.of_le (by simp only [List.length_reverse]; omega))
  have read₂ (i : ℕ) (hi : i < (bs.map (BitVec.setWidth p)).reverse.length) :
      z₃.mem (q₂ + i) = (bs.map (BitVec.setWidth p)).reverse[i].toNat := by
    have hi' : i < bs.length := by simpa using hi
    rw [zf₃ _ (by simp only [List.length_reverse]; omega), zm₂]
    simp [Counters.projectedPrefix, hi', List.map_reverse]
  have read₃ (i : ℕ) (hi : i < (cs.map (BitVec.setWidth p)).length) :
      z₃.mem (q₃ + i) = (cs.map (BitVec.setWidth p))[i].toNat := by
    have hi' : i < cs.length := by simpa using hi
    rw [zm₃]
    simp [Counters.projectedPrefix, hi']
  obtain ⟨u, hu, uf, um, _⟩ := selectAddress_exec (W := W) (b := q₂) (v := v₂) (h := h) true
    selectedForward
    (bs.map (BitVec.setWidth p)) g z₃ read₂ (hfit.of_le (by simp only [List.length_map]; omega))
  obtain ⟨y, hy, yb, ym, _⟩ := selectAddress_exec (W := W) (b := q₃) (v := v₃) (h := h₄) false
    selectedBackward
    (cs.map (BitVec.setWidth p)) g u
    (by intro i hi; rw [um]; exact read₃ i hi)
    (hfit.of_le (by simp only [List.length_map]; omega))
  obtain ⟨z, hz, zg, zi, zm, _⟩ := selectCounterIndices_exec g y (hfit.of_le (by omega))
  have exec := he₂.seq (he₃.seq (hu.seq (hy.seq hz)))
  refine ⟨z, ?_, ?_, ?_, zg, zi, ?_, ?_, ?_⟩
  · simpa only [selectQueries, List.length_map, List.length_reverse,
      Bool.false_eq_true, ↓reduceIte] using exec
  · rw [hz.regs_eq (by
      unfold selectCounterIndices
      simp only [Code.Preserves, Op.dest, ne_eq, Option.some.injEq]
      decide), hy.regs_eq (by
      unfold selectAddress
      simp only [Code.Preserves, Op.dest, ne_eq, Option.some.injEq]
      decide)]
    simpa only [List.length_map, ↓reduceIte] using uf
  · rw [hz.regs_eq (by
      unfold selectCounterIndices
      simp only [Code.Preserves, Op.dest, ne_eq, Option.some.injEq]
      decide)]
    simpa only [List.length_map, Bool.false_eq_true, ↓reduceIte] using yb
  · intro i hi
    rw [zm, ym, um]; exact read₂ i hi
  · intro i hi
    rw [zm, ym, um]; exact read₃ i hi
  · intro a ha
    rw [zm, ym, um, zf₃ _ (by simp only [List.length_reverse]; omega), zf₂ _ (by omega)]

end Cslib.Cryptanalysis.AddXNOR.Native.Quarter
