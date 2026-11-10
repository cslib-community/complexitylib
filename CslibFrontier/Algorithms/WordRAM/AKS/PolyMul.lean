/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Notation
public import CslibFrontier.Foundations.NumberTheory.AKS.Coefficients
import Mathlib.Tactic.Linarith

import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Multiplication modulo `X^r - 1` and `n` on the word RAM

Polynomials modulo `X^r - 1` with coefficients modulo `n` are stored as arrays of `r` words. The
program clears the destination array and then, for every pair `i, j < r`, adds `p i * q j` into
cell `(i + j) mod r`, reducing modulo `n` after each addition: schoolbook multiplication, with
`O(r²)` instructions. Every product and sum stays below `n² + n`. The result has the coefficients
`Cslib.AKS.mulCoeff n r p q`, so its class is the product of the classes of the factors
(`Cslib.AKS.toQuot_mulCoeff`). The factors may coincide, which is how a polynomial is squared; the
destination must be disjoint from both.

## Main definitions

* `Cslib.Algorithms.WordRAM.AKS.PolyMul.program`: the multiplication program.

## Main results

* `Cslib.Algorithms.WordRAM.AKS.PolyMul.exec`: the destination receives `Cslib.AKS.mulCoeff`
  within `14 (r + 1)²` instructions, and no other memory cell changes.

## References

* [M. Agrawal, N. Kayal, N. Saxena, *PRIMES is in P*][AKS2004]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.AKS.PolyMul

open Cslib.WordRAM Finset

/-- Base address of the first factor. -/
abbrev pa : Fin 14 := 0
/-- Base address of the second factor. -/
abbrev pb : Fin 14 := 1
/-- Base address of the product. -/
abbrev pt : Fin 14 := 2
/-- The number `r` of coefficients. -/
abbrev rr : Fin 14 := 3
/-- The modulus `n` of the coefficients. -/
abbrev nn : Fin 14 := 4
/-- Index into the first factor. -/
abbrev i : Fin 14 := 5
/-- Index into the second factor. -/
abbrev j : Fin 14 := 6
/-- Index `(i + j) mod r` into the product. -/
abbrev k : Fin 14 := 7
/-- Address scratch. -/
abbrev addr : Fin 14 := 8
/-- The coefficient `p i`. -/
abbrev u : Fin 14 := 9
/-- The product `p i * q j`. -/
abbrev v : Fin 14 := 10
/-- The updated product coefficient. -/
abbrev s : Fin 14 := 11
/-- Constant one. -/
abbrev one : Fin 14 := 12
/-- Constant zero. -/
abbrev zero : Fin 14 := 13

/-- Clear one cell of the product. -/
def clearBody : Code .standard 14 := ram[ addr ← pt + i; *addr ← zero; i ← i + one ]

/-- Form `p i * q j` and the index `(i + j) mod r`. -/
def innerProd : Code .standard 14 := ram[
  addr ← pb + j; v ← *addr; v ← u * v; k ← i + j; k ← k % rr ]

/-- Add the product into its cell, reducing modulo `n`, and advance `j`. -/
def innerAcc : Code .standard 14 := ram[
  addr ← pt + k; s ← *addr; s ← s + v; s ← s % nn; *addr ← s; j ← j + one ]

/-- Add `p i * q j` into cell `(i + j) mod r` of the product. -/
def innerBody : Code .standard 14 := .seq innerProd innerAcc

/-- Add the products of `p i` with every coefficient of `q`. -/
def outerBody : Code .standard 14 :=
  .seq (ram[ addr ← pa + i; u ← *addr; j ← #0 ])
    (.seq (.loop (.lt j rr) innerBody) (ram[ i ← i + one ]))

/-- Clear the product, then accumulate every pair of coefficients. -/
def program : Code .standard 14 :=
  .seq (ram[ one ← #1; zero ← #0; i ← #0 ]) (.seq (.loop (.lt i rr) clearBody)
    (.seq (ram[ i ← #0 ]) (.loop (.lt i rr) outerBody)))

/-- Memory holding `f` in the block `[t, t + len)` and agreeing with `m` elsewhere. -/
private def view (m : ℕ → ℕ) (t len : ℕ) (f : ℕ → ℕ) (a : ℕ) : ℕ :=
  if t ≤ a ∧ a < t + len then f (a - t) else m a

private theorem view_of_not_mem {m f : ℕ → ℕ} {t len a : ℕ} (h : ¬(t ≤ a ∧ a < t + len)) :
    view m t len f a = m a := by
  simp only [view, h, ↓reduceIte]

private theorem view_add {m f : ℕ → ℕ} {t len k₀ : ℕ} (h : k₀ < len) :
    view m t len f (t + k₀) = f k₀ := by
  simp only [view]
  split_ifs with h'
  · rw [Nat.add_sub_cancel_left]
  · omega

private theorem view_update {m f : ℕ → ℕ} {t len k₀ : ℕ} (hk₀ : k₀ < len) (val : ℕ) :
    Function.update (view m t len f) (t + k₀) val = view m t len (Function.update f k₀ val) := by
  funext a
  by_cases ha : a = t + k₀
  · subst ha; simp [view, hk₀]
  · rw [Function.update_of_ne ha]
    simp only [view]
    split_ifs with h
    · rw [Function.update_of_ne (by omega)]
    · rfl

/-- The partial row sum `∑_{j' < j, (i + j') mod r = k} p i q j'`. -/
private def rowSum (p q : ℕ → ℕ) (r i j k : ℕ) : ℕ :=
  ∑ j' ∈ range j, if (i + j') % r = k then p i * q j' else 0

/-- The sum over all complete rows `i' < i` and the first `j` entries of row `i`. -/
private def partSum (p q : ℕ → ℕ) (r i j k : ℕ) : ℕ :=
  ∑ i' ∈ range i, rowSum p q r i' r k + rowSum p q r i j k

private theorem partSum_succ (p q : ℕ → ℕ) (r i j k : ℕ) :
    partSum p q r i (j + 1) k =
      partSum p q r i j k + if (i + j) % r = k then p i * q j else 0 := by
  simp only [partSum, rowSum, sum_range_succ]; ring

private theorem partSum_row (p q : ℕ → ℕ) (r i k : ℕ) :
    partSum p q r i r k = partSum p q r (i + 1) 0 k := by
  simp [partSum, rowSum, sum_range_succ]

/-- The registers that every phase preserves. -/
private def Regs (a b t r n : ℕ) (y : Data 14) : Prop := y.regs pa = a ∧ y.regs pb = b ∧
  y.regs pt = t ∧ y.regs rr = r ∧ y.regs nn = n ∧ y.regs one = 1 ∧ y.regs zero = 0

/-- The block hypotheses of `exec`, with `m` the original memory. -/
private structure Hyp (w a b t r n : ℕ) (m : ℕ → ℕ) : Prop where
  hn0 : 0 < n
  hta : t + r ≤ a ∨ a + r ≤ t
  htb : t + r ≤ b ∨ b + r ≤ t
  hpa : ∀ i' < r, m (a + i') < n
  hpb : ∀ j' < r, m (b + j') < n
  hfa : Fits w (a + r)
  hfb : Fits w (b + r)
  hft : Fits w (t + r)
  hf2 : Fits w (2 * r)
  hfn : Fits w (n * n + n)

private theorem clear_step {w a b t r n : ℕ} {m : ℕ → ℕ} (H : Hyp w a b t r n m) (y : Data 14)
    (hy : Regs a b t r n y ∧ y.mem = view m t (y.regs i) (fun _ => 0))
    (hc : y.regs i < r) :
    ∃ z, ExecWithin w clearBody y z 3 ∧
      (Regs a b t r n z ∧ z.mem = view m t (y.regs i + 1) (fun _ => 0)) ∧
      z.regs i = y.regs i + 1 := by
  obtain ⟨⟨hya, hyb, hyt, hyr, hyn, hyo, hyz⟩, hym⟩ := hy
  have hft := H.hft
  have hf2 := H.hf2
  unfold clearBody Regs
  wram_exec [hya, hyb, hyt, hyr, hyn, hyo, hyz]
  wram_simp [hya, hyb, hyt, hyr, hyn, hyo, hyz]
  rw [hym]
  funext a'
  simp only [Function.update_apply, view]
  split_ifs <;> first | rfl | omega

private theorem inner_step {w a b t r n I : ℕ} {m : ℕ → ℕ} (H : Hyp w a b t r n m) (hIr : I < r)
    (y : Data 14)
    (hy : Regs a b t r n y ∧ y.regs i = I ∧ y.regs u = m (a + I) ∧
      y.mem = view m t r
        (fun k' => partSum (fun i' => m (a + i')) (fun j' => m (b + j')) r I (y.regs j) k' % n))
    (hc : y.regs j < r) :
    ∃ z, ExecWithin w innerBody y z 11 ∧
      (Regs a b t r n z ∧ z.regs i = I ∧ z.regs u = m (a + I) ∧
        z.mem = view m t r
          (fun k' =>
            partSum (fun i' => m (a + i')) (fun j' => m (b + j')) r I (y.regs j + 1) k' % n)) ∧
      z.regs j = y.regs j + 1 := by
  obtain ⟨⟨hya, hyb, hyt, hyr, hyn, hyo, hyz⟩, hyi, hyu, hym⟩ := hy
  obtain ⟨hn0, -, htb, hpa, hpb, -, hfb, hft, hf2, hfn⟩ := H
  obtain ⟨J, hJ⟩ : ∃ J, y.regs j = J := ⟨_, rfl⟩
  have hlt : J < r := by simpa only [hJ] using hc
  rw [hJ] at hym
  obtain ⟨k₀, hk₀⟩ : ∃ k₀, (I + J) % r = k₀ := ⟨_, rfl⟩
  have hk₀r : k₀ < r := hk₀ ▸ Nat.mod_lt _ (by omega)
  obtain ⟨p, hp⟩ : ∃ p, m (a + I) = p := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, m (b + J) = q := ⟨_, rfl⟩
  have hQJ : y.mem (b + J) = q := by
    rw [hym, view_of_not_mem (by rcases htb with h | h <;> omega), hq]
  obtain ⟨S, hS⟩ : ∃ S, partSum (fun i' => m (a + i')) (fun j' => m (b + j')) r I J k₀ = S :=
    ⟨_, rfl⟩
  have hSm : y.mem (t + k₀) = S % n := by rw [hym, view_add hk₀r, hS]
  have hprod : p * q ≤ n * n := Nat.mul_le_mul (hp ▸ hpa I hIr).le (hq ▸ hpb J hlt).le
  have hSn : S % n < n := Nat.mod_lt _ hn0
  have hRn : (S % n + p * q) % n < n := Nat.mod_lt _ hn0
  unfold innerBody innerProd innerAcc Regs
  wram_exec [hya, hyb, hyt, hyr, hyn, hyo, hyz, hyi, hyu, hp, hJ, hQJ, hk₀, hSm]
  wram_simp [hya, hyb, hyt, hyr, hyn, hyo, hyz, hyi, hyu, hp, hJ]
  rw [hym, view_update hk₀r]
  congr 1 with k' : 1
  rw [partSum_succ, Function.update_apply, hp, hq]
  by_cases h : k' = k₀
  · subst h; simp [hk₀, hS, Nat.mod_add_mod]
  · have h' : ¬(I + J) % r = k' := fun h' => h (hk₀ ▸ h'.symm)
    simp only [h, h', ↓reduceIte, Nat.add_zero]

private theorem outer_step {w a b t r n : ℕ} {m : ℕ → ℕ} (H : Hyp w a b t r n m) (y : Data 14)
    (hy : Regs a b t r n y ∧ y.mem = view m t r
      (fun k' => partSum (fun i' => m (a + i')) (fun j' => m (b + j')) r (y.regs i) 0 k' % n))
    (hc : y.regs i < r) :
    ∃ z, ExecWithin w outerBody y z (13 * r + 6) ∧
      (Regs a b t r n z ∧ z.mem = view m t r
        (fun k' =>
          partSum (fun i' => m (a + i')) (fun j' => m (b + j')) r (y.regs i + 1) 0 k' % n)) ∧
      z.regs i = y.regs i + 1 := by
  obtain ⟨⟨hya, hyb, hyt, hyr, hyn, hyo, hyz⟩, hym⟩ := hy
  obtain ⟨I, hI⟩ : ∃ I, y.regs i = I := ⟨_, rfl⟩
  have hlt : I < r := by simpa only [hI] using hc
  rw [hI] at hym
  have hPI : y.mem (a + I) = m (a + I) := by
    rw [hym, view_of_not_mem (by rcases H.hta with h | h <;> omega)]
  have hfa := H.hfa
  have hf2 := H.hf2
  let P (k : ℕ) (z : Data 14) : Prop :=
    Regs a b t r n z ∧ z.regs i = I ∧ z.regs u = m (a + I) ∧
      z.mem = view m t r
        (fun k' => partSum (fun i' => m (a + i')) (fun j' => m (b + j')) r I k k' % n)
  unfold outerBody
  wram_exec [hya, hI, hPI]
  refine WP.name fun y₁ hy₁ => ?_
  have hj₁ : y₁.regs j = 0 := by subst hy₁; wram_simp
  have hP₁ : P (y₁.regs j) y₁ := by
    subst hy₁
    simp only [P, Regs]
    wram_simp [hya, hyb, hyt, hyr, hyn, hyo, hyz, hI, hym]
  obtain ⟨y₂, hrun₂, ⟨⟨hya₂, hyb₂, hyt₂, hyr₂, hyn₂, hyo₂, hyz₂⟩, hyi₂, _, hym₂⟩, _⟩ :=
    ExecWithin.loop_count P (fun _ ⟨⟨_, _, _, hlim, _, _, _⟩, _⟩ => hlim) (inner_step H hlt)
      (by omega) hP₁
  refine WP.of_execWithin hrun₂ ?_
  unfold Regs
  wram_exec [hyi₂, hyo₂]
  wram_simp [hya₂, hyb₂, hyt₂, hyr₂, hyn₂, hyo₂, hyz₂, hyi₂, hym₂, hI, hj₁, partSum_row]

/-- **Multiplication modulo `X^r - 1` and `n`.** If the product block `[t, t + r)` is disjoint
from both factor blocks, the factors' coefficients are below `n ≥ 1`, and the word size holds the
block ends, `2 r` and `n² + n`, then the product block receives the coefficients
`Cslib.AKS.mulCoeff n r p q` within `14 (r + 1)²` instructions, and no other cell changes. -/
theorem exec {w : ℕ} (x : Data 14) {a b t r n : ℕ} (ha : x.regs pa = a) (hb : x.regs pb = b)
    (ht : x.regs pt = t) (hr : x.regs rr = r) (hn : x.regs nn = n) (hn0 : 0 < n)
    (hta : t + r ≤ a ∨ a + r ≤ t) (htb : t + r ≤ b ∨ b + r ≤ t)
    (hpa : ∀ i' < r, x.mem (a + i') < n) (hpb : ∀ j' < r, x.mem (b + j') < n)
    (hfa : Fits w (a + r)) (hfb : Fits w (b + r)) (hft : Fits w (t + r)) (hf2 : Fits w (2 * r))
    (hfn : Fits w (n * n + n)) :
    ∃ y, ExecWithin w program x y (14 * (r + 1) * (r + 1)) ∧
      (∀ k' < r, y.mem (t + k') =
        Cslib.AKS.mulCoeff n r (fun i' => x.mem (a + i')) (fun j' => x.mem (b + j')) k') ∧
      (∀ a', ¬(t ≤ a' ∧ a' < t + r) → y.mem a' = x.mem a') ∧
      y.regs pa = a ∧ y.regs pb = b ∧ y.regs pt = t ∧ y.regs rr = r ∧ y.regs nn = n := by
  have H : Hyp w a b t r n x.mem := ⟨hn0, hta, htb, hpa, hpb, hfa, hfb, hft, hf2, hfn⟩
  let Clear (k : ℕ) (z : Data 14) := Regs a b t r n z ∧
    z.mem = view x.mem t k (fun _ => 0)
  let Product (k : ℕ) (z : Data 14) := Regs a b t r n z ∧ z.mem =
    view x.mem t r (fun k' =>
      partSum (fun i' => x.mem (a + i')) (fun j' => x.mem (b + j')) r k 0 k' % n)
  unfold program
  wram_exec
  refine WP.name fun x₀ hx₀ => ?_
  have hi₀ : x₀.regs i = 0 := by subst hx₀; wram_simp
  have hx₀' : Clear (x₀.regs i) x₀ := by
    subst hx₀
    simp only [Clear, Regs]
    wram_simp [ha, hb, ht, hr, hn]
    funext a'
    simp [view]
  obtain ⟨y₁, hrun₁, ⟨⟨hya, hyb, hyt, hyr, hyn, hyo, hyz⟩, hym⟩, _⟩ :=
    ExecWithin.loop_count Clear (fun _ ⟨⟨_, _, _, hlim, _, _, _⟩, _⟩ => hlim) (clear_step H)
      (by omega) hx₀'
  refine WP.of_execWithin hrun₁ ?_
  wram_exec
  refine WP.name fun y₂ hy₂ => ?_
  have hi₂ : y₂.regs i = 0 := by subst hy₂; wram_simp
  have hy₂' : Product (y₂.regs i) y₂ := by
    subst hy₂
    simp only [Product, Regs]
    wram_simp [hya, hyb, hyt, hyr, hyn, hyo, hyz, hym]
    congr 1
  obtain ⟨y₃, hrun₃, ⟨⟨hya₃, hyb₃, hyt₃, hyr₃, hyn₃, _, _⟩, hym₃⟩, _⟩ :=
    ExecWithin.loop_count Product (fun _ ⟨⟨_, _, _, hlim, _, _, _⟩, _⟩ => hlim) (outer_step H)
      (by omega) hy₂'
  refine WP.of_execWithin hrun₃ ⟨?_, fun k' hk' => ?_, fun a' ha' => ?_, hya₃, hyb₃, hyt₃, hyr₃,
    hyn₃⟩
  · rw [hi₀, hi₂, Nat.sub_zero]
    nlinarith
  · rw [hym₃, view_add hk']
    simp only [Cslib.AKS.mulCoeff, partSum, rowSum, sum_range_zero, add_zero]
  · rw [hym₃, view_of_not_mem ha']

end Cslib.Algorithms.WordRAM.AKS.PolyMul
