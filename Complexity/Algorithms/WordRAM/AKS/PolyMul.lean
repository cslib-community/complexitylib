/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Notation
public import Complexity.Foundations.NumberTheory.AKS.Coefficients
import Mathlib.Tactic.Linarith

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
    (hy : Regs a b t r n y ∧ y.regs i ≤ r ∧ y.mem = view m t (y.regs i) (fun _ => 0))
    (hc : (Cond.lt i rr).Holds y) :
    ∃ z, ExecWithin w clearBody y z 3 ∧
      (Regs a b t r n z ∧ z.regs i ≤ r ∧ z.mem = view m t (z.regs i) (fun _ => 0)) ∧
      r - z.regs i < r - y.regs i := by
  obtain ⟨⟨hya, hyb, hyt, hyr, hyn, hyo, hyz⟩, hyi, hym⟩ := hy
  obtain ⟨I, hI⟩ : ∃ I, y.regs i = I := ⟨_, rfl⟩
  have hlt : I < r := by simpa only [Cond.holds_lt, hyr, hI] using hc
  have hfaddr : Fits w (t + I) := H.hft.of_le (by omega)
  have hfinc : Fits w (I + 1) := H.hf2.of_le (by omega)
  let z := ((y.set addr (t + I)).write (t + I) 0).set i (I + 1)
  have hrun : ExecWithin (B := .standard) w clearBody y z 3 := by
    ram_eval [clearBody, z, hyt, hI, hyo, hyz, hfaddr, hfinc]
  refine ⟨z, hrun, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩ <;>
    simp +decide only [z, Data.set_regs, Data.write_regs, Data.set_mem, Data.write_mem,
      Function.update_apply, ↓reduceIte, hya, hyb, hyt, hyr, hyn, hyo, hyz, hI]
  · omega
  · rw [hym, hI]
    funext a'
    simp only [Function.update_apply, view]
    split_ifs <;> first | rfl | omega
  · omega

private theorem inner_step {w a b t r n I : ℕ} {m : ℕ → ℕ} (H : Hyp w a b t r n m) (hIr : I < r)
    (y : Data 14)
    (hy : Regs a b t r n y ∧ y.regs i = I ∧ y.regs u = m (a + I) ∧ y.regs j ≤ r ∧
      y.mem = view m t r
        (fun k' => partSum (fun i' => m (a + i')) (fun j' => m (b + j')) r I (y.regs j) k' % n))
    (hc : (Cond.lt j rr).Holds y) :
    ∃ z, ExecWithin w innerBody y z 11 ∧
      (Regs a b t r n z ∧ z.regs i = I ∧ z.regs u = m (a + I) ∧ z.regs j ≤ r ∧
        z.mem = view m t r
          (fun k' => partSum (fun i' => m (a + i')) (fun j' => m (b + j')) r I (z.regs j) k' % n)) ∧
      r - z.regs j < r - y.regs j := by
  obtain ⟨⟨hya, hyb, hyt, hyr, hyn, hyo, hyz⟩, hyi, hyu, hyj, hym⟩ := hy
  obtain ⟨J, hJ⟩ : ∃ J, y.regs j = J := ⟨_, rfl⟩
  have hlt : J < r := by simpa only [Cond.holds_lt, hyr, hJ] using hc
  rw [hJ] at hym
  have hr0 : 0 < r := by omega
  obtain ⟨k₀, hk₀⟩ : ∃ k₀, (I + J) % r = k₀ := ⟨_, rfl⟩
  have hk₀r : k₀ < r := hk₀ ▸ Nat.mod_lt _ hr0
  obtain ⟨p, hp⟩ : ∃ p, m (a + I) = p := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, m (b + J) = q := ⟨_, rfl⟩
  rw [hp] at hyu
  have hQJ : y.mem (b + J) = q := by
    rw [hym, view_of_not_mem (by rcases H.htb with h | h <;> omega), hq]
  obtain ⟨S, hS⟩ : ∃ S, partSum (fun i' => m (a + i')) (fun j' => m (b + j')) r I J k₀ = S :=
    ⟨_, rfl⟩
  have hSm : y.mem (t + k₀) = S % n := by rw [hym, view_add hk₀r, hS]
  have hPn : p < n := hp ▸ H.hpa I hIr
  have hQn : q < n := hq ▸ H.hpb J hlt
  have hprod : p * q ≤ n * n := Nat.mul_le_mul hPn.le hQn.le
  have hSn : S % n < n := Nat.mod_lt _ H.hn0
  have hf₁ : Fits w (b + J) := H.hfb.of_le (by omega)
  have hf₂ : Fits w (p * q) := H.hfn.of_le (by omega)
  have hf₃ : Fits w (I + J) := H.hf2.of_le (by omega)
  have hf₄ : Fits w k₀ := hf₃.of_le (hk₀ ▸ Nat.mod_le _ _)
  have hf₅ : Fits w (t + k₀) := H.hft.of_le (by omega)
  have hf₆ : Fits w (S % n + p * q) := H.hfn.of_le (by omega)
  have hf₇ : Fits w ((S % n + p * q) % n) := H.hfn.of_le
    (by have := Nat.mod_lt (S % n + p * q) H.hn0; nlinarith)
  have hf₈ : Fits w (J + 1) := H.hf2.of_le (by omega)
  let y₁ := ((((y.set addr (b + J)).set v q).set v (p * q)).set k (I + J)).set k k₀
  have hrun₁ : ExecWithin (B := .standard) w innerProd y y₁ 5 := by
    ram_eval [innerProd, y₁, hyb, hJ, hyu, hyi, hyr, hQJ, hk₀, hf₁, hf₂, hf₃, hf₄]
  have hy₁ (j' : Fin 14) (hj' : j' ≠ addr ∧ j' ≠ v ∧ j' ≠ k) : y₁.regs j' = y.regs j' := by
    simp [y₁, hj'.1, hj'.2.1, hj'.2.2]
  have hy₁v : y₁.regs v = p * q := by simp +decide [y₁]
  have hy₁k : y₁.regs k = k₀ := by simp [y₁]
  have hy₁m : y₁.mem = y.mem := rfl
  let z := (((((y₁.set addr (t + k₀)).set s (S % n)).set s (S % n + p * q)).set s
    ((S % n + p * q) % n)).write (t + k₀) ((S % n + p * q) % n)).set j (J + 1)
  have hrun₂ : ExecWithin (B := .standard) w innerAcc y₁ z 6 := by
    ram_eval [innerAcc, z, hy₁ pt (by decide), hy₁ s (by decide), hy₁ nn (by decide),
      hy₁ j (by decide), hy₁ one (by decide), hy₁v, hy₁k, hy₁m, hyt, hyn, hJ, hyo, hSm,
      hf₅, hf₆, hf₇, hf₈]
  have hz (j' : Fin 14) (hj' : j' ≠ addr ∧ j' ≠ v ∧ j' ≠ k ∧ j' ≠ s ∧ j' ≠ j) :
      z.regs j' = y.regs j' := by
    simp [z, hj'.1, hj'.2.1, hj'.2.2.1, hj'.2.2.2.1, hj'.2.2.2.2, y₁]
  have hzj : z.regs j = J + 1 := by simp [z]
  refine ⟨z, (hrun₁.seq hrun₂).mono (by omega), ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hz pa (by decide), hya]
  · rw [hz pb (by decide), hyb]
  · rw [hz pt (by decide), hyt]
  · rw [hz rr (by decide), hyr]
  · rw [hz nn (by decide), hyn]
  · rw [hz one (by decide), hyo]
  · rw [hz zero (by decide), hyz]
  · rw [hz i (by decide), hyi]
  · rw [hz u (by decide), hyu, hp]
  · rw [hzj]; omega
  · change Function.update y.mem (t + k₀) ((S % n + p * q) % n) = _
    rw [hzj, hym, view_update hk₀r]
    congr 1
    funext k'
    rw [partSum_succ, Function.update_apply, hp, hq]
    by_cases h : k' = k₀
    · subst h; simp [hk₀, hS, Nat.mod_add_mod]
    · have h' : ¬(I + J) % r = k' := fun h' => h (hk₀ ▸ h'.symm)
      simp only [h, h', ↓reduceIte, Nat.add_zero]
  · rw [hzj, hJ]; omega

private theorem outer_step {w a b t r n : ℕ} {m : ℕ → ℕ} (H : Hyp w a b t r n m) (y : Data 14)
    (hy : Regs a b t r n y ∧ y.regs i ≤ r ∧ y.mem = view m t r
      (fun k' => partSum (fun i' => m (a + i')) (fun j' => m (b + j')) r (y.regs i) 0 k' % n))
    (hc : (Cond.lt i rr).Holds y) :
    ∃ z, ExecWithin w outerBody y z (13 * r + 6) ∧
      (Regs a b t r n z ∧ z.regs i ≤ r ∧ z.mem = view m t r
        (fun k' => partSum (fun i' => m (a + i')) (fun j' => m (b + j')) r (z.regs i) 0 k' % n)) ∧
      r - z.regs i < r - y.regs i := by
  obtain ⟨⟨hya, hyb, hyt, hyr, hyn, hyo, hyz⟩, hyi, hym⟩ := hy
  obtain ⟨I, hI⟩ : ∃ I, y.regs i = I := ⟨_, rfl⟩
  have hlt : I < r := by simpa only [Cond.holds_lt, hyr, hI] using hc
  rw [hI] at hym
  have hfaddr : Fits w (a + I) := H.hfa.of_le (by omega)
  have hPI : y.mem (a + I) = m (a + I) := by
    rw [hym, view_of_not_mem (by rcases H.hta with h | h <;> omega)]
  let y₁ := ((y.set addr (a + I)).set u (m (a + I))).set j 0
  have hrun₁ : ExecWithin (B := .standard) w (ram[ addr ← pa + i; u ← *addr; j ← #0 ]) y y₁ 3 := by
    ram_eval [y₁, hya, hI, hfaddr, hPI]
  have hy₁ : Regs a b t r n y₁ ∧ y₁.regs i = I ∧ y₁.regs u = m (a + I) ∧ y₁.regs j ≤ r ∧
      y₁.mem = view m t r
        (fun k' => partSum (fun i' => m (a + i')) (fun j' => m (b + j')) r I (y₁.regs j) k' %
          n) := by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?mem⟩
    case mem => simpa [y₁] using hym
    all_goals simp +decide [y₁, hya, hyb, hyt, hyr, hyn, hyo, hyz, hI]
  obtain ⟨y₂, hrun₂, hy₂, hc₂⟩ := ExecWithin.loop_invariant _ (fun y => r - y.regs j)
    (inner_step H hlt) hy₁
  obtain ⟨⟨hya₂, hyb₂, hyt₂, hyr₂, hyn₂, hyo₂, hyz₂⟩, hyi₂, -, hyj₂, hym₂⟩ := hy₂
  have hJr : y₂.regs j = r := by simp only [Cond.holds_lt, hyr₂] at hc₂; omega
  have hf₉ : Fits w (I + 1) := H.hf2.of_le (by omega)
  have hrun₃ : ExecWithin (B := .standard) w (ram[ i ← i + one ]) y₂ (y₂.set i (I + 1)) 1 := by
    ram_eval [hyi₂, hyo₂, hf₉]
  refine ⟨y₂.set i (I + 1), ?_, ?_, ?_⟩
  · refine (hrun₁.seq (hrun₂.seq hrun₃)).mono ?_
    have : y₁.regs j = 0 := by simp [y₁]
    rw [this]; omega
  · refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?le, ?mem⟩
    case le => simp only [Data.set_regs, Function.update_self]; omega
    case mem =>
      simp only [Data.set_mem, Data.set_regs, Function.update_self]
      rw [hym₂, hJr]
      congr 1
      funext k'
      rw [partSum_row]
    all_goals simp +decide [hya₂, hyb₂, hyt₂, hyr₂, hyn₂, hyo₂, hyz₂]
  · simp; omega

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
  have h1 : Fits w 1 := hfn.of_le (by nlinarith)
  let x₀ := ((x.set one 1).set zero 0).set i 0
  have hrun₀ : ExecWithin (B := .standard) w (ram[ one ← #1; zero ← #0; i ← #0 ]) x x₀ 3 := by
    ram_eval [x₀, h1]
  have hx₀ : Regs a b t r n x₀ ∧ x₀.regs i ≤ r ∧
      x₀.mem = view x.mem t (x₀.regs i) (fun _ => 0) := by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?mem⟩
    case mem => funext a'; simp [x₀, view]
    all_goals simp +decide [x₀, ha, hb, ht, hr, hn]
  obtain ⟨y₁, hrun₁, hy₁, hc₁⟩ := ExecWithin.loop_invariant _ (fun y => r - y.regs i)
    (clear_step H) hx₀
  obtain ⟨⟨hya, hyb, hyt, hyr, hyn, hyo, hyz⟩, hyi, hym⟩ := hy₁
  have hir : y₁.regs i = r := by simp only [Cond.holds_lt, hyr] at hc₁; omega
  have hrun₂ : ExecWithin (B := .standard) w (ram[ i ← #0 ]) y₁ (y₁.set i 0) 1 :=
    ExecWithin.const (fits_zero w)
  have hy₂ : Regs a b t r n (y₁.set i 0) ∧ (y₁.set i 0).regs i ≤ r ∧ (y₁.set i 0).mem =
      view x.mem t r (fun k' => partSum (fun i' => x.mem (a + i')) (fun j' => x.mem (b + j')) r
        ((y₁.set i 0).regs i) 0 k' % n) := by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?mem⟩
    case mem =>
      simp only [Data.set_mem, Data.set_regs, Function.update_self]
      rw [hym, hir]
      congr 1
    all_goals simp +decide [hya, hyb, hyt, hyr, hyn, hyo, hyz]
  obtain ⟨y₃, hrun₃, hy₃, hc₃⟩ := ExecWithin.loop_invariant _ (fun y => r - y.regs i)
    (outer_step H) hy₂
  obtain ⟨⟨hya₃, hyb₃, hyt₃, hyr₃, hyn₃, -, -⟩, hyi₃, hym₃⟩ := hy₃
  have hir₃ : y₃.regs i = r := by simp only [Cond.holds_lt, hyr₃] at hc₃; omega
  refine ⟨y₃, ?_, ?_, ?_, hya₃, hyb₃, hyt₃, hyr₃, hyn₃⟩
  · refine (hrun₀.seq (hrun₁.seq (hrun₂.seq hrun₃))).mono ?_
    have h0 : x₀.regs i = 0 := by simp [x₀]
    have h0' : (y₁.set i 0).regs i = 0 := by simp
    rw [h0, h0', Nat.sub_zero]
    nlinarith
  · intro k' hk'
    rw [hym₃, hir₃, view_add hk']
    simp only [Cslib.AKS.mulCoeff, partSum, rowSum, sum_range_zero, add_zero]
  · intro a' ha'
    rw [hym₃, view_of_not_mem ha']

end Cslib.Algorithms.WordRAM.AKS.PolyMul
