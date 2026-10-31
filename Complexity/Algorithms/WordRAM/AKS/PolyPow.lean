/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.AKS.PolyMul
public import Complexity.Computability.WordRAM.Copy
public import Complexity.Computability.WordRAM.RegisterFrame
public import Mathlib.Data.Nat.Size

/-!
# Powers modulo `X^r - 1` and `n` on the word RAM

Raising a polynomial modulo `X^r - 1` and `n` to the power `e` by repeated squaring: with a result
block `R`, a base block `B` and a scratch block `T`, each round multiplies `R` by `B` into `T` and
copies it back when `e` is odd, squares `B` into `T` and copies it back, and halves `e`. The class
of `R · B^e` is invariant, so when `e` reaches `0` the result block holds the class of
`R · B^e` for the original `R`, `B` and `e`. The loop makes `Nat.size e` rounds, each of `O(r²)`
instructions (`Cslib.Algorithms.WordRAM.AKS.PolyMul.program` and
`Cslib.WordRAM.ArrayCopy.program`). This is the polynomial arithmetic of step 5 of the AKS
algorithm [Agrawal, Kayal, Saxena, Section 4][AKS2004].

## Main definitions

* `Cslib.Algorithms.WordRAM.AKS.PolyPow.program`: the repeated-squaring loop.
* `Cslib.Algorithms.WordRAM.AKS.PolyPow.time`: its instruction bound.

## Main results

* `Cslib.Algorithms.WordRAM.AKS.PolyPow.exec`: the result block receives the coefficients of
  `R · B^e` within `time r e` instructions.

## References

* [M. Agrawal, N. Kayal, N. Saxena, *PRIMES is in P*][AKS2004]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.AKS.PolyPow

open Cslib.WordRAM Cslib.AKS Polynomial

/-- Base address of the result block. -/
abbrev R : Fin 21 := 0
/-- Base address of the base block. -/
abbrev B : Fin 21 := 1
/-- Base address of the scratch block. -/
abbrev T : Fin 21 := 2
/-- The number `r` of coefficients. -/
abbrev rr : Fin 21 := 3
/-- The modulus `n` of the coefficients. -/
abbrev nn : Fin 21 := 4
/-- The exponent, halved every round. -/
abbrev e : Fin 21 := 5
/-- The parity of the exponent. -/
abbrev par : Fin 21 := 6
/-- Constant two. -/
abbrev two : Fin 21 := 7
/-- Constant zero, for the loop test. -/
abbrev z : Fin 21 := 8
/-- First argument of the multiplication, and source of the copy. -/
abbrev pa : Fin 21 := 9
/-- Second argument of the multiplication, and destination of the copy. -/
abbrev pb : Fin 21 := 10
/-- Product block of the multiplication. -/
abbrev pt : Fin 21 := 11

/-- The multiplication runs on `pa`, `pb`, `pt`, `rr`, `nn` and the scratch registers `12, …, 20`.
-/
def mulMap : Fin 14 → Fin 21 := ![pa, pb, pt, rr, nn, 12, 13, 14, 15, 16, 17, 18, 19, 20]

/-- The copy runs from `pa` to `pb` over `rr` words, with scratch among `12, …, 20`. -/
def copyMap : Fin 7 → Fin 21 := ![pa, pb, rr, 12, 15, 16, 19]

theorem mulMap_injective : mulMap.Injective := by decide
theorem copyMap_injective : copyMap.Injective := by decide

/-- The multiplication touches no register below `9` other than `rr` and `nn`. -/
private theorem mulMap_ne {j : Fin 21} (hj : j.val < 9) (hr : j ≠ rr) (hn : j ≠ nn) (a : Fin 14) :
    mulMap a ≠ j := by
  intro h
  subst h
  fin_cases a <;> simp_all [mulMap]

/-- The copy touches no register below `9` other than `rr`. -/
private theorem copyMap_ne {j : Fin 21} (hj : j.val < 9) (hr : j ≠ rr) (a : Fin 7) :
    copyMap a ≠ j := by
  intro h
  subst h
  fin_cases a <;> simp_all [copyMap]

/-- Multiply the blocks at `x` and `y` into `T`, then copy `T` into the block at `d`. -/
def mulInto (x y d : Fin 21) : Code .standard 21 :=
  .seq (ram[ pa ← x; pb ← y; pt ← T ]) (.seq (PolyMul.program.rename mulMap)
    (.seq (ram[ pa ← T; pb ← d ]) (ArrayCopy.program.rename copyMap)))

/-- One round: multiply `R` by `B` if `e` is odd, square `B`, and halve `e`. -/
def body : Code .standard 21 := ram[
  par ← e % two; if z < par then [ ⟪mulInto R B R⟫ ] else [ par ← par ]; ⟪mulInto B B B⟫;
  e ← e / two ]

/-- Repeated squaring while the exponent is positive. -/
def program : Code .standard 21 := .seq (ram[ two ← #2; z ← #0 ]) (.loop (.lt z e) body)

/-- The instruction bound of one multiplication followed by a copy. -/
def mulTime (r : ℕ) : ℕ := 14 * (r + 1) * (r + 1) + 7 * r + 9

/-- The instruction bound of `program`: `Nat.size e` rounds of two multiplications. -/
def time (r e : ℕ) : ℕ := Nat.size e * (2 * mulTime r + 6) + 4

/-- Halving a positive number shortens its binary representation. -/
theorem size_div_two_lt {m : ℕ} (hm : 0 < m) : Nat.size (m / 2) < Nat.size m := by
  have hs : 0 < Nat.size m := Nat.size_pos.mpr hm
  have hlt : m < 2 ^ Nat.size m := Nat.lt_size_self m
  have : Nat.size (m / 2) ≤ Nat.size m - 1 := by
    rw [Nat.size_le]
    have h2 : 2 ^ Nat.size m = 2 * 2 ^ (Nat.size m - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  omega

private theorem mulInto_exec {w : ℕ} (X : Data 21) {x y d : Fin 21} (hx : x.val < 9)
    (hy : y.val < 9) (hd : d.val < 9) {a b t dd r n : ℕ} (ha : X.regs x = a) (hb : X.regs y = b)
    (ht : X.regs T = t) (hdd : X.regs d = dd) (hr : X.regs rr = r) (hn : X.regs nn = n)
    (hn0 : 0 < n) (hta : t + r ≤ a ∨ a + r ≤ t) (htb : t + r ≤ b ∨ b + r ≤ t)
    (htd : t + r ≤ dd ∨ dd + r ≤ t)
    (hpa : ∀ i < r, X.mem (a + i) < n) (hpb : ∀ j < r, X.mem (b + j) < n)
    (hfa : Fits w (a + r)) (hfb : Fits w (b + r)) (hft : Fits w (t + r)) (hfd : Fits w (dd + r))
    (hf2 : Fits w (2 * r)) (hfn : Fits w (n * n + n)) :
    ∃ Y, ExecWithin w (mulInto x y d) X Y (mulTime r) ∧
      (∀ k < r, Y.mem (dd + k) =
        mulCoeff n r (fun i => X.mem (a + i)) (fun j => X.mem (b + j)) k) ∧
      (∀ a', ¬(t ≤ a' ∧ a' < t + r) → ¬(dd ≤ a' ∧ a' < dd + r) → Y.mem a' = X.mem a') ∧
      (∀ j : Fin 21, j.val < 9 → Y.regs j = X.regs j) := by
  have hxa : x ≠ pa := fun h => by subst h; simp at hx
  have hya : y ≠ pa := fun h => by subst h; simp at hy
  have hyb : y ≠ pb := fun h => by subst h; simp at hy
  have hda : d ≠ pa := fun h => by subst h; simp at hd
  have hdb : d ≠ pb := fun h => by subst h; simp at hd
  have h1 : Fits w 1 := hfn.of_le (by nlinarith)
  -- Set the arguments of the multiplication.
  let X₁ := ((X.set pa a).set pb b).set pt t
  have hrun₁ : ExecWithin (B := .standard) w (ram[ pa ← x; pb ← y; pt ← T ]) X X₁ 3 := by
    ram_eval [X₁, ha, hb, ht, hxa, hya, hyb]
  have hX₁ (j : Fin 21) (hj : j.val < 9) : X₁.regs j = X.regs j := by
    have h9 : j ≠ pa ∧ j ≠ pb ∧ j ≠ pt := by
      refine ⟨?_, ?_, ?_⟩ <;> (intro h; subst h; simp at hj)
    simp [X₁, h9.1, h9.2.1, h9.2.2]
  -- Multiply.
  obtain ⟨Y₁, hrun₂, hprod, hframe, -, -, -, hY₁r, hY₁n⟩ :=
    PolyMul.exec (w := w) (X₁.comap mulMap) (a := a) (b := b) (t := t) (r := r) (n := n)
      (by change X₁.regs pa = a; simp +decide [X₁]) (by change X₁.regs pb = b; simp +decide [X₁])
      (by change X₁.regs pt = t; simp +decide [X₁])
      (by change X₁.regs rr = r; rw [hX₁ rr (by simp), hr])
      (by change X₁.regs nn = n; rw [hX₁ nn (by simp), hn])
      hn0 hta htb hpa hpb hfa hfb hft hf2 hfn
  have hrun₂' := hrun₂.rename mulMap_injective
  set Y₁' := Y₁.extend mulMap X₁ with hY₁'
  have hY₁'m : Y₁'.mem = Y₁.mem := rfl
  have hY₁'r (j : Fin 21) (hj : j.val < 9) : Y₁'.regs j = X.regs j := by
    by_cases hjr : j = rr
    · subst hjr
      rw [hr, hY₁', show rr = mulMap PolyMul.rr from rfl]
      exact (mulMap_injective.extend_apply _ _ _).trans hY₁r
    by_cases hjn : j = nn
    · subst hjn
      rw [hn, hY₁', show nn = mulMap PolyMul.nn from rfl]
      exact (mulMap_injective.extend_apply _ _ _).trans hY₁n
    rw [hrun₂'.regs_eq (Code.preserves_rename_of_forall_ne _ _ _ (mulMap_ne hj hjr hjn)),
      hX₁ j hj]
  -- Set the arguments of the copy.
  let X₂ := (Y₁'.set pa t).set pb dd
  have hrun₃ : ExecWithin (B := .standard) w (ram[ pa ← T; pb ← d ]) Y₁' X₂ 2 := by
    ram_eval [X₂, hY₁'r T (by simp), ht, hY₁'r d hd, hdd, hda]
  have hX₂ (j : Fin 21) (hj : j.val < 9) : X₂.regs j = X.regs j := by
    have h9 : j ≠ pa ∧ j ≠ pb := by
      refine ⟨?_, ?_⟩ <;> (intro h; subst h; simp at hj)
    simp [X₂, h9.1, h9.2, hY₁'r j hj]
  -- Copy.
  have hXr : X₂.regs rr = r := by rw [hX₂ rr (by simp), hr]
  have hsrc : (X₂.comap copyMap).regs ArrayCopy.src = t := by
    change X₂.regs pa = t; simp +decide [X₂]
  have hdst : (X₂.comap copyMap).regs ArrayCopy.dst = dd := by
    change X₂.regs pb = dd; simp +decide [X₂]
  have hlen : (X₂.comap copyMap).regs ArrayCopy.len = r := hXr
  obtain ⟨Y₂, hrun₄, hY₂m, -, -, hY₂len⟩ := ArrayCopy.exec_of_separated_or_eq (w := w)
    (X₂.comap copyMap) h1 (by rw [hsrc, hlen]; exact hft) (by rw [hdst, hlen]; exact hfd)
    (by rw [hsrc, hdst, hlen]; omega)
  have hrun₄' := hrun₄.rename copyMap_injective
  rw [hlen, hsrc, hdst] at hY₂m
  rw [hlen] at hrun₄'
  refine ⟨Y₂.extend copyMap X₂, ?_, ?_, ?_, ?_⟩
  · exact (hrun₁.seq (hrun₂'.seq (hrun₃.seq hrun₄'))).mono (by unfold mulTime; omega)
  · intro k hk
    change Y₂.mem (dd + k) = _
    rw [hY₂m, ArrayCopy.copyPrefix_read hk]
    exact hprod k hk
  · intro a' hat had
    change Y₂.mem a' = _
    rw [hY₂m, ArrayCopy.copyPrefix_outside had]
    exact hframe a' hat
  · intro j hj
    by_cases hjr : j = rr
    · subst hjr
      change Function.extend copyMap Y₂.regs X₂.regs (copyMap ArrayCopy.len) = X.regs rr
      rw [copyMap_injective.extend_apply, hY₂len, hlen, hr]
    rw [hrun₄'.regs_eq (Code.preserves_rename_of_forall_ne _ _ _ (copyMap_ne hj hjr)), hX₂ j hj]

/-- The hypotheses of `exec` on the three blocks, the modulus and the word size. -/
private structure Hyp (w a b t r n e₀ : ℕ) : Prop where
  hn0 : 0 < n
  hab : a + r ≤ b ∨ b + r ≤ a
  hta : t + r ≤ a ∨ a + r ≤ t
  htb : t + r ≤ b ∨ b + r ≤ t
  hfa : Fits w (a + r)
  hfb : Fits w (b + r)
  hft : Fits w (t + r)
  hf2 : Fits w (2 * r)
  hfn : Fits w (n * n + n)
  hfe : Fits w e₀

/-- The loop invariant: the registers, the reduced blocks and the class of `R · B^e`. -/
private def Inv (a b t r n e₀ : ℕ) (target : AdjoinRoot (X ^ r - 1 : (ZMod n)[X]))
    (y : Data 21) : Prop :=
  y.regs R = a ∧ y.regs B = b ∧ y.regs T = t ∧ y.regs rr = r ∧ y.regs nn = n ∧ y.regs two = 2 ∧
    y.regs z = 0 ∧ y.regs e ≤ e₀ ∧ (∀ i < r, y.mem (a + i) < n) ∧ (∀ i < r, y.mem (b + i) < n) ∧
    toQuot n r (fun i => y.mem (a + i)) * toQuot n r (fun i => y.mem (b + i)) ^ y.regs e = target

private theorem body_step {w a b t r n e₀ : ℕ} (H : Hyp w a b t r n e₀)
    {target : AdjoinRoot (X ^ r - 1 : (ZMod n)[X])} (y : Data 21)
    (hy : Inv a b t r n e₀ target y) (hc : (Cond.lt z e).Holds y) :
    ∃ y', ExecWithin w body y y' (2 * mulTime r + 4) ∧ Inv a b t r n e₀ target y' ∧
      Nat.size (y'.regs e) < Nat.size (y.regs e) := by
  obtain ⟨hyR, hyB, hyT, hyr, hyn, hy2, hyz, hye, hRred, hBred, hq⟩ := hy
  obtain ⟨E, hE⟩ : ∃ E, y.regs e = E := ⟨_, rfl⟩
  have hEpos : 0 < E := by simpa only [Cond.holds_lt, hyz, hE] using hc
  rw [hE] at hye hq
  have h2 : Fits w 2 := H.hfn.of_le (by have := H.hn0; nlinarith)
  have hfE : Fits w E := H.hfe.of_le hye
  -- The parity.
  let y₁ := y.set par (E % 2)
  have hrun₁ : ExecWithin (B := .standard) w (ram[ par ← e % two ]) y y₁ 1 := by
    ram_eval [y₁, hE, hy2, h2.of_le (Nat.mod_lt E (by norm_num)).le]
  have hy₁ (j : Fin 21) (hj : j ≠ par) : y₁.regs j = y.regs j := by simp [y₁, hj]
  have hz₁ : y₁.regs z = 0 := by rw [hy₁ z (by decide), hyz]
  have hp₁ : y₁.regs par = E % 2 := by simp [y₁]
  -- Multiply `R` by `B` when the exponent is odd.
  obtain ⟨y₂, hrun₂, hy₂r, hy₂R, hy₂Rred, hy₂B⟩ : ∃ y₂, ExecWithin w
      (.branch (.lt z par) (mulInto R B R) (ram[ par ← par ])) y₁ y₂ (mulTime r + 2) ∧
      (∀ j : Fin 21, j.val < 9 → y₂.regs j = y₁.regs j) ∧
      toQuot n r (fun i => y₂.mem (a + i)) =
        toQuot n r (fun i => y.mem (a + i)) * toQuot n r (fun i => y.mem (b + i)) ^ (E % 2) ∧
      (∀ i < r, y₂.mem (a + i) < n) ∧ (∀ i < r, y₂.mem (b + i) = y.mem (b + i)) := by
    rcases Nat.mod_two_eq_zero_or_one E with hpar | hpar
    · refine ⟨y₁.set par (y₁.regs par), ?_, ?_, ?_, ?_, ?_⟩
      · refine (ExecWithin.branch_neg ?_ ExecWithin.copy).mono (by unfold mulTime; omega)
        simp only [Cond.holds_lt, hz₁, hp₁, hpar]; omega
      · intro j _; simp
      · simp [y₁, hpar]
      · simpa [y₁] using hRred
      · intro i _; rfl
    · have hc' : (Cond.lt z par).Holds y₁ := by
        simp only [Cond.holds_lt, hz₁, hp₁, hpar]; omega
      obtain ⟨Y, hrun, hprod, hframe, hregs⟩ := mulInto_exec (w := w) y₁ (x := R) (y := B) (d := R)
        (by decide) (by decide) (by decide) (a := a) (b := b) (t := t) (dd := a) (r := r) (n := n)
        (by rw [hy₁ R (by decide), hyR]) (by rw [hy₁ B (by decide), hyB])
        (by rw [hy₁ T (by decide), hyT]) (by rw [hy₁ R (by decide), hyR])
        (by rw [hy₁ rr (by decide), hyr]) (by rw [hy₁ nn (by decide), hyn]) H.hn0 H.hta H.htb H.hta
        (by simpa [y₁] using hRred) (by simpa [y₁] using hBred) H.hfa H.hfb H.hft H.hfa H.hf2 H.hfn
      refine ⟨Y, (ExecWithin.branch_pos hc' hrun).mono (by omega), hregs, ?_, ?_, ?_⟩
      · rw [toQuot_congr hprod, toQuot_mulCoeff, hpar, pow_one]
        rfl
      · intro i hi
        rw [hprod i hi]
        exact mulCoeff_lt H.hn0 _ _ _
      · intro i hi
        refine hframe _ ?_ ?_
        · rcases H.htb with h | h <;> omega
        · rcases H.hab with h | h <;> omega
  -- Square `B`.
  have hy₂' (j : Fin 21) (hj : j.val < 9) (hjp : j ≠ par) : y₂.regs j = y.regs j := by
    rw [hy₂r j hj, hy₁ j hjp]
  obtain ⟨y₃, hrun₃, hprod₃, hframe₃, hregs₃⟩ := mulInto_exec (w := w) y₂ (x := B) (y := B)
    (d := B) (by decide) (by decide) (by decide) (a := b) (b := b) (t := t) (dd := b) (r := r)
    (n := n) (by rw [hy₂' B (by decide) (by decide), hyB])
    (by rw [hy₂' B (by decide) (by decide), hyB]) (by rw [hy₂' T (by decide) (by decide), hyT])
    (by rw [hy₂' B (by decide) (by decide), hyB]) (by rw [hy₂' rr (by decide) (by decide), hyr])
    (by rw [hy₂' nn (by decide) (by decide), hyn]) H.hn0 H.htb H.htb H.htb
    (fun i hi => by rw [hy₂B i hi]; exact hBred i hi)
    (fun i hi => by rw [hy₂B i hi]; exact hBred i hi)
    H.hfb H.hfb H.hft H.hfb H.hf2 H.hfn
  have hy₃R (i : ℕ) (hi : i < r) : y₃.mem (a + i) = y₂.mem (a + i) := by
    refine hframe₃ _ ?_ ?_
    · rcases H.hta with h | h <;> omega
    · rcases H.hab with h | h <;> omega
  -- Halve the exponent.
  have hy₃e : y₃.regs e = E := by rw [hregs₃ e (by decide), hy₂' e (by decide) (by decide), hE]
  have hy₃2 : y₃.regs two = 2 := by
    rw [hregs₃ two (by decide), hy₂' two (by decide) (by decide), hy2]
  let y₄ := y₃.set e (E / 2)
  have hrun₄ : ExecWithin (B := .standard) w (ram[ e ← e / two ]) y₃ y₄ 1 := by
    ram_eval [y₄, hy₃e, hy₃2, hfE.of_le (Nat.div_le_self E 2)]
  have hy₄ (j : Fin 21) (hj : j.val < 9) (hjp : j ≠ par) (hje : j ≠ e) : y₄.regs j = y.regs j := by
    simp only [y₄, Data.set_regs, Function.update_of_ne hje]
    rw [hregs₃ j hj, hy₂' j hj hjp]
  refine ⟨y₄, ?_, ?_, ?_⟩
  · exact (hrun₁.seq (hrun₂.seq (hrun₃.seq hrun₄))).mono (by omega)
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hy₄ R (by decide) (by decide) (by decide), hyR]
    · rw [hy₄ B (by decide) (by decide) (by decide), hyB]
    · rw [hy₄ T (by decide) (by decide) (by decide), hyT]
    · rw [hy₄ rr (by decide) (by decide) (by decide), hyr]
    · rw [hy₄ nn (by decide) (by decide) (by decide), hyn]
    · rw [hy₄ two (by decide) (by decide) (by decide), hy2]
    · rw [hy₄ z (by decide) (by decide) (by decide), hyz]
    · simp only [y₄, Data.set_regs, Function.update_self]
      exact (Nat.div_le_self E 2).trans hye
    · intro i hi
      change y₃.mem (a + i) < n
      rw [hy₃R i hi]
      exact hy₂Rred i hi
    · intro i hi
      change y₃.mem (b + i) < n
      rw [hprod₃ i hi]
      exact mulCoeff_lt H.hn0 _ _ _
    · simp only [y₄, Data.set_regs, Function.update_self]
      change toQuot n r (fun i => y₃.mem (a + i)) * toQuot n r (fun i => y₃.mem (b + i)) ^ (E / 2) =
        target
      rw [toQuot_congr hy₃R, toQuot_congr hprod₃, toQuot_mulCoeff, toQuot_congr hy₂B, hy₂R, ← hq,
        ← sq, ← pow_mul, mul_assoc, ← pow_add, Nat.mod_add_div]
  · simp only [y₄, Data.set_regs, Function.update_self, hE]
    exact size_div_two_lt hEpos

/-- **Powers modulo `X^r - 1` and `n`.** If the result, base and scratch blocks `[a, a + r)`,
`[b, b + r)` and `[t, t + r)` are pairwise disjoint, the result and base coefficients are below
`n ≥ 1`, and the word size holds the block ends, `2 r`, `n² + n` and the exponent `e`, then within
`time r e` instructions the result block receives reduced coefficients whose class is that of
`R · B^e`. -/
theorem exec {w : ℕ} (x : Data 21) {a b t r n : ℕ} (ha : x.regs R = a) (hb : x.regs B = b)
    (ht : x.regs T = t) (hr : x.regs rr = r) (hn : x.regs nn = n) (hn0 : 0 < n)
    (hab : a + r ≤ b ∨ b + r ≤ a) (hta : t + r ≤ a ∨ a + r ≤ t) (htb : t + r ≤ b ∨ b + r ≤ t)
    (hpa : ∀ i < r, x.mem (a + i) < n) (hpb : ∀ i < r, x.mem (b + i) < n)
    (hfa : Fits w (a + r)) (hfb : Fits w (b + r)) (hft : Fits w (t + r)) (hf2 : Fits w (2 * r))
    (hfn : Fits w (n * n + n)) (hfe : Fits w (x.regs e)) :
    ∃ y, ExecWithin w program x y (time r (x.regs e)) ∧
      toQuot n r (fun i => y.mem (a + i)) =
        toQuot n r (fun i => x.mem (a + i)) * toQuot n r (fun i => x.mem (b + i)) ^ x.regs e ∧
      (∀ i < r, y.mem (a + i) < n) ∧ y.regs R = a ∧ y.regs B = b ∧ y.regs T = t ∧
      y.regs rr = r ∧ y.regs nn = n := by
  have H : Hyp w a b t r n (x.regs e) := ⟨hn0, hab, hta, htb, hfa, hfb, hft, hf2, hfn, hfe⟩
  have h2 : Fits w 2 := hfn.of_le (by nlinarith)
  let x₀ := (x.set two 2).set z 0
  have hrun₀ : ExecWithin (B := .standard) w (ram[ two ← #2; z ← #0 ]) x x₀ 2 := by
    ram_eval [x₀, h2]
  have hx₀ (j : Fin 21) (h2 : j ≠ two) (hz : j ≠ z) : x₀.regs j = x.regs j := by
    simp [x₀, h2, hz]
  have hI : Inv a b t r n (x.regs e) (toQuot n r (fun i => x.mem (a + i)) *
      toQuot n r (fun i => x.mem (b + i)) ^ x.regs e) x₀ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, by simp +decide [x₀], by simp [x₀], ?_, hpa, hpb, ?_⟩
    · rw [hx₀ R (by decide) (by decide), ha]
    · rw [hx₀ B (by decide) (by decide), hb]
    · rw [hx₀ T (by decide) (by decide), ht]
    · rw [hx₀ rr (by decide) (by decide), hr]
    · rw [hx₀ nn (by decide) (by decide), hn]
    · rw [hx₀ e (by decide) (by decide)]
    · rw [hx₀ e (by decide) (by decide)]; rfl
  obtain ⟨y, hrun, hy, hc⟩ := ExecWithin.loop_invariant _ (fun y => Nat.size (y.regs e))
    (body_step H) hI
  obtain ⟨hyR, hyB, hyT, hyr, hyn, -, hyz, -, hRred, -, hq⟩ := hy
  have hy0 : y.regs e = 0 := by simp only [Cond.holds_lt, hyz] at hc; omega
  refine ⟨y, ?_, ?_, hRred, hyR, hyB, hyT, hyr, hyn⟩
  · refine (hrun₀.seq hrun).mono ?_
    rw [hx₀ e (by decide) (by decide), show 2 * mulTime r + 4 + 2 = 2 * mulTime r + 6 by ring]
    unfold time
    omega
  · rw [← hq, hy0, pow_zero, mul_one]

end Cslib.Algorithms.WordRAM.AKS.PolyPow
