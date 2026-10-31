/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.AKS.PolyArray
public import Complexity.Algorithms.WordRAM.AKS.PolyPow

/-!
# The AKS congruence for one `a` on the word RAM

Step 5 of the AKS algorithm [Agrawal, Kayal, Saxena, Section 4][AKS2004] tests
`(X + a)^n ≡ X^n + a (mod X^r - 1, n)`. The program writes the coefficients of `X + a` into a base
block `B` and those of `1` into a result block `R`, raises by repeated squaring
(`Cslib.Algorithms.WordRAM.AKS.PolyPow.program`) so that `R` holds `(X + a)^n`, writes the
coefficients of `X^n + a` into the scratch block `T`, and compares `R` with `T`. Both blocks are
reduced, so they agree exactly when the classes agree (`Cslib.AKS.toQuot_eq_toQuot_iff`), which is
the congruence (`Cslib.AKS.congruence_iff_toQuot`).

## Main definitions

* `Cslib.Algorithms.WordRAM.AKS.Congruence.program`: the congruence test.
* `Cslib.Algorithms.WordRAM.AKS.Congruence.time`: its instruction bound.

## Main results

* `Cslib.Algorithms.WordRAM.AKS.Congruence.exec`: the flag is `1` exactly when
  `Cslib.AKS.Congruence n r a` holds, within `time r n` instructions.

## References

* [M. Agrawal, N. Kayal, N. Saxena, *PRIMES is in P*][AKS2004]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.AKS.Congruence

open Cslib.WordRAM Cslib.AKS Polynomial

/-- Base address of the result block. -/
abbrev R : Fin 25 := 0
/-- Base address of the base block. -/
abbrev B : Fin 25 := 1
/-- Base address of the scratch block. -/
abbrev T : Fin 25 := 2
/-- The number `r` of coefficients. -/
abbrev rr : Fin 25 := 3
/-- The modulus `n`, which is also the exponent. -/
abbrev nn : Fin 25 := 4
/-- The exponent of the power. -/
abbrev e : Fin 25 := 5
/-- Block argument of the subroutines. -/
abbrev pa : Fin 25 := 9
/-- Second block argument of the comparison. -/
abbrev pb : Fin 25 := 10
/-- Constant one. -/
abbrev one : Fin 25 := 19
/-- The tested value `a`, preserved. -/
abbrev av : Fin 25 := 21
/-- The exponent residue for `Fill`. -/
abbrev er : Fin 25 := 22
/-- The constant term for `Fill`. -/
abbrev aa : Fin 25 := 23
/-- The answer: `1` when the congruence holds. -/
abbrev flag : Fin 25 := 24

/-- The power runs on the first `21` registers. -/
def powMap : Fin 21 → Fin 25 := Fin.castLE (by norm_num)

/-- `Fill` writes the block at `pa`, with scratch shared with the power. -/
def fillMap : Fin 10 → Fin 25 := ![pa, rr, nn, er, aa, 12, 15, 16, one, 20]

/-- `Compare` compares the blocks at `pa` and `pb`. -/
def cmpMap : Fin 9 → Fin 25 := ![pa, pb, rr, 12, 15, 16, 17, flag, one]

theorem powMap_injective : powMap.Injective := Fin.castLE_injective _
theorem fillMap_injective : fillMap.Injective := by decide
theorem cmpMap_injective : cmpMap.Injective := by decide

/-- Write `X^e + a` into the block at `pa`. -/
def fill : Code .standard 25 := Fill.program.rename fillMap

/-- Raise `R` by `B` to the power in `e`. -/
def pow : Code .standard 25 := PolyPow.program.rename powMap

/-- Compare the blocks at `pa` and `pb`. -/
def cmp : Code .standard 25 := Compare.program.rename cmpMap

/-- Write `X + a` into `B` and `1` into `R`, raise to the power `n`, write `X^n + a` into `T`, and
compare `R` with `T`. -/
def program : Code .standard 25 :=
  .seq (ram[ one ← #1; er ← one % rr; aa ← av; pa ← B ]) (.seq fill
    (.seq (ram[ er ← #0; aa ← #0; pa ← R ]) (.seq fill
    (.seq (ram[ e ← nn ]) (.seq pow
    (.seq (ram[ er ← nn % rr; aa ← av; pa ← T ]) (.seq fill
    (.seq (ram[ pa ← R; pb ← T ]) cmp))))))))

/-- The instruction bound of `program`. -/
def time (r n : ℕ) : ℕ := PolyPow.time r n + 26 * r + 57

/-- The registers that every subroutine call preserves. -/
def Keep (j : Fin 25) : Prop := j = R ∨ j = B ∨ j = T ∨ j = rr ∨ j = nn ∨ j = av

instance : DecidablePred Keep := fun _ => by unfold Keep; infer_instance

private theorem fill_preserves : ∀ j, Keep j → fill.Preserves j := by decide
private theorem pow_preserves : ∀ j, Keep j → pow.Preserves j := by decide
private theorem cmp_preserves : ∀ j, Keep j → cmp.Preserves j := by decide

private theorem fill_exec {w : ℕ} (x : Data 25) {bs r n e' A : ℕ} (hb : x.regs pa = bs)
    (hr : x.regs rr = r) (hn : x.regs nn = n) (her : x.regs er = e' % r) (ha : x.regs aa = A)
    (hr0 : 0 < r) (hn0 : 0 < n) (hfb : Fits w (bs + r)) (hfa : Fits w A) (hfn : Fits w (n + 1)) :
    ∃ y, ExecWithin w fill x y (5 * r + 13) ∧
      (∀ k < r, y.mem (bs + k) = powAddCoeff n r e' A k) ∧
      (∀ a', ¬(bs ≤ a' ∧ a' < bs + r) → y.mem a' = x.mem a') ∧
      (∀ j, Keep j → y.regs j = x.regs j) := by
  obtain ⟨y, hy, hblk, hframe, -⟩ := Fill.exec (x.comap fillMap) hb hr hn her ha hr0 hn0 hfb hfa hfn
  have hy' := hy.rename fillMap_injective
  exact ⟨_, hy', hblk, hframe, fun j hj => hy'.regs_eq (fill_preserves j hj)⟩

private theorem cmp_exec {w : ℕ} (x : Data 25) {a b r : ℕ} (ha : x.regs pa = a)
    (hb : x.regs pb = b) (hr : x.regs rr = r) (hfa : Fits w (a + r)) (hfb : Fits w (b + r))
    (h1 : Fits w 1) :
    ∃ y, ExecWithin w cmp x y (11 * r + 5) ∧ y.regs flag ≤ 1 ∧
      (y.regs flag = 1 ↔ ∀ k' < r, x.mem (a + k') = x.mem (b + k')) ∧
      (∀ j, Keep j → y.regs j = x.regs j) := by
  obtain ⟨y, hy, hle, hiff, -⟩ := Compare.exec (x.comap cmpMap) ha hb hr hfa hfb h1
  have hy' := hy.rename cmpMap_injective
  have hfl : (y.extend cmpMap x).regs flag = y.regs Compare.flag :=
    cmpMap_injective.extend_apply _ _ Compare.flag
  exact ⟨_, hy', by rw [hfl]; exact hle, by rw [hfl]; exact hiff,
    fun j hj => hy'.regs_eq (cmp_preserves j hj)⟩

private theorem pow_exec {w : ℕ} (x : Data 25) {a b t r n : ℕ} (ha : x.regs R = a)
    (hb : x.regs B = b) (ht : x.regs T = t) (hr : x.regs rr = r) (hn : x.regs nn = n)
    (hn0 : 0 < n) (hab : a + r ≤ b ∨ b + r ≤ a) (hta : t + r ≤ a ∨ a + r ≤ t)
    (htb : t + r ≤ b ∨ b + r ≤ t) (hpa : ∀ i < r, x.mem (a + i) < n)
    (hpb : ∀ i < r, x.mem (b + i) < n) (hfa : Fits w (a + r)) (hfb : Fits w (b + r))
    (hft : Fits w (t + r)) (hf2 : Fits w (2 * r)) (hfn : Fits w (n * n + n))
    (hfe : Fits w (x.regs e)) :
    ∃ y, ExecWithin w pow x y (PolyPow.time r (x.regs e)) ∧
      toQuot n r (fun i => y.mem (a + i)) =
        toQuot n r (fun i => x.mem (a + i)) * toQuot n r (fun i => x.mem (b + i)) ^ x.regs e ∧
      (∀ i < r, y.mem (a + i) < n) ∧ (∀ j, Keep j → y.regs j = x.regs j) := by
  obtain ⟨y, hy, hq, hred, -⟩ := PolyPow.exec (x.comap powMap) ha hb ht hr hn hn0 hab hta htb hpa
    hpb hfa hfb hft hf2 hfn hfe
  have hy' := hy.rename powMap_injective
  exact ⟨_, hy', hq, hred, fun j hj => hy'.regs_eq (pow_preserves j hj)⟩

/-- The class of `1`, written as `X^0 + 0`. -/
private theorem toQuot_one {n r : ℕ} (hr : 0 < r) : toQuot n r (powAddCoeff n r 0 0) = 1 := by
  rw [toQuot_powAddCoeff hr, pow_zero, Nat.cast_zero, C_0, add_zero, map_one]

/-- **The AKS congruence for one `a`.** For `r ≥ 1` and `n ≥ 1`, with the result, base and scratch
blocks `[a, a + r)`, `[b, b + r)` and `[t, t + r)` pairwise disjoint, and the word size holding the
block ends, `2 r`, `n² + n` and the tested value `A`, the program leaves `1` in `flag` if
`(X + A)^n ≡ X^n + A (mod X^r - 1, n)` and `0` otherwise, within `time r n` instructions. -/
theorem exec {w : ℕ} (x : Data 25) {a b t r n A : ℕ} (ha : x.regs R = a) (hb : x.regs B = b)
    (ht : x.regs T = t) (hr : x.regs rr = r) (hn : x.regs nn = n) (hA : x.regs av = A)
    (hr0 : 0 < r) (hn0 : 0 < n) (hab : a + r ≤ b ∨ b + r ≤ a) (hta : t + r ≤ a ∨ a + r ≤ t)
    (htb : t + r ≤ b ∨ b + r ≤ t) (hfa : Fits w (a + r)) (hfb : Fits w (b + r))
    (hft : Fits w (t + r)) (hf2 : Fits w (2 * r)) (hfn : Fits w (n * n + n)) (hfA : Fits w A) :
    ∃ y, ExecWithin w program x y (time r n) ∧ y.regs flag ≤ 1 ∧
      (y.regs flag = 1 ↔ Congruence n r A) ∧
      ∀ j, Keep j → y.regs j = x.regs j := by
  have h1 : Fits w 1 := hfn.of_le (by nlinarith)
  have hfn1 : Fits w (n + 1) := hfn.of_le (by nlinarith)
  have hfnn : Fits w n := hfn.of_le (by nlinarith)
  have hfr : Fits w r := hf2.of_le (by omega)
  -- `B := X + A`.
  let x₁ := (((x.set one 1).set er (1 % r)).set aa A).set pa b
  have hrun₁ : ExecWithin (B := .standard) w (ram[ one ← #1; er ← one % rr; aa ← av; pa ← B ])
      x x₁ 4 := by
    ram_eval [x₁, hr, hA, hb, h1, h1.of_le (Nat.mod_le 1 r)]
  have hx₁ (j : Fin 25) (hj : Keep j) : x₁.regs j = x.regs j := by
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> simp +decide [x₁]
  obtain ⟨y₁, hrun₂, hB₁, hfr₁, hy₁⟩ := fill_exec (w := w) x₁ (bs := b) (r := r) (n := n) (e' := 1)
    (A := A) (by simp +decide [x₁]) (by rw [hx₁ rr (by simp [Keep]), hr])
    (by rw [hx₁ nn (by simp [Keep]), hn]) (by simp +decide [x₁]) (by simp +decide [x₁]) hr0 hn0
    hfb hfA hfn1
  have hy₁' (j : Fin 25) (hj : Keep j) : y₁.regs j = x.regs j := by rw [hy₁ j hj, hx₁ j hj]
  -- `R := 1`.
  let x₂ := ((y₁.set er 0).set aa 0).set pa a
  have hrun₃ : ExecWithin (B := .standard) w (ram[ er ← #0; aa ← #0; pa ← R ]) y₁ x₂ 3 := by
    ram_eval [x₂, hy₁' R (by simp [Keep]), ha]
  have hx₂ (j : Fin 25) (hj : Keep j) : x₂.regs j = x.regs j := by
    rw [← hy₁' j hj]
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> simp +decide [x₂]
  obtain ⟨y₂, hrun₄, hR₂, hfr₂, hy₂⟩ := fill_exec (w := w) x₂ (bs := a) (r := r) (n := n) (e' := 0)
    (A := 0) (by simp +decide [x₂]) (by rw [hx₂ rr (by simp [Keep]), hr])
    (by rw [hx₂ nn (by simp [Keep]), hn]) (by simp +decide [x₂]) (by simp +decide [x₂]) hr0 hn0 hfa
    (fits_zero w) hfn1
  have hy₂' (j : Fin 25) (hj : Keep j) : y₂.regs j = x.regs j := by rw [hy₂ j hj, hx₂ j hj]
  have hB₂ (k : ℕ) (hk : k < r) : y₂.mem (b + k) = powAddCoeff n r 1 A k := by
    rw [hfr₂ _ (by rcases hab with h | h <;> omega)]
    exact hB₁ k hk
  -- `R := R · B^n`.
  let x₃ := y₂.set e n
  have hrun₅ : ExecWithin (B := .standard) w (ram[ e ← nn ]) y₂ x₃ 1 := by
    ram_eval [x₃, hy₂' nn (by simp [Keep]), hn]
  have hx₃ (j : Fin 25) (hj : Keep j) : x₃.regs j = x.regs j := by
    rw [← hy₂' j hj]
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> simp +decide [x₃]
  obtain ⟨y₃, hrun₆, hq₃, hred₃, hy₃⟩ := pow_exec (w := w) x₃ (a := a) (b := b) (t := t) (r := r)
    (n := n) (by rw [hx₃ R (by simp [Keep]), ha]) (by rw [hx₃ B (by simp [Keep]), hb])
    (by rw [hx₃ T (by simp [Keep]), ht]) (by rw [hx₃ rr (by simp [Keep]), hr])
    (by rw [hx₃ nn (by simp [Keep]), hn]) hn0 hab hta htb
    (fun i hi => by rw [show x₃.mem = y₂.mem from rfl, hR₂ i hi]; exact powAddCoeff_lt hn0 _ _ _)
    (fun i hi => by rw [show x₃.mem = y₂.mem from rfl, hB₂ i hi]; exact powAddCoeff_lt hn0 _ _ _)
    hfa hfb hft hf2 hfn (by simpa [x₃] using hfnn)
  have hx₃e : x₃.regs e = n := by simp +decide [x₃]
  rw [hx₃e] at hrun₆ hq₃
  have hy₃' (j : Fin 25) (hj : Keep j) : y₃.regs j = x.regs j := by rw [hy₃ j hj, hx₃ j hj]
  -- `T := X^n + A`.
  let x₄ := ((y₃.set er (n % r)).set aa A).set pa t
  have hrun₇ : ExecWithin (B := .standard) w (ram[ er ← nn % rr; aa ← av; pa ← T ]) y₃ x₄ 3 := by
    ram_eval [x₄, hy₃' nn (by simp [Keep]), hn, hy₃' rr (by simp [Keep]), hr,
      hy₃' av (by simp [Keep]), hA, hy₃' T (by simp [Keep]), ht,
      hfnn.of_le (Nat.mod_le _ _)]
  have hx₄ (j : Fin 25) (hj : Keep j) : x₄.regs j = x.regs j := by
    rw [← hy₃' j hj]
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> simp +decide [x₄]
  obtain ⟨y₄, hrun₈, hT₄, hfr₄, hy₄⟩ := fill_exec (w := w) x₄ (bs := t) (r := r) (n := n) (e' := n)
    (A := A) (by simp +decide [x₄]) (by rw [hx₄ rr (by simp [Keep]), hr])
    (by rw [hx₄ nn (by simp [Keep]), hn]) (by simp +decide [x₄]) (by simp +decide [x₄]) hr0 hn0
    hft hfA hfn1
  have hy₄' (j : Fin 25) (hj : Keep j) : y₄.regs j = x.regs j := by rw [hy₄ j hj, hx₄ j hj]
  have hR₄ (k : ℕ) (hk : k < r) : y₄.mem (a + k) = y₃.mem (a + k) := by
    rw [hfr₄ _ (by rcases hta with h | h <;> omega)]
    rfl
  -- Compare `R` with `T`.
  let x₅ := (y₄.set pa a).set pb t
  have hrun₉ : ExecWithin (B := .standard) w (ram[ pa ← R; pb ← T ]) y₄ x₅ 2 := by
    ram_eval [x₅, hy₄' R (by simp [Keep]), ha, hy₄' T (by simp [Keep]), ht]
  have hx₅ (j : Fin 25) (hj : Keep j) : x₅.regs j = x.regs j := by
    rw [← hy₄' j hj]
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> simp +decide [x₅]
  obtain ⟨y₅, hrun₁₀, hle, hiff, hy₅⟩ := cmp_exec (w := w) x₅ (a := a) (b := t) (r := r)
    (by simp +decide [x₅]) (by simp +decide [x₅]) (by rw [hx₅ rr (by simp [Keep]), hr]) hfa hft h1
  refine ⟨y₅, ?_, hle, ?_, fun j hj => by rw [hy₅ j hj, hx₅ j hj]⟩
  · refine (hrun₁.seq (hrun₂.seq (hrun₃.seq (hrun₄.seq (hrun₅.seq (hrun₆.seq (hrun₇.seq
      (hrun₈.seq (hrun₉.seq hrun₁₀))))))))).mono ?_
    unfold time
    omega
  · rw [hiff, congruence_iff_toQuot hr0]
    change (∀ k' < r, y₄.mem (a + k') = y₄.mem (t + k')) ↔ _
    have hRred (k : ℕ) (hk : k < r) : y₄.mem (a + k) < n := by rw [hR₄ k hk]; exact hred₃ k hk
    have hTred (k : ℕ) (hk : k < r) : y₄.mem (t + k) < n := by
      rw [hT₄ k hk]; exact powAddCoeff_lt hn0 _ _ _
    rw [← toQuot_eq_toQuot_iff hn0 hr0 hRred hTred, toQuot_congr hR₄, hq₃, toQuot_congr hT₄,
      toQuot_congr (c := fun i => x₃.mem (a + i)) (fun k hk => hR₂ k hk),
      toQuot_congr (c := fun i => x₃.mem (b + i)) (fun k hk => hB₂ k hk), toQuot_one hr0, one_mul]

end Cslib.Algorithms.WordRAM.AKS.Congruence
