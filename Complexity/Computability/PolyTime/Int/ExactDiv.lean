/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Rational.Runtime.Determinant
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.BinaryDiv
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Plain polynomial-time signed integer division and modular reduction

Plain `Turing.MultiTapeTM.ComputableInPolyTime` certificates, exact-division identities, and
sign-magnitude bit-length bounds for signed binary integer division and remainder over
`Turing.MultiTapeTM.encIntBin`:

* truncated-toward-zero division and remainder (`Int.tdiv`, `Int.tmod`);
* Euclidean division and nonnegative remainder (`Int.ediv`, `Int.emod`, and the `/` and `%`
  operators on `ℤ`);
* power-of-two modular reduction `Int.modPowTwo x ℓ = x % 2 ^ ℓ` with `ℓ` in unary
  `Turing.MultiTapeTM.encUnary`, used to recover integer counts modulo `2 ^ ℓ` in Appendix B.3
  of [OpenAI2026ETH].

All certificates are total (at divisor `0`, `a / 0 = 0`, `a.tdiv 0 = 0`, `a % 0 = a`, and
`a.tmod 0 = a`) and build on the binary natural division and modular reduction primitives of
`PolyTime/Nat/BinaryDiv` and `PolyTime/Int/BinaryDiv` without constructing new Turing machines.

## Main definitions

* `Int.modPowTwo`: least nonnegative residue `x % (2 : ℤ) ^ ℓ` modulo `2 ^ ℓ`.

## Main results

* `Int.ediv_mul_left_exact`, `Int.ediv_mul_right_exact`: exact Euclidean division of integer
  multiples `(d * q).ediv d = q` and `(q * d).ediv d = q` for `d ≠ 0`.
* `Int.modPowTwo_eq_of_dvd_sub`: unique recovery of `z ∈ [0, 2 ^ ℓ)` from any `x` with
  `2 ^ ℓ ∣ x - z`.
* `Cslib.Circuits.Rational.intBits_ediv_le`, `Cslib.Circuits.Rational.intBits_tdiv_le`,
  `Cslib.Circuits.Rational.intBits_emod_le_of_ne_zero`,
  `Cslib.Circuits.Rational.intBits_emod_le_add_one_of_ne_zero`,
  `Cslib.Circuits.Rational.intBits_modPowTwo_le`: sign-magnitude bit-length bounds.
* `Turing.MultiTapeTM.ComputableInPolyTime.intBin_tdiv`, `.intBin_tmod`, `.intBin_ediv`,
  `.intBin_emod`, `.intBin_div`, `.intBin_mod`, `.intBin_modPowTwo`: plain polynomial-time
  certificates and `@[fun_prop]` composition rules (`.intBin_tdiv'`, `.intBin_tmod'`,
  `.intBin_ediv'`, `.intBin_emod'`, `.intBin_div'`, `.intBin_mod'`, `.intBin_modPowTwo'`).

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Int

/-! ### Exact division and power-of-two modular reduction -/

/-- Least nonnegative residue of `x` modulo `2 ^ ℓ`, i.e., `x - 2 ^ ℓ * ⌊x / 2 ^ ℓ⌋`. -/
def modPowTwo (x : ℤ) (ℓ : ℕ) : ℤ :=
  x % (2 : ℤ) ^ ℓ

theorem modPowTwo_eq_emod (x : ℤ) (ℓ : ℕ) : x.modPowTwo ℓ = x.emod ((2 : ℤ) ^ ℓ) :=
  rfl

theorem modPowTwo_eq_sub_mul_ediv (x : ℤ) (ℓ : ℕ) :
    x.modPowTwo ℓ = x - (2 : ℤ) ^ ℓ * x.ediv ((2 : ℤ) ^ ℓ) :=
  Int.emod_def x ((2 : ℤ) ^ ℓ)

theorem modPowTwo_nonneg (x : ℤ) (ℓ : ℕ) : 0 ≤ x.modPowTwo ℓ :=
  Int.emod_nonneg x (by positivity)

theorem modPowTwo_lt (x : ℤ) (ℓ : ℕ) : x.modPowTwo ℓ < (2 : ℤ) ^ ℓ :=
  Int.emod_lt_of_pos x (by positivity)

theorem natAbs_modPowTwo_lt (x : ℤ) (ℓ : ℕ) : (x.modPowTwo ℓ).natAbs < 2 ^ ℓ := by
  have h₀ := modPowTwo_nonneg x ℓ
  have h₁ := modPowTwo_lt x ℓ
  have hcast : ((x.modPowTwo ℓ).natAbs : ℤ) < ((2 ^ ℓ : ℕ) : ℤ) := by
    rw [Int.natCast_natAbs, abs_of_nonneg h₀, Nat.cast_pow, Nat.cast_ofNat]
    exact h₁
  exact Int.ofNat_lt.mp hcast

/-- If `z ∈ [0, 2 ^ ℓ)` and `2 ^ ℓ` divides `x - z`, then `x.modPowTwo ℓ = z`. -/
theorem modPowTwo_eq_of_dvd_sub {x z : ℤ} {ℓ : ℕ} (hz₀ : 0 ≤ z) (hz₁ : z < (2 : ℤ) ^ ℓ)
    (hdvd : (2 : ℤ) ^ ℓ ∣ x - z) : x.modPowTwo ℓ = z := by
  obtain ⟨k, hk⟩ := hdvd
  have hx : x = z + (2 : ℤ) ^ ℓ * k := by lia
  rw [modPowTwo, hx, Int.add_mul_emod_self_left, Int.emod_eq_of_lt hz₀ hz₁]

/-- Exact Euclidean division of a left multiple `(d * q).ediv d = q` for `d ≠ 0`, stated directly
on `Int.ediv` for rewriting without folding to `/`. -/
theorem ediv_mul_left_exact {d : ℤ} (q : ℤ) (hd : d ≠ 0) : (d * q).ediv d = q :=
  Int.mul_ediv_cancel_left q hd

/-- Exact Euclidean division of a right multiple `(q * d).ediv d = q` for `d ≠ 0`, stated directly
on `Int.ediv` for rewriting without folding to `/`. -/
theorem ediv_mul_right_exact (q : ℤ) {d : ℤ} (hd : d ≠ 0) : (q * d).ediv d = q :=
  Int.mul_ediv_cancel q hd

/-! ### Sign-magnitude reductions and magnitude bounds -/

private theorem tdiv_eq_signMagnitude (a b : ℤ) :
    a.tdiv b =
      if (decide (a < 0) ^^ decide (b < 0)) then -((a.natAbs / b.natAbs : ℕ) : ℤ)
      else ((a.natAbs / b.natAbs : ℕ) : ℤ) := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n => dsimp only [Int.tdiv, Int.natAbs]; split_ifs <;> lia
    | negSucc n => simp [Int.tdiv]
  | negSucc m =>
    cases b with
    | ofNat n =>
      cases n
      · simp [Int.tdiv]
      · dsimp only [Int.tdiv, Int.natAbs]; split_ifs <;> lia
    | negSucc n => simp [Int.tdiv]

private theorem tmod_eq_signMagnitude (a b : ℤ) :
    a.tmod b =
      if decide (a < 0) then -((a.natAbs % b.natAbs : ℕ) : ℤ)
      else ((a.natAbs % b.natAbs : ℕ) : ℤ) := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n => simp [Int.tmod]
    | negSucc n => simp [Int.tmod]
  | negSucc m =>
    cases b with
    | ofNat n =>
      cases n <;> simp [Int.tmod]
    | negSucc n => simp [Int.tmod]

private theorem ediv_eq_signMagnitude (a b : ℤ) :
    a.ediv b =
      if b = 0 then 0
      else if a < 0 then
        if b < 0 then (((a.natAbs - 1) / b.natAbs + 1 : ℕ) : ℤ)
        else -(((a.natAbs - 1) / b.natAbs + 1 : ℕ) : ℤ)
      else
        if b < 0 then -((a.natAbs / b.natAbs : ℕ) : ℤ)
        else ((a.natAbs / b.natAbs : ℕ) : ℤ) := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n =>
      cases n
      · simp [Int.ediv]
      · dsimp only [Int.ediv, Int.natAbs]; split_ifs <;> lia
    | negSucc n => simp [Int.ediv]
  | negSucc m =>
    cases b with
    | ofNat n =>
      cases n
      · simp [Int.ediv]
      · dsimp only [Int.ediv, Int.natAbs]; rw [Int.negSucc_eq]; split_ifs <;> lia
    | negSucc n => simp [Int.ediv]

private theorem emod_natAbs_eq (a b : ℤ) : a % (b.natAbs : ℤ) = a % b := by
  rcases le_or_gt 0 b with hb0 | hb0
  · rw [Int.natAbs_of_nonneg hb0]
  · have hbn : (b.natAbs : ℤ) = -b := by lia
    rw [hbn, Int.emod_neg]

private theorem emod_eq_emodNat (a b : ℤ) :
    a.emod b = if b = 0 then a else ((a % (b.natAbs : ℤ)).toNat : ℤ) := by
  change a % b = _
  by_cases hb : b = 0
  · simp [hb]
  · simp only [hb, ↓reduceIte, emod_natAbs_eq]
    exact (Int.toNat_of_nonneg (Int.emod_nonneg a hb)).symm

theorem natAbs_tdiv_le (a b : ℤ) : (a.tdiv b).natAbs ≤ a.natAbs := by
  rw [tdiv_eq_signMagnitude]
  split_ifs <;> simp only [Int.natAbs_neg, Int.natAbs_natCast] <;> exact Nat.div_le_self _ _

theorem natAbs_ediv_le (a b : ℤ) : (a.ediv b).natAbs ≤ a.natAbs := by
  rw [ediv_eq_signMagnitude]
  by_cases hb : b = 0
  · simp [hb]
  · simp only [hb, ↓reduceIte]
    by_cases ha : a < 0
    · simp only [ha, ↓reduceIte]
      have ha_pos : 1 ≤ a.natAbs := Int.natAbs_pos.mpr (ne_of_lt ha)
      have hle : (a.natAbs - 1) / b.natAbs + 1 ≤ a.natAbs := by
        have := Nat.div_le_self (a.natAbs - 1) b.natAbs
        omega
      split_ifs <;> simp only [Int.natAbs_neg, Int.natAbs_natCast] <;> exact hle
    · simp only [ha, ↓reduceIte]
      split_ifs <;> simp only [Int.natAbs_neg, Int.natAbs_natCast] <;> exact Nat.div_le_self _ _

theorem natAbs_emod_lt_of_ne_zero (a : ℤ) {b : ℤ} (hb : b ≠ 0) :
    (a.emod b).natAbs < b.natAbs := by
  have h₀ : 0 ≤ a % b := Int.emod_nonneg a hb
  have h₁ : a % b < (b.natAbs : ℤ) := by
    rw [← emod_natAbs_eq]
    exact Int.emod_lt_of_pos a (by exact_mod_cast Int.natAbs_pos.mpr hb)
  have hcast : ((a.emod b).natAbs : ℤ) < (b.natAbs : ℤ) := by
    change ((a % b).natAbs : ℤ) < (b.natAbs : ℤ)
    rw [Int.natCast_natAbs, abs_of_nonneg h₀]
    exact h₁
  exact Int.ofNat_lt.mp hcast

theorem size_natAbs_tdiv_le (a b : ℤ) : (a.tdiv b).natAbs.size ≤ a.natAbs.size :=
  Nat.size_le_size (natAbs_tdiv_le a b)

theorem size_natAbs_ediv_le (a b : ℤ) : (a.ediv b).natAbs.size ≤ a.natAbs.size :=
  Nat.size_le_size (natAbs_ediv_le a b)

theorem size_natAbs_emod_le_of_ne_zero (a : ℤ) {b : ℤ} (hb : b ≠ 0) :
    (a.emod b).natAbs.size ≤ b.natAbs.size :=
  Nat.size_le_size (natAbs_emod_lt_of_ne_zero a hb).le

theorem size_natAbs_modPowTwo_le (x : ℤ) (ℓ : ℕ) : (x.modPowTwo ℓ).natAbs.size ≤ ℓ :=
  Nat.size_le.mpr (natAbs_modPowTwo_lt x ℓ)

end Int

namespace Cslib.Circuits.Rational

/-! ### Bit-length bounds -/

/-- Truncated integer division never increases the sign-magnitude bit length of the dividend. -/
theorem intBits_tdiv_le (a b : ℤ) : intBits (a.tdiv b) ≤ intBits a :=
  Nat.add_le_add_right (Int.size_natAbs_tdiv_le a b) 1

/-- Euclidean integer division never increases the sign-magnitude bit length of the dividend. -/
theorem intBits_ediv_le (a b : ℤ) : intBits (a.ediv b) ≤ intBits a :=
  Nat.add_le_add_right (Int.size_natAbs_ediv_le a b) 1

/-- For a nonzero divisor `b`, the Euclidean remainder `a.emod b` has sign-magnitude bit length at
most `intBits b`. -/
theorem intBits_emod_le_of_ne_zero (a : ℤ) {b : ℤ} (hb : b ≠ 0) :
    intBits (a.emod b) ≤ intBits b :=
  Nat.add_le_add_right (Int.size_natAbs_emod_le_of_ne_zero a hb) 1

/-- For a nonzero divisor `b`, `intBits (a.emod b) ≤ intBits b + 1`. -/
theorem intBits_emod_le_add_one_of_ne_zero (a : ℤ) {b : ℤ} (hb : b ≠ 0) :
    intBits (a.emod b) ≤ intBits b + 1 :=
  (intBits_emod_le_of_ne_zero a hb).trans (Nat.le_succ _)

/-- Unconditionally on `b` (including `b = 0`),
`intBits (a.emod b) ≤ max (intBits a) (intBits b)`. -/
theorem intBits_emod_le_max (a b : ℤ) : intBits (a.emod b) ≤ max (intBits a) (intBits b) := by
  by_cases hb : b = 0
  · subst hb
    change intBits (a % 0) ≤ _
    rw [Int.emod_zero]
    exact le_max_left _ _
  · exact (intBits_emod_le_of_ne_zero a hb).trans (le_max_right _ _)

/-- Reducing modulo `2 ^ ℓ` produces an integer of sign-magnitude bit length at most `ℓ + 1`. -/
theorem intBits_modPowTwo_le (x : ℤ) (ℓ : ℕ) : intBits (x.modPowTwo ℓ) ≤ ℓ + 1 :=
  (intBits_le_iff _ _).mpr (Int.natAbs_modPowTwo_lt x ℓ)

end Cslib.Circuits.Rational

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-! ### Plain polynomial-time certificates -/

private theorem intBin_tdiv_tidy :
    ComputableTidilyInPolyTime (fun p : ℤ × ℤ => p.1.tdiv p.2)
      (encPair encIntBin encIntBin) encIntBin := by
  have hsa := ComputableTidilyInPolyTime.intBin_isNeg.comp
    (ComputableTidilyInPolyTime.fst encIntBin encIntBin)
  have hsb := ComputableTidilyInPolyTime.intBin_isNeg.comp
    (ComputableTidilyInPolyTime.snd encIntBin encIntBin)
  have hma := ComputableTidilyInPolyTime.intBin_natAbs.comp
    (ComputableTidilyInPolyTime.fst encIntBin encIntBin)
  have hmb := ComputableTidilyInPolyTime.intBin_natAbs.comp
    (ComputableTidilyInPolyTime.snd encIntBin encIntBin)
  have h := ComputableTidilyInPolyTime.intBin_signMagnitude.comp
    ((ComputableTidilyInPolyTime.bool_xor.comp (hsa.prod hsb)).prod
      (ComputableTidilyInPolyTime.binary_div.comp (hma.prod hmb)))
  refine h.of_enc_eq fun ⟨a, b⟩ => congrArg encIntBin ?_
  simpa only [Function.comp_apply] using Int.tdiv_eq_signMagnitude a b

private theorem intBin_tmod_tidy :
    ComputableTidilyInPolyTime (fun p : ℤ × ℤ => p.1.tmod p.2)
      (encPair encIntBin encIntBin) encIntBin := by
  have hsa := ComputableTidilyInPolyTime.intBin_isNeg.comp
    (ComputableTidilyInPolyTime.fst encIntBin encIntBin)
  have hma := ComputableTidilyInPolyTime.intBin_natAbs.comp
    (ComputableTidilyInPolyTime.fst encIntBin encIntBin)
  have hmb := ComputableTidilyInPolyTime.intBin_natAbs.comp
    (ComputableTidilyInPolyTime.snd encIntBin encIntBin)
  have h := ComputableTidilyInPolyTime.intBin_signMagnitude.comp
    (hsa.prod (ComputableTidilyInPolyTime.binary_mod.comp (hma.prod hmb)))
  refine h.of_enc_eq fun ⟨a, b⟩ => congrArg encIntBin ?_
  simpa only [Function.comp_apply] using Int.tmod_eq_signMagnitude a b

private theorem intBin_ediv_tidy :
    ComputableTidilyInPolyTime (fun p : ℤ × ℤ => p.1.ediv p.2)
      (encPair encIntBin encIntBin) encIntBin := by
  have hb0 : ComputableTidilyInPolyTime (fun p : ℤ × ℤ => decide (p.2 = 0))
      (encPair encIntBin encIntBin) encBool :=
    ComputableTidilyInPolyTime.intBin_isZero.comp (ComputableTidilyInPolyTime.snd _ _)
  have ha_neg : ComputableTidilyInPolyTime (fun p : ℤ × ℤ => decide (p.1 < 0))
      (encPair encIntBin encIntBin) encBool :=
    ComputableTidilyInPolyTime.intBin_isNeg.comp (ComputableTidilyInPolyTime.fst _ _)
  have hb_neg : ComputableTidilyInPolyTime (fun p : ℤ × ℤ => decide (p.2 < 0))
      (encPair encIntBin encIntBin) encBool :=
    ComputableTidilyInPolyTime.intBin_isNeg.comp (ComputableTidilyInPolyTime.snd _ _)
  have hq_neg : ComputableTidilyInPolyTime
      (fun p : ℤ × ℤ => (((p.1.natAbs - 1) / p.2.natAbs + 1 : ℕ) : ℤ))
      (encPair encIntBin encIntBin) encIntBin := by fun_prop
  have hq_nonneg : ComputableTidilyInPolyTime
      (fun p : ℤ × ℤ => ((p.1.natAbs / p.2.natAbs : ℕ) : ℤ))
      (encPair encIntBin encIntBin) encIntBin := by fun_prop
  have h := hb0.ite_decide (.const 0)
    (ha_neg.ite_decide
      (hb_neg.ite_decide hq_neg (ComputableTidilyInPolyTime.intBin_neg.comp hq_neg))
      (hb_neg.ite_decide (ComputableTidilyInPolyTime.intBin_neg.comp hq_nonneg) hq_nonneg))
  refine h.of_enc_eq fun ⟨a, b⟩ => congrArg encIntBin ?_
  simpa only [Function.comp_apply] using Int.ediv_eq_signMagnitude a b

private theorem intBin_emod_tidy :
    ComputableTidilyInPolyTime (fun p : ℤ × ℤ => p.1.emod p.2)
      (encPair encIntBin encIntBin) encIntBin := by
  have hb0 : ComputableTidilyInPolyTime (fun p : ℤ × ℤ => decide (p.2 = 0))
      (encPair encIntBin encIntBin) encBool :=
    ComputableTidilyInPolyTime.intBin_isZero.comp (ComputableTidilyInPolyTime.snd _ _)
  have hrem : ComputableTidilyInPolyTime
      (fun p : ℤ × ℤ => ((p.1 % (p.2.natAbs : ℤ)).toNat : ℤ))
      (encPair encIntBin encIntBin) encIntBin := by fun_prop
  have h := hb0.ite_decide (ComputableTidilyInPolyTime.fst encIntBin encIntBin) hrem
  refine h.of_enc_eq fun ⟨a, b⟩ => congrArg encIntBin ?_
  simpa only [Function.comp_apply] using Int.emod_eq_emodNat a b

/-- Truncated-toward-zero division of signed binary integers is computable in polynomial time. -/
@[fun_prop]
theorem intBin_tdiv :
    ComputableInPolyTime (fun p : ℤ × ℤ => p.1.tdiv p.2)
      (encPair encIntBin encIntBin) encIntBin :=
  .of_tidy intBin_tdiv_tidy

/-- Truncated-toward-zero division of computed binary integers. -/
@[fun_prop]
theorem intBin_tdiv' {α : Type} {input : α ↪ List Bool} {left right : α → ℤ}
    (hleft : ComputableInPolyTime left input encIntBin)
    (hright : ComputableInPolyTime right input encIntBin) :
    ComputableInPolyTime (fun a => (left a).tdiv (right a)) input encIntBin :=
  intBin_tdiv.comp (hleft.prod hright)

/-- Truncated-toward-zero remainder of signed binary integers is computable in polynomial time. -/
@[fun_prop]
theorem intBin_tmod :
    ComputableInPolyTime (fun p : ℤ × ℤ => p.1.tmod p.2)
      (encPair encIntBin encIntBin) encIntBin :=
  .of_tidy intBin_tmod_tidy

/-- Truncated-toward-zero remainder of computed binary integers. -/
@[fun_prop]
theorem intBin_tmod' {α : Type} {input : α ↪ List Bool} {left right : α → ℤ}
    (hleft : ComputableInPolyTime left input encIntBin)
    (hright : ComputableInPolyTime right input encIntBin) :
    ComputableInPolyTime (fun a => (left a).tmod (right a)) input encIntBin :=
  intBin_tmod.comp (hleft.prod hright)

/-- Euclidean division (`Int.ediv`) of signed binary integers is computable in polynomial time. -/
@[fun_prop]
theorem intBin_ediv :
    ComputableInPolyTime (fun p : ℤ × ℤ => p.1.ediv p.2)
      (encPair encIntBin encIntBin) encIntBin :=
  .of_tidy intBin_ediv_tidy

/-- Euclidean division (`Int.ediv`) of computed binary integers. -/
@[fun_prop]
theorem intBin_ediv' {α : Type} {input : α ↪ List Bool} {left right : α → ℤ}
    (hleft : ComputableInPolyTime left input encIntBin)
    (hright : ComputableInPolyTime right input encIntBin) :
    ComputableInPolyTime (fun a => (left a).ediv (right a)) input encIntBin :=
  intBin_ediv.comp (hleft.prod hright)

/-- Euclidean division (`/`) of signed binary integers is computable in polynomial time. -/
@[fun_prop]
theorem intBin_div :
    ComputableInPolyTime (fun p : ℤ × ℤ => p.1 / p.2)
      (encPair encIntBin encIntBin) encIntBin :=
  intBin_ediv

/-- Euclidean division (`/`) of computed binary integers. -/
@[fun_prop]
theorem intBin_div' {α : Type} {input : α ↪ List Bool} {left right : α → ℤ}
    (hleft : ComputableInPolyTime left input encIntBin)
    (hright : ComputableInPolyTime right input encIntBin) :
    ComputableInPolyTime (fun a => left a / right a) input encIntBin :=
  intBin_div.comp (hleft.prod hright)

/-- Euclidean remainder (`Int.emod`) of signed binary integers is computable in polynomial time. -/
@[fun_prop]
theorem intBin_emod :
    ComputableInPolyTime (fun p : ℤ × ℤ => p.1.emod p.2)
      (encPair encIntBin encIntBin) encIntBin :=
  .of_tidy intBin_emod_tidy

/-- Euclidean remainder (`Int.emod`) of computed binary integers. -/
@[fun_prop]
theorem intBin_emod' {α : Type} {input : α ↪ List Bool} {left right : α → ℤ}
    (hleft : ComputableInPolyTime left input encIntBin)
    (hright : ComputableInPolyTime right input encIntBin) :
    ComputableInPolyTime (fun a => (left a).emod (right a)) input encIntBin :=
  intBin_emod.comp (hleft.prod hright)

/-- Euclidean remainder (`%`) of signed binary integers is computable in polynomial time. -/
@[fun_prop]
theorem intBin_mod :
    ComputableInPolyTime (fun p : ℤ × ℤ => p.1 % p.2)
      (encPair encIntBin encIntBin) encIntBin :=
  intBin_emod

/-- Euclidean remainder (`%`) of computed binary integers. -/
@[fun_prop]
theorem intBin_mod' {α : Type} {input : α ↪ List Bool} {left right : α → ℤ}
    (hleft : ComputableInPolyTime left input encIntBin)
    (hright : ComputableInPolyTime right input encIntBin) :
    ComputableInPolyTime (fun a => left a % right a) input encIntBin :=
  intBin_mod.comp (hleft.prod hright)

/-- Reduction `Int.modPowTwo p.1 p.2 = p.1 % 2 ^ p.2` of a binary integer modulo `2 ^ ℓ` (with
`ℓ` in unary) is computable in polynomial time. -/
@[fun_prop]
theorem intBin_modPowTwo :
    ComputableInPolyTime (fun p : ℤ × ℕ => p.1.modPowTwo p.2)
      (encPair encIntBin encUnary) encIntBin := by
  refine .of_tidy ?_
  have hpow : ComputableTidilyInPolyTime (fun p : ℤ × ℕ => ((2 : ℤ) ^ p.2))
      (encPair encIntBin encUnary) encIntBin := by fun_prop
  exact intBin_emod_tidy.comp ((ComputableTidilyInPolyTime.fst encIntBin encUnary).prod hpow)

/-- Reduction `Int.modPowTwo (value a) (exponent a)` of a computed binary integer modulo a
computed unary power of two. -/
@[fun_prop]
theorem intBin_modPowTwo' {α : Type} {input : α ↪ List Bool} {value : α → ℤ} {exponent : α → ℕ}
    (hvalue : ComputableInPolyTime value input encIntBin)
    (hexponent : ComputableInPolyTime exponent input encUnary) :
    ComputableInPolyTime (fun a => (value a).modPowTwo (exponent a)) input encIntBin :=
  intBin_modPowTwo.comp (hvalue.prod hexponent)

end Turing.MultiTapeTM.ComputableInPolyTime
