/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Time
import Complexity.Computability.Complexity.Classes.Time.Verifier
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolynomialPadding
import Complexity.Computability.Machines.Turing.MultiTape.Internal.OCombinators
import Mathlib.Tactic.Linarith

/-!
# Polynomial padding for nondeterministic time

A collapse `NTIME ((n + 1) ^ b) ⊆ NTIME ((n + 1) ^ a)`, with `1 ≤ a` and `2 ≤ b`, propagates
after multiplying the exponents by a positive integer `k`, up to one more degree on the right:
`NTIME ((n + 1) ^ (b * k)) ⊆ NTIME ((n + 1) ^ (a * (k + 1) + 1))`
(`Cslib.Complexity.NTIME_pow_mul_subset_of_subset`).

The padded language of `A` consists of the words `x` carrying a word `y = unframe x` framed at
their start, with `(y.length + 1) ^ (k + 1) ≤ x.length` and `y ∈ A`. Both directions guess a
certificate and run a verifier (`Cslib.Complexity.setOf_exists_mem_NTIME`), with the linear-time
verifier of the other language (`Cslib.Complexity.exists_verifier_of_mem_NTIME`).

* **Padding** (`Cslib.Complexity.setOf_padded_mem_NTIME`). If `A` is in
  `NTIME ((n + 1) ^ (b * k))`, the padded language is in `NTIME ((n + 1) ^ b)`. Test the padding
  in quadratic time, then guess a certificate for `y` of a length rounded to a power of two. The
  padding exponent is `k + 1` rather than `k`: writing the rounded length in unary costs one
  more factor `y.length + 1`, and the padding pays for it.
* **Unpadding** (`Cslib.Complexity.mem_NTIME_of_setOf_padded_mem`). If the padded language is in
  `NTIME ((n + 1) ^ a)`, then `A` is in `NTIME ((n + 1) ^ (a * (k + 1) + 1))`. Write the padding
  of `y`, rounded to a power of two, then guess a certificate for the padded word. Writing the
  certificate length in unary costs the extra degree.

The plain calculus has no linear-time unary writer for polynomial lengths, so neither direction
preserves the degree exactly, unlike the deterministic transfer
`Cslib.Complexity.DTIME_pow_mul_subset_of_subset`. The lost degree is harmless for hierarchy
amplification. This is the padding technique of [Arora and Barak, §2.6.2, Theorem 2.25 and
Remark 2.26][AroraBarak07], by which equalities between classes scale up, specialized to integer
powers with all native computation costs proved. No class-closure or simulation hypothesis is
hidden in the statements.

## Main results

* `Cslib.Complexity.setOf_padded_mem_NTIME`: padding into nondeterministic time.
* `Cslib.Complexity.mem_NTIME_of_setOf_padded_mem`: unpadding out of nondeterministic time.
* `Cslib.Complexity.NTIME_pow_mul_subset_of_subset`: a nondeterministic polynomial-time collapse
  propagates after multiplying both exponents by the same positive integer, up to one degree.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, web draft of January
  2007][AroraBarak07]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- Unframing is linear. -/
private theorem computableInO_unframe :
    ComputableInO unframe encBits encBits (fun x => x.length) (fun x => x.length) :=
  .of_linear (.of_unframe fun _ => rfl)

/-- **Padding into nondeterministic time.** If `A` is in nondeterministic time
`O((n + 1) ^ (b * k))`, with `2 ≤ b` and `1 ≤ k`, then the words carrying a word `y` of `A` framed
at their start, padded to a length of at least `(y.length + 1) ^ (k + 1)`, form a problem in
nondeterministic time `O((n + 1) ^ b)`. -/
theorem setOf_padded_mem_NTIME {A : Set (List Bool)} {b k : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k)
    (hA : A ∈ NTIME encBits (fun n => (n + 1) ^ (b * k))) :
    {x : List Bool | ((unframe x).length + 1) ^ (k + 1) ≤ x.length ∧ unframe x ∈ A} ∈
      NTIME encBits (fun n => (n + 1) ^ b) := by
  classical
  obtain ⟨V, c, hV, hc⟩ := exists_verifier_of_mem_NTIME hA
  -- the certificate length for `y = unframe x`, rounded to a power of two, when padded enough
  let guard (x : List Bool) : Bool := decide (((unframe x).length + 1) ^ (k + 1) ≤ x.length)
  let L (x : List Bool) : ℕ := 2 ^ (b * k * Nat.size ((unframe x).length + 1) + (c + 1))
  let ℓ (x : List Bool) : ℕ := if guard x then L x else 0
  let V' (p : List Bool × List Bool) : Bool := if guard p.1 then V (unframe p.1, p.2) else false
  have hL (x : List Bool) :
      c * ((unframe x).length + 1) ^ (b * k) + c ≤ L x := by
    have hp := (polynomialPaddingPower_bounds (b * k) (unframe x).length).1
    have hc' : 2 * c ≤ 2 ^ (c + 1) := by
      have : c < 2 ^ c := Nat.lt_two_pow_self
      rw [pow_succ]
      omega
    have h1 : 1 ≤ ((unframe x).length + 1) ^ (b * k) := Nat.one_le_pow _ _ (by omega)
    calc
      _ ≤ 2 * c * ((unframe x).length + 1) ^ (b * k) := by nlinarith
      _ ≤ 2 ^ (c + 1) * 2 ^ (b * k * Nat.size ((unframe x).length + 1)) := Nat.mul_le_mul hc' hp
      _ = L x := by rw [Nat.mul_comm, ← pow_add]
  have hset :
      {x : List Bool | ((unframe x).length + 1) ^ (k + 1) ≤ x.length ∧ unframe x ∈ A} =
        {x | ∃ w : List Bool, w.length = ℓ x ∧ V' (x, w) = true} := by
    ext x
    simp only [Set.mem_ofPred_eq, ℓ, V', guard]
    by_cases hg : ((unframe x).length + 1) ^ (k + 1) ≤ x.length
    · simp only [hg, decide_true, ↓reduceIte, true_and]
      exact hc (unframe x) (L x) (by simpa only [encBits_apply] using hL x)
    · simp [hg]
  rw [hset]
  -- the certificate length and the verifier, as plain computations
  have hlen := ComputableInO.lengthNat.comp computableInO_unframe
  have hℓ := (computableInO_polynomialPaddingGuard (k + 1)).ite
    ((computableInO_unary_roundedPower (k := b * k) (Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (by omega))) (c + 1)).comp hlen)
    (ComputableInO.const (encIn := encBits) (encMid := encUnary) 0)
  have hpair := (computableInO_unframe.comp (ComputableInO.fst encBits encBits)).prod
    (ComputableInO.snd encBits encBits)
  have hV' := ((computableInO_polynomialPaddingGuard (k + 1)).comp
    (ComputableInO.fst encBits encBits)).ite (hV.comp hpair)
      (ComputableInO.const (encIn := encPair encBits encBits) (encMid := encBool) false)
  refine setOf_exists_mem_NTIME (ℓ := ℓ) (V := V') hℓ hV'
    (C := 40 + 8 * 2 ^ (b * k + (c + 1))) fun x w hw => ?_
  -- the bound
  set n := x.length with hn
  set m := (unframe x).length with hm
  have hmn : m ≤ n := length_unframe_le x
  have hsq : (n + 1) ^ 2 ≤ (n + 1) ^ b := Nat.pow_le_pow_right (by omega) hb
  have hsq' : (m + 1) ^ 2 ≤ (n + 1) ^ b :=
    (Nat.pow_le_pow_left (by omega) 2).trans hsq
  have hlin : n + 1 ≤ (n + 1) ^ b :=
    (Nat.le_self_pow (by omega) _).trans hsq
  simp only [Function.comp_apply, encBits_apply, length_encPair, ← hn, ← hm] at hw ⊢
  by_cases hg : (m + 1) ^ (k + 1) ≤ n
  · have hgx : guard x = true := decide_eq_true hg
    simp only [ℓ, hgx, ↓reduceIte] at hw
    simp only [hg, decide_true, ↓reduceIte]
    -- the padding pays for the certificate and for writing its length
    have hpad : (m + 1) ^ (b * k + 1) ≤ (n + 1) ^ b := by
      calc
        _ ≤ (m + 1) ^ (b * (k + 1)) := Nat.pow_le_pow_right (by omega) (by nlinarith)
        _ = ((m + 1) ^ (k + 1)) ^ b := by rw [← pow_mul, Nat.mul_comm]
        _ ≤ (n + 1) ^ b := Nat.pow_le_pow_left (by omega) b
    have hpow : (m + 1) ^ (b * k) ≤ (m + 1) ^ (b * k + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hW : w.length ≤ 2 ^ (b * k + (c + 1)) * (n + 1) ^ b := by
      have hb' := (polynomialPaddingPower_bounds (b * k) m).2
      rw [hw]
      simp only [L, ← hm]
      calc
        _ = 2 ^ (b * k * Nat.size (m + 1)) * 2 ^ (c + 1) := pow_add _ _ _
        _ ≤ 2 ^ (b * k) * (m + 1) ^ (b * k) * 2 ^ (c + 1) := Nat.mul_le_mul_right _ hb'
        _ = 2 ^ (b * k + (c + 1)) * (m + 1) ^ (b * k) := by rw [pow_add]; ring
        _ ≤ _ := Nat.mul_le_mul_left _ (hpow.trans hpad)
    calc
      _ ≤ 40 * (n + 1) ^ b + 8 * (2 ^ (b * k + (c + 1)) * (n + 1) ^ b) := by
        have := hpow.trans hpad
        omega
      _ = (40 + 8 * 2 ^ (b * k + (c + 1))) * (n + 1) ^ b := by ring
      _ ≤ _ := Nat.le_add_right _ _
  · have hgx : guard x = false := decide_eq_false hg
    simp only [ℓ, hgx, Bool.false_eq_true, ↓reduceIte] at hw
    simp only [hg, decide_false, Bool.false_eq_true, ↓reduceIte, hw]
    calc
      _ ≤ 40 * (n + 1) ^ b := by omega
      _ ≤ (40 + 8 * 2 ^ (b * k + (c + 1))) * (n + 1) ^ b := Nat.mul_le_mul_right _ (by omega)
      _ ≤ _ := Nat.le_add_right _ _

/-- **Unpadding out of nondeterministic time.** If the words carrying a word `y` of `A` framed at
their start, padded to a length of at least `(y.length + 1) ^ (k + 1)`, form a problem in
nondeterministic time `O((n + 1) ^ a)`, with `1 ≤ a`, then `A` is in nondeterministic time
`O((n + 1) ^ (a * (k + 1) + 1))`. -/
theorem mem_NTIME_of_setOf_padded_mem {A : Set (List Bool)} {a k : ℕ} (ha : 1 ≤ a)
    (hB : {x : List Bool | ((unframe x).length + 1) ^ (k + 1) ≤ x.length ∧ unframe x ∈ A} ∈
      NTIME encBits (fun n => (n + 1) ^ a)) :
    A ∈ NTIME encBits (fun n => (n + 1) ^ (a * (k + 1) + 1)) := by
  classical
  obtain ⟨V, c, hV, hc⟩ := exists_verifier_of_mem_NTIME hB
  -- pad `y` to a rounded length, and guess a certificate of a rounded length
  let R (y : List Bool) : ℕ := 2 ^ ((k + 1) * Nat.size (y.length + 1))
  let pad (y : List Bool) : List Bool := frame y ++ List.replicate (R y) true
  let s := 2 * c * 3 ^ a
  let ℓ (y : List Bool) : ℕ := 2 ^ (a * (k + 1) * Nat.size (y.length + 1) + s)
  let V' (p : List Bool × List Bool) : Bool := V (pad p.1, p.2)
  have hR (y : List Bool) : (y.length + 1) ^ (k + 1) ≤ R y :=
    (polynomialPaddingPower_bounds (k + 1) y.length).1
  have hpadlen (y : List Bool) : (pad y).length = 2 * y.length + 1 + R y := by
    simp only [pad, List.length_append, length_frame, List.length_replicate]
  have hℓ' (y : List Bool) : c * ((pad y).length + 1) ^ a + c ≤ ℓ y := by
    have h1 : y.length + 1 ≤ (y.length + 1) ^ (k + 1) := Nat.le_self_pow (by omega) _
    have hRy := hR y
    have h3 : (pad y).length + 1 ≤ 3 * R y := by rw [hpadlen]; omega
    have hpow : ((pad y).length + 1) ^ a ≤ 3 ^ a * R y ^ a := by
      rw [← mul_pow]
      exact Nat.pow_le_pow_left h3 a
    have hRa : R y ^ a = 2 ^ (a * (k + 1) * Nat.size (y.length + 1)) := by
      rw [← pow_mul]
      ring
    have h2 : 1 ≤ R y ^ a := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (by simp [R]))
    have hs : s ≤ 2 ^ s := Nat.lt_two_pow_self.le
    calc
      _ ≤ c * (3 ^ a * R y ^ a) + c * (3 ^ a * R y ^ a) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hpow)
          (Nat.le_mul_of_pos_right _ (Nat.mul_pos (Nat.pow_pos (by omega)) h2))
      _ = s * R y ^ a := by simp only [s]; ring
      _ ≤ 2 ^ s * R y ^ a := Nat.mul_le_mul_right _ hs
      _ = ℓ y := by rw [hRa, Nat.mul_comm, ← pow_add]
  have hset : A = {y | ∃ w : List Bool, w.length = ℓ y ∧ V' (y, w) = true} := by
    ext y
    have hmem : y ∈ A ↔ pad y ∈
        {x : List Bool | ((unframe x).length + 1) ^ (k + 1) ≤ x.length ∧ unframe x ∈ A} := by
      simp only [Set.mem_ofPred_eq, pad, unframe_frame_append]
      have := hR y
      have := hpadlen y
      simp only [pad] at this
      exact ⟨fun h => ⟨by omega, h⟩, fun h => h.2⟩
    rw [hmem, hc (pad y) (ℓ y) (by simpa only [encBits_apply] using hℓ' y)]
    rfl
  rw [hset]
  -- the certificate length and the verifier, as plain computations
  have hℓ := (computableInO_unary_roundedPower (k := a * (k + 1)) (Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (by omega))) s).comp ComputableInO.lengthNat
  have hpair := ((computableInO_roundedPolynomialPadding (k := k + 1) (by omega)).comp
    (ComputableInO.fst encBits encBits)).prod (ComputableInO.snd encBits encBits)
  have hV' := hV.comp hpair
  refine setOf_exists_mem_NTIME (ℓ := ℓ) (V := V') hℓ hV'
    (C := 20 + 4 * 2 ^ (k + 1) + 4 * 2 ^ (a * (k + 1) + s)) fun y w hw => ?_
  -- the bound
  set m := y.length with hm
  set X := (m + 1) ^ (a * (k + 1) + 1)
  have hka : k + 2 ≤ a * (k + 1) + 1 := by nlinarith
  have hX (e : ℕ) (he : e ≤ a * (k + 1) + 1) : (m + 1) ^ e ≤ X :=
    Nat.pow_le_pow_right (by omega) he
  have hRb : R y ≤ 2 ^ (k + 1) * X := by
    have := (polynomialPaddingPower_bounds (k + 1) m).2
    exact this.trans (Nat.mul_le_mul_left _ (hX _ (by omega)))
  have hW : w.length ≤ 2 ^ (a * (k + 1) + s) * X := by
    have hb' := (polynomialPaddingPower_bounds (a * (k + 1)) m).2
    rw [hw]
    calc
      _ = 2 ^ (a * (k + 1) * Nat.size (m + 1)) * 2 ^ s := pow_add _ _ _
      _ ≤ 2 ^ (a * (k + 1)) * (m + 1) ^ (a * (k + 1)) * 2 ^ s := Nat.mul_le_mul_right _ hb'
      _ = 2 ^ (a * (k + 1) + s) * (m + 1) ^ (a * (k + 1)) := by rw [pow_add]; ring
      _ ≤ _ := Nat.mul_le_mul_left _ (hX _ (by omega))
  have h1 := hX 1 (by omega)
  have h2 := hX 2 (by omega)
  have hk2 := hX (k + 1 + 1) hka
  simp only [pow_one] at h1
  simp only [Function.comp_apply, encBits_apply, length_encPair, ← hm] at hw ⊢
  rw [hpadlen, ← hm]
  calc
    _ ≤ 20 * X + 4 * (2 ^ (k + 1) * X) + 4 * (2 ^ (a * (k + 1) + s) * X) := by omega
    _ = (20 + 4 * 2 ^ (k + 1) + 4 * 2 ^ (a * (k + 1) + s)) * X := by ring
    _ ≤ _ := Nat.le_add_right _ _

/-- **A nondeterministic polynomial-time collapse propagates under padding**, up to one degree. If
`NTIME ((n + 1) ^ b) ⊆ NTIME ((n + 1) ^ a)`, with `1 ≤ a` and `2 ≤ b`, then
`NTIME ((n + 1) ^ (b * k)) ⊆ NTIME ((n + 1) ^ (a * (k + 1) + 1))` for every `k ≥ 1`. -/
theorem NTIME_pow_mul_subset_of_subset {a b k : ℕ} (ha : 1 ≤ a) (hb : 2 ≤ b) (hk : 1 ≤ k)
    (h : NTIME encBits (fun n => (n + 1) ^ b) ⊆ NTIME encBits (fun n => (n + 1) ^ a)) :
    NTIME encBits (fun n => (n + 1) ^ (b * k)) ⊆
      NTIME encBits (fun n => (n + 1) ^ (a * (k + 1) + 1)) :=
  fun _ hA => mem_NTIME_of_setOf_padded_mem ha (h (setOf_padded_mem_NTIME hb hk hA))

end Cslib.Complexity
