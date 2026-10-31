/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.SpaceInTime
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.NatPower
import Complexity.Computability.Machines.Turing.MultiTape.Universal.Compose
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant

/-!
# Constructible resource bounds

A time- or space-constructible bound is computed in binary from a word of length `n` by one
finite-state binary-alphabet machine, within `O(t n)` time or `O(s n)` work space respectively.
The input tape is read-only and the output tape write-only. Neither definition imposes a lower
bound on the resource function; hierarchy theorems state the lower bounds they need separately.

The shared length and arithmetic routines give concrete constructible bounds, without importing
any hierarchy theorem. The length of a word in binary
(`Turing.MultiTapeTM.ComputableInO.lengthNat`) and the bounds on binary digits
(`Turing.MultiTapeTM.exists_pow_length_encNat_le`) are in
`Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible`; unary word
length is supplied by the quantitative API (`Turing.MultiTapeTM.ComputableInO.lengthUnary`).

## Main definitions

* `Cslib.Complexity.TimeConstructible`: time-constructible bounds.
* `Cslib.Complexity.SpaceConstructible`: space-constructible bounds.

## Main results

* `Cslib.Complexity.TimeConstructible.spaceConstructible`: time constructibility implies
  space constructibility.
* `Cslib.Complexity.timeConstructible_two_pow`,
  `Cslib.Complexity.timeConstructible_two_pow_two_pow`,
  `Cslib.Complexity.timeConstructible_succ_pow`,
  `Cslib.Complexity.TimeConstructible.succ_mul`: time-constructible bounds.
* `Cslib.Complexity.spaceConstructible_const`, `Cslib.Complexity.spaceConstructible_id`,
  `Cslib.Complexity.spaceConstructible_succ`, `Cslib.Complexity.spaceConstructible_succ_pow`,
  `Cslib.Complexity.spaceConstructible_two_pow`,
  `Cslib.Complexity.spaceConstructible_two_pow_two_pow`: space-constructible bounds.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Definition 9.1][Sipser2013]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 1.3][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal

/-- A bound `t` is time-constructible when some machine with a binary alphabet and finitely many
states computes `t n` in binary from any word of length `n` within time `O(t n)`. Arora and Barak
also ask for `n ≤ t n` [Arora and Barak, Section 1.3][AroraBarak09]; this definition omits that
condition, and the results that need it, such as `Cslib.Complexity.DTIME_ssubset_DTIME`, assume it
separately. -/
def TimeConstructible (t : ℕ → ℕ) : Prop :=
  ∃ c : ℕ, ∃ s : ℕ → ℕ, ComputableInTimeAndSpaceOfLength (fun x : List Bool => t x.length) encBits
    encNat (fun n => c * t n + c) s

/-- A time-constructible bound is computed within time and space `O(t n)`. -/
theorem TimeConstructible.computableInO {t : ℕ → ℕ} (ht : TimeConstructible t) :
    ComputableInO (fun x : List Bool => t x.length) encBits encNat (fun x => t x.length)
      fun x => t x.length := by
  obtain ⟨c, s, h⟩ := ht
  obtain ⟨k, h⟩ := ComputableInTimeAndSpace.exists_space_linear h
  refine .of_bounds h (k * c + c + k + 1) (fun x => ?_) (fun x => ?_)
    fun x => (length_encNat_le _).trans ?_
  · dsimp only
    simp only [encBits_apply]
    ring_nf
    omega
  · dsimp only
    simp only [encBits_apply]
    ring_nf
    omega
  · exact (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ (by omega))

/-- A computation of `t n` in binary within time `O(t n)` makes `t` time-constructible. -/
theorem TimeConstructible.of_computableInO {t : ℕ → ℕ} {T S : List Bool → ℕ} {s : ℕ → ℕ}
    (c : ℕ) (h : ComputableInO (fun x : List Bool => t x.length) encBits encNat T S)
    (hT : ∀ x, T x ≤ c * t x.length + c) (hS : ∀ x, S x ≤ s x.length) : TimeConstructible t := by
  obtain ⟨k, hk, -⟩ := h
  refine ⟨k * (c + 1), fun n => k * (s n + 1), hk.mono (fun x => ?_) fun x => ?_⟩
  · simp only [encBits_apply]
    have := Nat.mul_le_mul_left k (Nat.add_le_add_right (hT x) 1)
    have e₁ : k * (c * t x.length + c + 1) = k * c * t x.length + k * c + k := by ring
    have e₂ : k * (c + 1) * t x.length + k * (c + 1) =
        k * c * t x.length + k * t x.length + k * c + k := by ring
    omega
  · simp only [encBits_apply]
    exact Nat.mul_le_mul_left k (Nat.add_le_add_right (hS x) 1)

/-- `2 ^ n` is time-constructible: its binary digits are `n` zeros followed by a one. -/
theorem timeConstructible_two_pow : TimeConstructible (2 ^ ·) :=
  TimeConstructible.of_computableInO 1
    (ComputableInDegree.two_pow_length encBits).inO_one
    (s := fun n => n) (fun x => by
      simp only [encBits_apply]
      have := Nat.lt_two_pow_self (n := x.length)
      omega) fun _ => le_rfl

private theorem succ_mul_two_pow_le_two_pow_two_pow : ∀ n : ℕ, (n + 1) * 2 ^ n ≤ 2 ^ (2 ^ n)
  | 0 => by decide
  | 1 => by decide
  | n + 2 => by
    have ih := succ_mul_two_pow_le_two_pow_two_pow (n + 1)
    have h₁ : 4 ≤ 2 ^ (2 ^ (n + 1)) := by
      calc 4 = 2 ^ (2 ^ 1) := by decide
        _ ≤ 2 ^ (2 ^ (n + 1)) :=
          Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_right (by decide) (by omega))
    have h₂ : 2 ^ (2 ^ (n + 2)) = 2 ^ (2 ^ (n + 1)) * 2 ^ (2 ^ (n + 1)) := by
      rw [← Nat.pow_add, ← two_mul, pow_succ']
    rw [h₂]
    calc (n + 2 + 1) * 2 ^ (n + 2)
        ≤ 2 * (n + 1 + 1) * (2 * 2 ^ (n + 1)) :=
          Nat.mul_le_mul (by omega) (by rw [pow_succ'])
      _ = 4 * ((n + 1 + 1) * 2 ^ (n + 1)) := by ring
      _ ≤ 4 * 2 ^ (2 ^ (n + 1)) := Nat.mul_le_mul_left 4 ih
      _ ≤ 2 ^ (2 ^ (n + 1)) * 2 ^ (2 ^ (n + 1)) := Nat.mul_le_mul_right _ h₁

/-- `2 ^ (2 ^ n)` is time-constructible: count `2 ^ n` in unary and then write `2 ^ (2 ^ n)` in
binary as `2 ^ n` zeros followed by a one. -/
theorem timeConstructible_two_pow_two_pow : TimeConstructible fun n => 2 ^ (2 ^ n) := by
  have h₁ := ComputableInO.unary_two_pow.comp ComputableInO.lengthUnary
  have h₂ := ((ComputableInDegree.two_pow_length encUnary).inO_one.comp
    h₁).of_enc_eq (encC := encNat) (g := fun x : List Bool => 2 ^ (2 ^ x.length)) fun x => by
      simp only [Function.comp_apply, encUnary_apply, List.length_replicate]
  refine TimeConstructible.of_computableInO 3 h₂
    (s := fun n => n + 2 ^ n + 2 ^ n) (fun x => ?_) fun x => ?_
  · simp only [Function.comp_apply, encUnary_apply, List.length_replicate]
    have hle := succ_mul_two_pow_le_two_pow_two_pow x.length
    have hpow : 1 ≤ 2 ^ x.length := Nat.one_le_two_pow
    nlinarith
  · simp only [Function.comp_apply, encUnary_apply, List.length_replicate]
    exact le_rfl

private theorem cube_add_le (u v : ℕ) : (u + v) ^ 3 ≤ 8 * (u ^ 3 + v ^ 3) := by
  rcases le_total u v with h | h
  · have h₁ : (u + v) ^ 3 ≤ (2 * v) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have h₂ : (2 * v) ^ 3 = 8 * v ^ 3 := by ring
    omega
  · have h₁ : (u + v) ^ 3 ≤ (2 * u) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have h₂ : (2 * u) ^ 3 = 8 * u ^ 3 := by ring
    omega

/-- If `f n` is computed in binary from words of length `n` within time `O((n + 1) * f n)` and
`n ≤ f n`, then `(n + 1) * f n` is time-constructible: writing the length of the word in binary
takes time `O(n ^ 2)`, and the product time polylogarithmic in the factors. -/
theorem TimeConstructible.succ_mul_of_computableInO {f : ℕ → ℕ} {T : List Bool → ℕ}
    {S : ℕ → ℕ} (c : ℕ)
    (hf : ComputableInO (fun x : List Bool => f x.length) encBits encNat T
      fun x => S x.length)
    (hT : ∀ x, T x ≤ c * ((x.length + 1) * f x.length) + c) (hn : ∀ n, n ≤ f n) :
    TimeConstructible fun n => (n + 1) * f n := by
  have hlen := ComputableInO.natSucc.comp ComputableInO.lengthNat
  have h := computableInDegree_mul.inO.comp (hlen.prod hf)
  obtain ⟨C, hC⟩ := exists_pow_length_encNat_le 3
  obtain ⟨C₂, hC₂⟩ := exists_pow_length_encNat_le 2
  refine TimeConstructible.of_computableInO (150 * C + C₂ + c + 10) h (fun x => ?_)
    (s := fun n =>
    n + 1 + ((encNat n).length + 1) + S n + (2 * (encNat (n + 1)).length + 1 +
      (encNat (f n)).length + 1) ^ 3) fun x => ?_
  · simp only [Function.comp_apply, length_encPair]
    have hTx := hT x
    set n := x.length
    have hfn := hn n
    have h₁ : (n + 1) ^ 2 ≤ 2 * ((n + 1) * f n) + 1 := by nlinarith
    have h₂ : ((encNat n).length + 1) ^ 2 ≤ C₂ * ((n + 1) * f n) + C₂ := by
      have := hC₂ n
      have : C₂ * (n + 1) ≤ C₂ * ((n + 1) * f n + 1) := Nat.mul_le_mul_left _ (by nlinarith)
      have e : C₂ * ((n + 1) * f n + 1) = C₂ * ((n + 1) * f n) + C₂ := by ring
      omega
    have h₃ : f n ≤ (n + 1) * f n := Nat.le_mul_of_pos_left _ (by omega)
    have h₄ := cube_add_le (2 * ((encNat (n + 1)).length + 1)) ((encNat (f n)).length + 1)
    have h₅ : (2 * ((encNat (n + 1)).length + 1)) ^ 3 = 8 * ((encNat (n + 1)).length + 1) ^ 3 := by
      ring
    have h₆ := hC (n + 1)
    have h₇ := hC (f n)
    have h₈ : (2 * (encNat (n + 1)).length + 1 + (encNat (f n)).length + 1) ^ 3 ≤
        (2 * ((encNat (n + 1)).length + 1) + ((encNat (f n)).length + 1)) ^ 3 :=
      Nat.pow_le_pow_left (by omega) 3
    have h₉ : C * (n + 1 + 1) ≤ C * ((n + 1) * f n) + 2 * C := by
      have : n + 1 + 1 ≤ (n + 1) * f n + 2 := by nlinarith
      have := Nat.mul_le_mul_left C this
      have e : C * ((n + 1) * f n + 2) = C * ((n + 1) * f n) + 2 * C := by ring
      omega
    have h₁₀ : C * (f n + 1) ≤ C * ((n + 1) * f n) + C := by
      have := Nat.mul_le_mul_left C (Nat.add_le_add_right h₃ 1)
      have e : C * ((n + 1) * f n + 1) = C * ((n + 1) * f n) + C := by ring
      omega
    have e : (150 * C + C₂ + c + 10) * ((n + 1) * f n) =
        150 * (C * ((n + 1) * f n)) + C₂ * ((n + 1) * f n) + c * ((n + 1) * f n) +
          10 * ((n + 1) * f n) := by
      ring
    omega
  · simp only [Function.comp_apply, length_encPair]
    exact le_rfl

/-- If `f` is time-constructible and `n ≤ f n`, then so is `(n + 1) * f n`. -/
theorem TimeConstructible.succ_mul {f : ℕ → ℕ} (hf : TimeConstructible f) (hn : ∀ n, n ≤ f n) :
    TimeConstructible fun n => (n + 1) * f n :=
  TimeConstructible.succ_mul_of_computableInO 1 hf.computableInO (fun x => by
    have : f x.length ≤ (x.length + 1) * f x.length := Nat.le_mul_of_pos_left _ (by omega)
    omega) hn

/-- `(n + 1) ^ 2` is time-constructible. -/
theorem timeConstructible_succ_sq : TimeConstructible fun n => (n + 1) ^ 2 := by
  have hlen := ComputableInO.natSucc.comp ComputableInO.lengthNat
  obtain ⟨C₂, hC₂⟩ := exists_pow_length_encNat_le 2
  have h := TimeConstructible.succ_mul_of_computableInO (f := fun n => n + 1)
    (S := fun n => n + 1 + ((encNat n).length + 1)) (C₂ + 2) hlen (fun x => by
      have := hC₂ x.length
      have e : (C₂ + 2) * ((x.length + 1) * (x.length + 1)) =
          C₂ * ((x.length + 1) * (x.length + 1)) + 2 * ((x.length + 1) * (x.length + 1)) := by
        ring
      have : C₂ * (x.length + 1) ≤ C₂ * ((x.length + 1) * (x.length + 1)) :=
        Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
      nlinarith) fun n => Nat.le_succ n
  simpa only [sq] using h

/-- `(n + 1) ^ k` is time-constructible for `k ≥ 2`. -/
theorem timeConstructible_succ_pow {k : ℕ} (hk : 2 ≤ k) :
    TimeConstructible fun n => (n + 1) ^ k := by
  induction k, hk using Nat.le_induction with
  | base => exact timeConstructible_succ_sq
  | succ k hk ih =>
    have h := ih.succ_mul fun n =>
      (Nat.le_succ n).trans (Nat.le_self_pow (by omega) _)
    simpa only [pow_succ', mul_comm] using h

/-! ### Space-constructible bounds -/

/-- A bound `s` is space-constructible when some machine with a binary alphabet and finitely many
states computes `s n` in binary from any word of length `n` within space `O(s n)`, halting
[Sipser, Definition 9.1][Sipser2013]. Unlike [Sipser, Definition 9.1][Sipser2013], `s n ≥ log n`
is not required here; the space hierarchy theorem asks for `n ≤ s n`. -/
def SpaceConstructible (s : ℕ → ℕ) : Prop :=
  ∃ c : ℕ, ∃ t : ℕ → ℕ, ComputableInTimeAndSpaceOfLength (fun x : List Bool => s x.length) encBits
    encNat t fun n => c * s n + c

/-- A space-constructible bound is computed within space `O(s n)`, within some time. -/
theorem SpaceConstructible.computableInO {s : ℕ → ℕ} (hs : SpaceConstructible s) :
    ∃ T, ComputableInO (fun x : List Bool => s x.length) encBits encNat T
      fun x => s x.length := by
  obtain ⟨c, t, h⟩ := hs
  refine ⟨fun x => t x.length, .of_bounds h (c + 1) (fun x => ?_) (fun x => ?_) fun x => ?_⟩
  · exact (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ (by omega))
  · dsimp only [encBits_apply]
    nlinarith
  · exact (Universal.length_encNat_le _).trans
      ((Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ (by omega)))

/-- A time-constructible bound is space-constructible, since space is at most time. -/
theorem TimeConstructible.spaceConstructible {t : ℕ → ℕ} (ht : TimeConstructible t) :
    SpaceConstructible t := by
  obtain ⟨c, s, h⟩ := ht
  obtain ⟨k, h⟩ := ComputableInTimeAndSpace.exists_space_linear h
  exact ⟨k * c + k, fun n => c * t n + c, ComputableInTimeAndSpace.mono h (fun _ => le_rfl)
    fun x => by dsimp only; nlinarith⟩

/-- A computation of `s n` in binary within space `O(s n)` makes `s` space-constructible:
it halts within a time bound of `n`, its number of configurations. -/
theorem SpaceConstructible.of_computableInO {s : ℕ → ℕ} {T S : List Bool → ℕ} (c : ℕ)
    (h : ComputableInO (fun x : List Bool => s x.length) encBits encNat T S)
    (hS : ∀ x, S x ≤ c * s x.length + c) : SpaceConstructible s := by
  obtain ⟨k, hk, -⟩ := h
  obtain ⟨t, ht⟩ := ComputableInTimeAndSpace.exists_time_of_length
    (s := fun n => k * (c * s n + c + 1)) (hk.mono (fun _ => le_rfl)
      fun x => Nat.mul_le_mul_left k (by have := hS x; simp only [encBits_apply]; omega))
  exact ⟨k * (c + 1), t, ComputableInTimeAndSpace.mono ht (fun _ => le_rfl) fun x => by
    dsimp only; nlinarith⟩

/-- `n` is space-constructible: count the length of the word in binary. -/
theorem spaceConstructible_id : SpaceConstructible fun n => n :=
  SpaceConstructible.of_computableInO 1 ComputableInO.lengthNat fun x => by omega

/-- `n + 1` is space-constructible. -/
theorem spaceConstructible_succ : SpaceConstructible fun n => n + 1 :=
  SpaceConstructible.of_computableInO 2
    (ComputableInO.natSucc.comp ComputableInO.lengthNat)
    fun x => by have := Universal.length_encNat_le x.length; omega

/-- Constant bounds are space-constructible, in zero space. -/
theorem spaceConstructible_const (c : ℕ) : SpaceConstructible fun _ => c := by
  obtain ⟨t, h⟩ := computableInTimeAndSpace_of_const (α := List Bool) (encIn := encBits)
    (encOut := encNat) c
  exact ⟨0, fun _ => t, h.mono (fun _ => le_rfl) fun _ => Nat.zero_le _⟩

/-- `(n + 1) ^ k` is space-constructible. -/
theorem spaceConstructible_succ_pow (k : ℕ) : SpaceConstructible fun n => (n + 1) ^ k := by
  rcases k with _ | _ | k
  · simpa using spaceConstructible_const 1
  · simpa using spaceConstructible_succ
  · exact (timeConstructible_succ_pow (by omega)).spaceConstructible

/-- `2 ^ n` is space-constructible. -/
theorem spaceConstructible_two_pow : SpaceConstructible (2 ^ ·) :=
  timeConstructible_two_pow.spaceConstructible

/-- `2 ^ (2 ^ n)` is space-constructible. -/
theorem spaceConstructible_two_pow_two_pow : SpaceConstructible fun n => 2 ^ (2 ^ n) :=
  timeConstructible_two_pow_two_pow.spaceConstructible

end Cslib.Complexity
