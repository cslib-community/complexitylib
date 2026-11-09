/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.Interfaces
public import CslibFrontier.Computability.GenericRAM.Native.ExpTimePolySpace

/-!
# Calling a contraction algorithm behind a guard

Applications of the contraction interface
(`Cslib.Complexity.CountingSimulation.ContractionAlgorithm`) evaluate a polynomial-time guard and
then either compute a precision and a network in polynomial time and run the contraction algorithm
on them, or return a polynomial-time fallback answer. When the networks of the inputs passing the
guard are admissible at a size `s ≥ 2` with a fixed constant, with a precision between `1` and a
fixed multiple of `s`, this machine runs in time `2 ^ E` times a polynomial and in polynomial space
for every exponent `E` that bounds the interface's exponent `K s / √⌊log₂ s⌋` on those inputs
(`Cslib.Complexity.CountingSimulation.ContractionAlgorithm.expTimePolySpace_branch`).

## Main results

* `Cslib.Complexity.CountingSimulation.ContractionAlgorithm.expTimePolySpace_branch`: the time and
  space of a guarded call.
-/

public section

namespace Cslib.Complexity.CountingSimulation

open Turing.MultiTapeTM Cslib.GenericRAM

variable {α N : Type} {enc : α ↪ List Bool} {encN : N ↪ List Bool} {value : N → ℕ}
  {Admissible : ℕ → ℕ → N → Prop}

/-- **A guarded call of a contraction algorithm** runs in time `2 ^ E` times a polynomial and in
polynomial space. The machine evaluates a polynomial-time `guard`; on the inputs passing it, it
computes a precision and a network by the polynomial-time `input` and runs the contraction
algorithm `A`, and elsewhere it returns the polynomial-time `fallback`. If the network of every
input `a` passing the guard is admissible at a size `s a ≥ 2` with constant `C`, with a precision
between `1` and `D * s a`, then for some `K` the machine runs in time `2 ^ E` times a polynomial
and in polynomial space for every exponent `E` with `K * s a / √⌊log₂ (s a)⌋ ≤ E a` on those
inputs. -/
theorem ContractionAlgorithm.expTimePolySpace_branch
    (A : ContractionAlgorithm encN value Admissible)
    {guard : α → Bool} (hguard : ComputableInPolyTime guard enc encBool)
    {input : α → ℕ × N} (hinput : ComputableInPolyTime input enc (encPair encNat encN))
    {fallback : α → ℕ} (hfallback : ComputableInPolyTime fallback enc encNat)
    (C D : ℕ) (s : α → ℕ)
    (hs : ∀ a, guard a = true → 2 ≤ s a ∧ 1 ≤ (input a).1 ∧ (input a).1 ≤ D * s a ∧
      Admissible C (s a) (input a).2) :
    ∃ K : ℕ, ∀ E : α → ℕ, (∀ a, guard a = true → K * s a / Nat.sqrt (Nat.log 2 (s a)) ≤ E a) →
      (NativeCertificate.branch (NativeCertificate.ofPolyTime hguard)
        (A.certificate.comp (NativeCertificate.ofPolyTime hinput))
        (NativeCertificate.ofPolyTime hfallback)).ExpTimePolySpace E := by
  obtain ⟨K, hK⟩ := A.bound C D
  obtain ⟨p, q, hlen⟩ := hinput.polyBounded_length.exists_le
  refine ⟨K, fun E hE => ?_⟩
  obtain ⟨Cg, dg, hg⟩ := NativeCertificate.expTimePolySpace_ofPolyTime hguard E
  obtain ⟨Ci, di, hi⟩ := NativeCertificate.expTimePolySpace_ofPolyTime hinput E
  obtain ⟨Cf, df, hf⟩ := NativeCertificate.expTimePolySpace_ofPolyTime hfallback E
  set d := dg + di + df + q * K
  refine ⟨Cg + Ci + Cf + K * (p + 1) ^ K, d, fun a => ?_⟩
  -- every time bound is a multiple of `2 ^ E a * Y` and every space bound a multiple of `Y`
  set Y := ((enc a).length + 1) ^ d
  have hY {e : ℕ} (he : e ≤ d) : ((enc a).length + 1) ^ e ≤ Y :=
    Nat.pow_le_pow_right (Nat.succ_pos _) he
  have hT {c t e : ℕ} (he : e ≤ d) (h : t ≤ c * 2 ^ E a * ((enc a).length + 1) ^ e) :
      t ≤ c * (2 ^ E a * Y) := by
    rw [← Nat.mul_assoc]
    exact h.trans (Nat.mul_le_mul_left _ (hY he))
  have hS {c t e : ℕ} (he : e ≤ d) (h : t ≤ c * ((enc a).length + 1) ^ e) : t ≤ c * Y :=
    h.trans (Nat.mul_le_mul_left _ (hY he))
  have tg := hT (by omega) (hg a).1
  have sg := hS (by omega) (hg a).2
  have ti := hT (by omega) (hi a).1
  have si := hS (by omega) (hi a).2
  have tf := hT (by omega) (hf a).1
  have sf := hS (by omega) (hf a).2
  rw [NativeCertificate.branch_time, NativeCertificate.branch_space, NativeCertificate.comp_time,
    NativeCertificate.comp_space, Nat.mul_assoc]
  have hsplit (c₁ c₂ c₃ c₄ Z : ℕ) :
      (c₁ + c₂ + c₃ + c₄) * Z = c₁ * Z + c₂ * Z + c₃ * Z + c₄ * Z := by ring
  rw [hsplit, hsplit]
  by_cases hga : guard a = true
  · -- the contraction, on an input of length polynomial in that of `a`
    obtain ⟨hs2, hP1, hPD, hadm⟩ := hs a hga
    obtain ⟨hAt, hAs⟩ := hK (s a) (input a).1 (input a).2 hs2 hP1 hPD hadm
    have hlenK : ((encPair encNat encN (input a)).length + 1) ^ K ≤
        (p + 1) ^ K * ((enc a).length + 1) ^ (q * K) := by
      have h1 := hlen a
      have h2 : 1 ≤ ((enc a).length + 1) ^ q := Nat.one_le_pow _ _ (Nat.succ_pos _)
      calc _ ≤ ((p + 1) * ((enc a).length + 1) ^ q) ^ K := Nat.pow_le_pow_left (by nlinarith) K
        _ = _ := by rw [mul_pow, pow_mul]
    have hqK := hY (e := q * K) (by omega)
    have ta : A.certificate.time (input a) ≤ K * (p + 1) ^ K * (2 ^ E a * Y) :=
      calc A.certificate.time (input a)
          ≤ K * ((p + 1) ^ K * ((enc a).length + 1) ^ (q * K)) * 2 ^ E a :=
            hAt.trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ hlenK)
              (Nat.pow_le_pow_right (by norm_num) (hE a hga)))
        _ = K * (p + 1) ^ K * (2 ^ E a * ((enc a).length + 1) ^ (q * K)) := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hqK)
    have sa : A.certificate.space (input a) ≤ K * (p + 1) ^ K * Y :=
      calc A.certificate.space (input a)
          ≤ K * ((p + 1) ^ K * ((enc a).length + 1) ^ (q * K)) :=
            hAs.trans (Nat.mul_le_mul_left _ hlenK)
        _ ≤ _ := by
            rw [← Nat.mul_assoc]
            exact Nat.mul_le_mul_left _ hqK
    rw [ite_eq_left hga, ite_eq_left hga]
    omega
  · rw [ite_eq_right hga, ite_eq_right hga]
    omega

end Cslib.Complexity.CountingSimulation
