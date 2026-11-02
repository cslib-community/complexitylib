/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Reader.Arith
public import Complexity.Computability.TreeEval.Reader.Cert.Residue
public import Mathlib.Data.Nat.Choose.Basic

/-!
# Binomial coefficients modulo a prime in binary argument space

The multiplicative recurrence for a binomial coefficient can be evaluated using one residue
and a binary counter. Each denominator is inverted by the existing modular Fermat routine.
When the lower index is smaller than the prime modulus, all denominators are invertible.

This supplies scalar coefficient arithmetic for streaming interpolation. The procedure never
materializes the integer binomial coefficient or its factorials. The native work-space theorem
is total, including zero moduli and lower indices larger than the upper index.

The streaming-counting application is motivated by a personal communication from Charlie Cruz
[Cruz2026SublinearSpace]. The multiplicative binomial recurrence itself is standard.

## Main results

* `Cslib.Arithmetic.binomialMod_eq`: agreement with `Nat.choose` modulo a prime when `k < p`.
* `Cslib.Arithmetic.binomialMod_inSpace`: work space linear in the binary arguments `(p,n,k)`.
-/

public section

namespace Cslib.Arithmetic

open TreeEval Reader

/-- The multiplicative binomial recurrence, retaining a reduced accumulator after each step.
The zero-modulus branch keeps the state bounded even outside the prime-modulus domain. -/
@[expose] def binomialAccumulator (p n : ℕ) : ℕ → ℕ
  | 0 => 1 % p
  | j + 1 => if p = 0 then 0 else
      mulMod p (mulMod p (binomialAccumulator p n j) (n - j)) (unitInv p j)

/-- Compute a binomial residue by a binary counter and one modular accumulator.
Zero moduli and lower indices larger than the upper index return zero. For prime `p`,
correctness requires `k < p`, so that every denominator in the recurrence is a unit. -/
@[expose] def binomialMod (p n k : ℕ) : ℕ :=
  if p = 0 then 0 else if n < k then 0 else binomialAccumulator p n k

/-- A lower index above the upper index gives zero without running the recurrence. -/
@[simp] theorem binomialMod_of_lt {p n k : ℕ} (h : n < k) : binomialMod p n k = 0 := by
  simp [binomialMod, h]

/-- A zero modulus has a specified bounded result. -/
@[simp] theorem binomialMod_zero_modulus (n k : ℕ) : binomialMod 0 n k = 0 := by
  simp [binomialMod]

private theorem binomialAccumulator_le (p n k : ℕ) :
    binomialAccumulator p n k ≤ p + 1 := by
  cases k with
  | zero => exact (Nat.mod_le _ _).trans (by omega)
  | succ k =>
    simp only [binomialAccumulator]
    split_ifs with hp
    · omega
    · exact (Nat.mod_lt _ (Nat.pos_of_ne_zero hp)).le.trans (by omega)

private theorem binomialAccumulator_lt {p : ℕ} (hp : 0 < p) (n k : ℕ) :
    binomialAccumulator p n k < p := by
  cases k with
  | zero => exact Nat.mod_lt _ hp
  | succ k =>
    simp only [binomialAccumulator, hp.ne', ↓reduceIte]
    exact Nat.mod_lt _ hp

/-- Every result is a reduced residue when the modulus is positive. -/
theorem binomialMod_lt {p : ℕ} (hp : 0 < p) (n k : ℕ) : binomialMod p n k < p := by
  simp only [binomialMod, hp.ne', ↓reduceIte]
  split_ifs
  · exact hp
  · exact binomialAccumulator_lt hp n k

private theorem cast_binomialAccumulator {p : ℕ} [Fact p.Prime] (n k : ℕ) (hk : k < p) :
    ((binomialAccumulator p n k : ℕ) : ZMod p) = (Nat.choose n k : ZMod p) := by
  induction k with
  | zero => simp [binomialAccumulator]
  | succ k ih =>
    have hj : k < p - 1 := by omega
    have hrec := congrArg (fun m : ℕ => (m : ZMod p)) (Nat.choose_succ_right_eq n k)
    simp only [Nat.cast_mul] at hrec
    have hu : (Iter.zmodUnit p k : ZMod p) = ((k + 1 : ℕ) : ZMod p) := by
      rw [Iter.zmodUnit_val hj, Nat.cast_add, Nat.cast_one]
    rw [← hu] at hrec
    simp only [binomialAccumulator, (Fact.out : p.Prime).ne_zero, ↓reduceIte,
      cast_mulMod, ih (by omega), cast_unitInv_eq hj]
    rw [← hrec]
    exact Units.mul_inv_cancel_right _ _

/-- For a prime modulus, the counter procedure computes the binomial coefficient modulo `p`
as long as the lower index is smaller than the modulus. There is no bound on the upper index. -/
theorem binomialMod_eq {p : ℕ} [Fact p.Prime] (n k : ℕ) (hk : k < p) :
    binomialMod p n k = Nat.choose n k % p := by
  by_cases hnk : n < k
  · simp [binomialMod_of_lt hnk, Nat.choose_eq_zero_of_lt hnk]
  · have h := congrArg ZMod.val (cast_binomialAccumulator n k hk)
    simpa only [binomialMod, (Fact.out : p.Prime).ne_zero, hnk, ↓reduceIte,
      ZMod.val_natCast, Nat.mod_eq_of_lt (binomialAccumulator_lt (Fact.out : p.Prime).pos n k)]
      using h

/-- The residue returned by the procedure casts to the binomial coefficient in the prime field. -/
theorem cast_binomialMod {p : ℕ} [Fact p.Prime] (n k : ℕ) (hk : k < p) :
    ((binomialMod p n k : ℕ) : ZMod p) = (Nat.choose n k : ZMod p) := by
  rw [binomialMod_eq n k hk, ZMod.natCast_mod]

private def binomialStep (state : (ℕ × ℕ) × ℕ × ℕ) : (ℕ × ℕ) × ℕ × ℕ :=
  let ((p, n), j, acc) := state
  ((p, n), j + 1, if p = 0 then 0 else
    mulMod p (mulMod p acc (n - j)) (unitInv p j))

private theorem iterate_binomialStep (p n j : ℕ) :
    binomialStep^[j] ((p, n), 0, 1 % p) = ((p, n), j, binomialAccumulator p n j) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', ih]; rfl

open Turing MultiTapeTM ComputableInSpace

private abbrev encBinomialState : (ℕ × ℕ) × ℕ × ℕ ↪ List Bool :=
  encPair (encPair encNat encNat) (encPair encNat encNat)

private theorem binomialStep_inSpace :
    ComputableInSpace binomialStep encBinomialState encBinomialState
      fun state => (encBinomialState state).length := by
  have hpar := fst (encPair encNat encNat) (encPair encNat encNat)
  have hp := fst' hpar
  have hn := snd' hpar
  have hja := snd (encPair encNat encNat) (encPair encNat encNat)
  have hj := fst' hja
  have hacc := snd' hja
  have hnum := budget_comp_linear mulMod_inSpace
    (budget_prod hp (budget_prod hacc (budget_natSub hn hj)))
  have hinv := budget_comp_linear unitInv_inSpace (budget_prod hp hj)
  have hmul := budget_comp_linear mulMod_inSpace (budget_prod hp (budget_prod hnum hinv))
  have hnext := budget_ite (budget_natIsZero hp)
    (budget_const (encB := encNat) 0 (.refl _)) hmul
  exact (budget_prod hpar (budget_prod (budget_natSucc hj) hnext)).of_enc_eq fun state => by
    rcases state with ⟨⟨p, n⟩, j, acc⟩
    by_cases h : p = 0 <;> simp [binomialStep, h]

/-- The modular binomial procedure is computed by a native multitape Turing machine in work
space linear in the binary encodings of `(p,n,k)`. The resource certificate is total and does not
assume that `p` is prime or that either index is in the correctness range. -/
theorem binomialMod_inSpace :
    ComputableInSpace (fun (p, n, k) => binomialMod p n k) encNat3 encNat
      fun args => (encNat3 args).length := by
  have hp := fst encNat (encPair encNat encNat)
  have hnk := snd encNat (encPair encNat encNat)
  have hn := fst' hnk
  have hk := snd' hnk
  have hpar := budget_prod hp hn
  have hone := budget_natMod (budget_const (encB := encNat) 1 (.refl _)) hp
  have hinit := budget_prod hpar
    (budget_prod (budget_const (encB := encNat) 0 (.refl _)) hone)
  have hstates (args : ℕ × ℕ × ℕ) (j : ℕ) (hj : j ≤ args.2.2) :
      (encBinomialState (binomialStep^[j] ((args.1, args.2.1), 0, 1 % args.1))).length ≤
        16 * ((encNat3 args).length + 1) := by
    rw [iterate_binomialStep]
    have hacc := length_encNat_mono (binomialAccumulator_le args.1 args.2.1 j)
    have hcounter := length_encNat_mono hj
    have hsucc := length_encNat_add_le_add args.1 1
    have h1 : (encNat 1).length = 1 := rfl
    simp only [encBinomialState, encNat3, length_encPair] at hacc hcounter hsucc ⊢
    omega
  have hrun := budget_iterate hk hinit binomialStep_inSpace hstates
    (.of_le_linear 16 16 fun _ => le_rfl)
  have hacc : ComputableInSpace (fun (p, n, k) => binomialAccumulator p n k) encNat3 encNat
      (fun args => (encNat3 args).length) :=
    (snd' (snd' hrun)).of_enc_eq fun args => by rw [iterate_binomialStep]
  have hzero := budget_const (encB := encNat) 0 (α := ℕ × ℕ × ℕ)
    (encIn := encNat3) (.refl _)
  exact (budget_ite (budget_natIsZero hp) hzero
    (budget_ite (budget_natLt hn hk) hzero hacc)).of_enc_eq fun args => by
      rcases args with ⟨p, n, k⟩
      by_cases hp : p = 0 <;> by_cases hnk : n < k <;> simp [binomialMod, hp, hnk]

end Cslib.Arithmetic
