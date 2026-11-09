/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.RP
public import CslibFrontier.Foundations.NumberTheory.Primality.StrongLiars
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Words
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.PowMod
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Nat
import CslibFrontier.Foundations.Data.BitString.Binary
import CslibFrontier.Foundations.Data.BitString.Counter
import Mathlib.Data.Int.CardIntervalMod

/-!
# The Miller–Rabin test: PRIMES is in coRP

The Miller–Rabin test [Rabin][Rabin1980] is a polynomial-time verifier that puts the non-primes
(the composite numbers, `0` and `1`), given in binary, in `RP`, and so the primes in `coRP`. On an
odd `n > 2` it reads a random word `r` of `2 |n|` bits, where `|n|` is the length of the binary
encoding of `n`. It takes the base `a = 1 + (value of r mod (n - 1))`, in `[1, n - 1]`, and
accepts, declaring `n` composite, when `a` is not a strong liar for `n` (`ZMod.IsStrongLiar`).
Numbers below `2` and even numbers other than `2` are accepted outright, and `2` is rejected.

* A prime is never accepted: modulo a prime every nonzero residue is a strong liar
  (`ZMod.isStrongLiar_of_prime`).
* An odd composite `n` is accepted on at least half of the random words. At most `φ(n) / 2 ≤
  (n - 2) / 2` residues are strong liars (`ZMod.two_mul_card_isStrongLiar_le`), and each residue
  modulo `n - 1` is hit by at most `2 ^ (2 |n|) / (n - 1) + 1` words. The bias from reducing a
  random word modulo `n - 1` is absorbed because `2 ^ (2 |n|) ≥ n ^ 2`.

The test `MillerRabin.passes m a` checks the strong-liar condition for the base `a` modulo `m + 1`
without computing the decomposition `m = 2 ^ s * t`, `t` odd: it scans every `j < |m|` with
`2 ^ j ∣ m` and accepts when `m / 2 ^ j` is odd and `a ^ (m / 2 ^ j) ≡ 1`, or when `j > 0` and
`a ^ (m / 2 ^ j) ≡ -1`. The powers use polynomial-time square-and-multiply
(`Turing.MultiTapeTM.ComputableInPolyTime.binary_powMod`).

Membership of the primes in `coRP` already follows from the AKS theorem: `primes_mem_P` (PRIMES is
in `P`) with `P_subset_coRP`. The point of this file is the explicit randomized verifier and its
error analysis, which are independent of AKS.

## Main definitions

* `Cslib.Complexity.MillerRabin.passes`: one Miller–Rabin round for the candidate `m + 1`.
* `Cslib.Complexity.MillerRabin.verifier`: the one-sided-error verifier for the non-primes.

## Main results

* `Cslib.Complexity.MillerRabin.passes_eq_true_iff`: a round passes exactly on strong liars.
* `Cslib.Complexity.MillerRabin.verifier_polyTime`: the verifier runs in polynomial time.
* `Cslib.Complexity.MillerRabin.decidesWithOneSidedError`: the verifier decides the non-primes
  with one-sided error, using `2 |n|` random bits.
* `Cslib.Complexity.MillerRabin.primes_mem_coRP`: the primes are in `coRP`.

## References

* [M. O. Rabin, *Probabilistic algorithm for testing primality*][Rabin1980]
* [R. Motwani, P. Raghavan, *Randomized Algorithms*][MotwaniRaghavan95]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

public section

open Turing.MultiTapeTM

namespace Cslib.Complexity.MillerRabin

/-- One **Miller–Rabin round** for the candidate `m + 1` with base `a`: some `j < |m|` with
`2 ^ j ∣ m` has `m / 2 ^ j` odd and `a ^ (m / 2 ^ j) ≡ 1`, or `j > 0` and `a ^ (m / 2 ^ j) ≡ -1`,
modulo `m + 1`. For `m > 0` this holds exactly when `a` is a strong liar for `m + 1`
(`passes_eq_true_iff`). -/
@[expose] def passes (m a : ℕ) : Bool :=
  (List.range m.size).any fun j =>
    m % 2 ^ j == 0 &&
      ((m / 2 ^ j % 2 == 1 && a ^ (m / 2 ^ j) % (m + 1) == 1) ||
        (0 < j && a ^ (m / 2 ^ j) % (m + 1) == m))

/-- The **Miller–Rabin verifier** for the non-primes. It accepts `n < 2` and even `n ≠ 2`,
rejects `2`, and on an odd `n > 2` accepts exactly when the base `1 + (ofBits r mod (n - 1))` fails
the round. -/
@[expose] def verifier (x : ℕ × List Bool) : Bool :=
  if x.1 < 2 then true
  else if x.1 % 2 = 0 then x.1 != 2
  else !passes (x.1 - 1) (1 + ofBits x.2 % (x.1 - 1))

/-- A Miller–Rabin round is computable in polynomial time. -/
theorem passes_polyTime :
    ComputableInPolyTime (fun p : ℕ × ℕ => passes p.1 p.2) (encPair encNat encNat) encBool := by
  unfold passes
  apply ComputableInPolyTime.anyWithInput (encA := encUnary)
  · fun_prop
  · have hexp : ComputableInPolyTime (fun q : (ℕ × ℕ) × ℕ => q.1.1 / 2 ^ q.2)
        (encPair (encPair encNat encNat) encUnary) encNat := by
      fun_prop
    have hpow : ComputableInPolyTime
        (fun q : (ℕ × ℕ) × ℕ => q.1.2 ^ (q.1.1 / 2 ^ q.2) % (q.1.1 + 1))
        (encPair (encPair encNat encNat) encUnary) encNat :=
      ComputableInPolyTime.binary_powMod (by fun_prop) hexp (by fun_prop) fun _ => Nat.succ_pos _
    fun_prop

/-- The Miller–Rabin verifier is computable in polynomial time. -/
theorem verifier_polyTime :
    ComputableInPolyTime verifier (encPair encNat encBits) encBool := by
  have hinner : ComputableInPolyTime
      (fun x : ℕ × List Bool => (x.1 - 1, 1 + ofBits x.2 % (x.1 - 1)))
      (encPair encNat encBits) (encPair encNat encNat) := by
    fun_prop
  have hpasses : ComputableInPolyTime
      (fun x : ℕ × List Bool => passes (x.1 - 1) (1 + ofBits x.2 % (x.1 - 1)))
      (encPair encNat encBits) encBool :=
    passes_polyTime.comp hinner
  unfold verifier
  fun_prop

private theorem pow_mod_eq_one_iff {m a e : ℕ} (hm : 0 < m) :
    a ^ e % (m + 1) = 1 ↔ (a : ZMod (m + 1)) ^ e = 1 := by
  rw [← Nat.cast_pow, ← Nat.cast_one (R := ZMod (m + 1)), ZMod.natCast_eq_natCast_iff',
    Nat.mod_eq_of_lt (show 1 < m + 1 by omega)]

private theorem pow_mod_eq_neg_one_iff {m a e : ℕ} :
    a ^ e % (m + 1) = m ↔ (a : ZMod (m + 1)) ^ e = -1 := by
  have hm : ((m : ℕ) : ZMod (m + 1)) = -1 := by
    have h := ZMod.natCast_self (m + 1)
    rw [Nat.cast_add, Nat.cast_one] at h
    exact eq_neg_of_add_eq_zero_left h
  rw [← hm, ← Nat.cast_pow, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (Nat.lt_succ_self m)]

/-- For `m > 0`, a Miller–Rabin round for `m + 1` passes exactly on the strong liars. -/
theorem passes_eq_true_iff {m a : ℕ} (hm : 0 < m) :
    passes m a = true ↔ ZMod.IsStrongLiar (m + 1) (a : ZMod (m + 1)) := by
  rw [ZMod.isStrongLiar_iff, Nat.add_sub_cancel]
  set s := m.factorization 2 with hs
  set t := ordCompl[2] m with ht
  have hst : 2 ^ s * t = m := Nat.ordProj_mul_ordCompl_eq_self m 2
  have htodd : t % 2 = 1 := Nat.two_dvd_ne_zero.1 (Nat.not_dvd_ordCompl Nat.prime_two hm.ne')
  have hdvd : ∀ j, m % 2 ^ j = 0 ↔ j ≤ s := fun j => by
    rw [← Nat.dvd_iff_mod_eq_zero]
    exact Nat.prime_two.pow_dvd_iff_le_factorization hm.ne'
  have hdiv : ∀ j ≤ s, m / 2 ^ j = 2 ^ (s - j) * t := fun j hj => by
    rw [← hst, show s = (s - j) + j by omega, pow_add, Nat.add_sub_cancel,
      Nat.mul_assoc, Nat.mul_comm (2 ^ j), ← Nat.mul_assoc, Nat.mul_div_cancel _ (by positivity)]
  have hodd : ∀ j ≤ s, m / 2 ^ j % 2 = 1 ↔ j = s := fun j hj => by
    rw [hdiv j hj]
    rcases Nat.eq_zero_or_pos (s - j) with h | h
    · rw [h, pow_zero, one_mul]
      exact ⟨fun _ => by omega, fun _ => htodd⟩
    · obtain ⟨u, hu⟩ : ∃ u, s - j = u + 1 := ⟨s - j - 1, by omega⟩
      rw [hu, pow_succ, Nat.mul_comm (2 ^ u) 2, Nat.mul_assoc, Nat.mul_mod_right]
      omega
  have hsize : s < m.size := by
    rw [Nat.lt_size]
    calc 2 ^ s ≤ 2 ^ s * t := Nat.le_mul_of_pos_right _ (Nat.ordCompl_pos 2 hm.ne')
      _ = m := hst
  have hdivs : m / 2 ^ s = t := by rw [hdiv s le_rfl, Nat.sub_self, pow_zero, one_mul]
  simp only [passes, List.any_eq_true, List.mem_range, Bool.and_eq_true, Bool.or_eq_true,
    beq_iff_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨j, -, hj, (⟨hjodd, h⟩ | ⟨hj0, h⟩)⟩
    · have hjs := (hdvd j).1 hj
      obtain rfl := (hodd j hjs).1 hjodd
      left
      rwa [hdivs, pow_mod_eq_one_iff hm] at h
    · have hjs := (hdvd j).1 hj
      right
      refine ⟨s - j, by omega, ?_⟩
      rwa [hdiv j hjs, pow_mod_eq_neg_one_iff] at h
  · rintro (h | ⟨i, hi, h⟩)
    · refine ⟨s, hsize, (hdvd s).2 le_rfl, Or.inl ⟨(hodd s le_rfl).2 rfl, ?_⟩⟩
      rwa [hdivs, pow_mod_eq_one_iff hm]
    · refine ⟨s - i, by omega, (hdvd _).2 (by omega), Or.inr ⟨by omega, ?_⟩⟩
      rwa [hdiv _ (by omega), show s - (s - i) = i by omega, pow_mod_eq_neg_one_iff]

/-- Among the words of `k` bits, at most `#S * (2 ^ k / N + 1)` have binary value modulo `N` in
`S`. -/
private theorem card_filter_ofBits_mod_mem_le {k N : ℕ} (hN : 0 < N) (S : Finset ℕ) :
    (Finset.univ.filter fun r : Fin k → Bool => ofBits (List.ofFn r) % N ∈ S).card ≤
      (2 ^ k / N + 1) * S.card := by
  classical
  refine Finset.card_le_mul_card_image_of_maps_to (f := fun r => ofBits (List.ofFn r) % N)
    (fun r hr => (Finset.mem_filter.1 hr).2) _ fun v _ => ?_
  have hval : ∀ r : Fin k → Bool, ofBits (List.ofFn r) = (BitString.equivFin k r : ℕ) := fun r => by
    rw [ofBits, ← BitString.lsbValue_eq_foldr_bit, BitString.lsbValue_ofFn]
  calc _ ≤ ((Finset.range (2 ^ k)).filter fun x => x ≡ v [MOD N]).card := by
        refine Finset.card_le_card_of_injOn (fun r => ofBits (List.ofFn r)) ?_ ?_
        · intro r hr
          simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
            Set.mem_ofPred_eq] at hr
          simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq, hval]
          refine ⟨(BitString.equivFin k r).2, ?_⟩
          rw [← hval, Nat.ModEq, ← hr.2, Nat.mod_mod]
        · intro r _ r' _ h
          simp only [hval] at h
          exact (BitString.equivFin k).injective (Fin.ext h)
    _ = (2 ^ k).count (· ≡ v [MOD N]) := (Nat.count_eq_card_filter_range _ _).symm
    _ ≤ 2 ^ k / N + 1 := by
        rw [Nat.count_modEq_card (2 ^ k) hN v]
        split_ifs <;> omega

private theorem succ_mul_pred_le {Q N : ℕ} (h : N - 1 ≤ Q) : (Q + 1) * (N - 1) ≤ Q * N := by
  rcases N with _ | N
  · simp
  · rw [Nat.add_sub_cancel] at h ⊢
    nlinarith

/-- For an odd composite `n`, at most half of the random words make the verifier reject. -/
private theorem two_mul_card_reject_le {n : ℕ} (hodd : Odd n) (h1 : 1 < n) (hn : ¬ n.Prime) :
    2 * (Finset.univ.filter fun r : Fin (2 * n.size) → Bool =>
      passes (n - 1) (1 + ofBits (List.ofFn r) % (n - 1)) = true).card ≤ 2 ^ (2 * n.size) := by
  classical
  have : NeZero n := ⟨by omega⟩
  set N := n - 1 with hNdef
  have hN : 0 < N := by obtain ⟨k, rfl⟩ := hodd; omega
  have hnN : N + 1 = n := by omega
  set S := (Finset.range N).filter fun v => passes N (1 + v) = true with hS
  have hsub : (Finset.univ.filter fun r : Fin (2 * n.size) → Bool =>
      passes N (1 + ofBits (List.ofFn r) % N) = true) ⊆
      Finset.univ.filter fun r : Fin (2 * n.size) → Bool => ofBits (List.ofFn r) % N ∈ S := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hS, Finset.mem_range] at hr ⊢
    exact ⟨Nat.mod_lt _ hN, hr⟩
  have hcount := (Finset.card_le_card hsub).trans (card_filter_ofBits_mod_mem_le hN S)
  -- the residues in `S` give distinct strong liars
  have hS_le : 2 * S.card ≤ N - 1 := by
    have hinj : S.card ≤ (Finset.univ.filter (ZMod.IsStrongLiar n)).card := by
      refine Finset.card_le_card_of_injOn (fun v => ((1 + v : ℕ) : ZMod n)) ?_ ?_
      · intro v hv
        simp only [hS, Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hv
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
        have := (passes_eq_true_iff hN).1 hv.2
        rwa [hnN] at this
      · intro v hv w hw h
        simp only [hS, Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hv hw
        have h' := (ZMod.natCast_eq_natCast_iff' _ _ _).1 h
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h'
        omega
    have hliar := ZMod.two_mul_card_isStrongLiar_le hodd h1 hn
    have htot : n.totient ≤ n - 2 := by
      have hlt := Nat.totient_lt n h1
      have hne : n.totient ≠ n - 1 := fun h => hn ((Nat.totient_eq_iff_prime (by omega)).1 h)
      omega
    omega
  -- `2 ^ (2 * size n) ≥ N ^ 2`
  have hsq : N * N ≤ 2 ^ (2 * n.size) := by
    have hlt : n < 2 ^ n.size := Nat.lt_size_self n
    rw [two_mul, pow_add]
    exact Nat.mul_le_mul (by omega) (by omega)
  have hQ : N - 1 ≤ 2 ^ (2 * n.size) / N := by
    rw [Nat.le_div_iff_mul_le hN]
    exact (Nat.mul_le_mul_right _ (Nat.sub_le N 1)).trans hsq
  have hQN : 2 ^ (2 * n.size) / N * N ≤ 2 ^ (2 * n.size) := Nat.div_mul_le_self _ _
  calc 2 * _ ≤ 2 * ((2 ^ (2 * n.size) / N + 1) * S.card) := Nat.mul_le_mul_left 2 hcount
    _ = (2 ^ (2 * n.size) / N + 1) * (2 * S.card) := by ring
    _ ≤ (2 ^ (2 * n.size) / N + 1) * (N - 1) := Nat.mul_le_mul_left _ hS_le
    _ ≤ 2 ^ (2 * n.size) / N * N := succ_mul_pred_le hQ
    _ ≤ 2 ^ (2 * n.size) := hQN

/-- **The Miller–Rabin test** decides the non-primes with one-sided error, reading `2 |n|` random
bits on the input `n`: `0`, `1` and even composites are always accepted, an odd composite is
accepted on at least half of the random words, and a prime on none. -/
theorem decidesWithOneSidedError :
    DecidesWithOneSidedError encNat (2 * Polynomial.X) verifier {n | ¬ n.Prime} := by
  intro n
  have hlen : (2 * Polynomial.X : Polynomial ℕ).eval (encNat n).length = 2 * n.size := by
    rw [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat, encNat_apply,
      Nat.size_eq_bits_len]
  rw [hlen]
  refine ⟨fun hn => ?_, fun hn r => ?_⟩
  · simp only [PromiseProblem.yes_ofSet, Set.mem_ofPred_eq] at hn
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (2 * n.size) → Bool)))
      (fun r => verifier (n, List.ofFn r) = true)
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
      Bool.not_eq_true] at hsplit
    suffices hrej : 2 * (Finset.univ.filter fun r : Fin (2 * n.size) → Bool =>
        verifier (n, List.ofFn r) = false).card ≤ 2 ^ (2 * n.size) by omega
    by_cases hodd : n < 2 ∨ n % 2 = 0
    · have hempty : (Finset.univ.filter fun r : Fin (2 * n.size) → Bool =>
          verifier (n, List.ofFn r) = false) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 fun r _ => ?_
        rcases hodd with h | h
        · simp [verifier, h]
        · have h2 : n ≠ 2 := fun h2 => hn (h2 ▸ Nat.prime_two)
          simp [verifier, h, h2]
      rw [hempty, Finset.card_empty]
      exact Nat.zero_le _
    · rw [not_or, not_lt] at hodd
      have hodd' : Odd n := Nat.odd_iff.2 (by omega)
      have heq : (Finset.univ.filter fun r : Fin (2 * n.size) → Bool =>
          verifier (n, List.ofFn r) = false) =
          Finset.univ.filter fun r : Fin (2 * n.size) → Bool =>
            passes (n - 1) (1 + ofBits (List.ofFn r) % (n - 1)) = true := by
        refine Finset.filter_congr fun r _ => ?_
        simp only [verifier, show ¬ n < 2 by omega, hodd.2, ite_false, Bool.not_eq_false']
      rw [heq]
      exact two_mul_card_reject_le hodd' (by omega) hn
  · simp only [PromiseProblem.no_ofSet, Set.mem_compl_iff, Set.mem_ofPred_eq, not_not] at hn
    have h1 := hn.one_lt
    rcases hn.eq_two_or_odd with h2 | hodd
    · simp [verifier, h2]
    · have : Fact n.Prime := ⟨hn⟩
      have hN : 0 < n - 1 := by omega
      simp only [verifier, show ¬ n < 2 by omega, hodd, ite_false, one_ne_zero,
        Bool.not_eq_false']
      rw [passes_eq_true_iff hN, Nat.sub_add_cancel (by omega)]
      apply ZMod.isStrongLiar_of_prime
      intro h0
      rw [ZMod.natCast_eq_zero_iff] at h0
      have hlt := Nat.mod_lt (ofBits (List.ofFn r)) hN
      exact absurd (Nat.le_of_dvd (by omega) h0) (by omega)

/-- **PRIMES is in coRP**, by the Miller–Rabin test. This membership also follows from AKS
(`primes_mem_P` with `P_subset_coRP`); this proof uses only the randomized verifier. -/
theorem primes_mem_coRP : {n : ℕ | n.Prime} ∈ coRP encNat := by
  rw [mem_coRP, Set.compl_ofPred]
  exact ⟨_, _, verifier_polyTime, decidesWithOneSidedError⟩

end Cslib.Complexity.MillerRabin
