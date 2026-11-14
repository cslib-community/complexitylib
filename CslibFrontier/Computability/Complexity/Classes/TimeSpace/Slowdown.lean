/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Constructible
public import CslibFrontier.Computability.Complexity.Classes.Time.SigmaTwo
import CslibFrontier.Computability.Complexity.Classes.Constructible.UnaryClock
import CslibFrontier.Computability.Complexity.Classes.Time.Verifier
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Frame.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.LinearPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCombinators
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OPrimitives
import CslibFrontier.Foundations.Data.Nat.Doubling
import CslibFrontier.Tactic.EncLen

/-!
# The slowdown lemma for two-quantifier alternating time

If nondeterministic linear time is in deterministic time `t'`, then the universal quantifier of a
`Σ₂TIME(t)` problem can be removed at the cost of one application of `t'`: `Σ₂TIME(t)` is in
nondeterministic time `t'(O(t n))` (`Cslib.Complexity.SigmaTwoTIME_subset_NTIME`). For
`t' m = m ^ c` this is the step "if `NTIME(n) ⊆ DTIME(n ^ c)` then `Σ₂TIME(t) ⊆ NTIME(t ^ c)`" of
the time–space lower bounds for nondeterministic linear time of
[Arora and Barak, Section 5.4][AroraBarak09], following [Fortnow, 2000][Fortnow2000] and
[Lipton and Viglas, 1999][LiptonViglas1999]; see also
[Fortnow et al., 2005][FortnowLiptonVanMelkebeekViglas2005].

## Virtual padding

Let `V` be a `Σ₂TIME(t)` verifier with threshold `c`, and fix an instance `y` of length `n` and
the certificate length `L y = c * 2 ^ Nat.size (t n)`, which lies between `c * t n + c` and
`c * (2 * t n + 1)` and is computable in unary within `O(t n)` steps because `t` is
time-constructible. The proof does not pad instances explicitly. Instead, it applies the
hypothesis `NTIME(n) ⊆ DTIME(t')` to the *universal block* `B'`: the set of words `z` such that
some `v` of length `|dropFrame z|` makes `V (unframe z, (dropFrame z, v))` false. An instance of
`B'` of the form `z = frame y ++ u` carries the existential certificate `u` itself, so its length
`2 * n + 1 + L y` is at least `c * t n` and at most `O(n + t n)`. The verifier of `B'` runs `V` once
and is linear in `|z|`, because the certificate `v` is not longer than `z`. Hence `B'` is in
`NTIME(n)`, so in `DTIME(t')`, and a nondeterministic machine for the original problem guesses
`u` of length `L y`, then decides `frame y ++ u ∉ B'` deterministically within
`t'(|z|) = t'(O(n + t n))` steps.

Two features of `Cslib.Complexity.SigmaTwoTIME` are used. Every certificate length above the
threshold decides membership, so the rounded length `L y` may be used. And the verifier is linear
on every input, also on certificates below the threshold, so `B'` is in `NTIME(n)` on all words,
not only on the padded ones.

## Main results

* `Cslib.Complexity.SigmaTwoTIME_subset_NTIME`: `NTIME(n) ⊆ DTIME(t')` implies
  `Σ₂TIME(t) ⊆ NTIME(τ)` whenever `n + t n + t'(O(n + t n)) = O(τ n)`.
* `Cslib.Complexity.SigmaTwoTIME_succ_pow_subset_NTIME_succ_pow`: the polynomial form, for
  `t' m ^ q = O((m + 1) ^ p)` with `q > 0`: `Σ₂TIME((n + 1) ^ a) ⊆ NTIME((n + 1) ^ b)` whenever
  `1 ≤ a ≤ b` and `a * p ≤ b * q`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [L. Fortnow, *Time-space tradeoffs for satisfiability*][Fortnow2000]
* [L. Fortnow, R. Lipton, D. van Melkebeek, A. Viglas,
  *Time-space lower bounds for satisfiability*][FortnowLiptonVanMelkebeekViglas2005]
* [R. J. Lipton, A. Viglas, *On the complexity of SAT*][LiptonViglas1999]
-/

public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM

/-- **The slowdown lemma.** If nondeterministic linear time is in deterministic time `t'`, then
`Σ₂TIME(t)` is in nondeterministic time `τ` for every `τ` with
`n + t n + t' m = O(τ n)` uniformly over `m = O(n + t n)`. The universal block of a `Σ₂TIME(t)`
verifier, read on the instance followed by the existential certificate, is a problem in
nondeterministic linear time, since the certificate pads the instance (see the module
documentation). -/
theorem SigmaTwoTIME_subset_NTIME {t t' τ : ℕ → ℕ} (ht : TimeConstructible t)
    (hN : NTIME encBits id ⊆ DTIME encBits t')
    (hτ : ∀ C, ∃ D, ∀ n m, m ≤ C * (n + t n) + C → n + t n + t' m ≤ D * τ n + D) :
    SigmaTwoTIME encBits t ⊆ NTIME encBits τ := by
  intro A hA
  obtain ⟨V, c, hV, hmem⟩ := mem_SigmaTwoTIME_iff.mp hA
  -- the universal block, as a verifier on the framed instance followed by the certificate
  have hunframe : ComputableInO (fun x : List Bool × List Bool => unframe x.1)
      (encPair encBits encBits) encBits (fun x => (encPair encBits encBits x).length)
      (fun x => (encPair encBits encBits x).length) :=
    (ComputableInO.of_linear (ComputableInDegree.of_unframe fun _ => rfl)).comp_linear
      (ComputableInO.fst encBits encBits)
  have hdrop : ComputableInO (fun x : List Bool × List Bool => dropFrame x.1)
      (encPair encBits encBits) encBits (fun x => (encPair encBits encBits x).length)
      (fun x => (encPair encBits encBits x).length) :=
    (ComputableInO.of_linear (ComputableInDegree.of_dropFrame fun _ => rfl)).comp_linear
      (ComputableInO.fst encBits encBits)
  have htriple := (hunframe.prod (hdrop.prod (ComputableInO.snd encBits encBits))).mono
    (T' := fun x => (encPair encBits encBits x).length)
    (S' := fun x => (encPair encBits encBits x).length) 3
    (fun _ => by omega) fun _ => by omega
  have hW := (hV.comp_linear htriple).not'
  have hℓ : ComputableInO (fun z : List Bool => (dropFrame z).length) encBits encUnary
      (fun z => z.length) fun z => z.length :=
    ComputableInO.lengthUnary.comp_linear
      (ComputableInO.of_linear (ComputableInDegree.of_dropFrame fun _ => rfl))
  have hB := setOf_exists_mem_NTIME (t := id) (C := 5) hℓ hW fun z v hv => by
    have := length_dropFrame_le z
    enc_len [id_eq] at hv ⊢
  -- the universal block is decided deterministically within `t'`
  have hdec := computableInO_indicator_of_mem_DTIME (hN hB)
  have hV₂ := (hdec.of_encIn_eq (encD := encPair encBits encBits)
    (fun x : List Bool × List Bool => frame x.1 ++ x.2) fun _ => rfl).not'
  -- the certificate length, from the time-constructibility of `t`
  have hL : ComputableInO (fun y : List Bool => c * 2 ^ Nat.size (t y.length)) encBits encUnary
      (fun y => t y.length) fun y => t y.length :=
    (ht.computableInO_unaryClock c).of_enc_eq fun _ => rfl
  obtain ⟨D, hD⟩ := hτ (2 * c + 3)
  have hbound (n : ℕ) : c * t n + c ≤ c * 2 ^ Nat.size (t n) ∧
      c * 2 ^ Nat.size (t n) ≤ 2 * c * t n + c := by
    have h₁ := Nat.lt_size_self (t n)
    have h₂ := Nat.two_pow_size_le (t n)
    constructor
    · have := Nat.mul_le_mul_left c (Nat.succ_le_of_lt h₁)
      rw [Nat.mul_succ] at this
      exact this
    · have := Nat.mul_le_mul_left c h₂
      rw [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, Nat.mul_comm c 2] at this
      exact this
  have hN₂ := setOf_exists_mem_NTIME (t := τ) (C := D) hL hV₂ fun y u hu => by
    obtain ⟨-, hup⟩ := hbound y.length
    have hlen : (frame y ++ u).length ≤ (2 * c + 3) * (y.length + t y.length) + (2 * c + 3) := by
      rw [List.length_append, length_frame, hu]
      nlinarith
    have := hD y.length _ hlen
    simp only [Function.comp_apply, encBits_apply]
    omega
  convert hN₂ using 1
  refine Set.ext fun y => ?_
  obtain ⟨hlow, -⟩ := hbound y.length
  rw [hmem y _ hlow]
  refine exists_congr fun u => and_congr_right fun hu => ?_
  have hind (z : List Bool) {B : Set (List Bool)} : indicator B z = true ↔ z ∈ B := by
    unfold indicator
    split_ifs with h <;> simp [h]
  simp only [Function.comp_apply, Bool.not_eq_true', ← Bool.not_eq_true, hind,
    Set.mem_ofPred_eq, unframe_frame_append, dropFrame_frame_append, not_exists, not_and,
    not_not, hu]

/-- **The slowdown lemma, polynomial form.** If nondeterministic linear time is in deterministic
time `t'` with `t' m ^ q ≤ C * (m + 1) ^ p` for some `q > 0`, that is `t' m = O(m ^ (p / q))`, then
`Σ₂TIME((n + 1) ^ a) ⊆ NTIME((n + 1) ^ b)` whenever `1 ≤ a ≤ b` and `a * p ≤ b * q`. -/
theorem SigmaTwoTIME_succ_pow_subset_NTIME_succ_pow {t' : ℕ → ℕ} {p q a b C : ℕ}
    (hN : NTIME encBits id ⊆ DTIME encBits t') (ht' : ∀ m, t' m ^ q ≤ C * (m + 1) ^ p)
    (hq : 0 < q) (ha : 1 ≤ a) (hab : a ≤ b) (hpq : a * p ≤ b * q) :
    SigmaTwoTIME encBits (fun n => (n + 1) ^ a) ⊆ NTIME encBits (fun n => (n + 1) ^ b) := by
  refine SigmaTwoTIME_subset_NTIME (timeConstructible_succ_pow a) hN fun C₁ => ?_
  set M := C * (3 * C₁ + 1) ^ p + 1
  refine ⟨M + 2, fun n m hm => ?_⟩
  beta_reduce at hm ⊢
  have hX : n + 1 ≤ (n + 1) ^ a := Nat.le_self_pow (by omega) _
  have hXb : (n + 1) ^ a ≤ (n + 1) ^ b := Nat.pow_le_pow_right (Nat.succ_pos n) hab
  have hm' : m + 1 ≤ (3 * C₁ + 1) * (n + 1) ^ a := by nlinarith
  have hpow : t' m ^ q ≤ (M * (n + 1) ^ b) ^ q := by
    calc t' m ^ q ≤ C * (m + 1) ^ p := ht' m
      _ ≤ C * ((3 * C₁ + 1) * (n + 1) ^ a) ^ p := by gcongr
      _ = C * (3 * C₁ + 1) ^ p * (n + 1) ^ (a * p) := by rw [mul_pow, ← pow_mul, Nat.mul_assoc]
      _ ≤ M * (n + 1) ^ (b * q) :=
        Nat.mul_le_mul (Nat.le_succ _) (Nat.pow_le_pow_right (Nat.succ_pos n) hpq)
      _ ≤ M ^ q * (n + 1) ^ (b * q) :=
        Nat.mul_le_mul_right _ (Nat.le_self_pow (Nat.pos_iff_ne_zero.mp hq) M)
      _ = (M * (n + 1) ^ b) ^ q := by rw [mul_pow, ← pow_mul]
  have ht'm := (Nat.pow_le_pow_iff_left (Nat.pos_iff_ne_zero.mp hq)).mp hpow
  nlinarith

end Cslib.Complexity
