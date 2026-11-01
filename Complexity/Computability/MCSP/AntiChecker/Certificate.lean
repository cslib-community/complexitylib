/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.MCSP.AntiChecker
public import Complexity.Computability.MCSP.NP
import Complexity.Foundations.Data.BitString.List

/-!
# Anti-checkers counted by circuit certificates

The description-counting step of the anti-checker construction must count circuit descriptions,
including distinct descriptions of the same function. Counting their semantic image instead
does not give the witness count needed by approximate counting.

This module instantiates the ordered-tuple variant of the good-string argument in
[OliveiraPichSanthanam2019, Section 4.2, Lemma 23] with the library's fixed-length MCSP
certificates. Their validity and evaluation use the existing polynomial-time verifier in
`MCSP.NP`. The existing unary-field encoding uses
`certLength n s = s + (n + s) + s * (3 + 2 * (n + s))` bits. No compact description-length bound
or injectivity of certificate evaluation is assumed.

The resulting statements give a good input for every nonempty subfamily of valid certificates,
a geometric bound on the number surviving any prescribed number of greedy rounds, and an
anti-checker with at most `16 * (certLength n s + 1)` inputs. These are existence and counting
results. The efficient generator of [OliveiraPichSanthanam2019, Section 4.1, Lemma 17] still
requires approximate-counting circuits, search, and circuit-size accounting.

## Main definitions

* `Cslib.MCSP.validCertificates`: all valid certificates of the prescribed fixed length.
* `Cslib.MCSP.certificateFunction`: the function computed by a fixed-length certificate.

## Main results

* `Cslib.MCSP.card_validCertificates_le`: at most `2 ^ certLength n s` descriptions.
* `Cslib.MCSP.image_validCertificates`: their semantic image is exactly the functions
  computable with at most `s` gates.
* `Cslib.MCSP.filter_validCertificates_eq_filter_checkCertificateOn`: the surviving
  descriptions are exactly the witnesses accepted by the existing sample verifier.
* `Cslib.MCSP.exists_card_le_sixteen_mul_validCertificates`: a good input refutes a sixteenth
  of any nonempty subfamily, counting descriptions with their multiplicities.
* `Cslib.MCSP.exists_card_filter_validCertificates_le`: geometric shrinkage of the number of
  consistent descriptions.
* `Cslib.MCSP.exists_isAntiChecker_le_certLength`: an anti-checker with an explicit bound in
  the certificate length.

## References

* [I. C. Oliveira, J. Pich, R. Santhanam, *Hardness magnification near state-of-the-art lower
  bounds*][OliveiraPichSanthanam2019]
-/

public section

namespace Cslib.MCSP

open Finset Circuits Circuits.Boolean

/-- All valid descriptions of circuits on `n` inputs with at most `s` gates, at the fixed
certificate length. Different descriptions computing the same function remain distinct. -/
@[expose] def validCertificates (n s : ℕ) : Finset (BitString (certLength n s)) :=
  univ.filter fun w => validCertificate n s (List.ofFn w) = true

/-- Evaluation of a fixed-length MCSP certificate as a Boolean function. -/
@[expose] def certificateFunction (n s : ℕ) (w : BitString (certLength n s)) :
    BooleanFunction n :=
  fun x => evalCertificate n s (List.ofFn w) (List.ofFn x)

/-- Membership in the description family is exactly certificate validity. -/
@[simp] theorem mem_validCertificates {n s : ℕ} {w : BitString (certLength n s)} :
    w ∈ validCertificates n s ↔ validCertificate n s (List.ofFn w) = true := by
  simp [validCertificates]

/-- The number of valid descriptions is at most the number of strings of the certificate length. -/
theorem card_validCertificates_le (n s : ℕ) :
    #(validCertificates n s) ≤ 2 ^ certLength n s := by
  exact (card_le_univ _).trans_eq BitString.card

/-- Every valid fixed-length certificate computes a function with at most `s` gates. -/
theorem certificateFunction_mem_computableFunctions {n s : ℕ}
    {w : BitString (certLength n s)} (hw : w ∈ validCertificates n s) :
    certificateFunction n s w ∈ computableFunctions n s := by
  obtain ⟨C, hsize, heval⟩ := exists_circuit_of_validCertificate (mem_validCertificates.mp hw)
  exact Boolean.mem_computableFunctions.mpr
    ⟨C, Circuit.computes_single_iff.mpr heval, hsize⟩

/-- The semantic image of valid fixed-length certificates is exactly the family of functions
computable with at most `s` gates. This identifies the image, without identifying descriptions. -/
theorem image_validCertificates (n s : ℕ) :
    certificateFunction n s '' (validCertificates n s : Set (BitString (certLength n s))) =
      (computableFunctions n s : Set (BooleanFunction n)) := by
  ext f
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact certificateFunction_mem_computableFunctions hw
  · intro hf
    obtain ⟨C, hC, hsize⟩ := Boolean.mem_computableFunctions.mp hf
    obtain ⟨w, hlen, hvalid, heval⟩ := exists_validCertificate_of_circuit C hsize
    refine ⟨BitString.ofList (certLength n s) w, ?_, ?_⟩
    · exact mem_validCertificates.mpr (by rwa [BitString.ofFn_ofList hlen])
    · funext x
      rw [certificateFunction, BitString.ofFn_ofList hlen, heval x]
      exact Circuit.computes_single_iff.mp hC x

/-- Descriptions consistent with the labeled sample set are exactly the fixed-length witnesses
accepted by `checkCertificateOn`. Labels are supplied as sample data; the verifier's acceptance
test only compares its output with the supplied label. -/
theorem filter_validCertificates_eq_filter_checkCertificateOn {n s : ℕ}
    (f : BooleanFunction n) (S : Finset (BitString n)) :
    (validCertificates n s).filter (fun w => ∀ x ∈ S, certificateFunction n s w x = f x) =
      (univ : Finset (BitString (certLength n s))).filter (fun w =>
        checkCertificateOn (S.toList.map fun x => (x, f x))
          (fun p => List.ofFn p.1) (fun p out => out == p.2) n s (List.ofFn w) = true) := by
  ext w
  rw [Finset.mem_filter, mem_validCertificates, Finset.mem_filter]
  simp [checkCertificateOn, List.all_eq_true, certificateFunction]

private theorem certificate_strictMajority_ne {n s m : ℕ} {f : BooleanFunction n}
    (hf : m * s + complexity interpretation (single (strictMajority m)) <
      complexity interpretation (single f))
    (w : Fin m → BitString (certLength n s)) (hw : ∀ i, w i ∈ validCertificates n s) :
    (fun x => strictMajority m fun i => certificateFunction n s (w i) x) ≠ f := by
  intro heq
  have hle := complexity_strictMajority_le (fun i => certificateFunction n s (w i))
  rw [heq] at hle
  have hsum : ∑ i, complexity interpretation (single (certificateFunction n s (w i))) ≤
      ∑ _i : Fin m, s :=
    sum_le_sum fun i _ => mem_computableFunctions_iff_complexity_le.mp
      (certificateFunction_mem_computableFunctions (hw i))
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  omega

/-- The good-string bound for every nonempty subfamily of valid circuit descriptions. The
refuted fraction is measured before quotienting descriptions by the function they compute. -/
theorem exists_card_le_sixteen_mul_validCertificates {n s m : ℕ}
    (hm : 0 < m) (hnm : n ≤ m) {f : BooleanFunction n}
    (hf : m * s + complexity interpretation (single (strictMajority m)) <
      complexity interpretation (single f))
    {G : Finset (BitString (certLength n s))} (hG : G.Nonempty)
    (hsub : G ⊆ validCertificates n s) :
    ∃ x, #G ≤ 16 * #{w ∈ G | certificateFunction n s w x ≠ f x} := by
  apply exists_card_le_sixteen_mul_eval (certificateFunction n s) hm
    (by rw [BitString.card]; exact Nat.pow_le_pow_right two_pos hnm) hG
  exact fun w hw => certificate_strictMajority_ne hf w (fun i => hsub (hw i))

/-- After `k` good-input choices, at most a `(15 / 16) ^ k` fraction of valid circuit
descriptions survives. This retains the exact initial description count. -/
theorem exists_card_filter_validCertificates_le {n s m : ℕ}
    (hm : 0 < m) (hnm : n ≤ m) {f : BooleanFunction n}
    (hf : m * s + complexity interpretation (single (strictMajority m)) <
      complexity interpretation (single f)) (k : ℕ) :
    ∃ S : Finset (BitString n), #S ≤ k ∧
      16 ^ k * #{w ∈ validCertificates n s | ∀ x ∈ S, certificateFunction n s w x = f x} ≤
        15 ^ k * #(validCertificates n s) := by
  obtain ⟨S, hS, hcount⟩ := exists_card_filter_le_eval (certificateFunction n s) hm
    (by rw [BitString.card]; exact Nat.pow_le_pow_right two_pos hnm)
    (validCertificates n s) (certificate_strictMajority_ne hf) k
  refine ⟨S, hS, ?_⟩
  convert hcount using 3
  ext w
  simp only [Finset.mem_filter]

/-- Small anti-checkers against all size-`s` circuits, with a bound in the fixed description
length. This does not give an efficient algorithm for finding the anti-checker. -/
theorem exists_isAntiChecker_le_certLength {n s m : ℕ}
    (hm : 0 < m) (hnm : n ≤ m) {f : BooleanFunction n}
    (hf : m * s + complexity interpretation (single (strictMajority m)) <
      complexity interpretation (single f)) :
    ∃ S : Finset (BitString n), #S ≤ 16 * (certLength n s + 1) ∧
      IsAntiChecker (computableFunctions n s) f S := by
  have hb : #(validCertificates n s) < 2 ^ (certLength n s + 1) :=
    (card_validCertificates_le n s).trans_lt
      (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))
  obtain ⟨S, hS, hanti⟩ := exists_isAntiChecker_image (certificateFunction n s) hm
    (by rw [BitString.card]; exact Nat.pow_le_pow_right two_pos hnm)
    (validCertificates n s) (certificate_strictMajority_ne hf) hb
  rw [image_validCertificates] at hanti
  exact ⟨S, hS, hanti⟩

end Cslib.MCSP
