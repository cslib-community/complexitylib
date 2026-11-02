/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.CountingSimulation.TruncatedEntry
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.TruncatedPolynomialEntries

/-!
# Polynomial truncation on bounded-degree networks

For a fixed polynomial-time entry procedure, bounded-degree rows-first networks with linearly
many vertices admit the enlarged truncation bounds at every size at least two. Direct summation
handles the finitely many sizes where the fixed degree exceeds the schedule's degree bound.

## Main definitions

* `truncBoundedDegreeCertificate`: a native truncated contraction, correct on every input.

## Main results

* `truncBoundedDegreeCertificate_bound`: time `poly(L) 2 ^ O(s / √⌊log₂ s⌋)` and polynomial
  space, for precision `O(s log s)` and every fixed polynomial truncation order.
-/

public section

namespace Cslib.Complexity.CountingSimulation

open Cslib.Circuits.Frontier Cslib.GenericRAM Turing.MultiTapeTM

variable {T : Type} {encT : T ↪ List Bool} {entry : T → List Bool → List ℕ}

/-- The fixed finite range in which direct contraction handles a possibly large degree. -/
@[expose] def truncSmallSize (k : ℕ) : ℕ × ℕ × ℕ × DescribedNetwork T → Bool
  | (_, _, _, G) => decide (G.numEdges < (k + 1) ^ 10 + 2)

theorem truncSmallSize_polyTime (k : ℕ) :
    ComputableInPolyTime (truncSmallSize (T := T) k) (encTrunc encT) encBool := by
  have hnet : ComputableInPolyTime (fun x : ℕ × ℕ × ℕ × DescribedNetwork T => x.2.2.2)
      (encTrunc encT) (DescribedNetwork.encDescribed encT) :=
    (ComputableInPolyTime.snd _ _).comp ((ComputableInPolyTime.snd _ _).comp
      (ComputableInPolyTime.snd _ _))
  exact ComputableInPolyTime.unary_lt.comp
    ((DescribedNetwork.numEdges_polyTime.comp hnet).prod
      (ComputableInPolyTime.const ((k + 1) ^ 10 + 2)))

/-- A native truncated contraction for bounded-degree applications. Both branches compute the
same contraction on every input; the degree hypothesis is used only for the resource bound. -/
@[expose] noncomputable def truncBoundedDegreeCertificate
    (ce : NativeCertificate (fun q : T × List Bool => entry q.1 q.2) (encPair encT encBits)
      (encList encNat)) (k : ℕ) :
    NativeCertificate
      (fun ((P, ℓ, _, G) : ℕ × ℕ × ℕ × DescribedNetwork T) => G.truncContraction entry P ℓ)
      (encTrunc encT) (encList encNat) :=
  (NativeCertificate.branch (NativeCertificate.ofPolyTime (truncSmallSize_polyTime k))
    (truncDirectCertificate entry ce) (truncEntryContractionAlgorithm ce).certificate).congr
      fun _ => by split <;> rfl

/-- Fixed-degree networks with polynomial-time entries satisfy the enlarged truncation bound.
The degree, density and polynomial parameters are fixed before the instance. -/
theorem truncBoundedDegreeCertificate_bound
    (ce : NativeCertificate (fun q : T × List Bool => entry q.1 q.2) (encPair encT encBits)
      (encList encNat)) (hce : ce.IsPolynomial) (k C D d : ℕ) :
    ∃ K : ℕ, ∀ (P ℓ r : ℕ) (G : DescribedNetwork T), 2 ≤ G.numEdges →
      G.IsRowsFirstBipartite r → G.vertices.length ≤ C * G.numEdges →
      (∀ v ∈ G.vertices, v.1.length ≤ k) →
      1 ≤ P → P ≤ D * G.numEdges * (Nat.log 2 G.numEdges + 1) →
      1 ≤ ℓ → ℓ ≤ D * (G.numEdges + 1) ^ d →
      (truncBoundedDegreeCertificate ce k).time (P, ℓ, r, G) ≤
          K * ((encTrunc encT (P, ℓ, r, G)).length + 1) ^ K *
            2 ^ (K * G.numEdges / Nat.sqrt (Nat.log 2 G.numEdges)) ∧
        (truncBoundedDegreeCertificate ce k).space (P, ℓ, r, G) ≤
          K * ((encTrunc encT (P, ℓ, r, G)).length + 1) ^ K := by
  obtain ⟨C₀, hC₀⟩ := EntryContraction.exists_entryAdmissible_of_isPolynomial hce
  obtain ⟨KT, hKT⟩ := (truncEntryContractionAlgorithm ce).bound_polynomial (C + C₀ + 1) D d
  obtain ⟨KD, hKD⟩ := truncDirectCertificate_le_of_isPolynomial ce hce
  obtain ⟨pg, hpg, -, hgle⟩ := exists_mono_poly_cert (truncSmallSize_polyTime (encT := encT) k)
  let M := (k + 1) ^ 10 + 2
  let F : ℕ → ℕ := fun n => pg n + KT * (n + 1) ^ KT + KD * 2 ^ M * (n + 1) ^ KD
  have hFp : PolyBounded id F :=
    ((PolyBounded.of_polynomiallyBounded id hpg).add
      ((PolyBounded.const KT).mul ((PolyBounded.self.add (PolyBounded.const 1)).pow KT))).add
      ((PolyBounded.const (KD * 2 ^ M)).mul
        ((PolyBounded.self.add (PolyBounded.const 1)).pow KD))
  obtain ⟨aF, dF, hF⟩ := hFp.exists_le
  refine ⟨aF + dF + KT, fun P ℓ r G hs hrows hv hk hP hPD hℓ hℓD => ?_⟩
  set n := (encTrunc encT (P, ℓ, r, G)).length
  set X := 2 ^ (KT * G.numEdges / Nat.sqrt (Nat.log 2 G.numEdges))
  have hX : 1 ≤ X := Nat.one_le_two_pow
  have hFp' : F n ≤ (aF + dF + KT) * (n + 1) ^ (aF + dF + KT) :=
    (hF n).trans (Nat.mul_le_mul (by omega)
      (Nat.pow_le_pow_right (by omega) (by omega)))
  have hX' : X ≤ 2 ^ ((aF + dF + KT) * G.numEdges / Nat.sqrt (Nat.log 2 G.numEdges)) :=
    Nat.pow_le_pow_right (by norm_num)
      (Nat.div_le_div_right (Nat.mul_le_mul_right _ (by omega)))
  have hgt : (NativeCertificate.ofPolyTime (truncSmallSize_polyTime k)).time (P, ℓ, r, G) ≤
      pg n := (hgle _).1
  have hgs : (NativeCertificate.ofPolyTime (truncSmallSize_polyTime k)).space (P, ℓ, r, G) ≤
      pg n := (hgle _).2
  have hfast (hg : truncSmallSize k (P, ℓ, r, G) = false) :
      (truncEntryContractionAlgorithm ce).certificate.time (P, ℓ, r, G) ≤
          KT * (n + 1) ^ KT * X ∧
        (truncEntryContractionAlgorithm ce).certificate.space (P, ℓ, r, G) ≤
          KT * (n + 1) ^ KT := by
    have hM : (k + 1) ^ 10 + 2 ≤ G.numEdges := by simpa [truncSmallSize] using hg
    have hdegree : k ≤ ceilNineTenths G.numEdges := by
      apply (le_ceilNineTenths_iff (by omega)).2
      have h1 : (k - 1) ^ 10 ≤ (k + 1) ^ 10 := Nat.pow_le_pow_left (by omega) _
      have h2 : G.numEdges ≤ G.numEdges ^ 9 := by
        calc G.numEdges = G.numEdges ^ 1 := (pow_one _).symm
          _ ≤ G.numEdges ^ 9 := Nat.pow_le_pow_right (by omega) (by norm_num)
      omega
    have hA : TruncEntryAdmissible ce (C + C₀ + 1) G.numEdges (r, G) :=
      ⟨hC₀ (C + C₀ + 1) G.numEdges r G (by omega) hrows le_rfl
        (Nat.le_mul_of_pos_left _ (by omega)) (fun v hmem => (hk v hmem).trans hdegree),
        hv.trans (Nat.mul_le_mul_right _ (by omega))⟩
    exact hKT G.numEdges P ℓ r G hs hP hPD hℓ hℓD hA
  have hsmall (hg : truncSmallSize k (P, ℓ, r, G) = true) :
      (truncDirectCertificate entry ce).time (P, ℓ, r, G) ≤ KD * 2 ^ M * (n + 1) ^ KD ∧
        (truncDirectCertificate entry ce).space (P, ℓ, r, G) ≤ KD * 2 ^ M * (n + 1) ^ KD := by
    have hM : G.numEdges < M := by simpa [truncSmallSize, M] using hg
    have hpow : 2 ^ G.numEdges ≤ 2 ^ M := Nat.pow_le_pow_right (by norm_num) hM.le
    obtain ⟨hT, hS⟩ := hKD P ℓ r G
    constructor
    · calc _ ≤ KD * (n + 1) ^ KD * 2 ^ M := hT.trans (Nat.mul_le_mul_left _ hpow)
        _ = _ := by ring
    · calc _ ≤ KD * (n + 1) ^ KD := hS
        _ ≤ KD * (n + 1) ^ KD * 2 ^ M := Nat.le_mul_of_pos_right _ Nat.one_le_two_pow
        _ = _ := by ring
  have htime : (truncBoundedDegreeCertificate ce k).time (P, ℓ, r, G) ≤ F n * X := by
    simp only [truncBoundedDegreeCertificate, NativeCertificate.congr,
      NativeCertificate.branch_time]
    have hpgX : pg n ≤ pg n * X := Nat.le_mul_of_pos_right _ hX
    have hsX : KD * 2 ^ M * (n + 1) ^ KD ≤ KD * 2 ^ M * (n + 1) ^ KD * X :=
      Nat.le_mul_of_pos_right _ hX
    have hsum : F n * X = pg n * X + KT * (n + 1) ^ KT * X +
        KD * 2 ^ M * (n + 1) ^ KD * X := by simp only [F]; ring
    split
    · next hg => have := (hsmall hg).1; omega
    · next hg => have := (hfast (by simpa using hg)).1; omega
  have hspace : (truncBoundedDegreeCertificate ce k).space (P, ℓ, r, G) ≤ F n := by
    simp only [truncBoundedDegreeCertificate, NativeCertificate.congr,
      NativeCertificate.branch_space]
    dsimp only [F]
    split
    · next hg => have := (hsmall hg).2; omega
    · next hg => have := (hfast (by simpa using hg)).2; omega
  exact ⟨htime.trans (Nat.mul_le_mul hFp' hX'), hspace.trans hFp'⟩

end Cslib.Complexity.CountingSimulation
