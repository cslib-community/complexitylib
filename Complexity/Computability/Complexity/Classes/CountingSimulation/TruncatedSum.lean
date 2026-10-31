/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.CountingSimulation.Accumulate
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.TruncatedAlgorithm
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LinearSpaceArith
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Mathlib.Algebra.BigOperators.ModEq

/-!
# Summing the truncated contractions of a computed family of networks

On each branch, the proof of Lemma D.2 of [OpenAI2026ETH] (pp. 56–57) contracts one network per
degree array by Theorem D.1 at truncation order `ℓ`. It sums the contractions in
`B = (ℤ / 2 ^ p)[V] / (V ^ ℓ)`, applies the coefficient sum `S_ℓ`, and reduces modulo `2 ^ p`.
This file is that loop, for any computed family of networks and any algorithm with the interface
of Theorem D.1 at truncation order `ℓ` (`Cslib.Circuits.Frontier.TruncatedContractionAlgorithm`).

`S_ℓ` is additive. So the loop applies it to each contraction
(`Cslib.Complexity.CountingSimulation.truncCoeffSum`) and adds the residues modulo the modulus,
one network at a time (`Cslib.Complexity.CountingSimulation.truncSum`). The streamed modular sum
`Cslib.Complexity.CountingSimulation.modSum` keeps only the index, the context and the
accumulator. If the contractions sum, coefficientwise below `V ^ ℓ` and modulo `2 ^ P`, to given
integers, the loop computes their sum modulo `2 ^ P`
(`Cslib.Complexity.CountingSimulation.truncSum_modEq`). In Lemma D.2 these integers are the
coefficients below `V ^ ℓ` of the incidence sum, whose sum is the branch count modulo `2 ^ p` by the
congruence (D.2) (#2076).

**Resources** (`Cslib.Complexity.CountingSimulation.exists_truncSum_certificate`). Suppose the
networks are built in polynomial time from the context and the index. Suppose further that, on a
context `c`, they are admissible at size `s c` with precision and truncation order between `1` and
`D s c`. Then the loop takes time `(count c + 1) K (n + 1) ^ K 2 ^ (K s / √⌊log₂ s⌋)` and space
`K (n + 1) ^ K`, for the context's encoded length `n` and a constant `K`. The constant is chosen
before the context, and the number of networks is an explicit factor.

## Main definitions

* `Cslib.Complexity.CountingSimulation.truncCoeffSum`: `S_ℓ` of a truncated contraction.
* `Cslib.Complexity.CountingSimulation.truncSum`: the sum of the `truncCoeffSum` of the networks,
  modulo the modulus.

## Main results

* `Cslib.Complexity.CountingSimulation.truncSum_eq`: the loop is the sum modulo the modulus.
* `Cslib.Complexity.CountingSimulation.truncSum_modEq`: the congruence to the sum of the summed
  coefficients.
* `Cslib.Complexity.CountingSimulation.exists_truncSum_certificate`: time and space.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Theorem D.1 (p. 53) and the
  proof of Lemma D.2 (pp. 54–57).
-/

public section

namespace Cslib.Complexity.CountingSimulation

open Cslib.Circuits.Frontier Cslib.GenericRAM Turing.MultiTapeTM Finset

variable {C T : Type} {encC : C ↪ List Bool} {encT : T ↪ List Bool}
  {entry : T → List Bool → List ℕ}

/-- **The coefficient sum `S_ℓ` of a truncated contraction**: the sum of the `ℓ` coefficients of
the contraction of `G` in `(ℤ / 2 ^ P)[V] / (V ^ ℓ)`, for the input `(P, ℓ, r, G)`. -/
@[expose] noncomputable def truncCoeffSum (entry : T → List Bool → List ℕ)
    (x : ℕ × ℕ × ℕ × DescribedNetwork T) : ℕ :=
  (x.2.2.2.truncContraction entry x.1 x.2.1).sum

private theorem sum_map_range {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp only [List.range_zero, List.map_nil, List.sum_nil, range_zero, sum_empty]
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]

/-- `S_ℓ` of a truncated contraction is the sum of the coefficients below `V ^ ℓ` of the
contraction over `ℕ[V]`, each reduced modulo `2 ^ P`. -/
theorem truncCoeffSum_eq (entry : T → List Bool → List ℕ) (P ℓ r : ℕ) (G : DescribedNetwork T) :
    truncCoeffSum entry (P, ℓ, r, G) =
      ∑ j ∈ range ℓ, (G.polyContraction entry).coeff j % 2 ^ P := by
  rw [truncCoeffSum, DescribedNetwork.truncContraction, sum_map_range]

/-- **The loop of Lemma D.2 on one branch**: the sum, modulo `modulus c`, of the coefficient sums
of the truncated contractions of the networks `build (c, i)` for `i < count c`, streamed one
network at a time. -/
@[expose] noncomputable def truncSum (entry : T → List Bool → List ℕ)
    (build : C × ℕ → ℕ × ℕ × ℕ × DescribedNetwork T) (modulus count : C → ℕ) (c : C) : ℕ :=
  modSum (fun q => truncCoeffSum entry (build q) % modulus q.1) modulus count c

variable {build : C × ℕ → ℕ × ℕ × ℕ × DescribedNetwork T} {modulus count : C → ℕ}

/-- **The loop is the sum modulo the modulus.** -/
theorem truncSum_eq (c : C) :
    truncSum entry build modulus count c =
      (∑ i ∈ range (count c), truncCoeffSum entry (build (c, i))) % modulus c := by
  rw [truncSum, modSum_eq_sum_mod]
  change (∑ i ∈ range (count c), truncCoeffSum entry (build (c, i)) % modulus c) % modulus c = _
  exact (Finset.sum_nat_mod _ _ _).symm

/-- **The congruence of the loop.** Suppose the networks of context `c` have precision `P` and
truncation order `ℓ`, the modulus is `2 ^ P`, and for every `j < ℓ` the `V ^ j` coefficients of
their contractions over `ℕ[V]` sum to `q j` modulo `2 ^ P`. Then the loop is the sum of the
`q j` modulo `2 ^ P`. -/
theorem truncSum_modEq {c : C} {P ℓ : ℕ} (hmod : modulus c = 2 ^ P)
    (hbuild : ∀ i < count c, (build (c, i)).1 = P ∧ (build (c, i)).2.1 = ℓ) (q : ℕ → ℤ)
    (hq : ∀ j < ℓ, ((∑ i ∈ range (count c),
      ((build (c, i)).2.2.2.polyContraction entry).coeff j : ℕ) : ℤ) ≡ q j [ZMOD 2 ^ P]) :
    (truncSum entry build modulus count c : ℤ) ≡ ∑ j ∈ range ℓ, q j [ZMOD 2 ^ P] := by
  have hterm : ∀ i ∈ range (count c), truncCoeffSum entry (build (c, i)) =
      ∑ j ∈ range ℓ, ((build (c, i)).2.2.2.polyContraction entry).coeff j % 2 ^ P := by
    intro i hi
    obtain ⟨h1, h2⟩ := hbuild i (mem_range.mp hi)
    rw [← truncCoeffSum_eq entry P ℓ (build (c, i)).2.2.1, ← h1, ← h2]
  rw [truncSum_eq, hmod, sum_congr rfl hterm, sum_comm]
  push_cast
  refine (Int.mod_modEq _ _).trans ((Int.ModEq.sum fun j _ =>
    Int.ModEq.sum fun i _ => Int.mod_modEq _ _).trans ?_)
  refine Int.ModEq.sum fun j hj => ?_
  have h := hq j (mem_range.mp hj)
  push_cast at h
  exact h

/-! ### Resources -/

/-- A polynomial bound composed with a polynomially bounded size. -/
private theorem polyBounded_comp_poly {size u : C → ℕ} {p : ℕ → ℕ}
    (hp : Cslib.PolynomiallyBounded p) (hu : PolyBounded size u) :
    PolyBounded size fun c => p (u c) :=
  (PolyBounded.of_polynomiallyBounded id hp).comp hu

private theorem sum_polyTime : ComputableInPolyTime List.sum (encList encNat) encNat := by
  fun_prop

private theorem mod_polyTime :
    ComputableInPolyTime (fun p : ℕ × ℕ => p.1 % p.2) (encPair encNat encNat) encNat := by
  fun_prop

private theorem modulusFst_polyTime (hmodulus : ComputableInPolyTime modulus encC encNat) :
    ComputableInPolyTime (fun q : C × ℕ => modulus q.1) (encPair encC encNat) encNat :=
  hmodulus.comp (ComputableInPolyTime.fst _ _)

/-- The native certificate of the terms: build the network, contract it with `cA`, add its
coefficients and reduce modulo the modulus. -/
private noncomputable def termCertificate
    (cA : NativeCertificate
      (fun x : ℕ × ℕ × ℕ × DescribedNetwork T => x.2.2.2.truncContraction entry x.1 x.2.1)
      (encTrunc encT) (encList encNat))
    (hbuild : ComputableInPolyTime build (encPair encC encNat) (encTrunc encT))
    (hmodulus : ComputableInPolyTime modulus encC encNat) :
    NativeCertificate (fun q : C × ℕ => truncCoeffSum entry (build q) % modulus q.1)
      (encPair encC encNat) encNat :=
  ((NativeCertificate.ofPolyTime mod_polyTime).comp
    (((NativeCertificate.ofPolyTime sum_polyTime).comp
        (cA.comp (NativeCertificate.ofPolyTime hbuild))).prod
      (NativeCertificate.ofPolyTime (modulusFst_polyTime hmodulus)))).congr fun _ => rfl

private theorem termCertificate_time
    (cA : NativeCertificate
      (fun x : ℕ × ℕ × ℕ × DescribedNetwork T => x.2.2.2.truncContraction entry x.1 x.2.1)
      (encTrunc encT) (encList encNat))
    (hbuild : ComputableInPolyTime build (encPair encC encNat) (encTrunc encT))
    (hmodulus : ComputableInPolyTime modulus encC encNat) (q : C × ℕ) :
    (termCertificate cA hbuild hmodulus).time q =
      (NativeCertificate.ofPolyTime hbuild).time q + cA.time (build q) +
        (NativeCertificate.ofPolyTime sum_polyTime).time
          ((build q).2.2.2.truncContraction entry (build q).1 (build q).2.1) +
        (NativeCertificate.ofPolyTime (modulusFst_polyTime hmodulus)).time q +
        (NativeCertificate.ofPolyTime mod_polyTime).time
          (truncCoeffSum entry (build q), modulus q.1) := rfl

private theorem termCertificate_space
    (cA : NativeCertificate
      (fun x : ℕ × ℕ × ℕ × DescribedNetwork T => x.2.2.2.truncContraction entry x.1 x.2.1)
      (encTrunc encT) (encList encNat))
    (hbuild : ComputableInPolyTime build (encPair encC encNat) (encTrunc encT))
    (hmodulus : ComputableInPolyTime modulus encC encNat) (q : C × ℕ) :
    (termCertificate cA hbuild hmodulus).space q =
      (NativeCertificate.ofPolyTime hbuild).space q + cA.space (build q) +
        (NativeCertificate.ofPolyTime sum_polyTime).space
          ((build q).2.2.2.truncContraction entry (build q).1 (build q).2.1) +
        (NativeCertificate.ofPolyTime (modulusFst_polyTime hmodulus)).space q +
        (NativeCertificate.ofPolyTime mod_polyTime).space
          (truncCoeffSum entry (build q), modulus q.1) := rfl

/-- **Time and space of the loop.** Let `A` be an algorithm with the interface of Theorem D.1 at
truncation order `ℓ`, with admissibility `Adm`. Let the networks, the modulus (positive) and the
number of networks be computable in polynomial time from the context. Then there is a native
certificate of the loop and a constant `K` with the following property. On every context `c` with
`2 ≤ s c` all of whose networks are admissible at size `s c` with constant `Cadm`, with precision
and truncation order between `1` and `D s c`, the loop takes time at most
`(count c + 1) K (n + 1) ^ K 2 ^ (K s c / √⌊log₂ s c⌋)` and space at most `K (n + 1) ^ K`, where
`n` is the encoded length of `c`. -/
theorem exists_truncSum_certificate {Adm : ℕ → ℕ → ℕ × DescribedNetwork T → Prop}
    (A : TruncatedContractionAlgorithm encT entry Adm)
    (hbuild : ComputableInPolyTime build (encPair encC encNat) (encTrunc encT))
    (hmodulus : ComputableInPolyTime modulus encC encNat)
    (hcount : ComputableInPolyTime count encC encNat) (hpos : ∀ c, 0 < modulus c)
    (Cadm D : ℕ) (s : C → ℕ) :
    ∃ (cs : NativeCertificate (truncSum entry build modulus count) encC encNat) (K : ℕ),
      ∀ c, 2 ≤ s c →
        (∀ i < count c, 1 ≤ (build (c, i)).1 ∧ (build (c, i)).1 ≤ D * s c ∧
          1 ≤ (build (c, i)).2.1 ∧ (build (c, i)).2.1 ≤ D * s c ∧
          Adm Cadm (s c) ((build (c, i)).2.2.1, (build (c, i)).2.2.2)) →
        cs.time c ≤ (count c + 1) * (K * ((encC c).length + 1) ^ K *
            2 ^ (K * s c / Nat.sqrt (Nat.log 2 (s c)))) ∧
          cs.space c ≤ K * ((encC c).length + 1) ^ K := by
  set cr := termCertificate (entry := entry) A.certificate hbuild hmodulus with hcr
  let R : C → ℕ := fun c => (range (count c)).sup fun i => cr.time (c, i)
  let Q : C → ℕ := fun c => (range (count c)).sup fun i => cr.space (c, i)
  obtain ⟨a, d, h⟩ := exists_computableInO_modSum hmodulus hcount cr hpos
    (fun c i _ => Nat.mod_lt _ (hpos c)) R Q
    (fun c i hi => le_sup (f := fun i => cr.time (c, i)) (mem_range.mpr hi))
    (fun c i hi => le_sup (f := fun i => cr.space (c, i)) (mem_range.mpr hi))
  refine ⟨⟨_, _, h⟩, ?_⟩
  -- The polynomial-time pieces of a term.
  obtain ⟨pB, hpB, mB, bB⟩ := exists_mono_poly_cert hbuild
  obtain ⟨pS, hpS, mS, bS⟩ := exists_mono_poly_cert sum_polyTime
  obtain ⟨pF, hpF, mF, bF⟩ := exists_mono_poly_cert (modulusFst_polyTime hmodulus)
  obtain ⟨pM, hpM, mM, bM⟩ := exists_mono_poly_cert mod_polyTime
  obtain ⟨pBL, hpBL, mBL, bBL⟩ := exists_mono_poly hbuild.polyBounded_length
  obtain ⟨pSL, hpSL, mSL, bSL⟩ := exists_mono_poly sum_polyTime.polyBounded_length
  obtain ⟨K₀, hK₀⟩ := A.bound Cadm D
  obtain ⟨cO, -, hcO⟩ := A.certificate.computes
  -- Sizes, as functions of the context.
  set L : C → ℕ := fun c => (encC c).length with hL
  set lm : C → ℕ := fun c => (encNat (modulus c)).length with hlm
  set lk : C → ℕ := fun c => (encNat (count c)).length with hlk
  have hlmp : PolyBounded L lm := hmodulus.polyBounded_length
  have hlkp : PolyBounded L lk := hcount.polyBounded_length
  -- The input of a term, the network, the contraction and its coefficient sum.
  let Lq : C → ℕ := fun c => 2 * L c + 1 + lk c
  let Lb : C → ℕ := fun c => pBL (Lq c)
  let Sp : C → ℕ := fun c => K₀ * (Lb c + 1) ^ K₀
  let Lo : C → ℕ := fun c => cO * (Sp c + 1)
  let Lp : C → ℕ := fun c => 2 * pSL (Lo c) + 1 + lm c
  let U : C → ℕ := fun c => pB (Lq c) + pS (Lo c) + pF (Lq c) + pM (Lp c) + Sp c
  have hLq : PolyBounded L Lq :=
    (((PolyBounded.const 2).mul PolyBounded.self).add (PolyBounded.const 1)).add hlkp
  have hLb : PolyBounded L Lb := polyBounded_comp_poly hpBL hLq
  have hSp : PolyBounded L Sp :=
    (PolyBounded.const K₀).mul ((hLb.add (PolyBounded.const 1)).pow K₀)
  have hLo : PolyBounded L Lo := (PolyBounded.const cO).mul (hSp.add (PolyBounded.const 1))
  have hLp : PolyBounded L Lp :=
    (((PolyBounded.const 2).mul (polyBounded_comp_poly hpSL hLo)).add
      (PolyBounded.const 1)).add hlmp
  have hU : PolyBounded L U :=
    ((((polyBounded_comp_poly hpB hLq).add (polyBounded_comp_poly hpS hLo)).add
      (polyBounded_comp_poly hpF hLq)).add (polyBounded_comp_poly hpM hLp)).add hSp
  let W : C → ℕ := fun c => a * (L c + 1) ^ d + U c
  have hW : PolyBounded L W :=
    ((PolyBounded.const a).mul ((PolyBounded.self.add (PolyBounded.const 1)).pow d)).add hU
  obtain ⟨a', d', hWad⟩ := hW.exists_le
  refine ⟨a' + d' + K₀, fun c hs hgood => ?_⟩
  set E := 2 ^ (K₀ * s c / Nat.sqrt (Nat.log 2 (s c))) with hE
  have hE1 : 1 ≤ E := Nat.one_le_two_pow
  -- A term at a summed index costs at most `U c` plus the contraction.
  have hterm : ∀ i < count c, cr.time (c, i) ≤ U c * E ∧ cr.space (c, i) ≤ U c := by
    intro i hi
    obtain ⟨hP1, hPD, hℓ1, hℓD, hadm⟩ := hgood i hi
    have hq : (encPair encC encNat (c, i)).length ≤ Lq c := by
      rw [length_encPair]
      have : (encNat i).length ≤ lk c := length_encNat_mono (le_of_lt hi)
      simp only [Lq, L]
      omega
    have hxlen : (encTrunc encT (build (c, i))).length ≤ Lb c := (bBL (c, i)).trans (mBL hq)
    obtain ⟨hAt, hAs⟩ := hK₀ (s c) (build (c, i)).1 (build (c, i)).2.1 (build (c, i)).2.2.1
      (build (c, i)).2.2.2 hs hP1 hPD hℓ1 hℓD hadm
    have hpow : (encTrunc encT (build (c, i))).length + 1 ≤ Lb c + 1 := by omega
    have hAs' : A.certificate.space (build (c, i)) ≤ Sp c :=
      hAs.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpow _))
    have hAt' : A.certificate.time (build (c, i)) ≤ Sp c * E :=
      hAt.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpow _)))
    have hout : (encList encNat ((build (c, i)).2.2.2.truncContraction entry (build (c, i)).1
        (build (c, i)).2.1)).length ≤ Lo c :=
      (hcO (build (c, i))).trans (Nat.mul_le_mul_left _ (by omega))
    have hsumlen : (encNat (truncCoeffSum entry (build (c, i)))).length ≤ pSL (Lo c) :=
      (bSL _).trans (mSL hout)
    have hpair : (encPair encNat encNat (truncCoeffSum entry (build (c, i)), modulus c)).length ≤
        Lp c := by
      rw [length_encPair]
      simp only [Lp, lm]
      omega
    have h1 := (bB (c, i)).1.trans (mB hq)
    have h1' := (bB (c, i)).2.trans (mB hq)
    have h2 := (bS _).1.trans (mS hout)
    have h2' := (bS _).2.trans (mS hout)
    have h3 := (bF (c, i)).1.trans (mF hq)
    have h3' := (bF (c, i)).2.trans (mF hq)
    have h4 := (bM (truncCoeffSum entry (build (c, i)), modulus c)).1.trans (mM hpair)
    have h4' := (bM (truncCoeffSum entry (build (c, i)), modulus c)).2.trans (mM hpair)
    rw [hcr, termCertificate_time, termCertificate_space]
    dsimp only
    refine ⟨?_, ?_⟩
    · have hle : pB (Lq c) + pS (Lo c) + pF (Lq c) + pM (Lp c) ≤
          (pB (Lq c) + pS (Lo c) + pF (Lq c) + pM (Lp c)) * E := Nat.le_mul_of_pos_right _ hE1
      have hUE : U c * E = (pB (Lq c) + pS (Lo c) + pF (Lq c) + pM (Lp c)) * E + Sp c * E := by
        simp only [U]
        ring
      rw [hUE]
      omega
    · simp only [U]
      omega
  -- The trajectory maxima.
  have hR : R c ≤ U c * E := Finset.sup_le fun i hi => (hterm i (mem_range.mp hi)).1
  have hQ : Q c ≤ U c := Finset.sup_le fun i hi => (hterm i (mem_range.mp hi)).2
  have hWc := hWad c
  have hK : a' * (L c + 1) ^ d' ≤ (a' + d' + K₀) * (L c + 1) ^ (a' + d' + K₀) :=
    Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
  have hEK : E ≤ 2 ^ ((a' + d' + K₀) * s c / Nat.sqrt (Nat.log 2 (s c))) :=
    Nat.pow_le_pow_right (by omega)
      (Nat.div_le_div_right (Nat.mul_le_mul_right _ (by omega)))
  refine ⟨?_, ?_⟩
  · change (count c + 1) * (a * (L c + 1) ^ d + R c) ≤ _
    refine Nat.mul_le_mul_left _ ?_
    calc a * (L c + 1) ^ d + R c ≤ W c * E := by
          have : a * (L c + 1) ^ d ≤ a * (L c + 1) ^ d * E := Nat.le_mul_of_pos_right _ hE1
          simp only [W, add_mul]
          omega
      _ ≤ ((a' + d' + K₀) * (L c + 1) ^ (a' + d' + K₀)) *
          2 ^ ((a' + d' + K₀) * s c / Nat.sqrt (Nat.log 2 (s c))) :=
        Nat.mul_le_mul (hWc.trans hK) hEK
  · change a * (L c + 1) ^ d + Q c ≤ _
    have : a * (L c + 1) ^ d + Q c ≤ W c := by simp only [W]; omega
    exact this.trans (hWc.trans hK)

end Cslib.Complexity.CountingSimulation
