/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.HQC.SupportSampling
public import CslibFrontier.Foundations.Data.BitString.Parity.Circulant
public import CslibFrontier.Foundations.Data.BitString.Parity.Weight
public import CslibFrontier.Probability.BitString.FixedWeight
public import CslibFrontier.Probability.BitString.Parity
import CslibFrontier.Probability.PMF.Support

/-!
# Parity-constrained quasi-cyclic syndrome distributions

The real and comparison laws are the finite distributions in [HQC2026], Definitions
2.3.6–2.3.9, pp. 12–13. A public vector represents its circulant matrix, using Mathlib's
`Matrix.circulant`. The two-block syndrome is `x + circulant h *ᵥ y`. The three-block law
uses the same third sparse vector in both syndrome components and retains only a prefix of
the second component. Here `m` is the retained length, equal to the source's `n - ℓ`.

Public blocks and the first comparison syndrome have the prescribed parities. The second
comparison component is uniform on all `m` bits. These are distributions, not hardness
assumptions: no adversary class, efficient sampler, seed expansion, or security reduction is
asserted. Zero and full weights and zero/full retained length are admitted as explicit finite
extensions; source security claims use their stated positive parameters and primitive primes.

## Main definitions

* `Cslib.Crypto.HQC.syndrome`: a systematic two-block syndrome.
* `Cslib.Crypto.HQC.SyndromeSample`: the public circulant and syndrome.
* `Cslib.Crypto.HQC.TruncatedSyndromeSample`: two public circulants and the two output blocks.
* `Cslib.Crypto.HQC.realSyndromeLaw`, `Cslib.Crypto.HQC.uniformSyndromeLaw`: the 2-QCSD-P laws.
* `Cslib.Crypto.HQC.realTruncatedSyndromeLaw`,
  `Cslib.Crypto.HQC.uniformTruncatedSyndromeLaw`: the 3-QCSD-PT laws.

## Main results

* `Cslib.Crypto.HQC.parity_syndrome`: the exact syndrome parity from its three inputs.
* `Cslib.Crypto.HQC.parity_syndrome_of_weight`: the parity forced by the two fixed weights.
* `Cslib.Crypto.HQC.eval_idealSupport_map_indicatorVector`: the source's ideal support sampler
  is the uniform fixed-weight bit-string law used below.
* `Cslib.Crypto.HQC.mem_support_realTruncatedSyndromeLaw_iff`: a sample is real exactly when
  both public parities hold and one shared third fixed-weight vector produces both components.
* `Cslib.Crypto.HQC.parity_of_mem_support_realSyndromeLaw`: every real syndrome has that parity.

## References

* [HQC specification, version 5.1][HQC2026], Definitions 2.3.6–2.3.9, pp. 12–13.
-/

public section

namespace Cslib.Crypto.HQC

open Matrix BitString Probability

/-- The source's ideal support sampler, converted to a Boolean indicator, is exactly the uniform
fixed-weight bit-string law used in the syndrome distributions. -/
theorem eval_idealSupport_map_indicatorVector {n w : ℕ} (hw : w ≤ n) :
    (ProbComp.eval (sampleSupportFrom (idealCandidate n) 0 w)).map (indicatorVector n) =
      PMF.uniformOfFinset (weightLayer n w) (weightLayer_nonempty hw) := by
  rw [eval_idealSupport (by omega)]
  simpa only [Nat.Ico_zero_eq_range] using
    Probability.PMF.uniformOfFinset_map_indicatorVector hw

/-- A systematic binary syndrome, with public block `circulant h` and two secret blocks. -/
@[expose] def syndrome {n : ℕ} (h x y : BitString n) : BitString n :=
  x + circulant h *ᵥ y

/-- The parity obtained when both secret blocks have weight `w` and the public block parity `b`.
This is the source's `w + b*w mod 2`, expressed in the Boolean ring. -/
@[expose] def syndromeParity (w : ℕ) (b : Bool) : Bool :=
  decide (w % 2 = 1) ^^ (b && decide (w % 2 = 1))

/-- Circulant multiplication forces the indicated parity relation. -/
theorem parity_syndrome {n : ℕ} [NeZero n] (h x y : BitString n) :
    parity n (syndrome h x y) = (parity n x ^^ (parity n h && parity n y)) := by
  rw [syndrome, parity, parityOn_add]
  exact congrArg (parity n x ^^ ·) (parity_circulant_mulVec h y)

/-- Fixed weights in both secret blocks determine the syndrome parity. -/
theorem parity_syndrome_of_weight {n w : ℕ} [NeZero n] (h x y : BitString n) (b : Bool)
    (hh : parity n h = b) (hx : weight x = w) (hy : weight y = w) :
    parity n (syndrome h x y) = syndromeParity w b := by
  rw [parity_syndrome, hh, parity_eq_decide_weight, parity_eq_decide_weight, hx, hy]
  rfl

/-- A sample for the two-block problem, retaining its public circulant generator. -/
structure SyndromeSample (n : ℕ) where
  /-- Generator of the public circulant matrix. -/
  publicBlock : BitString n
  /-- The syndrome of the two secret blocks. -/
  value : BitString n
  deriving DecidableEq

/-- A sample for the three-block problem, with a prefix of its second syndrome. -/
structure TruncatedSyndromeSample (n m : ℕ) where
  /-- Generator of the first public circulant. -/
  firstBlock : BitString n
  /-- Generator of the second public circulant. -/
  secondBlock : BitString n
  /-- The entire first syndrome, whose parity is public. -/
  firstValue : BitString n
  /-- The retained prefix of the second syndrome. -/
  secondValue : BitString m
  deriving DecidableEq

/-- The 2-QCSD-P real distribution: independent uniform fixed-weight secret blocks. -/
@[expose] noncomputable def realSyndromeLaw (n w : ℕ) [NeZero n] (hw : w ≤ n) (b : Bool) :
    PMF (SyndromeSample n) := do
  let h ← uniformParity n b
  let x ← PMF.uniformOfFinset (weightLayer n w) (weightLayer_nonempty hw)
  let y ← PMF.uniformOfFinset (weightLayer n w) (weightLayer_nonempty hw)
  return ⟨h, syndrome h x y⟩

/-- The 2-DQCSD-P comparison distribution retains both public parity constraints. -/
@[expose] noncomputable def uniformSyndromeLaw (n w : ℕ) [NeZero n] (b : Bool) :
    PMF (SyndromeSample n) := do
  let h ← uniformParity n b
  let value ← uniformParity n (syndromeParity w b)
  return ⟨h, value⟩

/-- The 3-QCSD-PT real law. Both syndromes use the same sampled third secret block `z`. -/
@[expose] noncomputable def realTruncatedSyndromeLaw (n m w : ℕ) [NeZero n] (hm : m ≤ n)
    (hw : w ≤ n) (b₁ b₂ : Bool) : PMF (TruncatedSyndromeSample n m) := do
  let h₁ ← uniformParity n b₁
  let h₂ ← uniformParity n b₂
  let x ← PMF.uniformOfFinset (weightLayer n w) (weightLayer_nonempty hw)
  let y ← PMF.uniformOfFinset (weightLayer n w) (weightLayer_nonempty hw)
  let z ← PMF.uniformOfFinset (weightLayer n w) (weightLayer_nonempty hw)
  return ⟨h₁, h₂, syndrome h₁ x z, syndrome h₂ y z ∘ Fin.castLEEmb hm⟩

/-- The 3-DQCSD-PT comparison law: constrain the first syndrome's parity and draw the retained
second block independently and uniformly, as in the source distribution. -/
@[expose] noncomputable def uniformTruncatedSyndromeLaw (n m w : ℕ) [NeZero n] (b₁ b₂ : Bool) :
    PMF (TruncatedSyndromeSample n m) := do
  let h₁ ← uniformParity n b₁
  let h₂ ← uniformParity n b₂
  let firstValue ← uniformParity n (syndromeParity w b₁)
  let secondValue ← PMF.uniformOfFintype (BitString m)
  return ⟨h₁, h₂, firstValue, secondValue⟩

/-- Support characterization of the three-block real law. In particular, the same witness `z`
appears in both syndrome equations; replacing it by two independent vectors changes the law. -/
theorem mem_support_realTruncatedSyndromeLaw_iff {n m w : ℕ} [NeZero n]
    (hm : m ≤ n) (hw : w ≤ n) (b₁ b₂ : Bool) (sample : TruncatedSyndromeSample n m) :
    sample ∈ (realTruncatedSyndromeLaw n m w hm hw b₁ b₂).support ↔
      parity n sample.firstBlock = b₁ ∧ parity n sample.secondBlock = b₂ ∧
        ∃ x y z : BitString n,
          weight x = w ∧ weight y = w ∧ weight z = w ∧
            sample.firstValue = syndrome sample.firstBlock x z ∧
              sample.secondValue = syndrome sample.secondBlock y z ∘ Fin.castLEEmb hm := by
  simp only [realTruncatedSyndromeLaw, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff]
  constructor
  · rintro ⟨h₁, hh₁, h₂, hh₂, x, hx, y, hy, z, hz, rfl⟩
    exact ⟨(mem_support_uniformParity b₁ h₁).mp hh₁,
      (mem_support_uniformParity b₂ h₂).mp hh₂,
      x, y, z,
      mem_weightLayer.mp ((PMF.mem_support_uniformOfFinset_iff _ x).mp hx),
      mem_weightLayer.mp ((PMF.mem_support_uniformOfFinset_iff _ y).mp hy),
      mem_weightLayer.mp ((PMF.mem_support_uniformOfFinset_iff _ z).mp hz), rfl, rfl⟩
  · rintro ⟨hh₁, hh₂, x, y, z, hx, hy, hz, hfirst, hsecond⟩
    have hsample : sample =
        ⟨sample.firstBlock, sample.secondBlock, syndrome sample.firstBlock x z,
          syndrome sample.secondBlock y z ∘ Fin.castLEEmb hm⟩ := by
      cases sample
      simp_all
    exact ⟨sample.firstBlock, (mem_support_uniformParity b₁ sample.firstBlock).mpr hh₁,
      sample.secondBlock, (mem_support_uniformParity b₂ sample.secondBlock).mpr hh₂,
      x, (PMF.mem_support_uniformOfFinset_iff _ x).mpr (mem_weightLayer.mpr hx),
      y, (PMF.mem_support_uniformOfFinset_iff _ y).mpr (mem_weightLayer.mpr hy),
      z, (PMF.mem_support_uniformOfFinset_iff _ z).mpr (mem_weightLayer.mpr hz), hsample⟩

/-- All real two-block samples satisfy both parity constraints. -/
theorem parity_of_mem_support_realSyndromeLaw {n w : ℕ} [NeZero n] (hw : w ≤ n) (b : Bool)
    {sample : SyndromeSample n} (hs : sample ∈ (realSyndromeLaw n w hw b).support) :
    parity n sample.publicBlock = b ∧ parity n sample.value = syndromeParity w b := by
  simp only [realSyndromeLaw, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hs
  obtain ⟨h, hh, x, hx, y, hy, rfl⟩ := hs
  have hh' := (mem_support_uniformParity b h).mp hh
  exact ⟨hh', parity_syndrome_of_weight h x y b hh'
    (mem_weightLayer.mp ((PMF.mem_support_uniformOfFinset_iff _ x).mp hx))
    (mem_weightLayer.mp ((PMF.mem_support_uniformOfFinset_iff _ y).mp hy))⟩

/-- The three-block law preserves both public-block parities and the first syndrome parity.
No parity is asserted for the truncated second component. -/
theorem parity_of_mem_support_realTruncatedSyndromeLaw {n m w : ℕ} [NeZero n]
    (hm : m ≤ n) (hw : w ≤ n) (b₁ b₂ : Bool) {sample : TruncatedSyndromeSample n m}
    (hs : sample ∈ (realTruncatedSyndromeLaw n m w hm hw b₁ b₂).support) :
    parity n sample.firstBlock = b₁ ∧ parity n sample.secondBlock = b₂ ∧
      parity n sample.firstValue = syndromeParity w b₁ := by
  simp only [realTruncatedSyndromeLaw, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hs
  obtain ⟨h₁, hh₁, h₂, hh₂, x, hx, y, _, z, hz, rfl⟩ := hs
  have hh₁' := (mem_support_uniformParity b₁ h₁).mp hh₁
  exact ⟨hh₁', (mem_support_uniformParity b₂ h₂).mp hh₂,
    parity_syndrome_of_weight h₁ x z b₁ hh₁'
      (mem_weightLayer.mp ((PMF.mem_support_uniformOfFinset_iff _ x).mp hx))
      (mem_weightLayer.mp ((PMF.mem_support_uniformOfFinset_iff _ z).mp hz))⟩

/-- The public parity test is deterministic on real two-block samples. This is why their
comparison distribution must also constrain the syndrome parity. -/
theorem map_parity_realSyndromeLaw {n w : ℕ} [NeZero n] (hw : w ≤ n) (b : Bool) :
    (realSyndromeLaw n w hw b).map (fun sample => parity n sample.value) =
      PMF.pure (syndromeParity w b) :=
  PMF.map_eq_pure_iff.mpr fun _ hs => (parity_of_mem_support_realSyndromeLaw hw b hs).2

/-- The comparison law preserves the same deterministic syndrome parity as the real law. -/
theorem map_parity_uniformSyndromeLaw (n w : ℕ) [NeZero n] (b : Bool) :
    (uniformSyndromeLaw n w b).map (fun sample => parity n sample.value) =
      PMF.pure (syndromeParity w b) := by
  apply PMF.map_eq_pure_iff.mpr
  intro sample hs
  simp only [uniformSyndromeLaw, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hs
  obtain ⟨h, _, value, hvalue, rfl⟩ := hs
  exact (mem_support_uniformParity (syndromeParity w b) value).mp hvalue

end Cslib.Crypto.HQC
