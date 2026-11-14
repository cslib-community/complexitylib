/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.KickTree.SmallUniversePerm
public import CslibFrontier.Probability.KWiseIndependent.DoubleTabulation
public import CslibFrontier.Probability.KWiseIndependent.ReducedLimbs
import CslibFrontier.Foundations.Data.Nat.Log
import CslibFrontier.Foundations.Data.Nat.Power
import CslibFrontier.Probability.KWiseIndependent.Coupling
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.EventBind
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.StatisticalDistance.Coupling
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Case A unbalanced Feistel transfer and concrete Double-Tabulation round-seed parameters

This module formalizes the Case A 2-round unbalanced Feistel bijection (`caseAEquiv`), its abstract
`(1 - δ)`-w.h.p. `κ`-wise distributional transfer (`dist_caseA_restrict_le`), and the concrete
Double-Tabulation + `oddMulModWord` round-function parameter schedule (`quotientPermInd`,
`quotientPermThreshold`, `reduceBits`, `reducedDoubleTab`) together with its failure-event and
Naor–Reingold contraction bounds for `CslibFrontier.DataStructure.Dictionary.KickTree.QuotientPerm`.

## Main definitions

* `Cslib.DataStructure.Dictionary.KickTree.caseAGap`,
  `Cslib.DataStructure.Dictionary.KickTree.CaseARounds`,
  `Cslib.DataStructure.Dictionary.KickTree.caseAEquiv`,
  `Cslib.DataStructure.Dictionary.KickTree.caseAQuot`,
  `Cslib.DataStructure.Dictionary.KickTree.splitBucketAuxEquiv`,
  `Cslib.DataStructure.Dictionary.KickTree.caseABucketAux`: Case A 2-round unbalanced Feistel
  bijection and combined `(bucket, aux)` evaluator.
* `Cslib.DataStructure.Dictionary.KickTree.nrRounds`,
  `Cslib.DataStructure.Dictionary.KickTree.quotientPermInd`,
  `Cslib.DataStructure.Dictionary.KickTree.quotientPermRedBits`,
  `Cslib.DataStructure.Dictionary.KickTree.quotientPermCharBits`,
  `Cslib.DataStructure.Dictionary.KickTree.quotientPermChars`,
  `Cslib.DataStructure.Dictionary.KickTree.quotientPermRep`,
  `Cslib.DataStructure.Dictionary.KickTree.quotientPermInter`,
  `Cslib.DataStructure.Dictionary.KickTree.quotientPermThreshold`,
  `Cslib.DataStructure.Dictionary.KickTree.reduceBits`,
  `Cslib.DataStructure.Dictionary.KickTree.reducedDoubleTab`,
  `Cslib.DataStructure.Dictionary.KickTree.QuotientPermNRSeed`: concrete round-function parameter
  schedule and reduced double-tabulation evaluator.

## Main results

* `Cslib.DataStructure.Dictionary.KickTree.dens_not_injOn_caseAQuot_le`,
  `Cslib.DataStructure.Dictionary.KickTree.isKWiseIndependentHash_caseABucketAux_of_injOn`,
  `Cslib.DataStructure.Dictionary.KickTree.dist_caseA_restrict_le`: Round-1 quotient collision bound
  and abstract Case A `κ`-wise transfer.
* `Cslib.DataStructure.Dictionary.KickTree.four_le_quotientPermThreshold`,
  `Cslib.DataStructure.Dictionary.KickTree.val_reduceBits_eq_oddMulModWord`,
  `Cslib.DataStructure.Dictionary.KickTree.prob_not_isKUnique_quotientPerm_le`,
  `Cslib.DataStructure.Dictionary.KickTree.prob_not_injOn_reduceBits_le`,
  `Cslib.DataStructure.Dictionary.KickTree.nr_contraction_quotientPerm_le`,
  `Cslib.DataStructure.Dictionary.KickTree.quotientPermInd_le_self_of_threshold`,
  `Cslib.DataStructure.Dictionary.KickTree.dist_caseA_reducedDoubleTab_le`,
  `Cslib.DataStructure.Dictionary.KickTree.prob_doubleTab_bucketLoad_outside_le`: concrete failure,
  contraction, Case A transfer, and Case B shard-load bounds above `quotientPermThreshold c`.

## References

* [M. Thorup, *Simple Tabulation, Fast Expanders, Double Tabulation, and High
  Independence*][Thorup2013]
* [M. Naor and O. Reingold, *On the Construction of Pseudorandom Permutations: Luby–Rackoff
  Revisited*][NaorReingold1999]
-/

public section

namespace Cslib.DataStructure.Dictionary.KickTree

open Cslib.DataStructure.Dictionary Cslib.DataStructure.Dictionary.FeistelPerm
open Cslib.Probability Cslib.Probability.PMF Finset Fintype
open scoped BigOperators ENNReal Cslib.Probability.PMF

/-! ## Section 1: Case A 2-round unbalanced Feistel bijection and abstract transfer -/

/-- Logarithmic bit-gap threshold `(c + 3) * ⌈log₂ (max n 2)⌉` separating Case A (`m + gap ≤ a`,
2-round unbalanced Feistel) from Case B (`a < m + gap`, sharded Naor–Reingold). -/
@[expose] def caseAGap (c n : ℕ) : ℕ :=
  (c + 3) * Nat.clog 2 (max n 2)

/-- Round-function pair for the Case A 2-round unbalanced Feistel bijection on `Fin (2 ^ a)`. -/
structure CaseARounds (a m : ℕ) where
  /-- Round 1 quotient mask `Fin (2 ^ m) → Fin (2 ^ (a - m))`. -/
  g₀ : Fin (2 ^ m) → Fin (2 ^ (a - m))
  /-- Round 2 bucket mask `Fin (2 ^ (a - m)) → Fin (2 ^ m)`. -/
  g₁ : Fin (2 ^ (a - m)) → Fin (2 ^ m)

/-- Case A 2-round unbalanced Feistel bijection `Fin (2 ^ a) ≃ Fin (2 ^ m) × Fin (2 ^ (a - m))`
sending `(x_L, x_R) = bitDomainEquiv hma u` to `(x_L ^^^ g₁ (x_R ^^^ g₀ x_L), x_R ^^^ g₀ x_L)`. -/
@[expose] def caseAEquiv {a m : ℕ} (hma : m ≤ a) (r : CaseARounds a m) :
    Fin (2 ^ a) ≃ Fin (2 ^ m) × Fin (2 ^ (a - m)) :=
  (bitDomainEquiv hma).trans ((feistelRightEquiv r.g₀).trans (feistelPairEquiv r.g₁))

/-- Case A Round-1 quotient `q(u) = x_R ^^^ g₀ x_L : Fin (2 ^ (a - m))`. -/
@[expose] def caseAQuot {a m : ℕ} (hma : m ≤ a)
    (g₀ : Fin (2 ^ m) → Fin (2 ^ (a - m))) (u : Fin (2 ^ a)) : Fin (2 ^ (a - m)) :=
  (bitDomainEquiv hma u).2 ^^^ g₀ (bitDomainEquiv hma u).1

@[simp] theorem caseAEquiv_apply {a m : ℕ} (hma : m ≤ a) (r : CaseARounds a m) (u : Fin (2 ^ a)) :
    caseAEquiv hma r u =
      ((bitDomainEquiv hma u).1 ^^^ r.g₁ (caseAQuot hma r.g₀ u), caseAQuot hma r.g₀ u) :=
  rfl

@[simp] theorem caseAEquiv_symm_apply {a m : ℕ} (hma : m ≤ a) (r : CaseARounds a m)
    (p : Fin (2 ^ m) × Fin (2 ^ (a - m))) :
    (caseAEquiv hma r).symm p =
      (bitDomainEquiv hma).symm (p.1 ^^^ r.g₁ p.2, p.2 ^^^ r.g₀ (p.1 ^^^ r.g₁ p.2)) :=
  rfl


/-- Split `Fin (2 ^ (m + b_aux)) ≃ Fin (2 ^ m) × Fin (2 ^ b_aux)`. -/
@[expose] def splitBucketAuxEquiv (m b_aux : ℕ) :
    Fin (2 ^ (m + b_aux)) ≃ Fin (2 ^ m) × Fin (2 ^ b_aux) :=
  (bitDomainEquiv (Nat.le_add_right m b_aux)).trans
    (Equiv.prodCongr (Equiv.refl _) (finCongr (congrArg (2 ^ ·) (Nat.add_sub_cancel_left m b_aux))))

/-- Case A combined `(bucket, aux)` evaluation given Round-1 quotient function `g₀` and combined
Round-2 `(m + b_aux)`-bit hash `f₁₂ : Fin (2 ^ (a - m)) → Fin (2 ^ (m + b_aux))`. -/
@[expose] def caseABucketAux {a m b_aux : ℕ} (hma : m ≤ a)
    (g₀ : Fin (2 ^ m) → Fin (2 ^ (a - m)))
    (f₁₂ : Fin (2 ^ (a - m)) → Fin (2 ^ (m + b_aux)))
    (u : Fin (2 ^ a)) : Fin (2 ^ m) × Fin (2 ^ b_aux) :=
  let pair := splitBucketAuxEquiv m b_aux (f₁₂ (caseAQuot hma g₀ u))
  ((caseAEquiv hma ⟨g₀, fun q => (splitBucketAuxEquiv m b_aux (f₁₂ q)).1⟩ u).1, pair.2)

/-- Pairwise-independent Round-1 quotient collision bound in Case A (via
`FeistelPerm.dens_not_injOn_feistelHead_le`), requiring pairwise independence only on the active
left-coordinate image `S.image fun u => (bitDomainEquiv hma u).1`. -/
theorem dens_not_injOn_caseAQuot_le {ι₀ : Type*} [Fintype ι₀] [Nonempty ι₀] {a m : ℕ}
    (hma : m ≤ a) {h₀ : ι₀ → Fin (2 ^ m) → Fin (2 ^ (a - m))}
    (S : Finset (Fin (2 ^ a)))
    (hh₀ : IsPairwiseIndependentHash
      (fun s₀ (x : S.image fun u => (bitDomainEquiv hma u).1) => h₀ s₀ x.1)) :
    (dens {s₀ : ι₀ | ¬ Set.InjOn (caseAQuot hma (h₀ s₀)) (S : Set (Fin (2 ^ a)))} : ℝ) ≤
      ((#S * (#S - 1) : ℕ) : ℝ) / (2 * (2 ^ (a - m) : ℝ)) := by
  classical
  let S_L : Finset (Fin (2 ^ m)) := S.image fun u => (bitDomainEquiv hma u).1
  let toPair : {u // u ∈ S} ↪ Fin (2 ^ (a - m)) × S_L :=
    { toFun := fun ⟨u, hu⟩ =>
        ((bitDomainEquiv hma u).2, ⟨(bitDomainEquiv hma u).1, mem_image_of_mem _ hu⟩)
      inj' := fun ⟨u₁, _⟩ ⟨u₂, _⟩ h => by
        rcases Prod.mk.inj h with ⟨h2, h1⟩
        exact Subtype.ext ((bitDomainEquiv hma).injective
          (Prod.ext (congrArg Subtype.val h1) h2)) }
  let S_pair : Finset (Fin (2 ^ (a - m)) × S_L) := S.attach.map toPair
  have hSp_card : #S_pair = #S := by simp [S_pair]
  have hd := dens_not_injOn_feistelHead_le hh₀ S_pair
  have hiff (s₀ : ι₀) :
      Set.InjOn (caseAQuot hma (h₀ s₀)) (S : Set (Fin (2 ^ a))) ↔
        Set.InjOn (feistelHead (fun x : S_L => h₀ s₀ x.1)) (S_pair : Set _) := by
    constructor
    · intro h p₁ hp₁ p₂ hp₂ heq
      rcases mem_map.mp hp₁ with ⟨⟨u₁, hu₁⟩, _, rfl⟩
      rcases mem_map.mp hp₂ with ⟨⟨u₂, hu₂⟩, _, rfl⟩
      exact congrArg toPair (Subtype.ext (h hu₁ hu₂ heq))
    · intro h u₁ hu₁ u₂ hu₂ heq
      have hp₁ : toPair ⟨u₁, hu₁⟩ ∈ S_pair := mem_map.mpr ⟨⟨u₁, hu₁⟩, mem_attach _ _, rfl⟩
      have hp₂ : toPair ⟨u₂, hu₂⟩ ∈ S_pair := mem_map.mpr ⟨⟨u₂, hu₂⟩, mem_attach _ _, rfl⟩
      exact congrArg Subtype.val (toPair.injective (h hp₁ hp₂ heq))
  have hset : (univ.filter fun s₀ : ι₀ =>
      ¬ Set.InjOn (caseAQuot hma (h₀ s₀)) (S : Set (Fin (2 ^ a)))) =
      (univ.filter fun s₀ : ι₀ =>
        ¬ Set.InjOn (feistelHead (fun x : S_L => h₀ s₀ x.1)) (S_pair : Set _)) := by
    ext s₀
    simp only [mem_filter, mem_univ, true_and, hiff]
  rw [hset]
  simpa only [hSp_card] using hd

theorem isKWiseIndependentHash_caseABucketAux_of_comp {ι₁ : Type*} [Fintype ι₁]
    {a m b_aux κ : ℕ} (hma : m ≤ a) {g₀ : Fin (2 ^ m) → Fin (2 ^ (a - m))}
    {S : Finset (Fin (2 ^ a))}
    {h₁₂ : ι₁ → Fin (2 ^ (a - m)) → Fin (2 ^ (m + b_aux))}
    (hcomp : IsKWiseIndependentHash κ (fun s₁ (u : S) => h₁₂ s₁ (caseAQuot hma g₀ u.1))) :
    IsKWiseIndependentHash κ (fun s₁ (u : S) => caseABucketAux hma g₀ (h₁₂ s₁) u.1) := by
  classical
  refine ⟨fun {I} hI vals => ?_⟩
  let vals' : I → Fin (2 ^ (m + b_aux)) := fun u =>
    (splitBucketAuxEquiv m b_aux).symm
      ((bitDomainEquiv hma u.1.1).1 ^^^ (vals u).1, (vals u).2)
  have hfilt : (univ.filter fun s₁ : ι₁ =>
      I.restrict (fun u : S => caseABucketAux hma g₀ (h₁₂ s₁) u.1) = vals) =
      (univ.filter fun s₁ : ι₁ =>
        I.restrict (fun u : S => h₁₂ s₁ (caseAQuot hma g₀ u.1)) = vals') := by
    ext s₁
    simp only [mem_filter, mem_univ, true_and, funext_iff, restrict, caseABucketAux,
      caseAEquiv_apply]
    constructor
    · intro hs u
      have hi := hs u
      dsimp only [vals']
      rw [← hi]
      simp only [Prod.mk.eta, xor_cancel_left, Equiv.symm_apply_apply]
    · intro hs u
      have hi := congrArg (splitBucketAuxEquiv m b_aux) (hs u)
      dsimp only [vals'] at hi
      rw [Equiv.apply_symm_apply] at hi
      have h1 := congrArg Prod.fst hi
      have h2 := congrArg Prod.snd hi
      dsimp only at h1 h2
      refine Prod.ext ?_ h2
      dsimp only
      rw [h1, xor_cancel_left]
  rw [hfilt, hcomp.dens_filter_restrict_eq hI vals']
  simp only [Fintype.card_prod, Fintype.card_fin, pow_add]

/-- When `caseAQuot hma g₀` is injective on `S` and `h₁₂` is `κ`-wise independent on the active
quotient image `S.image (caseAQuot hma g₀)`, the induced `(bucket, aux)` family on `S` is exact
`κ`-wise independent (`IsKWiseIndependentHash κ`). -/
theorem isKWiseIndependentHash_caseABucketAux_of_injOn {ι₁ : Type*} [Fintype ι₁]
    {a m b_aux κ : ℕ} (hma : m ≤ a) {g₀ : Fin (2 ^ m) → Fin (2 ^ (a - m))}
    {S : Finset (Fin (2 ^ a))} (hinj : Set.InjOn (caseAQuot hma g₀) (S : Set (Fin (2 ^ a))))
    {h₁₂ : ι₁ → Fin (2 ^ (a - m)) → Fin (2 ^ (m + b_aux))}
    (hh₁₂ : IsKWiseIndependentHash κ (fun s₁ (q : S.image (caseAQuot hma g₀)) => h₁₂ s₁ q.1)) :
    IsKWiseIndependentHash κ (fun s₁ (u : S) => caseABucketAux hma g₀ (h₁₂ s₁) u.1) :=
  isKWiseIndependentHash_caseABucketAux_of_comp hma
    (hh₁₂.comp (e := fun u : S => ⟨caseAQuot hma g₀ u.1, mem_image_of_mem _ u.2⟩)
      fun u₁ u₂ h => Subtype.ext (hinj u₁.2 u₂.2 (congrArg Subtype.val h)))

/-- **Abstract Case A distributional transfer**: over a three-stage seed `(τ, s₀, s₁)` where
`τ ∈ GoodTop` (failure probability `≤ δ_top`) makes `h₀ τ` pairwise independent on the active
left-coordinate image of `S` and `h₁₂ τ` within `δ₁` of uniform whenever `caseAQuot hma (h₀ τ s₀)`
is injective on `S`, the restriction of `caseABucketAux` to `T` is within statistical distance
`δ_top + (#S * (#S - 1)) / (2 * 2 ^ (a - m)) + δ₁` of uniform. -/
theorem dist_caseA_restrict_le {Top ι₀ ι₁ : Type*}
    [Fintype Top] [Nonempty Top] [Fintype ι₀] [Nonempty ι₀] [Fintype ι₁] [Nonempty ι₁]
    {a m b_aux : ℕ} (hma : m ≤ a)
    (h₀ : Top → ι₀ → Fin (2 ^ m) → Fin (2 ^ (a - m)))
    (h₁₂ : Top → ι₁ → Fin (2 ^ (a - m)) → Fin (2 ^ (m + b_aux)))
    (S T : Finset (Fin (2 ^ a)))
    (GoodTop : Set Top) {δ_top δ₁ : ℝ} (hδ₁ : 0 ≤ δ₁)
    (hδ_top : ((PMF.uniformOfFintype Top).toOuterMeasure GoodTopᶜ).toReal ≤ δ_top)
    (hgood₀ : ∀ τ ∈ GoodTop, IsPairwiseIndependentHash
      (fun s₀ (x : S.image fun u => (bitDomainEquiv hma u).1) => h₀ τ s₀ x.1))
    (hgood₁₂ : ∀ τ ∈ GoodTop, ∀ s₀ : ι₀,
      Set.InjOn (caseAQuot hma (h₀ τ s₀)) (S : Set (Fin (2 ^ a))) →
      dist ((PMF.uniformOfFintype ι₁).map fun s₁ (u : T) =>
          caseABucketAux hma (h₀ τ s₀) (h₁₂ τ s₁) u.1)
        (PMF.uniformOfFintype (T → Fin (2 ^ m) × Fin (2 ^ b_aux))) ≤ δ₁) :
    dist (((PMF.uniformOfFintype Top).bind fun τ =>
        (PMF.uniformOfFintype ι₀).bind fun s₀ =>
          (PMF.uniformOfFintype ι₁).map fun s₁ (u : T) =>
            caseABucketAux hma (h₀ τ s₀) (h₁₂ τ s₁) u.1))
      (PMF.uniformOfFintype (T → Fin (2 ^ m) × Fin (2 ^ b_aux))) ≤
      δ_top + ((#S * (#S - 1) : ℕ) : ℝ) / (2 * (2 ^ (a - m) : ℝ)) + δ₁ := by
  classical
  let U_target := PMF.uniformOfFintype (T → Fin (2 ^ m) × Fin (2 ^ b_aux))
  have hgood_τ (τ : Top) (hτ : τ ∈ GoodTop) :
      dist ((PMF.uniformOfFintype ι₀).bind fun s₀ =>
          (PMF.uniformOfFintype ι₁).map fun s₁ (u : T) =>
            caseABucketAux hma (h₀ τ s₀) (h₁₂ τ s₁) u.1) U_target ≤
        ((#S * (#S - 1) : ℕ) : ℝ) / (2 * (2 ^ (a - m) : ℝ)) + δ₁ := by
    let Good₀ : Set ι₀ := {s₀ | Set.InjOn (caseAQuot hma (h₀ τ s₀)) (S : Set (Fin (2 ^ a)))}
    refine (dist_bind_of_good _ _ U_target Good₀ hδ₁ (hgood₁₂ τ hτ)).trans ?_
    rw [toOuterMeasure_uniformOfFintype_toReal]
    have hd := dens_not_injOn_caseAQuot_le hma S (hgood₀ τ hτ)
    rw [dens_eq_card_div_card, NNRat.cast_div, NNRat.cast_natCast, NNRat.cast_natCast] at hd
    have hfilt : univ.filter (· ∈ Good₀ᶜ) =
        univ.filter (fun s₀ : ι₀ => ¬ Set.InjOn (caseAQuot hma (h₀ τ s₀))
          (S : Set (Fin (2 ^ a)))) :=
      filter_congr fun _ _ => Iff.rfl
    rw [hfilt]
    linarith
  have hnn : 0 ≤ ((#S * (#S - 1) : ℕ) : ℝ) / (2 * (2 ^ (a - m) : ℝ)) + δ₁ :=
    add_nonneg (by positivity) hδ₁
  refine (dist_bind_of_good _ _ U_target GoodTop hnn hgood_τ).trans ?_
  linarith


/-! ## Section 2: Concrete Double-Tabulation + `oddMulModWord` parameters and failure bounds -/

/-- Number of composed 3-round Naor–Reingold blocks `18 * (c + 2) = O(c)` in Case B. -/
def nrRounds (c : ℕ) : ℕ := 18 * (c + 2)

theorem nrRounds_eq (c : ℕ) : nrRounds c = 18 * (c + 2) := by unfold nrRounds; rfl

theorem one_le_nrRounds (c : ℕ) : 1 ≤ nrRounds c := by unfold nrRounds; omega

/-- Logarithmic independence order `κ = 8 * (c + 3) * ⌈log₂ (max n 2)⌉ = Θ(c log n)`. -/
def quotientPermInd (c n : ℕ) : ℕ := 8 * (c + 3) * Nat.clog 2 (max n 2)

theorem quotientPermInd_eq (c n : ℕ) :
    quotientPermInd c n = 8 * (c + 3) * Nat.clog 2 (max n 2) := by unfold quotientPermInd; rfl

/-- Multiply-shift reduced bit-width `R = (c + 5) * ⌈log₂ (max n 4)⌉`. -/
def quotientPermRedBits (c n : ℕ) : ℕ := (c + 5) * Nat.clog 2 (max n 4)

theorem quotientPermRedBits_eq (c n : ℕ) :
    quotientPermRedBits c n = (c + 5) * Nat.clog 2 (max n 4) := by unfold quotientPermRedBits; rfl

/-- Double-tabulation character bit-width `b = max 1 (⌊log₂ n⌋ / 4)`. -/
def quotientPermCharBits (n : ℕ) : ℕ := max 1 (Nat.log 2 n / 4)

theorem quotientPermCharBits_eq (n : ℕ) :
    quotientPermCharBits n = max 1 (Nat.log 2 n / 4) := by unfold quotientPermCharBits; rfl

/-- Number of input characters `c_tab = 8 * (c + 5)` for the shared top-level table. -/
def quotientPermChars (c : ℕ) : ℕ := 8 * (c + 5)

theorem quotientPermChars_eq (c : ℕ) :
    quotientPermChars c = 8 * (c + 5) := by unfold quotientPermChars; rfl

/-- Code repetition parameter `q_tab = 4 * c + 11` in `DoubleTabulation.card_not_isKUnique_le`. -/
def quotientPermRep (c : ℕ) : ℕ := 4 * c + 11

theorem quotientPermRep_eq (c : ℕ) :
    quotientPermRep c = 4 * c + 11 := by unfold quotientPermRep; rfl

/-- Number of intermediate characters `d_tab = 2 * q_tab * c_tab`. -/
def quotientPermInter (c : ℕ) : ℕ := 2 * quotientPermRep c * quotientPermChars c

theorem quotientPermInter_eq (c : ℕ) :
    quotientPermInter c = 2 * quotientPermRep c * quotientPermChars c := by
  unfold quotientPermInter; rfl

private def quotientPermCodeExp (c : ℕ) : ℕ := (4 * quotientPermChars c + 1) * quotientPermRep c + 1

private def quotientPermMinB (c : ℕ) : ℕ := 4 * (quotientPermCodeExp c) ^ 2

/-- Finite-size capacity threshold `N₀(c) = 2 ^ (4 * quotientPermMinB c)`. -/
def quotientPermThreshold (c : ℕ) : ℕ := 2 ^ (4 * quotientPermMinB c)

private theorem one_le_quotientPermMinB (c : ℕ) : 1 ≤ quotientPermMinB c := by
  have : 0 < quotientPermCodeExp c := by unfold quotientPermCodeExp; positivity
  have : 0 < quotientPermMinB c := by unfold quotientPermMinB; positivity
  omega

/-- The concrete threshold satisfies `4 ≤ quotientPermThreshold c` for every `c`. -/
theorem four_le_quotientPermThreshold (c : ℕ) : 4 ≤ quotientPermThreshold c := by
  unfold quotientPermThreshold
  have hpos := one_le_quotientPermMinB c
  calc 4 = 2 ^ 2 := by decide
    _ ≤ 2 ^ (4 * quotientPermMinB c) := Nat.pow_le_pow_right (by decide) (by omega)

/-- Bit-width reduction `Fin (2 ^ s_in) → Fin (2 ^ min s_in R)` via `multiplyShiftReduced`. -/
@[expose] def reduceBits (s_in R : ℕ) (α : Fin (2 ^ (s_in - 1))) (x : Fin (2 ^ s_in)) :
    Fin (2 ^ min s_in R) :=
  multiplyShiftReduced (2 ^ s_in) s_in R α x

/-- Overflow-free Word-RAM equivalence via `ReducedLimbs.oddMulModWord`. -/
theorem val_reduceBits_eq_oddMulModWord {s_in R : ℕ} (hs : 0 < s_in)
    (α : Fin (2 ^ (s_in - 1))) (x : Fin (2 ^ s_in)) :
    (reduceBits s_in R α x).val = oddMulModWord s_in α.val x.val >>> (s_in - R) :=
  (oddMulModWord_shiftRight_eq_multiplyShiftReduced hs α x).symm

/-- Reduced double-tabulation round function `Fin (2 ^ s_in) → Fin (2 ^ s_out)`. -/
@[expose] def reducedDoubleTab (c n s_in s_out : ℕ) (α : Fin (2 ^ (s_in - 1)))
    (T₁ : DoubleTabTopSeed (quotientPermChars c) (quotientPermInter c) (quotientPermCharBits n))
    (T₂ : DoubleTabBotSeed (quotientPermInter c) (quotientPermCharBits n) s_out)
    (x : Fin (2 ^ s_in)) : Fin (2 ^ s_out) :=
  doubleTabHash (quotientPermChars c) (quotientPermInter c) (quotientPermCharBits n)
    (2 ^ min s_in (quotientPermRedBits c n)) s_out T₁ T₂
    (reduceBits s_in (quotientPermRedBits c n) α x)

private theorem clog_max_le_eight_mul_charBits_aux {c n : ℕ} (hn : quotientPermThreshold c ≤ n) :
    quotientPermMinB c ≤ quotientPermCharBits n ∧
      Nat.clog 2 (max n 4) ≤ 8 * quotientPermCharBits n ∧
      quotientPermRedBits c n ≤ quotientPermChars c * quotientPermCharBits n := by
  have hmin_pos := one_le_quotientPermMinB c
  have hlog : 4 * quotientPermMinB c ≤ Nat.log 2 n :=
    Nat.le_log_of_pow_le (by decide) hn
  have hb_min : quotientPermMinB c ≤ quotientPermCharBits n := by
    unfold quotientPermCharBits; omega
  have h4n : 4 ≤ n := (four_le_quotientPermThreshold c).trans hn
  have hlog_ub : Nat.log 2 n + 1 ≤ 8 * quotientPermCharBits n := by
    unfold quotientPermCharBits; omega
  have hn_pow : max n 4 ≤ 2 ^ (8 * quotientPermCharBits n) := by
    rw [max_eq_left h4n]
    exact (Nat.lt_pow_succ_log_self (by decide) n).le.trans
      (Nat.pow_le_pow_right (by decide) hlog_ub)
  have hclog : Nat.clog 2 (max n 4) ≤ 8 * quotientPermCharBits n :=
    Nat.clog_le_of_le_pow hn_pow
  refine ⟨hb_min, hclog, ?_⟩
  calc quotientPermRedBits c n = (c + 5) * Nat.clog 2 (max n 4) := rfl
    _ ≤ (c + 5) * (8 * quotientPermCharBits n) := Nat.mul_le_mul_left _ hclog
    _ = quotientPermChars c * quotientPermCharBits n := by unfold quotientPermChars; ring

theorem clog_max_le_eight_mul_charBits {c n : ℕ} (hn : quotientPermThreshold c ≤ n) :
    Nat.clog 2 (max n 4) ≤ 8 * quotientPermCharBits n ∧
      quotientPermRedBits c n ≤ quotientPermChars c * quotientPermCharBits n :=
  (clog_max_le_eight_mul_charBits_aux hn).2

private theorem threshold_charBits_bounds {c n : ℕ} (hn : quotientPermThreshold c ≤ n) :
    4 ≤ n ∧
      n ≤ 2 ^ (8 * quotientPermCharBits n) ∧
      quotientPermInd c n ≤ 8 * quotientPermChars c * quotientPermCharBits n ∧
      40 ≤ quotientPermChars c ∧
      11 ≤ quotientPermRep c ∧
      4 * (44 * quotientPermChars c) ^ 2 ≤ quotientPermCharBits n ∧
      4 * (quotientPermCodeExp c) ^ 2 ≤ quotientPermCharBits n := by
  obtain ⟨hb_min, hclog4, _⟩ := clog_max_le_eight_mul_charBits_aux hn
  have h4n : 4 ≤ n := (four_le_quotientPermThreshold c).trans hn
  have hn_pow : n ≤ 2 ^ (8 * quotientPermCharBits n) :=
    (le_max_left n 4).trans ((Nat.le_pow_clog (by decide) _).trans
      (Nat.pow_le_pow_right (by decide) hclog4))
  have hclog2 : Nat.clog 2 (max n 2) ≤ 8 * quotientPermCharBits n :=
    (Nat.clog_mono_right 2 (max_le_max_left n (by decide))).trans hclog4
  have hκ_le : quotientPermInd c n ≤ 8 * quotientPermChars c * quotientPermCharBits n := by
    calc quotientPermInd c n = 8 * (c + 3) * Nat.clog 2 (max n 2) := rfl
      _ ≤ 8 * (c + 5) * (8 * quotientPermCharBits n) := Nat.mul_le_mul (by omega) hclog2
      _ = 8 * quotientPermChars c * quotientPermCharBits n := by unfold quotientPermChars; ring
  have hc_ge : 40 ≤ quotientPermChars c := by unfold quotientPermChars; omega
  have hq_ge : 11 ≤ quotientPermRep c := by unfold quotientPermRep; omega
  have hD_ge : 44 * quotientPermChars c ≤ quotientPermCodeExp c := by
    unfold quotientPermCodeExp; nlinarith
  have hmin_eq : 4 * (quotientPermCodeExp c) ^ 2 ≤ quotientPermCharBits n := hb_min
  exact ⟨h4n, hn_pow, hκ_le, hc_ge, hq_ge,
    (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hD_ge 2)).trans hmin_eq, hmin_eq⟩

/-- Top-level `k`-uniqueness failure probability `≤ 1 / (8 * n ^ (c + 2))` above
`quotientPermThreshold c`. -/
theorem prob_not_isKUnique_quotientPerm_le {c n : ℕ} (hn : quotientPermThreshold c ≤ n) :
    ((PMF.uniformOfFintype (DoubleTabTopSeed (quotientPermChars c) (quotientPermInter c)
        (quotientPermCharBits n))).toOuterMeasure
      {T₁ | IsKUnique (quotientPermInd c n) (simpleTabTuple T₁)}ᶜ).toReal ≤
      1 / (8 * (n : ℝ) ^ (c + 2)) := by
  classical
  obtain ⟨h4n, hn_pow, hκ_le, hc_ge, hq_ge, hb_44c, hb_D⟩ := threshold_charBits_bounds hn
  have hκ_pos : 0 < quotientPermInd c n := by
    have : 1 ≤ Nat.clog 2 (max n 2) := Nat.clog_pos (by decide) (by omega)
    unfold quotientPermInd; positivity
  have hq1 : 4 * (c + 2) + 1 ≤ quotientPermRep c - 1 := by unfold quotientPermRep; omega
  have hD_eq : quotientPermCodeExp c = (4 * quotientPermChars c + 1) * quotientPermRep c + 1 := rfl
  have hd_eq : quotientPermInter c = 2 * quotientPermRep c * quotientPermChars c := rfl
  generalize quotientPermChars c = c_tab at *
  generalize quotientPermRep c = q_tab at *
  generalize quotientPermInter c = d_tab at *
  generalize quotientPermCharBits n = b_char at *
  generalize quotientPermInd c n = κ at *
  generalize quotientPermCodeExp c = D at *
  subst hd_eq
  have hb_c2 : 8 * c_tab ^ 2 ≤ b_char := by nlinarith
  have hb_d : 2 * q_tab * c_tab ≤ b_char := by nlinarith
  have hb_4c : 4 * c_tab ≤ b_char := by nlinarith
  have hcκ : c_tab * κ ≤ b_char ^ 2 := by nlinarith
  have hinner : (c_tab * κ) ^ (2 * c_tab) * (2 * q_tab * c_tab) ≤ b_char ^ (4 * c_tab + 1) := by
    calc (c_tab * κ) ^ (2 * c_tab) * (2 * q_tab * c_tab)
        ≤ (b_char ^ 2) ^ (2 * c_tab) * b_char :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hcκ _) hb_d
      _ = b_char ^ (4 * c_tab + 1) := by
          rw [← pow_mul, ← pow_succ]; exact congrArg (b_char ^ ·) (by omega)
  have h4B : 4 * doubleTabCodeBound c_tab (2 * q_tab * c_tab) q_tab κ ≤ 2 ^ b_char := by
    calc 4 * doubleTabCodeBound c_tab (2 * q_tab * c_tab) q_tab κ
        = (4 * c_tab) * ((c_tab * κ) ^ (2 * c_tab) * (2 * q_tab * c_tab)) ^ q_tab := by
          unfold doubleTabCodeBound; rw [← Nat.mul_assoc]
      _ ≤ b_char * (b_char ^ (4 * c_tab + 1)) ^ q_tab :=
          Nat.mul_le_mul hb_4c (Nat.pow_le_pow_left hinner _)
      _ = b_char ^ D := by
          rw [← pow_mul, ← pow_succ']; exact congrArg (b_char ^ ·) (by omega)
      _ ≤ 2 ^ b_char := Nat.pow_le_two_pow (by omega) hb_D
  set B := doubleTabCodeBound c_tab (2 * q_tab * c_tab) q_tab κ
  set W := 2 ^ ((q_tab - 1) * b_char)
  have hexp_W : 4 * (c + 2) * b_char + b_char ≤ (q_tab - 1) * b_char := by
    calc 4 * (c + 2) * b_char + b_char = (4 * (c + 2) + 1) * b_char := by ring
      _ ≤ (q_tab - 1) * b_char := Nat.mul_le_mul_right b_char hq1
  have hWB : 4 * 2 ^ (4 * (c + 2) * b_char) * B ≤ W := by
    calc 4 * 2 ^ (4 * (c + 2) * b_char) * B
        = 2 ^ (4 * (c + 2) * b_char) * (4 * B) := by ring
      _ ≤ 2 ^ (4 * (c + 2) * b_char) * 2 ^ b_char := Nat.mul_le_mul_left _ h4B
      _ = 2 ^ (4 * (c + 2) * b_char + b_char) := (pow_add _ _ _).symm
      _ ≤ W := Nat.pow_le_pow_right (by decide) hexp_W
  have h2B : 2 * B ≤ W := by
    have : 1 ≤ 2 ^ (4 * (c + 2) * b_char) := Nat.one_le_two_pow
    nlinarith
  have hcard := card_not_isKUnique_le (c := c_tab) (d := 2 * q_tab * c_tab) (b := b_char)
    (q := q_tab) (k := κ) (by omega) (by omega) rfl h2B
  have hnpow_c : n ^ (c + 2) ≤ (2 ^ (4 * (c + 2) * b_char)) ^ 2 := by
    calc n ^ (c + 2) ≤ (2 ^ (8 * b_char)) ^ (c + 2) := Nat.pow_le_pow_left hn_pow _
      _ = (2 ^ (4 * (c + 2) * b_char)) ^ 2 := by
          rw [← pow_mul, ← pow_mul]; exact congrArg (2 ^ ·) (by ring)
  have hB_pos : 0 < B := by
    have : 0 < 2 * q_tab * c_tab := by positivity
    unfold B doubleTabCodeBound; positivity
  set Bad := univ.filter fun T₁ : DoubleTabTopSeed c_tab (2 * q_tab * c_tab) b_char =>
    ¬ IsKUnique κ (simpleTabTuple T₁)
  have hmul_bad : 8 * n ^ (c + 2) * #Bad ≤
      Fintype.card (DoubleTabTopSeed c_tab (2 * q_tab * c_tab) b_char) := by
    have hsq : (2 * B ^ 2) * (8 * n ^ (c + 2)) ≤ W ^ 2 := by
      calc (2 * B ^ 2) * (8 * n ^ (c + 2))
          = 16 * n ^ (c + 2) * B ^ 2 := by ring
        _ ≤ 16 * (2 ^ (4 * (c + 2) * b_char)) ^ 2 * B ^ 2 :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 16 hnpow_c)
        _ = (4 * 2 ^ (4 * (c + 2) * b_char) * B) ^ 2 := by ring
        _ ≤ W ^ 2 := Nat.pow_le_pow_left hWB 2
    have hchain : (2 * B ^ 2) * (8 * n ^ (c + 2) * #Bad) ≤
        (2 * B ^ 2) * Fintype.card (DoubleTabTopSeed c_tab (2 * q_tab * c_tab) b_char) := by
      calc (2 * B ^ 2) * (8 * n ^ (c + 2) * #Bad)
          = ((2 * B ^ 2) * (8 * n ^ (c + 2))) * #Bad := by ring
        _ ≤ W ^ 2 * #Bad := Nat.mul_le_mul_right _ hsq
        _ ≤ 2 * B ^ 2 * Fintype.card (DoubleTabTopSeed c_tab (2 * q_tab * c_tab) b_char) := hcard
    exact Nat.le_of_mul_le_mul_left hchain (by positivity)
  rw [toOuterMeasure_uniformOfFintype_toReal]
  have hfilt : univ.filter (· ∈ ({T₁ : DoubleTabTopSeed c_tab (2 * q_tab * c_tab) b_char |
      IsKUnique κ (simpleTabTuple T₁)}ᶜ : Set _)) = Bad :=
    filter_congr fun _ _ => Iff.rfl
  rw [hfilt, div_le_div_iff₀ (Nat.cast_pos.mpr Fintype.card_pos) (by positivity)]
  have hnat : #Bad * (8 * n ^ (c + 2)) ≤
      Fintype.card (DoubleTabTopSeed c_tab (2 * q_tab * c_tab) b_char) := by linarith
  simpa [one_mul] using (Nat.cast_le (α := ℝ)).mpr hnat

/-- Multiply-shift reduction non-injectivity bound `≤ 1 / (16 * n ^ (c + 1))` on any `#X ≤ n`. -/
theorem prob_not_injOn_reduceBits_le {c n s_in : ℕ} (hn : quotientPermThreshold c ≤ n)
    (X : Finset (Fin (2 ^ s_in))) (hX : #X ≤ n) :
    ((PMF.uniformOfFintype (Fin (2 ^ (s_in - 1)))).toOuterMeasure
      {α | Set.InjOn (reduceBits s_in (quotientPermRedBits c n) α) (X : Set _)}ᶜ).toReal ≤
      1 / (16 * (n : ℝ) ^ (c + 1)) := by
  classical
  have h4n : 4 ≤ n := (four_le_quotientPermThreshold c).trans hn
  rcases Nat.eq_zero_or_pos s_in with rfl | hs
  · have hemp : ({α : Fin (2 ^ (0 - 1)) |
        Set.InjOn (reduceBits 0 (quotientPermRedBits c n) α) (X : Set _)}ᶜ : Set _) = ∅ := by
      ext α
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      intro x _ y _ _
      exact Fin.ext (by omega : x.val = y.val)
    have hzero : univ.filter (· ∈ (∅ : Set (Fin (2 ^ (0 - 1))))) = ∅ :=
      filter_eq_empty_iff.mpr fun _ _ h => h
    rw [hemp, toOuterMeasure_uniformOfFintype_toReal, hzero, Finset.card_empty, Nat.cast_zero,
      zero_div]
    positivity
  · have hbad := card_not_injOn_multiplyShiftReduced_le hs le_rfl (R := quotientPermRedBits c n) X
    have hX2 : #X * (#X - 1) ≤ n ^ 2 := by
      calc #X * (#X - 1) ≤ #X * #X := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        _ ≤ n * n := Nat.mul_le_mul hX hX
        _ = n ^ 2 := (sq n).symm
    have hn_clog : n ≤ 2 ^ Nat.clog 2 (max n 4) :=
      (le_max_left n 4).trans (Nat.le_pow_clog (by decide) _)
    have hR_pow : 16 * n ^ (c + 1) * n ^ 2 ≤ 2 ^ quotientPermRedBits c n := by
      calc 16 * n ^ (c + 1) * n ^ 2
          ≤ n ^ 2 * n ^ (c + 1) * n ^ 2 :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by nlinarith))
        _ = n ^ (c + 5) := by ring
        _ ≤ (2 ^ Nat.clog 2 (max n 4)) ^ (c + 5) := Nat.pow_le_pow_left hn_clog _
        _ = 2 ^ quotientPermRedBits c n := by
            unfold quotientPermRedBits; rw [← pow_mul, Nat.mul_comm]
    set Bad := univ \ reducedGoodTop (2 ^ s_in) s_in (quotientPermRedBits c n) X
    have hmul : 16 * n ^ (c + 1) * #Bad ≤ Fintype.card (Fin (2 ^ (s_in - 1))) := by
      have hchain : n ^ 2 * (16 * n ^ (c + 1) * #Bad) ≤ n ^ 2 * 2 ^ (s_in - 1) := by
        calc n ^ 2 * (16 * n ^ (c + 1) * #Bad)
            = #Bad * (16 * n ^ (c + 1) * n ^ 2) := by ring
          _ ≤ #Bad * 2 ^ quotientPermRedBits c n := Nat.mul_le_mul_left _ hR_pow
          _ ≤ (#X * (#X - 1)) * 2 ^ (s_in - 1) := hbad
          _ ≤ n ^ 2 * 2 ^ (s_in - 1) := Nat.mul_le_mul_right _ hX2
      simpa only [Fintype.card_fin] using Nat.le_of_mul_le_mul_left hchain (by positivity)
    rw [toOuterMeasure_uniformOfFintype_toReal]
    have hfilt : univ.filter (· ∈ ({α : Fin (2 ^ (s_in - 1)) |
        Set.InjOn (reduceBits s_in (quotientPermRedBits c n) α) (X : Set _)}ᶜ : Set _)) = Bad := by
      ext α
      unfold reduceBits
      simp [Bad, mem_sdiff, mem_reducedGoodTop]
    rw [hfilt, div_le_div_iff₀ (Nat.cast_pos.mpr Fintype.card_pos) (by positivity)]
    have hnat : #Bad * (16 * n ^ (c + 1)) ≤ Fintype.card (Fin (2 ^ (s_in - 1))) := by linarith
    simpa [one_mul] using (Nat.cast_le (α := ℝ)).mpr hnat

/-- Quantitative Naor–Reingold contraction bound `≤ 1 / (8 * n ^ (c + 2))` for `nrRounds c`
blocks whenever `2 * quotientPermCharBits n ≤ a'` and `quotientPermThreshold c ≤ n`. -/
theorem nr_contraction_quotientPerm_le {c n a' : ℕ} (hn : quotientPermThreshold c ≤ n)
    (ha' : 2 * quotientPermCharBits n ≤ a') :
    (1 / 2 : ℝ) *
      (3 * (quotientPermInd c n : ℝ) ^ 2 / (2 ^ nrHalfLow a' : ℝ)) ^ (nrRounds c) ≤
      1 / (8 * (n : ℝ) ^ (c + 2)) := by
  obtain ⟨_, hn_pow, hκ_le, hc_ge, _, hb_44c, _⟩ := threshold_charBits_bounds hn
  have hb_lo : quotientPermCharBits n ≤ nrHalfLow a' := by
    unfold nrHalfLow; omega
  generalize quotientPermChars c = c_tab at *
  generalize quotientPermCharBits n = b_char at *
  generalize quotientPermInd c n = κ at *
  set h_char := b_char / 2
  have hh_24c : 24 * c_tab ≤ h_char := by
    have : 48 * c_tab + 2 ≤ b_char := by nlinarith
    omega
  have hh_100 : 4 * 5 ^ 2 ≤ h_char := by
    have : 202 ≤ b_char := by nlinarith
    omega
  have hκ_h2 : κ ≤ h_char ^ 2 := by
    have hb_2h : b_char ≤ 3 * h_char := by omega
    calc κ ≤ 8 * c_tab * b_char := hκ_le
      _ ≤ 8 * c_tab * (3 * h_char) := Nat.mul_le_mul_left _ hb_2h
      _ = (24 * c_tab) * h_char := by ring
      _ ≤ h_char * h_char := Nat.mul_le_mul_right _ hh_24c
      _ = h_char ^ 2 := (sq h_char).symm
  have h3κ : 3 * κ ^ 2 ≤ 2 ^ h_char := by
    calc 3 * κ ^ 2 ≤ h_char * (h_char ^ 2) ^ 2 :=
          Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left hκ_h2 2)
      _ = h_char ^ 5 := by ring
      _ ≤ 2 ^ h_char := Nat.pow_le_two_pow (by decide) hh_100
  have hstep_nat : 3 * κ ^ 2 * 2 ^ h_char ≤ 2 ^ nrHalfLow a' := by
    calc 3 * κ ^ 2 * 2 ^ h_char ≤ 2 ^ h_char * 2 ^ h_char := Nat.mul_le_mul_right _ h3κ
      _ = 2 ^ (2 * h_char) := by rw [← pow_add, two_mul]
      _ ≤ 2 ^ nrHalfLow a' := Nat.pow_le_pow_right (by decide) (by omega)
  have hstep_real : 3 * (κ : ℝ) ^ 2 / (2 ^ nrHalfLow a' : ℝ) ≤ 1 / (2 ^ h_char : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (3 * (κ : ℝ) ^ 2) * (2 ^ h_char : ℝ) ≤ 1 * (2 ^ nrHalfLow a' : ℝ) := by
      exact_mod_cast (by simpa only [one_mul] using hstep_nat)
    exact this
  have hexp : 8 * (c + 2) * b_char + 2 ≤ h_char * nrRounds c := by
    unfold nrRounds
    have h18 : 8 * b_char + 2 ≤ 18 * h_char := by omega
    calc 8 * (c + 2) * b_char + 2
        ≤ 8 * (c + 2) * b_char + 2 * (c + 2) := Nat.add_le_add_left (by omega) _
      _ = (8 * b_char + 2) * (c + 2) := by ring
      _ ≤ (18 * h_char) * (c + 2) := Nat.mul_le_mul_right _ h18
      _ = h_char * (18 * (c + 2)) := by ring
  have hden_nat : 4 * n ^ (c + 2) ≤ 2 ^ (h_char * nrRounds c) := by
    calc 4 * n ^ (c + 2)
        ≤ 2 ^ 2 * (2 ^ (8 * b_char)) ^ (c + 2) :=
          Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hn_pow _)
      _ = 2 ^ (8 * (c + 2) * b_char + 2) := by
          rw [← pow_mul, ← pow_add]; exact congrArg (2 ^ ·) (by ring)
      _ ≤ 2 ^ (h_char * nrRounds c) := Nat.pow_le_pow_right (by decide) hexp
  have hden_real : 8 * (n : ℝ) ^ (c + 2) ≤ 2 * ((2 ^ h_char : ℝ) ^ nrRounds c) := by
    have h4 : 4 * (n : ℝ) ^ (c + 2) ≤ (2 : ℝ) ^ (h_char * nrRounds c) := by exact_mod_cast hden_nat
    rw [← pow_mul]
    linarith
  calc (1 / 2 : ℝ) * (3 * (κ : ℝ) ^ 2 / (2 ^ nrHalfLow a' : ℝ)) ^ nrRounds c
      ≤ (1 / 2 : ℝ) * (1 / (2 ^ h_char : ℝ)) ^ nrRounds c := by
        gcongr
    _ = 1 / (2 * ((2 ^ h_char : ℝ) ^ nrRounds c)) := by
        rw [one_div_pow]; ring
    _ ≤ 1 / (8 * (n : ℝ) ^ (c + 2)) :=
        one_div_le_one_div_of_le (by positivity) hden_real

/-- Above `quotientPermThreshold c`, `2 ≤ quotientPermInd c n ≤ n`,
`4 * quotientPermCharBits n ≤ Nat.log 2 n`, and `2 * (quotientPermInd c n) ^ 2 ≤ 2 ^ b_char`. -/
theorem quotientPermInd_le_self_of_threshold {c n : ℕ} (hn : quotientPermThreshold c ≤ n) :
    4 * quotientPermCharBits n ≤ Nat.log 2 n ∧
      2 ≤ quotientPermInd c n ∧
      quotientPermInd c n ≤ n ∧
      2 * (quotientPermInd c n) ^ 2 ≤ 2 ^ quotientPermCharBits n := by
  have hmin_pos := one_le_quotientPermMinB c
  have hlog : 4 * quotientPermMinB c ≤ Nat.log 2 n :=
    Nat.le_log_of_pow_le (by decide : 1 < 2) hn
  have hb_log : 4 * quotientPermCharBits n ≤ Nat.log 2 n := by
    unfold quotientPermCharBits; omega
  obtain ⟨h4n, _, hκ_le, hc_ge, _, hb_44c, _⟩ := threshold_charBits_bounds hn
  have hκ_ge : 2 ≤ quotientPermInd c n := by
    have : 1 ≤ Nat.clog 2 (max n 2) := Nat.clog_pos (by decide) (by omega)
    unfold quotientPermInd; nlinarith
  generalize quotientPermChars c = c_tab at *
  generalize quotientPermCharBits n = b_char at *
  generalize quotientPermInd c n = κ at *
  have hb_8c : 8 * c_tab ≤ b_char := by nlinarith
  have hb_100 : 4 * 5 ^ 2 ≤ b_char := by nlinarith
  have hκ_b2 : κ ≤ b_char ^ 2 := by
    calc κ ≤ 8 * c_tab * b_char := hκ_le
      _ ≤ b_char * b_char := Nat.mul_le_mul_right _ hb_8c
      _ = b_char ^ 2 := (sq b_char).symm
  have h2κ2 : 2 * κ ^ 2 ≤ 2 ^ b_char := by
    calc 2 * κ ^ 2 ≤ b_char * (b_char ^ 2) ^ 2 :=
          Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left hκ_b2 2)
      _ = b_char ^ 5 := by ring
      _ ≤ 2 ^ b_char := Nat.pow_le_two_pow (by decide) hb_100
  have hn_pos : 0 < n := lt_of_lt_of_le (by decide : 0 < 4) h4n
  refine ⟨hb_log, hκ_ge, ?_, h2κ2⟩
  calc κ ≤ 2 * κ ^ 2 := by nlinarith
    _ ≤ 2 ^ b_char := h2κ2
    _ ≤ 2 ^ Nat.log 2 n := Nat.pow_le_pow_right (by decide) (by omega)
    _ ≤ n := Nat.pow_log_le_self 2 hn_pos.ne'


/-- Bottom-level simple-tabulation seed bundle for all `nrRounds c` Case B Naor–Reingold blocks. -/
abbrev QuotientPermNRSeed (c a m n : ℕ) :=
  NRComposedSeed (nrRounds c)
    (DoubleTabBotSeed (quotientPermInter c) (quotientPermCharBits n) (nrHalfHigh (suffixBits a m)))
    (DoubleTabBotSeed (quotientPermInter c) (quotientPermCharBits n) (nrHalfLow (suffixBits a m)))
    (DoubleTabBotSeed (quotientPermInter c) (quotientPermCharBits n) (nrHalfHigh (suffixBits a m)))

theorem isKWise_doubleTab_pow_of_le {c n s_in s_out k : ℕ}
    (hs_in : s_in ≤ quotientPermChars c * quotientPermCharBits n)
    {τ : DoubleTabTopSeed (quotientPermChars c) (quotientPermInter c) (quotientPermCharBits n)}
    (hτ : IsKUnique k (simpleTabTuple τ)) :
    IsKWiseIndependentHash k (fun bot =>
      doubleTabHash (quotientPermChars c) (quotientPermInter c) (quotientPermCharBits n)
        (2 ^ s_in) s_out τ bot) :=
  isKWiseIndependentHash_doubleTabHash_of_isKUnique (Nat.pow_le_pow_right (by decide) hs_in) hτ

theorem isKWise_reducedDoubleTab_of_injOn {c n s_in s_out k : ℕ}
    (hn : quotientPermThreshold c ≤ n)
    {τ : DoubleTabTopSeed (quotientPermChars c) (quotientPermInter c) (quotientPermCharBits n)}
    (hτ : IsKUnique k (simpleTabTuple τ))
    {α : Fin (2 ^ (s_in - 1))} {X : Finset (Fin (2 ^ s_in))}
    (hinj : Set.InjOn (reduceBits s_in (quotientPermRedBits c n) α) (X : Set _)) :
    IsKWiseIndependentHash k (fun bot (x : X) =>
      reducedDoubleTab c n s_in s_out α τ bot x.1) := by
  have hmin : min s_in (quotientPermRedBits c n) ≤ quotientPermChars c * quotientPermCharBits n :=
    (min_le_right _ _).trans (clog_max_le_eight_mul_charBits hn).2
  have hdt := isKWise_doubleTab_pow_of_le (s_out := s_out) hmin hτ
  have hinj_sub : Function.Injective
      (fun x : X => reduceBits s_in (quotientPermRedBits c n) α x.1) :=
    fun x₁ x₂ h => Subtype.ext (hinj x₁.2 x₂.2 h)
  exact hdt.comp hinj_sub

/-- Concrete 4-stage Case A statistical-distance bound for `caseABucketAux` instantiated with
`reducedDoubleTab` over uniform `(Top, α₀, BotA₀, α₁, BotA₁₂)` (`≤ 1 / n ^ (c + 1)`), proved via
`dist_caseA_restrict_le` and `isKWiseIndependentHash_caseABucketAux_of_injOn`. -/
theorem dist_caseA_reducedDoubleTab_le {a m b_aux c n : ℕ}
    (hma : m ≤ a) (hgap : m + caseAGap c n ≤ a) (hn : quotientPermThreshold c ≤ n)
    {S T : Finset (Fin (2 ^ a))} (hS : #S ≤ n) (hTS : T ⊆ S)
    (hT : #T ≤ quotientPermInd c n) :
    dist ((PMF.uniformOfFintype
          (DoubleTabTopSeed (quotientPermChars c) (quotientPermInter c)
            (quotientPermCharBits n))).bind fun τ =>
        (PMF.uniformOfFintype (Fin (2 ^ (m - 1)))).bind fun α₀ =>
          (PMF.uniformOfFintype
              (DoubleTabBotSeed (quotientPermInter c) (quotientPermCharBits n) (a - m))).bind
            fun botA₀ =>
              (PMF.uniformOfFintype (Fin (2 ^ (a - m - 1)))).bind fun α₁ =>
                (PMF.uniformOfFintype
                    (DoubleTabBotSeed (quotientPermInter c) (quotientPermCharBits n)
                      (m + b_aux))).map
                  fun botA₁₂ (u : T) =>
                    caseABucketAux hma (reducedDoubleTab c n m (a - m) α₀ τ botA₀)
                      (reducedDoubleTab c n (a - m) (m + b_aux) α₁ τ botA₁₂) u.1)
      (PMF.uniformOfFintype (T → Fin (2 ^ m) × Fin (2 ^ b_aux))) ≤
      1 / (n : ℝ) ^ (c + 1) := by
  classical
  let Top := DoubleTabTopSeed (quotientPermChars c) (quotientPermInter c) (quotientPermCharBits n)
  let BotA₀ := DoubleTabBotSeed (quotientPermInter c) (quotientPermCharBits n) (a - m)
  let BotA₁₂ := DoubleTabBotSeed (quotientPermInter c) (quotientPermCharBits n) (m + b_aux)
  have : Nonempty Top := ⟨fun _ _ _ => 0⟩
  have : Nonempty BotA₀ := ⟨fun _ _ => 0⟩
  have : Nonempty BotA₁₂ := ⟨fun _ _ => 0⟩
  have : Nonempty (Fin (2 ^ (m - 1))) := ⟨0⟩
  have : Nonempty (Fin (2 ^ (a - m - 1))) := ⟨0⟩
  let U_target := PMF.uniformOfFintype (T → Fin (2 ^ m) × Fin (2 ^ b_aux))
  have h4n : 4 ≤ n := (four_le_quotientPermThreshold c).trans hn
  have h2κ : 2 ≤ quotientPermInd c n := (quotientPermInd_le_self_of_threshold hn).2.1
  have hT_card : Fintype.card T ≤ quotientPermInd c n := by simpa using hT
  let S_L : Finset (Fin (2 ^ m)) := S.image fun u => (bitDomainEquiv hma u).1
  have hSL : #S_L ≤ n := card_image_le.trans hS
  have hquot_div :
      ((#S * (#S - 1) : ℕ) : ℝ) / (2 * (2 ^ (a - m) : ℝ)) ≤ 1 / (2 * (n : ℝ) ^ (c + 1)) := by
    have hS2 : #S * (#S - 1) ≤ n ^ 2 := by
      calc #S * (#S - 1) ≤ #S * #S := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        _ ≤ n * n := Nat.mul_le_mul hS hS
        _ = n ^ 2 := (sq n).symm
    have hn_clog : n ≤ 2 ^ Nat.clog 2 (max n 2) :=
      (le_max_left n 2).trans (Nat.le_pow_clog (by decide) _)
    have hgap' : caseAGap c n ≤ a - m := by omega
    have hnat : (#S * (#S - 1)) * n ^ (c + 1) ≤ 2 ^ (a - m) := by
      calc (#S * (#S - 1)) * n ^ (c + 1)
          ≤ n ^ 2 * n ^ (c + 1) := Nat.mul_le_mul_right _ hS2
        _ = n ^ (c + 3) := by ring
        _ ≤ (2 ^ Nat.clog 2 (max n 2)) ^ (c + 3) := Nat.pow_le_pow_left hn_clog _
        _ = 2 ^ caseAGap c n := by unfold caseAGap; rw [← pow_mul, Nat.mul_comm]
        _ ≤ 2 ^ (a - m) := Nat.pow_le_pow_right (by decide) hgap'
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hreal : ((#S * (#S - 1) : ℕ) : ℝ) * (n : ℝ) ^ (c + 1) ≤ (2 ^ (a - m) : ℝ) := by
      exact_mod_cast hnat
    linarith
  have hgroup : ((PMF.uniformOfFintype Top).bind fun τ =>
      (PMF.uniformOfFintype (Fin (2 ^ (m - 1)))).bind fun α₀ =>
        (PMF.uniformOfFintype BotA₀).bind fun botA₀ =>
          (PMF.uniformOfFintype (Fin (2 ^ (a - m - 1)))).bind fun α₁ =>
            (PMF.uniformOfFintype BotA₁₂).map fun botA₁₂ (u : T) =>
              caseABucketAux hma (reducedDoubleTab c n m (a - m) α₀ τ botA₀)
                (reducedDoubleTab c n (a - m) (m + b_aux) α₁ τ botA₁₂) u.1) =
      (PMF.uniformOfFintype (Top × Fin (2 ^ (m - 1)))).bind fun p =>
        (PMF.uniformOfFintype BotA₀).bind fun botA₀ =>
          (PMF.uniformOfFintype (Fin (2 ^ (a - m - 1)) × BotA₁₂)).map fun q (u : T) =>
            caseABucketAux hma (reducedDoubleTab c n m (a - m) p.2 p.1 botA₀)
              (reducedDoubleTab c n (a - m) (m + b_aux) q.1 p.1 q.2) u.1 := by
    rw [← uniformOfFintype_prod Top, PMF.bind_bind]
    refine congrArg ((PMF.uniformOfFintype Top).bind ·) (funext fun τ => ?_)
    rw [PMF.bind_map]
    refine congrArg ((PMF.uniformOfFintype (Fin (2 ^ (m - 1)))).bind ·) (funext fun α₀ => ?_)
    refine congrArg ((PMF.uniformOfFintype BotA₀).bind ·) (funext fun botA₀ => ?_)
    rw [← uniformOfFintype_prod (Fin (2 ^ (a - m - 1))), PMF.map_bind]
    simp only [PMF.map_comp, Function.comp_def]; rfl
  rw [hgroup]
  let GoodTop : Set (Top × Fin (2 ^ (m - 1))) :=
    {p | IsKUnique (quotientPermInd c n) (simpleTabTuple p.1) ∧
      Set.InjOn (reduceBits m (quotientPermRedBits c n) p.2) (S_L : Set _)}
  have hbad_top : ((PMF.uniformOfFintype (Top × Fin (2 ^ (m - 1)))).toOuterMeasure
      GoodTopᶜ).toReal ≤ 1 / (8 * (n : ℝ) ^ (c + 2)) + 1 / (16 * (n : ℝ) ^ (c + 1)) := by
    have hstep : ∀ τ ∈ (PMF.uniformOfFintype Top).support,
        τ ∈ {τ | IsKUnique (quotientPermInd c n) (simpleTabTuple τ)} →
        (((PMF.uniformOfFintype (Fin (2 ^ (m - 1)))).map fun α₀ => (τ, α₀)).toOuterMeasure
          GoodTopᶜ).toReal ≤ 1 / (16 * (n : ℝ) ^ (c + 1)) := by
      intro τ _ hτ
      rw [PMF.toOuterMeasure_map_apply]
      have hτ_uniq : IsKUnique (quotientPermInd c n) (simpleTabTuple τ) := hτ
      have hsub : (fun α₀ => (τ, α₀)) ⁻¹' GoodTopᶜ =
          {α₀ | Set.InjOn (reduceBits m (quotientPermRedBits c n) α₀) (S_L : Set _)}ᶜ := by
        ext α₀
        simp [GoodTop, hτ_uniq]
      rw [hsub]
      exact prob_not_injOn_reduceBits_le hn S_L hSL
    have hbind := toOuterMeasure_bind_failure_toReal_le (PMF.uniformOfFintype Top)
      (fun τ => (PMF.uniformOfFintype (Fin (2 ^ (m - 1)))).map fun α₀ => (τ, α₀))
      {τ | IsKUnique (quotientPermInd c n) (simpleTabTuple τ)} GoodTopᶜ
      (by positivity) hstep
    rw [uniformOfFintype_prod Top (Fin (2 ^ (m - 1)))] at hbind
    exact hbind.trans (add_le_add (prob_not_isKUnique_quotientPerm_le hn) le_rfl)
  have habs := dist_caseA_restrict_le hma
    (fun (p : Top × Fin (2 ^ (m - 1))) (botA₀ : BotA₀) =>
      reducedDoubleTab c n m (a - m) p.2 p.1 botA₀)
    (fun (p : Top × Fin (2 ^ (m - 1))) (q : Fin (2 ^ (a - m - 1)) × BotA₁₂) =>
      reducedDoubleTab c n (a - m) (m + b_aux) q.1 p.1 q.2)
    S T GoodTop (δ₁ := 1 / (16 * (n : ℝ) ^ (c + 1))) (by positivity) hbad_top
    (fun p hp => (isKWise_reducedDoubleTab_of_injOn hn hp.1 hp.2).isPairwiseIndependentHash h2κ)
    (fun p hp botA₀ hb₀ => by
      let g₀ := reducedDoubleTab c n m (a - m) p.2 p.1 botA₀
      let T_Q : Finset (Fin (2 ^ (a - m))) := T.image (caseAQuot hma g₀)
      have hTQ : #T_Q ≤ n := card_image_le.trans ((card_le_card hTS).trans hS)
      have hprod_map : ((PMF.uniformOfFintype (Fin (2 ^ (a - m - 1)) × BotA₁₂)).map fun q (u : T) =>
          caseABucketAux hma g₀ (reducedDoubleTab c n (a - m) (m + b_aux) q.1 p.1 q.2) u.1) =
          (PMF.uniformOfFintype (Fin (2 ^ (a - m - 1)))).bind fun α₁ =>
            (PMF.uniformOfFintype BotA₁₂).map fun botA₁₂ (u : T) =>
              caseABucketAux hma g₀
                (reducedDoubleTab c n (a - m) (m + b_aux) α₁ p.1 botA₁₂) u.1 := by
        rw [← uniformOfFintype_prod (Fin (2 ^ (a - m - 1))), PMF.map_bind]
        simp only [PMF.map_comp, Function.comp_def]; rfl
      rw [hprod_map]
      let Goodα₁ : Set (Fin (2 ^ (a - m - 1))) :=
        {α₁ | Set.InjOn (reduceBits (a - m) (quotientPermRedBits c n) α₁) (T_Q : Set _)}
      refine (dist_bind_of_good _ _ U_target Goodα₁ le_rfl fun α₁ hα₁ => ?_).trans ?_
      · have hinjT : Set.InjOn (caseAQuot hma g₀) (T : Set (Fin (2 ^ a))) :=
          hb₀.mono (Finset.coe_subset.mpr hTS)
        have hkw := isKWiseIndependentHash_caseABucketAux_of_injOn (b_aux := b_aux) hma hinjT
          (isKWise_reducedDoubleTab_of_injOn (s_out := m + b_aux) hn hp.1 hα₁)
        rw [uniformOfFintype_map_of_isKWise hkw hT_card, dist_self]
      · rw [add_zero]
        exact prob_not_injOn_reduceBits_le hn T_Q hTQ)
  have hτ_le : 1 / (8 * (n : ℝ) ^ (c + 2)) ≤ 1 / (32 * (n : ℝ) ^ (c + 1)) := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    have h4r : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h4n
    calc 32 * (n : ℝ) ^ (c + 1) = 8 * ((n : ℝ) ^ (c + 1) * 4) := by ring
      _ ≤ 8 * ((n : ℝ) ^ (c + 1) * (n : ℝ)) := by gcongr
      _ = 8 * (n : ℝ) ^ (c + 2) := by ring
  have hr₃ : 1 / (32 * (n : ℝ) ^ (c + 1)) + 1 / (16 * (n : ℝ) ^ (c + 1)) +
      1 / (2 * (n : ℝ) ^ (c + 1)) + 1 / (16 * (n : ℝ) ^ (c + 1)) =
      (21 / 32 : ℝ) * (1 / (n : ℝ) ^ (c + 1)) := by ring
  have hpos_pow : 0 ≤ 1 / (n : ℝ) ^ (c + 1) := by positivity
  linarith

/-- Concrete double-tabulation 1-round Feistel shard-load tail bound via
`FeistelPerm.dens_exists_bucketLoad_sub_ge_le`. -/
theorem prob_doubleTab_bucketLoad_outside_le {c n s_in s_out k_mom : ℕ}
    (hn : quotientPermThreshold c ≤ n)
    (hs_in : s_in ≤ quotientPermChars c * quotientPermCharBits n)
    (hk_pos : 1 ≤ k_mom) (hk_ind : 2 * k_mom ≤ quotientPermInd c n)
    (S_sh : Finset (Fin (2 ^ s_out) × Fin (2 ^ s_in))) {a_dev : ℝ}
    (hk_mu : 2 * (k_mom : ℝ) ≤ 3 * ((#S_sh : ℝ) / (2 ^ s_out : ℝ))) (ha_dev : 0 < a_dev) :
    ((PMF.uniformOfFintype
        (DoubleTabTopSeed (quotientPermChars c) (quotientPermInter c) (quotientPermCharBits n) ×
          DoubleTabBotSeed (quotientPermInter c) (quotientPermCharBits n) s_out)).toOuterMeasure
      {p | ∃ σ : Fin (2 ^ s_out),
        a_dev ≤ |(bucketLoad
            (doubleTabHash (quotientPermChars c) (quotientPermInter c) (quotientPermCharBits n)
              (2 ^ s_in) s_out p.1 p.2) S_sh σ : ℝ) -
          (#S_sh : ℝ) / (2 ^ s_out : ℝ)|}).toReal ≤
      1 / (8 * (n : ℝ) ^ (c + 2)) +
        (2 ^ (s_out + 1) : ℝ) *
          (3 * (k_mom : ℝ) * ((#S_sh : ℝ) / (2 ^ s_out : ℝ)) / a_dev ^ 2) ^ k_mom := by
  classical
  let Top := DoubleTabTopSeed (quotientPermChars c) (quotientPermInter c) (quotientPermCharBits n)
  let BotSh := DoubleTabBotSeed (quotientPermInter c) (quotientPermCharBits n) s_out
  have : Nonempty Top := ⟨fun _ _ _ => 0⟩
  have : Nonempty BotSh := ⟨fun _ _ => 0⟩
  let h_sh (τ : Top) (b : BotSh) :=
    doubleTabHash (quotientPermChars c) (quotientPermInter c) (quotientPermCharBits n)
      (2 ^ s_in) s_out τ b
  let E_pair : Set (Top × BotSh) := {p | ∃ σ : Fin (2 ^ s_out),
    a_dev ≤ |(bucketLoad (h_sh p.1 p.2) S_sh σ : ℝ) - (#S_sh : ℝ) / (2 ^ s_out : ℝ)|}
  let tailB := (2 ^ (s_out + 1) : ℝ) *
    (3 * (k_mom : ℝ) * ((#S_sh : ℝ) / (2 ^ s_out : ℝ)) / a_dev ^ 2) ^ k_mom
  have hstep : ∀ τ ∈ (PMF.uniformOfFintype Top).support,
      τ ∈ {τ | IsKUnique (quotientPermInd c n) (simpleTabTuple τ)} →
      (((PMF.uniformOfFintype BotSh).map fun b => (τ, b)).toOuterMeasure
        E_pair).toReal ≤ tailB := by
    intro τ _ hτ
    rw [PMF.toOuterMeasure_map_apply]
    have hkw := (isKWise_doubleTab_pow_of_le (s_out := s_out) hs_in hτ).mono hk_ind
    have hd := dens_exists_bucketLoad_sub_ge_le hk_pos hkw S_sh hk_mu ha_dev
    have hpre : (fun b => (τ, b)) ⁻¹' E_pair =
        {b : BotSh | ∃ σ : Fin (2 ^ s_out),
          a_dev ≤ |(bucketLoad (h_sh τ b) S_sh σ : ℝ) - (#S_sh : ℝ) / (2 ^ s_out : ℝ)|} := rfl
    rw [PMF.toOuterMeasure_uniformOfFintype_toReal]
    simpa only [hpre, Set.mem_ofPred_eq, dens_eq_card_div_card, NNRat.cast_div,
      NNRat.cast_natCast] using hd
  have hbind := toOuterMeasure_bind_failure_toReal_le (PMF.uniformOfFintype Top)
    (fun τ => (PMF.uniformOfFintype BotSh).map fun b => (τ, b))
    {τ | IsKUnique (quotientPermInd c n) (simpleTabTuple τ)} E_pair
    (by positivity) hstep
  rw [uniformOfFintype_prod Top BotSh] at hbind
  exact hbind.trans (add_le_add (prob_not_isKUnique_quotientPerm_le hn) le_rfl)

end Cslib.DataStructure.Dictionary.KickTree
