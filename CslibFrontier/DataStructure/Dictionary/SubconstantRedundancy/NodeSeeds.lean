/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.Schedule
public import CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.BitBudget
import CslibFrontier.Foundations.Data.Finset.Density
import CslibFrontier.Foundations.Probability.TwoStage

/-!
# Regime-Switched Child-Router and Node-Level Hash Seeds

This file formalizes the regime-switched child-router seed family (`RouterSeed`), grouped per-node
hash-seed spaces (`NodeSeed`), and unified seed-failure concentration bounds for the multi-level
dictionary tree of Tianxiao Li, Jingxun Liang, Huacheng Yu, and Renfei Zhou, *Dynamic Dictionary
with Subconstant Wasted Bits per Key* ([LiLiangYuZhou2024, Sections 5.4 and 5.5];
[arXiv:2310.20536v1](https://arxiv.org/abs/2310.20536v1), PDF pp. 32–34 / printed pp. 31–33).
Pure node storage structures and Section 5.6 metadata separation are defined in `StorageNode.lean`.

## Regime-switched child routing (formalization adaptation)

In [LiLiangYuZhou2024, Section 5.4, Lemma 5.1 & Appendix B, Claim B.2], child routing uses Mikkel
Thorup's double-tabulation family [Thorup2013] uniformly across all tree levels under an idealized
asymptotic threshold. In `FeistelPerm`, the explicit finite-size uniqueness threshold
`FeistelPerm.childRouterThreshold epsInv alphaInv` is doubly exponential, so deep internal levels
can satisfy `nLow ℓ < childRouterThreshold epsInv alphaInv` at moderate `n`. We therefore switch
statically per level `0 ≤ ℓ < depth` via `TreeSchedule.usesDoubleTabRouter`:

* **Large-node regime (`childRouterThreshold epsInv alphaInv ≤ nLow ℓ`):** uses
  `FeistelPerm.ChildRouterSeed` (`DoubleTabulation`) and bounds bucket-load deviation via
  `FeistelPerm.dens_childRouter_bucketLoad_outside_le_of_threshold`.
* **Small-node regime (`nLow ℓ < childRouterThreshold epsInv alphaInv`):** uses exact
  `(2 * childRouterHalfInd (nHigh ℓ))`-wise `Cslib.Probability.trinomialPolyHash`, whose degree is
  bounded by the capacity-independent constant `smallRouterMaxDegree epsInv alphaInv`
  (`TreeSchedule.smallRouterDegree_le`) for constant-time Horner evaluation, and bounds bucket-load
  deviation via `FeistelPerm.dens_exists_bucketLoad_sub_ge_le`.

Both regimes satisfy the identical bucket-window failure bound `≤ 1 / (nFloor ℓ) ^ 2`
(`TreeSchedule.dens_routerRound_outside_bounds_le`) and exact bit-budget match
`Fintype.card (P.RouterSeed ℓ) = 2 ^ P.routerSeedBits ℓ`.

## Main definitions

* `Cslib.DataStructure.Dictionary.SubconstantRedundancy.smallRouterMaxDegree`,
  `TreeSchedule.usesDoubleTabRouter`, `TreeSchedule.RouterSeed`, `TreeSchedule.routerRound`,
  `TreeSchedule.routerPerm`: regime-switched child-router seed family and Feistel bijection.
* `TreeSchedule.PrimId`, `TreeSchedule.NodeSeed`, `TreeSchedule.IsGoodNodeSeed`: grouped per-node
  hash seed `g_u` (`Section 5.5`, PDF p. 34 / printed p. 33) and collision/load-balance predicate.

## Main results

* `TreeSchedule.card_routerSeed`, `TreeSchedule.card_nodeSeed`: seed cardinalities match
  `2 ^ routerSeedBits ℓ` and `2 ^ nodeHashSeedBits ℓ`.
* `TreeSchedule.smallRouterDegree_le`: constant `O_{ε, α}(1)` polynomial degree below threshold.
* `TreeSchedule.dens_routerRound_outside_bounds_le`: unified `1 / (nFloor ℓ) ^ 2` child-load failure
  bound across both child-router regimes (`Lemma 5.1(c)`, PDF p. 32 / printed p. 31).
* `TreeSchedule.dens_not_isGoodNodeSeed_le`, `TreeSchedule.exists_isGoodNodeSeed`,
  `TreeSchedule.exists_isGoodNodeSeed_pair`: unified `3 / (nFloor ℓ) ^ 2` node-seed failure bound
  and good-seed existence (`Section 5.5`, PDF p. 34 / printed p. 33).

## References

* [T. Li, J. Liang, H. Yu, and R. Zhou,
  *Dynamic Dictionary with Subconstant Wasted Bits per Key*][LiLiangYuZhou2024]
* [M. Pătrașcu, *Succincter*][Patrascu2008]
* [M. Thorup, *Simple Tabulation, Fast Expanders, Double Tabulation, and High
  Independence*][Thorup2013]
-/

public section

namespace Cslib.DataStructure.Dictionary.SubconstantRedundancy

open Cslib.DataStructure.Dictionary
open Cslib.Probability
open Finset

/-- Capacity-independent upper bound on the polynomial degree `2 * childRouterHalfInd (nHigh ℓ)`
whenever `nLow ℓ < childRouterThreshold epsInv alphaInv` (`Section 5.4` small-node adaptation). -/
@[expose]
def smallRouterMaxDegree (epsInv alphaInv : ℕ) : ℕ :=
  2 * FeistelPerm.childRouterHalfInd (4 * FeistelPerm.childRouterThreshold epsInv alphaInv)


namespace TreeSchedule

variable (P : TreeSchedule)

/-! ## Section 1: Regime-switched child-router seed family and load concentration -/

/-- Static level predicate selecting `DoubleTabulation` (`childRouterThreshold ≤ nLow ℓ`) versus
small-node `trinomialPolyHash` (`nLow ℓ < childRouterThreshold`). -/
@[expose]
def usesDoubleTabRouter (ℓ : ℕ) : Prop :=
  FeistelPerm.childRouterThreshold P.epsInv P.alphaInv ≤ P.nLow ℓ

instance instDecidableUsesDoubleTabRouter (ℓ : ℕ) : Decidable (P.usesDoubleTabRouter ℓ) := by
  unfold usesDoubleTabRouter
  infer_instance

/-- Double-tabulation child-router seed type at level `ℓ` above `childRouterThreshold`. -/
abbrev LargeRouterSeed (ℓ : ℕ) : Type :=
  FeistelPerm.ChildRouterSeed
    (FeistelPerm.childRouterChars P.epsInv)
    (FeistelPerm.childRouterRep P.epsInv P.alphaInv)
    (FeistelPerm.childRouterCharBits (FeistelPerm.childRouterChars P.epsInv) (P.routerRightUniv ℓ))
    (P.branchBits ℓ)

/-- Exact `(2 * childRouterHalfInd (nHigh ℓ))`-wise trinomial seed type at level `ℓ` below
`childRouterThreshold`. -/
abbrev SmallRouterSeed (ℓ : ℕ) : Type :=
  Fin (2 * FeistelPerm.childRouterHalfInd (P.nHigh ℓ)) →
    Fin (2 ^ trinomialDeg (P.routerRightUniv ℓ) (P.branchBits ℓ))

/-- Regime-switched child-router seed at level `0 ≤ ℓ < depth`. -/
inductive RouterSeed (P : TreeSchedule) (ℓ : ℕ) : Type
  | doubleTab (h : P.usesDoubleTabRouter ℓ) (seed : P.LargeRouterSeed ℓ)
  | trinomial (h : ¬ P.usesDoubleTabRouter ℓ) (seed : P.SmallRouterSeed ℓ)
  deriving DecidableEq

/-- Canonical equivalence with `LargeRouterSeed ℓ` when `usesDoubleTabRouter ℓ` holds. -/
def routerSeedDoubleTabEquiv {ℓ : ℕ} (h : P.usesDoubleTabRouter ℓ) :
    P.LargeRouterSeed ℓ ≃ P.RouterSeed ℓ where
  toFun := RouterSeed.doubleTab h
  invFun
    | .doubleTab _ s => s
    | .trinomial hn _ => False.elim (hn h)
  left_inv _ := rfl
  right_inv
    | .doubleTab _ _ => rfl
    | .trinomial hn _ => False.elim (hn h)

/-- Canonical equivalence with `SmallRouterSeed ℓ` when `¬ usesDoubleTabRouter ℓ` holds. -/
def routerSeedTrinomialEquiv {ℓ : ℕ} (h : ¬ P.usesDoubleTabRouter ℓ) :
    P.SmallRouterSeed ℓ ≃ P.RouterSeed ℓ where
  toFun := RouterSeed.trinomial h
  invFun
    | .doubleTab hp _ => False.elim (h hp)
    | .trinomial _ s => s
  left_inv _ := rfl
  right_inv
    | .doubleTab hp _ => False.elim (h hp)
    | .trinomial _ _ => rfl

@[simp]
theorem routerSeedDoubleTabEquiv_apply {ℓ : ℕ} (h : P.usesDoubleTabRouter ℓ)
    (seed : P.LargeRouterSeed ℓ) :
    P.routerSeedDoubleTabEquiv h seed = .doubleTab h seed := by rfl

@[simp]
theorem routerSeedTrinomialEquiv_apply {ℓ : ℕ} (h : ¬ P.usesDoubleTabRouter ℓ)
    (seed : P.SmallRouterSeed ℓ) :
    P.routerSeedTrinomialEquiv h seed = .trinomial h seed := by rfl

instance instFintypeRouterSeed (ℓ : ℕ) : Fintype (P.RouterSeed ℓ) :=
  if h : P.usesDoubleTabRouter ℓ then
    Fintype.ofEquiv (P.LargeRouterSeed ℓ) (P.routerSeedDoubleTabEquiv h)
  else
    Fintype.ofEquiv (P.SmallRouterSeed ℓ) (P.routerSeedTrinomialEquiv h)

instance instInhabitedRouterSeed (ℓ : ℕ) : Inhabited (P.RouterSeed ℓ) :=
  if h : P.usesDoubleTabRouter ℓ then
    ⟨.doubleTab h (fun _ _ _ => ⟨0, Nat.two_pow_pos _⟩, fun _ _ => ⟨0, Nat.two_pow_pos _⟩)⟩
  else
    ⟨.trinomial h fun _ => ⟨0, Nat.two_pow_pos _⟩⟩

/-- `RouterSeed P ℓ` has exact cardinality `2 ^ P.routerSeedBits ℓ`. -/
theorem card_routerSeed (ℓ : ℕ) :
    Fintype.card (P.RouterSeed ℓ) = 2 ^ P.routerSeedBits ℓ := by
  dsimp only [routerSeedBits]
  by_cases h : P.usesDoubleTabRouter ℓ
  · have hth : FeistelPerm.childRouterThreshold P.epsInv P.alphaInv ≤ P.nLow ℓ := h
    rw [ite_eq_left hth, ← Fintype.card_congr (P.routerSeedDoubleTabEquiv h)]
    exact FeistelPerm.card_childRouterSeed _ _ _ _
  · have hth : ¬ FeistelPerm.childRouterThreshold P.epsInv P.alphaInv ≤ P.nLow ℓ := h
    rw [ite_eq_right hth, ← Fintype.card_congr (P.routerSeedTrinomialEquiv h)]
    simp only [SmallRouterSeed, Fintype.card_fun, Fintype.card_fin, ← Nat.pow_mul]
    congr 1
    ring

/-- Below `childRouterThreshold`, the trinomial child-router polynomial degree is bounded by the
capacity-independent constant `smallRouterMaxDegree P.epsInv P.alphaInv`. -/
theorem smallRouterDegree_le (hcr : P.ConcentrationReady) {ℓ : ℕ} (hℓ : ℓ < P.depth)
    (hsmall : ¬ P.usesDoubleTabRouter ℓ) :
    2 * FeistelPerm.childRouterHalfInd (P.nHigh ℓ) ≤
      smallRouterMaxDegree P.epsInv P.alphaInv := by
  have hlt : P.nLow ℓ < FeistelPerm.childRouterThreshold P.epsInv P.alphaInv := not_le.mp hsmall
  have hnhi : P.nHigh ℓ ≤ 4 * FeistelPerm.childRouterThreshold P.epsInv P.alphaInv := by
    rcases Nat.eq_zero_or_pos ℓ with rfl | hpos
    · have hcap : 2 ≤ P.cap := P.two_le_cap
      simp only [nLow, nHigh, ↓reduceIte] at hlt ⊢
      omega
    · have h2d := hcr.two_mul_delta_le_nFloor ℓ hpos hℓ.le
      dsimp only [nLow, nHigh] at hlt ⊢
      rw [ite_eq_right hpos.ne'] at hlt ⊢
      omega
  dsimp only [smallRouterMaxDegree]
  rw [FeistelPerm.childRouterHalfInd_eq, FeistelPerm.childRouterHalfInd_eq]
  have hclog : Nat.clog 2 (max (P.nHigh ℓ) 2) ≤
      Nat.clog 2 (max (4 * FeistelPerm.childRouterThreshold P.epsInv P.alphaInv) 2) :=
    Nat.clog_mono_right 2 (max_le_max_right 2 hnhi)
  omega

/-- Zero-pad a small-node trinomial router seed from `2 * childRouterHalfInd (nHigh ℓ)`
coefficients to the static capacity-independent degree `smallRouterMaxDegree P.epsInv P.alphaInv`,
so Word-RAM polynomial evaluation (`KWise.evalCode`) can use a single `O(1)`-degree circuit across
all small-node levels. -/
@[expose]
def padSmallRouterSeed (ℓ : ℕ) (seed : P.SmallRouterSeed ℓ) :
    Fin (smallRouterMaxDegree P.epsInv P.alphaInv) →
      Fin (2 ^ trinomialDeg (P.routerRightUniv ℓ) (P.branchBits ℓ)) :=
  fun i =>
    if hi : i.val < 2 * FeistelPerm.childRouterHalfInd (P.nHigh ℓ) then
      seed ⟨i.val, hi⟩
    else
      ⟨0, Nat.two_pow_pos _⟩

/-- Regime-switched Feistel round function `Fin (routerRightUniv ℓ) → Fin (2 ^ branchBits ℓ)`. -/
noncomputable def routerRound (ℓ : ℕ) :
    P.RouterSeed ℓ → Fin (P.routerRightUniv ℓ) → Fin (2 ^ P.branchBits ℓ)
  | .doubleTab _ seed =>
    FeistelPerm.childRouterRound
      (FeistelPerm.childRouterChars P.epsInv)
      (FeistelPerm.childRouterRep P.epsInv P.alphaInv)
      (FeistelPerm.childRouterCharBits (FeistelPerm.childRouterChars P.epsInv)
        (P.routerRightUniv ℓ))
      (P.branchBits ℓ) (P.routerRightUniv ℓ) seed
  | .trinomial _ seed =>
    trinomialPolyHash
      (trinomialStep (P.routerRightUniv ℓ) (P.branchBits ℓ))
      (2 * FeistelPerm.childRouterHalfInd (P.nHigh ℓ))
      (P.routerRightUniv ℓ) (P.branchBits ℓ) seed

/-- Below `childRouterThreshold`, evaluating `routerRound` on a `.trinomial` seed equals evaluating
`trinomialPolyHash` at the static degree `smallRouterMaxDegree P.epsInv P.alphaInv` on
`padSmallRouterSeed ℓ seed`. -/
theorem routerRound_trinomial_eq_padded (hcr : P.ConcentrationReady) {ℓ : ℕ} (hℓ : ℓ < P.depth)
    (hsmall : ¬ P.usesDoubleTabRouter ℓ) (seed : P.SmallRouterSeed ℓ)
    (x : Fin (P.routerRightUniv ℓ)) :
    P.routerRound ℓ (.trinomial hsmall seed) x =
      trinomialPolyHash
        (trinomialStep (P.routerRightUniv ℓ) (P.branchBits ℓ))
        (smallRouterMaxDegree P.epsInv P.alphaInv)
        (P.routerRightUniv ℓ) (P.branchBits ℓ) (P.padSmallRouterSeed ℓ seed) x := by
  have hkM : 2 * FeistelPerm.childRouterHalfInd (P.nHigh ℓ) ≤
      smallRouterMaxDegree P.epsInv P.alphaInv := P.smallRouterDegree_le hcr hℓ hsmall
  let t := trinomialStep (P.routerRightUniv ℓ) (P.branchBits ℓ)
  let k := 2 * FeistelPerm.childRouterHalfInd (P.nHigh ℓ)
  let M := smallRouterMaxDegree P.epsInv P.alphaInv
  apply Fin.ext
  dsimp only [routerRound, trinomialPolyHash, trinomialPolyEval, polynomialHash,
    SmallRouterSeed, trinomialDeg] at seed ⊢
  apply congrArg (· % 2 ^ P.branchBits ℓ)
  apply congrArg Fin.val
  apply congrArg (TrinomialField.equivFin t)
  rw [← Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin M)))
    (p := fun i : Fin M => i.val < k)]
  have htail : ∑ i ∈ Finset.univ.filter (fun i : Fin M => ¬ i.val < k),
      (TrinomialField.equivFin t).symm (P.padSmallRouterSeed ℓ seed i) *
        AdjoinRoot.mk (trinomial t) (polyOfCode x.val) ^ (i : ℕ) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hnot : ¬ i.val < 2 * FeistelPerm.childRouterHalfInd (P.nHigh ℓ) := (mem_filter.mp hi).2
    dsimp only [padSmallRouterSeed, trinomialDeg]
    rw [dite_eq_right hnot, TrinomialField.equivFin_symm_eq_mk_polyOfCode]
    simp
  rw [htail, add_zero]
  refine Finset.sum_bij (fun (j : Fin k) _ => (⟨j.val, j.isLt.trans_le hkM⟩ : Fin M))
    (fun j _ => mem_filter.mpr ⟨mem_univ _, j.isLt⟩)
    (fun _ _ _ _ h => Fin.ext (Fin.mk.inj h))
    (fun i hi => ⟨⟨i.val, (mem_filter.mp hi).2⟩, mem_univ _, rfl⟩)
    fun j _ => ?_
  dsimp only [padSmallRouterSeed, trinomialDeg]
  rw [dite_eq_left j.isLt]

/-- Regime-switched child-router Feistel involution on
`Fin (2 ^ branchBits ℓ) × Fin (routerRightUniv ℓ)`. -/
noncomputable def routerPerm (ℓ : ℕ) (θ : P.RouterSeed ℓ) :
    Equiv.Perm (Fin (2 ^ P.branchBits ℓ) × Fin (P.routerRightUniv ℓ)) :=
  FeistelPerm.feistelPairEquiv (P.routerRound ℓ θ)

@[simp]
theorem routerPerm_apply (ℓ : ℕ) (θ : P.RouterSeed ℓ)
    (x : Fin (2 ^ P.branchBits ℓ) × Fin (P.routerRightUniv ℓ)) :
    P.routerPerm ℓ θ x = FeistelPerm.feistelPair (P.routerRound ℓ θ) x := by rfl

@[simp]
theorem routerPerm_symm (ℓ : ℕ) (θ : P.RouterSeed ℓ) :
    (P.routerPerm ℓ θ).symm = P.routerPerm ℓ θ := by rfl

theorem routerPerm_involutive (ℓ : ℕ) (θ : P.RouterSeed ℓ) :
    Function.Involutive (P.routerPerm ℓ θ) :=
  FeistelPerm.feistelPair_involutive (P.routerRound ℓ θ)

private theorem nFloor_le_two_mul_of_nLow_le (hcr : P.ConcentrationReady) {ℓ m : ℕ}
    (hℓ : ℓ ≤ P.depth) (hlo : P.nLow ℓ ≤ m) :
    P.nFloor ℓ ≤ 2 * m := by
  rcases Nat.eq_zero_or_pos ℓ with rfl | hpos
  · have h6 := hcr.six_le_nFloor 0 (Nat.zero_le _)
    have h0 := P.nFloor_zero
    simp only [nLow, ↓reduceIte] at hlo
    omega
  · have h2d := hcr.two_mul_delta_le_nFloor ℓ hpos hℓ
    dsimp only [nLow] at hlo
    rw [ite_eq_right hpos.ne'] at hlo
    omega

open scoped Classical in
/-- **Unified child-router bucket-load concentration (`Lemma 5.1(c)` across both regimes)**:
for any level `0 ≤ ℓ < depth` and input set `S` with `nLow ℓ ≤ #S ≤ nHigh ℓ`, under
`P.ConcentrationReady`, at most a `1 / (nFloor ℓ) ^ 2` fraction of seeds in `P.RouterSeed ℓ` let
any child bucket load fall outside `[nLow (ℓ + 1), nHigh (ℓ + 1)]` ([LiLiangYuZhou2024, Section
5.4, Lemma 5.1(c)]; [arXiv:2310.20536v1](https://arxiv.org/abs/2310.20536v1), PDF p. 32 /
printed p. 31). -/
theorem dens_routerRound_outside_bounds_le (hcr : P.ConcentrationReady) {ℓ : ℕ}
    (hℓ : ℓ < P.depth)
    (S : Finset (Fin (2 ^ P.branchBits ℓ) × Fin (P.routerRightUniv ℓ)))
    (hlo : P.nLow ℓ ≤ #S) (hhi : #S ≤ P.nHigh ℓ) :
    (dens {θ : P.RouterSeed ℓ |
      ¬ ∀ b : Fin (2 ^ P.branchBits ℓ),
        P.nLow (ℓ + 1) ≤ FeistelPerm.bucketLoad (P.routerRound ℓ θ) S b ∧
          FeistelPerm.bucketLoad (P.routerRound ℓ θ) S b ≤ P.nHigh (ℓ + 1)} : ℝ) ≤
      1 / (P.nFloor ℓ : ℝ) ^ 2 := by
  let s := P.branchBits ℓ
  let T := P.routerRightUniv ℓ
  let μ : ℝ := (#S : ℝ) / (2 ^ s : ℝ)
  let a : ℝ := ((1 : ℝ) / 5) * μ ^ ((2 : ℝ) / 3)
  have hnF_pos : (0 : ℝ) < (P.nFloor ℓ : ℝ) :=
    Nat.cast_pos.mpr (P.nFloor_pos ℓ hℓ.le)
  have h2m : P.nFloor ℓ ≤ 2 * #S := P.nFloor_le_two_mul_of_nLow_le hcr hℓ.le hlo
  have hwin_imp : ∀ f : Fin T → Fin (2 ^ s),
      (∀ b : Fin (2 ^ s), μ - a ≤ (FeistelPerm.bucketLoad f S b : ℝ) ∧
        (FeistelPerm.bucketLoad f S b : ℝ) ≤ μ + a) →
      ∀ b : Fin (2 ^ s),
        P.nLow (ℓ + 1) ≤ FeistelPerm.bucketLoad f S b ∧
          FeistelPerm.bucketLoad f S b ≤ P.nHigh (ℓ + 1) := by
    intro f hf b
    exact hcr.window_contained ℓ hℓ #S (FeistelPerm.bucketLoad f S b) hlo hhi (hf b).1 (hf b).2
  by_cases hdt : P.usesDoubleTabRouter ℓ
  · rw [← Fintype.dens_filter_comp_equiv (P.routerSeedDoubleTabEquiv hdt)]
    have hthresh : FeistelPerm.childRouterThreshold P.epsInv P.alphaInv ≤ #S := hdt.trans hlo
    have hm_mono : FeistelPerm.childRouterHalfInd #S ≤
        FeistelPerm.childRouterHalfInd (P.nHigh ℓ) := by
      rw [FeistelPerm.childRouterHalfInd_eq, FeistelPerm.childRouterHalfInd_eq]
      have hc := Nat.clog_mono_right 2 (max_le_max_right 2 hhi)
      omega
    have hconc : 2 ^ s * (150 * FeistelPerm.childRouterHalfInd #S) ^ 3 ≤ #S :=
      (Nat.mul_le_mul_left (2 ^ s) (Nat.pow_le_pow_left (by omega) 3)).trans
        ((hcr.conc_bound ℓ hℓ).trans hlo)
    have hsub : (Finset.univ.filter fun seed : P.LargeRouterSeed ℓ =>
        ¬ ∀ b : Fin (2 ^ s),
          P.nLow (ℓ + 1) ≤ FeistelPerm.bucketLoad (P.routerRound ℓ
            ((P.routerSeedDoubleTabEquiv hdt) seed)) S b ∧
            FeistelPerm.bucketLoad (P.routerRound ℓ
              ((P.routerSeedDoubleTabEquiv hdt) seed)) S b ≤ P.nHigh (ℓ + 1)) ⊆
        Finset.univ.filter fun seed : P.LargeRouterSeed ℓ =>
          ¬ ∀ b : Fin (2 ^ s),
            μ - a ≤ (FeistelPerm.bucketLoad
              (FeistelPerm.childRouterRound (FeistelPerm.childRouterChars P.epsInv)
                (FeistelPerm.childRouterRep P.epsInv P.alphaInv)
                (FeistelPerm.childRouterCharBits (FeistelPerm.childRouterChars P.epsInv) T)
                s T seed) S b : ℝ) ∧
              (FeistelPerm.bucketLoad
                (FeistelPerm.childRouterRound (FeistelPerm.childRouterChars P.epsInv)
                  (FeistelPerm.childRouterRep P.epsInv P.alphaInv)
                  (FeistelPerm.childRouterCharBits (FeistelPerm.childRouterChars P.epsInv) T)
                  s T seed) S b : ℝ) ≤ μ + a := by
      intro seed hseed
      simp only [mem_filter, Finset.mem_univ, true_and, routerSeedDoubleTabEquiv_apply,
        routerRound] at hseed ⊢
      exact fun hgood => hseed (hwin_imp _ hgood)
    have hbase := FeistelPerm.dens_childRouter_bucketLoad_outside_le_of_threshold
      (hcr.gap_bound ℓ hℓ) S hthresh hconc
    have h4S : (P.nFloor ℓ : ℝ) ^ 2 ≤ 4 * (#S : ℝ) ^ 2 := by
      have hnat : (P.nFloor ℓ) ^ 2 ≤ 4 * #S ^ 2 := by nlinarith
      exact_mod_cast hnat
    exact ((NNRat.cast_le.mpr (dens_le_dens hsub)).trans hbase).trans
      (one_div_le_one_div_of_le (sq_pos_of_pos hnF_pos) h4S)
  · rw [← Fintype.dens_filter_comp_equiv (P.routerSeedTrinomialEquiv hdt)]
    let m_hi := FeistelPerm.childRouterHalfInd (P.nHigh ℓ)
    let L_hi := Nat.clog 2 (max (P.nHigh ℓ) 2)
    have hm_eq : m_hi = 3 * L_hi + 4 := FeistelPerm.childRouterHalfInd_eq (P.nHigh ℓ)
    have hm4 : 4 ≤ m_hi := by omega
    have hm1 : 1 ≤ m_hi := by omega
    have hconc_hi : 2 ^ s * (150 * m_hi) ^ 3 ≤ #S := (hcr.conc_bound ℓ hℓ).trans hlo
    have hS_pos : 1 ≤ #S := by
      have h1 : 1 ≤ 2 ^ s * (150 * m_hi) ^ 3 := Nat.mul_pos (Nat.two_pow_pos s) (by positivity)
      omega
    have hμ_pos : 0 < μ := by dsimp only [μ]; positivity
    let u : ℝ := μ ^ ((1 : ℝ) / 3)
    have hu_pos : 0 < u := Real.rpow_pos_of_pos hμ_pos _
    have hu3 : u ^ 3 = μ := by
      dsimp only [u]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hμ_pos.le]
      norm_num
    have hu2 : μ ^ ((2 : ℝ) / 3) = u ^ 2 := by
      dsimp only [u]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hμ_pos.le]
      norm_num
    have h150_cube : (150 * (m_hi : ℝ)) ^ 3 ≤ u ^ 3 := by
      rw [hu3]
      dsimp only [μ]
      rw [le_div_iff₀ (by positivity), mul_comm]
      exact_mod_cast hconc_hi
    have h150 : 150 * (m_hi : ℝ) ≤ u :=
      (pow_le_pow_iff_left₀ (by positivity) hu_pos.le (by decide : 3 ≠ 0)).mp h150_cube
    have ha_pos : 0 < a := by dsimp only [a]; positivity
    have hm_real : (4 : ℝ) ≤ m_hi := by exact_mod_cast hm4
    have hmμ : 2 * (m_hi : ℝ) ≤ 3 * μ := by
      rw [← hu3]
      nlinarith [sq_nonneg u]
    have hrat : 3 * (m_hi : ℝ) * μ / a ^ 2 ≤ (1 : ℝ) / 2 := by
      rw [div_le_iff₀ (pow_pos ha_pos 2)]
      have ha2 : a ^ 2 = ((1 : ℝ) / 25) * u ^ 4 := by dsimp only [a]; rw [hu2]; ring
      rw [ha2, ← hu3]
      nlinarith [pow_pos hu_pos 3]
    have hkw : IsKWiseIndependentHash (2 * m_hi)
        (trinomialPolyHash (trinomialStep T s) (2 * m_hi) T s) :=
      isKWiseIndependentHash_trinomialPolyHash (le_two_pow_trinomialDeg T s) (le_trinomialDeg T s)
    have hsub : (Finset.univ.filter fun seed : P.SmallRouterSeed ℓ =>
        ¬ ∀ b : Fin (2 ^ s),
          P.nLow (ℓ + 1) ≤ FeistelPerm.bucketLoad (P.routerRound ℓ
            ((P.routerSeedTrinomialEquiv hdt) seed)) S b ∧
            FeistelPerm.bucketLoad (P.routerRound ℓ
              ((P.routerSeedTrinomialEquiv hdt) seed)) S b ≤ P.nHigh (ℓ + 1)) ⊆
        Finset.univ.filter fun seed : P.SmallRouterSeed ℓ => ∃ b : Fin (2 ^ s),
          a ≤ |(FeistelPerm.bucketLoad
            (trinomialPolyHash (trinomialStep T s) (2 * m_hi) T s seed) S b : ℝ) - μ| := by
      intro seed hseed
      simp only [mem_filter, Finset.mem_univ, true_and, routerSeedTrinomialEquiv_apply,
        routerRound] at hseed ⊢
      by_contra hno
      simp only [not_exists, not_le] at hno
      refine hseed (hwin_imp _ fun b => ?_)
      have hb := abs_lt.mp (hno b)
      exact ⟨by linarith, by linarith⟩
    have htail := FeistelPerm.dens_exists_bucketLoad_sub_ge_le hm1 hkw S hmμ ha_pos
    have h2s_le : 2 ^ s ≤ 2 ^ L_hi := by
      calc 2 ^ s ≤ 2 ^ s * (150 * m_hi) ^ 3 :=
            Nat.le_mul_of_pos_right _ (by positivity)
        _ ≤ #S := hconc_hi
        _ ≤ max (P.nHigh ℓ) 2 := hhi.trans (le_max_left _ 2)
        _ ≤ 2 ^ L_hi := Nat.le_pow_clog Nat.one_lt_two _
    have hnF_le : P.nFloor ℓ ≤ 2 ^ L_hi := by
      have hnF_hi : P.nFloor ℓ ≤ P.nHigh ℓ := by
        dsimp only [nHigh]
        rcases Nat.eq_zero_or_pos ℓ with rfl | hpos
        · simp [P.nFloor_zero]
        · rw [ite_eq_right hpos.ne']; omega
      exact (hnF_hi.trans (le_max_left _ 2)).trans (Nat.le_pow_clog Nat.one_lt_two _)
    have hpow_nat : 2 ^ (s + 1) * (P.nFloor ℓ) ^ 2 ≤ 2 ^ m_hi := by
      calc 2 ^ (s + 1) * (P.nFloor ℓ) ^ 2
          = 2 * 2 ^ s * (P.nFloor ℓ) ^ 2 := by rw [Nat.pow_succ']
        _ ≤ 2 * 2 ^ L_hi * (2 ^ L_hi) ^ 2 :=
            Nat.mul_le_mul (Nat.mul_le_mul_left 2 h2s_le) (Nat.pow_le_pow_left hnF_le 2)
        _ = 2 ^ (3 * L_hi + 1) := by
            rw [← Nat.pow_mul, ← Nat.pow_succ', ← Nat.pow_add]
            congr 1; omega
        _ ≤ 2 ^ m_hi :=
            Nat.pow_le_pow_right Nat.two_pos (by omega)
    have hpow_real : (2 ^ (s + 1) : ℝ) * ((1 : ℝ) / 2) ^ m_hi ≤
        1 / (P.nFloor ℓ : ℝ) ^ 2 := by
      rw [one_div_pow, mul_one_div, div_le_div_iff₀ (by positivity) (sq_pos_of_pos hnF_pos),
        one_mul]
      exact_mod_cast hpow_nat
    exact (((NNRat.cast_le.mpr (dens_le_dens hsub)).trans htail).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hrat m_hi)
        (by positivity))).trans hpow_real

/-! ## Section 2: Grouped per-node hash seeds `g_u` and unified `3 / n_ℓ ^ 2` bound -/

/-- Level-`ℓ` primitive key-ID domain (`Section 5.5` input `x_prim` to `g_u`):
`Fin (2 ^ branchBits 0) × Fin (routerRightUniv 0)` at `ℓ = 0`, and
`Fin (2 ^ idBits ℓ) × Fin (idCompRightUniv ℓ)` at `ℓ ≥ 1`. -/
abbrev PrimId (P : TreeSchedule) : ℕ → Type
  | 0 => Fin (2 ^ P.branchBits 0) × Fin (P.routerRightUniv 0)
  | ℓ + 1 => Fin (2 ^ P.idBits (ℓ + 1)) × Fin (P.idCompRightUniv (ℓ + 1))

instance instFintypePrimId (ℓ : ℕ) : Fintype (P.PrimId ℓ) := by
  cases ℓ <;> dsimp only [PrimId] <;> infer_instance

instance instDecidableEqPrimId (ℓ : ℕ) : DecidableEq (P.PrimId ℓ) := by
  cases ℓ <;> dsimp only [PrimId] <;> infer_instance

/-- Grouped per-node hash seed `g_u ∈ G_ℓ` (`Section 5.5`, PDF p. 34 / printed p. 33):
`RouterSeed 0` at `ℓ = 0`, `(IdCompressorSeed, RouterSeed ℓ)` for `1 ≤ ℓ < depth`, and
`IdCompressorSeed` at leaf level `ℓ ≥ depth`. -/
inductive NodeSeed (P : TreeSchedule) : ℕ → Type
  | top (router : P.RouterSeed 0) : NodeSeed P 0
  | inner {ℓ : ℕ} (hlt : ℓ + 1 < P.depth)
      (idSeed : FeistelPerm.IdCompressorSeed (P.idBits (ℓ + 1)) (P.idCompRightUniv (ℓ + 1)))
      (router : P.RouterSeed (ℓ + 1)) : NodeSeed P (ℓ + 1)
  | leaf {ℓ : ℕ} (hge : ¬ (ℓ + 1 < P.depth))
      (idSeed : FeistelPerm.IdCompressorSeed (P.idBits (ℓ + 1)) (P.idCompRightUniv (ℓ + 1))) :
      NodeSeed P (ℓ + 1)
  deriving DecidableEq

/-- Equivalence `RouterSeed 0 ≃ NodeSeed 0` at the top router. -/
def nodeSeedZeroEquiv : P.RouterSeed 0 ≃ P.NodeSeed 0 where
  toFun := NodeSeed.top
  invFun | .top r => r
  left_inv _ := rfl
  right_inv | .top _ => rfl

/-- Equivalence `(IdCompressorSeed × RouterSeed) ≃ NodeSeed (ℓ + 1)` for `ℓ + 1 < depth`. -/
def nodeSeedInnerEquiv {ℓ : ℕ} (hlt : ℓ + 1 < P.depth) :
    (FeistelPerm.IdCompressorSeed (P.idBits (ℓ + 1)) (P.idCompRightUniv (ℓ + 1)) ×
      P.RouterSeed (ℓ + 1)) ≃ P.NodeSeed (ℓ + 1) where
  toFun p := .inner hlt p.1 p.2
  invFun
    | .inner _ idS r => (idS, r)
    | .leaf hge _ => False.elim (hge hlt)
  left_inv _ := rfl
  right_inv
    | .inner _ _ _ => rfl
    | .leaf hge _ => False.elim (hge hlt)

/-- Equivalence `IdCompressorSeed ≃ NodeSeed (ℓ + 1)` for `¬ (ℓ + 1 < depth)`. -/
def nodeSeedLeafEquiv {ℓ : ℕ} (hge : ¬ (ℓ + 1 < P.depth)) :
    FeistelPerm.IdCompressorSeed (P.idBits (ℓ + 1)) (P.idCompRightUniv (ℓ + 1)) ≃
      P.NodeSeed (ℓ + 1) where
  toFun idS := .leaf hge idS
  invFun
    | .inner hlt _ _ => False.elim (hge hlt)
    | .leaf _ idS => idS
  left_inv _ := rfl
  right_inv
    | .inner hlt _ _ => False.elim (hge hlt)
    | .leaf _ _ => rfl

@[simp]
theorem nodeSeedZeroEquiv_apply (r : P.RouterSeed 0) :
    P.nodeSeedZeroEquiv r = .top r := by rfl

@[simp]
theorem nodeSeedInnerEquiv_apply {ℓ : ℕ} (hlt : ℓ + 1 < P.depth)
    (p : FeistelPerm.IdCompressorSeed (P.idBits (ℓ + 1)) (P.idCompRightUniv (ℓ + 1)) ×
      P.RouterSeed (ℓ + 1)) :
    P.nodeSeedInnerEquiv hlt p = .inner hlt p.1 p.2 := by rfl

@[simp]
theorem nodeSeedLeafEquiv_apply {ℓ : ℕ} (hge : ¬ (ℓ + 1 < P.depth))
    (idS : FeistelPerm.IdCompressorSeed (P.idBits (ℓ + 1)) (P.idCompRightUniv (ℓ + 1))) :
    P.nodeSeedLeafEquiv hge idS = .leaf hge idS := by rfl

instance instFintypeNodeSeed : ∀ ℓ, Fintype (P.NodeSeed ℓ)
  | 0 => Fintype.ofEquiv _ P.nodeSeedZeroEquiv
  | ℓ + 1 =>
    if hlt : ℓ + 1 < P.depth then
      Fintype.ofEquiv _ (P.nodeSeedInnerEquiv hlt)
    else
      Fintype.ofEquiv _ (P.nodeSeedLeafEquiv hlt)

instance instInhabitedNodeSeed : ∀ ℓ, Inhabited (P.NodeSeed ℓ)
  | 0 => ⟨.top default⟩
  | ℓ + 1 =>
    if hlt : ℓ + 1 < P.depth then
      ⟨.inner hlt (fun _ => ⟨0, Nat.two_pow_pos _⟩) default⟩
    else
      ⟨.leaf hlt fun _ => ⟨0, Nat.two_pow_pos _⟩⟩

/-- `NodeSeed P ℓ` has exact cardinality `2 ^ P.nodeHashSeedBits ℓ`. -/
theorem card_nodeSeed (ℓ : ℕ) :
    Fintype.card (P.NodeSeed ℓ) = 2 ^ P.nodeHashSeedBits ℓ := by
  cases ℓ with
  | zero =>
    rw [← Fintype.card_congr P.nodeSeedZeroEquiv, P.card_routerSeed 0]
    rfl
  | succ j =>
    dsimp only [nodeHashSeedBits]
    rw [ite_eq_right (Nat.succ_ne_zero j)]
    by_cases hlt : j + 1 < P.depth
    · rw [ite_eq_left hlt, ← Fintype.card_congr (P.nodeSeedInnerEquiv hlt), Fintype.card_prod,
        FeistelPerm.card_idCompressorSeed, P.card_routerSeed (j + 1), ← Nat.pow_add, Nat.add_comm]
    · rw [ite_eq_right hlt, Nat.zero_add, ← Fintype.card_congr (P.nodeSeedLeafEquiv hlt),
        FeistelPerm.card_idCompressorSeed]

/-- Extract the ID-compressor seed component of `g : P.NodeSeed (ℓ + 1)`. -/
@[expose]
def idSeedOfNodeSeed {ℓ : ℕ} :
    P.NodeSeed (ℓ + 1) →
      FeistelPerm.IdCompressorSeed (P.idBits (ℓ + 1)) (P.idCompRightUniv (ℓ + 1))
  | .inner _ idS _ => idS
  | .leaf _ idS => idS

/-- Extract the child-router seed component of `g : P.NodeSeed ℓ` when `ℓ < P.depth`. -/
@[expose]
def routerSeedOfNodeSeed : ∀ {ℓ : ℕ}, ℓ < P.depth → P.NodeSeed ℓ → P.RouterSeed ℓ
  | 0, _, .top r => r
  | _ + 1, _, .inner _ _ r => r
  | _ + 1, hlt, .leaf hge _ => False.elim (hge hlt)

/-- Node-seed goodness predicate (`Section 5.5` "does not fail", PDF p. 34 / printed p. 33):
no ID collision on `S` (`ℓ ≥ 1`), and every child bucket load lies in
`[nLow (ℓ + 1), nHigh (ℓ + 1)]` (`ℓ < depth`). -/
@[expose]
def IsGoodNodeSeed : ∀ ℓ : ℕ, P.NodeSeed ℓ → Finset (P.PrimId ℓ) → Prop
  | 0, .top router, S =>
    ∀ b : Fin (2 ^ P.branchBits 0),
      P.nLow 1 ≤ FeistelPerm.bucketLoad (P.routerRound 0 router) S b ∧
        FeistelPerm.bucketLoad (P.routerRound 0 router) S b ≤ P.nHigh 1
  | ℓ + 1, .inner hlt idSeed router, S =>
    have hsL : P.branchBits (ℓ + 1) ≤ P.idBits (ℓ + 1) := by
      have := P.idBits_step_le (ℓ + 1) (by omega) hlt
      omega
    Set.InjOn (FeistelPerm.idCompressorHead (P.idBits (ℓ + 1)) (P.idCompRightUniv (ℓ + 1)) idSeed)
        (S : Set (P.PrimId (ℓ + 1))) ∧
      ∀ b : Fin (2 ^ P.branchBits (ℓ + 1)),
        let S_id := (S.image
          (FeistelPerm.idCompressorHead (P.idBits (ℓ + 1)) (P.idCompRightUniv (ℓ + 1)) idSeed)).map
          (FeistelPerm.bitDomainEquiv hsL).toEmbedding
        P.nLow (ℓ + 2) ≤ FeistelPerm.bucketLoad (P.routerRound (ℓ + 1) router) S_id b ∧
          FeistelPerm.bucketLoad (P.routerRound (ℓ + 1) router) S_id b ≤ P.nHigh (ℓ + 2)
  | ℓ + 1, .leaf _ idSeed, S =>
    Set.InjOn (FeistelPerm.idCompressorHead (P.idBits (ℓ + 1)) (P.idCompRightUniv (ℓ + 1)) idSeed)
      (S : Set (P.PrimId (ℓ + 1)))

open scoped Classical in
/-- **Unified `3 / n_ℓ ^ 2` single-set node-seed failure bound (`Section 5.5`)**:
for any `0 ≤ ℓ ≤ depth` and primitive-ID set `S` with `nLow ℓ ≤ #S ≤ nHigh ℓ`, under
`P.ConcentrationReady`, a uniform seed `g : P.NodeSeed ℓ` fails on `S` with density at most
`3 / (nFloor ℓ) ^ 2` ([LiLiangYuZhou2024, Section 5.5];
[arXiv:2310.20536v1](https://arxiv.org/abs/2310.20536v1), PDF p. 34 / printed p. 33). -/
theorem dens_not_isGoodNodeSeed_le (hcr : P.ConcentrationReady) {ℓ : ℕ} (hℓ : ℓ ≤ P.depth)
    (S : Finset (P.PrimId ℓ)) (hlo : P.nLow ℓ ≤ #S) (hhi : #S ≤ P.nHigh ℓ) :
    (dens {g : P.NodeSeed ℓ | ¬ P.IsGoodNodeSeed ℓ g S} : ℝ) ≤
      3 / (P.nFloor ℓ : ℝ) ^ 2 := by
  have hnF_pos : (0 : ℝ) < (P.nFloor ℓ : ℝ) := Nat.cast_pos.mpr (P.nFloor_pos ℓ hℓ)
  cases ℓ with
  | zero =>
    rw [← Fintype.dens_filter_comp_equiv P.nodeSeedZeroEquiv]
    have hsub0 : (Finset.univ.filter fun a : P.RouterSeed 0 =>
        ¬ P.IsGoodNodeSeed 0 (P.nodeSeedZeroEquiv a) S) ⊆
        Finset.univ.filter fun θ : P.RouterSeed 0 =>
          ¬ ∀ b : Fin (2 ^ P.branchBits 0),
            P.nLow 1 ≤ FeistelPerm.bucketLoad (P.routerRound 0 θ) S b ∧
              FeistelPerm.bucketLoad (P.routerRound 0 θ) S b ≤ P.nHigh 1 := by
      intro θ hθ
      simp only [mem_filter, Finset.mem_univ, true_and, nodeSeedZeroEquiv_apply,
        IsGoodNodeSeed] at hθ ⊢
      exact hθ
    have h0 := P.dens_routerRound_outside_bounds_le hcr (Nat.lt_of_lt_of_le Nat.zero_lt_two
      P.two_le_depth) S hlo hhi
    calc (dens _ : ℝ)
        ≤ _ := by exact_mod_cast dens_le_dens hsub0
      _ ≤ 1 / (P.nFloor 0 : ℝ) ^ 2 := h0
      _ ≤ 3 / (P.nFloor 0 : ℝ) ^ 2 := by
          rw [div_le_div_iff_of_pos_right (sq_pos_of_pos hnF_pos)]; norm_num
  | succ j =>
    let S0 : Finset (Fin (2 ^ P.idBits (j + 1)) × Fin (P.idCompRightUniv (j + 1))) := S
    have hid_le := FeistelPerm.dens_not_injOn_idCompressorHead_le_two_div_sq S0 hhi
      (P.nFloor_pos (j + 1) hℓ) (hcr.id_collision_bound (j + 1) (by omega) hℓ)
    by_cases hlt : j + 1 < P.depth
    · rw [← Fintype.dens_filter_comp_equiv (P.nodeSeedInnerEquiv hlt)]
      have hsL : P.branchBits (j + 1) ≤ P.idBits (j + 1) := by
        have := P.idBits_step_le (j + 1) (by omega) hlt
        omega
      have hprod := dens_prod_le_add_of_good
        (good := fun idS : FeistelPerm.IdCompressorSeed (P.idBits (j + 1))
          (P.idCompRightUniv (j + 1)) =>
          Set.InjOn (FeistelPerm.idCompressorHead (P.idBits (j + 1)) (P.idCompRightUniv (j + 1))
            idS) (S0 : Set (Fin (2 ^ P.idBits (j + 1)) × Fin (P.idCompRightUniv (j + 1)))))
        (bad := fun p : FeistelPerm.IdCompressorSeed (P.idBits (j + 1))
          (P.idCompRightUniv (j + 1)) × P.RouterSeed (j + 1) =>
          ¬ P.IsGoodNodeSeed (j + 1) (.inner hlt p.1 p.2) S)
        (δ := 2 / (P.nFloor (j + 1) : ℝ) ^ 2)
        (p := 1 / (P.nFloor (j + 1) : ℝ) ^ 2)
        hid_le
        (by positivity)
        (fun idS hinj => by
          let S_id := (S0.image
            (FeistelPerm.idCompressorHead (P.idBits (j + 1)) (P.idCompRightUniv (j + 1)) idS)).map
            (FeistelPerm.bitDomainEquiv hsL).toEmbedding
          have hcard_id : #S_id = #S := (card_map _).trans (card_image_of_injOn hinj)
          have hsub_r : (Finset.univ.filter fun r : P.RouterSeed (j + 1) =>
              ¬ P.IsGoodNodeSeed (j + 1) (.inner hlt idS r) S) ⊆
              Finset.univ.filter fun r : P.RouterSeed (j + 1) =>
                ¬ ∀ b : Fin (2 ^ P.branchBits (j + 1)),
                  P.nLow (j + 2) ≤ FeistelPerm.bucketLoad (P.routerRound (j + 1) r) S_id b ∧
                    FeistelPerm.bucketLoad (P.routerRound (j + 1) r) S_id b ≤ P.nHigh (j + 2) := by
            intro r hr
            simp only [mem_filter, Finset.mem_univ, true_and, IsGoodNodeSeed] at hr ⊢
            exact fun hall => hr ⟨hinj, hall⟩
          exact (NNRat.cast_le.mpr (dens_le_dens hsub_r)).trans
            (P.dens_routerRound_outside_bounds_le hcr hlt S_id
              (hcard_id.symm ▸ hlo) (hcard_id.symm ▸ hhi)))
      have hsub_in : (Finset.univ.filter
          fun p : FeistelPerm.IdCompressorSeed (P.idBits (j + 1))
            (P.idCompRightUniv (j + 1)) × P.RouterSeed (j + 1) =>
            ¬ P.IsGoodNodeSeed (j + 1) ((P.nodeSeedInnerEquiv hlt) p) S) ⊆
          Finset.univ.filter
            fun p : FeistelPerm.IdCompressorSeed (P.idBits (j + 1))
              (P.idCompRightUniv (j + 1)) × P.RouterSeed (j + 1) =>
              ¬ P.IsGoodNodeSeed (j + 1) (.inner hlt p.1 p.2) S := by
        intro p hp
        simp only [mem_filter, Finset.mem_univ, true_and, nodeSeedInnerEquiv_apply] at hp ⊢
        exact hp
      calc (dens _ : ℝ)
          ≤ _ := by exact_mod_cast dens_le_dens hsub_in
        _ ≤ 2 / (P.nFloor (j + 1) : ℝ) ^ 2 + 1 / (P.nFloor (j + 1) : ℝ) ^ 2 := hprod
        _ = 3 / (P.nFloor (j + 1) : ℝ) ^ 2 := by ring
    · rw [← Fintype.dens_filter_comp_equiv (P.nodeSeedLeafEquiv hlt)]
      have hsub_lf : (Finset.univ.filter fun idS : FeistelPerm.IdCompressorSeed (P.idBits (j + 1))
          (P.idCompRightUniv (j + 1)) =>
          ¬ P.IsGoodNodeSeed (j + 1) ((P.nodeSeedLeafEquiv hlt) idS) S) ⊆
          Finset.univ.filter fun θ : FeistelPerm.IdCompressorSeed (P.idBits (j + 1))
            (P.idCompRightUniv (j + 1)) =>
            ¬ Set.InjOn
              (FeistelPerm.idCompressorHead (P.idBits (j + 1)) (P.idCompRightUniv (j + 1)) θ)
              (S0 : Set (Fin (2 ^ P.idBits (j + 1)) × Fin (P.idCompRightUniv (j + 1)))) := by
        intro θ hθ
        simp only [mem_filter, Finset.mem_univ, true_and, nodeSeedLeafEquiv_apply,
          IsGoodNodeSeed] at hθ ⊢
        exact hθ
      calc (dens _ : ℝ)
          ≤ _ := by exact_mod_cast dens_le_dens hsub_lf
        _ ≤ 2 / (P.nFloor (j + 1) : ℝ) ^ 2 := hid_le
        _ ≤ 3 / (P.nFloor (j + 1) : ℝ) ^ 2 := by
            rw [div_le_div_iff_of_pos_right (sq_pos_of_pos hnF_pos)]; norm_num

open scoped Classical in
/-- Under `P.ConcentrationReady`, at least `(1 - 3 / n_ℓ ^ 2) ≥ 11 / 12` of all seeds in
`P.NodeSeed ℓ` satisfy `IsGoodNodeSeed ℓ g S`. -/
theorem card_isGoodNodeSeed_ge (hcr : P.ConcentrationReady) {ℓ : ℕ} (hℓ : ℓ ≤ P.depth)
    (S : Finset (P.PrimId ℓ)) (hlo : P.nLow ℓ ≤ #S) (hhi : #S ≤ P.nHigh ℓ) :
    ((P.nFloor ℓ) ^ 2 - 3) * Fintype.card (P.NodeSeed ℓ) ≤
      (P.nFloor ℓ) ^ 2 * #{g : P.NodeSeed ℓ | P.IsGoodNodeSeed ℓ g S} := by
  have hbad := P.dens_not_isGoodNodeSeed_le hcr hℓ S hlo hhi
  rw [dens_eq_card_div_card, NNRat.cast_div, NNRat.cast_natCast, NNRat.cast_natCast] at hbad
  have hN_pos : (0 : ℝ) < (Fintype.card (P.NodeSeed ℓ) : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hnF6 := hcr.six_le_nFloor ℓ hℓ
  have hsq_pos : (0 : ℝ) < (P.nFloor ℓ : ℝ) ^ 2 := by positivity
  rw [div_le_div_iff₀ hN_pos hsq_pos] at hbad
  have hpart : #{g : P.NodeSeed ℓ | P.IsGoodNodeSeed ℓ g S} +
      #{g : P.NodeSeed ℓ | ¬ P.IsGoodNodeSeed ℓ g S} = Fintype.card (P.NodeSeed ℓ) :=
    card_filter_add_card_filter_not _
  have hpart_real : (#{g : P.NodeSeed ℓ | P.IsGoodNodeSeed ℓ g S} : ℝ) +
      (#{g : P.NodeSeed ℓ | ¬ P.IsGoodNodeSeed ℓ g S} : ℝ) =
      (Fintype.card (P.NodeSeed ℓ) : ℝ) := by exact_mod_cast hpart
  have h36 : 36 ≤ (P.nFloor ℓ) ^ 2 := by nlinarith
  have hsub_ge : 3 ≤ (P.nFloor ℓ) ^ 2 := by omega
  have hgoal_real : (((P.nFloor ℓ) ^ 2 - 3 : ℕ) : ℝ) * (Fintype.card (P.NodeSeed ℓ) : ℝ) ≤
      ((P.nFloor ℓ : ℝ) ^ 2) * (#{g : P.NodeSeed ℓ | P.IsGoodNodeSeed ℓ g S} : ℝ) := by
    rw [Nat.cast_sub hsub_ge, Nat.cast_pow, Nat.cast_ofNat]
    nlinarith
  exact_mod_cast hgoal_real

/-- Every valid primitive-ID set `S` (`nLow ℓ ≤ #S ≤ nHigh ℓ`) admits at least one good seed
`g : P.NodeSeed ℓ`. -/
theorem exists_isGoodNodeSeed (hcr : P.ConcentrationReady) {ℓ : ℕ} (hℓ : ℓ ≤ P.depth)
    (S : Finset (P.PrimId ℓ)) (hlo : P.nLow ℓ ≤ #S) (hhi : #S ≤ P.nHigh ℓ) :
    ∃ g : P.NodeSeed ℓ, P.IsGoodNodeSeed ℓ g S := by
  classical
  have hge := P.card_isGoodNodeSeed_ge hcr hℓ S hlo hhi
  have hnF6 := hcr.six_le_nFloor ℓ hℓ
  have h36 : 36 ≤ (P.nFloor ℓ) ^ 2 := by nlinarith
  have hcard_pos : 0 < Fintype.card (P.NodeSeed ℓ) := Fintype.card_pos
  have hgood_pos : 0 < #{g : P.NodeSeed ℓ | P.IsGoodNodeSeed ℓ g S} := by
    have h33 : 33 ≤ (P.nFloor ℓ) ^ 2 - 3 := by omega
    have lhs_pos : 0 < ((P.nFloor ℓ) ^ 2 - 3) * Fintype.card (P.NodeSeed ℓ) :=
      Nat.mul_pos (by omega) hcard_pos
    exact Nat.pos_of_mul_pos_left (lhs_pos.trans_le hge)
  obtain ⟨g, hg⟩ := card_pos.mp hgood_pos
  exact ⟨g, (mem_filter.mp hg).2⟩

/-- Every pair of valid primitive-ID sets `S₁, S₂` (`nLow ℓ ≤ #Sᵢ ≤ nHigh ℓ`) admits a single
seed `g : P.NodeSeed ℓ` simultaneously satisfying `IsGoodNodeSeed` on both `S₁` and `S₂`. -/
theorem exists_isGoodNodeSeed_pair (hcr : P.ConcentrationReady) {ℓ : ℕ} (hℓ : ℓ ≤ P.depth)
    (S₁ S₂ : Finset (P.PrimId ℓ))
    (hlo₁ : P.nLow ℓ ≤ #S₁) (hhi₁ : #S₁ ≤ P.nHigh ℓ)
    (hlo₂ : P.nLow ℓ ≤ #S₂) (hhi₂ : #S₂ ≤ P.nHigh ℓ) :
    ∃ g : P.NodeSeed ℓ, P.IsGoodNodeSeed ℓ g S₁ ∧ P.IsGoodNodeSeed ℓ g S₂ := by
  classical
  by_contra hno
  simp only [not_exists, not_and] at hno
  have huniv : (Finset.univ : Finset (P.NodeSeed ℓ)) ⊆
      (Finset.univ.filter fun g => ¬ P.IsGoodNodeSeed ℓ g S₁) ∪
        (Finset.univ.filter fun g => ¬ P.IsGoodNodeSeed ℓ g S₂) := by
    intro g _
    rw [mem_union, mem_filter, mem_filter]
    by_cases hg₁ : P.IsGoodNodeSeed ℓ g S₁
    · exact Or.inr ⟨mem_univ g, hno g hg₁⟩
    · exact Or.inl ⟨mem_univ g, hg₁⟩
  have h1 := P.card_isGoodNodeSeed_ge hcr hℓ S₁ hlo₁ hhi₁
  have h2 := P.card_isGoodNodeSeed_ge hcr hℓ S₂ hlo₂ hhi₂
  have hp1 : #{g : P.NodeSeed ℓ | P.IsGoodNodeSeed ℓ g S₁} +
      #{g : P.NodeSeed ℓ | ¬ P.IsGoodNodeSeed ℓ g S₁} = Fintype.card (P.NodeSeed ℓ) :=
    card_filter_add_card_filter_not _
  have hp2 : #{g : P.NodeSeed ℓ | P.IsGoodNodeSeed ℓ g S₂} +
      #{g : P.NodeSeed ℓ | ¬ P.IsGoodNodeSeed ℓ g S₂} = Fintype.card (P.NodeSeed ℓ) :=
    card_filter_add_card_filter_not _
  have hcard_le : Fintype.card (P.NodeSeed ℓ) ≤
      #{g : P.NodeSeed ℓ | ¬ P.IsGoodNodeSeed ℓ g S₁} +
        #{g : P.NodeSeed ℓ | ¬ P.IsGoodNodeSeed ℓ g S₂} := by
    rw [← Finset.card_univ]
    exact (card_le_card huniv).trans (card_union_le _ _)
  have hnF6 := hcr.six_le_nFloor ℓ hℓ
  have h36 : 36 ≤ (P.nFloor ℓ) ^ 2 := by nlinarith
  have hc_pos : 0 < Fintype.card (P.NodeSeed ℓ) := Fintype.card_pos
  have hsub : ((P.nFloor ℓ) ^ 2 - 3) * Fintype.card (P.NodeSeed ℓ) +
      3 * Fintype.card (P.NodeSeed ℓ) = (P.nFloor ℓ) ^ 2 * Fintype.card (P.NodeSeed ℓ) := by
    rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
  have hd1 : (P.nFloor ℓ) ^ 2 * #{g : P.NodeSeed ℓ | P.IsGoodNodeSeed ℓ g S₁} +
      (P.nFloor ℓ) ^ 2 * #{g : P.NodeSeed ℓ | ¬ P.IsGoodNodeSeed ℓ g S₁} =
      (P.nFloor ℓ) ^ 2 * Fintype.card (P.NodeSeed ℓ) := by
    rw [← Nat.mul_add, hp1]
  have hd2 : (P.nFloor ℓ) ^ 2 * #{g : P.NodeSeed ℓ | P.IsGoodNodeSeed ℓ g S₂} +
      (P.nFloor ℓ) ^ 2 * #{g : P.NodeSeed ℓ | ¬ P.IsGoodNodeSeed ℓ g S₂} =
      (P.nFloor ℓ) ^ 2 * Fintype.card (P.NodeSeed ℓ) := by
    rw [← Nat.mul_add, hp2]
  have hb1 : (P.nFloor ℓ) ^ 2 * #{g : P.NodeSeed ℓ | ¬ P.IsGoodNodeSeed ℓ g S₁} ≤
      3 * Fintype.card (P.NodeSeed ℓ) := by omega
  have hb2 : (P.nFloor ℓ) ^ 2 * #{g : P.NodeSeed ℓ | ¬ P.IsGoodNodeSeed ℓ g S₂} ≤
      3 * Fintype.card (P.NodeSeed ℓ) := by omega
  have htot : (P.nFloor ℓ) ^ 2 * Fintype.card (P.NodeSeed ℓ) ≤
      6 * Fintype.card (P.NodeSeed ℓ) := by
    calc (P.nFloor ℓ) ^ 2 * Fintype.card (P.NodeSeed ℓ)
        ≤ (P.nFloor ℓ) ^ 2 * (#{g : P.NodeSeed ℓ | ¬ P.IsGoodNodeSeed ℓ g S₁} +
            #{g : P.NodeSeed ℓ | ¬ P.IsGoodNodeSeed ℓ g S₂}) := Nat.mul_le_mul_left _ hcard_le
      _ = (P.nFloor ℓ) ^ 2 * #{g : P.NodeSeed ℓ | ¬ P.IsGoodNodeSeed ℓ g S₁} +
            (P.nFloor ℓ) ^ 2 * #{g : P.NodeSeed ℓ | ¬ P.IsGoodNodeSeed ℓ g S₂} := Nat.mul_add ..
      _ ≤ 6 * Fintype.card (P.NodeSeed ℓ) := by omega
  nlinarith

end TreeSchedule

end Cslib.DataStructure.Dictionary.SubconstantRedundancy
