/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.FeistelPerm
public import CslibFrontier.Probability.StatisticalDistance.Event
public import CslibFrontier.Probability.UniformEmbedding
import CslibFrontier.Probability.KWiseIndependent.Coupling
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.StatisticalDistance.Coupling
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Unbalanced Naor–Reingold Feistel blocks and Arbitman–Naor–Segev sharding

This module constructs unbalanced 3-round Feistel Naor–Reingold blocks and `t`-round compositions on
`Fin (2 ^ a')` ([NaorReingold1999], Sections 3.2, 5.2, 6, and 8), combines them with the
Arbitman–Naor–Segev 1-round Feistel shard router (`caseBEquiv`, [ArbitmanNaorSegev2010], Section 5.2
construction for intra-shard injectivity and Section 5.4 Claim 5.7 for bin load bounds), and proves
abstract `k`-tuple statistical-distance contraction and intra-shard suffix bijectivity for
`CslibFrontier.DataStructure.Dictionary.KickTree.QuotientPerm`.

## Main definitions

* `Cslib.DataStructure.Dictionary.KickTree.nrHalfLow`,
  `Cslib.DataStructure.Dictionary.KickTree.nrHalfHigh`,
  `Cslib.DataStructure.Dictionary.KickTree.nrSplitEquiv`,
  `Cslib.DataStructure.Dictionary.KickTree.NRBlockFuncs`,
  `Cslib.DataStructure.Dictionary.KickTree.nrBlockEquiv`,
  `Cslib.DataStructure.Dictionary.KickTree.nrComposedEquiv`,
  `Cslib.DataStructure.Dictionary.KickTree.NRBlockSeed`,
  `Cslib.DataStructure.Dictionary.KickTree.nrBlockSeedDist`,
  `Cslib.DataStructure.Dictionary.KickTree.NRComposedSeed`,
  `Cslib.DataStructure.Dictionary.KickTree.nrComposedSeedDist`: unbalanced 3-round Feistel
  Naor–Reingold blocks and composed permutation laws.
* `Cslib.DataStructure.Dictionary.KickTree.CaseBRounds`,
  `Cslib.DataStructure.Dictionary.KickTree.caseBEquiv`,
  `Cslib.DataStructure.Dictionary.KickTree.bucketShard`,
  `Cslib.DataStructure.Dictionary.KickTree.bucketLocal`,
  `Cslib.DataStructure.Dictionary.KickTree.keySuffix`,
  `Cslib.DataStructure.Dictionary.KickTree.caseBShard`,
  `Cslib.DataStructure.Dictionary.KickTree.intraShardSuffixSet`: Case B sharded bijection and
  intra-shard suffix preimage.

## Main results

* `Cslib.DataStructure.Dictionary.KickTree.dist_permTupleKernel_nrBlock_le`,
  `Cslib.DataStructure.Dictionary.KickTree.dist_permTupleKernel_nrComposed_le`: single-block and
  `t`-composed Naor–Reingold `k`-tuple statistical-distance bounds.
* `Cslib.DataStructure.Dictionary.KickTree.injOn_yR_of_caseBShard_eq`,
  `Cslib.DataStructure.Dictionary.KickTree.dist_caseB_shardTuple_le`: intra-shard suffix injectivity
  and abstract Case B shard-tuple statistical-distance transfer.

## References

* [M. Naor and O. Reingold, *On the Construction of Pseudorandom Permutations: Luby–Rackoff
  Revisited*][NaorReingold1999]
* [Y. Arbitman, M. Naor and G. Segev, *Backyard Cuckoo Hashing: Constant Worst-Case Operations
  with a Succinct Representation*][ArbitmanNaorSegev2010]
-/

public section

namespace Cslib.DataStructure.Dictionary.KickTree

open Cslib.DataStructure.Dictionary Cslib.DataStructure.Dictionary.FeistelPerm
open Cslib.Probability Cslib.Probability.PMF Finset Fintype
open scoped BigOperators ENNReal Cslib.Probability.PMF

/-! ## Section 1: Single-block Naor–Reingold Feistel permutations -/

/-- Low-half bit-width `⌊a' / 2⌋` of an unbalanced Naor–Reingold block on `Fin (2 ^ a')`. -/
@[expose] def nrHalfLow (a' : ℕ) : ℕ := a' / 2

/-- High-half bit-width `a' - ⌊a' / 2⌋ = ⌈a' / 2⌉` of an unbalanced Naor–Reingold block. -/
@[expose] def nrHalfHigh (a' : ℕ) : ℕ := a' - a' / 2

theorem nrHalfLow_le (a' : ℕ) : nrHalfLow a' ≤ a' := Nat.div_le_self a' 2

theorem nrHalfLow_add_nrHalfHigh (a' : ℕ) : nrHalfLow a' + nrHalfHigh a' = a' :=
  Nat.add_sub_of_le (nrHalfLow_le a')

theorem nrHalfLow_le_nrHalfHigh (a' : ℕ) : nrHalfLow a' ≤ nrHalfHigh a' := by
  dsimp only [nrHalfLow, nrHalfHigh]; omega

/-- Split `Fin (2 ^ a') ≃ Fin (2 ^ ⌊a' / 2⌋) × Fin (2 ^ ⌈a' / 2⌉)` into low and high halves. -/
@[expose] def nrSplitEquiv (a' : ℕ) :
    Fin (2 ^ a') ≃ Fin (2 ^ nrHalfLow a') × Fin (2 ^ nrHalfHigh a') :=
  bitDomainEquiv (nrHalfLow_le a')

/-- Round-function triple `(f₀, f₁, f₂)` for one unbalanced 3-round Feistel Naor–Reingold block on
`Fin (2 ^ a')` ([NaorReingold1999], Definition 3.1, Section 5.2, and Section 6 Definition 6.1). -/
structure NRBlockFuncs (a' : ℕ) where
  /-- Pre-whitening Feistel round function `Fin (2 ^ ⌊a'/2⌋) → Fin (2 ^ ⌈a'/2⌉)`. -/
  f₀ : Fin (2 ^ nrHalfLow a') → Fin (2 ^ nrHalfHigh a')
  /-- Middle Feistel round function `Fin (2 ^ ⌈a'/2⌉) → Fin (2 ^ ⌊a'/2⌋)`. -/
  f₁ : Fin (2 ^ nrHalfHigh a') → Fin (2 ^ nrHalfLow a')
  /-- Final Feistel round function `Fin (2 ^ ⌊a'/2⌋) → Fin (2 ^ ⌈a'/2⌉)`. -/
  f₂ : Fin (2 ^ nrHalfLow a') → Fin (2 ^ nrHalfHigh a')

/-- Reversing `f₀` and `f₂` in an `NRBlockFuncs` inverts the 3-round Feistel block. -/
@[expose] def NRBlockFuncs.rev {a' : ℕ} (blk : NRBlockFuncs a') : NRBlockFuncs a' :=
  ⟨blk.f₂, blk.f₁, blk.f₀⟩

@[simp] theorem NRBlockFuncs.rev_rev {a' : ℕ} (blk : NRBlockFuncs a') : blk.rev.rev = blk := rfl

/-- Pair-domain 3-round Feistel Naor–Reingold permutation. -/
@[expose] def nrPairBlock {a' : ℕ} (blk : NRBlockFuncs a') :
    Equiv.Perm (Fin (2 ^ nrHalfLow a') × Fin (2 ^ nrHalfHigh a')) :=
  (feistelRightEquiv blk.f₀).trans ((feistelPairEquiv blk.f₁).trans (feistelRightEquiv blk.f₂))

@[simp] theorem nrPairBlock_symm {a' : ℕ} (blk : NRBlockFuncs a') :
    (nrPairBlock blk).symm = nrPairBlock blk.rev :=
  Equiv.ext fun p => by
    simp only [nrPairBlock, NRBlockFuncs.rev, Equiv.symm_trans_apply, Equiv.trans_apply,
      feistelRightEquiv_symm, feistelPairEquiv_symm]

/-- Flat 3-round Feistel Naor–Reingold permutation on `Fin (2 ^ a')`. -/
@[expose] def nrBlockEquiv (a' : ℕ) (blk : NRBlockFuncs a') : Equiv.Perm (Fin (2 ^ a')) :=
  (nrSplitEquiv a').symm.permCongr (nrPairBlock blk)

@[simp] theorem nrBlockEquiv_symm (a' : ℕ) (blk : NRBlockFuncs a') :
    (nrBlockEquiv a' blk).symm = nrBlockEquiv a' blk.rev :=
  Equiv.ext fun u => by
    simp only [nrBlockEquiv, Equiv.permCongr_def, Equiv.symm_trans_apply, Equiv.trans_apply,
      Equiv.symm_symm, nrPairBlock_symm]

/-- Composition of `t` Naor–Reingold blocks on `Fin (2 ^ a')` in index order `0, 1, …, t - 1`. -/
def nrComposedEquiv (a' : ℕ) : (t : ℕ) → (Fin t → NRBlockFuncs a') → Equiv.Perm (Fin (2 ^ a'))
  | 0, _ => Equiv.refl (Fin (2 ^ a'))
  | t + 1, blks =>
    (nrComposedEquiv a' t (fun i => blks i.castSucc)).trans (nrBlockEquiv a' (blks (Fin.last t)))

@[simp] theorem nrComposedEquiv_zero (a' : ℕ) (blks : Fin 0 → NRBlockFuncs a') :
    nrComposedEquiv a' 0 blks = Equiv.refl (Fin (2 ^ a')) := by
  unfold nrComposedEquiv; rfl

@[simp] theorem nrComposedEquiv_succ (a' t : ℕ) (blks : Fin (t + 1) → NRBlockFuncs a') :
    nrComposedEquiv a' (t + 1) blks =
      (nrComposedEquiv a' t (fun i => blks i.castSucc)).trans
        (nrBlockEquiv a' (blks (Fin.last t))) := by
  conv_lhs => unfold nrComposedEquiv

theorem nrComposedEquiv_succ_left (a' : ℕ) :
    ∀ (t : ℕ) (blks : Fin (t + 1) → NRBlockFuncs a'),
      nrComposedEquiv a' (t + 1) blks =
        (nrBlockEquiv a' (blks 0)).trans (nrComposedEquiv a' t (fun i => blks i.succ))
  | 0, _ => Equiv.ext fun u => by simp [nrComposedEquiv]
  | t + 1, blks => by
    have ih := nrComposedEquiv_succ_left a' t (fun i => blks i.castSucc)
    change (nrComposedEquiv a' (t + 1) (fun i => blks i.castSucc)).trans
        (nrBlockEquiv a' (blks (Fin.last (t + 1)))) =
      (nrBlockEquiv a' (blks 0)).trans
        ((nrComposedEquiv a' t (fun i => blks i.castSucc.succ)).trans
          (nrBlockEquiv a' (blks (Fin.last t).succ)))
    rw [ih]
    exact Equiv.ext fun u => by
      simp only [Equiv.trans_apply, Fin.castSucc_zero, Fin.succ_castSucc, Fin.succ_last]

@[simp] theorem nrComposedEquiv_symm (a' : ℕ) :
    ∀ (t : ℕ) (blks : Fin t → NRBlockFuncs a'),
      (nrComposedEquiv a' t blks).symm =
        nrComposedEquiv a' t (fun i => (blks (Fin.rev i)).rev)
  | 0, _ => by unfold nrComposedEquiv; rfl
  | t + 1, blks => by
    rw [nrComposedEquiv_succ_left a' t (fun i => (blks (Fin.rev i)).rev)]
    exact Equiv.ext fun u => by
      simp only [nrComposedEquiv, Equiv.symm_trans_apply, nrBlockEquiv_symm,
        nrComposedEquiv_symm a' t (fun i => blks i.castSucc), Equiv.trans_apply, Fin.rev_zero,
        Fin.rev_succ]

/-- Seed triple `(s₀, s₁, s₂)` for one Naor–Reingold block over seed spaces `ι₀, ι₁, ι₂`. -/
structure NRBlockSeed (ι₀ ι₁ ι₂ : Type*) where
  /-- Pre-whitening round seed. -/
  s₀ : ι₀
  /-- Middle round seed. -/
  s₁ : ι₁
  /-- Final round seed. -/
  s₂ : ι₂

/-- Equivalence between `NRBlockSeed ι₀ ι₁ ι₂` and `ι₀ × ι₁ × ι₂`. -/
def nrBlockSeedEquivProd (ι₀ ι₁ ι₂ : Type*) : NRBlockSeed ι₀ ι₁ ι₂ ≃ ι₀ × ι₁ × ι₂ where
  toFun s := (s.s₀, s.s₁, s.s₂)
  invFun | (s₀, s₁, s₂) => ⟨s₀, s₁, s₂⟩
  left_inv s := by cases s; rfl
  right_inv p := by rcases p with ⟨_, _, _⟩; rfl

instance {ι₀ ι₁ ι₂ : Type*} [Fintype ι₀] [Fintype ι₁] [Fintype ι₂] :
    Fintype (NRBlockSeed ι₀ ι₁ ι₂) :=
  Fintype.ofEquiv (ι₀ × ι₁ × ι₂) (nrBlockSeedEquivProd ι₀ ι₁ ι₂).symm

instance {ι₀ ι₁ ι₂ : Type*} [Nonempty ι₀] [Nonempty ι₁] [Nonempty ι₂] :
    Nonempty (NRBlockSeed ι₀ ι₁ ι₂) :=
  ⟨⟨Classical.arbitrary ι₀, Classical.arbitrary ι₁, Classical.arbitrary ι₂⟩⟩

/-- Random Naor–Reingold block on `Fin (2 ^ a')` induced by uniform independent seeds in
`NRBlockSeed ι₀ ι₁ ι₂`. -/
noncomputable def nrBlockSeedDist {ι₀ ι₁ ι₂ : Type*} [Fintype ι₀] [Nonempty ι₀]
    [Fintype ι₁] [Nonempty ι₁] [Fintype ι₂] [Nonempty ι₂]
    (a' : ℕ)
    (h₀ : ι₀ → Fin (2 ^ nrHalfLow a') → Fin (2 ^ nrHalfHigh a'))
    (h₁ : ι₁ → Fin (2 ^ nrHalfHigh a') → Fin (2 ^ nrHalfLow a'))
    (h₂ : ι₂ → Fin (2 ^ nrHalfLow a') → Fin (2 ^ nrHalfHigh a')) :
    PMF (Equiv.Perm (Fin (2 ^ a'))) :=
  (PMF.uniformOfFintype (NRBlockSeed ι₀ ι₁ ι₂)).map
    fun s => nrBlockEquiv a' ⟨h₀ s.s₀, h₁ s.s₁, h₂ s.s₂⟩

theorem nrBlockSeedDist_eq {ι₀ ι₁ ι₂ : Type*} [Fintype ι₀] [Nonempty ι₀]
    [Fintype ι₁] [Nonempty ι₁] [Fintype ι₂] [Nonempty ι₂] (a' : ℕ)
    (h₀ : ι₀ → Fin (2 ^ nrHalfLow a') → Fin (2 ^ nrHalfHigh a'))
    (h₁ : ι₁ → Fin (2 ^ nrHalfHigh a') → Fin (2 ^ nrHalfLow a'))
    (h₂ : ι₂ → Fin (2 ^ nrHalfLow a') → Fin (2 ^ nrHalfHigh a')) :
    nrBlockSeedDist a' h₀ h₁ h₂ =
      (PMF.uniformOfFintype (NRBlockSeed ι₀ ι₁ ι₂)).map
        fun s => nrBlockEquiv a' ⟨h₀ s.s₀, h₁ s.s₁, h₂ s.s₂⟩ := by
  unfold nrBlockSeedDist; rfl

/-- **Single-block Naor–Reingold `k`-tuple statistical-distance bound** ([NaorReingold1999],
Section 3.2 Definition 3.1, Section 5.2, Section 6 Definition 6.1, and Section 8 Corollary 8.1,
printed pp. 38, 49–50, 52, 60–61 / PDF pp. 10, 21–22, 24, 32–33).

Per Definition 2.10 item 2 of [NaorReingold1999], the uniform embedding distribution
`PMF.uniformOfFintype (T ↪ Fin (2 ^ a'))` models the uniform distribution on tuples of distinct
elements, and this theorem bounds distinguishing advantage from that ideal distribution. -/
theorem dist_permTupleKernel_nrBlock_le {ι₀ ι₁ ι₂ T : Type*}
    [Fintype ι₀] [Fintype ι₁] [Fintype ι₂] [Fintype T]
    {a' k : ℕ}
    {h₀ : ι₀ → Fin (2 ^ nrHalfLow a') → Fin (2 ^ nrHalfHigh a')}
    {h₁ : ι₁ → Fin (2 ^ nrHalfHigh a') → Fin (2 ^ nrHalfLow a')}
    {h₂ : ι₂ → Fin (2 ^ nrHalfLow a') → Fin (2 ^ nrHalfHigh a')}
    (hh₀ : IsKWiseIndependentHash 2 h₀)
    (hh₁ : IsKWiseIndependentHash k h₁)
    (hh₂ : IsKWiseIndependentHash k h₂)
    (hT : Fintype.card T ≤ k) (x : T ↪ Fin (2 ^ a')) :
    haveI : Nonempty ι₀ := hh₀.nonempty
    haveI : Nonempty ι₁ := hh₁.nonempty
    haveI : Nonempty ι₂ := hh₂.nonempty
    haveI : Nonempty (T ↪ Fin (2 ^ a')) := ⟨x⟩
    dist (permTupleKernel (nrBlockSeedDist a' h₀ h₁ h₂) x)
      (PMF.uniformOfFintype (T ↪ Fin (2 ^ a'))) ≤
      3 * ((Fintype.card T * (Fintype.card T - 1) : ℕ) : ℝ) /
        (2 * (2 ^ nrHalfLow a' : ℝ)) := by
  classical
  have : Nonempty ι₀ := hh₀.nonempty
  have : Nonempty ι₁ := hh₁.nonempty
  have : Nonempty ι₂ := hh₂.nonempty
  have : Nonempty (T ↪ Fin (2 ^ a')) := ⟨x⟩
  have hT_a : Fintype.card T ≤ 2 ^ a' := by
    simpa using Fintype.card_le_of_injective x x.injective
  let j : (T ↪ Fin (2 ^ a')) → (T → Fin (2 ^ a')) := fun e i => e i
  have hj : Function.Injective j := fun _ _ h => DFunLike.ext' h
  rw [← dist_map_of_injective _ _ hj]
  refine (dist_triangle _ (PMF.uniformOfFintype (T → Fin (2 ^ a'))) _).trans ?_
  have hpart2 : dist (PMF.uniformOfFintype (T → Fin (2 ^ a')))
      ((PMF.uniformOfFintype (T ↪ Fin (2 ^ a'))).map j) ≤
      ((Fintype.card T * (Fintype.card T - 1) : ℕ) : ℝ) / (2 * (2 ^ a' : ℝ)) := by
    rw [dist_comm]
    simpa using dist_uniform_embedding_to_fun (T := T) (α := Fin (2 ^ a')) (by simpa using hT_a)
  let splitFun : ((T → Fin (2 ^ nrHalfLow a')) × (T → Fin (2 ^ nrHalfHigh a'))) ≃
      (T → Fin (2 ^ a')) :=
    { toFun := fun p i => (nrSplitEquiv a').symm (p.1 i, p.2 i)
      invFun := fun f => (fun i => (nrSplitEquiv a' (f i)).1, fun i => (nrSplitEquiv a' (f i)).2)
      left_inv := fun p => by ext i <;> simp
      right_inv := fun f => by ext i; simp }
  let L₀ (i : T) : Fin (2 ^ nrHalfLow a') := (nrSplitEquiv a' (x i)).1
  let R₀ (i : T) : Fin (2 ^ nrHalfHigh a') := (nrSplitEquiv a' (x i)).2
  let R₁ (s₀ : ι₀) (i : T) : Fin (2 ^ nrHalfHigh a') := R₀ i ^^^ h₀ s₀ (L₀ i)
  let L₂ (s₀ : ι₀) (s₁ : ι₁) (i : T) : Fin (2 ^ nrHalfLow a') := L₀ i ^^^ h₁ s₁ (R₁ s₀ i)
  let R₃ (s₀ : ι₀) (s₁ : ι₁) (s₂ : ι₂) (i : T) : Fin (2 ^ nrHalfHigh a') :=
    R₁ s₀ i ^^^ h₂ s₂ (L₂ s₀ s₁ i)
  let μ_pair : PMF ((T → Fin (2 ^ nrHalfLow a')) × (T → Fin (2 ^ nrHalfHigh a'))) :=
    (PMF.uniformOfFintype ι₀).bind fun s₀ =>
      (PMF.uniformOfFintype ι₁).bind fun s₁ =>
        (PMF.uniformOfFintype ι₂).map fun s₂ => (L₂ s₀ s₁, R₃ s₀ s₁ s₂)
  have hμ_map : (permTupleKernel (nrBlockSeedDist a' h₀ h₁ h₂) x).map j =
      μ_pair.map splitFun := by
    have hunif_seed : (PMF.uniformOfFintype (NRBlockSeed ι₀ ι₁ ι₂)).map
        (nrBlockSeedEquivProd ι₀ ι₁ ι₂) = PMF.uniformOfFintype (ι₀ × ι₁ × ι₂) :=
      uniformOfFintype_map_equiv (nrBlockSeedEquivProd ι₀ ι₁ ι₂)
    have h1 : (permTupleKernel (nrBlockSeedDist a' h₀ h₁ h₂) x).map j =
        (PMF.uniformOfFintype (ι₀ × ι₁ × ι₂)).map fun p =>
          splitFun (L₂ p.1 p.2.1, R₃ p.1 p.2.1 p.2.2) := by
      rw [← hunif_seed]
      simp only [permTupleKernel_eq, nrBlockSeedDist, PMF.map_comp, Function.comp_def, j,
        Equiv.embeddingCongr_apply, Function.Embedding.congr_apply, Equiv.refl_symm,
        Equiv.refl_apply, nrBlockEquiv, Equiv.permCongr_apply, Equiv.symm_symm, nrPairBlock,
        Equiv.trans_apply, feistelRightEquiv_apply, feistelPairEquiv_apply, feistelPair,
        feistelHead, nrBlockSeedEquivProd, splitFun, Equiv.coe_fn_mk, L₀, R₀, R₁, L₂, R₃]
    rw [h1, ← uniformOfFintype_prod, ← uniformOfFintype_prod]
    simp only [μ_pair, PMF.map_bind, PMF.map_comp, Function.comp_def]
  have hunif_split : PMF.uniformOfFintype (T → Fin (2 ^ a')) =
      (PMF.uniformOfFintype ((T → Fin (2 ^ nrHalfLow a')) ×
        (T → Fin (2 ^ nrHalfHigh a')))).map splitFun :=
    (uniformOfFintype_map_equiv splitFun).symm
  have hpart1 : dist ((permTupleKernel (nrBlockSeedDist a' h₀ h₁ h₂) x).map j)
      (PMF.uniformOfFintype (T → Fin (2 ^ a'))) ≤
      ((Fintype.card T * (Fintype.card T - 1) : ℕ) : ℝ) / (2 * (2 ^ nrHalfHigh a' : ℝ)) +
      ((Fintype.card T * (Fintype.card T - 1) : ℕ) : ℝ) / (2 * (2 ^ nrHalfLow a' : ℝ)) := by
    rw [hμ_map, hunif_split, dist_map_of_injective _ _ splitFun.injective]
    let U₁ := PMF.uniformOfFintype (T → Fin (2 ^ nrHalfLow a'))
    let U₂ := PMF.uniformOfFintype (T → Fin (2 ^ nrHalfHigh a'))
    have hunif_prod :
        PMF.uniformOfFintype ((T → Fin (2 ^ nrHalfLow a')) × (T → Fin (2 ^ nrHalfHigh a'))) =
          U₁.bind fun l => U₂.map fun r => (l, r) :=
      (uniformOfFintype_prod (T → Fin (2 ^ nrHalfLow a')) (T → Fin (2 ^ nrHalfHigh a'))).symm
    rw [hunif_prod]
    let mid (s₀ : ι₀) (l : T → Fin (2 ^ nrHalfLow a')) : PMF (T → Fin (2 ^ nrHalfHigh a')) :=
      (PMF.uniformOfFintype ι₂).map fun s₂ i => R₁ s₀ i ^^^ h₂ s₂ (l i)
    have hgood_dist (s₀ : ι₀) (hR₁ : Function.Injective (R₁ s₀)) :
        dist ((PMF.uniformOfFintype ι₁).bind fun s₁ =>
          (PMF.uniformOfFintype ι₂).map fun s₂ => (L₂ s₀ s₁, R₃ s₀ s₁ s₂))
          (U₁.bind fun l => U₂.map fun r => (l, r)) ≤
          ((Fintype.card T * (Fintype.card T - 1) : ℕ) : ℝ) / (2 * (2 ^ nrHalfLow a' : ℝ)) := by
      have hL₂_unif : (PMF.uniformOfFintype ι₁).map (L₂ s₀) = U₁ :=
        map_xor_restrict_eq_uniform hh₁ hT L₀ hR₁
      have hf_eq : ((PMF.uniformOfFintype ι₁).bind fun s₁ =>
          (PMF.uniformOfFintype ι₂).map fun s₂ => (L₂ s₀ s₁, R₃ s₀ s₁ s₂)) =
          U₁.bind fun l => (mid s₀ l).map (l, ·) := by
        rw [← hL₂_unif, PMF.bind_map]
        refine congrArg ((PMF.uniformOfFintype ι₁).bind ·) (funext fun s₁ => ?_)
        simp only [mid, PMF.map_comp, Function.comp_def, R₃]
      rw [hf_eq, dist_bind_pair U₁ (mid s₀) (fun _ => U₂)]
      let E₁ : Set (T → Fin (2 ^ nrHalfLow a')) := {l | ¬ Function.Injective l}
      have hterm (l : T → Fin (2 ^ nrHalfLow a')) :
          (U₁ l).toReal * dist (mid s₀ l) U₂ ≤ if l ∈ E₁ then (U₁ l).toReal else 0 := by
        by_cases hl : Function.Injective l
        · have heq : mid s₀ l = U₂ := map_xor_restrict_eq_uniform hh₂ hT (R₁ s₀) hl
          simp [E₁, hl, heq]
        · simpa [E₁, hl] using mul_le_mul_of_nonneg_left (dist_le_one _ _) ENNReal.toReal_nonneg
      calc ∑ l, (U₁ l).toReal * dist (mid s₀ l) U₂
          ≤ ∑ l, if l ∈ E₁ then (U₁ l).toReal else 0 := sum_le_sum fun l _ => hterm l
        _ = (U₁.toOuterMeasure E₁).toReal := by
            rw [toOuterMeasure_apply_toReal]
            exact sum_congr rfl fun l _ => by by_cases hl : l ∈ E₁ <;> simp [hl]
        _ ≤ ((Fintype.card T * (Fintype.card T - 1) : ℕ) : ℝ) / (2 * (2 ^ nrHalfLow a' : ℝ)) := by
            simpa using prob_not_injective_uniform_le T (Fin (2 ^ nrHalfLow a'))
    refine (dist_bind_of_good _ _ _ {s₀ | Function.Injective (R₁ s₀)} (by positivity)
      hgood_dist).trans ?_
    gcongr
    rw [toOuterMeasure_uniformOfFintype_toReal]
    let S₀ : Finset (Fin (2 ^ nrHalfHigh a') × Fin (2 ^ nrHalfLow a')) :=
      (univ : Finset T).map ⟨fun i => (R₀ i, L₀ i), fun i₁ i₂ h => by
        have hsplit : nrSplitEquiv a' (x i₁) = nrSplitEquiv a' (x i₂) :=
          Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
        exact x.injective ((nrSplitEquiv a').injective hsplit)⟩
    have hS₀_card : #S₀ = Fintype.card T := by simp [S₀]
    have hfeistel := dens_not_injOn_feistelHead_le (hh₀.isPairwiseIndependentHash le_rfl) S₀
    rw [hS₀_card, dens_eq_card_div_card, NNRat.cast_div, NNRat.cast_natCast,
      NNRat.cast_natCast] at hfeistel
    have hsub : #(univ.filter (· ∈ ({s₀ : ι₀ | Function.Injective (R₁ s₀)}ᶜ : Set ι₀))) ≤
        #{s₀ : ι₀ | ¬ Set.InjOn (feistelHead (h₀ s₀))
          (S₀ : Set (Fin (2 ^ nrHalfHigh a') × Fin (2 ^ nrHalfLow a')))} := by
      refine card_le_card fun s₀ hs₀ => ?_
      rw [mem_filter] at hs₀ ⊢
      refine ⟨mem_univ s₀, fun hInj => hs₀.2 fun i₁ i₂ heq => ?_⟩
      have h1 : (R₀ i₁, L₀ i₁) ∈ S₀ := mem_map.mpr ⟨i₁, mem_univ i₁, rfl⟩
      have h2 : (R₀ i₂, L₀ i₂) ∈ S₀ := mem_map.mpr ⟨i₂, mem_univ i₂, rfl⟩
      have heq' := hInj h1 h2 heq
      have hsplit : nrSplitEquiv a' (x i₁) = nrSplitEquiv a' (x i₂) :=
        Prod.ext (congrArg Prod.snd heq') (congrArg Prod.fst heq')
      exact x.injective ((nrSplitEquiv a').injective hsplit)
    exact (div_le_div_of_nonneg_right (Nat.cast_le.mpr hsub) (Nat.cast_nonneg _)).trans hfeistel
  have hpow_hi : (2 ^ nrHalfLow a' : ℝ) ≤ (2 ^ nrHalfHigh a' : ℝ) := by
    exact_mod_cast Nat.pow_le_pow_right two_pos (nrHalfLow_le_nrHalfHigh a')
  have hpow_a : (2 ^ nrHalfLow a' : ℝ) ≤ (2 ^ a' : ℝ) := by
    exact_mod_cast Nat.pow_le_pow_right two_pos (nrHalfLow_le a')
  have hdiv_hi :
      ((Fintype.card T * (Fintype.card T - 1) : ℕ) : ℝ) / (2 * (2 ^ nrHalfHigh a' : ℝ)) ≤
        ((Fintype.card T * (Fintype.card T - 1) : ℕ) : ℝ) / (2 * (2 ^ nrHalfLow a' : ℝ)) := by
    gcongr
  have hdiv_a :
      ((Fintype.card T * (Fintype.card T - 1) : ℕ) : ℝ) / (2 * (2 ^ a' : ℝ)) ≤
        ((Fintype.card T * (Fintype.card T - 1) : ℕ) : ℝ) / (2 * (2 ^ nrHalfLow a' : ℝ)) := by
    gcongr
  set num : ℝ := ((Fintype.card T * (Fintype.card T - 1) : ℕ) : ℝ)
  set den : ℝ := 2 * (2 ^ nrHalfLow a' : ℝ)
  have hsum3 : num / den + num / den + num / den = 3 * num / den := by ring
  linarith


/-! ## Section 2: Composed Naor–Reingold blocks and Case B sharded bijection -/

/-- Seed tuple `Fin t → NRBlockSeed ι₀ ι₁ ι₂` for `t` independent Naor–Reingold blocks. -/
structure NRComposedSeed (t : ℕ) (ι₀ ι₁ ι₂ : Type*) where
  /-- Per-round block seeds. -/
  blocks : Fin t → NRBlockSeed ι₀ ι₁ ι₂

/-- Equivalence between `NRComposedSeed t ι₀ ι₁ ι₂` and `Fin t → NRBlockSeed ι₀ ι₁ ι₂`. -/
def nrComposedSeedEquivFun (t : ℕ) (ι₀ ι₁ ι₂ : Type*) :
    NRComposedSeed t ι₀ ι₁ ι₂ ≃ (Fin t → NRBlockSeed ι₀ ι₁ ι₂) where
  toFun s := s.blocks
  invFun f := ⟨f⟩
  left_inv s := by cases s; rfl
  right_inv _ := rfl

instance {t : ℕ} {ι₀ ι₁ ι₂ : Type*} [Fintype ι₀] [Fintype ι₁] [Fintype ι₂] :
    Fintype (NRComposedSeed t ι₀ ι₁ ι₂) :=
  Fintype.ofEquiv (Fin t → NRBlockSeed ι₀ ι₁ ι₂) (nrComposedSeedEquivFun t ι₀ ι₁ ι₂).symm

instance {t : ℕ} {ι₀ ι₁ ι₂ : Type*} [Nonempty ι₀] [Nonempty ι₁] [Nonempty ι₂] :
    Nonempty (NRComposedSeed t ι₀ ι₁ ι₂) :=
  ⟨⟨fun _ => Classical.arbitrary (NRBlockSeed ι₀ ι₁ ι₂)⟩⟩

/-- Random `t`-composed Naor–Reingold permutation on `Fin (2 ^ a')` under a uniform
`NRComposedSeed`. -/
noncomputable def nrComposedSeedDist {ι₀ ι₁ ι₂ : Type*} [Fintype ι₀] [Nonempty ι₀]
    [Fintype ι₁] [Nonempty ι₁] [Fintype ι₂] [Nonempty ι₂]
    (a' t : ℕ)
    (h₀ : ι₀ → Fin (2 ^ nrHalfLow a') → Fin (2 ^ nrHalfHigh a'))
    (h₁ : ι₁ → Fin (2 ^ nrHalfHigh a') → Fin (2 ^ nrHalfLow a'))
    (h₂ : ι₂ → Fin (2 ^ nrHalfLow a') → Fin (2 ^ nrHalfHigh a')) :
    PMF (Equiv.Perm (Fin (2 ^ a'))) :=
  (PMF.uniformOfFintype (NRComposedSeed t ι₀ ι₁ ι₂)).map fun s =>
    nrComposedEquiv a' t (fun r => ⟨h₀ (s.blocks r).s₀, h₁ (s.blocks r).s₁, h₂ (s.blocks r).s₂⟩)

theorem nrComposedSeedDist_eq {ι₀ ι₁ ι₂ : Type*} [Fintype ι₀] [Nonempty ι₀]
    [Fintype ι₁] [Nonempty ι₁] [Fintype ι₂] [Nonempty ι₂]
    (a' t : ℕ)
    (h₀ : ι₀ → Fin (2 ^ nrHalfLow a') → Fin (2 ^ nrHalfHigh a'))
    (h₁ : ι₁ → Fin (2 ^ nrHalfHigh a') → Fin (2 ^ nrHalfLow a'))
    (h₂ : ι₂ → Fin (2 ^ nrHalfLow a') → Fin (2 ^ nrHalfHigh a')) :
    nrComposedSeedDist a' t h₀ h₁ h₂ =
      (PMF.uniformOfFintype (NRComposedSeed t ι₀ ι₁ ι₂)).map fun s =>
        nrComposedEquiv a' t
          (fun r => ⟨h₀ (s.blocks r).s₀, h₁ (s.blocks r).s₁, h₂ (s.blocks r).s₂⟩) := by
  unfold nrComposedSeedDist; rfl

theorem nrComposedSeedDist_eq_composePermDist {ι₀ ι₁ ι₂ : Type*}
    [Fintype ι₀] [Nonempty ι₀] [Fintype ι₁] [Nonempty ι₁] [Fintype ι₂] [Nonempty ι₂]
    (a' : ℕ)
    (h₀ : ι₀ → Fin (2 ^ nrHalfLow a') → Fin (2 ^ nrHalfHigh a'))
    (h₁ : ι₁ → Fin (2 ^ nrHalfHigh a') → Fin (2 ^ nrHalfLow a'))
    (h₂ : ι₂ → Fin (2 ^ nrHalfLow a') → Fin (2 ^ nrHalfHigh a')) :
    ∀ t : ℕ,
      nrComposedSeedDist a' t h₀ h₁ h₂ =
        composePermDist t (fun _ => nrBlockSeedDist a' h₀ h₁ h₂)
  | 0 => by
    rw [nrComposedSeedDist_eq, composePermDist_zero]
    simp only [nrComposedEquiv_zero]
    exact PMF.map_const _ (Equiv.refl (Fin (2 ^ a')))
  | t + 1 => by
    let splitFin : (Fin (t + 1) → NRBlockSeed ι₀ ι₁ ι₂) ≃
        (Fin t → NRBlockSeed ι₀ ι₁ ι₂) × NRBlockSeed ι₀ ι₁ ι₂ :=
      { toFun := fun f => (fun i => f i.castSucc, f (Fin.last t))
        invFun := fun p => Fin.snoc p.1 p.2
        left_inv := fun f => by ext i; cases i using Fin.lastCases <;> simp
        right_inv := fun p => by rcases p with ⟨f, x⟩; ext <;> simp }
    let seedEq : NRComposedSeed (t + 1) ι₀ ι₁ ι₂ ≃
        NRComposedSeed t ι₀ ι₁ ι₂ × NRBlockSeed ι₀ ι₁ ι₂ :=
      (nrComposedSeedEquivFun (t + 1) ι₀ ι₁ ι₂).trans
        (splitFin.trans (Equiv.prodCongr (nrComposedSeedEquivFun t ι₀ ι₁ ι₂).symm (Equiv.refl _)))
    have hunif : (PMF.uniformOfFintype (NRComposedSeed (t + 1) ι₀ ι₁ ι₂)).map seedEq =
        PMF.uniformOfFintype (NRComposedSeed t ι₀ ι₁ ι₂ × NRBlockSeed ι₀ ι₁ ι₂) :=
      uniformOfFintype_map_equiv seedEq
    have hstep : nrComposedSeedDist a' (t + 1) h₀ h₁ h₂ =
        (PMF.uniformOfFintype (NRComposedSeed t ι₀ ι₁ ι₂ × NRBlockSeed ι₀ ι₁ ι₂)).map fun p =>
          (nrComposedEquiv a' t
            (fun r => ⟨h₀ (p.1.blocks r).s₀, h₁ (p.1.blocks r).s₁, h₂ (p.1.blocks r).s₂⟩)).trans
          (nrBlockEquiv a' ⟨h₀ p.2.s₀, h₁ p.2.s₁, h₂ p.2.s₂⟩) := by
      rw [nrComposedSeedDist_eq, ← hunif, PMF.map_comp]
      refine PMF.map_congr_on_support _ _ _ fun s _ => ?_
      simp only [Function.comp_def, nrComposedEquiv_succ, seedEq, nrComposedSeedEquivFun, splitFin,
        Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
      rfl
    rw [hstep, ← PMF.uniformOfFintype_prod, composePermDist_succ,
      ← nrComposedSeedDist_eq_composePermDist a' h₀ h₁ h₂ t]
    simp only [nrComposedSeedDist_eq, nrBlockSeedDist_eq, PMF.map_bind, PMF.bind_map, PMF.map_comp,
      Function.comp_def]

/-- **`t`-composed Naor–Reingold `k`-tuple statistical-distance contraction**: composing `t ≥ 1`
independent 3-round Feistel Naor–Reingold blocks with `2`-wise independent `h₀` and `k`-wise
independent `h₁, h₂` achieves statistical distance at most
`(1 / 2) * (3 * k ^ 2 / 2 ^ ⌊a' / 2⌋) ^ t` from uniform on `T ↪ Fin (2 ^ a')`. -/
theorem dist_permTupleKernel_nrComposed_le {ι₀ ι₁ ι₂ T : Type*}
    [Fintype ι₀] [Fintype ι₁] [Fintype ι₂] [Fintype T]
    {a' t k : ℕ} (ht : 1 ≤ t)
    {h₀ : ι₀ → Fin (2 ^ nrHalfLow a') → Fin (2 ^ nrHalfHigh a')}
    {h₁ : ι₁ → Fin (2 ^ nrHalfHigh a') → Fin (2 ^ nrHalfLow a')}
    {h₂ : ι₂ → Fin (2 ^ nrHalfLow a') → Fin (2 ^ nrHalfHigh a')}
    (hh₀ : IsKWiseIndependentHash 2 h₀)
    (hh₁ : IsKWiseIndependentHash k h₁)
    (hh₂ : IsKWiseIndependentHash k h₂)
    (hT : Fintype.card T ≤ k) (x : T ↪ Fin (2 ^ a')) :
    haveI : Nonempty ι₀ := hh₀.nonempty
    haveI : Nonempty ι₁ := hh₁.nonempty
    haveI : Nonempty ι₂ := hh₂.nonempty
    haveI : Nonempty (T ↪ Fin (2 ^ a')) := ⟨x⟩
    dist (permTupleKernel (nrComposedSeedDist a' t h₀ h₁ h₂) x)
      (PMF.uniformOfFintype (T ↪ Fin (2 ^ a'))) ≤
      (1 / 2 : ℝ) * (3 * (k : ℝ) ^ 2 / (2 ^ nrHalfLow a' : ℝ)) ^ t := by
  have : Nonempty ι₀ := hh₀.nonempty
  have : Nonempty ι₁ := hh₁.nonempty
  have : Nonempty ι₂ := hh₂.nonempty
  have : Nonempty (T ↪ Fin (2 ^ a')) := ⟨x⟩
  rw [nrComposedSeedDist_eq_composePermDist]
  have h1 (y : T ↪ Fin (2 ^ a')) :
      dist (permTupleKernel (nrBlockSeedDist a' h₀ h₁ h₂) y)
        (PMF.uniformOfFintype (T ↪ Fin (2 ^ a'))) ≤
        3 * (k : ℝ) ^ 2 / (2 * (2 ^ nrHalfLow a' : ℝ)) := by
    refine (dist_permTupleKernel_nrBlock_le hh₀ hh₁ hh₂ hT y).trans ?_
    have hnat : Fintype.card T * (Fintype.card T - 1) ≤ k ^ 2 := by
      calc Fintype.card T * (Fintype.card T - 1)
          ≤ Fintype.card T * Fintype.card T := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        _ ≤ k * k := Nat.mul_le_mul hT hT
        _ = k ^ 2 := (sq k).symm
    have hreal : ((Fintype.card T * (Fintype.card T - 1) : ℕ) : ℝ) ≤ (k : ℝ) ^ 2 := by
      exact_mod_cast hnat
    gcongr
  refine (dist_permTupleKernel_composePermDist_le ht _ (fun _ y => h1 y) x).trans_eq ?_
  congr 1
  congr 1
  ring

/-- Shard-index bit-width `⌊m / 2⌋` for Arbitman–Naor–Segev 1-round Feistel sharding in Case B. -/
abbrev shardBits (m : ℕ) : ℕ := m / 2

/-- Intra-shard local bucket bit-width `m - shardBits m = ⌈m / 2⌉` in Case B. -/
abbrev localBucketBits (m : ℕ) : ℕ := m - shardBits m

/-- Right-coordinate suffix bit-width `a' = a - ⌊m / 2⌋` permuted by Naor–Reingold in Case B. -/
abbrev suffixBits (a m : ℕ) : ℕ := a - shardBits m

theorem shardBits_le_bucketBits (m : ℕ) : shardBits m ≤ m := Nat.div_le_self m 2

theorem shardBits_le_of_le {a m : ℕ} (hma : m ≤ a) : shardBits m ≤ a :=
  (shardBits_le_bucketBits m).trans hma

theorem localBucketBits_le_suffixBits {a m : ℕ} (hma : m ≤ a) :
    localBucketBits m ≤ suffixBits a m := by
  dsimp only [localBucketBits, suffixBits, shardBits]; omega

theorem suffixBits_sub_localBucketBits {a m : ℕ} (hma : m ≤ a) :
    suffixBits a m - localBucketBits m = a - m := by
  dsimp only [suffixBits, localBucketBits, shardBits]; omega

/-- Round-function bundle for Case B: 1-round Feistel shard router `fShard` plus `t` composed
3-round Feistel Naor–Reingold blocks on `Fin (2 ^ suffixBits a m)`. -/
structure CaseBRounds (a m t : ℕ) where
  /-- Arbitman–Naor–Segev 1-round Feistel shard function `Fin (2 ^ a') → Fin (2 ^ ⌊m / 2⌋)`. -/
  fShard : Fin (2 ^ suffixBits a m) → Fin (2 ^ shardBits m)
  /-- `t` Naor–Reingold 3-round Feistel blocks on `Fin (2 ^ a')`. -/
  nrBlocks : Fin t → NRBlockFuncs (suffixBits a m)

/-- Split `Fin (2 ^ suffixBits a m) ≃ Fin (2 ^ localBucketBits m) × Fin (2 ^ (a - m))`. -/
@[expose] def suffixSplitEquiv {a m : ℕ} (hma : m ≤ a) :
    Fin (2 ^ suffixBits a m) ≃ Fin (2 ^ localBucketBits m) × Fin (2 ^ (a - m)) :=
  (bitDomainEquiv (localBucketBits_le_suffixBits hma)).trans
    (Equiv.prodCongr (Equiv.refl _)
      (finCongr (pow_congr_right (suffixBits_sub_localBucketBits hma))))
where
  pow_congr_right {x y : ℕ} (h : x = y) : 2 ^ x = 2 ^ y := congrArg (2 ^ ·) h

/-- Combine `(shard, (localBucket, quot))` into `(Fin (2 ^ m)) × (Fin (2 ^ (a - m)))`. -/
@[expose] def shardLocalMergeEquiv (a m : ℕ) :
    Fin (2 ^ shardBits m) × (Fin (2 ^ localBucketBits m) × Fin (2 ^ (a - m))) ≃
      Fin (2 ^ m) × Fin (2 ^ (a - m)) :=
  (Equiv.prodAssoc _ _ _).symm.trans
    (Equiv.prodCongr (bitDomainEquiv (shardBits_le_bucketBits m)).symm (Equiv.refl _))

/-- Case B bijection `(u : Fin (2 ^ a)) ≃ Fin (2 ^ m) × Fin (2 ^ (a - m))`:
1-round Feistel shard `σ = x_L ^^^ fShard y_R` followed by `t`-round Naor–Reingold permutation
`z = nrComposedEquiv a' t nrBlocks y_R` split into `(localBucket, quot)`. -/
@[expose] def caseBEquiv {a m t : ℕ} (hma : m ≤ a) (r : CaseBRounds a m t) :
    Fin (2 ^ a) ≃ Fin (2 ^ m) × Fin (2 ^ (a - m)) :=
  (bitDomainEquiv (shardBits_le_of_le hma)).trans <|
    (feistelPairEquiv r.fShard).trans <|
      (Equiv.prodCongr (Equiv.refl _)
        ((nrComposedEquiv (suffixBits a m) t r.nrBlocks).trans (suffixSplitEquiv hma))).trans
        (shardLocalMergeEquiv a m)

/-- Shard index `σ : Fin (2 ^ shardBits m)` extracted from a `Fin (2 ^ m)` bucket index. -/
@[expose] def bucketShard (m : ℕ) (b : Fin (2 ^ m)) : Fin (2 ^ shardBits m) :=
  (bitDomainEquiv (shardBits_le_bucketBits m) b).1

/-- Local intra-shard bucket `Fin (2 ^ localBucketBits m)` extracted from `b : Fin (2 ^ m)`. -/
@[expose] def bucketLocal (m : ℕ) (b : Fin (2 ^ m)) : Fin (2 ^ localBucketBits m) :=
  (bitDomainEquiv (shardBits_le_bucketBits m) b).2

/-- Right-coordinate suffix `y_R : Fin (2 ^ suffixBits a m)` of `u : Fin (2 ^ a)`. -/
@[expose] def keySuffix {a m : ℕ} (hma : m ≤ a) (u : Fin (2 ^ a)) : Fin (2 ^ suffixBits a m) :=
  (bitDomainEquiv (shardBits_le_of_le hma) u).2

/-- Shard `σ(u) = x_L ^^^ fShard y_R` assigned to `u` by `caseBEquiv`. -/
@[expose] def caseBShard {a m t : ℕ} (hma : m ≤ a) (r : CaseBRounds a m t) (u : Fin (2 ^ a)) :
    Fin (2 ^ shardBits m) :=
  bucketShard m (caseBEquiv hma r u).1

@[simp] theorem caseBShard_eq_feistelHead {a m t : ℕ} (hma : m ≤ a) (r : CaseBRounds a m t)
    (u : Fin (2 ^ a)) :
    caseBShard hma r u = feistelHead r.fShard (bitDomainEquiv (shardBits_le_of_le hma) u) := by
  unfold caseBShard bucketShard caseBEquiv shardLocalMergeEquiv
  simp [Equiv.trans_apply, Equiv.prodCongr_apply, feistelPair]

/-- **Deterministic shard collision-freedom** ([ArbitmanNaorSegev2010], `arXiv:0912.5424v3`,
Section 5.2 construction, PDF pp. 21–23 / printed pp. 20–22): for every `CaseBRounds` `r` and shard
`σ : Fin (2 ^ shardBits m)`, the suffix projection `keySuffix hma` (`y_R`) is strictly injective on
all keys routed into shard `σ`. (Section 5.4 Claim 5.7 provides bin load bounds for this
construction.) -/
theorem injOn_yR_of_caseBShard_eq {a m t : ℕ} (hma : m ≤ a) (r : CaseBRounds a m t)
    (σ : Fin (2 ^ shardBits m)) :
    Set.InjOn (keySuffix hma) {u : Fin (2 ^ a) | caseBShard hma r u = σ} := by
  intro u₁ hu₁ u₂ hu₂ hsuf
  rw [Set.mem_ofPred_eq, caseBShard_eq_feistelHead] at hu₁ hu₂
  exact (bitDomainEquiv (shardBits_le_of_le hma)).injective
    (eq_of_feistelHead_eq_of_snd_eq (hu₁.trans hu₂.symm) hsuf)

/-- **Abstract Case B shard-tuple statistical-distance transfer**: on any `T : Finset (Fin (2 ^ a))`
with `#T ≤ κ` and `yEmb : T ↪ Fin (2 ^ suffixBits a m)`, under a `(1 - δ_top)`-good top seed
`τ ∈ GoodTop`, the joint distribution of `(shard(u), nrPerm(y_R u), aux(u))_{u ∈ T}` is within
`δ_top + (1 / 2) * (3 * κ ^ 2 / 2 ^ ⌊a' / 2⌋) ^ t` of `Uniform × UniformInj × Uniform`. -/
theorem dist_caseB_shardTuple_le {Top ι_sh ι₀ ι₁ ι₂ ι_aux : Type*}
    [Fintype Top] [Nonempty Top] [Fintype ι_sh] [Nonempty ι_sh]
    [Fintype ι₀] [Nonempty ι₀] [Fintype ι₁] [Nonempty ι₁] [Fintype ι₂] [Nonempty ι₂]
    [Fintype ι_aux] [Nonempty ι_aux]
    {a m b_aux t κ : ℕ} (hma : m ≤ a) (ht : 1 ≤ t)
    (h_sh : Top → ι_sh → Fin (2 ^ suffixBits a m) → Fin (2 ^ shardBits m))
    (h_nr₀ : Top → ι₀ →
      Fin (2 ^ nrHalfLow (suffixBits a m)) → Fin (2 ^ nrHalfHigh (suffixBits a m)))
    (h_nr₁ : Top → ι₁ →
      Fin (2 ^ nrHalfHigh (suffixBits a m)) → Fin (2 ^ nrHalfLow (suffixBits a m)))
    (h_nr₂ : Top → ι₂ →
      Fin (2 ^ nrHalfLow (suffixBits a m)) → Fin (2 ^ nrHalfHigh (suffixBits a m)))
    (h_aux : Top → ι_aux → Fin (2 ^ a) → Fin (2 ^ b_aux))
    {T : Finset (Fin (2 ^ a))} (hT : #T ≤ κ)
    (yEmb : T ↪ Fin (2 ^ suffixBits a m))
    (GoodTop : Set Top) {δ_top : ℝ}
    (hδ_top : ((PMF.uniformOfFintype Top).toOuterMeasure GoodTopᶜ).toReal ≤ δ_top)
    (hgood_sh : ∀ τ ∈ GoodTop, IsKWiseIndependentHash κ (h_sh τ))
    (hgood_nr₀ : ∀ τ ∈ GoodTop, IsKWiseIndependentHash 2 (h_nr₀ τ))
    (hgood_nr₁ : ∀ τ ∈ GoodTop, IsKWiseIndependentHash κ (h_nr₁ τ))
    (hgood_nr₂ : ∀ τ ∈ GoodTop, IsKWiseIndependentHash κ (h_nr₂ τ))
    (hgood_aux : ∀ τ ∈ GoodTop, IsKWiseIndependentHash κ (h_aux τ)) :
    haveI : Nonempty (T ↪ Fin (2 ^ suffixBits a m)) := ⟨yEmb⟩
    dist (((PMF.uniformOfFintype Top).bind fun τ =>
        (PMF.uniformOfFintype ι_sh).bind fun s_sh =>
          (nrComposedSeedDist (suffixBits a m) t (h_nr₀ τ) (h_nr₁ τ) (h_nr₂ τ)).bind fun π =>
            (PMF.uniformOfFintype ι_aux).map fun s_aux =>
              ((fun u : T => (bitDomainEquiv (shardBits_le_of_le hma) u.1).1 ^^^
                  h_sh τ s_sh (yEmb u)),
                ((Equiv.refl T).embeddingCongr π yEmb, fun u : T => h_aux τ s_aux u.1))))
      (PMF.uniformOfFintype
        ((T → Fin (2 ^ shardBits m)) ×
          ((T ↪ Fin (2 ^ suffixBits a m)) × (T → Fin (2 ^ b_aux))))) ≤
      δ_top +
        (1 / 2 : ℝ) * (3 * (κ : ℝ) ^ 2 / (2 ^ nrHalfLow (suffixBits a m) : ℝ)) ^ t := by
  classical
  have : Nonempty (T ↪ Fin (2 ^ suffixBits a m)) := ⟨yEmb⟩
  let U_sh := PMF.uniformOfFintype (T → Fin (2 ^ shardBits m))
  let U_nr := PMF.uniformOfFintype (T ↪ Fin (2 ^ suffixBits a m))
  let U_aux := PMF.uniformOfFintype (T → Fin (2 ^ b_aux))
  let U_all := PMF.uniformOfFintype
    ((T → Fin (2 ^ shardBits m)) × ((T ↪ Fin (2 ^ suffixBits a m)) × (T → Fin (2 ^ b_aux))))
  have hT_card : Fintype.card T ≤ κ := by simpa using hT
  have hgood_τ (τ : Top) (hτ : τ ∈ GoodTop) :
      dist ((PMF.uniformOfFintype ι_sh).bind fun s_sh =>
          (nrComposedSeedDist (suffixBits a m) t (h_nr₀ τ) (h_nr₁ τ) (h_nr₂ τ)).bind fun π =>
            (PMF.uniformOfFintype ι_aux).map fun s_aux =>
              ((fun u : T => (bitDomainEquiv (shardBits_le_of_le hma) u.1).1 ^^^
                  h_sh τ s_sh (yEmb u)),
                ((Equiv.refl T).embeddingCongr π yEmb, fun u : T => h_aux τ s_aux u.1))) U_all ≤
        (1 / 2 : ℝ) * (3 * (κ : ℝ) ^ 2 / (2 ^ nrHalfLow (suffixBits a m) : ℝ)) ^ t := by
    have hsh_unif : ((PMF.uniformOfFintype ι_sh).map fun s_sh (u : T) =>
        (bitDomainEquiv (shardBits_le_of_le hma) u.1).1 ^^^ h_sh τ s_sh (yEmb u)) = U_sh :=
      map_xor_restrict_eq_uniform (hgood_sh τ hτ) hT_card _ yEmb.injective
    have haux_unif : ((PMF.uniformOfFintype ι_aux).map fun s_aux (u : T) =>
        h_aux τ s_aux u.1) = U_aux :=
      uniformOfFintype_map_of_isKWise ((hgood_aux τ hτ).comp Subtype.val_injective) hT_card
    let μ_nr := permTupleKernel (nrComposedSeedDist (suffixBits a m) t
      (h_nr₀ τ) (h_nr₁ τ) (h_nr₂ τ)) yEmb
    have hrewrite : ((PMF.uniformOfFintype ι_sh).bind fun s_sh =>
          (nrComposedSeedDist (suffixBits a m) t (h_nr₀ τ) (h_nr₁ τ) (h_nr₂ τ)).bind fun π =>
            (PMF.uniformOfFintype ι_aux).map fun s_aux =>
              ((fun u : T => (bitDomainEquiv (shardBits_le_of_le hma) u.1).1 ^^^
                  h_sh τ s_sh (yEmb u)),
                ((Equiv.refl T).embeddingCongr π yEmb, fun u : T => h_aux τ s_aux u.1))) =
        U_sh.bind fun f_sh => (μ_nr.bind fun e => U_aux.map (e, ·)).map (f_sh, ·) := by
      rw [← hsh_unif, PMF.bind_map]
      refine congrArg ((PMF.uniformOfFintype ι_sh).bind ·) (funext fun s_sh => ?_)
      dsimp only [Function.comp_def, μ_nr]
      rw [permTupleKernel_eq, PMF.map_bind, PMF.bind_map]
      refine congrArg ((nrComposedSeedDist (suffixBits a m) t
        (h_nr₀ τ) (h_nr₁ τ) (h_nr₂ τ)).bind ·) (funext fun π => ?_)
      dsimp only [Function.comp_def]
      rw [← haux_unif]
      simp only [PMF.map_comp, Function.comp_def]
    have hU_all : U_all =
        U_sh.bind fun f_sh => (U_nr.bind fun e => U_aux.map (e, ·)).map (f_sh, ·) := by
      have hp1 := (uniformOfFintype_prod (T → Fin (2 ^ shardBits m))
        ((T ↪ Fin (2 ^ suffixBits a m)) × (T → Fin (2 ^ b_aux)))).symm
      have hp2 := (uniformOfFintype_prod (T ↪ Fin (2 ^ suffixBits a m))
        (T → Fin (2 ^ b_aux))).symm
      rw [show U_all = _ from hp1]
      refine congrArg (U_sh.bind ·) (funext fun f_sh => ?_)
      rw [show PMF.uniformOfFintype
          ((T ↪ Fin (2 ^ suffixBits a m)) × (T → Fin (2 ^ b_aux))) = _ from hp2]
    have hpair_dist : dist (μ_nr.bind fun e => U_aux.map (e, ·))
        (U_nr.bind fun e => U_aux.map (e, ·)) = dist μ_nr U_nr := by
      have hcomm (ν : PMF (T ↪ Fin (2 ^ suffixBits a m))) :
          (ν.bind fun e => U_aux.map (e, ·)) =
            (U_aux.bind fun f_aux => ν.map (f_aux, ·)).map (Equiv.prodComm _ _) := by
        ext ⟨e, f_aux⟩
        rw [map_equiv_apply, bind_map_prodMk_apply, bind_map_prodMk_apply]
        exact mul_comm _ _
      rw [hcomm μ_nr, hcomm U_nr, dist_map_of_injective _ _ (Equiv.prodComm _ _).injective,
        dist_bind_pair, ← sum_mul, sum_toReal, one_mul]
    rw [hrewrite, hU_all, dist_bind_pair]
    simp only [hpair_dist, ← sum_mul, sum_toReal, one_mul]
    exact dist_permTupleKernel_nrComposed_le ht (hgood_nr₀ τ hτ) (hgood_nr₁ τ hτ)
      (hgood_nr₂ τ hτ) hT_card yEmb
  refine (dist_bind_of_good _ _ U_all GoodTop (by positivity) hgood_τ).trans ?_
  linarith

/-- Suffix-space preimage `(B.image (bucketLocal m) ×ˢ univ)` of an intra-shard bucket set `B`. -/
def intraShardSuffixSet {a m : ℕ} (hma : m ≤ a) [DecidableEq (Fin (2 ^ localBucketBits m))]
    (B : Finset (Fin (2 ^ m))) : Finset (Fin (2 ^ suffixBits a m)) :=
  (B.image (bucketLocal m) ×ˢ (univ : Finset (Fin (2 ^ (a - m))))).map
    (suffixSplitEquiv hma).symm.toEmbedding

theorem mem_intraShardSuffixSet_iff {a m : ℕ} (hma : m ≤ a)
    (σ : Fin (2 ^ shardBits m)) {B : Finset (Fin (2 ^ m))}
    (hB : ∀ b ∈ B, bucketShard m b = σ)
    (sh : Fin (2 ^ shardBits m)) (z : Fin (2 ^ suffixBits a m)) :
    (shardLocalMergeEquiv a m (sh, suffixSplitEquiv hma z)).1 ∈ B ↔
      sh = σ ∧ z ∈ intraShardSuffixSet hma B := by
  have hmerge : (shardLocalMergeEquiv a m (sh, suffixSplitEquiv hma z)).1 =
      (bitDomainEquiv (shardBits_le_bucketBits m)).symm (sh, (suffixSplitEquiv hma z).1) := rfl
  rw [hmerge]
  unfold intraShardSuffixSet
  simp only [mem_map, Equiv.coe_toEmbedding, mem_product, mem_image, mem_univ, and_true]
  constructor
  · intro hmem
    have hsh : bucketShard m
        ((bitDomainEquiv (shardBits_le_bucketBits m)).symm (sh, (suffixSplitEquiv hma z).1)) = σ :=
      hB _ hmem
    unfold bucketShard at hsh
    rw [Equiv.apply_symm_apply] at hsh
    refine ⟨hsh, ⟨(suffixSplitEquiv hma z).1, (suffixSplitEquiv hma z).2⟩,
      ⟨_, hmem, ?_⟩, (suffixSplitEquiv hma).symm_apply_apply z⟩
    unfold bucketLocal
    rw [Equiv.apply_symm_apply]
  · rintro ⟨hsh, ⟨loc, q⟩, ⟨b, hb, hloc⟩, rfl⟩
    rw [hsh, Equiv.apply_symm_apply]
    have hb_eq : bitDomainEquiv (shardBits_le_bucketBits m) b = (σ, loc) :=
      Prod.ext (hB b hb) hloc
    rwa [← hb_eq, Equiv.symm_apply_apply]

theorem card_intraShardSuffixSet {a m : ℕ} (hma : m ≤ a)
    (σ : Fin (2 ^ shardBits m)) {B : Finset (Fin (2 ^ m))}
    (hB : ∀ b ∈ B, bucketShard m b = σ) :
    #(intraShardSuffixSet hma B) = #B * 2 ^ (a - m) := by
  unfold intraShardSuffixSet
  rw [card_map, card_product, card_univ, Fintype.card_fin]
  have hinj : Set.InjOn (bucketLocal m) (B : Set (Fin (2 ^ m))) := by
    intro b₁ hb₁ b₂ hb₂ hloc
    exact (bitDomainEquiv (shardBits_le_bucketBits m)).injective
      (Prod.ext ((hB b₁ hb₁).trans (hB b₂ hb₂).symm) hloc)
  rw [card_image_of_injOn hinj]

theorem prob_shardTuple_event_eq {T : Type*} [Fintype T] [DecidableEq T]
    {a m b_aux : ℕ} [Nonempty (T ↪ Fin (2 ^ suffixBits a m))]
    (σ : Fin (2 ^ shardBits m))
    (Q : T → Finset (Fin (2 ^ suffixBits a m)))
    (A : T → Finset (Fin (2 ^ b_aux))) :
    ((PMF.uniformOfFintype
        ((T → Fin (2 ^ shardBits m)) ×
          ((T ↪ Fin (2 ^ suffixBits a m)) × (T → Fin (2 ^ b_aux))))).toOuterMeasure
      {p | let (sh, emb, aux) := p; ∀ i : T, sh i = σ ∧ emb i ∈ Q i ∧ aux i ∈ A i}).toReal =
      ((1 : ℝ) / (2 ^ shardBits m : ℝ)) ^ Fintype.card T *
        ((PMF.uniformOfFintype (T ↪ Fin (2 ^ suffixBits a m))).toOuterMeasure
          {e | ∀ i : T, e i ∈ Q i}).toReal *
        (∏ i : T, ((#(A i) : ℝ) / (2 ^ b_aux : ℝ))) := by
  classical
  let E₁ : Finset (T → Fin (2 ^ shardBits m)) := {fun _ => σ}
  let S₂ : Set (T ↪ Fin (2 ^ suffixBits a m)) := {e | ∀ i : T, e i ∈ Q i}
  let E₂ : Finset (T ↪ Fin (2 ^ suffixBits a m)) := univ.filter (· ∈ S₂)
  let E₃ : Finset (T → Fin (2 ^ b_aux)) := Fintype.piFinset A
  let S_all : Set ((T → Fin (2 ^ shardBits m)) ×
      ((T ↪ Fin (2 ^ suffixBits a m)) × (T → Fin (2 ^ b_aux)))) :=
    {p | let (sh, emb, aux) := p; ∀ i : T, sh i = σ ∧ emb i ∈ Q i ∧ aux i ∈ A i}
  change ((PMF.uniformOfFintype _).toOuterMeasure S_all).toReal = _
  rw [toOuterMeasure_uniformOfFintype_toReal, toOuterMeasure_uniformOfFintype_toReal]
  have hfilt : univ.filter (· ∈ S_all) = E₁ ×ˢ (E₂ ×ˢ E₃) := by
    ext ⟨f₁, e, f₃⟩
    simp only [mem_filter, mem_univ, true_and, S_all, Set.mem_ofPred_eq, mem_product,
      E₁, mem_singleton, funext_iff, E₂, S₂, E₃, Fintype.mem_piFinset, forall_and]
  rw [hfilt, card_product, card_product, card_singleton, Fintype.card_piFinset]
  simp only [Fintype.card_prod, Fintype.card_pi, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Nat.cast_mul, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_prod]
  rw [one_div_pow, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]
  ring

end Cslib.DataStructure.Dictionary.KickTree
