/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.Schedule
import CslibFrontier.Foundations.Data.Nat.Choose
import CslibFrontier.Foundations.Data.Nat.Choose.Vandermonde
import CslibFrontier.Foundations.Data.Nat.Log
import CslibFrontier.Foundations.Data.Nat.Power
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Multi-Level Subconstant-Redundancy Bit Budget and Canonical Large-Parameter Schedule

This module builds on `CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.Schedule` to
formalize the complete Section 5 bit-budget accounting (`totalTreeBits`), the polynomial-universe
large-parameter regime (`ValidRegime`), the canonical Section 5 parameter instantiation
(`canonicalSchedule`), its concentration readiness (`canonicalSchedule_concentrationReady`), and
the end-to-end pure space bound `totalTreeBits ≤ infoBits U V n + spaceConst * R`
([LiLiangYuZhou2024, Sections 5.1–5.2 and 5.4–5.6];
[arXiv:2310.20536v1](https://arxiv.org/abs/2310.20536v1), PDF pp. 25–36 / printed pp. 24–35).

## Source mapping, adaptations, and scope

* **Bit-budget conservation (`Section 5.2`, PDF pp. 27–30 / printed pp. 26–29; `Section 5.6`,
  PDF pp. 35–36 / printed pp. 34–35)**:
  - Leaf nodes (`ℓ = k`) store fixed-capacity minimaps (`Minimap.FixedEncoded`, `m = nLow k`),
    contributing `allLeavesBits ≤ infoBits paddedUniv V n_L + 3 * numNodes k` via Vandermonde's
    inequality (`allLeavesBits_le_padded_infoBits_add`).
  - Inner nodes (`2 ≤ ℓ < k`) store `SuccinctBucket` metadata + `(quot, val)` slots; root nodes
    (`ℓ = 1`) store `SuccinctBucket` metadata + `(quot, localSlotIdx)` slots indexing a slab+tail
    shared root value pool (`SuccinctBucket.globalMetaLen rootValPoolCap * globalPtrBits
    rootValPoolCap` directory bits + `rootValPoolCap` `⌈log₂ V⌉`-bit value slots), avoiding `V`
    overhead on unused root capacity (`totalTreeBits_le_padded_infoBits_add`).
  - Non-root waiting lists (`allWaitingListsBits`), regime-switched child-router and ID-compressor
    seeds (`allHashSeedsBits`), and all four shared global lookup tables (`sharedTablesBits`:
    leaf dynamic-matching permutations, shared minimap lookup table, Four-Russians `clmul` table,
    and Section 5.6 level-3 DFS subtree lookup table) sum to `O(R_eff) ≤ O(R)` bits.
* **Small-node child-router regime switch (`Section 5.4` & `Claim B.2` adaptation)**:
  Nodes with `nLow ℓ ≥ childRouterThreshold epsInv alphaInv` use Thorup's `DoubleTabulation`
  (`ChildRouterSeed`), whereas nodes with `nLow ℓ < childRouterThreshold epsInv alphaInv` switch
  to `(2 * childRouterHalfInd (nHigh ℓ))`-wise `trinomialPolyHash`, avoiding the doubly exponential
  `childRouterThreshold` lower bound on `thresholdN`.
* **Out-of-scope gaps**: Word-RAM `Memory.Prog` compilation (`T76`–`T77`), Section 4 small-`R`
  adapter trees (`R < n / log₂ ^ 0.1 n`), strong history independence, dynamic resizing in `|S|`,
  and super-polynomial key universes (`U > n ^ (1 + α_max)`) are out of scope here.

## Main definitions

* `Cslib.DataStructure.Dictionary.SubconstantRedundancy.waitingListBits`,
  `succinctTableMetaBits`, `TreeSchedule.routerSeedBits`, `TreeSchedule.nodeHashSeedBits`,
  `TreeSchedule.nodeMetaBits`, `TreeSchedule.subtreeMetaBits`, `TreeSchedule.allLeavesBits`,
  `TreeSchedule.allInnerTablesBits`, `TreeSchedule.allRootTablesBits`,
  `TreeSchedule.allWaitingListsBits`, `TreeSchedule.allHashSeedsBits`,
  `TreeSchedule.sharedTablesBits`, `TreeSchedule.totalTreeBits`, `TreeSchedule.redundancySlack`:
  complete node, subtree, and global table bit-budget accounting.
* `Cslib.DataStructure.Dictionary.SubconstantRedundancy.routerEpsInv`, `routerAlphaInv`,
  `thresholdLogN`, `thresholdN`, `ValidRegime`, `canonicalSchedule`, `spaceConst`:
  large-parameter polynomial-universe regime and canonical Section 5 schedule.

## Main results

* `TreeSchedule.allLeavesBits_le_padded_infoBits_add`,
  `TreeSchedule.nonLeaf_infoBits_conservation`,
  `TreeSchedule.totalTreeBits_le_padded_infoBits_add`: general `TreeSchedule` bit conservation
  (`totalTreeBits ≤ infoBits paddedUniv V cap + redundancySlack`, valid for all `1 ≤ V`).
* `canonicalSchedule_concentrationReady`: `canonicalSchedule` satisfies `ConcentrationReady` across
  the entire `ValidRegime`.
* `totalTreeBits_le_infoBits_add`: end-to-end pure bit-budget bound
  `totalTreeBits ≤ infoBits U V n + spaceConst * R`.

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
open Finset

/-- Waiting-list bit width `⌈log₂(cap + 1)⌉ + cap * (I_cur + I_prev)` (`Section 5.2`). -/
@[expose]
def waitingListBits (cap I_cur I_prev : ℕ) : ℕ :=
  Nat.clog 2 (cap + 1) + cap * (I_cur + I_prev)

/-- Metadata bit width of a `SuccinctBucket` storage table on `Fin (2 ^ I)` with capacity `m`:
`m` ID-quotients of `quotientBits (2 ^ I) m` bits, `LocalMeta`, `GlobalMeta`, and the 3-wise
trinomial hash seed (`Section 5.2` & `Section 5.6`). -/
@[expose]
def succinctTableMetaBits (I m : ℕ) : ℕ :=
  m * FeistelQuotient.quotientBits (2 ^ I) m +
    SuccinctBucket.localMetaLen m * SuccinctBucket.effBucketPosBits m +
    SuccinctBucket.globalMetaLen m * SuccinctBucket.globalPtrBits m +
    3 * Cslib.Probability.trinomialDeg (2 ^ FeistelQuotient.quotientBits (2 ^ I) m)
      (SuccinctBucket.totalMicroBits m)

namespace TreeSchedule

variable (P : TreeSchedule)

/-! ## Section 1: Tree bit-budget accounting and core information conservation -/

/-- Bit width of the regime-switched child-router seed at level `0 ≤ ℓ < depth`:
`FeistelPerm.childRouterSeedBits` when `childRouterThreshold epsInv alphaInv ≤ nLow ℓ`, and
`2 * childRouterHalfInd (nHigh ℓ) * trinomialDeg T_ℓ s_ℓ` below `childRouterThreshold`. -/
@[expose]
def routerSeedBits (ℓ : ℕ) : ℕ :=
  if FeistelPerm.childRouterThreshold P.epsInv P.alphaInv ≤ P.nLow ℓ then
    let c := FeistelPerm.childRouterChars P.epsInv
    let q := FeistelPerm.childRouterRep P.epsInv P.alphaInv
    let b := FeistelPerm.childRouterCharBits c (P.routerRightUniv ℓ)
    FeistelPerm.childRouterSeedBits c q b (P.branchBits ℓ)
  else
    2 * FeistelPerm.childRouterHalfInd (P.nHigh ℓ) *
      Cslib.Probability.trinomialDeg (P.routerRightUniv ℓ) (P.branchBits ℓ)

/-- Per-node hash-seed bits (`g_u` in `Section 5.5`): `routerSeedBits 0` at `ℓ = 0`,
`routerSeedBits ℓ + idCompressorSeedBits` for `1 ≤ ℓ < depth`, and `idCompressorSeedBits` at
`ℓ = depth`. -/
@[expose]
def nodeHashSeedBits (ℓ : ℕ) : ℕ :=
  if ℓ = 0 then P.routerSeedBits 0
  else
    (if ℓ < P.depth then P.routerSeedBits ℓ else 0) +
      FeistelPerm.idCompressorSeedBits (P.idBits ℓ) (P.idCompRightUniv ℓ)

/-- Per-node metadata bits (`Section 5.6` ID-set + waiting-list + hash-seed metadata, excluding
`O(w)`-bit quotient/value payload slots and independent of `valBound` at leaf spillovers via
`2 * nLow depth` upper bound). -/
@[expose]
def nodeMetaBits (ℓ : ℕ) : ℕ :=
  if ℓ = 0 then P.routerSeedBits 0
  else if ℓ = 1 then
    P.nodeHashSeedBits 1 + succinctTableMetaBits (P.idBits 1) (P.tableCap 1)
  else if ℓ < P.depth then
    P.nodeHashSeedBits ℓ +
      waitingListBits (P.waitCap ℓ) (P.idBits ℓ) (P.idBits (ℓ - 1)) +
      succinctTableMetaBits (P.idBits ℓ) (P.tableCap ℓ)
  else
    let n' := P.nLow P.depth
    P.nodeHashSeedBits P.depth +
      waitingListBits (P.waitCap P.depth) (P.idBits P.depth) (P.idBits (P.depth - 1)) +
      Nat.clog 2 ((2 ^ P.idBits P.depth).choose n' * (2 * n') ^ n')

/-- Total DFS pre-order subtree metadata bit width rooted at a single level-`ℓ` node
(`1 ≤ ℓ ≤ depth`, `Section 5.6`). -/
@[expose]
def subtreeMetaBits (ℓ : ℕ) : ℕ :=
  ∑ j ∈ Finset.Icc ℓ P.depth,
    (P.numNodes j / P.numNodes ℓ) * P.nodeMetaBits j

/-- Total leaf representation bits across all `N_depth` fixed-capacity leaf minimaps
(`header + slots`). -/
@[expose]
def allLeavesBits : ℕ :=
  P.numNodes P.depth *
    Minimap.bitWidth (2 ^ P.idBits P.depth) (P.nLow P.depth) (P.quotUniv P.depth * P.valBound)

/-- Total inner-node storage-table bits (`SuccinctBucket` metadata + `quot` + `val` payload slots)
across levels `2 ≤ ℓ < depth`. -/
@[expose]
def allInnerTablesBits : ℕ :=
  ∑ ℓ ∈ Finset.Ico 2 P.depth,
    P.numNodes ℓ *
      (succinctTableMetaBits (P.idBits ℓ) (P.tableCap ℓ) +
        P.tableCap ℓ * (Nat.clog 2 (P.quotUniv ℓ) + Nat.clog 2 P.valBound))

/-- Slab size `K_slab = (⌈log₂(cap + 2)⌉) ^ 2` for the shared root value pool. -/
@[expose]
def rootSlabSize : ℕ :=
  (Nat.clog 2 (P.cap + 2)) ^ 2

/-- Directory and free-list overhead bits of the slab+tail shared root value pool across all `N_1`
roots (`O(n / log n + n / log ^ 6 n)` bits, independent of `valBound`). -/
@[expose]
def rootPoolDirBits : ℕ :=
  let ptrBits := Nat.clog 2 (P.cap + 2)
  let K := max P.rootSlabSize 1
  (P.numNodes 1 * (P.tableCap 1 / K + 1 + K) + P.rootValPoolCap / K + 4) * ptrBits

/-- Total root storage-table bits (`SuccinctBucket` metadata + `(quot, localIdx)` slots across all
`N_1` roots) plus the shared root value pool (`rootValPoolCap` `⌈log₂ V⌉`-bit value slots +
`rootPoolDirBits` slab/tail directory). -/
@[expose]
def allRootTablesBits : ℕ :=
  P.numNodes 1 *
      (succinctTableMetaBits (P.idBits 1) (P.tableCap 1) +
        P.tableCap 1 * (Nat.clog 2 (P.quotUniv 1) + Nat.clog 2 (P.tableCap 1 + 1))) +
    P.rootValPoolCap * Nat.clog 2 P.valBound +
    P.rootPoolDirBits

/-- Total waiting-list bits across all non-root levels `2 ≤ ℓ ≤ depth`. -/
@[expose]
def allWaitingListsBits : ℕ :=
  ∑ ℓ ∈ Finset.Icc 2 P.depth,
    P.numNodes ℓ * waitingListBits (P.waitCap ℓ) (P.idBits ℓ) (P.idBits (ℓ - 1))

/-- Total hash-seed bits across the top router (`ℓ = 0`) and all tree nodes (`1 ≤ ℓ ≤ depth`). -/
@[expose]
def allHashSeedsBits : ℕ :=
  P.routerSeedBits 0 +
    ∑ ℓ ∈ Finset.Icc 1 P.depth, P.numNodes ℓ * P.nodeHashSeedBits ℓ

/-- Total bit budget of shared global lookup tables:
(1) leaf `DynamicMatching.Scheme` permutations,
(2) shared leaf `Minimap.lookupHeader` table (`Lemma 3.7`),
(3) shared Four-Russians carryless-multiplication table (`KWise`), and
(4) shared Section 5.6 level-3 DFS subtree lookup table (when `3 ≤ depth`). -/
@[expose]
def sharedTablesBits : ℕ :=
  let U_leaf := 2 ^ P.idBits P.depth
  let n_leaf := P.nLow P.depth
  let matchBits := U_leaf * (U_leaf + n_leaf) * Nat.clog 2 (U_leaf + n_leaf + 1)
  let minimapTabBits := U_leaf *
      Minimap.headerUniv U_leaf n_leaf (P.quotUniv P.depth * P.valBound) n_leaf *
      Nat.clog 2 (2 * n_leaf ^ 2 + 2)
  let clmulBits := 2 ^ (2 * (Nat.log 2 (max P.cap 2) / 3)) *
      (6 * Nat.clog 2 (max P.paddedUniv 2) + 6)
  let dfsBits :=
    if 3 ≤ P.depth then
      2 ^ (P.subtreeMetaBits 3 + P.idBits 3) * (Nat.clog 2 (P.cap + P.depth + 2) + P.idBits 3)
    else 0
  matchBits + minimapTabBits + clmulBits + dfsBits

/-- **Total pure tree representation bits** summing all leaf minimaps, inner/root `SuccinctBucket`
storage tables, shared root value pool, waiting lists, Feistel / trinomial hash seeds, and shared
global lookup tables. -/
@[expose]
def totalTreeBits : ℕ :=
  P.allLeavesBits + P.allInnerTablesBits + P.allRootTablesBits +
    P.allWaitingListsBits + P.allHashSeedsBits + P.sharedTablesBits

/-- Leaf minimap bit conservation (`Section 5.2`): across all `N_depth` full-capacity leaves
(`n_L = N_depth * nLow depth`), `allLeavesBits ≤ infoBits paddedUniv valBound n_L + 3 * N_depth`. -/
theorem allLeavesBits_le_padded_infoBits_add :
    P.allLeavesBits ≤
      infoBits P.paddedUniv P.valBound (P.numNodes P.depth * P.nLow P.depth) +
        3 * P.numNodes P.depth := by
  set N_k := P.numNodes P.depth
  set A := 2 ^ P.idBits P.depth
  set m := P.nLow P.depth
  set Q_k := P.quotUniv P.depth
  set V := P.valBound
  have hm1 : 1 ≤ m := P.nLow_pos le_rfl
  have hmA : m ≤ A := by
    dsimp only [m, nLow, A]
    rw [ite_eq_right (by have := P.two_le_depth; omega)]
    exact (Nat.sub_le _ _).trans
      ((Nat.le_add_right _ _).trans (P.nHigh_le_two_pow_idBits P.depth
        (by have := P.two_le_depth; omega) le_rfl))
  have hXV : 1 ≤ Q_k * V := Nat.mul_pos (P.quotUniv_pos P.depth) P.val_pos
  have hleaf := Minimap.bitWidth_le_infoBits_add_two hm1 hmA hXV
  set X_leaf := A.choose m * (Q_k * V) ^ m
  have hX_pos : 1 ≤ X_leaf := Nat.mul_pos (Nat.choose_pos hmA) (Nat.pow_pos hXV)
  have hpow_clog : 2 ^ Minimap.infoBits A m (Q_k * V) ≤ 2 * X_leaf :=
    Nat.pow_clog_le_mul Nat.one_lt_two (by omega)
  have hvand : (A.choose m) ^ N_k ≤ (N_k * A).choose (N_k * m) := by
    simpa only [Finset.prod_const, Finset.sum_const, Finset.card_range, smul_eq_mul] using
      Nat.prod_choose_le_choose_sum (Finset.range N_k) (fun _ => A) (fun _ => m)
  have hscale : Q_k ^ (N_k * m) * (N_k * A).choose (N_k * m) ≤
      P.paddedUniv.choose (N_k * m) := by
    have hmul_le : N_k * m ≤ N_k * A := Nat.mul_le_mul_left N_k hmA
    have h := Nat.pow_mul_choose_le_choose_mul (P.quotUniv_pos P.depth) hmul_le
    have hpad : Q_k * (N_k * A) = P.paddedUniv := by
      calc Q_k * (N_k * A) = N_k * A * Q_k := by ring
        _ = P.paddedUniv :=
            P.numNodes_mul_idUniv_mul_quotUniv (by have := P.two_le_depth; omega) le_rfl
    rwa [hpad] at h
  have hprod_le : X_leaf ^ N_k ≤ P.paddedUniv.choose (N_k * m) * V ^ (N_k * m) := by
    calc X_leaf ^ N_k
        = (A.choose m) ^ N_k * (Q_k ^ m * V ^ m) ^ N_k := by
          dsimp only [X_leaf]; rw [Nat.mul_pow, Nat.mul_pow]
      _ = (Q_k ^ (N_k * m) * (A.choose m) ^ N_k) * V ^ (N_k * m) := by
          rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm m N_k]; ring
      _ ≤ (Q_k ^ (N_k * m) * (N_k * A).choose (N_k * m)) * V ^ (N_k * m) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hvand)
      _ ≤ P.paddedUniv.choose (N_k * m) * V ^ (N_k * m) :=
          Nat.mul_le_mul_right _ hscale
  set Y := P.paddedUniv.choose (N_k * m) * V ^ (N_k * m)
  have hpow_tot : 2 ^ (N_k * Minimap.infoBits A m (Q_k * V)) ≤
      2 ^ (N_k + Nat.clog 2 Y) := by
    calc 2 ^ (N_k * Minimap.infoBits A m (Q_k * V))
        = (2 ^ Minimap.infoBits A m (Q_k * V)) ^ N_k := by rw [Nat.mul_comm, Nat.pow_mul]
      _ ≤ (2 * X_leaf) ^ N_k := Nat.pow_le_pow_left hpow_clog N_k
      _ = 2 ^ N_k * X_leaf ^ N_k := Nat.mul_pow 2 X_leaf N_k
      _ ≤ 2 ^ N_k * Y := Nat.mul_le_mul_left _ hprod_le
      _ ≤ 2 ^ N_k * 2 ^ Nat.clog 2 Y :=
          Nat.mul_le_mul_left _ (Nat.le_pow_clog Nat.one_lt_two Y)
      _ = 2 ^ (N_k + Nat.clog 2 Y) := (Nat.pow_add 2 N_k _).symm
  have hexp_le : N_k * Minimap.infoBits A m (Q_k * V) ≤ N_k + infoBits P.paddedUniv V (N_k * m) :=
    (Nat.pow_le_pow_iff_right Nat.one_lt_two).mp hpow_tot
  calc P.allLeavesBits
      = N_k * Minimap.bitWidth A m (Q_k * V) := rfl
    _ ≤ N_k * (Minimap.infoBits A m (Q_k * V) + 2) := Nat.mul_le_mul_left N_k hleaf
    _ = N_k * Minimap.infoBits A m (Q_k * V) + 2 * N_k := by ring
    _ ≤ infoBits P.paddedUniv V (N_k * m) + 3 * N_k := by omega

/-- Non-leaf quotient + value bit conservation: combining `infoBits U_pad V n_L` with `d = n - n_L`
slots of `(⌈log₂ ⌈U_pad / n⌉⌉ + ⌈log₂ V⌉)` bits never exceeds `infoBits U_pad V n + 3 * d + 1`
whenever `3 * n ≤ U_pad`. -/
theorem nonLeaf_infoBits_conservation {U_pad V n n_L : ℕ}
    (hn : 1 ≤ n) (hV : 1 ≤ V) (hnL : n_L ≤ n) (hU : 3 * n ≤ U_pad) :
    let d := n - n_L
    let q_base := Nat.clog 2 ((U_pad + n - 1) / n)
    infoBits U_pad V n_L + d * (q_base + Nat.clog 2 V) ≤ infoBits U_pad V n + 3 * d + 1 := by
  intro d q_base
  set Q_up := (U_pad + n - 1) / n
  have hnU : n ≤ U_pad := by omega
  have hnLU : n_L ≤ U_pad := hnL.trans hnU
  have hQ_pos : 1 ≤ Q_up := (Nat.le_div_iff_mul_le hn).mpr (by omega)
  have hnQ : n * Q_up ≤ 2 * (U_pad - n + 1) := by
    have hmul : Q_up * n ≤ U_pad + n - 1 := Nat.div_mul_le_self (U_pad + n - 1) n
    have hcomm : Q_up * n = n * Q_up := Nat.mul_comm _ _
    omega
  have h2q : 2 ^ q_base ≤ 2 * Q_up := Nat.pow_clog_le_mul Nat.one_lt_two (by omega)
  have h2V : 2 ^ Nat.clog 2 V ≤ 2 * V := Nat.pow_clog_le_mul Nat.one_lt_two (by omega)
  have hstep : n * 2 ^ (q_base + Nat.clog 2 V) ≤ 8 * (U_pad - n + 1) * V := by
    calc n * 2 ^ (q_base + Nat.clog 2 V)
        = n * (2 ^ q_base * 2 ^ Nat.clog 2 V) := by rw [Nat.pow_add]
      _ ≤ n * ((2 * Q_up) * (2 * V)) :=
          Nat.mul_le_mul_left n (Nat.mul_le_mul h2q h2V)
      _ = 4 * (n * Q_up) * V := by ring
      _ ≤ 4 * (2 * (U_pad - n + 1)) * V :=
          Nat.mul_le_mul_right V (Nat.mul_le_mul_left 4 hnQ)
      _ = 8 * (U_pad - n + 1) * V := by ring
  have hpow_d : n ^ d * 2 ^ (d * (q_base + Nat.clog 2 V)) ≤
      2 ^ (3 * d) * (U_pad - n + 1) ^ d * V ^ d := by
    calc n ^ d * 2 ^ (d * (q_base + Nat.clog 2 V))
        = (n * 2 ^ (q_base + Nat.clog 2 V)) ^ d := by
          rw [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_comm d]
      _ ≤ (8 * (U_pad - n + 1) * V) ^ d := Nat.pow_le_pow_left hstep d
      _ = 8 ^ d * (U_pad - n + 1) ^ d * V ^ d := by rw [Nat.mul_pow, Nat.mul_pow]
      _ = 2 ^ (3 * d) * (U_pad - n + 1) ^ d * V ^ d := by
          have h8 : (8 : ℕ) = 2 ^ 3 := by decide
          rw [h8, ← Nat.pow_mul]
  set X_L := U_pad.choose n_L * V ^ n_L
  set X_n := U_pad.choose n * V ^ n
  have hXL_pos : 1 ≤ X_L := Nat.mul_pos (Nat.choose_pos hnLU) (Nat.pow_pos hV)
  have hsub_eq : n - d = n_L := by omega
  have hchoose := Nat.choose_sub_mul_pow_le (m := U_pad) (ℓ := n) (s := d) (Nat.sub_le n n_L) hnU
  rw [hsub_eq] at hchoose
  have hV_split : V ^ n_L * V ^ d = V ^ n := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hmul_nd : n ^ d * (X_L * 2 ^ (d * (q_base + Nat.clog 2 V))) ≤
      n ^ d * (2 ^ (3 * d) * X_n) := by
    calc n ^ d * (X_L * 2 ^ (d * (q_base + Nat.clog 2 V)))
        = U_pad.choose n_L * V ^ n_L * (n ^ d * 2 ^ (d * (q_base + Nat.clog 2 V))) := by ring
      _ ≤ U_pad.choose n_L * V ^ n_L * (2 ^ (3 * d) * (U_pad - n + 1) ^ d * V ^ d) :=
          Nat.mul_le_mul_left _ hpow_d
      _ = (U_pad.choose n_L * (U_pad - n + 1) ^ d) * (2 ^ (3 * d) * (V ^ n_L * V ^ d)) := by ring
      _ ≤ (U_pad.choose n * n ^ d) * (2 ^ (3 * d) * V ^ n) := by
          rw [hV_split]
          exact Nat.mul_le_mul_right _ hchoose
      _ = n ^ d * (2 ^ (3 * d) * X_n) := by dsimp only [X_n]; ring
  have hXL_le : X_L * 2 ^ (d * (q_base + Nat.clog 2 V)) ≤ 2 ^ (3 * d) * X_n :=
    Nat.le_of_mul_le_mul_left hmul_nd (Nat.pow_pos hn)
  have hpow_tot : 2 ^ (infoBits U_pad V n_L + d * (q_base + Nat.clog 2 V)) ≤
      2 ^ (infoBits U_pad V n + 3 * d + 1) := by
    calc 2 ^ (infoBits U_pad V n_L + d * (q_base + Nat.clog 2 V))
        = 2 ^ infoBits U_pad V n_L * 2 ^ (d * (q_base + Nat.clog 2 V)) := Nat.pow_add _ _ _
      _ ≤ (2 * X_L) * 2 ^ (d * (q_base + Nat.clog 2 V)) :=
          Nat.mul_le_mul_right _ (Nat.pow_clog_le_mul Nat.one_lt_two (by omega))
      _ = 2 * (X_L * 2 ^ (d * (q_base + Nat.clog 2 V))) := by ring
      _ ≤ 2 * (2 ^ (3 * d) * X_n) := Nat.mul_le_mul_left 2 hXL_le
      _ ≤ 2 * (2 ^ (3 * d) * 2 ^ infoBits U_pad V n) :=
          Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ (Nat.le_pow_clog Nat.one_lt_two X_n))
      _ = 2 ^ (infoBits U_pad V n + 3 * d + 1) := by
          rw [← Nat.pow_add, ← Nat.pow_succ']
          congr 1
          omega
  exact (Nat.pow_le_pow_iff_right Nat.one_lt_two).mp hpow_tot

/-- `V`-independent redundancy slack combining inner/root `SuccinctBucket` metadata, per-level
quotient-bit excess above `⌈log₂ ⌈U_pad / cap⌉⌉`, unused root slot slack, root slab/tail directory,
waiting lists, hash seeds, and shared lookup tables. -/
@[expose]
def redundancySlack : ℕ :=
  let n_L := P.numNodes P.depth * P.nLow P.depth
  let d := P.cap - n_L
  let rootExtra := P.numNodes 1 * P.tableCap 1 - P.rootValPoolCap
  let q_base := Nat.clog 2 ((P.paddedUniv + P.cap - 1) / P.cap)
  3 * P.numNodes P.depth + 3 * d + 1 +
    (∑ ℓ ∈ Finset.Ico 2 P.depth,
      P.numNodes ℓ *
        (succinctTableMetaBits (P.idBits ℓ) (P.tableCap ℓ) +
          P.tableCap ℓ * Nat.clog 2 (2 * (P.nFloor ℓ + 1)))) +
    P.numNodes 1 *
      (succinctTableMetaBits (P.idBits 1) (P.tableCap 1) +
        P.tableCap 1 *
          (Nat.clog 2 (2 * (P.nFloor 1 + 1)) + Nat.clog 2 (P.tableCap 1 + 1))) +
    rootExtra * q_base + P.rootPoolDirBits +
    P.allWaitingListsBits + P.allHashSeedsBits + P.sharedTablesBits

/-- **General `TreeSchedule` bit-budget bound** (for all `1 ≤ valBound`, with zero upper bound on
`valBound`): whenever `cap ≤ N_ℓ * (nFloor ℓ + 1)` across `1 ≤ ℓ < depth` and
`3 * cap ≤ paddedUniv`, `totalTreeBits ≤ infoBits paddedUniv valBound cap + redundancySlack`. -/
theorem totalTreeBits_le_padded_infoBits_add
    (hdiv : ∀ ℓ, 1 ≤ ℓ → ℓ < P.depth → P.cap ≤ P.numNodes ℓ * (P.nFloor ℓ + 1))
    (hU3 : 3 * P.cap ≤ P.paddedUniv) :
    P.totalTreeBits ≤ infoBits P.paddedUniv P.valBound P.cap + P.redundancySlack := by
  set n_L := P.numNodes P.depth * P.nLow P.depth
  set d := P.cap - n_L
  set Q_up := (P.paddedUniv + P.cap - 1) / P.cap
  set q_base := Nat.clog 2 Q_up
  have hcap1 : 1 ≤ P.cap := by have := P.two_le_cap; omega
  have hnL_le : n_L ≤ P.cap := by
    have htot := P.total_value_slots_eq_cap
    omega
  have hd_eq :
      (∑ ℓ ∈ Finset.Ico 2 P.depth, P.numNodes ℓ * P.tableCap ℓ) + P.rootValPoolCap = d := by
    have htot := P.total_value_slots_eq_cap
    omega
  have hquot_le : ∀ ℓ, 1 ≤ ℓ → ℓ < P.depth →
      Nat.clog 2 (P.quotUniv ℓ) ≤ q_base + Nat.clog 2 (2 * (P.nFloor ℓ + 1)) := by
    intro ℓ h1 hlt
    have hcons := P.numNodes_mul_idUniv_mul_quotUniv h1 hlt.le
    have hNQ : P.numNodes ℓ * P.quotUniv ℓ ≤ P.paddedUniv := by
      calc P.numNodes ℓ * P.quotUniv ℓ
          ≤ P.numNodes ℓ * (2 ^ P.idBits ℓ * P.quotUniv ℓ) :=
            Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))
        _ = P.paddedUniv := by rw [← Nat.mul_assoc, hcons]
    have hQup_cov : P.paddedUniv ≤ P.cap * Q_up := by
      have hmod := Nat.div_add_mod (P.paddedUniv + P.cap - 1) P.cap
      have hrem := Nat.mod_lt (P.paddedUniv + P.cap - 1) hcap1
      dsimp only [Q_up]
      omega
    have hmul_cap : P.cap * P.quotUniv ℓ ≤ P.cap * (Q_up * (P.nFloor ℓ + 1)) := by
      calc P.cap * P.quotUniv ℓ
          ≤ (P.numNodes ℓ * (P.nFloor ℓ + 1)) * P.quotUniv ℓ :=
            Nat.mul_le_mul_right _ (hdiv ℓ h1 hlt)
        _ = (P.numNodes ℓ * P.quotUniv ℓ) * (P.nFloor ℓ + 1) := by ring
        _ ≤ P.paddedUniv * (P.nFloor ℓ + 1) := Nat.mul_le_mul_right _ hNQ
        _ ≤ (P.cap * Q_up) * (P.nFloor ℓ + 1) := Nat.mul_le_mul_right _ hQup_cov
        _ = P.cap * (Q_up * (P.nFloor ℓ + 1)) := by ring
    have hQ_le : P.quotUniv ℓ ≤ Q_up * (P.nFloor ℓ + 1) :=
      Nat.le_of_mul_le_mul_left hmul_cap hcap1
    refine Nat.clog_le_of_le_pow ?_
    calc P.quotUniv ℓ
        ≤ Q_up * (P.nFloor ℓ + 1) := hQ_le
      _ ≤ 2 ^ q_base * (2 * (P.nFloor ℓ + 1)) :=
          Nat.mul_le_mul (Nat.le_pow_clog Nat.one_lt_two Q_up) (by omega)
      _ ≤ 2 ^ q_base * 2 ^ Nat.clog 2 (2 * (P.nFloor ℓ + 1)) :=
          Nat.mul_le_mul_left _ (Nat.le_pow_clog Nat.one_lt_two _)
      _ = 2 ^ (q_base + Nat.clog 2 (2 * (P.nFloor ℓ + 1))) := (Nat.pow_add 2 _ _).symm
  have hinner_le : P.allInnerTablesBits ≤
      (∑ ℓ ∈ Finset.Ico 2 P.depth, P.numNodes ℓ * P.tableCap ℓ) *
          (q_base + Nat.clog 2 P.valBound) +
        ∑ ℓ ∈ Finset.Ico 2 P.depth,
          P.numNodes ℓ *
            (succinctTableMetaBits (P.idBits ℓ) (P.tableCap ℓ) +
              P.tableCap ℓ * Nat.clog 2 (2 * (P.nFloor ℓ + 1))) := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun ℓ hℓ => ?_
    obtain ⟨h2, hlt⟩ := Finset.mem_Ico.mp hℓ
    have hq := hquot_le ℓ (by omega) hlt
    have hmul : P.numNodes ℓ * P.tableCap ℓ * Nat.clog 2 (P.quotUniv ℓ) ≤
        P.numNodes ℓ * P.tableCap ℓ * (q_base + Nat.clog 2 (2 * (P.nFloor ℓ + 1))) :=
      Nat.mul_le_mul_left _ hq
    nlinarith
  have hroot_q := hquot_le 1 le_rfl (by have := P.two_le_depth; omega)
  have hroot_split : P.numNodes 1 * P.tableCap 1 * q_base ≤
      P.rootValPoolCap * q_base + (P.numNodes 1 * P.tableCap 1 - P.rootValPoolCap) * q_base := by
    have hle : P.numNodes 1 * P.tableCap 1 ≤
        P.rootValPoolCap + (P.numNodes 1 * P.tableCap 1 - P.rootValPoolCap) := by omega
    calc P.numNodes 1 * P.tableCap 1 * q_base
        ≤ (P.rootValPoolCap + (P.numNodes 1 * P.tableCap 1 - P.rootValPoolCap)) * q_base :=
          Nat.mul_le_mul_right q_base hle
      _ = P.rootValPoolCap * q_base +
          (P.numNodes 1 * P.tableCap 1 - P.rootValPoolCap) * q_base := Nat.add_mul _ _ _
  have hroot_le : P.allRootTablesBits ≤
      P.rootValPoolCap * (q_base + Nat.clog 2 P.valBound) +
        P.numNodes 1 *
          (succinctTableMetaBits (P.idBits 1) (P.tableCap 1) +
            P.tableCap 1 *
              (Nat.clog 2 (2 * (P.nFloor 1 + 1)) + Nat.clog 2 (P.tableCap 1 + 1))) +
        (P.numNodes 1 * P.tableCap 1 - P.rootValPoolCap) * q_base +
        P.rootPoolDirBits := by
    dsimp only [allRootTablesBits]
    have hmul1 : P.numNodes 1 * P.tableCap 1 * Nat.clog 2 (P.quotUniv 1) ≤
        P.numNodes 1 * P.tableCap 1 * (q_base + Nat.clog 2 (2 * (P.nFloor 1 + 1))) :=
      Nat.mul_le_mul_left _ hroot_q
    nlinarith
  have hleaves := P.allLeavesBits_le_padded_infoBits_add
  have hnonleaf := nonLeaf_infoBits_conservation hcap1 P.val_pos hnL_le hU3
  have hd_mul :
      (∑ ℓ ∈ Finset.Ico 2 P.depth, P.numNodes ℓ * P.tableCap ℓ) *
          (q_base + Nat.clog 2 P.valBound) +
        P.rootValPoolCap * (q_base + Nat.clog 2 P.valBound) =
      d * (q_base + Nat.clog 2 P.valBound) := by
    rw [← Nat.add_mul, hd_eq]
  dsimp only [totalTreeBits, redundancySlack]
  linarith

end TreeSchedule

end Cslib.DataStructure.Dictionary.SubconstantRedundancy
