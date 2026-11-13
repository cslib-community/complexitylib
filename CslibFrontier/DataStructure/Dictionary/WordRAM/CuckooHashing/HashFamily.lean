/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.CuckooHashing.HashFamily
public import CslibFrontier.DataStructure.HashFamily.WordRAM.KWise
public import CslibFrontier.DataStructure.HashFamily.WordRAM.Tabulation
public import CslibFrontier.Computability.WordRAM.RegisterFrame
public import CslibFrontier.DataStructure.HashFamily.WordRAM.DoubleTabulation
public import CslibFrontier.Probability.PMF.Bind
public import CslibFrontier.Probability.PMF.Map
public import CslibFrontier.Probability.PMF.UniformSubset
public import CslibFrontier.Probability.Uniform
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Regime-switched Word-RAM cuckoo hash family

This module realizes a cuckoo hash pair by two Word-RAM hash blocks. Below
`doubleTabThreshold c_exp`, each block uses `(2 * maxEvictions n_max + 2)`-wise independent
trinomial polynomial hashing. At or above the threshold it uses Mikkel Thorup's double
tabulation [Thorup2013]. The pure table and replay semantics and generic `IsCuckooHashPair`
contract are imported from `CslibFrontier.DataStructure.Dictionary.CuckooHashing.HashFamily`.

The bridge `CslibFrontier.DataStructure.Dictionary.WordRAM.CuckooHashing.Analysis` proves
`isCuckooHashPair_provableFamily`: the resulting family satisfies that contract with `C_walk = 3`
and `C_reh = 4` for every `n_max : ℕ`, whenever `U ≤ max n_max 4 ^ c_exp` and
`32 * max n_max 4 ≤ 2 ^ M`. The oblivious dictionary sequence model and constants are unchanged.

## Main definitions

* `Seed`, `seedLaw`, `evalHash1`, `evalHash2`: regime-switched seed space, uniform seed law, and
  deterministic hash evaluation.
* `IsCuckooHashFamily`: specialization of the generic hash-pair contract to this seed law and pair.
* `HashPairRep`, `initTableHashPairCode`, `resampleHashPairCode`, `evalHash1Code`, `evalHash2Code`:
  two-block Word-RAM layout, initialization, resampling, and evaluation programs.

## Main results

* `initTableHashPairCode_execWithin`, `resampleHashPairCode_execRand`, `evalHash1Code_execWithin`,
  `evalHash2Code_execWithin`: program correctness.
* `hashPairSpace_le`, `evalHashSteps_le`: `O_{c_exp}(n_max + 1)` words across all capacities, and
  at most `evalHashBound c_exp` evaluation instructions whenever `U ≤ max n_max 4 ^ c_exp` and
  `M ≤ max c_exp 1 * Nat.clog 2 (max n_max 4) + 5`.

## References

* [R. Pagh and F. F. Rodler, "Cuckoo hashing"][PaghRodler2004] (8 December 2003 author manuscript,
  Section 2.3, pp. 6–10).
* [M. Thorup, "Simple Tabulation, Fast Expanders, Double Tabulation, and High
  Independence"][Thorup2013] (FOCS 2013, pp. 90–99; `arXiv:1311.3121v2`, pp. 4–5, 11–13).
* [J. L. Carter and M. N. Wegman, "Universal classes of hash functions"][CarterWegman1979]
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing

open Cslib.WordRAM
open Cslib.Probability
open Cslib.Probability.PMF
open Cslib.DataStructure.Dictionary.CuckooHashing
open Cslib.DataStructure.HashFamily.WordRAM
open scoped ENNReal Finset

/-! ## Regime-switched seed space and evaluation -/

/-- Regime-indexed seed space for a single regime-switched hash block (`h₁` or `h₂`):
- When `reg = true` (`n_max < doubleTabThreshold c_exp`), a
  `(2 * maxEvictions n_max + 2)`-wise independent trinomial polynomial seed
  `Fin (cuckooK n_max) → Fin (2 ^ trinomialDeg U M)`.
- When `reg = false` (`doubleTabThreshold c_exp ≤ n_max`), a double-tabulation seed pair
  `DoubleTabTopSeed c d b × DoubleTabBotSeed d b M` with
  `c = DoubleTabulation.provableC c_exp`, `d = DoubleTabulation.provableD c_exp`, and
  `b = DoubleTabulation.provableB n_max`. -/
@[expose]
def SingleSeedAux (reg : Bool) (c_exp n_max U M : ℕ) : Type :=
  match reg with
  | true => Fin (cuckooK n_max) → Fin (2 ^ trinomialDeg U M)
  | false =>
    DoubleTabTopSeed (DoubleTabulation.provableC c_exp)
      (DoubleTabulation.provableD c_exp) (DoubleTabulation.provableB n_max) ×
    DoubleTabBotSeed (DoubleTabulation.provableD c_exp) (DoubleTabulation.provableB n_max) M

/-- Seed type for a single regime-switched hash block (`h₁` or `h₂`). -/
abbrev SingleSeed (c_exp n_max U M : ℕ) : Type :=
  SingleSeedAux (decide (n_max < doubleTabThreshold c_exp)) c_exp n_max U M

instance (reg : Bool) (c_exp n_max U M : ℕ) :
    Fintype (SingleSeedAux reg c_exp n_max U M) := by
  cases reg <;> dsimp [SingleSeedAux] <;> infer_instance

instance (reg : Bool) (c_exp n_max U M : ℕ) :
    Nonempty (SingleSeedAux reg c_exp n_max U M) := by
  cases reg <;> dsimp [SingleSeedAux] <;> infer_instance

instance (c d b : ℕ) : DecidableEq (DoubleTabTopSeed c d b) :=
  inferInstanceAs (DecidableEq (Fin c → Fin d → Fin (2 ^ b) → Fin (2 ^ b)))

instance (d b M : ℕ) : DecidableEq (DoubleTabBotSeed d b M) :=
  inferInstanceAs (DecidableEq (Fin d → Fin (2 ^ b) → Fin (2 ^ M)))

instance (reg : Bool) (c_exp n_max U M : ℕ) :
    DecidableEq (SingleSeedAux reg c_exp n_max U M) := by
  cases reg <;> dsimp [SingleSeedAux] <;> infer_instance

/-- Regime-indexed deterministic evaluation of a single hash block (`h₁` or `h₂`). -/
@[expose]
noncomputable def evalSingleAux (reg : Bool) (c_exp n_max U M : ℕ) :
    SingleSeedAux reg c_exp n_max U M → Fin U → Fin (2 ^ M) :=
  match reg with
  | true => fun θ u => trinomialPolyHash (trinomialStep U M) (cuckooK n_max) U M θ u
  | false => fun θ u =>
    doubleTabHash (DoubleTabulation.provableC c_exp) (DoubleTabulation.provableD c_exp)
      (DoubleTabulation.provableB n_max) U M θ.1 θ.2 u

/-- Deterministic evaluation of a single regime-switched hash block (`h₁` or `h₂`). -/
@[expose]
noncomputable def evalSingle (c_exp n_max U M : ℕ) :
    SingleSeed c_exp n_max U M → Fin U → Fin (2 ^ M) :=
  evalSingleAux (decide (n_max < doubleTabThreshold c_exp)) c_exp n_max U M

/-- Regime-indexed seed space for the unconditional cuckoo hash pair `(h₁, h₂)`. -/
abbrev SeedAux (reg : Bool) (c_exp n_max U M : ℕ) : Type :=
  SingleSeedAux reg c_exp n_max U M × SingleSeedAux reg c_exp n_max U M

/-- Regime-indexed first cuckoo hash function. -/
@[expose]
noncomputable def evalHash1Aux (reg : Bool) (c_exp n_max U M : ℕ) :
    SeedAux reg c_exp n_max U M → Fin U → Fin (2 ^ M) :=
  fun θ => evalSingleAux reg c_exp n_max U M θ.1

/-- Regime-indexed second cuckoo hash function. -/
@[expose]
noncomputable def evalHash2Aux (reg : Bool) (c_exp n_max U M : ℕ) :
    SeedAux reg c_exp n_max U M → Fin U → Fin (2 ^ M) :=
  fun θ => evalSingleAux reg c_exp n_max U M θ.2

/-- Seed space for the regime-switched cuckoo hash pair (`trinomialPolyHash` below
`doubleTabThreshold c_exp`, `doubleTabHash` at or above `doubleTabThreshold c_exp`). -/
abbrev Seed (c_exp n_max U M : ℕ) : Type :=
  SeedAux (decide (n_max < doubleTabThreshold c_exp)) c_exp n_max U M

/-- Uniform seed distribution over `Seed c_exp n_max U M`. -/
@[expose]
noncomputable def seedLaw (c_exp n_max U M : ℕ) : PMF (Seed c_exp n_max U M) :=
  PMF.uniformOfFintype (Seed c_exp n_max U M)

/-- First cuckoo hash function `h₁(u)` of the regime-switched cuckoo hash pair. -/
@[expose]
noncomputable def evalHash1 {c_exp n_max U M : ℕ} :
    Seed c_exp n_max U M → Fin U → Fin (2 ^ M) :=
  fun θ => evalSingle c_exp n_max U M θ.1

/-- Second cuckoo hash function `h₂(u)` of the regime-switched cuckoo hash pair. -/
@[expose]
noncomputable def evalHash2 {c_exp n_max U M : ℕ} :
    Seed c_exp n_max U M → Fin U → Fin (2 ^ M) :=
  fun θ => evalSingle c_exp n_max U M θ.2

/-- Specialization of `IsCuckooHashPair` to the regime-switched cuckoo hash pair
`(evalHash1, evalHash2)` over `seedLaw c_exp n_max U M`.
Proved unconditionally for every `n_max : ℕ` (`C_walk = 3`, `C_reh = 4`) whenever
`U ≤ max n_max 4 ^ c_exp` and `32 * max n_max 4 ≤ 2 ^ M` via
`Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing.isCuckooHashPair_provableFamily`. -/
abbrev IsCuckooHashFamily (c_exp U n_max M MaxLoop C_walk C_reh : ℕ) : Prop :=
  IsCuckooHashPair (seedLaw c_exp n_max U M) evalHash1 evalHash2 n_max MaxLoop C_walk C_reh

/-! ## Two-block Word-RAM hash pair representation and programs -/

open Cslib.DataStructure.HashFamily.WordRAM

/-- Word-RAM memory footprint of a single regime-switched hash instance (`h₁` or `h₂`). -/
@[expose]
def singleHashSpace (c_exp n_max : ℕ) : ℕ :=
  DoubleTabulation.provableSpace c_exp (cuckooK n_max) n_max

/-- Word-RAM memory footprint of the two-block hash pair `(h₁, h₂)` at `hashBase`:
`singleHashSpace c_exp n_max` words at `hashBase` for `h₁` followed by
`singleHashSpace c_exp n_max` words at `hash2Base hashBase c_exp n_max` for `h₂`. -/
@[expose]
def hashPairSpace (c_exp n_max : ℕ) : ℕ :=
  2 * singleHashSpace c_exp n_max

/-- Base address of the second hash instance `h₂`. -/
@[expose]
def hash2Base (hashBase c_exp n_max : ℕ) : ℕ :=
  hashBase + singleHashSpace c_exp n_max

theorem le_singleHashSpace (c_exp n_max : ℕ) :
    47 ≤ singleHashSpace c_exp n_max := by
  dsimp only [singleHashSpace, DoubleTabulation.provableSpace]
  split_ifs
  · dsimp only [KWise.space, KWise.spaceFromB]
    have hk := thirtyEight_le_cuckooK n_max
    have hpow : 1 ≤ 2 ^ (2 * KWise.chunkBits n_max) := Nat.one_le_two_pow
    omega
  · dsimp only [DoubleTabulation.space]
    have hc : 2 ≤ DoubleTabulation.provableC c_exp := by
      dsimp only [DoubleTabulation.provableC]; omega
    have hd : 16 ≤ DoubleTabulation.provableD c_exp := by
      dsimp only [DoubleTabulation.provableD, DoubleTabulation.provableC]; omega
    have hb : 2 ≤ 2 ^ DoubleTabulation.provableB n_max := by
      have h1 := DoubleTabulation.one_le_provableB n_max
      exact Nat.le_self_pow (by omega) 2
    have hcd : 48 ≤ (DoubleTabulation.provableC c_exp + 1) * DoubleTabulation.provableD c_exp := by
      nlinarith
    nlinarith

/-- Below `doubleTabThreshold c_exp`, a single hash instance occupies a `cuckooK`-wise polynomial
table. -/
private theorem singleHashSpace_of_lt {c_exp n_max : ℕ} (h : n_max < doubleTabThreshold c_exp) :
    singleHashSpace c_exp n_max = KWise.space n_max (cuckooK n_max) := by
  simp only [singleHashSpace, DoubleTabulation.provableSpace, h, ↓reduceIte]

/-- From `doubleTabThreshold c_exp` on, a single hash instance occupies a Double Tabulation
table. -/
private theorem singleHashSpace_of_not_lt {c_exp n_max : ℕ}
    (h : ¬ n_max < doubleTabThreshold c_exp) :
    singleHashSpace c_exp n_max =
      DoubleTabulation.space (DoubleTabulation.provableC c_exp)
        (DoubleTabulation.provableD c_exp) (DoubleTabulation.provableB n_max) := by
  simp only [singleHashSpace, DoubleTabulation.provableSpace, h, ↓reduceIte]

theorem le_hashPairSpace (c_exp n_max : ℕ) :
    49 ≤ hashPairSpace c_exp n_max := by
  have := le_singleHashSpace c_exp n_max
  dsimp only [hashPairSpace]
  omega

/-- Constant upper bound `24 * doubleTabMinB c_exp + 26` on `cuckooK n_max` throughout the small
regime `n_max < doubleTabThreshold c_exp`. -/
@[expose]
def cuckooKBound (c_exp : ℕ) : ℕ :=
  24 * doubleTabMinB c_exp + 26

theorem cuckooK_le_cuckooKBound_of_lt {c_exp n_max : ℕ}
    (hlt : n_max < doubleTabThreshold c_exp) :
    cuckooK n_max ≤ cuckooKBound c_exp := by
  have hb_pos : 1 ≤ doubleTabMinB c_exp := by
    rw [doubleTabMinB_eq]
    have hbase : 1 ≤ 24 * (2 * max c_exp 1) + 8 := by omega
    have hsq : 1 ≤ (24 * (2 * max c_exp 1) + 8) ^ 2 := Nat.one_le_pow 2 _ hbase
    omega
  have hpow_ge_2 : 2 ≤ 2 ^ (2 * doubleTabMinB c_exp) := by
    calc 2 = 2 ^ 1 := by ring
      _ ≤ 2 ^ (2 * doubleTabMinB c_exp) := Nat.pow_le_pow_right (by decide) (by omega)
  have hmax_le : max n_max 2 ≤ 2 ^ (2 * doubleTabMinB c_exp) := by
    rw [← doubleTabThreshold_eq]
    exact max_le (le_of_lt hlt) (by rw [doubleTabThreshold_eq]; exact hpow_ge_2)
  have hclog : Nat.clog 2 (max n_max 2) ≤ 2 * doubleTabMinB c_exp :=
    Nat.clog_le_of_le_pow hmax_le
  dsimp only [cuckooK, maxEvictions, cuckooKBound]
  omega

theorem singleHashSpace_le_provableSpace_cuckooKBound (c_exp n_max : ℕ) :
    singleHashSpace c_exp n_max ≤
      DoubleTabulation.provableSpace c_exp (cuckooKBound c_exp) n_max := by
  dsimp only [singleHashSpace, DoubleTabulation.provableSpace]
  split_ifs with h
  · dsimp only [KWise.space, KWise.spaceFromB]
    have hk := cuckooK_le_cuckooKBound_of_lt h
    omega
  · exact le_rfl

/-- Explicit `O_{c_exp}(1)` linear-space factor for `hashPairSpace c_exp n_max`. -/
@[expose]
def hashPairSpaceFactor (c_exp : ℕ) : ℕ :=
  2 * DoubleTabulation.provableSpaceFactor c_exp (cuckooKBound c_exp)

/-- **All-`n_max` linear space bound for `hashPairSpace` (`O_{c_exp}(n_max + 1)`)**. -/
theorem hashPairSpace_le (c_exp n_max : ℕ) :
    hashPairSpace c_exp n_max ≤ hashPairSpaceFactor c_exp * (n_max + 1) := by
  dsimp only [hashPairSpace, hashPairSpaceFactor]
  rw [Nat.mul_assoc]
  exact Nat.mul_le_mul_left 2
    ((singleHashSpace_le_provableSpace_cuckooKBound c_exp n_max).trans
      (DoubleTabulation.provableSpace_le c_exp (cuckooKBound c_exp) n_max))

/-- Regime-indexed deterministic table representation for a single hash block at `base`. -/
@[expose]
def SingleTableRepAux (reg : Bool) (base n_max U M : ℕ) (mem : ℕ → ℕ) : Prop :=
  match reg with
  | true => KWise.TableRep base (KWise.chunkBits n_max) U M (cuckooK n_max) mem
  | false => True

/-- Deterministic table representation for a single hash block at `base`. -/
@[expose]
def SingleTableRep (base c_exp n_max U M : ℕ) (mem : ℕ → ℕ) : Prop :=
  SingleTableRepAux (decide (n_max < doubleTabThreshold c_exp)) base n_max U M mem

/-- Deterministic table representation invariant for the two-block hash pair at `hashBase`. -/
@[expose]
def HashPairTableRep (hashBase c_exp n_max U M : ℕ) (mem : ℕ → ℕ) : Prop :=
  SingleTableRep hashBase c_exp n_max U M mem ∧
  SingleTableRep (hash2Base hashBase c_exp n_max) c_exp n_max U M mem

/-- Regime-indexed seed representation for a single hash block at `base`. -/
@[expose]
def SingleSeedRepAux (reg : Bool) (base c_exp n_max U M : ℕ) :
    SingleSeedAux reg c_exp n_max U M → (ℕ → ℕ) → Prop :=
  match reg with
  | true => fun θ mem => KWise.SeedRep base U M (cuckooK n_max) θ mem
  | false => fun θ mem =>
    DoubleTabulation.SeedRep base
      (DoubleTabulation.provableC c_exp) (DoubleTabulation.provableD c_exp)
      (DoubleTabulation.provableB n_max) M θ mem

/-- Seed representation for a single regime-switched hash block at `base`. -/
@[expose]
def SingleSeedRep (base c_exp n_max U M : ℕ)
    (θ : SingleSeed c_exp n_max U M) (mem : ℕ → ℕ) : Prop :=
  SingleSeedRepAux (decide (n_max < doubleTabThreshold c_exp)) base c_exp n_max U M θ mem

/-- Regime-indexed seed extraction for a single hash block at `base`. -/
@[expose]
def extractSingleSeedAux (reg : Bool) (base c_exp n_max U M : ℕ) (mem : ℕ → ℕ) :
    SingleSeedAux reg c_exp n_max U M :=
  match reg with
  | true => KWise.extractSeeds base U M (cuckooK n_max) mem
  | false =>
    DoubleTabulation.extractSeed base
      (DoubleTabulation.provableC c_exp) (DoubleTabulation.provableD c_exp)
      (DoubleTabulation.provableB n_max) M mem

/-- Extract the seed of a single regime-switched hash block at `base`. -/
@[expose]
def extractSingleSeed (base c_exp n_max U M : ℕ) (mem : ℕ → ℕ) :
    SingleSeed c_exp n_max U M :=
  extractSingleSeedAux (decide (n_max < doubleTabThreshold c_exp)) base c_exp n_max U M mem

/-- Regime-indexed seed representation for the two-block hash pair at `hashBase`. -/
@[expose]
def HashPairSeedRepAux (reg : Bool) (hashBase c_exp n_max U M : ℕ)
    (θ : SeedAux reg c_exp n_max U M) (mem : ℕ → ℕ) : Prop :=
  SingleSeedRepAux reg hashBase c_exp n_max U M θ.1 mem ∧
  SingleSeedRepAux reg (hash2Base hashBase c_exp n_max) c_exp n_max U M θ.2 mem

/-- Seed representation invariant for `θ : Seed c_exp n_max U M` at `hashBase`. -/
@[expose]
def HashPairSeedRep (hashBase c_exp n_max U M : ℕ)
    (θ : Seed c_exp n_max U M) (mem : ℕ → ℕ) : Prop :=
  SingleSeedRep hashBase c_exp n_max U M θ.1 mem ∧
  SingleSeedRep (hash2Base hashBase c_exp n_max) c_exp n_max U M θ.2 mem

/-- Full representation invariant for the hash pair `(h₁, h₂)` at `hashBase`. -/
@[expose]
def HashPairRep (hashBase c_exp n_max U M : ℕ)
    (θ : Seed c_exp n_max U M) (mem : ℕ → ℕ) : Prop :=
  HashPairTableRep hashBase c_exp n_max U M mem ∧
  HashPairSeedRep hashBase c_exp n_max U M θ mem

/-- Regime-indexed seed extraction from memory at `hashBase`. -/
@[expose]
def extractSeedAux (reg : Bool) (hashBase c_exp n_max U M : ℕ) (mem : ℕ → ℕ) :
    SeedAux reg c_exp n_max U M :=
  (extractSingleSeedAux reg hashBase c_exp n_max U M mem,
   extractSingleSeedAux reg (hash2Base hashBase c_exp n_max) c_exp n_max U M mem)

/-- Extract the full cuckoo hash seed `Seed c_exp n_max U M` from memory at `hashBase`. -/
@[expose]
def extractSeed (hashBase c_exp n_max U M : ℕ) (mem : ℕ → ℕ) : Seed c_exp n_max U M :=
  (extractSingleSeed hashBase c_exp n_max U M mem,
   extractSingleSeed (hash2Base hashBase c_exp n_max) c_exp n_max U M mem)

theorem extractSingleSeed_eq_of_SingleSeedRep {base c_exp n_max U M : ℕ}
    {θ : SingleSeed c_exp n_max U M} {mem : ℕ → ℕ}
    (hseed : SingleSeedRep base c_exp n_max U M θ mem) :
    extractSingleSeed base c_exp n_max U M mem = θ := by
  unfold SingleSeed extractSingleSeed SingleSeedRep at *
  revert θ hseed
  cases decide (n_max < doubleTabThreshold c_exp) <;> intro θ hseed
  · exact DoubleTabulation.extractSeed_eq_of_seedRep hseed
  · exact KWise.extractSeeds_eq_of_seedRep hseed

theorem extractSeed_eq_of_HashPairSeedRep {hashBase c_exp n_max U M : ℕ}
    {θ : Seed c_exp n_max U M} {mem : ℕ → ℕ}
    (hseed : HashPairSeedRep hashBase c_exp n_max U M θ mem) :
    extractSeed hashBase c_exp n_max U M mem = θ :=
  Prod.ext (extractSingleSeed_eq_of_SingleSeedRep hseed.1)
    (extractSingleSeed_eq_of_SingleSeedRep hseed.2)

theorem SingleTableRep.congr_of_footprint {base c_exp n_max U M : ℕ} {mem mem' : ℕ → ℕ}
    (htab : SingleTableRep base c_exp n_max U M mem)
    (hm : ∀ a, base ≤ a → a < base + singleHashSpace c_exp n_max → mem' a = mem a) :
    SingleTableRep base c_exp n_max U M mem' := by
  unfold SingleTableRep at *
  revert htab
  cases h : decide (n_max < doubleTabThreshold c_exp) <;> intro htab
  · trivial
  · have hlt : n_max < doubleTabThreshold c_exp := of_decide_eq_true h
    have hsp := singleHashSpace_of_lt hlt
    have hk := thirtyEight_le_cuckooK n_max
    have hpow : 1 ≤ 2 ^ (2 * KWise.chunkBits n_max) := Nat.one_le_two_pow
    have hkw : KWise.space n_max (cuckooK n_max) =
        8 + cuckooK n_max + 2 ^ (2 * KWise.chunkBits n_max) := rfl
    rcases htab with ⟨h0, h1, h2, h3, h4, h5, h6, h7, hcl⟩
    refine ⟨(hm _ (by omega) (by omega)).trans h0,
      (hm _ (by omega) (by omega)).trans h1,
      (hm _ (by omega) (by omega)).trans h2,
      (hm _ (by omega) (by omega)).trans h3,
      (hm _ (by omega) (by omega)).trans h4,
      (hm _ (by omega) (by omega)).trans h5,
      (hm _ (by omega) (by omega)).trans h6,
      (hm _ (by omega) (by omega)).trans h7,
      fun idx hidx => (hm _ (by omega) (by omega)).trans (hcl idx hidx)⟩

theorem SingleTableRep.of_copy_from_hashBase {hashBase c_exp n_max U M : ℕ} {mem : ℕ → ℕ}
    (htab : SingleTableRep hashBase c_exp n_max U M mem)
    (hcopy : ∀ j < singleHashSpace c_exp n_max,
      mem (hash2Base hashBase c_exp n_max + j) = mem (hashBase + j)) :
    SingleTableRep (hash2Base hashBase c_exp n_max) c_exp n_max U M mem := by
  unfold SingleTableRep at *
  revert htab
  cases h : decide (n_max < doubleTabThreshold c_exp) <;> intro htab
  · trivial
  · have hlt : n_max < doubleTabThreshold c_exp := of_decide_eq_true h
    have hsp := singleHashSpace_of_lt hlt
    have hk := thirtyEight_le_cuckooK n_max
    have hpow : 1 ≤ 2 ^ (2 * KWise.chunkBits n_max) := Nat.one_le_two_pow
    have hkw : KWise.space n_max (cuckooK n_max) =
        8 + cuckooK n_max + 2 ^ (2 * KWise.chunkBits n_max) := rfl
    rcases htab with ⟨h0, h1, h2, h3, h4, h5, h6, h7, hcl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun idx hidx => ?_⟩
    · simpa using (hcopy 0 (by omega)).trans (by simpa using h0)
    · exact (hcopy 1 (by omega)).trans h1
    · exact (hcopy 2 (by omega)).trans h2
    · exact (hcopy 3 (by omega)).trans h3
    · exact (hcopy 4 (by omega)).trans h4
    · exact (hcopy 5 (by omega)).trans h5
    · exact (hcopy 6 (by omega)).trans h6
    · exact (hcopy 7 (by omega)).trans h7
    · rw [show hash2Base hashBase c_exp n_max + 8 + cuckooK n_max + idx =
            hash2Base hashBase c_exp n_max + (8 + cuckooK n_max + idx) by omega,
          hcopy (8 + cuckooK n_max + idx) (by omega),
          show hashBase + (8 + cuckooK n_max + idx) = hashBase + 8 + cuckooK n_max + idx by omega]
      exact hcl idx hidx

theorem HashPairTableRep.congr_of_footprint {hashBase c_exp n_max U M : ℕ} {mem mem' : ℕ → ℕ}
    (htab : HashPairTableRep hashBase c_exp n_max U M mem)
    (hm : ∀ a, hashBase ≤ a → a < hashBase + hashPairSpace c_exp n_max → mem' a = mem a) :
    HashPairTableRep hashBase c_exp n_max U M mem' :=
  ⟨htab.1.congr_of_footprint (fun a hge hlt =>
    hm a hge (by dsimp only [hashPairSpace]; omega)),
   htab.2.congr_of_footprint (fun a hge hlt =>
    hm a (by dsimp only [hash2Base] at hge; omega)
      (by dsimp only [hash2Base, hashPairSpace] at hlt ⊢; omega))⟩

theorem SingleSeedRep.congr_of_footprint {base c_exp n_max U M : ℕ}
    {θ : SingleSeed c_exp n_max U M} {mem mem' : ℕ → ℕ}
    (hseed : SingleSeedRep base c_exp n_max U M θ mem)
    (hm : ∀ a, base ≤ a → a < base + singleHashSpace c_exp n_max → mem' a = mem a) :
    SingleSeedRep base c_exp n_max U M θ mem' := by
  unfold SingleSeed SingleSeedRep at *
  revert θ hseed
  cases h : decide (n_max < doubleTabThreshold c_exp) <;> intro θ hseed
  · have hge : ¬ (n_max < doubleTabThreshold c_exp) := of_decide_eq_false h
    have hsp := singleHashSpace_of_not_lt hge
    exact hseed.congr_mem (fun a ha1 ha2 => hm a ha1 (by omega))
  · have hlt : n_max < doubleTabThreshold c_exp := of_decide_eq_true h
    have hsp := singleHashSpace_of_lt hlt
    have hpow : 1 ≤ 2 ^ (2 * KWise.chunkBits n_max) := Nat.one_le_two_pow
    have hkw : KWise.space n_max (cuckooK n_max) =
        8 + cuckooK n_max + 2 ^ (2 * KWise.chunkBits n_max) := rfl
    exact hseed.congr_of_footprint (fun a ha1 ha2 => hm a ha1 (by omega))

theorem HashPairSeedRep.congr_of_footprint {hashBase c_exp n_max U M : ℕ}
    {θ : Seed c_exp n_max U M} {mem mem' : ℕ → ℕ}
    (hseed : HashPairSeedRep hashBase c_exp n_max U M θ mem)
    (hm : ∀ a, hashBase ≤ a → a < hashBase + hashPairSpace c_exp n_max → mem' a = mem a) :
    HashPairSeedRep hashBase c_exp n_max U M θ mem' :=
  ⟨hseed.1.congr_of_footprint (fun a ha1 ha2 =>
    hm a ha1 (by dsimp only [hashPairSpace]; omega)),
   hseed.2.congr_of_footprint (fun a ha1 ha2 =>
    hm a (by dsimp only [hash2Base] at ha1; omega)
      (by dsimp only [hash2Base, hashPairSpace] at ha2 ⊢; omega))⟩

theorem HashPairRep.congr_of_footprint {hashBase c_exp n_max U M : ℕ}
    {θ : Seed c_exp n_max U M} {mem mem' : ℕ → ℕ}
    (hrep : HashPairRep hashBase c_exp n_max U M θ mem)
    (hm : ∀ a, hashBase ≤ a → a < hashBase + hashPairSpace c_exp n_max → mem' a = mem a) :
    HashPairRep hashBase c_exp n_max U M θ mem' :=
  ⟨hrep.1.congr_of_footprint hm, hrep.2.congr_of_footprint hm⟩

theorem HashPairRep.congr_of_ge_hashBase {hashBase c_exp n_max U M : ℕ}
    {θ : Seed c_exp n_max U M} {mem mem' : ℕ → ℕ}
    (hrep : HashPairRep hashBase c_exp n_max U M θ mem)
    (hm : ∀ a, hashBase ≤ a → mem' a = mem a) :
    HashPairRep hashBase c_exp n_max U M θ mem' :=
  hrep.congr_of_footprint (fun a hge _ => hm a hge)

theorem extractSingleSeed_congr_of_footprint {base c_exp n_max U M : ℕ} {mem mem' : ℕ → ℕ}
    (hm : ∀ a, base ≤ a → a < base + singleHashSpace c_exp n_max → mem' a = mem a) :
    extractSingleSeed base c_exp n_max U M mem' = extractSingleSeed base c_exp n_max U M mem := by
  unfold SingleSeed extractSingleSeed
  cases h : decide (n_max < doubleTabThreshold c_exp)
  · have hge : ¬ (n_max < doubleTabThreshold c_exp) := of_decide_eq_false h
    have hsp := singleHashSpace_of_not_lt hge
    exact DoubleTabulation.extractSeed_congr_mem (fun a ha1 ha2 => hm a ha1 (by omega))
  · have hlt : n_max < doubleTabThreshold c_exp := of_decide_eq_true h
    have hsp := singleHashSpace_of_lt hlt
    have hpow : 1 ≤ 2 ^ (2 * KWise.chunkBits n_max) := Nat.one_le_two_pow
    have hkw : KWise.space n_max (cuckooK n_max) =
        8 + cuckooK n_max + 2 ^ (2 * KWise.chunkBits n_max) := rfl
    exact KWise.extractSeeds_congr_of_footprint (fun a ha1 ha2 => hm a ha1 (by omega))

theorem extractSeed_congr_of_footprint {hashBase c_exp n_max U M : ℕ} {mem mem' : ℕ → ℕ}
    (hm : ∀ a, hashBase ≤ a → a < hashBase + hashPairSpace c_exp n_max → mem' a = mem a) :
    extractSeed hashBase c_exp n_max U M mem' = extractSeed hashBase c_exp n_max U M mem :=
  Prod.ext
    (extractSingleSeed_congr_of_footprint (fun a ha1 ha2 =>
      hm a ha1 (by dsimp only [hashPairSpace]; omega)))
    (extractSingleSeed_congr_of_footprint (fun a ha1 ha2 =>
      hm a (by dsimp only [hash2Base] at ha1; omega)
        (by dsimp only [hash2Base, hashPairSpace] at ha2 ⊢; omega)))

theorem extractSeed_congr_of_ge_hashBase {hashBase c_exp n_max U M : ℕ} {mem mem' : ℕ → ℕ}
    (hm : ∀ a, hashBase ≤ a → mem' a = mem a) :
    extractSeed hashBase c_exp n_max U M mem' = extractSeed hashBase c_exp n_max U M mem :=
  extractSeed_congr_of_footprint (fun a hge _ => hm a hge)

/-- Injective register map embedding `Data 18` into `Data 19`. -/
@[expose]
def cast18To19 : Fin 18 → Fin 19 :=
  Fin.castLE (by decide : 18 ≤ 19)

theorem injective_cast18To19 : Function.Injective cast18To19 :=
  Fin.castLE_injective _

/-- Injective register map embedding `Data 12` into `Data 19`. -/
@[expose]
def cast12To19 : Fin 12 → Fin 19 :=
  Fin.castLE (by decide : 12 ≤ 19)

theorem injective_cast12To19 : Function.Injective cast12To19 :=
  Fin.castLE_injective _

/-- Body of `copyWordsLoop`: copies one word from `[reg 3]` to `[reg 4]` and increments both
pointers by `reg 6 = 1`. -/
@[expose]
def copyWordsBody : Code .exact 19 :=
  .seq (.op (.load 7 3))
  (.seq (.op (.store 4 7))
  (.seq (.op (.exactBin .add 3 3 6))
        (.op (.exactBin .add 4 4 6))))

/-- Word-slice copy loop `while reg 4 < reg 5 do copyWordsBody`. -/
@[expose]
def copyWordsLoop : Code .exact 19 :=
  .loop (.lt 4 5) copyWordsBody

theorem copyWordsLoop_exec {w : ℕ} (len src dst : ℕ) {x : Data 19}
    (hsrc : x.regs 3 = src) (hdst : x.regs 4 = dst)
    (hend : x.regs 5 = dst + len) (hone : x.regs 6 = 1)
    (hdisj : src + len ≤ dst) (hfit_end : Fits w (dst + len)) :
    ∃ y : Data 19,
      Exec w copyWordsLoop x y (6 * len + 2) ∧
      (∀ r : Fin 19, r ≠ 3 ∧ r ≠ 4 ∧ r ≠ 7 → y.regs r = x.regs r) ∧
      (∀ j < len, y.mem (dst + j) = x.mem (src + j)) ∧
      (∀ a, (a < dst ∨ dst + len ≤ a) → y.mem a = x.mem a) := by
  induction len generalizing src dst x with
  | zero =>
    have hc : ¬ (Cond.lt (4 : Fin 19) 5).Holds x := by
      simp [Cond.Holds, hdst, hend]
    exact ⟨x, Exec.loop_exit hc, fun _ _ => rfl, fun _ hj => by omega, fun _ _ => rfl⟩
  | succ len ih =>
    have hc : (Cond.lt (4 : Fin 19) 5).Holds x := by
      simp [Cond.Holds, hdst, hend]
    have hfit_src1 : Fits w (src + 1) := hfit_end.of_le (by omega)
    have hfit_dst1 : Fits w (dst + 1) := hfit_end.of_le (by omega)
    set s1 := x.set 7 (x.mem src)
    have e1 : Exec w (.op (.load 7 3) : Code .exact 19) x s1 1 := by
      simpa +decide [s1, hsrc] using (Exec.load (B := .exact) (w := w) (d := 7) (a := 3) (x := x))
    set s2 := s1.write dst (x.mem src)
    have e2 : Exec w (.op (.store 4 7) : Code .exact 19) s1 s2 1 := by
      simpa +decide [s2, s1, hdst] using
        (Exec.store (B := .exact) (w := w) (a := 4) (s := 7) (x := s1))
    set s3 := s2.set 3 (src + 1)
    have e3 : Exec w (.op (.exactBin .add 3 3 6) : Code .exact 19) s2 s3 1 :=
      ExactLog.exec_exactBin (by simp +decide [s2, s1, hsrc, hone]) hfit_src1
    set s4 := s3.set 4 (dst + 1)
    have e4 : Exec w (.op (.exactBin .add 4 4 6) : Code .exact 19) s3 s4 1 :=
      ExactLog.exec_exactBin (by simp +decide [s3, s2, s1, hdst, hone]) hfit_dst1
    have hbody : Exec w copyWordsBody x s4 4 := e1.seq (e2.seq (e3.seq e4))
    obtain ⟨y, hrec, hy_regs, hy_copy, hy_frame⟩ :=
      ih (src + 1) (dst + 1) (x := s4)
        (by simp +decide [s4, s3])
        (by simp +decide [s4])
        (by simp +decide [s4, s3, s2, s1, hend]; omega)
        (by simp +decide [s4, s3, s2, s1, hone])
        (by omega)
        (by rwa [show dst + 1 + len = dst + (len + 1) by omega])
    have hiter := Exec.loop_iter hc hbody hrec
    refine ⟨y, ?_, ?_, ?_, ?_⟩
    · simpa only [copyWordsLoop, show 4 + (6 * len + 2) + 2 = 6 * (len + 1) + 2 by ring] using
        hiter
    · intro r ⟨hr3, hr4, hr7⟩
      rw [hy_regs r ⟨hr3, hr4, hr7⟩]
      dsimp only [s4, s3, s2, s1, Data.write, Data.set]
      rw [Function.update_of_ne hr4, Function.update_of_ne hr3, Function.update_of_ne hr7]
    · intro j hj
      rcases eq_or_ne j 0 with rfl | hj0
      · rw [Nat.add_zero, Nat.add_zero, hy_frame dst (Or.inl (by omega))]
        simp [s4, s3, s2, Data.write]
      · have h1 := hy_copy (j - 1) (by omega)
        rw [show dst + 1 + (j - 1) = dst + j by omega,
          show src + 1 + (j - 1) = src + j by omega] at h1
        rw [h1]
        dsimp only [s4, s3, s2, s1, Data.write, Data.set]
        rw [Function.update_of_ne (by omega)]
    · intro a ha
      rw [hy_frame a (ha.imp (by omega) (by omega))]
      dsimp only [s4, s3, s2, s1, Data.write, Data.set]
      rw [Function.update_of_ne (by omega)]

/-- Setup block preparing `copyWordsLoop` to duplicate
`[hashBase, hashBase + singleHashSpace c_exp n_max)` into
`[hash2Base hashBase c_exp n_max, hash2Base hashBase c_exp n_max + singleHashSpace c_exp n_max)`. -/
@[expose]
def copyTableSetup (c_exp n_max : ℕ) : Code .exact 19 :=
  .seq (.op (.copy 3 0))
  (.seq (.op (.const 4 (singleHashSpace c_exp n_max)))
  (.seq (.op (.exactBin .add 4 0 4))
  (.seq (.op (.const 5 (singleHashSpace c_exp n_max)))
  (.seq (.op (.exactBin .add 5 4 5))
        (.op (.const 6 1))))))

/-- Deterministic table-initialization program for the two-block hash pair at `hashBase`:
in the small-`n_max` regime `n_max < doubleTabThreshold c_exp`, initializes the `KWise` lookup table
at `hashBase` and copies it to `hash2Base hashBase c_exp n_max`; in the large-`n_max` regime,
executes a 1-instruction no-op (`SingleTableRep` is `True`). -/
@[expose]
def initTableHashPairCode (c_exp n_max : ℕ) : Code .exact 19 :=
  if n_max < doubleTabThreshold c_exp then
    .seq ((KWise.initTableCode (cuckooK n_max)).rename cast18To19)
    (.seq (copyTableSetup c_exp n_max) copyWordsLoop)
  else
    .op (.copy 0 0)

/-- Instruction bound for `initTableHashPairCode`. -/
@[expose]
def initTableHashPairSteps (c_exp n_max U M : ℕ) : ℕ :=
  KWise.initTableSteps n_max U M + 6 * singleHashSpace c_exp n_max + 8

theorem initTableHashPairCode_execWithin {w hashBase c_exp n_max U M : ℕ} {x : Data 19}
    (h0 : x.regs 0 = hashBase) (h1 : x.regs 1 = n_max)
    (h2 : x.regs 2 = U) (h3 : x.regs 3 = M)
    (hfit_space : Fits w (hashBase + hashPairSpace c_exp n_max))
    (hfit_n : Fits w (max n_max 2)) (hfit_U : Fits w (max U 2 + 1))
    (hfit_q : Fits w (2 ^ Probability.trinomialDeg U M)) :
    ∃ y : Data 19,
      ExecWithin w (initTableHashPairCode c_exp n_max) x y
        (initTableHashPairSteps c_exp n_max U M) ∧
      HashPairTableRep hashBase c_exp n_max U M y.mem ∧
      y.regs 0 = hashBase ∧
      (∀ a, (a < hashBase ∨ hashBase + hashPairSpace c_exp n_max ≤ a) → y.mem a = x.mem a) := by
  unfold initTableHashPairCode
  split_ifs with hlt
  · have hsp := singleHashSpace_of_lt hlt
    have hle_sp := le_singleHashSpace c_exp n_max
    have hfit_kw : Fits w (hashBase + KWise.space n_max (cuckooK n_max)) :=
      hfit_space.of_le (by dsimp only [hashPairSpace]; omega)
    have hfit_1 : Fits w 1 := hfit_space.of_le (by dsimp only [hashPairSpace]; omega)
    have hfit_sh : Fits w (singleHashSpace c_exp n_max) :=
      hfit_space.of_le (by dsimp only [hashPairSpace]; omega)
    have hfit_h2 : Fits w (hash2Base hashBase c_exp n_max) :=
      hfit_space.of_le (by dsimp only [hash2Base, hashPairSpace]; omega)
    have hfit_end : Fits w (hash2Base hashBase c_exp n_max + singleHashSpace c_exp n_max) :=
      hfit_space.of_le (by dsimp only [hash2Base, hashPairSpace]; omega)
    obtain ⟨y_kw, ⟨t_kw, ht_kw, he_kw⟩, htab_kw, hy_kw0, hy_kw_out⟩ :=
      KWise.initTableCode_execWithin (w := w) (base := hashBase) (n_max := n_max)
        (U := U) (M := M) (k := cuckooK n_max) (x := x.comap cast18To19)
        (by simp +decide [cast18To19, Data.comap, h0])
        (by simp +decide [cast18To19, Data.comap, h1])
        (by simp +decide [cast18To19, Data.comap, h2])
        (by simp +decide [cast18To19, Data.comap, h3])
        hfit_kw hfit_n hfit_U hfit_q
    set d1 := y_kw.extend cast18To19 x
    have he_kw' : Exec w ((KWise.initTableCode (cuckooK n_max)).rename cast18To19) x d1 t_kw :=
      he_kw.rename injective_cast18To19
    have hd1_0 : d1.regs 0 = hashBase := by
      change ((y_kw.extend cast18To19 x).comap cast18To19).regs 0 = hashBase
      rw [Data.comap_extend injective_cast18To19, hy_kw0]
    have hd1_mem : d1.mem = y_kw.mem := rfl
    set s1 := d1.set 3 hashBase
    have es1 : Exec w (.op (.copy 3 0) : Code .exact 19) d1 s1 1 := by
      simpa +decide [s1, hd1_0] using (Exec.copy (B := .exact) (w := w) (d := 3) (s := 0) (x := d1))
    set s2 := s1.set 4 (singleHashSpace c_exp n_max)
    have es2 : Exec w (.op (.const 4 (singleHashSpace c_exp n_max)) : Code .exact 19) s1 s2 1 :=
      Exec.const hfit_sh
    set s3 := s2.set 4 (hash2Base hashBase c_exp n_max)
    have es3 : Exec w (.op (.exactBin .add 4 0 4) : Code .exact 19) s2 s3 1 :=
      ExactLog.exec_exactBin (by simp +decide [s2, s1, hd1_0, hash2Base]) hfit_h2
    set s4 := s3.set 5 (singleHashSpace c_exp n_max)
    have es4 : Exec w (.op (.const 5 (singleHashSpace c_exp n_max)) : Code .exact 19) s3 s4 1 :=
      Exec.const hfit_sh
    set s5 := s4.set 5 (hash2Base hashBase c_exp n_max + singleHashSpace c_exp n_max)
    have es5 : Exec w (.op (.exactBin .add 5 4 5) : Code .exact 19) s4 s5 1 :=
      ExactLog.exec_exactBin (by simp +decide [s4, s3]) hfit_end
    set s6 := s5.set 6 1
    have es6 : Exec w (.op (.const 6 1) : Code .exact 19) s5 s6 1 := Exec.const hfit_1
    have esetup : Exec w (copyTableSetup c_exp n_max) d1 s6 6 :=
      es1.seq (es2.seq (es3.seq (es4.seq (es5.seq es6))))
    obtain ⟨y, ecopy, hy_regs, hy_copy, hy_frame⟩ :=
      copyWordsLoop_exec (w := w) (singleHashSpace c_exp n_max) hashBase
        (hash2Base hashBase c_exp n_max) (x := s6)
        (by simp +decide [s6, s5, s4, s3, s2, s1])
        (by simp +decide [s6, s5, s4, s3])
        (by simp +decide [s6, s5])
        (by simp +decide [s6])
        (by dsimp only [hash2Base]; omega)
        hfit_end
    have hall := he_kw'.seq (esetup.seq ecopy)
    have hy0 : y.regs 0 = hashBase := by
      rw [hy_regs 0 ⟨by decide, by decide, by decide⟩]
      simp +decide [s6, s5, s4, s3, s2, s1, hd1_0]
    have htab1_d1 : SingleTableRep hashBase c_exp n_max U M d1.mem := by
      unfold SingleTableRep
      rw [decide_eq_true hlt]
      exact htab_kw
    have htab1_y : SingleTableRep hashBase c_exp n_max U M y.mem :=
      htab1_d1.congr_of_footprint (fun a ha1 ha2 =>
        hy_frame a (Or.inl (by dsimp only [hash2Base]; omega)))
    have htab2_y : SingleTableRep (hash2Base hashBase c_exp n_max) c_exp n_max U M y.mem :=
      htab1_y.of_copy_from_hashBase (fun j hj => by
        rw [hy_copy j hj, hy_frame (hashBase + j) (Or.inl (by dsimp only [hash2Base]; omega))])
    refine ⟨y, ⟨t_kw + (6 + (6 * singleHashSpace c_exp n_max + 2)),
      by dsimp only [initTableHashPairSteps]; omega, hall⟩,
      ⟨htab1_y, htab2_y⟩, hy0, fun a ha => ?_⟩
    have ha_copy : a < hash2Base hashBase c_exp n_max ∨
        hash2Base hashBase c_exp n_max + singleHashSpace c_exp n_max ≤ a := by
      dsimp only [hash2Base, hashPairSpace] at ha ⊢
      exact ha.imp (by omega) (by omega)
    have ha_kw : a < hashBase ∨ hashBase + KWise.space n_max (cuckooK n_max) ≤ a := by
      dsimp only [hashPairSpace] at ha
      exact ha.imp id (by omega)
    exact (hy_frame a ha_copy).trans (hy_kw_out a ha_kw)
  · refine ⟨x.set 0 (x.regs 0),
      ⟨1, by dsimp only [initTableHashPairSteps]; omega, Exec.copy⟩,
      ?_, by simp +decide [h0], fun _ _ => rfl⟩
    unfold HashPairTableRep SingleTableRep
    rw [decide_eq_false hlt]
    exact ⟨trivial, trivial⟩

/-- Shifts `reg 0` (`base`) forward by `singleHashSpace c_exp n_max` (`hashBase → hash2Base`)
using scratch register `15`. -/
@[expose]
def shiftToHash2BaseCode (c_exp n_max : ℕ) : Code .exact 19 :=
  .seq (.op (.const 15 (singleHashSpace c_exp n_max)))
       (.op (.exactBin .add 0 0 15))

/-- Closed-form machine state after `shiftToHash2BaseCode c_exp n_max`. -/
@[expose]
def shiftToHash2BaseData (hashBase c_exp n_max : ℕ) (x : Data 19) : Data 19 :=
  (x.set 15 (singleHashSpace c_exp n_max)).set 0 (hash2Base hashBase c_exp n_max)

/-- Shifts `reg 0` (`base`) back by `singleHashSpace c_exp n_max` (`hash2Base → hashBase`)
using scratch register `15`. -/
@[expose]
def unshiftFromHash2BaseCode (c_exp n_max : ℕ) : Code .exact 19 :=
  .seq (.op (.const 15 (singleHashSpace c_exp n_max)))
       (.op (.exactBin .sub 0 0 15))

/-- Closed-form machine state after `unshiftFromHash2BaseCode c_exp n_max`. -/
@[expose]
def unshiftFromHash2BaseData (hashBase c_exp n_max : ℕ) (x : Data 19) : Data 19 :=
  (x.set 15 (singleHashSpace c_exp n_max)).set 0 hashBase

theorem shiftToHash2BaseCode_exec {w hashBase c_exp n_max : ℕ} {x : Data 19}
    (h0 : x.regs 0 = hashBase)
    (hfit_space : Fits w (hashBase + hashPairSpace c_exp n_max)) :
    Exec w (shiftToHash2BaseCode c_exp n_max) x
      (shiftToHash2BaseData hashBase c_exp n_max x) 2 := by
  have hfit_sh : Fits w (singleHashSpace c_exp n_max) :=
    hfit_space.of_le (by dsimp only [hashPairSpace]; omega)
  have hfit_h2 : Fits w (hash2Base hashBase c_exp n_max) :=
    hfit_space.of_le (by dsimp only [hash2Base, hashPairSpace]; omega)
  have e1 : Exec w (.op (.const 15 (singleHashSpace c_exp n_max)) : Code .exact 19)
      x (x.set 15 (singleHashSpace c_exp n_max)) 1 :=
    Exec.const hfit_sh
  have e2 : Exec w (.op (.exactBin .add 0 0 15) : Code .exact 19)
      (x.set 15 (singleHashSpace c_exp n_max))
      (shiftToHash2BaseData hashBase c_exp n_max x) 1 :=
    ExactLog.exec_exactBin (by simp +decide [h0, hash2Base]) hfit_h2
  exact e1.seq e2

theorem unshiftFromHash2BaseCode_exec {w hashBase c_exp n_max : ℕ} {x : Data 19}
    (h0 : x.regs 0 = hash2Base hashBase c_exp n_max)
    (hfit_space : Fits w (hashBase + hashPairSpace c_exp n_max)) :
    Exec w (unshiftFromHash2BaseCode c_exp n_max) x
      (unshiftFromHash2BaseData hashBase c_exp n_max x) 2 := by
  have hfit_sh : Fits w (singleHashSpace c_exp n_max) :=
    hfit_space.of_le (by dsimp only [hashPairSpace]; omega)
  have hfit_hb : Fits w hashBase :=
    hfit_space.of_le (by omega)
  have e1 : Exec w (.op (.const 15 (singleHashSpace c_exp n_max)) : Code .exact 19)
      x (x.set 15 (singleHashSpace c_exp n_max)) 1 :=
    Exec.const hfit_sh
  have e2 : Exec w (.op (.exactBin .sub 0 0 15) : Code .exact 19)
      (x.set 15 (singleHashSpace c_exp n_max))
      (unshiftFromHash2BaseData hashBase c_exp n_max x) 1 :=
    ExactLog.exec_exactBin (by simp +decide [h0, hash2Base]) hfit_hb
  exact e1.seq e2

private theorem ExecRand.seqDet {w : ℕ} {c₁ c₂ : Code .exact 19} {x : Data 19}
    {m₁ : ProbComp (Data 19 × ℕ)} {f : Data 19 → Data 19} {n₂ : ℕ}
    (h₁ : ExecRand w c₁ x m₁)
    (h₂ : ∀ z ∈ m₁.support, Exec w c₂ z.1 (f z.1) n₂) :
    ExecRand w (.seq c₁ c₂) x ((fun z => (f z.1, z.2 + n₂)) <$> m₁) := by
  have hseq := ExecRand.seq h₁ (m₂ := fun y => pure (f y, n₂)) fun z hz => (h₂ z hz).execRand
  simpa only [pure_bind, ← bind_pure_comp] using hseq

/-- Program resampling a single regime-switched hash block at `reg 0 = base`. -/
@[expose]
def resampleSingleCode (c_exp n_max M : ℕ) : Code .exact 19 :=
  if n_max < doubleTabThreshold c_exp then
    (KWise.resampleCode (cuckooK n_max)).rename cast18To19
  else
    (DoubleTabulation.resampleCode
      (DoubleTabulation.provableC c_exp) (DoubleTabulation.provableD c_exp)
      (DoubleTabulation.provableB n_max) M).rename cast12To19

/-- Program shifting `reg 0` to `hash2Base`, resampling the second hash block, and restoring
`reg 0 = hashBase`. -/
@[expose]
def resampleSecondBlockCode (c_exp n_max M : ℕ) : Code .exact 19 :=
  .seq (shiftToHash2BaseCode c_exp n_max)
  (.seq (resampleSingleCode c_exp n_max M)
        (unshiftFromHash2BaseCode c_exp n_max))

/-- Complete seed-resampling program `resampleHashPairCode`: resamples both regime-switched hash
blocks at `hashBase` and `hash2Base hashBase c_exp n_max` while preserving `reg 0 = hashBase` and
`HashPairTableRep`. -/
@[expose]
def resampleHashPairCode (c_exp n_max M : ℕ) : Code .exact 19 :=
  .seq (resampleSingleCode c_exp n_max M) (resampleSecondBlockCode c_exp n_max M)

/-- Exact instruction count of `resampleSingleCode c_exp n_max M`. -/
@[expose]
def resampleSingleSteps (c_exp n_max : ℕ) : ℕ :=
  if n_max < doubleTabThreshold c_exp then
    5 * cuckooK n_max + 10
  else
    DoubleTabulation.resampleSteps
      (DoubleTabulation.provableC c_exp) (DoubleTabulation.provableD c_exp)
      (DoubleTabulation.provableB n_max)

/-- Exact instruction count of `resampleHashPairCode c_exp n_max M`. -/
@[expose]
def resampleHashPairSteps (c_exp n_max : ℕ) : ℕ :=
  2 * resampleSingleSteps c_exp n_max + 4

/-- Explicit `ProbComp (Data 19 × ℕ)` induced by `resampleSingleCode c_exp n_max M` at `base`. -/
@[expose]
noncomputable def resampleSingleComp (base c_exp n_max U M : ℕ) (x : Data 19) :
    ProbComp (Data 19 × ℕ) :=
  if n_max < doubleTabThreshold c_exp then
    (fun z : Data 18 × ℕ => (z.1.extend cast18To19 x, z.2)) <$>
      KWise.resampleComp base U M (cuckooK n_max) (x.comap cast18To19)
  else
    (fun z : Data 12 × ℕ => (z.1.extend cast12To19 x, z.2)) <$>
      DoubleTabulation.resampleComp base
        (DoubleTabulation.provableC c_exp) (DoubleTabulation.provableD c_exp)
        (DoubleTabulation.provableB n_max) M (x.comap cast12To19)

/-- Explicit `ProbComp (Data 19 × ℕ)` induced by `resampleSecondBlockCode c_exp n_max M`. -/
@[expose]
noncomputable def resampleSecondBlockComp (hashBase c_exp n_max U M : ℕ) (x : Data 19) :
    ProbComp (Data 19 × ℕ) :=
  let d0 := shiftToHash2BaseData hashBase c_exp n_max x
  (fun z : Data 19 × ℕ => (unshiftFromHash2BaseData hashBase c_exp n_max z.1, 2 + (z.2 + 2))) <$>
    resampleSingleComp (hash2Base hashBase c_exp n_max) c_exp n_max U M d0

/-- Exact `ProbComp` semantics of `resampleHashPairCode c_exp n_max M`. -/
@[expose]
noncomputable def resampleHashPairComp (hashBase c_exp n_max U M : ℕ) (x : Data 19) :
    ProbComp (Data 19 × ℕ) := do
  let z1 ← resampleSingleComp hashBase c_exp n_max U M x
  let z2 ← resampleSecondBlockComp hashBase c_exp n_max U M z1.1
  pure (z2.1, z1.2 + z2.2)

theorem resampleSingleCode_execRand {w base c_exp n_max U M : ℕ} {x : Data 19}
    (htab : SingleTableRep base c_exp n_max U M x.mem) (hbase : x.regs 0 = base)
    (hfit_space : Fits w (base + singleHashSpace c_exp n_max))
    (hfit_q : Fits w (2 ^ Probability.trinomialDeg U M)) :
    ExecRand w (resampleSingleCode c_exp n_max M) x
      (resampleSingleComp base c_exp n_max U M x) := by
  unfold resampleSingleCode resampleSingleComp
  split_ifs with hlt
  · have hsp := singleHashSpace_of_lt hlt
    have hpow : 1 ≤ 2 ^ (2 * KWise.chunkBits n_max) := Nat.one_le_two_pow
    have hkw : KWise.space n_max (cuckooK n_max) =
        8 + cuckooK n_max + 2 ^ (2 * KWise.chunkBits n_max) := rfl
    have hfit_end : Fits w (base + 8 + cuckooK n_max) :=
      hfit_space.of_le (by omega)
    have htab_kw : KWise.TableRep base (KWise.chunkBits n_max) U M (cuckooK n_max) x.mem := by
      unfold SingleTableRep at htab
      rwa [decide_eq_true hlt] at htab
    have hbase18 : (x.comap cast18To19).regs 0 = base := hbase
    exact (KWise.resampleCode_execRand htab_kw hbase18 hfit_end hfit_q).rename injective_cast18To19
  · have hsp := singleHashSpace_of_not_lt hlt
    have hfit_dt : Fits w (base + DoubleTabulation.space (DoubleTabulation.provableC c_exp)
        (DoubleTabulation.provableD c_exp) (DoubleTabulation.provableB n_max)) := by
      rwa [← hsp]
    have hpow_b_le := DoubleTabulation.two_pow_provableB_le_space c_exp n_max
    have hfit_mask_b : Fits w (2 ^ DoubleTabulation.provableB n_max - 1) :=
      hfit_dt.of_le (by omega)
    have hfit_mask_M : Fits w (2 ^ M - 1) :=
      hfit_q.of_le ((Nat.sub_le _ 1).trans
        (Nat.pow_le_pow_right (by decide) (Probability.le_trinomialDeg U M)))
    have hfit_1 : Fits w 1 :=
      hfit_space.of_le (by have := le_singleHashSpace c_exp n_max; omega)
    have hbase12 : (x.comap cast12To19).regs 0 = base := hbase
    exact (DoubleTabulation.resampleCode_execRand hbase12 hfit_dt
      hfit_mask_b hfit_mask_M hfit_1).rename injective_cast12To19

theorem mem_support_resampleSingleComp {base c_exp n_max U M : ℕ} {x : Data 19} {z : Data 19 × ℕ}
    (htab : SingleTableRep base c_exp n_max U M x.mem) (hbase : x.regs 0 = base)
    (hz : z ∈ (resampleSingleComp base c_exp n_max U M x).support) :
    z.2 ≤ resampleSingleSteps c_exp n_max ∧
    z.1.regs 0 = base ∧
    SingleTableRep base c_exp n_max U M z.1.mem ∧
    SingleSeedRep base c_exp n_max U M (extractSingleSeed base c_exp n_max U M z.1.mem) z.1.mem ∧
    (∀ a, (a < base ∨ base + singleHashSpace c_exp n_max ≤ a) → z.1.mem a = x.mem a) := by
  unfold resampleSingleComp at hz
  split_ifs at hz with hlt
  · obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    have htab_kw : KWise.TableRep base (KWise.chunkBits n_max) U M (cuckooK n_max) x.mem := by
      unfold SingleTableRep at htab
      rwa [decide_eq_true hlt] at htab
    have hbase18 : (x.comap cast18To19).regs 0 = base := hbase
    obtain ⟨⟨⟨htab', hseed'⟩, hz0, hout⟩, hsteps⟩ :=
      KWise.mem_support_resampleComp htab_kw hbase18 hz₀
    have h0' : (z₀.1.extend cast18To19 x).regs 0 = base := by
      change ((z₀.1.extend cast18To19 x).comap cast18To19).regs 0 = base
      rw [Data.comap_extend injective_cast18To19, hz0]
    have hsp := singleHashSpace_of_lt hlt
    have hpow : 1 ≤ 2 ^ (2 * KWise.chunkBits n_max) := Nat.one_le_two_pow
    have hkw : KWise.space n_max (cuckooK n_max) =
        8 + cuckooK n_max + 2 ^ (2 * KWise.chunkBits n_max) := rfl
    refine ⟨by simpa [resampleSingleSteps, hlt] using hsteps, h0', ?_, ?_,
      fun a ha => hout a (by omega)⟩
    · unfold SingleTableRep
      rw [decide_eq_true hlt]
      exact htab'
    · unfold SingleSeedRep extractSingleSeed
      revert hseed'
      rw [decide_eq_true hlt]
      exact id
  · obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    have hbase12 : (x.comap cast12To19).regs 0 = base := hbase
    obtain ⟨hz0, hseed', hout, hsteps⟩ :=
      DoubleTabulation.mem_support_resampleComp hbase12 hz₀
    have h0' : (z₀.1.extend cast12To19 x).regs 0 = base := by
      change ((z₀.1.extend cast12To19 x).comap cast12To19).regs 0 = base
      rw [Data.comap_extend injective_cast12To19, hz0]
    have hsp := singleHashSpace_of_not_lt hlt
    refine ⟨by simp [resampleSingleSteps, hlt, hsteps], h0', ?_, ?_,
      fun a ha => hout a (by rwa [← hsp])⟩
    · unfold SingleTableRep
      rw [decide_eq_false hlt]
      trivial
    · unfold SingleSeedRep extractSingleSeed
      revert hseed'
      rw [decide_eq_false hlt]
      exact id

theorem resampleSecondBlockCode_execRand {w hashBase c_exp n_max U M : ℕ} {x : Data 19}
    (htab2 : SingleTableRep (hash2Base hashBase c_exp n_max) c_exp n_max U M x.mem)
    (h0 : x.regs 0 = hashBase)
    (hfit_space : Fits w (hashBase + hashPairSpace c_exp n_max))
    (hfit_q : Fits w (2 ^ Probability.trinomialDeg U M)) :
    ExecRand w (resampleSecondBlockCode c_exp n_max M) x
      (resampleSecondBlockComp hashBase c_exp n_max U M x) := by
  have esh := shiftToHash2BaseCode_exec h0 hfit_space
  set d0 := shiftToHash2BaseData hashBase c_exp n_max x
  have hd0_0 : d0.regs 0 = hash2Base hashBase c_exp n_max := by
    simp +decide [d0, shiftToHash2BaseData]
  have hfit_h2 : Fits w (hash2Base hashBase c_exp n_max + singleHashSpace c_exp n_max) :=
    hfit_space.of_le (by dsimp only [hash2Base, hashPairSpace]; omega)
  have hres := resampleSingleCode_execRand (x := d0) htab2 hd0_0 hfit_h2 hfit_q
  have hdet := ExecRand.seqDet hres (f := unshiftFromHash2BaseData hashBase c_exp n_max) (n₂ := 2)
    fun z hz => by
      obtain ⟨-, hz0, -, -, -⟩ := mem_support_resampleSingleComp (x := d0) htab2 hd0_0 hz
      exact unshiftFromHash2BaseCode_exec hz0 hfit_space
  simpa only [resampleSecondBlockCode, resampleSecondBlockComp, d0, Functor.map_map] using
    esh.seqRand hdet

theorem mem_support_resampleSecondBlockComp {hashBase c_exp n_max U M : ℕ} {x : Data 19}
    {z : Data 19 × ℕ}
    (htab2 : SingleTableRep (hash2Base hashBase c_exp n_max) c_exp n_max U M x.mem)
    (hz : z ∈ (resampleSecondBlockComp hashBase c_exp n_max U M x).support) :
    z.2 ≤ resampleSingleSteps c_exp n_max + 4 ∧
    z.1.regs 0 = hashBase ∧
    SingleTableRep (hash2Base hashBase c_exp n_max) c_exp n_max U M z.1.mem ∧
    SingleSeedRep (hash2Base hashBase c_exp n_max) c_exp n_max U M
      (extractSingleSeed (hash2Base hashBase c_exp n_max) c_exp n_max U M z.1.mem) z.1.mem ∧
    (∀ a, (a < hash2Base hashBase c_exp n_max ∨
      hash2Base hashBase c_exp n_max + singleHashSpace c_exp n_max ≤ a) → z.1.mem a = x.mem a) := by
  dsimp only [resampleSecondBlockComp] at hz
  obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
  set d0 := shiftToHash2BaseData hashBase c_exp n_max x
  have hd0_0 : d0.regs 0 = hash2Base hashBase c_exp n_max := by
    simp +decide [d0, shiftToHash2BaseData]
  obtain ⟨ht, -, htab', hseed', hout⟩ := mem_support_resampleSingleComp (x := d0) htab2 hd0_0 hz₀
  exact ⟨by omega, by simp +decide [unshiftFromHash2BaseData], htab', hseed', hout⟩

/-- **`resampleHashPairCode` randomized execution**: resamples both regime-switched hash blocks at
`hashBase` and `hash2Base hashBase c_exp n_max`. -/
theorem resampleHashPairCode_execRand {w hashBase c_exp n_max U M : ℕ} {x : Data 19}
    (htab : HashPairTableRep hashBase c_exp n_max U M x.mem) (h0 : x.regs 0 = hashBase)
    (hfit_space : Fits w (hashBase + hashPairSpace c_exp n_max))
    (hfit_q : Fits w (2 ^ Probability.trinomialDeg U M)) :
    ExecRand w (resampleHashPairCode c_exp n_max M) x
      (resampleHashPairComp hashBase c_exp n_max U M x) := by
  have hfit_h1 : Fits w (hashBase + singleHashSpace c_exp n_max) :=
    hfit_space.of_le (by dsimp only [hashPairSpace]; omega)
  have h1 := resampleSingleCode_execRand htab.1 h0 hfit_h1 hfit_q
  refine h1.seq fun z1 hz1 => ?_
  obtain ⟨-, hz1_0, -, -, hz1_frame⟩ := mem_support_resampleSingleComp htab.1 h0 hz1
  have htab2_z1 : SingleTableRep (hash2Base hashBase c_exp n_max) c_exp n_max U M z1.1.mem :=
    htab.2.congr_of_footprint (fun a ha1 _ =>
      hz1_frame a (Or.inr (by dsimp only [hash2Base] at ha1; omega)))
  exact resampleSecondBlockCode_execRand htab2_z1 hz1_0 hfit_space hfit_q

theorem mem_support_resampleHashPairComp {hashBase c_exp n_max U M : ℕ} {x : Data 19}
    {z : Data 19 × ℕ}
    (htab : HashPairTableRep hashBase c_exp n_max U M x.mem) (h0 : x.regs 0 = hashBase)
    (hz : z ∈ (resampleHashPairComp hashBase c_exp n_max U M x).support) :
    z.2 ≤ resampleHashPairSteps c_exp n_max ∧
    z.1.regs 0 = hashBase ∧
    HashPairRep hashBase c_exp n_max U M (extractSeed hashBase c_exp n_max U M z.1.mem) z.1.mem ∧
    (∀ a, (a < hashBase ∨ hashBase + hashPairSpace c_exp n_max ≤ a) → z.1.mem a = x.mem a) := by
  dsimp only [resampleHashPairComp] at hz
  obtain ⟨z1, hz1, hrest⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
  obtain ⟨z2, hz2, hpure⟩ := OracleComp.mem_supportWith_bind_iff.mp hrest
  cases OracleComp.eq_of_mem_supportWith_pure hpure
  obtain ⟨ht1, -, htab1_z1, hseed1_z1, hframe1⟩ :=
    mem_support_resampleSingleComp htab.1 h0 hz1
  have htab2_z1 : SingleTableRep (hash2Base hashBase c_exp n_max) c_exp n_max U M z1.1.mem :=
    htab.2.congr_of_footprint (fun a ha1 _ =>
      hframe1 a (Or.inr (by dsimp only [hash2Base] at ha1; omega)))
  obtain ⟨ht2, hz2_0, htab2_z2, hseed2_z2, hframe2⟩ :=
    mem_support_resampleSecondBlockComp htab2_z1 hz2
  have hframe_block1 : ∀ a, hashBase ≤ a → a < hashBase + singleHashSpace c_exp n_max →
      z2.1.mem a = z1.1.mem a :=
    fun a _ ha2 => hframe2 a (Or.inl (by dsimp only [hash2Base]; omega))
  have htab1_z2 : SingleTableRep hashBase c_exp n_max U M z2.1.mem :=
    htab1_z1.congr_of_footprint hframe_block1
  have hextract1_eq :
      extractSingleSeed hashBase c_exp n_max U M z2.1.mem =
        extractSingleSeed hashBase c_exp n_max U M z1.1.mem :=
    extractSingleSeed_congr_of_footprint hframe_block1
  have hseed1_z2 : SingleSeedRep hashBase c_exp n_max U M
      (extractSingleSeed hashBase c_exp n_max U M z2.1.mem) z2.1.mem := by
    rw [hextract1_eq]
    exact hseed1_z1.congr_of_footprint hframe_block1
  refine ⟨by dsimp only [resampleHashPairSteps]; omega, hz2_0,
    ⟨⟨htab1_z2, htab2_z2⟩, ⟨hseed1_z2, hseed2_z2⟩⟩,
    fun a ha => ?_⟩
  have ha2 : a < hash2Base hashBase c_exp n_max ∨
      hash2Base hashBase c_exp n_max + singleHashSpace c_exp n_max ≤ a := by
    dsimp only [hash2Base, hashPairSpace] at ha ⊢
    exact ha.imp (by omega) (by omega)
  have ha1 : a < hashBase ∨ hashBase + singleHashSpace c_exp n_max ≤ a := by
    dsimp only [hashPairSpace] at ha
    exact ha.imp id (by omega)
  rw [hframe2 a ha2, hframe1 a ha1]

private theorem map_extractSingleSeed_eval_resampleSingleComp
    (base c_exp n_max U M : ℕ) (x : Data 19) :
    ((resampleSingleComp base c_exp n_max U M x).eval).map
      (fun z => extractSingleSeed base c_exp n_max U M z.1.mem) =
      PMF.uniformOfFintype (SingleSeed c_exp n_max U M) := by
  unfold resampleSingleComp SingleSeed extractSingleSeed
  split_ifs with hlt
  · rw [decide_eq_true hlt, ProbComp.eval_map, PMF.map_comp]
    exact KWise.map_extractSeeds_eval_resampleComp base U M (cuckooK n_max) (x.comap cast18To19)
  · rw [decide_eq_false hlt, ProbComp.eval_map, PMF.map_comp]
    exact DoubleTabulation.map_extractSeed_eval_resampleComp base
      (DoubleTabulation.provableC c_exp) (DoubleTabulation.provableD c_exp)
      (DoubleTabulation.provableB n_max) M (x.comap cast12To19)

private theorem map_pair_extractSingleSeed_eval_resampleSecondBlockComp
    {hashBase c_exp n_max U M : ℕ} {d : Data 19}
    (htab2 : SingleTableRep (hash2Base hashBase c_exp n_max) c_exp n_max U M d.mem) :
    ((resampleSecondBlockComp hashBase c_exp n_max U M d).eval).map
      (fun z : Data 19 × ℕ =>
        (extractSingleSeed hashBase c_exp n_max U M z.1.mem,
         extractSingleSeed (hash2Base hashBase c_exp n_max) c_exp n_max U M z.1.mem)) =
      (PMF.uniformOfFintype (SingleSeed c_exp n_max U M)).map
        (extractSingleSeed hashBase c_exp n_max U M d.mem, ·) := by
  set d0 := shiftToHash2BaseData hashBase c_exp n_max d
  have hd0_0 : d0.regs 0 = hash2Base hashBase c_exp n_max := by
    simp +decide [d0, shiftToHash2BaseData]
  dsimp only [resampleSecondBlockComp]
  rw [ProbComp.eval_map, PMF.map_comp]
  have hcongr :
      ((resampleSingleComp (hash2Base hashBase c_exp n_max) c_exp n_max U M d0).eval).map
        ((fun z : Data 19 × ℕ =>
            (extractSingleSeed hashBase c_exp n_max U M z.1.mem,
             extractSingleSeed (hash2Base hashBase c_exp n_max) c_exp n_max U M z.1.mem)) ∘
          fun z : Data 19 × ℕ =>
            (unshiftFromHash2BaseData hashBase c_exp n_max z.1, 2 + (z.2 + 2))) =
      ((resampleSingleComp (hash2Base hashBase c_exp n_max) c_exp n_max U M d0).eval).map
        ((fun θ₂ => (extractSingleSeed hashBase c_exp n_max U M d.mem, θ₂)) ∘
          fun z : Data 19 × ℕ =>
            extractSingleSeed (hash2Base hashBase c_exp n_max) c_exp n_max U M z.1.mem) := by
    refine PMF.map_congr_on_support _ _ _ fun z hz => ?_
    rw [ProbComp.support_eval] at hz
    obtain ⟨-, -, -, -, hframe⟩ := mem_support_resampleSingleComp (x := d0) htab2 hd0_0 hz
    have h1 : extractSingleSeed hashBase c_exp n_max U M z.1.mem =
        extractSingleSeed hashBase c_exp n_max U M d.mem :=
      extractSingleSeed_congr_of_footprint (fun a _ ha2 =>
        hframe a (Or.inl (by dsimp only [hash2Base]; omega)))
    dsimp only [Function.comp_apply, unshiftFromHash2BaseData, Data.set]
    rw [h1]
  rw [hcongr, ← PMF.map_comp,
    map_extractSingleSeed_eval_resampleSingleComp
      (hash2Base hashBase c_exp n_max) c_exp n_max U M d0]

private theorem map_pair_extractSingleSeed_eval_resampleHashPairComp
    {hashBase c_exp n_max U M : ℕ} {x : Data 19}
    (htab : HashPairTableRep hashBase c_exp n_max U M x.mem) (h0 : x.regs 0 = hashBase) :
    ((resampleHashPairComp hashBase c_exp n_max U M x).eval).map
      (fun z : Data 19 × ℕ =>
        (extractSingleSeed hashBase c_exp n_max U M z.1.mem,
         extractSingleSeed (hash2Base hashBase c_exp n_max) c_exp n_max U M z.1.mem)) =
      PMF.uniformOfFintype (SingleSeed c_exp n_max U M × SingleSeed c_exp n_max U M) := by
  dsimp only [resampleHashPairComp]
  rw [ProbComp.eval_bind, PMF.map_bind]
  have hcongr :
      (resampleSingleComp hashBase c_exp n_max U M x).eval.bind
        (fun z1 : Data 19 × ℕ =>
          ((do
            let z2 ← resampleSecondBlockComp hashBase c_exp n_max U M z1.1
            pure (z2.1, z1.2 + z2.2)).eval).map
            (fun z : Data 19 × ℕ =>
              (extractSingleSeed hashBase c_exp n_max U M z.1.mem,
               extractSingleSeed (hash2Base hashBase c_exp n_max) c_exp n_max U M z.1.mem))) =
      (resampleSingleComp hashBase c_exp n_max U M x).eval.bind
        (fun z1 : Data 19 × ℕ =>
          (PMF.uniformOfFintype (SingleSeed c_exp n_max U M)).map
            (extractSingleSeed hashBase c_exp n_max U M z1.1.mem, ·)) := by
    refine PMF.bind_congr_on_support _ _ _ fun z1 hz1 => ?_
    rw [ProbComp.support_eval] at hz1
    obtain ⟨-, -, -, -, hframe1⟩ := mem_support_resampleSingleComp htab.1 h0 hz1
    have htab2_z1 : SingleTableRep (hash2Base hashBase c_exp n_max) c_exp n_max U M z1.1.mem :=
      htab.2.congr_of_footprint (fun a ha1 _ =>
        hframe1 a (Or.inr (by dsimp only [hash2Base] at ha1; omega)))
    have hd : (do
        let z2 ← resampleSecondBlockComp hashBase c_exp n_max U M z1.1
        pure (z2.1, z1.2 + z2.2)) =
        (fun z2 : Data 19 × ℕ => (z2.1, z1.2 + z2.2)) <$>
          resampleSecondBlockComp hashBase c_exp n_max U M z1.1 :=
      bind_pure_comp _ _
    rw [hd, ProbComp.eval_map, PMF.map_comp]
    exact map_pair_extractSingleSeed_eval_resampleSecondBlockComp htab2_z1
  rw [hcongr]
  have hbind :
      (resampleSingleComp hashBase c_exp n_max U M x).eval.bind
        (fun z1 : Data 19 × ℕ =>
          (PMF.uniformOfFintype (SingleSeed c_exp n_max U M)).map
            (extractSingleSeed hashBase c_exp n_max U M z1.1.mem, ·)) =
      (((resampleSingleComp hashBase c_exp n_max U M x).eval).map
          (fun z1 => extractSingleSeed hashBase c_exp n_max U M z1.1.mem)).bind
        (fun θ₁ => (PMF.uniformOfFintype (SingleSeed c_exp n_max U M)).map (θ₁, ·)) := by
    rw [PMF.bind_map]
    rfl
  rw [hbind, map_extractSingleSeed_eval_resampleSingleComp,
    PMF.uniformOfFintype_prod]

/-- **Exact uniformity of `resampleHashPairComp`**: the extracted seed
`extractSeed hashBase c_exp n_max U M z.1.mem` is distributed according to
`seedLaw c_exp n_max U M`. -/
theorem map_extractSeed_eval_resampleHashPairComp {hashBase c_exp n_max U M : ℕ} {x : Data 19}
    (htab : HashPairTableRep hashBase c_exp n_max U M x.mem) (h0 : x.regs 0 = hashBase) :
    ((resampleHashPairComp hashBase c_exp n_max U M x).eval).map
      (fun z => extractSeed hashBase c_exp n_max U M z.1.mem) = seedLaw c_exp n_max U M :=
  map_pair_extractSingleSeed_eval_resampleHashPairComp htab h0

/-- Word-RAM program evaluating a single regime-switched hash block at `reg 0 = base` and
`reg 1 = u.val` into `reg 2` (`regOut`) without modifying memory. -/
@[expose]
def evalSingleCode (c_exp n_max : ℕ) : Code .exact 19 :=
  if n_max < doubleTabThreshold c_exp then
    (KWise.evalCode (cuckooK n_max)).rename cast18To19
  else
    (DoubleTabulation.evalCode
      (DoubleTabulation.provableC c_exp) (DoubleTabulation.provableD c_exp)
      (DoubleTabulation.provableB n_max)).rename cast12To19

/-- Word-RAM program evaluating `h₁(u)` into `reg 2` (`regOut`) while preserving
`reg 0 = hashBase`, `reg 1 = u.val`, and all of memory (`y.mem = x.mem`). -/
@[expose]
def evalHash1Code (c_exp n_max : ℕ) : Code .exact 19 :=
  evalSingleCode c_exp n_max

/-- Word-RAM program evaluating `h₂(u)` into `reg 2` (`regOut`) while preserving
`reg 0 = hashBase`, `reg 1 = u.val`, and all of memory (`y.mem = x.mem`). -/
@[expose]
def evalHash2Code (c_exp n_max : ℕ) : Code .exact 19 :=
  .seq (shiftToHash2BaseCode c_exp n_max)
  (.seq (evalSingleCode c_exp n_max)
        (unshiftFromHash2BaseCode c_exp n_max))

/-- Step bound for `evalSingleCode c_exp n_max`. -/
@[expose]
def evalSingleSteps (c_exp n_max U M : ℕ) : ℕ :=
  if n_max < doubleTabThreshold c_exp then
    KWise.evalSteps n_max U M (cuckooK n_max)
  else
    DoubleTabulation.evalSteps (DoubleTabulation.provableC c_exp) (DoubleTabulation.provableD c_exp)

/-- Step bound for `evalHash1Code c_exp n_max` and `evalHash2Code c_exp n_max`. -/
@[expose]
def evalHashSteps (c_exp n_max U M : ℕ) : ℕ :=
  evalSingleSteps c_exp n_max U M + 4

/-- Instruction bound on `evalHashSteps c_exp n_max U M` depending only on `c_exp`. It holds for
all `n_max : ℕ` whenever `U ≤ max n_max 4 ^ c_exp` and
`M ≤ max c_exp 1 * Nat.clog 2 (max n_max 4) + 5` (`evalHashSteps_le`); below
`doubleTabThreshold c_exp` it uses `cuckooK n_max ≤ cuckooKBound c_exp`
(`cuckooK_le_cuckooKBound_of_lt`). -/
@[expose]
def evalHashBound (c_exp : ℕ) : ℕ :=
  DoubleTabulation.provableEvalBound c_exp (cuckooKBound c_exp) + 4

/-- **All-`n_max` constant instruction bound for `evalHashSteps` (`O_{c_exp}(1)`)**:
whenever `U ≤ max n_max 4 ^ c_exp` and `M ≤ max c_exp 1 * Nat.clog 2 (max n_max 4) + 5`,
`evalHashSteps c_exp n_max U M ≤ evalHashBound c_exp`. -/
theorem evalHashSteps_le {c_exp n_max U M : ℕ}
    (hU : U ≤ max n_max 4 ^ c_exp)
    (hM : M ≤ max c_exp 1 * Nat.clog 2 (max n_max 4) + 5) :
    evalHashSteps c_exp n_max U M ≤ evalHashBound c_exp := by
  dsimp only [evalHashSteps, evalSingleSteps, evalHashBound, DoubleTabulation.provableEvalBound]
  refine Nat.add_le_add_right ?_ 4
  split_ifs with hlt
  · refine le_trans ?_ (le_max_left _ _)
    dsimp only [KWise.evalSteps, KWise.evalStepsFromB]
    have hL : KWise.limbCountFromB (KWise.chunkBits n_max) (trinomialDeg U M) ≤
        DoubleTabulation.provableLimbBound c_exp :=
      DoubleTabulation.limbCount_le_provableLimbBound hU hM
    have hk : cuckooK n_max ≤ cuckooKBound c_exp :=
      cuckooK_le_cuckooKBound_of_lt hlt
    gcongr
  · exact le_max_right _ _

theorem evalSingleCode_execWithin {w base c_exp n_max U M : ℕ}
    {θ₀ : SingleSeed c_exp n_max U M} (u : Fin U) {x : Data 19}
    (htab : SingleTableRep base c_exp n_max U M x.mem)
    (hseed : SingleSeedRep base c_exp n_max U M θ₀ x.mem)
    (h0 : x.regs 0 = base) (h1 : x.regs 1 = u.val)
    (hw : 2 * Probability.trinomialDeg U M ≤ w)
    (hfit_space : Fits w (base + singleHashSpace c_exp n_max)) :
    ∃ y : Data 19,
      ExecWithin w (evalSingleCode c_exp n_max) x y (evalSingleSteps c_exp n_max U M) ∧
      y.regs 0 = base ∧
      y.regs 1 = u.val ∧
      y.regs 2 = (evalSingle c_exp n_max U M θ₀ u).val ∧
      y.mem = x.mem := by
  unfold evalSingleCode evalSingleSteps
  split_ifs with hlt
  · have hsp := singleHashSpace_of_lt hlt
    have hfit_kw : Fits w (base + KWise.space n_max (cuckooK n_max)) := by
      rwa [← hsp]
    have htab_kw : KWise.TableRep base (KWise.chunkBits n_max) U M (cuckooK n_max) x.mem := by
      unfold SingleTableRep at htab
      rwa [decide_eq_true hlt] at htab
    unfold SingleSeed SingleSeedRep evalSingle at *
    revert θ₀ hseed
    rw [decide_eq_true hlt]
    intro θ₀ hseed
    obtain ⟨y_kw, hex_kw, hy0, hy1, hy2, hymem⟩ :=
      KWise.evalCode_execWithin (w := w) (base := base) (n_max := n_max)
        (U := U) (M := M) (k := cuckooK n_max) (c := θ₀) u (x := x.comap cast18To19)
        ⟨htab_kw, hseed⟩
        (by simp +decide [cast18To19, Data.comap, h0])
        (by simp +decide [cast18To19, Data.comap, h1])
        hw hfit_kw
    refine ⟨y_kw.extend cast18To19 x, hex_kw.rename injective_cast18To19, ?_, ?_, ?_, hymem⟩
    · change ((y_kw.extend cast18To19 x).comap cast18To19).regs 0 = base
      rw [Data.comap_extend injective_cast18To19, hy0]
    · change ((y_kw.extend cast18To19 x).comap cast18To19).regs 1 = u.val
      rw [Data.comap_extend injective_cast18To19, hy1]
    · change ((y_kw.extend cast18To19 x).comap cast18To19).regs 2 =
        (trinomialPolyHash (trinomialStep U M) (cuckooK n_max) U M θ₀ u).val
      rw [Data.comap_extend injective_cast18To19, hy2]
  · have hsp := singleHashSpace_of_not_lt hlt
    have hfit_dt : Fits w (base + DoubleTabulation.space (DoubleTabulation.provableC c_exp)
        (DoubleTabulation.provableD c_exp) (DoubleTabulation.provableB n_max)) := by
      rwa [← hsp]
    have hpow_b_le := DoubleTabulation.two_pow_provableB_le_space c_exp n_max
    have hfit_pow_b : Fits w (2 ^ DoubleTabulation.provableB n_max) :=
      hfit_dt.of_le (by omega)
    have hfit_q := KWise.fits_two_pow_trinomialDeg hw
    have hfit_pow_M : Fits w (2 ^ M) :=
      hfit_q.of_le (Nat.pow_le_pow_right (by decide) (Probability.le_trinomialDeg U M))
    have hfit_u : Fits w u.val :=
      hfit_q.of_le (le_trans (le_of_lt u.isLt) (Probability.le_two_pow_trinomialDeg U M))
    unfold SingleSeed SingleSeedRep evalSingle at *
    revert θ₀ hseed
    rw [decide_eq_false hlt]
    intro θ₀ hseed
    obtain ⟨y12, he12, hymem, hy0, hy1, hy2, _⟩ :=
      DoubleTabulation.evalCode_execWithin u (x := x.comap cast12To19)
        (by simp +decide [cast12To19, Data.comap, h0])
        (by simp +decide [cast12To19, Data.comap, h1])
        hseed hfit_dt hfit_pow_b hfit_pow_M hfit_u
    refine ⟨y12.extend cast12To19 x, he12.rename injective_cast12To19, ?_, ?_, ?_, hymem⟩
    · change ((y12.extend cast12To19 x).comap cast12To19).regs 0 = base
      rw [Data.comap_extend injective_cast12To19, hy0]
    · change ((y12.extend cast12To19 x).comap cast12To19).regs 1 = u.val
      rw [Data.comap_extend injective_cast12To19, hy1]
    · change ((y12.extend cast12To19 x).comap cast12To19).regs 2 =
        (doubleTabHash (DoubleTabulation.provableC c_exp) (DoubleTabulation.provableD c_exp)
          (DoubleTabulation.provableB n_max) U M θ₀.1 θ₀.2 u).val
      rw [Data.comap_extend injective_cast12To19, hy2]

theorem evalHash1Code_execWithin {w hashBase c_exp n_max U M : ℕ}
    {θ : Seed c_exp n_max U M} (u : Fin U) {x : Data 19}
    (hrep : HashPairRep hashBase c_exp n_max U M θ x.mem)
    (h0 : x.regs 0 = hashBase) (h1 : x.regs 1 = u.val)
    (hw : 2 * Probability.trinomialDeg U M ≤ w)
    (hfit_space : Fits w (hashBase + hashPairSpace c_exp n_max)) :
    ∃ y : Data 19,
      ExecWithin w (evalHash1Code c_exp n_max) x y (evalHashSteps c_exp n_max U M) ∧
      y.regs 0 = hashBase ∧
      y.regs 1 = u.val ∧
      y.regs 2 = (evalHash1 θ u).val ∧
      HashPairRep hashBase c_exp n_max U M θ y.mem ∧
      y.mem = x.mem := by
  have hfit_h1 : Fits w (hashBase + singleHashSpace c_exp n_max) :=
    hfit_space.of_le (by dsimp only [hashPairSpace]; omega)
  obtain ⟨y, ⟨t, ht, he⟩, hy0, hy1, hy2, hymem⟩ :=
    evalSingleCode_execWithin u hrep.1.1 hrep.2.1 h0 h1 hw hfit_h1
  refine ⟨y, ⟨t, by dsimp only [evalHashSteps]; omega, he⟩, hy0, hy1, hy2, ?_, hymem⟩
  rwa [hymem]

theorem evalHash2Code_execWithin {w hashBase c_exp n_max U M : ℕ}
    {θ : Seed c_exp n_max U M} (u : Fin U) {x : Data 19}
    (hrep : HashPairRep hashBase c_exp n_max U M θ x.mem)
    (h0 : x.regs 0 = hashBase) (h1 : x.regs 1 = u.val)
    (hw : 2 * Probability.trinomialDeg U M ≤ w)
    (hfit_space : Fits w (hashBase + hashPairSpace c_exp n_max)) :
    ∃ y : Data 19,
      ExecWithin w (evalHash2Code c_exp n_max) x y (evalHashSteps c_exp n_max U M) ∧
      y.regs 0 = hashBase ∧
      y.regs 1 = u.val ∧
      y.regs 2 = (evalHash2 θ u).val ∧
      HashPairRep hashBase c_exp n_max U M θ y.mem ∧
      y.mem = x.mem := by
  have esh := shiftToHash2BaseCode_exec h0 hfit_space
  set d0 := shiftToHash2BaseData hashBase c_exp n_max x
  have hfit_h2 : Fits w (hash2Base hashBase c_exp n_max + singleHashSpace c_exp n_max) :=
    hfit_space.of_le (by dsimp only [hash2Base, hashPairSpace]; omega)
  obtain ⟨d1, ⟨t, ht, he⟩, hd1_0, hd1_1, hd1_2, hd1_mem⟩ :=
    evalSingleCode_execWithin u (x := d0) hrep.1.2 hrep.2.2
      (by simp +decide [d0, shiftToHash2BaseData])
      (by simp +decide [d0, shiftToHash2BaseData, h1])
      hw hfit_h2
  have eun := unshiftFromHash2BaseCode_exec hd1_0 hfit_space
  set y := unshiftFromHash2BaseData hashBase c_exp n_max d1
  refine ⟨y, ⟨2 + (t + 2), by dsimp only [evalHashSteps]; omega, esh.seq (he.seq eun)⟩,
    by simp +decide [y, unshiftFromHash2BaseData],
    by simp +decide [y, unshiftFromHash2BaseData, hd1_1],
    by simp +decide [y, unshiftFromHash2BaseData, hd1_2, evalHash2],
    ?_, ?_⟩
  · change HashPairRep hashBase c_exp n_max U M θ d1.mem
    rwa [hd1_mem]
  · exact hd1_mem

end Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing
