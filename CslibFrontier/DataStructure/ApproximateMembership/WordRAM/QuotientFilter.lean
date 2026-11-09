/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.ApproximateMembership.QuotientFilter.Probability
public import CslibFrontier.DataStructure.ApproximateMembership.WordRAM.QuotientFilter.Cluster
public import CslibFrontier.DataStructure.WordRAM.Randomized.ObliviousSequence
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map

/-!
# Word-RAM Implementation of the Two-Stage Quotient Filter

This module packages the bit-packed two-stage quotient filter into a reusable
`Cslib.DataStructure.WordRAM.Randomized.ObliviousSequenceImpl` certificate realizing
`Cslib.DataStructure.ApproximateMembership.spec U n ε` on the Word-RAM without any universe-to-table
restriction `log₂ U ≤ c · log₂ n`.

## Architecture

1. **Deterministic branch-wise transcript (`simResult`, `simTranscript`):**
   Because runs are maintained in canonical sorted order, on each fixed random seed
   `p : FilterSeed w₀ n` the active slot configuration depends only on the current active set
   `S : Finset (Fin U)`. Every query on seed `p` deterministically returns
   `decide (remHash U w₀ k p.2 u ∈ bucketRun S (quotHash U w₀ n p.1) (remHash U w₀ k p.2) _)`.
   Hence zero false negatives hold on every random branch, and the false-positive event at query
   index `idx` is bounded by `(1 / 2 : ℝ≥0∞) ^ k ≤ ε`.
2. **Expected `O(1)` time per operation (`charge = opStepBound 290`):**
   Evaluating the two-stage quotient hash and the independent remainder hash takes at most
   `236841 + 45 = 236886` instructions, and the `Memory.Prog` cluster operation lowered via the
   `realize` tactic (`realizes_clusterOp.code`) executes in at most
   `19 + clusterFactor * (11 * ℓ + 14)` instructions for a cluster of length `ℓ`. By
   `tsum_seedClusterBound_le` (`𝔼[ℓ] ≤ 290`), the expected instruction count of every operation is
   at most `charge = opStepBound 290`.
3. **Compact space (`space_le`, `implOfEps_space_le`):**
   The single contiguous memory block of `space w w₀ n k` words stores the two-stage quotient seed,
   the `o(n)`-bit Four-Russians carryless multiplication table, the remainder seed, and the four
   bit-packed slot arrays (`isFull`, `isOcc`, `isRunStart`, `remAt`), totaling at most
   `640 * ((n * k + w - 1) / w + 1)` words.

## Main definitions

* `Cslib.DataStructure.ApproximateMembership.QuotientFilter.subroutineCode`:
  Word-RAM `SubroutineCode .exact rQF 0` for the quotient filter.
* `Cslib.DataStructure.ApproximateMembership.QuotientFilter.impl`,
  `Cslib.DataStructure.ApproximateMembership.QuotientFilter.implStandard`:
  `ObliviousSequenceImpl` certificates realizing `spec U n ((1 / 2 : ℝ≥0∞) ^ k)`.
* `Cslib.DataStructure.ApproximateMembership.QuotientFilter.implOfEps`,
  `Cslib.DataStructure.ApproximateMembership.QuotientFilter.implOfEpsStandard`:
  `ObliviousSequenceImpl` certificates realizing `spec U n ε` for any `ε ≠ 0` using
  `k = epsLog ε = max 1 ⌈log₂(1 / ε)⌉`.

## Main results

* `Cslib.DataStructure.ApproximateMembership.QuotientFilter.quotBits_lt_w_of_fits_space`:
  `quotBits w₀ n < w` holds automatically whenever `0 < w₀`, `2 * w₀ ≤ w`, and
  `Fits w (base + space w w₀ n k)`.
* `Cslib.DataStructure.ApproximateMembership.QuotientFilter.contract_map_simTranscript`:
  `simTranscript` under `filterSeedLaw w₀ n` satisfies `spec U n ((1 / 2 : ℝ≥0∞) ^ k).Contract ops`.
* `Cslib.DataStructure.ApproximateMembership.QuotientFilter.opCode_execWithin`:
  single-operation deterministic execution and invariant preservation on each seed `p`.
* `Cslib.DataStructure.ApproximateMembership.QuotientFilter.implOfEps_space_le`:
  word-space bound `≤ 640 * ((n * epsLog ε + w - 1) / w + 1)`.

## References

* [A. Pagh, R. Pagh and S. S. Rao, *An optimal Bloom filter replacement*][PaghPaghRao2005]
* [M. A. Bender, M. Farach-Colton, R. Johnson, R. Kraner, B. C. Kuszmaul, D. Medjedovic, P. Montes,
  P. Shetty, R. P. Spillane and E. Zadok, *Don't thrash: how to cache your hash on
  flash*][BenderEtAl2012]
-/

public section

namespace Cslib.DataStructure.ApproximateMembership.QuotientFilter

open Cslib.WordRAM Cslib.DataStructure.WordRAM.Randomized Cslib.Probability
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.Dictionary.WordRAM.LinearProbing
open scoped ENNReal BigOperators Finset

/-! ## Section 1: Derived word-width bounds and representation invariant `Rep` -/

/-- Whenever `0 < w₀`, `2 * w₀ ≤ w`, and `Fits w (base + space w w₀ n k)`, the Four-Russians double
limb width `2 * reducedChunkBits` is strictly less than `w`. -/
theorem two_mul_reducedChunkBits_lt_of_fits_space {base w w₀ n k : ℕ}
    (hw₀ : 0 < w₀) (hw : 2 * w₀ ≤ w)
    (hfit : Fits w (base + space w w₀ n k)) :
    2 * reducedChunkBits (reducedTrinomialStep w₀ (quotBits w₀ n) (quotBits w₀ n)) < w := by
  have hb_lt := quotBits_lt_w_of_fits_space hw₀ hw hfit
  have hc_le :=
    two_mul_reducedChunkBits_le (b := quotBits w₀ n) (by omega : w₀ ≤ w) hb_lt.le (by omega)
  have hfit_kwise : Fits w (base + ReducedKWise.space w w₀ (quotBits w₀ n) (quotBits w₀ n) 5) :=
    hfit.of_le (by dsimp only [space]; omega)
  exact ReducedKWise.two_mul_reducedChunkBits_lt_of_fits_space hc_le hfit_kwise

/-- `ReducedKWise.TableRep` depends only on memory below `base + ReducedKWise.space`. -/
theorem tableRep_congr {base w w₀ b b' k : ℕ} {mem₁ mem₂ : ℕ → ℕ}
    (h : ∀ a < base + ReducedKWise.space w w₀ b b' k, mem₁ a = mem₂ a) :
    ReducedKWise.TableRep base w w₀ b b' k mem₁ ↔
      ReducedKWise.TableRep base w w₀ b b' k mem₂ := by
  dsimp only [ReducedKWise.TableRep]
  let t := reducedTrinomialStep w₀ b b'
  let c := reducedChunkBits t
  let p := reducedPackShift t w
  let tBase := ReducedKWise.tabBase base w₀ b b' k
  refine and_congr (forall₂_congr fun wIdx hwIdx => ?_) (forall₂_congr fun idx hidx => ?_)
  · rw [h (tBase + wIdx) (by
      dsimp only [tBase, ReducedKWise.tabBase, ReducedKWise.space]
      omega)]
  · have hwIdx : idx >>> p < ReducedKWise.tableWords w w₀ b b' :=
      shiftRight_lt_reducedTableWords hidx
    rw [h (tBase + (idx >>> p)) (by
      dsimp only [tBase, ReducedKWise.tabBase, ReducedKWise.space]
      omega)]

/-- `ReducedKWise.SeedRep` depends only on memory below `base + ReducedKWise.space`. -/
theorem seedRep_congr {base w w₀ b b' k : ℕ} (θ : ReducedPolySeed w₀ b b' k)
    {mem₁ mem₂ : ℕ → ℕ}
    (h : ∀ a < base + ReducedKWise.space w w₀ b b' k, mem₁ a = mem₂ a) :
    ReducedKWise.SeedRep base w₀ b b' k θ mem₁ ↔
      ReducedKWise.SeedRep base w₀ b b' k θ mem₂ := by
  dsimp only [ReducedKWise.SeedRep]
  let L := reducedLimbCount (reducedTrinomialStep w₀ b b')
  have h0 : base < base + ReducedKWise.space w w₀ b b' k := by
    dsimp only [ReducedKWise.space, ReducedKWise.seedWords]
    omega
  refine and_congr (by rw [h base h0]) (forall₂_congr fun j m => ?_)
  have hidx : m.val + L * j.val < k * L := by
    calc m.val + L * j.val < L + L * j.val := Nat.add_lt_add_right m.isLt _
      _ = (j.val + 1) * L := by ring
      _ ≤ k * L := Nat.mul_le_mul_right L j.isLt
  rw [h (base + 1 + (m.val + L * j.val)) (by
    dsimp only [ReducedKWise.space, ReducedKWise.seedWords, L] at hidx ⊢
    omega)]

/-- Seed-coupled Word-RAM representation invariant linking seed `p : FilterSeed w₀ n`, active key
set `S : Finset (Fin U)`, and machine state `x : Data rQF`. -/
@[expose] def Rep (U w base w₀ n k : ℕ) (p : FilterSeed w₀ n) (S : Finset (Fin U))
    (x : Data rQF) : Prop :=
  x.Bounded w ∧
  x.regs (qfReg 0) = base ∧
  x.regs (qfReg 240) = base + space w w₀ n k ∧
  ReducedKWise.TableRep base w w₀ (quotBits w₀ n) (quotBits w₀ n) 5 x.mem ∧
  ReducedKWise.SeedRep base w₀ (quotBits w₀ n) (quotBits w₀ n) 5 p.1 x.mem ∧
  x.mem (remSeedAddr base w w₀ n) = p.2.val ∧
  FilterInv n S (quotHash U w₀ n p.1) (remHash U w₀ k p.2)
    (extractFilterState base w w₀ n k x.mem)

/-! ## Section 2: Deterministic branch-wise transcript (`simResult`, `simTranscript`) -/

/-- Deterministic branch-wise result of operation `o : Op U` on seed `p : FilterSeed w₀ n` from
active key set `S : Finset (Fin U)`. -/
@[expose] noncomputable def simResult (U w₀ n k : ℕ) (p : FilterSeed w₀ n)
    (S : Finset (Fin U)) : (o : Op U) → Result o
  | .insert _ => PUnit.unit
  | .delete _ => PUnit.unit
  | .query u =>
      decide (remHash U w₀ k p.2 u ∈
        bucketRun S (quotHash U w₀ n p.1) (remHash U w₀ k p.2) (quotHash U w₀ n p.1 u))

/-- Deterministic branch-wise transcript produced across `ops : List (Op U)` on seed
`p : FilterSeed w₀ n` starting from active key set `S : Finset (Fin U)`. -/
@[expose] noncomputable def simTranscript (U w₀ n k : ℕ) (p : FilterSeed w₀ n) :
    Finset (Fin U) → List (Op U) → List (Label U)
  | _, [] => []
  | S, o :: rest =>
      ⟨o, simResult U w₀ n k p S o⟩ :: simTranscript U w₀ n k p (stepSet S o) rest

@[simp]
theorem simTranscript_nil (U w₀ n k : ℕ) (p : FilterSeed w₀ n) (S : Finset (Fin U)) :
    simTranscript U w₀ n k p S [] = [] := rfl

@[simp]
theorem simTranscript_cons (U w₀ n k : ℕ) (p : FilterSeed w₀ n) (S : Finset (Fin U))
    (o : Op U) (rest : List (Op U)) :
    simTranscript U w₀ n k p S (o :: rest) =
      ⟨o, simResult U w₀ n k p S o⟩ :: simTranscript U w₀ n k p (stepSet S o) rest := rfl

theorem simTranscript_append (U w₀ n k : ℕ) (p : FilterSeed w₀ n)
    (S : Finset (Fin U)) (ops₁ ops₂ : List (Op U)) :
    simTranscript U w₀ n k p S (ops₁ ++ ops₂) =
      simTranscript U w₀ n k p S ops₁ ++
        simTranscript U w₀ n k p (activeSetFrom S ops₁) ops₂ := by
  induction ops₁ generalizing S with
  | nil => simp
  | cons o rest ih =>
    simp only [List.cons_append, simTranscript_cons, activeSetFrom_cons, ih (stepSet S o)]

theorem transcriptMatches_simTranscript (U w₀ n k : ℕ) (p : FilterSeed w₀ n)
    (S : Finset (Fin U)) (ops : List (Op U)) :
    TranscriptMatches ops (simTranscript U w₀ n k p S ops) := by
  induction ops generalizing S with
  | nil => rfl
  | cons o rest ih =>
    simp only [simTranscript_cons, Cslib.DataStructure.transcriptMatches_cons]
    exact ih (stepSet S o)

theorem getElem?_simTranscript (U w₀ n k : ℕ) (p : FilterSeed w₀ n)
    (S : Finset (Fin U)) (ops : List (Op U)) (idx : ℕ) :
    (simTranscript U w₀ n k p S ops)[idx]? =
      ops[idx]?.map fun o =>
        ⟨o, simResult U w₀ n k p (activeSetFrom S (ops.take idx)) o⟩ := by
  induction ops generalizing S idx with
  | nil => simp
  | cons o rest ih =>
    cases idx with
    | zero => simp
    | succ idx =>
      simp only [simTranscript_cons, List.getElem?_cons_succ, List.take_succ_cons,
        activeSetFrom_cons, ih (stepSet S o) idx]

theorem noFalseNegatives_simTranscript (U w₀ n k : ℕ) (p : FilterSeed w₀ n)
    (ops : List (Op U)) :
    NoFalseNegatives ops (simTranscript U w₀ n k p ∅ ops) := by
  intro idx _ u hq hu
  rw [getElem?_simTranscript, hq]
  dsimp only [Option.map]
  rw [Option.some.injEq, Sigma.mk.injEq, and_iff_right rfl, heq_eq_eq]
  change decide (remHash U w₀ k p.2 u ∈
    bucketRun (activeSetBefore ops idx) (quotHash U w₀ n p.1) (remHash U w₀ k p.2)
      (quotHash U w₀ n p.1 u)) = true
  rw [decide_eq_true_eq]
  exact (mem_bucketRun_iff _ _ _ _ _).mpr ⟨u, hu, rfl, rfl⟩

theorem falsePositiveAt_simTranscript_iff (U w₀ n k : ℕ) (p : FilterSeed w₀ n)
    (ops : List (Op U)) {idx : ℕ} {u : Fin U}
    (hq : ops[idx]? = some (.query u)) :
    FalsePositiveAt (simTranscript U w₀ n k p ∅ ops) idx u ↔
      ∃ x ∈ activeSetBefore ops idx,
        quotHash U w₀ n p.1 x = quotHash U w₀ n p.1 u ∧
        remHash U w₀ k p.2 x = remHash U w₀ k p.2 u := by
  dsimp only [FalsePositiveAt]
  rw [getElem?_simTranscript, hq]
  dsimp only [Option.map]
  rw [Option.some.injEq, Sigma.mk.injEq, and_iff_right rfl, heq_eq_eq]
  change decide (remHash U w₀ k p.2 u ∈
    bucketRun (activeSetBefore ops idx) (quotHash U w₀ n p.1) (remHash U w₀ k p.2)
      (quotHash U w₀ n p.1 u)) = true ↔ _
  rw [decide_eq_true_eq]
  exact mem_bucketRun_iff _ _ _ _ _

/-- The transcript distribution induced by `simTranscript` under `filterSeedLaw w₀ n` satisfies
`(spec U n ((1 / 2 : ℝ≥0∞) ^ k)).Contract ops`. -/
theorem contract_map_simTranscript {U w₀ n k : ℕ} (hw₀ : 0 < w₀) (hU : U ≤ 2 ^ w₀)
    {ops : List (Op U)} (hv : ValidOpSeq n ops) :
    (spec U n ((1 / 2 : ℝ≥0∞) ^ k)).Contract ops
      ((filterSeedLaw w₀ n).map fun p => simTranscript U w₀ n k p ∅ ops) := by
  refine ⟨?_, ?_⟩
  · intro tr htr
    change tr ∈ ((filterSeedLaw w₀ n).map fun p => simTranscript U w₀ n k p ∅ ops).support at htr
    rw [PMF.mem_support_map_iff] at htr
    obtain ⟨p, _, rfl⟩ := htr
    exact ⟨transcriptMatches_simTranscript U w₀ n k p ∅ ops,
      noFalseNegatives_simTranscript U w₀ n k p ops⟩
  · intro idx _ u hq hnotMem
    change ((filterSeedLaw w₀ n).map fun p => simTranscript U w₀ n k p ∅ ops).toOuterMeasure
      {tr | FalsePositiveAt tr idx u} ≤ (1 / 2 : ℝ≥0∞) ^ k
    rw [PMF.toOuterMeasure_map_apply]
    have hpre :
        (fun p : FilterSeed w₀ n => simTranscript U w₀ n k p ∅ ops) ⁻¹'
          {tr | FalsePositiveAt tr idx u} =
        {p : FilterSeed w₀ n |
          ∃ x ∈ activeSetBefore ops idx,
            quotHash U w₀ n p.1 x = quotHash U w₀ n p.1 u ∧
            remHash U w₀ k p.2 x = remHash U w₀ k p.2 u} := by
      ext p
      exact falsePositiveAt_simTranscript_iff U w₀ n k p ops hq
    rw [hpre]
    exact toOuterMeasure_falsePositive_le hw₀ hU (card_activeSetBefore_le hv idx) hnotMem

/-! ## Section 3: Initialization (`allocSpan`, `initSetup`, `initSetup_exec`) -/

/-- Allocate `[base, base + space w w₀ n k)` by setting `qfReg 0 ← qfReg 240` and advancing
`qfReg 240 ← qfReg 0 + space w w₀ n k` in `3` instructions. -/
@[expose] noncomputable def allocSpan (w w₀ n k : ℕ) : Code .exact rQF :=
  .seq (.op (.copy (qfReg 0) (qfReg 240)))
  (.seq (.op (.const (qfReg 30) (space w w₀ n k)))
        (.op (.exactBin .add (qfReg 240) (qfReg 0) (qfReg 30))))

theorem allocSpan_execWithin {base w w₀ n k : ℕ}
    (hfit_space : Fits w (base + space w w₀ n k))
    {x : Data rQF} (hfr : x.regs (qfReg 240) = base) :
    ∃ x₁ : Data rQF,
      ExecWithin w (allocSpan w w₀ n k) x x₁ 3 ∧
      x₁.mem = x.mem ∧
      x₁.regs (qfReg 0) = base ∧
      x₁.regs (qfReg 240) = base + space w w₀ n k := by
  have hfit_sp : Fits w (space w w₀ n k) := hfit_space.of_le (Nat.le_add_left _ _)
  set s1 := x.set (qfReg 0) (x.regs (qfReg 240))
  have e1 : Exec w (.op (.copy (qfReg 0) (qfReg 240)) : Code .exact rQF) x s1 1 := Exec.copy
  set s2 := s1.set (qfReg 30) (space w w₀ n k)
  have e2 : Exec w (.op (.const (qfReg 30) (space w w₀ n k)) : Code .exact rQF) s1 s2 1 :=
    Exec.const hfit_sp
  set s3 := s2.set (qfReg 240) (base + space w w₀ n k)
  have e3 : Exec w (.op (.exactBin .add (qfReg 240) (qfReg 0) (qfReg 30)) : Code .exact rQF)
      s2 s3 1 := by
    have hs2_0 : s2.regs (qfReg 0) = base := by simp +decide [s2, s1, hfr]
    have hs2_30 : s2.regs (qfReg 30) = space w w₀ n k := by simp +decide [s2]
    apply Exec.op
    rw [Op.eval_exactBin, hs2_0, hs2_30]
    exact Data.put_of_fits hfit_space
  exact ⟨s3, (e1.seq (e2.seq e3)).within, rfl, by simp +decide [s3, s2, s1, hfr],
    by simp +decide [s3]⟩

/-- Initialize the Four-Russians carryless multiplication table, sample the two-stage quotient seed,
and sample the multiply-shift remainder seed. -/
@[expose] noncomputable def initSetup (w w₀ n : ℕ) : Code .exact rQF :=
  let b := quotBits w₀ n
  .seq ((ReducedKWise.initTableCode w w₀ b b 5).rename kwiseMap)
  (.seq ((ReducedKWise.resampleCode w₀ b b 5).rename kwiseMap)
        (remInitCode w w₀ n))

/-- Exact instruction count of `initSetup w w₀ n`. -/
@[expose] def setupSteps (w₀ n : ℕ) : ℕ :=
  let b := quotBits w₀ n
  ReducedKWise.initTableSteps w₀ b b + (ReducedKWise.resampleSteps w₀ b b 5 + 5)

/-- Combined `ProbComp` semantics for sampling the quotient seed and the remainder seed. -/
@[expose] noncomputable def sampleSeedsComp (base w w₀ n : ℕ) (x₂ : Data rQF) :
    ProbComp (Data rQF × ℕ) := do
  let b := quotBits w₀ n
  let z1 ← ReducedKWise.resampleComp base w₀ b b 5 (x₂.comap kwiseMap)
  let x₃ := z1.1.extend kwiseMap x₂
  let z2 ← remInitComp base w w₀ n x₃
  pure (z2.1, z1.2 + z2.2)

theorem extractSeed_remInitData (base w w₀ n : ℕ) (x : Data rQF) (γ : ℕ) :
    ReducedKWise.extractSeed base w₀ (quotBits w₀ n) (quotBits w₀ n) 5
      (remInitData base w w₀ n x γ).mem =
    ReducedKWise.extractSeed base w₀ (quotBits w₀ n) (quotBits w₀ n) 5 x.mem := by
  let b := quotBits w₀ n
  let t := reducedTrinomialStep w₀ b b
  let c := reducedChunkBits t
  let L := reducedLimbCount t
  have htop : ReducedKWise.extractTop base w₀ (remInitData base w w₀ n x γ).mem =
      ReducedKWise.extractTop base w₀ x.mem := by
    dsimp only [ReducedKWise.extractTop]
    congr 1
    funext idx
    dsimp only [Tabulation.extractSlice, remInitData, Data.write, Data.set]
    have hne : base + idx.val ≠ remSeedAddr base w w₀ n := by
      have := idx.isLt
      dsimp only [remSeedAddr, ReducedKWise.space, ReducedKWise.seedWords]
      omega
    rw [Function.update_of_ne hne]
  have hbot : ReducedKWise.extractBot base w₀ b b 5 (remInitData base w w₀ n x γ).mem =
      ReducedKWise.extractBot base w₀ b b 5 x.mem := by
    dsimp only [ReducedKWise.extractBot]
    congr 1
    funext idx
    dsimp only [Tabulation.extractSlice, remInitData, Data.write, Data.set]
    have hne : base + 1 + idx.val ≠ remSeedAddr base w w₀ n := by
      have hlt := idx.isLt
      dsimp only [remSeedAddr, ReducedKWise.space, ReducedKWise.seedWords, L, t, b] at hlt ⊢
      omega
    rw [Function.update_of_ne hne]
  exact Prod.ext htop hbot

theorem map_extractFilterSeed_eval_sampleSeedsComp (base w w₀ n : ℕ) (x₂ : Data rQF) :
    ((sampleSeedsComp base w w₀ n x₂).eval).map
      (fun z => extractFilterSeed base w w₀ n z.1.mem) =
      filterSeedLaw w₀ n := by
  set b := quotBits w₀ n
  set m1 := ReducedKWise.resampleComp base w₀ b b 5 (x₂.comap kwiseMap)
  have hm1 : m1.eval.map (fun z1 => ReducedKWise.extractSeed base w₀ b b 5 z1.1.mem) =
      PMF.uniformOfFintype (QuotSeed w₀ n) :=
    ReducedKWise.map_extractSeed_eval_resampleComp base w₀ b b 5 (x₂.comap kwiseMap)
  have hinner : ∀ z1 : Data 240 × ℕ,
      (let x₃ := z1.1.extend kwiseMap x₂
       (do
         let z2 ← remInitComp base w w₀ n x₃
         pure (z2.1, z1.2 + z2.2)).eval).map
        (fun z : Data rQF × ℕ => extractFilterSeed base w w₀ n z.1.mem) =
      (PMF.uniformOfFintype (RemSeed w₀)).map
        (fun γ => (ReducedKWise.extractSeed base w₀ b b 5 z1.1.mem, γ)) := by
    intro z1
    dsimp only
    set x₃ := z1.1.extend kwiseMap x₂
    have hd : (do
        let z2 ← remInitComp base w w₀ n x₃
        pure (z2.1, z1.2 + z2.2)) =
        (fun z2 : Data rQF × ℕ => (z2.1, z1.2 + z2.2)) <$> remInitComp base w w₀ n x₃ :=
      bind_pure_comp _ _
    rw [hd, ProbComp.eval_map, PMF.map_comp]
    have hcongr :
        (remInitComp base w w₀ n x₃).eval.map
          ((fun z : Data rQF × ℕ => extractFilterSeed base w w₀ n z.1.mem) ∘
            fun z2 : Data rQF × ℕ => (z2.1, z1.2 + z2.2)) =
        (remInitComp base w w₀ n x₃).eval.map
          ((fun γ => (ReducedKWise.extractSeed base w₀ b b 5 z1.1.mem, γ)) ∘
            fun z2 : Data rQF × ℕ => extractRemSeed base w w₀ n z2.1.mem) := by
      refine Cslib.Probability.PMF.map_congr_on_support _ _ _ fun z2 hz2 => ?_
      rw [ProbComp.support_eval] at hz2
      dsimp only [remInitComp] at hz2
      obtain ⟨γ, -, hpure⟩ := OracleComp.mem_supportWith_bind_iff.mp hz2
      cases OracleComp.eq_of_mem_supportWith_pure hpure
      dsimp only [Function.comp_apply, extractFilterSeed]
      rw [extractSeed_remInitData]
      rfl
    rw [hcongr, ← PMF.map_comp, map_extractRemSeed_eval_remInitComp]
  dsimp only [sampleSeedsComp]
  rw [ProbComp.eval_bind, PMF.map_bind]
  have hbind :
      m1.eval.bind
        (fun z1 =>
          (let x₃ := z1.1.extend kwiseMap x₂
           (do
             let z2 ← remInitComp base w w₀ n x₃
             pure (z2.1, z1.2 + z2.2)).eval).map
            (fun z : Data rQF × ℕ => extractFilterSeed base w w₀ n z.1.mem)) =
      m1.eval.bind
        (fun z1 =>
          (PMF.uniformOfFintype (RemSeed w₀)).map
            (fun γ => (ReducedKWise.extractSeed base w₀ b b 5 z1.1.mem, γ))) := by
    congr 1
    funext z1
    exact hinner z1
  rw [hbind]
  have hmap_bind :
      m1.eval.bind
        (fun z1 =>
          (PMF.uniformOfFintype (RemSeed w₀)).map
            (fun γ => (ReducedKWise.extractSeed base w₀ b b 5 z1.1.mem, γ))) =
      (m1.eval.map (fun z1 => ReducedKWise.extractSeed base w₀ b b 5 z1.1.mem)).bind
        (fun θ => (PMF.uniformOfFintype (RemSeed w₀)).map (θ, ·)) := by
    rw [PMF.bind_map]
    rfl
  rw [hmap_bind, hm1, filterSeedLaw, PMF.uniformOfFintype_prod]

theorem initSetup_exec {U base w w₀ n k : ℕ}
    (hw₀_pos : 0 < w₀) (hw : 2 * w₀ ≤ w)
    (hfit_space : Fits w (base + space w w₀ n k))
    {x₁ : Data rQF}
    (hx₁ : x₁.Bounded w) (hb : x₁.regs (qfReg 0) = base)
    (hfr : x₁.regs (qfReg 240) = base + space w w₀ n k)
    (hzero : ∀ a ∈ (Block.mk base (space w w₀ n k)).footprint, x₁.mem a = 0) :
    ∃ ν₀ : PMF (LatentState (FilterSeed w₀ n) rQF),
      ExecCodeDist w (initSetup w w₀ n) x₁ (ν₀.map LatentState.data) (setupSteps w₀ n) ∧
      (ν₀.map LatentState.latent = filterSeedLaw w₀ n ∧
        ∀ t ∈ ν₀.support, Rep U w base w₀ n k t.latent ∅ t.data) ∧
      ∀ t ∈ ν₀.support,
        t.data.Bounded w ∧
        t.data.regs (qfReg 240) = base + space w w₀ n k ∧
        Modifies (Block.mk base (space w w₀ n k)).footprint x₁.mem t.data.mem := by
  let b := quotBits w₀ n
  have hw₀_le : w₀ ≤ w := by omega
  have hc_lt := two_mul_reducedChunkBits_lt_of_fits_space hw₀_pos hw hfit_space
  have hfit_kwise : Fits w (base + ReducedKWise.space w w₀ b b 5) :=
    hfit_space.of_le (by dsimp only [space, b]; omega)
  obtain ⟨y_tab, he_tab_inner, hy_tab_0, htab, hframe_tab⟩ :=
    ReducedKWise.initTableCode_exec (k := 5) (x := x₁.comap kwiseMap)
      hb hc_lt.le hfit_kwise
  have he_tab := he_tab_inner.rename injective_kwiseMap
  set x₂ := y_tab.extend kwiseMap x₁
  have hx₂_bdd : x₂.Bounded w := he_tab.within.bounded hx₁
  have hx₂_0 : (x₂.comap kwiseMap).regs 0 = base := by
    rw [Data.comap_extend injective_kwiseMap]
    exact hy_tab_0
  have hx₂_fr : x₂.regs (qfReg 240) = base + space w w₀ n k := by
    rw [extend_kwiseMap_regs (by decide : 240 ≤ (qfReg 240).val)]
    exact hfr
  have he_res_inner := ReducedKWise.resampleCode_execRand (base := base) (w := w)
    (w₀ := w₀) (b := b) (b' := b) (k := 5) (x := x₂.comap kwiseMap)
    hx₂_0 hw₀_le hc_lt.le hfit_kwise
  have he_res := he_res_inner.rename injective_kwiseMap
  have he_seeds : ExecRand w
      (.seq ((ReducedKWise.resampleCode w₀ b b 5).rename kwiseMap) (remInitCode w w₀ n))
      x₂ (sampleSeedsComp base w w₀ n x₂) := by
    have hseq := ExecRand.seq
      (m₂ := fun x₃ : Data rQF => remInitComp base w w₀ n x₃)
      he_res (fun x₃ hx₃ => by
        obtain ⟨z1, hz1, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hx₃
        obtain ⟨hz1_0, _, _, _, _⟩ :=
          ReducedKWise.mem_support_resampleComp (x := x₂.comap kwiseMap) hx₂_0 htab hz1
        have hx₃_0 : (z1.1.extend kwiseMap x₂).regs (qfReg 0) = base := by
          change ((z1.1.extend kwiseMap x₂).comap kwiseMap).regs 0 = base
          rw [Data.comap_extend injective_kwiseMap]
          exact hz1_0
        exact remInitCode_execRand hw₀_le hfit_space hx₃_0)
    simpa only [sampleSeedsComp, bind_assoc, pure_bind, map_eq_bind_pure_comp,
      Function.comp_def] using hseq
  have hsupp_seeds : ∀ z ∈ (sampleSeedsComp base w w₀ n x₂).support,
      z.1.Bounded w ∧
      z.1.regs (qfReg 240) = base + space w w₀ n k ∧
      Rep U w base w₀ n k (extractFilterSeed base w w₀ n z.1.mem) ∅ z.1 ∧
      Modifies (Block.mk base (space w w₀ n k)).footprint x₁.mem z.1.mem ∧
      z.2 ≤ ReducedKWise.resampleSteps w₀ b b 5 + 5 := by
    intro z hz
    have hbdd_z : z.1.Bounded w := he_seeds.bounded hx₂_bdd hz
    dsimp only [sampleSeedsComp] at hz
    obtain ⟨z1, hz1, hrest⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
    obtain ⟨z2, hz2, hpure⟩ := OracleComp.mem_supportWith_bind_iff.mp hrest
    cases OracleComp.eq_of_mem_supportWith_pure hpure
    obtain ⟨hz1_0, htab1, hseed1, hframe1, hsteps1⟩ :=
      ReducedKWise.mem_support_resampleComp (x := x₂.comap kwiseMap) hx₂_0 htab hz1
    set x₃ := z1.1.extend kwiseMap x₂
    dsimp only [remInitComp] at hz2
    obtain ⟨γ, -, hpure2⟩ := OracleComp.mem_supportWith_bind_iff.mp hz2
    cases OracleComp.eq_of_mem_supportWith_pure hpure2
    set y := remInitData base w w₀ n x₃ γ.val
    have hy_0 : y.regs (qfReg 0) = base := by
      dsimp only [y, remInitData, Data.write, Data.set]
      rw [Function.update_of_ne (by decide : qfReg 0 ≠ qfReg 32),
        Function.update_of_ne (by decide : qfReg 0 ≠ qfReg 31),
        Function.update_of_ne (by decide : qfReg 0 ≠ qfReg 30),
        Function.update_of_ne (by decide : qfReg 0 ≠ qfReg 30)]
      change (x₃.comap kwiseMap).regs 0 = base
      rw [Data.comap_extend injective_kwiseMap]
      exact hz1_0
    have hy_fr : y.regs (qfReg 240) = base + space w w₀ n k := by
      dsimp only [y, remInitData, Data.write, Data.set]
      rw [Function.update_of_ne (by decide : qfReg 240 ≠ qfReg 32),
        Function.update_of_ne (by decide : qfReg 240 ≠ qfReg 31),
        Function.update_of_ne (by decide : qfReg 240 ≠ qfReg 30),
        Function.update_of_ne (by decide : qfReg 240 ≠ qfReg 30)]
      rw [extend_kwiseMap_regs (by decide : 240 ≤ (qfReg 240).val)]
      exact hx₂_fr
    have hmem_below : ∀ a < base + ReducedKWise.space w w₀ b b 5, y.mem a = z1.1.mem a := by
      intro a ha
      dsimp only [y, remInitData, Data.write, Data.set]
      have hne : a ≠ remSeedAddr base w w₀ n := by
        dsimp only [remSeedAddr, b] at ha ⊢
        omega
      rw [Function.update_of_ne hne]
      rfl
    have htab_y : ReducedKWise.TableRep base w w₀ b b 5 y.mem :=
      (tableRep_congr hmem_below).mpr htab1
    have hseed_eq : ReducedKWise.extractSeed base w₀ b b 5 y.mem =
        ReducedKWise.extractSeed base w₀ b b 5 z1.1.mem :=
      extractSeed_remInitData base w w₀ n x₃ γ.val
    have hseed_y : ReducedKWise.SeedRep base w₀ b b 5
        (ReducedKWise.extractSeed base w₀ b b 5 y.mem) y.mem := by
      rw [hseed_eq]
      exact (seedRep_congr _ hmem_below).mpr hseed1
    have hγ_lt : γ.val < 2 ^ (w₀ - 1) := by
      have := Nat.one_le_two_pow (n := w₀ - 1)
      have := γ.isLt
      omega
    have hrem_y : y.mem (remSeedAddr base w w₀ n) =
        (extractRemSeed base w w₀ n y.mem).val := by
      dsimp only [extractRemSeed, y, remInitData, Data.write, Data.set, Tabulation.extractWord]
      simp [hγ_lt]
    have hzero_slots : ∀ a, fullBase base w w₀ n ≤ a → a < base + space w w₀ n k →
        y.mem a = 0 := by
      intro a hle hlt
      dsimp only [y, remInitData, Data.write, Data.set]
      have hne : a ≠ remSeedAddr base w w₀ n := by dsimp only [fullBase] at hle; omega
      rw [Function.update_of_ne hne]
      change z1.1.mem a = 0
      have ha1 : a < base ∨ base + ReducedKWise.seedWords w₀ b b 5 ≤ a := by
        dsimp only [fullBase, remSeedAddr, ReducedKWise.space, b] at hle ⊢
        omega
      have ha2 : a < ReducedKWise.tabBase base w₀ b b 5 ∨
          base + ReducedKWise.space w w₀ b b 5 ≤ a := by
        dsimp only [fullBase, remSeedAddr, b] at hle ⊢
        omega
      rw [hframe1 a ha1]
      change y_tab.mem a = 0
      rw [hframe_tab a ha2]
      exact hzero a (Block.mem_footprint.mpr
        ⟨by dsimp only [fullBase, remSeedAddr, Block.Owns] at hle ⊢; omega, hlt⟩)
    have hst_empty : extractFilterState base w w₀ n k y.mem =
        FilterState.empty (quotBits w₀ n) (remBits w₀ k) :=
      extractFilterState_of_zero hzero_slots
    have hinv_y : FilterInv n (∅ : Finset (Fin U))
        (quotHash U w₀ n (extractFilterSeed base w w₀ n y.mem).1)
        (remHash U w₀ k (extractFilterSeed base w w₀ n y.mem).2)
        (extractFilterState base w w₀ n k y.mem) := by
      rw [hst_empty]
      exact filterInv_empty n _ _
    have hmod_y : Modifies (Block.mk base (space w w₀ n k)).footprint x₁.mem y.mem := by
      intro a ha
      rw [Block.mem_footprint, Block.Owns, not_and_or, not_le, not_lt] at ha
      dsimp only [y, remInitData, Data.write, Data.set]
      have hne : a ≠ remSeedAddr base w w₀ n := by
        rcases ha with hlt | hge
        · dsimp only [remSeedAddr] at hlt ⊢; omega
        · dsimp only [remSeedAddr, space] at hge ⊢; omega
      rw [Function.update_of_ne hne]
      change z1.1.mem a = x₁.mem a
      have ha1 : a < base ∨ base + ReducedKWise.seedWords w₀ b b 5 ≤ a := by
        rcases ha with hlt | hge
        · exact Or.inl hlt
        · exact Or.inr (by dsimp only [space, ReducedKWise.space, b] at hge ⊢; omega)
      have ha2 : a < ReducedKWise.tabBase base w₀ b b 5 ∨
          base + ReducedKWise.space w w₀ b b 5 ≤ a := by
        rcases ha with hlt | hge
        · exact Or.inl (by dsimp only [ReducedKWise.tabBase] at hlt ⊢; omega)
        · exact Or.inr (by dsimp only [space, b] at hge ⊢; omega)
      rw [hframe1 a ha1]
      change y_tab.mem a = x₁.mem a
      exact hframe_tab a ha2
    refine ⟨hbdd_z, hy_fr, ⟨hbdd_z, hy_0, hy_fr, htab_y, hseed_y, hrem_y, hinv_y⟩, hmod_y, ?_⟩
    rw [hsteps1]
  let liftOut (z : Data rQF × ℕ) : LatentState (FilterSeed w₀ n) rQF :=
    ⟨extractFilterSeed base w w₀ n z.1.mem, z.1⟩
  let ν₀ : PMF (LatentState (FilterSeed w₀ n) rQF) :=
    ((sampleSeedsComp base w w₀ n x₂).eval).map liftOut
  have he_dist2 : ExecCodeDist w
      (.seq ((ReducedKWise.resampleCode w₀ b b 5).rename kwiseMap) (remInitCode w w₀ n))
      x₂ (ν₀.map LatentState.data) ((ReducedKWise.resampleSteps w₀ b b 5 + 5 : ℕ) : ℝ≥0∞) := by
    refine (ExecCodeDist.of_execRand he_seeds).congr_dist ?_ ?_
    · dsimp only [ν₀]
      rw [ProbComp.eval_map, PMF.map_comp]
      rfl
    · calc ProbComp.expect (sampleSeedsComp base w w₀ n x₂) (fun z => (z.2 : ℝ≥0∞))
          ≤ ProbComp.expect (sampleSeedsComp base w w₀ n x₂)
              (fun _ => ((ReducedKWise.resampleSteps w₀ b b 5 + 5 : ℕ) : ℝ≥0∞)) :=
            ProbComp.expect_mono_on_support fun z hz => Nat.cast_le.mpr (hsupp_seeds z hz).2.2.2.2
        _ = ((ReducedKWise.resampleSteps w₀ b b 5 + 5 : ℕ) : ℝ≥0∞) :=
            ProbComp.expect_const _ _
  have he_setup : ExecCodeDist w (initSetup w w₀ n) x₁ (ν₀.map LatentState.data)
      (setupSteps w₀ n) := by
    dsimp only [initSetup, setupSteps]
    rw [Nat.cast_add]
    exact (ExecCodeDist.of_execWithin he_tab.within).seq_pure he_dist2
  have hlat : ν₀.map LatentState.latent = filterSeedLaw w₀ n := by
    dsimp only [ν₀]
    rw [PMF.map_comp]
    exact map_extractFilterSeed_eval_sampleSeedsComp base w w₀ n x₂
  refine ⟨ν₀, he_setup, ⟨hlat, ?_⟩, ?_⟩
  · intro t ht
    dsimp only [ν₀] at ht
    rw [PMF.mem_support_map_iff] at ht
    obtain ⟨z, hz, rfl⟩ := ht
    rw [ProbComp.support_eval] at hz
    exact (hsupp_seeds z hz).2.2.1
  · intro t ht
    dsimp only [ν₀] at ht
    rw [PMF.mem_support_map_iff] at ht
    obtain ⟨z, hz, rfl⟩ := ht
    rw [ProbComp.support_eval] at hz
    obtain ⟨hbdd_z, hfr_z, _, hmod_z, _⟩ := hsupp_seeds z hz
    exact ⟨hbdd_z, hfr_z, hmod_z⟩

/-! ## Section 4: Operation dispatcher `opCode` and single-step execution -/

/-- Underlying key `Fin U` of a filter operation `o : Op U`. -/
@[expose] def opKey {U : ℕ} : Op U → Fin U
  | .insert u => u
  | .delete u => u
  | .query u => u

/-- Numeric operation tag (`0 = insert`, `1 = delete`, `2 = query`). -/
@[expose] def opTag {U : ℕ} : Op U → ℕ
  | .insert _ => 0
  | .delete _ => 1
  | .query _ => 2

/-- Input-register mask (`qfReg 1` = key, `qfReg 247` = operation tag). -/
@[expose] noncomputable def inputReg : Fin rQF → Bool :=
  fun i => decide (i = qfReg 1 ∨ i = qfReg 247)

/-- Standalone register encoding for argument delivery. -/
@[expose] noncomputable def encode {U : ℕ} (o : Op U) (i : Fin rQF) : ℕ :=
  if i = qfReg 1 then (opKey o).val
  else if i = qfReg 247 then opTag o
  else 0

/-- Output decoder reading typed operation observations from final registers. -/
@[expose] noncomputable def decode {U : ℕ} : (o : Op U) → (Fin rQF → ℕ) → Option (Result o)
  | .insert _, _ => some PUnit.unit
  | .delete _, _ => some PUnit.unit
  | .query _, regs => some (decide (regs (qfReg 1) = 1))

/-- Unified Word-RAM operation body: evaluates the two-stage quotient hash into `qfReg 2` and the
remainder hash into `qfReg 3`, then runs the realized `clusterCode` (`clusterOpProg`). -/
@[expose] noncomputable def opCode (w w₀ n k : ℕ) : Code .exact rQF :=
  let b := quotBits w₀ n
  .seq (.op (.copy (qfReg 246) (qfReg 1)))
  (.seq ((ReducedKWise.evalCode w w₀ b b 5).rename kwiseMap)
  (.seq (.op (.copy (qfReg 1) (qfReg 246)))
  (.seq (.op (.copy (qfReg 245) (qfReg 2)))
  (.seq (remEvalCode w w₀ n k)
  (.seq (.op (.copy (qfReg 2) (qfReg 245)))
        (clusterCode w w₀ n k))))))

/-- Upper bound `clusterFactor * (11 * ℓ + 14) + 236909` on the instruction count of `opCode` when
the cluster around `quot u` has length `ℓ`. -/
@[expose] noncomputable def opStepBound (ℓ : ℕ) : ℕ :=
  clusterFactor * (11 * ℓ + 14) + 236909

/-- Per-operation expected instruction charge `opStepBound 290`. -/
@[expose] noncomputable def charge : ℕ :=
  opStepBound 290

theorem opCode_execWithin {U base w w₀ n k : ℕ}
    (hw₀_pos : 0 < w₀) (hw : 2 * w₀ ≤ w) (hU : U ≤ 2 ^ w₀)
    (hfit_space : Fits w (base + space w w₀ n k))
    {S : Finset (Fin U)} (hS : #S ≤ n)
    {p : FilterSeed w₀ n} {o : Op U} (ho : ValidOp n S o)
    {x : Data rQF}
    (hrep : Rep U w base w₀ n k p S x)
    (h1 : x.regs (qfReg 1) = (opKey o).val)
    (h247 : x.regs (qfReg 247) = opTag o) :
    ∃ y : Data rQF,
      ExecWithin w (opCode w w₀ n k) x y
        (opStepBound (seedClusterBound U w₀ n S (opKey o) p.1)) ∧
      Rep U w base w₀ n k p (stepSet S o) y ∧
      decode o y.regs = some (simResult U w₀ n k p S o) ∧
      Modifies (Block.mk base (space w w₀ n k)).footprint x.mem y.mem := by
  let b := quotBits w₀ n
  let u := opKey o
  obtain ⟨hx_bdd, hx_0, hx_fr, htab, hseed, hrem_seed, hinv⟩ := hrep
  have hw₀_le : w₀ ≤ w := by omega
  have hb_lt := quotBits_lt_w_of_fits_space hw₀_pos hw hfit_space
  have hc_lt := two_mul_reducedChunkBits_lt_of_fits_space hw₀_pos hw hfit_space
  have hfit_kwise : Fits w (base + ReducedKWise.space w w₀ b b 5) :=
    hfit_space.of_le (by dsimp only [space, b]; omega)
  have hS_lt : #S < 2 ^ b := card_lt_two_pow_quotBits hU hS
  set s1 := x.set (qfReg 246) (x.regs (qfReg 1))
  have e1 : Exec w (.op (.copy (qfReg 246) (qfReg 1)) : Code .exact rQF) x s1 1 := Exec.copy
  have hs1_0 : (s1.comap kwiseMap).regs 0 = base := by
    change s1.regs (qfReg 0) = base
    simp +decide [s1, hx_0]
  have hs1_1 : (s1.comap kwiseMap).regs 1 = u.val := by
    change s1.regs (qfReg 1) = u.val
    simp +decide [s1, h1, u]
  obtain ⟨y_ev, he_ev_inner, hy_ev_0, hy_ev_2, hy_ev_mem⟩ :=
    ReducedKWise.evalCode_exec hw₀_pos hw₀_le hU hb_lt.le hc_lt hfit_kwise p.1 u
      (s1.comap kwiseMap) hs1_0 hs1_1 htab hseed
  have e2 := he_ev_inner.rename injective_kwiseMap
  set s2 := y_ev.extend kwiseMap s1
  have hs2_mem : s2.mem = x.mem := hy_ev_mem
  have hs2_0 : s2.regs (qfReg 0) = base := by
    change (s2.comap kwiseMap).regs 0 = base
    rw [Data.comap_extend injective_kwiseMap]
    exact hy_ev_0
  have hs2_2 : s2.regs (qfReg 2) = (quotHash U w₀ n p.1 u).val := by
    change (s2.comap kwiseMap).regs 2 = (quotHash U w₀ n p.1 u).val
    rw [Data.comap_extend injective_kwiseMap]
    exact hy_ev_2
  have hs2_fr : s2.regs (qfReg 240) = base + space w w₀ n k := by
    rw [extend_kwiseMap_regs (by decide : 240 ≤ (qfReg 240).val)]
    simp +decide [s1, hx_fr]
  have hs2_246 : s2.regs (qfReg 246) = u.val := by
    rw [extend_kwiseMap_regs (by decide : 240 ≤ (qfReg 246).val)]
    simp +decide [s1, h1, u]
  have hs2_247 : s2.regs (qfReg 247) = opTag o := by
    rw [extend_kwiseMap_regs (by decide : 240 ≤ (qfReg 247).val)]
    simp +decide [s1, h247]
  set s3 := s2.set (qfReg 1) (s2.regs (qfReg 246))
  have e3 : Exec w (.op (.copy (qfReg 1) (qfReg 246)) : Code .exact rQF) s2 s3 1 := Exec.copy
  set s4 := s3.set (qfReg 245) (s3.regs (qfReg 2))
  have e4 : Exec w (.op (.copy (qfReg 245) (qfReg 2)) : Code .exact rQF) s3 s4 1 := Exec.copy
  have hs4_0 : s4.regs (qfReg 0) = base := by simp +decide [s4, s3, hs2_0]
  have hs4_1 : s4.regs (qfReg 1) = u.val := by simp +decide [s4, s3, hs2_246]
  have hs4_rem : s4.mem (remSeedAddr base w w₀ n) = p.2.val := by
    change s2.mem (remSeedAddr base w w₀ n) = p.2.val
    rw [hs2_mem]
    exact hrem_seed
  obtain ⟨s5, e5, hs5_mem, hs5_0, hs5_3, hs5_240⟩ :=
    remEvalCode_exec hw₀_pos hw₀_le hU hfit_space p.2 u hs4_0 hs4_1 hs4_rem
  have hs5_fr : s5.regs (qfReg 240) = base + space w w₀ n k := by
    rw [hs5_240 (qfReg 240) (by decide)]
    simp +decide [s4, s3, hs2_fr]
  have hs5_245 : s5.regs (qfReg 245) = (quotHash U w₀ n p.1 u).val := by
    rw [hs5_240 (qfReg 245) (by decide)]
    simp +decide [s4, s3, hs2_2]
  have hs5_247 : s5.regs (qfReg 247) = opTag o := by
    rw [hs5_240 (qfReg 247) (by decide)]
    simp +decide [s4, s3, hs2_247]
  set s6 := s5.set (qfReg 2) (s5.regs (qfReg 245))
  have e6 : Exec w (.op (.copy (qfReg 2) (qfReg 245)) : Code .exact rQF) s5 s6 1 := Exec.copy
  have he_pre := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq e6))))
  have hs6_bdd : s6.Bounded w := he_pre.within.bounded hx_bdd
  have hs6_mem : s6.mem = x.mem := hs5_mem.trans hs2_mem
  have hs6_0 : s6.regs (qfReg 0) = base := by simp +decide [s6, hs5_0]
  have hs6_fr : s6.regs (qfReg 240) = base + space w w₀ n k := by simp +decide [s6, hs5_fr]
  have hs6_2 : s6.regs (qfReg 2) = (quotHash U w₀ n p.1 u).val := by simp +decide [s6, hs5_245]
  have hs6_3 : s6.regs (qfReg 3) = (remHash U w₀ k p.2 u).val := by simp +decide [s6, hs5_3]
  have hs6_247 : s6.regs (qfReg 247) = opTag o := by simp +decide [s6, hs5_247]
  have hop_lt : opTag o < 4 := by cases o <;> simp [opTag]
  have hinv_s6 : FilterInv n S (quotHash U w₀ n p.1) (remHash U w₀ k p.2)
      (extractFilterState base w w₀ n k s6.mem) := by
    rwa [hs6_mem]
  obtain ⟨y, hy_exec, hy_bdd, hy_0, hy_fr, hy_1, hy_mem⟩ :=
    clusterCode_execWithin hw₀_pos hw hfit_space u hop_lt hs6_bdd hs6_0 hs6_fr
      hs6_2 hs6_3 hs6_247 hinv_s6 hS_lt
  rw [hs6_mem] at hy_fr hy_1 hy_mem
  set s₀ : Memory.State := ⟨x.mem, base + space w w₀ n k⟩
  have hev_le : ReducedKWise.evalSteps w₀ b b 5 ≤ 236841 := by
    have := ReducedKWise.evalSteps_le w₀ b b 5
    dsimp only [ReducedKWise.evalBound] at this
    omega
  have hℓ_le : hinv_s6.clusterLen hS_lt (quotHash U w₀ n p.1 u) ≤
      seedClusterBound U w₀ n S u p.1 :=
    hinv_s6.clusterLen_le_seedClusterBound hS_lt u
  have hstep_le :
      1 + (ReducedKWise.evalSteps w₀ b b 5 +
        (1 + (1 + (45 + (1 +
          (19 + clusterFactor * (11 * hinv_s6.clusterLen hS_lt (quotHash U w₀ n p.1 u) + 14))))))) ≤
        opStepBound (seedClusterBound U w₀ n S u p.1) := by
    dsimp only [opStepBound]
    have hmul : clusterFactor * (11 * hinv_s6.clusterLen hS_lt (quotHash U w₀ n p.1 u) + 14) ≤
        clusterFactor * (11 * seedClusterBound U w₀ n S u p.1 + 14) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  have he_raw : ExecWithin w (opCode w w₀ n k) x y
      (1 + (ReducedKWise.evalSteps w₀ b b 5 +
        (1 + (1 + (45 + (1 +
          (19 +
            clusterFactor * (11 * hinv_s6.clusterLen hS_lt (quotHash U w₀ n p.1 u) + 14)))))))) :=
    e1.within.seq (e2.within.seq (e3.within.seq (e4.within.seq (e5.within.seq
      (e6.within.seq hy_exec)))))
  have he_all : ExecWithin w (opCode w w₀ n k) x y
      (opStepBound (seedClusterBound U w₀ n S u p.1)) :=
    he_raw.mono hstep_le
  cases o with
  | insert u' =>
    dsimp only [u, opKey, opTag] at hy_fr hy_1 hy_mem ho ⊢
    obtain ⟨_, hst_y, hframe_y⟩ :=
      clusterOpProg_mk_insert base w w₀ n k u' s₀ hinv hS_lt
    have hy_fr' : y.regs (qfReg 240) = base + space w w₀ n k := by
      rw [hy_fr, hframe_y.1]
    have hmem_below : ∀ addr < base + ReducedKWise.space w w₀ b b 5,
        y.mem addr = x.mem addr := fun addr haddr => by
      rw [hy_mem]
      exact hframe_y.2 addr (Or.inl (by dsimp only [fullBase, remSeedAddr, b] at *; omega))
    have hrem_y : y.mem (remSeedAddr base w w₀ n) = p.2.val := by
      rw [hy_mem, hframe_y.2 _ (Or.inl (by dsimp only [fullBase]; omega))]
      exact hrem_seed
    have hinv_y : FilterInv n (insert u' S) (quotHash U w₀ n p.1) (remHash U w₀ k p.2)
        (extractFilterState base w w₀ n k y.mem) := by
      rw [hy_mem, hst_y]
      have hcap' : #(insert u' S) ≤ n := card_stepSet_le hS ho
      exact hinv.insertState_filterInv ho.1 hcap' (card_lt_two_pow_quotBits hU hcap')
    have hmod_y : Modifies (Block.mk base (space w w₀ n k)).footprint x.mem y.mem := by
      intro addr haddr
      rw [Block.mem_footprint, Block.Owns, not_and_or, not_le, not_lt] at haddr
      rw [hy_mem]
      apply hframe_y.2 addr
      rcases haddr with hlt | hge
      · exact Or.inl (by dsimp only [fullBase, remSeedAddr] at *; omega)
      · exact Or.inr hge
    exact ⟨y, he_all,
      ⟨hy_bdd, hy_0, hy_fr', (tableRep_congr hmem_below).mpr htab,
        (seedRep_congr p.1 hmem_below).mpr hseed, hrem_y, hinv_y⟩,
      rfl, hmod_y⟩
  | delete u' =>
    dsimp only [u, opKey, opTag] at hy_fr hy_1 hy_mem ho ⊢
    obtain ⟨_, hst_y, hframe_y⟩ :=
      clusterOpProg_mk_delete base w w₀ n k ho s₀ hinv hS_lt
    have hy_fr' : y.regs (qfReg 240) = base + space w w₀ n k := by
      rw [hy_fr, hframe_y.1]
    have hmem_below : ∀ addr < base + ReducedKWise.space w w₀ b b 5,
        y.mem addr = x.mem addr := fun addr haddr => by
      rw [hy_mem]
      exact hframe_y.2 addr (Or.inl (by dsimp only [fullBase, remSeedAddr, b] at *; omega))
    have hrem_y : y.mem (remSeedAddr base w w₀ n) = p.2.val := by
      rw [hy_mem, hframe_y.2 _ (Or.inl (by dsimp only [fullBase]; omega))]
      exact hrem_seed
    have hinv_y : FilterInv n (S.erase u') (quotHash U w₀ n p.1) (remHash U w₀ k p.2)
        (extractFilterState base w w₀ n k y.mem) := by
      rw [hy_mem, hst_y]
      exact hinv.deleteState_filterInv ho hS_lt
    have hmod_y : Modifies (Block.mk base (space w w₀ n k)).footprint x.mem y.mem := by
      intro addr haddr
      rw [Block.mem_footprint, Block.Owns, not_and_or, not_le, not_lt] at haddr
      rw [hy_mem]
      apply hframe_y.2 addr
      rcases haddr with hlt | hge
      · exact Or.inl (by dsimp only [fullBase, remSeedAddr] at *; omega)
      · exact Or.inr hge
    exact ⟨y, he_all,
      ⟨hy_bdd, hy_0, hy_fr', (tableRep_congr hmem_below).mpr htab,
        (seedRep_congr p.1 hmem_below).mpr hseed, hrem_y, hinv_y⟩,
      rfl, hmod_y⟩
  | query u' =>
    dsimp only [u, opKey, opTag] at hy_fr hy_1 hy_mem ho ⊢
    obtain ⟨hres_y, hstate_y⟩ :=
      clusterOpProg_mk_query base w w₀ n k u' s₀ hinv hS_lt
    have hy_fr' : y.regs (qfReg 240) = base + space w w₀ n k := by
      rw [hy_fr, hstate_y]
    have hy_mem' : y.mem = x.mem := by
      rw [hy_mem, hstate_y]
    have hy_1' : y.regs (qfReg 1) =
        (decide (remHash U w₀ k p.2 u' ∈
          bucketRun S (quotHash U w₀ n p.1) (remHash U w₀ k p.2)
            (quotHash U w₀ n p.1 u'))).toNat := by
      rw [hy_1, hres_y]
    have hdec : decode (.query u') y.regs = some (simResult U w₀ n k p S (.query u')) := by
      dsimp only [decode, simResult]
      rw [hy_1']
      congr 1
      cases decide (remHash U w₀ k p.2 u' ∈
        bucketRun S (quotHash U w₀ n p.1) (remHash U w₀ k p.2) (quotHash U w₀ n p.1 u')) <;> rfl
    have hmod_y : Modifies (Block.mk base (space w w₀ n k)).footprint x.mem y.mem := by
      intro addr _
      rw [hy_mem']
    refine ⟨y, he_all, ?_, hdec, hmod_y⟩
    exact ⟨hy_bdd, hy_0, hy_fr', by rwa [hy_mem'], by rwa [hy_mem'], by rwa [hy_mem'],
      by rwa [hy_mem']⟩

/-! ## Section 5: Packaging as `SubroutineCode` and `ObliviousSequenceImpl` -/

/-- Relocatable Word-RAM `SubroutineCode` for the two-stage quotient filter over `Basis.exact`. -/
@[expose] noncomputable def subroutineCode (w w₀ n k : ℕ) : SubroutineCode .exact rQF 0 where
  allocSpan := allocSpan w w₀ n k
  initSetup := initSetup w w₀ n
  code := opCode w w₀ n k
  frontierReg := qfReg 240
  baseReg := qfReg 0
  initParams := ![]
  curReg := qfReg 241
  zeroReg := qfReg 242
  oneReg := qfReg 243
  incCur := .exactBin .add (qfReg 241) (qfReg 241) (qfReg 243)
  input := inputReg
  output := qfReg 1

theorem prepare_rep {U base w w₀ n k : ℕ}
    (hw₀_pos : 0 < w₀) (hw : 2 * w₀ ≤ w) (hU : U ≤ 2 ^ w₀)
    {p : FilterSeed w₀ n} {S : Finset (Fin U)} (o : Op U) {x : Data rQF}
    (hrep : Rep U w base w₀ n k p S x) :
    let x_prep := ((subroutineCode w w₀ n k).toDynamicProgram encode decode).prepare o x
    Rep U w base w₀ n k p S x_prep ∧
    x_prep.regs (qfReg 1) = (opKey o).val ∧
    x_prep.regs (qfReg 247) = opTag o ∧
    (∀ i, (subroutineCode w w₀ n k).input i = true → Fits w (encode o i)) := by
  intro x_prep
  have hfit_args : ∀ i, (subroutineCode w w₀ n k).input i = true → Fits w (encode o i) := by
    intro i hi
    change decide (i = qfReg 1 ∨ i = qfReg 247) = true at hi
    rcases of_decide_eq_true hi with rfl | rfl
    · dsimp only [encode, ite_true]
      have hlt : (opKey o).val < 2 ^ w₀ := (opKey o).isLt.trans_le hU
      exact hlt.trans_le (Nat.pow_le_pow_right two_pos (by omega))
    · have h247 : encode o (qfReg 247) = opTag o := by simp +decide [encode]
      rw [h247]
      have htag : opTag o ≤ 2 := by cases o <;> simp [opTag]
      have hpow : 4 ≤ 2 ^ w := by
        calc 4 = 2 ^ 2 := by decide
          _ ≤ 2 ^ w := Nat.pow_le_pow_right two_pos (by omega)
      change opTag o < 2 ^ w
      omega
  have hbdd_prep : x_prep.Bounded w :=
    ((subroutineCode w w₀ n k).toDynamicProgram encode decode).prepare_bounded hrep.1 hfit_args
  have h0_prep : x_prep.regs (qfReg 0) = base := by
    change (if inputReg (qfReg 0) then encode o (qfReg 0) else x.regs (qfReg 0)) = base
    simp +decide [hrep.2.1]
  have hfr_prep : x_prep.regs (qfReg 240) = base + space w w₀ n k := by
    change (if inputReg (qfReg 240) then encode o (qfReg 240) else x.regs (qfReg 240)) =
      base + space w w₀ n k
    simp +decide [hrep.2.2.1]
  have h1_prep : x_prep.regs (qfReg 1) = (opKey o).val := by
    change (if inputReg (qfReg 1) then encode o (qfReg 1) else x.regs (qfReg 1)) = (opKey o).val
    simp +decide [encode]
  have h247_prep : x_prep.regs (qfReg 247) = opTag o := by
    change (if inputReg (qfReg 247) then encode o (qfReg 247) else x.regs (qfReg 247)) = opTag o
    simp +decide [encode]
  exact ⟨⟨hbdd_prep, h0_prep, hfr_prep, hrep.2.2.2⟩, h1_prep, h247_prep, hfit_args⟩

theorem tsum_opStepBound_le {U w₀ n : ℕ} (hw₀_pos : 0 < w₀) (hU : U ≤ 2 ^ w₀)
    {S : Finset (Fin U)} (hS : #S ≤ n) (u : Fin U) :
    (∑' p : FilterSeed w₀ n,
      (filterSeedLaw w₀ n) p *
        (opStepBound (seedClusterBound U w₀ n S u p.1) : ℝ≥0∞)) ≤
      (charge : ℝ≥0∞) := by
  have hbound := tsum_seedClusterBound_le hw₀_pos hU hS u
  let A : ℝ≥0∞ := (clusterFactor * 11 : ℕ)
  let B : ℝ≥0∞ := (clusterFactor * 14 + 236909 : ℕ)
  have hop_eq (ℓ : ℕ) : (opStepBound ℓ : ℝ≥0∞) = A * (ℓ : ℝ≥0∞) + B := by
    dsimp only [opStepBound, A, B]
    push_cast
    ring
  calc (∑' p : FilterSeed w₀ n,
        (filterSeedLaw w₀ n) p *
          (opStepBound (seedClusterBound U w₀ n S u p.1) : ℝ≥0∞))
      = ∑' p : FilterSeed w₀ n,
          ((filterSeedLaw w₀ n) p *
            (A * (seedClusterBound U w₀ n S u p.1 : ℝ≥0∞)) +
          (filterSeedLaw w₀ n) p * B) := by
        refine tsum_congr fun p => ?_
        rw [hop_eq, mul_add]
    _ = A *
          (∑' p : FilterSeed w₀ n,
            (filterSeedLaw w₀ n) p * (seedClusterBound U w₀ n S u p.1 : ℝ≥0∞)) +
        B := by
        rw [Summable.tsum_add CompleteLattice.summable CompleteLattice.summable,
          ENNReal.tsum_mul_right, (filterSeedLaw w₀ n).tsum_coe, one_mul]
        congr 1
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun p => by ring
    _ ≤ A * 290 + B := by
        gcongr
    _ = (charge : ℝ≥0∞) := by
        dsimp only [charge]
        exact (hop_eq 290).symm

private theorem steps_exec_aux {U base w w₀ n k : ℕ}
    (hw₀_pos : 0 < w₀) (hw : 2 * w₀ ≤ w) (hU : U ≤ 2 ^ w₀)
    (hfit_space : Fits w (base + space w w₀ n k))
    {ε : ℝ≥0∞}
    (prefOps remOps : List (Op U))
    (ν : PMF (SeqOutcome (FilterSeed w₀ n) (@Result U) rQF))
    (hS : #(activeSet prefOps) ≤ n)
    (hv : ValidOpSeqFrom n (activeSet prefOps) remOps)
    (hseed : ν.map SeqOutcome.latent = filterSeedLaw w₀ n)
    (hsupp : ∀ t ∈ ν.support,
      t.transcript = simTranscript U w₀ n k t.latent ∅ prefOps ∧
      Rep U w base w₀ n k t.latent (activeSet prefOps) t.data) :
    ∃ (ν_final : PMF (SeqOutcome (FilterSeed w₀ n) (@Result U) rQF)) (T_ops : ℝ≥0∞),
      ExecSteps (subroutineCode w w₀ n k) (spec U n ε)
        (FilterSeed w₀ n) w base (space w w₀ n k) encode decode remOps ν ν_final T_ops ∧
      ν_final.map SeqOutcome.latent = filterSeedLaw w₀ n ∧
      (∀ t ∈ ν_final.support,
        t.transcript = simTranscript U w₀ n k t.latent ∅ (prefOps ++ remOps) ∧
        Rep U w base w₀ n k t.latent (activeSet (prefOps ++ remOps)) t.data) ∧
      T_ops ≤ ((remOps.map (fun _ : Op U => charge)).sum : ℝ≥0∞) := by
  induction remOps generalizing prefOps ν with
  | nil =>
    refine ⟨ν, 0, ExecSteps.nil (S := spec U n ε) ν, hseed, fun t ht => ?_, by simp⟩
    rw [List.append_nil]
    exact hsupp t ht
  | cons o os ih =>
    set S := activeSet prefOps
    obtain ⟨ho_valid, hos_valid⟩ := hv
    let xPrep (t : SeqOutcome (FilterSeed w₀ n) (@Result U) rQF) : Data rQF :=
      ((subroutineCode w w₀ n k).toDynamicProgram encode decode).prepare o t.data
    have hstep_ex : ∀ (t : SeqOutcome (FilterSeed w₀ n) (@Result U) rQF),
        t ∈ ν.support →
        ∃ y : Data rQF,
          ExecWithin w (opCode w w₀ n k) (xPrep t) y
            (opStepBound (seedClusterBound U w₀ n S (opKey o) t.latent.1)) ∧
          Rep U w base w₀ n k t.latent (stepSet S o) y ∧
          decode o y.regs = some (simResult U w₀ n k t.latent S o) ∧
          Modifies (Block.mk base (space w w₀ n k)).footprint t.data.mem y.mem := by
      intro t ht
      obtain ⟨hrep_prep, h1_prep, h247_prep, _⟩ :=
        prepare_rep hw₀_pos hw hU o (hsupp t ht).2
      exact opCode_execWithin hw₀_pos hw hU hfit_space hS ho_valid hrep_prep h1_prep h247_prep
    classical
    let nextData (t : SeqOutcome (FilterSeed w₀ n) (@Result U) rQF) : Data rQF :=
      if ht : t ∈ ν.support then Classical.choose (hstep_ex t ht) else t.data
    let μ_step (t : SeqOutcome (FilterSeed w₀ n) (@Result U) rQF) :
        PMF (StepOutcome (FilterSeed w₀ n) (Result o) rQF) :=
      PMF.pure ⟨t.latent, nextData t, simResult U w₀ n k t.latent S o⟩
    let T_step (t : SeqOutcome (FilterSeed w₀ n) (@Result U) rQF) : ℝ≥0∞ :=
      (opStepBound (seedClusterBound U w₀ n S (opKey o) t.latent.1) : ℝ≥0∞)
    let ν₁ : PMF (SeqOutcome (FilterSeed w₀ n) (@Result U) rQF) :=
      ν.bind fun t => (μ_step t).map (t.appendStep o)
    have hseed₁ : ν₁.map SeqOutcome.latent = filterSeedLaw w₀ n := by
      dsimp only [ν₁, μ_step]
      rw [PMF.map_bind]
      have hbind_eq :
          (ν.bind fun t =>
            ((PMF.pure ⟨t.latent, nextData t, simResult U w₀ n k t.latent S o⟩).map
              (t.appendStep o)).map SeqOutcome.latent) =
          ν.map SeqOutcome.latent := by
        refine congrArg (ν.bind ·) (funext fun t => ?_)
        rw [PMF.pure_map, PMF.pure_map]
        rfl
      rw [hbind_eq, hseed]
    have hact_append : activeSet (prefOps ++ [o]) = stepSet S o := by
      dsimp only [activeSet, S]
      rw [activeSetFrom_append, activeSetFrom_cons, activeSetFrom_nil]
    have hS₁ : #(activeSet (prefOps ++ [o])) ≤ n := by
      rw [hact_append]
      exact card_stepSet_le hS ho_valid
    have hos_valid' : ValidOpSeqFrom n (activeSet (prefOps ++ [o])) os := by
      rwa [hact_append]
    have hsupp₁ : ∀ q_seq ∈ ν₁.support,
        q_seq.transcript = simTranscript U w₀ n k q_seq.latent ∅ (prefOps ++ [o]) ∧
        Rep U w base w₀ n k q_seq.latent (activeSet (prefOps ++ [o])) q_seq.data := by
      intro q_seq hq_seq
      dsimp only [ν₁, μ_step] at hq_seq
      rw [PMF.mem_support_bind_iff] at hq_seq
      obtain ⟨t, ht, hq_map⟩ := hq_seq
      rw [PMF.mem_support_map_iff] at hq_map
      obtain ⟨q, hq, rfl⟩ := hq_map
      rw [PMF.mem_support_pure_iff] at hq
      subst hq
      obtain ⟨htr_t, _⟩ := hsupp t ht
      have hspec := Classical.choose_spec (hstep_ex t ht)
      have hnd : nextData t = Classical.choose (hstep_ex t ht) :=
        dite_eq_left_of_eq_true (eq_true ht)
      refine ⟨?_, ?_⟩
      · dsimp only [SeqOutcome.appendStep]
        rw [htr_t, simTranscript_append]
        rfl
      · dsimp only [SeqOutcome.appendStep]
        rw [hact_append, hnd]
        exact hspec.2.1
    obtain ⟨ν_final, T_rest, hex_rest, hseed_final, hsupp_final, hcost_rest⟩ :=
      ih (prefOps ++ [o]) ν₁ hS₁ hos_valid' hseed₁ hsupp₁
    let T₁ : ℝ≥0∞ := ∑' t, ν t * T_step t
    have hex_cons :
        ExecSteps (subroutineCode w w₀ n k) (spec U n ε)
          (FilterSeed w₀ n) w base (space w w₀ n k) encode decode (o :: os) ν ν_final
          (T₁ + T_rest) := by
      refine ExecSteps.cons (S := spec U n ε) (μ_step := μ_step) (T_step := T_step)
        (fun t ht => ?_) hex_rest
      obtain ⟨_, hrep_t⟩ := hsupp t ht
      obtain ⟨hrep_prep, _, _, hfit_args⟩ := prepare_rep hw₀_pos hw hU o hrep_t
      have hspec := Classical.choose_spec (hstep_ex t ht)
      have hnd : nextData t = Classical.choose (hstep_ex t ht) :=
        dite_eq_left_of_eq_true (eq_true ht)
      have hmap_data : (μ_step t).map StepOutcome.data = PMF.pure (nextData t) := by
        dsimp only [μ_step]
        rw [PMF.pure_map]
      refine ⟨hrep_t.1, hfit_args, hrep_prep.1, ?_, ?_⟩
      · rw [hmap_data, hnd]
        exact ExecCodeDist.of_execWithin hspec.1
      · intro q hq
        dsimp only [μ_step] at hq
        rw [PMF.mem_support_pure_iff] at hq
        subst hq
        dsimp only
        rw [hnd]
        exact ⟨hspec.2.1.1, hspec.2.2.1, hspec.2.2.2⟩
    have hT₁_le : T₁ ≤ (charge : ℝ≥0∞) := by
      have hmap :
          T₁ = ∑' p : FilterSeed w₀ n,
            (ν.map SeqOutcome.latent) p *
              (opStepBound (seedClusterBound U w₀ n S (opKey o) p.1) : ℝ≥0∞) :=
        (Cslib.Probability.PMF.tsum_map_mul ν SeqOutcome.latent
          fun p => (opStepBound (seedClusterBound U w₀ n S (opKey o) p.1) : ℝ≥0∞)).symm
      rw [hmap, hseed]
      exact tsum_opStepBound_le hw₀_pos hU hS (opKey o)
    refine ⟨ν_final, T₁ + T_rest, hex_cons, hseed_final, fun t ht => ?_, ?_⟩
    · have h := hsupp_final t ht
      rwa [List.append_assoc, List.singleton_append] at h
    · simp only [List.map_cons, List.sum_cons, Nat.cast_add]
      exact add_le_add hT₁_le hcost_rest

/-- Parametric `ObliviousSequenceImpl` certificate for `spec U n ε` whenever
`(1 / 2 : ℝ≥0∞) ^ k ≤ ε`. -/
@[expose] noncomputable def implOfLe {U base w w₀ n k : ℕ} {ε : ℝ≥0∞}
    (hε : (1 / 2 : ℝ≥0∞) ^ k ≤ ε)
    (hw₀_pos : 0 < w₀) (hw : 2 * w₀ ≤ w) (hU : U ≤ 2 ^ w₀)
    (hfit_space : Fits w (base + space w w₀ n k)) :
    ObliviousSequenceImpl (subroutineCode w w₀ n k)
      (spec U n ε) w base ![] where
  Latent := FilterSeed w₀ n
  space := space w w₀ n k
  spanTime := 3
  setupTime := setupSteps w₀ n
  initPotential := 0
  charge _ := charge
  initInv ν₀ :=
    ν₀.map LatentState.latent = filterSeedLaw w₀ n ∧
    ∀ t ∈ ν₀.support, Rep U w base w₀ n k t.latent ∅ t.data
  validOp _ _ := True
  encode := encode
  decode := decode
  bounded hinv t ht := (hinv.2 t ht).1
  arguments_fit o _ i hi := by
    change decide (i = qfReg 1 ∨ i = qfReg 247) = true at hi
    rcases of_decide_eq_true hi with rfl | rfl
    · dsimp only [encode, ite_true]
      have hlt : (opKey o).val < 2 ^ w₀ := (opKey o).isLt.trans_le hU
      exact hlt.trans_le (Nat.pow_le_pow_right two_pos (by omega))
    · have h247 : encode o (qfReg 247) = opTag o := by simp +decide [encode]
      rw [h247]
      have htag : opTag o ≤ 2 := by cases o <;> simp [opTag]
      have hpow : 4 ≤ 2 ^ w := by
        calc 4 = 2 ^ 2 := by decide
          _ ≤ 2 ^ w := Nat.pow_le_pow_right two_pos (by omega)
      change opTag o < 2 ^ w
      omega
  clear_nodup := by simp +decide [subroutineCode]
  params_not_clear j := Fin.elim0 j
  incCur_eval {x} h1 hfit := by
    dsimp only [subroutineCode] at h1 hfit ⊢
    rw [Op.eval_exactBin, h1]
    exact Data.put_of_fits hfit
  span_exec _ hfr _ := by
    obtain ⟨x₁, he, hmem, hb, hfr₁⟩ := allocSpan_execWithin hfit_space hfr
    exact ⟨x₁, he, hmem, hb, hfr₁, fun j => Fin.elim0 j⟩
  setup_exec hx₁ hb hfr _ hz :=
    initSetup_exec hw₀_pos hw hfit_space hx₁ hb hfr hz
  steps_exec ops ν₀ hv hinv := by
    let ν_seq : PMF (SeqOutcome (FilterSeed w₀ n) (@Result U) rQF) :=
      ν₀.map SeqOutcome.ofLatentState
    have hseed_seq : ν_seq.map SeqOutcome.latent = filterSeedLaw w₀ n := by
      dsimp only [ν_seq]
      rw [PMF.map_comp]
      exact hinv.1
    have hsupp_seq : ∀ t ∈ ν_seq.support,
        t.transcript = simTranscript U w₀ n k t.latent ∅ [] ∧
        Rep U w base w₀ n k t.latent (activeSet []) t.data := by
      intro t ht
      dsimp only [ν_seq] at ht
      rw [PMF.mem_support_map_iff] at ht
      obtain ⟨u, hu, rfl⟩ := ht
      exact ⟨rfl, hinv.2 u hu⟩
    obtain ⟨ν_final, T_ops, hex, hseed_final, hsupp_final, hcost⟩ :=
      steps_exec_aux hw₀_pos hw hU hfit_space [] ops ν_seq (by simp) hv hseed_seq hsupp_seq
    have htr_map :
        ν_final.map SeqOutcome.transcript =
          (filterSeedLaw w₀ n).map (fun p => simTranscript U w₀ n k p ∅ ops) := by
      have hcongr :
          ν_final.map SeqOutcome.transcript =
            ν_final.map ((fun p => simTranscript U w₀ n k p ∅ ops) ∘ SeqOutcome.latent) := by
        refine Cslib.Probability.PMF.map_congr_on_support _ _ _ fun t ht => ?_
        have h := (hsupp_final t ht).1
        rw [List.nil_append] at h
        exact h
      rw [hcongr, ← PMF.map_comp, hseed_final]
    refine ⟨ν_final, T_ops, hex, ?_, ?_⟩
    · rw [htr_map]
      exact spec_weaken hε (contract_map_simTranscript hw₀_pos hU hv)
    · simpa only [Nat.cast_zero, zero_add] using hcost

/-- Exact-basis `ObliviousSequenceImpl` certificate for the two-stage quotient filter realizing
`spec U n ((1 / 2 : ℝ≥0∞) ^ k)`. -/
@[expose] noncomputable def impl {U base w w₀ n k : ℕ}
    (hw₀_pos : 0 < w₀) (hw : 2 * w₀ ≤ w) (hU : U ≤ 2 ^ w₀)
    (hfit_space : Fits w (base + space w w₀ n k)) :
    ObliviousSequenceImpl (subroutineCode w w₀ n k)
      (spec U n ((1 / 2 : ℝ≥0∞) ^ k)) w base ![] :=
  implOfLe le_rfl hw₀_pos hw hU hfit_space

/-- Standard-basis `ObliviousSequenceImpl` certificate for `spec U n ((1 / 2 : ℝ≥0∞) ^ k)`. -/
@[expose] noncomputable def implStandard {U base w w₀ n k : ℕ}
    (hw₀_pos : 0 < w₀) (hw : 2 * w₀ ≤ w) (hU : U ≤ 2 ^ w₀)
    (hfit_space : Fits w (base + space w w₀ n k)) :
    ObliviousSequenceImpl (subroutineCode w w₀ n k).toStandard
      (spec U n ((1 / 2 : ℝ≥0∞) ^ k)) w base ![] :=
  (impl hw₀_pos hw hU hfit_space).toStandard

/-- Exact-basis `ObliviousSequenceImpl` certificate realizing `spec U n ε` for any `ε ≠ 0` by
choosing `k = epsLog ε = max 1 ⌈log₂(1 / ε)⌉`. -/
@[expose] noncomputable def implOfEps {U base w w₀ n : ℕ} {ε : ℝ≥0∞}
    (hε0 : ε ≠ 0) (hw₀_pos : 0 < w₀) (hw : 2 * w₀ ≤ w) (hU : U ≤ 2 ^ w₀)
    (hfit_space : Fits w (base + space w w₀ n (epsLog ε))) :
    ObliviousSequenceImpl (subroutineCode w w₀ n (epsLog ε))
      (spec U n ε) w base ![] :=
  implOfLe (two_pow_neg_epsLog_le hε0) hw₀_pos hw hU hfit_space

/-- Standard-basis `ObliviousSequenceImpl` certificate realizing `spec U n ε` for any `ε ≠ 0`. -/
@[expose] noncomputable def implOfEpsStandard {U base w w₀ n : ℕ} {ε : ℝ≥0∞}
    (hε0 : ε ≠ 0) (hw₀_pos : 0 < w₀) (hw : 2 * w₀ ≤ w) (hU : U ≤ 2 ^ w₀)
    (hfit_space : Fits w (base + space w w₀ n (epsLog ε))) :
    ObliviousSequenceImpl (subroutineCode w w₀ n (epsLog ε)).toStandard
      (spec U n ε) w base ![] :=
  (implOfEps hε0 hw₀_pos hw hU hfit_space).toStandard

/-- Space bound for `impl` without requiring `quotBits w₀ n ≤ w` as a separate hypothesis. -/
theorem impl_space_le {U base w w₀ n k : ℕ}
    (hw₀_pos : 0 < w₀) (hw : 2 * w₀ ≤ w) (hU : U ≤ 2 ^ w₀)
    (hfit_space : Fits w (base + space w w₀ n k))
    (hn : 1 ≤ n) (hk : 1 ≤ k) :
    (impl hw₀_pos hw hU hfit_space).space ≤ 640 * ((n * k + w - 1) / w + 1) :=
  space_le hw₀_pos hw (quotBits_lt_w_of_fits_space hw₀_pos hw hfit_space).le hn hk

/-- Space bound for `implOfEps`: at most `640 * ((n * epsLog ε + w - 1) / w + 1)` words for all
`1 ≤ n`, `0 < w₀`, `2 * w₀ ≤ w`. -/
theorem implOfEps_space_le {U base w w₀ n : ℕ} {ε : ℝ≥0∞}
    (hε0 : ε ≠ 0) (hw₀_pos : 0 < w₀) (hw : 2 * w₀ ≤ w) (hU : U ≤ 2 ^ w₀)
    (hfit_space : Fits w (base + space w w₀ n (epsLog ε)))
    (hn : 1 ≤ n) :
    (implOfEps hε0 hw₀_pos hw hU hfit_space).space ≤
      640 * ((n * epsLog ε + w - 1) / w + 1) :=
  impl_space_le hw₀_pos hw hU hfit_space hn (one_le_epsLog ε)

end Cslib.DataStructure.ApproximateMembership.QuotientFilter
