/-
Copyright (c) 2026 Karn Seth, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.RandomFunctionHybrid
public import CslibFrontier.Crypto.Primitives.BlockCipher.Modes
public import CslibFrontier.Crypto.Primitives.PRF.Finite
public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
public import CslibFrontier.Languages.Probabilistic.QueryCount
import CslibFrontier.Languages.Probabilistic.Oracle.Interaction
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Languages.Probabilistic.UntilBad.TwoCost
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Support

/-!
# CPA Security of Counter (CTR) Mode

Counter mode ([KatzLindell2020], Section 3.6.3, Figure 3.9) encrypts a message of `k` blocks under
a block function `f`, a counter schedule `counter : BitString n → ℕ → BitString n`, and a uniform
initialization vector `iv` by XORing the keystream `f (counter iv 0), f (counter iv 1), …` with
the plaintext blocks. [KatzLindell2020] (Section 3.6.3, Theorem 3.33, p. 93) proves that CTR mode
is CPA-secure whenever `f` is a pseudorandom function.

The security notion is the left-or-right multiple-encryption experiment of [KatzLindell2020],
Definition 3.22, using the shared block-mode query/cost/ideal-game interface (`BlockModeQuery`,
`BlockModeAdversary`, `blockModeSelect`, `blockModeBlocks`, `blockModeCost`, `blockModeIdealGame`)
from `RandomFunctionHybrid.lean`.

The proof works for any counter schedule `counter : BitString n → ℕ → BitString n` satisfying
within-query distinctness (`∀ iv i j, i < ℓ → j < ℓ → i ≠ j → counter iv i ≠ counter iv j`) and
per-offset injectivity in the IV (`∀ i < ℓ, Function.Injective (fun iv => counter iv i)`), and is
instantiated on the canonical modular counter schedule `ctrModCounter` when `ℓ ≤ 2 ^ n`:
1. The CTR experiment is the real PRF experiment for a reduction encrypting with its oracle
   (`ctrCpaGame_eq_realExperiment`), making at most `K` oracle calls
   (`isQueryBounded_ctrReduction`).
2. Against a lazily sampled uniform random function, the reduction's view differs from fresh
   uniform ciphertexts only when some `counter iv i` hits an earlier queried input. Within-query
   distinctness rules out intra-query collisions, and per-offset injectivity bounds inter-query
   collisions by `K ^ 2 / 2 ^ n` (`advantage_idealExperiment_ctrReduction_le`).
3. Combining the ideal hybrids with the two PRF advantages yields the concrete bound
   (`advantage_ctrCpaGame_le`, and `advantage_ctrCpaGame_ctrModCounter_le` for `ctrModCounter`).

The PRF experiments are the concrete ones of `Cslib.Crypto.PRF` ([BonehShoup2023], Chapter 4). The
reduction is concrete (`ProbOracleComp`); no native multitape PPT statement is made.

## Main definitions

* `Cslib.Crypto.ctrOracle`, `Cslib.Crypto.ctrCpaGame`: real CTR left-or-right oracle and
  experiment.
* `Cslib.Crypto.ctrMaskQueriesFrom`, `Cslib.Crypto.ctrQueryProgram`, `Cslib.Crypto.ctrReduction`:
  the PRF distinguisher built from a `BlockModeAdversary`.
* `Cslib.Crypto.ctrModCounter`: canonical modular-addition counter `iv + i mod 2 ^ n`.

## Main results

* `Cslib.Crypto.ctrCpaGame_eq_realExperiment`, `Cslib.Crypto.isQueryBounded_ctrReduction`: exact
  real-PRF equivalence and oracle-call bound.
* `Cslib.Crypto.advantage_idealExperiment_ctrReduction_le`: random-function idealization bound
  `K ^ 2 / 2 ^ n` against `blockModeIdealGame`.
* `Cslib.Crypto.advantage_ctrCpaGame_randomFunction_le`, `Cslib.Crypto.advantage_ctrCpaGame_le`:
  concrete CTR left-or-right CPA security bounds.
* `Cslib.Crypto.ctrModCounter_injective_left`, `Cslib.Crypto.ctrModCounter_injOn`,
  `Cslib.Crypto.advantage_ctrCpaGame_ctrModCounter_randomFunction_le`,
  `Cslib.Crypto.advantage_ctrCpaGame_ctrModCounter_le`: specializations to `ctrModCounter` for
  `ℓ ≤ 2 ^ n`.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*, 3rd ed.][KatzLindell2020],
  Section 3.6.3 (Figure 3.9, p. 92), Definition 3.22 (p. 74), Theorem 3.23 (p. 75), and
  Theorem 3.33 (p. 93).
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Chapter 4.
-/

public section

namespace Cslib.Crypto

open Cslib.Probability
open OracleComp (sumHandler)
open scoped ENNReal NNReal

variable {n : ℕ}

/-! ### Section 1: The CTR Left-or-Right Experiment -/

/-- The CTR left-or-right oracle for counter schedule `counter`, block function `f`, and challenge
bit `b` ([KatzLindell2020], Section 3.6.3, Figure 3.9). -/
@[expose]
noncomputable def ctrOracle (counter : BitString n → ℕ → BitString n) (ℓ : ℕ)
    (f : BitString n → BitString n) (b : Bool) (q : BlockModeQuery n) :
    ProbComp (BitString n × List (BitString n)) :=
  blockModeOracle (ctrEncryptBlocks f counter) ℓ b q

/-- The CTR left-or-right experiment for keyed block function `F` and challenge bit `b`
([KatzLindell2020], Definition 3.22). -/
@[expose]
noncomputable def ctrCpaGame {Key : Type} (counter : BitString n → ℕ → BitString n)
    [Fintype Key] [Nonempty Key] (F : Key → BitString n → BitString n) (ℓ : ℕ) (b : Bool)
    (adversary : BlockModeAdversary n) : Game :=
  blockModeCpaGame (fun key => ctrEncryptBlocks (F key) counter) ℓ b adversary

/-! ### Section 2: The Reduction to a Pseudorandom Function -/

/-- Query the function oracle on `counter iv i, counter iv (i + 1), …, counter iv (i + k - 1)`. -/
@[expose]
def ctrMaskQueriesFrom (counter : BitString n → ℕ → BitString n) (iv : BitString n) :
    ℕ → ℕ → ProbOracleComp (fun _ : BitString n => BitString n) (List (BitString n))
  | _, 0 => pure []
  | i, k + 1 => do
    let y ← ProbOracleComp.query (counter iv i)
    let ys ← ctrMaskQueriesFrom counter iv (i + 1) k
    return y :: ys

/-- One CTR encryption computed with a function oracle: sample a uniform IV, evaluate the keystream
masks via oracle queries starting at offset `0`, and XOR with the selected plaintext. -/
@[expose]
noncomputable def ctrQueryProgram (counter : BitString n → ℕ → BitString n) (ℓ : ℕ) (b : Bool)
    (q : BlockModeQuery n) :
    ProbOracleComp (fun _ : BitString n => BitString n) (BitString n × List (BitString n)) :=
  blockModeQueryProgram (fun iv k => ctrMaskQueriesFrom counter iv 0 k) ℓ b q

/-- The PRF distinguisher built from a CTR left-or-right adversary ([KatzLindell2020], proof of
Theorem 3.33). -/
@[expose]
noncomputable def ctrReduction (counter : BitString n → ℕ → BitString n) (ℓ : ℕ) (b : Bool)
    (adversary : BlockModeAdversary n) : PRF.Adversary (BitString n) (BitString n) :=
  blockModeReduction (fun iv k => ctrMaskQueriesFrom counter iv 0 k) ℓ b adversary

private theorem range'_map_eq (i k : ℕ) (g : ℕ → BitString n) :
    (List.range' i k).map g = (List.range k).map (fun j => g (i + j)) := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih =>
    simp only [List.range'_succ, List.map_cons, ih (i + 1), List.range_succ_eq_map,
      List.map_map, Function.comp_def]
    refine congrArg (g i :: ·) (List.map_congr_left fun j _ => congrArg g ?_)
    omega

/-- Answering `ctrMaskQueriesFrom counter iv i k` with a fixed function `f` evaluates
`(List.range' i k).map (fun j => f (counter iv j))`. -/
theorem run_ctrMaskQueriesFrom (f : BitString n → BitString n)
    (counter : BitString n → ℕ → BitString n) (iv : BitString n) (i k : ℕ) :
    (ctrMaskQueriesFrom counter iv i k).run (fun y => pure (f y)) =
      pure ((List.range' i k).map (fun j => f (counter iv j))) := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih =>
    simp only [ctrMaskQueriesFrom, ProbOracleComp.run_bind, ProbOracleComp.run_query, ih,
      pure_bind, ProbOracleComp.run_pure, List.range'_succ, List.map_cons]

/-- Answering `ctrMaskQueriesFrom counter iv 0 k` with `f` computes `ctrMaskBlocks f counter iv k`.
-/
theorem run_ctrMaskQueriesFrom_zero (f : BitString n → BitString n)
    (counter : BitString n → ℕ → BitString n) (iv : BitString n) (k : ℕ) :
    (ctrMaskQueriesFrom counter iv 0 k).run (fun y => pure (f y)) =
      pure (ctrMaskBlocks f counter iv k) := by
  rw [run_ctrMaskQueriesFrom, ctrMaskBlocks, range'_map_eq]
  simp

/-- The CTR experiment for keyed function `F` equals the real PRF experiment for `F` and
`ctrReduction counter ℓ b adversary`. -/
theorem ctrCpaGame_eq_realExperiment {Key : Type} (counter : BitString n → ℕ → BitString n)
    [Fintype Key] [Nonempty Key] (F : Key → BitString n → BitString n) (ℓ : ℕ) (b : Bool)
    (adversary : BlockModeAdversary n) :
    ctrCpaGame counter F ℓ b adversary =
      ProbComp.eval (PRF.realExperiment F (ctrReduction counter ℓ b adversary)) :=
  blockModeCpaGame_eq_realExperiment (fun key => ctrEncryptBlocks (F key) counter)
    (fun iv k => ctrMaskQueriesFrom counter iv 0 k) F ℓ b adversary fun key iv ms =>
      ⟨ctrMaskBlocks (F key) counter iv ms.length,
        run_ctrMaskQueriesFrom_zero (F key) counter iv ms.length, rfl⟩

/-- `ctrMaskQueriesFrom counter iv i k` makes at most `k` oracle queries. -/
theorem isQueryBounded_ctrMaskQueriesFrom (counter : BitString n → ℕ → BitString n)
    (iv : BitString n) (i k : ℕ) :
    ProbOracleComp.IsQueryBounded (ctrMaskQueriesFrom counter iv i k) k := by
  induction k generalizing i with
  | zero =>
    simp only [ctrMaskQueriesFrom]
    exact OracleComp.IsCostBounded.pure _ _
  | succ k ih =>
    simp only [ctrMaskQueriesFrom]
    exact OracleComp.IsCostBounded.mono
      (OracleComp.IsCostBounded.bind
        (OracleComp.IsCostBounded.query (Sum.inr (counter iv i))) fun y =>
          OracleComp.IsCostBounded.bind (ih (i + 1)) fun ys =>
            OracleComp.IsCostBounded.pure (y :: ys) 0)
      (by simp only [Sum.elim_inr]; omega)

/-- If `adversary` asks at most `K` blocks in total, `ctrReduction counter ℓ b adversary` makes at
most `K` oracle calls. -/
theorem isQueryBounded_ctrReduction (counter : BitString n → ℕ → BitString n) (ℓ : ℕ) (b : Bool)
    {adversary : BlockModeAdversary n} {K : ℕ}
    (h : OracleComp.IsCostBounded (blockModeCost ℓ) adversary K) :
    ProbOracleComp.IsQueryBounded (ctrReduction counter ℓ b adversary) K :=
  isQueryBounded_blockModeReduction (fun iv k => ctrMaskQueriesFrom counter iv 0 k) ℓ b
    (fun iv k _ => isQueryBounded_ctrMaskQueriesFrom counter iv 0 k) h

/-! ### Section 3: Inter-Query Collision Bound for Fresh CTR Sampling -/

private def ctrCache (c : List (BitString n × BitString n))
    (counter : BitString n → ℕ → BitString n) (iv : BitString n) :
    ℕ → List (BitString n) → List (BitString n × BitString n)
  | _, [] => c
  | i, u :: us => ctrCache ((counter iv i, u) :: c) counter iv (i + 1) us

private def ctrAnyHit (c : List (BitString n × BitString n))
    (counter : BitString n → ℕ → BitString n) (iv : BitString n) : ℕ → ℕ → Bool
  | _, 0 => false
  | i, k + 1 => (c.lookup (counter iv i)).isSome || ctrAnyHit c counter iv (i + 1) k

private theorem length_ctrCache (c : List (BitString n × BitString n))
    (counter : BitString n → ℕ → BitString n) (iv : BitString n) (i : ℕ)
    (us : List (BitString n)) :
    (ctrCache c counter iv i us).length = c.length + us.length := by
  induction us generalizing c i with
  | nil => simp [ctrCache]
  | cons u us ih =>
    simp only [ctrCache, ih, List.length_cons]
    omega

private theorem ctrAnyHit_cons_eq (c : List (BitString n × BitString n))
    (counter : BitString n → ℕ → BitString n) (iv : BitString n) (u : BitString n)
    (i₀ i k : ℕ) (hdistinct : ∀ j < k, counter iv (i + j) ≠ counter iv i₀) :
    ctrAnyHit ((counter iv i₀, u) :: c) counter iv i k = ctrAnyHit c counter iv i k := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih =>
    have h0 : counter iv i ≠ counter iv i₀ := by simpa using hdistinct 0 (Nat.zero_lt_succ k)
    have hbeq : (counter iv i == counter iv i₀) = false := by simpa using h0
    have hhead : (((counter iv i₀, u) :: c).lookup (counter iv i)).isSome =
        (c.lookup (counter iv i)).isSome := by
      simp [List.lookup, hbeq]
    have htail := ih (i + 1) fun j hj => by
      have := hdistinct (j + 1) (Nat.add_lt_add_right hj 1)
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using this
    simp only [ctrAnyHit, hhead, htail]

private theorem ctrAnyHit_eq_true_iff (c : List (BitString n × BitString n))
    (counter : BitString n → ℕ → BitString n) (iv : BitString n) (i k : ℕ) :
    ctrAnyHit c counter iv i k = true ↔ ∃ j < k, counter iv (i + j) ∈ c.map Prod.fst := by
  induction k generalizing i with
  | zero => simp [ctrAnyHit]
  | succ k ih =>
    simp only [ctrAnyHit, Bool.or_eq_true, List.lookup_isSome_iff, ih]
    constructor
    · rintro (⟨p, hp, hpe⟩ | ⟨j, hj, hmem⟩)
      · exact ⟨0, Nat.zero_lt_succ k,
          by simpa using List.mem_map.2 ⟨p, hp, (beq_iff_eq.1 hpe).symm⟩⟩
      · exact ⟨j + 1, Nat.add_lt_add_right hj 1,
          by simpa [Nat.add_assoc, Nat.add_comm 1 j] using hmem⟩
    · rintro ⟨j, hj, hmem⟩
      cases j with
      | zero =>
        obtain ⟨v, hv⟩ : ∃ v, (counter iv i, v) ∈ c := by simpa using hmem
        exact Or.inl ⟨(counter iv i, v), hv, beq_self_eq_true _⟩
      | succ j =>
        exact Or.inr ⟨j, Nat.lt_of_add_lt_add_right hj,
          by simpa [Nat.add_assoc, Nat.add_comm 1 j] using hmem⟩

private theorem runWith_freshStep_ctrMaskQueriesFrom
    (counter : BitString n → ℕ → BitString n) (iv : BitString n) (i k : ℕ) (s : FlagState n)
    (hinj : ∀ a b, i ≤ a → a < i + k → i ≤ b → b < i + k → a ≠ b →
      counter iv a ≠ counter iv b) :
    ProbOracleComp.runWith freshStep (ctrMaskQueriesFrom counter iv i k) s =
      (uniformBlocks k).map fun us =>
        (us, (ctrCache s.1 counter iv i us, s.2 || ctrAnyHit s.1 counter iv i k)) := by
  induction k generalizing i s with
  | zero => simp [ctrMaskQueriesFrom, ctrCache, ctrAnyHit]
  | succ k ih =>
    have hsub : ∀ a b, i + 1 ≤ a → a < i + 1 + k → i + 1 ≤ b → b < i + 1 + k → a ≠ b →
        counter iv a ≠ counter iv b := fun a b ha₀ ha₁ hb₀ hb₁ hab =>
      hinj a b (by omega) (by omega) (by omega) (by omega) hab
    have hdistinct : ∀ j < k, counter iv (i + 1 + j) ≠ counter iv i := fun j hj =>
      hinj (i + 1 + j) i (by omega) (by omega) le_rfl (by omega) (by omega)
    simp only [ctrMaskQueriesFrom, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query,
      ProbOracleComp.runWith_pure]
    change ((freshStep (counter iv i) s).bind fun p =>
      (ProbOracleComp.runWith freshStep (ctrMaskQueriesFrom counter iv (i + 1) k) p.2).map
        fun q => (p.1 :: q.1, q.2)) = _
    simp only [freshStep, Function.comp_def, ← PMF.bind_pure_comp, PMF.bind_bind, PMF.pure_bind]
    have hstep : ∀ u : BitString n,
        ProbOracleComp.runWith freshStep (ctrMaskQueriesFrom counter iv (i + 1) k)
          ((counter iv i, u) :: s.1, s.2 || (s.1.lookup (counter iv i)).isSome) =
          (uniformBlocks k).map fun us =>
            (us, (ctrCache ((counter iv i, u) :: s.1) counter iv (i + 1) us,
              s.2 || ((s.1.lookup (counter iv i)).isSome || ctrAnyHit s.1 counter iv (i + 1) k))) :=
      fun u => by
        rw [ih (i + 1) _ hsub, ctrAnyHit_cons_eq s.1 counter iv u i (i + 1) k hdistinct]
        simp only [Bool.or_assoc]
    simp only [hstep, uniformBlocks_succ, Function.comp_def, ← PMF.bind_pure_comp, PMF.bind_bind,
      PMF.pure_bind, ctrCache, ctrAnyHit]

private theorem runWith_freshStep_ctrQueryProgram
    (counter : BitString n → ℕ → BitString n) (ℓ : ℕ) (b : Bool) (q : BlockModeQuery n)
    (s : FlagState n)
    (hintra : ∀ iv i j, i < ℓ → j < ℓ → i ≠ j → counter iv i ≠ counter iv j) :
    ProbOracleComp.runWith freshStep (ctrQueryProgram counter ℓ b q) s =
      ((PMF.uniformOfFintype (BitString n)).bind fun iv =>
        (uniformBlocks (blockModeBlocks ℓ q)).map (iv, ·)).map fun p =>
          ((p.1, List.zipWith (· + ·) p.2 (blockModeSelect ℓ b q)),
            (ctrCache s.1 counter p.1 0 p.2,
              s.2 || ctrAnyHit s.1 counter p.1 0 (blockModeBlocks ℓ q))) := by
  simp only [ctrQueryProgram, blockModeQueryProgram, ProbOracleComp.runWith_bind,
    ProbOracleComp.runWith_sample, ProbComp.eval_uniform, length_blockModeSelect, Function.comp_def,
    ← PMF.bind_pure_comp, PMF.bind_bind, PMF.pure_bind]
  refine PMF.bind_congr_on_support _ _ _ fun iv _ => ?_
  have hinj : ∀ a b', 0 ≤ a → a < 0 + blockModeBlocks ℓ q → 0 ≤ b' → b' < 0 + blockModeBlocks ℓ q →
      a ≠ b' → counter iv a ≠ counter iv b' := fun a b' _ ha _ hb hab =>
    hintra iv a b' (lt_of_lt_of_le (by omega) (blockModeBlocks_le ℓ q))
      (lt_of_lt_of_le (by omega) (blockModeBlocks_le ℓ q)) hab
  rw [runWith_freshStep_ctrMaskQueriesFrom counter iv 0 (blockModeBlocks ℓ q) s hinj]
  simp only [ProbOracleComp.runWith_pure, Function.comp_def, ← PMF.bind_pure_comp, PMF.bind_bind,
    PMF.pure_bind]

private theorem length_of_mem_support_freshQuery
    (counter : BitString n → ℕ → BitString n) (ℓ : ℕ) (b : Bool) (q : BlockModeQuery n)
    (s : FlagState n)
    (hintra : ∀ iv i j, i < ℓ → j < ℓ → i ≠ j → counter iv i ≠ counter iv j)
    {x : (BitString n × List (BitString n)) × FlagState n}
    (hx : x ∈ (ProbOracleComp.runWith freshStep (ctrQueryProgram counter ℓ b q) s).support) :
    x.2.1.length = s.1.length + blockModeBlocks ℓ q := by
  rw [runWith_freshStep_ctrQueryProgram counter ℓ b q s hintra, PMF.support_map] at hx
  obtain ⟨⟨iv, us⟩, hp, rfl⟩ := hx
  have hlen : us.length = blockModeBlocks ℓ q := length_snd_of_mem_support_uniformDraws hp
  simp only [length_ctrCache, hlen]

private theorem toOuterMeasure_eq_val_of_inj {y : BitString n}
    (f : BitString n → BitString n) (hf : Function.Injective f) :
    (PMF.uniformOfFintype (BitString n)).toOuterMeasure {iv | f iv = y} ≤
      ((2 : ℝ≥0∞) ^ n)⁻¹ := by
  classical
  by_cases hne : ∃ iv₀, f iv₀ = y
  · obtain ⟨iv₀, hiv₀⟩ := hne
    have hset : {iv : BitString n | f iv = y} = {iv₀} := by
      ext iv
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · intro h
        exact hf (h.trans hiv₀.symm)
      · rintro rfl
        exact hiv₀
    rw [hset, PMF.toOuterMeasure_apply_singleton, PMF.uniformOfFintype_apply]
    simp
  · have hset : {iv : BitString n | f iv = y} = ∅ := by
      ext iv
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hne ⟨iv, h⟩
    rw [hset]
    simp

private theorem toOuterMeasure_exists_ctr_mem_le
    (counter : BitString n → ℕ → BitString n) (ks : List (BitString n)) (k : ℕ)
    (hiv : ∀ i < k, Function.Injective (fun iv => counter iv i)) :
    (PMF.uniformOfFintype (BitString n)).toOuterMeasure
        {iv | ∃ j < k, counter iv j ∈ ks} ≤
      ((k * ks.length : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ n)⁻¹ := by
  classical
  have hsub : {iv : BitString n | ∃ j < k, counter iv j ∈ ks} ⊆
      ⋃ j ∈ Finset.range k, ⋃ y ∈ ks.toFinset, {iv | counter iv j = y} := by
    intro iv ⟨j, hj, hmem⟩
    refine Set.mem_biUnion (Finset.mem_range.2 hj) ?_
    exact Set.mem_biUnion (List.mem_toFinset.2 hmem) rfl
  calc (PMF.uniformOfFintype (BitString n)).toOuterMeasure
          {iv | ∃ j < k, counter iv j ∈ ks}
      ≤ (PMF.uniformOfFintype (BitString n)).toOuterMeasure
          (⋃ j ∈ Finset.range k, ⋃ y ∈ ks.toFinset, {iv | counter iv j = y}) :=
        MeasureTheory.measure_mono hsub
    _ ≤ ∑ j ∈ Finset.range k, (PMF.uniformOfFintype (BitString n)).toOuterMeasure
          (⋃ y ∈ ks.toFinset, {iv | counter iv j = y}) :=
        MeasureTheory.measure_biUnion_finset_le _ _
    _ ≤ ∑ j ∈ Finset.range k, ∑ y ∈ ks.toFinset,
          (PMF.uniformOfFintype (BitString n)).toOuterMeasure {iv | counter iv j = y} :=
        Finset.sum_le_sum fun _ _ => MeasureTheory.measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ Finset.range k, ∑ _y ∈ ks.toFinset, ((2 : ℝ≥0∞) ^ n)⁻¹ := by
        refine Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun y _ => ?_
        exact toOuterMeasure_eq_val_of_inj (fun iv => counter iv j)
          (hiv j (Finset.mem_range.1 hj))
    _ = (k : ℝ≥0∞) * ((ks.toFinset.card : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ n)⁻¹) := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (k : ℝ≥0∞) * ((ks.length : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ n)⁻¹) := by
        gcongr
        exact_mod_cast List.toFinset_card_le ks
    _ = ((k * ks.length : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ n)⁻¹ := by
        push_cast
        ring

private theorem toOuterMeasure_bad_freshQuery_le
    (counter : BitString n → ℕ → BitString n) (ℓ : ℕ) (b : Bool) (q : BlockModeQuery n)
    (s : FlagState n) (hs : ¬s.2 = true)
    (hintra : ∀ iv i j, i < ℓ → j < ℓ → i ≠ j → counter iv i ≠ counter iv j)
    (hiv : ∀ i < ℓ, Function.Injective (fun iv => counter iv i)) :
    (ProbOracleComp.runWith freshStep (ctrQueryProgram counter ℓ b q) s).toOuterMeasure
        {x | x.2.2 = true} ≤
      ((blockModeBlocks ℓ q * s.1.length : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ n)⁻¹ := by
  rw [runWith_freshStep_ctrQueryProgram counter ℓ b q s hintra, PMF.toOuterMeasure_map_apply]
  have hs' : s.2 = false := by simpa using hs
  have hpre :
      ((fun p : BitString n × List (BitString n) =>
          ((p.1, List.zipWith (· + ·) p.2 (blockModeSelect ℓ b q)),
            (ctrCache s.1 counter p.1 0 p.2,
              s.2 || ctrAnyHit s.1 counter p.1 0 (blockModeBlocks ℓ q)))) ⁻¹'
        {x | x.2.2 = true}) =
      {p : BitString n × List (BitString n) |
        ctrAnyHit s.1 counter p.1 0 (blockModeBlocks ℓ q) = true} := by
    ext p
    simp [hs']
  rw [hpre, PMF.toOuterMeasure_bind_apply]
  calc ∑' iv, (PMF.uniformOfFintype (BitString n)) iv *
        ((uniformBlocks (n := n) (blockModeBlocks ℓ q)).map (iv, ·)).toOuterMeasure
          {p | ctrAnyHit s.1 counter p.1 0 (blockModeBlocks ℓ q) = true}
      ≤ ∑' iv, (PMF.uniformOfFintype (BitString n)) iv *
          ({iv' | ∃ j < blockModeBlocks ℓ q, counter iv' j ∈ s.1.map Prod.fst}.indicator 1 iv) := by
        refine tsum_le_tsum fun iv => mul_le_mul_of_nonneg_left ?_ zero_le
        rw [PMF.toOuterMeasure_map_apply]
        by_cases hhit : ctrAnyHit s.1 counter iv 0 (blockModeBlocks ℓ q) = true
        · have hex :
              iv ∈ {iv' | ∃ j < blockModeBlocks ℓ q, counter iv' j ∈ s.1.map Prod.fst} := by
            have := (ctrAnyHit_eq_true_iff s.1 counter iv 0 (blockModeBlocks ℓ q)).1 hhit
            simpa using this
          rw [Set.indicator_of_mem hex, Pi.one_apply]
          exact PMF.toOuterMeasure_le_one _ _
        · have hpre2 :
              ((iv, ·) ⁻¹' {p : BitString n × List (BitString n) |
                ctrAnyHit s.1 counter p.1 0 (blockModeBlocks ℓ q) = true}) = ∅ := by
            ext us
            simp [hhit]
          rw [hpre2]
          simp
    _ = (PMF.uniformOfFintype (BitString n)).toOuterMeasure
          {iv' | ∃ j < blockModeBlocks ℓ q, counter iv' j ∈ s.1.map Prod.fst} := by
        rw [← PMF.toOuterMeasure_eq_tsum_mul_indicator]
    _ ≤ ((blockModeBlocks ℓ q * (s.1.map Prod.fst).length : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ n)⁻¹ :=
        toOuterMeasure_exists_ctr_mem_le counter (s.1.map Prod.fst) (blockModeBlocks ℓ q)
          fun i hi => hiv i (lt_of_lt_of_le hi (blockModeBlocks_le ℓ q))
    _ = ((blockModeBlocks ℓ q * s.1.length : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ n)⁻¹ := by
        simp

private theorem toOuterMeasure_bad_fresh_le
    (counter : BitString n → ℕ → BitString n) (ℓ : ℕ) (b : Bool)
    {adversary : BlockModeAdversary n} {K : ℕ}
    (h : OracleComp.IsCostBounded (blockModeCost ℓ) adversary K)
    (hintra : ∀ iv i j, i < ℓ → j < ℓ → i ≠ j → counter iv i ≠ counter iv j)
    (hiv : ∀ i < ℓ, Function.Injective (fun iv => counter iv i)) :
    PMF.toOuterMeasure
        (ProbOracleComp.runWith freshStep (ctrReduction counter ℓ b adversary) ([], false))
        {x | x.2.2 = true} ≤
      ((K * K : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ n)⁻¹ := by
  rw [ctrReduction, blockModeReduction, ProbOracleComp.runWith_interpret_sumHandler]
  refine (OracleComp.toOuterMeasure_bad_le_two_budgets
    (handler := sumHandler (fun i => StateT.lift (ProbComp.unifOracle i))
      fun q => ProbOracleComp.runWith freshStep (ctrQueryProgram counter ℓ b q))
    (bad := fun s : FlagState n => s.2 = true) (blockModeCost ℓ) (fun _ => 0)
    (fun s => (s.1.length : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ n)⁻¹) (fun _ => 0)
    ((2 : ℝ≥0∞) ^ n)⁻¹ 0 0 0 ?_ ?_ ?_ h
    (OracleComp.IsCostBounded.of_forall_cost_eq_zero (fun _ => rfl) adversary)
    (s := ([], false)) (by simp)).trans (le_of_eq ?_)
  · intro q s hs
    cases q with
    | inl i =>
      exact (PMF.toOuterMeasure_lift_eq_zero (bad := fun s : FlagState n => s.2 = true)
        (ProbComp.unifOracle i) s hs).trans_le zero_le
    | inr q =>
      calc (ProbOracleComp.runWith freshStep (ctrQueryProgram counter ℓ b q) s).toOuterMeasure
            {x | x.2.2 = true}
          ≤ ((blockModeBlocks ℓ q * s.1.length : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ n)⁻¹ :=
            toOuterMeasure_bad_freshQuery_le counter ℓ b q s hs hintra hiv
        _ = _ := by
            simp only [blockModeCost, Sum.elim_inr, Nat.cast_zero, zero_mul, add_zero, Nat.cast_mul,
              mul_assoc]
  · intro q s _ x hx _
    cases q with
    | inl i =>
      rw [PMF.snd_eq_of_mem_support_lift hx]
      exact le_add_right (le_add_right le_rfl)
    | inr q =>
      have hlen := length_of_mem_support_freshQuery counter ℓ b q s hintra hx
      simp only [hlen, blockModeCost, Sum.elim_inr]
      refine le_of_eq ?_
      push_cast
      ring
  · intro _ _ _ _ _ _
    exact zero_le
  · simp only [List.length_nil, Nat.cast_mul, Nat.cast_zero, zero_mul, zero_add, add_zero,
      mul_zero]
    ring

/-! ### Section 4: Security of CTR Mode and Modular Counter Instantiation -/

/-- **The CTR reduction against a uniform random function.** If the queries of `adversary` ask at
most `K` blocks in total, and `counter` has no intra-query collisions below `ℓ` and is injective in
`iv` at every offset below `ℓ`, then the reduction's output is within `K ^ 2 / 2 ^ n` of
`blockModeIdealGame` for each challenge bit `b`. -/
theorem advantage_idealExperiment_ctrReduction_le
    (counter : BitString n → ℕ → BitString n) (ℓ : ℕ) (b : Bool)
    {adversary : BlockModeAdversary n} {K : ℕ}
    (h : OracleComp.IsCostBounded (blockModeCost ℓ) adversary K)
    (hintra : ∀ iv i j, i < ℓ → j < ℓ → i ≠ j → counter iv i ≠ counter iv j)
    (hiv : ∀ i < ℓ, Function.Injective (fun iv => counter iv i)) :
    (Game.advantage (ProbComp.eval (PRF.idealExperiment (ctrReduction counter ℓ b adversary)))
        (blockModeIdealGame ℓ adversary) : ℝ) ≤
      (K : ℝ) ^ 2 / 2 ^ n := by
  have hfresh := freshGame_eq_blockModeIdealGame
    (fun iv k => ctrMaskQueriesFrom counter iv 0 k) ℓ b adversary fun q iv s => by
      have hinj : ∀ a b', 0 ≤ a → a < 0 + blockModeBlocks ℓ q → 0 ≤ b' →
          b' < 0 + blockModeBlocks ℓ q → a ≠ b' → counter iv a ≠ counter iv b' :=
        fun a b' _ ha _ hb hab =>
          hintra iv a b' (lt_of_lt_of_le (by omega) (blockModeBlocks_le ℓ q))
            (lt_of_lt_of_le (by omega) (blockModeBlocks_le ℓ q)) hab
      rw [runWith_freshStep_ctrMaskQueriesFrom counter iv 0 (blockModeBlocks ℓ q) s hinj,
        PMF.map_comp]
      exact PMF.map_id _
  rw [ctrReduction, ← hfresh]
  refine (advantage_idealExperiment_freshStep_le _).trans ?_
  have hne : ((K * K : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ n)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.inv_ne_top.2 (pow_ne_zero _ two_ne_zero))
  refine (ENNReal.toReal_mono hne (toOuterMeasure_bad_fresh_le counter ℓ b h hintra hiv)).trans
    (le_of_eq ?_)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast,
    ENNReal.toReal_ofNat, Nat.cast_mul]
  ring

/-- **CTR mode with a uniform random function** ([KatzLindell2020], Section 3.6.3): when
`adversary` asks at most `K` blocks in total and at most `ℓ` blocks per query, its left-or-right
advantage is at most `2 * K ^ 2 / 2 ^ n`. -/
theorem advantage_ctrCpaGame_randomFunction_le
    (counter : BitString n → ℕ → BitString n) (ℓ : ℕ) {adversary : BlockModeAdversary n} {K : ℕ}
    (h : OracleComp.IsCostBounded (blockModeCost ℓ) adversary K)
    (hintra : ∀ iv i j, i < ℓ → j < ℓ → i ≠ j → counter iv i ≠ counter iv j)
    (hiv : ∀ i < ℓ, Function.Injective (fun iv => counter iv i)) :
    (Game.advantage
        (ctrCpaGame counter (fun f : BitString n → BitString n => f) ℓ false adversary)
        (ctrCpaGame counter (fun f : BitString n → BitString n => f) ℓ true adversary) : ℝ) ≤
      2 * ((K : ℝ) ^ 2 / 2 ^ n) := by
  have e : ∀ b,
      ctrCpaGame counter (fun f : BitString n → BitString n => f) ℓ b adversary =
        ProbComp.eval (PRF.idealExperiment (ctrReduction counter ℓ b adversary)) := fun b => by
    rw [ctrCpaGame_eq_realExperiment]
    rfl
  rw [e, e]
  have h₀ := advantage_idealExperiment_ctrReduction_le counter ℓ false h hintra hiv
  have h₁ := advantage_idealExperiment_ctrReduction_le counter ℓ true h hintra hiv
  refine (advantage_le_two _ (blockModeIdealGame ℓ adversary) _).trans ?_
  linarith

/-- **CTR mode is CPA-secure for a pseudorandom function** ([KatzLindell2020], Section 3.6.3,
Theorem 3.33, p. 93): if `adversary` asks at most `K` blocks in total and at most `ℓ` blocks per
query, its left-or-right advantage against CTR mode with keyed function `F` is at most the PRF
advantages of the two reductions `ctrReduction counter ℓ false adversary` and
`ctrReduction counter ℓ true adversary` (each making at most `K` queries by
`isQueryBounded_ctrReduction`) plus `2 * K ^ 2 / 2 ^ n`. -/
theorem advantage_ctrCpaGame_le {Key : Type} (counter : BitString n → ℕ → BitString n)
    [Fintype Key] [Nonempty Key] (F : Key → BitString n → BitString n) (ℓ : ℕ)
    {adversary : BlockModeAdversary n} {K : ℕ}
    (h : OracleComp.IsCostBounded (blockModeCost ℓ) adversary K)
    (hintra : ∀ iv i j, i < ℓ → j < ℓ → i ≠ j → counter iv i ≠ counter iv j)
    (hiv : ∀ i < ℓ, Function.Injective (fun iv => counter iv i)) :
    (Game.advantage (ctrCpaGame counter F ℓ false adversary)
        (ctrCpaGame counter F ℓ true adversary) : ℝ) ≤
      PRF.advantage F (ctrReduction counter ℓ false adversary) +
        PRF.advantage F (ctrReduction counter ℓ true adversary) + 2 * ((K : ℝ) ^ 2 / 2 ^ n) := by
  rw [ctrCpaGame_eq_realExperiment, ctrCpaGame_eq_realExperiment]
  have h₀ := advantage_idealExperiment_ctrReduction_le counter ℓ false h hintra hiv
  have h₁ := advantage_idealExperiment_ctrReduction_le counter ℓ true h hintra hiv
  refine (advantage_le_four _
    (ProbComp.eval (PRF.idealExperiment (ctrReduction counter ℓ false adversary)))
    (blockModeIdealGame ℓ adversary)
    (ProbComp.eval (PRF.idealExperiment (ctrReduction counter ℓ true adversary))) _).trans ?_
  linarith

/-- Canonical modular-addition counter schedule `iv + i mod 2 ^ n` ([KatzLindell2020], Figure 3.9),
via `BitString.equivFin`. -/
@[expose]
def ctrModCounter (iv : BitString n) (i : ℕ) : BitString n :=
  (BitString.equivFin n).symm ⟨((BitString.equivFin n iv).val + i) % 2 ^ n,
    Nat.mod_lt _ (pow_pos (by decide) n)⟩

/-- For every offset `i`, `ctrModCounter · i` is injective on the initialization vector `iv`. -/
theorem ctrModCounter_injective_left (i : ℕ) :
    Function.Injective (fun iv : BitString n => ctrModCounter iv i) := by
  intro iv₁ iv₂ h
  have hv := congrArg (fun x => (BitString.equivFin n x).val) h
  simp only [ctrModCounter, Equiv.apply_symm_apply] at hv
  have hmod : (BitString.equivFin n iv₁).val ≡ (BitString.equivFin n iv₂).val [MOD 2 ^ n] :=
    Nat.ModEq.add_right_cancel' i hv
  have heq : (BitString.equivFin n iv₁).val = (BitString.equivFin n iv₂).val := by
    rw [← Nat.mod_eq_of_lt (BitString.equivFin n iv₁).isLt,
      ← Nat.mod_eq_of_lt (BitString.equivFin n iv₂).isLt]
    exact hmod
  exact (BitString.equivFin n).injective (Fin.ext heq)

/-- Whenever `ℓ ≤ 2 ^ n`, distinct offsets below `ℓ` yield distinct `ctrModCounter iv i` blocks. -/
theorem ctrModCounter_injOn {ℓ : ℕ} (hℓ : ℓ ≤ 2 ^ n) (iv : BitString n)
    {i j : ℕ} (hi : i < ℓ) (hj : j < ℓ) (hij : i ≠ j) :
    ctrModCounter iv i ≠ ctrModCounter iv j := by
  intro h
  apply hij
  have hv := congrArg (fun x => (BitString.equivFin n x).val) h
  simp only [ctrModCounter, Equiv.apply_symm_apply] at hv
  have hmod : i ≡ j [MOD 2 ^ n] := Nat.ModEq.add_left_cancel' (BitString.equivFin n iv).val hv
  rw [← Nat.mod_eq_of_lt (lt_of_lt_of_le hi hℓ), ← Nat.mod_eq_of_lt (lt_of_lt_of_le hj hℓ)]
  exact hmod

/-- Modular CTR mode with a uniform random function when `ℓ ≤ 2 ^ n`. -/
theorem advantage_ctrCpaGame_ctrModCounter_randomFunction_le {ℓ : ℕ} (hℓ : ℓ ≤ 2 ^ n)
    {adversary : BlockModeAdversary n} {K : ℕ}
    (h : OracleComp.IsCostBounded (blockModeCost ℓ) adversary K) :
    (Game.advantage
        (ctrCpaGame ctrModCounter (fun f : BitString n → BitString n => f) ℓ false adversary)
        (ctrCpaGame ctrModCounter (fun f : BitString n → BitString n => f) ℓ true adversary) :
        ℝ) ≤
      2 * ((K : ℝ) ^ 2 / 2 ^ n) :=
  advantage_ctrCpaGame_randomFunction_le ctrModCounter ℓ h
    (fun iv _ _ hi hj hij => ctrModCounter_injOn hℓ iv hi hj hij)
    (fun i _ => ctrModCounter_injective_left i)

/-- Modular CTR mode is CPA-secure for any pseudorandom function `F` whenever `ℓ ≤ 2 ^ n`
([KatzLindell2020], Section 3.6.3, Theorem 3.33). -/
theorem advantage_ctrCpaGame_ctrModCounter_le {Key : Type} [Fintype Key] [Nonempty Key]
    (F : Key → BitString n → BitString n) {ℓ : ℕ} (hℓ : ℓ ≤ 2 ^ n)
    {adversary : BlockModeAdversary n} {K : ℕ}
    (h : OracleComp.IsCostBounded (blockModeCost ℓ) adversary K) :
    (Game.advantage (ctrCpaGame ctrModCounter F ℓ false adversary)
        (ctrCpaGame ctrModCounter F ℓ true adversary) : ℝ) ≤
      PRF.advantage F (ctrReduction ctrModCounter ℓ false adversary) +
        PRF.advantage F (ctrReduction ctrModCounter ℓ true adversary) + 2 * ((K : ℝ) ^ 2 / 2 ^ n) :=
  advantage_ctrCpaGame_le ctrModCounter F ℓ h
    (fun iv _ _ hi hj hij => ctrModCounter_injOn hℓ iv hi hj hij)
    (fun i _ => ctrModCounter_injective_left i)

end Cslib.Crypto
