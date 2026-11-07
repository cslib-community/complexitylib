/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.MaxSAT.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolynomialQueries
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
import Complexity.Foundations.Data.Nat.SqrtLog.Shifted
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Exact MAX-SAT score distributions and optimum

The threshold counter gives the number of assignments satisfying at least `q` clauses. Querying
all cutoffs from `0` through `m + 1`, for `m` clauses, gives the exact score distribution by
adjacent differences. The number of positive threshold counts, minus one, is the exact optimum.
Repeated and empty clauses retain their original contribution to the score.

Both outputs have native algorithms using
`2 ^ O(N / √log N) poly(L)` time and polynomial space, where `N` is literal occurrences plus
clauses and `L` is the complete encoded input length. The generic native query and postprocessing
theorems preserve the threshold counter's exponential factor. A bound in the declared variable
count requires a density hypothesis; this module does not discard clauses or multiplicities.

## Main results

* `MaxSAT.histogramFromCounts_thresholdCounts`: adjacent differences recover every exact count.
* `MaxSAT.optimumFromCounts_thresholdCounts`: positive threshold counts recover the optimum.
* `MaxSAT.exists_histogram_algorithm`, `MaxSAT.exists_optimum_algorithm`: native resource bounds.
* `MaxSAT.exists_sparse_histogram_algorithm`, `MaxSAT.exists_sparse_optimum_algorithm`:
  the rate in declared variables under fixed width and density bounds.
-/

@[expose] public section

namespace Cslib.Complexity.MaxSAT

open Cslib.Logic.PL Turing.MultiTapeTM

/-- Number of assignments satisfying exactly `q` clauses. -/
def exactCount (F : Instance) (q : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : BitString F.1 => score F x = q)).card

/-- The complete score distribution, including the zero-score coefficient. -/
def histogram (F : Instance) : List ℕ :=
  (List.range (F.2.length + 1)).map (exactCount F)

/-- Maximum number of simultaneously satisfied clauses. -/
def optimum (F : Instance) : ℕ := Finset.univ.sup (score F)

/-- Threshold counts with one trailing zero at cutoff `m + 1`. -/
def thresholdCounts (F : Instance) : List ℕ :=
  (List.range (F.2.length + 2)).map (thresholdCount F)

/-- Adjacent differences of a threshold-count list. -/
def histogramFromCounts (counts : List ℕ) : List ℕ :=
  (counts.zip counts.tail).map (fun p => p.1 - p.2)

/-- The number of feasible score cutoffs, minus the always-feasible zero cutoff. -/
def optimumFromCounts (counts : List ℕ) : ℕ :=
  counts.countP (fun n => decide (0 < n)) - 1

/-- Differences of consecutive tail counts give the exact score count. -/
theorem thresholdCount_sub (F : Instance) (q : ℕ) :
    thresholdCount F q - thresholdCount F (q + 1) = exactCount F q := by
  have hsub : (Finset.univ.filter (fun x : BitString F.1 => q + 1 ≤ score F x)) ⊆
      Finset.univ.filter (fun x : BitString F.1 => q ≤ score F x) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    omega
  have heq : (Finset.univ.filter (fun x : BitString F.1 => q ≤ score F x)) \
      (Finset.univ.filter (fun x : BitString F.1 => q + 1 ≤ score F x)) =
      Finset.univ.filter (fun x : BitString F.1 => score F x = q) := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  simpa only [thresholdCount, exactCount, heq] using
    (Finset.card_sdiff_of_subset hsub).symm

/-- Adjacent differences preserve the increasing order of score indices. -/
theorem histogramFromCounts_range (f : ℕ → ℕ) (m : ℕ) :
    histogramFromCounts ((List.range (m + 1)).map f) =
      (List.range m).map (fun q => f q - f (q + 1)) := by
  apply List.ext_getElem
  · simp [histogramFromCounts]
  · intro i hi hj
    simp [histogramFromCounts]

/-- The returned histogram contains every exact assignment count. -/
theorem histogramFromCounts_thresholdCounts (F : Instance) :
    histogramFromCounts (thresholdCounts F) = histogram F := by
  simpa only [thresholdCounts, histogram, Nat.add_assoc, thresholdCount_sub] using
    histogramFromCounts_range (thresholdCount F) (F.2.length + 1)

/-- Every score is at most the optimum. -/
theorem score_le_optimum (F : Instance) (x : BitString F.1) : score F x ≤ optimum F :=
  Finset.le_sup (Finset.mem_univ x)

/-- The optimum is attained by an assignment, including when there are no variables. -/
theorem exists_score_eq_optimum (F : Instance) : ∃ x : BitString F.1, score F x = optimum F := by
  obtain ⟨x, _, hx⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (BitString F.1))
    Finset.univ_nonempty (score F)
  exact ⟨x, hx.symm⟩

/-- The optimum is at most the number of clauses. -/
theorem optimum_le (F : Instance) : optimum F ≤ F.2.length :=
  Finset.sup_le (fun x _ => score_le F x)

/-- The feasible thresholds are exactly the integers from zero through the optimum. -/
theorem thresholdCount_pos_iff_le_optimum (F : Instance) (q : ℕ) :
    0 < thresholdCount F q ↔ q ≤ optimum F := by
  rw [thresholdCount_pos_iff]
  constructor
  · rintro ⟨x, hx⟩
    exact hx.trans (score_le_optimum F x)
  · intro hq
    obtain ⟨x, hx⟩ := exists_score_eq_optimum F
    exact ⟨x, hx ▸ hq⟩

private theorem countP_range_le (m q : ℕ) :
    (List.range m).countP (fun j => decide (j ≤ q)) = min m (q + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.countP_append, ih]
    by_cases h : m ≤ q <;> simp [h] <;> omega

/-- Counting positive threshold counts returns the exact maximum score. -/
theorem optimumFromCounts_thresholdCounts (F : Instance) :
    optimumFromCounts (thresholdCounts F) = optimum F := by
  simp only [optimumFromCounts, thresholdCounts, List.countP_map, Function.comp_def,
    thresholdCount_pos_iff_le_optimum]
  rw [countP_range_le, Nat.min_eq_right (by have := optimum_le F; omega)]
  omega

/-- Differences are polynomial-time on binary counts. -/
theorem histogramFromCounts_polyTime :
    ComputableInPolyTime histogramFromCounts (encList encNat) (encList encNat) := by
  have hsub := ComputableInPolyTime.binary_sub'
    (ComputableInPolyTime.fst encNat encNat) (ComputableInPolyTime.snd encNat encNat)
  exact (ComputableInPolyTime.map hsub).comp
    ((ComputableInPolyTime.zip encNat encNat).comp
      (ComputableInPolyTime.id'.prod (ComputableInPolyTime.tail (encA := encNat))))

/-- Recovering the optimum is polynomial-time in the list of binary counts. -/
theorem optimumFromCounts_polyTime :
    ComputableInPolyTime optimumFromCounts (encList encNat) encNat := by
  have hp : ComputableInPolyTime (fun p : List ℕ × ℕ => decide (0 < p.2))
      (encPair (encList encNat) encNat) encBool :=
    ComputableInPolyTime.binary_lt' (ComputableInPolyTime.const 0)
      (ComputableInPolyTime.snd _ _)
  have hn : ComputableInPolyTime
      (fun counts : List ℕ => counts.countP (fun n => decide (0 < n)))
      (encList encNat) encUnary :=
    ComputableInPolyTime.countPWithInput (encA := encNat) ComputableInPolyTime.id' hp
  exact ComputableInPolyTime.unary_to_binary.comp
    (ComputableInPolyTime.unary_sub' hn (ComputableInPolyTime.const 1))

/-! ### Native runtime bounds -/

/-- The complete threshold list is computed at the same contraction rate. The number of queries
and the materialized answer list contribute only polynomial factors. -/
theorem exists_thresholdCounts_algorithm :
    ∃ A d : ℕ, ComputableInO thresholdCounts encInstance (encList encNat)
      (fun F => 2 ^ (A * (workSize F + 1) / Nat.sqrt (Nat.log 2 (workSize F + 2))) *
        ((encInstance F).length + 1) ^ d)
      (fun F => ((encInstance F).length + 1) ^ d) := by
  obtain ⟨count, A, e, b, hcount, hc⟩ := exists_thresholdCounter
  have he : count = fun p => thresholdCount p.1 p.2 := funext hcount
  rw [he] at hc
  have hm : ComputableInPolyTime (fun F : Instance => F.2.length) encInstance encUnary :=
    (ComputableInPolyTime.length_list (encList (encPair encNat encBool))).comp
      (ComputableInPolyTime.snd encUnary encCNF)
  have hq := ComputableInPolyTime.range.comp
    (ComputableInPolyTime.unary_add' hm (ComputableInPolyTime.const 2))
  obtain ⟨d, hd⟩ := ComputableInO.polynomial_queries
    (T := fun F => 2 ^ (A * (workSize F + 1) / Nat.sqrt (Nat.log 2 (workSize F + 2))))
    (e := e) (b := b) hc hq (fun _ => Nat.one_le_two_pow)
  exact ⟨A, d, hd⟩

/-- A native algorithm returns all exact score counts, in increasing order from `0` through `m`,
within the threshold counter's exponential rate and polynomial space. -/
theorem exists_histogram_algorithm :
    ∃ A d : ℕ, ComputableInO histogram encInstance (encList encNat)
      (fun F => 2 ^ (A * (workSize F + 1) / Nat.sqrt (Nat.log 2 (workSize F + 2))) *
        ((encInstance F).length + 1) ^ d)
      (fun F => ((encInstance F).length + 1) ^ d) := by
  obtain ⟨A, d, hd⟩ := exists_thresholdCounts_algorithm
  obtain ⟨e, he⟩ := hd.polynomial_postprocessing histogramFromCounts_polyTime
    (fun _ => Nat.one_le_two_pow)
  refine ⟨A, e, he.of_enc_eq fun F => ?_⟩
  rw [Function.comp_apply, histogramFromCounts_thresholdCounts]

/-- A native algorithm returns the exact MAX-SAT optimum at the contraction rate, with
polynomial space. This is uniform in clause width and in the input's declared variable count. -/
theorem exists_optimum_algorithm :
    ∃ A d : ℕ, ComputableInO optimum encInstance encNat
      (fun F => 2 ^ (A * (workSize F + 1) / Nat.sqrt (Nat.log 2 (workSize F + 2))) *
        ((encInstance F).length + 1) ^ d)
      (fun F => ((encInstance F).length + 1) ^ d) := by
  obtain ⟨A, d, hd⟩ := exists_thresholdCounts_algorithm
  obtain ⟨e, he⟩ := hd.polynomial_postprocessing optimumFromCounts_polyTime
    (fun _ => Nat.one_le_two_pow)
  refine ⟨A, e, he.of_enc_eq fun F => ?_⟩
  rw [Function.comp_apply, optimumFromCounts_thresholdCounts]

/-! ### Sparse fixed-width instances -/

/-- Width at most `k` and at most `c (n+1)` clauses on `n` declared variables. References retain
the total evaluation convention of `Instance`; well-formed instances have all references below
`n`. Both resource parameters are fixed before the input. -/
abbrev SparseInstance (k c : ℕ) :=
  {F : Instance // (∀ clause ∈ F.2, clause.length ≤ k) ∧ F.2.length ≤ c * (F.1 + 1)}

/-- The declared variable count of a sparse instance. -/
abbrev SparseInstance.numVars {k c : ℕ} : SparseInstance k c → ℕ
  | ⟨(numVars, _), _⟩ => numVars

/-- Sparse instances use the same complete encoding as their underlying formulas. -/
def encSparseInstance (k c : ℕ) : SparseInstance k c ↪ List Bool :=
  (Function.Embedding.subtype _).trans encInstance

/-- Width and density give an explicit linear bound on the parameter in the exponent. -/
theorem sparse_workSize_le {k c : ℕ} (F : SparseInstance k c) :
    workSize F.1 ≤ (k + 1) * c * F.numVars + (k + 1) * c := by
  calc workSize F.1 ≤ (k + 1) * F.1.2.length := workSize_le_of_width k F.1 F.2.1
    _ ≤ (k + 1) * (c * (F.1.1 + 1)) := Nat.mul_le_mul_left _ F.2.2
    _ = (k + 1) * c * F.1.1 + (k + 1) * c := by ring

private theorem sparse_algorithm {β : Type} {enc : β ↪ List Bool} {f : Instance → β}
    {A d : ℕ} (k c : ℕ)
    (hf : ComputableInO f encInstance enc
      (fun F => 2 ^ (A * (workSize F + 1) / Nat.sqrt (Nat.log 2 (workSize F + 2))) *
        ((encInstance F).length + 1) ^ d)
      (fun F => ((encInstance F).length + 1) ^ d)) :
    ComputableInO (fun F : SparseInstance k c => f F.1) (encSparseInstance k c) enc
      (fun F => 2 ^ (A * (8 * ((k + 1) * c) + 14) * (F.numVars + 1) /
        Nat.sqrt (Nat.log 2 (F.numVars + 2))) * ((encSparseInstance k c F).length + 1) ^ d)
      (fun F => ((encSparseInstance k c F).length + 1) ^ d) := by
  have h := hf.of_encIn_eq (encD := encSparseInstance k c) Subtype.val (fun _ => rfl)
  refine h.mono_le (fun F => ?_) (fun _ => le_rfl)
  apply Nat.mul_le_mul_right
  apply Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ))
  exact Nat.mul_succ_div_sqrt_log_two_le (sparse_workSize_le F)

/-- Exact score distributions for sparse MAX-`k`-SAT in `2 ^ O(n / √log n) poly(L)` time and
polynomial space, for fixed width `k` and density `c`. Every one of the `2^n` canonical declared
assignments is counted, including assignments to unused variables. -/
theorem exists_sparse_histogram_algorithm (k c : ℕ) :
    ∃ A d : ℕ, ComputableInO (fun F : SparseInstance k c => histogram F.1)
      (encSparseInstance k c) (encList encNat)
      (fun F => 2 ^ (A * (F.numVars + 1) / Nat.sqrt (Nat.log 2 (F.numVars + 2))) *
        ((encSparseInstance k c F).length + 1) ^ d)
      (fun F => ((encSparseInstance k c F).length + 1) ^ d) := by
  obtain ⟨A, d, h⟩ := exists_histogram_algorithm
  exact ⟨A * (8 * ((k + 1) * c) + 14), d, sparse_algorithm k c h⟩

/-- The exact ordinary clause-count optimum for sparse MAX-`k`-SAT has the same native rate and
polynomial workspace. The input may contain duplicate and empty clauses. -/
theorem exists_sparse_optimum_algorithm (k c : ℕ) :
    ∃ A d : ℕ, ComputableInO (fun F : SparseInstance k c => optimum F.1)
      (encSparseInstance k c) encNat
      (fun F => 2 ^ (A * (F.numVars + 1) / Nat.sqrt (Nat.log 2 (F.numVars + 2))) *
        ((encSparseInstance k c F).length + 1) ^ d)
      (fun F => ((encSparseInstance k c F).length + 1) ^ d) := by
  obtain ⟨A, d, h⟩ := exists_optimum_algorithm
  exact ⟨A * (8 * ((k + 1) * c) + 14), d, sparse_algorithm k c h⟩

end Cslib.Complexity.MaxSAT
