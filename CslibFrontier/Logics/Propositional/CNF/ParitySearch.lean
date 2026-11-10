/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Enumeration
public import CslibFrontier.Foundations.Data.BitString.List.Binary
public import CslibFrontier.Logics.Propositional.CNF.KWiseIndependent
public import CslibFrontier.Logics.Propositional.CNF.ModelCount
public import CslibFrontier.Logics.Propositional.CNF.UnsatVal
public import CslibFrontier.Probability.BitString.AffineHash.ThreeWise
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Log
import CslibFrontier.Foundations.Data.Nat.PowClog

/-!
# Searching a three-wise independent sample space for MAX-SAT

Number the variables of a list `vs` by their positions `j < n = |vs|`, and let `d = ⌈log₂ n⌉`. A
seed `t ∈ {0,1}^(d+1)` gives the variable at position `j` the value `t ⬝ (1, bin_d(j))` over
`GF(2)`, where `bin_d(j)` are the `d` low binary digits of `j`
(`Cslib.Logic.PL.paritySample_ofFn`). Over a uniformly random seed these values are three-wise
independent and uniform: the family `x ↦ t ⬝ (1, x)` on `{0,1}^d` is the one-row Boolean affine
hash family (`Cslib.BitString.LinearHash.isKWiseIndependentHash_dotProduct_cons_true`), and the
variables have distinct binary numbers. This is the case `k = 3` of the small sample spaces of
`k`-wise independent bits of Alon, Babai and Itai [AlonBabaiItai1986]; it has `2 ^ (d + 1) < 4 n`
points (`Cslib.Logic.PL.length_parityCandidates_lt`).

By `Cslib.Logic.PL.exists_two_pow_mul_countUnsat_le`, if every clause of `φ` has at least
`k ≤ 3` distinct literals and `vs` lists the variables of `φ`, one of the seeds falsifies at most
`2 ^ -k` of the clauses (`Cslib.Logic.PL.exists_mem_parityCandidates_two_pow_mul_countUnsat_le`).
The candidate assignments, as the lists `Cslib.Logic.PL.parityCandidates vs` of variables set to
`true`, depend only on `vs` and not on the clauses: the same `< 4 n` assignments serve every
formula on these variables. The deterministic algorithm `Cslib.Logic.PL.paritySearch` tries them
all on the distinct variables of `φ` and keeps one falsifying the fewest clauses; it satisfies at
least `7 / 8` of the clauses of every formula with three distinct variables per clause
(`Cslib.Logic.PL.CNF.IsExactThreeDistinct.eight_mul_countUnsat_paritySearchAssignment_le`). This is
the guarantee of Johnson's algorithm (`Cslib.Logic.PL.johnson`), obtained by exhaustive search of a
small sample space instead of the method of conditional expectations
[Alon and Spencer, Section 16.2][AlonSpencer2016].

The polynomial running time is proved in
`CslibFrontier.Logics.Propositional.CNF.ParitySearch.PolyTime`.

## Main definitions

* `Cslib.Logic.PL.paritySample`: the value a seed gives a variable.
* `Cslib.Logic.PL.parityCandidates`: the assignments of the sample space, as lists of variables
  set to `true`.
* `Cslib.Logic.PL.betterCandidate`, `Cslib.Logic.PL.paritySearch`,
  `Cslib.Logic.PL.paritySearchAssignment`: exhaustive search of the sample space.

## Main results

* `Cslib.Logic.PL.length_parityCandidates`, `Cslib.Logic.PL.length_parityCandidates_lt`: the
  sample space has `2 ^ (⌈log₂ n⌉ + 1) < 4 n` points.
* `Cslib.Logic.PL.exists_mem_parityCandidates_two_pow_mul_countUnsat_le`: some point of the sample
  space falsifies at most `2 ^ -k` of the clauses when every clause has `k ≤ 3` distinct literals.
* `Cslib.Logic.PL.two_pow_mul_countUnsat_paritySearchAssignment_le`,
  `Cslib.Logic.PL.CNF.IsExactThreeDistinct.eight_mul_countUnsat_paritySearchAssignment_le`,
  `Cslib.Logic.PL.two_mul_countUnsat_paritySearchAssignment_le`: the guarantees of the search.
* `Cslib.Logic.PL.CNF.IsExactThreeDistinct.seven_div_eight_mul_le_paritySearchAssignment`: the
  `7 / 8` approximation ratio against `1 - unsatVal`.

## References

* [N. Alon, L. Babai, A. Itai, *A fast and simple randomized parallel algorithm for the maximal
  independent set problem*][AlonBabaiItai1986]
* [N. Alon, J. H. Spencer, *The Probabilistic Method*, Section 16.2][AlonSpencer2016]
-/

public section

namespace Cslib.Logic.PL

open Cslib.Probability Cslib.BitString

variable {V : Type*} [DecidableEq V]

/-! ### The sample space -/

/-- The value that the seed `t ∈ {0,1}^(d+1)` gives the variable at position `j` of `vs`: the
parity of the bits of `t` selected by `1` followed by the `d` low binary digits of `j`. -/
@[expose] def paritySample (vs : List V) (seed : List Bool) (v : V) : Bool :=
  ((true :: lowBits (seed.length - 1) (vs.idxOf v)).zipWith Bool.and seed).foldl Bool.xor false

/-- The points of the sample space for the variables `vs`: for each seed of `⌈log₂ |vs|⌉ + 1`
bits, the variables of `vs` that it sets to `true`. -/
@[expose] def parityCandidates (vs : List V) : List (List V) :=
  (enumList (Nat.clog 2 vs.length + 1)).map fun seed => vs.filter (paritySample vs seed)

/-- Of the current choice `best` and a candidate `T`, both lists of variables set to `true`, the
one falsifying fewer clauses of `φ`, keeping `best` on ties. -/
@[expose] def betterCandidate (φ : CNF V) (best T : List V) : List V :=
  if φ.countUnsat (fun v => decide (v ∈ T)) < φ.countUnsat (fun v => decide (v ∈ best)) then T
  else best

/-- **Exhaustive search of the three-wise independent sample space**: the point of the sample space
for the distinct variables of `φ` that falsifies the fewest clauses, as the list of variables set to
`true`. The search starts from the all-`false` assignment, which is itself the point of the zero
seed. -/
@[expose] def paritySearch (φ : CNF V) : List V :=
  (parityCandidates φ.distinctVars).foldl (betterCandidate φ) []

/-- The assignment computed by `Cslib.Logic.PL.paritySearch`. -/
@[expose] def paritySearchAssignment (φ : CNF V) (v : V) : Bool :=
  decide (v ∈ paritySearch φ)

/-- The sample space has one point per seed. -/
@[simp] theorem length_parityCandidates (vs : List V) :
    (parityCandidates vs).length = 2 ^ (Nat.clog 2 vs.length + 1) := by
  simp [parityCandidates]

/-- **The sample space is small**: fewer than `4 n` points for `n ≥ 1` variables. -/
theorem length_parityCandidates_lt {vs : List V} (hvs : vs ≠ []) :
    (parityCandidates vs).length < 4 * vs.length := by
  rw [length_parityCandidates]
  have hlt := Nat.pow_clog_lt_mul Nat.one_lt_two (List.length_pos_iff.2 hvs).ne'
  rw [pow_succ]
  omega

/-! ### Binary positions -/

/-- On a seed of `d + 1` bits, `Cslib.Logic.PL.paritySample` is the dot product of the seed with
`1` followed by the `d` low binary digits of the position. -/
theorem paritySample_ofFn {d : ℕ} (vs : List V) (t : BitString (d + 1)) (v : V) :
    paritySample vs (List.ofFn t) v =
      t ⬝ᵥ Fin.cons true fun i : Fin d => (vs.idxOf v).testBit i := by
  rw [paritySample, List.length_ofFn, Nat.add_sub_cancel, lowBits_eq_ofFn, ← List.ofFn_cons,
    ← dotProduct_eq_foldl, dotProduct_comm]

/-- Distinct variables of `vs` have distinct `d`-digit binary positions when `|vs| ≤ 2 ^ d`. -/
private theorem testBit_idxOf_injOn {d : ℕ} {vs : List V} (hd : vs.length ≤ 2 ^ d)
    {v w : V} (hv : v ∈ vs) (hw : w ∈ vs)
    (h : (fun i : Fin d => (vs.idxOf v).testBit i) = fun i : Fin d => (vs.idxOf w).testBit i) :
    v = w := by
  have hv' := (List.idxOf_lt_length_of_mem hv).trans_le hd
  have hw' := (List.idxOf_lt_length_of_mem hw).trans_le hd
  refine (List.idxOf_inj hv).1 (Nat.eq_of_testBit_eq fun i => ?_)
  rcases Nat.lt_or_ge i d with hi | hi
  · exact congrFun h ⟨i, hi⟩
  · rw [Nat.testBit_lt_two_pow (hv'.trans_le (Nat.pow_le_pow_right (by norm_num) hi)),
      Nat.testBit_lt_two_pow (hw'.trans_le (Nat.pow_le_pow_right (by norm_num) hi))]

/-! ### Correctness -/

/-- **A good point of the sample space**: if `vs` contains the variables of `φ` and every clause
has at least `k ≤ 3` distinct literals, some point of the sample space for `vs` falsifies at most
`2 ^ -k` of the clauses. -/
theorem exists_mem_parityCandidates_two_pow_mul_countUnsat_le {k : ℕ} (hk3 : k ≤ 3)
    {φ : CNF V} {vs : List V} (hvs : ∀ v ∈ φ.vars, v ∈ vs)
    (hk : ∀ c ∈ φ, k ≤ c.toFinset.card) :
    ∃ T ∈ parityCandidates vs, 2 ^ k * φ.countUnsat (fun v => decide (v ∈ T)) ≤ φ.length := by
  obtain ⟨d, hd'⟩ : ∃ d, Nat.clog 2 vs.length = d := ⟨_, rfl⟩
  have hd : vs.length ≤ 2 ^ d := hd' ▸ Nat.le_pow_clog (by norm_num) _
  obtain ⟨t, ht⟩ := exists_two_pow_mul_countUnsat_le
    ((LinearHash.isKWiseIndependentHash_dotProduct_cons_true d).mono hk3)
    (e := fun v (i : Fin d) => (vs.idxOf v).testBit i)
    (fun v hv w hw hvw => testBit_idxOf_injOn hd (hvs v hv) (hvs w hw) hvw) hk
  refine ⟨vs.filter (paritySample vs (List.ofFn t)),
    List.mem_map.2 ⟨List.ofFn t, by simp [hd'], rfl⟩, ?_⟩
  rw [CNF.countUnsat_congr (τ := fun v => t ⬝ᵥ Fin.cons true fun i : Fin d =>
    (vs.idxOf v).testBit i) fun v hv => by
      rw [← paritySample_ofFn]
      simp [hvs v hv]]
  exact ht

/-- Folding `Cslib.Logic.PL.betterCandidate` finds a list falsifying no more clauses than the
starting list and than every candidate. -/
theorem countUnsat_foldl_betterCandidate_le (φ : CNF V) (cands : List (List V)) (init : List V) :
    φ.countUnsat (fun v => decide (v ∈ cands.foldl (betterCandidate φ) init)) ≤
        φ.countUnsat (fun v => decide (v ∈ init)) ∧
      ∀ T ∈ cands, φ.countUnsat (fun v => decide (v ∈ cands.foldl (betterCandidate φ) init)) ≤
        φ.countUnsat (fun v => decide (v ∈ T)) := by
  induction cands generalizing init with
  | nil => exact ⟨le_rfl, fun _ h => by simp at h⟩
  | cons T cands ih =>
    obtain ⟨h1, h2⟩ := ih (betterCandidate φ init T)
    have hstep : φ.countUnsat (fun v => decide (v ∈ betterCandidate φ init T)) ≤
          φ.countUnsat (fun v => decide (v ∈ init)) ∧
        φ.countUnsat (fun v => decide (v ∈ betterCandidate φ init T)) ≤
          φ.countUnsat (fun v => decide (v ∈ T)) := by
      unfold betterCandidate
      split <;> omega
    refine ⟨h1.trans hstep.1, fun T' hT' => ?_⟩
    rcases List.mem_cons.1 hT' with rfl | hT'
    · exact h1.trans hstep.2
    · exact h2 T' hT'

/-- **Correctness of the search**: if every clause of `φ` has at least `k ≤ 3` distinct literals,
`Cslib.Logic.PL.paritySearch` falsifies at most `2 ^ -k` of the clauses. -/
theorem two_pow_mul_countUnsat_paritySearchAssignment_le {k : ℕ} (hk3 : k ≤ 3) {φ : CNF V}
    (hk : ∀ c ∈ φ, k ≤ c.toFinset.card) :
    2 ^ k * φ.countUnsat (paritySearchAssignment φ) ≤ φ.length := by
  obtain ⟨T, hT, hTk⟩ := exists_mem_parityCandidates_two_pow_mul_countUnsat_le hk3
    (vs := φ.distinctVars) (fun v hv => CNF.mem_distinctVars.2 hv) hk
  exact (Nat.mul_le_mul_left _ ((countUnsat_foldl_betterCandidate_le φ _ []).2 T hT)).trans hTk

/-- **The `7 / 8` guarantee**: on a formula with three distinct variables per clause,
`Cslib.Logic.PL.paritySearch` falsifies at most `1 / 8` of the clauses. -/
theorem CNF.IsExactThreeDistinct.eight_mul_countUnsat_paritySearchAssignment_le {φ : CNF V}
    (hφ : φ.IsExactThreeDistinct) : 8 * φ.countUnsat (paritySearchAssignment φ) ≤ φ.length :=
  two_pow_mul_countUnsat_paritySearchAssignment_le (k := 3) le_rfl fun _ hc =>
    (hφ.card_toFinset_eq hc).ge

/-- **The `1 / 2` guarantee**: on a formula without empty clauses, `Cslib.Logic.PL.paritySearch`
falsifies at most half of the clauses. -/
theorem two_mul_countUnsat_paritySearchAssignment_le {φ : CNF V} (hφ : ∀ c ∈ φ, c ≠ []) :
    2 * φ.countUnsat (paritySearchAssignment φ) ≤ φ.length :=
  two_pow_mul_countUnsat_paritySearchAssignment_le (k := 1) (by norm_num) fun c hc =>
    Finset.one_le_card.2 ⟨_, List.mem_toFinset.2 (List.head_mem (hφ c hc))⟩

/-- **The `7 / 8` approximation ratio** for MAX-E3SAT with three distinct variables per clause:
`Cslib.Logic.PL.paritySearch` satisfies at least `7 / 8` times the largest proportion of the clauses
that an assignment satisfies. -/
theorem CNF.IsExactThreeDistinct.seven_div_eight_mul_le_paritySearchAssignment {φ : CNF V}
    (hφ : φ.IsExactThreeDistinct) :
    7 / 8 * (1 - φ.unsatVal) ≤
      1 - (φ.countUnsat (paritySearchAssignment φ) : ℝ) / φ.length := by
  have h := CNF.one_sub_inv_two_pow_mul_le_of_two_pow_mul_countUnsat_le (k := 3)
    hφ.eight_mul_countUnsat_paritySearchAssignment_le
  rwa [show (1 : ℝ) - 2⁻¹ ^ 3 = 7 / 8 by norm_num] at h

end Cslib.Logic.PL
