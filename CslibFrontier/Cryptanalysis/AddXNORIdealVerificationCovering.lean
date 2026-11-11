/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORIdealSearchUnion
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import Mathlib.Data.Fin.Tuple.Take

/-!
# Level-specific covering during actual search verification

A single forward verification walk makes at most one query at each layer. Count covered
prefixes through births at their last layer, rather than charging every verification edge.
No frontier-sampler simulation is used.

## Main results

* `Cslib.Cryptanalysis.AddXNOR.IdealChain.VerificationCovering.verified_counts`: one new
  forward birth at each layer, and no new reverse-view forward births, from actual execution.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.VerificationCovering.source_search_rate`: the
  whole planted-search bound with the single verification prefix charged.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.VerificationCovering.source_search_bound`: the
  full source range with covering coefficient `3*T+1` and collision coefficient `18`.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.VerificationCovering.source_theorem_eight_even`:
  literal source Theorem 8 for every even chain length under its remaining exact hypotheses.

The source's odd-length sharp inequality still needs a tighter joint planted-success/guessing
argument. The valid cut coupling is used throughout; no exact law for the source's false
Lemma 10 frontier sampler is claimed. See [WangLvShenZhang2027], Theorem 8, PDF pp. 25–28.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.IdealChain.VerificationCovering

open Probability OracleComp RandomPermutation
open Forest (selected covered_card_le_selected)
open scoped ENNReal

variable {Index Word : Type} [DecidableEq Word]

variable [DecidableEq Index] [Fintype Word] [Nonempty Word]

private theorem answer_counts (P : Index → Bool) (label : Index) (point : Word)
    (old : List (Forest.Record Index Word)) (value : Word)
    (next : List (Forest.Record Index Word))
    (hout : (value, next) ∈ (Ledger.answer (label, .forward point) old).support) :
    (next.filter (selected P)).length ≤ (old.filter (selected P)).length +
      (if P label then 1 else 0) ∧
    ((next.map Forest.Record.reverse).filter (selected P)).length =
      ((old.map Forest.Record.reverse).filter (selected P)).length := by
  simp only [Ledger.answer, PMF.mem_support_map_iff] at hout
  obtain ⟨⟨value, cache⟩, _, he⟩ := hout
  cases he
  simp only [Ledger.update]
  split <;> cases hp : P label <;>
    simp [selected, hp, Forest.Record.reverse]

/-- A real forward walk adds births only at its queried labels. Its reverse view adds no
forward births at all, so it cannot enlarge backward rooted covering on collision-free runs. -/
theorem walk_counts (P : Index → Bool) (labels : List Index) (seed : Word)
    (old : List (Forest.Record Index Word)) (endpoint : Word)
    (next : List (Forest.Record Index Word))
    (hout : (endpoint, next) ∈ (OracleComp.runWith Ledger.answer (walk labels seed) old).support) :
    (next.filter (selected P)).length ≤
        (old.filter (selected P)).length + (labels.filter P).length ∧
      ((next.map Forest.Record.reverse).filter (selected P)).length =
        ((old.map Forest.Record.reverse).filter (selected P)).length := by
  induction labels generalizing seed old with
  | nil =>
    simp only [walk, OracleComp.runWith_pure, PMF.mem_support_pure_iff] at hout
    cases hout
    simp
  | cons label rest ih =>
    rw [walk, OracleComp.runWith_bind, PMF.mem_support_bind_iff] at hout
    obtain ⟨⟨value, middle⟩, hfirst, hrest⟩ := hout
    rw [OracleComp.runWith_query] at hfirst
    have h₁ := answer_counts P label seed old value middle hfirst
    have h₂ := ih value middle hrest
    constructor
    · cases hp : P label <;> simp only [hp, Bool.false_eq_true, ↓reduceIte,
        List.filter_cons, List.length_cons] at h₁ ⊢ <;> omega
    · exact h₂.2.trans h₁.2

/-- The actual verification label list visits each layer at most once. -/
theorem verification_layer_count {q : ℕ} (bits : Operators q) (k : Fin q) :
    ((List.ofFn fun i => (i, bits i)).filter
      (fun label : Label q => decide (label.1 = k))).length ≤ 1 := by
  classical
  have hn : (List.ofFn fun i => (i, bits i)).Nodup :=
    List.nodup_ofFn.mpr (fun _ _ h => (Prod.mk.inj h).1)
  rw [← List.toFinset_card_of_nodup (hn.filter _)]
  apply Finset.card_le_one.mpr
  intro a ha b hb
  simp only [List.mem_toFinset, List.mem_filter, List.mem_ofFn, decide_eq_true_eq] at ha hb
  obtain ⟨⟨i, rfl⟩, hi⟩ := ha
  obtain ⟨⟨j, rfl⟩, hj⟩ := hb
  cases hi
  cases hj
  rfl

/-- The two relevant birth counts after executing the real verifier: at most one additional
forward birth at a selected layer, and no additional reverse-view forward births. -/
theorem verified_counts {q : ℕ} (seed target : Word) (k : Fin q)
    (adversary : Word → Word → ProbOracleComp (Spec q Word) (Operators q))
    (T : ℕ) (hbudget : ProbOracleComp.IsQueryBounded (adversary seed target) T)
    (accepted : Bool) (records : List (Forest.Record (Label q) Word))
    (hout : (accepted, records) ∈ (ProbOracleComp.runWith Ledger.answer
      (verifiedAdversary adversary seed target) []).support) :
    (records.filter (selected (fun label => decide (label.1 = k)))).length ≤ T + 1 ∧
      ∀ P : Label q → Bool,
        ((records.map Forest.Record.reverse).filter (selected P)).length ≤ T := by
  rw [verifiedAdversary, ProbOracleComp.runWith_bind, PMF.mem_support_bind_iff] at hout
  obtain ⟨⟨bits, old⟩, hold, hwalk⟩ := hout
  rw [ProbOracleComp.runWith_bind, PMF.mem_support_bind_iff] at hwalk
  obtain ⟨⟨endpoint, next⟩, hwalk, hpure⟩ := hwalk
  rw [ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff] at hpure
  cases hpure
  rw [ProbOracleComp.runWith_liftRight] at hwalk
  have hsize := Ledger.run_length (adversary seed target) T hbudget bits old hold
  constructor
  · have h := (walk_counts (fun label => decide (label.1 = k)) _ _ _ _ _ hwalk).1
    have hfilter := List.length_filter_le (selected (fun label => decide (label.1 = k))) old
    have hl := verification_layer_count bits k
    dsimp only at h ⊢
    omega
  · intro P
    have h := (walk_counts P _ _ _ _ _ hwalk).2
    rw [h]
    exact (List.length_filter_le _ _).trans (by simpa using hsize)

omit [DecidableEq Index] [Fintype Word] [Nonempty Word] in
/-- Hidden binary covering is bounded by births at its final layer, rather than the size
of the entire ledger. This is a derived cardinality bound for any collision-free ledger. -/
theorem uniform_binary_covered_le_selected {q h : ℕ} (hh : 0 < h)
    (layer : Fin h → Fin q) (initial : Finset Word) (seed : Word) (hs : seed ∈ initial)
    (records : List (Forest.Record (Label q) Word)) (hc : Forest.NoCollision initial records) :
    (PMF.uniformOfFintype (Operators h)).toOuterMeasure
        {word | ∃ endpoint, Forest.Follows records seed (Forest.binaryLabels layer word) endpoint} ≤
      ((records.filter (selected (fun label =>
        decide (label.1 = layer ⟨h - 1, by omega⟩)))).length : ℝ≥0∞) / 2 ^ h := by
  classical
  have hne (word : Operators h) : Forest.binaryLabels layer word ≠ [] := by
    intro he
    have hl := congrArg List.length he
    simp only [Forest.binaryLabels, List.length_ofFn, List.length_nil] at hl
    omega
  have hb := covered_card_le_selected initial seed hs records hc (Forest.binaryLabels layer)
    (Forest.binaryLabels_injective layer) hne
    (fun label => decide (label.1 = layer ⟨h - 1, by omega⟩))
    (fun word stem label he => by
      have hg := congrArg List.getLast? he
      rw [List.getLast?_eq_some_getLast (hne word), List.getLast?_concat] at hg
      simp only [Forest.binaryLabels, List.getLast_ofFn, Option.some.injEq] at hg
      rw [← hg]
      simp)
  rw [Probability.PMF.toOuterMeasure_uniformOfFintype]
  have hcard : Fintype.card (Operators h) = 2 ^ h := by simp [Operators]
  simp only [hcard, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hb) zero_le

/-- At a source cut, the actual verification walk adds at most one forward prefix and no
backward suffixes, not `q` arbitrary forest endpoints on each side. -/
theorem uniform_verified_covering {q : ℕ} (k : Fin q) (hd : 0 < q - (k.val + 1))
    (seed target : Word)
    (adversary : Word → Word → ProbOracleComp (Spec q Word) (Operators q))
    (T : ℕ) (hbudget : ProbOracleComp.IsQueryBounded (adversary seed target) T)
    (accepted : Bool) (records : List (Forest.Record (Label q) Word))
    (hout : (accepted, records) ∈ (ProbOracleComp.runWith Ledger.answer
      (verifiedAdversary adversary seed target) []).support)
    (hc : Forest.NoCollision {seed, target} records) :
    ((PMF.uniformOfFintype (Operators q)).map
      (fun bits => CutBounds.coveredRecords (sourceCut bits k) seed target records)) true ≤
      ((T + 1 : ℕ) : ℝ≥0∞) / 2 ^ (k.val + 1) + T / 2 ^ (q - (k.val + 1)) := by
  classical
  have hn := verified_counts seed target k adversary T hbudget accepted records hout
  let A := fun bits : Operators q => decide
    (∃ endpoint, Forest.Follows records seed
      ((sourceCut bits k).left ++ [(sourceCut bits k).edge]) endpoint)
  let B := fun bits : Operators q => decide
    (∃ endpoint, Forest.Follows (records.map Forest.Record.reverse) target
      (sourceCut bits k).right.reverse endpoint)
  have hf : (PMF.uniformOfFintype (Operators q)).toOuterMeasure
      {bits | ∃ endpoint, Forest.Follows records seed
        ((sourceCut bits k).left ++ [(sourceCut bits k).edge]) endpoint} ≤
      ((T + 1 : ℕ) : ℝ≥0∞) / 2 ^ (k.val + 1) := by
    simp only [Covering.source_front]
    change (PMF.uniformOfFintype (Operators q)).toOuterMeasure
      ((Fin.take (k.val + 1) (by omega)) ⁻¹'
        {bits | ∃ endpoint, Forest.Follows records seed
          (Forest.binaryLabels (fun i => i.castLE (by omega)) bits) endpoint}) ≤ _
    rw [← PMF.toOuterMeasure_map_apply, Covering.uniform_take]
    have hl : ((⟨k.val + 1 - 1, by omega⟩ : Fin (k.val + 1)).castLE (by omega) : Fin q) = k := by
      apply Fin.ext
      simp
    have h := uniform_binary_covered_le_selected (by omega : 0 < k.val + 1)
      (fun i => i.castLE (by omega)) {seed, target} seed
      (Finset.mem_insert_self ..) records hc
    simp only [hl] at h
    apply h.trans
    simp only [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hn.1) zero_le
  have hb : (PMF.uniformOfFintype (Operators q)).toOuterMeasure
      {bits | ∃ endpoint, Forest.Follows (records.map Forest.Record.reverse) target
        (sourceCut bits k).right.reverse endpoint} ≤
      (T : ℝ≥0∞) / 2 ^ (q - (k.val + 1)) := by
    simp only [Covering.source_back]
    change (PMF.uniformOfFintype (Operators q)).toOuterMeasure
      (((Fin.take (q - (k.val + 1)) (by omega)) ∘ (fun bits i => bits i.rev)) ⁻¹'
        {bits | ∃ endpoint, Forest.Follows (records.map Forest.Record.reverse) target
          (Forest.binaryLabels (fun i => (i.castLE (by omega)).rev) bits) endpoint}) ≤ _
    rw [← PMF.toOuterMeasure_map_apply, ← PMF.map_comp,
      Covering.uniform_reverse, Covering.uniform_take]
    have h := uniform_binary_covered_le_selected hd
      (fun i => (i.castLE (by omega)).rev) {seed, target} target
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      (records.map Forest.Record.reverse) ((Forest.noCollision_reverse _ _).mpr hc)
    apply h.trans
    simp only [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hn.2 _)) zero_le
  have hA : ((PMF.uniformOfFintype (Operators q)).map A) true ≤
      ((T + 1 : ℕ) : ℝ≥0∞) / 2 ^ (k.val + 1) := by
    simpa only [A, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
      Set.preimage, Set.mem_singleton_iff, decide_eq_true_eq] using hf
  have hB : ((PMF.uniformOfFintype (Operators q)).map B) true ≤
      (T : ℝ≥0∞) / 2 ^ (q - (k.val + 1)) := by
    simpa only [B, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
      Set.preimage, Set.mem_singleton_iff, decide_eq_true_eq] using hb
  have h := Probability.PMF.map_true_le_add (PMF.uniformOfFintype (Operators q))
    (A := A) (B := B)
    (E := fun bits => CutBounds.coveredRecords (sourceCut bits k) seed target records)
    (fun bits _ hh => by
      simp only [CutBounds.coveredRecords, decide_eq_true_eq] at hh
      simpa only [A, B, decide_eq_true_eq] using hh.2)
  exact h.trans (add_le_add hA hB)

/-- Hidden-word covering averaged over the actual candidate-dependent verifier. The only
premise on the adversary is its syntactic budget, not a traversal or probability contract. -/
theorem uniform_verified_covering_run {q : ℕ} (k : Fin q) (hd : 0 < q - (k.val + 1))
    (seed target : Word)
    (adversary : Word → Word → ProbOracleComp (Spec q Word) (Operators q))
    (T : ℕ) (hbudget : ProbOracleComp.IsQueryBounded (adversary seed target) T) :
    ((PMF.uniformOfFintype (Operators q)).bind fun bits =>
      (ProbOracleComp.runWith Ledger.answer (verifiedAdversary adversary seed target) []).map
        (fun (_, records) =>
          CutBounds.coveredRecords (sourceCut bits k) seed target records)) true ≤
      ((T + 1 : ℕ) : ℝ≥0∞) / 2 ^ (k.val + 1) + T / 2 ^ (q - (k.val + 1)) := by
  classical
  have he : ((PMF.uniformOfFintype (Operators q)).bind fun bits =>
      (ProbOracleComp.runWith Ledger.answer (verifiedAdversary adversary seed target) []).map
        (fun (_, records) => CutBounds.coveredRecords (sourceCut bits k) seed target records)) =
      (ProbOracleComp.runWith Ledger.answer (verifiedAdversary adversary seed target) []).bind
        fun (_, records) => (PMF.uniformOfFintype (Operators q)).map
          (fun bits => CutBounds.coveredRecords (sourceCut bits k) seed target records) := by
    simp only [PMF.map]
    exact PMF.bind_comm _ _ _
  rw [he]
  apply Probability.PMF.bind_apply_le_on_support
  rintro ⟨out, records⟩ hout
  by_cases hc : Forest.NoCollision {seed, target} records
  · exact uniform_verified_covering k hd seed target adversary T hbudget out records hout hc
  · simp [CutBounds.coveredRecords, hc]

/-- The full original planted-search experiment with the verifier's single new prefix.
All source hypotheses are retained, and the hidden reveal's calls are still charged. -/
theorem source_search_rate {q : ℕ} (hq : 3 ≤ q) (m T : ℕ)
    (adversary : Fin (2 ^ m) → Fin (2 ^ m) →
      ProbOracleComp (Spec q (Fin (2 ^ m))) (Operators q))
    (hbudget : ∀ seed target, ProbOracleComp.IsQueryBounded (adversary seed target) T)
    (hT : max q 4 ≤ T) (hlimit : T ≤ 2 ^ (m - 3)) :
    ((plantedSearch adversary) true).toReal ≤
      Collisions.rate (2 ^ m) (T + q + q) +
        (T + 1 : ℕ) / (2 : ℝ) ^ ((q + 1) / 2) +
        (T : ℝ) / 2 ^ (q - (q + 1) / 2) := by
  apply SearchUnion.source_search_rate_of_covering hq m T adversary hbudget hT hlimit (T + 1) T
  intro seed target
  have hd : 0 < q - ((Security.middleIndex q hq).val + 1) := by
    simp only [Security.middleIndex]
    omega
  simpa only [Security.middleIndex, Nat.sub_add_cancel (by omega : 1 ≤ (q + 1) / 2)] using
    uniform_verified_covering_run (Security.middleIndex q hq) hd seed target adversary T
      (hbudget seed target)

/-- Full-range normalization after charging the single verification prefix: the old factor
six becomes `3*T+1`; the actual `T+2*q` collision horizon is unchanged. -/
theorem source_search_bound {q : ℕ} (hq : 3 ≤ q) (m T : ℕ)
    (adversary : Fin (2 ^ m) → Fin (2 ^ m) →
      ProbOracleComp (Spec q (Fin (2 ^ m))) (Operators q))
    (hbudget : ∀ seed target, ProbOracleComp.IsQueryBounded (adversary seed target) T)
    (hT : max q 4 ≤ T) (hlimit : T ≤ 2 ^ (m - 3)) :
    ((plantedSearch adversary) true).toReal ≤
      (3 * T + 1) / 2 ^ ((q + 1) / 2) + 18 * (T : ℝ) ^ 2 / 2 ^ m := by
  have hqT := (le_max_left q 4).trans hT
  have hr := Collisions.rate_le_eighteen (2 ^ m) T (T + q + q)
    ((le_max_right q 4).trans hT) (by omega)
    (Collisions.source_word_budget m T ((le_max_right q 4).trans hT) hlimit)
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hr
  have hs : (q + 1) / 2 = q - (q + 1) / 2 ∨
      (q + 1) / 2 = q - (q + 1) / 2 + 1 := by omega
  have hc := Collisions.covering_fractions_le_three T ((q + 1) / 2)
    (q - (q + 1) / 2) hs
  have hp := source_search_rate hq m T adversary hbudget hT hlimit
  simp only [Nat.cast_add, Nat.cast_one, add_div] at hp
  rw [add_div]
  linarith

private theorem rate_le_ten (N T Q : ℕ) (hT : 12 ≤ T) (hQ : Q ≤ 3 * T)
    (hN : 10 * T ^ 2 ≤ N) : Collisions.rate N Q ≤ 10 * (T : ℝ) ^ 2 / N := by
  have ht : (12 : ℝ) ≤ T := by exact_mod_cast hT
  have hq : (Q : ℝ) ≤ 3 * T := by exact_mod_cast hQ
  have hn : 10 * (T : ℝ) ^ 2 ≤ N := by exact_mod_cast hN
  have htn : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  have hqn : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
  have hnpos : (0 : ℝ) < N := by nlinarith
  have hdpos : (0 : ℝ) < N - Q := by nlinarith
  have hnum : (Q : ℝ) ^ 2 + 3 * Q ≤ 9 * (T : ℝ) ^ 2 + 9 * T := by nlinarith
  have hbase : 0 ≤ ((T : ℝ) - 9) * N - 30 * T ^ 2 := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ T - 12 by linarith) hnpos.le]
  change ((Q : ℝ) ^ 2 + 3 * Q) / (N - Q) ≤ _
  apply (div_le_div_iff₀ hdpos hnpos).mpr
  nlinarith [mul_le_mul_of_nonneg_right hnum hnpos.le,
    mul_nonneg htn hbase, mul_nonneg (sq_nonneg (T : ℝ)) (show 0 ≤ 3 * (T : ℝ) - Q by linarith)]

/-- Literal Theorem 8 for every even source chain length. The one-prefix verification bound
has enough covering slack here; the odd-length joint guessing argument remains separate. -/
theorem source_theorem_eight_even {q : ℕ} (hq : 3 ≤ q) (heven : q % 2 = 0) (m T : ℕ)
    (adversary : Fin (2 ^ m) → Fin (2 ^ m) →
      ProbOracleComp (Spec q (Fin (2 ^ m))) (Operators q))
    (hbudget : ∀ seed target, ProbOracleComp.IsQueryBounded (adversary seed target) T)
    (hT : max q 4 ≤ T) (hlimit : T ≤ 2 ^ (m - 3)) :
    ((plantedSearch adversary) true).toReal ≤
      3 * T / 2 ^ ((q + 1) / 2) + 10 * (T : ℝ) ^ 2 / 2 ^ m + 1 / 2 ^ q := by
  have hqT := (le_max_left q 4).trans hT
  have hT4 := (le_max_right q 4).trans hT
  have hprob : ((plantedSearch adversary) true).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ⊤)
      (PMF.coe_le_one (plantedSearch adversary) true)
  have hnonneg : 0 ≤ 10 * (T : ℝ) ^ 2 / 2 ^ m + 1 / 2 ^ q := by positivity
  by_cases hvacuous : (1 : ℝ) ≤ 3 * T / 2 ^ ((q + 1) / 2) +
      10 * (T : ℝ) ^ 2 / 2 ^ m + 1 / 2 ^ q
  · exact hprob.trans hvacuous
  have hN : 10 * T ^ 2 ≤ 2 ^ m := by
    by_contra hn
    have hn' : (2 : ℝ) ^ m < 10 * (T : ℝ) ^ 2 := by
      exact_mod_cast (show 2 ^ m < 10 * T ^ 2 by omega)
    have hp : (0 : ℝ) < 2 ^ m := by positivity
    have hge : (1 : ℝ) ≤ 10 * (T : ℝ) ^ 2 / 2 ^ m := (le_div_iff₀ hp).mpr (by linarith)
    apply hvacuous
    have hcover : (0 : ℝ) ≤ 3 * T / 2 ^ ((q + 1) / 2) := by positivity
    have hguess : (0 : ℝ) ≤ 1 / 2 ^ q := by positivity
    linarith
  have hbal : q - (q + 1) / 2 = (q + 1) / 2 := by omega
  have hr := source_search_rate hq m T adversary hbudget hT hlimit
  rw [hbal] at hr
  by_cases hlarge : 12 ≤ T
  · have hc := rate_le_ten (2 ^ m) T (T + q + q) hlarge (by omega) hN
    simp only [Nat.cast_pow, Nat.cast_ofNat] at hc
    have hcov : (T + 1 : ℕ) / (2 : ℝ) ^ ((q + 1) / 2) +
        (T : ℝ) / 2 ^ ((q + 1) / 2) ≤ 3 * T / 2 ^ ((q + 1) / 2) := by
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ (by positivity)
      simp only [Nat.cast_add, Nat.cast_one]
      have ht : (12 : ℝ) ≤ T := by exact_mod_cast hlarge
      linarith
    linarith [show (0 : ℝ) ≤ 1 / 2 ^ q by positivity]
  · have hcases : q = 4 ∨ q = 6 ∨ q = 8 ∨ q = 10 := by omega
    have hcover_small (hqsmall : q = 4 ∨ q = 6 ∨ q = 8) :
        (1 : ℝ) ≤ 3 * T / 2 ^ ((q + 1) / 2) := by
      have ht : (q : ℝ) ≤ T := by exact_mod_cast hqT
      rcases hqsmall with rfl | rfl | rfl <;>
        norm_num only [Nat.cast_ofNat] at ht <;> norm_num at ⊢ <;> linarith only [ht]
    rcases hcases with h4 | h6 | h8 | h10
    · exact (hvacuous (by have h := hcover_small (Or.inl h4); linarith)).elim
    · exact (hvacuous (by have h := hcover_small (Or.inr (Or.inl h6)); linarith)).elim
    · exact (hvacuous (by have h := hcover_small (Or.inr (Or.inr h8)); linarith)).elim
    · subst q
      have htime : T = 10 := by
        by_contra hn
        have ht : (11 : ℝ) ≤ T := by exact_mod_cast (show 11 ≤ T by omega)
        apply hvacuous
        norm_num
        have hn : (0 : ℝ) ≤ 10 * T ^ 2 / 2 ^ m := by positivity
        linarith
      subst T
      have hNreal : (1000 : ℝ) ≤ 2 ^ m := by exact_mod_cast hN
      have hstrong : (16000 : ℝ) < 2 ^ m := by
        have hs : (1000 : ℝ) / 2 ^ m < 1 / 16 := by norm_num at hvacuous; linarith
        have hp : (0 : ℝ) < 2 ^ m := by positivity
        have hm := (div_lt_iff₀ hp).mp hs
        linarith
      have hrate : Collisions.rate (2 ^ m) (10 + 10 + 10) ≤ (1 / 4 : ℝ) := by
        simp only [Collisions.rate, Nat.cast_pow, Nat.cast_ofNat]
        norm_num
        apply (div_le_iff₀ (show (0 : ℝ) < 2 ^ m - 30 by linarith)).mpr
        linarith
      norm_num at hr ⊢
      linarith

end Cslib.Cryptanalysis.AddXNOR.IdealChain.VerificationCovering
