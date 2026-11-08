/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.PerfectHashing.Table
public import Complexity.Languages.Probabilistic.Retry
public import Complexity.Probability.HashFamily.Collisions

/-!
# Building an FKS table

The randomized construction of the Fredman–Komlós–Szemerédi table [FredmanKomlosSzemeredi1984],
in the form of [CLRS2009], Section 11.5, for a duplicate-free list of `n` keys and a range-indexed
universal family `F` (`∀ r, IsTwoUniversal (F.seed r) (F.hash r)`):

1. draw top seeds into `n` values (range `n - 1`) until the squared bucket sizes sum to at most
   `4 n`;
2. for each bucket of `b` keys, draw seeds into `b²` values (range `b² - 1`) until one is injective
   on the bucket.

Each attempt succeeds with probability at least `1 / 2` (`Collisions`: Markov's inequality for the
first level, and `n² ≤ m` for the second), so each level takes at most `2` attempts in expectation.

## Cost model

The construction is an `OracleComp` over the interface `PerfectHashing.buildSpec F`, whose calls are
`draw r`, a fresh seed of range `r`, and `eval r s x`, the value of the function of seed `s` at the
key `x`. Under the honest answers `PerfectHashing.answer F` a draw follows the seed law and an
evaluation returns the hash value. The model is **abstract**: it counts seed draws
(`PerfectHashing.drawCost`) and hash evaluations (`PerfectHashing.evalCost`), not word-RAM
instructions. Sorting keys into buckets, checking an attempt and laying out the memory are local
computation and are not charged; they use only the hash values the program obtained from its calls.

An oracle program is a finite tree of calls, so the unbounded Las Vegas loop is truncated: each
level makes at most `fuel` attempts (`OracleComp.retry`), and the construction returns `none` if
some level exhausts its fuel. The expected costs are bounded uniformly in `fuel`, and the
probability of `none` decays geometrically in `fuel`.

## Main definitions

* `PerfectHashing.Query`, `PerfectHashing.buildSpec`, `PerfectHashing.answer`,
  `PerfectHashing.drawCost`, `PerfectHashing.evalCost`: the interface, its honest answers and its
  two costs.
* `PerfectHashing.trial`: draw a seed and evaluate it at every key.
* `PerfectHashing.bucketOf`, `PerfectHashing.TopGood`, `PerfectHashing.SecGood`: buckets from
  observed hash values, and the success tests of the two levels.
* `PerfectHashing.buildSecondary`, `PerfectHashing.buildRest`, `PerfectHashing.build`: the
  construction.

## Main results

* `PerfectHashing.valid_of_mem_support_build`: every table the construction returns satisfies the
  FKS conditions, so it answers lookups correctly (`PerfectHashing.runLookup_of_mem_support_build`)
  in at most `5 n + 2` cells (`PerfectHashing.size_le_of_mem_support_build`).
* `PerfectHashing.evalWith_build_none_le`: the construction fails with probability at most
  `(n + 1) 2^{-fuel}` for `n ≥ 1` keys.
* `PerfectHashing.expectedCost_build_draw_le`: at most `2 (n + 1)` expected seed draws for
  `n ≥ 1` keys, whatever the fuel.
* `PerfectHashing.expectedCost_build_eval_le`: at most `4 n` expected hash evaluations, whatever
  the fuel.

## References

* [M. L. Fredman, J. Komlós, E. Szemerédi, *Storing a Sparse Table with O(1) Worst Case Access
  Time*][FredmanKomlosSzemeredi1984]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, C. Stein, *Introduction to Algorithms*, 3rd ed.,
  Section 11.5][CLRS2009]
-/

@[expose] public section

open scoped ENNReal

namespace Cslib.DataStructure.Dictionary.PerfectHashing

open Finset OracleComp Probability

variable {X : Type}

/-! ### The interface -/

/-- The calls of the construction: draw a seed of range `r`, or evaluate the function of a seed
at a key. -/
inductive Query (F : Family X) where
  /-- Draw a fresh seed of range `r`. -/
  | draw (r : ℕ)
  /-- Evaluate the function of the seed `s` of range `r` at the key `x`. -/
  | eval (r : ℕ) (s : F.Seed r) (x : X)

/-- The answer type of a call. -/
abbrev Query.Response {F : Family X} : Query F → Type
  | .draw r => F.Seed r
  | .eval r _ _ => Fin (r + 1)

/-- The interface of the construction. -/
abbrev buildSpec (F : Family X) : OracleSpec (Query F) := Query.Response

/-- The honest answers: a draw follows the seed law, an evaluation returns the hash value. -/
noncomputable def answer (F : Family X) : (q : Query F) → PMF (Query.Response q)
  | .draw r => F.seed r
  | .eval r s x => PMF.pure (F.hash r s x)

@[simp] theorem answer_draw (F : Family X) (r : ℕ) : answer F (.draw r) = F.seed r := rfl

@[simp] theorem answer_eval (F : Family X) (r : ℕ) (s : F.Seed r) (x : X) :
    answer F (.eval r s x) = PMF.pure (F.hash r s x) := rfl

/-- Count seed draws. -/
def drawCost {F : Family X} : Query F → ℝ≥0∞
  | .draw _ => 1
  | .eval _ _ _ => 0

/-- Count hash evaluations. -/
def evalCost {F : Family X} : Query F → ℝ≥0∞
  | .draw _ => 0
  | .eval _ _ _ => 1

/-! ### One attempt -/

/-- Evaluate the function of the seed `s` at each key, in order. -/
def evalAll (F : Family X) (r : ℕ) (s : F.Seed r) :
    List X → OracleComp (buildSpec F) (List (Fin (r + 1)))
  | [] => pure []
  | x :: xs => do
    let v ← query (spec := buildSpec F) (Query.eval r s x)
    let vs ← evalAll F r s xs
    pure (v :: vs)

/-- The outcome of one attempt: a seed and the observed values of its function at the keys. -/
structure Trial (F : Family X) (r : ℕ) where
  /-- The drawn seed. -/
  seed : F.Seed r
  /-- The values of its function at the keys, in order. -/
  values : List (Fin (r + 1))

/-- One attempt: draw a seed of range `r` and evaluate it at every key. -/
def trial (F : Family X) (r : ℕ) (keys : List X) : OracleComp (buildSpec F) (Trial F r) := do
  let s ← query (spec := buildSpec F) (Query.draw r)
  let vs ← evalAll F r s keys
  pure ⟨s, vs⟩

/-- The keys whose observed value is `j`. -/
def bucketOf {r : ℕ} (keys : List X) (vs : List (Fin (r + 1))) (j : Fin (r + 1)) : List X :=
  ((keys.zip vs).filter fun p => p.2 = j).map Prod.fst

/-- A top-level attempt succeeds when the squared bucket sizes sum to at most `4 n`. -/
def TopGood {F : Family X} {r : ℕ} (keys : List X) (t : Trial F r) : Prop :=
  ∑ j, (bucketOf keys t.values j).length ^ 2 ≤ 4 * keys.length

instance {F : Family X} {r : ℕ} (keys : List X) : DecidablePred (TopGood (F := F) (r := r) keys) :=
  fun _ => inferInstanceAs (Decidable (_ ≤ _))

/-- A secondary attempt succeeds when the observed values are distinct, that is, when the function
is injective on the bucket. -/
def SecGood {F : Family X} {r : ℕ} (t : Trial F r) : Prop :=
  t.values.Nodup

instance {F : Family X} {r : ℕ} : DecidablePred (SecGood (F := F) (r := r)) :=
  fun t => inferInstanceAs (Decidable t.values.Nodup)

/-! ### The construction -/

/-- Build the block of a bucket: at most `fuel` attempts at a seed into `b²` values that is
injective on the bucket's `b` keys. -/
def buildSecondary (F : Family X) (fuel : ℕ) (bk : List X) :
    OracleComp (buildSpec F) (Option (Member F)) :=
  Option.map (fun t : Trial F (bk.length ^ 2 - 1) => (⟨_, t.seed⟩ : Member F)) <$>
    retry SecGood (trial F (bk.length ^ 2 - 1) bk) fuel

/-- The table, once every bucket has its block. -/
def assemble {F : Family X} (top : Member F) (sec : Fin (top.range + 1) → Option (Member F)) :
    Option (Description F) :=
  if hs : ∀ j, (sec j).isSome then some ⟨top, fun j => (sec j).get (hs j)⟩ else none

/-- After a successful top-level attempt, build the block of every bucket. -/
def buildRest (F : Family X) (fuel : ℕ) (keys : List X)
    (t : Trial F (keys.length - 1)) : OracleComp (buildSpec F) (Option (Description F)) :=
  assemble ⟨keys.length - 1, t.seed⟩ <$>
    OracleComp.pi fun j => buildSecondary F fuel (bucketOf keys t.values j)

/-- **The FKS construction** for the key list `keys`, with at most `fuel` attempts per level. -/
def build (F : Family X) (fuel : ℕ) (keys : List X) :
    OracleComp (buildSpec F) (Option (Description F)) :=
  retry (TopGood keys) (trial F (keys.length - 1) keys) fuel >>= fun o =>
    o.elim (pure none) (buildRest F fuel keys)

/-! ### One attempt under the honest answers -/

section Trial

variable {F : Family X}

@[simp] theorem evalWith_evalAll (r : ℕ) (s : F.Seed r) (keys : List X) :
    evalWith (answer F) (evalAll F r s keys) = PMF.pure (keys.map (F.hash r s)) := by
  induction keys with
  | nil => rfl
  | cons x xs ih =>
    simp only [evalAll, evalWith_bind, evalWith_query, ih, evalWith_pure, PMF.pure_bind,
      List.map_cons, answer_eval]

theorem expectedCost_evalAll (cost : Query F → ℝ≥0∞) (r : ℕ) (s : F.Seed r) (keys : List X) :
    expectedCost (answer F) cost (evalAll F r s keys) =
      (keys.map fun x => cost (Query.eval r s x)).sum := by
  induction keys with
  | nil => simp [evalAll]
  | cons x xs ih =>
    rw [evalAll, expectedCost_query_bind]
    simp only [expectedCost_bind, ih, expectedCost_pure, mul_zero, tsum_zero, add_zero,
      ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul, List.map_cons, List.sum_cons]

/-- One attempt draws a seed and observes the values of its function. -/
theorem evalWith_trial (r : ℕ) (keys : List X) :
    evalWith (answer F) (trial F r keys) =
      (F.seed r).map fun s => (⟨s, keys.map (F.hash r s)⟩ : Trial F r) := by
  simp only [trial, evalWith_bind, evalWith_query, evalWith_evalAll, evalWith_pure,
    PMF.pure_bind, answer_draw]
  rw [← PMF.bind_pure_comp]
  rfl

theorem expectedCost_trial (cost : Query F → ℝ≥0∞) (r : ℕ) (keys : List X) :
    expectedCost (answer F) cost (trial F r keys) =
      cost (Query.draw r) +
        ∑' s, F.seed r s * (keys.map fun x => cost (Query.eval r s x)).sum := by
  rw [trial, expectedCost_query_bind]
  simp only [expectedCost_bind, expectedCost_evalAll, expectedCost_pure, mul_zero, tsum_zero,
    add_zero, answer_draw]

/-- One attempt makes one draw. -/
@[simp] theorem expectedCost_trial_draw (r : ℕ) (keys : List X) :
    expectedCost (answer F) drawCost (trial F r keys) = 1 := by
  simp [expectedCost_trial, drawCost]

/-- One attempt makes one evaluation per key. -/
@[simp] theorem expectedCost_trial_eval (r : ℕ) (keys : List X) :
    expectedCost (answer F) evalCost (trial F r keys) = keys.length := by
  simp [expectedCost_trial, evalCost, ENNReal.tsum_mul_right]

theorem mem_supportWith_trial {r : ℕ} {keys : List X} {t : Trial F r}
    (ht : t ∈ supportWith (fun q => (answer F q).support) (trial F r keys)) :
    t.seed ∈ (F.seed r).support ∧ t.values = keys.map (F.hash r t.seed) := by
  rw [← support_evalWith, evalWith_trial, PMF.support_map] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  exact ⟨hs, rfl⟩

end Trial

/-! ### Buckets from observed values -/

section Buckets

theorem bucketOf_map {r : ℕ} (f : X → Fin (r + 1)) (keys : List X) (j : Fin (r + 1)) :
    bucketOf keys (keys.map f) j = keys.filter fun x => f x = j := by
  induction keys with
  | nil => rfl
  | cons x xs ih =>
    simp only [bucketOf, List.map_cons, List.zip_cons_cons, List.filter_cons] at ih ⊢
    by_cases hx : f x = j
    · simp [hx, ih]
    · simp [hx, ih]

theorem bucketOf_sublist {r : ℕ} (keys : List X) (vs : List (Fin (r + 1))) (j : Fin (r + 1)) :
    (bucketOf keys vs j).Sublist keys := by
  induction keys generalizing vs with
  | nil => simp [bucketOf]
  | cons x xs ih =>
    cases vs with
    | nil => simp [bucketOf]
    | cons v vs =>
      have := ih vs
      simp only [bucketOf, List.zip_cons_cons, List.filter_cons] at this ⊢
      by_cases hv : v = j
      · simpa [hv] using this.cons_cons x
      · simpa [hv] using this.cons x

theorem sum_length_bucketOf_le {r : ℕ} (keys : List X) (vs : List (Fin (r + 1))) :
    ∑ j, (bucketOf keys vs j).length ≤ keys.length := by
  induction keys generalizing vs with
  | nil => simp [bucketOf]
  | cons x xs ih =>
    cases vs with
    | nil => simp [bucketOf]
    | cons v vs =>
      have hstep : ∀ j, (bucketOf (x :: xs) (v :: vs) j).length =
          (bucketOf xs vs j).length + if v = j then 1 else 0 := by
        intro j
        by_cases hv : v = j
        · simp [bucketOf, hv]
        · simp [bucketOf, hv]
      simp only [hstep, sum_add_distrib, sum_ite_eq, mem_univ, ↓reduceIte, List.length_cons]
      exact Nat.add_le_add_right (ih vs) 1

variable [DecidableEq X]

theorem card_filter_eq_length {r : ℕ} {keys : List X} (hkeys : keys.Nodup)
    (f : X → Fin (r + 1)) (j : Fin (r + 1)) :
    (keys.toFinset.filter fun x => f x = j).card = (bucketOf keys (keys.map f) j).length := by
  rw [bucketOf_map, ← List.toFinset_card_of_nodup (hkeys.filter _), List.toFinset_filter]
  simp

theorem mem_bucket_iff_mem_bucketOf {F : Family X} {D : Description F} {keys : List X}
    {vs : List (Fin (D.top.range + 1))} (hvs : vs = keys.map D.top.apply)
    {j : Fin (D.top.range + 1)} {x : X} : x ∈ bucket D keys j ↔ x ∈ bucketOf keys vs j := by
  subst hvs
  simp [bucketOf_map, mem_bucket]

theorem card_bucket_eq_length {F : Family X} {D : Description F} {keys : List X}
    (hkeys : keys.Nodup) {vs : List (Fin (D.top.range + 1))} (hvs : vs = keys.map D.top.apply)
    (j : Fin (D.top.range + 1)) : (bucket D keys j).card = (bucketOf keys vs j).length := by
  subst hvs
  exact card_filter_eq_length hkeys _ j

end Buckets

/-! ### Correctness -/

section Correctness

variable {F : Family X} [DecidableEq X]

omit [DecidableEq X] in
theorem assemble_eq_some {top : Member F} {sec : Fin (top.range + 1) → Option (Member F)}
    {D : Description F} (h : assemble top sec = some D) :
    ∃ hs : ∀ j, (sec j).isSome, D = ⟨top, fun j => (sec j).get (hs j)⟩ := by
  unfold assemble at h
  split_ifs at h with hs
  exact ⟨hs, (Option.some.inj h).symm⟩

omit [DecidableEq X] in
theorem mem_supportWith_buildSecondary {fuel : ℕ} {bk : List X} {g : Member F}
    (hg : some g ∈ supportWith (fun q => (answer F q).support) (buildSecondary F fuel bk)) :
    g.range = bk.length ^ 2 - 1 ∧ Set.InjOn g.apply {x | x ∈ bk} := by
  rw [buildSecondary, mem_supportWith_map_iff] at hg
  obtain ⟨o, ho, hog⟩ := hg
  cases o with
  | none => cases hog
  | some t =>
    cases hog
    obtain ⟨hgood, ht⟩ := mem_supportWith_retry ho
    obtain ⟨-, htv⟩ := mem_supportWith_trial ht
    refine ⟨rfl, fun x hx y hy hxy => ?_⟩
    have hnodup : (bk.map (F.hash _ t.seed)).Nodup := htv ▸ hgood
    exact List.inj_on_of_nodup_map hnodup hx hy hxy

/-- **Correctness of the construction.** Under the honest answers, every table the construction
returns for a duplicate-free key list satisfies the FKS conditions. -/
theorem valid_of_mem_support_build {fuel : ℕ} {keys : List X} (hkeys : keys.Nodup)
    {D : Description F} (hD : some D ∈ (evalWith (answer F) (build F fuel keys)).support) :
    Valid D keys := by
  rw [support_evalWith, build, mem_supportWith_bind_iff] at hD
  obtain ⟨o, ho, hD⟩ := hD
  cases o with
  | none => simp at hD
  | some t =>
    obtain ⟨hgood, ht⟩ := mem_supportWith_retry ho
    obtain ⟨-, htv⟩ := mem_supportWith_trial ht
    simp only [Option.elim_some, buildRest, mem_supportWith_map_iff] at hD
    obtain ⟨sec, hsec, hasm⟩ := hD
    obtain ⟨hs, rfl⟩ := assemble_eq_some hasm
    rw [mem_supportWith_pi_iff] at hsec
    have hvs : t.values = keys.map (Member.apply ⟨keys.length - 1, t.seed⟩) := htv
    have hcard := card_bucket_eq_length (D := ⟨⟨keys.length - 1, t.seed⟩,
      fun j => (sec j).get (hs j)⟩) hkeys hvs
    have hsecj : ∀ j, ((sec j).get (hs j)).range = (bucketOf keys t.values j).length ^ 2 - 1 ∧
        Set.InjOn ((sec j).get (hs j)).apply {x | x ∈ bucketOf keys t.values j} := fun j =>
      mem_supportWith_buildSecondary (by rw [Option.some_get]; exact hsec j)
    refine ⟨rfl, ?_, fun j hj => ?_, fun j x hx y hy hxy => ?_⟩
    · simp only [hcard]
      exact hgood
    · rw [hcard] at hj ⊢
      have hpos : 0 < (bucketOf keys t.values j).length ^ 2 := by positivity
      dsimp only
      rw [(hsecj j).1]
      omega
    · rw [Finset.mem_coe, mem_bucket_iff_mem_bucketOf hvs] at hx hy
      exact (hsecj j).2 hx hy hxy

/-- A table returned by the construction answers every lookup correctly. -/
theorem runLookup_of_mem_support_build {fuel : ℕ} {keys : List X} (hkeys : keys.Nodup)
    {D : Description F} (hD : some D ∈ (evalWith (answer F) (build F fuel keys)).support)
    (x : X) : runLookup F (memory D keys) x = decide (x ∈ keys) :=
  runLookup_memory (valid_of_mem_support_build hkeys hD).secondaryInjective x

/-- A table returned by the construction for `n` keys occupies at most `5 n + 2` cells. -/
theorem size_le_of_mem_support_build {fuel : ℕ} {keys : List X} (hkeys : keys.Nodup)
    {D : Description F} (hD : some D ∈ (evalWith (answer F) (build F fuel keys)).support) :
    size D keys ≤ 5 * keys.length + 2 :=
  size_le (valid_of_mem_support_build hkeys hD)

end Correctness

/-! ### Failure probability and expected cost -/

section Probability

variable {F : Family X}

/-- A top-level attempt into `n` values fails with probability at most `1 / 2` (Markov's
inequality on the expected squared bucket sizes, `Collisions`). -/
theorem toOuterMeasure_not_topGood_le (hF : ∀ r, IsTwoUniversal (F.seed r) (F.hash r))
    {keys : List X} (hkeys : keys.Nodup) :
    (evalWith (answer F) (trial F (keys.length - 1) keys)).toOuterMeasure
      {t | ¬ TopGood keys t} ≤ 2⁻¹ := by
  classical
  rw [evalWith_trial, PMF.toOuterMeasure_map_apply]
  have hcard : keys.toFinset.card ≤ Fintype.card (Fin (keys.length - 1 + 1)) := by
    rw [Fintype.card_fin, List.toFinset_card_of_nodup hkeys]
    omega
  refine le_trans (MeasureTheory.measure_mono fun s hs => ?_)
    ((hF _).toOuterMeasure_four_mul_lt_sum_card_filter_sq_le keys.toFinset hcard)
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, TopGood, not_le] at hs ⊢
  simp only [card_filter_eq_length hkeys, List.toFinset_card_of_nodup hkeys]
  exact hs

/-- A secondary attempt into `b²` values on a duplicate-free bucket of `b` keys fails with
probability at most `1 / 2` (`Collisions`). -/
theorem toOuterMeasure_not_secGood_le (hF : ∀ r, IsTwoUniversal (F.seed r) (F.hash r))
    {bk : List X} (hbk : bk.Nodup) :
    (evalWith (answer F) (trial F (bk.length ^ 2 - 1) bk)).toOuterMeasure
      {t | ¬ SecGood t} ≤ 2⁻¹ := by
  classical
  rw [evalWith_trial, PMF.toOuterMeasure_map_apply]
  have hcard : bk.toFinset.card ^ 2 ≤ Fintype.card (Fin (bk.length ^ 2 - 1 + 1)) := by
    rw [Fintype.card_fin, List.toFinset_card_of_nodup hbk]
    omega
  refine le_trans (MeasureTheory.measure_mono fun s hs => ?_)
    ((hF _).toOuterMeasure_not_injOn_le bk.toFinset hcard)
  intro hinj
  apply hs
  exact hbk.map_on fun x hx y hy hxy => hinj (by simpa using hx) (by simpa using hy) hxy

private theorem evalWith_map_option_none {α β : Type} (f : α → β)
    (program : OracleComp (buildSpec F) (Option α)) :
    evalWith (answer F) (Option.map f <$> program) none = evalWith (answer F) program none := by
  rw [evalWith_map, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
    ← PMF.toOuterMeasure_apply_singleton]
  congr 1
  ext o
  cases o <;> simp

/-- The block of a bucket is built except with probability `2^{-fuel}` (always, for an empty
bucket and positive fuel). -/
theorem evalWith_buildSecondary_none_le (hF : ∀ r, IsTwoUniversal (F.seed r) (F.hash r))
    (fuel : ℕ) {bk : List X} (hbk : bk.Nodup) :
    evalWith (answer F) (buildSecondary F fuel bk) none ≤ 2⁻¹ ^ fuel := by
  classical
  rw [buildSecondary, evalWith_map_option_none]
  exact evalWith_retry_none_le _ _ _ (toOuterMeasure_not_secGood_le hF hbk) fuel

/-- After a successful top-level attempt, the blocks are all built except with probability
`n 2^{-fuel}` for `n ≥ 1` keys (a union bound over the buckets). -/
theorem evalWith_buildRest_none_le (hF : ∀ r, IsTwoUniversal (F.seed r) (F.hash r))
    (fuel : ℕ) {keys : List X} (hkeys : keys.Nodup) (t : Trial F (keys.length - 1)) :
    evalWith (answer F) (buildRest F fuel keys t) none ≤
      ((keys.length - 1 + 1 : ℕ) : ℝ≥0∞) * 2⁻¹ ^ fuel := by
  rw [buildRest, evalWith_map, ← PMF.toOuterMeasure_apply_singleton,
    PMF.toOuterMeasure_map_apply]
  refine le_trans (MeasureTheory.measure_mono fun sec hsec => ?_)
    ((toOuterMeasure_evalWith_pi_exists_le (answer F) _ fun _ o => o = none).trans ?_)
  · simp only [Set.mem_preimage, Set.mem_singleton_iff, assemble, dite_eq_right_iff,
      reduceCtorEq, imp_false, not_forall, Option.not_isSome_iff_eq_none] at hsec
    exact hsec
  · calc ∑ j : Fin (keys.length - 1 + 1), (evalWith (answer F)
          (buildSecondary F fuel (bucketOf keys t.values j))).toOuterMeasure {o | o = none}
        ≤ ∑ _j : Fin (keys.length - 1 + 1), (2⁻¹ : ℝ≥0∞) ^ fuel := by
          refine sum_le_sum fun j _ => ?_
          rw [Set.ofPred_eq_eq_singleton, PMF.toOuterMeasure_apply_singleton]
          exact evalWith_buildSecondary_none_le hF fuel
            ((bucketOf_sublist keys t.values j).nodup hkeys)
      _ = ((keys.length - 1 + 1 : ℕ) : ℝ≥0∞) * 2⁻¹ ^ fuel := by
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Failure probability of the construction.** With at most `fuel` attempts per level, the
construction for a duplicate-free list of `n ≥ 1` keys fails with probability at most
`(n + 1) 2^{-fuel}`: `2^{-fuel}` for the top level and `2^{-fuel}` for each of the `n` buckets. -/
theorem evalWith_build_none_le (hF : ∀ r, IsTwoUniversal (F.seed r) (F.hash r)) (fuel : ℕ)
    {keys : List X} (hkeys : keys.Nodup) :
    evalWith (answer F) (build F fuel keys) none ≤
      ((keys.length - 1 + 2 : ℕ) : ℝ≥0∞) * 2⁻¹ ^ fuel := by
  refine (evalWith_bind_elim_none_le (answer F) _ _
    (evalWith_buildRest_none_le hF fuel hkeys)).trans ?_
  calc evalWith (answer F) (retry (TopGood keys) (trial F (keys.length - 1) keys) fuel) none +
        ((keys.length - 1 + 1 : ℕ) : ℝ≥0∞) * 2⁻¹ ^ fuel
      ≤ 2⁻¹ ^ fuel + ((keys.length - 1 + 1 : ℕ) : ℝ≥0∞) * 2⁻¹ ^ fuel := by
        gcongr
        exact evalWith_retry_none_le _ _ _ (toOuterMeasure_not_topGood_le hF hkeys) fuel
    _ = ((keys.length - 1 + 2 : ℕ) : ℝ≥0∞) * 2⁻¹ ^ fuel := by
        push_cast
        ring

/-- The block of a bucket costs at most twice one attempt in expectation, whatever the fuel. -/
theorem expectedCost_buildSecondary_le (hF : ∀ r, IsTwoUniversal (F.seed r) (F.hash r))
    (cost : Query F → ℝ≥0∞) (fuel : ℕ) {bk : List X} (hbk : bk.Nodup) :
    expectedCost (answer F) cost (buildSecondary F fuel bk) ≤
      2 * expectedCost (answer F) cost (trial F (bk.length ^ 2 - 1) bk) := by
  classical
  rw [buildSecondary, expectedCost_map]
  exact expectedCost_retry_le_two_mul _ _ _ _ (toOuterMeasure_not_secGood_le hF hbk) fuel

/-- **Expected seed draws.** The construction for a duplicate-free list of `n ≥ 1` keys draws at
most `2 (n + 1)` seeds in expectation, whatever the fuel: two expected attempts at the top level
and at each of the `n` buckets. -/
theorem expectedCost_build_draw_le (hF : ∀ r, IsTwoUniversal (F.seed r) (F.hash r)) (fuel : ℕ)
    {keys : List X} (hkeys : keys.Nodup) :
    expectedCost (answer F) drawCost (build F fuel keys) ≤
      2 * ((keys.length - 1 + 2 : ℕ) : ℝ≥0∞) := by
  refine (expectedCost_bind_elim_le (answer F) drawCost _ _ (c := 2 * (keys.length - 1 + 1 : ℕ))
    fun t => ?_).trans ?_
  · rw [buildRest, expectedCost_map, expectedCost_pi]
    calc ∑ j : Fin (keys.length - 1 + 1), expectedCost (answer F) drawCost
          (buildSecondary F fuel (bucketOf keys t.values j))
        ≤ ∑ _j : Fin (keys.length - 1 + 1), (2 : ℝ≥0∞) := by
          refine sum_le_sum fun j _ => ?_
          refine (expectedCost_buildSecondary_le hF drawCost fuel
            ((bucketOf_sublist keys t.values j).nodup hkeys)).trans ?_
          simp
      _ = 2 * (keys.length - 1 + 1 : ℕ) := by
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]
  · calc expectedCost (answer F) drawCost
          (retry (TopGood keys) (trial F (keys.length - 1) keys) fuel) +
          2 * ((keys.length - 1 + 1 : ℕ) : ℝ≥0∞)
        ≤ 2 * 1 + 2 * ((keys.length - 1 + 1 : ℕ) : ℝ≥0∞) := by
          gcongr
          refine (expectedCost_retry_le_two_mul _ _ _ _
            (toOuterMeasure_not_topGood_le hF hkeys) fuel).trans ?_
          simp
      _ = 2 * ((keys.length - 1 + 2 : ℕ) : ℝ≥0∞) := by
          push_cast
          ring

/-- **Expected hash evaluations.** The construction for a duplicate-free list of `n` keys makes at
most `4 n` hash evaluations in expectation, whatever the fuel: two expected attempts of `n`
evaluations at the top level, and two expected attempts of `b_j` evaluations at each bucket. -/
theorem expectedCost_build_eval_le (hF : ∀ r, IsTwoUniversal (F.seed r) (F.hash r)) (fuel : ℕ)
    {keys : List X} (hkeys : keys.Nodup) :
    expectedCost (answer F) evalCost (build F fuel keys) ≤ 4 * keys.length := by
  refine (expectedCost_bind_elim_le (answer F) evalCost _ _ (c := 2 * keys.length)
    fun t => ?_).trans ?_
  · rw [buildRest, expectedCost_map, expectedCost_pi]
    calc ∑ j : Fin (keys.length - 1 + 1), expectedCost (answer F) evalCost
          (buildSecondary F fuel (bucketOf keys t.values j))
        ≤ ∑ j : Fin (keys.length - 1 + 1), 2 * ((bucketOf keys t.values j).length : ℝ≥0∞) := by
          refine sum_le_sum fun j _ => ?_
          refine (expectedCost_buildSecondary_le hF evalCost fuel
            ((bucketOf_sublist keys t.values j).nodup hkeys)).trans ?_
          simp
      _ ≤ 2 * keys.length := by
          rw [← mul_sum]
          gcongr
          exact_mod_cast sum_length_bucketOf_le keys t.values
  · calc expectedCost (answer F) evalCost
          (retry (TopGood keys) (trial F (keys.length - 1) keys) fuel) + 2 * (keys.length : ℝ≥0∞)
        ≤ 2 * keys.length + 2 * (keys.length : ℝ≥0∞) := by
          gcongr
          refine (expectedCost_retry_le_two_mul _ _ _ _
            (toOuterMeasure_not_topGood_le hF hkeys) fuel).trans ?_
          simp
      _ = 4 * keys.length := by ring

end Probability

end Cslib.DataStructure.Dictionary.PerfectHashing
