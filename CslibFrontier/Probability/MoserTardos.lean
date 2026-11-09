/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.MoserTardos.Witness
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Probability.ProductMeasure
import CslibFrontier.Foundations.Probability.InfinitePi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# The Moser–Tardos algorithmic local lemma

Let finitely many mutually independent random variables `σ v ∼ μ v` be given, and finitely many
events `A i`, each determined by the variables in a finite set `vbl i`. The Moser–Tardos algorithm
[MoserTardos2010] starts from a random assignment and, while some event occurs, picks one such
event and resamples its variables. The randomness is the *table* `table μ`: independent samples
`T (v, n) ∼ μ v`, where `T (v, n)` is the value of `v` after its `n`-th resampling. The paper calls
these the sample lists `P_v^(n)`.

A *selection rule* `sel T w` names the event to resample after the log `w` (latest first), or
returns `none` to stop. `run sel T n` is the log after `n` steps and `resamplings sel i T` the
total number of resamplings of `A i` (possibly `∞`). A rule is valid when it only selects events
that occur in the current assignment. The paper allows any rule, deterministic or randomized. A
rule here may depend on the whole table, future samples included. So the bounds below hold for
every valid rule, and a randomized rule's own coins can be averaged over afterwards.

## Main definitions

* `Cslib.Probability.MoserTardos.table`: the resampling table, `Measure.infinitePi`.
* `Cslib.Probability.MoserTardos.run`, `Cslib.Probability.MoserTardos.resamplings`: the log of the
  algorithm under a selection rule and the number of resamplings of each event.
* `Cslib.Probability.MoserTardos.greedy`: a rule resampling some occurring event, if any.

## Main results

Assume `x i ∈ [0, 1)` and `Pr[A i] ≤ x i ∏ j ∈ Γ i, (1 - x j)` for every `i`, where `Γ i` contains
every other event sharing a variable with `A i` (the hypothesis of the asymmetric local lemma).

* `Cslib.Probability.MoserTardos.measure_check_eq_prod`: a proper witness structure passes its
  check with probability `∏ p ∈ S, Pr[A p.1]` [MoserTardos2010, Lemma 2.1].
* `Cslib.Probability.MoserTardos.table_witness_le`: the probability that a fixed structure occurs
  as the witness structure of a step of a valid log is at most `∏ p ∈ S, Pr[A p.1]`
  [MoserTardos2010, Lemma 2.1(ii)].
* `Cslib.Probability.MoserTardos.lintegral_resamplings_le`: **Theorem 1.2** of [MoserTardos2010].
  For every valid rule, the expected number of resamplings of `A i` is at most
  `x i / (1 - x i)`. `lintegral_sum_resamplings_le` sums this over the events, and
  `lintegral_iSup_count_le` states it for all valid logs at once.
* `Cslib.Probability.MoserTardos.exists_measurable_ge_resamplings`: one measurable function with
  the same bound dominates the count under every valid rule, so the bound also holds for the outer
  expectation.
* `Cslib.Probability.MoserTardos.ae_exists_run_eq_none`: almost surely the algorithm stops after
  finitely many steps, for every valid rule.
* `Cslib.Probability.MoserTardos.ae_exists_forall_notMem_run`: almost surely a valid rule that
  stops only when no event occurs reaches an assignment avoiding every event;
  `ae_exists_forall_notMem_run_greedy` is the case of the greedy rule.
* `Cslib.Probability.MoserTardos.exists_forall_notMem`: consequently some assignment avoids every
  event. This is the variable version of the existential local lemma (compare
  `Cslib.Probability.PMF.prod_one_sub_le_pi_iInter_compl`).

## Implementation notes

A rule may be any function of the table and the log, measurable or not. For such a rule the
expectation `∫⁻` in `lintegral_resamplings_le` is the lower Lebesgue integral. The proof shows
more: the count is dominated, for every valid rule at once, by the measurable rule-independent
function `T ↦ ⨆ (w valid on T), w.count i` (`resamplings_le_iSup_count`,
`measurable_iSup_count`). The integral of that function is at most `x i / (1 - x i)`, so the bound
holds for the outer expectation too (`exists_measurable_ge_resamplings`). To bound this
function, the proof dominates the number of steps labelled `i` of a valid log by the number of
proper structures in `shapes vbl i H` whose checks pass
(`Cslib.Probability.MoserTardos.exists_witnesses`). That number is measurable, and its
expectation is at most `x i / (1 - x i)` by Lemma 2.1 and the counting bound
`Cslib.Probability.MoserTardos.sum_prod_shapes_le`.

## References

* [R. A. Moser, G. Tardos, *A constructive proof of the general Lovász Local Lemma*]
  [MoserTardos2010]
-/

public section

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace Cslib.Probability.MoserTardos

section Table

variable {V : Type*} {α : V → Type*} [∀ v, MeasurableSpace (α v)]
  (μ : ∀ v, Measure (α v)) [∀ v, IsProbabilityMeasure (μ v)]

/-- The resampling table: mutually independent samples `T (v, n) ∼ μ v` for every variable `v`
and every `n : ℕ`. -/
noncomputable def table : Measure (∀ p : V × ℕ, α p.1) :=
  Measure.infinitePi fun p : V × ℕ => μ p.1

omit [∀ v, IsProbabilityMeasure (μ v)] in
theorem table_def : table μ = Measure.infinitePi fun p : V × ℕ => μ p.1 := by
  rw [table]

instance : IsProbabilityMeasure (table μ) := by
  rw [table_def]
  infer_instance

/-- Reading one sample of every variable from the table gives the product distribution. -/
theorem table_map_read [Fintype V] (c : V → ℕ) :
    (table μ).map (fun T v => T (v, c v)) = Measure.pi μ := by
  have hinj : Function.Injective fun v : V => (v, c v) := fun v w h => congrArg Prod.fst h
  rw [table_def, Measure.map_infinitePi_infinitePi_of_inj (P := fun p : V × ℕ => μ p.1) hinj,
    Measure.infinitePi_eq_pi]

omit [∀ v, MeasurableSpace (α v)] in
theorem measurable_read [∀ v, MeasurableSpace (α v)] (c : V → ℕ) :
    Measurable fun (T : ∀ p : V × ℕ, α p.1) v => T (v, c v) :=
  measurable_pi_iff.2 fun v => measurable_pi_apply (v, c v)

end Table

section Check

variable {V ι : Type*} [Fintype V] [DecidableEq V] {α : V → Type*}
  [∀ v, MeasurableSpace (α v)] (μ : ∀ v, Measure (α v)) [∀ v, IsProbabilityMeasure (μ v)]
  (vbl : ι → Finset V)

/-- The event that vertex `p` of `S` passes its check. -/
private def checkAt (A : ι → Set (∀ v, α v)) (S : Finset (ι × ℕ)) (p : ι × ℕ) :
    Set (∀ q : V × ℕ, α q.1) :=
  (fun T v => T (v, depthUses vbl S p v)) ⁻¹' A p.1

/-- The table coordinates read by the check of vertex `p`. -/
private def coords (S : Finset (ι × ℕ)) (p : ι × ℕ) : Finset (V × ℕ) :=
  (vbl p.1).image fun v => (v, depthUses vbl S p v)

omit [Fintype V] [∀ v, MeasurableSpace (α v)] in
private theorem checkAt_dependsOn (A : ι → Set (∀ v, α v))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V)) (S : Finset (ι × ℕ)) (p : ι × ℕ) :
    DependsOn (· ∈ checkAt vbl A S p) (coords vbl S p : Set (V × ℕ)) := fun _ _ h =>
  hA p.1 fun _ hv => h _ (Finset.mem_coe.2 (mem_image_of_mem
    (fun v => (v, depthUses vbl S p v)) (Finset.mem_coe.1 hv)))

omit [Fintype V] in
private theorem measurableSet_checkAt (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (S : Finset (ι × ℕ)) (p : ι × ℕ) :
    MeasurableSet (checkAt vbl A S p) :=
  measurable_read _ (hAm p.1)

private theorem table_checkAt (A : ι → Set (∀ v, α v)) (hAm : ∀ i, MeasurableSet (A i))
    (S : Finset (ι × ℕ)) (p : ι × ℕ) :
    table μ (checkAt vbl A S p) = Measure.pi μ (A p.1) := by
  rw [checkAt, ← Measure.map_apply (measurable_read _) (hAm p.1), table_map_read]

omit [Fintype V] in
private theorem disjoint_coords {S : Finset (ι × ℕ)} (hS : Proper vbl S) {p q : ι × ℕ}
    (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q) : Disjoint (coords vbl S p) (coords vbl S q) := by
  rw [Finset.disjoint_left]
  intro c hcp hcq
  obtain ⟨v, hv, rfl⟩ := mem_image.1 hcp
  obtain ⟨v', hv', he⟩ := mem_image.1 hcq
  obtain ⟨hvv, he⟩ := Prod.mk.inj he
  rw [hvv] at hv' he
  exact depthUses_ne vbl hS hp hq hpq hv hv' he.symm

private theorem table_iInter_checkAt (A : ι → Set (∀ v, α v)) (hAm : ∀ i, MeasurableSet (A i))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V)) {S : Finset (ι × ℕ)} (hS : Proper vbl S) :
    ∀ R ⊆ S, table μ (⋂ p ∈ R, checkAt vbl A S p) = ∏ p ∈ R, Measure.pi μ (A p.1) := by
  classical
  intro R
  induction R using Finset.induction_on with
  | empty => intro _; simp
  | insert a R ha ih =>
    intro hR
    have haS : a ∈ S := hR (mem_insert_self a R)
    have hRS : R ⊆ S := (subset_insert a R).trans hR
    rw [set_biInter_insert, prod_insert ha, ← ih hRS, ← table_checkAt μ vbl A hAm S a, table_def]
    refine (indepSet_infinitePi_of_dependsOn (S := coords vbl S a)
      (T := R.biUnion (coords vbl S)) (measurableSet_checkAt vbl A hAm S a)
      (MeasurableSet.biInter R.countable_toSet fun p _ => measurableSet_checkAt vbl A hAm S p)
      (checkAt_dependsOn vbl A hA S a) ?_ ?_).measure_inter_eq_mul
    · intro T T' h
      simp only [Set.mem_iInter]
      refine propext (forall₂_congr fun p hp => ?_)
      have := checkAt_dependsOn vbl A hA S p fun c hc =>
        h c (Finset.mem_coe.2 (mem_biUnion.2 ⟨p, hp, Finset.mem_coe.1 hc⟩))
      exact Iff.of_eq this
    · refine (disjoint_biUnion_right _ _ _).2 fun p hp => ?_
      exact disjoint_coords vbl hS haS (hRS hp) fun h => ha (h ▸ hp)

omit [Fintype V] [∀ v, MeasurableSpace (α v)] in
private theorem check_eq_iInter (A : ι → Set (∀ v, α v)) (S : Finset (ι × ℕ)) :
    {T | Check vbl A S T} = ⋂ p ∈ S, checkAt vbl A S p := by
  ext T
  simp only [Set.mem_ofPred_eq, Set.mem_iInter, checkAt, Set.mem_preimage]
  exact check_iff vbl

omit [Fintype V] in
theorem measurableSet_check (A : ι → Set (∀ v, α v)) (hAm : ∀ i, MeasurableSet (A i))
    (S : Finset (ι × ℕ)) : MeasurableSet {T : ∀ p : V × ℕ, α p.1 | Check vbl A S T} := by
  rw [check_eq_iInter]
  exact MeasurableSet.biInter S.countable_toSet fun p _ => measurableSet_checkAt vbl A hAm S p

/-- **The witness-structure lemma** [MoserTardos2010, Lemma 2.1(ii)]: a proper structure passes
its check with probability exactly `∏ p ∈ S, Pr[A p.1]`. With the coupling `check_witness`, this
bounds the probability that the structure occurs in the log, as in the paper. -/
theorem measure_check_eq_prod (A : ι → Set (∀ v, α v)) (hAm : ∀ i, MeasurableSet (A i))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V)) {S : Finset (ι × ℕ)} (hS : Proper vbl S) :
    table μ {T | Check vbl A S T} = ∏ p ∈ S, Measure.pi μ (A p.1) := by
  rw [check_eq_iInter]
  exact table_iInter_checkAt μ vbl A hAm hA hS S subset_rfl

/-- **Lemma 2.1(ii)** of [MoserTardos2010]: the probability that a fixed structure `S` occurs as
the witness structure of a step of some valid log on the table is at most
`∏ p ∈ S, Pr[A p.1]`. The event is measured by the outer measure, so no measurability is
needed. -/
theorem table_witness_le [DecidableEq ι] (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (S : Finset (ι × ℕ)) :
    table μ {T | ∃ i w, IsLog vbl A T (i :: w) ∧ witness vbl i w = S} ≤
      ∏ p ∈ S, Measure.pi μ (A p.1) := by
  rcases Set.eq_empty_or_nonempty {T | ∃ i w, IsLog vbl A T (i :: w) ∧ witness vbl i w = S} with
    he | ⟨T₀, i₀, w₀, -, hw₀⟩
  · rw [he, measure_empty]
    exact zero_le
  have hS : Proper vbl S := hw₀ ▸ proper_witness vbl i₀ w₀
  rw [← measure_check_eq_prod μ vbl A hAm hA hS]
  refine measure_mono fun T ⟨i, w, hlog, hw⟩ => ?_
  rw [Set.mem_ofPred_eq, ← hw]
  exact check_witness vbl A hA i w T hlog

end Check

section Expectation

variable {V ι : Type*} [Fintype V] [DecidableEq V] [DecidableEq ι] [Fintype ι]
  {α : V → Type*} [∀ v, MeasurableSpace (α v)] (μ : ∀ v, Measure (α v))
  [∀ v, IsProbabilityMeasure (μ v)] (vbl : ι → Finset V)

open scoped Classical in
/-- The number of proper structures in `shapes vbl i H` whose checks pass on `T`. -/
private noncomputable def passCount (A : ι → Set (∀ v, α v)) (i : ι) (H : ℕ)
    (T : ∀ p : V × ℕ, α p.1) : ℝ≥0∞ :=
  ∑ S ∈ shapes vbl i H, if Proper vbl S ∧ Check vbl A S T then 1 else 0

omit [Fintype V] [∀ v, MeasurableSpace (α v)] in
private theorem passCount_mono (A : ι → Set (∀ v, α v)) (i : ι) (T : ∀ p : V × ℕ, α p.1) :
    Monotone fun H => passCount vbl A i H T :=
  monotone_nat_of_le_succ fun H =>
    sum_le_sum_of_subset_of_nonneg (shapes_mono vbl i H) fun _ _ _ => zero_le

omit [Fintype V] [∀ v, MeasurableSpace (α v)] in
private theorem count_le_iSup_passCount (A : ι → Set (∀ v, α v))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V)) {T : ∀ p : V × ℕ, α p.1} (i : ι)
    {w : List ι} (hw : IsLog vbl A T w) :
    (w.count i : ℝ≥0∞) ≤ ⨆ H, passCount vbl A i H T := by
  classical
  refine le_trans ?_ (le_iSup (fun H => passCount vbl A i H T) w.length)
  obtain ⟨W, hcard, hW⟩ := exists_witnesses vbl A hA T i w.length w hw le_rfl
  rw [← hcard, passCount, card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  calc ∑ S ∈ W, (1 : ℝ≥0∞)
      = ∑ S ∈ W, if Proper vbl S ∧ Check vbl A S T then 1 else 0 :=
        sum_congr rfl fun S hS => (ite_eq_left (hW S hS).2).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (fun S hS => (hW S hS).1) fun _ _ _ => zero_le

omit [Fintype V] in
private theorem measurable_passCount (A : ι → Set (∀ v, α v)) (hAm : ∀ i, MeasurableSet (A i))
    (i : ι) (H : ℕ) : Measurable (passCount vbl A i H) := by
  classical
  unfold passCount
  refine Finset.measurable_sum _ fun S _ => ?_
  by_cases hS : Proper vbl S
  · simp only [hS, true_and]
    exact Measurable.ite (measurableSet_check vbl A hAm S) measurable_const measurable_const
  · simp only [hS, false_and, ite_false]
    exact measurable_const

private theorem lintegral_passCount_le (A : ι → Set (∀ v, α v)) (hAm : ∀ i, MeasurableSet (A i))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V)) (Γ : ι → Finset ι)
    (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    (hP : ∀ i, (Measure.pi μ).real (A i) ≤ x i * ∏ j ∈ Γ i, (1 - x j)) (i : ι) (H : ℕ) :
    ∫⁻ T, passCount vbl A i H T ∂table μ ≤ ENNReal.ofReal (x i / (1 - x i)) := by
  classical
  have hy0 : ∀ B, 0 ≤ (Measure.pi μ).real (A B) := fun B => measureReal_nonneg
  have hterm : ∀ S ∈ shapes vbl i H,
      ∫⁻ T, (if Proper vbl S ∧ Check vbl A S T then 1 else 0) ∂table μ ≤
        ENNReal.ofReal (∏ p ∈ S, (Measure.pi μ).real (A p.1)) := by
    intro S _
    by_cases hS : Proper vbl S
    · have heq : (fun T => if Proper vbl S ∧ Check vbl A S T then (1 : ℝ≥0∞) else 0) =
          {T | Check vbl A S T}.indicator 1 := by
        funext T
        simp only [hS, true_and, Set.indicator, Set.mem_ofPred_eq, Pi.one_apply]
      rw [heq, lintegral_indicator_one (measurableSet_check vbl A hAm S),
        measure_check_eq_prod μ vbl A hAm hA hS, ENNReal.ofReal_prod_of_nonneg fun p _ => hy0 _]
      exact (prod_congr rfl fun p _ => (ofReal_measureReal).symm).le
    · simp only [hS, false_and, ite_false, lintegral_zero]
      exact zero_le
  simp only [passCount]
  rw [lintegral_finsetSum _ fun S _ => ?_]
  · refine (sum_le_sum hterm).trans ?_
    rw [← ENNReal.ofReal_sum_of_nonneg fun S _ => prod_nonneg fun p _ => hy0 _]
    exact ENNReal.ofReal_le_ofReal (sum_prod_shapes_le vbl Γ hΓ hx hy0 hP i H)
  · by_cases hS : Proper vbl S
    · simp only [hS, true_and]
      exact Measurable.ite (measurableSet_check vbl A hAm S) measurable_const measurable_const
    · simp only [hS, false_and, ite_false]
      exact measurable_const

private theorem lintegral_iSup_passCount_le (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    (hP : ∀ i, (Measure.pi μ).real (A i) ≤ x i * ∏ j ∈ Γ i, (1 - x j)) (i : ι) :
    ∫⁻ T, ⨆ H, passCount vbl A i H T ∂table μ ≤ ENNReal.ofReal (x i / (1 - x i)) := by
  rw [lintegral_iSup (measurable_passCount vbl A hAm i)
    (fun _ _ h T => passCount_mono vbl A i T h)]
  exact iSup_le fun H => lintegral_passCount_le μ vbl A hAm hA Γ hΓ hx hP i H

omit [Fintype ι] in
/-- **Moser–Tardos, for all valid logs at once** [MoserTardos2010, Theorem 1.2]. Under the
local-lemma hypothesis, the expected supremum, over all valid logs `w` on the table, of the number
of resamplings of `A i` in `w` is at most `x i / (1 - x i)`. -/
theorem lintegral_iSup_count_le [Finite ι] (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V)) (Γ : ι → Finset ι)
    (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    (hP : ∀ i, (Measure.pi μ).real (A i) ≤ x i * ∏ j ∈ Γ i, (1 - x j)) (i : ι) :
    ∫⁻ T, ⨆ (w : List ι) (_ : IsLog vbl A T w), (w.count i : ℝ≥0∞) ∂table μ ≤
      ENNReal.ofReal (x i / (1 - x i)) := by
  have := Fintype.ofFinite ι
  calc ∫⁻ T, ⨆ (w : List ι) (_ : IsLog vbl A T w), (w.count i : ℝ≥0∞) ∂table μ
      ≤ ∫⁻ T, ⨆ H, passCount vbl A i H T ∂table μ :=
        lintegral_mono fun _ => iSup₂_le fun _ hw => count_le_iSup_passCount vbl A hA i hw
    _ ≤ _ := lintegral_iSup_passCount_le μ vbl A hAm hA Γ hΓ hx hP i

end Expectation

section Algorithm

variable {V ι : Type*} {α : V → Type*}

/-- The log (latest first) of the Moser–Tardos algorithm after `n` steps on the table `T`, under
the selection rule `sel`. At each step `sel T w` names the event to resample after the log `w`, or
returns `none`, after which the log stays fixed. -/
def run (sel : (∀ p : V × ℕ, α p.1) → List ι → Option ι) (T : ∀ p : V × ℕ, α p.1) :
    ℕ → List ι
  | 0 => []
  | n + 1 =>
    match sel T (run sel T n) with
    | none => run sel T n
    | some i => i :: run sel T n

theorem run_zero (sel : (∀ p : V × ℕ, α p.1) → List ι → Option ι) (T : ∀ p : V × ℕ, α p.1) :
    run sel T 0 = [] := by
  rw [run]

theorem run_succ_of_eq_none {sel : (∀ p : V × ℕ, α p.1) → List ι → Option ι}
    {T : ∀ p : V × ℕ, α p.1} {n : ℕ} (h : sel T (run sel T n) = none) :
    run sel T (n + 1) = run sel T n := by
  rw [run, h]

theorem run_succ_of_eq_some {sel : (∀ p : V × ℕ, α p.1) → List ι → Option ι}
    {T : ∀ p : V × ℕ, α p.1} {n : ℕ} {i : ι} (h : sel T (run sel T n) = some i) :
    run sel T (n + 1) = i :: run sel T n := by
  rw [run, h]

/-- Under a valid selection rule, which only selects occurring events, every prefix of the run is
a valid log. -/
theorem isLog_run [DecidableEq V] (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    {sel : (∀ p : V × ℕ, α p.1) → List ι → Option ι}
    (hsel : ∀ T w i, sel T w = some i → current vbl T w ∈ A i) (T : ∀ p : V × ℕ, α p.1) :
    ∀ n, IsLog vbl A T (run sel T n)
  | 0 => by
    rw [run_zero]
    exact isLog_nil vbl A T
  | n + 1 => by
    cases h : sel T (run sel T n) with
    | none =>
      rw [run_succ_of_eq_none h]
      exact isLog_run vbl A hsel T n
    | some i =>
      rw [run_succ_of_eq_some h, isLog_cons]
      exact ⟨hsel T _ i h, isLog_run vbl A hsel T n⟩

/-- The number of resamplings of `A i` performed by the algorithm on the table `T` under the rule
`sel` (possibly `∞`). -/
noncomputable def resamplings [DecidableEq ι] (sel : (∀ p : V × ℕ, α p.1) → List ι → Option ι)
    (i : ι) (T : ∀ p : V × ℕ, α p.1) : ℝ≥0∞ :=
  ⨆ n, ((run sel T n).count i : ℝ≥0∞)

theorem resamplings_def [DecidableEq ι] (sel : (∀ p : V × ℕ, α p.1) → List ι → Option ι)
    (i : ι) (T : ∀ p : V × ℕ, α p.1) :
    resamplings sel i T = ⨆ n, ((run sel T n).count i : ℝ≥0∞) := by
  rw [resamplings]

/-- Under a valid selection rule, the number of resamplings of `A i` is at most the largest number
of steps labelled `i` in a valid log on the table, a bound that does not depend on the rule. -/
theorem resamplings_le_iSup_count [DecidableEq V] [DecidableEq ι] (vbl : ι → Finset V)
    (A : ι → Set (∀ v, α v)) {sel : (∀ p : V × ℕ, α p.1) → List ι → Option ι}
    (hsel : ∀ T w i, sel T w = some i → current vbl T w ∈ A i) (i : ι)
    (T : ∀ p : V × ℕ, α p.1) :
    resamplings sel i T ≤ ⨆ (w : List ι) (_ : IsLog vbl A T w), (w.count i : ℝ≥0∞) := by
  rw [resamplings_def]
  exact iSup_le fun n => le_iSup₂_of_le (f := fun (w : List ι) (_ : IsLog vbl A T w) =>
    (w.count i : ℝ≥0∞)) (run sel T n) (isLog_run vbl A hsel T n) le_rfl

variable [DecidableEq V] (vbl : ι → Finset V)

open scoped Classical in
/-- The selection rule resampling some occurring event, if there is one. -/
noncomputable def greedy (A : ι → Set (∀ v, α v)) (T : ∀ p : V × ℕ, α p.1) (w : List ι) :
    Option ι :=
  if h : ∃ i, current vbl T w ∈ A i then some h.choose else none

theorem greedy_eq_some {A : ι → Set (∀ v, α v)} {T : ∀ p : V × ℕ, α p.1} {w : List ι} {i : ι}
    (h : greedy vbl A T w = some i) : current vbl T w ∈ A i := by
  unfold greedy at h
  split_ifs at h with hex
  cases h
  exact hex.choose_spec

theorem greedy_eq_none {A : ι → Set (∀ v, α v)} {T : ∀ p : V × ℕ, α p.1} {w : List ι}
    (h : greedy vbl A T w = none) (i : ι) : current vbl T w ∉ A i := by
  unfold greedy at h
  split_ifs at h with hex
  exact fun hi => hex ⟨i, hi⟩

end Algorithm

section Theorem

variable {V ι : Type*} [Fintype V] [DecidableEq V]
  {α : V → Type*} [∀ v, MeasurableSpace (α v)] (μ : ∀ v, Measure (α v))
  [∀ v, IsProbabilityMeasure (μ v)] (vbl : ι → Finset V)

/-- **The Moser–Tardos theorem** [MoserTardos2010, Theorem 1.2]. Let `x i ∈ [0, 1)` with
`Pr[A i] ≤ x i ∏ j ∈ Γ i, (1 - x j)`, where `Γ i` contains every other event sharing a variable
with `A i`. Then for every selection rule that only resamples occurring events, the expected
number of resamplings of `A i` is at most `x i / (1 - x i)`.

The rule is not assumed measurable, so `∫⁻` is the lower Lebesgue integral. The upper bound is
nevertheless the full statement: `exists_measurable_ge_resamplings` dominates the count, for every
valid rule, by one measurable function with the same bound. -/
theorem lintegral_resamplings_le [DecidableEq ι] [Finite ι] (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V)) (Γ : ι → Finset ι)
    (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    (hP : ∀ i, (Measure.pi μ).real (A i) ≤ x i * ∏ j ∈ Γ i, (1 - x j))
    {sel : (∀ p : V × ℕ, α p.1) → List ι → Option ι}
    (hsel : ∀ T w i, sel T w = some i → current vbl T w ∈ A i) (i : ι) :
    ∫⁻ T, resamplings sel i T ∂table μ ≤ ENNReal.ofReal (x i / (1 - x i)) :=
  (lintegral_mono fun T => resamplings_le_iSup_count vbl A hsel i T).trans
    (lintegral_iSup_count_le μ vbl A hAm hA Γ hΓ hx hP i)

omit [Fintype V] in
/-- Valid logs form a measurable set of tables. -/
theorem measurableSet_isLog (A : ι → Set (∀ v, α v)) (hAm : ∀ i, MeasurableSet (A i)) :
    ∀ w : List ι, MeasurableSet {T : ∀ p : V × ℕ, α p.1 | IsLog vbl A T w}
  | [] => by
    simp only [isLog_nil, Set.ofPred_true, MeasurableSet.univ]
  | j :: w => by
    have hcur : ∀ T : ∀ p : V × ℕ, α p.1, current vbl T w = fun v => T (v, uses vbl w v) :=
      fun T => funext fun v => current_apply vbl T w v
    have heq : {T : ∀ p : V × ℕ, α p.1 | IsLog vbl A T (j :: w)} =
        (fun T v => T (v, uses vbl w v)) ⁻¹' A j ∩ {T | IsLog vbl A T w} := by
      ext T
      rw [Set.mem_ofPred_eq, isLog_cons, hcur]
      rfl
    rw [heq]
    exact (measurable_read (fun v => uses vbl w v) (hAm j)).inter (measurableSet_isLog A hAm w)

omit [Fintype V] in
/-- The largest number of steps labelled `i` in a valid log is a measurable function of the
table. -/
theorem measurable_iSup_count [DecidableEq ι] [Countable ι] (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (i : ι) :
    Measurable fun T : ∀ p : V × ℕ, α p.1 =>
      ⨆ (w : List ι) (_ : IsLog vbl A T w), (w.count i : ℝ≥0∞) := by
  classical
  refine Measurable.iSup fun w => ?_
  have heq : (fun T : ∀ p : V × ℕ, α p.1 => ⨆ (_ : IsLog vbl A T w), (w.count i : ℝ≥0∞)) =
      fun T => if IsLog vbl A T w then (w.count i : ℝ≥0∞) else 0 :=
    funext fun T => iSup_eq_if _
  rw [heq]
  exact Measurable.ite (measurableSet_isLog vbl A hAm w) measurable_const measurable_const

/-- **Theorem 1.2 for the outer expectation** [MoserTardos2010]. Under the local-lemma hypothesis
there is a measurable function `g` of the table, with `∫⁻ g ≤ x i / (1 - x i)`, that bounds the
number of resamplings of `A i` under every valid selection rule. So the bound holds for the upper
(outer) expectation of the count as well, whether or not the rule is measurable. -/
theorem exists_measurable_ge_resamplings [DecidableEq ι] [Finite ι] (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V)) (Γ : ι → Finset ι)
    (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    (hP : ∀ i, (Measure.pi μ).real (A i) ≤ x i * ∏ j ∈ Γ i, (1 - x j)) (i : ι) :
    ∃ g : (∀ p : V × ℕ, α p.1) → ℝ≥0∞, Measurable g ∧
      ∫⁻ T, g T ∂table μ ≤ ENNReal.ofReal (x i / (1 - x i)) ∧
      ∀ sel : (∀ p : V × ℕ, α p.1) → List ι → Option ι,
        (∀ T w j, sel T w = some j → current vbl T w ∈ A j) →
          ∀ T, resamplings sel i T ≤ g T :=
  ⟨_, measurable_iSup_count vbl A hAm i, lintegral_iSup_count_le μ vbl A hAm hA Γ hΓ hx hP i,
    fun _ hsel T => resamplings_le_iSup_count vbl A hsel i T⟩

omit [Fintype V] [∀ v, MeasurableSpace (α v)] in
private theorem length_le_sum_iSup_passCount [DecidableEq ι] [Fintype ι] (A : ι → Set (∀ v, α v))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V)) {T : ∀ p : V × ℕ, α p.1}
    {w : List ι} (hw : IsLog vbl A T w) :
    (w.length : ℝ≥0∞) ≤ ∑ i, ⨆ H, passCount vbl A i H T := by
  have hlen : (w.length : ℝ≥0∞) = ∑ i, (w.count i : ℝ≥0∞) := by
    rw [← Nat.cast_sum]
    congr 1
    have := Multiset.sum_count_eq_card (s := univ) (m := (w : Multiset ι)) fun a _ => mem_univ a
    simpa using this.symm
  rw [hlen]
  exact sum_le_sum fun i _ => count_le_iSup_passCount vbl A hA i hw

/-- **The expected total number of resamplings** [MoserTardos2010, Theorem 1.2]: at most
`∑ i, x i / (1 - x i)`, for every valid selection rule. -/
theorem lintegral_sum_resamplings_le [DecidableEq ι] [Fintype ι] (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V)) (Γ : ι → Finset ι)
    (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    (hP : ∀ i, (Measure.pi μ).real (A i) ≤ x i * ∏ j ∈ Γ i, (1 - x j))
    {sel : (∀ p : V × ℕ, α p.1) → List ι → Option ι}
    (hsel : ∀ T w i, sel T w = some i → current vbl T w ∈ A i) :
    ∫⁻ T, ∑ i, resamplings sel i T ∂table μ ≤ ∑ i, ENNReal.ofReal (x i / (1 - x i)) := by
  calc ∫⁻ T, ∑ i, resamplings sel i T ∂table μ
      ≤ ∫⁻ T, ∑ i, ⨆ H, passCount vbl A i H T ∂table μ := by
        refine lintegral_mono fun T => sum_le_sum fun i _ => ?_
        rw [resamplings_def]
        exact iSup_le fun n => count_le_iSup_passCount vbl A hA i (isLog_run vbl A hsel T n)
    _ = ∑ i, ∫⁻ T, ⨆ H, passCount vbl A i H T ∂table μ :=
        lintegral_finsetSum _ fun i _ => Measurable.iSup fun H => measurable_passCount vbl A hAm i H
    _ ≤ _ := sum_le_sum fun i _ => lintegral_iSup_passCount_le μ vbl A hAm hA Γ hΓ hx hP i

omit [Fintype V] [DecidableEq V] [∀ v, MeasurableSpace (α v)] in
private theorem length_run_of_forall {sel : (∀ p : V × ℕ, α p.1) → List ι → Option ι}
    {T : ∀ p : V × ℕ, α p.1} (h : ∀ n, sel T (run sel T n) ≠ none) :
    ∀ n, (run sel T n).length = n
  | 0 => by rw [run_zero, List.length_nil]
  | n + 1 => by
    obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.1 (h n)
    rw [run_succ_of_eq_some hi, List.length_cons, length_run_of_forall h n]

/-- **Termination** [MoserTardos2010, Theorem 1.2]: under the local-lemma hypothesis, for every
valid selection rule, almost surely the rule stops (returns `none`) after finitely many steps. -/
theorem ae_exists_run_eq_none [Finite ι] (A : ι → Set (∀ v, α v)) (hAm : ∀ i, MeasurableSet (A i))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V)) (Γ : ι → Finset ι)
    (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    (hP : ∀ i, (Measure.pi μ).real (A i) ≤ x i * ∏ j ∈ Γ i, (1 - x j))
    {sel : (∀ p : V × ℕ, α p.1) → List ι → Option ι}
    (hsel : ∀ T w i, sel T w = some i → current vbl T w ∈ A i) :
    ∀ᵐ T ∂table μ, ∃ n, sel T (run sel T n) = none := by
  classical
  have := Fintype.ofFinite ι
  have hmeas : Measurable fun T => ∑ i, ⨆ H, passCount vbl A i H T :=
    Finset.measurable_sum _ fun i _ => Measurable.iSup fun H => measurable_passCount vbl A hAm i H
  have hint : ∫⁻ T, ∑ i, ⨆ H, passCount vbl A i H T ∂table μ ≠ ∞ := by
    rw [lintegral_finsetSum _ fun i _ =>
      Measurable.iSup fun H => measurable_passCount vbl A hAm i H]
    exact ENNReal.sum_ne_top.2 fun i _ => ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (lintegral_iSup_passCount_le μ vbl A hAm hA Γ hΓ hx hP i)
  filter_upwards [ae_lt_top hmeas hint] with T hT
  by_contra hne
  simp only [not_exists] at hne
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hT.ne
  have hlen := length_le_sum_iSup_passCount vbl A hA (isLog_run vbl A hsel T n)
  rw [length_run_of_forall hne n] at hlen
  exact lt_irrefl _ (hlen.trans_lt hn)

/-- **The algorithm finds a good assignment** [MoserTardos2010, Theorem 1.2]: under the
local-lemma hypothesis, for every valid selection rule that stops only when no event occurs,
almost surely the run reaches, after finitely many resamplings, an assignment in which no event
occurs. -/
theorem ae_exists_forall_notMem_run [Finite ι] (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    (hP : ∀ i, (Measure.pi μ).real (A i) ≤ x i * ∏ j ∈ Γ i, (1 - x j))
    {sel : (∀ p : V × ℕ, α p.1) → List ι → Option ι}
    (hsel : ∀ T w i, sel T w = some i → current vbl T w ∈ A i)
    (hstop : ∀ T w, sel T w = none → ∀ i, current vbl T w ∉ A i) :
    ∀ᵐ T ∂table μ, ∃ n, ∀ i, current vbl T (run sel T n) ∉ A i := by
  filter_upwards [ae_exists_run_eq_none μ vbl A hAm hA Γ hΓ hx hP hsel] with T ⟨n, hn⟩
  exact ⟨n, hstop T _ hn⟩

/-- **The greedy run finds a good assignment** [MoserTardos2010, Theorem 1.2]: under the
local-lemma hypothesis, almost surely the greedy run reaches, after finitely many resamplings, an
assignment in which no event occurs. -/
theorem ae_exists_forall_notMem_run_greedy [Finite ι] (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    (hP : ∀ i, (Measure.pi μ).real (A i) ≤ x i * ∏ j ∈ Γ i, (1 - x j)) :
    ∀ᵐ T ∂table μ, ∃ n, ∀ i, current vbl T (run (greedy vbl A) T n) ∉ A i :=
  ae_exists_forall_notMem_run μ vbl A hAm hA Γ hΓ hx hP (fun _ _ _ h => greedy_eq_some vbl h)
    fun _ _ h => greedy_eq_none vbl h

omit [DecidableEq V] in
/-- **The variable local lemma, constructively** [MoserTardos2010, Theorem 1.2]: under the
local-lemma hypothesis some assignment avoids every event. -/
theorem exists_forall_notMem [Finite ι] (A : ι → Set (∀ v, α v)) (hAm : ∀ i, MeasurableSet (A i))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V)) (Γ : ι → Finset ι)
    (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    (hP : ∀ i, (Measure.pi μ).real (A i) ≤ x i * ∏ j ∈ Γ i, (1 - x j)) :
    ∃ σ : ∀ v, α v, ∀ i, σ ∉ A i := by
  classical
  obtain ⟨T, n, hn⟩ := (ae_exists_forall_notMem_run_greedy μ vbl A hAm hA Γ hΓ hx hP).exists
  exact ⟨_, hn⟩

end Theorem

end Cslib.Probability.MoserTardos
