/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.PACLearning.Compression.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Data.List.MinMax

/-!
# Compression schemes for thresholds and intervals

On a linear order, the binary concepts whose positive examples form a lower set have a sample
compression scheme of size `1`: keep the positive example with the largest instance, and label
`x` positive when it lies below a kept positive example. On `ℝ` or `ℕ` these concepts are exactly
the thresholds `x ≤ θ` and `x < θ` and the two constants; on an order such as `ℚ` they also
include cuts at irrational points. The concepts whose positive examples form an order-connected
set (on `ℝ` or `ℕ`, the intervals) have a scheme of size `2`: keep the positive examples with
the smallest and the largest instance, and label `x` positive when it lies between two kept
positive examples. Intervals are the one-dimensional case of the axis-aligned rectangles of
[ShalevShwartzBenDavid2014, §30.2.1], whose scheme keeps the two extremal positive examples in
each dimension.

Both reconstructions are measurable on a linear order with the order topology and a second
countable Borel structure, such as `ℝ`, and on countable domains such as `ℕ`
(`measurableReconstruction_lowerSetScheme`, `measurableReconstruction_ordConnectedScheme`), so the
compression bound gives PAC learners from `m` examples whenever
`(m + 1) (1 - ε) ^ (m - 1) ≤ δ` for thresholds and `(m + 1) ^ 2 (1 - ε) ^ (m - 2) ≤ δ` for
intervals. `CslibFrontier/MachineLearning/PACLearning/Compression/Thresholds.lean` applies the
threshold scheme to the thresholds of the mistake-bound development, whose Littlestone dimension is
infinite.

## Main definitions

- `lowerSetClass α`: the binary concepts on `α` whose positive examples form a lower set.
- `ordConnectedClass α`: the binary concepts whose positive examples form an order-connected set.
- `lowerSetScheme`: a sample compression scheme of size `1` for `lowerSetClass α`.
- `ordConnectedScheme`: a sample compression scheme of size `2` for `ordConnectedClass α`.

## Main results

- `measurableReconstruction_lowerSetScheme`, `measurableReconstruction_ordConnectedScheme`: the
  reconstructions are measurable on second countable order topologies.
- `isPACLearnable_lowerSetClass`, `isPACLearnable_ordConnectedClass`: both classes are PAC
  learnable in the realizable setting.

## References

* [S. Floyd, M. K. Warmuth, *Sample compression, learnability, and the Vapnik–Chervonenkis
  dimension*][FloydWarmuth1995]
* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014]
-/

public section

open MeasureTheory Set

namespace Cslib.MachineLearning.PACLearning

/-- The indices of the positive examples of a sample, in increasing order. -/
@[expose] def positiveIndices {α : Type*} {m : ℕ} (S : LabeledSample α Bool m) : List (Fin m) :=
  (List.finRange m).filter fun i => (S i).2

/-- An index is in `positiveIndices S` when its example is labelled `true`. -/
theorem mem_positiveIndices {α : Type*} {m : ℕ} {S : LabeledSample α Bool m} {i : Fin m} :
    i ∈ positiveIndices S ↔ (S i).2 = true := by
  simp [positiveIndices]

variable {α : Type*} [LinearOrder α]

/-- The binary concepts whose positive examples form a lower set. On `ℝ` or `ℕ` these are exactly
the thresholds `x ≤ θ` and `x < θ` and the two constants. -/
def lowerSetClass (α : Type*) [LinearOrder α] : ConceptClass α Bool :=
  {c | IsLowerSet {x | c x = true}}

/-- The binary concepts whose positive examples form an order-connected set. On `ℝ` or `ℕ` these
are exactly the intervals of every kind, including the empty one. -/
def ordConnectedClass (α : Type*) [LinearOrder α] : ConceptClass α Bool :=
  {c | OrdConnected {x | c x = true}}

/-- A concept is in `lowerSetClass α` when every instance below a positive instance is
positive. -/
theorem mem_lowerSetClass {c : α → Bool} :
    c ∈ lowerSetClass α ↔ ∀ ⦃x y⦄, y ≤ x → c x = true → c y = true := Iff.rfl

/-- A concept is in `ordConnectedClass α` when every instance between two positive instances is
positive. -/
theorem mem_ordConnectedClass {c : α → Bool} :
    c ∈ ordConnectedClass α ↔ ∀ ⦃x y z⦄, x ≤ y → y ≤ z → c x = true → c z = true → c y = true :=
  ⟨fun h _ _ _ hxy hyz hx hz => OrdConnected.out h hx hz ⟨hxy, hyz⟩,
    fun h => ⟨fun _ hx _ hz _ hy => h hy.1 hy.2 hx hz⟩⟩

/-- Every lower set is order-connected. -/
theorem lowerSetClass_subset_ordConnectedClass : lowerSetClass α ⊆ ordConnectedClass α :=
  fun _ hc => hc.ordConnected

/-- **Thresholds have a compression scheme of size `1`.** Keep the positive example with the
largest instance; label `x` positive when some kept positive example lies above it. -/
@[expose] def lowerSetScheme : SampleCompressionScheme (lowerSetClass α) 1 where
  compress S := ((positiveIndices S).argmax fun i => (S i).1).toList
  reconstruct T x := T.any fun p => p.2 && decide (x ≤ p.1)
  length_compress_le _ _ := Option.length_toList_le
  reconstruct_correct S hS i := by
    obtain ⟨c, hc, hcS⟩ := hS
    rw [Bool.eq_iff_iff, List.any_eq_true]
    constructor
    · rintro ⟨p, hp, hpx⟩
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hp
      rw [Bool.and_eq_true, decide_eq_true_eq] at hpx
      rw [hcS i]
      exact mem_lowerSetClass.1 hc hpx.2 ((hcS j).symm.trans hpx.1)
    · intro hi
      have hne : positiveIndices S ≠ [] := List.ne_nil_of_mem (mem_positiveIndices.2 hi)
      obtain ⟨j, hj⟩ : ∃ j, (positiveIndices S).argmax (fun i => (S i).1) = some j :=
        Option.ne_none_iff_exists'.1 fun h => hne (List.argmax_eq_none.1 h)
      refine ⟨S j, List.mem_map.2 ⟨j, by simp [hj], rfl⟩, ?_⟩
      rw [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨mem_positiveIndices.1 (List.argmax_mem hj),
        List.le_of_mem_argmax (f := fun i => (S i).1) (mem_positiveIndices.2 hi) hj⟩

/-- **Intervals have a compression scheme of size `2`.** Keep the positive examples with the
smallest and the largest instance; label `x` positive when it lies between two kept positive
examples. -/
@[expose] def ordConnectedScheme : SampleCompressionScheme (ordConnectedClass α) 2 where
  compress S := ((positiveIndices S).argmin fun i => (S i).1).toList ++
    ((positiveIndices S).argmax fun i => (S i).1).toList
  reconstruct T x := (T.any fun p => p.2 && decide (p.1 ≤ x)) &&
    (T.any fun p => p.2 && decide (x ≤ p.1))
  length_compress_le _ _ := by
    rw [List.length_append]
    exact Nat.add_le_add Option.length_toList_le Option.length_toList_le
  reconstruct_correct S hS i := by
    obtain ⟨c, hc, hcS⟩ := hS
    rw [Bool.eq_iff_iff, Bool.and_eq_true, List.any_eq_true, List.any_eq_true]
    constructor
    · rintro ⟨⟨p, hp, hpx⟩, ⟨q, hq, hqx⟩⟩
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hp
      obtain ⟨l, -, rfl⟩ := List.mem_map.1 hq
      rw [Bool.and_eq_true, decide_eq_true_eq] at hpx hqx
      rw [hcS i]
      exact mem_ordConnectedClass.1 hc hpx.2 hqx.2 ((hcS j).symm.trans hpx.1)
        ((hcS l).symm.trans hqx.1)
    · intro hi
      have hne : positiveIndices S ≠ [] := List.ne_nil_of_mem (mem_positiveIndices.2 hi)
      obtain ⟨j, hj⟩ : ∃ j, (positiveIndices S).argmin (fun i => (S i).1) = some j :=
        Option.ne_none_iff_exists'.1 fun h => hne (List.argmin_eq_none.1 h)
      obtain ⟨l, hl⟩ : ∃ l, (positiveIndices S).argmax (fun i => (S i).1) = some l :=
        Option.ne_none_iff_exists'.1 fun h => hne (List.argmax_eq_none.1 h)
      refine ⟨⟨S j, List.mem_map.2 ⟨j, by simp [hj], rfl⟩, ?_⟩,
        ⟨S l, List.mem_map.2 ⟨l, by simp [hl], rfl⟩, ?_⟩⟩
      · rw [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨mem_positiveIndices.1 (List.argmin_mem hj),
          List.le_of_mem_argmin (f := fun i => (S i).1) (mem_positiveIndices.2 hi) hj⟩
      · rw [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨mem_positiveIndices.1 (List.argmax_mem hl),
          List.le_of_mem_argmax (f := fun i => (S i).1) (mem_positiveIndices.2 hi) hl⟩

variable [MeasurableSpace α]

omit [LinearOrder α] in
/-- If the relation `r` is measurable, the test "some kept positive example `p` has `r p.1 x`" is
measurable in the kept examples and `x`. -/
private theorem measurable_any_ofFn (j : ℕ) (r : α → α → Prop)
    [DecidableRel r] (hr : MeasurableSet {q : α × α | r q.1 q.2}) :
    Measurable fun q : LabeledSample α Bool j × α =>
      (List.ofFn q.1).any fun p => p.2 && decide (r p.1 q.2) := by
  refine measurable_to_bool ?_
  have : (fun q : LabeledSample α Bool j × α =>
      (List.ofFn q.1).any fun p => p.2 && decide (r p.1 q.2)) ⁻¹' {true} =
      ⋃ t : Fin j, ({q | (q.1 t).2 = true} ∩ {q | r (q.1 t).1 q.2}) := by
    ext q
    simp [List.any_eq_true, List.mem_ofFn]
  rw [this]
  refine MeasurableSet.iUnion fun t => (measurableSet_eq_fun (by fun_prop) measurable_const).inter
    (hr.preimage (f := fun q : LabeledSample α Bool j × α => ((q.1 t).1, q.2)) (by fun_prop))

/-- The threshold reconstruction is measurable on a second countable order topology with its
Borel sets, for example on `ℝ`. -/
theorem measurableReconstruction_lowerSetScheme [TopologicalSpace α] [OrderClosedTopology α]
    [SecondCountableTopology α] [OpensMeasurableSpace α] :
    MeasurableReconstruction (lowerSetScheme (α := α)).reconstruct :=
  measurableReconstruction_of_measurable fun j =>
    measurable_any_ofFn j (fun a x => x ≤ a) (measurableSet_le measurable_snd measurable_fst)

/-- The interval reconstruction is measurable on a second countable order topology with its
Borel sets, for example on `ℝ`. -/
theorem measurableReconstruction_ordConnectedScheme [TopologicalSpace α] [OrderClosedTopology α]
    [SecondCountableTopology α] [OpensMeasurableSpace α] :
    MeasurableReconstruction (ordConnectedScheme (α := α)).reconstruct :=
  measurableReconstruction_of_measurable fun j =>
    (measurable_of_countable fun b : Bool × Bool => b.1 && b.2).comp
      ((measurable_any_ofFn j (fun a x => a ≤ x)
        (measurableSet_le measurable_fst measurable_snd)).prodMk
      (measurable_any_ofFn j (fun a x => x ≤ a) (measurableSet_le measurable_snd measurable_fst)))

/-- Lower-set concepts (thresholds) on a second countable order topology are PAC learnable in the
realizable setting. -/
theorem isPACLearnable_lowerSetClass [TopologicalSpace α] [OrderClosedTopology α]
    [SecondCountableTopology α] [OpensMeasurableSpace α] :
    IsPACLearnable (lowerSetClass α) (realizableDistributions (lowerSetClass α)) :=
  lowerSetScheme.isPACLearnable measurableReconstruction_lowerSetScheme

/-- Order-connected concepts (intervals) on a second countable order topology are PAC learnable in
the realizable setting. -/
theorem isPACLearnable_ordConnectedClass [TopologicalSpace α] [OrderClosedTopology α]
    [SecondCountableTopology α] [OpensMeasurableSpace α] :
    IsPACLearnable (ordConnectedClass α) (realizableDistributions (ordConnectedClass α)) :=
  ordConnectedScheme.isPACLearnable measurableReconstruction_ordConnectedScheme

end Cslib.MachineLearning.PACLearning
