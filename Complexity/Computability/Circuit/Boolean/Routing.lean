/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Broadcast
public import Complexity.Computability.Circuit.Boolean.KeyedSort
import Complexity.Foundations.Data.List.OfFn
import Mathlib.Tactic.Ring

/-!
# Two-sort batched routing

The first sort groups matching keys and places false-tagged sources before true-tagged
requests. Shared broadcast replaces values while retaining every header bit. The second
sort computes an arbitrary restoration key from each retained header. It does not rewrite
headers or depend on the broadcast values.

Correctness is stated directly against the original unsorted input. Destination keys may
repeat. Without source uniqueness, each destination receives the bitwise OR of all matching
sources. A unique source is copied exactly. To recover a fixed output position, the client
identifies a unique restoration key and counts the smaller keys in the original input.

Both sorts have `2 ^ depth` records; padding is supplied by the caller. Keys and values may be
empty, selectors may repeat, and computed restoration keys are charged once per record.
Constants, negations and unused gates are included. The circuit constructor is executable;
these gate bounds do not certify its running time. Concrete table layout and padding bounds
for batched lookup are separate clients.

## Main definitions

* `Cslib.Circuits.Boolean.routeCircuit`: the complete two-sort router.
* `Cslib.Circuits.Boolean.routeCircuit.matchKey`: wiring that selects the matching key followed by
  its source/destination tag.
* `Cslib.Circuits.Boolean.routeCircuit.broadcast`: matching sort and shared broadcast.

## Main results

* `Cslib.Circuits.Boolean.routeCircuit_headers_perm`: all headers are retained.
* `Cslib.Circuits.Boolean.eval_routeCircuit_value_eq_true_iff`: destination OR semantics.
* `Cslib.Circuits.Boolean.eval_routeCircuit_value_of_unique_source`: fixed-position copying.
* `Cslib.Circuits.Boolean.four_mul_cost_program_routeCircuit`: exact weighted gate cost.
* `Cslib.Circuits.Boolean.four_mul_size_routeCircuit`: exact gate count.

## References

Adapts MassProduction/Nonuniform/BatchRouting.lean from
[S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
The computed-key sorting API preserves the original headers without a separate complementing pass.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open broadcastCircuit Finset

namespace routeCircuit

/-- Select the matching key followed by its source/destination tag. -/
def matchKey {h k : ℕ} (key : Fin k → Fin h) (tag : Fin h) (width : ℕ) :
    Circuit signature (h + width) (k + 1) :=
  Circuit.wiring signature (Fin.snoc (α := fun _ => Fin (h + width))
    (Fin.castAdd width ∘ key) (Fin.castAdd width tag))

/-- Sort by matching key and tag, then broadcast values while retaining every header. -/
def broadcast {h k : ℕ} (key : Fin k → Fin h) (tag : Fin h) (depth width : ℕ) :
    Circuit signature (BitonicSort.arity depth * (h + width))
      (BitonicSort.arity depth * (h + width)) :=
  (broadcastCircuit key tag (BitonicSort.arity depth) width).comp
    (keyedSortCircuit (matchKey key tag width) depth true)

/-- Matching and broadcast preserve the multiset of complete headers. -/
theorem headers_perm {h k depth width : ℕ} (key : Fin k → Fin h) (tag : Fin h)
    (x : BitString (BitonicSort.arity depth * (h + width))) :
    (List.ofFn (header ((broadcast key tag depth width).eval interpretation x))).Perm
      (List.ofFn (header x)) := by
  rw [broadcast, Circuit.eval_comp, funext (eval_broadcastCircuit_header key tag _)]
  change (List.ofFn (fun record => directProductInput _ record ∘ Fin.castAdd width)).Perm
    (List.ofFn (fun record => directProductInput x record ∘ Fin.castAdd width))
  simpa only [List.map_ofFn, Function.comp_def, header] using
    (keyedSortCircuit_perm (matchKey key tag width) depth true x).map
      (fun row : BitString (h + width) => row ∘ Fin.castAdd width)

/-- Each destination after matching receives the OR of its original matching sources. -/
theorem value_eq_true_iff {h k depth width : ℕ} (key : Fin k → Fin h) (tag : Fin h)
    (x : BitString (BitonicSort.arity depth * (h + width)))
    (destination : Fin (BitonicSort.arity depth))
    (htag : header ((broadcast key tag depth width).eval interpretation x) destination tag = true)
    (bit : Fin width) :
    value ((broadcast key tag depth width).eval interpretation x) destination bit = true ↔
      ∃ source, header x source ∘ key =
        header ((broadcast key tag depth width).eval interpretation x) destination ∘ key ∧
        header x source tag = false ∧ value x source bit = true := by
  simp only [broadcast, Circuit.eval_comp, eval_broadcastCircuit_header] at htag ⊢
  rw [eval_broadcastCircuit_value_eq_true_iff key tag _ ?_ destination htag bit]
  · exact List.Perm.exists_ofFn_iff
      (keyedSortCircuit_perm (matchKey key tag width) depth true x)
      (fun row => (row ∘ Fin.castAdd width) ∘ key = _ ∧
        row (Fin.castAdd width tag) = false ∧ row (Fin.natAdd h bit) = true)
  · simpa only [matchKey, Circuit.eval_wiring, Fin.comp_snoc, Function.comp_assoc,
      Function.comp_apply, header] using
      monotone_keyedSortCircuit (matchKey key tag width) depth x

end routeCircuit

/-- Sort, broadcast, then sort by a computed header key. Both sorts retain the original header. -/
def routeCircuit {h k o : ℕ} (key : Fin k → Fin h) (tag : Fin h)
    (order : Circuit signature h o) (depth width : ℕ) :
    Circuit signature (BitonicSort.arity depth * (h + width))
      (BitonicSort.arity depth * (h + width)) :=
  (keyedSortCircuit (order.comp (Circuit.wiring signature (Fin.castAdd width))) depth true).comp
    (routeCircuit.broadcast key tag depth width)

/-- The complete router preserves the multiset of headers, including all routing metadata. -/
theorem routeCircuit_headers_perm {h k o depth width : ℕ}
    (key : Fin k → Fin h) (tag : Fin h) (order : Circuit signature h o)
    (x : BitString (BitonicSort.arity depth * (h + width))) :
    (List.ofFn (header ((routeCircuit key tag order depth width).eval interpretation x))).Perm
      (List.ofFn (header x)) := by
  apply List.Perm.trans _ (routeCircuit.headers_perm key tag x)
  rw [routeCircuit, Circuit.eval_comp]
  change (List.ofFn (fun record => directProductInput _ record ∘ Fin.castAdd width)).Perm
    (List.ofFn (fun record => directProductInput _ record ∘ Fin.castAdd width))
  simpa only [List.map_ofFn, Function.comp_def] using
    (keyedSortCircuit_perm (order.comp (Circuit.wiring signature (Fin.castAdd width))) depth true
      ((routeCircuit.broadcast key tag depth width).eval interpretation x)).map
      (fun row : BitString (h + width) => row ∘ Fin.castAdd width)

/-- The final headers are ordered by the computed restoration key. -/
theorem monotone_routeCircuit {h k o depth width : ℕ}
    (key : Fin k → Fin h) (tag : Fin h) (order : Circuit signature h o)
    (x : BitString (BitonicSort.arity depth * (h + width))) :
    Monotone (fun record => toLex (order.eval interpretation
      (header ((routeCircuit key tag order depth width).eval interpretation x) record))) := by
  simpa only [routeCircuit, Circuit.eval_comp, Circuit.eval_wiring, header] using
    monotone_keyedSortCircuit (order.comp (Circuit.wiring signature (Fin.castAdd width))) depth
      ((routeCircuit.broadcast key tag depth width).eval interpretation x)

/-- A destination receives the OR of matching original sources, even with repeated source keys. -/
theorem eval_routeCircuit_value_eq_true_iff {h k o depth width : ℕ}
    (key : Fin k → Fin h) (tag : Fin h) (order : Circuit signature h o)
    (x : BitString (BitonicSort.arity depth * (h + width)))
    (destination : Fin (BitonicSort.arity depth))
    (htag : header ((routeCircuit key tag order depth width).eval interpretation x)
      destination tag = true) (bit : Fin width) :
    value ((routeCircuit key tag order depth width).eval interpretation x) destination bit = true ↔
      ∃ source, header x source ∘ key =
        header ((routeCircuit key tag order depth width).eval interpretation x) destination ∘ key ∧
        header x source tag = false ∧ value x source bit = true := by
  simp only [routeCircuit, Circuit.eval_comp] at htag ⊢
  let y := (routeCircuit.broadcast key tag depth width).eval interpretation x
  let z := (keyedSortCircuit
    (order.comp (Circuit.wiring signature (Fin.castAdd width))) depth true).eval interpretation y
  change header z destination tag = true at htag
  change value z destination bit = true ↔
    ∃ source, header x source ∘ key = header z destination ∘ key ∧
      header x source tag = false ∧ value x source bit = true
  have perm := keyedSortCircuit_perm
    (order.comp (Circuit.wiring signature (Fin.castAdd width))) depth true y
  obtain ⟨d, hd⟩ := List.mem_ofFn.mp (perm.mem_iff.mp (List.mem_ofFn.mpr ⟨destination, rfl⟩))
  have hh : header z destination = header y d :=
    congrArg (fun row : BitString (h + width) => row ∘ Fin.castAdd width) hd.symm
  have hv : value z destination = value y d :=
    congrArg (fun row : BitString (h + width) => row ∘ Fin.natAdd h) hd.symm
  rw [hh] at htag
  rw [hv, hh]
  exact routeCircuit.value_eq_true_iff key tag x d htag bit

open scoped Classical in
/-- A uniquely keyed destination header is restored to its rank in the original input. -/
theorem eval_routeCircuit_header_of_rank {h k o depth width : ℕ}
    (key : Fin k → Fin h) (tag : Fin h) (order : Circuit signature h o)
    (x : BitString (BitonicSort.arity depth * (h + width)))
    (destination target : Fin (BitonicSort.arity depth))
    (unique : ∀ i, order.eval interpretation (header x i) =
      order.eval interpretation (header x destination) → i = destination)
    (rank : #{i | toLex (order.eval interpretation (header x i)) <
      toLex (order.eval interpretation (header x destination))} = target.val) :
    header ((routeCircuit key tag order depth width).eval interpretation x) target =
      header x destination :=
  List.Perm.apply_ofFn_eq_of_rank (β := Lex (BitString o))
    (routeCircuit_headers_perm key tag order x).symm
    (fun row => toLex (order.eval interpretation row)) (monotone_routeCircuit key tag order x)
    destination target (fun i h => unique i h) (by
      convert rank using 1
      apply congrArg Finset.card
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rfl)

open scoped Classical in
/-- At a fixed restored position, destination values are the OR of matching original sources. -/
theorem eval_routeCircuit_value_eq_true_iff_of_rank {h k o depth width : ℕ}
    (key : Fin k → Fin h) (tag : Fin h) (order : Circuit signature h o)
    (x : BitString (BitonicSort.arity depth * (h + width)))
    (destination target : Fin (BitonicSort.arity depth))
    (unique : ∀ i, order.eval interpretation (header x i) =
      order.eval interpretation (header x destination) → i = destination)
    (rank : #{i | toLex (order.eval interpretation (header x i)) <
      toLex (order.eval interpretation (header x destination))} = target.val)
    (htag : header x destination tag = true) (bit : Fin width) :
    value ((routeCircuit key tag order depth width).eval interpretation x) target bit = true ↔
      ∃ source, header x source ∘ key = header x destination ∘ key ∧
        header x source tag = false ∧ value x source bit = true := by
  have hh := eval_routeCircuit_header_of_rank key tag order x destination target unique rank
  rw [eval_routeCircuit_value_eq_true_iff key tag order x target (hh ▸ htag) bit, hh]

open scoped Classical in
/-- A uniquely keyed destination copies its unique matching source to a fixed position. -/
theorem eval_routeCircuit_value_of_unique_source {h k o depth width : ℕ}
    (key : Fin k → Fin h) (tag : Fin h) (order : Circuit signature h o)
    (x : BitString (BitonicSort.arity depth * (h + width)))
    (source destination target : Fin (BitonicSort.arity depth))
    (uniqueDestination : ∀ i, order.eval interpretation (header x i) =
      order.eval interpretation (header x destination) → i = destination)
    (rank : #{i | toLex (order.eval interpretation (header x i)) <
      toLex (order.eval interpretation (header x destination))} = target.val)
    (hkey : header x source ∘ key = header x destination ∘ key)
    (hsource : header x source tag = false) (hdestination : header x destination tag = true)
    (uniqueSource : ∀ i, header x i ∘ key = header x source ∘ key →
      header x i tag = false → i = source) :
    value ((routeCircuit key tag order depth width).eval interpretation x) target =
      value x source := by
  funext bit
  apply Bool.eq_iff_iff.mpr
  rw [eval_routeCircuit_value_eq_true_iff_of_rank key tag order x destination target
    uniqueDestination rank hdestination bit]
  constructor
  · rintro ⟨i, hi, ht, hv⟩
    exact uniqueSource i (hi.trans hkey.symm) ht ▸ hv
  · intro hv
    exact ⟨source, hkey, hsource, hv⟩

/-- Exact additive weighted cost of the two sorting circuits and shared broadcast. -/
theorem cost_program_routeCircuit {h k o : ℕ}
    (key : Fin k → Fin h) (tag : Fin h) (order : Circuit signature h o)
    (depth width : ℕ) (cost : signature.Op → ℕ) :
    (routeCircuit key tag order depth width).program.cost cost =
      (keyedSortCircuit (routeCircuit.matchKey key tag width) depth true).program.cost cost +
      (broadcastCircuit key tag (BitonicSort.arity depth) width).program.cost cost +
      (keyedSortCircuit (order.comp (Circuit.wiring signature (Fin.castAdd width)))
        depth true).program.cost cost := by
  simp only [routeCircuit, routeCircuit.broadcast, Circuit.cost_program_comp]

/-- Exact weighted cost, charging restoration keys once per record and all broadcast gates. -/
theorem four_mul_cost_program_routeCircuit {h k o : ℕ}
    (key : Fin k → Fin h) (tag : Fin h) (order : Circuit signature h o)
    (depth width : ℕ) (cost : signature.Op → ℕ) :
    4 * (routeCircuit key tag order depth width).program.cost cost =
      4 * 2 ^ depth * order.program.cost cost + depth * (depth + 1) * 2 ^ depth *
        ((compareSwapCircuit
          (Fin.castAdd (h + width) : Fin (k + 1) → Fin (k + 1 + (h + width)))).program.cost cost +
        (compareSwapCircuit
          (Fin.castAdd (h + width) : Fin o → Fin (o + (h + width)))).program.cost cost) +
      4 * ((cost (.const false) + (2 ^ depth - 1) *
        (cost (.const true) + k * (3 * cost .and + 2 * cost .not + cost .or))) +
        width * (cost (.const false) + 2 ^ depth * (cost .not + 2 * cost .and + cost .or))) := by
  rw [cost_program_routeCircuit, Nat.mul_add, Nat.mul_add,
    four_mul_cost_program_keyedSortCircuit, four_mul_cost_program_keyedSortCircuit,
    cost_program_broadcastCircuit, BitonicSort.arity_eq_two_pow]
  simp only [routeCircuit.matchKey, Circuit.cost_program_wiring, Circuit.cost_program_comp,
    Nat.zero_add, Nat.mul_zero, pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0),
    ↓reduceIte]
  ring

/-- Exact gate count; the factor four avoids natural division, including at depth zero. -/
theorem four_mul_size_routeCircuit {h k o : ℕ}
    (key : Fin k → Fin h) (tag : Fin h) (order : Circuit signature h o)
    (depth width : ℕ) :
    4 * (routeCircuit key tag order depth width).size =
      4 * 2 ^ depth * order.size + depth * (depth + 1) * 2 ^ depth *
        (12 * (k + 1 + o + h + width) + 4) +
      4 * (1 + (2 ^ depth - 1) * (6 * k + 1) + width * (1 + 4 * 2 ^ depth)) := by
  have positive : 0 < h := Nat.zero_lt_of_lt tag.isLt
  have h₁ : k + 1 + (h + width) ≠ 0 := by lia
  have h₂ : o + (h + width) ≠ 0 := by lia
  have hc := four_mul_cost_program_routeCircuit key tag order depth width (fun _ => 1)
  simp only [Program.cost_const, one_mul, size_compareSwapCircuit, h₁, h₂, ↓reduceIte] at hc
  convert hc using 1
  ring

end Cslib.Circuits.Boolean
