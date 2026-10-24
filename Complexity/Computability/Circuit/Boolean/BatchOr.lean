/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.RoutingValues
public import Complexity.Computability.Circuit.Boolean.Substitution
import Complexity.Foundations.Data.Nat.Log
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Shared OR lookup over dynamic records

Sources supply keys and value fields; queries supply keys. One source array serves every query,
including repeated queries. A query receives the bitwise OR of all matching source values;
missing keys receive zero. The circuit sorts once and reverses saved swaps on the answer fields,
so it needs neither request identifiers nor a second sort.

Inputs are ordinary variables or Boolean constants, using the existing `substitute` interface.
All constants and negations are charged. Input preparation uses two shared constant gates even
when unused. Sources, queries, keys, and values may all be empty. Padding records are destinations
and cannot introduce a spurious source. These gate bounds do not certify constructor runtime.

## Main definitions

* `Cslib.Circuits.Boolean.batchOrCircuit`: shared OR lookup with automatic padding.
* `Cslib.Circuits.Boolean.batchOrCircuit.withPadding`: the same construction with supplied padding.
* `Cslib.Circuits.Boolean.batchOrCircuit.rows`, `batchOrCircuit.substitution`,
  `batchOrCircuit.requestIndex`, `batchOrCircuit.outputs`: record layout and output wiring for the
  padded network.
* `Cslib.Circuits.Boolean.batchOrCircuit.depth`, `batchOrCircuit.padding`: canonical sorting depth
  and padding count for a batch of requests and sources.

## Main results

* `Cslib.Circuits.Boolean.eval_batchOrCircuit_iff`: exact matching-source semantics.
* `Cslib.Circuits.Boolean.batchOrCircuit.cost_program_withPadding`: arbitrary weighted cost.
* `Cslib.Circuits.Boolean.batchOrCircuit.size_withPadding`: exact gate count.
* `Cslib.Circuits.Boolean.size_batchOrCircuit_le`: a factored bound for canonical padding.

## References

Simplifies MassProduction/Nonuniform/BatchOrCircuit.lean in
[S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open bitonicSortTraceCircuit broadcastCircuit

namespace batchOrCircuit

section Layout

variable {input sources requests k v padding d : ℕ}
variable (sourceKeys : Fin sources → Fin k → Fin input ⊕ Bool)
  (sourceValues : Fin sources → Fin v → Fin input ⊕ Bool)
  (queryKeys : Fin requests → Fin k → Fin input ⊕ Bool)

/-- Symbolic request records, source records, and padding destinations. -/
def rows : Fin (requests + (sources + padding)) → Fin (k + 1 + v) → Fin input ⊕ Bool :=
  Fin.append
    (fun request => Fin.append (Fin.snoc (queryKeys request) (.inr true)) (fun _ => .inr false))
    (Fin.append
      (fun source => Fin.append (Fin.snoc (sourceKeys source) (.inr false)) (sourceValues source))
      (fun _ => Sum.inr ∘ Fin.append (Fin.snoc (fun _ => false) true) (fun _ => false)))

/-- Flatten symbolic records into variables and constants for the padded network. -/
def substitution (h : requests + (sources + padding) = BitonicSort.arity d) :
    Fin (BitonicSort.arity d * (k + 1 + v)) → Fin input ⊕ Bool :=
  fun i => let jb := finProdFinEquiv.symm i
    rows sourceKeys sourceValues queryKeys (Fin.cast h.symm jb.1) jb.2

/-- Interpret the record layout on the circuit input. -/
private def layout (h : requests + (sources + padding) = BitonicSort.arity d)
    (x : BitString input) : BitString (BitonicSort.arity d * (k + 1 + v)) :=
  substitute (substitution sourceKeys sourceValues queryKeys h) x

/-- The original position of a request in the padded layout. -/
def requestIndex (h : requests + (sources + padding) = BitonicSort.arity d)
    (request : Fin requests) : Fin (BitonicSort.arity d) :=
  Fin.cast h (Fin.castAdd (sources + padding) request)

/-- The original position of a source in the padded layout. -/
private def sourceIndex (h : requests + (sources + padding) = BitonicSort.arity d)
    (source : Fin sources) : Fin (BitonicSort.arity d) :=
  Fin.cast h (Fin.natAdd requests (Fin.castAdd padding source))

private theorem layout_apply (h : requests + (sources + padding) = BitonicSort.arity d)
    (x : BitString input) (i : Fin (requests + (sources + padding))) (bit : Fin (k + 1 + v)) :
    directProductInput (layout sourceKeys sourceValues queryKeys h x) (Fin.cast h i) bit =
      (rows sourceKeys sourceValues queryKeys i bit).elim x id := by
  simp [layout, substitution, substitute, directProductInput]

private theorem request_key (h : requests + (sources + padding) = BitonicSort.arity d)
    (x : BitString input) (request : Fin requests) :
    header (layout sourceKeys sourceValues queryKeys h x) (requestIndex h request) ∘ Fin.castSucc =
      substitute (queryKeys request) x := by
  funext bit
  simp [header, Function.comp_def, requestIndex, layout_apply, rows, substitute]

private theorem request_tag (h : requests + (sources + padding) = BitonicSort.arity d)
    (x : BitString input) (request : Fin requests) :
    header (layout sourceKeys sourceValues queryKeys h x) (requestIndex h request) (Fin.last k) =
      true := by
  simp [header, Function.comp_def, requestIndex, layout_apply, rows]

private theorem source_key (h : requests + (sources + padding) = BitonicSort.arity d)
    (x : BitString input) (source : Fin sources) :
    header (layout sourceKeys sourceValues queryKeys h x) (sourceIndex h source) ∘ Fin.castSucc =
      substitute (sourceKeys source) x := by
  funext bit
  simp [header, Function.comp_def, sourceIndex, layout_apply, rows, substitute]

private theorem source_tag (h : requests + (sources + padding) = BitonicSort.arity d)
    (x : BitString input) (source : Fin sources) :
    header (layout sourceKeys sourceValues queryKeys h x) (sourceIndex h source) (Fin.last k) =
      false := by
  simp [header, Function.comp_def, sourceIndex, layout_apply, rows]

private theorem source_value (h : requests + (sources + padding) = BitonicSort.arity d)
    (x : BitString input) (source : Fin sources) :
    value (layout sourceKeys sourceValues queryKeys h x) (sourceIndex h source) =
      substitute (sourceValues source) x := by
  funext bit
  simp [value, Function.comp_def, sourceIndex, layout_apply, rows, substitute]

private theorem exists_source_iff (h : requests + (sources + padding) = BitonicSort.arity d)
    (x : BitString input) (p : BitString k → BitString v → Prop) :
    (∃ i, header (layout sourceKeys sourceValues queryKeys h x) i (Fin.last k) = false ∧
      p (header (layout sourceKeys sourceValues queryKeys h x) i ∘ Fin.castSucc)
        (value (layout sourceKeys sourceValues queryKeys h x) i)) ↔
      ∃ j, p (substitute (sourceKeys j) x) (substitute (sourceValues j) x) := by
  constructor
  · rintro ⟨i, ht, hp⟩
    obtain ⟨i, rfl⟩ := (finCongr h).surjective i
    revert ht hp
    refine Fin.addCases (fun request ht hp => ?_) (fun i => ?_) i
    · have := request_tag sourceKeys sourceValues queryKeys h x request
      simp only [requestIndex] at this
      exact Bool.noConfusion (this.symm.trans ht)
    · refine Fin.addCases (fun j ht hp => ?_) (fun pad ht hp => ?_) i
      · change p (header (layout sourceKeys sourceValues queryKeys h x) (sourceIndex h j) ∘
          Fin.castSucc)
          (value (layout sourceKeys sourceValues queryKeys h x) (sourceIndex h j)) at hp
        exact ⟨j, by simpa only [source_key, source_value] using hp⟩
      · simp [header, Function.comp_def, layout_apply, rows] at ht
  · rintro ⟨j, hj⟩
    exact ⟨sourceIndex h j, source_tag sourceKeys sourceValues queryKeys h x j, by
      simpa only [source_key, source_value] using hj⟩

/-- Select the values at the original request positions by free wiring. -/
def outputs (h : requests + (sources + padding) = BitonicSort.arity d) :
    Circuit signature (BitonicSort.arity d * v) (requests * v) :=
  Circuit.wiring signature fun i => let jb := finProdFinEquiv.symm i
    finProdFinEquiv (requestIndex h jb.1, jb.2)

/-- Shared OR lookup with a supplied power-of-two record count. -/
def withPadding (h : requests + (sources + padding) = BitonicSort.arity d) :
    Circuit signature input (requests * v) :=
  (outputs h).comp ((routeValuesCircuit Fin.castSucc (Fin.last k) d v).comp
    (substituteCircuit (substitution sourceKeys sourceValues queryKeys h)))

/-- A query bit is true exactly when some matching source bit is true. -/
theorem eval_withPadding_iff (h : requests + (sources + padding) = BitonicSort.arity d)
    (x : BitString input) (request : Fin requests) (bit : Fin v) :
    (withPadding sourceKeys sourceValues queryKeys h).eval interpretation x
        (finProdFinEquiv (request, bit)) = true ↔
      ∃ source, substitute (sourceKeys source) x = substitute (queryKeys request) x ∧
        substitute (sourceValues source) x bit = true := by
  simp only [withPadding, Circuit.eval_comp, outputs, Circuit.eval_wiring,
    eval_substituteCircuit, Function.comp_apply, Equiv.symm_apply_apply]
  change directProductInput
    ((routeValuesCircuit Fin.castSucc (Fin.last k) d v).eval interpretation
      (layout sourceKeys sourceValues queryKeys h x)) (requestIndex h request) bit = true ↔ _
  rw [eval_routeValuesCircuit_value_eq_true_iff Fin.castSucc (Fin.last k) _ _
    (request_tag sourceKeys sourceValues queryKeys h x request),
    request_key]
  simpa only [and_left_comm] using exists_source_iff sourceKeys sourceValues queryKeys h x
    (fun key value => key = substitute (queryKeys request) x ∧ value bit = true)

/-- Input preparation adds one shared gate for each Boolean constant. -/
theorem cost_program_withPadding (h : requests + (sources + padding) = BitonicSort.arity d)
    (cost : signature.Op → ℕ) :
    (withPadding sourceKeys sourceValues queryKeys h).program.cost cost =
      (routeValuesCircuit Fin.castSucc (Fin.last k) d v).program.cost cost +
        cost (.const false) + cost (.const true) := by
  simp only [withPadding, outputs, Circuit.cost_program_comp,
    Circuit.cost_program_wiring, cost_program_substituteCircuit]
  ac_rfl

/-- Exact gate count, including constants and negations, independent of the selectors. -/
theorem size_withPadding (h : requests + (sources + padding) = BitonicSort.arity d) :
    (withPadding sourceKeys sourceValues queryKeys h).size =
      BitonicSort.sortTraceSize d * (12 * (k + v) + 14) +
        (1 + (BitonicSort.arity d - 1) * (6 * k + 1) + v * (1 + 4 * BitonicSort.arity d)) + 2 := by
  have ha : BitonicSort.arity d ≠ 0 := by
    rw [BitonicSort.arity_eq_two_pow]
    exact pow_ne_zero _ (by decide)
  have hc := cost_program_withPadding sourceKeys sourceValues queryKeys h (fun _ => 1)
  simp only [Program.cost_const, one_mul, size_routeValuesCircuit, size_broadcastCircuit,
    ite_eq_right ha] at hc
  rw [hc]
  ring

/-- A bound linear in the record count and field width, and quadratic in sorting depth. -/
theorem size_withPadding_le (h : requests + (sources + padding) = BitonicSort.arity d) :
    (withPadding sourceKeys sourceValues queryKeys h).size ≤
      24 * BitonicSort.arity d * (d + 1) ^ 2 * (k + v + 1) := by
  have ha : 1 ≤ BitonicSort.arity d := by
    rw [BitonicSort.arity_eq_two_pow]
    exact Nat.one_le_pow _ _ (by decide)
  have hd : 1 ≤ (d + 1) ^ 2 := Nat.one_le_pow _ _ (by lia)
  have ht : BitonicSort.sortTraceSize d ≤ BitonicSort.arity d * (d + 1) ^ 2 := by
    have hh := BitonicSort.four_mul_sortTraceSize d
    rw [← BitonicSort.arity_eq_two_pow] at hh
    nlinarith
  have hl : 1 + (BitonicSort.arity d - 1) * (6 * k + 1) +
      v * (1 + 4 * BitonicSort.arity d) + 2 ≤ 10 * BitonicSort.arity d * (k + v + 1) := by
    have hn := Nat.mul_le_mul_right (6 * k + 1) (Nat.sub_le (BitonicSort.arity d) 1)
    nlinarith
  have hm := Nat.mul_le_mul ht (show 12 * (k + v) + 14 ≤ 14 * (k + v + 1) by lia)
  have hp := Nat.mul_le_mul_left (10 * BitonicSort.arity d * (k + v + 1)) hd
  rw [size_withPadding]
  nlinarith

end Layout

/-- The least sorting depth accommodating the requests and sources; zero records use depth zero. -/
def depth (requests sources : ℕ) : ℕ := Nat.clog 2 (requests + sources)

/-- Unused destination slots filling the next power-of-two record count. -/
def padding (requests sources : ℕ) : ℕ :=
  BitonicSort.arity (depth requests sources) - (requests + sources)

/-- Padding fills the network exactly, also for an empty batch. -/
theorem add_padding_eq_arity (requests sources : ℕ) :
    requests + (sources + padding requests sources) =
      BitonicSort.arity (depth requests sources) := by
  have h := Nat.le_pow_clog (by decide : 1 < 2) (requests + sources)
  simp only [padding, depth, BitonicSort.arity_eq_two_pow]
  lia

/-- Canonical padding is linear in the total record count, including the empty batch. -/
theorem arity_depth_le (requests sources : ℕ) :
    BitonicSort.arity (depth requests sources) ≤ 2 * (requests + sources + 1) := by
  rw [BitonicSort.arity_eq_two_pow]
  by_cases h : requests + sources = 0
  · simp [depth, h]
  · exact (Nat.pow_clog_le_mul (by decide : 1 < 2) h).trans (by lia)

end batchOrCircuit

open batchOrCircuit

variable {input sources requests k v : ℕ}
variable (sourceKeys : Fin sources → Fin k → Fin input ⊕ Bool)
  (sourceValues : Fin sources → Fin v → Fin input ⊕ Bool)
  (queryKeys : Fin requests → Fin k → Fin input ⊕ Bool)

/-- Look up bitwise ORs of dynamic source values with automatic padding.
Source and query keys may repeat, and absent keys return false. -/
def batchOrCircuit : Circuit signature input (requests * v) :=
  withPadding sourceKeys sourceValues queryKeys (add_padding_eq_arity requests sources)

/-- An output bit is true exactly when a matching source bit is true. -/
theorem eval_batchOrCircuit_iff (x : BitString input) (request : Fin requests) (bit : Fin v) :
    (batchOrCircuit sourceKeys sourceValues queryKeys).eval interpretation x
        (finProdFinEquiv (request, bit)) = true ↔
      ∃ source, substitute (sourceKeys source) x = substitute (queryKeys request) x ∧
        substitute (sourceValues source) x bit = true :=
  eval_withPadding_iff sourceKeys sourceValues queryKeys (add_padding_eq_arity requests sources)
    x request bit

/-- Canonical shared OR lookup has linear record-count cost up to the displayed factors.
This is a circuit gate bound, not a certificate of constructor runtime. -/
theorem size_batchOrCircuit_le :
    (batchOrCircuit sourceKeys sourceValues queryKeys).size ≤
      48 * (requests + sources + 1) * (Nat.clog 2 (requests + sources) + 1) ^ 2 * (k + v + 1) := by
  calc
    _ ≤ 24 * BitonicSort.arity (depth requests sources) * (depth requests sources + 1) ^ 2 *
        (k + v + 1) := size_withPadding_le sourceKeys sourceValues queryKeys _
    _ ≤ 24 * (2 * (requests + sources + 1)) * (depth requests sources + 1) ^ 2 * (k + v + 1) := by
      gcongr
      exact arity_depth_le requests sources
    _ = _ := by dsimp only [depth]; ring

end Cslib.Circuits.Boolean
