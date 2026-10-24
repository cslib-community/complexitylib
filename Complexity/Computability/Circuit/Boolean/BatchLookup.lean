/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.BatchOr
public import Complexity.Foundations.Data.BitString.Basic
import Complexity.Foundations.Data.Nat.Log
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Batched table lookup with one sort

A fixed table is hardwired into one source record per address. Query addresses are input wires;
queries and padding are destination records. Sort once, broadcast matching source values, and
reverse the saved sorting decisions on the values alone. Selecting the original request positions
then returns the answers in input order, including repeated addresses. No request identifiers or
restoration ranks are used. Empty keys, empty values, and zero requests are allowed.

The circuit uses CSLib's native `Circuit` representation. Input preparation shares exactly two
constant gates, including when one or both are unused. The exact weighted cost and total gate count
include these constants; the polynomial gate bound does not certify constructor runtime.

## Main definitions

* `Cslib.Circuits.Boolean.batchLookupCircuit`: lookup with inferred sorting depth and padding.
* `Cslib.Circuits.Boolean.batchLookupCircuit.withPadding`: lookup with a supplied record count.
* `Cslib.Circuits.Boolean.batchLookupCircuit.depth`,
  `Cslib.Circuits.Boolean.batchLookupCircuit.padding`: the canonical sorting depth and record
  padding for a given request count and key width.

## Main results

* `Cslib.Circuits.Boolean.eval_batchLookupCircuit`: arbitrary repeated queries are answered exactly.
* `Cslib.Circuits.Boolean.batchLookupCircuit.size_withPadding`: exact total gate count.
* `Cslib.Circuits.Boolean.size_batchLookupCircuit_le`: a bound linear in table size plus request
  count and field width, and quadratic in sorting depth.

## References

Simplifies the nonuniform lookup construction in
[S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction],
using the sorting network of
[K. E. Batcher, *Sorting Networks and Their Applications*][Batcher1968].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

namespace batchLookupCircuit

/-- Batched lookup using a specified power-of-two record count and padding. -/
def withPadding {k v requests padding d : ℕ} (table : BitString k → BitString v)
    (h : requests + (2 ^ k + padding) = BitonicSort.arity d) :
    Circuit signature (requests * k) (requests * v) :=
  batchOrCircuit.withPadding
    (fun source => Sum.inr ∘ (BitString.equivFin k).symm source)
    (fun source => Sum.inr ∘ table ((BitString.equivFin k).symm source))
    (fun request bit => Sum.inl (finProdFinEquiv (request, bit))) h

/-- Every request receives its table value, including repeated addresses. -/
theorem eval_withPadding {k v requests padding d : ℕ} (table : BitString k → BitString v)
    (h : requests + (2 ^ k + padding) = BitonicSort.arity d) (x : BitString (requests * k)) :
    directProductInput ((withPadding table h).eval interpretation x) =
      table ∘ directProductInput x := by
  funext request bit
  apply Bool.eq_iff_iff.mpr
  change (batchOrCircuit.withPadding _ _ _ h).eval interpretation x
    (finProdFinEquiv (request, bit)) = true ↔ _
  rw [batchOrCircuit.eval_withPadding_iff]
  simp only [substitute, Function.comp_apply, Sum.elim_inr, id_eq]
  constructor
  · rintro ⟨source, hkey, hvalue⟩
    change (BitString.equivFin k).symm source = directProductInput x request at hkey
    exact hkey ▸ hvalue
  · intro hvalue
    exact ⟨(BitString.equivFin k) (directProductInput x request),
      (BitString.equivFin k).symm_apply_apply _, by
        simpa only [Equiv.symm_apply_apply] using hvalue⟩

/-- Input preparation adds exactly two shared constant gates to the routing cost. -/
theorem cost_program_withPadding {k v requests padding d : ℕ}
    (table : BitString k → BitString v)
    (h : requests + (2 ^ k + padding) = BitonicSort.arity d) (cost : signature.Op → ℕ) :
    (withPadding table h).program.cost cost =
      (routeValuesCircuit Fin.castSucc (Fin.last k) d v).program.cost cost +
        cost (.const false) + cost (.const true) :=
  batchOrCircuit.cost_program_withPadding _ _ _ h cost

/-- Exact total gate count, including all constants and negations. -/
theorem size_withPadding {k v requests padding d : ℕ}
    (table : BitString k → BitString v)
    (h : requests + (2 ^ k + padding) = BitonicSort.arity d) :
    (withPadding table h).size =
      BitonicSort.sortTraceSize d * (12 * (k + v) + 14) +
        (1 + (BitonicSort.arity d - 1) * (6 * k + 1) + v * (1 + 4 * BitonicSort.arity d)) + 2 :=
  batchOrCircuit.size_withPadding _ _ _ h

/-- A factored gate bound, linear in record count and field width and quadratic in depth. -/
theorem size_withPadding_le {k v requests padding d : ℕ}
    (table : BitString k → BitString v)
    (h : requests + (2 ^ k + padding) = BitonicSort.arity d) :
    (withPadding table h).size ≤
      24 * BitonicSort.arity d * (d + 1) ^ 2 * (k + v + 1) :=
  batchOrCircuit.size_withPadding_le _ _ _ h

/-- The least sorting depth accommodating all requests and one source per address. -/
abbrev depth (requests k : ℕ) : ℕ := batchOrCircuit.depth requests (2 ^ k)

/-- The number of unused destinations filling the next power-of-two record count. -/
abbrev padding (requests k : ℕ) : ℕ := batchOrCircuit.padding requests (2 ^ k)

/-- The canonical padding fills its sorting network exactly. -/
theorem add_padding_eq_arity (requests k : ℕ) :
    requests + (2 ^ k + padding requests k) = BitonicSort.arity (depth requests k) :=
  batchOrCircuit.add_padding_eq_arity requests (2 ^ k)

end batchLookupCircuit

open batchLookupCircuit

/-- Look up all input addresses in one hardwired table, preserving request order.
Padding and sorting depth are inferred from the number of requests and the key width. -/
def batchLookupCircuit {k v : ℕ} (table : BitString k → BitString v) (requests : ℕ) :
    Circuit signature (requests * k) (requests * v) :=
  withPadding table (add_padding_eq_arity requests k)

/-- The complete circuit computes the table value at each input address. -/
@[simp] theorem eval_batchLookupCircuit {k v : ℕ} (table : BitString k → BitString v) (requests : ℕ)
    (x : BitString (requests * k)) :
    (batchLookupCircuit table requests).eval interpretation x = blockMap table requests x := by
  funext i
  obtain ⟨⟨request, bit⟩, rfl⟩ := finProdFinEquiv.surjective i
  rw [blockMap_apply]
  exact congrFun (congrFun (eval_withPadding table (add_padding_eq_arity requests k) x) request) bit

/-- Batched lookup uses at most the displayed bound in table size plus request count.
This bounds circuit gates, not the running time of the circuit constructor. -/
theorem size_batchLookupCircuit_le {k v : ℕ} (table : BitString k → BitString v) (requests : ℕ) :
    (batchLookupCircuit table requests).size ≤
      48 * (requests + 2 ^ k) * (Nat.clog 2 (requests + 2 ^ k) + 1) ^ 2 * (k + v + 1) := by
  have hn : requests + 2 ^ k ≠ 0 := by positivity
  calc
    _ ≤ 24 * BitonicSort.arity (depth requests k) * (depth requests k + 1) ^ 2 * (k + v + 1) :=
      size_withPadding_le table (add_padding_eq_arity requests k)
    _ ≤ 24 * (2 * (requests + 2 ^ k)) * (depth requests k + 1) ^ 2 * (k + v + 1) := by
      gcongr
      rw [BitonicSort.arity_eq_two_pow]
      exact Nat.pow_clog_le_mul (by decide : 1 < 2) hn
    _ = _ := by dsimp only [depth, batchOrCircuit.depth]; ring

/-- Independent applications of any fixed table admit a shared lookup circuit. -/
theorem complexity_blockMap_le_lookup {k v : ℕ} (table : BitString k → BitString v) (requests : ℕ) :
    complexity interpretation (blockMap table requests) ≤
      48 * (requests + 2 ^ k) * (Nat.clog 2 (requests + 2 ^ k) + 1) ^ 2 * (k + v + 1) :=
  (complexity_le_of_computes (batchLookupCircuit table requests)
    (eval_batchLookupCircuit table requests)).trans (size_batchLookupCircuit_le table requests)

end Cslib.Circuits.Boolean
