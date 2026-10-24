/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Sorting
import Mathlib.Tactic.Ring

/-!
# Reversing sorting circuits with saved comparison decisions

The forward circuits in `Sorting` sort records once and retain the comparison controls.
This module reverses those decisions on new payloads using the same CSLib circuit representation.
Reversal inspects only the controls, so answer payloads may have a different width and need not
contain keys or unique identifiers.

A trace has `BitonicSort.sortTraceSize d` decisions stored as twice that many control wires,
followed by `BitonicSort.arity d` consecutive records. The reverse circuit expects complementary
control pairs; arbitrary pairs are not asserted to describe a permutation.

Reversal costs six gates per answer bit and comparison. These are circuit gate costs with free
wiring, not bounds on retained storage or the circuit constructor's runtime.

## Main definitions

* `Cslib.Circuits.Boolean.bitonicUnsortCircuit`: reverse saved decisions on new payloads.

## Main results

* `Cslib.Circuits.Boolean.eval_bitonicUnsortCircuit`: reverse arbitrary paired decisions.
* `Cslib.Circuits.Boolean.eval_bitonicUnsortCircuit_sort`: restore transformed sorted records.
  The transformation is a semantic parameter; its implementation cost is not included.
* `Cslib.Circuits.Boolean.size_bitonicUnsortCircuit`: exact reversal gate count.

## References

* [K. E. Batcher, *Sorting Networks and Their Applications*][Batcher1968].
* Extends the sorting backend adapted from
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open bitonicSortTraceCircuit
open BitonicSort (arity mergeTraceSize sortTraceSize)

namespace bitonicSortTraceCircuit

/-- Select controls and records independently by free wiring. -/
def select {a t n m r : ℕ} (cs : Fin a → Fin t) (rs : Fin n → Fin m) :
    Circuit signature (t * 2 + m * r) (a * 2 + n * r) :=
  Circuit.wiringOn signature (layout t m r) (layout a n r)
    (Sum.map (Prod.map cs id) (Prod.map rs id))

private theorem eval_select {a t n m r : ℕ} (cs : Fin a → Fin t) (rs : Fin n → Fin m)
    (c : Fin t → BitString 2) (x : Fin m → BitString r) :
    (select cs rs).eval interpretation (pack c x) = pack (c ∘ cs) (x ∘ rs) := by
  apply ext <;> funext j bit <;>
    simp [controls, records, select, layout, Circuit.eval_wiringOn, pack, directProductInput,
      flatten, -finProdFinEquiv_symm_apply, -Fin.natAdd_eq_addNat]

/-- Reverse a comparison layer, reading the saved decision and its complement. -/
def unlayer (n r : ℕ) : Circuit signature (n * 2 + (n + n) * r) ((n + n) * r) :=
  (Circuit.wiring signature (bitonicLayerCircuit.scatter n r)).comp
    (((compareSwapCircuit.switch r).replicate n).comp
      (Circuit.wiring signature (fun i =>
        let jb := finProdFinEquiv.symm i
        Fin.addCases
          (fun bit => Fin.castAdd ((n + n) * r) (finProdFinEquiv (jb.1, bit)))
          (Fin.addCases
            (fun bit => Fin.natAdd (n * 2) (finProdFinEquiv (Fin.castAdd n jb.1, bit)))
            (fun bit => Fin.natAdd (n * 2) (finProdFinEquiv (Fin.natAdd n jb.1, bit)))) jb.2)))

private theorem unlayer_input {n r : ℕ} (flags : BitString n)
    (x : Fin (n + n) → BitString r) (j : Fin n) :
    (fun bit : Fin (2 + (r + r)) =>
      pack (pairs flags) x (Fin.addCases
        (fun bit => Fin.castAdd ((n + n) * r) (finProdFinEquiv (j, bit)))
        (Fin.addCases
          (fun bit => Fin.natAdd (n * 2) (finProdFinEquiv (Fin.castAdd n j, bit)))
          (fun bit => Fin.natAdd (n * 2) (finProdFinEquiv (Fin.natAdd n j, bit)))) bit)) =
      Fin.append ![flags j, !flags j] (Fin.append (x (Fin.castAdd n j)) (x (Fin.natAdd n j))) := by
  funext bit
  cases bit using Fin.addCases with
  | left bit =>
    simp only [Fin.addCases_left, pack, Fin.append_left, flatten, Equiv.symm_apply_apply, pairs]
  | right bit =>
    cases bit using Fin.addCases <;>
      simp only [Fin.addCases_right, Fin.addCases_left, pack, Fin.append_right, Fin.append_left,
        flatten, Equiv.symm_apply_apply]

private theorem eval_unlayer (n r : ℕ) (flags : BitString n) (x : Fin (n + n) → BitString r) :
    directProductInput ((unlayer n r).eval interpretation (pack (pairs flags) x)) =
      BitonicSort.routeLayer flags x := by
  funext j bit
  cases j using Fin.addCases <;>
    simp only [unlayer, Circuit.eval_comp, Circuit.eval_wiring, directProductInput,
      Function.comp_apply, bitonicLayerCircuit.scatter, Equiv.symm_apply_apply,
      Fin.addCases_left, Fin.addCases_right, Circuit.eval_replicate_apply]
  all_goals
    unfold directProductInput
    simp only [Function.comp_def, Equiv.symm_apply_apply]
    erw [unlayer_input, compareSwapCircuit.eval_switch]
    simp only [BitonicSort.routeLayer, Fin.append_left, Fin.append_right]
    split_ifs <;> simp only [Fin.append_left, Fin.append_right]

private theorem cost_unlayer (n r : ℕ) (cost : signature.Op → ℕ) :
    (unlayer n r).program.cost cost = n * (2 * r * (2 * cost .and + cost .or)) := by
  simp only [unlayer, Circuit.cost_program_comp, Circuit.cost_program_wiring,
    Circuit.cost_program_replicate, compareSwapCircuit.cost_switch, Nat.zero_add, Nat.add_zero]

/-- Reverse two independent circuits using the matching halves of their controls and records. -/
def unhalves {a b n r : ℕ} (left : Circuit signature (a * 2 + n * r) (n * r))
    (right : Circuit signature (b * 2 + n * r) (n * r)) :
    Circuit signature ((a + b) * 2 + (n + n) * r) ((n + n) * r) :=
  (Circuit.wiringOn signature
    ((finProdFinEquiv.sumCongr finProdFinEquiv).trans finSumFinEquiv)
    ((finSumFinEquiv.prodCongr (Equiv.refl (Fin r))).trans finProdFinEquiv)
    (Equiv.sumProdDistrib (Fin n) (Fin n) (Fin r))).comp
    ((left.comp (select (Fin.castAdd b) (Fin.castAdd n))).append
      (right.comp (select (Fin.natAdd a) (Fin.natAdd n))))

private theorem eval_unhalves {a b n r : ℕ} (left : Circuit signature (a * 2 + n * r) (n * r))
    (right : Circuit signature (b * 2 + n * r) (n * r))
    (c : Fin (a + b) → BitString 2) (x : Fin (n + n) → BitString r) :
    directProductInput ((unhalves left right).eval interpretation (pack c x)) =
      Fin.append
        (directProductInput (left.eval interpretation
          (pack (c ∘ Fin.castAdd b) (x ∘ Fin.castAdd n))))
        (directProductInput (right.eval interpretation
          (pack (c ∘ Fin.natAdd a) (x ∘ Fin.natAdd n)))) := by
  funext j bit
  cases j using Fin.addCases <;>
    simp [unhalves, Circuit.eval_wiringOn, directProductInput, eval_select,
      -finProdFinEquiv_symm_apply, -Fin.natAdd_eq_addNat]

private theorem cost_unhalves {a b n r : ℕ} (left : Circuit signature (a * 2 + n * r) (n * r))
    (right : Circuit signature (b * 2 + n * r) (n * r)) (cost : signature.Op → ℕ) :
    (unhalves left right).program.cost cost =
      left.program.cost cost + right.program.cost cost := by
  simp only [unhalves, select, Circuit.cost_program_comp, Circuit.cost_program_append,
    Circuit.cost_program_wiringOn, Nat.zero_add, Nat.add_zero]

/-- Preserve the first controls while undoing the second stage, then undo the first stage. -/
def unchain {a b n r : ℕ} (first : Circuit signature (a * 2 + n * r) (n * r))
    (second : Circuit signature (b * 2 + n * r) (n * r)) :
    Circuit signature ((a + b) * 2 + n * r) (n * r) :=
  first.comp ((Circuit.wiringOn signature (layout (a + b) n r) finProdFinEquiv
    (fun (j, bit) => Sum.inl (Fin.castAdd b j, bit))).append
      (second.comp (select (Fin.natAdd a) id)))

private theorem eval_unchain {a b n r : ℕ} (first : Circuit signature (a * 2 + n * r) (n * r))
    (second : Circuit signature (b * 2 + n * r) (n * r))
    (c : Fin (a + b) → BitString 2) (x : Fin n → BitString r) :
    (unchain first second).eval interpretation (pack c x) =
      first.eval interpretation (pack (c ∘ Fin.castAdd b)
        (directProductInput (second.eval interpretation (pack (c ∘ Fin.natAdd a) x)))) := by
  simp only [unchain, Circuit.eval_comp, Circuit.eval_append, eval_select, Function.comp_id]
  congr 1
  funext i
  cases i using Fin.addCases with
  | left i =>
    simp [Circuit.eval_wiringOn, layout, pack, flatten,
      -finProdFinEquiv_symm_apply, -Fin.natAdd_eq_addNat]
  | right i =>
    simp only [Fin.append_right, pack, flatten, directProductInput, Prod.mk.eta,
      Equiv.apply_symm_apply]

private theorem cost_unchain {a b n r : ℕ} (first : Circuit signature (a * 2 + n * r) (n * r))
    (second : Circuit signature (b * 2 + n * r) (n * r)) (cost : signature.Op → ℕ) :
    (unchain first second).program.cost cost =
      first.program.cost cost + second.program.cost cost := by
  simp only [unchain, select, Circuit.cost_program_comp, Circuit.cost_program_append,
    Circuit.cost_program_wiringOn, Nat.zero_add]
  exact Nat.add_comm _ _

private theorem pairs_comp {a b : ℕ} (flags : BitString a) (f : Fin b → Fin a) :
    pairs (flags ∘ f) = pairs flags ∘ f := rfl

end bitonicSortTraceCircuit

/-- Undo the child merges before reversing the first comparison layer. -/
def bitonicUnmergeCircuit (r : ℕ) : (d : ℕ) →
    Circuit signature (mergeTraceSize d * 2 + arity d * r) (arity d * r)
  | 0 => Circuit.wiring signature (Fin.natAdd 0)
  | d + 1 =>
    unchain (unlayer (arity d) r) (unhalves (bitonicUnmergeCircuit r d) (bitonicUnmergeCircuit r d))

/-- Undo the final merge before reversing the two child sorts. -/
def bitonicUnsortCircuit (r : ℕ) : (d : ℕ) →
    Circuit signature (sortTraceSize d * 2 + arity d * r) (arity d * r)
  | 0 => Circuit.wiring signature (Fin.natAdd 0)
  | d + 1 =>
    unchain (unhalves (bitonicUnsortCircuit r d) (bitonicUnsortCircuit r d))
      (bitonicUnmergeCircuit r (d + 1))

/-- The reverse merge implements reversal for every paired trace and payload. -/
theorem eval_bitonicUnmergeCircuit (r d : ℕ) (flags : BitString (mergeTraceSize d))
    (x : Fin (arity d) → BitString r) :
    directProductInput ((bitonicUnmergeCircuit r d).eval interpretation (pack (pairs flags) x)) =
      BitonicSort.unrouteMerge d flags x := by
  induction d with
  | zero =>
    simp only [bitonicUnmergeCircuit, BitonicSort.unrouteMerge]
    erw [Circuit.eval_wiring]
    exact records_pack _ _
  | succ d ih =>
    dsimp only [arity, mergeTraceSize] at flags x
    simp only [bitonicUnmergeCircuit, arity, mergeTraceSize, BitonicSort.unrouteMerge]
    erw [eval_unchain, eval_unhalves]
    simp only [← pairs_comp, ih]
    exact eval_unlayer _ _ _ _

/-- The reverse sorter implements reversal for every paired trace and payload. -/
theorem eval_bitonicUnsortCircuit (r d : ℕ) (flags : BitString (sortTraceSize d))
    (x : Fin (arity d) → BitString r) :
    directProductInput ((bitonicUnsortCircuit r d).eval interpretation (pack (pairs flags) x)) =
      BitonicSort.unrouteSort d flags x := by
  induction d with
  | zero =>
    simp only [bitonicUnsortCircuit, BitonicSort.unrouteSort]
    erw [Circuit.eval_wiring]
    exact records_pack _ _
  | succ d ih =>
    dsimp only [arity, sortTraceSize] at flags x
    simp only [bitonicUnsortCircuit, arity, sortTraceSize, BitonicSort.unrouteSort]
    erw [eval_unchain]
    simp only [← pairs_comp]
    erw [eval_bitonicUnmergeCircuit, eval_unhalves]
    simp only [← pairs_comp, ih]

/-- A reverse merge charges only switching; saved controls require no new negations. -/
private theorem cost_program_bitonicUnmergeCircuit (r d : ℕ) (cost : signature.Op → ℕ) :
    (bitonicUnmergeCircuit r d).program.cost cost =
      mergeTraceSize d * (2 * r * (2 * cost .and + cost .or)) := by
  induction d with
  | zero => simp [bitonicUnmergeCircuit, mergeTraceSize]
  | succ d ih =>
    simp only [bitonicUnmergeCircuit]
    erw [cost_unchain, cost_unlayer, cost_unhalves, ih, mergeTraceSize]
    ring

/-- A reverse sort charges only switching; saved controls require no new negations. -/
theorem cost_program_bitonicUnsortCircuit (r d : ℕ) (cost : signature.Op → ℕ) :
    (bitonicUnsortCircuit r d).program.cost cost =
      sortTraceSize d * (2 * r * (2 * cost .and + cost .or)) := by
  induction d with
  | zero => simp [bitonicUnsortCircuit, sortTraceSize]
  | succ d ih =>
    simp only [bitonicUnsortCircuit]
    erw [cost_unchain, cost_unhalves, ih, cost_program_bitonicUnmergeCircuit, sortTraceSize]
    ring

/-- Reversing a sort uses six gates per payload bit and comparison. -/
theorem size_bitonicUnsortCircuit (r d : ℕ) :
    (bitonicUnsortCircuit r d).size = sortTraceSize d * (6 * r) := by
  have h := cost_program_bitonicUnsortCircuit r d (fun _ => 1)
  simp only [Program.cost_const, one_mul] at h
  rw [h]
  ring

/-- Saved controls restore transformed records, even when the answer has a different width. -/
theorem eval_bitonicUnsortCircuit_sort {k r v : ℕ} (key : Fin k → Fin r) (d : ℕ)
    (ascending : Bool) (f : BitString r → BitString v) (x : BitString (arity d * r)) :
    let output := (bitonicSortTraceCircuit key d ascending).eval interpretation x
    directProductInput ((bitonicUnsortCircuit v d).eval interpretation
      (pack (controls output) (f ∘ records output))) = f ∘ directProductInput x := by
  dsimp only
  rw [eval_bitonicSortTraceCircuit, controls_pack, records_pack, eval_bitonicUnsortCircuit]
  exact BitonicSort.unrouteSort_comp_sort _ _ _ _ _

end Cslib.Circuits.Boolean
