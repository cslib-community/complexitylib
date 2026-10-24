/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.Sort.Bitonic.Trace
public import Complexity.Computability.Circuit.Boolean.CompareSwap
public import Complexity.Computability.Circuit.Parallel
public import Complexity.Computability.Circuit.Replication
public import Complexity.Computability.Circuit.Wiring
import Complexity.Algorithms.Lean.Sort.Bitonic.Correctness
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Batcher sorting circuits

Records occupy consecutive blocks of input wires. The key selects coordinates in
lexicographic order, with coordinate zero most significant. Each comparison moves whole
records and shares its comparison flag across the record bits. Descending layers reverse
ascending pairs, including ties; the complete sorter is not stable.
Traced outputs prepend each comparison decision and its complement to the record blocks,
sharing the original negation. Ordinary sorting selects the record outputs by free wiring.
Empty records bypass the traced construction and use identity wiring; traced sorting still
computes its control pairs.
At depth `d` there are `2^d` records and `d * (d + 1) * 2^d / 4` comparisons.
The circuit constructor is executable; the gate-count theorems do not certify its running time.

## Main definitions

* `Cslib.Circuits.Boolean.bitonicLayerCircuit`: compare corresponding records in two halves.
* `Cslib.Circuits.Boolean.bitonicMergeCircuit`: merge a bitonic record array.
* `Cslib.Circuits.Boolean.bitonicSortCircuit`: sort a power-of-two record array.
* `Cslib.Circuits.Boolean.bitonicSortTraceCircuit`: sort and retain the comparison controls.
* `Cslib.Circuits.Boolean.bitonicSortTraceCircuit.pack`: controls followed by records.

## Main results

* `Cslib.Circuits.Boolean.eval_bitonicSortCircuit`: agreement with the generic algorithm.
* `Cslib.Circuits.Boolean.eval_bitonicSortTraceCircuit`: exact trace and record semantics.
* `Cslib.Circuits.Boolean.monotone_bitonicSortCircuit` and
  `Cslib.Circuits.Boolean.antitone_bitonicSortCircuit`: key sortedness in both directions.
* `Cslib.Circuits.Boolean.bitonicSortCircuit_perm`: preservation of complete records.
* `Cslib.Circuits.Boolean.four_mul_cost_program_bitonicSortCircuit`: exact weighted gate cost.
* `Cslib.Circuits.Boolean.cost_program_bitonicSortTraceCircuit_eq`: retaining controls adds
  no gates at nonzero record width, under arbitrary gate weights.

## References

* [K. E. Batcher, *Sorting Networks and Their Applications*][Batcher1968].
* Adapted from MassProduction/SortingNetwork.lean and MassProduction/SortingCorrectness.lean in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

namespace bitonicLayerCircuit

/-- Read a comparison's two records from the two halves. -/
def pairInput {n r : ℕ} (j : Fin n) : Fin (r + r) → Fin ((n + n) * r) :=
  Fin.addCases (fun b => finProdFinEquiv (Fin.castAdd n j, b))
    (fun b => finProdFinEquiv (Fin.natAdd n j, b))

/-- Gather corresponding records into adjacent pairs. -/
def gather (n r : ℕ) : Fin (n * (r + r)) → Fin ((n + n) * r) :=
  fun i => pairInput (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

/-- Scatter the compared pairs back into the two record halves. -/
def scatter (n r : ℕ) : Fin ((n + n) * r) → Fin (n * (r + r)) :=
  fun i =>
    let jb := finProdFinEquiv.symm i
    Fin.addCases (fun j => finProdFinEquiv (j, Fin.castAdd r jb.2))
      (fun j => finProdFinEquiv (j, Fin.natAdd r jb.2)) jb.1

end bitonicLayerCircuit

open bitonicLayerCircuit

/-- Gather reads corresponding records from the two halves without changing their bits. -/
private theorem bitonicLayerCircuit.gather_pair {n r : ℕ} (x : BitString ((n + n) * r))
    (j : Fin n) :
    directProductInput (x ∘ gather n r) j =
      Fin.append (directProductInput x (Fin.castAdd n j))
        (directProductInput x (Fin.natAdd n j)) := by
  funext b
  cases b using Fin.addCases <;>
    simp [directProductInput, gather, pairInput, -Fin.natAdd_eq_addNat]

namespace bitonicMergeCircuit

/-- Select the first half of a flat record array. -/
def firstHalf (n r : ℕ) : Fin (n * r) → Fin ((n + n) * r) :=
  fun i => finProdFinEquiv (Fin.castAdd n (finProdFinEquiv.symm i).1,
    (finProdFinEquiv.symm i).2)

/-- Select the second half of a flat record array. -/
def secondHalf (n r : ℕ) : Fin (n * r) → Fin ((n + n) * r) :=
  fun i => finProdFinEquiv (Fin.natAdd n (finProdFinEquiv.symm i).1,
    (finProdFinEquiv.symm i).2)

end bitonicMergeCircuit

open bitonicMergeCircuit

/-- The first flat input block is the first half of the record array. -/
private theorem bitonicMergeCircuit.records_firstHalf {n r : ℕ} (x : BitString ((n + n) * r)) :
    directProductInput (x ∘ firstHalf n r) = directProductInput x ∘ Fin.castAdd n := by
  funext j b
  simp only [firstHalf, directProductInput, Function.comp_apply, Equiv.symm_apply_apply]

/-- The second flat input block is the second half of the record array. -/
private theorem bitonicMergeCircuit.records_secondHalf {n r : ℕ} (x : BitString ((n + n) * r)) :
    directProductInput (x ∘ secondHalf n r) = directProductInput x ∘ Fin.natAdd n := by
  funext j b
  simp only [secondHalf, directProductInput, Function.comp_apply, Equiv.symm_apply_apply]

namespace bitonicSortTraceCircuit

/-- Flatten a finite array of equal-width records. -/
def flatten {n r : ℕ} (x : Fin n → BitString r) : BitString (n * r) :=
  fun i => x (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

@[simp] theorem directProductInput_flatten {n r : ℕ} (x : Fin n → BitString r) :
    directProductInput (flatten x) = x := by
  funext i b
  simp only [directProductInput, flatten, Equiv.symm_apply_apply]

/-- The controls retain both a decision and its complement. -/
def controls {t n r : ℕ} (x : BitString (t * 2 + n * r)) : Fin t → BitString 2 :=
  directProductInput (x ∘ Fin.castAdd (n * r))

/-- The payload records following the controls. -/
def records {t n r : ℕ} (x : BitString (t * 2 + n * r)) : Fin n → BitString r :=
  directProductInput (x ∘ Fin.natAdd (t * 2))

/-- Encode control pairs followed by records. -/
def pack {t n r : ℕ} (c : Fin t → BitString 2) (x : Fin n → BitString r) :
    BitString (t * 2 + n * r) :=
  Fin.append (flatten c) (flatten x)

@[simp] theorem controls_pack {t n r : ℕ} (c : Fin t → BitString 2)
    (x : Fin n → BitString r) : controls (pack c x) = c := by
  funext i b
  simp only [controls, pack, flatten, directProductInput, Function.comp_apply,
    Fin.append_left, Equiv.symm_apply_apply]

@[simp] theorem records_pack {t n r : ℕ} (c : Fin t → BitString 2)
    (x : Fin n → BitString r) : records (pack c x) = x := by
  funext i b
  simp only [records, pack, flatten, directProductInput, Function.comp_apply,
    Fin.append_right, Equiv.symm_apply_apply]

@[simp] theorem pack_comp_natAdd {t n r : ℕ} (c : Fin t → BitString 2)
    (x : Fin n → BitString r) : pack c x ∘ Fin.natAdd (t * 2) = flatten x :=
  Fin.append_comp_natAdd _ _

/-- Flattening the record view recovers the original wire assignment. -/
@[simp] theorem flatten_directProductInput {n r : ℕ} (x : BitString (n * r)) :
    flatten (directProductInput x) = x := by
  funext i
  simp only [flatten, directProductInput, Prod.mk.eta, Equiv.apply_symm_apply]

/-- Apply a circuit to the payload while retaining every control pair by free wiring. -/
theorem eval_parallel_pack {t n m r v : ℕ}
    (f : Circuit signature (n * r) (m * v)) (c : Fin t → BitString 2)
    (x : Fin n → BitString r) :
    ((Circuit.id signature (t * 2)).parallel f).eval interpretation (pack c x) =
      pack c (directProductInput (f.eval interpretation (flatten x))) := by
  simp only [Circuit.eval_parallel, Circuit.id, Circuit.eval_wiring, Function.comp_id,
    pack, Fin.append_comp_castAdd, Fin.append_comp_natAdd, flatten_directProductInput]

/-- Control pairs and payload records determine the complete wire assignment. -/
theorem ext {t n r : ℕ} {x y : BitString (t * 2 + n * r)}
    (hc : controls x = controls y) (hd : records x = records y) : x = y := by
  funext i
  cases i using Fin.addCases with
  | left i =>
    obtain ⟨⟨j, b⟩, rfl⟩ := finProdFinEquiv.surjective i
    exact congrFun (congrFun hc j) b
  | right i =>
    obtain ⟨⟨j, b⟩, rfl⟩ := finProdFinEquiv.surjective i
    exact congrFun (congrFun hd j) b

/-- The explicit numbering of control-pair and record coordinates. -/
def layout (t n r : ℕ) : (Fin t × Fin 2) ⊕ (Fin n × Fin r) ≃
    Fin (t * 2 + n * r) :=
  (finProdFinEquiv.sumCongr finProdFinEquiv).trans finSumFinEquiv

/-- Collect two circuits' controls before their concatenated record outputs. -/
def collect {input a b n m r : ℕ}
    (left : Circuit signature input (a * 2 + n * r))
    (right : Circuit signature input (b * 2 + m * r)) :
    Circuit signature input ((a + b) * 2 + (n + m) * r) :=
  (Circuit.wiringOn signature
    (((layout a n r).sumCongr (layout b m r)).trans finSumFinEquiv)
    (((finSumFinEquiv.prodCongr (Equiv.refl _)).sumCongr
      (finSumFinEquiv.prodCongr (Equiv.refl _))).trans (layout (a + b) (n + m) r))
    (((Equiv.sumProdDistrib (Fin a) (Fin b) (Fin 2)).sumCongr
      (Equiv.sumProdDistrib (Fin n) (Fin m) (Fin r))).trans
        (Equiv.sumSumSumComm _ _ _ _))).comp (left.append right)

private theorem controls_collect {input a b n m r : ℕ}
    (left : Circuit signature input (a * 2 + n * r))
    (right : Circuit signature input (b * 2 + m * r)) (x : BitString input) :
    controls ((collect left right).eval interpretation x) =
      Fin.append (controls (left.eval interpretation x))
        (controls (right.eval interpretation x)) := by
  funext j bit
  cases j using Fin.addCases <;>
    simp [controls, collect, layout, Circuit.eval_wiringOn, directProductInput,
      Equiv.sumSumSumComm, -finProdFinEquiv_symm_apply, -Fin.natAdd_eq_addNat]

private theorem records_collect {input a b n m r : ℕ}
    (left : Circuit signature input (a * 2 + n * r))
    (right : Circuit signature input (b * 2 + m * r)) (x : BitString input) :
    records ((collect left right).eval interpretation x) =
      Fin.append (records (left.eval interpretation x))
        (records (right.eval interpretation x)) := by
  funext j bit
  cases j using Fin.addCases <;>
    simp [records, collect, layout, Circuit.eval_wiringOn, directProductInput,
      Equiv.sumSumSumComm, -finProdFinEquiv_symm_apply, -Fin.natAdd_eq_addNat]

private theorem cost_collect {input a b n m r : ℕ}
    (left : Circuit signature input (a * 2 + n * r))
    (right : Circuit signature input (b * 2 + m * r)) (cost : signature.Op → ℕ) :
    (collect left right).program.cost cost = left.program.cost cost + right.program.cost cost := by
  simp only [collect, Circuit.cost_program_comp, Circuit.cost_program_append,
    Circuit.cost_program_wiringOn, Nat.add_zero]

/-- Preserve the first controls while executing the second circuit on its payload. -/
def chain {input a b n m r : ℕ}
    (first : Circuit signature input (a * 2 + n * r))
    (second : Circuit signature (n * r) (b * 2 + m * r)) :
    Circuit signature input ((a + b) * 2 + m * r) :=
  (Circuit.wiringOn signature
    ((finProdFinEquiv.sumCongr (layout b m r)).trans finSumFinEquiv)
    (((finSumFinEquiv.prodCongr (Equiv.refl _)).sumCongr (Equiv.refl _)).trans
      (layout (a + b) m r))
    (((Equiv.sumProdDistrib (Fin a) (Fin b) (Fin 2)).sumCongr (Equiv.refl _)).trans
      (Equiv.sumAssoc _ _ _))).comp
    (((Circuit.id signature (a * 2)).parallel second).comp first)

private theorem controls_chain {input a b n m r : ℕ}
    (first : Circuit signature input (a * 2 + n * r))
    (second : Circuit signature (n * r) (b * 2 + m * r)) (x : BitString input) :
    controls ((chain first second).eval interpretation x) =
      Fin.append (controls (first.eval interpretation x))
        (controls (second.eval interpretation
          (first.eval interpretation x ∘ Fin.natAdd (a * 2)))) := by
  funext j bit
  cases j using Fin.addCases <;>
    simp [controls, chain, layout, Circuit.eval_wiringOn, directProductInput,
      -finProdFinEquiv_symm_apply, -Fin.natAdd_eq_addNat]

private theorem records_chain {input a b n m r : ℕ}
    (first : Circuit signature input (a * 2 + n * r))
    (second : Circuit signature (n * r) (b * 2 + m * r)) (x : BitString input) :
    records ((chain first second).eval interpretation x) =
      records (second.eval interpretation (first.eval interpretation x ∘ Fin.natAdd (a * 2))) := by
  funext j bit
  simp [records, chain, layout, Circuit.eval_wiringOn, directProductInput,
    -finProdFinEquiv_symm_apply, -Fin.natAdd_eq_addNat]

private theorem cost_chain {input a b n m r : ℕ}
    (first : Circuit signature input (a * 2 + n * r))
    (second : Circuit signature (n * r) (b * 2 + m * r)) (cost : signature.Op → ℕ) :
    (chain first second).program.cost cost =
      first.program.cost cost + second.program.cost cost := by
  simp only [chain, Circuit.cost_program_comp, Circuit.cost_program_parallel, Circuit.id,
    Circuit.cost_program_wiringOn, Circuit.cost_program_wiring, Nat.zero_add, Nat.add_zero]

private theorem eval_collect {input a b n m r : ℕ}
    (left : Circuit signature input (a * 2 + n * r))
    (right : Circuit signature input (b * 2 + m * r)) (x : BitString input) :
    (collect left right).eval interpretation x =
      pack (Fin.append (controls (left.eval interpretation x))
        (controls (right.eval interpretation x)))
        (Fin.append (records (left.eval interpretation x))
          (records (right.eval interpretation x))) := by
  apply ext <;> simp only [controls_collect, records_collect, controls_pack, records_pack]

private theorem eval_chain {input a b n m r : ℕ}
    (first : Circuit signature input (a * 2 + n * r))
    (second : Circuit signature (n * r) (b * 2 + m * r))
    (x : BitString input) (c : Fin a → BitString 2) (y : Fin n → BitString r)
    (h : first.eval interpretation x = pack c y) :
    (chain first second).eval interpretation x =
      pack (Fin.append c (controls (second.eval interpretation (flatten y))))
        (records (second.eval interpretation (flatten y))) := by
  apply ext <;>
    simp only [controls_chain, records_chain, controls_pack, records_pack, h, pack_comp_natAdd]

/-- Pair each decision with its complement. -/
def pairs {n : ℕ} (flags : BitString n) : Fin n → BitString 2 :=
  fun i => ![flags i, !flags i]

private theorem pairs_append {n m : ℕ} (x : BitString n) (y : BitString m) :
    pairs (Fin.append x y) = Fin.append (pairs x) (pairs y) := by
  funext i b
  cases i using Fin.addCases <;> simp only [pairs, Fin.append_left, Fin.append_right]

/-- Descending compare-exchange reverses both the payload and the two control wires. -/
def pair {r : ℕ} (flag : Circuit signature (r + r) 1) (ascending : Bool) :
    Circuit signature (r + r) (2 + (r + r)) :=
  if ascending then compareSwapCircuit.record flag else
    (Circuit.wiring signature (Fin.addCases
      (Fin.castAdd (r + r) ∘ Fin.rev)
      (Fin.natAdd 2 ∘ compareSwapCircuit.swapInput r))).comp
        (compareSwapCircuit.record flag)

private theorem eval_pair {r : ℕ} (flag : Circuit signature (r + r) 1) (ascending : Bool)
    (x y : BitString r) :
    (pair flag ascending).eval interpretation (Fin.append x y) =
      let b := if ascending then flag.eval interpretation (Fin.append x y) 0
        else !flag.eval interpretation (Fin.append x y) 0
      Fin.append ![b, !b] (if b then Fin.append y x else Fin.append x y) := by
  cases ascending <;> cases h : flag.eval interpretation (Fin.append x y) 0 <;>
    funext i
  all_goals
    cases i using Fin.addCases with
    | left i =>
      fin_cases i <;> simp [pair, compareSwapCircuit.eval_record, h]
    | right i =>
      cases i using Fin.addCases <;>
        simp [pair, compareSwapCircuit.eval_record, h, compareSwapCircuit.swapInput,
          -Fin.natAdd_eq_addNat]

private theorem cost_pair {r : ℕ} (flag : Circuit signature (r + r) 1) (ascending : Bool)
    (cost : signature.Op → ℕ) :
    (pair flag ascending).program.cost cost =
      (compareSwapCircuit.record flag).program.cost cost := by
  cases ascending with
  | true => rfl
  | false =>
    unfold pair
    erw [Circuit.cost_program_comp, Circuit.cost_program_wiring, Nat.add_zero]

/-- Compare a layer and retain all of its controls before the payload. -/
def layer {k r : ℕ} (key : Fin k → Fin r) (n : ℕ) (ascending : Bool) :
    Circuit signature ((n + n) * r) (n * 2 + (n + n) * r) :=
  let comparator := pair
    (Formula.lexLt (Fin.natAdd r ∘ key) (Fin.castAdd r ∘ key)).toCircuit ascending
  (Circuit.wiring signature (Fin.addCases
    (fun i =>
      let jb := finProdFinEquiv.symm i
      finProdFinEquiv (jb.1, Fin.castAdd (r + r) jb.2))
    (fun i =>
      let jb := finProdFinEquiv.symm i
      Fin.addCases
        (fun j => finProdFinEquiv (j, Fin.natAdd 2 (Fin.castAdd r jb.2)))
        (fun j => finProdFinEquiv (j, Fin.natAdd 2 (Fin.natAdd r jb.2))) jb.1))).comp
    ((comparator.replicate n).comp (Circuit.wiring signature (bitonicLayerCircuit.gather n r)))

open Classical in
private theorem flag_eq_decide {k r : ℕ} (key : Fin k → Fin r) (x y : BitString r) :
    (Formula.lexLt (Fin.natAdd r ∘ key) (Fin.castAdd r ∘ key)).toCircuit.eval interpretation
      (Fin.append x y) 0 = decide (toLex (y ∘ key) < toLex (x ∘ key)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Formula.eval_toCircuit, Formula.eval_lexLt_iff, Function.comp_def,
    Fin.append_left, Fin.append_right, decide_eq_true_eq]

private theorem eval_layer {k r : ℕ} (key : Fin k → Fin r) (n : ℕ) (ascending : Bool)
    (x : BitString ((n + n) * r)) :
    (layer key n ascending).eval interpretation x =
      pack (pairs (BitonicSort.layerFlags (fun row : BitString r => toLex (row ∘ key))
        ascending (directProductInput x)))
        (BitonicSort.compareLayer (fun row : BitString r => toLex (row ∘ key))
          ascending (directProductInput x)) := by
  classical
  apply ext
  · rw [controls_pack]
    funext j bit
    simp only [controls, layer, directProductInput, Circuit.eval_comp,
      Circuit.eval_wiring, Function.comp_apply, Fin.addCases_left,
      Equiv.symm_apply_apply, Circuit.eval_replicate_apply, bitonicLayerCircuit.gather_pair,
      eval_pair, Fin.append_left, flag_eq_decide, pairs, BitonicSort.layerFlags]
    cases ascending <;>
      simp only [Bool.false_eq_true, ↓reduceIte, decide_not, Bool.not_not] <;>
      congr 2 <;> first
      | exact Bool.decide_congr Iff.rfl
      | exact congrArg Bool.not (Bool.decide_congr Iff.rfl)
  · rw [records_pack]
    funext j bit
    cases j using Fin.addCases <;>
      simp only [records, layer, directProductInput, Circuit.eval_comp,
        Circuit.eval_wiring, Function.comp_apply, Fin.addCases_right, Fin.addCases_left,
        Equiv.symm_apply_apply, Circuit.eval_replicate_apply, bitonicLayerCircuit.gather_pair,
        eval_pair, Fin.append_right, flag_eq_decide, BitonicSort.compareLayer,
        BitonicSort.compareLayer.source]
    all_goals
      cases ascending <;>
        simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq,
          Bool.not_eq_true', decide_eq_false_iff_not] <;>
        split_ifs <;>
        simp_all only [Fin.append_left, Fin.append_right, directProductInput] <;>
        contradiction

private theorem cost_layer {k r : ℕ} (key : Fin k → Fin r) (n : ℕ) (ascending : Bool)
    (cost : signature.Op → ℕ) :
    (layer key n ascending).program.cost cost = n *
      (compareSwapCircuit.record
        (Formula.lexLt (Fin.natAdd r ∘ key) (Fin.castAdd r ∘ key)).toCircuit).program.cost
          cost := by
  simp only [layer, Circuit.cost_program_comp, Circuit.cost_program_wiring,
    Circuit.cost_program_replicate, cost_pair, Nat.zero_add, Nat.add_zero]

/-- Run one traced circuit on each half of a record array. -/
def halves {a b n r : ℕ} (left : Circuit signature (n * r) (a * 2 + n * r))
    (right : Circuit signature (n * r) (b * 2 + n * r)) :
    Circuit signature ((n + n) * r) ((a + b) * 2 + (n + n) * r) :=
  collect (left.comp (Circuit.wiring signature (bitonicMergeCircuit.firstHalf n r)))
    (right.comp (Circuit.wiring signature (bitonicMergeCircuit.secondHalf n r)))

private theorem eval_halves {a b n r : ℕ} (left : Circuit signature (n * r) (a * 2 + n * r))
    (right : Circuit signature (n * r) (b * 2 + n * r)) (x : BitString ((n + n) * r)) :
    (halves left right).eval interpretation x =
      pack (Fin.append
        (controls (left.eval interpretation (x ∘ bitonicMergeCircuit.firstHalf n r)))
        (controls (right.eval interpretation (x ∘ bitonicMergeCircuit.secondHalf n r))))
        (Fin.append
          (records (left.eval interpretation (x ∘ bitonicMergeCircuit.firstHalf n r)))
          (records (right.eval interpretation (x ∘ bitonicMergeCircuit.secondHalf n r)))) := by
  simp only [halves, eval_collect, Circuit.eval_comp, Circuit.eval_wiring]

private theorem cost_halves {a b n r : ℕ} (left : Circuit signature (n * r) (a * 2 + n * r))
    (right : Circuit signature (n * r) (b * 2 + n * r)) (cost : signature.Op → ℕ) :
    (halves left right).program.cost cost = left.program.cost cost + right.program.cost cost := by
  simp only [halves, cost_collect, Circuit.cost_program_comp, Circuit.cost_program_wiring,
    Nat.zero_add]

end bitonicSortTraceCircuit

open bitonicSortTraceCircuit
open BitonicSort (arity mergeTraceSize sortTraceSize)

/-- Bitonic merge, retaining comparison decisions before the merged records. -/
def bitonicMergeTraceCircuit {k r : ℕ} (key : Fin k → Fin r) : (d : ℕ) → Bool →
    Circuit signature (arity d * r) (mergeTraceSize d * 2 + arity d * r)
  | 0, _ => Circuit.wiring signature (Fin.addCases Fin.elim0 id)
  | d + 1, ascending =>
    chain (layer key (arity d) ascending)
      (halves (bitonicMergeTraceCircuit key d ascending) (bitonicMergeTraceCircuit key d ascending))

/-- Bitonic sorting, retaining comparison decisions before the sorted records. -/
def bitonicSortTraceCircuit {k r : ℕ} (key : Fin k → Fin r) : (d : ℕ) → Bool →
    Circuit signature (arity d * r) (sortTraceSize d * 2 + arity d * r)
  | 0, _ => Circuit.wiring signature (Fin.addCases Fin.elim0 id)
  | d + 1, ascending =>
    chain (halves (bitonicSortTraceCircuit key d true) (bitonicSortTraceCircuit key d false))
      (bitonicMergeTraceCircuit key (d + 1) ascending)

/-- The forward merge exposes exactly the semantic trace and merged records. -/
theorem eval_bitonicMergeTraceCircuit {k r : ℕ} (key : Fin k → Fin r) (d : ℕ)
    (ascending : Bool) (x : BitString (arity d * r)) :
    (bitonicMergeTraceCircuit key d ascending).eval interpretation x =
      pack (pairs (BitonicSort.mergeTrace (fun row : BitString r => toLex (row ∘ key))
        d ascending (directProductInput x)))
        (BitonicSort.merge (fun row : BitString r => toLex (row ∘ key))
          d ascending (directProductInput x)) := by
  induction d with
  | zero =>
    dsimp only [bitonicMergeTraceCircuit, mergeTraceSize, BitonicSort.merge, BitonicSort.mergeTrace]
    funext i
    cases i using Fin.addCases with
    | left i => exact Fin.elim0 i
    | right i =>
      simp only [Circuit.eval_wiring, Function.comp_apply, Fin.addCases_right,
        pack, Fin.append_right, flatten, directProductInput, Prod.mk.eta,
        Equiv.apply_symm_apply, id_eq]
  | succ d ih =>
    dsimp only [arity] at x
    simp only [bitonicMergeTraceCircuit, mergeTraceSize, arity,
      BitonicSort.mergeTrace, BitonicSort.merge]
    erw [eval_chain _ _ _ _ _ (eval_layer key (arity d) ascending x), eval_halves]
    simp only [ih, controls_pack, records_pack, bitonicMergeCircuit.records_firstHalf,
      bitonicMergeCircuit.records_secondHalf, directProductInput_flatten, pairs_append]

/-- The forward sorter exposes exactly the semantic trace and sorted records. -/
theorem eval_bitonicSortTraceCircuit {k r : ℕ} (key : Fin k → Fin r) (d : ℕ)
    (ascending : Bool) (x : BitString (arity d * r)) :
    (bitonicSortTraceCircuit key d ascending).eval interpretation x =
      pack (pairs (BitonicSort.sortTrace (fun row : BitString r => toLex (row ∘ key))
        d ascending (directProductInput x)))
        (BitonicSort.sort (fun row : BitString r => toLex (row ∘ key))
          d ascending (directProductInput x)) := by
  induction d generalizing ascending with
  | zero =>
    dsimp only [bitonicSortTraceCircuit, sortTraceSize, BitonicSort.sort, BitonicSort.sortTrace]
    funext i
    cases i using Fin.addCases with
    | left i => exact Fin.elim0 i
    | right i =>
      simp only [Circuit.eval_wiring, Function.comp_apply, Fin.addCases_right,
        pack, Fin.append_right, flatten, directProductInput, Prod.mk.eta,
        Equiv.apply_symm_apply, id_eq]
  | succ d ih =>
    dsimp only [arity] at x
    simp only [bitonicSortTraceCircuit, sortTraceSize, arity,
      BitonicSort.sortTrace, BitonicSort.sort]
    erw [eval_chain _ _ _ _ _ (eval_halves _ _ x), eval_bitonicMergeTraceCircuit]
    simp only [ih, arity, mergeTraceSize, controls_pack, records_pack,
      bitonicMergeCircuit.records_firstHalf,
      bitonicMergeCircuit.records_secondHalf, directProductInput_flatten]
    erw [controls_pack, records_pack, ← pairs_append, ← pairs_append]

/-- A traced merge computes each comparator once, retaining its existing control pair. -/
private theorem cost_program_bitonicMergeTraceCircuit {k r : ℕ} (key : Fin k → Fin r) (d : ℕ)
    (ascending : Bool) (cost : signature.Op → ℕ) :
    (bitonicMergeTraceCircuit key d ascending).program.cost cost = mergeTraceSize d *
      (compareSwapCircuit.record
        (Formula.lexLt (Fin.natAdd r ∘ key) (Fin.castAdd r ∘ key)).toCircuit).program.cost
          cost := by
  induction d with
  | zero => simp [bitonicMergeTraceCircuit, mergeTraceSize]
  | succ d ih =>
    simp only [bitonicMergeTraceCircuit]
    erw [cost_chain, cost_layer, cost_halves, ih, mergeTraceSize]
    ring

/-- A traced sort computes each comparator once, retaining its existing control pair. -/
theorem cost_program_bitonicSortTraceCircuit {k r : ℕ} (key : Fin k → Fin r) (d : ℕ)
    (ascending : Bool) (cost : signature.Op → ℕ) :
    (bitonicSortTraceCircuit key d ascending).program.cost cost = sortTraceSize d *
      (compareSwapCircuit.record
        (Formula.lexLt (Fin.natAdd r ∘ key) (Fin.castAdd r ∘ key)).toCircuit).program.cost
          cost := by
  induction d generalizing ascending with
  | zero => simp [bitonicSortTraceCircuit, sortTraceSize]
  | succ d ih =>
    simp only [bitonicSortTraceCircuit]
    erw [cost_chain, cost_halves, ih, ih, cost_program_bitonicMergeTraceCircuit, sortTraceSize]
    ring

/-- Compare corresponding records, discarding the saved controls. Empty records use no gates. -/
def bitonicLayerCircuit {k r : ℕ} (key : Fin k → Fin r) (n : ℕ) (ascending : Bool) :
    Circuit signature ((n + n) * r) ((n + n) * r) :=
  if r = 0 then Circuit.id signature _ else
    (Circuit.wiring signature (Fin.natAdd (n * 2))).comp (layer key n ascending)

/-- Merge a bitonic array by selecting its traced merge's record outputs. -/
def bitonicMergeCircuit {k r : ℕ} (key : Fin k → Fin r) (depth : ℕ) (ascending : Bool) :
    Circuit signature (arity depth * r) (arity depth * r) :=
  if r = 0 then Circuit.id signature _ else
    (Circuit.wiring signature (Fin.natAdd (mergeTraceSize depth * 2))).comp
      (bitonicMergeTraceCircuit key depth ascending)

/-- Sort complete records, retaining the traced construction's sharing internally. -/
def bitonicSortCircuit {k r : ℕ} (key : Fin k → Fin r) (depth : ℕ) (ascending : Bool) :
    Circuit signature (arity depth * r) (arity depth * r) :=
  if r = 0 then Circuit.id signature _ else
    (Circuit.wiring signature (Fin.natAdd (sortTraceSize depth * 2))).comp
      (bitonicSortTraceCircuit key depth ascending)

/-- Reading complete output records agrees with the generic bitonic comparison layer. -/
theorem eval_bitonicLayerCircuit {k r : ℕ} (key : Fin k → Fin r) (n : ℕ) (ascending : Bool)
    (x : BitString ((n + n) * r)) :
    directProductInput ((bitonicLayerCircuit key n ascending).eval interpretation x) =
      BitonicSort.compareLayer (fun record : BitString r => toLex (record ∘ key)) ascending
        (directProductInput x) := by
  by_cases hr : r = 0
  · subst r
    funext j bit
    exact Fin.elim0 bit
  · rw [bitonicLayerCircuit, ite_eq_right hr, Circuit.eval_comp,
      Circuit.eval_wiring, eval_layer]
    exact records_pack _ _

/-- The native circuit realizes bitonic merge on complete records. -/
theorem eval_bitonicMergeCircuit {k r : ℕ} (key : Fin k → Fin r) (depth : ℕ)
    (ascending : Bool) (x : BitString (BitonicSort.arity depth * r)) :
    directProductInput ((bitonicMergeCircuit key depth ascending).eval interpretation x) =
      BitonicSort.merge (fun record : BitString r => toLex (record ∘ key)) depth ascending
        (directProductInput x) := by
  by_cases hr : r = 0
  · subst r
    funext j bit
    exact Fin.elim0 bit
  · rw [bitonicMergeCircuit, ite_eq_right hr, Circuit.eval_comp,
      Circuit.eval_wiring, eval_bitonicMergeTraceCircuit]
    exact records_pack _ _

/-- The native circuit realizes Batcher sorting on complete records. -/
theorem eval_bitonicSortCircuit {k r : ℕ} (key : Fin k → Fin r) (depth : ℕ)
    (ascending : Bool) (x : BitString (BitonicSort.arity depth * r)) :
    directProductInput ((bitonicSortCircuit key depth ascending).eval interpretation x) =
      BitonicSort.sort (fun record : BitString r => toLex (record ∘ key)) depth ascending
        (directProductInput x) := by
  by_cases hr : r = 0
  · subst r
    funext j bit
    exact Fin.elim0 bit
  · rw [bitonicSortCircuit, ite_eq_right hr, Circuit.eval_comp,
      Circuit.eval_wiring, eval_bitonicSortTraceCircuit]
    exact records_pack _ _

/-- The output keys of ascending sorting are nondecreasing. -/
theorem monotone_bitonicSortCircuit {k r : ℕ} (key : Fin k → Fin r) (depth : ℕ)
    (x : BitString (BitonicSort.arity depth * r)) :
    Monotone (fun j => toLex (directProductInput
      ((bitonicSortCircuit key depth true).eval interpretation x) j ∘ key)) := by
  rw [eval_bitonicSortCircuit]
  exact BitonicSort.monotone_sort (fun record : BitString r => toLex (record ∘ key)) depth _

/-- The output keys of descending sorting are nonincreasing. -/
theorem antitone_bitonicSortCircuit {k r : ℕ} (key : Fin k → Fin r) (depth : ℕ)
    (x : BitString (BitonicSort.arity depth * r)) :
    Antitone (fun j => toLex (directProductInput
      ((bitonicSortCircuit key depth false).eval interpretation x) j ∘ key)) := by
  rw [eval_bitonicSortCircuit]
  exact BitonicSort.antitone_sort (fun record : BitString r => toLex (record ∘ key)) depth _

/-- Sorting preserves the multiset of complete input records, including payload and duplicates. -/
theorem bitonicSortCircuit_perm {k r : ℕ} (key : Fin k → Fin r) (depth : ℕ)
    (ascending : Bool) (x : BitString (BitonicSort.arity depth * r)) :
    (List.ofFn (directProductInput
      ((bitonicSortCircuit key depth ascending).eval interpretation x))).Perm
        (List.ofFn (directProductInput x)) := by
  rw [eval_bitonicSortCircuit]
  exact BitonicSort.sort_perm _ _ _ _

/-- A layer uses `n` copies of the comparator under any assignment of gate costs. -/
private theorem cost_program_bitonicLayerCircuit {k r : ℕ} (key : Fin k → Fin r) (n : ℕ)
    (ascending : Bool) (cost : signature.Op → ℕ) :
    (bitonicLayerCircuit key n ascending).program.cost cost =
      n * (compareSwapCircuit key).program.cost cost := by
  by_cases hr : r = 0
  · rw [bitonicLayerCircuit, ite_eq_left hr, compareSwapCircuit, ite_eq_left hr]
    simp only [Circuit.id, Circuit.cost_program_wiring, Nat.mul_zero]
  · rw [bitonicLayerCircuit, ite_eq_right hr, Circuit.cost_program_comp,
      Circuit.cost_program_wiring, Nat.add_zero, cost_layer,
      compareSwapCircuit.cost_record_eq_exchange, compareSwapCircuit, ite_eq_right hr]

/-- Exact merge cost: `depth * 2^depth / 2` comparisons, stated without natural division. -/
theorem two_mul_cost_program_bitonicMergeCircuit {k r : ℕ} (key : Fin k → Fin r)
    (depth : ℕ) (ascending : Bool) (cost : signature.Op → ℕ) :
    2 * (bitonicMergeCircuit key depth ascending).program.cost cost =
      depth * 2 ^ depth * (compareSwapCircuit key).program.cost cost := by
  by_cases hr : r = 0
  · rw [bitonicMergeCircuit, ite_eq_left hr, compareSwapCircuit, ite_eq_left hr]
    simp only [Circuit.id, Circuit.cost_program_wiring, Nat.mul_zero]
  · rw [bitonicMergeCircuit, ite_eq_right hr, Circuit.cost_program_comp,
      Circuit.cost_program_wiring, Nat.add_zero, cost_program_bitonicMergeTraceCircuit,
      ← Nat.mul_assoc, BitonicSort.two_mul_mergeTraceSize,
      compareSwapCircuit.cost_record_eq_exchange, compareSwapCircuit, ite_eq_right hr]

/-- Exact sorting cost: `depth * (depth + 1) * 2^depth / 4` comparisons. The identity includes
depth zero, empty keys, empty records, and arbitrary gate costs. -/
theorem four_mul_cost_program_bitonicSortCircuit {k r : ℕ} (key : Fin k → Fin r)
    (depth : ℕ) (ascending : Bool) (cost : signature.Op → ℕ) :
    4 * (bitonicSortCircuit key depth ascending).program.cost cost =
      depth * (depth + 1) * 2 ^ depth * (compareSwapCircuit key).program.cost cost := by
  by_cases hr : r = 0
  · rw [bitonicSortCircuit, ite_eq_left hr, compareSwapCircuit, ite_eq_left hr]
    simp only [Circuit.id, Circuit.cost_program_wiring, Nat.mul_zero]
  · rw [bitonicSortCircuit, ite_eq_right hr, Circuit.cost_program_comp,
      Circuit.cost_program_wiring, Nat.add_zero, cost_program_bitonicSortTraceCircuit,
      ← Nat.mul_assoc, BitonicSort.four_mul_sortTraceSize,
      compareSwapCircuit.cost_record_eq_exchange, compareSwapCircuit, ite_eq_right hr]

/-- Each of the `n` comparisons is charged once, including constants and negations. -/
@[simp] theorem size_bitonicLayerCircuit {k r : ℕ} (key : Fin k → Fin r) (n : ℕ)
    (ascending : Bool) :
    (bitonicLayerCircuit key n ascending).size = n * (compareSwapCircuit key).size := by
  simpa only [Program.cost_const, one_mul] using
    cost_program_bitonicLayerCircuit key n ascending (fun _ => 1)

/-- Exact total gate count, including constants and negations. -/
theorem four_mul_size_bitonicSortCircuit {k r : ℕ} (key : Fin k → Fin r) (depth : ℕ)
    (ascending : Bool) :
    4 * (bitonicSortCircuit key depth ascending).size =
      depth * (depth + 1) * 2 ^ depth * (if r = 0 then 0 else 6 * k + 6 * r + 2) := by
  simpa only [Program.cost_const, one_mul, size_compareSwapCircuit] using
    four_mul_cost_program_bitonicSortCircuit key depth ascending (fun _ => 1)

/-- Retaining the trace adds no gates to ordinary sorting when records are nonempty. -/
theorem cost_program_bitonicSortTraceCircuit_eq {k r : ℕ} (key : Fin k → Fin r) (d : ℕ)
    (ascending : Bool) (hr : r ≠ 0) (cost : signature.Op → ℕ) :
    (bitonicSortTraceCircuit key d ascending).program.cost cost =
      (bitonicSortCircuit key d ascending).program.cost cost := by
  rw [bitonicSortCircuit, ite_eq_right hr, Circuit.cost_program_comp,
    Circuit.cost_program_wiring, Nat.add_zero]

/-- Exact gate count, including the comparison constant and shared negation at empty width. -/
theorem size_bitonicSortTraceCircuit {k r : ℕ} (key : Fin k → Fin r) (d : ℕ) (ascending : Bool) :
    (bitonicSortTraceCircuit key d ascending).size = sortTraceSize d * (6 * k + 6 * r + 2) := by
  have h := cost_program_bitonicSortTraceCircuit key d ascending (fun _ => 1)
  rw [compareSwapCircuit.cost_record] at h
  simp only [Program.cost_const, one_mul, Formula.size_toCircuit, Formula.size_lexLt] at h
  rw [h]
  ring

end Cslib.Circuits.Boolean
