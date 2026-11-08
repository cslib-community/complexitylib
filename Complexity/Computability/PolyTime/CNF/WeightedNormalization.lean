/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.WeightedExecution
public import Complexity.Computability.PolyTime.Int.Table
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Foundations.Data.Int.Order
import Complexity.Foundations.Data.List.OfFn

/-!
# Binary normalization of original weighted occurrences

Framed-list preprocessing for [ChenJiangZhu2027], Section 7.1, Theorem 7.1,
PDF pp. 22–24. Variable indices and the declared width are unary; coefficients
and targets are signed binary integers. Runtime claims use the plain multitape
calculus, including binary sums and actual list materialization. No composed
query-writing or whole-machine peak-space theorem is asserted.
-/

public section

namespace Cslib.Logic.PL.WeightedRow.BinaryNormalization

open Turing.MultiTapeTM
open scoped BigOperators

/-- Serialized occurrence: variable index, polarity and binary integer weight. -/
abbrev Entry := ℕ × (Bool × ℤ)
/-- Serialized row: explicit occurrences and a signed integer target. -/
abbrev Input := List Entry × ℤ

/-- Framed unary-index / sign / binary-weight encoding. -/
@[expose] def encEntry : Entry ↪ List Bool := encPair encUnary (encPair encBool encIntBin)
/-- Framed row encoding, with binary weights and target. -/
@[expose] def encInput : Input ↪ List Bool := encPair (encList encEntry) encIntBin

/-- Sum exactly the occurrences of one variable and polarity. -/
@[expose] def aggregate (p : Input) (i : ℕ) (s : Bool) : ℤ :=
  (p.1.map fun (j, (t, w)) => if j = i ∧ t = s then w else 0).sum

/-- Common constant extracted at one declared variable. -/
@[expose] def common (p : Input) (i : ℕ) : ℤ :=
  if decide (aggregate p i true ≤ aggregate p i false) then aggregate p i true
  else aggregate p i false

/-- Nonnegative difference on valid positive-weight inputs. -/
@[expose] def difference (p : Input) (i : ℕ) : ℤ :=
  if decide (aggregate p i false < aggregate p i true) then
    aggregate p i true - aggregate p i false else aggregate p i false - aggregate p i true

/-- Extracted constant on all declared variables. -/
@[expose] def constant (n : ℕ) (p : Input) : ℤ :=
  ((List.range n).map (common p)).sum

/-- Total remaining weight. -/
@[expose] def total (n : ℕ) (p : Input) : ℤ :=
  ((List.range n).map (difference p)).sum

/-- Shifted signed target. -/
@[expose] def shifted (n : ℕ) (p : Input) : ℤ := p.2 - constant n p

/-- Interval validity is computed before retaining a row. -/
@[expose] def valid (n : ℕ) (p : Input) : Bool :=
  decide (0 ≤ shifted n p) && decide (shifted n p ≤ total n p)

/-- Smaller residual demand; on invalid inputs it may be negative and is discarded. -/
@[expose] def demand (n : ℕ) (p : Input) : ℤ :=
  if decide (shifted n p ≤ total n p - shifted n p) then shifted n p else total n p - shifted n p

/-- Polarity after demand-minimizing complementation. -/
@[expose] def sign (n : ℕ) (p : Input) (i : ℕ) : Bool :=
  if decide (total n p - shifted n p < shifted n p) then
    !decide (aggregate p i false < aggregate p i true)
  else decide (aggregate p i false < aggregate p i true)

/-- Capped weight in the binary integer representation. -/
@[expose] def weight (n : ℕ) (p : Input) (i : ℕ) : ℤ :=
  if decide (difference p i ≤ demand n p + 1) then difference p i else demand n p + 1

/-- Actual capped affine coefficients in declared-variable order. -/
@[expose] def coefficients (n : ℕ) (p : Input) : List ℤ :=
  (List.range n).map fun i => if sign n p i then weight n p i else -weight n p i

/-- Actual capped affine right hand side. -/
@[expose] def rhs (n : ℕ) (p : Input) : ℤ :=
  demand n p - ((List.range n).map fun i => if sign n p i then 0 else weight n p i).sum

/-- Keep precisely valid nonconstant rows; invalid rows are tracked separately. -/
@[expose] def retained (n : ℕ) (p : Input) : Bool := valid n p && !decide (total n p = 0)

/-- Materialize matrix and RHS, preserving original row order and deleting true rows. -/
@[expose] def materialize (n : ℕ) (rows : List Input) : List (List ℤ) × List ℤ :=
  let kept := rows.filter (retained n)
  (kept.map (coefficients n), kept.map (rhs n))

section Runtime

variable {α : Type} {enc : α ↪ List Bool}

private theorem le_polytime {f g : α → ℤ}
    (hf : ComputableInPolyTime f enc encIntBin) (hg : ComputableInPolyTime g enc encIntBin) :
    ComputableInPolyTime (fun x => decide (f x ≤ g x)) enc encBool :=
  (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.intBin_le).comp (hf.prod hg)

private theorem lt_polytime {f g : α → ℤ}
    (hf : ComputableInPolyTime f enc encIntBin) (hg : ComputableInPolyTime g enc encIntBin) :
    ComputableInPolyTime (fun x => decide (f x < g x)) enc encBool :=
  (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.intBin_lt).comp (hf.prod hg)

attribute [local fun_prop] le_polytime lt_polytime

/-- Aggregation charges every occurrence and all binary additions. -/
@[fun_prop] theorem aggregate_polytime {p : α → Input} {i : α → ℕ} {s : α → Bool}
    (hp : ComputableInPolyTime p enc encInput)
    (hi : ComputableInPolyTime i enc encUnary) (hs : ComputableInPolyTime s enc encBool) :
    ComputableInPolyTime (fun x => aggregate (p x) (i x) (s x)) enc encIntBin := by
  unfold aggregate
  exact (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.intBin_sum).comp
    (ComputableInPolyTime.mapWithInput (by fun_prop) (by
      dsimp only
      fun_prop))

/-- Pointwise constant extraction is binary polynomial time. -/
@[fun_prop] theorem common_polytime {p : α → Input} {i : α → ℕ}
    (hp : ComputableInPolyTime p enc encInput) (hi : ComputableInPolyTime i enc encUnary) :
    ComputableInPolyTime (fun x => common (p x) (i x)) enc encIntBin := by
  unfold common
  fun_prop

/-- Difference coefficients are computed with binary subtraction and comparison. -/
@[fun_prop] theorem difference_polytime {p : α → Input} {i : α → ℕ}
    (hp : ComputableInPolyTime p enc encInput) (hi : ComputableInPolyTime i enc encUnary) :
    ComputableInPolyTime (fun x => difference (p x) (i x)) enc encIntBin := by
  unfold difference
  fun_prop

/-- Binary normalization scalar stages, with unary declared width. -/
@[fun_prop] theorem constant_polytime {n : α → ℕ} {p : α → Input}
    (hn : ComputableInPolyTime n enc encUnary) (hp : ComputableInPolyTime p enc encInput) :
    ComputableInPolyTime (fun x => constant (n x) (p x)) enc encIntBin := by
  unfold constant
  fun_prop

/-- Total weight computation includes all binary arithmetic and loop output. -/
@[fun_prop] theorem total_polytime {n : α → ℕ} {p : α → Input}
    (hn : ComputableInPolyTime n enc encUnary) (hp : ComputableInPolyTime p enc encInput) :
    ComputableInPolyTime (fun x => total (n x) (p x)) enc encIntBin := by
  unfold total
  fun_prop

/-- Shifted targets remain binary throughout. -/
@[fun_prop] theorem shifted_polytime {n : α → ℕ} {p : α → Input}
    (hn : ComputableInPolyTime n enc encUnary) (hp : ComputableInPolyTime p enc encInput) :
    ComputableInPolyTime (fun x => shifted (n x) (p x)) enc encIntBin := by
  unfold shifted
  fun_prop

/-- Interval rejection is binary polynomial time. -/
@[fun_prop] theorem valid_polytime {n : α → ℕ} {p : α → Input}
    (hn : ComputableInPolyTime n enc encUnary) (hp : ComputableInPolyTime p enc encInput) :
    ComputableInPolyTime (fun x => valid (n x) (p x)) enc encBool := by
  unfold valid
  fun_prop

/-- Demand minimization needs no unary conversion of its potentially large value. -/
@[fun_prop] theorem demand_polytime {n : α → ℕ} {p : α → Input}
    (hn : ComputableInPolyTime n enc encUnary) (hp : ComputableInPolyTime p enc encInput) :
    ComputableInPolyTime (fun x => demand (n x) (p x)) enc encIntBin := by
  unfold demand
  fun_prop

/-- Complemented polarity is computed from binary comparisons. -/
@[fun_prop] theorem sign_polytime {n : α → ℕ} {p : α → Input} {i : α → ℕ}
    (hn : ComputableInPolyTime n enc encUnary) (hp : ComputableInPolyTime p enc encInput)
    (hi : ComputableInPolyTime i enc encUnary) :
    ComputableInPolyTime (fun x => sign (n x) (p x) (i x)) enc encBool := by
  unfold sign
  fun_prop

/-- Capping is binary polynomial time. -/
@[fun_prop] theorem weight_polytime {n : α → ℕ} {p : α → Input} {i : α → ℕ}
    (hn : ComputableInPolyTime n enc encUnary) (hp : ComputableInPolyTime p enc encInput)
    (hi : ComputableInPolyTime i enc encUnary) :
    ComputableInPolyTime (fun x => weight (n x) (p x) (i x)) enc encIntBin := by
  unfold weight
  fun_prop

/-- Actual matrix-row writing is charged in the binary runtime certificate. -/
@[fun_prop] theorem coefficients_polytime {n : α → ℕ} {p : α → Input}
    (hn : ComputableInPolyTime n enc encUnary) (hp : ComputableInPolyTime p enc encInput) :
    ComputableInPolyTime (fun x => coefficients (n x) (p x)) enc (encList encIntBin) := by
  unfold coefficients
  fun_prop

/-- Actual RHS construction, including negative-literal constant extraction. -/
@[fun_prop] theorem rhs_polytime {n : α → ℕ} {p : α → Input}
    (hn : ComputableInPolyTime n enc encUnary) (hp : ComputableInPolyTime p enc encInput) :
    ComputableInPolyTime (fun x => rhs (n x) (p x)) enc encIntBin := by
  unfold rhs
  fun_prop

/-- Filtering tests are computed, with no retained-row advice. -/
@[fun_prop] theorem retained_polytime {n : α → ℕ} {p : α → Input}
    (hn : ComputableInPolyTime n enc encUnary) (hp : ComputableInPolyTime p enc encInput) :
    ComputableInPolyTime (fun x => retained (n x) (p x)) enc encBool := by
  unfold retained
  fun_prop

/-- Uniform binary polynomial time for normalization/capping and matrix/RHS writing. -/
@[fun_prop] theorem materialize_polytime :
    ComputableInPolyTime (fun p : ℕ × List Input => materialize p.1 p.2)
      (encPair encUnary (encList encInput))
      (encPair (encList (encList encIntBin)) (encList encIntBin)) := by
  unfold materialize
  fun_prop

end Runtime

/-- Serialize an actual original row, without supplying normalized data. -/
@[expose] def ofOccurrences {n m : ℕ} (R : Occurrences n m) : Input :=
  (List.ofFn fun j => ((R.var j : ℕ), (R.sign j, (R.weight j : ℤ))), R.target)

/-- Binary aggregation equals the actual occurrence-indexed aggregate. -/
theorem aggregate_ofOccurrences {n m : ℕ} (R : Occurrences n m) (i : Fin n) (s : Bool) :
    aggregate (ofOccurrences R) i s = (R.aggregate i s : ℤ) := by
  simp [aggregate, ofOccurrences, Occurrences.aggregate, List.sum_ofFn, Nat.cast_sum,
    Nat.cast_ite, Fin.val_inj]

/-- Pointwise extracted constants agree with original normalization. -/
theorem common_ofOccurrences {n m : ℕ} (R : Occurrences n m) (i : Fin n) :
    common (ofOccurrences R) i = (min (R.aggregate i true) (R.aggregate i false) : ℕ) := by
  simp [common, aggregate_ofOccurrences, min_def, Nat.cast_ite]

/-- Pointwise difference coefficients agree, including opposite polarities and cancellation. -/
theorem difference_ofOccurrences {n m : ℕ} (R : Occurrences n m) (i : Fin n) :
    difference (ofOccurrences R) i = (R.difference i : ℤ) := by
  simp only [difference, aggregate_ofOccurrences, decide_eq_true_eq, Occurrences.difference]
  split <;> omega

/-- The extracted common constant agrees on every declared variable. -/
theorem constant_ofOccurrences {n m : ℕ} (R : Occurrences n m) :
    constant n (ofOccurrences R) = (R.constant : ℤ) := by
  rw [constant, List.sum_map_range]
  simp only [Occurrences.constant, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact common_ofOccurrences R i

/-- Total remaining weight agrees with the reviewed frontend. -/
theorem total_ofOccurrences {n m : ℕ} (R : Occurrences n m) :
    total n (ofOccurrences R) = (R.total : ℤ) := by
  rw [total, List.sum_map_range]
  simp only [Occurrences.total, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact difference_ofOccurrences R i

/-- Shifted signed targets agree before the validity check. -/
theorem shifted_ofOccurrences {n m : ℕ} (R : Occurrences n m) :
    shifted n (ofOccurrences R) = R.shifted := by
  change R.target - constant n (ofOccurrences R) = R.target - R.constant
  rw [constant_ofOccurrences]

/-- Interval rejection is the same computed check as in original normalization. -/
theorem valid_ofOccurrences {n m : ℕ} (R : Occurrences n m) :
    valid n (ofOccurrences R) = decide (0 ≤ R.shifted ∧ R.shifted ≤ (R.total : ℤ)) := by
  simp [valid, shifted_ofOccurrences, total_ofOccurrences]

/-- Valid targets have the same nonnegative minimized demand in the binary representation. -/
theorem demand_ofOccurrences {n m : ℕ} (R : Occurrences n m)
    (hv : 0 ≤ R.shifted ∧ R.shifted ≤ (R.total : ℤ)) :
    demand n (ofOccurrences R) = (R.demand : ℤ) := by
  simp only [demand, shifted_ofOccurrences, total_ofOccurrences,
    decide_eq_true_eq, Occurrences.demand]
  split <;> omega

/-- Truncated minimized demand agrees even for inconsistent signed targets. -/
theorem demand_toNat_ofOccurrences {n m : ℕ} (R : Occurrences n m) :
    (demand n (ofOccurrences R)).toNat = R.demand := by
  simp only [demand, shifted_ofOccurrences, total_ofOccurrences, Occurrences.demand,
    decide_eq_true_eq, min_def]

/-- Complementation agrees with the original normalization on every declared variable. -/
theorem sign_ofOccurrences {n m : ℕ} (R : Occurrences n m) (i : Fin n) :
    sign n (ofOccurrences R) i = R.normalSign i := by
  simp [sign, total_ofOccurrences, shifted_ofOccurrences, aggregate_ofOccurrences,
    Occurrences.normalSign, Occurrences.flip, Occurrences.polarity]

/-- The actual capped binary weights agree with the reviewed natural coefficients. -/
theorem weight_ofOccurrences {n m : ℕ} (R : Occurrences n m)
    (hv : 0 ≤ R.shifted ∧ R.shifted ≤ (R.total : ℤ)) (i : Fin n) :
    weight n (ofOccurrences R) i = (min (R.difference i) (R.demand + 1) : ℕ) := by
  simp only [weight, difference_ofOccurrences, demand_ofOccurrences R hv, min_def,
    decide_eq_true_eq, Nat.cast_ite, Nat.cast_add, Nat.cast_one]
  split_ifs <;> omega

/-- Every emitted affine coefficient is the actual capped normalized row coefficient. -/
theorem coefficient_ofOccurrences {n m d : ℕ} (R : Occurrences n m)
    (hd : R.demand ≤ d) (hv : 0 ≤ R.shifted ∧ R.shifted ≤ (R.total : ℤ)) (i : Fin n) :
    (if sign n (ofOccurrences R) i then weight n (ofOccurrences R) i
      else -weight n (ofOccurrences R) i) = (R.toRow d hd).coefficient i := by
  simp only [sign_ofOccurrences, weight_ofOccurrences R hv, Row.coefficient,
    Occurrences.toRow, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hi : 0 < R.difference i
  · simp [hi]
  · have hz : R.difference i = 0 := by omega
    simp [hz]

/-- The materialized binary row equals the reviewed affine row, not a supplied matrix. -/
theorem coefficients_ofOccurrences {n m d : ℕ} (R : Occurrences n m)
    (hd : R.demand ≤ d) (hv : 0 ≤ R.shifted ∧ R.shifted ≤ (R.total : ℤ)) :
    coefficients n (ofOccurrences R) = (R.toRow d hd).coefficients := by
  rw [coefficients, ← List.map_coe_finRange_eq_range, List.map_map, ← List.ofFn_eq_map]
  unfold Row.coefficients
  congr 1
  funext i
  exact coefficient_ofOccurrences R hd hv i

/-- The negative-literal constant is computed over exactly the nonzero support. -/
private theorem negativeConstant_ofOccurrences {n m d : ℕ} (R : Occurrences n m)
    (hd : R.demand ≤ d) (hv : 0 ≤ R.shifted ∧ R.shifted ≤ (R.total : ℤ)) :
    ((List.range n).map fun i =>
      if sign n (ofOccurrences R) i then 0 else weight n (ofOccurrences R) i).sum =
        (R.toRow d hd).negativeConstant := by
  rw [List.sum_map_range]
  simp only [sign_ofOccurrences, weight_ofOccurrences R hv, Row.negativeConstant,
    Occurrences.toRow, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : 0 < R.difference i
  · simp [hi]
  · have hz : R.difference i = 0 := by omega
    simp [hz]

/-- The materialized binary RHS is the actual normalized/capped affine RHS. -/
theorem rhs_ofOccurrences {n m d : ℕ} (R : Occurrences n m)
    (hd : R.demand ≤ d) (hv : 0 ≤ R.shifted ∧ R.shifted ≤ (R.total : ℤ)) :
    rhs n (ofOccurrences R) = (R.toRow d hd).rhs := by
  rw [rhs, demand_ofOccurrences R hv, negativeConstant_ofOccurrences R hd hv]
  rfl

/-- Serialized rejection scan, separate from deletion of true rows. -/
@[expose] def rejects (n : ℕ) (rows : List Input) : Bool :=
  rows.any fun p => !valid n p

/-- Computed normalization and binary solver diagnostics. Candidate Booleanity is tested
only at full computed rank; it is not interpreted as feasibility at deficient rank. -/
@[expose] def analyze (n : ℕ) (rows : List Input) : Bool × (List ℕ × (Bool × Bool)) :=
  let (A, b) := materialize n rows
  let ids := LinearSystem.gramRowBasis n A
  (rejects n rows, (ids, (LinearSystem.rectangularConsistent n A b,
    if decide (ids.length = n) then LinearSystem.rectangularBoolean n A b else false)))

private theorem rejects_polytime :
    ComputableInPolyTime (fun p : ℕ × List Input => rejects p.1 p.2)
      (encPair encUnary (encList encInput)) encBool := by
  unfold rejects
  exact ComputableInPolyTime.anyWithInput (by fun_prop) (by fun_prop)

/-- Uniform polynomial binary time through actual normalization, affine writing, original-row
selection, consistency and the full-rank candidate test. No desired bound is supplied. -/
@[fun_prop] theorem analyze_polytime :
    ComputableInPolyTime (fun p : ℕ × List Input => analyze p.1 p.2)
      (encPair encUnary (encList encInput))
      (encPair encBool (encPair (encList encUnary) (encPair encBool encBool))) := by
  have hn : ComputableInPolyTime (fun p : ℕ × List Input => p.1)
      (encPair encUnary (encList encInput)) encUnary := by fun_prop
  have hA := materialize_polytime.fst'
  have hb := materialize_polytime.snd'
  have hids := LinearSystem.gramRowBasis_polytime.comp (hn.prod hA)
  have hc := LinearSystem.rectangularConsistent_polytime.comp ((hn.prod hA).prod hb)
  have hbool := LinearSystem.rectangularBoolean_polytime.comp ((hn.prod hA).prod hb)
  have hl : ComputableInPolyTime
      (fun p : ℕ × List Input => (LinearSystem.gramRowBasis p.1 (materialize p.1 p.2).1).length)
      (encPair encUnary (encList encInput)) encUnary := by fun_prop
  have ht := (ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.decide_eq encUnary)).comp (hl.prod hn)
  exact rejects_polytime.prod (hids.prod (hc.prod (ht.ite' hbool (by fun_prop))))

/-- Filtering and writing the serialized original rows matches the actual retained capped rows. -/
private theorem retained_pairs {n t d : ℕ} {m : Fin t → ℕ} (R : (j : Fin t) → Occurrences n (m j))
    (hd : ∀ j, (R j).demand ≤ d) (js : List (Fin t)) :
    ((js.map fun j => ofOccurrences (R j)).filter (retained n)).map
        (fun p => (coefficients n p, rhs n p)) =
      (cappedRows (js.map fun j => (R j).normalize d (hd j))).map
        (fun Q => (Q.coefficients, Q.rhs)) := by
  induction js with
  | nil => simp [cappedRows]
  | cons j js ih =>
    by_cases hv : 0 ≤ (R j).shifted ∧ (R j).shifted ≤ ((R j).total : ℤ)
    · by_cases hz : (R j).total = 0
      · have hshift : (R j).shifted = 0 := by rw [hz] at hv; omega
        simp [retained, valid_ofOccurrences, total_ofOccurrences,
          Occurrences.normalize, hz, hshift, cappedRows, ih]
      · simp [retained, valid_ofOccurrences, total_ofOccurrences,
          Occurrences.normalize, hv, hz, cappedRows, ih,
          coefficients_ofOccurrences (R j) (hd j) hv, rhs_ofOccurrences (R j) (hd j) hv]
    · simp [retained, valid_ofOccurrences,
        Occurrences.normalize, hv, cappedRows, ih]

/-- Both emitted tables equal the actual original-input normalized/capped affine tables. -/
theorem materialize_ofOccurrences {n t d : ℕ} {m : Fin t → ℕ}
    (R : (j : Fin t) → Occurrences n (m j))
    (hd : ∀ j, (R j).demand ≤ d) :
    materialize n ((List.finRange t).map fun j => ofOccurrences (R j)) =
      (cappedMatrix ((List.finRange t).map fun j => (R j).normalize d (hd j)),
        cappedRhs ((List.finRange t).map fun j => (R j).normalize d (hd j))) := by
  have h := retained_pairs R hd (List.finRange t)
  have ha := congrArg (List.map Prod.fst) h
  have hb := congrArg (List.map Prod.snd) h
  simp only [List.map_map, Function.comp_def] at ha hb
  exact Prod.ext ha hb

/-- Rejection is preserved even though invalid rows do not enter the emitted matrix. -/
theorem rejects_ofOccurrences {n t d : ℕ} {m : Fin t → ℕ} (R : (j : Fin t) → Occurrences n (m j))
    (hd : ∀ j, (R j).demand ≤ d) :
    rejects n ((List.finRange t).map fun j => ofOccurrences (R j)) =
      rejected ((List.finRange t).map fun j => (R j).normalize d (hd j)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [rejects, List.any_map, List.any_eq_true, rejected_iff, List.mem_map]
  constructor
  · rintro ⟨j, hj, hv⟩
    have hv : ¬ (0 ≤ (R j).shifted ∧ (R j).shifted ≤ ((R j).total : ℤ)) := by
      simpa only [Function.comp_def, valid_ofOccurrences, Bool.not_eq_true',
        decide_eq_false_iff_not] using hv
    exact ⟨j, hj, by simp [Occurrences.normalize, hv]⟩
  · rintro ⟨j, hj, he⟩
    refine ⟨j, hj, ?_⟩
    by_cases hv : 0 ≤ (R j).shifted ∧ (R j).shifted ≤ ((R j).total : ℤ)
    · exfalso
      unfold Occurrences.normalize at he
      split_ifs at he
    · simp [valid_ofOccurrences, hv]

/-- Exact link from the certified binary stage to every computed large-dimension dispatcher test. -/
theorem analyze_ofOccurrences {n t d : ℕ} {m : Fin t → ℕ} (R : (j : Fin t) → Occurrences n (m j))
    (hd : ∀ j, (R j).demand ≤ d) :
    let ns := (List.finRange t).map fun j => (R j).normalize d (hd j)
    analyze n ((List.finRange t).map fun j => ofOccurrences (R j)) =
      (rejected ns, (cappedBasis ns,
        (LinearSystem.rectangularConsistent n (cappedMatrix ns) (cappedRhs ns),
          if (cappedBasis ns).length = n then
            LinearSystem.rectangularBoolean n (cappedMatrix ns) (cappedRhs ns) else false))) := by
  simp only [analyze, materialize_ofOccurrences R hd, rejects_ofOccurrences R hd,
    cappedBasis, decide_eq_true_eq]
  rfl

/-- Each original coefficient's binary magnitude fits inside the actual framed row input. -/
theorem entry_bits_le_input (p : Input) (j : ℕ) (s : Bool) (w : ℤ)
    (he : (j, s, w) ∈ p.1) : w.natAbs.size ≤ (encInput p).length := by
  have h := SizedListEncoding.length_elem_le (encA := encEntry) (encL := encList encEntry)
    p.1 (j, s, w) he
  have hp := length_le_encPair_left (encList encEntry) encIntBin p
  have hw : w.natAbs.size ≤ (encEntry (j, s, w)).length := by
    simp only [encEntry, length_encPair, length_encIntBin]
    omega
  exact hw.trans (h.trans hp)

/-- Every partial binary aggregation sum has input-controlled bit growth, before capping. -/
theorem aggregate_prefix_bits (p : Input) (i k : ℕ) (s : Bool) :
    (((p.1.map fun (j, (t, w)) => if j = i ∧ t = s then (w : ℤ) else 0).take k).sum).natAbs.size ≤
      (encInput p).length + p.1.length := by
  have h := Int.size_natAbs_sum_le (b := (encInput p).length)
    (l := (p.1.map fun (j, (t, w)) => if j = i ∧ t = s then (w : ℤ) else 0).take k) (by
      intro z hz
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_of_mem_take hz)
      rcases e with ⟨j, t, w⟩
      dsimp only
      split_ifs
      · exact entry_bits_le_input p j t w he
      · simp)
  exact h.trans (Nat.add_le_add_left
    ((Nat.size_le_self _).trans (by simp only [List.length_take, List.length_map]; omega)) _)

private theorem row_coefficient_bound {n d : ℕ} (R : Row (Fin n) d) (i : Fin n) :
    (R.coefficient i).natAbs ≤ d + 1 := by
  unfold Row.coefficient
  split_ifs with hi hs
  · simpa using (R.capped i hi).trans (Nat.add_le_add_right R.bounded 1)
  · simpa using (R.capped i hi).trans (Nat.add_le_add_right R.bounded 1)
  · simp

private theorem row_rhs_bound {n d : ℕ} (R : Row (Fin n) d) :
    R.rhs.natAbs ≤ (n + 1) * (d + 1) := by
  have he : R.negativeConstant =
      ((∑ i ∈ R.support, if R.sign i then 0 else R.weight i : ℕ) : ℤ) := by
    simp [Row.negativeConstant]
  have hn : R.negativeConstant.natAbs ≤ n * (d + 1) := by
    rw [he, Int.natAbs_natCast]
    calc
      _ ≤ ∑ _i ∈ R.support, (d + 1) := by
        apply Finset.sum_le_sum
        intro i hi
        split_ifs
        · omega
        · exact (R.capped i hi).trans (Nat.add_le_add_right R.bounded 1)
      _ = R.support.card * (d + 1) := by simp
      _ ≤ n * (d + 1) := Nat.mul_le_mul_right _ (by simpa using Finset.card_le_univ R.support)
  have h := Int.natAbs_sub_le (R.demand : ℤ) R.negativeConstant
  simp only [Int.natAbs_natCast] at h
  unfold Row.rhs
  have := R.bounded
  nlinarith

/-- Actual post-cap matrix entries have demand-controlled magnitude, including default zeros. -/
theorem materialize_coefficient_bound {n t d : ℕ} {m : Fin t → ℕ}
    (R : (j : Fin t) → Occurrences n (m j))
    (hd : ∀ j, (R j).demand ≤ d) (i j : ℕ) :
    (rowEntry (materialize n ((List.finRange t).map fun j => ofOccurrences (R j))).1 i j).natAbs ≤
      d + 1 := by
  rw [materialize_ofOccurrences R hd]
  refine rowEntry_rel_of_mem (P := fun z : ℤ => z.natAbs ≤ d + 1) (by simp) ?_ i j
  intro row hr z hz
  unfold cappedMatrix at hr
  obtain ⟨Q, _, rfl⟩ := List.mem_map.mp hr
  obtain ⟨c, rfl⟩ := List.mem_ofFn.mp hz
  exact row_coefficient_bound Q c

/-- Actual post-cap RHS entries have demand/width-controlled magnitude. -/
theorem materialize_rhs_bound {n t d : ℕ} {m : Fin t → ℕ} (R : (j : Fin t) → Occurrences n (m j))
    (hd : ∀ j, (R j).demand ≤ d) (i : ℕ) :
    ((materialize n ((List.finRange t).map fun j => ofOccurrences (R j))).2.getD i 0).natAbs ≤
      (n + 1) * (d + 1) := by
  rw [materialize_ofOccurrences R hd]
  apply List.natAbs_getD_le_of_forall
  intro z hz
  unfold cappedRhs at hz
  obtain ⟨Q, _, rfl⟩ := List.mem_map.mp hz
  exact row_rhs_bound Q

/-- Bird determinant intermediate widths on the actual normalized matrix and computed basis. -/
theorem original_gram_stage_bits {n t d : ℕ} {m : Fin t → ℕ} (R : (j : Fin t) → Occurrences n (m j))
    (hd : ∀ j, (R j).demand ≤ d) (k i j : ℕ) :
    let A := (materialize n ((List.finRange t).map fun j => ofOccurrences (R j))).1
    let ids := LinearSystem.gramRowBasis n A
    let β := (n + 1) * (d + 1)
    Circuits.Rational.intBits
        (rowEntry (Circuits.Rational.stagesRows (LinearSystem.rowGram n A ids) k) i j) ≤
      n + 2 * β + k * (1 + n + (n + 2 * β)) + 1 := by
  dsimp only
  have ha (i j : ℕ) :
      (rowEntry (materialize n ((List.finRange t).map fun j => ofOccurrences (R j))).1 i j).natAbs <
        2 ^ ((n + 1) * (d + 1)) := by
    apply (materialize_coefficient_bound R hd i j).trans_lt
    exact (Nat.lt_two_pow_self).trans_le
      (Nat.pow_le_pow_right (by decide) (by nlinarith : d + 1 ≤ (n + 1) * (d + 1)))
  let A := (materialize n ((List.finRange t).map fun j => ofOccurrences (R j))).1
  have h := LinearSystem.rowGram_stage_bits_le n A (LinearSystem.gramRowBasis n A)
    ((n + 1) * (d + 1)) k i j ha
  have hl := LinearSystem.gramRowBasis_length n
    (materialize n ((List.finRange t).map fun j => ofOccurrences (R j))).1
  apply h.trans
  gcongr

/-- Explicit binary growth for the actual recovered solver certificate after original normalization.
The bound is derived from capping and declared width, not supplied as rank/size advice. -/
theorem original_certificate_bits {n t d : ℕ} {m : Fin t → ℕ}
    (R : (j : Fin t) → Occurrences n (m j))
    (hd : ∀ j, (R j).demand ≤ d) :
    let (A, b) := materialize n ((List.finRange t).map fun j => ofOccurrences (R j))
    let β := (n + 1) * (d + 1)
    let g := n + 2 * β
    let B := g + n * (1 + n + g) + 2
    Circuits.Rational.intBits (LinearSystem.rectangularCertificate n A b).1 ≤ B ∧
      ∀ z ∈ (LinearSystem.rectangularCertificate n A b).2,
        Circuits.Rational.intBits z ≤ n + β + B + 1 := by
  dsimp only
  apply LinearSystem.rectangularCertificate_bits_le
  · intro i j
    apply (materialize_coefficient_bound R hd i j).trans_lt
    exact (Nat.lt_two_pow_self).trans_le
      (Nat.pow_le_pow_right (by decide) (by nlinarith : d + 1 ≤ (n + 1) * (d + 1)))
  · intro i
    exact (materialize_rhs_bound R hd i).trans_lt Nat.lt_two_pow_self

/-- Output storage is polynomial as a consequence of the proved machine-time certificate. -/
theorem materialize_output_polyBounded :
    PolyBounded (fun p : ℕ × List Input => (encPair encUnary (encList encInput) p).length)
      (fun p => (encPair (encList (encList encIntBin)) (encList encIntBin)
        (materialize p.1 p.2)).length) :=
  ((ComputableInPolyTime.encoding_length _).comp materialize_polytime).polyBounded

end Cslib.Logic.PL.WeightedRow.BinaryNormalization
