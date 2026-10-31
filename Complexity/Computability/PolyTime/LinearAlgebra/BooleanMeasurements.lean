/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.GenericRAM.Native.BooleanSearch
public import Complexity.Computability.PolyTime.Int.Table
public import Complexity.Foundations.Data.BitString.Sign
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Foundations.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.GetD

/-!
# Integer measurements of Boolean words

Rows and matrices use the existing integer-list/table representations. Evaluation is total:
missing bits are false, extra bits are ignored, and each row uses its own stored length. Matrix
equality compares the complete output list, so a target with the wrong length cannot match.
On rectangular inputs this agrees with the ordinary integer matrix/Boolean-vector product.

The unrestricted representative scan in [OpenAI2026ETH], Lemma 3.2, printed pp. 22–23, searches
for a word having the requested measurements. Fixed-bit restrictions belong to the later scan.
This module supplies evaluation and that representative search, not the full counting identity.

## Main definitions

* `Cslib.LinearAlgebra.BooleanMeasurements.evalBoolRow`: one signed integer measurement.
* `Cslib.LinearAlgebra.BooleanMeasurements.evalBoolMatrix`: all measurements in row order.
* `Cslib.LinearAlgebra.BooleanMeasurements.test`: full measurement-list equality.
* `Cslib.LinearAlgebra.BooleanMeasurements.search`: an unrestricted representative, if one exists.
* `Cslib.LinearAlgebra.BooleanMeasurements.searchCertificate`: native search with raw bit words.

## Main results

* `Cslib.LinearAlgebra.BooleanMeasurements.evalBoolMatrix_getD_eq_sum`: finite-matrix semantics.
* `Cslib.LinearAlgebra.BooleanMeasurements.evalBoolRow_polyTime`,
  `Cslib.LinearAlgebra.BooleanMeasurements.evalBoolMatrix_polyTime`: native evaluation costs.
* `Cslib.LinearAlgebra.BooleanMeasurements.search_some`,
  `Cslib.LinearAlgebra.BooleanMeasurements.search_eq_none_iff_cube`: search correctness.
* `Cslib.LinearAlgebra.BooleanMeasurements.exists_computableInO_search`: traversal-proportional
  time and independent polynomial workspace, including encoding conversions.
* `Cslib.LinearAlgebra.BooleanMeasurements.polyBounded_searchCertificate_space`,
  `Cslib.LinearAlgebra.BooleanMeasurements.exists_polyBounded_searchCertificate_time`:
  composable bounds on the exported certificate itself.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Lemma 3.2, pp. 22–23.
-/

public section

namespace Cslib.LinearAlgebra.BooleanMeasurements

open Turing.MultiTapeTM Cslib.GenericRAM
open scoped BigOperators

/-- Evaluate one integer row. Missing bits are false; bits beyond the row are ignored. -/
@[expose] def evalBoolRow (row : List ℤ) (y : List Bool) : ℤ :=
  ((List.range row.length).map fun j => if y.getD j false then row.getD j 0 else 0).sum

/-- Evaluate every stored row, including ragged inputs, in the original row order. -/
@[expose] def evalBoolMatrix (M : List (List ℤ)) (y : List Bool) : List ℤ :=
  M.map (fun row => evalBoolRow row y)

/-- Row evaluation is the integer dot product with the padded Boolean word. -/
theorem evalBoolRow_eq_sum (row : List ℤ) (y : List Bool) :
    evalBoolRow row y = ∑ j ∈ Finset.range row.length,
      row.getD j 0 * BitString.bitVal ℤ (y.getD j false) := by
  rw [evalBoolRow, List.sum_map_range,
    Fin.sum_univ_eq_sum_range
      (fun j => if y.getD j false then row.getD j 0 else 0) row.length]
  apply Finset.sum_congr rfl
  intro j _
  cases y.getD j false <;> simp [BitString.bitVal]

/-- Evaluation preserves the number of rows, also for malformed/ragged tables. -/
@[simp] theorem length_evalBoolMatrix (M : List (List ℤ)) (y : List Bool) :
    (evalBoolMatrix M y).length = M.length := List.length_map _

/-- Total lookup of an evaluated row agrees with evaluating the total row lookup. -/
theorem evalBoolMatrix_getD (M : List (List ℤ)) (y : List Bool) (i : ℕ) :
    (evalBoolMatrix M y).getD i 0 = evalBoolRow (M.getD i []) y := by
  exact List.getD_map M [] (n := i) (fun row => evalBoolRow row y)

/-- A target of the wrong length cannot be the matrix's complete measurement vector. -/
theorem evalBoolMatrix_ne_of_length_ne (M : List (List ℤ)) (y : List Bool) (target : List ℤ)
    (h : M.length ≠ target.length) : evalBoolMatrix M y ≠ target := by
  intro heq
  exact h (by simpa only [length_evalBoolMatrix] using congrArg List.length heq)

/-- On an `(r,d)` table, measurement `i < r` is the finite integer dot product. The word is
still padded/truncated by the total convention; an exactly `d`-bit word needs no padding. -/
theorem evalBoolMatrix_getD_eq_sum {M : List (List ℤ)} {r d : ℕ}
    (hM : IsTableShape r d M) (y : List Bool) (i : Fin r) :
    (evalBoolMatrix M y).getD i 0 =
      ∑ j : Fin d, rowEntry M i j * BitString.bitVal ℤ (y.getD j false) := by
  have hi : (i : ℕ) < M.length := hM.1.symm ▸ i.isLt
  have hlen : (M.getD i []).length = d := by
    rw [List.getD_eq_getElem _ _ hi]
    exact hM.2 _ (List.getElem_mem hi)
  rw [evalBoolMatrix_getD, evalBoolRow_eq_sum, hlen,
    Fin.sum_univ_eq_sum_range
      (fun j => rowEntry M i j * BitString.bitVal ℤ (y.getD j false)) d]
  rfl

/-- One fixed native polynomial-time routine evaluates arbitrary signed rows and bit words. -/
theorem evalBoolRow_polyTime :
    ComputableInPolyTime (fun p : List ℤ × List Bool => evalBoolRow p.1 p.2)
      (encPair (encList encIntBin) encBits) encIntBin := by
  let ei := encPair (encList encIntBin) encBits
  have hr := ComputableInPolyTime.fst (encList encIntBin) encBits
  have hy := ComputableInPolyTime.snd (encList encIntBin) encBits
  have hp := ComputableInPolyTime.fst ei encUnary
  have hj := ComputableInPolyTime.snd ei encUnary
  have hb := (hy.comp hp).bitsGetDWithInput hj false
  have hv := (hr.comp hp).listGetDWithInput hj 0
  have hm := ComputableInPolyTime.mapWithInput
    (f := fun p j => if p.2.getD j false then p.1.getD j 0 else (0 : ℤ))
    (ComputableInPolyTime.range.comp ((ComputableInPolyTime.length_list encIntBin).comp hr))
    (hb.ite hv (ComputableInPolyTime.const 0))
  exact (show ComputableInPolyTime List.sum (encList encIntBin) encIntBin by fun_prop).comp hm

/-- Evaluate a runtime matrix on a runtime Boolean word with polynomial native costs. -/
theorem evalBoolMatrix_polyTime :
    ComputableInPolyTime (fun p : List (List ℤ) × List Bool => evalBoolMatrix p.1 p.2)
      (encPair (encList (encList encIntBin)) encBits) (encList encIntBin) := by
  let ei := encPair (encList (encList encIntBin)) encBits
  have hM := ComputableInPolyTime.fst (encList (encList encIntBin)) encBits
  have hy := ComputableInPolyTime.snd (encList (encList encIntBin)) encBits
  have hrow : ComputableInPolyTime
      (fun p : (List (List ℤ) × List Bool) × List ℤ => evalBoolRow p.2 p.1.2)
      (encPair ei (encList encIntBin)) encIntBin :=
    evalBoolRow_polyTime.comp
      (g := fun p : (List (List ℤ) × List Bool) × List ℤ => (p.2, p.1.2))
      ((ComputableInPolyTime.snd ei (encList encIntBin)).prod
        (hy.comp (ComputableInPolyTime.fst ei (encList encIntBin))))
  exact ComputableInPolyTime.mapWithInput (f := fun p row => evalBoolRow row p.2) hM hrow

variable {C : Type}

/-- Compare the complete measurement list to the target retained in the runtime context. -/
@[expose] def test (matOf : C → List (List ℤ)) (targetOf : C → List ℤ)
    (p : C × List Bool) : Bool :=
  decide (evalBoolMatrix (matOf p.1) p.2 = targetOf p.1)

/-- Search the unrestricted measurement fiber with the existing streaming first-match loop. -/
@[expose] def search (matOf : C → List (List ℤ)) (targetOf : C → List ℤ)
    (p : C × ℕ) : Option (List Bool) :=
  GenericRAM.BooleanSearch.run (test matOf targetOf) p

/-- A returned representative has the requested width and exactly the requested measurements. -/
theorem search_some (matOf : C → List (List ℤ)) (targetOf : C → List ℤ)
    (p : C × ℕ) {y : List Bool} (h : search matOf targetOf p = some y) :
    y.length = p.2 ∧ evalBoolMatrix (matOf p.1) y = targetOf p.1 := by
  have hs := GenericRAM.BooleanSearch.run_some (test matOf targetOf) p h
  simpa only [test, decide_eq_true_eq] using hs

/-- The raw-bit optional representative has at most the declared width plus its option tag. -/
theorem length_search_le (matOf : C → List (List ℤ)) (targetOf : C → List ℤ) (p : C × ℕ) :
    (encOption encBits (search matOf targetOf p)).length ≤ p.2 + 1 := by
  cases h : search matOf targetOf p with
  | none => simp
  | some y =>
    have hy := (search_some matOf targetOf p h).1
    simp only [encOption_some, List.length_cons, encBits_apply, hy]
    omega

/-- Failure is equivalent to the unrestricted fiber being empty. This uses the total padding
convention even for ragged matrices, rather than silently assuming rectangular input. -/
theorem search_eq_none_iff (matOf : C → List (List ℤ)) (targetOf : C → List ℤ)
    (p : C × ℕ) :
    search matOf targetOf p = none ↔ ∀ y : List Bool, y.length = p.2 →
      evalBoolMatrix (matOf p.1) y ≠ targetOf p.1 := by
  rw [search, GenericRAM.BooleanSearch.run_eq_none_iff]
  simp only [test, decide_eq_false_iff_not]

/-- The equality test is uniformly polynomial in the complete retained context and candidate
word encodings, using the supplied polynomial matrix/target projections. -/
theorem test_polyTime {encC : C ↪ List Bool}
    {matOf : C → List (List ℤ)} {targetOf : C → List ℤ}
    (hM : ComputableInPolyTime matOf encC (encList (encList encIntBin)))
    (ht : ComputableInPolyTime targetOf encC (encList encIntBin)) :
    ComputableInPolyTime (test matOf targetOf) (encPair encC encBits) encBool := by
  have hc := ComputableInPolyTime.fst encC encBits
  have hy := ComputableInPolyTime.snd encC encBits
  exact (evalBoolMatrix_polyTime.comp ((hM.comp hc).prod hy)).decide_eq' (ht.comp hc)

/-- Empty-fiber completeness stated on the ordinary finite Boolean cube. -/
theorem search_eq_none_iff_cube (matOf : C → List (List ℤ)) (targetOf : C → List ℤ)
    (p : C × ℕ) :
    search matOf targetOf p = none ↔ ∀ y : BitString p.2,
      evalBoolMatrix (matOf p.1) (List.ofFn y) ≠ targetOf p.1 := by
  rw [search_eq_none_iff]
  constructor
  · intro h y
    exact h _ List.length_ofFn
  · intro h y hy
    let x : BitString p.2 := fun i => y.getD i false
    have hx : List.ofFn x = y := by
      apply List.ext_getElem (by simpa only [List.length_ofFn] using hy.symm)
      intro i hi hi'
      simp only [List.getElem_ofFn, x, List.getD_eq_getElem _ _ hi']
    exact hx ▸ h x

private theorem listTest_polyTime {encC : C ↪ List Bool}
    {matOf : C → List (List ℤ)} {targetOf : C → List ℤ}
    (hM : ComputableInPolyTime matOf encC (encList (encList encIntBin)))
    (ht : ComputableInPolyTime targetOf encC (encList encIntBin)) :
    ComputableInPolyTime (test matOf targetOf) (encPair encC (encList encBool)) encBool := by
  have hi : ComputableInPolyTime (id : C × List Bool → C × List Bool)
      (encPair encC (encList encBool)) (encPair encC encBits) :=
    (ComputableInPolyTime.fst encC (encList encBool)).prod
      (ComputableInPolyTime.listToBits.comp
        (ComputableInPolyTime.snd encC (encList encBool)))
  exact (test_polyTime hM ht).comp hi

private theorem optionBits_polyTime :
    ComputableInPolyTime (id : Option (List Bool) → Option (List Bool))
      (encOption (encList encBool)) (encOption encBits) := by
  have hi : ComputableInPolyTime (id : Option (List Bool) → Option (List Bool))
      (encOption (encList encBool)) (encOption (encList encBool)) := .id'
  have hs : ComputableInPolyTime
      (fun p : Option (List Bool) × List Bool => some p.2)
      (encPair (encOption (encList encBool)) (encList encBool)) (encOption encBits) :=
    (ComputableInPolyTime.optionSome encBits).comp
      (ComputableInPolyTime.listToBits.comp
        (ComputableInPolyTime.snd (encOption (encList encBool)) (encList encBool)))
  have hn : ComputableInPolyTime (fun _ : Option (List Bool) => (none : Option (List Bool)))
      (encOption (encList encBool)) (encOption encBits) := ComputableInPolyTime.const none
  have h := hi.optionElimWithInput (body := fun _ y => some y) hn hs
  convert h using 1
  funext y
  cases y <;> rfl

/-- The fixed native representative search has traversal-proportional time and polynomial
charged workspace in the full runtime context/width encoding, including both codec boundaries. -/
theorem exists_computableInO_search {encC : C ↪ List Bool}
    {matOf : C → List (List ℤ)} {targetOf : C → List ℤ}
    (hM : ComputableInPolyTime matOf encC (encList (encList encIntBin)))
    (ht : ComputableInPolyTime targetOf encC (encList encIntBin)) :
    ∃ overhead workspace : C × ℕ → ℕ,
      PolyBounded (fun p => (encPair encC encUnary p).length) overhead ∧
      PolyBounded (fun p => (encPair encC encUnary p).length) workspace ∧
      ComputableInO (search matOf targetOf) (encPair encC encUnary) (encOption encBits)
        (fun p => (2 ^ p.2 + 1) * overhead p) workspace := by
  obtain ⟨P, Q, hP, hQ, hs⟩ := GenericRAM.BooleanSearch.exists_computableInO
    (NativeCertificate.ofPolyTime (listTest_polyTime hM ht))
    (NativeCertificate.ofPolyTime_isPolynomial _)
  let codec := NativeCertificate.ofPolyTime optionBits_polyTime
  have hc := NativeCertificate.ofPolyTime_isPolynomial optionBits_polyTime
  have hlen : PolyBounded (fun p : C × ℕ => (encPair encC encUnary p).length)
      (fun p => (encOption (encList encBool) (search matOf targetOf p)).length) := by
    refine PolyBounded.of_forall_le 3 1 fun p => ?_
    have h := GenericRAM.BooleanSearch.length_prefix_result_le
      (test matOf targetOf) p (2 ^ p.2)
    change (encOption (encList encBool) (search matOf targetOf p)).length ≤ 3 * p.2 + 1 at h
    simp only [pow_one, length_encPair, encUnary_apply, List.length_replicate]
    omega
  refine ⟨fun p => P p + codec.time (search matOf targetOf p),
    fun p => Q p + codec.space (search matOf targetOf p),
    hP.add (hc.1.comp hlen), hQ.add (hc.2.comp hlen), ?_⟩
  apply (codec.computes.comp hs).mono_le
  · intro p
    have hn : (1 : ℕ) ≤ 2 ^ p.2 + 1 := Nat.le_add_left 1 _
    change (2 ^ p.2 + 1) * P p + codec.time (search matOf targetOf p) ≤ _
    nlinarith
  · intro p
    exact le_rfl

/-- Native representative search with the consumer's raw-bit option encoding, selecting the
independent resource bounds above once, before any runtime context/width input. Both codec
boundaries are included. -/
noncomputable def searchCertificate {encC : C ↪ List Bool}
    {matOf : C → List (List ℤ)} {targetOf : C → List ℤ}
    (hM : ComputableInPolyTime matOf encC (encList (encList encIntBin)))
    (ht : ComputableInPolyTime targetOf encC (encList encIntBin)) :
    NativeCertificate (search matOf targetOf) (encPair encC encUnary) (encOption encBits) :=
  let h := exists_computableInO_search hM ht
  { time := fun p => (2 ^ p.2 + 1) * h.choose p
    space := h.choose_spec.choose
    computes := h.choose_spec.choose_spec.2.2 }

/-- The exported certificate's actual charged workspace is polynomial in the full input. -/
theorem polyBounded_searchCertificate_space {encC : C ↪ List Bool}
    {matOf : C → List (List ℤ)} {targetOf : C → List ℤ}
    (hM : ComputableInPolyTime matOf encC (encList (encList encIntBin)))
    (ht : ComputableInPolyTime targetOf encC (encList encIntBin)) :
    PolyBounded (fun p => (encPair encC encUnary p).length) (searchCertificate hM ht).space :=
  (exists_computableInO_search hM ht).choose_spec.choose_spec.2.1

/-- The exported certificate's actual time has a fixed polynomial factor times the traversal
count. Its encoded output is charged to its separate polynomial workspace bound. -/
theorem exists_polyBounded_searchCertificate_time {encC : C ↪ List Bool}
    {matOf : C → List (List ℤ)} {targetOf : C → List ℤ}
    (hM : ComputableInPolyTime matOf encC (encList (encList encIntBin)))
    (ht : ComputableInPolyTime targetOf encC (encList encIntBin)) :
    ∃ overhead : C × ℕ → ℕ,
      PolyBounded (fun p => (encPair encC encUnary p).length) overhead ∧
      ∀ p, (searchCertificate hM ht).time p = (2 ^ p.2 + 1) * overhead p :=
  ⟨_, (exists_computableInO_search hM ht).choose_spec.choose_spec.1, fun _ => rfl⟩

end Cslib.LinearAlgebra.BooleanMeasurements
