/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.PolyTime.CSP.Edge.Buffer
public import Complexity.Foundations.Data.BitString.ListParity
public import Complexity.Logics.Propositional.CSP.Edge.Size
import Complexity.Foundations.Data.List.Lookup
import Complexity.Foundations.Data.List.Blocks
import Mathlib.Data.List.GetD
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.EraseDupsBy

/-!
# Explicit-table edge-model checks

Check scope widths, nonempty well-formed stored relations, edge incidences, common parity and
the one-sided symmetric exchange axiom by scanning actual stored rows and coordinates.
No Boolean cube or interval below a binary arity or variable name is enumerated. Duplicate
rows and constraints are permitted; repeated names within a scope are rejected.

The checked model is `EdgeInstance.EvenConstraints` with the actual `Table.sem`, including
its global well-formedness guard. The even delta-matroid convention requires nonempty local
relations, including the unique true nullary relation. This checker is original bookkeeping
for Definition 5 of [KazdaKolmogorovRolinek2018], arXiv:1602.03124v6, printed pp. 4–5.
-/

public section

namespace Cslib.Complexity.CSP.EdgeSolver

open Cslib.Logic.PL Cslib.Logic.PL.CSP Turing.MultiTapeTM Cslib.BitString

/-- Check parity and all one-sided exchanges between two explicit stored rows.
The coordinates are paid for by the first row's actual list. -/
@[expose] def checkPair (table : Table) (x y : List Bool) : Bool :=
  decide (wordParity x = wordParity y) && x.zipIdx.all fun (a, i) =>
    a == y.getD i false || x.zipIdx.any fun (b, j) =>
      b != y.getD j false && table.sem (EdgeAugmenting.flip x [i, j])

/-- Check a constraint's full finite model, including declared arity and scope width. -/
@[expose] def checkConstraint (c : Constraint Table ℕ) : Bool :=
  c.1.wellFormed && decide (c.1.arity = c.2.length) && !c.1.rows.isEmpty &&
    c.1.rows.all fun x => c.1.rows.all fun y => checkPair c.1 x y

/-- Check the actual edge model without scanning a finite universe of names. -/
@[expose] def checkEdge (F : CSP Table ℕ) : Bool :=
  F.all (fun c => decide c.2.Nodup) && F.vars.all (fun v => decide (F.vars.count v = 2))

/-- Complete model guard. False and malformed relations reject before optimization. -/
@[expose] def checkModel (F : CSP Table ℕ) : Bool :=
  checkEdge F && F.all checkConstraint

/-- The incidence guard checks precisely the original positional edge model. -/
theorem checkEdge_eq_true (F : CSP Table ℕ) : checkEdge F = true ↔ EdgeInstance F := by
  simp only [checkEdge, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hs, hc⟩
    exact edgeInstance_of_count_vars (fun i => hs _ (List.getElem_mem i.isLt)) hc
  · intro h
    refine ⟨?_, fun v hv => h.count_vars hv⟩
    intro c hc
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
    exact h.scope_nodup ⟨i, hi⟩

private theorem flip_ofFn {n : ℕ} (x : Fin n → Bool) (i j : Fin n) :
    EdgeAugmenting.flip (List.ofFn x) [i.val, j.val] =
      List.ofFn (BitString.flipOn {i, j} x) := by
  apply List.ext_getElem
  · simp [EdgeAugmenting.flip]
  · intro k hk hl
    have hk' : k < n := by simpa using hl
    simp [EdgeAugmenting.flip, BitString.flipOn_apply, Fin.ext_iff]

/-- The stored-row tests establish the actual nonempty even delta-matroid relation on the
scope's ordered positions. There is no assumed exchange or parity certificate. -/
theorem checkConstraint_sound (c : Constraint Table ℕ) (h : checkConstraint c = true) :
    IsEvenDeltaMatroid {x : Fin c.2.length → Bool | c.1.sem (List.ofFn x) = true} := by
  simp only [checkConstraint, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    List.isEmpty_eq_false_iff, List.all_eq_true] at h
  obtain ⟨⟨⟨hw, ha⟩, hn⟩, hp⟩ := h
  have hrow (x : Fin c.2.length → Bool) (hx : c.1.sem (List.ofFn x) = true) :
      List.ofFn x ∈ c.1.rows := (Table.sem_eq_true.mp hx).2
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · obtain ⟨row, hr⟩ := List.exists_mem_of_ne_nil _ hn
    have hl : row.length = c.2.length := (Table.wellFormed_eq_true.mp hw row hr).trans ha
    let x : Fin c.2.length → Bool := fun j => row.getD j.val false
    have he : List.ofFn x = row := by
      apply List.ext_getElem
      · simpa using hl.symm
      · intro j hj hk
        simp [x, hk]
    refine ⟨x, ?_⟩
    change c.1.sem (List.ofFn x) = true
    rw [he]
    exact Table.sem_eq_true.mpr ⟨hw, hr⟩
  · intro x y hx hy i hi
    have hh := hp _ (hrow x hx) _ (hrow y hy)
    simp only [checkPair, Bool.and_eq_true, List.all_eq_true] at hh
    have hm : (x i, i.val) ∈ (List.ofFn x).zipIdx := by
      have hi' : i.val < ((List.ofFn x).zipIdx).length := by simp
      simpa using (List.getElem_mem hi')
    have hex := hh.2 _ hm
    simp only [List.getD_ofFn, Bool.or_eq_true, beq_iff_eq, hi,
      false_or, List.any_eq_true, Bool.and_eq_true, bne_iff_ne] at hex
    obtain ⟨⟨b, j⟩, hj, hdiff, hvalid⟩ := hex
    have hjn : j < c.2.length := by
      have := List.mem_zipIdx hj
      simpa using this.2.1
    let k : Fin c.2.length := ⟨j, hjn⟩
    have hb : b = x k := by
      simpa [k] using (List.mem_zipIdx hj).2.2
    refine ⟨k, ?_, ?_⟩
    · simpa [hb, k, hjn] using hdiff
    · change c.1.sem (List.ofFn (BitString.flipOn {i, k} x)) = true
      rw [← flip_ofFn]
      exact hvalid
  · intro x y hx hy
    have hh := hp _ (hrow x hx) _ (hrow y hy)
    simp only [checkPair, Bool.and_eq_true, decide_eq_true_eq, wordParity_ofFn] at hh
    exact hh.1

/-- Every actual nonempty even delta-matroid table on the scope passes the stored-row test.
In particular, the checker does not impose even local parity or distinct stored rows. -/
theorem checkConstraint_complete (c : Constraint Table ℕ)
    (hR : IsEvenDeltaMatroid {x : Fin c.2.length → Bool |
      c.1.sem (List.ofFn x) = true}) : checkConstraint c = true := by
  obtain ⟨z, hz⟩ := hR.isDeltaMatroid.nonempty
  have hw := (Table.sem_eq_true.mp hz).1
  have ha : c.1.arity = c.2.length := by
    have hl := Table.wellFormed_eq_true.mp hw _ (Table.sem_eq_true.mp hz).2
    simpa only [List.length_ofFn] using hl.symm
  have hn : c.1.rows ≠ [] := List.ne_nil_of_mem (Table.sem_eq_true.mp hz).2
  have he (row : List Bool) (hr : row ∈ c.1.rows) :
      List.ofFn (fun i : Fin c.2.length => row.getD i.val false) = row := by
    have hl := (Table.wellFormed_eq_true.mp hw row hr).trans ha
    rw [← List.map_range_eq_ofFn c.2.length (fun j => row.getD j false)]
    simpa only [hl] using List.map_getD_range row false
  simp only [checkConstraint, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true]
  refine ⟨⟨⟨hw, ha⟩, hn⟩, ?_⟩
  intro row hrow other hother
  let x : Fin c.2.length → Bool := fun i => row.getD i.val false
  let y : Fin c.2.length → Bool := fun i => other.getD i.val false
  have hx : List.ofFn x = row := he row hrow
  have hy : List.ofFn y = other := he other hother
  have hxm : x ∈ {x : Fin c.2.length → Bool | c.1.sem (List.ofFn x) = true} := by
    change c.1.sem (List.ofFn x) = true
    rw [hx]
    exact Table.sem_eq_true.mpr ⟨hw, hrow⟩
  have hym : y ∈ {x : Fin c.2.length → Bool | c.1.sem (List.ofFn x) = true} := by
    change c.1.sem (List.ofFn y) = true
    rw [hy]
    exact Table.sem_eq_true.mpr ⟨hw, hother⟩
  simp only [checkPair, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨?_, ?_⟩
  · rw [← hx, ← hy, wordParity_ofFn, wordParity_ofFn]
    exact hR.parity_eq hxm hym
  · rintro ⟨a, i⟩ hi
    have hib : i < c.2.length := by
      have hh := (List.mem_zipIdx hi).2.1
      rw [← hx] at hh
      simpa only [List.length_ofFn, Nat.zero_add] using hh
    let k : Fin c.2.length := ⟨i, hib⟩
    have hai : a = x k := by
      have hh := (List.mem_zipIdx hi).2.2
      change a = row.getD i false
      rw [List.getD_eq_getElem _ _ (by simpa using (List.mem_zipIdx hi).2.1)]
      simpa only [Nat.sub_zero] using hh
    by_cases hab : a = other.getD i false
    · simp [hab]
    · have hdiff : x k ≠ y k := by simpa only [← hai] using hab
      obtain ⟨j, hj, hv⟩ := hR.isDeltaMatroid.exchange hxm hym hdiff
      have hm : (x j, j.val) ∈ row.zipIdx := by
        rw [← hx]
        have hj' : j.val < ((List.ofFn x).zipIdx).length := by simp
        simpa using List.getElem_mem hj'
      have hvalid : c.1.sem (EdgeAugmenting.flip row [i, j.val]) = true := by
        rw [← hx]
        change c.1.sem (EdgeAugmenting.flip (List.ofFn x) [k.val, j.val]) = true
        rw [flip_ofFn]
        exact hv
      simp only [Bool.or_eq_true]
      right
      apply List.any_eq_true.mpr
      exact ⟨(x j, j.val), hm, by simpa only [Bool.and_eq_true, bne_iff_ne] using
        (show x j ≠ other.getD j.val false ∧ _ from ⟨hj, hvalid⟩)⟩

/-- Every semantic solver precondition follows from the guard on the raw framed input. -/
theorem checkModel_sound (F : CSP Table ℕ) (h : checkModel F = true) :
    EdgeInstance F ∧ EdgeInstance.EvenConstraints Table.sem F := by
  have ⟨he, hc⟩ : checkEdge F = true ∧ F.all checkConstraint = true := by
    simpa only [checkModel, Bool.and_eq_true] using h
  exact ⟨(checkEdge_eq_true F).mp he,
    fun i => checkConstraint_sound _ (List.all_eq_true.mp hc _ (List.getElem_mem i.isLt))⟩

/-- The full guard recognizes exactly the original edge/even-delta-matroid model. -/
theorem checkModel_eq_true (F : CSP Table ℕ) : checkModel F = true ↔
    EdgeInstance F ∧ EdgeInstance.EvenConstraints Table.sem F := by
  refine ⟨checkModel_sound F, ?_⟩
  rintro ⟨hF, hM⟩
  simp only [checkModel, Bool.and_eq_true, List.all_eq_true]
  refine ⟨(checkEdge_eq_true F).mpr hF, ?_⟩
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
  exact checkConstraint_complete _ (hM ⟨i, hi⟩)

end Cslib.Complexity.CSP.EdgeSolver
