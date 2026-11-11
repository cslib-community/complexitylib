/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Table.DeltaMatroid
public import CslibFrontier.Logics.Propositional.CSP.Edge.DAGPaths.Blossom
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax

/-!
# Whole-instance blossom contraction

The construction in Section 5.3 of [KazdaKolmogorovRolinek2018], arXiv:1602.03124v6,
printed pp. 12–13. Constraints retain their original list positions, with the new exactly-one
constraint appended. Each distinct touched original constraint is processed once; all its
internal positions are contracted together, even when the cycle visits that constraint repeatedly.
Outside positions retain their original order. Fresh binary natural names are obtained by an
upper-bound fold followed by addition, without enumerating the interval below that bound.

The input and output are the original `CSP Table ℕ`. The intermediate rows below are finite
buffers for its positional occurrence labeling, not a second CSP representation.
-/

public section

open Cslib.BitString

namespace Cslib.Logic.PL.CSP.Blossom

open Table

variable {F : CSP Table ℕ}

/-- Distinct variables used by the actual closed incidence trail. -/
@[expose] def internal (w : Walk F) : List ℕ := (w.edges.map Occurrence.var).dedup

/-- All internal positions of one original constraint, in original argument order. -/
@[expose] def positions (vs scope : List ℕ) : List ℕ :=
  (List.range scope.length).filter fun j => vs.contains (scope.getD j 0)

/-- Selected positions are distinct and in range, independently of variable-name magnitudes. -/
theorem validPositions_positions (vs scope : List ℕ) :
    validPositions scope.length (positions vs scope) = true := by
  apply validPositions_eq_true.mpr
  exact ⟨List.nodup_range.filter _, fun j hj =>
    List.mem_range.mp (List.mem_filter.mp hj).1⟩

/-- One index per distinct touched original constraint, in original constraint order. -/
@[expose] def touched (F : CSP Table ℕ) (vs : List ℕ) : List (Fin F.length) :=
  (List.finRange F.length).filter fun i => !(positions vs F[i.val].2).isEmpty

/-- A name strictly larger than every old variable. Its computation scans actual occurrences. -/
@[expose] def freshBase (F : CSP Table ℕ) : ℕ := F.vars.foldr max 0 + 1

/-- Different original constraint positions receive different fresh binary names. -/
@[expose] def connector (F : CSP Table ℕ) (i : Fin F.length) : ℕ := freshBase F + i.val

/-- The central scope contains one connector per touched original constraint. -/
@[expose] def connectors (F : CSP Table ℕ) (vs : List ℕ) : List ℕ :=
  (touched F vs).map (connector F)

/-- One original constraint is replaced by its simultaneous local contraction. Untouched
constraints, including nullary constraints, retain their relation and scope. -/
@[expose] def constraint (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (i : Fin F.length) : Constraint Table ℕ :=
  if (positions vs F[i.val].2).isEmpty then F[i.val]
  else
    let ps := positions vs F[i.val].2
    let os := outsidePositions F[i.val].2.length ps
    (F[i.val].1.contract (localTuple f i) ps,
      os.map (fun j => F[i.val].2.getD j 0) ++ [connector F i])

/-- Executable whole-instance contraction. This keeps every old constraint and appends the
central exactly-one constraint, even when some old constraints have empty scopes. -/
@[expose] def contract (f : OccurrenceLabeling F Bool) (vs : List ℕ) : CSP Table ℕ :=
  List.ofFn (constraint f vs) ++ [(exactlyOne (connectors F vs), connectors F vs)]

/-- Ordered outside projections of actual original labels, with supplied connector bits and
one supplied central row. The buffers retain exactly the old constraint ordering. -/
@[expose] def transportRows (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (bits : Fin F.length → Bool) (central : List Bool) : List (List Bool) :=
  List.ofFn (fun i : Fin F.length =>
    if (positions vs F[i.val].2).isEmpty then localTuple f i
    else project (localTuple f i)
      (outsidePositions F[i.val].2.length (positions vs F[i.val].2)) ++
      [bits i]) ++ [central]

/-- The local reference rows of the contracted instance. The central row is honestly one-hot;
zero at all connector occurrences would not satisfy its exactly-one relation. -/
@[expose] def referenceRows (f : OccurrenceLabeling F Bool) (vs : List ℕ) : List (List Bool) :=
  transportRows f vs (fun _ => false) (listSingle (connectors F vs).length 0)

/-- Read an actual finite row buffer as the original positional labeling interface. -/
@[expose] def labels (G : CSP Table ℕ) (rows : List (List Bool)) :
    OccurrenceLabeling G Bool := fun o => (rows.getD o.1.val []).getD o.2.val false

/-- The contracted initial labeling. -/
@[expose] def reference (f : OccurrenceLabeling F Bool) (vs : List ℕ) :
    OccurrenceLabeling (contract f vs) Bool := labels _ (referenceRows f vs)

@[simp] theorem length_contract (f : OccurrenceLabeling F Bool) (vs : List ℕ) :
    (contract f vs).length = F.length + 1 := by
  simp [contract]

@[simp] theorem length_connectors (F : CSP Table ℕ) (vs : List ℕ) :
    (connectors F vs).length = (touched F vs).length := by
  simp [connectors]

/-- The constructor never visits an integer interval funded by variable names. -/
theorem freshBase_gt {v : ℕ} (hv : v ∈ F.vars) : v < freshBase F := by
  exact Nat.lt_succ_of_le (List.le_max_of_le hv le_rfl)

/-- Fresh connectors cannot coincide with any old occurring variable. -/
theorem connector_not_mem (i : Fin F.length) : connector F i ∉ F.vars := by
  intro hi
  have := freshBase_gt hi
  simp only [connector] at this
  omega

/-- Connectors distinguish constraint positions even for identical original constraints. -/
theorem connector_injective (F : CSP Table ℕ) : Function.Injective (connector F) := by
  intro i j h
  apply Fin.ext
  exact Nat.add_left_cancel h

/-- Fresh names lie below one addition of the original constraint count to the scanned name
bound. The constructor never loops over the interval below this binary bound. -/
theorem connector_lt (i : Fin F.length) : connector F i < freshBase F + F.length :=
  Nat.add_lt_add_left i.isLt _

@[simp] theorem nodup_touched (F : CSP Table ℕ) (vs : List ℕ) :
    (touched F vs).Nodup := (List.nodup_finRange _).filter _

@[simp] theorem nodup_connectors (F : CSP Table ℕ) (vs : List ℕ) :
    (connectors F vs).Nodup := (nodup_touched F vs).map (connector_injective F)

/-- Every local contraction guard follows from the original valid occurrence labeling. -/
theorem canContract_constraint {f : OccurrenceLabeling F Bool}
    (hf : ValidLabeling sem f) (vs : List ℕ) (i : Fin F.length) :
    F[i.val].1.canContract (localTuple f i) (positions vs F[i.val].2) = true := by
  simp only [canContract, Bool.and_eq_true]
  refine ⟨hf i, ?_⟩
  simpa only [localTuple, List.length_ofFn] using validPositions_positions vs F[i.val].2

/-- Output arity equals the actual output scope, including for untouched nullary constraints. -/
theorem arity_constraint {f : OccurrenceLabeling F Bool}
    (hf : ValidLabeling sem f) (vs : List ℕ) (i : Fin F.length) :
    (constraint f vs i).1.arity = (constraint f vs i).2.length := by
  have hlen : F[i.val].1.arity = F[i.val].2.length := by
    have hs := sem_eq_true.mp (hf i)
    simpa only [localTuple, List.length_ofFn, Fin.getElem_fin] using
      (wellFormed_eq_true.mp hs.1 _ hs.2).symm
  unfold constraint
  split
  · exact hlen
  · simp only [List.length_append, List.length_map, List.length_singleton]
    simpa only [localTuple, List.length_ofFn, Fin.getElem_fin] using
      arity_contract (canContract_constraint hf vs i)

/-- The number of stored rows of each old constraint never increases. Duplicate rows retain
multiplicity, as in `Table.contract`. -/
theorem rows_constraint_le (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (i : Fin F.length) : (constraint f vs i).1.rows.length ≤ F[i.val].1.rows.length := by
  unfold constraint
  split
  · exact le_rfl
  · exact length_rows_contract_le _ _ _

end Cslib.Logic.PL.CSP.Blossom

namespace Cslib.Logic.PL.CSP.Blossom

open Table

variable {F : CSP Table ℕ}

/-- Reading a row buffer recovers each complete row when its width is the actual scope width. -/
theorem localTuple_labels (G : CSP Table ℕ) (rows : List (List Bool)) (i : Fin G.length)
    (hw : (rows.getD i.val []).length = G[i.val].2.length) :
    localTuple (labels G rows) i = rows.getD i.val [] := by
  apply List.ext_getElem
  · simp only [localTuple, List.length_ofFn, hw]
  · intro j hj hk
    simp only [localTuple, labels, List.getElem_ofFn]
    exact List.getD_eq_getElem _ _ hk

/-- A finite row buffer is valid exactly when all its actual local rows are accepted. -/
theorem valid_labels (G : CSP Table ℕ) (rows : List (List Bool))
    (hw : ∀ i : Fin G.length, (rows.getD i.val []).length = G[i.val].2.length)
    (hv : ∀ i : Fin G.length, G[i.val].1.sem (rows.getD i.val []) = true) :
    ValidLabeling sem (labels G rows) := by
  intro i
  rw [localTuple_labels G rows i (hw i)]
  exact hv i

/-- Every retained output constraint has its original list index. -/
theorem get_contract_old (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (i : Fin F.length) : (contract f vs)[i.val]'(by simp) = constraint f vs i := by
  simp [contract]

/-- The finite reference buffer at a retained original constraint. -/
theorem get_referenceRows_old (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (i : Fin F.length) : (referenceRows f vs).getD i.val [] =
      if (positions vs F[i.val].2).isEmpty then localTuple f i
      else project (localTuple f i)
      (outsidePositions F[i.val].2.length (positions vs F[i.val].2)) ++
        [false] := by
  rw [List.getD_eq_getElem _ _ (by simp [referenceRows, transportRows])]
  simp [referenceRows, transportRows]

/-- The central relation occupies the single newly appended constraint position. -/
theorem get_contract_central (f : OccurrenceLabeling F Bool) (vs : List ℕ) :
    (contract f vs)[F.length]'(by simp) =
      (exactlyOne (connectors F vs), connectors F vs) := by
  simp [contract, List.getElem_append_right]

/-- The reference buffer at the central constraint is one-hot, with position zero selected. -/
theorem get_referenceRows_central (f : OccurrenceLabeling F Bool) (vs : List ℕ) :
    (referenceRows f vs).getD F.length [] = listSingle (connectors F vs).length 0 := by
  simp [referenceRows, transportRows]

/-- Each original local reference row is accepted by its actual output constraint. -/
theorem referenceRow_valid {f : OccurrenceLabeling F Bool} (hf : ValidLabeling sem f)
    (vs : List ℕ) (i : Fin F.length) :
    (constraint f vs i).1.sem ((referenceRows f vs).getD i.val []) = true := by
  rw [get_referenceRows_old]
  unfold constraint
  split
  · exact hf i
  · simpa only [localTuple, List.length_ofFn] using
      sem_contract_reference (canContract_constraint hf vs i)

/-- Reference rows have exactly the constructor's scope widths. -/
theorem referenceRow_length (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (i : Fin F.length) :
    ((referenceRows f vs).getD i.val []).length = (constraint f vs i).2.length := by
  rw [get_referenceRows_old]
  unfold constraint
  split <;> simp [localTuple, project]

/-- The constructed initial labeling satisfies all constraints. A nonempty touched set is
necessary: exactly-one on zero connectors rejects every row. -/
theorem valid_reference {f : OccurrenceLabeling F Bool} (hf : ValidLabeling sem f)
    (vs : List ℕ) (hne : touched F vs ≠ []) :
    ValidLabeling sem (reference f vs) := by
  have hpos : 0 < (connectors F vs).length := by
    simpa only [length_connectors] using List.length_pos_iff.mpr hne
  have hlast := get_referenceRows_central f vs
  have hconstraint := get_contract_central f vs
  apply valid_labels
  · intro i
    by_cases hi : i.val < F.length
    · simpa only [get_contract_old f vs ⟨i.val, hi⟩] using
        referenceRow_length f vs ⟨i.val, hi⟩
    · have he : i.val = F.length := by have := i.isLt; simp only [length_contract] at this; omega
      simp only [he, hlast, hconstraint, listSingle, List.length_map, List.length_range]
  · intro i
    by_cases hi : i.val < F.length
    · simpa only [get_contract_old f vs ⟨i.val, hi⟩] using
        referenceRow_valid hf vs ⟨i.val, hi⟩
    · have he : i.val = F.length := by have := i.isLt; simp only [length_contract] at this; omega
      simp only [he, hlast, hconstraint]
      apply (sem_exactlyOne_eq_true _ _).mpr
      exact ⟨by simp [listSingle], count_true_listSingle hpos⟩

/-- No output relation is empty: the explicit reference witnesses it, rather than an assumed
model of the original instance. -/
theorem rows_contract_nonempty {f : OccurrenceLabeling F Bool} (hf : ValidLabeling sem f)
    (vs : List ℕ) (hne : touched F vs ≠ []) (i : Fin (contract f vs).length) :
    (contract f vs)[i.val].1.rows ≠ [] :=
  List.ne_nil_of_mem (sem_eq_true.mp (valid_reference hf vs hne i)).2

end Cslib.Logic.PL.CSP.Blossom

namespace Cslib.Logic.PL.CSP.Blossom

open Table

variable {F : CSP Table ℕ}

private theorem even_arity {table : Table} {n : ℕ} (h : table.arity = n) :
    BitString.IsEvenDeltaMatroid (booleanRelation arity sem table) ↔
      BitString.IsEvenDeltaMatroid {t : Fin n → Bool | table.sem (List.ofFn t) = true} := by
  subst n
  rfl

/-- Local evenness is preserved on the actual ordered output scope. -/
theorem even_constraint {f : OccurrenceLabeling F Bool} (hf : ValidLabeling sem f)
    (hM : EdgeInstance.EvenConstraints sem F) (vs : List ℕ) (i : Fin F.length) :
    BitString.IsEvenDeltaMatroid
      {t : Fin (constraint f vs i).2.length → Bool |
        (constraint f vs i).1.sem (List.ofFn t) = true} := by
  let P (c : Constraint Table ℕ) : Prop := BitString.IsEvenDeltaMatroid
    {t : Fin c.2.length → Bool | c.1.sem (List.ofFn t) = true}
  change P (constraint f vs i)
  have hl : F[i.val].1.arity = F[i.val].2.length := by
    have hs := sem_eq_true.mp (hf i)
    simpa only [localTuple, List.length_ofFn, Fin.getElem_fin] using
      (wellFormed_eq_true.mp hs.1 _ hs.2).symm
  have hm : BitString.IsEvenDeltaMatroid (booleanRelation arity sem F[i.val].1) := by
    apply (even_arity hl).mpr
    simpa only [Fin.getElem_fin] using hM i
  by_cases hp : (positions vs F[i.val].2).isEmpty = true
  · have he : constraint f vs i = F[i.val] := by simp [constraint, hp]
    rw [he]
    simpa only [P, Fin.getElem_fin] using hM i
  · have he : constraint f vs i =
        (F[i.val].1.contract (localTuple f i) (positions vs F[i.val].2),
          (outsidePositions F[i.val].2.length (positions vs F[i.val].2)).map
            (fun j => F[i.val].2.getD j 0) ++ [connector F i]) := by
      simp [constraint, hp]
    have hout := arity_constraint hf vs i
    rw [he] at hout
    rw [he]
    exact (even_arity hout).mp (isEvenDeltaMatroid_contract hm (canContract_constraint hf vs i))

/-- Every actual output relation is a nonempty even delta-matroid, including the central
exactly-one relation with its odd common parity. -/
theorem even_contract {f : OccurrenceLabeling F Bool} (hf : ValidLabeling sem f)
    (hM : EdgeInstance.EvenConstraints sem F) (vs : List ℕ) (hne : touched F vs ≠ []) :
    EdgeInstance.EvenConstraints sem (contract f vs) := by
  intro i
  let P (c : Constraint Table ℕ) : Prop := BitString.IsEvenDeltaMatroid
    {t : Fin c.2.length → Bool | c.1.sem (List.ofFn t) = true}
  change P ((contract f vs)[i.val])
  by_cases hi : i.val < F.length
  · rw [get_contract_old f vs ⟨i.val, hi⟩]
    exact even_constraint hf hM vs ⟨i.val, hi⟩
  · have he : i.val = F.length := by have := i.isLt; simp only [length_contract] at this; omega
    have hget : (contract f vs)[i.val] = (exactlyOne (connectors F vs), connectors F vs) := by
      simp [contract, he, List.getElem_append_right]
    have hscope : connectors F vs ≠ [] := by
      intro hz
      have := congrArg List.length hz
      simp only [length_connectors, List.length_nil, List.length_eq_zero_iff] at this
      exact hne this
    rw [hget]
    exact isEvenDeltaMatroid_exactlyOne (connectors F vs) hscope

end Cslib.Logic.PL.CSP.Blossom
