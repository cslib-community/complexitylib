/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CSP.Table
public import Complexity.Computability.PolyTime.CSP.ToCNF
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Structure
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length

/-!
# Native polynomial-time explicit relation tables

The alphabet is the infinite type `CSP.Table`: every active relation is supplied as an explicit
list of rows. No finite-alphabet lookup or assumed solver appears in these certificates.
`encTable` frames the binary arity before the doubly framed Boolean rows. Indices and variable
names are binary; list traversal counters are unary. Contraction ranges over the explicit
reference row, so malformed huge binary arities do not cause huge loops.

Exactly-one generation takes a scope list, whose length pays for its quadratic output.
This is polynomial in that list's framed encoding, not in a binary arity supplied alone.
The bounds below charge actual framing, binary arity and binary names. They are explicit
encoding calculations for the Section 5.3 update in [KazdaKolmogorovRolinek2018]; they do not
assert the paper's full solver or its combinatorial instance-size estimate.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL Turing.MultiTapeTM
open Cslib.Logic.PL.CSP.Table

/-- A table's binary arity, framed, followed by its framed list of framed Boolean rows.
Each Boolean row bit uses three bits under `encList encBool`; each row is framed again. -/
enc_structure encTable : Cslib.Logic.PL.CSP.Table where
  arity : encNat, rows : (encList (encList encBool))

/-- Reading the binary arity is a projection of the encoded field tuple. -/
@[fun_prop] theorem computableInPolyTime_tableArity :
    ComputableInPolyTime Cslib.Logic.PL.CSP.Table.arity encTable encNat :=
  encTable_arity_deg.computableInPolyTime

/-- Reading all rows preserves their actual doubly framed Boolean encoding. -/
@[fun_prop] theorem computableInPolyTime_tableRows :
    ComputableInPolyTime Cslib.Logic.PL.CSP.Table.rows encTable
      (encList (encList encBool)) := encTable_rows_deg.computableInPolyTime

/-- Contraction input: table, then feasible reference row, then binary internal positions;
the table and the reference row are framed by the enclosing pairs. -/
abbrev encTableContraction := encPair encTable (encPair (encList encBool) (encList encNat))

/-- Scanning a table for width errors is native polynomial-time, with binary arity. -/
@[fun_prop] theorem computableInPolyTime_tableWellFormed :
    ComputableInPolyTime Cslib.Logic.PL.CSP.Table.wellFormed encTable encBool := by
  unfold Cslib.Logic.PL.CSP.Table.wellFormed
  apply ComputableInPolyTime.allWithInput (by fun_prop)
  have hlen : ComputableInPolyTime
      (fun p : Cslib.Logic.PL.CSP.Table × List Bool => p.2.length)
      (encPair encTable (encList encBool)) encUnary := by fun_prop
  exact ComputableInPolyTime.decide_eq'
    ((ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.unary_to_binary).comp hlen)
    (by fun_prop)

/-- Native row membership uses an actual scan of the supplied row table. -/
@[fun_prop] theorem computableInPolyTime_tableSem :
    ComputableInPolyTime (fun p : Cslib.Logic.PL.CSP.Table × List Bool => p.1.sem p.2)
      (encPair encTable (encList encBool)) encBool := by
  unfold Cslib.Logic.PL.CSP.Table.sem
  simp only [List.contains_eq_mem]
  have hlen : ComputableInPolyTime
      (fun p : Cslib.Logic.PL.CSP.Table × List Bool => p.2.length)
      (encPair encTable (encList encBool)) encUnary := by fun_prop
  have heq := ComputableInPolyTime.decide_eq'
    ((ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.unary_to_binary).comp hlen)
    (show ComputableInPolyTime (fun p : Cslib.Logic.PL.CSP.Table × List Bool => p.1.arity)
      (encPair encTable (encList encBool)) encNat by fun_prop)
  fun_prop

/-- Binary coordinate lookup charges only the binary index, even beyond the row's end. -/
theorem computableInPolyTime_tableProject :
    ComputableInPolyTime (fun p : List Bool × List ℕ => project p.1 p.2)
      (encPair (encList encBool) (encList encNat)) (encList encBool) := by
  unfold project
  apply ComputableInPolyTime.mapWithInput (by fun_prop)
  exact .of_tidy (ComputableTidilyInPolyTime.listGetD_binary (encA := encBool)
    false (by fun_prop) (by fun_prop))

/-- Counting deviations scans binary positions and uses bounded binary lookup. -/
theorem computableInPolyTime_tableDeviations :
    ComputableInPolyTime (fun p : (List Bool × List Bool) × List ℕ =>
      deviations p.1.1 p.1.2 p.2)
      (encPair (encPair (encList encBool) (encList encBool)) (encList encNat)) encUnary := by
  unfold deviations
  apply ComputableInPolyTime.countPWithInput (by fun_prop)
  have hleft := ComputableTidilyInPolyTime.listGetD_binary (encA := encBool) false
    (show ComputableTidilyInPolyTime
      (fun p : ((List Bool × List Bool) × List ℕ) × ℕ => p.1.1.2)
      (encPair (encPair (encPair (encList encBool) (encList encBool)) (encList encNat)) encNat)
      (encList encBool) by fun_prop)
    (show ComputableTidilyInPolyTime
      (fun p : ((List Bool × List Bool) × List ℕ) × ℕ => p.2)
      (encPair (encPair (encPair (encList encBool) (encList encBool)) (encList encNat)) encNat)
      encNat by fun_prop)
  have hright := ComputableTidilyInPolyTime.listGetD_binary (encA := encBool) false
    (show ComputableTidilyInPolyTime
      (fun p : ((List Bool × List Bool) × List ℕ) × ℕ => p.1.1.1)
      (encPair (encPair (encPair (encList encBool) (encList encBool)) (encList encNat)) encNat)
      (encList encBool) by fun_prop)
    (show ComputableTidilyInPolyTime
      (fun p : ((List Bool × List Bool) × List ℕ) × ℕ => p.2)
      (encPair (encPair (encPair (encList encBool) (encList encBool)) (encList encNat)) encNat)
      encNat by fun_prop)
  exact ComputableInPolyTime.bne (.of_tidy hleft) (.of_tidy hright)

/-- Validate positions without expanding their binary values into unary indices. -/
theorem computableInPolyTime_tableValidPositions :
    ComputableInPolyTime (fun p : ℕ × List ℕ => validPositions p.1 p.2)
      (encPair encNat (encList encNat)) encBool := by
  unfold validPositions
  apply ComputableInPolyTime.allWithInput (by fun_prop)
  have hc : ComputableInPolyTime
      (fun p : (ℕ × List ℕ) × ℕ => p.1.2.count p.2)
      (encPair (encPair encNat (encList encNat)) encNat) encUnary :=
    .of_tidy (ComputableTidilyInPolyTime.countWithInput (by fun_prop) (by fun_prop))
  fun_prop

/-- Enumerating outside positions is polynomial in the unary width and binary selection list. -/
theorem computableInPolyTime_tableOutsidePositions :
    ComputableInPolyTime (fun p : ℕ × List ℕ => outsidePositions p.1 p.2)
      (encPair encUnary (encList encNat)) (encList encNat) := by
  have hrange : ComputableInPolyTime List.range encUnary (encList encNat) := by
    have h := ComputableInPolyTime.map
      (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.unary_to_binary)
    simpa only [Function.comp_def, List.map_id'] using h.comp
      (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.range)
  unfold outsidePositions
  simp only [List.contains_eq_mem]
  apply ComputableInPolyTime.filterWithInput (hrange.comp (by fun_prop))
  fun_prop

/-- Local contraction, including malformed cases, is native polynomial-time in actual input bits. -/
theorem computableInPolyTime_tableContract :
    ComputableInPolyTime
      (fun p : Cslib.Logic.PL.CSP.Table × List Bool × List ℕ => p.1.contract p.2.1 p.2.2)
      encTableContraction encTable := by
  have href : ComputableInPolyTime
      (fun p : Cslib.Logic.PL.CSP.Table × List Bool × List ℕ => p.2.1)
      encTableContraction (encList encBool) := by fun_prop
  have hwidth := (ComputableInPolyTime.length_list encBool).comp href
  have hout := computableInPolyTime_tableOutsidePositions.comp
    (hwidth.prod (show ComputableInPolyTime
      (fun p : Cslib.Logic.PL.CSP.Table × List Bool × List ℕ => p.2.2)
      encTableContraction (encList encNat) by fun_prop))
  have hguard : ComputableInPolyTime
      (fun p : Cslib.Logic.PL.CSP.Table × List Bool × List ℕ =>
        p.1.canContract p.2.1 p.2.2) encTableContraction encBool := by
    unfold canContract
    have hv := computableInPolyTime_tableValidPositions.comp
      (((ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.unary_to_binary).comp
        hwidth).prod (show ComputableInPolyTime
          (fun p : Cslib.Logic.PL.CSP.Table × List Bool × List ℕ => p.2.2)
          encTableContraction (encList encNat) by fun_prop))
    fun_prop
  have hdev : ComputableInPolyTime
      (fun p : (Cslib.Logic.PL.CSP.Table × List Bool × List ℕ) × List Bool =>
        deviations p.1.2.1 p.2 p.1.2.2)
      (encPair encTableContraction (encList encBool)) encUnary :=
    computableInPolyTime_tableDeviations.comp
      (show ComputableInPolyTime
        (fun p : (Cslib.Logic.PL.CSP.Table × List Bool × List ℕ) × List Bool =>
          ((p.1.2.1, p.2), p.1.2.2))
        (encPair encTableContraction (encList encBool))
        (encPair (encPair (encList encBool) (encList encBool)) (encList encNat)) by fun_prop)
  have hrows : ComputableInPolyTime
      (fun p : Cslib.Logic.PL.CSP.Table × List Bool × List ℕ =>
        p.1.rows.filter fun row => decide (deviations p.2.1 row p.2.2 ≤ 1))
      encTableContraction (encList (encList encBool)) := by
    apply ComputableInPolyTime.filterWithInput (by fun_prop)
    fun_prop
  have hproject : ComputableInPolyTime
      (fun p : (Cslib.Logic.PL.CSP.Table × List Bool × List ℕ) × List Bool =>
        project p.2 (outsidePositions p.1.2.1.length p.1.2.2))
      (encPair encTableContraction (encList encBool)) (encList encBool) :=
    computableInPolyTime_tableProject.comp
      ((ComputableInPolyTime.snd encTableContraction (encList encBool)).prod
        (hout.comp (ComputableInPolyTime.fst encTableContraction (encList encBool))))
  have hnewrows := ComputableInPolyTime.mapWithInput
    (f := fun (p : Cslib.Logic.PL.CSP.Table × List Bool × List ℕ) (row : List Bool) =>
      project row (outsidePositions p.2.1.length p.2.2) ++
        [decide (deviations p.2.1 row p.2.2 = 1)]) hrows
    (show ComputableInPolyTime
      (fun p : (Cslib.Logic.PL.CSP.Table × List Bool × List ℕ) × List Bool =>
        project p.2 (outsidePositions p.1.2.1.length p.1.2.2) ++
          [decide (deviations p.1.2.1 p.2 p.1.2.2 = 1)])
      (encPair encTableContraction (encList encBool)) (encList encBool) by fun_prop)
  have hnewwidth : ComputableInPolyTime
      (fun p : Cslib.Logic.PL.CSP.Table × List Bool × List ℕ =>
        (outsidePositions p.2.1.length p.2.2).length + 1) encTableContraction encNat := by
    apply (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.unary_to_binary).comp
    fun_prop
  unfold Cslib.Logic.PL.CSP.Table.contract
  apply hguard.ite
  · exact (hnewwidth.prod hnewrows).of_enc_eq fun _ => rfl
  · exact ComputableInPolyTime.const _

/-- One-hot row generation uses unary width and index. -/
theorem computableInPolyTime_tableOneHot :
    ComputableInPolyTime (fun p : ℕ × ℕ => oneHot p.1 p.2)
      (encPair encUnary encUnary) (encList encBool) := by
  unfold oneHot
  fun_prop

/-- Exactly-one generation is polynomial in the framed scope list, with binary variable names. -/
theorem computableInPolyTime_tableExactlyOne :
    ComputableInPolyTime (exactlyOne (V := ℕ)) (encList encNat) encTable := by
  have hwidth := ComputableInPolyTime.length_list encNat
  have harity := (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.unary_to_binary).comp
    hwidth
  have hrows : ComputableInPolyTime
      (fun scope : List ℕ => (List.range scope.length).map (oneHot scope.length))
      (encList encNat) (encList (encList encBool)) := by
    apply ComputableInPolyTime.mapWithInput (by fun_prop)
    exact computableInPolyTime_tableOneHot.comp
      (show ComputableInPolyTime (fun p : List ℕ × ℕ => (p.1.length, p.2))
        (encPair (encList encNat) encUnary) (encPair encUnary encUnary) by fun_prop)
  unfold exactlyOne
  exact (harity.prod hrows).of_enc_eq fun _ => rfl

/-- Exact full encoded table size, including binary arity, bit framing and row framing. -/
theorem length_encTable {table : Cslib.Logic.PL.CSP.Table} (h : table.wellFormed = true) :
    (encTable table).length = 2 * (encNat table.arity).length + 1 +
      table.rows.length * (6 * table.arity + 1) := by
  have hbits (row : List Bool) : (encList encBool row).length = 3 * row.length := by
    simp [length_encList, Nat.mul_comm]
  have hrows : (encList (encList encBool) table.rows).length =
      table.rows.length * (6 * table.arity + 1) := by
    rw [length_encList]
    calc
      _ = (table.rows.map fun _ => 6 * table.arity + 1).sum := by
        congr 1
        apply List.map_congr_left
        intro row hr
        rw [hbits, wellFormed_eq_true.mp h row hr]
        omega
      _ = _ := by simp [Nat.mul_comm]
  rw [encTable_apply, length_encPair, hrows]

/-- At least two distinct internal coordinates make the full encoded local table no larger,
including its binary arity. This is a local bound, not a whole-solver complexity theorem. -/
theorem length_encTable_contract_le {table : Cslib.Logic.PL.CSP.Table}
    {reference : List Bool} {positions : List ℕ}
    (h : table.canContract reference positions = true) (htwo : 2 ≤ positions.length) :
    (encTable (table.contract reference positions)).length ≤ (encTable table).length := by
  have hg : table.sem reference = true ∧ validPositions reference.length positions = true := by
    simpa only [canContract, Bool.and_eq_true] using h
  have hw := (sem_eq_true.mp hg.1).1
  have ha := arity_contract_lt h htwo
  have hb : (encNat (table.contract reference positions).arity).length ≤
      (encNat table.arity).length := by
    simpa only [encNat_apply, Nat.size_eq_bits_len] using Nat.size_le_size ha.le
  have hr := Nat.mul_le_mul (length_rows_contract_le table reference positions)
    (show 6 * (table.contract reference positions).arity + 1 ≤ 6 * table.arity + 1 by omega)
  rw [length_encTable (wellFormed_contract ..), length_encTable hw]
  omega

/-- Replacing any sublist of old names by that sublist followed by one binary connector name
costs at most the connector's full framed name. Table framing is included twice by the enclosing
constraint encoding. The caller supplies the outside scope and proves its sublist property. -/
theorem length_encConstraint_tableContract_le {table : Cslib.Logic.PL.CSP.Table}
    {reference : List Bool} {positions scope outsideScope : List ℕ} (connector : ℕ)
    (h : table.canContract reference positions = true) (htwo : 2 ≤ positions.length)
    (hscope : List.Sublist outsideScope scope) :
    (encConstraint encTable encNat
      (table.contract reference positions, outsideScope ++ [connector])).length ≤
      (encConstraint encTable encNat (table, scope)).length +
        2 * (encNat connector).length + 1 := by
  have ht := length_encTable_contract_le h htwo
  have hs := length_encList_sublist encNat hscope
  simp only [encConstraint, length_encPair, encList_append, List.length_append,
    encList_cons, encList_nil, List.append_nil, length_frame] at *
  omega

/-- Exactly-one's full encoded size is quadratic in the connector count, with binary arity. -/
theorem length_encTable_exactlyOne {V : Type*} (scope : List V) :
    (encTable (exactlyOne scope)).length = 2 * (encNat scope.length).length + 1 +
      scope.length * (6 * scope.length + 1) := by
  rw [length_encTable (wellFormed_exactlyOne scope), length_rows_exactlyOne]
  rfl

/-- Actual binary constraint size includes every supplied variable name, in addition to the
quadratic exactly-one table. -/
theorem length_encConstraint_exactlyOne (scope : List ℕ) :
    (encConstraint encTable encNat (exactlyOne scope, scope)).length =
      4 * (encNat scope.length).length + 3 +
        2 * scope.length * (6 * scope.length + 1) + (encList encNat scope).length := by
  rw [length_encPair, length_encTable_exactlyOne]
  dsimp only [Prod.snd]
  ring

/-- A concrete quadratic bound in the actual framed binary scope encoding. This resource pays
for both the quadratic table and the binary names; binary arity alone would not suffice. -/
theorem length_encConstraint_exactlyOne_le (scope : List ℕ) :
    (encConstraint encTable encNat (exactlyOne scope, scope)).length ≤
      21 * ((encList encNat scope).length + 1) ^ 2 := by
  have hlen := SizedListEncoding.length_le (encA := encNat) (encL := encList encNat) scope
  have hbits : (encNat scope.length).length ≤ scope.length := by
    simpa only [encNat_apply, Nat.size_eq_bits_len] using Nat.size_le_self scope.length
  rw [length_encConstraint_exactlyOne]
  nlinarith

end Cslib.Complexity.CSP
