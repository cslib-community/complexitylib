/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.GenericRAM.Native.StreamingEmitBounds
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.StreamingFilter
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Containers
import all CslibFrontier.Computability.GenericRAM.Native.Combinators
import all CslibFrontier.Computability.GenericRAM.Native.StreamingEmit
import all CslibFrontier.Computability.GenericRAM.Native.StreamingEmitBounds
import all CslibFrontier.Computability.GenericRAM.Native.StreamingFoldBounds
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.StreamFold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Data.List.Induction

/-!
# Streaming adjacent payload pairs

Read binary key/payload records once, remembering only the first payload of each
pair. Emit its pair with the next payload and clear the state. Keys are ignored;
an unmatched final record is discarded. Sorting and key alignment are separate
obligations for a caller. No unconsumed input or growing output is a callback state.

## Main results

* `run_flatMap`: exact ordered output on consecutive two-record blocks.
* `run_computable`: linear record count times a polynomial in maximum record width,
  including materialized input/output and every prefix/callback workspace.
-/

public section
namespace Turing.MultiTapeTM.AdjacentPairs
open Cslib.GenericRAM

/-- Pair payloads of consecutive records, dropping a possible unmatched final record. -/
def run : List (ℕ × ℕ) → List (ℕ × ℕ)
  | a :: b :: rows => (a.2, b.2) :: run rows
  | _ => []

private def next (s : Option ℕ) (row : ℕ × ℕ) : Option ℕ :=
  if s.isSome then none else some row.2

private def emit (s : Option ℕ) (row : ℕ × ℕ) : List (ℕ × ℕ) :=
  s.toList.map fun a => (a, row.2)

private theorem emitted (rows : List (ℕ × ℕ)) :
    NativeCertificate.emitFold next emit none rows = run rows := by
  induction rows using List.twoStepInduction with
  | nil => rfl
  | singleton a => rfl
  | cons_cons a b rows ih _ =>
    simpa only [NativeCertificate.emitFold, next, emit, Option.toList_none,
      Option.toList_some, List.map_nil, List.map_cons, List.nil_append,
      Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte, List.cons_append,
      run] using congrArg ((a.2, b.2) :: ·) ih

theorem run_flatMap {α : Type} (rows : List α) (left right : α → ℕ × ℕ) :
    run (rows.flatMap fun a => [left a, right a]) =
      rows.map (fun a => ((left a).2, (right a).2)) := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simpa only [List.flatMap_cons, List.cons_append, List.nil_append,
      run, List.map_cons] using congrArg (((left row).2, (right row).2) :: ·) ih

/-- Pairing never produces more records than it reads, including odd and empty inputs. -/
theorem length_le (rows : List (ℕ × ℕ)) : (run rows).length ≤ rows.length := by
  induction rows using List.twoStepInduction with
  | nil => rfl
  | singleton a => simp [run]
  | cons_cons a b rows ih _ => simp only [run, List.length_cons]; omega

/-- The two retained payloads fit within the original record-width budget. -/
theorem record_bound (rows : List (ℕ × ℕ)) (B : ℕ) :
    (∀ r ∈ rows, (encPair encNat encNat r).length ≤ B) →
      ∀ p ∈ run rows, (encPair encNat encNat p).length ≤ 3*B+1 := by
  induction rows using List.twoStepInduction with
  | nil => simp [run]
  | singleton a => simp [run]
  | cons_cons a b rows ih _ =>
    intro bound p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · have ha := bound a (by simp)
      have hb := bound b (by simp)
      simp only [length_encPair] at ha hb ⊢
      omega
    · exact ih (fun r hr => bound r (by simp [hr])) p hp

private theorem wire_le (rows : List (ℕ × ℕ)) :
    (encNatPairList (run rows)).length ≤ 2 * (encNatPairList rows).length := by
  induction rows using List.twoStepInduction with
  | nil => simp [run]
  | singleton a => simp [run]
  | cons_cons a b rows ih _ =>
    change (encList (encPair encNat encNat) (run rows)).length ≤
      2 * (encList (encPair encNat encNat) rows).length at ih
    simp only [run, encList_cons, List.length_append, length_frame, length_encPair] at *
    omega

private theorem next_polyTime : ComputableInPolyTime (fun q => next q.1 q.2)
    (encPair (encOption encNat) (encPair encNat encNat)) (encOption encNat) := by
  apply ComputableInPolyTime.of_tidy
  unfold next
  fun_prop

private theorem emit_polyTime : ComputableInPolyTime (fun q => emit q.1 q.2)
    (encPair (encOption encNat) (encPair encNat encNat)) encNatPairList := by
  have state := ComputableTidilyInPolyTime.fst (encOption encNat) (encPair encNat encNat)
  have value := (ComputableTidilyInPolyTime.snd (encOption encNat) (encPair encNat encNat)).snd'
  have pair := (state.optionGetDWithInput (ComputableTidilyInPolyTime.const 0)).prod value
  have single : ComputableTidilyInPolyTime (fun r : ℕ × ℕ => [r])
      (encPair encNat encNat) encNatPairList := .of_linear (.of_frame (fun _ => by simp))
  have h := state.optionIsSome.cond (single.comp pair) (ComputableTidilyInPolyTime.const [])
  exact (ComputableInPolyTime.of_tidy h).of_enc_eq (fun ⟨s, row⟩ => by cases s <;> rfl)

private theorem state_bound (rows : List (ℕ × ℕ)) (j : ℕ) (hj : j ≤ rows.length) :
    (encOption encNat (streamState none (fun q => next q.1 q.2) rows j)).length ≤
      streamRecordLength (encPair encNat encNat) rows + 1 := by
  let B := streamRecordLength (encPair encNat encNat) rows
  have inv := List.foldl_take_invariant rows next none
    (fun _ s => (encOption encNat s).length ≤ B+1) (by simp)
    (fun i hi s _ => by
      have hr := le_listMax (f := fun r => (encPair encNat encNat r).length) (List.getElem_mem hi)
      change (encPair encNat encNat rows[i]).length ≤ B at hr
      simp only [length_encPair] at hr
      cases s with
      | none =>
        simp only [next, Option.isSome_none, Bool.false_eq_true, ite_false, encOption_some,
          List.length_cons]
        change (encNat rows[i].2).length+1 ≤ B+1
        omega
      | some v => simp [next])
  exact inv j hj

/-- One uniform emitter with derived width-dependent callback and prefix-state bounds. -/
theorem run_computable : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ComputableInO run encNatPairList encNatPairList
      (fun rows => (rows.length+1)*P (streamRecordLength (encPair encNat encNat) rows+1))
      (fun rows => (rows.length+1)*P (streamRecordLength (encPair encNat encNat) rows+1)) := by
  let nm := NativeCertificate.ofPolyTime next_polyTime
  let em := NativeCertificate.ofPolyTime emit_polyTime
  obtain ⟨N, hn, mn, hN⟩ := exists_mono_poly
    ((NativeCertificate.ofPolyTime_isPolynomial next_polyTime).1.add
      (NativeCertificate.ofPolyTime_isPolynomial next_polyTime).2)
  obtain ⟨E, he, me, hE⟩ := exists_mono_poly
    ((NativeCertificate.ofPolyTime_isPolynomial emit_polyTime).1.add
      (NativeCertificate.ofPolyTime_isPolynomial emit_polyTime).2)
  let machine := NativeCertificate.emitFoldCertificate (encOption encNat)
    (encPair encNat encNat) (encPair encNat encNat) next emit nm em
  obtain ⟨K, bound⟩ := NativeCertificate.emitFoldCertificate_bounds (encOption encNat)
    (encPair encNat encNat) (encPair encNat encNat) next emit nm em
  let original : NativeCertificate (id : List (ℕ × ℕ) → _) encNatPairList encNatPairList :=
    .linear (.of_eq (fun _ => rfl))
  let prepare := (NativeCertificate.const (em := encOption encNat) none).prod original
  have actual := (machine.comp prepare).computes.of_enc_eq (g := run) (encC := encNatPairList)
    (fun rows => by simp only [Function.comp_def, id_eq, emitted])
  let Q := fun B => N (3*B+3)+E (3*B+3)+20*B+20
  let P := fun B => (10*K+10)*Q B
  have hp : Cslib.PolynomiallyBounded P := by dsimp only [P, Q]; fun_prop
  have mp : Monotone P := by
    intro a b hab
    have := mn (by omega : 3*a+3 ≤ 3*b+3)
    have := me (by omega : 3*a+3 ≤ 3*b+3)
    apply Nat.mul_le_mul_left
    dsimp only [Q]
    omega
  have budgets (rows : List (ℕ × ℕ)) :
      machine.time (none, rows) ≤ K*((rows.length+1)*Q
        (streamRecordLength (encPair encNat encNat) rows+1)) ∧
      machine.space (none, rows) ≤ K*((rows.length+1)*Q
        (streamRecordLength (encPair encNat encNat) rows+1)) := by
    let B := streamRecordLength (encPair encNat encNat) rows+1
    have state : NativeCertificate.foldStateWidth (encOption encNat)
        (fun (_ : Unit) => next) ((), (none, rows)) ≤ B := by
      apply Finset.sup_le
      intro j hj
      exact state_bound rows j (by have := Finset.mem_range.mp hj; omega)
    have cb (j : ℕ) (hj : j < rows.length) :
        nm.time (streamState none (fun q => next q.1 q.2) rows j, rows[j])+
        nm.space (streamState none (fun q => next q.1 q.2) rows j, rows[j])+
        em.time (streamState none (fun q => next q.1 q.2) rows j, rows[j])+
        em.space (streamState none (fun q => next q.1 q.2) rows j, rows[j]) ≤
          N (3*B+3)+E (3*B+3) := by
      have hs := state_bound rows j hj.le
      have hr := le_listMax (f := fun r => (encPair encNat encNat r).length) (List.getElem_mem hj)
      change (encPair encNat encNat rows[j]).length ≤
        streamRecordLength (encPair encNat encNat) rows at hr
      have hw : (encPair (encOption encNat) (encPair encNat encNat)
          (streamState none (fun q => next q.1 q.2) rows j, rows[j])).length ≤ 3*B+3 := by
        rw [length_encPair]
        dsimp only [B]
        omega
      have hnm := (hN _).trans (mn hw)
      have hem := (hE _).trans (me hw)
      change nm.time _ + nm.space _ ≤ _ at hnm
      change em.time _ + em.space _ ≤ _ at hem
      omega
    have input := length_encList_le (encPair encNat encNat) rows
      (fun r hr => le_listMax (f := fun r => (encPair encNat encNat r).length) hr)
    change (encList (encPair encNat encNat) rows).length ≤
      rows.length*(2*streamRecordLength (encPair encNat encNat) rows+1) at input
    have output := wire_le rows
    change (encList (encPair encNat encNat) (run rows)).length ≤
      2*(encList (encPair encNat encNat) rows).length at output
    have sum : (∑ j ∈ Finset.range rows.length, if h : j < rows.length then
        nm.time (streamState none (fun q => next q.1 q.2) rows j, rows[j])+
        em.time (streamState none (fun q => next q.1 q.2) rows j, rows[j])+
        (encPair encNat encNat rows[j]).length else 0) ≤
          rows.length*(N (3*B+3)+E (3*B+3)+B) := by
      have hsum := Finset.sum_le_sum (s := Finset.range rows.length)
        (f := fun j => if h : j < rows.length then
          nm.time (streamState none (fun q => next q.1 q.2) rows j, rows[j])+
          em.time (streamState none (fun q => next q.1 q.2) rows j, rows[j])+
          (encPair encNat encNat rows[j]).length else 0)
        (g := fun _ => N (3*B+3)+E (3*B+3)+B) (fun j hj => by
          rw [dite_eq_left (Finset.mem_range.mp hj)]
          have hj' : j < rows.length := Finset.mem_range.mp hj
          have hc := cb j hj'
          have hr := le_listMax (f := fun r => (encPair encNat encNat r).length)
            (List.getElem_mem (Finset.mem_range.mp hj))
          change (encPair encNat encNat rows[j]).length ≤
            streamRecordLength (encPair encNat encNat) rows at hr
          dsimp only [B] at *
          omega)
      simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id] using hsum
    have maximum : (Finset.range rows.length).sup (fun j => if h : j < rows.length then
        nm.space (streamState none (fun q => next q.1 q.2) rows j, rows[j])+
        em.space (streamState none (fun q => next q.1 q.2) rows j, rows[j]) else 0) ≤
          N (3*B+3)+E (3*B+3) := by
      apply Finset.sup_le
      intro j hj
      rw [dite_eq_left (Finset.mem_range.mp hj)]
      have := cb j (Finset.mem_range.mp hj)
      omega
    have bt : NativeCertificate.emitTimeBudget (encOption encNat) (encPair encNat encNat)
        (encPair encNat encNat) next emit nm em (none, rows) ≤ (rows.length+1)*Q B := by
      dsimp only [NativeCertificate.emitTimeBudget, Q]
      simp only [length_encPair, encOption_none, List.length_nil]
      have stateCopies := Nat.mul_le_mul_left (rows.length+1) state
      simp only [length_encPair] at sum
      dsimp only [B] at *
      nlinarith only [input, state, sum, stateCopies]
    have bs : NativeCertificate.emitSpaceBudget (encOption encNat) (encPair encNat encNat)
        (encPair encNat encNat) next emit nm em (none, rows) ≤ (rows.length+1)*Q B := by
      dsimp only [NativeCertificate.emitSpaceBudget, Q]
      rw [emitted]
      simp only [length_encPair, encOption_none, List.length_nil]
      have nonnegative := Nat.zero_le (rows.length*(N (3*B+3)+E (3*B+3)))
      dsimp only [B] at *
      nlinarith only [input, state, maximum, output, nonnegative]
    exact ⟨(bound (none, rows)).1.trans (Nat.mul_le_mul_left K bt),
      (bound (none, rows)).2.trans (Nat.mul_le_mul_left K bs)⟩
  refine ⟨P, hp, mp, actual.mono_le (fun rows => ?_) (fun rows => ?_)⟩
  · change (encNatPairList rows).length+(encNatPairList rows).length+machine.time (none, rows) ≤ _
    have h := (budgets rows).1
    have input := length_encList_le (encPair encNat encNat) rows
      (fun r hr => le_listMax (f := fun r => (encPair encNat encNat r).length) hr)
    change (encNatPairList rows).length ≤
      rows.length*(2*streamRecordLength (encPair encNat encNat) rows+1) at input
    dsimp only [P, Q] at *
    nlinarith
  · change (encNatPairList rows).length+(encNatPairList rows).length+machine.space (none, rows) ≤ _
    have h := (budgets rows).2
    have input := length_encList_le (encPair encNat encNat) rows
      (fun r hr => le_listMax (f := fun r => (encPair encNat encNat r).length) hr)
    change (encNatPairList rows).length ≤
      rows.length*(2*streamRecordLength (encPair encNat encNat) rows+1) at input
    dsimp only [P, Q] at *
    nlinarith

end Turing.MultiTapeTM.AdjacentPairs
