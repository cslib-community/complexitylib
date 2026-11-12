/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CSP.Edge.Solver.Driver
public import CslibFrontier.Computability.PolyTime.CSP.Edge.Solver.Spec
import CslibFrontier.Computability.PolyTime.CSP.Edge.Solver.Initialization
import CslibFrontier.Computability.PolyTime.CSP.Edge.Solver.GuardPolyTime
import CslibFrontier.Computability.PolyTime.CSP.Vars
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.EraseDupsBy
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length

/-!
# Native polynomial-time complete optimization

One checked improvement is followed by an outer list-funded optimization loop. The first
optimal status freezes that loop. Native certificates cover every raw complete framed CSP;
model and row checks are all internal, including malformed arities and sparse binary names.
The finite representation and resource bookkeeping are original.
-/

public section

namespace Cslib.Complexity.CSP.EdgeSolver.Program

open Cslib.Logic.PL Cslib.Logic.PL.CSP Turing.MultiTapeTM

/-- Current original occurrence bits are framed, followed by the stopped flag. -/
abbrev encOptimizeState := encPair (encList encBool) encBool

private def checkedStep (F : CSP Table ℕ) (state : OptimizeState) : OptimizeState :=
  if state.2 then state else
    (safeImprove ⟨F, state.1⟩).elim (state.1, true) fun bits => (bits, false)

private theorem poly_checkedStep : ComputableInPolyTime
    (fun p : CSP Table ℕ × OptimizeState => checkedStep p.1 p.2)
    (encPair (encCSP encTable encNat) encOptimizeState) encOptimizeState := by
  unfold checkedStep
  have hm := EdgeForest.encInput_mk_deg.computableInPolyTime
  have hi := computableInPolyTime_safeImprove.comp
    (show ComputableInPolyTime
      (fun p : CSP Table ℕ × OptimizeState => EdgeForest.Input.mk p.1 p.2.1)
      (encPair (encCSP encTable encNat) encOptimizeState) EdgeForest.encInput from by fun_prop)
  fun_prop

private theorem checkedStep_growth (F : CSP Table ℕ) (state : OptimizeState) :
    (encOptimizeState (checkedStep F state)).length ≤ (encOptimizeState state).length +
      (6 * (CSP.occurrences F).length + 2) := by
  rcases state with ⟨bits, stopped⟩
  cases stopped with
  | true => simp [checkedStep]
  | false =>
    cases hi : safeImprove ⟨F, bits⟩ with
    | none =>
      simp [checkedStep, hi, encOptimizeState, encBool_apply]
    | some out =>
      have hw := safeImprove_width ⟨F, bits⟩ hi
      have ho : (CSP.occurrences F).length = (incidenceList F).length := by
        simp [occurrences_eq_map_incidenceList]
      simp only [checkedStep, Bool.false_eq_true, ↓reduceIte, hi, Option.elim_some]
      simp only [encOptimizeState, length_encPair]
      have hlen : (encList encBool out).length = 3 * out.length := by
        simp [length_encList, encBool_apply, Nat.mul_comm]
      simp only [hlen, encBool_apply, List.length_cons, List.length_nil]
      dsimp only at hw
      omega

private def ValidState (F : CSP Table ℕ) (state : OptimizeState) : Prop :=
  ∃ f : OccurrenceLabeling F Bool, ValidLabeling Table.sem f ∧ state.1 = buffer f

private theorem checkedStep_eq (F : CSP Table ℕ) (state : OptimizeState)
    (hF : EdgeInstance F) (hM : EdgeInstance.EvenConstraints Table.sem F)
    (hvalid : ValidState F state) : checkedStep F state = optimizeStep F state := by
  obtain ⟨f, hf, hbits⟩ := hvalid
  rcases state with ⟨bits, stopped⟩
  dsimp only at hbits
  subst bits
  cases stopped with
  | true => rfl
  | false =>
    simp only [checkedStep, optimizeStep, Bool.false_eq_true, ↓reduceIte,
      safeImprove_buffer F f hF hf hM]
    cases improve ⟨F, buffer f⟩ <;> rfl

private theorem optimizeStep_valid (F : CSP Table ℕ) (state : OptimizeState)
    (hF : EdgeInstance F) (hM : EdgeInstance.EvenConstraints Table.sem F)
    (hvalid : ValidState F state) : ValidState F (optimizeStep F state) := by
  obtain ⟨f, hf, hbits⟩ := hvalid
  rcases state with ⟨bits, stopped⟩
  dsimp only at hbits
  subst bits
  cases stopped with
  | true => exact ⟨f, hf, rfl⟩
  | false =>
    have hs := Solver.improve_spec (F.contractionMeasure + 1) F f (by omega) hF hf hM
    cases he : Solver.improve (F.contractionMeasure + 1) F f with
    | none =>
      exact ⟨f, hf, by simp only [optimizeStep, Bool.false_eq_true, ↓reduceIte,
        improve_eq_source F f hF hf hM, he, Option.map_none]⟩
    | some g =>
      rw [he] at hs
      exact ⟨g, hs.1, by simp only [optimizeStep, Bool.false_eq_true, ↓reduceIte,
        improve_eq_source F f hF hf hM, he, Option.map_some]⟩

private theorem checked_iterate_eq (F : CSP Table ℕ) (state : OptimizeState)
    (hF : EdgeInstance F) (hM : EdgeInstance.EvenConstraints Table.sem F)
    (hvalid : ValidState F state) (n : ℕ) :
    (checkedStep F)^[n] state = (optimizeStep F)^[n] state := by
  have hv (n : ℕ) : ValidState F ((optimizeStep F)^[n] state) := by
    induction n with
    | zero => exact hvalid
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact optimizeStep_valid F _ hF hM ih
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    exact checkedStep_eq F _ hF hM (hv n)
/-- The complete optimizer is ordinary native polynomial-time in the full framed original
input, including every raw malformed explicit table and every binary label bit. -/
theorem computableInPolyTime_optimize : ComputableInPolyTime optimize
    (encCSP encTable encNat) (encOption (encList encBool)) := by
  have hv := computableInPolyTime_vars encTable encNat
  have huniq : ComputableInPolyTime (fun F : CSP Table ℕ => F.vars.eraseDups)
      (encCSP encTable encNat) (encList encNat) := by
    change ComputableInPolyTime (fun F : CSP Table ℕ => F.vars.eraseDupsBy (fun a b => a == b))
      (encCSP encTable encNat) (encList encNat)
    exact ComputableInPolyTime.eraseDupsByWithInput hv (by fun_prop)
  have hcount : ComputableInPolyTime
      (fun F : CSP Table ℕ => F.vars.eraseDups.length + 1) (encCSP encTable encNat) encUnary := by
    fun_prop
  have hinit : ComputableInPolyTime
      (fun F : CSP Table ℕ => ((initialRows F).flatten, false))
      (encCSP encTable encNat) encOptimizeState := by
    have hi := computableInPolyTime_initialBuffer
    fun_prop
  have hg : ComputableInPolyTime
      (fun F : CSP Table ℕ => 6 * (CSP.occurrences F).length + 2)
      (encCSP encTable encNat) encUnary := by
    have hr := EdgeAugmenting.poly_records
    fun_prop
  have hloop : ComputableInPolyTime
      (fun F : CSP Table ℕ => (checkedStep F)^[F.vars.eraseDups.length + 1]
        ((initialRows F).flatten, false)) (encCSP encTable encNat) encOptimizeState := by
    apply ComputableInPolyTime.of_tidy
    apply ComputableTidilyInPolyTime.iterateWithInput_of_bounded_growth hcount.tidy hinit.tidy
      poly_checkedStep.tidy
    refine ⟨?_, checkedStep_growth⟩
    simpa only [encUnary_apply, List.length_replicate] using hg.polyBounded_length
  have hguard := computableInPolyTime_checkModel
  have hresult := hguard.ite'
    ((ComputableInPolyTime.optionSome (encList encBool)).comp hloop.fst')
    (ComputableInPolyTime.const none)
  apply hresult.of_enc_eq
  intro F
  by_cases hm : checkModel F = true
  · have model := checkModel_sound F hm
    have hi := initial_buffer F hm
    have he := checked_iterate_eq F (buffer (initial F), false) model.1 model.2
      ⟨initial F, initial_valid F hm, rfl⟩ (F.vars.eraseDups.length + 1)
    simp only [optimize, hm, ↓reduceIte, Function.comp_def]
    rw [← hi, he]
  · simp [optimize, hm]

attribute [local fun_prop] EdgeAugmenting.poly_inconsistentWith

/-- The native decision routine supplies every model check internally and charges the full
complete framed CSP, with no input-validity premise in the runtime certificate. -/
theorem computableInPolyTime_decideSAT : ComputableInPolyTime decideSAT
    (encCSP encTable encNat) encBool := by
  have ho := computableInPolyTime_optimize
  have hv := computableInPolyTime_vars encTable encNat
  have hbody : ComputableInPolyTime
      (fun p : CSP Table ℕ × List Bool => !p.1.vars.any (EdgeAugmenting.inconsistent p.1 p.2))
      (encPair (encCSP encTable encNat) (encList encBool)) encBool := by fun_prop
  have h := ComputableInPolyTime.optionElimWithInput
    (body := fun F bits => !F.vars.any (EdgeAugmenting.inconsistent F bits))
    ho (ComputableInPolyTime.const false) hbody
  apply h.of_enc_eq
  intro F
  unfold decideSAT
  cases optimize F <;> rfl

end Cslib.Complexity.CSP.EdgeSolver.Program
