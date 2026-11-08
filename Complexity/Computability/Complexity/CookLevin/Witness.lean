/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.CookLevin.RunFeatures
public import Complexity.Computability.Complexity.CookLevin.Encoding
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Tape
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Window

/-!
# Polynomial time for the variables listed along a run

For a fixed machine, the variables `Cslib.Complexity.CookLevin.trueVars tm u w T` listed along its
run are computable in polynomial time from `u`, `w` and the unary bound `T`
(`Cslib.Complexity.CookLevin.computableInPolyTime_trueVars`). Each time step reads the tracked
storage (`Turing.MultiTapeTM.computableInPolyTime_trackedRun`) and builds its features with the
constructor certificates of `Complexity.Computability.Complexity.CookLevin.Encoding`; the features
with finitely many values are selected by a finite case analysis.

## Main results

* `Cslib.Complexity.CookLevin.computableInPolyTime_trueFeatures`: the features listed for tracked
  storage.
* `Cslib.Complexity.CookLevin.computableInPolyTime_trueVars`: the variables listed for a run.
-/

public section

namespace Cslib.Complexity.CookLevin

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.Feature Cslib.Logic.PL
  Cslib.Turing ComputableInPolyTime

variable {k : ℕ} {State : Type} [Fintype State]

/-- The view of a written output, by cases on its first two symbols. -/
private theorem ofList_eq_ite (l : List Bool) :
    OutView.ofList l = if l.length = 0 then .empty
      else if l.length = 1 then .one (l.headD false) else .many := by
  rcases l with _ | ⟨b, _ | ⟨b', l⟩⟩ <;> simp [OutView.ofList]

private theorem computableInPolyTime_ofList :
    ComputableInPolyTime OutView.ofList encBits (encFinite OutView) := by
  simp only [funext ofList_eq_ite]
  have hone : ComputableInPolyTime (fun l : List Bool => OutView.one (l.headD false))
      encBits (encFinite OutView) :=
    (of_finite OutView.one).comp (ComputableInPolyTime.headD (encA := encBool) false)
  fun_prop

/-- Reading a tape at an integer displacement, by cases on its sign. -/
private theorem read_eq_ite (tape : BiTape Bool) (d : ℤ) :
    tape.read d = if 0 < d then tape.right.toList.getD (d.toNat - 1) none
      else if d < 0 then tape.left.toList.getD (d.natAbs - 1) none else tape.head := by
  have hjoin (l : List (Option Bool)) (n : ℕ) : l.getD n none = l[n]?.join := by
    rw [List.getD_eq_getElem?_getD]
    cases l[n]? <;> rfl
  rcases d with (_ | n) | n
  · simp [BiTape.read]
  · simp only [BiTape.read, hjoin, ← StackTape.read_eq_getElem?]
    simp
  · simp only [BiTape.read, hjoin, ← StackTape.read_eq_getElem?]
    simp [Int.negSucc_lt_zero]

private theorem computableInPolyTime_read :
    ComputableInPolyTime (fun p : BiTape Bool × ℤ => p.1.read p.2)
      (encPair (encBiTape encBool) encIntUnary) (encOption encBool) := by
  simp only [read_eq_ite]
  have hright := (stackTape_toList encBool).comp ((biTape_right encBool).comp
    (fst (encBiTape encBool) encIntUnary))
  have hleft := (stackTape_toList encBool).comp ((biTape_left encBool).comp
    (fst (encBiTape encBool) encIntUnary))
  have hhead := (biTape_head encBool).comp (fst (encBiTape encBool) encIntUnary)
  have hd := snd (encBiTape encBool) encIntUnary
  have hpos := int_pos.comp hd
  have hneg := int_neg.comp hd
  have hr := listGetDWithInput hright (unary_sub.comp ((int_toNat.comp hd).prod (const 1))) none
  have hl := listGetDWithInput hleft (unary_sub.comp ((int_natAbs.comp hd).prod (const 1))) none
  simpa [Function.comp_def] using hpos.ite hr (hneg.ite hl hhead)

/-- **The listed features are polynomial-time** in the unary window bound and the tracked
storage. -/
theorem computableInPolyTime_trueFeatures :
    ComputableInPolyTime
      (fun p : ℕ × (FiniteCfg k Bool State × (Fin k → ℤ)) => trueFeatures p.1 p.2)
      (encPair encUnary (encTrackedCfg (k := k) (State := State))) (encList encFeature) := by
  unfold trueFeatures
  have hc := snd encUnary (encTrackedCfg (k := k) (State := State))
  have hcfg : ComputableInPolyTime (fun p : ℕ × (FiniteCfg k Bool State × (Fin k → ℤ)) => p.2.1)
      (encPair encUnary encTrackedCfg) encFiniteCfg := (fst _ _).comp hc
  have hpos : ComputableInPolyTime (fun p : ℕ × (FiniteCfg k Bool State × (Fin k → ℤ)) => p.2.2)
      (encPair encUnary encTrackedCfg) (encPi encIntUnary) := (snd _ _).comp hc
  have hkey := (finiteCfg_state.comp hcfg).prod ((finiteCfg_inputSymbol.comp hcfg).prod
    ((finiteCfg_workTapeSymbols.comp hcfg).prod
      (computableInPolyTime_ofList.comp (finiteCfg_output.comp hcfg))))
  have hfin := (of_finite (encIn := encPair (encFinite (Option State))
    (encPair (encFinEnum (Option Bool)) (encPair (encFinEnum (Fin k → Option Bool))
      (encFinite OutView)))) (encOut := encList encFeature)
    (finiteFeatures (k := k) (State := State))).comp hkey
  refine listAppend' hfin (cons' (computableInPolyTime_inPos.comp
    (finiteCfg_inputPos.comp hcfg)) (flatMapConst _ fun i _ => cons'
      ((computableInPolyTime_head i).comp ((pi_apply encIntUnary i).comp hpos)) ?_))
  -- The cells of tape `i` in the window, each read relative to the head.
  have hz := snd (encPair encUnary (encTrackedCfg (k := k) (State := State))) encIntUnary
  have hx := fst (encPair encUnary (encTrackedCfg (k := k) (State := State))) encIntUnary
  have hsym := computableInPolyTime_read.comp
    (((pi_apply (encBiTape encBool) i).comp (finiteCfg_workTapes.comp (hcfg.comp hx))).prod
      (int_sub.comp (hz.prod ((pi_apply encIntUnary i).comp (hpos.comp hx)))))
  refine mapWithInput (computableInPolyTime_windowList.comp (fst _ _)) ?_
  exact finite_cases (tagEncoding := encOption encBool) hsym fun s =>
    (computableInPolyTime_cell i s).comp hz

/-- **The listed variables are polynomial-time** in the input prefix `u`, the certificate `w`
and the unary bound `T`, for a fixed machine. -/
theorem computableInPolyTime_trueVars (tm : MultiTapeTM k Bool State) :
    ComputableInPolyTime (fun x : (List Bool × List Bool) × ℕ => trueVars tm x.1.1 x.1.2 x.2)
      (encPair (encPair encBits encBits) encUnary) (encList encVar) := by
  unfold trueVars
  have hrun : ComputableInPolyTime
      (fun p : ((List Bool × List Bool) × ℕ) × ℕ => trackedRun tm (p.1.1.1 ++ p.1.1.2, p.2))
      (encPair (encPair (encPair encBits encBits) encUnary) encUnary) encTrackedCfg :=
    (computableInPolyTime_trackedRun tm).comp (by fun_prop)
  have hfeatures := computableInPolyTime_trueFeatures.comp
    (((snd (encPair encBits encBits) encUnary).comp (fst _ encUnary)).prod hrun)
  have hholds : ComputableInPolyTime
      (fun p : (((List Bool × List Bool) × ℕ) × ℕ) × Feature k State => Var.holds p.1.2 p.2)
      (encPair (encPair (encPair (encPair encBits encBits) encUnary) encUnary) encFeature)
      encVar :=
    computableInPolyTime_holds.comp (((snd _ _).comp (fst _ _)).prod (snd _ _))
  refine listAppend' (flatMapWithInput (by fun_prop) (mapWithInput hfeatures hholds)) ?_
  fun_prop

end Cslib.Complexity.CookLevin
