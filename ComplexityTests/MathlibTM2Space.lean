/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Computability.Complexity.Classes.Space.TM2

/-! Regression checks for the Mathlib TM2 polynomial-space bridge. Source certificates in this
file supply termination, without supplying polynomial runtime certificates. -/

namespace ComplexityTests.MathlibTM2Space

open Computability Turing Turing.MultiTapeTM

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin

private abbrev prependMachine : FinTM2 :=
  { idComputer Bool with m := fun _ => .push () (fun _ => false) .halt }

private instance : ∀ k, Finite (prependMachine.Γ k) := fun _ => inferInstanceAs (Finite Bool)

private noncomputable abbrev prependComputer :
    TM2Computable id id (fun w : List Bool => false :: w) where
  tm := prependMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  outputsFun _ := ⟨1, rfl⟩

private theorem prepend_bound (w : List Bool) (i : ℕ) (k : Unit) :
    (((TM2.stepTotal prependMachine.m)^[i] (initList prependMachine w)).stk k).length ≤
      w.length + 1 := by
  cases k
  cases i with
  | zero => change w.length ≤ w.length + 1; omega
  | succ i =>
    change (((TM2.stepTotal prependMachine.m)^[i]
      (haltList prependMachine (false :: w))).stk ()).length ≤ w.length + 1
    have hfixed := Function.iterate_fixed (show TM2.stepTotal prependMachine.m
      (haltList prependMachine (false :: w)) = haltList prependMachine (false :: w) from rfl) i
    exact (congrArg (fun cfg : prependMachine.Cfg => (cfg.stk ()).length) hfixed).le.trans
      (by change (false :: w).length ≤ w.length + 1; simp)

-- The endpoint starts from termination and a source-space bound, with no runtime argument; and
-- `TM2.run_polySpace` exercises an explicit exponential binary clock.
example : ComputableInPolySpace (fun w : List Bool => false :: w)
    (encList (encFinEnum Bool)) (encList (encFinEnum Bool)) ∧
    ComputableInPolySpace
      (fun w : List Bool => (TM2.stepTotal prependMachine.m)^[2 ^ (w.length + 1)]
        (initList prependMachine w)) (encList (encFinEnum Bool)) TM2.encCfg := by
  refine ⟨prependComputer.computableInPolySpace_encList Function.injective_id Function.injective_id
    (space := fun w => w.length + 1) (PolyBounded.self.add (.const 1)) ?_, ?_⟩
  · intro w i k
    exact (prepend_bound (List.map prependComputer.inputAlphabet.symm w) i k).trans
      (Nat.add_le_add_right (List.length_map prependComputer.inputAlphabet.symm).le 1)
  · have hlength := ComputableInPolyTime.length_list (encFinEnum Bool)
    have hexponent := ComputableInPolyTime.unary_add.comp
      (hlength.prod (ComputableInPolyTime.const 1))
    have hstart : ComputableInPolyTime (fun w => w) (encList (encFinEnum Bool))
        (encList (encFinite (prependMachine.Γ prependMachine.k₀))) :=
      (ComputableInPolyTime.map
        (.of_finite (encOut := encFinite (prependMachine.Γ prependMachine.k₀)) id)).of_enc_eq
        (fun _ => by simp only [List.map_id]; rfl)
    exact TM2.run_polySpace prependMachine hstart
      (ComputableInPolyTime.binary_two_pow.comp hexponent) hexponent.polyBounded
      (fun w i _ k => prepend_bound w i k)

private theorem identity_bound {Γ : Type} [Fintype Γ] (w : List Γ) (i : ℕ) (k : Unit) :
    (((TM2.stepTotal (idComputer Γ).m)^[i] (initList (idComputer Γ) w)).stk k).length ≤
      w.length := by
  cases k
  cases i with
  | zero => exact le_rfl
  | succ i =>
    change (((TM2.stepTotal (idComputer Γ).m)^[i]
      (haltList (idComputer Γ) w)).stk ()).length ≤ w.length
    have hfixed := Function.iterate_fixed (show TM2.stepTotal (idComputer Γ).m
      (haltList (idComputer Γ) w) = haltList (idComputer Γ) w from rfl) i
    exact (congrArg (fun cfg : (idComputer Γ).Cfg => (cfg.stk ()).length) hfixed).le

private noncomputable abbrev identityComputer (Γ : Type) [Fintype Γ] :
    TM2Computable id id (id : List Γ → List Γ) where
  tm := idComputer Γ
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  outputsFun _ := ⟨1, rfl⟩

-- Input and output alphabets are independent, even when only the output alphabet is empty.
private abbrev clearMachine : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ k := match k with
    | false => Bool
    | true => Empty
  Λ := Unit
  main := ()
  σ := Bool
  initialState := false
  m _ := .pop false (fun _ a => a.isSome) (.branch id (.goto (fun _ => ())) .halt)

private def clearCfg (xs : List Bool) (v : Bool) : clearMachine.Cfg where
  l := some ()
  var := v
  stk k := match k with
    | false => xs
    | true => []

private theorem clear_step (xs : List Bool) (v : Bool) :
    clearMachine.step (clearCfg xs v) = some (match xs with
      | [] => haltList clearMachine []
      | _ :: xs => clearCfg xs true) := by
  cases xs <;> apply congrArg some <;>
    change TM2.Cfg.mk _ _ _ = TM2.Cfg.mk _ _ _ <;>
    congr 1 <;> funext k <;> cases k <;> rfl

private noncomputable abbrev clearComputer :
    TM2Computable id id (fun _ : List Bool => ([] : List Empty)) where
  tm := clearMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Empty
  outputsFun xs := by
    have hrun (xs : List Bool) (v : Bool) :
        (fun s : Option clearMachine.Cfg => s.bind clearMachine.step)^[xs.length + 1]
          (some (clearCfg xs v)) = some (haltList clearMachine []) := by
      induction xs generalizing v with
      | nil => exact clear_step [] v
      | cons a xs ih =>
        rw [List.length_cons, Function.iterate_succ_apply]
        simp only [Option.bind_some, clear_step]
        exact ih true
    refine ⟨xs.length + 1, ?_⟩
    have hinit : initList clearMachine xs = clearCfg xs false := by
      change TM2.Cfg.mk _ _ _ = TM2.Cfg.mk _ _ _
      congr 1
      funext k
      cases k <;> rfl
    change (fun s : Option clearMachine.Cfg => s.bind clearMachine.step)^[xs.length + 1]
      (some (initList clearMachine (List.map id xs))) = some (haltList clearMachine [])
    rw [List.map_id, hinit]
    exact hrun xs false

private theorem clear_bound (xs : List Bool) (i : ℕ) : ∀ k,
    (((TM2.stepTotal clearMachine.m)^[i] (initList clearMachine xs)).stk k).length ≤
      xs.length := by
  have hstep (cfg : clearMachine.Cfg) (h : ∀ k, (cfg.stk k).length ≤ xs.length) :
      ∀ k, ((TM2.stepTotal clearMachine.m cfg).stk k).length ≤ xs.length := by
    cases hl : cfg.l with
    | none =>
      have heq : TM2.stepTotal clearMachine.m cfg = cfg := by
        change cfg.l.elim cfg _ = cfg
        rw [hl]
        rfl
      exact fun k => (congrArg (fun c : clearMachine.Cfg => (c.stk k).length) heq).le.trans (h k)
    | some label =>
      have heq : TM2.stepTotal clearMachine.m cfg =
          TM2.stepAux (clearMachine.m label) cfg.var cfg.stk := by
        change cfg.l.elim cfg _ = _
        rw [hl]
        rfl
      rw [heq]
      exact TM2.stepAux_stack_bound (clearMachine.m label) cfg.var cfg.stk xs.length h
  induction i with
  | zero => intro k; cases k <;> simp [initList]
  | succ i ih =>
    have heq := Function.iterate_succ_apply' (TM2.stepTotal clearMachine.m) i
      (initList clearMachine xs)
    exact fun k =>
      (congrArg (fun c : clearMachine.Cfg => (c.stk k).length) heq).le.trans (hstep _ ih k)

-- A concrete Boolean decider crosses the final framed-word-to-Boolean encoding conversion.
private noncomputable abbrev boolComputer :
    TM2Computable encodeBool encodeBool (id : Bool → Bool) :=
  { tm := idComputer Bool
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    outputsFun _ := ⟨1, rfl⟩ }

-- A decider over all Boolean words, including empty and nonempty inputs. It saves the
-- emptiness answer on a separate stack, clears the input, then halts with that one-bit output.
private abbrev emptyMachine : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ _ := Bool
  Λ := Bool
  main := false
  σ := Bool
  initialState := false
  m
    | false => .peek false (fun _ a => a.isNone)
        (.push true id (.load (fun _ => false) (.goto (fun _ => true))))
    | true => .pop false (fun _ a => a.isSome) (.branch id (.goto (fun _ => true)) .halt)

private def emptyCfg (xs : List Bool) (answer v : Bool) : emptyMachine.Cfg where
  l := some true
  var := v
  stk k := if k then [answer] else xs

private theorem empty_init (xs : List Bool) :
    emptyMachine.step (initList emptyMachine xs) =
      some (emptyCfg xs xs.isEmpty false) := by
  cases xs <;> apply congrArg some <;>
    change TM2.Cfg.mk _ _ _ = TM2.Cfg.mk _ _ _ <;>
    congr 1 <;> funext k <;> cases k <;> rfl

private theorem empty_step (xs : List Bool) (answer v : Bool) :
    emptyMachine.step (emptyCfg xs answer v) = some (match xs with
      | [] => haltList emptyMachine [answer]
      | _ :: xs => emptyCfg xs answer true) := by
  cases xs <;> apply congrArg some <;>
    change TM2.Cfg.mk _ _ _ = TM2.Cfg.mk _ _ _ <;>
    congr 1 <;> funext k <;> cases k <;> rfl

private noncomputable abbrev emptyComputer :
    TM2Computable id encodeBool (List.isEmpty : List Bool → Bool) where
  tm := emptyMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  outputsFun xs := by
    have hrun (xs : List Bool) (answer v : Bool) :
        (fun s : Option emptyMachine.Cfg => s.bind emptyMachine.step)^[xs.length + 1]
          (some (emptyCfg xs answer v)) = some (haltList emptyMachine [answer]) := by
      induction xs generalizing v with
      | nil => exact empty_step [] answer v
      | cons a xs ih =>
        rw [List.length_cons, Function.iterate_succ_apply]
        simp only [Option.bind_some, empty_step]
        exact ih true
    refine ⟨xs.length + 2, ?_⟩
    change (fun s : Option emptyMachine.Cfg => s.bind emptyMachine.step)^[xs.length + 2]
      (some (initList emptyMachine (List.map id xs))) =
        some (haltList emptyMachine (List.map id (encodeBool xs.isEmpty)))
    rw [List.map_id, List.map_id, Function.iterate_succ_apply]
    simp only [Option.bind_some, empty_init]
    exact hrun xs xs.isEmpty false

private theorem empty_bound (xs : List Bool) (i : ℕ) (k : Bool) :
    (((TM2.stepTotal emptyMachine.m)^[i] (initList emptyMachine xs)).stk k).length ≤
      xs.length + 1 := by
  have hrun (i : ℕ) (xs : List Bool) (answer v : Bool) :
      (((TM2.stepTotal emptyMachine.m)^[i] (emptyCfg xs answer v)).stk k).length ≤
        xs.length + 1 := by
    induction i generalizing xs v with
    | zero => cases k <;> simp [emptyCfg]
    | succ i ih =>
      have hstep : TM2.stepTotal emptyMachine.m (emptyCfg xs answer v) =
          (match xs with
          | [] => haltList emptyMachine [answer]
          | _ :: xs => emptyCfg xs answer true) := by
        exact (TM2.stepTotal_of_step emptyMachine.m (emptyCfg xs answer v)).trans
          (congrArg (fun cfg : Option emptyMachine.Cfg => cfg.getD (emptyCfg xs answer v))
            (empty_step xs answer v))
      have heq := (Function.iterate_succ_apply (TM2.stepTotal emptyMachine.m) i
        (emptyCfg xs answer v)).trans (congrArg ((TM2.stepTotal emptyMachine.m)^[i]) hstep)
      have hlength := (congrArg (fun cfg : emptyMachine.Cfg => (cfg.stk k).length) heq).le
      cases xs with
      | nil =>
        have hfixed := Function.iterate_fixed (show TM2.stepTotal emptyMachine.m
          (haltList emptyMachine [answer]) = haltList emptyMachine [answer] from rfl) i
        exact hlength.trans
          ((congrArg (fun cfg : emptyMachine.Cfg => (cfg.stk k).length) hfixed).le.trans
            (by cases k <;> simp [haltList]))
      | cons a xs => exact hlength.trans ((ih xs true).trans (by simp))
  cases i with
  | zero => cases k <;> simp [initList]
  | succ i =>
    have hstep : TM2.stepTotal emptyMachine.m (initList emptyMachine xs) =
        emptyCfg xs xs.isEmpty false := by
      exact (TM2.stepTotal_of_step emptyMachine.m (initList emptyMachine xs)).trans
        (congrArg (fun cfg : Option emptyMachine.Cfg => cfg.getD (initList emptyMachine xs))
          (empty_init xs))
    have heq := (Function.iterate_succ_apply (TM2.stepTotal emptyMachine.m) i
      (initList emptyMachine xs)).trans (congrArg ((TM2.stepTotal emptyMachine.m)^[i]) hstep)
    exact (congrArg (fun cfg : emptyMachine.Cfg => (cfg.stk k).length) heq).le.trans
      (hrun i xs xs.isEmpty false)

-- Empty alphabets, independent input/output alphabets, and Boolean deciders in `PSPACE`.
example :
    ComputableInPolySpace (id : List Empty → List Empty)
      (encList (encFinEnum Empty)) (encList (encFinEnum Empty)) ∧
    ComputableInPolySpace (fun _ : List Bool => ([] : List Empty))
      (encList (encFinEnum Bool)) (encList (encFinEnum Empty)) ∧
    {b : Bool | b = true} ∈ Cslib.Complexity.PSPACE
      ((⟨encodeBool, encodingBoolBool.encode_injective⟩ : Bool ↪ List Bool).trans
        (encList (encFinEnum Bool))) ∧
    {xs : List Bool | xs = []} ∈ Cslib.Complexity.PSPACE (encList (encFinEnum Bool)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · let h := identityComputer Empty
    let : ∀ k, Finite (h.tm.Γ k) := fun _ => inferInstanceAs (Finite Empty)
    exact h.computableInPolySpace_encList Function.injective_id Function.injective_id
      (space := List.length) .self
      (fun w i k => (identity_bound (Γ := Empty) (List.map h.inputAlphabet.symm w) i k).trans
        (List.length_map h.inputAlphabet.symm).le)
  · let : ∀ k, Finite (clearComputer.tm.Γ k) := fun k => by
      change Finite (clearMachine.Γ k)
      cases k <;> infer_instance
    exact clearComputer.computableInPolySpace_encList Function.injective_id Function.injective_id
      (space := List.length) .self
      (fun xs i k => by
        simpa only [Equiv.refl_symm, Equiv.coe_refl, id_eq, List.map_id] using clear_bound xs i k)
  · let : ∀ k, Finite (boolComputer.tm.Γ k) := fun _ => inferInstanceAs (Finite Bool)
    apply Cslib.Complexity.mem_PSPACE_of_tm2 boolComputer encodingBoolBool.encode_injective
      encodingBoolBool.encode_injective (space := fun _ => 1) (.const 1) ?_ (fun _ => Iff.rfl)
    intro b i k
    have hbound := identity_bound (Γ := Bool)
      (List.map boolComputer.inputAlphabet.symm (encodeBool b)) i k
    exact hbound.trans ((List.length_map boolComputer.inputAlphabet.symm).le.trans
      (show (encodeBool b).length ≤ 1 from le_rfl))
  · let : ∀ k, Finite (emptyComputer.tm.Γ k) := fun _ => inferInstanceAs (Finite Bool)
    apply Cslib.Complexity.mem_PSPACE_of_tm2 emptyComputer Function.injective_id
      encodingBoolBool.encode_injective (space := fun xs => xs.length + 1)
      (PolyBounded.self.add (.const 1)) ?_ (by simp)
    intro xs i k
    simpa only [Equiv.refl_symm, Equiv.coe_refl, id_eq, List.map_id] using empty_bound xs i k

end ComplexityTests.MathlibTM2Space
