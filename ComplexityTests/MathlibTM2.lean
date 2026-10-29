/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Computability.Machines.Turing.TM2.PolyTime
import Mathlib.Logic.Equiv.Bool

/-! Regression checks for the public Mathlib TM2 bridge. Source machines adapted from the
Complexitylib TM2 bridge tests: https://github.com/SamuelSchlesinger/complexitylib/pull/72. -/

namespace ComplexityTests.MathlibTM2

open Turing Turing.MultiTapeTM

private def prependMachine : FinTM2 :=
  { idComputer Bool with m := fun _ => .push () (fun _ => false) .halt }

private noncomputable def prependComputer :
    TM2ComputableInPolyTime id id (fun w : List Bool => false :: w) where
  tm := prependMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 1
  outputsFun _ := ⟨⟨1, rfl⟩, by simp⟩

-- An infinite input domain and order-sensitive output; this includes the empty word.
example : ComputableInPolyTime (fun w : List Bool => false :: w)
    (encList (encFinEnum Bool)) (encList (encFinEnum Bool)) := by
  let : ∀ k, Finite (prependComputer.tm.Γ k) := fun _ => inferInstanceAs (Finite Bool)
  exact prependComputer.computableInPolyTime_encList Function.injective_id Function.injective_id

example : TM2.stepTotal prependMachine.m (initList prependMachine [true, true]) =
    haltList prependMachine [false, true, true] := rfl

-- Padded clocks retain the result instead of losing it when the partial source step returns none.
example : (TM2.stepTotal prependMachine.m)^[9] (initList prependMachine [true, true]) =
    haltList prependMachine [false, true, true] := rfl

-- Nonidentity alphabet equivalences: internal false represents external true.
private noncomputable def flippedComputer :
    TM2ComputableInPolyTime id id (fun w : List Bool => true :: w) where
  tm := prependMachine
  inputAlphabet := Equiv.boolNot
  outputAlphabet := Equiv.boolNot
  time := 1
  outputsFun _ := ⟨⟨1, rfl⟩, by simp⟩

example : ComputableInPolyTime (fun w : List Bool => true :: w)
    (encList (encFinEnum Bool)) (encList (encFinEnum Bool)) := by
  let : ∀ k, Finite (flippedComputer.tm.Γ k) := fun _ => inferInstanceAs (Finite Bool)
  exact flippedComputer.computableInPolyTime_encList Function.injective_id Function.injective_id

-- Register changes, peeking without popping, and a jump to a different label.
private def peekMachine : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Bool
  main := false
  σ := Bool
  initialState := false
  m
    | false => .load (fun _ => true) (.peek () (fun v a => v && a.getD false)
        (.branch id (.goto (fun _ => true)) .halt))
    | true => .load not (.push () id .halt)

example : (TM2.stepTotal peekMachine.m)^[2] (initList peekMachine [true, false]) =
    haltList peekMachine [false, true, false] := rfl

example : TM2.stepTotal peekMachine.m (initList peekMachine [false, true]) =
    haltList peekMachine [false, true] := rfl

/-- Clear a four-letter input stack, then return one letter on a different singleton stack. -/
private abbrev constantMachine : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ k := match k with
    | false => Fin 4
    | true => Fin 1
  Λ := Unit
  main := ()
  σ := Bool
  initialState := false
  m _ := .pop false (fun _ a => a.isSome)
    (.branch id (.goto (fun _ => ())) (.push true (fun _ => (0 : Fin 1)) .halt))

/-- Source states while consuming the input. -/
private def constantCfg (xs : List (Fin 4)) (v : Bool) : constantMachine.Cfg where
  l := some ()
  var := v
  stk k := match k with
    | false => xs
    | true => []

private lemma constant_nil (v : Bool) :
    constantMachine.step (constantCfg [] v) = some (haltList constantMachine [(0 : Fin 1)]) := by
  apply congrArg some
  change TM2.Cfg.mk _ _ _ = TM2.Cfg.mk _ _ _
  congr 1
  funext k
  cases k <;> rfl

private lemma constant_cons (a : Fin 4) (xs : List (Fin 4)) (v : Bool) :
    constantMachine.step (constantCfg (a :: xs) v) = some (constantCfg xs true) := by
  apply congrArg some
  change TM2.Cfg.mk _ _ _ = TM2.Cfg.mk _ _ _
  congr 1
  funext k
  cases k <;> rfl

private lemma constant_iterate (xs : List (Fin 4)) (v : Bool) :
    (fun s : Option constantMachine.Cfg => s.bind constantMachine.step)^[xs.length + 1]
      (some (constantCfg xs v)) = some (haltList constantMachine [(0 : Fin 1)]) := by
  induction xs generalizing v with
  | nil => exact constant_nil v
  | cons a xs ih =>
      change (fun s : Option constantMachine.Cfg => s.bind constantMachine.step)^[xs.length + 1 + 1]
        (some (constantCfg (a :: xs) v)) = _
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some, constant_cons]
      exact ih true

/-- A polynomial source certificate whose input and output alphabet sizes differ. -/
private noncomputable def constantComputer :
    TM2ComputableInPolyTime id id (fun _ : List (Fin 4) => [(0 : Fin 1)]) where
  tm := constantMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.X + 1
  outputsFun xs := by
    refine ⟨⟨xs.length + 1, ?_⟩, by simp⟩
    have hi : initList constantMachine xs = constantCfg xs false := by
      change TM2.Cfg.mk _ _ _ = TM2.Cfg.mk _ _ _
      congr 1
      funext k
      cases k <;> rfl
    simp only [Equiv.refl, id_eq, Option.map_some]
    change (fun s : Option constantMachine.Cfg => s.bind constantMachine.step)^[xs.length + 1]
      (some (initList constantMachine (xs.map (@id (Fin 4))))) =
        some (haltList constantMachine [(0 : Fin 1)])
    rw [List.map_id, hi]
    exact constant_iterate xs false


-- Independent input/output alphabets and a runtime that grows with the input length.
example : ComputableInPolyTime (fun _ : List (Fin 4) => [(0 : Fin 1)])
    (encList (encFinEnum (Fin 4))) (encList (encFinEnum (Fin 1))) := by
  let : ∀ k, Finite (constantComputer.tm.Γ k) := fun k => by
    change Finite (constantMachine.Γ k)
    cases k <;> infer_instance
  exact constantComputer.computableInPolyTime_encList Function.injective_id Function.injective_id

-- Empty alphabets require no default symbol.
example : ComputableInPolyTime (id : List Empty → List Empty)
    (encList (encFinEnum Empty)) (encList (encFinEnum Empty)) := by
  let computer := idComputableInPolyTime (id : List Empty → List Empty)
  let : ∀ k, Finite (computer.tm.Γ k) := fun _ => inferInstanceAs (Finite Empty)
  exact computer.computableInPolyTime_encList Function.injective_id Function.injective_id

-- A structured infinite source type is retained, rather than replacing the function by a word map.
private def naturalWord : ℕ ↪ List Bool :=
  ⟨Computability.encodeNat, Computability.encodingNatBool.encode_injective⟩

example : ComputableInPolyTime (id : ℕ → ℕ)
    (naturalWord.trans (encList (encFinEnum Bool)))
    (naturalWord.trans (encList (encFinEnum Bool))) := by
  let computer := idComputableInPolyTime Computability.encodeNat
  let : ∀ k, Finite (computer.tm.Γ k) := fun _ => inferInstanceAs (Finite Bool)
  exact computer.computableInPolyTime_encList
    Computability.encodingNatBool.encode_injective Computability.encodingNatBool.encode_injective

end ComplexityTests.MathlibTM2
