/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests of the uniform implicit evaluator)

public import Complexity.Computability.TreeEval.Ary.Packed.RawControllerQuery

/-!
# Uniform raw evaluation with actual input queries

Cyclic points, dirty banks, characteristic two and malformed storage exercise the executable
kernel. A real bit-reading supplier instantiates the native call interface and complete
physical-prefix bound. Its fixed template differs from the actual supplied initial state.
-/

@[expose] public section

namespace ComplexityTests.TreeEvalRawController

open Turing MultiTapeTM Cslib.TreeEval Cslib.TreeEval.Ary.Packed
open Cslib.TreeEval.Ary.Packed.RawController

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

def bank : List ℕ := [5, 6, 7, 8, 9, 5, 6, 7]

example : point 3 2 2 bank = [6, 7, 5, 6, 7, 8] := rfl
example : point 3 2 3 bank = [5, 6, 7, 8, 9, 5] := rfl
example : point 100000 0 1000 [] = [] := rfl

example : step 5 3 2 (1, [2, 4]) (bank, [], some (2, 2)) =
    ([5, 6, 7, 8, 8, 8, 6, 7], [], none) := rfl

example : step 5 3 2 (0, [1, 3]) (bank, [(0, 2, false, 2, 2)], none) =
    ([5, 6, 7, 8, 7, 9, 6, 7], [(0, 0, true, 2, 2)], some (4, 3)) := rfl

example : step 2 1 1 (1, [1]) ([2, 3], [], some (1, 0)) = ([3, 3], [], none) := rfl

example : step 5 1 1 (1, [1]) ([0, 0], [], some (1, 0)) =
    ([0, 0], [], some (1, 0)) := rfl
example : need 5 1 1 ([0, 0], [], some (1, 0)) = none := rfl

example : checkedScaleBank ((5, 2, 1, 2), bank) = [5, 6, 9, 6, 9, 5, 6, 7] := rfl
example : checkedScaleBank ((5, 2, 0, 2), [0, 0]) = [0, 0] := rfl

/-- Halt after returning the original input's first bit. The emitted junk must be discarded. -/
def bitReader : QueryMachine (Bool × Bool) where
  init := (false, false)
  query _ := 0
  next p := (true, p.2.getD false)
  emit _ := [true, true]
  halted := Prod.fst
  finish _ := [true, true]

abbrev encReader : Bool × Bool ↪ List Bool := encPair encBool encBool

def start (_ : Query.RequestArgs Unit) : Bool × Bool := (false, false)
def answer (q : Bool × Bool) : Reply := (1, [if q.2 then 1 else 0])

def root : Query.Context Unit := ((), (5, 1, 1), [5, 5], [], some (1, 0))
def template : Query.Context Unit := ((), (2, 0, 0), [], [], none)
def evaluator := Query.machine template bitReader start answer

example : evaluator.runFrom [true] (.inl root) 3 =
    .inl ((), (5, 1, 1), [6, 5], [], none) := rfl
example : evaluator.runFrom [] (.inl root) 3 =
    .inl ((), (5, 1, 1), [5, 5], [], none) := rfl
example : evaluator.runFrom [true] (.inl root) 5 =
    .inl ((), (5, 1, 1), [6, 5], [], none) := rfl
example : (Query.machine root bitReader start answer).output [true] 3 = [] := rfl

example : ComputableInSpace evaluator.next
    (encPair (Query.encMachineState encUnit encReader) (encOption encBool))
    (Query.encMachineState encUnit encReader)
    (fun q => (encPair (Query.encMachineState encUnit encReader) (encOption encBool) q).length) :=
  Query.machine_next_inSpace encUnit encReader template bitReader start answer
    (ComputableInSpace.of_finite _) (ComputableInSpace.of_finite _)
    (ComputableInSpace.budget_const _ (.refl _)) (ComputableInSpace.of_finite _)

def tree (w : List Bool) : Ary.Tree 1 1 0 := .leaf (fun _ => w[0]?.getD false)
def encodeBit (v : Fin 1 → Bool) : Fin 1 → ZMod 5 := fun _ => if v 0 then 1 else 0
def extension : Ary.Gate 1 1 → (Fin 1 → Fin 1 → ZMod 5) → Fin 1 → ZMod 5 :=
  fun _ _ _ => 0
def zeroBank : Ary.State (ZMod 5) 1 1 := fun _ _ => 0

/-- Actual input reads witness all requested-supplier premises, including physical peak states. -/
example (w : List Bool) :
    ∃ clock, evaluator.runFrom w
        (.inl ((), (5, 1, 1), ofCfg (Ary.Iter.initialCfg zeroBank 1 0))) clock =
      .inl ((), (5, 1, 1), ofCfg
        (⟨Ary.procWith encodeBit extension (units 5) (tree w) 1 0 zeroBank, [], .ret⟩ :
          Ary.Iter.Cfg (ZMod 5) 1 1)) ∧
      ∀ i ≤ clock, (Query.encMachineState encUnit encReader
        (evaluator.runFrom w
          (.inl ((), (5, 1, 1), ofCfg (Ary.Iter.initialCfg zeroBank 1 0))) i)).length ≤
            Query.queryStateBound (encUnit ()).length 5 1 1 0 4 := by
  apply Query.exists_runFrom_root_encoded_bound encUnit encReader template bitReader start
    answer w () (by decide) encodeBit extension (tree w) zeroBank 1 0 4
  intro n req hneed
  refine ⟨1, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have : i = 0 := by omega
    subst i
    rfl
  · rfl
  · let q := Ary.Iter.runFrom (by decide) encodeBit extension (units 5) (tree w).nodeAt
      (Ary.Iter.initialCfg zeroBank 1 0) n
    have hbound := Ary.Iter.runFrom_initial_bounds (tree w) (by decide) encodeBit extension
      (units 5) zeroBank 1 0 n
    have hstack : q.stack = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hs := hbound.1
      change q.stack.length ≤ 0 at hs
      omega
    change ReplyCorrect encodeBit extension (tree w).nodeAt q _
    cases hm : q.mode with
    | ret => simp [ReplyCorrect, hm, hstack]
    | call c t =>
      simp only [ReplyCorrect, hm, hstack, Ary.Iter.path_nil, tree, Ary.Tree.nodeAt]
      refine ⟨rfl, ?_⟩
      intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      change ((if w[0]?.getD false then 1 else 0 : ℕ) : ZMod 5) =
        if w[0]?.getD false then 1 else 0
      cases w[0]?.getD false <;> rfl
  · intro i hi
    simp [encReader, encBool_apply]

end ComplexityTests.TreeEvalRawController
