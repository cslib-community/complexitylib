/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.RotationMap.Walk
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Finite
import Complexity.Tactic.PolyTime

/-! Fixed walks carry runtime graph data and preserve exact return labels and kill signals. -/

namespace ComplexityTests.RotationWalk

open Cslib Turing.MultiTapeTM
open ComputableInPolyTime

private def rotate (p : ℕ × ((ℕ × Bool) × Bool)) : (ℕ × Bool) × Bool :=
  if p.2.1.1 = p.1 then ((p.2.1.1, !p.2.1.2), !p.2.2) else p.2

private def graph (selected : ℕ) : RotationMap (ℕ × Bool) Bool where
  rot p := rotate (selected, p)
  rot_involutive := by
    rintro ⟨⟨n, b⟩, d⟩
    by_cases h : n = selected <;> simp [rotate, h]

private theorem polytime_rotation : ComputableInPolyTime rotate
    (encPair encUnary (encPair (encPair encUnary encBool) encBool))
    (encPair (encPair encUnary encBool) encBool) := by
  unfold rotate
  polytime

example (T : ℕ) : ComputableInPolyTime (RotationMap.powRotWithInput rotate T)
    (encPair encUnary (encPair (encPair encUnary encBool) (encPi encBool)))
    (encPair (encPair encUnary encBool) (encPi encBool)) :=
  rotationMap_powRotWithInput polytime_rotation T

example : RotationMap.powRotWithInput rotate 0 (4, (4, false), Fin.elim0) =
    ((4, false), Fin.elim0) := rfl

example : RotationMap.powRotWithInput rotate 3 (4, (4, false), ![false, false, true]) =
    ((4, true), ![false, true, true]) := by
  decide

example : RotationMap.powRotWithInput rotate 3 (4, (5, false), ![false, false, true]) =
    ((5, false), ![true, false, false]) := by
  decide

example (T selected : ℕ) (v : ℕ × Bool) (k : Fin T → Bool) :
    RotationMap.powRotWithInput rotate T (selected, v, k) = ((graph selected).pow T).rot (v, k) :=
  RotationMap.powRotWithInput_eq rotate selected (graph selected) id (fun _ _ => rfl) T v k

example : RotationMap.killedPowRotWithInput rotate 4 2
    (4, (4, false), ![false, false, true, false], ![1, 1, 1, 0]) =
    ((4, true), ![false, true, true, false], ![1, 1, 1, 0]) := by
  have hkill : killTime (![1, 1, 1, 0] : Fin 4 → Fin 2) = 3 :=
    (killTime_eq_iff _ (by decide)).mpr (by decide)
  rw [RotationMap.killedPowRotWithInput_of_killTime rotate _ (by decide) hkill]
  decide

example : RotationMap.killedPowRotWithInput rotate 3 2
    (4, (4, false), ![false, false, true], ![0, 1, 1]) =
    ((4, false), ![false, false, true], ![0, 1, 1]) := by
  have hkill : killTime (![0, 1, 1] : Fin 3 → Fin 2) = 0 :=
    (killTime_eq_iff _ (by decide)).mpr (by decide)
  rw [RotationMap.killedPowRotWithInput_of_killTime rotate _ (by decide) hkill]
  decide

example : RotationMap.killedPowRotWithInput rotate 2 1
    (4, (4, false), ![true, false], ![0, 0]) =
    ((4, false), ![true, false], ![0, 0]) := by
  have hkill : killTime (![0, 0] : Fin 2 → Fin 1) = 0 :=
    (killTime_eq_iff _ (by decide)).mpr (by decide)
  rw [RotationMap.killedPowRotWithInput_of_killTime rotate _ (by decide) hkill]
  decide

example : RotationMap.walkAtWithInput rotate (4, (4, false), ![true, false, true]) 10 =
    (4, true) := by
  decide

/-- info: ((4, true), [false, true, true, false], [1, 1, 1, 0]) -/
#guard_msgs in
#eval
  let p := RotationMap.killedPowRotWithInput rotate 4 2
      (4, (4, false), ![false, false, true, false], ![1, 1, 1, 0])
  (p.1, List.ofFn p.2.1, List.ofFn p.2.2)

example (T q selected : ℕ) [NeZero q] (v : ℕ × Bool) (k : Fin T → Bool)
    (c : Fin T → Fin q) :
    RotationMap.killedPowRotWithInput rotate T q (selected, v, k, c) =
      ((graph selected).killedPow T q).rot (v, k, c) :=
  RotationMap.killedPowRotWithInput_eq rotate selected (graph selected) id
    (fun _ _ => rfl) T q v k c

example : ComputableInPolyTime
    (fun n : ℕ => RotationMap.powRotWithInput rotate 3 (n, (n, false), ![false, false, true]))
    encUnary (encPair (encPair encUnary encBool) (encPi encBool)) := by
  have := polytime_rotation
  fun_prop

example : ComputableInPolyTime
    (fun n : ℕ =>
      let initial := (n, (n + 1, false), ![false, false, true])
      RotationMap.powRotWithInput rotate 3 initial)
    encUnary (encPair (encPair encUnary encBool) (encPi encBool)) := by
  have := polytime_rotation
  fun_prop

example : ComputableInPolyTime (RotationMap.killedPowRotWithInput rotate 3 2)
    (encPair encUnary (encPair (encPair encUnary encBool)
      (encPair (encPi encBool) (encPi (encFinEnum (Fin 2))))))
    (encPair (encPair encUnary encBool)
      (encPair (encPi encBool) (encPi (encFinEnum (Fin 2))))) := by
  have := polytime_rotation
  fun_prop

example (signal : Fin 2 ↪ List Bool) : ComputableInPolyTime
    (fun n : ℕ => RotationMap.killedPowRotWithInput rotate 3 2
      (n, (n, false), ![false, false, true], ![1, 1, 0]))
    encUnary (encPair (encPair encUnary encBool) (encPair (encPi encBool) (encPi signal))) := by
  have := polytime_rotation
  fun_prop

example {P V D : Type} (input : P ↪ List Bool) (vertex : V ↪ List Bool)
    (label : D ↪ List Bool) (step : P × (V × D) → V × D)
    (hstep : ComputableInPolyTime step
      (encPair input (encPair vertex label)) (encPair vertex label)) (T : ℕ) :
    ComputableInPolyTime (RotationMap.powRotWithInput step T)
      (encPair input (encPair vertex (encPi label))) (encPair vertex (encPi label)) := by
  fail_if_success clear hstep; fun_prop
  fun_prop

end ComplexityTests.RotationWalk
