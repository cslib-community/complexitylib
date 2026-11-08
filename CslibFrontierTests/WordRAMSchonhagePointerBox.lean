/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (tests)

import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableBox.Pointer.Exec

-- VM fixtures check adapters; the symbolic endpoint separately checks admitted geometry.
set_option linter.hashCommand false

namespace ComplexityTests.WordRAMSchonhagePointerBox

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

private def physical : ℕ := 2 ^ 400
private def base : ℕ := physical + 100
private def left : ℕ := physical + 10
private def right : ℕ := physical + 20
private def queries : ℕ := physical + 30
private def X : Matrix (Fin 1) (Fin (D 0)) ℤ := fun _ _ => 1
private def Y : Matrix (Fin (D 0)) (Fin 1) ℤ := fun _ _ => 1
private def requests (Q : ℕ) : List (Fin 1 × Fin 1) := List.replicate Q (0, 0)

private def initial (Q : ℕ) (leftWord rightWord : ℕ := 1) : Data 173 :=
  let original := (State.init (BoxProduct.input true 0 0 X Y (requests Q)) : State 160).data
  let M := CallableProduct.windowSize 1 Q
  let I := QueriedProduct.inputEnd 0 1 Q
  let mem := fun a =>
    if a = left then leftWord else if a = right then rightWord else
    if queries ≤ a ∧ a < queries + 2 * Q then 0 else
    if base ≤ a ∧ a < base + 5 then original.mem (a - base) else
    if a = base + I then 0 else
    if base ≤ a ∧ a < base + M then 2 * M + 27 else
    if a = base + M then 91 else 0
  let x : Data 173 := ⟨fun _ => 777, mem⟩
  x.set PointerBoxProduct.Reg.base base |>.set PointerBoxProduct.Reg.left left |>.set
    PointerBoxProduct.Reg.right right |>.set PointerBoxProduct.Reg.queries queries

private def observe (Q : ℕ) (leftWord rightWord : ℕ := 1) : Option (List ℕ × Bool) :=
  let x := initial Q leftWord rightWord
  (PointerBoxProduct.program.eval 1024 1024 x).map fun (y, _) =>
    let out := y.regs (PointerBoxProduct.callableBank CallableProduct.Reg.result)
    ((List.range Q).map (fun i => y.mem (out + i)),
      decide (out = base + QueriedProduct.outputBase 0 0 1 Q ∧
        y.mem left = leftWord ∧ y.mem right = rightWord ∧
        (∀ i < 2 * Q, y.mem (queries + i) = x.mem (queries + i)) ∧
        y.regs PointerBoxProduct.Reg.left = left ∧
        y.regs PointerBoxProduct.Reg.right = right ∧
        y.regs PointerBoxProduct.Reg.queries = queries ∧
        y.mem (base + CallableProduct.windowSize 1 Q) = 91 ∧
        y.mem (base + QueriedProduct.inputEnd 0 1 Q) = 0 ∧
        y.mem (base + 5) = leftWord ∧ y.mem (base + 6) = rightWord))

-- External pointers exceed the actual virtual modulus; source and physical offsets differ.
example : CallableProduct.windowSize 1 3 < left := by decide +kernel

-- Actual raw one/one multiplication returns exact Signed.encode 1 = 2, in duplicate order.
#guard observe 3 == some ([2, 2, 2], true)
#guard observe 1 1 0 == some ([0], true)
#guard observe 0 == some ([], true)

-- Reuse the same dirty private window after changing the occurrence count.
private def reuse : Option (List ℕ × Bool) := do
  let (first, _) ← PointerBoxProduct.program.eval 1024 1024 (initial 3)
  let fresh := initial 1 0 1
  let x : Data 173 := ⟨fresh.regs, fun a =>
    if base ≤ a ∧ a < base + CallableProduct.windowSize 1 1 ∧
        ¬(a < base + 5 ∨ a = base + QueriedProduct.inputEnd 0 1 1)
      then first.mem a else fresh.mem a⟩
  let (y, _) ← PointerBoxProduct.program.eval 1024 1024 x
  let out := y.regs (PointerBoxProduct.callableBank CallableProduct.Reg.result)
  pure ([y.mem out], decide (y.mem left = 0 ∧ y.mem right = 1 ∧
    y.mem queries = 0 ∧ y.mem (queries + 1) = 0))

#guard reuse == some ([0], true)

-- Distinct coordinates distinguish occurrence order from a grouped or deduplicated answer list.
private def mixed : Option (List ℕ × Bool) :=
  let qs : List (Fin 2 × Fin 2) := [(1, 0), (0, 1), (1, 0)]
  let X : Matrix (Fin 2) (Fin (D 0)) ℤ := fun i _ => if i = 0 then 1 else 0
  let Y : Matrix (Fin (D 0)) (Fin 2) ℤ := fun _ j => if j = 1 then 1 else 0
  let original := (State.init (BoxProduct.input true 0 0 X Y qs) : State 160).data
  let M := CallableProduct.windowSize 2 3
  let I := QueriedProduct.inputEnd 0 2 3
  let words := [1, 0, 0, 1, 1, 0]
  let mem := fun a =>
    if a = left then 1 else if a = left + 1 then 0 else
    if a = right then 0 else if a = right + 1 then 1 else
    if queries ≤ a ∧ a < queries + 6 then words.getD (a - queries) 0 else
    if base ≤ a ∧ a < base + 5 then original.mem (a - base) else
    if a = base + I then 0 else
    if base ≤ a ∧ a < base + M then 2 * M + 27 else 0
  let x : Data 173 := ⟨fun _ => 777, mem⟩
  let x := x.set PointerBoxProduct.Reg.base base |>.set PointerBoxProduct.Reg.left left |>.set
    PointerBoxProduct.Reg.right right |>.set PointerBoxProduct.Reg.queries queries
  (PointerBoxProduct.program.eval 1024 1024 x).map fun (y, _) =>
    let out := y.regs (PointerBoxProduct.callableBank CallableProduct.Reg.result)
    ((List.range 3).map (fun i => y.mem (out + i)),
      decide (y.mem (base + 5) = 1 ∧ y.mem (base + 6) = 0 ∧
        y.mem (base + 7) = 0 ∧ y.mem (base + 8) = 1) &&
        (List.range 6).all (fun i => y.mem (queries + i) == words.getD i 0))

#guard mixed == some ([0, 2, 0], true)

end ComplexityTests.WordRAMSchonhagePointerBox
