/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: test

public import CslibFrontier.Computability.WordRAM.Dynamic

/-! Canonical native result parsing copies payload words and rejects malformed typed tags and
indices. Option and product examples exercise the shared sequential output bank. -/

open Cslib.WordRAM

example (word : ℕ) : ResultType.nat.decode (fun _ => word) 0 = some word := rfl

example : ResultType.bool.decode (fun _ => 0) 0 = some false := by decide
example : ResultType.bool.decode (fun _ => 1) 0 = some true := by decide
example : ResultType.bool.decode (fun _ => 2) 0 = none := by decide

example : (ResultType.fin 3).decode (fun _ => 2) 0 = some ⟨2, by decide⟩ := by decide
example : (ResultType.fin 3).decode (fun _ => 3) 0 = none := by decide
example : (ResultType.fin 0).decode (fun _ => 0) 0 = none := by decide

example : ResultType.unit.decode (fun _ => 99) 0 = some PUnit.unit := rfl

example : (ResultType.option .nat).decode (fun _ => 0) 0 = some none := by decide
example : (ResultType.option .nat).decode (fun i => [1, 7].getD i 0) 0 = some (some 7) := by
  decide
example : (ResultType.option .nat).decode (fun _ => 2) 0 = none := by decide

example : (ResultType.prod .nat .bool).decode (fun i => [17, 1].getD i 0) 0 =
    some (17, true) := by decide
example : (ResultType.option (.prod .nat (.fin 3))).decode
    (fun i => [1, 17, 2].getD i 0) 0 = some (some (17, ⟨2, by decide⟩)) := by decide
example : (ResultType.option (.prod .nat (.fin 3))).decode
    (fun i => [1, 17, 3].getD i 0) 0 = none := by decide

/-- Even an arbitrary semantic function cannot be supplied by the native natural parser: the
claimed answer must already be the actual output-bank word. -/
example {B : Basis} {r : ℕ} (P : DynamicProgram ⟨ℕ, fun _ => ℕ⟩ r B)
    (f : ℕ → ℕ) (o : ℕ) (regs : Fin r → ℕ) (ho : P.resultType o = .nat)
    (hf : f o ≠ regs (P.resultBank 0)) (hd : P.decode o regs = some (f o)) : False := by
  rw [P.decode_nat o regs ho] at hd
  exact hf (Option.some.inj hd).symm
