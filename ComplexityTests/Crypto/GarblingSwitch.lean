/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import Complexity.Crypto.Primitives.Garbling.Privacy
import Complexity.Crypto.Primitives.Garbling.Switch.Oblivious

/-! # Garbled switch systems: checked instances

A five-gate switch system over `ℤ_4` that outputs `x` when the control input `c` is `0` and `0`
when `c` is `1`: a constant wire `z = 0`, the complement `c' = 1 - c`, a switch from `x` to `w`
controlled by `c`, a switch from `z` to `w'` controlled by `c'`, and a join `w = w'`. Propagation
solves it on every input with a control bit, it is well formed, and labels in `ℤ_4` with the low
bit as colour garble it correctly on concrete hash, offset and input labels. The correctness and
obliviousness theorems apply with satisfiable hypotheses. -/

namespace ComplexityTests.GarblingSwitch

open Cslib Cslib.Crypto Cslib.Crypto.Garbling Cslib.Crypto.Garbling.Switch

/-- `w = x` if `c = 0`, `w = 0` if `c = 1`; inputs `x = inl 0`, `c = inl 1`; internal wires
`z = inr 0`, `w = inr 1`, `c' = inr 2`, `w' = inr 3`. -/
def mux : SwitchSystem 2 1 4 (ZMod 4) where
  gates :=
    [.affine [] 0 0,
     .affine [(.inl 1, -1)] 1 2,
     .switch (.inl 0) 1 (.inl 1),
     .switch (.inr 0) 3 (.inr 2),
     .join (.inr 1) (.inr 3)]
  output _ := .inr 1

/-- The satisfying assignment on input `(x, c)` for a control bit `c`. -/
def muxσ (x c : ZMod 4) : Fin 2 ⊕ Fin 4 → ZMod 4 :=
  ![x, c] |> Sum.elim <| ![0, if c = 0 then x else 0, 1 - c, if c = 0 then x else 0]

theorem mux_wellFormed : mux.WellFormed := by
  simp [mux, SwitchSystem.WellFormed, SwitchSystem.WellFormedFrom, SwitchGate.WellPlaced,
    SwitchGate.define]

theorem mux_satisfies (x : ZMod 4) {c : ZMod 4} (hc : c = 0 ∨ c = 1) :
    mux.Satisfies ![x, c] (muxσ x c) := by
  refine ⟨fun i => by fin_cases i <;> rfl, ?_⟩
  have h10 : (1 : ZMod 4) ≠ 0 := by decide
  rcases hc with rfl | rfl <;> simp [mux, muxσ, SwitchGate.Holds, SwitchGate.termSum, h10]

-- Propagation finds the output on both control values.
example : mux.solve ![3, 0] (mux.output 0) = some 3 := by decide
example : mux.solve ![3, 1] (mux.output 0) = some 0 := by decide

/-- The low bit of `ℤ_4`, the colour of a label. -/
def col4 : ZMod 4 →+ ZMod 2 := (ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)).toAddMonoidHom

instance : Nonempty {Δ : ZMod 4 // col4 Δ = 1} := ⟨⟨1, by decide⟩⟩

/-- A toy tweaked hash. It is not correlation robust; it only makes the statements concrete. -/
def toyH (k : ZMod 4) (t : ℕ) : ZMod 4 := 3 * k + t

-- The garbled system decodes to `x` on control `0` and to `0` on control `1`, by computation.
example : (garbleWith mux toyH col4 3 ![1, 2]).run mux toyH col4 ![1, 0] 0 = some 1 := by
  decide
example : (garbleWith mux toyH col4 3 ![1, 2]).run mux toyH col4 ![1, 1] 0 = some 0 := by
  decide

-- The general correctness theorem applies to every hash, offset of colour `1` and input labels.
example (H : ZMod 4 → ℕ → ZMod 4) (Δ : ZMod 4) (hΔ : col4 Δ = 1) (K : Fin 2 → ZMod 4) :
    (garbleWith mux H col4 Δ K).run mux H col4 ![1, 0] 0 = some 1 := by
  have h := Garbled.run_garbleWith mux_wellFormed (mux_satisfies 1 (.inl rfl)) H col4 hΔ K 0
    (v := 1) (by decide) (.inr rfl)
  simpa [show (1 : ZMod 4) ≠ 0 by decide] using h

-- Obliviousness applies to the multiplexer: the advantage of every distinguisher equals the CCR
-- advantage of a reduction that never repeats a tweak.
example (x c : ZMod 4) (hc : c = 0 ∨ c = 1) (D : SwitchView (ZMod 4) 2 → ProbComp Bool) :
    Game.advantage (realGame mux toyH col4 ![x, c] D)
        (simGame mux toyH col4 (mux.controls (muxσ x c)) D) =
      CCR.advantage toyH col4 (reduction mux toyH col4 (muxσ x c) D) ∧
    CCR.IsTweakUnique (reduction mux toyH col4 (muxσ x c) D) :=
  ⟨advantage_realGame_simGame mux_wellFormed (mux_satisfies x hc) toyH col4 D,
    isTweakUnique_reduction mux toyH col4 (muxσ x c) D⟩

-- The simulator sees one control bit per gate; only the third gate is open when `c = 1`.
example (x : ZMod 4) : mux.controls (muxσ x 1) = [false, false, true, false, false] := by
  simp [SwitchSystem.controls, mux, muxσ, SwitchGate.isOpen, show (1 : ZMod 4) ≠ 0 by decide]

end ComplexityTests.GarblingSwitch
