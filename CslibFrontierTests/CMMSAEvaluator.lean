/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Computability.MCSP.PartialHardness.Evaluator

/-! Tests for the explicit-table evaluator of the CMMSA partial truth table. -/

public section

namespace CslibFrontierTests.CMMSAEvaluator

open Cslib Cslib.Complexity Cslib.PartialMCSP.FromCMMSA

/-! Three formulas `x₀`, `¬x₀`, `x₀` over one variable of weight `2`, with `Δ = k = λ = 1`. The
formula index takes `⌈log₂ 3⌉ = 2` bits, and slot `(0, 0)` holds a seed of `W = ℓ 0 = 1` bit and
a mask, so inputs have `4` bits: the index in bits `0, 1`, the seed in bit `2` and the mask in
bit `3`. Index `3` is not a formula, so its entries are undefined. -/

/-- Three one-literal formulas over one variable of weight `2`. -/
def small : CMMSAInstance := ⟨[2], 1, [[[(0, true)]], [[(0, false)]], [[(0, true)]]]⟩

example : inputLength small 1 1 1 = 4 := by decide

/-- The function of variable `0` is the identity on its one input bit. -/
def f₀ : VarFunctions small 1 := fun v y => if h : 0 < varLength small 1 v then y ⟨0, h⟩ else false

example : tables f₀ = [[false, true]] := by decide

/-- The entry at `x` is the mask plus `f₀` at the seed: here bit `3` plus bit `2` of `x`. -/
example : tableN small 1 1 1 [[false, true]] =
    [some false, some false, some false, none, some true, some true, some true, none,
      some true, some true, some true, none, some false, some false, some false, none] := by
  decide

/-- A table for `f₀` produces the table of `toInstance`. -/
example : tableN small 1 1 1 [[false, true]] = List.ofFn (toInstance small 1 1 1 1 f₀).table := by
  rw [← show tables f₀ = [[false, true]] by decide]
  exact tableN_tables f₀ 1

/-- The table of `f₀` must be in `equivFin` order: the swapped table is not a table of `f₀`. -/
example : ¬ IsVarTable small 1 f₀ [[true, false]] 0 := fun h => by
  have h0 := h fun _ => false
  revert h0
  decide

/-! Strides: one formula with terms `x₀ x₁` and `¬x₁` over variables of weights `1` and `2`, with
`Δ = k = 2` and `λ = 1`. Then `ℓ 0 = 0`, `ℓ 1 = W = 1`, the index takes no bits and each slot has
`k W + 1 = 3` bits, the two seeds then the mask. Slot `(t, q)` starts at bit `3 (q + 2 t)`, so
inputs have `12` bits. With `f 0 = true` and `f 1` the identity, the slots of term `0` contribute
bit `2` (the two seeds of variable `0` cancel) and bits `3, 4, 5`, and term `1` has bits `6, 7, 8`;
slot `(1, 1)`, bits `9` to `11`, is not occupied. -/

/-- One formula with two terms over variables of weights `1` and `2`. -/
def strides : CMMSAInstance := ⟨[1, 2], 1, [[[(0, true), (1, true)], [(1, false)]]]⟩

example : inputLength strides 2 2 1 = 12 := by decide

/-- `f 0` is the constant `true` on no inputs and `f 1` is the identity on one input. -/
def f₁ : VarFunctions strides 1 := fun v y =>
  if h : 0 < varLength strides 1 v then y ⟨0, h⟩ else true

example : tables f₁ = [[true], [false, true]] := by decide

/-- At `0` both term parities are `0`. Bit `2` alone gives parities `1, 0`; bits `2, 6` give `1, 1`;
bits `3, 7` (the first seed of slot `(0, 1)` and the second seed of slot `(1, 0)`) give `1, 1`;
bits `4, 5` give `0, 0`; and bit `9`, in the unoccupied slot `(1, 1)`, is not read. -/
example : [0, 4, 68, 136, 48, 512].map (entryN strides 2 2 1 [[true], [false, true]]) =
    [some false, none, some true, some true, some false, some false] := by
  decide

/-- The strides agree with `toInstance`, read off the input bits directly. -/
example : (toInstance strides 2 2 1 1 f₁).table ⟨136, by decide⟩ = some true := by decide

/-- Term parities need only the tables of the term's own variables: here an arbitrary table list
`T` that has the table of `f v` at every variable `v` of term `t`. -/
example {I : CMMSAInstance} {Δ k lam : ℕ} (f : VarFunctions I lam) (T : List (List Bool))
    (x : Fin (2 ^ inputLength I Δ k lam)) (t : Fin Δ)
    (hT : ∀ q : Fin Δ, (q : ℕ) < (term I ((x : ℕ) % 2 ^ indexWidth I) t).length →
      T.getD (var I ((x : ℕ) % 2 ^ indexWidth I) t q) [] =
        varTable f (var I ((x : ℕ) % 2 ^ indexWidth I) t q)) :
    termParityN I Δ k lam T x t = termParity f ((BitString.equivFin _).symm x) t :=
  termParityN_eq x t fun q hq => .of_getD_eq (hT q hq)

end CslibFrontierTests.CMMSAEvaluator
