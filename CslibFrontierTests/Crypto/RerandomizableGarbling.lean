/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import CslibFrontier.Crypto.Primitives.Garbling.Rerandomizable
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Ring

/-! # Rerandomizable garbling: checked instances

A one-input toy scheme over `ZMod 3` computing `f xor x₀`: garbling with coins `r` puts the
labels `r` and `r + 1` on the input wire and publishes `[f] - r`; rerandomizing with coins `r'`
shifts the circuit by `-r'` and every label by `r'`. It is correct, satisfies randomness
composition with additive explanations, carries the inverse data of
`RandomnessComposition.Invertible`, and its label action respects composition, so the hypotheses
of both reductions are satisfiable. Its explanation maps are bijective in the second argument,
so rerandomization privacy and fixed-coin explainability hold with zero error. -/

namespace CslibFrontierTests.RerandomizableGarbling

open Cslib Cslib.Crypto Cslib.Crypto.Garbling Cslib.Crypto.Garbling.RerandomizableGarbling

/-- The toy scheme. The garbled circuit `[f] - r` together with the label `r + x₀` determines
`f xor x₀`, and nothing else is published. -/
abbrev toy : RerandomizableGarbling Bool 1 where
  GC := ZMod 3
  Label := ZMod 3
  Perm := ZMod 3
  Coins := ZMod 3
  RerandCoins := ZMod 3
  Out := Bool
  evalFn f x := xor f (x 0)
  garble f r := ((if f then 1 else 0) - r, fun _ => (r, r + 1))
  rerand gc r' := (gc - r', fun _ => r')
  act p L := L + p
  comp p q := p + q
  evaluate gc X := decide (gc + X 0 = 1)

-- Fresh garblings are correct, by computation.
example : toy.Correct := by
  intro f x r
  revert f x r
  decide

/-- Additive explanations. -/
def toyRC : toy.RandomnessComposition where
  explainGb r r' := r + r'
  explainRerand r₁ r₂ := r₁ + r₂
  garble_explainGb f r r' := by
    refine Prod.ext ?_ (funext fun _ => Prod.ext ?_ ?_) <;>
      simp only [permEncoding] <;> ring
  rerand_explainRerand f r r₁ r₂ := by
    refine Prod.ext ?_ rfl
    simp only
    ring

-- Rerandomized garblings are correct, from randomness composition.
example : toy.RerandCorrect :=
  rerandCorrect_of_correct toyRC (by intro f x r; revert f x r; decide)

/-- The inverse data: subtract the explanation, and undo rerandomization by negating its coins. -/
def toyInvertible : toyRC.Invertible where
  unexplainGb r r' := r - r'
  unexplainGb_explainGb r r' := add_sub_cancel_right r r'
  explainGb_unexplainGb r r' := sub_add_cancel r r'
  explainRerand_bijective r₂ := (Equiv.addRight r₂).bijective
  invRerand := Equiv.neg (ZMod 3)
  rerand_invRerand gc r' := by
    change gc - r' - -r' = gc
    ring
  act_invRerand gc r' i L := by
    change L + r' + -r' = L
    ring

-- The label action respects composition.
example (p q L : ZMod 3) : toy.act (toy.comp p q) L = toy.act q (toy.act p L) := by
  change L + (p + q) = L + p + q
  ring

-- Both reductions apply to the toy scheme.
example (f : Bool) (x : Fin 1 → Bool)
    (D : (Fin 1 → ZMod 3) × ZMod 3 × ZMod 3 × ZMod 3 → ProbComp Bool) :
    toy.explainGbAdvantage toyRC f x D = toy.rerandAdvantage f x (toy.explainGbReduction f D) :=
  explainGbAdvantage_eq toyRC toyInvertible f x D

example (f : Bool) (x : Fin 1 → Bool)
    (D : ZMod 3 × (Fin 1 → ZMod 3) × ZMod 3 × ZMod 3 × ZMod 3 → ProbComp Bool) :
    toy.explainRerandAdvantage toyRC f x D ≤
      toy.rerandAdvantage f x (toy.explainRerandReductionLeft toyInvertible f D) +
        toy.rerandAdvantage f x (toy.explainRerandReductionRight f D) :=
  explainRerandAdvantage_le toyRC toyInvertible
    (fun p q L => show L + (p + q) = L + p + q by ring) f x D

-- Rerandomization privacy holds with zero error.
example (f : Bool) (x : Fin 1 → Bool) :
    ProbComp.eval (toy.rerandReal f x) = ProbComp.eval (toy.rerandIdeal f x) :=
  eval_rerandReal toyRC (fun r => (Equiv.addLeft r).bijective) f x

-- Fixed-coin explainability holds with zero error.
example (f : Bool) (x : Fin 1 → Bool) (r r₁ : ZMod 3) :
    ProbComp.eval (toy.explainGbFixedReal toyRC f x r) =
        ProbComp.eval (toy.explainGbFixedIdeal f x r) ∧
      ProbComp.eval (toy.explainRerandFixedReal toyRC f x r r₁) =
        ProbComp.eval (toy.explainRerandFixedIdeal f x r r₁) :=
  ⟨eval_explainGbFixedReal toyRC f x r (Equiv.addLeft r).bijective,
    eval_explainRerandFixedReal toyRC f x r r₁ (Equiv.addLeft r₁).bijective⟩

end CslibFrontierTests.RerandomizableGarbling
