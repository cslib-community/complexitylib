/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Basic

/-!
# Inversion and prediction experiments

The two experiments behind one-way functions and hard-core predicates, stated for one fixed
function and input distribution.

* `inversionExperiment sample f A`: draw `x ← sample` and give the inverter `f x`; it wins when it
  returns any `x'` with `f x' = f x`.
* `predictionExperiment sample f h A`: draw `x ← sample` and give the predictor `f x`; it wins when
  it returns the bit `h x`.

The input distribution is a parameter, so the same experiment serves fixed-length inputs of a
word function and the finite Goldreich–Levin analysis, and can serve other input laws such as
uniform residues.
There is no security parameter, setup or encoding: asymptotic notions such as
`Cslib.Crypto.OneWay` draw their setup and then run these experiments. The experiments are written
for any monad. Programs use `ProbComp`; finite distributional arguments use `PMF`, and
`ProbComp.eval_inversionExperiment` relates the two.

## Main definitions

* `Cslib.Crypto.inversionExperiment`: the inversion experiment, accepting any preimage.
* `Cslib.Crypto.predictionExperiment`: the experiment of predicting a hidden bit of the input from
  its image.

## Main results

* `Cslib.Crypto.inversionExperiment_eq_of_injective`: for an injective function, accepting any
  preimage is the same as recovering the sampled input.
* `Cslib.ProbComp.eval_inversionExperiment`, `Cslib.ProbComp.eval_predictionExperiment`:
  evaluating a program experiment gives the same experiment on distributions.
* `Cslib.Crypto.inversionExperiment_bind`: randomness that the inverter samples independently of
  its challenge may be sampled before the experiment.
* `Cslib.Crypto.predictionExperiment_uniform_bit`: an independent uniform hidden bit is guessed
  with probability exactly one half.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09],
  Section 9.2.1, Definition 9.4 (one-way functions).
* [O. Goldreich, *Foundations of Cryptography, Volume 1*][Goldreich2001], Definitions 2.2.1
  (strong one-way functions) and 2.5.1 (hard-core predicates).
-/

@[expose] public section

namespace Cslib.Crypto

open Probability

variable {m : Type → Type*} [Monad m] {α : Type} {β : Type*}

/-- The inversion experiment for `f` on inputs drawn from `sample`: the challenger draws `x` and
gives the inverter `f x`; the inverter wins when it returns any preimage of `f x`. -/
def inversionExperiment [BEq β] (sample : m α) (f : α → β) (inverter : β → m α) : m Bool := do
  let x ← sample
  let x' ← inverter (f x)
  return f x' == f x

/-- The prediction experiment for the bit `h` of inputs drawn from `sample`: the challenger draws
`x` and gives the predictor `f x`; the predictor wins when it returns `h x`. -/
def predictionExperiment (sample : m α) (f : α → β) (h : α → Bool)
    (predictor : β → m Bool) : m Bool := do
  let x ← sample
  let guess ← predictor (f x)
  return guess == h x

/-- For an injective function, accepting any preimage is the same as recovering the sampled
input. -/
theorem inversionExperiment_eq_of_injective [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (sample : m α)
    {f : α → β} (hf : Function.Injective f) (inverter : β → m α) :
    inversionExperiment sample f inverter = (do
      let x ← sample
      let x' ← inverter (f x)
      return x' == x) := by
  have heq (x' x : α) : (f x' == f x) = (x' == x) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, hf.eq_iff]
  simp only [inversionExperiment, heq]

/-- On distributions, the inversion experiment maps the inverter's output distribution through
the success test. -/
theorem inversionExperiment_eq_bind_map [BEq β] (sample : PMF α) (f : α → β)
    (inverter : β → PMF α) :
    inversionExperiment sample f inverter =
      sample.bind fun x => (inverter (f x)).map fun x' => f x' == f x :=
  rfl

/-- Randomness that the inverter samples independently of its challenge may be sampled before
the experiment. -/
theorem inversionExperiment_bind [BEq β] {Coins : Type*} (sample : PMF α) (f : α → β)
    (coins : PMF Coins) (inverter : Coins → β → PMF α) :
    inversionExperiment sample f (fun image => coins.bind fun seed => inverter seed image) =
      coins.bind fun seed => inversionExperiment sample f (inverter seed) := by
  simp only [inversionExperiment_eq_bind_map, PMF.map_bind]
  rw [PMF.bind_comm]

/-- An independent uniform hidden bit is guessed correctly with probability exactly one half,
whatever the predictor: with a fixed view `o`, the experiment's outcome is a fair bit. -/
theorem predictionExperiment_uniform_bit {O : Type} (o : O) (predictor : O → PMF Bool) :
    predictionExperiment ((PMF.uniformOfFintype Bool).map (o, ·)) Prod.fst Prod.snd predictor =
      PMF.uniformOfFintype Bool := by
  have hbit (guess : Bool) :
      (PMF.uniformOfFintype Bool).bind (fun bit => PMF.pure (guess == bit)) =
        PMF.uniformOfFintype Bool := by
    ext bit
    cases guess <;> cases bit <;>
      simp [PMF.bind_apply, tsum_fintype, PMF.uniformOfFintype_apply]
  simp only [predictionExperiment, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_map,
    Function.comp_def]
  rw [PMF.bind_comm]
  simp only [hbit, PMF.bind_const]

end Cslib.Crypto

namespace Cslib.ProbComp

open Cslib.Crypto

variable {α : Type} {β : Type}

/-- Evaluating the inversion experiment of programs gives the inversion experiment of their
distributions. -/
@[simp]
theorem eval_inversionExperiment [BEq β] (sample : ProbComp α) (f : α → β)
    (inverter : β → ProbComp α) :
    eval (inversionExperiment sample f inverter) =
      inversionExperiment (eval sample) f (fun image => eval (inverter image)) := by
  simp only [inversionExperiment, eval_bind, eval_pure]
  rfl

/-- Evaluating the prediction experiment of programs gives the prediction experiment of their
distributions. -/
@[simp]
theorem eval_predictionExperiment (sample : ProbComp α) (f : α → β) (h : α → Bool)
    (predictor : β → ProbComp Bool) :
    eval (predictionExperiment sample f h predictor) =
      predictionExperiment (eval sample) f h (fun image => eval (predictor image)) := by
  simp only [predictionExperiment, eval_bind, eval_pure]
  rfl

end Cslib.ProbComp
