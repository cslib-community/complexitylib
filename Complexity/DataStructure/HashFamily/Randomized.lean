/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.HashFamily.Spec
public import Complexity.DataStructure.StateTransition.Randomized

/-!
# Resamplable hash families as randomized specifications

`HashFamily.seedSpec seedLaw eval` is the seed-level model of a resamplable hash family as a
`RandomizedSpec`. Its state is the current seed: `resample` draws a fresh seed from `seedLaw`, and
`eval u` answers `eval θ u` at the seed `θ`. On the oblivious client of an operation list it is
`evalOpsFromSeed` (`run_obliviousClient_seedSpec`), and after an initial resample it is `evalOps`
(`run_resample_obliviousClient_seedSpec`). An implementation that refines `seedSpec` by a
`RandomizedRefinement` therefore meets every contract proved for `evalOps`, such as
`kWiseSpec_contract_evalOps`, and its adaptive clients are described by `seedSpec` as well.

## Main definitions

* `Cslib.DataStructure.HashFamily.seedSpec`: the seed-level randomized specification.

## Main results

* `Cslib.DataStructure.HashFamily.run_obliviousClient_seedSpec`: oblivious transcripts from a
  fixed seed are `evalOpsFromSeed`.
* `Cslib.DataStructure.HashFamily.run_resample_bind_seedSpec`,
  `Cslib.DataStructure.HashFamily.run_resample_obliviousClient_seedSpec`: after an initial
  resample, a client runs from a fresh seed, and oblivious transcripts are `evalOps`.
-/

@[expose] public section

namespace Cslib.DataStructure.HashFamily

variable {Seed : Type} {U m : ℕ} (seedLaw : PMF Seed) (eval : Seed → Fin U → Fin m)

/-- The seed-level model of a resamplable hash family: the state is the current seed, `resample`
draws a fresh seed from `seedLaw`, and `eval u` answers `eval θ u` without changing the seed. -/
noncomputable abbrev seedSpec : RandomizedSpec where
  State := Seed
  Op := HashFamily.Op U
  Result := HashFamily.Result m
  law
    | .resample => fun _ => seedLaw.map fun θ => (PUnit.unit, θ)
    | .eval u => fun θ => PMF.pure (eval θ u, θ)

/-- Running the oblivious client of `ops` from the seed `θ` gives the transcript law
`evalOpsFromSeed`. -/
theorem run_obliviousClient_seedSpec (θ : Seed) (ops : List (HashFamily.Op U)) :
    ((seedSpec seedLaw eval).run ((seedSpec seedLaw eval).obliviousClient ops) θ).map Prod.fst =
      evalOpsFromSeed seedLaw eval θ ops := by
  induction ops generalizing θ with
  | nil => exact PMF.pure_map Prod.fst ([], θ)
  | cons o rest ih =>
    rw [RandomizedSpec.obliviousClient_cons, RandomizedSpec.run_liftBind]
    cases o with
    | eval u =>
      change ((PMF.pure (eval θ u, θ)).bind _).map Prod.fst = _
      rw [PMF.pure_bind]
      dsimp only
      rw [RandomizedSpec.run_map, PMF.map_comp, evalOpsFromSeed, ← ih θ, PMF.map_comp]
      rfl
    | resample =>
      change (((seedLaw.map fun θ' => (PUnit.unit, θ')).bind _).map Prod.fst) = _
      rw [PMF.bind_map, PMF.map_bind, evalOpsFromSeed]
      refine congrArg seedLaw.bind (funext fun θ' => ?_)
      rw [Function.comp_apply]
      dsimp only
      rw [RandomizedSpec.run_map, PMF.map_comp, ← ih θ', PMF.map_comp]
      rfl

/-- After an initial resample, a client runs from a fresh seed drawn from `seedLaw`. -/
theorem run_resample_bind_seedSpec {α : Type} (θ : Seed)
    (p : OracleComp (HashFamily.Result (U := U) m) α) :
    (seedSpec seedLaw eval).run (OracleComp.query (.resample : HashFamily.Op U) >>= fun _ => p) θ =
      seedLaw.bind fun θ' => (seedSpec seedLaw eval).run p θ' := by
  rw [RandomizedSpec.run_bind]
  change ((((seedLaw.map fun θ' => (PUnit.unit, θ')).bind fun x => PMF.pure x)).bind _) = _
  rw [PMF.bind_pure, PMF.bind_map]
  rfl

/-- After an initial resample, the transcript law of the oblivious client of `ops` is
`evalOps`. -/
theorem run_resample_obliviousClient_seedSpec (θ : Seed) (ops : List (HashFamily.Op U)) :
    ((seedSpec seedLaw eval).run (OracleComp.query (.resample : HashFamily.Op U) >>= fun _ =>
        (seedSpec seedLaw eval).obliviousClient ops) θ).map Prod.fst =
      evalOps seedLaw eval ops := by
  rw [run_resample_bind_seedSpec, PMF.map_bind, evalOps]
  exact congrArg seedLaw.bind (funext fun θ' => run_obliviousClient_seedSpec seedLaw eval θ' ops)

end Cslib.DataStructure.HashFamily
