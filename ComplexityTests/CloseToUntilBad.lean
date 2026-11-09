/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Game.CloseTo.UntilBad
import Complexity.Crypto.Protocols.SigmaProtocol.FiatShamir

/-!
# Agreement outside bad: sharp errors and actual cache programming

The Boolean source has a sharp error of one half after mapping into the infinite type `ℕ`.
The support-restricted zero case permits different kernels on impossible inputs. The final
client applies the shared law to the actual Fiat–Shamir signing program, including optional
responses and the final cache, versus fresh challenge programming.
-/

open Cslib Cslib.Interactive Cslib.Probability Cslib.Probability.PMF
open scoped ENNReal

example : CloseTo
    ((PMF.uniformOfFintype Bool).bind fun b => PMF.pure (if b then 1 else 0 : ℕ))
    ((PMF.uniformOfFintype Bool).bind fun _ => PMF.pure (0 : ℕ)) (1 / 2) := by
  have h := CloseTo.bind_of_eq_on (PMF.uniformOfFintype Bool)
    (fun b => PMF.pure (if b then 1 else 0 : ℕ)) (fun _ => PMF.pure 0) {true}
    (by intro b hb hbad; cases b <;> simp_all)
  simpa [PMF.toOuterMeasure_apply_singleton, PMF.uniformOfFintype_apply] using h

example :
    (PMF.toOuterMeasure
      ((PMF.uniformOfFintype Bool).bind fun b => PMF.pure (if b then 1 else 0 : ℕ)) {1}) = 1 / 2 ∧
    (PMF.toOuterMeasure
      ((PMF.uniformOfFintype Bool).bind fun _ => PMF.pure (0 : ℕ)) {1}) = 0 := by
  norm_num [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_pure_apply,
    tsum_bool, PMF.uniformOfFintype_apply]

example : CloseTo
    ((PMF.pure false).bind fun b => PMF.pure (if b then 1 else 0 : ℕ))
    ((PMF.pure false).bind fun _ => PMF.pure (0 : ℕ)) 0 := by
  have h := CloseTo.bind_of_eq_on (PMF.pure false)
    (fun b => PMF.pure (if b then 1 else 0 : ℕ)) (fun _ => PMF.pure 0) ∅ (by
      intro b hb _
      have heq : b = false := by simpa using hb
      subst b
      rfl)
  exact h.mono (by simp)

/-- Input-dependent continuation errors via `CloseTo.bind_right_tsum` give `1 / 4` (averaging `0`
on `false` and `1 / 2` on `true`), sharper than constant-error `CloseTo.bind_right` (`1 / 2`). -/
example : CloseTo
    ((PMF.uniformOfFintype Bool).bind fun b =>
      if b then PMF.uniformOfFintype Bool else PMF.pure false)
    ((PMF.uniformOfFintype Bool).bind fun _ => PMF.pure false) (1 / 4) := by
  refine (CloseTo.bind_right_tsum (err := fun b => if b then (1 / 2 : ℝ≥0∞) else 0)
    (PMF.uniformOfFintype Bool) fun b _ => ?_).mono ?_
  · cases b
    · simp
    · intro event
      simp only [↓reduceIte, PMF.toOuterMeasure_apply]
      by_cases h0 : false ∈ event <;> by_cases h1 : true ∈ event <;>
        norm_num [tsum_bool, PMF.uniformOfFintype_apply, h0, h1]
  · rw [tsum_bool]
    simp only [PMF.uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat, Bool.false_eq_true,
      ↓reduceIte, mul_zero, zero_add, one_div]
    rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    norm_num

open Cslib.Crypto.Protocols Cslib.Crypto.Protocols.SigmaProtocol Cslib.Crypto.Protocols.ROMSignature
open Cslib.OracleComp

example {X Y T C Z M : Type} [DecidableEq M] [DecidableEq T]
    [Fintype C] [Nonempty C]
    (P : SigmaProtocol X Y T C (Option Z)) (keyGen : PMF (X × Y))
    (x : X) (y : Y) (msg : M) (cache : List ((M × T) × C)) :
    CloseTo
      ((P.commit x y).bind fun coin =>
        (interpret (oracle C)
          ((fiatShamir (Function.Embedding.refl _) P keyGen).sign (x, y) msg coin)).run cache)
      ((P.commit x y).bind fun coin => (PMF.uniformOfFintype C).map fun c =>
        ((coin.1, P.respond x y coin.2 c), ((msg, coin.1), c) :: cache))
      ((P.commit x y).toOuterMeasure {coin | (cache.lookup (msg, coin.1)).isSome}) := by
  apply CloseTo.bind_of_eq_on
  intro coin _ hgood
  have hlookup : cache.lookup (msg, coin.1) = none := by
    cases hq : cache.lookup (msg, coin.1) with
    | none => rfl
    | some c => exact False.elim (hgood (by simp only [Set.mem_ofPred_eq, hq, Option.isSome_some]))
  change ((oracle C (msg, coin.1) cache).map
    (fun r => ((coin.1, P.respond x y coin.2 r.1), r.2))) = _
  rw [oracle, memoize_of_none _ _ _ hlookup]
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.map_bind, PMF.pure_map]
  rfl
