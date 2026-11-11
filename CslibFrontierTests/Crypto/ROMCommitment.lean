/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Protocols.Commitment.RandomOracle
import CslibFrontier.Crypto.Negligible.Basic

/-!
# Tests for random-oracle hash commitments

Concrete and asymptotic checks for `Cslib.Crypto.Protocols.ROMCommitment`:
* Deterministic random-oracle handler evaluation and `eval_verify_commitOracle` completeness.
* Concrete two-stage `HidingAdversary` bound (`advantage_hidingGame_le`) and asymptotic
  `Negligible` hiding (`negligible_advantage_hidingGame`) for `2 ^ n ≤ |R n|`.
* Deterministic-salt (`R = Unit`) hiding attack (`deterministicHidingAttack`) achieving exact
  advantage `1 - |Digest|⁻¹` (`3 / 4` for `Fin 4`).
* Concrete query-bounded collision bound (`succProbability_bindingGame_le`) and asymptotic
  `Negligible` binding (`negligible_succProbability_bindingGame`) for `2 ^ n ≤ |Digest n|`.
-/

namespace CslibFrontierTests.Crypto.ROMCommitment

open Cslib Cslib.Crypto Cslib.Crypto.Protocols.ROMCommitment Cslib.Probability
open scoped NNReal

/-! ### 1. Completeness and deterministic ROM handler checks -/

private def detHashHandler {M R Digest : Type} (H : M → R → Digest) :
    (q : M × R) → Id Digest
  | (m, r) => H m r

example :
    (OracleComp.interpret (detHashHandler (fun m r : ℕ => (m + r) % 7)) do
      let c ← commitOracle 3 5
      return (c, ← verify 3 c 5, ← verify 4 c 5)).run = (1, true, false) := rfl

example (m : Fin 4) (r : Fin 8) (cache : List ((Fin 4 × Fin 8) × Fin 16)) :
    (ProbOracleComp.runWith (oracle (Fin 4) (Fin 8) (Fin 16))
      (do
        let c ← OracleComp.liftRight (spec₁ := unifSpec) (commitOracle m r)
        OracleComp.liftRight (spec₁ := unifSpec) (verify m c r))
      cache).map Prod.fst = PMF.pure true :=
  eval_verify_commitOracle m r cache

/-! ### 2. Concrete and asymptotic hiding (`hidingGame`) -/

/-- A one-query two-stage adversary guessing whether the challenge digest matches `H(m₀, r₀)`. -/
def oneQueryHidingAdv (M R Digest : Type) [DecidableEq Digest] (m₀ m₁ : M) (r₀ : R) :
    HidingAdversary M R Digest Digest where
  choose := do
    let d ← ProbOracleComp.query (spec := HashSpec M R Digest) (m₀, r₀)
    return ((m₀, m₁), d)
  guess st c := pure (st == c)

theorem isQueryBounded_oneQueryHidingAdv (M R Digest : Type) [DecidableEq Digest]
    (m₀ m₁ : M) (r₀ : R) :
    (oneQueryHidingAdv M R Digest m₀ m₁ r₀).choose.IsQueryBounded 1 ∧
      ∀ st c, ((oneQueryHidingAdv M R Digest m₀ m₁ r₀).guess st c).IsQueryBounded 0 := by
  refine ⟨?_, fun _ _ => OracleComp.IsCostBounded.pure _ 0⟩
  exact ((ProbOracleComp.IsQueryBounded.query (spec := HashSpec M R Digest) (m₀, r₀)).bind
    fun d => OracleComp.IsCostBounded.pure ((m₀, m₁), d) 0).mono (by omega)

example :
    Game.advantage
      (hidingGame (oneQueryHidingAdv (Fin 4) (Fin 16) (Fin 16) 0 1 0) false)
      (hidingGame (oneQueryHidingAdv (Fin 4) (Fin 16) (Fin 16) 0 1 0) true) ≤ 1 / 8 := by
  have h := isQueryBounded_oneQueryHidingAdv (Fin 4) (Fin 16) (Fin 16) 0 1 0
  have hle := advantage_hidingGame_le
    (oneQueryHidingAdv (Fin 4) (Fin 16) (Fin 16) 0 1 0) h.1 h.2
  norm_num [Fintype.card_fin] at hle ⊢
  exact hle

example :
    Negligible fun n =>
      Game.advantage
        (hidingGame (oneQueryHidingAdv (Fin (2 ^ n)) (Fin (2 ^ n)) (Fin (2 ^ n))
          ⟨0, Nat.two_pow_pos n⟩ ⟨0, Nat.two_pow_pos n⟩ ⟨0, Nat.two_pow_pos n⟩) false)
        (hidingGame (oneQueryHidingAdv (Fin (2 ^ n)) (Fin (2 ^ n)) (Fin (2 ^ n))
          ⟨0, Nat.two_pow_pos n⟩ ⟨0, Nat.two_pow_pos n⟩ ⟨0, Nat.two_pow_pos n⟩) true) := by
  haveI (n : ℕ) : Nonempty (Fin (2 ^ n)) := ⟨⟨0, Nat.two_pow_pos n⟩⟩
  refine negligible_advantage_hidingGame
    (fun n => oneQueryHidingAdv (Fin (2 ^ n)) (Fin (2 ^ n)) (Fin (2 ^ n))
      ⟨0, Nat.two_pow_pos n⟩ ⟨0, Nat.two_pow_pos n⟩ ⟨0, Nat.two_pow_pos n⟩)
    (q₁ := fun _ => 1) (q₂ := fun _ => 0)
    (fun n => (isQueryBounded_oneQueryHidingAdv _ _ _ _ _ _).1)
    (fun n st c => (isQueryBounded_oneQueryHidingAdv _ _ _ _ _ _).2 st c)
    (PolynomiallyBounded.const 1) (PolynomiallyBounded.const 0)
    (fun n => by simp)

/-! ### 3. Deterministic-salt hiding counterexample (`R = Unit`) -/

example :
    (deterministicHidingAttack (Fin 2) (Fin 4) 0 1).choose.IsQueryBounded 0 ∧
      ∀ st c, ((deterministicHidingAttack (Fin 2) (Fin 4) 0 1).guess st c).IsQueryBounded 1 :=
  isQueryBounded_deterministicHidingAttack (Fin 2) (Fin 4) 0 1

example :
    Game.advantage
      (hidingGame (deterministicHidingAttack (Fin 2) (Fin 4) 0 1) false)
      (hidingGame (deterministicHidingAttack (Fin 2) (Fin 4) 0 1) true) = 3 / 4 := by
  rw [advantage_hidingGame_deterministicHidingAttack (by decide : (0 : Fin 2) ≠ 1)]
  norm_num [Fintype.card_fin]

/-! ### 4. Concrete and asymptotic binding (`bindingGame`) -/

/-- A one-query binding forger hashing `(m₀, r₀)` and returning the same digest for `(m₀, r₀)`
and `(m₁, r₀)`. -/
def oneQueryBindingForger (M R Digest : Type) (m₀ m₁ : M) (r₀ : R) :
    ProbOracleComp (HashSpec M R Digest) (Digest × (M × R) × (M × R)) := do
  let c ← ProbOracleComp.query (spec := HashSpec M R Digest) (m₀, r₀)
  return (c, (m₀, r₀), (m₁, r₀))

theorem isQueryBounded_oneQueryBindingForger (M R Digest : Type) (m₀ m₁ : M) (r₀ : R) :
    (oneQueryBindingForger M R Digest m₀ m₁ r₀).IsQueryBounded 1 :=
  ((ProbOracleComp.IsQueryBounded.query (spec := HashSpec M R Digest) (m₀, r₀)).bind
    fun _ => OracleComp.IsCostBounded.pure _ 0).mono (by omega)

example :
    Game.succProbability
      (bindingGame (oneQueryBindingForger (Fin 4) (Fin 4) (Fin 16) 0 1 0)) ≤ 3 / 16 := by
  have hle := succProbability_bindingGame_le
    (oneQueryBindingForger (Fin 4) (Fin 4) (Fin 16) 0 1 0)
    (isQueryBounded_oneQueryBindingForger (Fin 4) (Fin 4) (Fin 16) 0 1 0)
  norm_num [Fintype.card_fin] at hle ⊢
  exact hle

example :
    Negligible fun n =>
      Game.succProbability
        (bindingGame (oneQueryBindingForger (Fin (2 ^ n)) (Fin (2 ^ n)) (Fin (2 ^ n))
          ⟨0, Nat.two_pow_pos n⟩ ⟨0, Nat.two_pow_pos n⟩ ⟨0, Nat.two_pow_pos n⟩)) := by
  haveI (n : ℕ) : Nonempty (Fin (2 ^ n)) := ⟨⟨0, Nat.two_pow_pos n⟩⟩
  exact negligible_succProbability_bindingGame
    (fun n => oneQueryBindingForger (Fin (2 ^ n)) (Fin (2 ^ n)) (Fin (2 ^ n))
      ⟨0, Nat.two_pow_pos n⟩ ⟨0, Nat.two_pow_pos n⟩ ⟨0, Nat.two_pow_pos n⟩)
    (q := fun _ => 1)
    (fun n => isQueryBounded_oneQueryBindingForger _ _ _ _ _ _)
    (PolynomiallyBounded.const 1)
    (fun n => by simp)

end CslibFrontierTests.Crypto.ROMCommitment
