/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import CslibFrontier.Crypto.Protocols.UC.Commitment

/-!
# Tests for ideal UC bit commitment and the Canetti–Fischlin impossibility theorem

We verify non-vacuity and concrete behavior of `fcom` and `PlainCommitmentScheme`:
1. `trivialScheme` commits by sending the bit `b` in the clear (`commit _ b := pure (b, ())`,
   `verify _ c _ := pure (some c)`): it is deterministic (`IsPolyBounded 0 0`) and perfectly
   complete (`trivialScheme_perfectlyComplete`), so its honest UC execution (`C = ∅`) succeeds with
   probability `1`, yet by Canetti–Fischlin it cannot UC-realize `fcom`
   (`not_realizes_trivialScheme`) or emulate `fcom` within error `1 / 5`
   (`not_realizesWithin_trivialScheme`).
2. `oneTimePadScheme` masks the committed bit with a uniform Boolean pad `r` in the commit phase
   (`c = b ^^ r`, `o = r`) and unmasks `c ^^ o` on opening: its commit message alone is
   information-theoretically hiding, it is polynomial-call bounded (`IsPolyBounded 1 0`) and
   perfectly complete (`oneTimePadScheme_perfectlyComplete`), and by Canetti–Fischlin it still
   cannot UC-realize `fcom` (`not_realizes_oneTimePadScheme`).
-/

namespace CslibFrontierTests.Crypto.UCCommitment

open Polynomial
open Cslib Cslib.Crypto Cslib.Crypto.Protocols.UC
open scoped NNReal

/-- Deterministic plain-model commitment scheme that sends `b` as the commit message and `()` as the
opening message. -/
def trivialScheme : PlainCommitmentScheme Bool Unit where
  commit _ b := pure (b, ())
  verify _ c _ := pure (some c)

theorem trivialScheme_isPolyBounded : trivialScheme.IsPolyBounded 0 0 := by
  refine ⟨fun κ b => ?_, fun κ c o => ?_⟩
  · rw [Polynomial.eval_zero]
    exact OracleComp.IsCostBounded.pure _ 0
  · rw [Polynomial.eval_zero]
    exact OracleComp.IsCostBounded.pure _ 0

theorem trivialScheme_toProtocol_polyBounded : trivialScheme.toProtocol.PolyBounded (0 + 0) :=
  trivialScheme.toProtocol_polyBounded trivialScheme_isPolyBounded

@[simp] theorem acceptGame_trivialScheme (κ : ℕ) (b : Bool) :
    trivialScheme.acceptGame κ b = PMF.pure true := by
  simp [PlainCommitmentScheme.acceptGame, trivialScheme]

@[simp] theorem acceptProb_trivialScheme (κ : ℕ) (b : Bool) :
    trivialScheme.acceptProb κ b = 1 := by
  simp [PlainCommitmentScheme.acceptProb, Game.succProbability]

theorem trivialScheme_perfectlyComplete : trivialScheme.PerfectlyComplete :=
  acceptProb_trivialScheme

/-- Honest UC execution (`C = ∅`) of `trivialScheme` with `honestCommitEnv b` outputs `true` with
certainty. -/
example (b : Bool) (κ : ℕ) (z : List Bool) :
    (exec trivialScheme.toProtocol (dummyAdversary 2 _ _) ∅ (honestCommitEnv b) κ z).eval =
      PMF.pure true := by
  rw [eval_exec_honestCommitEnv, acceptGame_trivialScheme]

/-- Concrete Canetti–Fischlin bound for `trivialScheme`: for every pair of simulators `S₁, S₀`, the
four distinguishing advantages of `corruptReceiverEnv` and `corruptCommitterEnv` sum to at least
`1`. -/
theorem one_le_sum_advantage_trivialScheme
    (S₁ S₀ : Adversary 2
      ((Fin 2 × CommitmentInput) ⊕ PlainNetQ Bool Unit)
      (Option CommitmentOutput ⊕ PlainNetR Bool Unit)
      ((Fin 2 × CommitmentInput) ⊕ Unit)
      (Option CommitmentOutput ⊕ Option CommitmentOutput))
    (κ : ℕ) (z : List Bool) :
    1 ≤
      advantage trivialScheme.toProtocol fcom.toProtocol (dummyAdversary 2 _ _) S₁ {1}
        (corruptReceiverEnv trivialScheme false) κ z +
      advantage trivialScheme.toProtocol fcom.toProtocol (dummyAdversary 2 _ _) S₁ {1}
        (corruptReceiverEnv trivialScheme true) κ z +
      advantage trivialScheme.toProtocol fcom.toProtocol (dummyAdversary 2 _ _) S₀ {0}
        (corruptCommitterEnv S₁ false) κ z +
      advantage trivialScheme.toProtocol fcom.toProtocol (dummyAdversary 2 _ _) S₀ {0}
        (corruptCommitterEnv S₁ true) κ z := by
  have h := acceptProb_add_le_one_add_advantage trivialScheme S₁ S₀ κ z
  rw [acceptProb_trivialScheme, acceptProb_trivialScheme] at h
  rw [← NNReal.coe_le_coe] at h ⊢
  push_cast at h ⊢
  linarith

/-- Concrete impossibility: `trivialScheme` cannot UC-realize `fcom` within constant error `1 / 5`
for any simulator budget polynomial `g`. -/
theorem not_realizesWithin_trivialScheme (g : Polynomial ℕ) :
    ¬ RealizesWithin trivialScheme.toProtocol fcom g (fun _ _ _ => (1 / 5 : ℝ≥0)) := by
  refine not_realizesWithin_fcom (pV := 0) trivialScheme_isPolyBounded.2 g
    (fun _ _ _ => (1 / 5 : ℝ≥0)) 0 ?_
  rw [acceptProb_trivialScheme, acceptProb_trivialScheme]
  norm_num

/-- Asymptotic impossibility: `trivialScheme` does not UC-realize `fcom`. -/
theorem not_realizes_trivialScheme : ¬ Realizes trivialScheme.toProtocol fcom :=
  not_realizes_fcom_of_perfectlyComplete trivialScheme_isPolyBounded.2
    trivialScheme_perfectlyComplete

/-- Randomized one-time-pad commitment scheme: commits to `b` by sampling a uniform Boolean mask
`r ← unifFin 1` (`decide (r = 1)`) and sending `c = b ^^ mask` with opening `o = mask`. -/
def oneTimePadScheme : PlainCommitmentScheme Bool Bool where
  commit _ b := do
    let r ← ProbComp.unifFin 1
    let mask := decide (r.val = 1)
    return (b ^^ mask, mask)
  verify _ c o := pure (some (c ^^ o))

theorem oneTimePadScheme_isPolyBounded : oneTimePadScheme.IsPolyBounded 1 0 := by
  refine ⟨fun κ b => ?_, fun κ c o => ?_⟩
  · rw [Polynomial.eval_one]
    simp only [oneTimePadScheme, bind_pure_comp]
    exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (OracleComp.IsCostBounded.query 1)
  · rw [Polynomial.eval_zero]
    exact OracleComp.IsCostBounded.pure _ 0

theorem oneTimePadScheme_perfectlyComplete : oneTimePadScheme.PerfectlyComplete := fun κ b => by
  have hxor (r : Fin 2) :
      decide (some ((b ^^ decide (r.val = 1)) ^^ decide (r.val = 1)) = some b) = true := by
    cases b <;> fin_cases r <;> rfl
  simp only [PlainCommitmentScheme.acceptProb, PlainCommitmentScheme.acceptGame, oneTimePadScheme,
    bind_assoc, pure_bind, ProbComp.eval_bind, ProbComp.eval_pure, hxor, PMF.bind_const,
    Game.succProbability, PMF.pure_apply, ↓reduceIte, ENNReal.toNNReal_one]

/-- Even though `oneTimePadScheme`'s commit message `b ^^ mask` hides `b` perfectly, it still cannot
UC-realize `fcom` in the plain model. -/
theorem not_realizes_oneTimePadScheme : ¬ Realizes oneTimePadScheme.toProtocol fcom :=
  not_realizes_fcom_of_perfectlyComplete oneTimePadScheme_isPolyBounded.2
    oneTimePadScheme_perfectlyComplete

end CslibFrontierTests.Crypto.UCCommitment
