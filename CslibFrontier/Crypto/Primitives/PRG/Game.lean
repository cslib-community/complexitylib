/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game
public import Cslib.Crypto.Primitives.PRG.Asymptotic
import CslibFrontier.Crypto.Negligible.Basic

/-!
# Finite PRGs in the common game calculus

The pinned finite PRG API measures advantage in the reals. The shared game API uses the same
quantity in the nonnegative reals. These bridges identify their concrete and asymptotic security
notions without changing the generator or introducing another definition of PRG security.

## Main results

* `Cslib.Crypto.PRG.Generator.advantage_eq_game`: identical advantage conventions.
* `Cslib.Crypto.PRG.Family.secure_iff_indistinguishable`: identical asymptotic security.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Section 3.1.
-/

@[expose] public section

namespace Cslib.Crypto.PRG

open scoped NNReal

/-- Finite PRGs and Boolean security games use the same distinguishing advantage. -/
theorem Generator.advantage_eq_game {Seed Output : Type*}
    [Fintype Seed] [Nonempty Seed] [Fintype Output] [Nonempty Output]
    (G : Generator Seed Output) (adversary : Adversary Output) :
    G.advantage adversary =
      (Game.advantage (G.realExperiment adversary) (idealExperiment adversary) : ℝ) := by
  rw [Game.coe_advantage]
  rfl

namespace Family

variable {Seed Output : ℕ → Type*}
variable [∀ n, Fintype (Seed n)] [∀ n, Nonempty (Seed n)]
variable [∀ n, Fintype (Output n)] [∀ n, Nonempty (Output n)]

/-- Finite-family PRG security is indistinguishability of its real and ideal games. -/
theorem secure_iff_indistinguishable (G : Family Seed Output)
    (Admissible : (∀ n, Adversary (Output n)) → Prop) :
    G.Secure Admissible ↔ Game.Indistinguishable
      (fun adversary n => (G n).realExperiment (adversary n))
      (fun adversary n => Generator.idealExperiment (adversary n)) Admissible := by
  simp only [Secure, Game.Indistinguishable, negligible_iff_coe, ← Generator.advantage_eq_game]

/-- Concrete finite-family PRG security is the same common game advantage bound. -/
theorem secureWithError_iff_indistinguishableWithError (G : Family Seed Output)
    (Admissible : (∀ n, Adversary (Output n)) → Prop) (ε : ℕ → ℝ≥0) :
    G.SecureWithError Admissible ε ↔ Game.IndistinguishableWithError
      (fun adversary n => (G n).realExperiment (adversary n))
      (fun adversary n => Generator.idealExperiment (adversary n)) Admissible ε := by
  simp only [SecureWithError, Game.IndistinguishableWithError, Generator.advantage_eq_game,
    NNReal.coe_le_coe]

end Family
end Cslib.Crypto.PRG
