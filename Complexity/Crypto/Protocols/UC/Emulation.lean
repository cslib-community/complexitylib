/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Crypto.Negligible
public import Complexity.Crypto.Protocols.UC.Execution

/-!
# UC emulation against budgeted adversaries and environments

`UC.EmulatesWithin π φ g ε` says that protocol `π` UC-emulates protocol `φ` with simulator overhead
`g` and error `ε`, against interaction-bounded adversaries and environments: for every adversary
`A` whose activations make at most `pA.eval κ` calls there is a simulator `S` whose activations make
at most `pS.eval κ` calls, with `pS` bounded by `g` at `κ + pA.eval κ` (`UC.SimPolyBound`), such
that for every set of corrupted parties `C` and every environment `Z` making at most
`pZ.eval κ` calls, `Z` distinguishes `(π, A)` from `(φ, S)` with advantage at most
`ε pA pZ κ`. The error may depend on the security parameter and on the budgets of the adversary and
the environment, as in [Canetti2020]. `UC.RealizesWithin π F g ε` is emulation of the ideal
protocol of the functionality `F`.

The simulator is chosen after the adversary but before the corruption set and the environment, so
one simulator serves every environment. Emulation is reflexive with zero error
(`UC.EmulatesWithin.refl`) and transitive (`UC.EmulatesWithin.trans`): the simulators compose and
the errors add, the second error being evaluated at the budget `g₁₂.comp (X + pA)` of the
intermediate simulator, which requires that error to be monotone in the adversary's budget.

Budgets count calls (`Cslib.Crypto.Protocols.UC.Machine.IsBounded`); they bound interaction, not
running time.

`UC.Emulates π φ` is the asymptotic notion: every adversary with a polynomial budget has a
simulator with a polynomial budget such that, for every polynomial environment budget `pZ`, one
negligible function of `κ` bounds the advantage of every environment with budget `pZ`, uniformly in
the corrupted parties and the auxiliary input. `UC.EmulatesWithin π φ g ε` implies it whenever
every error `ε pA pZ` is negligible (`UC.EmulatesWithin.emulates`). It is reflexive and transitive,
and its transitivity needs no monotonicity, because the negligible bound for the second step is
chosen after the intermediate simulator. Since all participants are only call-bounded, these are
notions of security against interaction-bounded, computationally unbounded participants; UC
security against polynomial-time machines would additionally restrict them by machine
realizability.

## Main definitions

* `Cslib.Crypto.Protocols.UC.EmulatesWithin`: concrete UC emulation against budgeted adversaries and
  environments.
* `Cslib.Crypto.Protocols.UC.RealizesWithin`: concrete UC realization of an ideal functionality.
* `Cslib.Crypto.Protocols.UC.Emulates`, `Cslib.Crypto.Protocols.UC.Realizes`: UC emulation and
  realization with negligible error.

## Main results

* `Cslib.Crypto.Protocols.UC.EmulatesWithin.mono`: a larger error bound is still an error bound.
* `Cslib.Crypto.Protocols.UC.EmulatesWithin.refl`: every protocol emulates itself with zero error.
* `Cslib.Crypto.Protocols.UC.EmulatesWithin.trans`: emulation is transitive.
* `Cslib.Crypto.Protocols.UC.EmulatesWithin.emulates`: concrete emulation with negligible errors is
  emulation.
* `Cslib.Crypto.Protocols.UC.Emulates.refl`, `Cslib.Crypto.Protocols.UC.Emulates.trans`: emulation
  with negligible error is a preorder.

## References

* [R. Canetti, *Universally Composable Security*][Canetti2020], Section 4: UC emulation, and the
  transitivity of UC emulation. Here corruptions are static, and polynomial time is replaced by
  polynomial call budgets for adversaries, simulators and environments.
-/

public section

namespace Cslib.Crypto.Protocols.UC

open scoped NNReal

variable {n : ℕ} {In Out NetQ NetR NetQ₁ NetR₁ NetQ₂ NetR₂ NetQ₃ NetR₃ BackQ BackR : Type}

/-- Concrete UC emulation: protocol `π` emulates protocol `φ` with simulator overhead `g` and error
`ε`. Every adversary `A` with per-activation budget `pA` has a simulator `S` with per-activation
budget `pS ≤ g (κ + pA κ)` such that every environment with budget `pZ`, whatever the corrupted
parties, distinguishes `(π, A)` from `(φ, S)` with advantage at most `ε pA pZ κ`. -/
@[expose] def EmulatesWithin (π : Protocol n In Out NetQ₁ NetR₁) (φ : Protocol n In Out NetQ₂ NetR₂)
    (g : Polynomial ℕ) (ε : Polynomial ℕ → Polynomial ℕ → ℕ → ℝ≥0) : Prop :=
  ∀ (AdvQ AdvR : Type) (A : Adversary n AdvQ AdvR ((Fin n × In) ⊕ NetQ₁) (Option Out ⊕ NetR₁))
    (pA : Polynomial ℕ), A.PolyBounded pA →
    ∃ (S : Adversary n AdvQ AdvR ((Fin n × In) ⊕ NetQ₂) (Option Out ⊕ NetR₂)) (pS : Polynomial ℕ),
      S.PolyBounded pS ∧ SimPolyBound g pA pS ∧
        ∀ (C : Finset (Fin n)) (Z : Environment n In Out AdvQ AdvR) (pZ : Polynomial ℕ),
          Z.PolyBounded pZ → ∀ (κ : ℕ) (z : List Bool), advantage π φ A S C Z κ z ≤ ε pA pZ κ

/-- Concrete UC realization: protocol `π` emulates the ideal protocol of the functionality `F`. -/
abbrev RealizesWithin (π : Protocol n In Out NetQ NetR)
    (F : IdealFunctionality n In Out BackQ BackR)
    (g : Polynomial ℕ) (ε : Polynomial ℕ → Polynomial ℕ → ℕ → ℝ≥0) : Prop :=
  EmulatesWithin π F.toProtocol g ε

namespace EmulatesWithin

/-- A larger error bound is still an error bound. -/
theorem mono {π : Protocol n In Out NetQ₁ NetR₁} {φ : Protocol n In Out NetQ₂ NetR₂}
    {g : Polynomial ℕ} {ε ε' : Polynomial ℕ → Polynomial ℕ → ℕ → ℝ≥0}
    (h : EmulatesWithin π φ g ε) (hε : ∀ pA pZ κ, ε pA pZ κ ≤ ε' pA pZ κ) :
    EmulatesWithin π φ g ε' := by
  intro AdvQ AdvR A pA hA
  obtain ⟨S, pS, hS, hSg, hadv⟩ := h AdvQ AdvR A pA hA
  exact ⟨S, pS, hS, hSg, fun C Z pZ hZ κ z => (hadv C Z pZ hZ κ z).trans (hε pA pZ κ)⟩

/-- Every protocol emulates itself with zero error: the adversary is its own simulator. -/
theorem refl (π : Protocol n In Out NetQ NetR) : EmulatesWithin π π Polynomial.X (fun _ _ _ => 0) :=
  fun _ _ A pA hA => ⟨A, pA, hA, SimPolyBound.refl pA, fun C Z _ _ κ z => by simp⟩

/-- Transitivity of concrete UC emulation. If `π₁` emulates `π₂` with overhead `g₁₂` and error
`ε₁₂`, and `π₂` emulates `π₃` with overhead `g₂₃` and error `ε₂₃` monotone in the adversary's
budget, then `π₁` emulates `π₃`: the simulator for `π₂`'s simulator is a simulator for the original
adversary, and the errors add, the second at the intermediate simulator's budget bound. -/
theorem trans {π₁ : Protocol n In Out NetQ₁ NetR₁} {π₂ : Protocol n In Out NetQ₂ NetR₂}
    {π₃ : Protocol n In Out NetQ₃ NetR₃} {g₁₂ g₂₃ : Polynomial ℕ}
    {ε₁₂ ε₂₃ : Polynomial ℕ → Polynomial ℕ → ℕ → ℝ≥0}
    (h₁₂ : EmulatesWithin π₁ π₂ g₁₂ ε₁₂) (h₂₃ : EmulatesWithin π₂ π₃ g₂₃ ε₂₃)
    (hmono : ∀ p p' pZ κ, (∀ κ', p.eval κ' ≤ p'.eval κ') → ε₂₃ p pZ κ ≤ ε₂₃ p' pZ κ) :
    EmulatesWithin π₁ π₃ (g₂₃.comp (Polynomial.X + g₁₂))
      (fun pA pZ κ => ε₁₂ pA pZ κ + ε₂₃ (g₁₂.comp (Polynomial.X + pA)) pZ κ) := by
  intro AdvQ AdvR A pA hA
  obtain ⟨S₂, pS₂, hS₂, hS₂g, hadv₁₂⟩ := h₁₂ AdvQ AdvR A pA hA
  obtain ⟨S₃, pS₃, hS₃, hS₃g, hadv₂₃⟩ := h₂₃ AdvQ AdvR S₂ pS₂ hS₂
  refine ⟨S₃, pS₃, hS₃, hS₂g.trans hS₃g, fun C Z pZ hZ κ z => ?_⟩
  calc advantage π₁ π₃ A S₃ C Z κ z
      ≤ advantage π₁ π₂ A S₂ C Z κ z + advantage π₂ π₃ S₂ S₃ C Z κ z :=
        advantage_triangle π₁ π₂ π₃ A S₂ S₃ C Z κ z
    _ ≤ ε₁₂ pA pZ κ + ε₂₃ (g₁₂.comp (Polynomial.X + pA)) pZ κ :=
        add_le_add (hadv₁₂ C Z pZ hZ κ z)
          ((hadv₂₃ C Z pZ hZ κ z).trans (hmono _ _ pZ κ hS₂g.le_eval_comp))

end EmulatesWithin

/-! ### Negligible error -/

/-- UC emulation with negligible error: every adversary with a polynomial budget has a simulator
with a polynomial budget, such that for each polynomial environment budget one negligible function
bounds the advantage of every such environment, for all corrupted parties and auxiliary inputs. -/
@[expose] def Emulates (π : Protocol n In Out NetQ₁ NetR₁) (φ : Protocol n In Out NetQ₂ NetR₂) :
    Prop :=
  ∀ (AdvQ AdvR : Type) (A : Adversary n AdvQ AdvR ((Fin n × In) ⊕ NetQ₁) (Option Out ⊕ NetR₁))
    (pA : Polynomial ℕ), A.PolyBounded pA →
    ∃ (S : Adversary n AdvQ AdvR ((Fin n × In) ⊕ NetQ₂) (Option Out ⊕ NetR₂)) (pS : Polynomial ℕ),
      S.PolyBounded pS ∧
        ∀ pZ : Polynomial ℕ, ∃ ν : ℕ → ℝ≥0, Negligible ν ∧
          ∀ (C : Finset (Fin n)) (Z : Environment n In Out AdvQ AdvR),
            Z.PolyBounded pZ → ∀ (κ : ℕ) (z : List Bool), advantage π φ A S C Z κ z ≤ ν κ

/-- UC realization with negligible error: protocol `π` emulates the ideal protocol of `F`. -/
abbrev Realizes (π : Protocol n In Out NetQ NetR) (F : IdealFunctionality n In Out BackQ BackR) :
    Prop :=
  Emulates π F.toProtocol

/-- Concrete emulation whose errors are negligible for all budgets is emulation. -/
theorem EmulatesWithin.emulates {π : Protocol n In Out NetQ₁ NetR₁}
    {φ : Protocol n In Out NetQ₂ NetR₂} {g : Polynomial ℕ}
    {ε : Polynomial ℕ → Polynomial ℕ → ℕ → ℝ≥0} (h : EmulatesWithin π φ g ε)
    (hε : ∀ pA pZ, Negligible (ε pA pZ)) : Emulates π φ := by
  intro AdvQ AdvR A pA hA
  obtain ⟨S, pS, hS, _, hadv⟩ := h AdvQ AdvR A pA hA
  exact ⟨S, pS, hS, fun pZ => ⟨ε pA pZ, hε pA pZ, fun C Z hZ κ z => hadv C Z pZ hZ κ z⟩⟩

namespace Emulates

/-- Every protocol emulates itself. -/
theorem refl (π : Protocol n In Out NetQ NetR) : Emulates π π :=
  (EmulatesWithin.refl π).emulates fun _ _ => negligible_zero

/-- UC emulation is transitive. -/
theorem trans {π₁ : Protocol n In Out NetQ₁ NetR₁} {π₂ : Protocol n In Out NetQ₂ NetR₂}
    {π₃ : Protocol n In Out NetQ₃ NetR₃} (h₁₂ : Emulates π₁ π₂) (h₂₃ : Emulates π₂ π₃) :
    Emulates π₁ π₃ := by
  intro AdvQ AdvR A pA hA
  obtain ⟨S₂, pS₂, hS₂, hadv₁₂⟩ := h₁₂ AdvQ AdvR A pA hA
  obtain ⟨S₃, pS₃, hS₃, hadv₂₃⟩ := h₂₃ AdvQ AdvR S₂ pS₂ hS₂
  refine ⟨S₃, pS₃, hS₃, fun pZ => ?_⟩
  obtain ⟨ν₁₂, hν₁₂, h₁⟩ := hadv₁₂ pZ
  obtain ⟨ν₂₃, hν₂₃, h₂⟩ := hadv₂₃ pZ
  refine ⟨ν₁₂ + ν₂₃, hν₁₂.add hν₂₃, fun C Z hZ κ z => ?_⟩
  exact (advantage_triangle π₁ π₂ π₃ A S₂ S₃ C Z κ z).trans
    (add_le_add (h₁ C Z hZ κ z) (h₂ C Z hZ κ z))

end Emulates

end Cslib.Crypto.Protocols.UC
