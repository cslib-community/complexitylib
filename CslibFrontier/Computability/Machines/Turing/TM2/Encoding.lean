/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.DPi
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
public import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Tactic.Linarith

/-!
# Binary encodings of Mathlib's stack-machine configurations

Each stack retains its own alphabet. Labels, registers and symbols use the existing finite-type
encoding; the stack family uses the dependent finite-table encoding. No tape direction or word
reversal is involved.

## Main definitions

* `Turing.TM2.encCfg`: encode a Mathlib TM2 configuration as a binary word.

## Main results

* `Turing.TM2.length_encCfg_le`: bounded stack lengths give a linear configuration-size bound.

## References

The configurations are those of `Mathlib.Computability.TuringMachine.StackTuringMachine`.
-/

@[expose] public section

namespace Turing.TM2

open MultiTapeTM
open scoped BigOperators

variable {K : Type} [Fintype K] {Γ : K → Type} {Λ σ : Type}
  [Finite Λ] [Finite σ] [∀ k, Finite (Γ k)]

/-- Store the label, registers and all stacks using the library's standard binary encodings. -/
noncomputable def encCfg : Cfg Γ Λ σ ↪ List Bool where
  toFun cfg := encPair (encFinite (Option Λ))
    (encPair (encFinite σ) (encDPi (fun k => encList (encFinite (Γ k)))))
    (cfg.l, cfg.var, cfg.stk)
  inj' := by
    rintro ⟨l, v, store⟩ ⟨l', v', store'⟩ h
    have hparts := (encPair _ _).injective h
    obtain ⟨rfl, hparts⟩ := Prod.mk.inj hparts
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hparts
    rfl

@[simp] theorem encCfg_apply (cfg : Cfg Γ Λ σ) :
    encCfg cfg = encPair (encFinite (Option Λ))
      (encPair (encFinite σ) (encDPi (fun k => encList (encFinite (Γ k)))))
      (cfg.l, cfg.var, cfg.stk) := rfl

/-- The constant depends only on the fixed stack alphabets, labels and registers. -/
theorem length_encCfg_le : ∃ C : ℕ, ∀ (cfg : Cfg Γ Λ σ) (bound : ℕ),
    (∀ k, (cfg.stk k).length ≤ bound) → (encCfg cfg).length ≤ C * (bound + 1) := by
  let alphabetSize := ∑ k : K, Nat.card (Γ k)
  let stackSize := 2 * alphabetSize + 1
  refine ⟨2 * Nat.card (Option Λ) + 2 * Nat.card σ +
    Fintype.card K * (2 * stackSize + 1) + 2, ?_⟩
  intro cfg bound hbound
  have hsymbol (k : K) (a : Γ k) : (encFinite (Γ k) a).length ≤ alphabetSize :=
    (length_encFinite_lt a).le.trans
      (Finset.single_le_sum (f := fun k => Nat.card (Γ k))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ k))
  have hstack (k : K) : (encList (encFinite (Γ k)) (cfg.stk k)).length ≤ bound * stackSize :=
    (length_encList_le _ _ (fun a _ => hsymbol k a)).trans
      (Nat.mul_le_mul_right stackSize (hbound k))
  have hstacks := length_encDPi_le (fun k => encList (encFinite (Γ k))) cfg.stk hstack
  have hl := (length_encFinite_lt cfg.l).le
  have hv := (length_encFinite_lt cfg.var).le
  simp only [encCfg_apply, length_encPair]
  nlinarith

end Turing.TM2
