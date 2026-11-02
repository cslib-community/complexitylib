/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Ary.Packed.QueryGateSpace
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.NatPow

/-!
# Charged initialization of the same-input interpolation loop

The alphabet size and coordinate count determine the assignment limit. This initialization
computes that power in native space, charging its possible binary output length in addition to
the supplied context, interpolation point and parameters. The limit is not a free input oracle.
-/

@[expose] public section

namespace Cslib.TreeEval.Ary.Packed.QueryGate

open Turing MultiTapeTM ComputableInSpace Reader

/-- Supplier context, modulus/alphabet/coordinate parameters, and the interpolation point. -/
abbrev Input (γ : Type) := γ × (ℕ × ℕ × ℕ) × List ℕ

/-- The original parameters without a precomputed assignment limit. -/
abbrev encInput {γ : Type} (encG : γ ↪ List Bool) : Input γ ↪ List Bool :=
  encPair encG (encPair encNat3 (encList encNat))

/-- Compute the full grid limit, retaining the supplied parameters. -/
def prepare {γ : Type} (q : Input γ) : Params γ :=
  (q.1, q.2.1, q.2.2, q.2.1.2.1 ^ q.2.1.2.2)

/-- Input storage and the possible binary size of the assignment limit. -/
def initializationSpace {γ : Type} (encG : γ ↪ List Bool) (q : Input γ) : ℕ :=
  (encInput encG q).length + (q.2.1.2.2 + 1) * (encNat q.2.1.2.1).length +
    (encNat q.2.1.2.2).length + 1

/-- The actual grid limit can be computed without a unary space charge for the alphabet size. -/
theorem prepare_inSpace {γ : Type} (encG : γ ↪ List Bool) :
    ComputableInSpace prepare (encInput encG) (encParams encG)
      (initializationSpace encG) := by
  have hin : (fun q : Input γ => (encInput encG q).length) ≼ initializationSpace encG :=
    .of_le fun q => by simp only [initializationSpace]; omega
  have hctx := (fst encG (encPair encNat3 (encList encNat))).weaken hin
  have hrest := (snd encG (encPair encNat3 (encList encNat))).weaken hin
  have hpsn := fst' hrest
  have hpoint := snd' hrest
  have hs := fst' (snd' hpsn)
  have hn := snd' (snd' hpsn)
  have hlimit := budget_natPow_variable hs hn
    (show (fun q : Input γ => (q.2.1.2.2 + 1) * (encNat q.2.1.2.1).length +
      (encNat q.2.1.2.2).length + 1) ≼ initializationSpace encG from
      .of_le fun q => by simp only [initializationSpace]; omega)
  exact (budget_prod hctx (budget_prod hpsn (budget_prod hpoint hlimit))).of_enc_eq
    fun _ => rfl

/-- Fresh counters are initialized after the charged power computation. -/
theorem initial_prepare_inSpace {γ : Type} (encG : γ ↪ List Bool) :
    ComputableInSpace (fun q : Input γ => initial (prepare q)) (encInput encG)
      (encState encG) (initializationSpace encG) := by
  have hin : (fun q : Input γ => (encInput encG q).length) ≼ initializationSpace encG :=
    .of_le fun q => by simp only [initializationSpace]; omega
  exact budget_prod (prepare_inSpace encG)
    (budget_prod (budget_const 0 hin) (budget_const 0 hin))

@[simp] theorem prepare_limit {γ : Type} (q : Input γ) :
    (prepare q).2.2.2 = (prepare q).2.1.2.1 ^ (prepare q).2.1.2.2 := rfl

end Cslib.TreeEval.Ary.Packed.QueryGate
