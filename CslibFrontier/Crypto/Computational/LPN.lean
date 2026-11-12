/-
Copyright (c) 2026 Samuel Schlesinger, real-roots. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, real-roots
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.LWE.NormalForm
public import CslibFrontier.Probability.PMF.Coin
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.UnitInterval

/-!
# Learning Parity with Noise

LPN is LWE over `ZMod 2` with Bernoulli noise.

## Main definitions

* `Cslib.Crypto.SearchLPN`: Search LPN over `ZMod 2`.
* `Cslib.Crypto.DecisionLPN`: Decision LPN over `ZMod 2`.
* `Cslib.Crypto.SearchLPNErrorSecret`: Search LPN over `ZMod 2` with error secret.
* `Cslib.Crypto.DecisionLPNErrorSecret`: Decision LPN over `ZMod 2` with error secret.
-/

public section

namespace Cslib.Crypto

open Probability PrimeLWE PMF
open scoped unitInterval

/-- Bernoulli noise over `ZMod 2`. -/
noncomputable def bernoulliZMod2 (τ : I) : PMF (ZMod 2) :=
  (coin τ).map (fun b => if b then 1 else 0)

/-- Search LPN hypothesis. -/
def SearchLPN (n m : ℕ → ℕ) (τ : ℕ → I) : Prop :=
  PrimeLWE.SearchLWE n m (fun _ => 2) (fun sec => bernoulliZMod2 (τ sec))

/-- Decision LPN hypothesis. -/
def DecisionLPN (n m : ℕ → ℕ) (τ : ℕ → I) : Prop :=
  PrimeLWE.DecisionLWE n m (fun _ => 2) (fun sec => bernoulliZMod2 (τ sec))

/-- Search LPN with error secret. -/
def SearchLPNErrorSecret (n m : ℕ → ℕ) (τ : ℕ → I) : Prop :=
  PrimeLWE.SearchLWEErrorSecret n m (fun _ => 2) (fun sec => bernoulliZMod2 (τ sec))

/-- Decision LPN with error secret. -/
def DecisionLPNErrorSecret (n m : ℕ → ℕ) (τ : ℕ → I) : Prop :=
  PrimeLWE.DecisionLWEErrorSecret n m (fun _ => 2) (fun sec => bernoulliZMod2 (τ sec))

end Cslib.Crypto
