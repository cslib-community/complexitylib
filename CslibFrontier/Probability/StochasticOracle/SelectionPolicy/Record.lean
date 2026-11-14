/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Basic
public import Mathlib.Basic.Real.Basic

/-!
# Oracle-policy call and halt records

A call record retains both the selected batch and its actual response. A halt
record supplies neither proposals nor resources. These decoders are shared by
finite-table and arbitrary discrete policy laws.
-/

public section
namespace Cslib.Probability.StochasticOracle.SelectionPolicy

/-- Full records retain the chosen batch and its response; `none` is a halt. -/
abbrev Record (B R : Type) := Option (B × R)

/-- Whether a record is an issued call, rather than a halt token. -/
@[expose] def issued {B R : Type} (_ : List (Record B R)) (x : Record B R) : Bool := x.isSome

/-- Decode proposals from an issued call; a halt supplies no proposals. -/
@[expose] def recordProposals {B R J : Type}
    (propose : List (Record B R) → B → R → List (Finset J))
    (h : List (Record B R)) : Record B R → List (Finset J)
  | none => []
  | some (b, x) => propose h b x

/-- Decode a call's actual resource charge; a halt has zero resource use. -/
@[expose] def recordResource {B R : Type}
    (resource : List (Record B R) → B → R → ℝ)
    (h : List (Record B R)) : Record B R → ℝ
  | none => 0
  | some (b, x) => resource h b x

@[simp] theorem recordProposals_none {B R J : Type}
    (propose : List (Record B R) → B → R → List (Finset J)) (h : List (Record B R)) :
    recordProposals propose h none = [] := rfl

@[simp] theorem recordProposals_some {B R J : Type}
    (propose : List (Record B R) → B → R → List (Finset J)) (h : List (Record B R))
    (b : B) (x : R) : recordProposals propose h (some (b, x)) = propose h b x := rfl

@[simp] theorem recordResource_none {B R : Type}
    (resource : List (Record B R) → B → R → ℝ) (h : List (Record B R)) :
    recordResource resource h none = 0 := rfl

@[simp] theorem recordResource_some {B R : Type}
    (resource : List (Record B R) → B → R → ℝ) (h : List (Record B R))
    (b : B) (x : R) : recordResource resource h (some (b, x)) = resource h b x := rfl

/-- Nonnegative call resources remain nonnegative after adding zero-cost halt records. -/
theorem recordResource_nonneg {B R : Type}
    (resource : List (Record B R) → B → R → ℝ)
    (hn : ∀ h b x, 0 ≤ resource h b x) (h : List (Record B R)) (x : Record B R) :
    0 ≤ recordResource resource h x := by
  cases x with
  | none => exact le_rfl
  | some z => exact hn h z.1 z.2

end Cslib.Probability.StochasticOracle.SelectionPolicy
