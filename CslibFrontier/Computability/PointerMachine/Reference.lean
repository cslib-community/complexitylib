/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init

/-!
# Record identities

Private allocation labels and their elementary laws. Programs cannot inspect these labels.
-/

public section

namespace Cslib.PointerMachine

/-- A record identity. Its numerical representation is private to the allocator.
There are no arithmetic instances or machine instructions converting identities to data. -/
-- `structureInType` constructs public projection names and cannot resolve this private field.
-- The field stores a natural number, so this identity type is not propositional.
@[nolint structureInType]
structure NodeId where
  private mk ::
  private index : ℕ
  deriving DecidableEq

namespace NodeId
/-- Semantic allocation name, not a machine data operation. -/
def ofIndex (n : ℕ) : NodeId := ⟨n⟩
/-- Whether an identity is in the allocated prefix. -/
def Below (a : NodeId) (n : ℕ) : Prop := a.index < n
/-- Computable decision procedure for the allocator's membership predicate. -/
def decBelow (a : NodeId) (n : ℕ) : Decidable (a.Below n) :=
  inferInstanceAs (Decidable (a.index < n))
instance (a : NodeId) (n : ℕ) : Decidable (a.Below n) := decBelow a n
/-- Allocation labels are distinct. -/
theorem ofIndex_injective : Function.Injective ofIndex := by
  intro a b h
  exact congrArg NodeId.index h
/-- Characterize allocated allocation labels. -/
@[simp] theorem below_ofIndex (a n : ℕ) : (ofIndex a).Below n ↔ a < n := Iff.rfl
/-- Every identity has an allocator label; programs cannot obtain this label. -/
theorem exists_index (a : NodeId) : ∃ n, ofIndex n = a := ⟨a.index, rfl⟩
/-- Extending the allocated prefix adds exactly the fresh identity. -/
theorem below_succ (a : NodeId) (n : ℕ) :
    a.Below (n + 1) ↔ a.Below n ∨ a = ofIndex n := by
  cases a
  simp [Below, ofIndex]; omega
end NodeId


end Cslib.PointerMachine
