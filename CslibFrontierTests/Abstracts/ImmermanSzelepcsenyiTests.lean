/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract tests)

import CslibFrontierAbstracts.ImmermanSzelepcsenyiAbstract

/-! # Concrete clients of the public Immerman–Szelepcsényi abstract

The public classes are definitionally the library's native `NL`, `coNL`, `NSPACE` and `coNSPACE`,
and the general theorem applies at linear space. Directed non-reachability has both yes- and
no-instances: the single arc `1 → 0` does not lead from `0` to `1`, while the path `0 → 1 → 2`
leads from `0` to `2`. The encoding of the path is pinned bit by bit. Combining the public
theorems puts directed reachability itself in `NL`.
-/

namespace CslibFrontierTests.Abstracts.ImmermanSzelepcsenyiTests

open CslibFrontierAbstracts.ImmermanSzelepcsenyiAbstract

-- The public classes are the library's native classes.
example {α : Type} (enc : α ↪ List Bool) : NL enc = Cslib.Complexity.NL enc := rfl

example {α : Type} (enc : α ↪ List Bool) : coNL enc = Cslib.Complexity.coNL enc := rfl

example {α : Type} (enc : α ↪ List Bool) (s : ℕ → ℕ) :
    NSPACE enc s = Cslib.Complexity.NSPACE enc s := rfl

example {α : Type} (enc : α ↪ List Bool) (s : ℕ → ℕ) :
    coNSPACE enc s = Cslib.Complexity.coNSPACE enc s := rfl

-- The general theorem at linear space, a bound that is never logarithmic.
example {α : Type} (enc : α ↪ List Bool) : NSPACE enc id = coNSPACE enc id :=
  nspace_eq_conspace enc id Nat.log2_le_self

/-- The path `0 → 1 → 2`, from `0` to `2`. -/
def pathInstance : Instance := ⟨3, fun a b => decide ((a : ℕ) + 1 = b), 0, 2⟩

/-- The single arc `1 → 0`, from `0` to `1`. -/
def backInstance : Instance := ⟨2, fun a b => decide ((a : ℕ) = 1 ∧ (b : ℕ) = 0), 0, 1⟩

-- The encoding of the path: `1^3 0`, `1^0 0`, `1^2 0`, then the matrix row by row.
example : encode pathInstance =
    [true, true, true, false, false, true, true, false,
      false, true, false, false, false, true, false, false, false] := by
  decide

theorem pathInstance_mem : pathInstance ∈ STCON := by
  change Relation.ReflTransGen (fun a b : Fin 3 => decide ((a : ℕ) + 1 = b) = true) 0 2
  refine Relation.ReflTransGen.tail (b := 1) (.single ?_) ?_ <;> rfl

/-- The arc `1 → 0` reaches nothing from `0` but `0` itself. -/
theorem backInstance_mem_compl : backInstance ∈ STCONᶜ := by
  have key : ∀ x, Relation.ReflTransGen (fun a b => backInstance.adjacency a b = true)
      backInstance.source x → (x : ℕ) = 0 := by
    intro x hx
    induction hx with
    | refl => rfl
    | @tail y z _ hyz ih =>
      have hz := z.isLt
      change decide ((y : ℕ) = 1 ∧ (z : ℕ) = 0) = true at hyz
      simp only [decide_eq_true_eq] at hyz
      omega
  intro h
  exact absurd (key _ h) (by decide)

/-- Directed reachability is in `NL`: its complement is, and `NL = coNL`. -/
example : STCON ∈ NL encInstance := by
  rw [nl_eq_conl]
  exact stcon_compl_mem_nl

end CslibFrontierTests.Abstracts.ImmermanSzelepcsenyiTests
