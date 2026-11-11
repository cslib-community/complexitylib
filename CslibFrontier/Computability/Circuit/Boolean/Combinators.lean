/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Substitution
public import CslibFrontier.Foundations.Data.BitString.Block
import CslibFrontier.Computability.Circuit.Boolean.Word

/-!
# Complexity of circuit combinators

Size bounds for building a De Morgan circuit from circuits for its parts, stated with `complexity`
in the style of `complexity_and_le`: a multiplexer, a finite conjunction, and reading one block of
a tuple of `BitString` blocks with the other blocks fixed to constants. The bounds are on size
only.

## Main definitions

* `blockInputs`: the substitution that feeds one block from the input and fixes the others.

## Main results

* `complexity_ite_le`: a multiplexer costs four gates beyond its arguments.
* `complexity_decide_forall_mem_le`: a conjunction of `#s` tests of cost `c` costs
  `#s (c + 1) + 1`.
* `complexity_single_block_le`: reading one block, with the others fixed, costs at most two gates
  more than reading the whole flat tuple.
-/

public section

namespace Cslib.Circuits.Boolean

open Finset

variable {n : ℕ}

/-- **Multiplexer**: choosing between two outputs by a third costs four gates beyond the three
outputs. -/
theorem complexity_ite_le (a f g : BooleanFunction n) :
    complexity interpretation (single fun x => if a x then f x else g x) ≤
      complexity interpretation (single a) + complexity interpretation (single f) +
        complexity interpretation (single g) + 4 := by
  have hmux : complexity interpretation
      (single fun y : Fin (1 + 1 + 1) → Bool => if y 0 then y 1 else y 2) ≤ 4 :=
    (Synthesis.mux (s := inputs (1 + 1 + 1)) ⟨0, rfl⟩ ⟨1, rfl⟩ ⟨2, rfl⟩).complexity_le
  have h := complexity_comp_le (I := interpretation)
    (fun x => Fin.append (Fin.append (single a x) (single f x)) (single g x))
    (single fun y : Fin (1 + 1 + 1) → Bool => if y 0 then y 1 else y 2)
  have heq : (single fun y : Fin (1 + 1 + 1) → Bool => if y 0 then y 1 else y 2) ∘
      (fun x => Fin.append (Fin.append (single a x) (single f x)) (single g x)) =
      single fun x => if a x then f x else g x := by
    funext x j
    rfl
  rw [heq] at h
  refine h.trans ?_
  have happ := (complexity_append_le (I := interpretation)
    (fun x => Fin.append (single a x) (single f x)) (single g)).trans
    (Nat.add_le_add_right (complexity_append_le (I := interpretation) (single a) (single f)) _)
  omega

/-- **Finite conjunction**: the conjunction of the tests `F i` over `i ∈ s`, each costing at most
`c` gates, costs at most `#s (c + 1) + 1` gates. The lemma takes the `Decidable` instance of the
caller's statement, such as `Nat.decidableForallFin` when `ι = Fin k`, so it applies directly. -/
theorem complexity_decide_forall_mem_le {ι : Type*} (s : Finset ι)
    (F : ι → BooleanFunction n) [dec : ∀ x, Decidable (∀ i ∈ s, F i x = true)] {c : ℕ}
    (hF : ∀ i ∈ s, complexity interpretation (single (F i)) ≤ c) :
    complexity interpretation (single fun x => decide (∀ i ∈ s, F i x = true)) ≤
      #s * (c + 1) + 1 := by
  classical
  obtain rfl : dec = fun x => Finset.decidableDforallFinset := Subsingleton.elim _ _
  induction s using Finset.induction_on with
  | empty =>
    simpa using (Synthesis.const (s := inputs n) true).complexity_le
  | insert i s hi ih =>
    have heq : (fun x => decide (∀ j ∈ insert i s, F j x = true)) =
        fun x => F i x && decide (∀ j ∈ s, F j x = true) := by
      funext x
      simp
    rw [heq, card_insert_of_notMem hi]
    refine (complexity_and_le _ _).trans ?_
    refine (Nat.add_le_add_right (Nat.add_le_add (hF i (mem_insert_self i s))
      (ih fun j hj => hF j (mem_insert_of_mem hj))) 1).trans (le_of_eq ?_)
    ring

/-- The substitution that feeds block `j` of a flat tuple of `k` blocks from the input and fixes
every other block to the corresponding bits of `z`. -/
def blockInputs {k : ℕ} (z : Fin k → BitString n) (j : Fin k) : Fin (k * n) → Fin n ⊕ Bool :=
  fun p => if (finProdFinEquiv.symm p).1 = j then .inl (finProdFinEquiv.symm p).2
    else .inr (z (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2)

/-- Substituting `blockInputs z j` and cutting into blocks puts `x` at block `j` of `z`. -/
@[simp] theorem block_substitute_blockInputs {k : ℕ} (z : Fin k → BitString n) (j : Fin k)
    (x : BitString n) :
    BitString.block (substitute (blockInputs z j) x) = Function.update z j x := by
  funext i a
  by_cases hij : i = j
  · subst hij
    simp [substitute, blockInputs]
  · simp [substitute, blockInputs, hij]

/-- **Reading one block**: fixing every block but block `j` to the bits of `z` costs at most two
more gates than reading all of them. -/
theorem complexity_single_block_le {k : ℕ} (G : (Fin k → BitString n) → Bool)
    (z : Fin k → BitString n) (j : Fin k) :
    complexity interpretation (single fun x : BitString n => G (Function.update z j x)) ≤
      complexity interpretation (single fun y : BitString (k * n) => G (BitString.block y)) +
        2 := by
  have h := complexity_substitute_le (blockInputs z j) fun y => G (BitString.block y)
  simp only [block_substitute_blockInputs] at h
  exact h

end Cslib.Circuits.Boolean
