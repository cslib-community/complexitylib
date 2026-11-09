/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (additions to `Cslib/Computability/Circuit/Complexity.lean`)

public import Cslib.Computability.Circuit.Complexity
public import Mathlib.Algebra.BigOperators.Fin

/-!
# More bounds on circuit complexity

Bounds on the complexity of single functions and of several functions computed side by side.

The coordinate projections cost nothing, and they are the only functions computed without gates,
since a circuit without gates outputs one of its inputs. Applying a unary or binary operation to
functions costs at most their complexities plus the complexity of the operation on fresh inputs:
compute the arguments, then feed them to a circuit for the operation. Computing `m` functions of
the same inputs at once costs at most the sum of their complexities: the circuits are placed next
to each other.

## Main results

* `Cslib.Circuits.Circuit.computesOn_single_iff`, `Cslib.Circuits.Circuit.computes_single_iff`:
  a one-output circuit computes `single f` when its output `0` agrees with `f`.
* `Cslib.Circuits.complexity_single_proj`, `Cslib.Circuits.one_le_complexity_single`: exactly the
  projections are computed without gates.
* `Cslib.Circuits.complexity_single_unary_le`, `Cslib.Circuits.complexity_single_binary_le`:
  applying an operation to functions costs at most their complexities plus its complexity on
  fresh inputs.
* `Cslib.Circuits.ecomplexity_pi_le`, `Cslib.Circuits.complexity_pi_le`: computing functions side
  by side costs at most the sum of their complexities.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib.Circuits

variable {σ : Signature} {U : Type*} {I : Interpretation σ U} {n : ℕ}

/-! ### Single functions -/

section Single

/-- A one-output circuit computes `single f` on `S` exactly when its output `0` agrees with `f`
on `S`. -/
theorem Circuit.computesOn_single_iff {c : Circuit σ n 1} {S : Set (Fin n → U)}
    {f : (Fin n → U) → U} :
    c.ComputesOn I S (single f) ↔ ∀ x ∈ S, c.eval I x 0 = f x :=
  ⟨fun h _ hx => congrFun (h hx) 0, fun h _ hx => funext fun i =>
    Subsingleton.elim i 0 ▸ h _ hx⟩

/-- A one-output circuit computes `single f` exactly when its output `0` agrees with `f` on
every input. -/
theorem Circuit.computes_single_iff {c : Circuit σ n 1} {f : (Fin n → U) → U} :
    c.Computes I (single f) ↔ ∀ x, c.eval I x 0 = f x :=
  ⟨fun h x => congrFun (h x) 0, fun h x => funext fun i => Subsingleton.elim i 0 ▸ h x⟩

variable [I.IsComplete]

/-- The coordinate projections cost no gates. -/
@[simp] theorem complexity_single_proj (i : Fin n) :
    complexity I (single fun x : Fin n → U => x i) = 0 :=
  complexity_wiring fun _ => i

/-- A function that is not a coordinate projection needs a gate: circuits without gates compute
projections. -/
theorem one_le_complexity_single {f : (Fin n → U) → U} (hf : ∀ i, f ≠ fun x => x i) :
    1 ≤ complexity I (single f) := by
  by_contra h
  obtain ⟨c, hc, hsize⟩ := exists_computes_size_eq_complexity (I := I) (f := single f)
  cases hw : c.outputs 0 with
  | input i =>
    refine hf i (funext fun x => ?_)
    have := Circuit.computes_single_iff.mp hc x
    simp only [Circuit.eval, Function.comp_apply, hw, Program.trace_input] at this
    exact this.symm
  | gate j => exact absurd j.isLt (by omega)

/-- Applying a unary operation to an output costs at most the complexity of the operation on one
input. -/
theorem complexity_single_unary_le (op : U → U) (f : (Fin n → U) → U) :
    complexity I (single fun x => op (f x)) ≤
      complexity I (single f) + complexity I (single fun y : Fin 1 → U => op (y 0)) := by
  have h := complexity_comp_le (I := I) (single f) (single fun y : Fin 1 → U => op (y 0))
  have heq : (single fun y : Fin 1 → U => op (y 0)) ∘ single f = single fun x => op (f x) := rfl
  rwa [heq] at h

/-- Combining two outputs by a binary operation costs at most the complexity of the operation on
two inputs. -/
theorem complexity_single_binary_le (op : U → U → U) (f g : (Fin n → U) → U) :
    complexity I (single fun x => op (f x) (g x)) ≤
      complexity I (single f) + complexity I (single g) +
        complexity I (single fun y : Fin 2 → U => op (y 0) (y 1)) := by
  have h := complexity_comp_le (I := I)
    (fun x => Fin.append (single f x) (single g x)) (single fun y : Fin 2 → U => op (y 0) (y 1))
  have heq : (single fun y : Fin 2 → U => op (y 0) (y 1)) ∘
      (fun x => Fin.append (single f x) (single g x)) = single fun x => op (f x) (g x) := by
    funext x j
    exact congrArg₂ op (Fin.append_left (single f x) (single g x) 0)
      (Fin.append_right (single f x) (single g x) 0)
  rw [heq] at h
  exact h.trans (Nat.add_le_add_right (complexity_append_le _ _) _)

end Single

/-! ### Several functions side by side -/

/-- Computing `m` functions side by side costs at most the sum of their complexities. -/
theorem ecomplexity_pi_le : ∀ {m : ℕ} (f : Fin m → (Fin n → U) → U),
    ecomplexity I (fun x i => f i x) ≤ ∑ i, ecomplexity I (single (f i))
  | 0, f => by
    have : (fun x (i : Fin 0) => f i x) = fun x => x ∘ (Fin.elim0 : Fin 0 → Fin n) :=
      funext fun _ => funext fun i => i.elim0
    rw [this, ecomplexity_wiring]
    exact bot_le
  | m + 1, f => by
    have : (fun x (i : Fin (m + 1)) => f i x) =
        fun x => Fin.append (fun i : Fin m => f i.castSucc x) (single (f (Fin.last m)) x) := by
      funext x i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simp [single, Fin.append, Fin.addCases, Fin.last]
      · simp [Fin.append, Fin.addCases]
    rw [this, Fin.sum_univ_castSucc]
    exact (ecomplexity_append_le _ _).trans (add_le_add (ecomplexity_pi_le _) le_rfl)

/-- Computing `m` functions side by side costs at most the sum of their complexities. -/
theorem complexity_pi_le [I.IsComplete] {m : ℕ} (f : Fin m → (Fin n → U) → U) :
    complexity I (fun x i => f i x) ≤ ∑ i, complexity I (single (f i)) := by
  have h := ecomplexity_pi_le (I := I) f
  simp only [← natCast_complexity] at h
  exact_mod_cast h

end Cslib.Circuits
