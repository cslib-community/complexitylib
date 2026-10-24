/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Formula
public import Complexity.Computability.Circuit.Boolean.Synthesis
public import Complexity.Foundations.Data.BitString.PartialAssignment
public import Mathlib.Basic.Real.Basic
import Complexity.Foundations.Data.BitString.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# Substituting variables and constants for inputs

A *substitution* `ρ : Fin N → Fin n ⊕ Bool` feeds every input of a Boolean function of `N`
variables from one of `n` new variables or from a constant; several inputs may receive the same
variable, so this is a projection in Valiant's sense rather than a restriction, which would leave
the remaining inputs free. A substitution does not make a function harder to compute: a circuit for
`f` with its inputs rewired, and two gates for the constants, computes `f ∘ ρ`.

The substitution `appendInputs r` fixes the last `p` inputs of a function of `n + p` variables to
the bits `r`: substituting it computes `x ↦ f (Fin.append x r)`; `prependInputs r` fixes the first
`p` inputs instead. A restriction (partial
assignment) is the substitution that replaces each bit by itself or by a constant
(`BitString.PartialAssignment.substitute_toSubstitution`).

Fixing inputs that a target function ignores keeps the agreement on average: if `g` agrees with a
function of its first `n` inputs on a `δ` fraction of all inputs, then for some fixing of the other
inputs the resulting function, two gates larger, agrees with it on a `δ` fraction of the inputs
(`Cslib.Circuits.Boolean.exists_complexity_le_of_agree_prefix`).

## Main definitions

* `Cslib.Circuits.Boolean.substitute`, `Cslib.Circuits.Boolean.appendInputs`,
  `Cslib.Circuits.Boolean.prependInputs`.
* `Cslib.Circuits.Boolean.substituteCircuit`: executable substitution with two shared constants.
* `Cslib.BitString.PartialAssignment.toSubstitution`: a partial assignment as a substitution.

## Main results

* `Cslib.Circuits.Boolean.complexity_substitute_le`: a substitution costs at most two gates.
* `Cslib.Circuits.Boolean.exists_complexity_le_of_agree_prefix`: fixing ignored inputs.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

variable {n N : ℕ}

/-- The inputs of a function of `N` variables fed by `ρ` from the variables `x`: input `j` is
`x i` when `ρ j = .inl i`, and the constant `b` when `ρ j = .inr b`. -/
def substitute (ρ : Fin N → Fin n ⊕ Bool) (x : Fin n → Bool) : Fin N → Bool :=
  fun j => (ρ j).elim x id

@[simp] theorem substitute_inl {ρ : Fin N → Fin n ⊕ Bool} {x : Fin n → Bool} {j : Fin N}
    {i : Fin n} (h : ρ j = .inl i) : substitute ρ x j = x i := by
  simp [substitute, h]

@[simp] theorem substitute_inr {ρ : Fin N → Fin n ⊕ Bool} {x : Fin n → Bool} {j : Fin N}
    {b : Bool} (h : ρ j = .inr b) : substitute ρ x j = b := by
  simp [substitute, h]

/-- Implement a substitution using one shared gate for each Boolean constant.
Both gates are included even when unused or when the output is empty. -/
def substituteCircuit {n N : ℕ} (ρ : Fin N → Fin n ⊕ Bool) : Circuit signature n N :=
  (Circuit.wiring signature (fun j => (ρ j).elim (Fin.castAdd 2)
    (fun b => Fin.natAdd n (if b then 1 else 0)))).comp
    ((Circuit.id signature n).append
      (Circuit.pi fun i : Fin 2 => (Formula.const (i == 1)).toCircuit))

/-- The shared-constant circuit implements its input substitution. -/
@[simp] theorem eval_substituteCircuit {n N : ℕ} (ρ : Fin N → Fin n ⊕ Bool) (x : BitString n) :
    (substituteCircuit ρ).eval interpretation x = substitute ρ x := by
  funext j
  cases h : ρ j with
  | inl i => simp [substituteCircuit, substitute, h]
  | inr b =>
    cases b <;> simp [substituteCircuit, substitute, h]

/-- Substitution charges each of the two shared constant gates once. -/
theorem cost_program_substituteCircuit {n N : ℕ} (ρ : Fin N → Fin n ⊕ Bool)
    (cost : signature.Op → ℕ) :
    (substituteCircuit ρ).program.cost cost = cost (.const false) + cost (.const true) := by
  unfold substituteCircuit
  erw [Circuit.cost_program_comp, Circuit.cost_program_wiring, Circuit.cost_program_append,
    Circuit.cost_program_pi]
  simp [Circuit.id, Formula.cost_toCircuit, Fin.sum_univ_two, Formula.const]

/-- The substitution circuit has exactly two gates, regardless of the output width. -/
@[simp] theorem size_substituteCircuit {n N : ℕ} (ρ : Fin N → Fin n ⊕ Bool) :
    (substituteCircuit ρ).size = 2 := by
  simpa only [Program.cost_const, one_mul] using
    cost_program_substituteCircuit ρ (fun _ => 1)


/-- The shared-constant substitution circuit has depth at most one. -/
theorem depth_substituteCircuit_le {n N : ℕ} (ρ : Fin N → Fin n ⊕ Bool) :
    (substituteCircuit ρ).depth ≤ 1 := by
  unfold substituteCircuit
  refine (Circuit.depth_comp_le _ _).trans ?_
  rw [Circuit.depth_wiring, Nat.zero_add]
  refine (Circuit.depth_append_le _ _).trans (max_le ?_ ?_)
  · simp [Circuit.id]
  · exact Circuit.depth_pi_le _ fun i =>
      (Formula.depth_toCircuit_le _).trans (by simp [Formula.const])

/-- A substitution costs at most two gates, one for each constant. -/
private theorem complexity_substitute_le_two (ρ : Fin N → Fin n ⊕ Bool) :
    complexity interpretation (substitute ρ) ≤ 2 := by
  simpa only [size_substituteCircuit] using
    complexity_le_of_computes (substituteCircuit ρ) (eval_substituteCircuit ρ)

/-- **Substitutions do not make functions harder.** Feeding the inputs of `f` from variables and
constants costs at most two more gates than `f`. -/
theorem complexity_substitute_le (ρ : Fin N → Fin n ⊕ Bool) (f : BooleanFunction N) :
    complexity interpretation (single fun x => f (substitute ρ x)) ≤
      complexity interpretation (single f) + 2 := by
  have h := complexity_comp_le (I := interpretation) (substitute ρ) (single f)
  rw [add_comm] at h
  exact h.trans (Nat.add_le_add_left (complexity_substitute_le_two ρ) _)

/-- The substitution fixing the last `p` inputs of a function of `n + p` variables to `r`. -/
def appendInputs {p : ℕ} (r : Fin p → Bool) : Fin (n + p) → Fin n ⊕ Bool :=
  Fin.append Sum.inl (Sum.inr ∘ r)

@[simp] theorem substitute_appendInputs {p : ℕ} (r : Fin p → Bool) (x : Fin n → Bool) :
    substitute (appendInputs r) x = Fin.append x r := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [substitute, appendInputs]

/-- The substitution fixing the first `p` inputs of a function of `p + n` variables to `r`. -/
def prependInputs {p : ℕ} (r : Fin p → Bool) : Fin (p + n) → Fin n ⊕ Bool :=
  Fin.append (Sum.inr ∘ r) Sum.inl

@[simp] theorem substitute_prependInputs {p : ℕ} (r : Fin p → Bool) (x : Fin n → Bool) :
    substitute (prependInputs r) x = Fin.append r x := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [substitute, prependInputs]

open Finset in
/-- **Fixing ignored inputs.** If `g` on `N` inputs agrees with a function `E` of its first `n`
inputs on more than `δ * 2 ^ N` inputs, then fixing the other `N - n` inputs suitably
(`appendInputs`) gives a function on `n` inputs, of complexity at most two more, that agrees with
`E` on more than `δ * 2 ^ n` inputs: some fixing does at least as well as the average. -/
theorem exists_complexity_le_of_agree_prefix (hle : n ≤ N) (E : BooleanFunction n)
    (g : BooleanFunction N) {δ : ℝ}
    (hagree : δ * 2 ^ N < #{y | g y = E fun i => y (Fin.castLE hle i)}) :
    ∃ C : BooleanFunction n, complexity interpretation (single C) ≤
      complexity interpretation (single g) + 2 ∧ δ * 2 ^ n < #{x | C x = E x} := by
  classical
  set p := N - n
  have hN : n + p = N := Nat.add_sub_cancel' hle
  -- fixing the last `p` inputs to `z`, through `appendInputs`
  let ρ : BitString p → Fin N → Fin n ⊕ Bool := fun z k => appendInputs z (Fin.cast hN.symm k)
  have hρ : ∀ z x, substitute (ρ z) x = fun k => Fin.append x z (Fin.cast hN.symm k) :=
    fun z x => funext fun k => congrFun (substitute_appendInputs z x) (Fin.cast hN.symm k)
  have hleft : ∀ (x : BitString n) (z : BitString p) (i : Fin n),
      Fin.append x z (Fin.cast hN.symm (Fin.castLE hle i)) = x i := fun x z i => by
    rw [show Fin.cast hN.symm (Fin.castLE hle i) = Fin.castAdd p i from Fin.ext rfl,
      Fin.append_left]
  -- the agreement splits over the fixings
  have hsplit : #{y | g y = E fun i => y (Fin.castLE hle i)} =
      ∑ z : BitString p, #{x | g (substitute (ρ z) x) = E x} := by
    rw [← card_sigma]
    refine card_nbij' (fun y => ⟨fun j => y (Fin.cast hN (Fin.natAdd n j)),
      fun i => y (Fin.castLE hle i)⟩) (fun q => fun k => Fin.append q.2 q.1 (Fin.cast hN.symm k))
      (fun y hy => ?_) (fun q hq => ?_) (fun y _ => ?_) (fun q _ => ?_)
    · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, coe_sigma,
        Set.mem_sigma_iff, mem_coe, hρ] at hy ⊢
      have hy' : (fun k => Fin.append (fun i => y (Fin.castLE hle i))
          (fun j => y (Fin.cast hN (Fin.natAdd n j))) (Fin.cast hN.symm k)) = y := by
        funext k
        obtain ⟨k', rfl⟩ : ∃ k', k = Fin.cast hN k' := ⟨Fin.cast hN.symm k, by simp⟩
        refine Fin.addCases (fun i => ?_) (fun j => ?_) k'
        · simp only [Fin.cast_cast, Fin.cast_eq_self, Fin.append_left]
          rfl
        · simp only [Fin.cast_cast, Fin.cast_eq_self, Fin.append_right]
      rw [hy']
      exact hy
    · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, coe_sigma,
        Set.mem_sigma_iff, mem_coe, hρ] at hq ⊢
      rw [show (fun i => Fin.append q.2 q.1 (Fin.cast hN.symm (Fin.castLE hle i))) = q.2 from
        funext (hleft q.2 q.1)]
      exact hq
    · funext k
      obtain ⟨k', rfl⟩ : ∃ k', k = Fin.cast hN k' := ⟨Fin.cast hN.symm k, by simp⟩
      refine Fin.addCases (fun i => ?_) (fun j => ?_) k'
      · simp only [Fin.cast_cast, Fin.cast_eq_self, Fin.append_left]
        rfl
      · simp only [Fin.cast_cast, Fin.cast_eq_self, Fin.append_right]
    · obtain ⟨z, x⟩ := q
      simp only [Sigma.mk.injEq]
      refine ⟨funext fun j => ?_, heq_of_eq (funext (hleft x z))⟩
      simp only [Fin.cast_cast, Fin.cast_eq_self, Fin.append_right]
  -- some fixing carries at least the average agreement
  have hex : ∃ z : BitString p, δ * 2 ^ n < #{x | g (substitute (ρ z) x) = E x} := by
    by_contra hall
    push Not at hall
    have hsum : (#{y | g y = E fun i => y (Fin.castLE hle i)} : ℝ) ≤
        ∑ _z : BitString p, δ * 2 ^ n := by
      rw [hsplit, Nat.cast_sum]
      exact sum_le_sum fun z _ => hall z
    rw [sum_const, card_univ, nsmul_eq_mul] at hsum
    have hcard : (Fintype.card (BitString p) : ℝ) * (δ * 2 ^ n) = δ * 2 ^ N := by
      rw [BitString.card, Nat.cast_pow, Nat.cast_ofNat]
      rw [mul_left_comm, ← pow_add, ← hN, add_comm]
    linarith
  obtain ⟨z, hz⟩ := hex
  exact ⟨fun x => g (substitute (ρ z) x), complexity_substitute_le (ρ z) g, hz⟩


end Cslib.Circuits.Boolean

namespace Cslib.BitString.PartialAssignment

open Circuits.Boolean

variable {n : ℕ}

/-- The substitution replacing each fixed bit by its value and each free bit by itself. -/
def toSubstitution (ρ : PartialAssignment (Fin n)) : Fin n → Fin n ⊕ Bool :=
  fun i => (ρ i).elim (.inl i) .inr

/-- Restricting is substituting constants for the fixed bits. -/
theorem substitute_toSubstitution (ρ : PartialAssignment (Fin n)) :
    substitute ρ.toSubstitution = ρ.fill := by
  funext x i
  cases h : ρ i <;> simp [toSubstitution, fill, h]

end Cslib.BitString.PartialAssignment
