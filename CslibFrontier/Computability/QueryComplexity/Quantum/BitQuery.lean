/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Quantum.Composition

/-!
# Query algorithms with bit queries

The query model of `Cslib.Quantum.run` charges *phase queries*. A Hadamard gate on the control bit
before and after a phase query turns it into a *bit query* `|i, b, w⟩ ↦ |i, b ⊕ x_i, w⟩`
(`Cslib.Quantum.hadCtrl_phaseOracle_hadCtrl_eq_permute`). Many algorithms are naturally written with
bit queries: a preparation isometry, then `T` bit queries separated by input-independent
permutations of the basis, then a final isometry (`Cslib.Quantum.bitQueryAlg`). Between the
preparation and the final isometry such an algorithm is a classical reversible computation: its
state after the last query is the prepared state with the basis permuted by the composite
permutation `Cslib.Quantum.bitQueryPerm` (`Cslib.Quantum.run_bitQueryAlg`). Each bit query costs
exactly one phase query, so the query count is `T`.

This is the setting of the algorithms of Bernstein–Vazirani and Simon, whose preparation and final
isometries are Hadamard transforms (`Cslib.Quantum.hadamardTransform`). The formulation is original
to this library.

## Main definitions

* `Cslib.Quantum.bitQueryAlg`: an algorithm with `T` bit queries.
* `Cslib.Quantum.bitQueryPerm`: the basis permutation computed by its bit queries.

## Main results

* `Cslib.Quantum.run_bitQueryAlg`: the state after the last query.
-/

public section

namespace Cslib.Quantum

variable {N : ℕ} {W : Type*} [Fintype W]

/-- An algorithm with `T` **bit queries**: the preparation isometry `prep`, then the basis
permutations `π 0, …, π T` separated by bit queries, then the final isometry `post`. The `t`-th
isometry of the underlying phase-query algorithm is `H π_t H` with Hadamard gates `H` on the control
bit (`Cslib.Quantum.hadCtrl`), except that `prep` replaces the first and `post` the last `H`. -/
noncomputable def bitQueryAlg (T : ℕ) (π : ℕ → Equiv.Perm (Fin N × Bool × W))
    (prep post : State N W →ₗᵢ[ℂ] State N W) : ℕ → State N W →ₗᵢ[ℂ] State N W := fun t =>
  (if t = T then post else hadCtrl).comp
    ((permute (π t)).toLinearIsometry.comp (if t = 0 then prep else hadCtrl))

/-- The basis permutation computed by `Cslib.Quantum.bitQueryAlg` after `t` bit queries to `x`:
`π_t ∘ B_x ∘ π_{t-1} ∘ ⋯ ∘ B_x ∘ π_0` with the bit oracle `B_x` (`Cslib.Quantum.bitFlip`). -/
@[expose] def bitQueryPerm (π : ℕ → Equiv.Perm (Fin N × Bool × W)) (x : Fin N → Bool) :
    ℕ → Equiv.Perm (Fin N × Bool × W)
  | 0 => π 0
  | t + 1 => π (t + 1) * bitFlip x * bitQueryPerm π x t

omit [Fintype W] in
@[simp] theorem bitQueryPerm_zero (π : ℕ → Equiv.Perm (Fin N × Bool × W)) (x : Fin N → Bool) :
    bitQueryPerm π x 0 = π 0 := rfl

omit [Fintype W] in
@[simp] theorem bitQueryPerm_succ (π : ℕ → Equiv.Perm (Fin N × Bool × W)) (x : Fin N → Bool)
    (t : ℕ) : bitQueryPerm π x (t + 1) = π (t + 1) * bitFlip x * bitQueryPerm π x t := rfl

/-- Before the last query, the state is the permuted prepared state followed by a Hadamard gate. -/
private theorem run_bitQueryAlg_of_lt {T : ℕ} {π : ℕ → Equiv.Perm (Fin N × Bool × W)}
    {prep post : State N W →ₗᵢ[ℂ] State N W} {ψ₀ : State N W} {x : Fin N → Bool} {t : ℕ}
    (ht : t < T) :
    run (bitQueryAlg T π prep post) ψ₀ x t = hadCtrl (permute (bitQueryPerm π x t) (prep ψ₀)) := by
  induction t with
  | zero =>
    simp only [run, bitQueryAlg, (Nat.pos_iff_ne_zero.mp ht).symm, ite_true, ite_false,
      LinearIsometry.coe_comp, Function.comp_apply, LinearIsometryEquiv.coe_toLinearIsometry,
      bitQueryPerm_zero]
  | succ t ih =>
    simp only [run, bitQueryAlg, show t + 1 ≠ T by omega, Nat.succ_ne_zero t, ite_false,
      LinearIsometry.coe_comp, Function.comp_apply, LinearIsometryEquiv.coe_toLinearIsometry]
    rw [ih (by omega), hadCtrl_phaseOracle_hadCtrl_eq_permute, bitQueryPerm_succ, permute_mul,
      permute_mul]

/-- **A bit-query algorithm is a classical reversible computation between its first and last
isometries**: after its `T` queries, its state is `post` applied to the prepared state `prep ψ₀`
with the basis permuted by `Cslib.Quantum.bitQueryPerm`. -/
theorem run_bitQueryAlg (T : ℕ) (π : ℕ → Equiv.Perm (Fin N × Bool × W))
    (prep post : State N W →ₗᵢ[ℂ] State N W) (ψ₀ : State N W) (x : Fin N → Bool) :
    run (bitQueryAlg T π prep post) ψ₀ x T = post (permute (bitQueryPerm π x T) (prep ψ₀)) := by
  cases T with
  | zero =>
    simp only [run, bitQueryAlg, ite_true, LinearIsometry.coe_comp, Function.comp_apply,
      LinearIsometryEquiv.coe_toLinearIsometry, bitQueryPerm_zero]
  | succ T =>
    rw [run, run_bitQueryAlg_of_lt (Nat.lt_succ_self T)]
    simp only [bitQueryAlg, ite_true, Nat.succ_ne_zero T, ite_false, LinearIsometry.coe_comp,
      Function.comp_apply, LinearIsometryEquiv.coe_toLinearIsometry]
    rw [hadCtrl_phaseOracle_hadCtrl_eq_permute, bitQueryPerm_succ, permute_mul, permute_mul]

end Cslib.Quantum
