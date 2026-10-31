/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.QueryComplexity.Quantum.Search

/-!
# Classically controlled query algorithms

A query algorithm (`Cslib.Quantum.run`) is a deterministic sequence of isometries, but its workspace
and initial state are arbitrary, so classical randomness fits inside it. Let the workspace be
`W × G`, where `G` is a *classical register* that the algorithm reads but never changes. Each
isometry `controlled V` applies `V g` to the *slice* `ψ_g` of the state where the register holds
`g` (`Cslib.Quantum.slice`, `Cslib.Quantum.controlled`). The oracle never touches the workspace,
so the slices evolve separately: the slice at `g` of the final state is the final state of the
algorithm `V g` started from the slice at `g` of the initial state (`Cslib.Quantum.slice_run`).
Measuring adds up the slices (`Cslib.Quantum.measureProb_eq_sum_slice`,
`Cslib.Quantum.regProb_eq_sum_slice`).

So preparing the register in the superposition `∑_g √(p_g) |g⟩` and running `V g` on the slice at
`g` makes every outcome probability the average, with weights `p_g`, of the outcome probabilities
of the algorithms `V g`: a *classical mixture* of query algorithms, with the classical coin
replaced by its purification.

To let algorithms with different numbers of queries share one query count, an algorithm whose
state after `k` queries has control bit `1` can be *parked* (`Cslib.Quantum.park`): after its
`k`-th query, the control bit is flipped to `0` (`Cslib.Quantum.flipCtrl`), where the controlled
oracle acts as the identity, and nothing happens afterwards (`Cslib.Quantum.run_park`). Parking
does not change the probability of any query index.

## Main definitions

* `Cslib.Quantum.slice`: the slice of a state at a value of a classical register.
* `Cslib.Quantum.controlled`: the isometry applying `V g` to the slice at `g`.
* `Cslib.Quantum.permute`: the isometry permuting the basis states.
* `Cslib.Quantum.flipCtrl`: the flip of the control bit.
* `Cslib.Quantum.park`: an algorithm stopped after `k` queries by flipping its control bit.

## Main results

* `Cslib.Quantum.slice_run`: classically controlled algorithms run slice by slice.
* `Cslib.Quantum.measureProb_eq_sum_slice`: outcome probabilities add up over the slices.
* `Cslib.Quantum.run_park`: a parked algorithm keeps its state after `k` queries.
-/

@[expose] public section

namespace Cslib.Quantum

open Finset

variable {N : ℕ} {W G : Type*}

/-! ### Slices and classical control -/

/-- The slice `ψ_g` of a state at the value `g` of a classical register `G` in the workspace: the
amplitudes of the basis states whose register holds `g`. -/
def slice (g : G) (ψ : State N (W × G)) : State N W :=
  WithLp.toLp 2 fun p => ψ.ofLp (p.1, p.2.1, p.2.2, g)

@[simp] theorem slice_apply (g : G) (ψ : State N (W × G)) (p : Fin N × Bool × W) :
    (slice g ψ).ofLp p = ψ.ofLp (p.1, p.2.1, p.2.2, g) := rfl

@[simp] theorem slice_add (g : G) (ψ φ : State N (W × G)) :
    slice g (ψ + φ) = slice g ψ + slice g φ := rfl

@[simp] theorem slice_smul (g : G) (c : ℂ) (ψ : State N (W × G)) :
    slice g (c • ψ) = c • slice g ψ := rfl

/-- The basis states of `Fin N × Bool × (W × G)`, sorted by the value of the register `G`. -/
private def splitEquiv : Fin N × Bool × (W × G) ≃ G × (Fin N × Bool × W) where
  toFun p := (p.2.2.2, p.1, p.2.1, p.2.2.1)
  invFun q := (q.2.1, q.2.2.1, q.2.2.2, q.1)
  left_inv _ := rfl
  right_inv _ := rfl

variable [Fintype W] [Fintype G]

/-- A sum over the basis states is the sum, over the values `g` of the register, of the sums over
the basis states whose register holds `g`. -/
private theorem sum_split {M : Type*} [AddCommMonoid M] (f : Fin N × Bool × (W × G) → M) :
    ∑ p, f p = ∑ g, ∑ q : Fin N × Bool × W, f (q.1, q.2.1, q.2.2, g) := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv splitEquiv _ _ fun _ => rfl

/-- The squared norm of a state is the sum of the squared norms of its slices. -/
theorem norm_sq_eq_sum_slice (ψ : State N (W × G)) : ‖ψ‖ ^ 2 = ∑ g, ‖slice g ψ‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, slice_apply]
  exact sum_split _

/-- The isometry **controlled by a classical register**: it applies `V g` to the slice at `g`. -/
noncomputable def controlled (V : G → State N W →ₗᵢ[ℂ] State N W) :
    State N (W × G) →ₗᵢ[ℂ] State N (W × G) where
  toFun ψ := WithLp.toLp 2 fun p => (V p.2.2.2 (slice p.2.2.2 ψ)).ofLp (p.1, p.2.1, p.2.2.1)
  map_add' ψ φ := by
    ext p
    simp
  map_smul' c ψ := by
    ext p
    simp
  norm_map' ψ := by
    have h : ‖(WithLp.toLp 2 fun p : Fin N × Bool × (W × G) =>
        (V p.2.2.2 (slice p.2.2.2 ψ)).ofLp (p.1, p.2.1, p.2.2.1) : State N (W × G))‖ ^ 2 =
          ‖ψ‖ ^ 2 := by
      rw [norm_sq_eq_sum_slice, norm_sq_eq_sum_slice]
      exact sum_congr rfl fun g _ => by rw [← (V g).norm_map (slice g ψ)]; rfl
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

@[simp] theorem slice_controlled (V : G → State N W →ₗᵢ[ℂ] State N W) (g : G)
    (ψ : State N (W × G)) : slice g (controlled V ψ) = V g (slice g ψ) := rfl

omit [Fintype W] [Fintype G] in
@[simp] theorem slice_phaseOracle (x : Fin N → Bool) (g : G) (ψ : State N (W × G)) :
    slice g (phaseOracle x ψ) = phaseOracle x (slice g ψ) := rfl

/-- **Classically controlled algorithms run slice by slice**: if the isometry after `s` queries
applies `V g s` to the slice at `g`, then the slice at `g` of the state after `t` queries is the
state after `t` queries of the algorithm `V g` started from the slice at `g`. -/
theorem slice_run (V : G → ℕ → State N W →ₗᵢ[ℂ] State N W) (ψ₀ : State N (W × G))
    (x : Fin N → Bool) (g : G) (t : ℕ) :
    slice g (run (fun s => controlled fun h => V h s) ψ₀ x t) = run (V g) (slice g ψ₀) x t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [run, slice_controlled, slice_phaseOracle, ih]

/-- **Outcome probabilities add up over the slices**: the probability of an outcome set `S` is the
sum over `g` of the probability, in the slice at `g`, of the outcomes whose extension by `g` lies
in `S`. -/
theorem measureProb_eq_sum_slice [DecidableEq W] [DecidableEq G] (ψ : State N (W × G))
    (S : Finset (Fin N × Bool × (W × G))) :
    measureProb ψ S =
      ∑ g, measureProb (slice g ψ) (univ.filter fun q => (q.1, q.2.1, q.2.2, g) ∈ S) := by
  simp only [measureProb, sum_filter, slice_apply]
  rw [← sum_split (fun p => if p ∈ S then ‖ψ.ofLp p‖ ^ 2 else 0), ← sum_filter,
    filter_mem_eq_inter, univ_inter]

/-- The probability of measuring query index `i` is the sum over the slices. -/
theorem regProb_eq_sum_slice (ψ : State N (W × G)) (i : Fin N) :
    regProb ψ i = ∑ g, regProb (slice g ψ) i := by
  classical
  rw [regProb, measureProb_eq_sum_slice]
  exact sum_congr rfl fun g _ => congrArg _ (by ext q; simp)

/-! ### Scaling -/

omit [Fintype G] in
/-- Query algorithms are linear in their initial state. -/
theorem run_smul (U : ℕ → State N W →ₗᵢ[ℂ] State N W) (c : ℂ) (ψ₀ : State N W)
    (x : Fin N → Bool) (t : ℕ) : run U (c • ψ₀) x t = c • run U ψ₀ x t := by
  induction t with
  | zero => exact map_smul (U 0) c ψ₀
  | succ t ih => simp only [run, ih, map_smul]

omit [Fintype W] [Fintype G] in
theorem measureProb_smul {ι : Type*} (c : ℂ) (ψ : EuclideanSpace ℂ ι) (S : Finset ι) :
    measureProb (c • ψ) S = ‖c‖ ^ 2 * measureProb ψ S := by
  simp only [measureProb, PiLp.smul_apply, smul_eq_mul, norm_mul, mul_pow, mul_sum]

omit [Fintype G] in
theorem regProb_smul (c : ℂ) (ψ : State N W) (i : Fin N) :
    regProb (c • ψ) i = ‖c‖ ^ 2 * regProb ψ i :=
  measureProb_smul c ψ _

/-! ### Permutations of the basis and parking -/

omit [Fintype G] in
/-- The isometry permuting the basis states by `e`: `|p⟩ ↦ |e p⟩`. -/
noncomputable def permute (e : Equiv.Perm (Fin N × Bool × W)) : State N W ≃ₗᵢ[ℂ] State N W :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e

omit [Fintype G] in
@[simp] theorem permute_apply (e : Equiv.Perm (Fin N × Bool × W)) (ψ : State N W)
    (p : Fin N × Bool × W) : (permute e ψ).ofLp p = ψ.ofLp (e.symm p) := rfl

omit [Fintype G] in
/-- The flip `|i, b, w⟩ ↦ |i, ¬b, w⟩` of the control bit. -/
noncomputable def flipCtrl : State N W ≃ₗᵢ[ℂ] State N W :=
  permute
    { toFun := fun p => (p.1, !p.2.1, p.2.2)
      invFun := fun p => (p.1, !p.2.1, p.2.2)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }

omit [Fintype G] in
@[simp] theorem flipCtrl_apply (ψ : State N W) (p : Fin N × Bool × W) :
    (flipCtrl ψ).ofLp p = ψ.ofLp (p.1, !p.2.1, p.2.2) := rfl

omit [Fintype G] in
/-- Flipping the control bit does not change the probability of any query index. -/
theorem regProb_flipCtrl (ψ : State N W) (i : Fin N) : regProb (flipCtrl ψ) i = regProb ψ i := by
  simp only [regProb_eq_sum, Fintype.sum_prod_type, Fintype.sum_bool, flipCtrl_apply,
    Bool.not_true, Bool.not_false]
  ring

omit [Fintype W] [Fintype G] in
/-- The controlled oracle acts as the identity on states with control bit `0`. -/
theorem phaseOracle_eq_self {x : Fin N → Bool} {ψ : State N W}
    (hψ : ∀ i w, ψ.ofLp (i, true, w) = 0) : phaseOracle x ψ = ψ := by
  ext ⟨i, b, w⟩
  cases b <;> simp [hψ]

omit [Fintype G] in
/-- The algorithm `U` **parked** after `k` queries: it runs `U` up to its `k`-th isometry, then
flips the control bit, and then does nothing. -/
noncomputable def park (k : ℕ) (U : ℕ → State N W →ₗᵢ[ℂ] State N W) :
    ℕ → State N W →ₗᵢ[ℂ] State N W := fun t =>
  if t < k then U t
  else if t = k then flipCtrl.toLinearIsometry.comp (U k) else LinearIsometry.id

omit [Fintype G] in
/-- **A parked algorithm keeps its state**: if the state of `U` after `k` queries has control bit
`1`, then after `t ≥ k` queries the parked algorithm is in that state with the control bit
flipped. -/
theorem run_park {k : ℕ} {U : ℕ → State N W →ₗᵢ[ℂ] State N W} {ψ₀ : State N W}
    {x : Fin N → Bool} (hctrl : ∀ i w, (run U ψ₀ x k).ofLp (i, false, w) = 0) {t : ℕ}
    (hkt : k ≤ t) : run (park k U) ψ₀ x t = flipCtrl (run U ψ₀ x k) := by
  have hlt : ∀ s, s < k → run (park k U) ψ₀ x s = run U ψ₀ x s := by
    intro s hs
    induction s with
    | zero => simp [run, park, hs]
    | succ s ih => simp [run, park, hs, ih (by omega)]
  have hk : run (park k U) ψ₀ x k = flipCtrl (run U ψ₀ x k) := by
    cases k with
    | zero => simp [run, park]
    | succ k => simp [run, park, hlt k (by omega)]
  induction t, hkt using Nat.le_induction with
  | base => exact hk
  | succ t hkt ih =>
    have hgt : ¬ t + 1 < k := by omega
    have hne : t + 1 ≠ k := by omega
    simp only [run, park, hgt, hne, ite_false, LinearIsometry.id_apply, ih]
    exact phaseOracle_eq_self fun i w => by simpa using hctrl i w

end Cslib.Quantum
