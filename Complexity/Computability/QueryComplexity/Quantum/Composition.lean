/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.QueryComplexity.Quantum.Search

/-!
# Composing quantum query algorithms

Constructions that build query algorithms (`Cslib.Quantum.run`) from others: classical control,
which realizes classical randomness, parking, checking an output with one more query, and
running an algorithm twice.

**Classical control.** A query algorithm is a deterministic sequence of isometries, but its
workspace and initial state are arbitrary, so classical randomness fits inside it. Let the
workspace be `W × G`, where `G` is a *classical register* that the algorithm reads but never
changes. The isometry `controlled V` applies `V g` to the *slice* `ψ_g` of the state where the
register holds `g` (`Cslib.Quantum.slice`, `Cslib.Quantum.controlled`). The oracle never touches the
workspace, so the slices evolve separately: the slice at `g` of the final state is the final state
of the algorithm `V g` started from the slice at `g` of the initial state
(`Cslib.Quantum.slice_run`), and measuring adds up the slices
(`Cslib.Quantum.measureProb_eq_sum_slice`, `Cslib.Quantum.regProb_eq_sum_slice`). So preparing the
register in the superposition `∑_g √(p_g) |g⟩` makes every outcome probability the average, with
weights `p_g`, of the outcome probabilities of the algorithms `V g`: a classical mixture of query
algorithms, with the coin replaced by its purification.

**Parking.** To let algorithms with different numbers of queries share one query count, an
algorithm whose state after `k` queries has control bit `1` can be *parked* (`Cslib.Quantum.park`):
after its `k`-th query the control bit is flipped to `0` (`Cslib.Quantum.flipCtrl`), where the
controlled oracle acts as the identity, and nothing happens afterwards (`Cslib.Quantum.run_park`).
Parking does not change the probability of any query index.

**Checking an output.** If the state after `T` queries has control bit `0`, a Hadamard gate on the
control bit (`Cslib.Quantum.hadCtrl`), one more query and another Hadamard gate write the queried
bit `x_i` of the query index `i` into the control bit (`Cslib.Quantum.check`,
`Cslib.Quantum.run_check`). The control bit is then `1` with the probability that measuring the
query register gives an index `i` with `x_i = 1` (`Cslib.Quantum.measureProb_run_check`).

**Running twice.** `Cslib.Quantum.twice` runs an algorithm with `T` queries twice, on two copies of
its registers: the second copy waits in the workspace during the first run, then the copies are
exchanged by a permutation of the basis (`Cslib.Quantum.permute`), and the outcome of the first run
waits in the workspace during the second. After `2T` queries the state is the product of two
copies of the final state of the algorithm (`Cslib.Quantum.run_twice`), so accepting when either
outcome is accepting succeeds with probability `1 - (1 - a)²`
(`Cslib.Quantum.measureProb_run_twice`).

These constructions are standard; their formulation in this query model is original.

## Main definitions

* `Cslib.Quantum.slice`, `Cslib.Quantum.controlled`: slices at a classical register, and the
  isometry applying `V g` to the slice at `g`.
* `Cslib.Quantum.permute`, `Cslib.Quantum.flipCtrl`, `Cslib.Quantum.hadCtrl`: a permutation of the
  basis, the flip of the control bit and the Hadamard gate on it.
* `Cslib.Quantum.park`: an algorithm stopped after `k` queries.
* `Cslib.Quantum.check`: an algorithm followed by a check of its output.
* `Cslib.Quantum.twice`, `Cslib.Quantum.twiceInit`: an algorithm run twice.

## Main results

* `Cslib.Quantum.slice_run`: classically controlled algorithms run slice by slice.
* `Cslib.Quantum.measureProb_eq_sum_slice`: outcome probabilities add up over the slices.
* `Cslib.Quantum.run_park`: a parked algorithm keeps its state after `k` queries.
* `Cslib.Quantum.run_add`: a run splits into two runs.
* `Cslib.Quantum.run_check`, `Cslib.Quantum.measureProb_run_check`: the state and acceptance
  probability after a check.
* `Cslib.Quantum.run_twice`, `Cslib.Quantum.measureProb_run_twice`: running twice gives two
  independent copies.
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

@[simp] theorem slice_phaseOracle (x : Fin N → Bool) (g : G) (ψ : State N (W × G)) :
    slice g (phaseOracle x ψ) = phaseOracle x (slice g ψ) := rfl

/-- The basis states of `Fin N × Bool × (W × G)`, sorted by the value of the register `G`. -/
private def splitEquiv : Fin N × Bool × (W × G) ≃ G × (Fin N × Bool × W) where
  toFun p := (p.2.2.2, p.1, p.2.1, p.2.2.1)
  invFun q := (q.2.1, q.2.2.1, q.2.2.2, q.1)
  left_inv _ := rfl
  right_inv _ := rfl

section Control

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

@[simp] theorem controlled_id :
    controlled (fun _ : G => (LinearIsometry.id : State N W →ₗᵢ[ℂ] State N W)) =
      LinearIsometry.id := by
  ext ψ p
  rfl

end Control

variable [Fintype W]

/-! ### Scaling -/

/-- Query algorithms are linear in their initial state. -/
theorem run_smul (U : ℕ → State N W →ₗᵢ[ℂ] State N W) (c : ℂ) (ψ₀ : State N W)
    (x : Fin N → Bool) (t : ℕ) : run U (c • ψ₀) x t = c • run U ψ₀ x t := by
  induction t with
  | zero => exact map_smul (U 0) c ψ₀
  | succ t ih => simp only [run, ih, map_smul]

omit [Fintype W] in
/-- Scaling a state by `c` scales every outcome probability by `‖c‖²`. -/
theorem measureProb_smul {ι : Type*} (c : ℂ) (ψ : EuclideanSpace ℂ ι) (S : Finset ι) :
    measureProb (c • ψ) S = ‖c‖ ^ 2 * measureProb ψ S := by
  simp only [measureProb, PiLp.smul_apply, smul_eq_mul, norm_mul, mul_pow, mul_sum]

/-- Scaling a state by `c` scales the probability of every query index by `‖c‖²`. -/
theorem regProb_smul (c : ℂ) (ψ : State N W) (i : Fin N) :
    regProb (c • ψ) i = ‖c‖ ^ 2 * regProb ψ i :=
  measureProb_smul c ψ _

/-! ### Permutations of the basis and parking -/

/-- The isometry permuting the basis states by `e`: `|p⟩ ↦ |e p⟩`. -/
noncomputable def permute (e : Equiv.Perm (Fin N × Bool × W)) : State N W ≃ₗᵢ[ℂ] State N W :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e

@[simp] theorem permute_apply (e : Equiv.Perm (Fin N × Bool × W)) (ψ : State N W)
    (p : Fin N × Bool × W) : (permute e ψ).ofLp p = ψ.ofLp (e.symm p) := rfl

/-- The flip `|i, b, w⟩ ↦ |i, ¬b, w⟩` of the control bit. -/
noncomputable def flipCtrl : State N W ≃ₗᵢ[ℂ] State N W :=
  permute
    { toFun := fun p => (p.1, !p.2.1, p.2.2)
      invFun := fun p => (p.1, !p.2.1, p.2.2)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }

@[simp] theorem flipCtrl_apply (ψ : State N W) (p : Fin N × Bool × W) :
    (flipCtrl ψ).ofLp p = ψ.ofLp (p.1, !p.2.1, p.2.2) := rfl

/-- Flipping the control bit does not change the probability of any query index. -/
theorem regProb_flipCtrl (ψ : State N W) (i : Fin N) : regProb (flipCtrl ψ) i = regProb ψ i := by
  simp only [regProb_eq_sum, Fintype.sum_prod_type, Fintype.sum_bool, flipCtrl_apply,
    Bool.not_true, Bool.not_false]
  ring

omit [Fintype W] in
/-- The controlled oracle acts as the identity on states with control bit `0`. -/
theorem phaseOracle_eq_self {x : Fin N → Bool} {ψ : State N W}
    (hψ : ∀ i w, ψ.ofLp (i, true, w) = 0) : phaseOracle x ψ = ψ := by
  ext ⟨i, b, w⟩
  cases b <;> simp [hψ]

/-- The algorithm `U` **parked** after `k` queries: it runs `U` up to its `k`-th isometry, then
flips the control bit, and then does nothing. -/
noncomputable def park (k : ℕ) (U : ℕ → State N W →ₗᵢ[ℂ] State N W) :
    ℕ → State N W →ₗᵢ[ℂ] State N W := fun t =>
  if t < k then U t
  else if t = k then flipCtrl.toLinearIsometry.comp (U k) else LinearIsometry.id

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

/-! ### Agreement and splitting of runs -/

/-- Two algorithms whose isometries agree up to `t` queries have the same state after `t`
queries. -/
theorem run_congr {U U' : ℕ → State N W →ₗᵢ[ℂ] State N W} {t : ℕ} (h : ∀ s ≤ t, U s = U' s)
    (ψ₀ : State N W) (x : Fin N → Bool) : run U ψ₀ x t = run U' ψ₀ x t := by
  induction t with
  | zero => simp [run, h 0 le_rfl]
  | succ t ih => simp only [run, h (t + 1) le_rfl, ih fun s hs => h s (by omega)]

/-- **Splitting a run**: if `V` does nothing before its first query and then follows `U` from the
`T`-th query on, then running `U` for `T + s` queries is running `V` for `s` queries from the
state of `U` after `T` queries. -/
theorem run_add {U V : ℕ → State N W →ₗᵢ[ℂ] State N W} {T : ℕ} (h0 : V 0 = LinearIsometry.id)
    (hV : ∀ r, V (r + 1) = U (T + r + 1)) (ψ₀ : State N W) (x : Fin N → Bool) (s : ℕ) :
    run U ψ₀ x (T + s) = run V (run U ψ₀ x T) x s := by
  induction s with
  | zero => simp [run, h0]
  | succ s ih =>
    rw [← Nat.add_assoc]
    simp only [run, hV, ih]

/-! ### Checking an output -/

/-- The Hadamard gate on the control bit:
`|i, b, w⟩ ↦ (|i, 0, w⟩ + (-1)^b |i, 1, w⟩) / √2`. -/
noncomputable def hadCtrl : State N W →ₗᵢ[ℂ] State N W where
  toFun ψ := WithLp.toLp 2 fun p => (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) *
    (ψ.ofLp (p.1, false, p.2.2) + (if p.2.1 then -1 else 1) * ψ.ofLp (p.1, true, p.2.2))
  map_add' ψ φ := by
    ext p
    simp only [PiLp.add_apply]
    ring
  map_smul' c ψ := by
    ext p
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
  norm_map' ψ := by
    have key : ∀ a b : ℂ, ‖(((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (a + -1 * b)‖ ^ 2 +
        ‖(((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (a + 1 * b)‖ ^ 2 = ‖b‖ ^ 2 + ‖a‖ ^ 2 := by
      intro a b
      simp only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow,
        Real.sq_sqrt zero_le_two, neg_one_mul, one_mul, ← sub_eq_add_neg, Complex.sq_norm,
        Complex.normSq_add, Complex.normSq_sub]
      ring
    have h : ‖(WithLp.toLp 2 fun p : Fin N × Bool × W => (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) *
        (ψ.ofLp (p.1, false, p.2.2) + (if p.2.1 then -1 else 1) * ψ.ofLp (p.1, true, p.2.2)) :
          State N W)‖ ^ 2 = ‖ψ‖ ^ 2 := by
      simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Fintype.sum_bool, ite_true,
        Bool.false_eq_true, ite_false]
      refine sum_congr rfl fun i _ => ?_
      rw [← sum_add_distrib, ← sum_add_distrib]
      exact sum_congr rfl fun w _ => key _ _
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

theorem hadCtrl_apply (ψ : State N W) (p : Fin N × Bool × W) :
    (hadCtrl ψ).ofLp p = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) *
      (ψ.ofLp (p.1, false, p.2.2) + (if p.2.1 then -1 else 1) * ψ.ofLp (p.1, true, p.2.2)) :=
  rfl

/-- **Checking a parked output**: if `φ` has control bit `0`, then a Hadamard gate on the control
bit, a query and another Hadamard gate write the queried bit into the control bit: the result has
amplitude `φ(i, 0, w)` at `|i, x_i, w⟩` and `0` elsewhere. -/
theorem hadCtrl_phaseOracle_hadCtrl {x : Fin N → Bool} {φ : State N W}
    (hφ : ∀ i w, φ.ofLp (i, true, w) = 0) (p : Fin N × Bool × W) :
    (hadCtrl (phaseOracle x (hadCtrl φ))).ofLp p =
      if p.2.1 = x p.1 then φ.ofLp (p.1, false, p.2.2) else 0 := by
  have h2 : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = 1 / 2 := by
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt zero_le_two]
    push_cast
    ring
  obtain ⟨i, b, w⟩ := p
  simp only [hadCtrl_apply, phaseOracle_apply, hφ, mul_zero, add_zero]
  generalize (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = c at h2 ⊢
  cases b <;> cases x i <;> simp <;> linear_combination (2 * φ.ofLp (i, false, w)) * h2

/-- The algorithm `U` **followed by a check** of its output after `T` queries: a Hadamard gate on
the control bit, one more query and another Hadamard gate, which write the queried bit `x_i` of
the measured index `i` into the control bit. -/
noncomputable def check (T : ℕ) (U : ℕ → State N W →ₗᵢ[ℂ] State N W) :
    ℕ → State N W →ₗᵢ[ℂ] State N W := fun t =>
  if t < T then U t else if t = T then hadCtrl.comp (U T) else hadCtrl

/-- **The state after a check**: if the state of `U` after `T` queries has control bit `0`, then
after the check the control bit holds the queried bit `x_i` of the query index `i`. -/
theorem run_check {T : ℕ} {U : ℕ → State N W →ₗᵢ[ℂ] State N W} {ψ₀ : State N W}
    {x : Fin N → Bool} (hctrl : ∀ i w, (run U ψ₀ x T).ofLp (i, true, w) = 0)
    (p : Fin N × Bool × W) :
    (run (check T U) ψ₀ x (T + 1)).ofLp p =
      if p.2.1 = x p.1 then (run U ψ₀ x T).ofLp (p.1, false, p.2.2) else 0 := by
  have hT : run (check T U) ψ₀ x T = hadCtrl (run U ψ₀ x T) := by
    cases T with
    | zero => simp [run, check]
    | succ T =>
      rw [run, run, run_congr (U' := U) (fun s hs => by simp [check, show s < T + 1 by omega])]
      simp [check]
  rw [run, hT]
  simp only [check, show ¬ T + 1 < T by omega, show T + 1 ≠ T by omega, ite_false]
  exact hadCtrl_phaseOracle_hadCtrl hctrl p

/-- **The acceptance probability of a check**: if the state of `U` after `T` queries has control
bit `0`, then after the check the control bit is `1` with the probability that measuring the state
of `U` gives a marked query index. -/
theorem measureProb_run_check {T : ℕ} {U : ℕ → State N W →ₗᵢ[ℂ] State N W} {ψ₀ : State N W}
    {x : Fin N → Bool} (hctrl : ∀ i w, (run U ψ₀ x T).ofLp (i, true, w) = 0) :
    measureProb (run (check T U) ψ₀ x (T + 1)) (univ.filter fun p => p.2.1 = true) =
      ∑ i with x i = true, regProb (run U ψ₀ x T) i := by
  simp only [measureProb, sum_filter, run_check hctrl, regProb_eq_sum, Fintype.sum_prod_type,
    Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false]
  refine sum_congr rfl fun i _ => ?_
  cases x i <;> simp [hctrl]

/-! ### Running an algorithm twice -/

/-- The basis permutation exchanging the query register, control bit and workspace with a copy of
them held in the workspace. -/
def swapCopy : Equiv.Perm (Fin N × Bool × (W × (Fin N × Bool × W))) where
  toFun p := (p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2, p.1, p.2.1, p.2.2.1)
  invFun p := (p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2, p.1, p.2.1, p.2.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The algorithm `U` with `T` queries **run twice**, on two copies of its registers: the second
copy waits in the workspace while the first run makes its `T` queries; then the copies are
exchanged, and the second run makes `T` more queries while the outcome of the first waits in the
workspace. -/
noncomputable def twice (T : ℕ) (U : ℕ → State N W →ₗᵢ[ℂ] State N W) :
    ℕ → State N (W × (Fin N × Bool × W)) →ₗᵢ[ℂ] State N (W × (Fin N × Bool × W)) := fun t =>
  if t < T then controlled fun _ => U t
  else if t = T then (controlled fun _ => U 0).comp
    ((permute swapCopy).toLinearIsometry.comp (controlled fun _ => U T))
  else controlled fun _ => U (t - T)

/-- The initial state of `twice`: two copies of `ψ₀`. -/
noncomputable def twiceInit (ψ₀ : State N W) : State N (W × (Fin N × Bool × W)) :=
  WithLp.toLp 2 fun p => ψ₀.ofLp (p.1, p.2.1, p.2.2.1) * ψ₀.ofLp p.2.2.2

/-- Two copies of a unit state form a unit state. -/
theorem norm_twiceInit {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) : ‖twiceInit ψ₀‖ = 1 := by
  have h : ‖twiceInit ψ₀‖ ^ 2 = 1 := by
    rw [norm_sq_eq_sum_slice]
    have hslice : ∀ g, slice g (twiceInit ψ₀) = ψ₀.ofLp g • ψ₀ := by
      intro g
      ext q
      simp [twiceInit, mul_comm]
    simp only [hslice, norm_smul, hψ₀, mul_one]
    rw [← EuclideanSpace.norm_sq_eq, hψ₀, one_pow]
  nlinarith [norm_nonneg (twiceInit ψ₀)]

/-- **Running twice gives two independent copies**: after `T + T` queries, the state of `twice` is
the product of two copies of the state of `U` after `T` queries. -/
theorem run_twice (T : ℕ) (U : ℕ → State N W →ₗᵢ[ℂ] State N W) (ψ₀ : State N W)
    (x : Fin N → Bool) (p : Fin N × Bool × (W × (Fin N × Bool × W))) :
    (run (twice T U) (twiceInit ψ₀) x (T + T)).ofLp p =
      (run U ψ₀ x T).ofLp (p.1, p.2.1, p.2.2.1) * (run U ψ₀ x T).ofLp p.2.2.2 := by
  set F := run U ψ₀ x T
  -- The first run, with the second copy waiting.
  have hfirst : ∀ g, slice g (run (fun s => controlled fun _ : Fin N × Bool × W => U s)
      (twiceInit ψ₀) x T) = ψ₀.ofLp g • F := by
    intro g
    rw [slice_run (fun _ s => U s)]
    have : slice g (twiceInit ψ₀) = ψ₀.ofLp g • ψ₀ := by
      ext q
      simp [twiceInit, mul_comm]
    rw [this, run_smul]
  -- The exchange.
  have hswap : run (twice T U) (twiceInit ψ₀) x T = (controlled fun _ => U 0)
      (permute swapCopy (run (fun s => controlled fun _ : Fin N × Bool × W => U s)
        (twiceInit ψ₀) x T)) := by
    cases T with
    | zero => simp [run, twice]
    | succ T =>
      rw [run, run, run_congr (U' := fun s => controlled fun _ : Fin N × Bool × W => U s)
        (fun s hs => by simp [twice, show s < T + 1 by omega])]
      simp [twice]
  have hmid : ∀ g, slice g (run (twice T U) (twiceInit ψ₀) x T) = F.ofLp g • U 0 ψ₀ := by
    intro g
    rw [hswap, slice_controlled, ← map_smul]
    congr 1
    ext q
    have := congrArg (fun φ => φ.ofLp (g.1, g.2.1, g.2.2)) (hfirst (q.1, q.2.1, q.2.2))
    simp only [slice_apply, PiLp.smul_apply, smul_eq_mul, permute_apply] at this ⊢
    exact this.trans (mul_comm _ _)
  -- The second run, with the outcome of the first waiting.
  have hsecond : run (twice T U) (twiceInit ψ₀) x (T + T) = run
      (fun r => controlled fun _ : Fin N × Bool × W =>
        if r = 0 then LinearIsometry.id else U r) (run (twice T U) (twiceInit ψ₀) x T) x T :=
    run_add (by simp) (fun r => by
      simp [twice, show ¬ T + r + 1 < T by omega, show T + r + 1 ≠ T by omega,
        show T + r + 1 - T = r + 1 by omega]) _ _ _
  have hU : run (fun r => if r = 0 then LinearIsometry.id else U r) (U 0 ψ₀) x T = F :=
    (run_add (T := 0) (by simp) (fun r => by simp) ψ₀ x T).symm.trans
      (by rw [Nat.zero_add])
  obtain ⟨i, b, w, g⟩ := p
  have := congrArg (fun φ => φ.ofLp (i, b, w)) (slice_run (fun _ r => if r = 0 then
    LinearIsometry.id else U r) (run (twice T U) (twiceInit ψ₀) x T) x g T)
  simp only [slice_apply] at this
  rw [hsecond, this, hmid, run_smul, hU, PiLp.smul_apply, smul_eq_mul, mul_comm]

/-- **The acceptance probability of running twice**: accepting when the outcome of either run lies
in `S`, `twice` accepts with probability `1 - (1 - a)²`, where `a` is the probability that the
outcome of one run lies in `S`. -/
theorem measureProb_run_twice [DecidableEq W] {T : ℕ} {U : ℕ → State N W →ₗᵢ[ℂ] State N W}
    {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (x : Fin N → Bool) (S : Finset (Fin N × Bool × W)) :
    measureProb (run (twice T U) (twiceInit ψ₀) x (T + T))
        (univ.filter fun p => (p.1, p.2.1, p.2.2.1) ∈ S ∨ p.2.2.2 ∈ S) =
      1 - (1 - measureProb (run U ψ₀ x T) S) ^ 2 := by
  set F := run U ψ₀ x T
  set f : Fin N × Bool × W → ℝ := fun q => ‖F.ofLp q‖ ^ 2
  have hprod : ∀ f₁ f₂ : Fin N × Bool × W → ℝ,
      ∑ p : Fin N × Bool × (W × (Fin N × Bool × W)), f₁ (p.1, p.2.1, p.2.2.1) * f₂ p.2.2.2 =
        (∑ q, f₁ q) * ∑ g, f₂ g := by
    intro f₁ f₂
    rw [sum_split, sum_mul_sum, sum_comm]
  have hF : ∑ q, f q = 1 := by
    simp only [f, ← EuclideanSpace.norm_sq_eq, F, norm_run, hψ₀, one_pow]
  have hS : measureProb F S = ∑ q, if q ∈ S then f q else 0 := by
    rw [measureProb, sum_ite_mem, univ_inter]
  have hSc : ∑ q, (if q ∈ S then 0 else f q) = 1 - measureProb F S := by
    rw [hS, ← hF, ← sum_sub_distrib]
    exact sum_congr rfl fun q _ => by split_ifs <;> ring
  have hterm : ∀ p : Fin N × Bool × (W × (Fin N × Bool × W)),
      (if (p.1, p.2.1, p.2.2.1) ∈ S ∨ p.2.2.2 ∈ S then ‖F.ofLp (p.1, p.2.1, p.2.2.1)‖ ^ 2 *
        ‖F.ofLp p.2.2.2‖ ^ 2 else 0) =
          f (p.1, p.2.1, p.2.2.1) * f p.2.2.2 - (fun q => if q ∈ S then 0 else f q)
            (p.1, p.2.1, p.2.2.1) * (fun q => if q ∈ S then 0 else f q) p.2.2.2 := by
    intro p
    by_cases h1 : (p.1, p.2.1, p.2.2.1) ∈ S <;> by_cases h2 : p.2.2.2 ∈ S <;> simp [h1, h2, f]
  simp only [measureProb, sum_filter, run_twice, norm_mul, mul_pow]
  rw [sum_congr rfl fun p _ => hterm p, sum_sub_distrib, hprod f f,
    hprod (fun q => if q ∈ S then 0 else f q) (fun q => if q ∈ S then 0 else f q), hF, hSc,
    measureProb]
  ring

end Cslib.Quantum
