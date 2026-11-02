/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Quantum.Measurement
import Mathlib.Algebra.Order.Chebyshev

/-!
# The quantum query lower bound for search

A *quantum query algorithm* with `T` queries to `x : Fin N → Bool` alternates `T + 1` arbitrary
linear isometries `U₀, …, U_T` of a finite-dimensional state space `ℂ^{Fin N × Bool × W}`, with a
query register, a control bit and a workspace `W`, with `T` applications of the *controlled phase
oracle* `O_x |i, b, w⟩ = (-1)^{b · x_i} |i, b, w⟩` (`Cslib.Quantum.phaseOracle`,
`Cslib.Quantum.run`). Up to Hadamard gates on the control bit this is the standard bit oracle
`|i, b⟩ ↦ |i, b ⊕ x_i⟩`, so the model is the standard quantum query model. Its output is the
measurement of the query register: the probability of outcome `i` is `∑_{b, w} |ψ(i, b, w)|²`
(`Cslib.Quantum.regProb`).

**The search lower bound.** Searching for a single marked item among `N` takes `Ω(√N)` queries:
if, for every `z`, the algorithm outputs `z` with probability at least `2 / 3` on the input `e_z`
marking only `z`, then `N - 2 ≤ 144 T²` (`Cslib.Quantum.card_sub_two_le`). The proof is the
hybrid argument of [Bennett, Bernstein, Brassard, Vazirani][BBBV1997].

On the all-zero input the oracle is the identity; replacing it by `O_{e_z}` at one query moves
the state by `2 ‖Π_z φ‖`, where `Π_z` projects onto query index `z` with control bit `1`
(`Cslib.Quantum.ctrlProj`) and `φ` is the state before that query. So the final states differ by
at most `2 ∑_{t < T} ‖Π_z φ_t‖`, and by Cauchy–Schwarz and `∑_z ‖Π_z φ‖² ≤ ‖φ‖² = 1`,
`∑_z ‖ψ_T^{e_z} - ψ_T^0‖² ≤ 4 T²` (`Cslib.Quantum.sum_sq_norm_run_sub_le`). Success on `e_z` but
not on the all-zero input, for all but at most two `z`, forces each of these distances to be at
least `1 / 6`.

**Source mapping** (numbering of arXiv:quant-ph/9701001v1, the preprint of [BBBV1997]). The source
works with oracle quantum Turing machines. Its query magnitude `q_y(|φ_i⟩)` (Definition 3.2) is
the squared norm of the part of the state that queries `y`; here this is `‖ctrlProj z φ‖²`, the
part with query index `z` and control bit `1`, which is the part the oracle of `e_z` acts on.
Theorem 3.3 bounds how far the final state moves when the answers to a set of queries of small
total query magnitude are changed; `norm_run_sub_le` is the case of the query `z` at every time,
in the triangle-inequality form `2 ∑_s ‖Π_z φ_s‖`, and `sum_sq_norm_run_sub_le` adds
Cauchy–Schwarz and `∑_z q_z ≤ 1`, as in the proof of Corollary 3.4. Theorem 3.1 compares the
outcome distributions of nearby states (total variation at most `4ε`); `regProb_sub_le` is the
per-outcome bound used here. The source applies Corollary 3.4 to prove that relative to a random
oracle `NP` is not contained in `BQTime(o(2^{n/2}))` (Theorem 3.5), which is not formalized here;
`card_sub_two_le` is the search lower bound in its standard query-model form, with the constants
of this proof. The decision form, for computing `OR_N`, is
`Cslib.Quantum.card_le_sixteen_mul_sq_of_threshold_one_right`, by the polynomial method.

## Main definitions

* `Cslib.Quantum.phaseOracle`: the controlled phase oracle of `x`.
* `Cslib.Quantum.run`: the state of a query algorithm after `t` queries.
* `Cslib.Quantum.regProb`: the probability of measuring query index `i`.
* `Cslib.Quantum.ctrlProj`: the projection onto query index `z` with control bit `1`.

## Main results

* `Cslib.Quantum.norm_run_sub_le`: the hybrid argument for one marked item.
* `Cslib.Quantum.sum_sq_norm_run_sub_le`: `∑_z ‖ψ_T^{e_z} - ψ_T^0‖² ≤ 4 T²`.
* `Cslib.Quantum.card_sub_two_le`: the BBBV lower bound `N - 2 ≤ 144 T²`.

## References

* [C. Bennett, E. Bernstein, G. Brassard, U. Vazirani, *Strengths and Weaknesses of Quantum
  Computing*][BBBV1997]
-/

@[expose] public section

namespace Cslib.Quantum

open Finset

variable {N : ℕ} {W : Type*} [Fintype W]

/-- The state space `ℂ^{Fin N × Bool × W}` of a query algorithm: a query register, a control bit
and a workspace. -/
abbrev State (N : ℕ) (W : Type*) := EuclideanSpace ℂ (Fin N × Bool × W)

/-- The **controlled phase oracle** of `x : Fin N → Bool`:
`|i, b, w⟩ ↦ (-1)^{b · x_i} |i, b, w⟩`. -/
noncomputable def phaseOracle (x : Fin N → Bool) : State N W →ₗ[ℂ] State N W where
  toFun ψ := WithLp.toLp 2 fun p => (if p.2.1 && x p.1 then -1 else 1) * ψ.ofLp p
  map_add' ψ φ := by
    ext p
    simp [mul_add]
  map_smul' c ψ := by
    ext p
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

omit [Fintype W] in
@[simp] theorem phaseOracle_apply (x : Fin N → Bool) (ψ : State N W) (p : Fin N × Bool × W) :
    (phaseOracle x ψ).ofLp p = (if p.2.1 && x p.1 then -1 else 1) * ψ.ofLp p := rfl

/-- The phase oracle preserves norms. -/
theorem norm_phaseOracle (x : Fin N → Bool) (ψ : State N W) : ‖phaseOracle x ψ‖ = ‖ψ‖ := by
  have h : ‖phaseOracle x ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    refine sum_congr rfl fun p _ => ?_
    rw [phaseOracle_apply, norm_mul]
    split_ifs <;> simp
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

omit [Fintype W] in
/-- The oracle of the all-zero input is the identity. -/
@[simp] theorem phaseOracle_zero (ψ : State N W) : phaseOracle (fun _ => false) ψ = ψ := by
  ext p
  simp

/-- **The state after `t` queries** of the algorithm with isometries `U` and initial state `ψ₀` on
input `x`: `U_t O_x U_{t-1} ⋯ O_x U_0 ψ₀`. -/
noncomputable def run (U : ℕ → State N W →ₗᵢ[ℂ] State N W) (ψ₀ : State N W)
    (x : Fin N → Bool) : ℕ → State N W
  | 0 => U 0 ψ₀
  | t + 1 => U (t + 1) (phaseOracle x (run U ψ₀ x t))

/-- Query algorithms preserve norms. -/
theorem norm_run (U : ℕ → State N W →ₗᵢ[ℂ] State N W) (ψ₀ : State N W) (x : Fin N → Bool)
    (t : ℕ) : ‖run U ψ₀ x t‖ = ‖ψ₀‖ := by
  induction t with
  | zero => exact (U 0).norm_map ψ₀
  | succ t ih => rw [run, LinearIsometry.norm_map, norm_phaseOracle, ih]

/-- The probability of measuring query index `i` in the state `ψ`: the probability
(`Cslib.Quantum.measureProb`) that measuring `ψ` gives an outcome `(i, b, w)`. -/
noncomputable def regProb (ψ : State N W) (i : Fin N) : ℝ :=
  measureProb ψ (univ.filter fun p => p.1 = i)

/-- The probability of measuring query index `i` is `∑_{b, w} |ψ(i, b, w)|²`. -/
theorem regProb_eq_sum (ψ : State N W) (i : Fin N) :
    regProb ψ i = ∑ w : Bool × W, ‖ψ.ofLp (i, w)‖ ^ 2 := by
  have h : (univ.filter fun p : Fin N × Bool × W => p.1 = i) =
      univ.map ⟨fun w => (i, w), fun _ _ h => (Prod.mk.inj h).2⟩ := by
    ext ⟨j, w⟩
    simp only [mem_filter, mem_univ, true_and, mem_map]
    constructor
    · rintro rfl
      exact ⟨w, rfl⟩
    · rintro ⟨w', h⟩
      exact (Prod.mk.inj h).1.symm
  rw [regProb, measureProb, h, sum_map]
  rfl

/-- The projection `Π_z` onto query index `z`. -/
noncomputable def proj (z : Fin N) (ψ : State N W) : State N W :=
  WithLp.toLp 2 fun p => if p.1 = z then ψ.ofLp p else 0

theorem norm_sq_proj (z : Fin N) (ψ : State N W) : ‖proj z ψ‖ ^ 2 = regProb ψ z := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, regProb_eq_sum]
  simp only [proj, PiLp.toLp_apply]
  rw [sum_eq_single z (fun i _ hi => by simp [hi]) (by simp)]
  simp

omit [Fintype W] in
theorem proj_sub (z : Fin N) (ψ φ : State N W) : proj z (ψ - φ) = proj z ψ - proj z φ := by
  ext p
  simp only [proj, PiLp.toLp_apply, PiLp.sub_apply]
  split_ifs <;> simp

theorem norm_proj_le (z : Fin N) (ψ : State N W) : ‖proj z ψ‖ ≤ ‖ψ‖ := by
  have h : ‖proj z ψ‖ ^ 2 ≤ ‖ψ‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    refine sum_le_sum fun p _ => ?_
    simp only [proj, PiLp.toLp_apply]
    split_ifs <;> simp
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- The measurement probabilities of all query indices sum to `‖ψ‖²`. -/
theorem sum_regProb (ψ : State N W) : ∑ i, regProb ψ i = ‖ψ‖ ^ 2 := by
  simp only [regProb_eq_sum]
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]

/-- The projection onto query index `z` with control bit `1`: the part of the state the oracle
of `e_z` acts on. -/
noncomputable def ctrlProj (z : Fin N) (ψ : State N W) : State N W :=
  WithLp.toLp 2 fun p => if p.1 = z ∧ p.2.1 = true then ψ.ofLp p else 0

theorem norm_sq_ctrlProj_le (z : Fin N) (ψ : State N W) : ‖ctrlProj z ψ‖ ^ 2 ≤ regProb ψ z := by
  rw [← norm_sq_proj, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  refine sum_le_sum fun p _ => ?_
  simp only [ctrlProj, proj, PiLp.toLp_apply]
  split_ifs <;> simp_all

variable [DecidableEq (Fin N)]

/-- The input `e_z` marking only `z`. -/
def marked (z : Fin N) : Fin N → Bool := fun i => decide (i = z)

omit [Fintype W] in
/-- Marking `z` changes a state by `-2 Π_z`. -/
theorem phaseOracle_marked_sub (z : Fin N) (ψ : State N W) :
    phaseOracle (marked z) ψ - ψ = (-2 : ℂ) • ctrlProj z ψ := by
  ext p
  simp only [PiLp.sub_apply, phaseOracle_apply, marked, PiLp.smul_apply, ctrlProj, smul_eq_mul]
  by_cases h : p.1 = z <;> cases p.2.1
  · simp [h]
  · simp only [h, decide_true, Bool.and_self, ite_true, and_self]
    ring
  · simp [h]
  · simp [h]

/-- **The hybrid argument** for one marked item: on the inputs `e_z` and `0`, the states after `t`
queries differ by at most `2 ∑_{s < t} ‖Π_z φ_s‖`, where `φ_s` is the state on the all-zero input
after `s` queries. -/
theorem norm_run_sub_le (U : ℕ → State N W →ₗᵢ[ℂ] State N W) (ψ₀ : State N W) (z : Fin N)
    (t : ℕ) :
    ‖run U ψ₀ (marked z) t - run U ψ₀ (fun _ => false) t‖ ≤
      2 * ∑ s ∈ range t, ‖ctrlProj z (run U ψ₀ (fun _ => false) s)‖ := by
  induction t with
  | zero => simp [run]
  | succ t ih =>
    set a := run U ψ₀ (marked z) t
    set b := run U ψ₀ (fun _ => false) t
    have hstep : run U ψ₀ (marked z) (t + 1) - run U ψ₀ (fun _ => false) (t + 1) =
        U (t + 1) (phaseOracle (marked z) a - b) := by
      simp only [run, phaseOracle_zero, map_sub, a, b]
    rw [hstep, LinearIsometry.norm_map, sum_range_succ, mul_add]
    calc
      ‖phaseOracle (marked z) a - b‖ ≤
          ‖phaseOracle (marked z) a - phaseOracle (marked z) b‖ +
            ‖phaseOracle (marked z) b - b‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = ‖a - b‖ + 2 * ‖ctrlProj z b‖ := by
        rw [← map_sub, norm_phaseOracle, phaseOracle_marked_sub, norm_smul]
        norm_num
      _ ≤ _ := by linarith

/-- **The sum of squared distances**: for a unit initial state,
`∑_z ‖ψ_T^{e_z} - ψ_T^0‖² ≤ 4 T²`. -/
theorem sum_sq_norm_run_sub_le (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W}
    (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ) :
    ∑ z, ‖run U ψ₀ (marked z) T - run U ψ₀ (fun _ => false) T‖ ^ 2 ≤ 4 * (T : ℝ) ^ 2 := by
  set φ := run U ψ₀ (fun _ => false)
  calc
    ∑ z, ‖run U ψ₀ (marked z) T - φ T‖ ^ 2 ≤
        ∑ z, (2 * ∑ s ∈ range T, ‖ctrlProj z (φ s)‖) ^ 2 :=
      sum_le_sum fun z _ => pow_le_pow_left₀ (norm_nonneg _) (norm_run_sub_le U ψ₀ z T) 2
    _ ≤ ∑ z, 4 * (T * ∑ s ∈ range T, ‖ctrlProj z (φ s)‖ ^ 2) := by
      refine sum_le_sum fun z _ => ?_
      rw [mul_pow]
      norm_num
      have := sq_sum_le_card_mul_sum_sq (s := range T) (f := fun s => ‖ctrlProj z (φ s)‖)
      simpa using this
    _ = 4 * (T * ∑ s ∈ range T, ∑ z, ‖ctrlProj z (φ s)‖ ^ 2) := by
      rw [← mul_sum, ← mul_sum, sum_comm]
    _ ≤ 4 * (T * ∑ s ∈ range T, ∑ z, regProb (φ s) z) := by
      gcongr with s _ z
      exact norm_sq_ctrlProj_le z (φ s)
    _ = 4 * (T : ℝ) ^ 2 := by
      simp only [sum_regProb, φ, norm_run, hψ₀, one_pow, sum_const, card_range,
        nsmul_eq_mul, mul_one]
      ring

omit [DecidableEq (Fin N)] in
/-- Two unit states assign probabilities to a query index that differ by at most twice their
distance. -/
theorem regProb_sub_le {ψ φ : State N W} (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) (z : Fin N) :
    regProb ψ z - regProb φ z ≤ 2 * ‖ψ - φ‖ := by
  rw [← norm_sq_proj, ← norm_sq_proj]
  have h1 : ‖proj z ψ‖ - ‖proj z φ‖ ≤ ‖ψ - φ‖ := by
    calc
      ‖proj z ψ‖ - ‖proj z φ‖ ≤ ‖proj z ψ - proj z φ‖ := norm_sub_norm_le _ _
      _ = ‖proj z (ψ - φ)‖ := by rw [proj_sub]
      _ ≤ ‖ψ - φ‖ := norm_proj_le _ _
  have h2 : ‖proj z ψ‖ + ‖proj z φ‖ ≤ 2 := by
    linarith [norm_proj_le z ψ, norm_proj_le z φ]
  have h3 : 0 ≤ ‖proj z ψ‖ + ‖proj z φ‖ := by positivity
  nlinarith [norm_nonneg (ψ - φ), norm_nonneg (proj z ψ), norm_nonneg (proj z φ)]

/-- **The quantum search lower bound** by the hybrid argument of [Bennett, Bernstein, Brassard,
Vazirani][BBBV1997]: if a `T`-query algorithm with a unit initial state outputs `z` with probability
at least `2 / 3` on the input marking only `z`, for every `z`, then `N - 2 ≤ 144 T²`. -/
theorem card_sub_two_le (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W}
    (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ) (hsucc : ∀ z, 2 / 3 ≤ regProb (run U ψ₀ (marked z) T) z) :
    (N : ℝ) - 2 ≤ 144 * (T : ℝ) ^ 2 := by
  classical
  set φ := run U ψ₀ (fun _ => false) T
  have hφ : ‖φ‖ = 1 := by rw [norm_run, hψ₀]
  -- At most two indices are likely on the all-zero input.
  set B := univ.filter fun z : Fin N => 1 / 3 < regProb φ z
  have hB : B.card ≤ 2 := by
    by_contra h
    have hsum : ∑ z ∈ B, regProb φ z ≤ 1 := by
      calc
        ∑ z ∈ B, regProb φ z ≤ ∑ z, regProb φ z :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun z _ _ =>
            sum_nonneg fun _ _ => by positivity
        _ = 1 := by rw [sum_regProb, hφ, one_pow]
    have hlt : (B.card : ℝ) * (1 / 3) < ∑ z ∈ B, regProb φ z := by
      have hne : B.Nonempty := card_pos.mp (by omega)
      calc
        (B.card : ℝ) * (1 / 3) = ∑ _z ∈ B, (1 / 3 : ℝ) := by rw [sum_const, nsmul_eq_mul]
        _ < ∑ z ∈ B, regProb φ z :=
          sum_lt_sum_of_nonempty hne fun z hz => (mem_filter.mp hz).2
    have : (3 : ℝ) ≤ B.card := by exact_mod_cast (by omega : 3 ≤ B.card)
    linarith
  -- Every other index forces a distance of at least `1 / 6`.
  have hfar : ∀ z ∉ B, (1 / 36 : ℝ) ≤ ‖run U ψ₀ (marked z) T - φ‖ ^ 2 := by
    intro z hz
    have hz' : regProb φ z ≤ 1 / 3 := by simpa [B] using hz
    have hd := regProb_sub_le (by rw [norm_run, hψ₀]) hφ z (ψ := run U ψ₀ (marked z) T)
    have h6 : (1 / 6 : ℝ) ≤ ‖run U ψ₀ (marked z) T - φ‖ := by linarith [hsucc z]
    nlinarith
  have hsum := sum_sq_norm_run_sub_le U hψ₀ T
  have hcompl : ((univ \ B).card : ℝ) * (1 / 36) ≤
      ∑ z, ‖run U ψ₀ (marked z) T - φ‖ ^ 2 := by
    calc
      ((univ \ B).card : ℝ) * (1 / 36) = ∑ _z ∈ univ \ B, (1 / 36 : ℝ) := by
        rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ z ∈ univ \ B, ‖run U ψ₀ (marked z) T - φ‖ ^ 2 :=
        sum_le_sum fun z hz => hfar z (mem_sdiff.mp hz).2
      _ ≤ ∑ z, ‖run U ψ₀ (marked z) T - φ‖ ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => by positivity
  have hcard : (N : ℝ) - 2 ≤ (univ \ B).card := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin]
    have : (B.card : ℝ) ≤ 2 := by exact_mod_cast hB
    rw [Nat.cast_sub (card_le_univ B |>.trans_eq (Fintype.card_fin N))]
    linarith
  nlinarith

end Cslib.Quantum
