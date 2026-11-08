/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.QueryComplexity.Quantum.BitQuery
public import Complexity.Computability.QueryComplexity.Simon
public import Complexity.Foundations.Quantum.HadamardTransform
import Complexity.Foundations.Data.BitString.Parity.DotProduct

/-!
# Simon's algorithm and the exponential quantum–classical query separation

**Simon's problem** (`Complexity/Computability/QueryComplexity/Simon.lean`, [Simon][Simon1997],
[de Wolf, §3.1][deWolf2019]): given `f : {0,1}^n → {0,1}^n` with the promise that for some `s`,
`f(a) = f(b)` exactly when `b ∈ {a, a ⊕ s}` (`Cslib.QueryComplexity.SimonPromise`), decide whether
`s ≠ 0`. The input is the truth table `X : Fin N → Bool` of the `N = n 2^n` output bits of `f`,
indexed by `E : Fin N ≃ {0,1}^n × Fin n` (`Cslib.QueryComplexity.simonFun`), and queries are bit
queries (`Cslib.Quantum.bitQueryAlg`): each query reads one bit `f(a)_j`.

**The algorithm** (`Cslib.Quantum.simonAlg m E i₀`, de Wolf §3.2) runs `m` rounds of Simon's
subroutine side by side. Its workspace (`Cslib.Quantum.SimonWork m n`) holds an input register `xs`
and an output register `ys` of `m` strings of `n` bits each. It starts in `|i₀, 0, 0, 0⟩` for a
fixed query index `i₀` (`Cslib.Quantum.simonInit`), applies the Hadamard transform to `xs`, computes
`ys_{r,j} = f(xs_r)_j` with `m n` bit queries, and applies the Hadamard transform to `xs` again.
For query `(r, j)` the basis permutation `Cslib.Quantum.simonRoute` moves the position
`E⁻¹(xs_r, j)` of the bit `f(xs_r)_j` into the query register and the target bit `ys_{r,j}` into
the control bit; after the bit query the same permutation moves them back. Measuring gives `m`
rows `z_1, …, z_m ∈ {0,1}^n`, and the algorithm accepts when they have a common nonzero orthogonal
vector (`Cslib.Quantum.simonAccept`), which Gaussian elimination decides without further queries.

**Analysis.** The final amplitude of `|i₀, 0, z, y⟩` is `2^{-mn} ∑_{a : f(a) = y} (-1)^{a ⬝ z}`,
with `f` applied rowwise (`Cslib.Quantum.run_simonAlg_apply`). If `s ≠ 0` and `z_r ⬝ s = 1` for a
row `r`, then adding `s` to row `r` of `a` pairs the terms of this sum with opposite signs. So every
measured row is orthogonal to `s`, and the algorithm accepts with certainty
(`Cslib.Quantum.measureProb_simonAlg_of_ne_zero`). If `f` is injective (`s = 0`), each row matrix
`z` is measured with probability `2^{-mn}`, and a fixed nonzero `w` is orthogonal to all rows of
`2^{(n-1)m}` of the `2^{nm}` matrices, so the algorithm accepts with probability at most
`(2^n - 1) / 2^m` (`Cslib.Quantum.measureProb_simonAlg_le_of_injective`). With `m = n + 2` rounds,
`n (n + 2)` bit queries decide Simon's problem with one-sided error below `1/4`
(`Cslib.Quantum.simonAlg_spec`).

**The separation.** Every randomized decision tree that decides Simon's problem with error `1/3`
has depth `q` with `2^n ≤ q²` (`Cslib.QueryComplexity.simon_two_pow_le_depth_sq`), so the
separation is exponential: `n (n + 2)` quantum bit queries against `2^{n/2}` randomized ones
(`Cslib.Quantum.simon_separation`). In terms of the input length `N = n 2^n`, for which
`n ≤ log₂ N`, the quantum algorithm makes at most `3 log₂² N` queries and every such randomized
decision tree has `N ≤ q² log₂ N`, so `q ≥ (N / log₂ N)^{1/2} = N^{1/2 - o(1)}`
(`Cslib.Quantum.simon_separation_inputLength`). Both sides count bit queries, so the comparison is
like for like; the quantum side pays a factor `n` over the `n + 2` value queries of de Wolf §3.2.
Simulating value queries by bit queries transfers the classical bound to value queries only up to
that factor (`q_v ≥ 2^{n/2} / n`); the coupling argument, which uses only that `q` queries touch at
most `q` inputs `a`, would give `2^n ≤ q_v²` directly, but that is not formalized.

**Source mapping.** de Wolf §3.2 repeats the subroutine `O(n)` times and solves the resulting
linear system to find `s`; de Wolf §3.3.2 proves the classical lower bound for the decision
version, which is the version separated here. Running the rounds side by side in one bit-query
algorithm, accepting by the rank test, and the union bound `(2^n - 1) / 2^m` with its constants
are formulated here. Finding `s` itself (the search version) is in
`Complexity/Computability/QueryComplexity/Quantum/SimonSearch.lean`, which uses the general bound
`Cslib.Quantum.measureProb_simonAlg_le` on the outcome probabilities.

## Main definitions

* `Cslib.Quantum.SimonWork`: the workspace of Simon's algorithm.
* `Cslib.Quantum.simonRoute`: the routing permutation of a bit query.
* `Cslib.Quantum.simonAlg`, `Cslib.Quantum.simonInit`: Simon's algorithm and its initial state.
* `Cslib.Quantum.simonAccept`: the accepting outcomes, row matrices with a nonzero kernel vector.

## Main results

* `Cslib.Quantum.run_simonAlg_apply`: the final amplitudes.
* `Cslib.Quantum.measureProb_simonAlg_le`: under the promise with fibers of size at most `K`, a
  set `Z` of row matrices is measured with probability at most `K / 2^{mn}` times the number of
  matrices in `Z` with all rows orthogonal to `s`.
* `Cslib.Quantum.measureProb_simonAlg_of_ne_zero`: certain acceptance when `s ≠ 0`.
* `Cslib.Quantum.measureProb_simonAlg_le_of_injective`: acceptance probability at most
  `(2^n - 1) / 2^m` when `f` is injective.
* `Cslib.Quantum.simonAlg_spec`: `n (n + 2)` bit queries decide Simon's problem with error below
  `1/4`.
* `Cslib.Quantum.simon_separation`: the exponential separation, `n (n + 2)` quantum queries against
  depth `q` with `2^n ≤ q²` for randomized decision trees.
* `Cslib.Quantum.simon_separation_inputLength`: the same in the input length `N = n 2^n`.

## References

* [D. R. Simon, *On the Power of Quantum Computation*][Simon1997]
* [R. de Wolf, *Quantum Computing: Lecture Notes*][deWolf2019], §3.1–§3.3
-/

public section

namespace Cslib.Quantum

open Finset BitString QueryComplexity

variable {N n m : ℕ}

/-- The workspace of Simon's algorithm with `m` rounds: the input register `xs` and the output
register `ys`, each holding `m` strings of `n` bits. -/
abbrev SimonWork (m n : ℕ) := (Fin m × Fin n → Bool) × (Fin m × Fin n → Bool)

/-- The basis of Simon's algorithm regrouped for the Hadamard transform on the input register:
`(i, b, xs, ys) ↦ (xs, (i, b, ys))`. -/
def simonEquiv : Fin N × Bool × SimonWork m n ≃
    (Fin m × Fin n → Bool) × (Fin N × Bool × (Fin m × Fin n → Bool)) where
  toFun p := (p.2.2.1, p.1, p.2.1, p.2.2.2)
  invFun q := (q.2.1, q.2.2.1, q.1, q.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem simonEquiv_apply (p : Fin N × Bool × SimonWork m n) :
    simonEquiv p = (p.2.2.1, p.1, p.2.1, p.2.2.2) := by rfl

@[simp] theorem simonEquiv_symm_apply
    (q : (Fin m × Fin n → Bool) × (Fin N × Bool × (Fin m × Fin n → Bool))) :
    simonEquiv.symm q = (q.2.1, q.2.2.1, q.1, q.2.2.2) := by rfl

/-- The routing permutation of query `k = (r, j)` with resting query index `i₀`: it exchanges the
query index `i₀` with the position `E⁻¹(xs_r, j)` of the bit `f(xs_r)_j`, and the control bit with
the output bit `ys_{r,j}`. It is an involution. -/
def simonRoute (E : Fin N ≃ (Fin n → Bool) × Fin n) (i₀ : Fin N) (k : Fin m × Fin n) :
    Equiv.Perm (Fin N × Bool × SimonWork m n) where
  toFun p := (Equiv.swap i₀ (E.symm (Function.curry p.2.2.1 k.1, k.2)) p.1, p.2.2.2 k, p.2.2.1,
    Function.update p.2.2.2 k p.2.1)
  invFun p := (Equiv.swap i₀ (E.symm (Function.curry p.2.2.1 k.1, k.2)) p.1, p.2.2.2 k, p.2.2.1,
    Function.update p.2.2.2 k p.2.1)
  left_inv p := by
    obtain ⟨i, b, xs, ys⟩ := p
    simp
  right_inv p := by
    obtain ⟨i, b, xs, ys⟩ := p
    simp

/-- A bit query between two routing permutations writes `f(xs_r)_j` into `ys_{r,j}`. -/
private theorem simonRoute_conj (E : Fin N ≃ (Fin n → Bool) × Fin n) (i₀ : Fin N)
    (k : Fin m × Fin n) (X : Fin N → Bool) (xs ys : Fin m × Fin n → Bool) :
    (simonRoute E i₀ k * bitFlip X * simonRoute E i₀ k : Equiv.Perm _) (i₀, false, xs, ys) =
      (i₀, false, xs, Function.update ys k (ys k ^^ X (E.symm (Function.curry xs k.1, k.2)))) := by
  simp [simonRoute]

/-- The order of the queries of Simon's algorithm. -/
private def simonOrd (m n : ℕ) : Fin (m * n) ≃ Fin m × Fin n := finProdFinEquiv.symm

/-- The routing permutation around query `t`. -/
private def simonSigma (E : Fin N ≃ (Fin n → Bool) × Fin n) (i₀ : Fin N) (t : ℕ) :
    Equiv.Perm (Fin N × Bool × SimonWork m n) :=
  if h : t < m * n then simonRoute E i₀ (simonOrd m n ⟨t, h⟩) else 1

/-- The basis permutations between the bit queries of Simon's algorithm. -/
private def simonPerm (E : Fin N ≃ (Fin n → Bool) × Fin n) (i₀ : Fin N) :
    ℕ → Equiv.Perm (Fin N × Bool × SimonWork m n)
  | 0 => simonSigma E i₀ 0
  | t + 1 => simonSigma E i₀ (t + 1) * simonSigma E i₀ t

variable (m) in
/-- **Simon's algorithm** with `m` rounds and resting query index `i₀`: the Hadamard transform on
the input register, `m n` bit queries computing `ys_{r,j} = f(xs_r)_j`, each between two routing
permutations `Cslib.Quantum.simonRoute`, and the Hadamard transform on the input register. -/
noncomputable def simonAlg (E : Fin N ≃ (Fin n → Bool) × Fin n) (i₀ : Fin N) :
    ℕ → State N (SimonWork m n) →ₗᵢ[ℂ] State N (SimonWork m n) :=
  bitQueryAlg (m * n) (simonPerm E i₀) (hadamardTransform simonEquiv)
    (hadamardTransform simonEquiv)

/-- The initial state `|i₀, 0, 0, 0⟩` of Simon's algorithm. -/
noncomputable def simonInit (i₀ : Fin N) : State N (SimonWork m n) := ket (i₀, false, 0, 0)

@[simp] theorem norm_simonInit (i₀ : Fin N) : ‖(simonInit i₀ : State N (SimonWork m n))‖ = 1 :=
  norm_ket _

/-- The values `f(xs_r)_j` of the function `Cslib.QueryComplexity.simonFun E X` on the rows `xs_r`
of `xs`. -/
def simonG (E : Fin N ≃ (Fin n → Bool) × Fin n) (X : Fin N → Bool)
    (xs : Fin m × Fin n → Bool) : Fin m × Fin n → Bool :=
  fun k => simonFun E X (Function.curry xs k.1) k.2

theorem simonG_apply (E : Fin N ≃ (Fin n → Bool) × Fin n) (X : Fin N → Bool)
    (xs : Fin m × Fin n → Bool) (k : Fin m × Fin n) :
    simonG E X xs k = simonFun E X (Function.curry xs k.1) k.2 := by rfl

/-- The permutation accumulated by the first `t` bit queries and their routing permutations. -/
private def simonAcc (E : Fin N ≃ (Fin n → Bool) × Fin n) (i₀ : Fin N) (X : Fin N → Bool) :
    ℕ → Equiv.Perm (Fin N × Bool × SimonWork m n)
  | 0 => 1
  | t + 1 => simonSigma E i₀ t * bitFlip X * simonSigma E i₀ t * simonAcc E i₀ X t

private theorem bitQueryPerm_simonPerm (E : Fin N ≃ (Fin n → Bool) × Fin n) (i₀ : Fin N)
    (X : Fin N → Bool) (t : ℕ) :
    bitQueryPerm (simonPerm (m := m) E i₀) X t = simonSigma E i₀ t * simonAcc E i₀ X t := by
  induction t with
  | zero => simp [simonPerm, simonAcc]
  | succ t ih =>
    rw [bitQueryPerm_succ, ih, simonPerm, simonAcc]
    simp only [mul_assoc]

private theorem simonAcc_apply (E : Fin N ≃ (Fin n → Bool) × Fin n) (i₀ : Fin N)
    (X : Fin N → Bool) {t : ℕ} (ht : t ≤ m * n) (xs : Fin m × Fin n → Bool) :
    simonAcc E i₀ X t (i₀, false, xs, 0) = (i₀, false, xs, fun k =>
      decide (((simonOrd m n).symm k : ℕ) < t) && simonG E X xs k) := by
  induction t with
  | zero =>
    refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (funext fun k => ?_)))
    simp [simonAcc, Bool.zero_eq_false]
  | succ t ih =>
    have h : t < m * n := by omega
    rw [simonAcc, Equiv.Perm.mul_apply, ih (by omega), simonSigma, dite_eq_left h,
      simonRoute_conj]
    refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (funext fun k => ?_)))
    by_cases hk : k = simonOrd m n ⟨t, h⟩
    · subst hk
      simp [simonG, simonFun]
    · have hne : ((simonOrd m n).symm k : ℕ) ≠ t := fun h' => hk <| by
        rw [← (simonOrd m n).apply_symm_apply k]
        exact congrArg _ (Fin.ext h')
      have hlt : ((simonOrd m n).symm k : ℕ) < t + 1 ↔ ((simonOrd m n).symm k : ℕ) < t := by
        omega
      simp only [Function.update_of_ne hk, hlt]

/-- **The bit queries of Simon's algorithm compute `f` rowwise**: from `|i₀, 0, xs, 0⟩` they reach
`|i₀, 0, xs, f(xs)⟩`. -/
private theorem bitQueryPerm_simonPerm_apply (E : Fin N ≃ (Fin n → Bool) × Fin n) (i₀ : Fin N)
    (X : Fin N → Bool) (xs : Fin m × Fin n → Bool) :
    bitQueryPerm (simonPerm E i₀) X (m * n) (i₀, false, xs, 0) =
      (i₀, false, xs, simonG E X xs) := by
  rw [bitQueryPerm_simonPerm, simonSigma, dite_eq_right (lt_irrefl _), one_mul,
    simonAcc_apply _ _ _ le_rfl]
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (funext fun k => ?_)))
  simp

private theorem home_iff {P : Equiv.Perm (Fin N × Bool × SimonWork m n)} {i₀ : Fin N}
    {G : (Fin m × Fin n → Bool) → Fin m × Fin n → Bool}
    (hP : ∀ xs, P (i₀, false, xs, 0) = (i₀, false, xs, G xs))
    (q : Fin N × Bool × SimonWork m n) :
    ((P.symm q).1 = i₀ ∧ (P.symm q).2.1 = false ∧ (P.symm q).2.2.2 = 0) ↔
      (q.1 = i₀ ∧ q.2.1 = false ∧ q.2.2.2 = G q.2.2.1) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    have e : P.symm q = (i₀, false, (P.symm q).2.2.1, 0) :=
      Prod.ext h1 (Prod.ext h2 (Prod.ext rfl h3))
    have hq := congrArg P e
    rw [P.apply_symm_apply, hP] at hq
    rw [hq]
    exact ⟨rfl, rfl, rfl⟩
  · obtain ⟨i, b, xs, ys⟩ := q
    rintro ⟨h1, h2, h3⟩
    simp only at h1 h2 h3
    subst h1 h2 h3
    rw [← hP, P.symm_apply_apply]
    exact ⟨rfl, rfl, rfl⟩

/-- **The final state of Simon's algorithm**: the amplitude of `|i₀, 0, z, y⟩` is
`2^{-mn} ∑_{a : f(a) = y} (-1)^{a ⬝ z}`, with `f` applied rowwise, and every other amplitude is
`0`. -/
theorem run_simonAlg_apply (E : Fin N ≃ (Fin n → Bool) × Fin n) (i₀ : Fin N) (X : Fin N → Bool)
    (p : Fin N × Bool × SimonWork m n) :
    (run (simonAlg m E i₀) (simonInit i₀) X (m * n)).ofLp p =
      if p.1 = i₀ ∧ p.2.1 = false then
        (((Real.sqrt (2 ^ Fintype.card (Fin m × Fin n)))⁻¹ : ℝ) : ℂ) *
        (((Real.sqrt (2 ^ Fintype.card (Fin m × Fin n)))⁻¹ : ℝ) : ℂ) *
          ∑ a with simonG E X a = p.2.2.2, ((signVal (a ⬝ᵥ p.2.2.1) : ℝ) : ℂ)
      else 0 := by
  have hP := bitQueryPerm_simonPerm_apply E i₀ X (m := m)
  have hcond : ∀ a, ((simonEquiv (i₀, false, (0 : Fin m × Fin n → Bool),
      (0 : Fin m × Fin n → Bool))).2 = (simonEquiv ((bitQueryPerm (simonPerm E i₀) X (m * n)).symm
        (simonEquiv.symm (a, (simonEquiv p).2)))).2) ↔
      (p.1 = i₀ ∧ p.2.1 = false ∧ simonG E X a = p.2.2.2) := by
    intro a
    have h := home_iff hP (simonEquiv.symm (a, (simonEquiv p).2))
    simp only [simonEquiv_apply, simonEquiv_symm_apply, Prod.mk.injEq] at h ⊢
    rw [eq_comm (a := i₀), eq_comm (a := false), eq_comm (a := (0 : Fin m × Fin n → Bool)), h,
      eq_comm (a := p.2.2.2)]
  rw [simonAlg, run_bitQueryAlg, hadamardTransform_apply]
  simp only [permute_apply, simonInit, hadamardTransform_ket, hcond]
  simp only [simonEquiv_apply, zero_dotProduct, Bool.zero_eq_false,
    signVal_false, Complex.ofReal_one, mul_one]
  by_cases h : p.1 = i₀ ∧ p.2.1 = false
  · simp only [h, true_and, ite_true, mul_ite, mul_zero, sum_filter, mul_sum]
    exact sum_congr rfl fun a _ => by split_ifs <;> ring
  · rw [ite_eq_right_iff.mpr fun h' => absurd h' h]
    refine (mul_eq_zero_of_right _ (sum_eq_zero fun a _ => ?_))
    rw [ite_eq_right_iff.mpr fun h' => absurd ⟨h'.1, h'.2.1⟩ h, mul_zero]

/-- The accepting outcomes of Simon's algorithm: the measured rows `z_r` (of the input register)
have a common nonzero orthogonal vector `w`, so they do not span `{0,1}^n`. -/
def simonAccept (m n : ℕ) : Finset (Fin N × Bool × SimonWork m n) :=
  univ.filter fun p => ∃ w : Fin n → Bool, w ≠ 0 ∧ ∀ r, Function.curry p.2.2.1 r ⬝ᵥ w = false

@[simp] theorem mem_simonAccept {p : Fin N × Bool × SimonWork m n} :
    p ∈ simonAccept m n ↔
      ∃ w : Fin n → Bool, w ≠ 0 ∧ ∀ r, Function.curry p.2.2.1 r ⬝ᵥ w = false := by
  simp [simonAccept]

private theorem signVal_add_true (x : Bool) : signVal (x + true) = -signVal x := by
  cases x
  · simp [show (false + true : Bool) = true from rfl]
  · simp [show (true + true : Bool) = false from rfl]

/-- Under Simon's promise with hidden string `s`, the amplitude of a row matrix with a row `z_r`
with `z_r ⬝ s = 1` vanishes. -/
private theorem sum_signVal_eq_zero {E : Fin N ≃ (Fin n → Bool) × Fin n} {X : Fin N → Bool}
    {s : Fin n → Bool} (hX : SimonPromise (simonFun E X) s) {zs ys : Fin m × Fin n → Bool}
    {r₀ : Fin m} (hr : Function.curry zs r₀ ⬝ᵥ s = true) :
    ∑ a with simonG E X a = ys, ((signVal (a ⬝ᵥ zs) : ℝ) : ℂ) = 0 := by
  set δ : Fin m × Fin n → Bool := fun k => if k.1 = r₀ then s k.2 else false with hδ
  have hδz : δ ⬝ᵥ zs = true := by
    rw [← hr, dotProduct, dotProduct, Fintype.sum_prod_type]
    simp only [hδ, Function.curry_apply, ite_mul]
    rw [sum_eq_single r₀ (fun r _ hr => sum_eq_zero fun j _ => by simp only [hr, ite_false]; rfl)
      (by simp)]
    exact sum_congr rfl fun j _ => by simp [mul_comm]
  have hG : ∀ a, simonG E X (a + δ) = simonG E X a := by
    intro a
    funext k
    simp only [simonG]
    by_cases hk : k.1 = r₀
    · have hc : Function.curry (a + δ) k.1 = Function.curry a k.1 + s := by
        funext j
        simp [hδ, hk]
      have hf := (hX (Function.curry a k.1) (Function.curry a k.1 + s)).mpr (Or.inr rfl)
      rw [hc, ← hf]
    · have hc : Function.curry (a + δ) k.1 = Function.curry a k.1 := by
        funext j
        simp [hδ, hk, Bool.zero_eq_false]
      rw [hc]
  set F : (Fin m × Fin n → Bool) → ℂ := fun a =>
    if simonG E X a = ys then ((signVal (a ⬝ᵥ zs) : ℝ) : ℂ) else 0 with hF
  have hFδ : ∀ a, F (a + δ) = -F a := by
    intro a
    simp only [hF, hG, add_dotProduct, hδz, signVal_add_true, Complex.ofReal_neg]
    split_ifs <;> simp
  have hS : ∑ a, F a = -∑ a, F a := by
    rw [← sum_neg_distrib]
    exact Fintype.sum_equiv (Equiv.addRight δ) _ _ fun a => by simp [hFδ]
  rw [sum_filter]
  linear_combination hS / 2

/-- **Simon's algorithm accepts with certainty when `s ≠ 0`**: every measured row is orthogonal to
the hidden string `s`. -/
theorem measureProb_simonAlg_of_ne_zero (E : Fin N ≃ (Fin n → Bool) × Fin n) (i₀ : Fin N)
    {X : Fin N → Bool} {s : Fin n → Bool} (hX : SimonPromise (simonFun E X) s) (hs : s ≠ 0) :
    measureProb (run (simonAlg m E i₀) (simonInit i₀) X (m * n)) (simonAccept m n) = 1 := by
  have h1 : measureProb (run (simonAlg m E i₀) (simonInit i₀) X (m * n)) univ = 1 := by
    rw [measureProb_univ, norm_run, simonInit, norm_ket, one_pow]
  rw [← h1, measureProb, measureProb]
  refine sum_subset (subset_univ _) fun p _ hp => ?_
  obtain ⟨r₀, hr⟩ : ∃ r, Function.curry p.2.2.1 r ⬝ᵥ s = true := by
    by_contra h
    push Not at h
    exact hp (mem_simonAccept.mpr ⟨s, hs, fun r => by simpa using h r⟩)
  rw [run_simonAlg_apply, sum_signVal_eq_zero hX hr]
  simp

private theorem simonG_injective {E : Fin N ≃ (Fin n → Bool) × Fin n} {X : Fin N → Bool}
    (hf : Function.Injective (simonFun E X)) : Function.Injective (simonG (m := m) E X) := by
  intro a b h
  funext k
  have hrow : Function.curry a k.1 = Function.curry b k.1 :=
    hf (funext fun j => congrFun h (k.1, j))
  exact congrFun hrow k.2

/-- Few row matrices have a nonzero kernel vector: at most `(2^n - 1) 2^{nm} / 2^m`. -/
private theorem card_kernel_rows_mul_le :
    #{zs : Fin m × Fin n → Bool | ∃ w : Fin n → Bool, w ≠ 0 ∧
      ∀ r, Function.curry zs r ⬝ᵥ w = false} * 2 ^ m ≤ (2 ^ n - 1) * 2 ^ (m * n) := by
  have hw : ∀ w : Fin n → Bool, w ≠ 0 →
      #{zs : Fin m × Fin n → Bool | ∀ r, Function.curry zs r ⬝ᵥ w = false} =
        (2 ^ (n - 1)) ^ m := by
    intro w hw
    rw [← card_kernel (c := m) hw]
    exact card_equiv (Equiv.curry _ _ _) fun zs => by simp
  have hsub : ({zs : Fin m × Fin n → Bool | ∃ w : Fin n → Bool, w ≠ 0 ∧
      ∀ r, Function.curry zs r ⬝ᵥ w = false} : Finset _) ⊆
      (univ.erase (0 : Fin n → Bool)).biUnion fun w =>
        ({zs : Fin m × Fin n → Bool | ∀ r, Function.curry zs r ⬝ᵥ w = false} : Finset _) := by
    intro zs hzs
    obtain ⟨w, hw0, hw⟩ := (mem_filter.mp hzs).2
    exact mem_biUnion.mpr ⟨w, mem_erase.mpr ⟨hw0, mem_univ _⟩, mem_filter.mpr ⟨mem_univ _, hw⟩⟩
  have hcard := (card_le_card hsub).trans card_biUnion_le
  rw [sum_congr rfl fun w hw' => hw w (mem_erase.mp hw').1, sum_const, card_erase_of_mem
    (mem_univ _), card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    smul_eq_mul] at hcard
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · calc _ ≤ (2 ^ n - 1) * (2 ^ (n - 1)) ^ m * 2 ^ m := Nat.mul_le_mul_right _ hcard
      _ = (2 ^ n - 1) * 2 ^ (m * n) := by
        rw [mul_assoc, ← mul_pow, ← pow_succ, Nat.sub_add_cancel hn, ← pow_mul, mul_comm n m]

private theorem norm_sq_sum_signVal_le (S : Finset (Fin m × Fin n → Bool))
    (zs : Fin m × Fin n → Bool) :
    ‖∑ a ∈ S, ((signVal (a ⬝ᵥ zs) : ℝ) : ℂ)‖ ^ 2 ≤ (#S : ℝ) ^ 2 := by
  have h : ‖∑ a ∈ S, ((signVal (a ⬝ᵥ zs) : ℝ) : ℂ)‖ ≤ #S := by
    refine (norm_sum_le _ _).trans_eq ?_
    simp
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

/-- **Outcome probabilities of Simon's algorithm.** Under Simon's promise with hidden string `s`,
if every fiber of the rowwise `f` has at most `K` elements, then the measured rows lie in a set `Z`
of row matrices with probability at most `K / 2^{mn}` times the number of matrices in `Z` whose rows
are all orthogonal to `s`. -/
theorem measureProb_simonAlg_le (E : Fin N ≃ (Fin n → Bool) × Fin n) (i₀ : Fin N)
    {X : Fin N → Bool} {s : Fin n → Bool} (hX : SimonPromise (simonFun E X) s) {K : ℕ}
    (hK : ∀ ys, #{a | simonG (m := m) E X a = ys} ≤ K) (Z : Finset (Fin m × Fin n → Bool)) :
    measureProb (run (simonAlg m E i₀) (simonInit i₀) X (m * n))
        (univ.filter fun p => p.2.2.1 ∈ Z) ≤
      K * #(Z.filter fun zs => ∀ r, Function.curry zs r ⬝ᵥ s = false) / 2 ^ (m * n) := by
  classical
  set c : ℝ := (Real.sqrt (2 ^ Fintype.card (Fin m × Fin n)))⁻¹ with hc
  set Z' := Z.filter fun zs => ∀ r, Function.curry zs r ⬝ᵥ s = false with hZ'
  have hc0 : 0 ≤ c := by positivity
  set B : Fin N × Bool × SimonWork m n → ℝ := fun p =>
    if p.1 = i₀ ∧ p.2.1 = false ∧ p.2.2.1 ∈ Z' then c ^ 4 * K * #{a | simonG E X a = p.2.2.2}
    else 0 with hBdef
  have hBnn : ∀ p, 0 ≤ B p := fun p => by
    simp only [hBdef]
    split_ifs <;> positivity
  have hpt : ∀ p ∈ univ.filter fun p : Fin N × Bool × SimonWork m n => p.2.2.1 ∈ Z,
      ‖(run (simonAlg m E i₀) (simonInit i₀) X (m * n)).ofLp p‖ ^ 2 ≤ B p := by
    intro p hp
    have hpZ : p.2.2.1 ∈ Z := (mem_filter.mp hp).2
    rw [run_simonAlg_apply]
    by_cases h : p.1 = i₀ ∧ p.2.1 = false
    · by_cases hs : ∀ r, Function.curry p.2.2.1 r ⬝ᵥ s = false
      · have hB : B p = c ^ 4 * K * #{a | simonG E X a = p.2.2.2} := by
          simp only [hBdef, h.1, h.2, hZ', mem_filter, hpZ, hs, implies_true, and_self, ite_true]
        rw [hB, ite_eq_left h, norm_mul, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg hc0]
        have h1 := norm_sq_sum_signVal_le {a | simonG E X a = p.2.2.2} p.2.2.1
        have h2 : ((#{a | simonG E X a = p.2.2.2} : ℕ) : ℝ) ^ 2 ≤
            K * #{a | simonG E X a = p.2.2.2} := by
          rw [sq]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hK p.2.2.2) (by positivity)
        calc (c * c * ‖∑ a with simonG E X a = p.2.2.2, ((signVal (a ⬝ᵥ p.2.2.1) : ℝ) : ℂ)‖) ^ 2
            = c ^ 4 *
                ‖∑ a with simonG E X a = p.2.2.2, ((signVal (a ⬝ᵥ p.2.2.1) : ℝ) : ℂ)‖ ^ 2 := by
              ring
          _ ≤ c ^ 4 * (#{a | simonG E X a = p.2.2.2} : ℝ) ^ 2 :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ ≤ c ^ 4 * (K * #{a | simonG E X a = p.2.2.2}) :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
          _ = c ^ 4 * K * #{a | simonG E X a = p.2.2.2} := by ring
      · push Not at hs
        obtain ⟨r₀, hr⟩ := hs
        rw [ite_eq_left h, sum_signVal_eq_zero hX (r₀ := r₀) (by simpa using hr), mul_zero,
          norm_zero, sq, mul_zero]
        exact hBnn p
    · rw [ite_eq_right h, norm_zero, sq, mul_zero]
      exact hBnn p
  have hfibsum : ∑ ys : Fin m × Fin n → Bool, (#{a | simonG E X a = ys} : ℝ) = 2 ^ (m * n) := by
    have := card_eq_sum_card_fiberwise (f := simonG (m := m) E X) (s := univ) (t := univ)
      fun _ _ => mem_univ _
    rw [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin] at this
    exact_mod_cast this.symm
  have hsum : ∑ p, B p = c ^ 4 * K * (#Z' * 2 ^ (m * n)) := by
    rw [Fintype.sum_prod_type, Fintype.sum_eq_single i₀ fun i hi =>
      sum_eq_zero fun q _ => by simp [hBdef, hi]]
    rw [Fintype.sum_prod_type, Fintype.sum_eq_single false fun b hb =>
      sum_eq_zero fun w _ => by simp [hBdef, hb]]
    rw [Fintype.sum_prod_type]
    have hrow : ∀ zs : Fin m × Fin n → Bool, ∑ ys, B (i₀, false, zs, ys) =
        if zs ∈ Z' then c ^ 4 * K * 2 ^ (m * n) else 0 := by
      intro zs
      simp only [hBdef, true_and]
      split_ifs
      · rw [← mul_sum, hfibsum]
      · exact sum_const_zero
    rw [sum_congr rfl fun zs _ => hrow zs, ← sum_filter, sum_const, nsmul_eq_mul,
      filter_mem_eq_inter, univ_inter]
    ring
  have hc2 : c ^ 2 = ((2 : ℝ) ^ (m * n))⁻¹ := by
    rw [hc, inv_pow, Real.sq_sqrt (by positivity), Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin]
  calc measureProb (run (simonAlg m E i₀) (simonInit i₀) X (m * n))
        (univ.filter fun p => p.2.2.1 ∈ Z)
      ≤ ∑ p ∈ univ.filter fun p : Fin N × Bool × SimonWork m n => p.2.2.1 ∈ Z, B p :=
        sum_le_sum hpt
    _ ≤ ∑ p, B p := sum_le_sum_of_subset_of_nonneg (subset_univ _) fun p _ _ => hBnn p
    _ = c ^ 4 * K * (#Z' * 2 ^ (m * n)) := hsum
    _ = K * #Z' / 2 ^ (m * n) := by
      rw [show c ^ 4 = (c ^ 2) ^ 2 by ring, hc2]
      field_simp

/-- **Simon's algorithm rarely accepts when `f` is injective**: with probability at most
`(2^n - 1) / 2^m`. -/
theorem measureProb_simonAlg_le_of_injective (E : Fin N ≃ (Fin n → Bool) × Fin n) (i₀ : Fin N)
    {X : Fin N → Bool} (hf : Function.Injective (simonFun E X)) :
    measureProb (run (simonAlg m E i₀) (simonInit i₀) X (m * n)) (simonAccept m n) ≤
      (2 ^ n - 1) / 2 ^ m := by
  classical
  set A : Finset (Fin m × Fin n → Bool) := {zs | ∃ w : Fin n → Bool, w ≠ 0 ∧
    ∀ r, Function.curry zs r ⬝ᵥ w = false} with hA
  have hnat : #A * 2 ^ m ≤ (2 ^ n - 1) * 2 ^ (m * n) := card_kernel_rows_mul_le
  have hG := simonG_injective (m := m) hf
  have hfib : ∀ ys, #{a | simonG (m := m) E X a = ys} ≤ 1 := fun ys =>
    card_le_one.mpr fun a ha b hb => hG ((mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm)
  have hacc : simonAccept m n = (univ.filter fun p : Fin N × Bool × SimonWork m n =>
      p.2.2.1 ∈ A) := by
    ext p
    simp [hA]
  have hA' : (A.filter fun zs => ∀ r, Function.curry zs r ⬝ᵥ (0 : Fin n → Bool) = false) = A :=
    filter_true_of_mem fun zs _ r => by simp [Bool.zero_eq_false]
  have h := measureProb_simonAlg_le E i₀ ((simonPromise_zero_iff _).mpr hf) hfib A
  rw [hA', Nat.cast_one, one_mul, ← hacc] at h
  have hreal : (#A : ℝ) * 2 ^ m ≤ (2 ^ n - 1) * 2 ^ (m * n) := by
    have h1 : ((2 ^ n - 1 : ℕ) : ℝ) = 2 ^ n - 1 := by
      rw [Nat.cast_sub Nat.one_le_two_pow]
      push_cast
      ring
    rw [← h1]
    exact_mod_cast hnat
  refine h.trans ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

/-- With `n + 2` rounds, Simon's algorithm accepts an injective `f` with probability below `1/4`. -/
private theorem measureProb_simonAlg_lt_of_injective (E : Fin N ≃ (Fin n → Bool) × Fin n)
    (i₀ : Fin N) {X : Fin N → Bool} (hf : Function.Injective (simonFun E X)) :
    measureProb (run (simonAlg (n + 2) E i₀) (simonInit i₀) X ((n + 2) * n))
      (simonAccept (n + 2) n) < 1 / 4 := by
  refine (measureProb_simonAlg_le_of_injective E i₀ hf).trans_lt ?_
  rw [div_lt_iff₀ (by positivity), pow_add]
  linarith

/-- **Simon's algorithm decides Simon's problem with `n (n + 2)` bit queries**: from a unit
initial state, with `n + 2` rounds, it accepts every promise input with acceptance probability
within `1/4` of the answer `s ≠ 0`; the error is one-sided, as it accepts with certainty when
`s ≠ 0`. -/
theorem simonAlg_spec (E : Fin N ≃ (Fin n → Bool) × Fin n) (i₀ : Fin N) :
    ‖(simonInit i₀ : State N (SimonWork (n + 2) n))‖ = 1 ∧
      ∀ X s, SimonPromise (simonFun E X) s →
        |measureProb (run (simonAlg (n + 2) E i₀) (simonInit i₀) X ((n + 2) * n))
          (simonAccept (n + 2) n) - bitVal ℝ (decide (s ≠ 0))| < 1 / 4 := by
  refine ⟨norm_ket _, fun X s hX => ?_⟩
  by_cases hs : s = 0
  · subst hs
    have hf := (simonPromise_zero_iff _).mp hX
    rw [decide_eq_false (not_not.mpr rfl), bitVal_false, sub_zero,
      abs_of_nonneg (measureProb_nonneg _ _)]
    exact measureProb_simonAlg_lt_of_injective E i₀ hf
  · rw [decide_eq_true hs, bitVal_true, measureProb_simonAlg_of_ne_zero E i₀ hX hs, sub_self,
      abs_zero]
    norm_num

/-- **The exponential quantum–classical separation for Simon's problem**, in the bit-query model
on the truth table `X : Fin N → Bool` of `f : {0,1}^n → {0,1}^n`, for `n ≥ 1`: Simon's algorithm
decides Simon's problem with `n (n + 2)` queries and error below `1/4`, while every randomized
decision tree deciding it with error `1/3` (as the restriction to the promise inputs of a total
function `F`) has depth `q` with `2^n ≤ q²`. -/
theorem simon_separation (E : Fin N ≃ (Fin n → Bool) × Fin n) (i₀ : Fin N) (hn : 1 ≤ n) :
    (∀ X s, SimonPromise (simonFun E X) s →
      |measureProb (run (simonAlg (n + 2) E i₀) (simonInit i₀) X ((n + 2) * n))
        (simonAccept (n + 2) n) - bitVal ℝ (decide (s ≠ 0))| < 1 / 4) ∧
    ∀ (μ : RandomizedDecisionTree (Fin N) Bool) (F : (Fin N → Bool) → Bool),
      (∀ X s, SimonPromise (simonFun E X) s → F X = decide (s ≠ 0)) →
      (∀ X s, SimonPromise (simonFun E X) s → μ.errorProb F X ≤ 1 / 3) →
      2 ^ n ≤ μ.depth ^ 2 :=
  ⟨(simonAlg_spec E i₀).2, fun μ F hF hμ => simon_two_pow_le_depth_sq E μ F hF hμ hn⟩

/-- **The separation in the input length** `N = n 2^n`, for `n ≥ 1`: Simon's algorithm decides
Simon's problem with error below `1/4` using `n (n + 2)` queries, which is at most `3 log₂² N`,
while every randomized decision tree deciding it with error `1/3` (as the restriction to the
promise inputs of a total function `F`) has depth `q` with `N ≤ q² log₂ N`, so
`q ≥ (N / log₂ N)^{1/2} = N^{1/2 - o(1)}`. -/
theorem simon_separation_inputLength (E : Fin N ≃ (Fin n → Bool) × Fin n) (i₀ : Fin N)
    (hn : 1 ≤ n) :
    (∀ X s, SimonPromise (simonFun E X) s →
      |measureProb (run (simonAlg (n + 2) E i₀) (simonInit i₀) X ((n + 2) * n))
        (simonAccept (n + 2) n) - bitVal ℝ (decide (s ≠ 0))| < 1 / 4) ∧
    (n + 2) * n ≤ 3 * Nat.log 2 N ^ 2 ∧
    ∀ (μ : RandomizedDecisionTree (Fin N) Bool) (F : (Fin N → Bool) → Bool),
      (∀ X s, SimonPromise (simonFun E X) s → F X = decide (s ≠ 0)) →
      (∀ X s, SimonPromise (simonFun E X) s → μ.errorProb F X ≤ 1 / 3) →
      N ≤ Nat.log 2 N * μ.depth ^ 2 := by
  have hN : N = 2 ^ n * n := by
    simpa [Fintype.card_prod, Fintype.card_fun] using Fintype.card_congr E
  have hlog : n ≤ Nat.log 2 N := by
    refine Nat.le_log_of_pow_le (by norm_num) ?_
    rw [hN]
    exact Nat.le_mul_of_pos_right _ hn
  refine ⟨(simonAlg_spec E i₀).2, ?_, fun μ F hF hμ => ?_⟩
  · calc (n + 2) * n ≤ (3 * n) * n := Nat.mul_le_mul_right _ (by omega)
      _ = 3 * n ^ 2 := by ring
      _ ≤ 3 * Nat.log 2 N ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlog 2)
  · have h := simon_two_pow_le_depth_sq E μ F hF hμ hn
    calc N = 2 ^ n * n := hN
      _ ≤ μ.depth ^ 2 * Nat.log 2 N := Nat.mul_le_mul h hlog
      _ = Nat.log 2 N * μ.depth ^ 2 := mul_comm _ _

end Cslib.Quantum
