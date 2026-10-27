/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.KernelVector
public import Complexity.Foundations.Data.Code.HintDecoding
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Circuits for Reed–Solomon decoding with a hint

Sudan decoding with a hint (`Cslib.Code.hintDecode`) is an arithmetic computation on the received
word, the hint and fixed constants: elimination for the interpolant of least `Y`-degree, then
Newton iteration evaluated on all of `F`. Over the full binary basis of the field, where every
operation on at most two field elements is one gate, it therefore has circuits of size polynomial
in `|F|`, the number of points and the number of monomials. For `n` points, `M` monomials of
`(1, d)`-weighted degree at most `D`, `ℓ = D / d` and `q = |F|`:

* the interpolant costs at most `interpolantCost n M ℓ` gates
  (`Cslib.Circuits.Synthesis.full_interpolantCoeffs`), dominated by `ℓ + 1` eliminations of
  `kernelVecCost n M` gates each;
* Newton iteration to degree `d` costs at most `henselCost q M d` gates
  (`Cslib.Circuits.Synthesis.full_henselValue`);
* the whole decoder costs at most `hintDecodeCost n q M ℓ d`, their sum
  (`Cslib.Circuits.Synthesis.full_hintDecode`).

The word, the hint position and the hint value may be arbitrary available functions of the
circuit's inputs.

## Main definitions

* `Cslib.Circuits.interpolantCost`, `Cslib.Circuits.henselStepCost`,
  `Cslib.Circuits.henselCost`, `Cslib.Circuits.hintDecodeCost`: the gate budgets.

## Main results

* `Cslib.Circuits.Synthesis.full_interpolantCoeffs`: the interpolant of least `Y`-degree.
* `Cslib.Circuits.Synthesis.full_henselValue`: Newton iteration.
* `Cslib.Circuits.Synthesis.full_hintDecode`: decoding with a hint.

## References

* [M. Sudan, L. Trevisan, S. Vadhan, *Pseudorandom generators without the XOR lemma*]
  [SudanTrevisanVadhan2001]
* [M. Sudan, *Decoding of Reed Solomon codes beyond the error-correction bound*][Sudan1997]
-/

@[expose] public section

namespace Cslib.Circuits

/-- The gate budget of the least-`Y`-degree interpolant for `n` points, `M` monomials and
`Y`-degrees up to `ℓ`. -/
def interpolantCost (n M ℓ : ℕ) : ℕ :=
  n * M + (ℓ + 1) * kernelVecCost n M + (ℓ + 1) * (M + 1) + (2 * (ℓ + 1) + 1) +
    M * (2 * (ℓ + 1) + 1)

/-- The gate budget of one Newton step over a field with `q` elements, for `M` monomials and
degree at most `d`. -/
def henselStepCost (q M d : ℕ) : ℕ := q * (2 * d + 3 * M + 6) + 2

/-- The gate budget of Newton iteration to degree `d`. -/
def henselCost (q M d : ℕ) : ℕ := 3 * M + 1 + d * henselStepCost q M d + (2 * d + 3)

/-- The gate budget of decoding with a hint. -/
def hintDecodeCost (n q M ℓ d : ℕ) : ℕ := interpolantCost n M ℓ + henselCost q M d

namespace Synthesis

open Finset Polynomial Cslib.LinearAlgebra Cslib.Code
open scoped Polynomial.Bivariate

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {N : ℕ} {s : Set ((Fin N → F) → F)}

/-! ### Newton iteration -/

omit [DecidableEq F] in
/-- Evaluating `Q(t + τ, ∑_{i ≤ k} h_i t^i)` at all points `t : F` costs at most
`|F| * (2 * k + 3) + |F| * (3 * #M + 1)` gates when `c`, `τ`, and `h_0, …, h_k` are in `s`. -/
private theorem full_henselEval (M : Finset (ℕ × ℕ)) (c : ℕ × ℕ → (Fin N → F) → F)
    (hc : ∀ m ∈ M, c m ∈ s) {τ : (Fin N → F) → F} (hτ : τ ∈ s)
    (h : ℕ → (Fin N → F) → F) (k : ℕ) (hh : ∀ i ≤ k, h i ∈ s) :
    Synthesis (fullInterpretation (k := 2)) s
      (Set.range fun t : F => fun x =>
        ∑ m ∈ M, c m x * ((t + τ x) ^ m.1 * (∑ i ∈ range (k + 1), h i x * t ^ i) ^ m.2))
      (Fintype.card F * (2 * k + 3) + Fintype.card F * (3 * #M + 1)) := by
  -- the values of the current iterate at all points
  let A : F → (Fin N → F) → F := fun t x => ∑ i ∈ range (k + 1), h i x * t ^ i
  have h₁ : Synthesis (fullInterpretation (k := 2)) s (Set.range A)
      (Fintype.card F * (2 * k + 3)) := by
    have := family (I := fullInterpretation (k := 2)) (s := s) A (fun _ => 2 * k + 3) fun t => by
      have hmul := biUnion (I := fullInterpretation (k := 2)) (s := s) (range (k + 1))
        (fun i => {fun x => h i x * t ^ i}) (fun _ => 1) fun i hi =>
          full_unary (fun v => v * t ^ i) (hh i (Nat.lt_succ_iff.1 (mem_range.1 hi)))
      have hsum := full_sum (s := s ∪ ⋃ i ∈ range (k + 1), {fun x => h i x * t ^ i})
        (range (k + 1)) (fun i x => h i x * t ^ i) fun i hi =>
          Set.mem_union_right _ (Set.mem_biUnion hi rfl)
      refine (hmul.trans hsum).mono Set.Subset.rfl Set.Subset.rfl ?_
      simp only [sum_const, card_range, smul_eq_mul, mul_one]
      omega
    simpa [card_univ] using this
  -- the values `Q(t + τ, A(t))`
  let V : F → (Fin N → F) → F := fun t x => ∑ m ∈ M, c m x * ((t + τ x) ^ m.1 * A t x ^ m.2)
  have h₂ : Synthesis (fullInterpretation (k := 2)) (s ∪ Set.range A) (Set.range V)
      (Fintype.card F * (3 * #M + 1)) := by
    have := family (I := fullInterpretation (k := 2)) (s := s ∪ Set.range A) V
      (fun _ => 3 * #M + 1) fun t => by
        have hg := biUnion (I := fullInterpretation (k := 2)) (s := s ∪ Set.range A) M
          (fun m => {fun x => (t + τ x) ^ m.1 * A t x ^ m.2}) (fun _ => 1) fun m _ =>
            full_binary_mem (fun u v => (t + u) ^ m.1 * v ^ m.2)
              (Set.mem_union_left _ hτ) (Set.mem_union_right _ ⟨t, rfl⟩)
        have hdot := full_dot
          (s := (s ∪ Set.range A) ∪ ⋃ m ∈ M, {fun x => (t + τ x) ^ m.1 * A t x ^ m.2}) M c
          (fun m x => (t + τ x) ^ m.1 * A t x ^ m.2)
          (fun m hm => Set.mem_union_left _ (Set.mem_union_left _ (hc m hm)))
          (fun m hm => Set.mem_union_right _ (Set.mem_biUnion hm rfl))
        refine (hg.trans hdot).mono Set.Subset.rfl Set.Subset.rfl ?_
        simp only [sum_const, smul_eq_mul, mul_one]
        omega
    simpa [card_univ] using this
  exact h₁.trans h₂

/-- Synthesizing the `(k + 1)`-st Newton coefficient from `c`, `τ`, `a`, `lam`, and the first
`k + 1` coefficients costs at most `henselStepCost (Fintype.card F) #M d` gates for `k + 1 ≤ d`. -/
private theorem full_henselStep (M : Finset (ℕ × ℕ)) (c : ℕ × ℕ → (Fin N → F) → F)
    (hc : ∀ m ∈ M, c m ∈ s) {τ a lam : (Fin N → F) → F} (hτ : τ ∈ s) (hlam : lam ∈ s)
    {k d : ℕ} (hk : k + 1 ≤ d)
    (h : ℕ → (Fin N → F) → F) (hhdef : ∀ i x,
      h i x = henselSeq (Sudan.bivariateOf M fun m => c m x) (τ x) (a x) (lam x) i)
    (hh : ∀ i ≤ k, h i ∈ s) :
    Synthesis (fullInterpretation (k := 2)) s {h (k + 1)}
      (henselStepCost (Fintype.card F) #M d) := by
  let V : F → (Fin N → F) → F := fun t x =>
    ∑ m ∈ M, c m x * ((t + τ x) ^ m.1 * (∑ i ∈ range (k + 1), h i x * t ^ i) ^ m.2)
  have h₁₂ : Synthesis (fullInterpretation (k := 2)) s (Set.range V)
      (Fintype.card F * (2 * k + 3) + Fintype.card F * (3 * #M + 1)) :=
    full_henselEval M c hc hτ h k hh
  -- the weighted sum
  let W : (Fin N → F) → F := fun x => ∑ t, coeffWeight (k + 1) t * V t x
  have h₃ : Synthesis (fullInterpretation (k := 2)) (s ∪ Set.range V) {W}
      (2 * Fintype.card F + 1) := by
    have hmul := biUnion (I := fullInterpretation (k := 2)) (s := s ∪ Set.range V) univ
      (fun t => {fun x => coeffWeight (k + 1) t * V t x}) (fun _ => 1) fun t _ =>
        full_unary (fun v => coeffWeight (k + 1) t * v) (Set.mem_union_right _ ⟨t, rfl⟩)
    have hsum := full_sum (s := (s ∪ Set.range V) ∪ ⋃ t ∈ (univ : Finset F),
        {fun x => coeffWeight (k + 1) t * V t x}) univ
      (fun t x => coeffWeight (k + 1) t * V t x) fun t ht =>
        Set.mem_union_right _ (Set.mem_biUnion ht rfl)
    refine (hmul.trans hsum).mono Set.Subset.rfl Set.Subset.rfl ?_
    simp only [sum_const, card_univ, smul_eq_mul, mul_one]
    omega
  -- the new coefficient
  have h₄ : Synthesis (fullInterpretation (k := 2)) ((s ∪ Set.range V) ∪ {W})
      {fun x => -W x / lam x} 1 :=
    full_binary_mem (fun u v => -u / v) (Set.mem_union_right _ rfl)
      (Set.mem_union_left _ (Set.mem_union_left _ hlam))
  refine (h₁₂.trans (h₃.trans h₄)).mono Set.Subset.rfl ?_ ?_
  · refine Set.singleton_subset_iff.2 (funext fun x => ?_)
    rw [hhdef, henselSeq, henselCoeff]
    simp only [W, V, hhdef, eval_henselTrunc, Sudan.evalEval_bivariateOf, mul_assoc]
  · unfold henselStepCost
    nlinarith

/-- The coefficients chosen by Newton iteration up to `k` cost `k * henselStepCost q M d` gates,
for `k ≤ d`, given the coefficients of `Q`, the hint position and value and `λ`. -/
private theorem full_henselSeq (M : Finset (ℕ × ℕ)) (c : ℕ × ℕ → (Fin N → F) → F)
    (hc : ∀ m ∈ M, c m ∈ s) {τ a lam : (Fin N → F) → F} (hτ : τ ∈ s) (ha : a ∈ s)
    (hlam : lam ∈ s) (d : ℕ) :
    ∀ k ≤ d, Synthesis (fullInterpretation (k := 2)) s
      (Set.range fun i : Fin (k + 1) => fun x =>
        henselSeq (Sudan.bivariateOf M fun m => c m x) (τ x) (a x) (lam x) i)
      (k * henselStepCost (Fintype.card F) #M d) := by
  intro k hk
  induction k with
  | zero =>
    rw [zero_mul]
    refine of_subset ?_
    rintro _ ⟨i, rfl⟩
    rw [Fin.fin_one_eq_zero i]
    exact ha
  | succ k ih =>
    set T := Set.range fun i : Fin (k + 1) => fun x =>
      henselSeq (Sudan.bivariateOf M fun m => c m x) (τ x) (a x) (lam x) i
    let h : ℕ → (Fin N → F) → F := fun i x =>
      henselSeq (Sudan.bivariateOf M fun m => c m x) (τ x) (a x) (lam x) i
    have hstep := full_henselStep (s := s ∪ T) M c (fun m hm => Set.mem_union_left _ (hc m hm))
      (Set.mem_union_left _ hτ) (Set.mem_union_left _ hlam) hk h (fun _ _ => rfl)
      (fun i hi => Set.mem_union_right _ ⟨⟨i, Nat.lt_succ_of_le hi⟩, rfl⟩)
    refine ((ih (Nat.le_of_succ_le hk)).comp hstep).mono Set.Subset.rfl ?_ (by rw [Nat.succ_mul])
    rintro _ ⟨i, rfl⟩
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
    · exact Set.mem_union_left _ ⟨i, rfl⟩
    · exact Set.mem_union_right _ rfl

/-- **Newton iteration by a circuit.** Given the coefficients on `M` of `Q`, the hint position and
the hint value as available functions, `henselValue Q τ a d` costs at most `henselCost q M d`
gates of the full binary basis. -/
theorem full_henselValue (M : Finset (ℕ × ℕ)) (c : ℕ × ℕ → (Fin N → F) → F)
    (hc : ∀ m ∈ M, c m ∈ s) {τ a : (Fin N → F) → F} (hτ : τ ∈ s) (ha : a ∈ s) (d : ℕ) :
    Synthesis (fullInterpretation (k := 2)) s
      {fun x => henselValue (Sudan.bivariateOf M fun m => c m x) (τ x) (a x) d}
      (henselCost (Fintype.card F) #M d) := by
  -- the derivative `λ`
  let lam : (Fin N → F) → F := fun x => ∑ m ∈ M, c m x * (m.2 * τ x ^ m.1 * a x ^ (m.2 - 1))
  have h₁ : Synthesis (fullInterpretation (k := 2)) s {lam} (3 * #M + 1) := by
    have hg := biUnion (I := fullInterpretation (k := 2)) (s := s) M
      (fun m => {fun x => (m.2 : F) * τ x ^ m.1 * a x ^ (m.2 - 1)}) (fun _ => 1)
      (fun m _ => full_binary_mem (fun u v => (m.2 : F) * u ^ m.1 * v ^ (m.2 - 1)) hτ ha)
    have hdot := full_dot (s := s ∪ ⋃ m ∈ M, {fun x => (m.2 : F) * τ x ^ m.1 * a x ^ (m.2 - 1)})
      M c (fun m x => (m.2 : F) * τ x ^ m.1 * a x ^ (m.2 - 1))
      (fun m hm => Set.mem_union_left _ (hc m hm))
      (fun m hm => Set.mem_union_right _ (Set.mem_biUnion hm rfl))
    refine (hg.trans hdot).mono Set.Subset.rfl Set.Subset.rfl ?_
    simp only [sum_const, smul_eq_mul, mul_one]
    omega
  set s₁ := s ∪ {lam}
  have h₂ := full_henselSeq (s := s₁) M c (fun m hm => Set.mem_union_left _ (hc m hm))
    (Set.mem_union_left _ hτ) (Set.mem_union_left _ ha) (Set.mem_union_right _ rfl) d d le_rfl
  set T := Set.range fun i : Fin (d + 1) => fun x =>
    henselSeq (Sudan.bivariateOf M fun m => c m x) (τ x) (a x) (lam x) i
  -- the value at `-τ`
  let h : ℕ → (Fin N → F) → F := fun i x =>
    henselSeq (Sudan.bivariateOf M fun m => c m x) (τ x) (a x) (lam x) i
  have h₃ : Synthesis (fullInterpretation (k := 2)) (s₁ ∪ T)
      {fun x => ∑ i ∈ range (d + 1), h i x * (-τ x) ^ i} (2 * d + 3) := by
    have hmul := biUnion (I := fullInterpretation (k := 2)) (s := s₁ ∪ T) (range (d + 1))
      (fun i => {fun x => h i x * (-τ x) ^ i}) (fun _ => 1)
      (fun i hi => full_binary_mem (fun u v => u * (-v) ^ i)
        (Set.mem_union_right _ ⟨⟨i, mem_range.1 hi⟩, rfl⟩)
        (Set.mem_union_left _ (Set.mem_union_left _ hτ)))
    have hsum := full_sum (s := (s₁ ∪ T) ∪ ⋃ i ∈ range (d + 1), {fun x => h i x * (-τ x) ^ i})
      (range (d + 1)) (fun i x => h i x * (-τ x) ^ i)
      (fun i hi => Set.mem_union_right _ (Set.mem_biUnion hi rfl))
    refine (hmul.trans hsum).mono Set.Subset.rfl Set.Subset.rfl ?_
    simp only [sum_const, card_range, smul_eq_mul, mul_one]
    omega
  refine (h₁.trans (h₂.trans h₃)).mono Set.Subset.rfl ?_ ?_
  · refine Set.singleton_subset_iff.2 (funext fun x => ?_)
    simp only [henselValue, eval_henselTrunc, evalEval_derivative_bivariateOf, h, lam]
  · unfold henselCost
    omega

/-! ### The interpolant -/

variable {ι : Type*} [Fintype ι]

omit [Fintype F] in
/-- Synthesizing the kernel vectors `Sudan.kernelVecUpTo α w d D j` for all `j : Fin (D / d + 1)`
costs at most `|ι| * #M + (D / d + 1) * kernelVecCost |ι| #M` gates. -/
private theorem full_kernelVecUpTo (α : ι → F) (w : ι → (Fin N → F) → F) (hw : ∀ i, w i ∈ s)
    (d D : ℕ) :
    Synthesis (fullInterpretation (k := 2)) s
      (⋃ j : Fin (D / d + 1), Set.range fun m : Fin #(Sudan.monomialsUpTo d D j) =>
        fun x => Sudan.kernelVecUpTo α (fun i => w i x) d D j m)
      (Fintype.card ι * #(Sudan.monomials d D) +
        (D / d + 1) * kernelVecCost (Fintype.card ι) #(Sudan.monomials d D)) := by
  set M := Sudan.monomials d D
  set ℓ := D / d
  -- the entries of the interpolation matrix
  let E : ι × M → (Fin N → F) → F := fun tm x =>
    α tm.1 ^ (tm.2 : ℕ × ℕ).1 * w tm.1 x ^ (tm.2 : ℕ × ℕ).2
  have h₁ : Synthesis (fullInterpretation (k := 2)) s (Set.range E) (Fintype.card ι * #M) := by
    have := family (I := fullInterpretation (k := 2)) (s := s) E (fun _ => 1) fun tm =>
      full_unary (fun v => α tm.1 ^ (tm.2 : ℕ × ℕ).1 * v ^ (tm.2 : ℕ × ℕ).2) (hw tm.1)
    simpa [card_univ, Fintype.card_prod, Fintype.card_coe] using this
  -- the kernel vectors
  let u : (j : Fin (ℓ + 1)) → Fin #(Sudan.monomialsUpTo d D j) → (Fin N → F) → F :=
    fun j m x => Sudan.kernelVecUpTo α (fun i => w i x) d D j m
  have hsubM : ∀ j : ℕ, Sudan.monomialsUpTo d D j ⊆ M := fun _ => filter_subset _ _
  have h₂ : Synthesis (fullInterpretation (k := 2)) (s ∪ Set.range E)
      (⋃ j : Fin (ℓ + 1), Set.range (u j)) ((ℓ + 1) * kernelVecCost (Fintype.card ι) #M) := by
    have := iUnion (I := fullInterpretation (k := 2)) (s := s ∪ Set.range E)
      (fun j : Fin (ℓ + 1) => Set.range (u j)) (fun _ => kernelVecCost (Fintype.card ι) #M)
      fun j => by
        refine (full_kernelVec (s := s ∪ Set.range E)
          (fun t m x => Sudan.interpMatrix α (fun i => w i x) (Sudan.monomialsUpTo d D j) t m)
          fun t m => Set.mem_union_right _ ⟨((Fintype.equivFin ι).symm t,
            ⟨_, hsubM j ((Sudan.monomialsUpTo d D j).equivFin.symm m).2⟩), rfl⟩).mono
          Set.Subset.rfl (by rintro _ ⟨m, rfl⟩; exact ⟨m, rfl⟩) ?_
        unfold kernelVecCost
        have : #(Sudan.monomialsUpTo d D j) ≤ #M := card_le_card (hsubM j)
        have : (#(Sudan.monomialsUpTo d D j) + 1) ^ 2 ≤ (#M + 1) ^ 2 :=
          Nat.pow_le_pow_left (by omega) 2
        nlinarith
    simpa [card_univ] using this
  exact h₁.trans h₂

omit [Fintype F] in
/-- The interpolant coefficient at a monomial `m` is the dot product over the degree bounds `j`
whose monomial set contains `m` of the first-nonzero flag and the `j`-th kernel vector entry. -/
private theorem interpolantCoeffs_eq_sum (α : ι → F) (w : ι → F) (d D : ℕ) (m : ℕ × ℕ) :
    Sudan.interpolantCoeffs α w d D m =
      ∑ j ∈ univ.filter (fun j : Fin (D / d + 1) => m ∈ Sudan.monomialsUpTo d D j),
        firstFlags (fun j => if Sudan.kernelVecUpTo α w d D j = 0 then (0 : F) else 1) j *
          Sudan.coeffsOf (Sudan.monomialsUpTo d D j) (Sudan.kernelVecUpTo α w d D j) m := by
  simp only [Sudan.interpolantCoeffs, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sum_filter]
  refine sum_congr rfl fun j _ => ?_
  split_ifs with hj
  · rfl
  · simp only [Sudan.coeffsOf, dite_eq_right hj, mul_zero]

omit [Fintype F] in
/-- **The least-`Y`-degree interpolant by a circuit.** Given the received word as available
functions, its interpolant coefficients on `monomials d D` cost at most
`interpolantCost n M (D / d)` gates of the full binary basis, for `n` points and `M` monomials. -/
theorem full_interpolantCoeffs (α : ι → F) (w : ι → (Fin N → F) → F) (hw : ∀ i, w i ∈ s)
    (d D : ℕ) :
    Synthesis (fullInterpretation (k := 2)) s
      (Set.range fun m : Sudan.monomials d D => fun x =>
        Sudan.interpolantCoeffs α (fun i => w i x) d D m)
      (interpolantCost (Fintype.card ι) #(Sudan.monomials d D) (D / d)) := by
  have h₁₂ := full_kernelVecUpTo α w hw d D
  set M := Sudan.monomials d D
  set ℓ := D / d
  let u : (j : Fin (ℓ + 1)) → Fin #(Sudan.monomialsUpTo d D j) → (Fin N → F) → F :=
    fun j m x => Sudan.kernelVecUpTo α (fun i => w i x) d D j m
  set s₂ := s ∪ ⋃ j : Fin (ℓ + 1), Set.range (u j)
  have hu : ∀ j m, u j m ∈ s₂ := fun j m => Set.mem_union_right _ (Set.mem_iUnion.2 ⟨j, ⟨m, rfl⟩⟩)
  -- their nonzero indicators
  let z : Fin (ℓ + 1) → (Fin N → F) → F := fun j x => if (fun m => u j m x) = 0 then 0 else 1
  have h₃ : Synthesis (fullInterpretation (k := 2)) s₂ (Set.range z) ((ℓ + 1) * (#M + 1)) := by
    simpa [card_univ] using family (I := fullInterpretation (k := 2)) (s := s₂) z
      (fun _ => #M + 1) fun j => (full_nonzero (u j) (hu j)).mono Set.Subset.rfl Set.Subset.rfl
        (by have : #(Sudan.monomialsUpTo d D j) ≤ #M := card_le_card (filter_subset _ _); omega)
  -- the first nonzero kernel vector
  let f : Fin (ℓ + 1) → (Fin N → F) → F := fun j x => firstFlags (fun j => z j x) j
  have h₄ := full_firstFlags (s := s₂ ∪ Set.range z) z fun j => Set.mem_union_right _ ⟨j, rfl⟩
  set s₄ := (s₂ ∪ Set.range z) ∪ Set.range f
  -- the coefficients
  let J (m : ℕ × ℕ) : Finset (Fin (ℓ + 1)) := univ.filter fun j => m ∈ Sudan.monomialsUpTo d D j
  let coef (m : M) (x : Fin N → F) : F :=
    ∑ j ∈ J m, f j x * Sudan.coeffsOf (Sudan.monomialsUpTo d D j) (fun m' => u j m' x) m
  have h₅ : Synthesis (fullInterpretation (k := 2)) s₄ (Set.range coef)
      (#M * (2 * (ℓ + 1) + 1)) := by
    simpa [card_univ, Fintype.card_coe] using family (I := fullInterpretation (k := 2)) (s := s₄)
      coef (fun _ => 2 * (ℓ + 1) + 1) fun m => by
        refine (full_dot (s := s₄) (J m) f (fun j x => Sudan.coeffsOf
          (Sudan.monomialsUpTo d D j) (fun m' => u j m' x) m)
          (fun j _ => Set.mem_union_right _ ⟨j, rfl⟩) fun j hj => ?_).mono
          Set.Subset.rfl Set.Subset.rfl ?_
        · have hm : (m : ℕ × ℕ) ∈ Sudan.monomialsUpTo d D j := (mem_filter.1 hj).2
          rw [show (fun x => Sudan.coeffsOf (Sudan.monomialsUpTo d D j) (fun m' => u j m' x) m) =
            u j ((Sudan.monomialsUpTo d D j).equivFin ⟨m, hm⟩) from
              funext fun x => by simp only [Sudan.coeffsOf, dite_eq_left hm]]
          exact Set.mem_union_left _ (Set.mem_union_left _ (hu j _))
        · have : #(J m) ≤ ℓ + 1 := (card_le_univ _).trans (by simp)
          omega
  refine (h₁₂.trans (h₃.trans (h₄.trans h₅))).mono Set.Subset.rfl ?_
    (by unfold interpolantCost; omega)
  rintro _ ⟨m, rfl⟩
  exact ⟨m, funext fun x => (interpolantCoeffs_eq_sum α (fun i => w i x) d D m).symm⟩

/-- **Decoding with a hint by a circuit.** Given the received word, the hint position and the
hint value as available functions, `hintDecode α w d D τ a` costs at most
`hintDecodeCost n q M (D / d) d` gates of the full binary basis, for `n` points, `q = |F|` and
`M` monomials of `(1, d)`-weighted degree at most `D`. -/
theorem full_hintDecode (α : ι → F) (w : ι → (Fin N → F) → F) (hw : ∀ i, w i ∈ s)
    {τ a : (Fin N → F) → F} (hτ : τ ∈ s) (ha : a ∈ s) (d D : ℕ) :
    Synthesis (fullInterpretation (k := 2)) s
      {fun x => hintDecode α (fun i => w i x) d D (τ x) (a x)}
      (hintDecodeCost (Fintype.card ι) (Fintype.card F) #(Sudan.monomials d D) (D / d) d) := by
  have h₁ := full_interpolantCoeffs α w hw d D
  set T := Set.range fun m : Sudan.monomials d D => fun x =>
    Sudan.interpolantCoeffs α (fun i => w i x) d D m
  have h₂ := full_henselValue (s := s ∪ T) (Sudan.monomials d D)
    (fun m x => Sudan.interpolantCoeffs α (fun i => w i x) d D m)
    (fun m hm => Set.mem_union_right _ ⟨⟨m, hm⟩, rfl⟩) (Set.mem_union_left _ hτ)
    (Set.mem_union_left _ ha) d
  exact (h₁.trans h₂).mono Set.Subset.rfl Set.Subset.rfl le_rfl

end Synthesis

end Cslib.Circuits
