/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.Query.Arith.FFT.Defs
public import Complexity.Foundations.Algebra.DFT
import Complexity.Algorithms.Lean.Query.FreeM.MOfFn

/-!
# Correctness of the fast Fourier transform and FFT multiplication

Under the honest oracle, which interprets queries by the ring operations of a commutative ring
`α`, the programs of `Complexity.Algorithms.Lean.Query.Arith.FFT.Defs` compute their
specifications:

* `Cslib.Query.fft (k + 1) w` computes `Cslib.dft ω` when `w j = ω ^ j` for `j < 2 ^ k` and
  `ω ^ (2 ^ k) = -1` (`Cslib.Query.eval_fft`). The induction follows the Cooley–Tukey splitting
  `Cslib.dft_eq_add_of_lt`, `Cslib.dft_eq_sub_of_le`. The hypothesis `ω ^ (2 ^ k) = -1` cannot be
  dropped: the test module `ComplexityTests.FFT` checks that with `ω = 4` in `ZMod 15`, where
  `4 ^ 2 = 1`, the program and the DFT differ. In an integral domain the hypothesis follows from
  `ω` being a primitive `2 ^ (k + 1)`-th root of unity (`IsPrimitiveRoot.pow_two_pow_eq_neg_one`).
* `Cslib.Query.ifft` inverts `fft` when moreover `nInv * 2 ^ (k + 1) = 1`, by the inversion
  formula `Cslib.dft_dft_neg` and `IsPrincipalRoot.of_pow_two_pow_eq_neg_one`.
* `Cslib.Query.cyclicMul` and `Cslib.Query.fftMul` compute the cyclic convolution, by the
  convolution theorem `Cslib.dft_cyclicConv`, and hence the product of polynomials whose degrees
  sum to less than the length (`Cslib.Query.eval_fftMul_coeff`, `Cslib.Query.eval_fftMul_eq_mul`).

## Main results

* `Cslib.Query.eval_fft`: the FFT computes the DFT.
* `Cslib.Query.eval_fft_of_isPrimitiveRoot`: the same for a primitive root in a domain.
* `Cslib.Query.eval_ifft_dft`: the inverse FFT inverts the DFT.
* `Cslib.Query.eval_cyclicMul`, `Cslib.Query.eval_fftMul`: FFT multiplication computes the cyclic
  convolution.
* `Cslib.Query.eval_fftMul_coeff`: FFT multiplication of coefficient vectors computes the
  coefficients of `p * q` when `natDegree p + natDegree q < 2 ^ (k + 1)`.
* `Cslib.Query.eval_fftMul_eq_mul`: the same, stated as an equality of polynomials.

## References

* [Cooley and Tukey, *An Algorithm for the Machine Calculation of Complex Fourier
  Series*][CooleyTukey1965].
* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009], Section 30.2
  and Theorem 30.8.
-/

public section

namespace Cslib.Query

open ArithQuery

variable {α : Type} [CommRing α]

namespace FFT

/-- The butterfly computes `(e + w * o, e - w * o)`. -/
theorem eval_butterfly (w e o : α) : (butterfly w e o).eval honest = (e + w * o, e - w * o) :=
  rfl

/-- `powersFrom ω r c` returns a list of length `r` under every oracle. -/
theorem length_eval_powersFrom {β : Type} (oracle : {ι : Type} → ArithQuery β ι → ι) (ω : β)
    (r : ℕ) (c : β) : ((powersFrom ω r c).eval oracle).length = r := by
  induction r using Nat.strongRecOn generalizing c with
  | ind r ih =>
    match r with
    | 0 => rfl
    | 1 => rfl
    | r + 2 =>
      simp only [powersFrom, FreeM.eval_bind, FreeM.eval_pure, List.length_cons, doMul,
        FreeM.eval_lift]
      rw [ih (r + 1) (by omega)]

/-- Entry `i` of `powersFrom ω r c` is `c * ω ^ i` under the honest oracle. -/
theorem getElem_eval_powersFrom (ω : α) (r : ℕ) (c : α) (i : ℕ)
    (hi : i < ((powersFrom ω r c).eval honest).length) :
    ((powersFrom ω r c).eval honest)[i] = c * ω ^ i := by
  induction r using Nat.strongRecOn generalizing c i with
  | ind r ih =>
    match r, hi with
    | 0, hi => simp [powersFrom] at hi
    | 1, hi =>
      simp only [powersFrom, FreeM.eval_pure, List.length_singleton, Nat.lt_one_iff] at hi ⊢
      subst hi
      simp
    | r + 2, hi =>
      simp only [powersFrom, FreeM.eval_bind, FreeM.eval_pure, doMul, FreeM.eval_lift] at hi ⊢
      rcases i with _ | i
      · simp
      · simp only [List.getElem_cons_succ]
        rw [ih (r + 1) (by omega)]
        simp only [honest]
        ring

end FFT

open FFT

/-- One Cooley–Tukey step: if the half-length transform with table `j ↦ w (2 j)` computes the
DFT for `ω ^ 2`, then the full transform computes the DFT for `ω`. -/
private theorem eval_fft_step {k : ℕ} {ω : α} {w : ℕ → α}
    (hw : ∀ j < 2 ^ k, w j = ω ^ j) (hω : ω ^ 2 ^ k = -1)
    (ih : ∀ b, (fft k (fun j => w (2 * j)) b).eval honest = dft (ω ^ 2) b)
    (a : Fin (2 ^ (k + 1)) → α) :
    (fft (k + 1) w a).eval honest = dft ω a := by
  funext i
  simp only [fft, FreeM.eval_bind, FreeM.eval_pure, ih, FreeM.eval_mOfFn, List.Vector.get_ofFn,
    eval_butterfly]
  split_ifs with h
  · rw [dft_eq_add_of_lt (Nat.pow_succ' ..) ω a i h, hw _ h]
  · have := i.isLt
    have := pow_succ' 2 k
    rw [dft_eq_sub_of_le (Nat.pow_succ' ..) hω a i (by omega), hw _ (by omega)]

/-- **Correctness of the FFT.** If `ω ^ (2 ^ k) = -1` and the twiddle table satisfies
`w j = ω ^ j` for `j < 2 ^ k`, the radix-2 transform of length `2 ^ (k + 1)` computes the DFT
with respect to `ω`. -/
theorem eval_fft {k : ℕ} {ω : α} {w : ℕ → α} (hw : ∀ j < 2 ^ k, w j = ω ^ j)
    (hω : ω ^ 2 ^ k = -1) (a : Fin (2 ^ (k + 1)) → α) :
    (fft (k + 1) w a).eval honest = dft ω a := by
  induction k generalizing ω w with
  | zero =>
    refine eval_fft_step hw hω (fun b => ?_) a
    exact (dft_fin_one _ b).symm
  | succ k ih =>
    refine eval_fft_step hw hω (fun b => ih (fun j hj => ?_) ?_ b) a
    · rw [hw _ (by rw [pow_succ]; omega), pow_mul]
    · rw [← pow_mul, ← pow_succ', hω]

/-- The transform of length `1` is the DFT for every `ω`. -/
theorem eval_fft_zero (w : ℕ → α) (ω : α) (a : Fin (2 ^ 0) → α) :
    (fft 0 w a).eval honest = dft ω a :=
  (dft_fin_one ω a).symm

/-- **Correctness of the FFT** for a primitive `2 ^ (k + 1)`-th root of unity in a domain. -/
theorem eval_fft_of_isPrimitiveRoot [IsDomain α] {k : ℕ} {ω : α} {w : ℕ → α}
    (hw : ∀ j < 2 ^ k, w j = ω ^ j) (hω : IsPrimitiveRoot ω (2 ^ (k + 1)))
    (a : Fin (2 ^ (k + 1)) → α) :
    (fft (k + 1) w a).eval honest = dft ω a :=
  eval_fft hw hω.pow_two_pow_eq_neg_one a

/-- The inverse FFT computes `j ↦ nInv * dft ω a (-j)`. -/
theorem eval_ifft {k : ℕ} {ω : α} {w : ℕ → α} (hw : ∀ j < 2 ^ k, w j = ω ^ j)
    (hω : ω ^ 2 ^ k = -1) (nInv : α) (a : Fin (2 ^ (k + 1)) → α) :
    (ifft (k + 1) w nInv a).eval honest = fun j => nInv * dft ω a (-j) := by
  funext j
  simp only [ifft, FreeM.eval_bind, FreeM.eval_pure, eval_fft hw hω, FreeM.eval_mOfFn,
    List.Vector.get_ofFn]
  rfl

/-- **The inverse FFT inverts the DFT** when `nInv * 2 ^ (k + 1) = 1`. -/
theorem eval_ifft_dft {k : ℕ} {ω : α} {w : ℕ → α} (hw : ∀ j < 2 ^ k, w j = ω ^ j)
    (hω : ω ^ 2 ^ k = -1) {nInv : α} (hn : nInv * 2 ^ (k + 1) = 1) (a : Fin (2 ^ (k + 1)) → α) :
    (ifft (k + 1) w nInv (dft ω a)).eval honest = a := by
  rw [eval_ifft hw hω]
  funext j
  rw [dft_dft_neg (IsPrincipalRoot.of_pow_two_pow_eq_neg_one hω), ← mul_assoc, Nat.cast_pow,
    Nat.cast_ofNat, hn, one_mul]

/-- **FFT cyclic convolution is correct**: under the hypotheses of `eval_ifft_dft`, `cyclicMul`
computes the cyclic convolution. -/
theorem eval_cyclicMul {k : ℕ} {ω : α} {w : ℕ → α} (hw : ∀ j < 2 ^ k, w j = ω ^ j)
    (hω : ω ^ 2 ^ k = -1) {nInv : α} (hn : nInv * 2 ^ (k + 1) = 1)
    (a b : Fin (2 ^ (k + 1)) → α) :
    (cyclicMul (k + 1) w nInv a b).eval honest = cyclicConv a b := by
  have hω' : ω ^ 2 ^ (k + 1) = 1 := (IsPrincipalRoot.of_pow_two_pow_eq_neg_one hω).pow_eq_one
  simp only [cyclicMul, FreeM.eval_bind, eval_fft hw hω, FreeM.eval_mOfFn]
  have hprod : (fun j => (doMul (dft ω a j) (dft ω b j) : FreeM (ArithQuery α) α).eval honest) =
      dft ω (cyclicConv a b) := by
    funext j
    rw [dft_cyclicConv hω']
    rfl
  have hget : (List.Vector.ofFn (dft ω (cyclicConv a b))).get = dft ω (cyclicConv a b) :=
    funext (List.Vector.get_ofFn _)
  rw [hprod, hget, eval_ifft_dft hw hω hn]

/-- **FFT multiplication is correct**: if `ω ^ (2 ^ k) = -1` and `nInv * 2 ^ (k + 1) = 1`, then
`fftMul` computes the cyclic convolution of length `2 ^ (k + 1)`. -/
theorem eval_fftMul {k : ℕ} {ω nInv : α} (hω : ω ^ 2 ^ k = -1) (hn : nInv * 2 ^ (k + 1) = 1)
    (a b : Fin (2 ^ (k + 1)) → α) :
    (fftMul k ω nInv a b).eval honest = cyclicConv a b := by
  simp only [fftMul, FreeM.eval_bind]
  refine eval_cyclicMul (fun j hj => ?_) hω hn a b
  have hlen := length_eval_powersFrom (fun {ι} => (honest : ArithQuery α ι → ι)) ω (2 ^ k) 1
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some,
    getElem_eval_powersFrom, one_mul]

/-- **Fast polynomial multiplication**: for polynomials with
`natDegree p + natDegree q < 2 ^ (k + 1)`, `fftMul` applied to their coefficient vectors returns
the coefficient vector of `p * q`. -/
theorem eval_fftMul_coeff {k : ℕ} {ω nInv : α} (hω : ω ^ 2 ^ k = -1)
    (hn : nInv * 2 ^ (k + 1) = 1) {p q : Polynomial α}
    (hpq : p.natDegree + q.natDegree < 2 ^ (k + 1)) :
    (fftMul k ω nInv (fun i : Fin (2 ^ (k + 1)) => p.coeff i)
      (fun i : Fin (2 ^ (k + 1)) => q.coeff i)).eval honest =
      fun i : Fin (2 ^ (k + 1)) => (p * q).coeff i := by
  rw [eval_fftMul hω hn]
  funext i
  exact cyclicConv_coeff hpq i

/-- **Fast polynomial multiplication**, as an equality of polynomials: summing the monomials of
the output of `fftMul` recovers `p * q`. -/
theorem eval_fftMul_eq_mul {k : ℕ} {ω nInv : α} (hω : ω ^ 2 ^ k = -1)
    (hn : nInv * 2 ^ (k + 1) = 1) {p q : Polynomial α}
    (hpq : p.natDegree + q.natDegree < 2 ^ (k + 1)) :
    ∑ i : Fin (2 ^ (k + 1)), Polynomial.monomial i
      ((fftMul k ω nInv (fun i : Fin (2 ^ (k + 1)) => p.coeff i)
        (fun i : Fin (2 ^ (k + 1)) => q.coeff i)).eval honest i) = p * q := by
  rw [eval_fftMul_coeff hω hn hpq,
    Fin.sum_univ_eq_sum_range (fun i => Polynomial.monomial i ((p * q).coeff i))]
  exact (Polynomial.as_sum_range' (p * q) _
    (lt_of_le_of_lt Polynomial.natDegree_mul_le hpq)).symm

end Cslib.Query
