/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Algorithms.Lean.Query.Arith.Defs
public import Mathlib.Data.Vector.Basic

/-!
# The fast Fourier transform as an arithmetic query program

This module defines the radix-2 Cooley–Tukey fast Fourier transform ([CooleyTukey1965];
[CLRS2009], Section 30.2) and FFT-based cyclic convolution as programs in cslib's arithmetic query
model `FreeM (ArithQuery α)`. Every ring addition, subtraction and multiplication is a query, and
index arithmetic and reading the supplied tables are free. This is the convention of
`Cslib.Query.complexMulNaive` and of Karatsuba multiplication.

The transform of length `2 ^ k` takes a twiddle table `w : ℕ → α`, which the correctness theorems
assume satisfies `w j = ω ^ j` for `j < 2 ^ (k - 1)`. `Cslib.Query.fftMul` computes that table
itself, at a cost of `2 ^ k - 1` multiplications, so its cost covers all of its ring arithmetic.

## Main definitions

* `Cslib.Query.FFT.butterfly w e o`: the radix-2 butterfly `(e + w o, e - w o)`, one
  multiplication and two additive operations.
* `Cslib.Query.fft k w a`: the recursive radix-2 transform of `a : Fin (2 ^ k) → α`.
* `Cslib.Query.ifft k w nInv a`: the inverse transform, a forward transform followed by index
  negation and scaling by `nInv`.
* `Cslib.Query.cyclicMul k w nInv a b`: cyclic convolution by two forward transforms, a pointwise
  product and one inverse transform.
* `Cslib.Query.FFT.powersFrom ω r c`: the list `c, c ω, …, c ω ^ (r - 1)`, using `r - 1`
  multiplications.
* `Cslib.Query.fftMul k ω nInv a b`: `cyclicMul` of length `2 ^ (k + 1)` with the twiddle table
  computed by `powersFrom`.

## References

* [Cooley and Tukey, *An Algorithm for the Machine Calculation of Complex Fourier
  Series*][CooleyTukey1965].
* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009], Section 30.2.
-/

public section

namespace Cslib.Query

open ArithQuery

variable {α : Type}

namespace FFT

/-- The radix-2 butterfly: from the twiddle factor `w` and the transforms `e`, `o` of the even
and odd parts, compute `(e + w * o, e - w * o)` with one multiplication, one addition and one
subtraction. -/
@[expose] def butterfly (w e o : α) : FreeM (ArithQuery α) (α × α) := do
  let t ← doMul w o
  let s ← doAdd e t
  let d ← doSub e t
  return (s, d)

end FFT

/-- The radix-2 Cooley–Tukey fast Fourier transform of `a : Fin (2 ^ k) → α` with twiddle table
`w`. Length `1` is the identity. For length `2 ^ (k + 1)` it transforms the even- and
odd-indexed halves recursively, with the table `j ↦ w (2 j)`, and combines output `j` and
`j + 2 ^ k` with one butterfly using the twiddle factor `w j`. -/
@[expose] def fft : (k : ℕ) → (ℕ → α) → (Fin (2 ^ k) → α) →
    FreeM (ArithQuery α) (Fin (2 ^ k) → α)
  | 0, _, a => pure a
  | k + 1, w, a => do
    let e ← fft k (fun j => w (2 * j)) fun i => a ⟨2 * i, by rw [Nat.pow_succ']; omega⟩
    let o ← fft k (fun j => w (2 * j)) fun i => a ⟨2 * i + 1, by rw [Nat.pow_succ']; omega⟩
    let y ← List.Vector.mOfFn fun j : Fin (2 ^ k) => FFT.butterfly (w j) (e j) (o j)
    return fun i => if h : (i : ℕ) < 2 ^ k then (y.get ⟨i, h⟩).1 else
      (y.get ⟨i - 2 ^ k, by have := i.isLt; have := pow_succ' 2 k; omega⟩).2

/-- The inverse fast Fourier transform: the forward transform `y` of `a`, then
`j ↦ nInv * y (-j)`. With `w j = ω ^ j` and `nInv * 2 ^ k = 1` this inverts the forward
transform (`Cslib.Query.eval_ifft_dft`). -/
@[expose] def ifft (k : ℕ) (w : ℕ → α) (nInv : α) (a : Fin (2 ^ k) → α) :
    FreeM (ArithQuery α) (Fin (2 ^ k) → α) := do
  let y ← fft k w a
  let z ← List.Vector.mOfFn fun j : Fin (2 ^ k) => doMul nInv (y (-j))
  return z.get

/-- Cyclic convolution of `a` and `b` of length `2 ^ k` via the convolution theorem: transform
both, multiply pointwise, and transform back. -/
@[expose] def cyclicMul (k : ℕ) (w : ℕ → α) (nInv : α) (a b : Fin (2 ^ k) → α) :
    FreeM (ArithQuery α) (Fin (2 ^ k) → α) := do
  let A ← fft k w a
  let B ← fft k w b
  let C ← List.Vector.mOfFn fun j : Fin (2 ^ k) => doMul (A j) (B j)
  ifft k w nInv C.get

namespace FFT

/-- `powersFrom ω r c` is the list `c, c * ω, …, c * ω ^ (r - 1)`, computed with `r - 1`
multiplications. -/
@[expose] def powersFrom (ω : α) : ℕ → α → FreeM (ArithQuery α) (List α)
  | 0, _ => pure []
  | 1, c => pure [c]
  | r + 2, c => do
    let c' ← doMul c ω
    let rest ← powersFrom ω (r + 1) c'
    return c :: rest

end FFT

/-- FFT-based cyclic convolution of length `2 ^ (k + 1)` from `ω` and `nInv` alone. The twiddle
table `1, ω, …, ω ^ (2 ^ k - 1)` is computed with `2 ^ k - 1` multiplications, then `cyclicMul`
runs. With `ω ^ (2 ^ k) = -1` and `nInv * 2 ^ (k + 1) = 1` it computes the cyclic convolution
(`Cslib.Query.eval_fftMul`), and hence products of polynomials with
`natDegree p + natDegree q < 2 ^ (k + 1)` (`Cslib.Query.eval_fftMul_coeff`). -/
@[expose] def fftMul [One α] (k : ℕ) (ω nInv : α) (a b : Fin (2 ^ (k + 1)) → α) :
    FreeM (ArithQuery α) (Fin (2 ^ (k + 1)) → α) := do
  let table ← FFT.powersFrom ω (2 ^ k) 1
  cyclicMul (k + 1) (fun j => table.getD j 1) nInv a b

end Cslib.Query
