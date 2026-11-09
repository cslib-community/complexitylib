/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (follow-up to #1067)

public import Cslib.Foundations.Data.Nat.PolynomialBound
public import Mathlib.Data.Nat.Log
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Tactic.FunProp

/-!
# Closure properties of polynomial bounds

`PolynomiallyBounded` is closed under the operations that arise when accounting for sizes and
running times: addition, multiplication, fixed powers, composition, truncated subtraction,
`max`/`min`, division and remainder, logarithms and conditionals. Every closure lemma is
registered with `fun_prop`, so a goal such as

```lean
example (hf : PolynomiallyBounded f) : PolynomiallyBounded (fun n => 2 * f n ^ 3 + n - 5) := by
  fun_prop
```

is discharged automatically from the local hypothesis `hf`. This is the arithmetic engine behind
the complexity calculus: time and size polynomials of composite constructions are stated as
expressions in the component bounds and collapsed by `fun_prop`.

## Main results

* `Nat.mul_add_one_pow_le_two_pow`: an explicit bound `c * (n + 1) ^ d` is at most
  `c * 2 ^ d * n ^ d + c`.
* `Cslib.PolynomiallyBounded.mono`: a function eventually below a polynomially bounded one is
  polynomially bounded.
* `Cslib.PolynomiallyBounded.add`, `mul`, `pow`, `comp`: the closure rules proper.
* `Cslib.PolynomiallyBounded.polynomial_eval`: evaluation of a polynomial.
* `Cslib.PolynomiallyBounded.tsub`, `max`, `min`, `div`, `mod`, `log`, `ite`: operations that
  never exceed one of their arguments.
-/

@[expose] public section

/-- An explicit polynomial bound `c * (n + 1) ^ d` is a bound `O(n ^ d)`. -/
theorem Nat.mul_add_one_pow_le_two_pow (c d n : ℕ) :
    c * (n + 1) ^ d ≤ c * 2 ^ d * n ^ d + c := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    · simp [Nat.zero_pow hd]
  · have : (n + 1) ^ d ≤ 2 ^ d * n ^ d := by
      rw [← Nat.mul_pow]
      exact Nat.pow_le_pow_left (by omega) d
    calc c * (n + 1) ^ d ≤ c * (2 ^ d * n ^ d) := Nat.mul_le_mul_left c this
      _ ≤ c * 2 ^ d * n ^ d + c := by rw [Nat.mul_assoc]; omega

namespace Cslib

attribute [fun_prop] PolynomiallyBounded

namespace PolynomiallyBounded

open Filter

variable {f g : ℕ → ℕ}

/-- Produce a polynomial bound from a bound `c * (n + 1) ^ d` valid at every input. -/
theorem of_forall_le (c d : ℕ) (h : ∀ n, f n ≤ c * (n + 1) ^ d) : PolynomiallyBounded f :=
  polynomiallyBounded_iff_le.2 ⟨c, d, h⟩

/-- A function eventually dominated by a polynomially bounded function is polynomially
bounded. -/
theorem mono (hg : PolynomiallyBounded g) (h : f ≤ᶠ[atTop] g) : PolynomiallyBounded f :=
  let ⟨d, hd⟩ := hg
  ⟨d, h.trans hd⟩

/-- A function dominated pointwise by a polynomially bounded function is polynomially bounded. -/
theorem mono_of_le (hg : PolynomiallyBounded g) (h : f ≤ g) : PolynomiallyBounded f :=
  hg.mono (Eventually.of_forall h)

/-- Constants are polynomially bounded. -/
@[fun_prop] protected theorem const (c : ℕ) : PolynomiallyBounded (fun _ => c) :=
  of_forall_le c 0 (by simp)

/-- The identity is polynomially bounded. -/
@[fun_prop] protected theorem id : PolynomiallyBounded (fun n => n) :=
  of_forall_le 1 1 (by simp)

/-- Sums of polynomially bounded functions are polynomially bounded. -/
@[fun_prop] protected theorem add (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n => f n + g n) := by
  obtain ⟨c, d, hf⟩ := polynomiallyBounded_iff_le.1 hf
  obtain ⟨c', d', hg⟩ := polynomiallyBounded_iff_le.1 hg
  refine of_forall_le (c + c') (d + d') fun n => ?_
  calc
    f n + g n ≤ c * (n + 1) ^ d + c' * (n + 1) ^ d' := Nat.add_le_add (hf n) (hg n)
    _ ≤ c * (n + 1) ^ (d + d') + c' * (n + 1) ^ (d + d') := by gcongr <;> omega
    _ = (c + c') * (n + 1) ^ (d + d') := by ring

/-- Products of polynomially bounded functions are polynomially bounded. -/
@[fun_prop] protected theorem mul (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n => f n * g n) := by
  obtain ⟨c, d, hf⟩ := polynomiallyBounded_iff_le.1 hf
  obtain ⟨c', d', hg⟩ := polynomiallyBounded_iff_le.1 hg
  refine of_forall_le (c * c') (d + d') fun n => ?_
  calc
    f n * g n ≤ (c * (n + 1) ^ d) * (c' * (n + 1) ^ d') := Nat.mul_le_mul (hf n) (hg n)
    _ = (c * c') * (n + 1) ^ (d + d') := by rw [pow_add]; ring

/-- Fixed powers of a polynomially bounded function are polynomially bounded. -/
@[fun_prop] protected theorem pow (hf : PolynomiallyBounded f) (d : ℕ) :
    PolynomiallyBounded (fun n => f n ^ d) := by
  obtain ⟨c, e, hf⟩ := polynomiallyBounded_iff_le.1 hf
  refine of_forall_le (c ^ d) (e * d) fun n => ?_
  calc
    f n ^ d ≤ (c * (n + 1) ^ e) ^ d := Nat.pow_le_pow_left (hf n) d
    _ = c ^ d * (n + 1) ^ (e * d) := by rw [mul_pow, pow_mul]

/-- Compositions of polynomially bounded functions are polynomially bounded. -/
@[fun_prop] protected theorem comp (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n => f (g n)) := by
  obtain ⟨c, d, hf⟩ := polynomiallyBounded_iff_le.1 hf
  obtain ⟨c', d', hg⟩ := polynomiallyBounded_iff_le.1 hg
  refine of_forall_le (c * (c' + 1) ^ d) (d' * d) fun n => ?_
  have hsize : g n + 1 ≤ (c' + 1) * (n + 1) ^ d' := by
    have hp : 1 ≤ (n + 1) ^ d' := Nat.one_le_pow _ _ (by omega)
    calc
      g n + 1 ≤ c' * (n + 1) ^ d' + (n + 1) ^ d' := Nat.add_le_add (hg n) hp
      _ = (c' + 1) * (n + 1) ^ d' := by ring
  calc
    f (g n) ≤ c * (g n + 1) ^ d := hf (g n)
    _ ≤ c * ((c' + 1) * (n + 1) ^ d') ^ d :=
      Nat.mul_le_mul_left c (Nat.pow_le_pow_left hsize d)
    _ = c * (c' + 1) ^ d * (n + 1) ^ (d' * d) := by rw [mul_pow, pow_mul, mul_assoc]

/-- Evaluating a polynomial with natural coefficients is polynomially bounded. This is how the
certificate lengths of `NP`, given by polynomials, enter bound computations. -/
@[fun_prop] protected theorem polynomial_eval (p : Polynomial ℕ) :
    PolynomiallyBounded (fun n => p.eval n) := by
  induction p using Polynomial.induction_on with
  | C a => simpa using PolynomiallyBounded.const a
  | add p q hp hq => simpa using hp.add hq
  | monomial n a h =>
    simpa [pow_succ, mul_assoc] using h.mul PolynomiallyBounded.id

/-- Truncated subtraction does not exceed its first argument. -/
@[fun_prop] protected theorem tsub (hf : PolynomiallyBounded f) (g : ℕ → ℕ) :
    PolynomiallyBounded (fun n => f n - g n) :=
  hf.mono_of_le fun _ => Nat.sub_le _ _

/-- The maximum of two polynomially bounded functions is polynomially bounded. -/
@[fun_prop] protected theorem max (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n => max (f n) (g n)) :=
  (hf.add hg).mono_of_le fun _ => max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)

/-- The minimum does not exceed its first argument. -/
@[fun_prop] protected theorem min (hf : PolynomiallyBounded f) (g : ℕ → ℕ) :
    PolynomiallyBounded (fun n => min (f n) (g n)) :=
  hf.mono_of_le fun _ => Nat.min_le_left _ _

/-- Division does not exceed the dividend. -/
@[fun_prop] protected theorem div (hf : PolynomiallyBounded f) (g : ℕ → ℕ) :
    PolynomiallyBounded (fun n => f n / g n) :=
  hf.mono_of_le fun _ => Nat.div_le_self _ _

/-- A remainder does not exceed the dividend. -/
@[fun_prop] protected theorem mod (hf : PolynomiallyBounded f) (g : ℕ → ℕ) :
    PolynomiallyBounded (fun n => f n % g n) :=
  hf.mono_of_le fun _ => Nat.mod_le _ _

/-- A logarithm does not exceed its argument. -/
@[fun_prop] protected theorem log (b : ℕ) (hf : PolynomiallyBounded f) :
    PolynomiallyBounded (fun n => Nat.log b (f n)) :=
  hf.mono_of_le fun n => Nat.log_le_self b (f n)

/-- A case distinction between polynomially bounded functions is polynomially bounded. -/
@[fun_prop] protected theorem ite (p : ℕ → Prop) [DecidablePred p]
    (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n => if p n then f n else g n) :=
  (hf.max hg).mono_of_le fun n => by split_ifs <;> simp

end PolynomiallyBounded

end Cslib
