/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.Simplex.Dantzig
public import Complexity.Algorithms.Lean.Simplex.LinearProgram
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Klee–Minty lower bound for Dantzig's rule

This module proves that the simplex method with Dantzig's largest-coefficient rule
(`Complexity.Algorithms.Lean.Simplex.Dantzig`) makes exactly `2 ^ n - 1` pivots on the
`n`-dimensional Klee–Minty program ([KleeMinty1972]; the form below is the one presented in
[Chvatal1983], Chapter 4), started from its slack dictionary, for every `n` and over every linearly
ordered field.

## The program

With `0`-based indices, the `n`-dimensional Klee–Minty program is

  maximize `∑_{j<n} 10 ^ (n - 1 - j) * x_j`
  subject to `2 * ∑_{j<i} 10 ^ (i - j) * x_j + x_i ≤ 100 ^ i` for `i < n`, and `x ≥ 0`

(`kleeMintyMatrix`, `kleeMintyRhs`, `kleeMintyObj`). [Chvatal1983] writes it with `1`-based
indices, `10 ^ (n - j)` and `100 ^ (i - 1)`. For `n ≥ 1` its optimum is `100 ^ (n - 1)`,
attained at `x = (0, …, 0, 100 ^ (n - 1))`.

## Proof

The variables are those of `slackDictionary`: `x_k` and its slack `w_k` form pair `k`. The run
visits the vertices `N = 0, 1, …, 2 ^ n - 1` in order, and the dictionary at vertex `N` is given in
closed form (`KleeMinty.dict`): `x_k` is basic iff bits `k` and `k + 1` of `N` differ (so the
basic original variables form the reflected binary Gray code of `N`), and the row constants,
coefficients and reduced costs are explicit functions of the bits of `N`. If `j` is the lowest zero
bit of `N < 2 ^ n - 1`, then

* the nonbasic variable of pair `j` has reduced cost `10 ^ (n - 1 - j)`, strictly larger than every
  other reduced cost, so Dantzig's rule enters it (`KleeMinty.dantzigEntering_dict`);
* the basic variable of pair `j` has a strictly smaller ratio than every other row that limits the
  entering variable, so the ratio test makes it leave (`KleeMinty.blandLeaving_dict`);
* the pivot yields exactly the dictionary at vertex `N + 1` (`KleeMinty.pivot_dict`).

At `N = 2 ^ n - 1` no reduced cost is positive (`KleeMinty.dantzigStep_dict_top`). The objective
strictly increases along the run and the `2 ^ n` bases are pairwise distinct, so the run visits
every vertex of the deformed cube. The entering and leaving variables are the unique maximizer and
minimizer at every step, so the tie-breaking conventions of `dantzigStep` play no role.

## Main definitions

* `Cslib.Algorithms.Lean.Simplex.kleeMintyMatrix`, `Cslib.Algorithms.Lean.Simplex.kleeMintyRhs`,
  `Cslib.Algorithms.Lean.Simplex.kleeMintyObj`: the Klee–Minty program.
* `Cslib.Algorithms.Lean.Simplex.KleeMinty.dict`: the dictionary at vertex `N`.

## Main results

* `dantzigRun_kleeMinty`: **Klee–Minty.** After `f < 2 ^ n - 1` pivots Dantzig's rule is at the
  dictionary of vertex `f`, and it stops at an optimal dictionary after exactly `2 ^ n - 1` pivots.
* `exists_dantzigRun_kleeMinty_eq_outOfFuel_iff`: a run with `f` pivots of fuel runs out of fuel
  iff `f < 2 ^ n - 1`.
* `isGreatest_kleeMinty`: the optimum of the `(n + 1)`-dimensional program is `100 ^ n`.
* `KleeMinty.objConst_dict_lt_of_lt`, `KleeMinty.eq_of_dict_basis_eq`: the visited vertices have
  strictly increasing objective values and pairwise distinct bases.

## Limitations

The lower bound counts pivots of this particular rule (Dantzig's entering rule with the
smallest-index ratio test); no machine-level running time is certified. Bland's rule also takes
more than polynomially many pivots on suitable programs, but that is not formalized here; the
worked examples only compare the two rules for `n = 3, 4`.

## References

* [V. Klee and G. J. Minty, *How good is the simplex algorithm?*][KleeMinty1972]
* [V. Chvátal, *Linear Programming*][Chvatal1983]
-/

public section

namespace Cslib.Algorithms.Lean.Simplex

open Finset Matrix

/-- The constraint matrix of the `n`-dimensional Klee–Minty program ([Chvatal1983], Chapter 4):
`2 * 10 ^ (i - j)` below the diagonal, `1` on it and `0` above it. -/
@[expose] def kleeMintyMatrix {K : Type*} [Field K] (n : ℕ) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j =>
    if (j : ℕ) < i then 2 * 10 ^ ((i : ℕ) - j) else if (j : ℕ) = i then 1 else 0

/-- The right-hand side `100 ^ i` of the `n`-dimensional Klee–Minty program. -/
@[expose] def kleeMintyRhs {K : Type*} [Field K] (n : ℕ) : Fin n → K := fun i => 100 ^ (i : ℕ)

/-- The objective `10 ^ (n - 1 - j)` of the `n`-dimensional Klee–Minty program. -/
@[expose] def kleeMintyObj {K : Type*} [Field K] (n : ℕ) : Fin n → K := fun j => 10 ^ (n - 1 - j)

namespace KleeMinty

variable {K : Type*} [Field K]

/-- `-1` if bit `k` of `N` is set, `1` otherwise. -/
def bitSign (N k : ℕ) : K := if N.testBit k then -1 else 1

/-- Pair `k` is flipped at vertex `N` when bits `k` and `k + 1` of `N` differ. -/
def flipped (N k : ℕ) : Bool := N.testBit k ^^ N.testBit (k + 1)

/-- The value at vertex `N` of `z_k = ∑_{j<k} 10^{k-1-j} x_j`. -/
def zVal (N : ℕ) : ℕ → K
  | 0 => 0
  | k + 1 => if flipped N k then 100 ^ k - 10 * zVal N k else 10 * zVal N k

/-- The constant of row `k` at vertex `N`. -/
def rowConst (N k : ℕ) : K := 100 ^ k - 20 * zVal N k

/-- The coefficient of the nonbasic variable of pair `p` in the row of pair `k`. -/
def rowCoeff (N k p : ℕ) : K :=
  if p < k then -2 * 10 ^ (k - p) * bitSign N p * bitSign N k else if p = k then -1 else 0

/-- The reduced cost of the nonbasic variable of pair `p`. -/
def cost (n N p : ℕ) : K := 10 ^ (n - 1 - p) * bitSign N p * bitSign N n

variable {n : ℕ}

/-- The pair of a variable: `x_k` and the slack `w_k` form pair `k`. -/
def pair : Fin (n + n) → Fin n := Fin.append id id

/-- Whether a variable is an original variable `x_k` rather than a slack `w_k`. -/
def isX : Fin (n + n) → Bool := Fin.append (fun _ => true) (fun _ => false)

/-- The variable of pair `k` that is an original variable iff `b`. -/
def var (k : Fin n) (b : Bool) : Fin (n + n) := if b then Fin.castAdd n k else Fin.natAdd n k

/-- `v` is basic at vertex `N`: `x_k` is basic iff pair `k` is flipped. -/
def Basic (N : ℕ) (v : Fin (n + n)) : Prop := isX v = flipped N (pair v)

instance (N : ℕ) : DecidablePred (Basic (n := n) N) :=
  fun v => inferInstanceAs (Decidable (isX v = flipped N (pair v)))

variable (n) in
/-- The dictionary at vertex `N` of the `n`-dimensional Klee–Minty program. The variables are
those of `slackDictionary`: `x_k = Fin.castAdd n k` and its slack `w_k = Fin.natAdd n k` form
pair `k`. Exactly one variable of each pair is basic, `x_k` iff bits `k` and `k + 1` of `N` differ
(`Basic`). Writing `t_p` for the nonbasic variable of pair `p`, the row of the basic variable of
pair `k` is `rowConst N k + ∑_{p<k} rowCoeff N k p * t_p - t_k`, and the objective is
`zVal N n + ∑_p cost n N p * t_p`. Entries outside these ranges are `0`, as in
`Dictionary.pivot`. -/
def dict (N : ℕ) : Dictionary (Fin (n + n)) K where
  basis := univ.filter (Basic N)
  rhs v := if Basic N v then rowConst N (pair v) else 0
  coeff v u := if Basic N v ∧ ¬Basic N u then rowCoeff N (pair v) (pair u) else 0
  objConst := zVal N n
  objCoeff u := if Basic N u then 0 else cost n N (pair u)

/-! ### Bits -/

private theorem testBit_succ_of_lowest {N j : ℕ} (hj : N.testBit j = false)
    (hlow : ∀ l < j, N.testBit l = true) (l : ℕ) :
    (N + 1).testBit l = if l < j then false else if l = j then true else N.testBit l := by
  induction j generalizing N l with
  | zero =>
    have h2 : N % 2 = 0 := by
      have := Nat.testBit_zero N
      rw [hj] at this
      have h := Nat.mod_two_eq_zero_or_one N
      rcases h with h | h
      · exact h
      · simp [h] at this
    rcases l with _ | l
    · simp only [Nat.testBit_zero, Nat.lt_irrefl, ↓reduceIte, decide_eq_true_eq]
      omega
    · simp only [Nat.not_lt_zero, ↓reduceIte, Nat.add_one_ne_zero, Nat.testBit_add_one]
      congr 1
      omega
  | succ j ih =>
    have h1 : N % 2 = 1 := by
      have := Nat.testBit_zero N
      rw [hlow 0 (Nat.zero_lt_succ j)] at this
      simpa using this.symm
    have hj' : (N / 2).testBit j = false := by rw [Nat.testBit_div_two]; exact hj
    have hlow' : ∀ l < j, (N / 2).testBit l = true := fun l hl => by
      rw [Nat.testBit_div_two]; exact hlow (l + 1) (by omega)
    rcases l with _ | l
    · simp only [Nat.testBit_zero, Nat.zero_lt_succ, ↓reduceIte, decide_eq_false_iff_not]
      omega
    · rw [Nat.testBit_add_one, show (N + 1) / 2 = N / 2 + 1 by omega, ih hj' hlow' l,
        Nat.testBit_add_one]
      simp only [Nat.add_lt_add_iff_right, Nat.add_right_cancel_iff]

/-- Adding one to `N` complements the bits up to its lowest zero bit `j`. -/
private theorem testBit_succ {N j : ℕ} (hj : N.testBit j = false)
    (hlow : ∀ l < j, N.testBit l = true) (l : ℕ) :
    (N + 1).testBit l = if l ≤ j then !N.testBit l else N.testBit l := by
  rw [testBit_succ_of_lowest hj hlow]
  rcases lt_trichotomy l j with h | h | h
  · simp [h, h.le, hlow l h]
  · subst h
    simp [hj]
  · simp [show ¬l < j by omega, show l ≠ j by omega, show ¬l ≤ j by omega]

/-- A number below `2 ^ n - 1` has a zero bit below `n`; the lowest one. -/
private theorem exists_lowest_zero {N : ℕ} (hN : N < 2 ^ n - 1) :
    ∃ j < n, N.testBit j = false ∧ ∀ l < j, N.testBit l = true := by
  have hex : ∃ j, j < n ∧ N.testBit j = false := by
    by_contra h
    push Not at h
    have hmod : N % 2 ^ n = 2 ^ n - 1 := Nat.eq_of_testBit_eq fun i => by
      rw [Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one]
      by_cases hi : i < n
      · simp only [hi, decide_true, Bool.true_and]
        simpa using h i hi
      · simp only [hi, decide_false, Bool.false_and]
    have := Nat.mod_le N (2 ^ n)
    omega
  classical
  let j := Nat.find hex
  have hjs : j < n ∧ N.testBit j = false := Nat.find_spec hex
  refine ⟨j, hjs.1, hjs.2, fun l hl => ?_⟩
  have := Nat.find_min hex hl
  simp only [not_and, Bool.not_eq_false] at this
  exact this (hl.trans hjs.1)

/-! ### Signs, values and coefficients -/

private theorem bitSign_succ (N k : ℕ) :
    (bitSign N (k + 1) : K) = if flipped N k then -bitSign N k else bitSign N k := by
  unfold bitSign flipped
  cases N.testBit k <;> cases N.testBit (k + 1) <;> simp

private theorem bitSign_of_testBit_false {N k : ℕ} (h : N.testBit k = false) :
    (bitSign N k : K) = 1 := by
  unfold bitSign; rw [h]; simp

private theorem bitSign_of_testBit_true {N k : ℕ} (h : N.testBit k = true) :
    (bitSign N k : K) = -1 := by
  unfold bitSign; rw [h]; simp

private theorem zVal_zero (N : ℕ) : (zVal N 0 : K) = 0 := by simp only [zVal]

private theorem zVal_succ (N k : ℕ) :
    (zVal N (k + 1) : K) = if flipped N k then 100 ^ k - 10 * zVal N k else 10 * zVal N k := by
  simp only [zVal]

private theorem rowCoeff_of_lt {N k p : ℕ} (h : p < k) :
    (rowCoeff N k p : K) = -2 * 10 ^ (k - p) * bitSign N p * bitSign N k := by
  rw [rowCoeff]; exact ite_eq_left h

private theorem rowCoeff_self (N k : ℕ) : (rowCoeff N k k : K) = -1 := by
  rw [rowCoeff, ite_eq_right (lt_irrefl k), ite_eq_left rfl]

private theorem rowCoeff_of_gt {N k p : ℕ} (h : k < p) : (rowCoeff N k p : K) = 0 := by
  rw [rowCoeff, ite_eq_right (show ¬p < k by omega), ite_eq_right (show ¬p = k by omega)]

/-! ### From vertex `N` to vertex `N + 1` -/

section Succ

variable {N j : ℕ}

private theorem bitSign_succ_of_le (hj : N.testBit j = false) (hlow : ∀ l < j, N.testBit l = true)
    {l : ℕ} (hl : l ≤ j) : (bitSign (N + 1) l : K) = -bitSign N l := by
  unfold bitSign
  rw [testBit_succ hj hlow, ite_eq_left hl]
  cases N.testBit l <;> simp

private theorem bitSign_succ_of_gt (hj : N.testBit j = false) (hlow : ∀ l < j, N.testBit l = true)
    {l : ℕ} (hl : j < l) : (bitSign (N + 1) l : K) = bitSign N l := by
  unfold bitSign
  rw [testBit_succ hj hlow, ite_eq_right (show ¬l ≤ j by omega)]

private theorem flipped_succ (hj : N.testBit j = false) (hlow : ∀ l < j, N.testBit l = true)
    (k : ℕ) :
    flipped (N + 1) k = if k = j then !flipped N k else flipped N k := by
  unfold flipped
  rw [testBit_succ hj hlow, testBit_succ hj hlow]
  rcases lt_trichotomy k j with h | h | h
  · rw [ite_eq_left h.le, ite_eq_left (show k + 1 ≤ j by omega), ite_eq_right h.ne]
    cases N.testBit k <;> cases N.testBit (k + 1) <;> rfl
  · subst h
    rw [ite_eq_left le_rfl, ite_eq_right (show ¬k + 1 ≤ k by omega), ite_eq_left rfl]
    cases N.testBit k <;> cases N.testBit (k + 1) <;> rfl
  · rw [ite_eq_right (show ¬k ≤ j by omega), ite_eq_right (show ¬k + 1 ≤ j by omega),
      ite_eq_right (show k ≠ j by omega)]

private theorem zVal_succ_of_le (hj : N.testBit j = false) (hlow : ∀ l < j, N.testBit l = true)
    {k : ℕ} (hk : k ≤ j) : (zVal (N + 1) k : K) = zVal N k := by
  induction k with
  | zero => rw [zVal_zero, zVal_zero]
  | succ k ih =>
    rw [zVal_succ (N + 1) k, zVal_succ N k, flipped_succ hj hlow,
      ite_eq_right (show k ≠ j by omega), ih (by omega)]

private theorem zVal_succ_of_gt (hj : N.testBit j = false) (hlow : ∀ l < j, N.testBit l = true)
    {m : ℕ} (hm : j ≤ m) :
    (zVal (N + 1) (m + 1) : K) =
      zVal N (m + 1) + 10 ^ (m - j) * bitSign N (m + 1) * rowConst N j := by
  induction m, hm using Nat.le_induction with
  | base =>
    rw [zVal_succ (N + 1) j, zVal_succ N j, flipped_succ hj hlow, ite_eq_left rfl,
      zVal_succ_of_le hj hlow le_rfl, bitSign_succ, bitSign_of_testBit_false hj, Nat.sub_self,
      pow_zero, rowConst]
    cases flipped N j
    · simp only [Bool.not_false, ↓reduceIte, Bool.false_eq_true]
      ring
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      ring
  | succ m hm ih =>
    rw [zVal_succ (N + 1) (m + 1), zVal_succ N (m + 1), flipped_succ hj hlow,
      ite_eq_right (show m + 1 ≠ j by omega), ih, bitSign_succ N (m + 1),
      show m + 1 - j = m - j + 1 by omega, pow_succ]
    cases flipped N (m + 1)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      ring
    · simp only [↓reduceIte]
      ring

private theorem rowConst_succ_self (hj : N.testBit j = false) (hlow : ∀ l < j, N.testBit l = true) :
    (rowConst (N + 1) j : K) = rowConst N j := by
  rw [rowConst, rowConst, zVal_succ_of_le hj hlow le_rfl]

private theorem rowConst_succ_of_ne (hj : N.testBit j = false) (hlow : ∀ l < j, N.testBit l = true)
    {P : ℕ} (hP : P ≠ j) :
    (rowConst (N + 1) P : K) = rowConst N P + rowCoeff N P j * rowConst N j := by
  rcases lt_or_gt_of_ne hP with h | h
  · rw [rowCoeff_of_gt h, zero_mul, add_zero, rowConst, rowConst, zVal_succ_of_le hj hlow h.le]
  · obtain ⟨m, rfl⟩ : ∃ m, P = m + 1 := ⟨P - 1, by omega⟩
    rw [rowConst, rowConst, zVal_succ_of_gt hj hlow (by omega : j ≤ m), rowCoeff_of_lt h,
      bitSign_of_testBit_false hj, show m + 1 - j = m - j + 1 by omega, pow_succ]
    ring

private theorem rowCoeff_succ_left (hj : N.testBit j = false) (hlow : ∀ l < j, N.testBit l = true)
    {p : ℕ} (hp : p ≠ j) : (rowCoeff (N + 1) j p : K) = rowCoeff N j p := by
  rcases lt_or_gt_of_ne hp with h | h
  · rw [rowCoeff_of_lt h, rowCoeff_of_lt h, bitSign_succ_of_le hj hlow h.le,
      bitSign_succ_of_le hj hlow le_rfl]
    ring
  · rw [rowCoeff_of_gt h, rowCoeff_of_gt h]

private theorem rowCoeff_succ_right (hj : N.testBit j = false) (hlow : ∀ l < j, N.testBit l = true)
    {P : ℕ} (hP : P ≠ j) : (rowCoeff (N + 1) P j : K) = -rowCoeff N P j := by
  rcases lt_or_gt_of_ne hP with h | h
  · rw [rowCoeff_of_gt h, rowCoeff_of_gt h, neg_zero]
  · rw [rowCoeff_of_lt h, rowCoeff_of_lt h, bitSign_succ_of_le hj hlow le_rfl,
      bitSign_succ_of_gt hj hlow h]
    ring

private theorem rowCoeff_succ (hj : N.testBit j = false) (hlow : ∀ l < j, N.testBit l = true)
    {P p : ℕ} (hP : P ≠ j) (hp : p ≠ j) :
    (rowCoeff (N + 1) P p : K) = rowCoeff N P p + rowCoeff N P j * rowCoeff N j p := by
  rcases lt_trichotomy p P with hpP | hpP | hpP
  · rcases lt_or_gt_of_ne hP with hPj | hPj
    · rw [rowCoeff_of_lt hpP, rowCoeff_of_lt hpP, rowCoeff_of_gt hPj, zero_mul, add_zero,
        bitSign_succ_of_le hj hlow (hpP.le.trans hPj.le), bitSign_succ_of_le hj hlow hPj.le]
      ring
    · rcases lt_or_gt_of_ne hp with hpj | hpj
      · rw [rowCoeff_of_lt hpP, rowCoeff_of_lt hpP, rowCoeff_of_lt hPj, rowCoeff_of_lt hpj,
          bitSign_succ_of_le hj hlow hpj.le, bitSign_succ_of_gt hj hlow hPj,
          bitSign_of_testBit_false hj]
        have : (10 : K) ^ (P - p) = 10 ^ (P - j) * 10 ^ (j - p) := by
          rw [← pow_add]; congr 1; omega
        rw [this]
        ring
      · rw [rowCoeff_of_lt hpP, rowCoeff_of_lt hpP, rowCoeff_of_gt hpj, mul_zero, add_zero,
          bitSign_succ_of_gt hj hlow hpj, bitSign_succ_of_gt hj hlow hPj]
  · subst hpP
    rw [rowCoeff_self, rowCoeff_self]
    rcases lt_or_gt_of_ne hP with h | h
    · rw [rowCoeff_of_gt h, zero_mul, add_zero]
    · rw [rowCoeff_of_gt h, mul_zero, add_zero]
  · rw [rowCoeff_of_gt hpP, rowCoeff_of_gt hpP]
    rcases lt_or_gt_of_ne hP with h | h
    · rw [rowCoeff_of_gt h, zero_mul, add_zero]
    · rw [rowCoeff_of_gt (h.trans hpP), mul_zero, add_zero]

private theorem cost_succ_self (hj : N.testBit j = false) (hlow : ∀ l < j, N.testBit l = true)
    (hjn : j < n) : (cost n (N + 1) j : K) = -cost n N j := by
  rw [cost, cost, bitSign_succ_of_le hj hlow le_rfl, bitSign_succ_of_gt hj hlow hjn]
  ring

private theorem cost_succ_of_ne (hj : N.testBit j = false) (hlow : ∀ l < j, N.testBit l = true)
    (hjn : j < n) {p : ℕ} (hp : p ≠ j) :
    (cost n (N + 1) p : K) = cost n N p + cost n N j * rowCoeff N j p := by
  rcases lt_or_gt_of_ne hp with h | h
  · rw [cost, cost, cost, rowCoeff_of_lt h, bitSign_succ_of_le hj hlow h.le,
      bitSign_succ_of_gt hj hlow hjn, bitSign_of_testBit_false hj]
    have : (10 : K) ^ (n - 1 - p) = 10 ^ (n - 1 - j) * 10 ^ (j - p) := by
      rw [← pow_add]; congr 1; omega
    rw [this]
    ring
  · rw [rowCoeff_of_gt h, mul_zero, add_zero, cost, cost, bitSign_succ_of_gt hj hlow h,
      bitSign_succ_of_gt hj hlow hjn]

private theorem zVal_succ_top (hj : N.testBit j = false) (hlow : ∀ l < j, N.testBit l = true)
    (hjn : j < n) : (zVal (N + 1) n : K) = zVal N n + cost n N j * rowConst N j := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [zVal_succ_of_gt hj hlow (by omega : j ≤ m), cost, bitSign_of_testBit_false hj,
    show m + 1 - 1 - j = m - j by omega]
  ring

end Succ

/-! ### Variables -/

@[simp] private theorem pair_castAdd (k : Fin n) : pair (Fin.castAdd n k) = k := by
  simp only [pair, Fin.append_left, id]

private theorem pair_natAdd (k : Fin n) : pair (Fin.natAdd n k) = k := by
  simp only [pair, Fin.append_right, id]

@[simp] private theorem isX_castAdd (k : Fin n) : isX (Fin.castAdd n k) = true := by
  simp only [isX, Fin.append_left]

private theorem isX_natAdd (k : Fin n) : isX (Fin.natAdd n k) = false := by
  simp only [isX, Fin.append_right]

@[simp] private theorem pair_var (k : Fin n) (b : Bool) : pair (var k b) = k := by
  cases b
  · rw [var, ite_eq_right Bool.false_ne_true, pair_natAdd]
  · rw [var, ite_eq_left rfl, pair_castAdd]

@[simp] private theorem isX_var (k : Fin n) (b : Bool) : isX (var k b) = b := by
  cases b
  · rw [var, ite_eq_right Bool.false_ne_true, isX_natAdd]
  · rw [var, ite_eq_left rfl, isX_castAdd]

private theorem eq_var_iff {v : Fin (n + n)} {k : Fin n} {b : Bool} :
    v = var k b ↔ pair v = k ∧ isX v = b := by
  constructor
  · rintro rfl
    exact ⟨pair_var k b, isX_var k b⟩
  · rintro ⟨rfl, rfl⟩
    induction v using Fin.addCases with
    | left i => rw [pair_castAdd, isX_castAdd, var, ite_eq_left rfl]
    | right i => rw [pair_natAdd, isX_natAdd, var, ite_eq_right Bool.false_ne_true]

theorem basic_var_self (N : ℕ) (j : Fin n) : Basic N (var j (flipped N j)) := by
  simp [Basic]

theorem not_basic_var_not (N : ℕ) (j : Fin n) : ¬Basic N (var j (!flipped N j)) := by
  simp [Basic]

private theorem eq_var_self_iff {N : ℕ} {j : Fin n} {v : Fin (n + n)} :
    v = var j (flipped N j) ↔ pair v = j ∧ Basic N v := by
  rw [eq_var_iff, Basic]
  constructor
  · rintro ⟨rfl, h⟩; exact ⟨rfl, h⟩
  · rintro ⟨rfl, h⟩; exact ⟨rfl, h⟩

private theorem eq_var_not_iff {N : ℕ} {j : Fin n} {v : Fin (n + n)} :
    v = var j (!flipped N j) ↔ pair v = j ∧ ¬Basic N v := by
  rw [eq_var_iff, Basic]
  constructor
  · rintro ⟨rfl, h⟩
    rw [h]
    exact ⟨rfl, by simp⟩
  · rintro ⟨rfl, h⟩
    refine ⟨rfl, ?_⟩
    revert h
    cases isX v <;> cases flipped N (pair v) <;> simp

private theorem basic_succ_iff {N : ℕ} {j : Fin n} (hj : N.testBit j = false)
    (hlow : ∀ l < (j : ℕ), N.testBit l = true) (v : Fin (n + n)) :
    Basic (N + 1) v ↔ (Basic N v ↔ pair v ≠ j) := by
  unfold Basic
  rw [flipped_succ hj hlow]
  by_cases h : pair v = j
  · rw [ite_eq_left (congrArg Fin.val h)]
    simp only [h, ne_eq, not_true_eq_false, iff_false]
    cases isX v <;> cases flipped N j <;> simp
  · rw [ite_eq_right (fun e => h (Fin.ext e))]
    simp [h]

/-! ### The dictionaries -/

theorem mem_dict_basis {N : ℕ} {v : Fin (n + n)} :
    v ∈ (dict n N : Dictionary (Fin (n + n)) K).basis ↔ Basic N v := by
  simp [dict]

theorem dict_rhs {N : ℕ} {v : Fin (n + n)} (h : Basic N v) :
    (dict n N : Dictionary (Fin (n + n)) K).rhs v = rowConst N (pair v) := by
  simp [dict, h]

theorem dict_coeff {N : ℕ} {v u : Fin (n + n)} (hv : Basic N v) (hu : ¬Basic N u) :
    (dict n N : Dictionary (Fin (n + n)) K).coeff v u = rowCoeff N (pair v) (pair u) := by
  simp [dict, hv, hu]

theorem dict_objCoeff {N : ℕ} {u : Fin (n + n)} (hu : ¬Basic N u) :
    (dict n N : Dictionary (Fin (n + n)) K).objCoeff u = cost n N (pair u) := by
  simp [dict, hu]

/-- **The pivot step**: at the lowest zero bit `j` of `N`, pivoting `dict n N` on the leaving
basic variable of pair `j` and the entering nonbasic variable of pair `j` yields `dict n (N + 1)`.
-/
theorem pivot_dict {N : ℕ} {j : Fin n} (hj : N.testBit j = false)
    (hlow : ∀ l < (j : ℕ), N.testBit l = true) :
    (dict n N : Dictionary (Fin (n + n)) K).pivot (var j (flipped N j)) (var j (!flipped N j)) =
      dict n (N + 1) := by
  have hrb := basic_var_self (n := n) N j
  have hsb := not_basic_var_not (n := n) N j
  have hcrs : (dict n N : Dictionary (Fin (n + n)) K).coeff (var j (flipped N j))
      (var j (!flipped N j)) = -1 := by
    rw [dict_coeff hrb hsb, pair_var, pair_var, rowCoeff_self]
  have hrr : (dict n N : Dictionary (Fin (n + n)) K).rhs (var j (flipped N j)) = rowConst N j := by
    rw [dict_rhs hrb, pair_var]
  have hcs : (dict n N : Dictionary (Fin (n + n)) K).objCoeff (var j (!flipped N j)) =
      cost n N j := by
    rw [dict_objCoeff hsb, pair_var]
  generalize hr : var j (flipped N j) = r at hrb hcrs hrr
  generalize hs : var j (!flipped N j) = s at hsb hcrs hcs
  have hpr : pair r = j := hr ▸ pair_var _ _
  have hps : pair s = j := hs ▸ pair_var _ _
  have hrs : r ≠ s := fun h => hsb (h ▸ hrb)
  have hr1 : ¬Basic (N + 1) r := by rw [basic_succ_iff hj hlow, hpr]; simp [hrb]
  have hs1 : Basic (N + 1) s := by rw [basic_succ_iff hj hlow, hps]; simp [hsb]
  have hcases : ∀ v, v = r ∨ v = s ∨ (pair v ≠ j ∧ v ≠ r ∧ v ≠ s) := by
    intro v
    by_cases h : pair v = j
    · by_cases hb : Basic N v
      · exact .inl (hr ▸ eq_var_self_iff.2 ⟨h, hb⟩)
      · exact .inr (.inl (hs ▸ eq_var_not_iff.2 ⟨h, hb⟩))
    · refine .inr (.inr ⟨h, ?_, ?_⟩) <;> rintro rfl
      · exact h hpr
      · exact h hps
  have hne : ∀ v : Fin (n + n), pair v ≠ j → (pair v : ℕ) ≠ j := fun v h e => h (Fin.ext e)
  have hb1 : ∀ v : Fin (n + n), pair v ≠ j → (Basic (N + 1) v ↔ Basic N v) := by
    intro v h
    rw [basic_succ_iff hj hlow]
    simp [h]
  apply Dictionary.ext
  · ext v
    simp only [Dictionary.mem_pivot_basis, mem_dict_basis]
    rcases hcases v with rfl | rfl | ⟨h, hvr, hvs⟩
    · simp [hr1, hrs]
    · simp [hs1]
    · simp [hvr, hvs, hb1 v h]
  · funext v
    simp only [Dictionary.pivot]
    rw [hcrs, hrr]
    rcases hcases v with rfl | rfl | ⟨h, hvr, hvs⟩
    · simp [dict, hr1, hrs]
    · simp [dict, hs1, hps, rowConst_succ_self hj hlow]
    · by_cases hb : Basic N v
      · rw [dict_coeff hb hsb, hps]
        simp [dict, hvr, hvs, hb, hb1 v h, rowConst_succ_of_ne hj hlow (hne v h), div_neg,
          sub_neg_eq_add]
      · simp [dict, hvs, hb, hb1 v h]
  · funext v u
    simp only [Dictionary.pivot]
    rw [hcrs]
    rcases hcases u with rfl | rfl | ⟨hu, hur, hus⟩
    · rcases hcases v with rfl | rfl | ⟨h, hvr, hvs⟩
      · simp [dict, hr1, hrs]
      · simp [dict, hs1, hr1, hrs, hps, hpr, rowCoeff_self]
      · by_cases hb : Basic N v
        · simp [dict, hvr, hvs, hb, hb1 v h, hsb, hr1, hrs, hps, hpr,
            rowCoeff_succ_right hj hlow (hne v h), div_neg]
        · simp [dict, hvr, hvs, hb, hb1 v h, hrs]
    · simp [dict, hs1]
    · by_cases hbu : Basic N u
      · simp [dict, hus, hur, hbu, hb1 u hu]
      · rcases hcases v with rfl | rfl | ⟨h, hvr, hvs⟩
        · simp [dict, hr1, hrs, hus, hur, hbu, hb1 u hu]
        · simp [dict, hs1, hus, hur, hbu, hb1 u hu, hrb, hps, hpr,
            rowCoeff_succ_left hj hlow (hne u hu), div_neg]
        · by_cases hb : Basic N v
          · simp [dict, hvr, hvs, hb, hb1 v h, hus, hur, hbu, hb1 u hu, hsb, hrb, hps, hpr,
              rowCoeff_succ hj hlow (hne v h) (hne u hu), div_neg, sub_neg_eq_add]
          · simp [dict, hvr, hvs, hb, hb1 v h, hus, hur, hbu, hb1 u hu]
  · simp only [Dictionary.pivot]
    rw [hcs, hrr, hcrs]
    simp [dict, zVal_succ_top hj hlow j.isLt, div_neg, sub_neg_eq_add]
  · funext u
    simp only [Dictionary.pivot]
    rw [hcs]
    rcases hcases u with rfl | rfl | ⟨hu, hur, hus⟩
    · rw [hcrs]
      simp [dict, hr1, hrs, hpr, cost_succ_self hj hlow j.isLt, div_neg]
    · simp [dict, hs1]
    · by_cases hbu : Basic N u
      · simp [dict, hus, hur, hbu, hb1 u hu]
      · rw [hcrs]
        simp [dict, hus, hur, hbu, hb1 u hu, hrb, hpr, cost_succ_of_ne hj hlow j.isLt (hne u hu),
          div_neg, sub_neg_eq_add]

/-! ### Dantzig's rule on the dictionaries -/

section Ordered

variable [LinearOrder K] [IsStrictOrderedRing K]

private theorem bitSign_le_one (N k : ℕ) : (bitSign N k : K) ≤ 1 := by
  unfold bitSign; split_ifs <;> norm_num

private theorem zVal_nonneg_and (N k : ℕ) :
    0 ≤ (zVal N k : K) ∧ 100 * (zVal N k : K) ≤ 100 ^ k := by
  induction k with
  | zero => simp [zVal]
  | succ k ih =>
    obtain ⟨h0, h1⟩ := ih
    have hp : (0 : K) ≤ 100 ^ k := by positivity
    rw [zVal_succ]
    split_ifs
    · constructor
      · nlinarith
      · rw [pow_succ]; nlinarith
    · constructor
      · nlinarith
      · rw [pow_succ]; nlinarith

private theorem rowConst_bounds (N k : ℕ) :
    4 * (100 : K) ^ k ≤ 5 * rowConst N k ∧ (rowConst N k : K) ≤ 100 ^ k := by
  obtain ⟨h0, h1⟩ := zVal_nonneg_and (K := K) N k
  unfold rowConst
  constructor <;> nlinarith

private theorem rowConst_pos (N k : ℕ) : 0 < (rowConst N k : K) := by
  have := (rowConst_bounds (K := K) N k).1
  have : (0 : K) < 100 ^ k := by positivity
  linarith

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem bitSign_top {N : ℕ} (hN : N < 2 ^ n) : (bitSign N n : K) = 1 :=
  bitSign_of_testBit_false (Nat.testBit_lt_two_pow hN)

/-- At vertex `N < 2 ^ n - 1` with lowest zero bit `j`, Dantzig's rule enters the nonbasic
variable of pair `j`: its reduced cost `10 ^ (n - 1 - j)` is the unique largest one. -/
theorem dantzigEntering_dict {N : ℕ} (hN : N < 2 ^ n) {j : Fin n} (hj : N.testBit j = false)
    (hlow : ∀ l < (j : ℕ), N.testBit l = true) :
    (dict n N : Dictionary (Fin (n + n)) K).dantzigEntering = some (var j (!flipped N j)) := by
  have hsb := not_basic_var_not (n := n) N j
  have hcs : (dict n N : Dictionary (Fin (n + n)) K).objCoeff (var j (!flipped N j)) =
      10 ^ (n - 1 - j) := by
    rw [dict_objCoeff hsb, pair_var, cost, bitSign_of_testBit_false hj, bitSign_top hN, mul_one,
      mul_one]
  have hlt : ∀ u, ¬Basic N u → u ≠ var j (!flipped N j) →
      (dict n N : Dictionary (Fin (n + n)) K).objCoeff u <
        (dict n N : Dictionary (Fin (n + n)) K).objCoeff (var j (!flipped N j)) := by
    intro u hu hus
    rw [hcs, dict_objCoeff hu, cost, bitSign_top hN, mul_one]
    have hpj : pair u ≠ j := fun h => hus (eq_var_not_iff.2 ⟨h, hu⟩)
    have hp := (pair u).isLt
    rcases lt_or_gt_of_ne (fun e => hpj (Fin.ext e)) with h | h
    · rw [bitSign_of_testBit_true (hlow _ h)]
      have : (0 : K) < 10 ^ (n - 1 - (pair u : ℕ)) := by positivity
      have : (0 : K) < 10 ^ (n - 1 - (j : ℕ)) := by positivity
      linarith
    · have hle : (10 : K) ^ (n - 1 - (pair u : ℕ)) < 10 ^ (n - 1 - (j : ℕ)) :=
        pow_lt_pow_right₀ (by norm_num) (by omega)
      have h0 : (0 : K) ≤ 10 ^ (n - 1 - (pair u : ℕ)) := by positivity
      calc (10 : K) ^ (n - 1 - (pair u : ℕ)) * bitSign N (pair u)
          ≤ 10 ^ (n - 1 - (pair u : ℕ)) * 1 := mul_le_mul_of_nonneg_left (bitSign_le_one _ _) h0
        _ < 10 ^ (n - 1 - (j : ℕ)) := by rw [mul_one]; exact hle
  rw [Dictionary.dantzigEntering_eq_some_iff, mem_dict_basis]
  refine ⟨hsb, by rw [hcs]; positivity, fun u hu => ?_, fun u hu heq => ?_⟩
  · rw [mem_dict_basis] at hu
    by_cases hus : u = var j (!flipped N j)
    · rw [hus]
    · exact (hlt u hu hus).le
  · rw [mem_dict_basis] at hu
    by_cases hus : u = var j (!flipped N j)
    · exact hus.symm.le
    · exact absurd heq (hlt u hu hus).ne

/-- At vertex `N` with lowest zero bit `j`, the ratio test leaves the basic variable of pair
`j`: its ratio is strictly smallest. -/
theorem blandLeaving_dict {N : ℕ} {j : Fin n} (hj : N.testBit j = false) :
    (dict n N : Dictionary (Fin (n + n)) K).blandLeaving (var j (!flipped N j)) =
      some (var j (flipped N j)) := by
  have hrb := basic_var_self (n := n) N j
  have hsb := not_basic_var_not (n := n) N j
  have hcrs : (dict n N : Dictionary (Fin (n + n)) K).coeff (var j (flipped N j))
      (var j (!flipped N j)) = -1 := by
    rw [dict_coeff hrb hsb, pair_var, pair_var, rowCoeff_self]
  have hratio : (dict n N : Dictionary (Fin (n + n)) K).ratio (var j (!flipped N j))
      (var j (flipped N j)) = rowConst N j := by
    rw [Dictionary.ratio, hcrs, dict_rhs hrb, pair_var, neg_neg, div_one]
  have hlt : ∀ i, Basic N i → i ≠ var j (flipped N j) →
      (dict n N : Dictionary (Fin (n + n)) K).coeff i (var j (!flipped N j)) < 0 →
      (dict n N : Dictionary (Fin (n + n)) K).ratio (var j (!flipped N j))
          (var j (flipped N j)) <
        (dict n N : Dictionary (Fin (n + n)) K).ratio (var j (!flipped N j)) i := by
    intro i hi hir hneg
    rw [dict_coeff hi hsb, pair_var] at hneg
    rw [hratio, Dictionary.ratio, dict_coeff hi hsb, dict_rhs hi, pair_var]
    have hPj : pair i ≠ j := fun h => hir (eq_var_self_iff.2 ⟨h, hi⟩)
    have hjP : (j : ℕ) < pair i := by
      rcases lt_or_gt_of_ne (fun e => hPj (Fin.ext e)) with h | h
      · rw [rowCoeff_of_gt h] at hneg; exact absurd hneg (lt_irrefl 0)
      · exact h
    rw [rowCoeff_of_lt hjP] at hneg ⊢
    rw [lt_div_iff₀ (by linarith)]
    obtain ⟨d, hd⟩ : ∃ d, (pair i : ℕ) = j + (d + 1) := ⟨pair i - j - 1, by omega⟩
    rw [hd, show (j : ℕ) + (d + 1) - j = d + 1 by omega] at hneg ⊢
    rw [bitSign_of_testBit_false hj, mul_one] at hneg ⊢
    set X : K := 10 ^ (d + 1) with hX
    have hX10 : (10 : K) ≤ X := by
      rw [hX, pow_succ]
      have : (1 : K) ≤ 10 ^ d := one_le_pow₀ (by norm_num)
      nlinarith
    have h100 : (100 : K) ^ ((j : ℕ) + (d + 1)) = 100 ^ (j : ℕ) * X * X := by
      rw [hX, pow_add, show (100 : K) = 10 * 10 by norm_num, mul_pow, mul_pow]
      ring
    obtain ⟨hPlo, -⟩ := rowConst_bounds (K := K) N ((j : ℕ) + (d + 1))
    obtain ⟨-, hjhi⟩ := rowConst_bounds (K := K) N j
    rw [h100] at hPlo
    have hc : -(-2 * X * bitSign N ((j : ℕ) + (d + 1))) ≤ 2 * X := by
      have := bitSign_le_one (K := K) N ((j : ℕ) + (d + 1))
      nlinarith
    have hpos : (0 : K) < 100 ^ (j : ℕ) := by positivity
    have hrj := rowConst_pos (K := K) N j
    have h1 : rowConst N j * -(-2 * X * bitSign N ((j : ℕ) + (d + 1))) ≤
        rowConst N j * (2 * X) := mul_le_mul_of_nonneg_left hc hrj.le
    have h2 : rowConst N j * (2 * X) ≤ 100 ^ (j : ℕ) * (2 * X) :=
      mul_le_mul_of_nonneg_right hjhi (by linarith)
    have h3 : 0 < 100 ^ (j : ℕ) * X * (4 * X - 10) := by
      apply mul_pos (mul_pos hpos (by linarith)); linarith
    nlinarith
  rw [Dictionary.blandLeaving_eq_some_iff, mem_dict_basis]
  refine ⟨hrb, by rw [hcrs]; norm_num, fun i hi hneg => ?_, fun i hi hneg heq => ?_⟩
  · rw [mem_dict_basis] at hi
    by_cases hir : i = var j (flipped N j)
    · rw [hir]
    · exact (hlt i hi hir hneg).le
  · rw [mem_dict_basis] at hi
    by_cases hir : i = var j (flipped N j)
    · exact hir.symm.le
    · exact absurd heq (hlt i hi hir hneg).ne'

/-- Below the last vertex, one step of Dantzig's rule moves from vertex `N` to vertex `N + 1`. -/
theorem dantzigStep_dict {N : ℕ} (hN : N < 2 ^ n - 1) :
    ∃ r s, (dict n N : Dictionary (Fin (n + n)) K).dantzigStep = .pivot r s ∧
      (dict n N : Dictionary (Fin (n + n)) K).pivot r s = dict n (N + 1) := by
  obtain ⟨j, hjn, hj, hlow⟩ := exists_lowest_zero hN
  refine ⟨var ⟨j, hjn⟩ (flipped N j), var ⟨j, hjn⟩ (!flipped N j), ?_,
    pivot_dict (j := ⟨j, hjn⟩) hj hlow⟩
  rw [Dictionary.dantzigStep_eq_pivot_iff]
  exact ⟨dantzigEntering_dict (by omega) (j := ⟨j, hjn⟩) hj hlow,
    blandLeaving_dict (j := ⟨j, hjn⟩) hj⟩

/-- At the last vertex `2 ^ n - 1` no reduced cost is positive, so Dantzig's rule stops. -/
theorem dantzigStep_dict_top :
    (dict n (2 ^ n - 1) : Dictionary (Fin (n + n)) K).dantzigStep = .optimal := by
  rw [Dictionary.dantzigStep_eq_optimal_iff, Dictionary.dantzigEntering_eq_none_iff]
  intro u hu
  rw [mem_dict_basis] at hu
  rw [dict_objCoeff hu, cost, bitSign_of_testBit_true (by simp), bitSign_of_testBit_false (by simp)]
  have : (0 : K) ≤ 10 ^ (n - 1 - (pair u : ℕ)) := by positivity
  linarith

/-- **The run of Dantzig's rule from vertex `N`**: after `f` pivots it is at vertex `N + f`, and
it stops at the last vertex `2 ^ n - 1`. -/
theorem dantzigRun_dict {N : ℕ} (hN : N ≤ 2 ^ n - 1) (f : ℕ) :
    (dict n N : Dictionary (Fin (n + n)) K).dantzigRun f =
      if N + f < 2 ^ n - 1 then .outOfFuel (dict n (N + f)) else .optimal (dict n (2 ^ n - 1)) := by
  induction f generalizing N with
  | zero =>
    rcases hN.lt_or_eq with h | rfl
    · obtain ⟨r, s, hstep, -⟩ := dantzigStep_dict (K := K) h
      simp only [Dictionary.dantzigRun, hstep, add_zero, h, ↓reduceIte]
    · simp only [Dictionary.dantzigRun, dantzigStep_dict_top, add_zero, lt_irrefl, ↓reduceIte]
  | succ f ih =>
    rcases hN.lt_or_eq with h | rfl
    · obtain ⟨r, s, hstep, hpiv⟩ := dantzigStep_dict (K := K) h
      simp only [Dictionary.dantzigRun, hstep, hpiv]
      rw [ih (by omega), show N + 1 + f = N + (f + 1) by omega]
    · simp only [Dictionary.dantzigRun, dantzigStep_dict_top]
      rw [ite_eq_right (by omega)]

theorem objConst_dict_lt {N : ℕ} (hN : N < 2 ^ n - 1) :
    (dict n N : Dictionary (Fin (n + n)) K).objConst < (dict n (N + 1)).objConst := by
  obtain ⟨j, hjn, hj, hlow⟩ := exists_lowest_zero hN
  simp only [dict]
  rw [zVal_succ_top hj hlow hjn, cost, bitSign_of_testBit_false hj, bitSign_top (by omega),
    mul_one, mul_one]
  have := rowConst_pos (K := K) N j
  have : (0 : K) < 10 ^ (n - 1 - j) := by positivity
  nlinarith

/-- Every dictionary `dict n N` is feasible. -/
theorem feasible_dict (N : ℕ) : (dict n N : Dictionary (Fin (n + n)) K).Feasible := by
  intro v hv
  rw [mem_dict_basis] at hv
  rw [dict_rhs hv]
  exact (rowConst_pos N _).le

/-- The objective strictly increases along the run: the vertices `0, …, 2 ^ n - 1` have
distinct objective values. -/
theorem objConst_dict_lt_of_lt {N M : ℕ} (hNM : N < M) (hM : M ≤ 2 ^ n - 1) :
    (dict n N : Dictionary (Fin (n + n)) K).objConst < (dict n M).objConst := by
  induction M, hNM using Nat.le_induction with
  | base => exact objConst_dict_lt (by omega)
  | succ M hNM ih => exact (ih (by omega)).trans (objConst_dict_lt (by omega))

end Ordered

/-- The bases of the dictionaries `dict n N`, `N < 2 ^ n`, are pairwise distinct. -/
theorem eq_of_dict_basis_eq {N M : ℕ} (hN : N < 2 ^ n) (hM : M < 2 ^ n)
    (h : (dict n N : Dictionary (Fin (n + n)) K).basis =
      (dict n M : Dictionary (Fin (n + n)) K).basis) : N = M := by
  have hfl : ∀ k < n, flipped N k = flipped M k := by
    intro k hk
    have := congrArg (var (⟨k, hk⟩ : Fin n) true ∈ ·) h
    simp only [mem_dict_basis, Basic, isX_var, pair_var, eq_iff_iff] at this
    cases hN' : flipped N k <;> cases hM' : flipped M k <;> simp_all
  have hbit : ∀ d ≤ n, N.testBit (n - d) = M.testBit (n - d) := by
    intro d hd
    induction d with
    | zero => rw [Nat.sub_zero, Nat.testBit_lt_two_pow hN, Nat.testBit_lt_two_pow hM]
    | succ d ih =>
      have h1 := hfl (n - (d + 1)) (by omega)
      have h2 := ih (by omega)
      rw [show n - d = n - (d + 1) + 1 by omega] at h2
      unfold flipped at h1
      rw [h2] at h1
      revert h1
      cases N.testBit (n - (d + 1)) <;> cases M.testBit (n - (d + 1)) <;> simp
  refine Nat.eq_of_testBit_eq fun k => ?_
  rcases lt_or_ge k n with hk | hk
  · have := hbit (n - k) (by omega)
    rwa [show n - (n - k) = k by omega] at this
  · rw [Nat.testBit_lt_two_pow (hN.trans_le (Nat.pow_le_pow_right two_pos hk)),
      Nat.testBit_lt_two_pow (hM.trans_le (Nat.pow_le_pow_right two_pos hk))]

/-! ### The Klee–Minty program -/

private theorem zVal_zero_left (k : ℕ) : (zVal 0 k : K) = 0 := by
  induction k with
  | zero => exact zVal_zero 0
  | succ k ih => simp [zVal_succ, flipped, ih]

theorem slackDictionary_kleeMinty :
    slackDictionary (kleeMintyMatrix n) (kleeMintyRhs n) (kleeMintyObj n) =
      (dict n 0 : Dictionary (Fin (n + n)) K) := by
  have hb : ∀ v : Fin (n + n), Basic 0 v ↔ isX v = false := fun v => by
    simp [Basic, flipped]
  have hs : ∀ k, (bitSign 0 k : K) = 1 := fun k => bitSign_of_testBit_false (Nat.zero_testBit k)
  apply Dictionary.ext
  · ext v
    rw [mem_dict_basis, hb, mem_slackDictionary_basis]
    induction v using Fin.addCases with
    | left i => simp [i.isLt]
    | right i => simp [-Fin.natAdd_eq_addNat, isX_natAdd]
  · funext v
    induction v using Fin.addCases with
    | left i => simp [slackDictionary, dict, hb]
    | right i =>
      simp [-Fin.natAdd_eq_addNat, pair_natAdd, isX_natAdd, slackDictionary, dict, hb, kleeMintyRhs,
        rowConst, zVal_zero_left]
  · funext v u
    induction v using Fin.addCases with
    | left i => simp [slackDictionary, dict, hb]
    | right i =>
      induction u using Fin.addCases with
      | left k =>
        simp only [slackDictionary, dict, hb, Fin.append_right, Fin.append_left, isX_natAdd,
          isX_castAdd, pair_natAdd, pair_castAdd, kleeMintyMatrix, Matrix.of_apply, rowCoeff, hs]
        split_ifs <;> simp_all
      | right k => simp [-Fin.natAdd_eq_addNat, isX_natAdd, slackDictionary, dict, hb]
  · simp [slackDictionary, dict, zVal_zero_left]
  · funext u
    induction u using Fin.addCases with
    | left k => simp [slackDictionary, dict, hb, kleeMintyObj, cost, hs]
    | right k => simp [-Fin.natAdd_eq_addNat, isX_natAdd, slackDictionary, dict, hb]

private theorem zVal_top_succ : (zVal (2 ^ (n + 1) - 1) (n + 1) : K) = 100 ^ n := by
  have h0 : ∀ k ≤ n, (zVal (2 ^ (n + 1) - 1) k : K) = 0 := by
    intro k hk
    induction k with
    | zero => exact zVal_zero _
    | succ k ih =>
      rw [zVal_succ, ih (by omega)]
      simp [flipped, Nat.testBit_two_pow_sub_one, show k < n + 1 by omega,
        show k + 1 < n + 1 by omega]
  rw [zVal_succ, h0 n le_rfl]
  simp [flipped, Nat.testBit_two_pow_sub_one]

/-- The objective value at the last vertex of the `(n + 1)`-dimensional program is `100 ^ n`. -/
theorem objConst_dict_top :
    (dict (n + 1) (2 ^ (n + 1) - 1) : Dictionary (Fin (n + 1 + (n + 1))) K).objConst = 100 ^ n :=
  zVal_top_succ

end KleeMinty

open KleeMinty

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **Klee–Minty**: on the `n`-dimensional Klee–Minty program, started from its slack dictionary,
the simplex method with Dantzig's rule runs out of fuel after `f < 2 ^ n - 1` pivots and stops at
an optimal dictionary after exactly `2 ^ n - 1` pivots. -/
theorem dantzigRun_kleeMinty (n f : ℕ) :
    (slackDictionary (kleeMintyMatrix n) (kleeMintyRhs n) (kleeMintyObj n) :
        Dictionary (Fin (n + n)) K).dantzigRun f =
      if f < 2 ^ n - 1 then .outOfFuel (dict n f) else .optimal (dict n (2 ^ n - 1)) := by
  rw [slackDictionary_kleeMinty, dantzigRun_dict (Nat.zero_le _), zero_add]

/-- **Dantzig's rule makes exactly `2 ^ n - 1` pivots on the `n`-dimensional Klee–Minty
program**: a run with fuel `f` runs out of fuel iff `f < 2 ^ n - 1`; otherwise it stops at an
optimal dictionary (`dantzigRun_kleeMinty`). -/
theorem exists_dantzigRun_kleeMinty_eq_outOfFuel_iff (n f : ℕ) :
    (∃ D, (slackDictionary (kleeMintyMatrix n) (kleeMintyRhs n) (kleeMintyObj n) :
        Dictionary (Fin (n + n)) K).dantzigRun f = .outOfFuel D) ↔ f < 2 ^ n - 1 := by
  rw [dantzigRun_kleeMinty]
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => ⟨_, rfl⟩⟩
  · exact ⟨fun ⟨_, hD⟩ => hD.elim, fun h' => absurd h' h⟩

/-- **The Klee–Minty optimum**: the maximum of the `(n + 1)`-dimensional Klee–Minty program is
`100 ^ n`, as certified by the final dictionary of the run of Dantzig's rule. -/
theorem isGreatest_kleeMinty (n : ℕ) :
    IsGreatest ((kleeMintyObj (n + 1) ⬝ᵥ ·) ''
      {x | 0 ≤ x ∧ kleeMintyMatrix (n + 1) *ᵥ x ≤ kleeMintyRhs (n + 1)}) (100 ^ n : K) := by
  set S : Dictionary (Fin (n + 1 + (n + 1))) K :=
    slackDictionary (kleeMintyMatrix (n + 1)) (kleeMintyRhs (n + 1)) (kleeMintyObj (n + 1))
  have hS : S.Feasible := (feasible_slackDictionary_iff _ _ _).2 fun i => by
    simp only [Pi.zero_apply, kleeMintyRhs]
    positivity
  have hrun := dantzigRun_kleeMinty (K := K) (n + 1) (2 ^ (n + 1) - 1)
  rw [ite_eq_right (lt_irrefl _)] at hrun
  obtain ⟨h1, h2, -, h4⟩ := S.dantzigRun_eq_optimal hS hrun
  rw [← image_value_slackDictionary, S.image_value_feasibleSet_eq h1]
  have := (dict (n + 1) (2 ^ (n + 1) - 1) : Dictionary _ K).isGreatest_value h2 h4
  rwa [objConst_dict_top] at this

end Cslib.Algorithms.Lean.Simplex
