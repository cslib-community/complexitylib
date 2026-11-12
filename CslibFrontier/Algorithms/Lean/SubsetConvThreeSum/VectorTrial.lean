/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.Trial
public import CslibFrontier.Algorithms.Lean.VectorConvolution
import Mathlib.Tactic.LinearCombination

/-!
# One base-`r` hashing trial of the reduction from 3SUM to convolution in `[r]^d`

One trial of the reduction of [ChanItakuraMaYu2026], Theorem 3.4 (Section 3.2), from deciding
`c ∈ A + B` for every query `c` to selected entries of the ranked convolution in `[r]^d`
(`CslibFrontier.Algorithms.Lean.VectorConvolution`).

The trial uses the hashes `f`, `g`, `h` of a `Seed p` as in Theorem 2.3, but views a number
`x < r ^ d` as the vector `digitVec r d x` of its base-`r` digits (the paper's `π`). Two numbers
are summed *without carries* when their digit vectors add up to a vector with digits below `r`;
then the digit vector of the sum is the sum of the digit vectors (`add_lt_and_digitVec_add`), and
conversely digit vectors adding up to a digit vector force the numbers to add up
(`add_eq_of_digitVec_add`).

The starred inputs are the elements whose hash is below `r ^ d` (`starLeftV`, `starRightV`), and the
queries are those whose target hash has a *balanced* digit vector: every digit `k < r` occurs
exactly `d / r` times (`Balanced`). For a query `c`, a pair `(a, b)` covers `c` (`VCovers`) when
the digit vectors of `f a` and `g b` add up to that of `h c`. The trial accepts `c` when `h c` is
balanced, some starred pair covers `c` and every covering starred pair sums to `c` (`VAccepts`),
as in Theorem 2.3.

**Soundness** (`exists_add_eq_of_vaccepts`) holds for every modulus and seed, and covering pairs
are congruent to the query modulo a prime (`natCast_add_eq_of_vcovers`). **Witnesses**
(`vaccepts_or_exists_vcovers_ne`): if `c = a + b` and the digit vectors of `f a` and `g b` add up
to a balanced vector, the trial accepts `c` unless a covering pair sums to a different number.

`vtrialM` computes the accepted queries. A balanced vector has size
`t = (d / r) ∑_{k < r} k` (`sum_digits_of_balancedVec`; the paper's `(r - 1) d / 2` when `r ∣ d`).
For each split `t₁ + t₂ = t` the trial runs one selected-entries convolution
(`VectorConvolution.solveM`) over `ℤ ^ 6`, with the left inputs of size `t₁` and the right inputs
of size `t₂`, both weighted by the factorials of their digits; the sum of the answers is
`(∏ j, z j !)` times the six moments over the covering pairs (`ret_vconvM`), and the moment test
is invariant under this positive factor (`momentTest_smul_iff`). This is the paper's loop over
the `O(t)` splits.

## Cost model

The `TimeM` unit-cost model of `CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.Trial`: one tick
to test an element or a query, to insert one weighted vector into a dictionary or to test the
moments of one query, and the ticks of the `VectorConvolution.solveM` runs. Splitting the starred
inputs by the size of their digit vectors is uncharged. `time_vtrialM` is exact.

## Main definitions

* `Cslib.Algorithms.Lean.SubsetConvThreeSum.digitVec`, `digitVal`: base-`r` digit vectors.
* `Cslib.Algorithms.Lean.SubsetConvThreeSum.BalancedVec`, `Balanced`: balanced digit vectors.
* `Cslib.Algorithms.Lean.SubsetConvThreeSum.VCovers`, `starLeftV`, `starRightV`, `vsigma`, `vtau`,
  `VAccepts`: the quantities of a base-`r` trial.
* `Cslib.Algorithms.Lean.SubsetConvThreeSum.vconvM`, `vtrialM`: the trial as a program.

## Main results

* `Cslib.Algorithms.Lean.SubsetConvThreeSum.add_eq_of_digitVec_add`,
  `add_lt_and_digitVec_add`: carry-free addition.
* `Cslib.Algorithms.Lean.SubsetConvThreeSum.exists_add_eq_of_vaccepts`: soundness.
* `Cslib.Algorithms.Lean.SubsetConvThreeSum.natCast_add_eq_of_vcovers`: congruence.
* `Cslib.Algorithms.Lean.SubsetConvThreeSum.vaccepts_or_exists_vcovers_ne`: witnesses.
* `Cslib.Algorithms.Lean.SubsetConvThreeSum.ret_vtrialM`, `time_vtrialM`: what the program returns
  and its exact cost.

## References

* [T. M. Chan, R. Itakura, Z. Ma, Y. Yu, *3SUM Made Simpler (Without Matrix Multiplication),
  k-SUM Hypothesis Refuted for Odd k, and Real 3SUM/APSP Derandomized*][ChanItakuraMaYu2026]
-/

public section

namespace Cslib.Algorithms.Lean.SubsetConvThreeSum

open Finset Cslib Cslib.Algorithms.Lean.TimeM

/-! ### Base-`r` digits -/

/-- The base-`r` digits of `x` in the positions `0, …, d - 1` (the paper's `π`). -/
@[expose] def digitVec (r d x : ℕ) : Fin d → ℕ := fun j => x / r ^ (j : ℕ) % r

/-- The number with base-`r` digits `v`. -/
@[expose] def digitVal (r : ℕ) {d : ℕ} (v : Fin d → ℕ) : ℕ := ∑ j, v j * r ^ (j : ℕ)

theorem digitVal_add (r : ℕ) {d : ℕ} (v w : Fin d → ℕ) :
    digitVal r (v + w) = digitVal r v + digitVal r w := by
  simp only [digitVal, Pi.add_apply, add_mul, sum_add_distrib]

private theorem digitVal_succ (r : ℕ) {d : ℕ} (v : Fin (d + 1) → ℕ) :
    digitVal r v = v 0 + r * digitVal r (Fin.tail v) := by
  simp only [digitVal, Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one, Fin.val_succ,
    pow_succ, Fin.tail, mul_sum]
  congr 1
  exact sum_congr rfl fun j _ => by ring

private theorem digitVec_succ (r : ℕ) {d : ℕ} (x : ℕ) (j : Fin d) :
    digitVec r (d + 1) x j.succ = digitVec r d (x / r) j := by
  simp only [digitVec, Fin.val_succ, pow_succ', Nat.div_div_eq_div_mul]

/-- The digits of a number below `r ^ d` give it back. -/
theorem digitVal_digitVec {r : ℕ} : ∀ {d x : ℕ}, x < r ^ d → digitVal r (digitVec r d x) = x
  | 0, x, hx => by simp only [digitVal, univ_eq_empty, sum_empty]; simp at hx; omega
  | d + 1, x, hx => by
    have hr : 0 < r := by
      rcases Nat.eq_zero_or_pos r with rfl | h
      · simp at hx
      · exact h
    rw [digitVal_succ]
    have htail : Fin.tail (digitVec r (d + 1) x) = digitVec r d (x / r) :=
      funext fun j => digitVec_succ r x j
    rw [htail, digitVal_digitVec (Nat.div_lt_of_lt_mul (by rwa [pow_succ', ] at hx))]
    simp only [digitVec, Fin.val_zero, pow_zero, Nat.div_one]
    exact Nat.mod_add_div x r

/-- A vector of digits below `r` is the digit vector of its number, which is below `r ^ d`. -/
theorem digitVal_lt_and_digitVec {r : ℕ} :
    ∀ {d : ℕ} {v : Fin d → ℕ}, (∀ j, v j < r) →
      digitVal r v < r ^ d ∧ digitVec r d (digitVal r v) = v
  | 0, v, _ => ⟨by simp [digitVal], funext fun j => j.elim0⟩
  | d + 1, v, hv => by
    obtain ⟨hlt, hdig⟩ := digitVal_lt_and_digitVec (d := d) (v := Fin.tail v) fun j => hv j.succ
    have hr : 0 < r := (Nat.zero_le _).trans_lt (hv 0)
    have hv0 := hv 0
    rw [digitVal_succ]
    refine ⟨?_, funext fun j => ?_⟩
    · rw [pow_succ']
      nlinarith
    · have hdiv : (v 0 + r * digitVal r (Fin.tail v)) / r = digitVal r (Fin.tail v) := by
        rw [Nat.add_mul_div_left _ _ hr, Nat.div_eq_of_lt hv0, zero_add]
      refine Fin.cases ?_ (fun j => ?_) j
      · simp only [digitVec, Fin.val_zero, pow_zero, Nat.div_one, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt hv0]
      · rw [digitVec_succ, hdiv, hdig]
        rfl

/-- **Digit vectors adding up** to a digit vector force the numbers to add up. -/
theorem add_eq_of_digitVec_add {r d x y z : ℕ} (hx : x < r ^ d) (hy : y < r ^ d)
    (hz : z < r ^ d) (h : digitVec r d x + digitVec r d y = digitVec r d z) : x + y = z := by
  rw [← digitVal_digitVec hx, ← digitVal_digitVec hy, ← digitVal_digitVec hz, ← h,
    digitVal_add]

/-- **Carry-free addition**: if the digits of `x` and `y` add up to digits below `r` in every
position, then `x + y < r ^ d` and its digit vector is the sum of theirs. -/
theorem add_lt_and_digitVec_add {r d x y : ℕ} (hx : x < r ^ d) (hy : y < r ^ d)
    (h : ∀ j, digitVec r d x j + digitVec r d y j < r) :
    x + y < r ^ d ∧ digitVec r d (x + y) = digitVec r d x + digitVec r d y := by
  have hval : digitVal r (digitVec r d x + digitVec r d y) = x + y := by
    rw [digitVal_add, digitVal_digitVec hx, digitVal_digitVec hy]
  have := digitVal_lt_and_digitVec (v := digitVec r d x + digitVec r d y) h
  rw [hval] at this
  exact this

/-! ### Balanced vectors -/

/-- Every digit of `v` is below `r`, and every `k < r` occurs exactly `d / r` times. -/
@[expose] def BalancedVec (r : ℕ) {d : ℕ} (v : Fin d → ℕ) : Prop :=
  (∀ j, v j < r) ∧ ∀ k < r, #(univ.filter fun j => v j = k) = d / r

instance (r : ℕ) {d : ℕ} (v : Fin d → ℕ) : Decidable (BalancedVec r v) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- `x` is below `r ^ d` and its digit vector is balanced: the paper's "perfectly balanced". -/
@[expose] def Balanced (r d x : ℕ) : Prop := x < r ^ d ∧ BalancedVec r (digitVec r d x)

instance (r d x : ℕ) : Decidable (Balanced r d x) := inferInstanceAs (Decidable (_ ∧ _))

/-- A balanced vector has size `(d / r) ∑_{k < r} k`. -/
theorem sum_digits_of_balancedVec {r d : ℕ} {v : Fin d → ℕ} (hv : BalancedVec r v) :
    ∑ j, v j = d / r * ∑ k ∈ range r, k := by
  rw [← sum_fiberwise_of_maps_to (g := v) (t := range r) fun j _ => mem_range.mpr (hv.1 j),
    mul_sum]
  refine sum_congr rfl fun k hk => ?_
  rw [sum_congr rfl fun j hj => (mem_filter.mp hj).2, sum_const, smul_eq_mul,
    hv.2 k (mem_range.mp hk)]

/-! ### The quantities of a base-`r` trial -/

variable {p : ℕ}

/-- `(a, b)` covers `c` under the seed `s`: the hashes of `a` and `b` are below `r ^ d` and their
digit vectors add up to that of `h c`. -/
@[expose] def VCovers (r d : ℕ) (s : Seed p) (a b c : ℕ) : Prop :=
  s.left a < r ^ d ∧ s.right b < r ^ d ∧
    digitVec r d (s.left a) + digitVec r d (s.right b) = digitVec r d (s.target c)

instance (r d : ℕ) (s : Seed p) (a b c : ℕ) : Decidable (VCovers r d s a b c) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The elements of `A` whose left hash is below `r ^ d`: the paper's `A*` for isolated `A`. -/
@[expose] def starLeftV (r d : ℕ) (s : Seed p) (A : List ℕ) : List ℕ :=
  A.filter fun a => decide (s.left a < r ^ d)

/-- The elements of `B` whose right hash is below `r ^ d`. -/
@[expose] def starRightV (r d : ℕ) (s : Seed p) (B : List ℕ) : List ℕ :=
  B.filter fun b => decide (s.right b < r ^ d)

/-- `σ(c)`: the number of starred pairs covering `c`. -/
@[expose] def vsigma (r d : ℕ) (s : Seed p) (A B : List ℕ) (c : ℕ) : ℤ :=
  pairSum (VCovers r d s · · c) (starLeftV r d s A) (starRightV r d s B) fun _ _ => 1

/-- `τ(c)`: the sum of `(a + b - c) ^ 2` over the starred pairs covering `c`. -/
@[expose] def vtau (r d : ℕ) (s : Seed p) (A B : List ℕ) (c : ℕ) : ℤ :=
  pairSum (VCovers r d s · · c) (starLeftV r d s A) (starRightV r d s B) fun a b =>
    ((a : ℤ) + b - c) ^ 2

/-- The trial accepts `c`: `h c` is balanced, some starred pair covers `c`, and every covering
starred pair sums to `c`. -/
@[expose] def VAccepts (r d : ℕ) (s : Seed p) (A B : List ℕ) (c : ℕ) : Prop :=
  Balanced r d (s.target c) ∧ 0 < vsigma r d s A B c ∧ vtau r d s A B c = 0

instance (r d : ℕ) (s : Seed p) (A B : List ℕ) (c : ℕ) : Decidable (VAccepts r d s A B c) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ### Soundness, congruence and witnesses -/

/-- **Soundness of a base-`r` trial**: if the trial accepts `c`, then `c = a + b` for some
`a ∈ A` and `b ∈ B`. -/
theorem exists_add_eq_of_vaccepts {r d : ℕ} {s : Seed p} {A B : List ℕ} {c : ℕ}
    (h : VAccepts r d s A B c) : ∃ a ∈ A, ∃ b ∈ B, a + b = c := by
  obtain ⟨a, ha, b, hb, -, habc⟩ := exists_add_eq_of_pairSum h.2.1 h.2.2
  exact ⟨a, List.mem_of_mem_filter ha, b, List.mem_of_mem_filter hb, habc⟩

/-- **Covering pairs are congruent to the query**: if `ξ ≠ 0` in the field `ZMod p` and
`h c < r ^ d`, a pair covering `c` satisfies `a + b ≡ c (mod p)`. -/
theorem natCast_add_eq_of_vcovers [Fact p.Prime] {r d : ℕ} {s : Seed p} (hξ : s.ξ ≠ 0)
    {a b c : ℕ} (hc : s.target c < r ^ d) (h : VCovers r d s a b c) :
    ((a + b : ℕ) : ZMod p) = c :=
  natCast_add_eq_of_left_add_right hξ (add_eq_of_digitVec_add h.1 h.2.1 hc h.2.2)

/-- **A witness with carry-free balanced hashes** (the event of the completeness analysis of
[ChanItakuraMaYu2026], Theorem 3.4): if `a ∈ A`, `b ∈ B`, `a + b = c`, the hashes `f a`, `g b`
are below `r ^ d` with digit vectors adding up to a balanced vector, and `r ^ d ≤ p`, then the
trial accepts `c` unless some covering starred pair sums to a number other than `c`. -/
theorem vaccepts_or_exists_vcovers_ne {r d : ℕ} (hp : r ^ d ≤ p) {s : Seed p} {A B : List ℕ}
    {a b c : ℕ} (ha : a ∈ A) (hb : b ∈ B) (habc : a + b = c) (hx : s.left a < r ^ d)
    (hy : s.right b < r ^ d)
    (hbal : BalancedVec r (digitVec r d (s.left a) + digitVec r d (s.right b))) :
    VAccepts r d s A B c ∨ ∃ a' ∈ starLeftV r d s A, ∃ b' ∈ starRightV r d s B,
      VCovers r d s a' b' c ∧ a' + b' ≠ c := by
  obtain ⟨hlt, hdig⟩ := add_lt_and_digitVec_add hx hy hbal.1
  have htarget := target_eq_add habc (hlt.trans_le hp)
  have hcov : VCovers r d s a b c := ⟨hx, hy, by rw [htarget, hdig]⟩
  have haS : a ∈ starLeftV r d s A := List.mem_filter.mpr ⟨ha, by simpa using hx⟩
  have hbS : b ∈ starRightV r d s B := List.mem_filter.mpr ⟨hb, by simpa using hy⟩
  by_cases hτ : vtau r d s A B c = 0
  · refine Or.inl ⟨⟨htarget ▸ hlt, by rwa [htarget, hdig]⟩, pairSum_one_pos haS hbS hcov, hτ⟩
  · obtain ⟨a', ha', b', hb', hc', hne⟩ := exists_of_pairSum_ne_zero hτ
    refine Or.inr ⟨a', ha', b', hb', hc', fun h => hne ?_⟩
    rw [← h]; push_cast; ring

/-! ### The trial as a program -/

/-- The moment test is invariant under multiplying the moments by a positive integer. -/
theorem momentTest_smul_iff {k : ℕ} (hk : 0 < k) (c : ℕ) (m : Moments) :
    MomentTest c ((k : Moments) * m) ↔ MomentTest c m := by
  have hk' : (0 : ℤ) < k := by exact_mod_cast hk
  simp only [MomentTest, Pi.mul_apply, Pi.natCast_apply]
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨pos_of_mul_pos_right h0 hk'.le, ?_⟩
    have : (k : ℤ) * (m 4 + m 5 + 2 * m 3 - 2 * c * m 1 - 2 * c * m 2 + (c : ℤ) ^ 2 * m 0) = 0 := by
      linear_combination h1
    exact (mul_eq_zero.mp this).resolve_left hk'.ne'
  · rintro ⟨h0, h1⟩
    exact ⟨mul_pos hk' h0, by linear_combination (k : ℤ) * h1⟩

/-- The digit vectors of the left hashes of `As` with size `t₁`, weighted by the factorials of
their digits times `w`, as a list of dictionary entries. -/
@[expose] def leftEntries (r d t₁ : ℕ) (σ : Seed p) (As : List ℕ) (w : ℕ → Moments) :
    List ((Fin d → ℕ) × Moments) :=
  (As.filter fun a => ∑ j, digitVec r d (σ.left a) j = t₁).map fun a =>
    (digitVec r d (σ.left a), (vecFactorial (digitVec r d (σ.left a)) : Moments) * w a)

/-- The same for the right hashes of `Bs` with size `t₂`. -/
@[expose] def rightEntries (r d t₂ : ℕ) (σ : Seed p) (Bs : List ℕ) (v : ℕ → Moments) :
    List ((Fin d → ℕ) × Moments) :=
  (Bs.filter fun b => ∑ j, digitVec r d (σ.right b) j = t₂).map fun b =>
    (digitVec r d (σ.right b), (vecFactorial (digitVec r d (σ.right b)) : Moments) * v b)

/-- The selected-entries convolutions of a base-`r` trial: one run of `VectorConvolution.solveM`
for each split `t₁ + (t - t₁) = t`, summed query by query. -/
@[expose] def vconvM (r d s t : ℕ) (σ : Seed p) (As Bs : List ℕ) (Q : List (Fin d → ℕ))
    (w v : ℕ → Moments) : TimeM ℕ (List Moments) := do
  let rows ← (List.range (t + 1)).mapM fun t₁ => do
    let F ← sparseM (leftEntries r d t₁ σ As w)
    let G ← sparseM (rightEntries r d (t - t₁) σ Bs v)
    VectorConvolution.solveM (List.finRange d) r s F G Q
  pure (rows.foldr (List.zipWith (· + ·)) (Q.map fun _ => 0))

private theorem foldr_zipWith_map {α : Type*} (Q : List α) (h : ℕ → α → Moments) (L : List ℕ) :
    (L.map fun t₁ => Q.map (h t₁)).foldr (List.zipWith (· + ·)) (Q.map fun _ => 0) =
      Q.map fun z => (L.map fun t₁ => h t₁ z).sum := by
  induction L with
  | nil => simp
  | cons t₁ L ih =>
    rw [List.map_cons, List.foldr_cons, ih]
    clear ih
    induction Q with
    | nil => rfl
    | cons z Q ihQ => simp [ihQ]

private theorem ret_sparseM_entries {d : ℕ} {l : List ℕ} (key : ℕ → Fin d → ℕ)
    (w : ℕ → Moments) (x : Fin d → ℕ) :
    (sparseM (l.map fun a => (key a, (vecFactorial (key a) : Moments) * w a))).ret x =
      (vecFactorial x : Moments) * (l.map fun a => if key a = x then w a else 0).sum := by
  rw [ret_sparseM, List.map_map, ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun a _ => ?_
  by_cases h : key a = x
  · simp [h]
  · simp [h]

/-- The vector convolution of two sparse dictionaries sums the products of the weights over the
pairs whose vectors add up to the query vector. -/
private theorem vecConvolution_sparse {d : ℕ} (As Bs : List ℕ) (kA kB : ℕ → Fin d → ℕ)
    (w v : ℕ → Moments) (z : Fin d → ℕ) :
    vecConvolution (fun x => (As.map fun a => if kA a = x then w a else 0).sum)
        (fun y => (Bs.map fun b => if kB b = y then v b else 0).sum) z =
      (As.map fun a => (Bs.map fun b => if kA a + kB b = z then w a * v b else 0).sum).sum := by
  induction As with
  | nil => simp [vecConvolution]
  | cons a As ih =>
    rw [List.map_cons, List.sum_cons, ← ih]
    simp only [vecConvolution, List.map_cons, List.sum_cons, add_mul, sum_add_distrib]
    congr 1
    simp only [ite_mul, zero_mul]
    rw [sum_ite_eq (Iic z) (kA a)]
    split_ifs with hle
    · rw [← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun b _ => ?_
      have hle' : ∀ j, kA a j ≤ z j := mem_Iic.mp hle
      have : kB b = z - kA a ↔ kA a + kB b = z := by
        constructor
        · intro h; funext j; have := congrFun h j; have := hle' j
          simp only [Pi.sub_apply, Pi.add_apply] at *; omega
        · intro h; funext j; have := congrFun h j
          simp only [Pi.sub_apply, Pi.add_apply] at *; omega
      by_cases h : kA a + kB b = z
      · rw [ite_eq_left (this.mpr h), ite_eq_left h]
      · rw [ite_eq_right (mt this.mp h), ite_eq_right h, mul_zero]
    · symm
      refine List.sum_eq_zero fun x hx => ?_
      obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx
      have : ¬ kA a + kB b = z := fun h => hle (mem_Iic.mpr (h ▸ fun j => Nat.le_add_right _ _))
      simp [this]

private theorem sum_list_map_comm {α : Type*} (s : Finset ℕ) (L : List α)
    (f : ℕ → α → Moments) :
    ∑ t₁ ∈ s, (L.map (f t₁)).sum = (L.map fun x => ∑ t₁ ∈ s, f t₁ x).sum := by
  induction L with
  | nil => simp
  | cons x L ih => simp [sum_add_distrib, ih]

private theorem sum_map_filter {α : Type*} (L : List α) (P : α → Prop) [DecidablePred P]
    (f : α → Moments) : ((L.filter fun x => decide (P x)).map f).sum =
      (L.map fun x => if P x then f x else 0).sum := by
  induction L with
  | nil => simp
  | cons x L ih => by_cases h : P x <;> simp [h, ih]

/-- The pair sums over the splits of the size of the left vector add up to the pair sum. -/
private theorem sum_pairSum_split (cov : ℕ → ℕ → Prop) [DecidableRel cov] (φ : ℕ → ℕ) (t : ℕ)
    (hφ : ∀ a b, cov a b → φ a ≤ t) (A B : List ℕ) (F : ℕ → ℕ → Moments) :
    ∑ t₁ ∈ range (t + 1), pairSum (fun a b => cov a b ∧ φ a = t₁) A B F = pairSum cov A B F := by
  simp only [pairSum, sum_list_map_comm]
  congr 1
  refine List.map_congr_left fun a _ => ?_
  congr 1
  refine List.map_congr_left fun b _ => ?_
  by_cases h : cov a b
  · rw [sum_eq_single (φ a)]
    · simp [h]
    · intro t₁ _ hne; simp [h, Ne.symm hne]
    · intro hn; exact absurd (mem_range.mpr (Nat.lt_succ_of_le (hφ a b h))) hn
  · simp [h]

/-- **What the convolutions of a base-`r` trial return** at the digit vectors of balanced
targets: `(∏ j, z j !)` times the pair sums of the weight products. -/
theorem ret_vconvM {r d s : ℕ} (σ : Seed p) {As Bs Cs : List ℕ}
    (hA : ∀ a ∈ As, σ.left a < r ^ d) (hB : ∀ b ∈ Bs, σ.right b < r ^ d)
    (hC : ∀ c ∈ Cs, Balanced r d (σ.target c)) (hs : s ≤ d / r * ∑ k ∈ range r, k)
    (w v : ℕ → Moments) :
    (vconvM r d s (d / r * ∑ k ∈ range r, k) σ As Bs (Cs.map fun c => digitVec r d (σ.target c))
      w v).ret = Cs.map fun c => (vecFactorial (digitVec r d (σ.target c)) : Moments) *
        pairSum (VCovers r d σ · · c) As Bs fun a b => w a * v b := by
  set t := d / r * ∑ k ∈ range r, k
  set Q := Cs.map fun c => digitVec r d (σ.target c)
  set kA : ℕ → Fin d → ℕ := fun a => digitVec r d (σ.left a)
  set kB : ℕ → Fin d → ℕ := fun b => digitVec r d (σ.right b)
  have hQ : ∀ z ∈ Q, (∀ i, z i < r) ∧ ∑ i, z i = t := by
    intro z hz
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hz
    exact ⟨(hC c hc).2.1, sum_digits_of_balancedVec (hC c hc).2⟩
  -- one split returns the factorial times the pair sum restricted to the split
  have hrow : ∀ t₁ ∈ List.range (t + 1),
      (VectorConvolution.solveM (List.finRange d) r s (sparseM (leftEntries r d t₁ σ As w)).ret
        (sparseM (rightEntries r d (t - t₁) σ Bs v)).ret Q).ret =
      Q.map fun z => (vecFactorial z : Moments) *
        pairSum (fun a b => kA a + kB b = z ∧ ∑ j, kA a j = t₁) As Bs fun a b => w a * v b := by
    intro t₁ ht₁
    have ht₁ : t₁ ≤ t := Nat.lt_succ_iff.mp (List.mem_range.mp ht₁)
    have hF := funext fun x => ret_sparseM_entries (l := As.filter fun a =>
      ∑ j, kA a j = t₁) kA w x
    have hG := funext fun y => ret_sparseM_entries (l := Bs.filter fun b =>
      ∑ j, kB b j = t - t₁) kB v y
    rw [leftEntries, rightEntries, hF, hG]
    rw [VectorConvolution.ret_solveM_factorial (List.nodup_finRange d) (List.mem_finRange)
      (t₁ := t₁) (t₂ := t - t₁) (fun x hx => ?_) (fun y hy => ?_)
      (fun z hz => ⟨(hQ z hz).1, by rw [(hQ z hz).2]; omega⟩) (by omega)]
    · refine List.map_congr_left fun z hz => ?_
      rw [vecConvolution_sparse, sum_map_filter]
      congr 1
      simp only [pairSum]
      refine congrArg List.sum (List.map_congr_left fun a _ => ?_)
      rw [sum_map_filter]
      by_cases ha : ∑ j, kA a j = t₁
      · simp only [ha, ite_true, and_true]
        refine congrArg List.sum (List.map_congr_left fun b _ => ?_)
        by_cases hab : kA a + kB b = z
        · have hsz : ∑ j, kB b j = t - t₁ := by
            have := congrArg (fun u : Fin d → ℕ => ∑ j, u j) hab
            simp only [Pi.add_apply, sum_add_distrib, ha, (hQ z hz).2] at this
            omega
          simp [hab, hsz]
        · simp [hab]
      · simp only [ha, ite_false, and_false]
        simp
    · obtain ⟨e, he, hne⟩ := List.exists_mem_ne_zero_of_sum_ne_zero hx
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
      by_cases h : kA a = x
      · rw [← h]; simpa using (List.mem_filter.mp ha).2
      · simp [h] at hne
    · obtain ⟨e, he, hne⟩ := List.exists_mem_ne_zero_of_sum_ne_zero hy
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp he
      by_cases h : kB b = y
      · rw [← h]; simpa using (List.mem_filter.mp hb).2
      · simp [h] at hne
  simp only [vconvM, ret_bind, ret_pure, ret_listMapM]
  rw [List.map_congr_left hrow, foldr_zipWith_map, List.map_map]
  refine List.map_congr_left fun c hc => ?_
  simp only [Function.comp_apply]
  rw [← List.sum_toFinset _ List.nodup_range,
    show (List.range (t + 1)).toFinset = range (t + 1) by ext; simp, ← mul_sum,
    sum_pairSum_split (fun a b => kA a + kB b = digitVec r d (σ.target c)) (fun a => ∑ j, kA a j) t
      (fun a b hab => ?_)]
  · congr 1
    refine pairSum_congr fun a ha b hb => ?_
    exact ⟨fun h => ⟨hA a ha, hB b hb, h⟩, fun h => h.2.2⟩
  · have := congrArg (fun u : Fin d → ℕ => ∑ j, u j) hab
    simp only [Pi.add_apply, sum_add_distrib, sum_digits_of_balancedVec (hC c hc).2] at this
    omega

/-- The size `(d / r) ∑_{k < r} k` of a balanced vector: the paper's `t = (r - 1) d / 2` when
`r ∣ d`. -/
@[expose] def balancedSize (r d : ℕ) : ℕ := d / r * ∑ k ∈ range r, k

/-- **One base-`r` trial**: the queries of `C` accepted under the seed `σ`, for isolated inputs
`Ag`, `Bg`. The six moments are computed by one selected-entries convolution in `[r]^d` over
`ℤ ^ 6` per split of `balancedSize r d`. -/
@[expose] def vtrialM (r d s : ℕ) (σ : Seed p) (Ag Bg C : List ℕ) : TimeM ℕ (List ℕ) := do
  let As ← filterTickM (fun a => σ.left a < r ^ d) Ag
  let Bs ← filterTickM (fun b => σ.right b < r ^ d) Bg
  let Cs ← filterTickM (fun c => Balanced r d (σ.target c)) C
  let ms ← vconvM r d s (balancedSize r d) σ As Bs (Cs.map fun c => digitVec r d (σ.target c))
    leftWeight rightWeight
  let acc ← filterTickM (fun row : ℕ × Moments => MomentTest row.1 row.2) (Cs.zip ms)
  pure (acc.map Prod.fst)

private theorem vecFactorial_pos {d : ℕ} (x : Fin d → ℕ) : 0 < vecFactorial x :=
  Nat.pos_of_ne_zero (prod_ne_zero_iff.mpr fun _ _ => Nat.factorial_ne_zero _)

/-- The starred inputs and the balanced queries of a trial, as the program computes them. -/
private theorem vtrial_filters {r d : ℕ} (σ : Seed p) (Ag Bg C : List ℕ) :
    (filterTickM (fun a => σ.left a < r ^ d) Ag).ret = starLeftV r d σ Ag ∧
    (filterTickM (fun b => σ.right b < r ^ d) Bg).ret = starRightV r d σ Bg ∧
    (filterTickM (fun c => Balanced r d (σ.target c)) C).ret =
      C.filter (fun c => decide (Balanced r d (σ.target c))) :=
  ⟨by rw [ret_filterTickM]; rfl, by rw [ret_filterTickM]; rfl, ret_filterTickM _ _⟩

/-- The convolutions of a trial return the factorial-weighted moments of the starred inputs. -/
private theorem ret_vconvM_trial {r d s : ℕ} (σ : Seed p) (Ag Bg C : List ℕ)
    (hs : s ≤ balancedSize r d) :
    (vconvM r d s (balancedSize r d) σ (starLeftV r d σ Ag) (starRightV r d σ Bg)
      ((C.filter fun c => decide (Balanced r d (σ.target c))).map
        fun c => digitVec r d (σ.target c)) leftWeight rightWeight).ret =
      (C.filter fun c => decide (Balanced r d (σ.target c))).map fun c =>
        (vecFactorial (digitVec r d (σ.target c)) : Moments) *
          pairSum (VCovers r d σ · · c) (starLeftV r d σ Ag) (starRightV r d σ Bg)
            fun a b => leftWeight a * rightWeight b :=
  ret_vconvM σ (fun a ha => by simpa using (List.mem_filter.mp ha).2)
    (fun b hb => by simpa using (List.mem_filter.mp hb).2)
    (fun c hc => by simpa using (List.mem_filter.mp hc).2) hs leftWeight rightWeight

/-- **What a base-`r` trial returns**: the queries of `C` that it accepts, for every threshold
`s ≤ balancedSize r d`. -/
theorem ret_vtrialM {r d s : ℕ} (σ : Seed p) (Ag Bg C : List ℕ) (hs : s ≤ balancedSize r d) :
    (vtrialM r d s σ Ag Bg C).ret = C.filter fun c => decide (VAccepts r d σ Ag Bg c) := by
  obtain ⟨e₁, e₂, e₃⟩ := vtrial_filters (r := r) (d := d) σ Ag Bg C
  rw [vtrialM]
  simp only [ret_bind, ret_pure]
  rw [e₁, e₂, e₃, ret_vconvM_trial σ Ag Bg C hs, ret_filterTickM, zip_map_self, List.filter_map,
    List.map_map, List.filter_filter]
  rw [show (Prod.fst ∘ fun c => (c, (vecFactorial (digitVec r d (σ.target c)) : Moments) *
      pairSum (VCovers r d σ · · c) (starLeftV r d σ Ag) (starRightV r d σ Bg)
        fun a b => leftWeight a * rightWeight b)) = id from rfl, List.map_id]
  refine List.filter_congr fun c _ => ?_
  have := momentTest_iff (VCovers r d σ · · c) (starLeftV r d σ Ag) (starRightV r d σ Bg) c
  simp only [Function.comp_apply, momentTest_smul_iff (vecFactorial_pos _), VAccepts, vsigma,
    vtau, ← this, Bool.decide_and, Bool.and_comm]

private theorem length_foldr_zipWith {n : ℕ} (init : List Moments) (hinit : init.length = n) :
    ∀ rows : List (List Moments), (∀ L ∈ rows, L.length = n) →
      (rows.foldr (List.zipWith (· + ·)) init).length = n
  | [], _ => hinit
  | L :: rows, h => by
    rw [List.foldr_cons, List.length_zipWith, h L (List.mem_cons_self ..),
      length_foldr_zipWith init hinit rows fun L' hL' => h L' (List.mem_cons_of_mem _ hL'),
      min_self]

/-- The convolutions of a trial return one row of moments per query. -/
theorem length_ret_vconvM (r d s t : ℕ) (σ : Seed p) (As Bs : List ℕ) (Q : List (Fin d → ℕ))
    (w v : ℕ → Moments) : (vconvM r d s t σ As Bs Q w v).ret.length = Q.length := by
  simp only [vconvM, ret_bind, ret_pure, ret_listMapM]
  refine length_foldr_zipWith _ (by simp) _ fun L hL => ?_
  obtain ⟨t₁, -, rfl⟩ := List.mem_map.mp hL
  simp [VectorConvolution.solveM, TrimmedYates.Passes.solveM]

/-- **The cost of a base-`r` trial**, exactly: one tick per element of `Ag`, `Bg` and `C` and per
balanced query (the final test); for each split `t₁ + t₂ = balancedSize r d`, one tick per
starred input of size `t₁` or `t₂` (dictionary insertions) and the ticks of one
`VectorConvolution.solveM` run. -/
theorem time_vtrialM {r d s : ℕ} (σ : Seed p) (Ag Bg C : List ℕ) :
    (vtrialM r d s σ Ag Bg C).time = Ag.length + Bg.length + C.length +
      ((List.range (balancedSize r d + 1)).map fun t₁ =>
        (leftEntries r d t₁ σ (starLeftV r d σ Ag) leftWeight).length +
        (rightEntries r d (balancedSize r d - t₁) σ (starRightV r d σ Bg) rightWeight).length +
        3 * (r * d + 1) *
          (#((Fintype.piFinset fun _ : Fin d => range r).filter fun x => ∑ i, x i ≤ s) +
            ((C.filter fun c => decide (Balanced r d (σ.target c))).map fun c =>
              #((Iic (digitVec r d (σ.target c))).filter fun y => s ≤ ∑ i, y i)).sum)).sum +
      (C.filter fun c => decide (Balanced r d (σ.target c))).length := by
  obtain ⟨e₁, e₂, e₃⟩ := vtrial_filters (r := r) (d := d) σ Ag Bg C
  rw [vtrialM]
  simp only [time_bind, time_pure]
  rw [e₁, e₂, e₃, time_filterTickM, time_filterTickM, time_filterTickM, time_filterTickM,
    List.length_zip, length_ret_vconvM, List.length_map, min_self]
  simp only [vconvM, time_bind, time_pure, time_listMapM, time_sparseM,
    VectorConvolution.time_solveM (List.nodup_finRange d) List.mem_finRange, List.length_finRange,
    List.map_map, Function.comp_def, add_zero]
  simp only [add_assoc]

end Cslib.Algorithms.Lean.SubsetConvThreeSum
