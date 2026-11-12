/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Hierarchy
public import CslibFrontier.Computability.Complexity.Classes.Time
public import CslibFrontier.Computability.Complexity.Reduction
import CslibFrontier.Computability.Complexity.Classes.TimeSpace.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.TwoPow
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# Exponential time

`Cslib.Complexity.EXP enc` is the union of the deterministic time classes
`Cslib.Complexity.DTIME enc (2 ^ n ^ k)` over `k`, and `Cslib.Complexity.E enc` the union of the
classes `DTIME enc (2 ^ (k * n))`, as in the classes proposed upstream in cslib pull request #767.
Their nondeterministic counterparts `Cslib.Complexity.NEXP enc` and `Cslib.Complexity.NE enc` are
the unions of the classes `Cslib.Complexity.NTIME enc (2 ^ n ^ k)` and `NTIME enc (2 ^ (k * n))`
[Arora and Barak, Sections 2.1 and 2.6][AroraBarak09].

`P` is the union of the classes `DTIME (n ^ k)` (`Cslib.Complexity.mem_P_iff_exists_mem_DTIME`)
and `NP` that of the classes `NTIME (n ^ k)` (`Cslib.Complexity.mem_NP_iff_exists_mem_NTIME`), so
`P ⊆ E ⊆ EXP`, `NP ⊆ NE ⊆ NEXP`, and each deterministic class is within its nondeterministic
counterpart (`Cslib.Complexity.DTIME_subset_NTIME`).

The inclusion `P ⊆ EXP` is strict for problems on bit words (`Cslib.Complexity.P_ssubset_EXP`):
the diagonal problem of `Cslib.Complexity.diagonal` is decided within time `O(2 ^ (4 * n))`, which
is within `2 ^ n ^ 2` from `n = 4` on, and is not in `P` by the diagonal argument of the time
hierarchy theorem [Arora and Barak, Theorem 3.1][AroraBarak09], [Sipser, Theorem 9.10][Sipser2013].

Polynomial-time computation on a bit word `y` paired with unary padding `2 ^ |y|` gives a problem
in `E` (`Cslib.Complexity.setOf_mem_E_of_computableInPolyTime_pad`): the padding is written and
`Ψ` run in time `2 ^ O(|y|)` (`Turing.MultiTapeTM.ComputableInPolyTime.exists_computableInO_pad`).

## Main definitions

* `Cslib.Complexity.E`, `Cslib.Complexity.EXP`: deterministic exponential time.
* `Cslib.Complexity.NE`, `Cslib.Complexity.NEXP`: nondeterministic exponential time.

## Main results

* `Cslib.Complexity.P_subset_E`, `Cslib.Complexity.E_subset_EXP`,
  `Cslib.Complexity.P_subset_EXP`: polynomial time is within exponential time.
* `Cslib.Complexity.NP_subset_NE`, `Cslib.Complexity.NE_subset_NEXP`,
  `Cslib.Complexity.NP_subset_NEXP`: the same for nondeterministic time.
* `Cslib.Complexity.E_subset_NE`, `Cslib.Complexity.EXP_subset_NEXP`: determinism is a special
  case.
* `Cslib.Complexity.DTIME_two_pow_subset_EXP`, `Cslib.Complexity.NTIME_two_pow_subset_NEXP`: time
  `2 ^ h n` for a polynomially bounded `h` is exponential time.
* `Cslib.Complexity.P_ssubset_EXP`: polynomial time is strictly within exponential time.
* `Cslib.Complexity.compl_mem_E`, `Cslib.Complexity.compl_mem_EXP`: closure under complement.
* `Cslib.Complexity.setOf_mem_E_of_computableInPolyTime_pad`: polynomial time on inputs
  padded to length `2 ^ n` gives `E`.
* `Cslib.Complexity.PolyTimeReducible.mem_EXP`: `EXP` is closed under polynomial-time many-one
  reductions.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM Filter

variable {α : Type*} {enc : α ↪ List Bool} {A : Set α}

/-- The problems decidable within time `O(2 ^ n ^ k)` for some `k`, on instances whose encoding
under `enc` has length `n` [Arora and Barak, Section 2.6][AroraBarak09]. -/
def EXP (enc : α ↪ List Bool) : Set (Set α) := ⋃ k, DTIME enc fun n => 2 ^ n ^ k

theorem mem_EXP_iff : A ∈ EXP enc ↔ ∃ k, A ∈ DTIME enc fun n => 2 ^ n ^ k :=
  Set.mem_iUnion

/-- The problems decidable within time `O(2 ^ (k * n))` for some `k`, on instances whose encoding
under `enc` has length `n`. -/
def E (enc : α ↪ List Bool) : Set (Set α) := ⋃ k, DTIME enc fun n => 2 ^ (k * n)

theorem mem_E_iff : A ∈ E enc ↔ ∃ k, A ∈ DTIME enc fun n => 2 ^ (k * n) :=
  Set.mem_iUnion

/-- The problems decidable by a nondeterministic machine within time `O(2 ^ n ^ k)` for some `k`,
on instances whose encoding under `enc` has length `n`
[Arora and Barak, Section 2.6][AroraBarak09]. -/
def NEXP (enc : α ↪ List Bool) : Set (Set α) := ⋃ k, NTIME enc fun n => 2 ^ n ^ k

theorem mem_NEXP_iff : A ∈ NEXP enc ↔ ∃ k, A ∈ NTIME enc fun n => 2 ^ n ^ k :=
  Set.mem_iUnion

/-- The problems decidable by a nondeterministic machine within time `O(2 ^ (k * n))` for some
`k`, on instances whose encoding under `enc` has length `n`. -/
def NE (enc : α ↪ List Bool) : Set (Set α) := ⋃ k, NTIME enc fun n => 2 ^ (k * n)

theorem mem_NE_iff : A ∈ NE enc ↔ ∃ k, A ∈ NTIME enc fun n => 2 ^ (k * n) :=
  Set.mem_iUnion

/-- A polynomial is eventually below `2 ^ n`. -/
private theorem eventually_pow_le_two_pow (k : ℕ) : ∀ᶠ n in atTop, n ^ k ≤ 2 ^ (1 * n) := by
  filter_upwards [PolynomiallyBounded.eventually_lt_two_pow (f := (· ^ k)) (by fun_prop)]
    with n hn
  simpa only [one_mul] using hn.le

/-- `2 ^ (k * n)` is eventually below `2 ^ n ^ 2`. -/
private theorem eventually_two_pow_mul_le (k : ℕ) : ∀ᶠ n in atTop, 2 ^ (k * n) ≤ 2 ^ n ^ 2 := by
  filter_upwards [eventually_ge_atTop k] with n hn
  exact Nat.pow_le_pow_right (by norm_num) (by rw [sq]; exact Nat.mul_le_mul_right n hn)

/-- **Polynomial time is within linear exponential time.** -/
theorem P_subset_E : P enc ⊆ E enc := fun _ hA =>
  let ⟨k, hk⟩ := mem_P_iff_exists_mem_DTIME.mp hA
  mem_E_iff.mpr ⟨1, DTIME_mono_of_eventually_le (eventually_pow_le_two_pow k) hk⟩

/-- **Linear exponential time is within exponential time.** -/
theorem E_subset_EXP : E enc ⊆ EXP enc := fun _ hA =>
  let ⟨k, hk⟩ := mem_E_iff.mp hA
  mem_EXP_iff.mpr ⟨2, DTIME_mono_of_eventually_le (eventually_two_pow_mul_le k) hk⟩

/-- **Nondeterministic polynomial time is within nondeterministic linear exponential time.** -/
theorem NP_subset_NE {α : Type} {enc : α ↪ List Bool} : NP enc ⊆ NE enc := fun _ hA =>
  let ⟨k, hk⟩ := mem_NP_iff_exists_mem_NTIME.mp hA
  mem_NE_iff.mpr ⟨1, NTIME_mono_of_eventually_le (eventually_pow_le_two_pow k) hk⟩

/-- **Nondeterministic linear exponential time is within nondeterministic exponential time.** -/
theorem NE_subset_NEXP : NE enc ⊆ NEXP enc := fun _ hA =>
  let ⟨k, hk⟩ := mem_NE_iff.mp hA
  mem_NEXP_iff.mpr ⟨2, NTIME_mono_of_eventually_le (eventually_two_pow_mul_le k) hk⟩

/-- **Nondeterministic polynomial time is within nondeterministic exponential time.** -/
theorem NP_subset_NEXP {α : Type} {enc : α ↪ List Bool} : NP enc ⊆ NEXP enc :=
  NP_subset_NE.trans NE_subset_NEXP

/-- **Linear exponential time is within nondeterministic linear exponential time.** -/
theorem E_subset_NE : E enc ⊆ NE enc := fun _ hA =>
  let ⟨k, hk⟩ := mem_E_iff.mp hA
  mem_NE_iff.mpr ⟨k, DTIME_subset_NTIME hk⟩

/-- **Exponential time is within nondeterministic exponential time.** -/
theorem EXP_subset_NEXP : EXP enc ⊆ NEXP enc := fun _ hA =>
  let ⟨k, hk⟩ := mem_EXP_iff.mp hA
  mem_NEXP_iff.mpr ⟨k, DTIME_subset_NTIME hk⟩

/-- **Polynomial time is within exponential time.** -/
theorem P_subset_EXP : P enc ⊆ EXP enc :=
  P_subset_E.trans E_subset_EXP

/-- Deterministic time `2 ^ h n`, for a polynomially bounded exponent `h`, is within exponential
time. -/
theorem DTIME_two_pow_subset_EXP {h : ℕ → ℕ} (hh : PolynomiallyBounded h) :
    DTIME enc (fun n => 2 ^ h n) ⊆ EXP enc := fun _ hA =>
  let ⟨k, hk⟩ := hh
  mem_EXP_iff.mpr ⟨k, DTIME_mono_of_eventually_le
    (hk.mono fun _ hn => Nat.pow_le_pow_right (by norm_num) hn) hA⟩

/-- Nondeterministic time `2 ^ h n`, for a polynomially bounded exponent `h`, is within
nondeterministic exponential time. -/
theorem NTIME_two_pow_subset_NEXP {h : ℕ → ℕ} (hh : PolynomiallyBounded h) :
    NTIME enc (fun n => 2 ^ h n) ⊆ NEXP enc := fun _ hA =>
  let ⟨k, hk⟩ := hh
  mem_NEXP_iff.mpr ⟨k, NTIME_mono_of_eventually_le
    (hk.mono fun _ hn => Nat.pow_le_pow_right (by norm_num) hn) hA⟩

/-- `E` is closed under complement (`Cslib.Complexity.compl_mem_DTIME`). -/
theorem compl_mem_E {α : Type} {enc : α ↪ List Bool} {A : Set α} (h : A ∈ E enc) : Aᶜ ∈ E enc :=
  let ⟨k, hk⟩ := mem_E_iff.mp h
  mem_E_iff.mpr ⟨k, compl_mem_DTIME hk⟩

/-- `EXP` is closed under complement (`Cslib.Complexity.compl_mem_DTIME`). -/
theorem compl_mem_EXP {α : Type} {enc : α ↪ List Bool} {A : Set α} (h : A ∈ EXP enc) :
    Aᶜ ∈ EXP enc :=
  let ⟨k, hk⟩ := mem_EXP_iff.mp h
  mem_EXP_iff.mpr ⟨k, compl_mem_DTIME hk⟩

/-- The diagonal problem is in exponential time. -/
theorem setOf_diagonal_mem_EXP : {x | diagonal x = true} ∈ EXP encBits :=
  mem_EXP_iff.mpr ⟨2, DTIME_mono_of_eventually_le
    (t₁ := fun n => 2 ^ (4 * n)) (eventually_atTop.mpr ⟨4, fun n hn =>
      Nat.pow_le_pow_right (by norm_num) (by nlinarith)⟩)
    (setOf_mem_DTIME_of_computableInO computableInO_diagonal fun _ => le_rfl)⟩

/-- **Polynomial time is strictly within exponential time**, for problems on bit words: the
diagonal problem is in `EXP` and not in `P` [Arora and Barak, Theorem 3.1][AroraBarak09]. -/
theorem P_ssubset_EXP : P encBits ⊂ EXP encBits :=
  (Set.ssubset_iff_of_subset P_subset_EXP).mpr
    ⟨_, setOf_diagonal_mem_EXP, diagonal_notMem_P⟩

/-! ### Exponential padding -/

/-- **Padding to exponential length.** If `Ψ` is polynomial-time on pairs of a bit word and a
unary number, then the words `y` with `Ψ (y, 2 ^ |y|)` form a problem in `E`: writing the padding
`2 ^ |y|` and running `Ψ` takes time `C 2 ^ (D |y|) (|y| + 1) ^ D`
(`Turing.MultiTapeTM.ComputableInPolyTime.exists_computableInO_pad`), which is `2 ^ O(|y|)`. -/
theorem setOf_mem_E_of_computableInPolyTime_pad {Ψ : List Bool × ℕ → Bool}
    (hΨ : ComputableInPolyTime Ψ (encPair encBits encUnary) encBool) :
    {y : List Bool | Ψ (y, 2 ^ y.length) = true} ∈ E encBits := by
  -- write the padding `2 ^ |y|`, then run `Ψ`
  obtain ⟨C, D, h⟩ := hΨ.exists_computableInO_pad ComputableInPolyTime.length_bits
  -- the time bound is `2 ^ O(n)`, since `n + 1 ≤ 2 ^ n`
  refine mem_E_iff.2 ⟨2 * D, DTIME_mono_of_le_mul_add (C := C) (fun _ => le_rfl)
    (setOf_mem_DTIME_of_computableInO (t := fun n => C * 2 ^ (2 * D * n) + C) h fun y => ?_)⟩
  simp only [encBits_apply]
  calc C * 2 ^ (D * y.length) * (y.length + 1) ^ D
      ≤ C * 2 ^ (D * y.length) * (2 ^ y.length) ^ D := by
        gcongr
        exact Nat.lt_two_pow_self
    _ = C * 2 ^ (2 * D * y.length) := by ring
    _ ≤ _ := Nat.le_add_right _ _

/-- **`EXP` is closed under polynomial-time many-one reductions.** -/
theorem PolyTimeReducible.mem_EXP {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {A : Set α} {B : Set β} (hAB : PolyTimeReducible encA encB A B) (hB : B ∈ EXP encB) :
    A ∈ EXP encA := by
  obtain ⟨f, hf, hred⟩ := hAB
  obtain ⟨k, hk⟩ := mem_EXP_iff.mp hB
  obtain ⟨T, S, hT, -, hfO⟩ := hf.exists_computableInO
  -- one polynomial bounds both the time of `f` and the length of its output
  obtain ⟨c, d, hcd⟩ := (hT.add hf.polyBounded_length).exists_le
  have hpre : f ⁻¹' B ∈ DTIME encA
      (fun n => c * (n + 1) ^ d + 2 ^ (c * (n + 1) ^ d) ^ k) := by
    refine preimage_mem_DTIME (C := 1) hk hfO fun a => ?_
    have hca := hcd a
    have hpow : 2 ^ (encB (f a)).length ^ k ≤ 2 ^ (c * ((encA a).length + 1) ^ d) ^ k :=
      Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_left (by omega) k)
    omega
  have hA_eq : A = f ⁻¹' B := Set.ext hred
  rw [hA_eq]
  refine DTIME_two_pow_subset_EXP (h := fun n => c * (n + 1) ^ d + (c * (n + 1) ^ d) ^ k + 1)
    (by fun_prop) (DTIME_mono (fun n => ?_) hpre)
  set M := c * (n + 1) ^ d + (c * (n + 1) ^ d) ^ k
  have h1 : c * (n + 1) ^ d ≤ 2 ^ M :=
    (Nat.le_add_right _ _).trans (Nat.lt_two_pow_self.le)
  have h2 : 2 ^ (c * (n + 1) ^ d) ^ k ≤ 2 ^ M :=
    Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left _ _)
  calc
    c * (n + 1) ^ d + 2 ^ (c * (n + 1) ^ d) ^ k ≤ 2 ^ M + 2 ^ M := Nat.add_le_add h1 h2
    _ = 2 ^ (M + 1) := by rw [← two_mul, pow_succ']

end Cslib.Complexity
