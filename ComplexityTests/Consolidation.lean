/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.Synthesis
import Complexity.Computability.Complexity.Classes.LogSpace
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import Complexity.Computability.Machines.Turing.MultiTape.Universal.PolyTime
import Complexity.Foundations.Control.Monad.IsMonadHom.StateT
import Complexity.Foundations.Data.BitString.Affine
import Complexity.Foundations.Data.BitString.Parity
import Complexity.Foundations.Data.Fin.Order
import Complexity.Foundations.Data.Finset.Average
import Complexity.Foundations.Data.List.Filter
import Complexity.Foundations.Data.List.OfFn
import Complexity.Foundations.Data.Nat.Asymptotics
import Complexity.Foundations.Data.Nat.Choose.Real
import Complexity.Foundations.Data.Nat.Div
import Complexity.Foundations.Data.Nat.Log
import Complexity.Foundations.Data.Nat.PolynomialBound.Log
import Complexity.Foundations.LinearAlgebra.CubeSum
import Complexity.Foundations.LinearAlgebra.Matrix.SchurComplement
import Complexity.Foundations.LinearAlgebra.Rank
import Complexity.Foundations.NumberTheory.PrimeCounting
import Mathlib.Tactic.FinCases

/-! General lemmas in their library homes: the costs of projections and the one-gate lower bound
for circuits on two and three inputs, the decoders of binary numbers and Booleans on encoded and
malformed words, the nondeterministic space predicate, the parity of a symmetric difference,
affine Boolean forms and step sums over `𝔽₂`, set difference via list filtering, block modular sums,
and logarithmic bounds, with their boundary cases. -/

namespace ComplexityTests.Consolidation

open Cslib Cslib.Complexity Turing Turing.MultiTapeTM

/-! ### Projections and the first gate -/

section Circuits

open Cslib.Circuits Cslib.Circuits.Boolean

example : complexity interpretation (single fun x : BitString 2 => x 1) = 0 :=
  complexity_single_proj 1

example : complexity interpretation (single fun x : BitString 3 => x 2) = 0 :=
  complexity_single_proj 2

/-- The conjunction of two inputs costs exactly one gate. -/
example : complexity interpretation (single fun x : BitString 2 => x 0 && x 1) = 1 := by
  refine le_antisymm ?_ (one_le_complexity_single fun i h => ?_)
  · have h := complexity_and_le (fun x : BitString 2 => x 0) fun x => x 1
    rw [complexity_single_proj, complexity_single_proj] at h
    exact h
  · fin_cases i
    · exact absurd (congrFun h ![true, false]) (by decide)
    · exact absurd (congrFun h ![false, true]) (by decide)

/-- The conjunction of three inputs needs at least one gate. -/
example : 1 ≤ complexity interpretation (single fun x : BitString 3 => x 0 && x 1 && x 2) :=
  one_le_complexity_single fun i h => by
    fin_cases i
    · exact absurd (congrFun h ![true, false, false]) (by decide)
    · exact absurd (congrFun h ![false, true, false]) (by decide)
    · exact absurd (congrFun h ![false, false, true]) (by decide)

/-- Negating the input costs at most one gate. -/
example : complexity interpretation (single fun x : BitString 1 => !x 0) ≤ 1 := by
  have h := complexity_not_le (fun x : BitString 1 => x 0)
  rwa [complexity_single_proj] at h

end Circuits

/-! ### Decoders of binary numbers and Booleans -/

/-- Binary digits are read least significant first: `[true, false, true]` is `5`. -/
example : Decoder.nat.decode [true, false, true] = 5 := rfl

example : Decoder.nat.decode (encNat 6) = 6 := Decoder.nat.decode_enc 6

/-- Malformed words: trailing `false`s are ignored, and the empty word is `0`. -/
example : Decoder.nat.decode [true, false, false] = 1 := rfl

example : Decoder.nat.decode [] = 0 := rfl

example : (ofBits [false, true, false]).bits = [false, true] := by
  rw [bits_ofBits]
  decide

example : Decoder.bool.decode (encBool true) = true := Decoder.bool.decode_enc true

/-- The empty word, which encodes no Boolean, decodes to `false`. -/
example : Decoder.bool.decode [] = false := rfl

/-! ### The nondeterministic space predicate -/

/-- `NPSPACE` is stated with `DecidesInSpace`. -/
example {A : Set (List Bool)} :
    A ∈ NPSPACE encBits ↔ ∃ (k : ℕ) (State : Type) (_ : Finite State)
      (ntm : MultiTapeNTM k Bool State) (s : List Bool → ℕ),
        PolyBounded (fun a => (encBits a).length) s ∧ ntm.DecidesInSpace encBits A s :=
  Iff.rfl

/-! ### Parities of symmetric differences -/

example : ∀ x : Fin 3 → Bool,
    parityOn (symmDiff ({0, 1} : Finset (Fin 3)) {1, 2}) x =
      (parityOn {0, 1} x ^^ parityOn {1, 2} x) := by
  decide

/-- The symmetric difference of a set with itself is empty, of parity `false`. -/
example (s : Finset (Fin 4)) (x : Fin 4 → Bool) : (parityOn s x ^^ parityOn s x) = false := by
  rw [← parityOn_symmDiff, symmDiff_self, Finset.bot_eq_empty, parityOn_empty]

/-! ### Logarithmic bounds -/

example (c : ℕ) :
    2 ^ (Nat.log2 5 + 1) ≤ 2 * (5 + 1) ∧
    2 ^ (Nat.log2 0 + 1) = 2 * (0 + 1) ∧
    PolynomiallyBounded (fun n => c * (Nat.log2 n + 1)) ∧
    PolyBounded (fun w : List Bool => w.length) (fun w => c * (Nat.log2 w.length + 1)) :=
  ⟨Nat.two_pow_log2_succ_le 5, by decide,
   polynomiallyBounded_mul_log2_add_one c,
   polyBounded_log _ c⟩

/-- Adding one increases `⌊log_b n⌋` by at most one, and equality holds at `n = b ^ k - 1`. -/
example : Nat.log 2 (7 + 1) ≤ Nat.log 2 7 + 1 ∧ Nat.log 2 (7 + 1) = Nat.log 2 7 + 1 :=
  ⟨Nat.log_add_one_le 2 7, by decide⟩

/-- `Nat.log_add_one_le` also holds for degenerate bases `b ≤ 1` and at `n = 0`. -/
example : Nat.log 0 (5 + 1) ≤ Nat.log 0 5 + 1 ∧ Nat.log 2 (0 + 1) ≤ Nat.log 2 0 + 1 :=
  ⟨Nat.log_add_one_le 0 5, Nat.log_add_one_le 2 0⟩

/-- `m * ⌊log_b n⌋ ≤ n + m * m` holds in both regimes (`⌊log_b n⌋ ≤ m` and `m < ⌊log_b n⌋`). -/
example : 3 * Nat.log 2 5 ≤ 5 + 3 * 3 ∧ 2 * Nat.log 2 16 ≤ 16 + 2 * 2 :=
  ⟨Nat.mul_log_le_add_sq Nat.one_lt_two 3 5, Nat.mul_log_le_add_sq Nat.one_lt_two 2 16⟩

/-! ### Affine forms, list filtering and block modular sums -/

/-- A function of bits depending only on `{0, 2}` and preserving sums of three points is affine. -/
example : ∃ T ⊆ ({0, 2} : Finset ℕ), ∀ u : ℕ → Bool,
    (true + u 0 + u 2) = (true + (0 : ℕ → Bool) 0 + (0 : ℕ → Bool) 2) + ∑ j ∈ T, u j :=
  BitString.exists_affine_of_add_add (M := {0, 2}) (g := fun u => true + u 0 + u 2)
    (fun u u' h => by simp [h 0 (by simp), h 2 (by simp)])
    (fun u u' u'' => by
      simp only [Pi.add_apply]
      cases u 0 <;> cases u' 0 <;> cases u'' 0 <;>
        cases u 2 <;> cases u' 2 <;> cases u'' 2 <;> rfl)

/-- Prefix parity accumulation from a step recurrence. -/
example (f : ℕ → Bool) :
    let z : ℕ → Bool := fun j => true + ∑ j' ∈ Finset.range j, f j'
    ∀ j ≤ 3, z j = true + ∑ j' ∈ Finset.range j, f j' :=
  BitString.eq_add_sum_of_step (z := fun j => true + ∑ j' ∈ Finset.range j, f j')
    (by simp)
    (fun j _ => by simp [Finset.sum_range_succ, ← add_assoc]; rfl)

/-- Filtering a list by non-membership in `H` takes the `Finset` difference. -/
example :
    (([1, 2, 2, 3].filter fun l => !([2, 4].any (· == l))).toFinset : Finset ℕ) =
      ([1, 2, 2, 3].toFinset \ [2, 4].toFinset) :=
  List.toFinset_filter_not_mem [1, 2, 2, 3] [2, 4]

/-- Summing over `n` blocks of length `ℓ` at offset `i < ℓ`. -/
example (F : ℕ → ℕ) :
    ∑ q ∈ Finset.range (3 * 4), (if q % 4 = 2 then F q else 0) =
      ∑ k ∈ Finset.range 3, F (k * 4 + 2) :=
  Nat.sum_range_mul_ite_mod 3 (by decide : 2 < 4) F

/-! ### Asymptotics, StateT folds, Boolean-cube product expansion and matrix scalar cancellation -/

/-- `(n + 1) ^ k * n` is eventually below `2 ^ n`. -/
example : ∀ᶠ n : ℕ in Filter.atTop, (n + 1) ^ 3 * n < 2 ^ n :=
  Nat.eventually_add_one_pow_mul_lt_pow 3 Nat.one_lt_two

/-- A real polynomial is eventually below an exponential with base `r > 1`. -/
example : ∃ α : ℕ, 1 ≤ α ∧ (5 : ℝ) * (α : ℝ) ^ 3 ≤ (3 / 2 : ℝ) ^ α :=
  Real.exists_one_le_and_mul_pow_le_pow 5 3 (by norm_num)

/-- Running a `foldlM` in `StateT σ (Except ε)` chains results via `Except.bind`. -/
example (g : ℕ → Bool → StateT ℕ (Except Unit) ℕ) :
    (([true, false].foldlM g 0).run 1) =
      [true, false].foldl (fun acc c => acc.bind fun p => (g p.1 c).run p.2) (.ok (0, 1)) :=
  StateT.foldlM_run_except g [true, false] 0 1

/-- Boolean-cube expansion of a product of differences over `ℤ`. -/
example (f g : Fin 2 → ℤ) :
    (∏ i, (f i - g i)) = ∑ w : Fin 2 → Bool,
      (-1 : ℤ) ^ (List.ofFn w).countP id * ∏ i, if w i then g i else f i :=
  Cslib.prod_sub_eq_sum f g

/-- The sum of all values in `Fin 4` is at most `4 * 4`. -/
example : (∑ j : Fin 4, j.val) ≤ 4 * 4 ∧ (∑ j : Fin 4, j.val) = 6 :=
  ⟨Fin.sum_val_le_mul_self 4, by decide⟩

/-- Rescaling two matrices over `ℚ` by the same nonzero scalar cancels in `(c • A)⁻¹ * (c • B)`. -/
example (B : Matrix (Fin 2) (Fin 2) ℚ) :
    ((3 : ℚ) • (1 : Matrix (Fin 2) (Fin 2) ℚ))⁻¹ * ((3 : ℚ) • B) =
      (1 : Matrix (Fin 2) (Fin 2) ℚ)⁻¹ * B :=
  Matrix.inv_smul_mul_smul_of_ne_zero 1 B (by simp) (by norm_num)

/-! ### `Nat.lcmUpto` bounds, monotone-key collisions, `Fin` subfamilies, range tail sums,
and vertex-choice bounds -/

/-- `lcm(1, …, m + n)` divides `lcm(1, …, m) * C(m + n, m)` and `2 * lcm(1, …, n) ≤ 4 ^ n`. -/
example :
    Nat.lcmUpto (4 + 2) ∣ Nat.lcmUpto 4 * (4 + 2).choose 4 ∧
      2 * Nat.lcmUpto 6 ≤ 4 ^ 6 ∧ Nat.lcmUpto 6 < 4 ^ 6 :=
  ⟨Nat.lcmUpto_add_dvd (by decide),
   Nat.two_mul_lcmUpto_le_four_pow 6 (by decide),
   Nat.lcmUpto_lt_four_pow 6 (by decide)⟩

/-- Distinct entries with equal keys in a monotone-key array force an adjacent collision. -/
example :
    let records : Fin 3 → ℕ × ℕ := ![(1, 0), (1, 1), (2, 0)]
    ∃ (p : ℕ) (hp : p + 1 < 3),
      records ⟨p, by omega⟩ ≠ records ⟨p + 1, hp⟩ ∧
      (records ⟨p, by omega⟩).1 = (records ⟨p + 1, hp⟩).1 ∧
      (records ⟨p, by omega⟩).1 = (records 0).1 :=
  Fin.exists_adjacent_ne_of_monotone_comp ![(1, 0), (1, 1), (2, 0)] Prod.fst
    (fun i j hij => by fin_cases i <;> fin_cases j <;> revert hij <;> decide)
    0 1 (by decide) (by decide) rfl

/-- Any `Fin`-indexed family over `ℚ` has a `Fin`-indexed linearly independent spanning
subfamily. -/
example (v : Fin 3 → Fin 2 → ℚ) :
    ∃ (k : ℕ) (a : Fin k → Fin 3), Function.Injective a ∧
      Submodule.span ℚ (Set.range (v ∘ a)) = Submodule.span ℚ (Set.range v) ∧
      LinearIndependent ℚ (v ∘ a) :=
  Submodule.exists_linearIndependent_fin_comp ℚ v

/-- Summing a tail of `List.range 4` after index `1 : Fin 4` matches the sum over `Finset.Ioi 1`. -/
example (f : ℕ → ℤ) :
    (((List.range 4).drop ((1 : Fin 4).val + 1)).map f).sum =
      ∑ k ∈ Finset.Ioi (1 : Fin 4), f k.val :=
  List.sum_map_drop_range_fin (1 : Fin 4) f

/-- Deterministic vertex-wise maximum choice beats any sub-probability weighting. -/
example :
    ∃ f : Fin 2 → Bool,
      (∑ _i : Fin 2, ∑ a : Bool, (1 / 2 : ℚ) * (if a = true then 1 else 0)) ≤
        ∑ i : Fin 2, (if f i = true then (1 : ℚ) else 0) :=
  Finset.exists_choice_sum_le id (fun _ a => if a = true then (1 : ℚ) else 0)
    (fun _ a => by cases a <;> norm_num) (fun _ _ => (1 / 2 : ℚ))
    (fun _ _ => by norm_num) (fun _ => by norm_num)

/-- Counting elements satisfying `p` is bounded by the sum of `f` when `1 ≤ f x` on matches. -/
example :
    ([1, 0, 3, 2].countP (· > 0)) ≤ (([1, 0, 3, 2].map id).sum) :=
  List.countP_le_sum_map fun x hx hp => by
    simp only [decide_eq_true_eq] at hp
    exact hp

end ComplexityTests.Consolidation
