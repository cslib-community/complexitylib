/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.NaturalProof.Generator
import Cslib.Crypto.Primitives.PRG.Basic


import Diag1155.Measure
/-! Truth-table languages on concrete words, a `P/poly`-natural property, a large property useful
against `P/poly`, circuit tests, the Razborov–Rudich distinguisher on the property of hard
functions at every input length from `16` on, the GGM family on fixed-width labels for a toy
generator with its circuits and security theorem, and the identity and constant families as
witnesses that exponential security is consistent and has content. -/


diag1155_install
namespace ComplexityTests.NaturalProofs

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.NaturalProof Cslib.Crypto
  Cslib.Crypto.PRG Cslib.MCSP Filter Finset
open scoped NNReal

/-! ### Truth-table languages -/

/-- A word of length `2 ^ n` is in the truth-table language of `C` exactly when the function it
tabulates is in `C n`. -/
example (C : ∀ n, Set (BooleanFunction n)) (T : BitString (2 ^ 1)) :
    List.ofFn T ∈ truthTableLanguage C ↔ (truthTable 1).symm T ∈ C 1 :=
  ofFn_mem_truthTableLanguage

/-- A word whose length is not a power of two is in no truth-table language. -/
example (C : ∀ n, Set (BooleanFunction n)) : [true, false, true] ∉ truthTableLanguage C := by
  rintro ⟨m, h, -⟩
  rcases m with _ | _ | m
  · simp at h
  · simp at h
  · have : 4 ≤ 2 ^ (m + 2) := by
      rw [pow_add]
      exact Nat.le_mul_of_pos_left 4 (Nat.two_pow_pos m)
    simp only [List.length_cons, List.length_nil] at h
    omega

/-- The empty property has an empty truth-table language. -/
example (w : List Bool) : w ∉ truthTableLanguage fun n => (∅ : Set (BooleanFunction n)) :=
  fun ⟨_, _, h⟩ => h

/-! ### A `P/poly`-natural property -/

/-- The words of length a power of two form a language in `P/poly`: each slice is constant. -/
theorem truthTableLanguage_univ_mem_PPoly :
    truthTableLanguage (fun n => (Set.univ : Set (BooleanFunction n))) ∈ PPoly := by
  classical
  refine PPoly.of_slice_const (fun N => decide (∃ n, N = 2 ^ n)) fun N x => ?_
  rw [Bool.eq_iff_iff, Language.slice_eq_true_iff, decide_eq_true_iff]
  constructor
  · rintro ⟨n, h, -⟩
    exact ⟨n, by simpa only [List.length_ofFn] using h⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n, List.length_ofFn, Set.mem_univ _⟩

/-- The property satisfied by every function is large. -/
theorem isLarge_univ : IsLarge fun n => (Set.univ : Set (BooleanFunction n)) :=
  ⟨0, Eventually.of_forall fun n => by
    simp [Set.ncard_univ, Nat.card_eq_fintype_card]⟩

/-- So the hypotheses of `IsNatural PPoly` can be met. -/
example : IsNatural PPoly fun n => (Set.univ : Set (BooleanFunction n)) :=
  ⟨_, fun _ => le_rfl, isLarge_univ, truthTableLanguage_univ_mem_PPoly⟩

/-! ### A large property useful against `P/poly` -/

/-- The hard functions are large and useful against `P/poly`, so both hypotheses can be met at
once; by `truthTableLanguage_setOf_lt_complexity_notMem_PPoly` the property is not
`P/poly`-constructive if an exponentially secure family exists. -/
example : IsLarge (fun n => {f : BooleanFunction n |
      2 ^ n / (5 * n) < complexity interpretation (single f)}) ∧
    IsUseful PPoly fun n => {f : BooleanFunction n |
      2 ^ n / (5 * n) < complexity interpretation (single f)} :=
  ⟨isLarge_setOf_lt_complexity, isUseful_PPoly_setOf_lt_complexity⟩

/-- Every property is useful against the empty class. -/
example (C : ∀ n, Set (BooleanFunction n)) : IsUseful ∅ C := fun _ h => h.elim

/-- A property useful against `P/poly` eventually holds only for functions needing more than
`n ^ 3` gates. -/
example (C : ∀ n, Set (BooleanFunction n)) (hC : IsUseful PPoly C) :
    ∀ᶠ n in atTop, ∀ f ∈ C n, n ^ 3 < complexity interpretation (single f) :=
  isUseful_PPoly_iff.1 hC _ (by fun_prop)

/-! ### Circuit tests -/

/-- A constant test is computed with one gate. -/
example (m : ℕ) (b : Bool) : IsCircuitTest (m := m) 1 fun _ => PMF.pure b :=
  ⟨fun _ => b, (Synthesis.const b).complexity_le, rfl⟩

/-- Circuit tests with more gates include those with fewer. -/
example {m t t' : ℕ} (h : t ≤ t') {A : Crypto.PRG.Adversary (BitString m)}
    (hA : IsCircuitTest t A) : IsCircuitTest t' A :=
  let ⟨test, htest, hA⟩ := hA
  ⟨test, htest.trans h, hA⟩

/-! ### The distinguisher on hard functions -/

section Hard

variable {n : ℕ} {Key : Type} [Fintype Key] [Nonempty Key]

/-- The functions that need more than `2 ^ n / (5 n)` gates. -/
abbrev hard (n : ℕ) : Set (BooleanFunction n) :=
  {f | 2 ^ n / (5 * n) < complexity interpretation (single f)}

/-- The test for hard functions rejects every member of a family of functions with at most
`2 ^ n / (5 n)` gates, so its advantage is the density of the hard functions. -/
example (F : Key → BooleanFunction n)
    (hF : ∀ key, complexity interpretation (single (F key)) ≤ 2 ^ n / (5 * n)) :
    (truthTableGenerator F).advantage (fun T => PMF.pure (truthTableTest (hard n) T)) =
      (hard n).ncard / 2 ^ 2 ^ n :=
  advantage_truthTableGenerator_truthTableTest F fun key hkey => (not_lt.2 (hF key)) hkey

/-- For `n ≥ 16`, no family of functions with at most `2 ^ n / (5 n)` gates is pseudorandom with
error `1 / 4` against circuits as large as the test for hard functions. -/
example (hn : 16 ≤ n) (F : Key → BooleanFunction n)
    (hF : ∀ key, complexity interpretation (single (F key)) ≤ 2 ^ n / (5 * n)) :
    ¬ (truthTableGenerator F).Secure
      (IsCircuitTest (complexity interpretation (single (truthTableTest (hard n))))) (1 / 4) := by
  refine not_secure_truthTableGenerator le_rfl (fun _ hf => hf) hF ?_
  have h := two_pow_two_pow_le_two_mul_ncard_setOf_lt_complexity hn
  have hpos : (0 : ℝ) < 2 ^ 2 ^ n := by positivity
  have h' : (2 : ℝ) ^ 2 ^ n ≤ 2 * (hard n).ncard := by exact_mod_cast h
  have hε : ((1 / 4 : ℝ≥0) : ℝ) = 1 / 4 := by norm_num
  rw [lt_div_iff₀ hpos, hε]
  linarith

end Hard

/-! ### A toy generator

The generator `s ↦ s ++ !s` on one bit, which is not pseudorandom: its children are the seed and
its complement, so the GGM function with key `s` is `s` plus the parity of the input. -/

/-- The one-bit generator `s ↦ (s, !s)`. -/
def toy : PRG.Generator (BitString 1) (BitString (2 * 1)) :=
  ⟨fun s i => if (i : ℕ) = 0 then s 0 else !s 0⟩

example : GGM.booleanFamily toy 3 (fun _ => false) (fun i => decide ((i : ℕ) ≠ 1)) = false := by
  decide

example : GGM.booleanFamily toy 3 (fun _ => true) (fun i => decide ((i : ℕ) = 1)) = false := by
  decide

example : GGM.booleanFamily toy 2 (fun _ => true) (fun _ => false) = true := by
  decide

/-- The fixed-width evaluation is the list construction with the generator read on lists. -/
example : List.ofFn (GGM.evalBits toy (fun _ => true) (fun i : Fin 2 => decide ((i : ℕ) = 0))) =
    GGM.eval (GGM.listGenerator toy) [true] [true, false] :=
  GGM.ofFn_evalBits toy _ _

example : GGM.eval (GGM.listGenerator toy) [true] [true, false] = [false] := by
  decide

/-- The members of the toy family on `n` inputs have circuits with `n (C + 4) + 2` gates. -/
example (n : ℕ) (seed : BitString 1) :
    complexity interpretation (single (GGM.booleanFamily toy n seed)) ≤
      n * (complexity interpretation ⇑toy + 4) + 2 := by
  simpa using GGM.complexity_booleanFamily_le toy n seed

/-! ### The security theorem

Every generator is secure with error `1`, so the hypothesis of the security theorem can be met; the
conclusion then bounds the advantage by `2 ^ n - 1`. -/

example (n t : ℕ) :
    (truthTableGenerator (GGM.booleanFamily toy n)).Secure (IsCircuitTest t) ((2 ^ n - 1) * 1) :=
  GGM.secure_truthTableGenerator_booleanFamily (toy.secure_one _)

/-- Subexponential security constrains only `m ≥ 1`: at `m = 0` it asks for error `1`. -/
example (G : ∀ k, PRG.Generator (BitString k) (BitString (2 * k))) (k : ℕ) :
    (G k).Secure (IsCircuitTest (2 ^ 0)) (2 ^ 0)⁻¹ := by
  simpa using (G k).secure_one _

/-- Security against circuits of size `2 ^ (k ^ ε)` with `ε = 1 / 2` gives subexponential security
with `d = 2`. -/
example (G : ∀ k, PRG.Generator (BitString k) (BitString (2 * k)))
    (hG : ∀ᶠ k in atTop, (G k).Secure (IsCircuitTest ⌊(2 : ℝ) ^ ((k : ℝ) ^ (1 / 2 : ℝ))⌋₊)
      ((2 : ℝ≥0) ^ ((k : ℝ) ^ (1 / 2 : ℝ)))⁻¹) :
    PRG.IsSubexponentiallySecure G 2 :=
  PRG.IsSubexponentiallySecure.of_rpow (by norm_num) hG

/-! ### Exponential security is consistent and has content

The identity family, keyed by the functions themselves, has uniformly random truth tables and so
is exponentially secure; its members are not of polynomial size, so it does not contradict
`not_isUseful_PPoly_of_isNatural`. A constant family is not exponentially secure: a test reading
one bit of the truth table has advantage `1 / 2`. -/

/-- The identity family is exponentially secure. -/
example : IsExponentiallySecure fun n (f : BooleanFunction n) => f := by
  refine fun c => Eventually.of_forall fun n => ?_
  refine ((truthTableGenerator fun f : BooleanFunction n => f).secure_zero_of_outputDist_eq ?_
    _).mono bot_le
  exact Probability.PMF.uniformOfFintype_map_equiv (truthTable n)

/-- A test reading one bit accepts half of all truth tables. -/
theorem toReal_idealExperiment_apply_zero (n : ℕ) :
    (PRG.Generator.idealExperiment (fun T : BitString (2 ^ n) => PMF.pure (T 0)) true).toReal =
      1 / 2 := by
  obtain ⟨N, hN⟩ : ∃ N, 2 ^ n = N + 1 := ⟨2 ^ n - 1, (Nat.succ_pred_eq_of_pos (by positivity)).symm⟩
  rw [PRG.Generator.toReal_idealExperiment_pure, dens, ← Fintype.piFinset_univ,
    Fintype.card_filter_piFinset_const_eq_of_mem _ _ (mem_univ true)]
  simp only [card_univ, Fintype.card_bool, Fintype.card_fin, Fintype.card_pi, prod_const]
  rw [hN, Nat.add_sub_cancel, pow_succ]
  push_cast
  field_simp

/-- A constant family is not exponentially secure. -/
example : ¬ IsExponentiallySecure fun n (_ : Unit) => fun _ : BitString n => false := by
  intro h
  obtain ⟨n, hsec, hn⟩ := ((h 1).and (eventually_ge_atTop 2)).exists
  have htest : IsCircuitTest (2 ^ (1 * n)) fun T : BitString (2 ^ n) => PMF.pure (T 0) := by
    refine ⟨fun T => T 0, ?_, rfl⟩
    have h0 : (single fun T : BitString (2 ^ n) => T 0) = fun T => T ∘ fun _ : Fin 1 => 0 := rfl
    rw [h0, complexity_wiring]
    exact Nat.zero_le _
  have hadv := hsec _ htest
  rw [PRG.Generator.advantage, toReal_idealExperiment_apply_zero,
    PRG.Generator.toReal_realExperiment_pure] at hadv
  have hfalse : ({u : Unit | (truthTableGenerator fun _ (x : BitString n) => false) u 0 = true} :
      Finset Unit) = ∅ := by
    ext u
    simp
  rw [hfalse, dens_empty, NNRat.cast_zero, zero_sub, abs_neg, abs_of_pos (by norm_num)] at hadv
  have hsmall : (((2 ^ (1 * n))⁻¹ : ℝ≥0) : ℝ) ≤ 1 / 4 := by
    rw [one_mul, NNReal.coe_inv, NNReal.coe_pow, NNReal.coe_ofNat, one_div]
    exact inv_anti₀ (by norm_num) (by
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := pow_le_pow_right₀ one_le_two (by omega))
  linarith

/-! ### The barrier corollaries -/

/-- Under subexponentially secure generators of polynomial circuit complexity, the property of
needing more than `2 ^ n / (5 n)` gates is not `P/poly`-natural. -/
example {G : ∀ k, PRG.Generator (BitString k) (BitString (2 * k))} {d : ℕ}
    (hsize : PolynomiallyBounded fun k => complexity interpretation ⇑(G k))
    (hG : PRG.IsSubexponentiallySecure G d) :
    ¬ IsNatural PPoly fun n => {f : BooleanFunction n |
      2 ^ n / (5 * n) < complexity interpretation (single f)} := fun hC =>
  not_isUseful_PPoly_of_isNatural_of_generator hsize hG hC isUseful_PPoly_setOf_lt_complexity

end ComplexityTests.NaturalProofs
