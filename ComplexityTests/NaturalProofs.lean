/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.NaturalProof.Generator
import Cslib.Crypto.Primitives.PRG.Basic

/-! Truth-table languages on concrete words, a `P/poly`-natural property, a large property useful
against `P/poly`, circuit tests, the Razborov–Rudich distinguisher on the property of hard
functions at every input length from `16` on, the GGM family on fixed-width labels for a toy
generator with its circuits and security theorem, and the identity and constant families as
witnesses that exponential security is consistent and has content. -/

namespace ComplexityTests.NaturalProofs

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.NaturalProof Cslib.Crypto
  Cslib.Crypto.PRG Cslib.MCSP Filter Finset
open scoped NNReal

/-! ### Truth-table languages -/

/-- A word of length `2 ^ n` is in the truth-table language of `C` exactly when the function it
tabulates is in `C n`; a word whose length is not a power of two is in no truth-table language; and
the empty property has an empty truth-table language. -/
example :
    (List.ofFn (0 : BitString (2 ^ 1)) ∈ truthTableLanguage
      (fun n => (Set.univ : Set (BooleanFunction n))) ↔
      (truthTable 1).symm 0 ∈ (Set.univ : Set (BooleanFunction 1))) ∧
    [true, false, true] ∉ truthTableLanguage (fun n => (Set.univ : Set (BooleanFunction n))) ∧
    [true] ∉ truthTableLanguage (fun n => (∅ : Set (BooleanFunction n))) := by
  refine ⟨ofFn_mem_truthTableLanguage, ?_, fun ⟨_, _, h⟩ => h⟩
  rintro ⟨m, h, -⟩
  rcases m with _ | _ | m
  · simp at h
  · simp at h
  · have : 4 ≤ 2 ^ (m + 2) := by
      rw [pow_add]
      exact Nat.le_mul_of_pos_left 4 (Nat.two_pow_pos m)
    simp only [List.length_cons, List.length_nil] at h
    omega

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

/-- The hard functions are large and useful against `P/poly` (and against `∅`), so they eventually
require more than `n ^ 3` gates; by `truthTableLanguage_setOf_lt_complexity_notMem_PPoly` the
property is not `P/poly`-constructive if an exponentially secure family exists. -/
example :
    IsLarge (fun n => {f : BooleanFunction n |
      2 ^ n / (5 * n) < complexity interpretation (single f)}) ∧
    IsUseful PPoly (fun n => {f : BooleanFunction n |
      2 ^ n / (5 * n) < complexity interpretation (single f)}) ∧
    IsUseful ∅ (fun n => {f : BooleanFunction n |
      2 ^ n / (5 * n) < complexity interpretation (single f)}) ∧
    (∀ᶠ n in atTop, ∀ f ∈ {f : BooleanFunction n |
      2 ^ n / (5 * n) < complexity interpretation (single f)},
      n ^ 3 < complexity interpretation (single f)) :=
  ⟨isLarge_setOf_lt_complexity, isUseful_PPoly_setOf_lt_complexity, fun _ h => h.elim,
    isUseful_PPoly_iff.1 isUseful_PPoly_setOf_lt_complexity _ (by fun_prop)⟩

/-! ### Circuit tests -/

/-- A constant test is computed with one gate, and circuit tests with more gates include those with
fewer. -/
example :
    IsCircuitTest (m := 4) 1 (fun _ => PMF.pure true) ∧
    IsCircuitTest (m := 4) 2 (fun _ => PMF.pure true) := by
  have h1 : IsCircuitTest (m := 4) 1 (fun _ => PMF.pure true) :=
    ⟨fun _ => true, (Synthesis.const true).complexity_le, rfl⟩
  exact ⟨h1, let ⟨test, htest, hA⟩ := h1; ⟨test, htest.trans (by decide), hA⟩⟩

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

/-- Evaluation of `GGM.booleanFamily toy`, the fixed-width/list bridge `GGM.ofFn_evalBits`, and the
circuit-size bound on `GGM.booleanFamily toy`. -/
example :
    GGM.booleanFamily toy 3 (fun _ => false) (fun i => decide ((i : ℕ) ≠ 1)) = false ∧
    GGM.booleanFamily toy 3 (fun _ => true) (fun i => decide ((i : ℕ) = 1)) = false ∧
    GGM.booleanFamily toy 2 (fun _ => true) (fun _ => false) = true ∧
    List.ofFn (GGM.evalBits toy (fun _ => true) (fun i : Fin 2 => decide ((i : ℕ) = 0))) =
      GGM.eval (GGM.listGenerator toy) [true] [true, false] ∧
    GGM.eval (GGM.listGenerator toy) [true] [true, false] = [false] ∧
    complexity interpretation (single (GGM.booleanFamily toy 3 (fun _ => true))) ≤
      3 * (complexity interpretation ⇑toy + 4) + 2 :=
  ⟨by decide, by decide, by decide, GGM.ofFn_evalBits toy _ _, by decide,
    by simpa using GGM.complexity_booleanFamily_le toy 3 (fun _ => true)⟩

/-! ### The security theorem

Every generator is secure with error `1`, so the hypothesis of the security theorem can be met; the
conclusion then bounds the advantage by `2 ^ n - 1`. -/

example :
    (truthTableGenerator (GGM.booleanFamily toy 3)).Secure (IsCircuitTest 10) ((2 ^ 3 - 1) * 1) ∧
    toy.Secure (IsCircuitTest (2 ^ 0)) (2 ^ 0)⁻¹ :=
  ⟨GGM.secure_truthTableGenerator_booleanFamily (toy.secure_one _),
    by simpa using toy.secure_one _⟩

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
