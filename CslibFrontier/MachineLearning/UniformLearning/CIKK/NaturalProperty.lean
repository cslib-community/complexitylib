/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.NaturalProof.ConstDepth
public import CslibFrontier.MachineLearning.UniformLearning.CIKK.DenseTest
public import CslibFrontier.MachineLearning.UniformLearning.CIKK.PPoly
import CslibFrontier.Computability.Circuit.Boolean.ACC0.Basic
import CslibFrontier.MachineLearning.UniformLearning.CIKK.Complexity

/-!
# The CIKK learner from a natural property

PLACEHOLDER
-/

public section

namespace Cslib.MachineLearning.UniformLearning

open Filter Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.NaturalProof

/-! ### Closed forms -/

/-- With `X = n + s + 2 ^ e + 1`, the direct-product length is at most `2 ^ 16 (g + 1) X²`. -/
private theorem cikkK_le_mul_sq (e g n s : ℕ) :
    cikkK e g ≤ 2 ^ 16 * (g + 1) * (n + s + 2 ^ e + 1) ^ 2 := by
  have he : e < 2 ^ e := Nat.lt_two_pow_self
  have hk := cikkK_le e g
  generalize hX : n + s + 2 ^ e + 1 = X
  have h1 : (g + 1) * (2 ^ e + 1) ≤ (g + 1) * X := Nat.mul_le_mul_left _ (by omega)
  have h2 : 2 ^ e ≤ (g + 1) * 2 ^ e := Nat.le_mul_of_pos_left _ (Nat.succ_pos g)
  have hlin : 6 * g + 3 * e + 36 ≤ 45 * (g + 1) * X := by nlinarith
  calc cikkK e g ≤ 2 ^ (e + 10) * (6 * g + 3 * e + 36) := hk
    _ = 2 ^ 10 * 2 ^ e * (6 * g + 3 * e + 36) := by ring
    _ ≤ 2 ^ 10 * X * (45 * (g + 1) * X) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hlin
    _ = 45 * 2 ^ 10 * ((g + 1) * X ^ 2) := by ring
    _ ≤ 2 ^ 16 * ((g + 1) * X ^ 2) := Nat.mul_le_mul_right _ (by norm_num)
    _ = _ := by ring

/-- With `X = n + s + 2 ^ e + 1`, the size bound of the generator's circuits is at most
`2 ^ 36 (g + 1)² X⁶`. -/
private theorem cikkSize_le (e g n s : ℕ) :
    cikkK e g * s + 6 * (cikkK e g * n + cikkK e g) ^ 2 + 3 ≤
      2 ^ 36 * (g + 1) ^ 2 * (n + s + 2 ^ e + 1) ^ 6 := by
  have hk := cikkK_le_mul_sq e g n s
  have hs : s ≤ n + s + 2 ^ e + 1 :=
    (Nat.le_add_left s n).trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
  have hn : n + 1 ≤ n + s + 2 ^ e + 1 :=
    Nat.add_le_add_right ((Nat.le_add_right n s).trans (Nat.le_add_right _ _)) 1
  generalize cikkK e g = k at hk ⊢
  generalize n + s + 2 ^ e + 1 = X at hk hs hn ⊢
  have h1 : k * s ≤ (k * X) ^ 2 :=
    (Nat.mul_le_mul_left _ hs).trans (Nat.le_self_pow two_ne_zero _)
  have h2 : (k * n + k) ^ 2 ≤ (k * X) ^ 2 := by
    gcongr
    calc k * n + k = k * (n + 1) := by ring
      _ ≤ k * X := Nat.mul_le_mul_left _ hn
  have h3 : (k * X) ^ 2 ≤ 2 ^ 32 * ((g + 1) ^ 2 * X ^ 6) :=
    calc (k * X) ^ 2 ≤ (2 ^ 16 * (g + 1) * X ^ 2 * X) ^ 2 := by gcongr
      _ = _ := by ring
  have h4 : 0 < (g + 1) ^ 2 * X ^ 6 := Nat.mul_pos (by positivity) (pow_pos (by omega) 6)
  calc k * s + 6 * (k * n + k) ^ 2 + 3 ≤ 2 ^ 36 * ((g + 1) ^ 2 * X ^ 6) := by omega
    _ = _ := by ring

/-- **Closed form of `cikkPPolyBound`**: with `X = n + s + 2 ^ e + 1`,
`cikkPPolyBound n ℓ e g s ≤ (2 ^ 41 (ℓ + g + 1)² X⁶) ^ 8`. The constants are this library's. -/
theorem cikkPPolyBound_le (n ℓ e g s : ℕ) :
    cikkPPolyBound n ℓ e g s ≤ (2 ^ 41 * (ℓ + g + 1) ^ 2 * (n + s + 2 ^ e + 1) ^ 6) ^ 8 := by
  rw [cikkPPolyBound_def]
  have hS := cikkSize_le e g n s
  have hX1 : 1 ≤ n + s + 2 ^ e + 1 := Nat.le_add_left 1 _
  generalize cikkK e g * s + 6 * (cikkK e g * n + cikkK e g) ^ 2 + 3 = S at hS ⊢
  generalize n + s + 2 ^ e + 1 = X at hS hX1 ⊢
  have hS' : S ≤ 2 ^ 36 * ((ℓ + g + 1) ^ 2 * X ^ 6) :=
    calc S ≤ 2 ^ 36 * (g + 1) ^ 2 * X ^ 6 := hS
      _ ≤ 2 ^ 36 * (ℓ + g + 1) ^ 2 * X ^ 6 := by gcongr; omega
      _ = _ := by ring
  have hℓ : ℓ + 1 ≤ (ℓ + g + 1) ^ 2 * X ^ 6 :=
    calc ℓ + 1 ≤ ℓ + g + 1 := by omega
      _ ≤ (ℓ + g + 1) ^ 2 := Nat.le_self_pow two_ne_zero _
      _ ≤ _ := Nat.le_mul_of_pos_right _ (pow_pos (by omega) 6)
  calc (2100 * 8) ^ 2 * (ℓ + S + 1) ^ 8
      ≤ (2 ^ 4) ^ 8 * (2 ^ 37 * ((ℓ + g + 1) ^ 2 * X ^ 6)) ^ 8 :=
        Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_left (by omega) 8)
    _ = _ := by ring

/-- **Admissible lengths**: at the advantage exponent `g = (c + 1) ℓ + 1`, if
`n + s + 2 ^ e + 1 ≤ ℓ ^ j` and `(2 ^ 45 (c + 1)²) ^ 8 ≤ ℓ`, then
`cikkPPolyBound n ℓ e g s ≤ ℓ ^ (48 j + 17)`. -/
theorem cikkPPolyBound_le_pow {n ℓ e s c j : ℕ} (hX : n + s + 2 ^ e + 1 ≤ ℓ ^ j)
    (hℓ : (2 ^ 45 * (c + 1) ^ 2) ^ 8 ≤ ℓ) :
    cikkPPolyBound n ℓ e ((c + 1) * ℓ + 1) s ≤ ℓ ^ (48 * j + 17) := by
  have hℓ1 : 1 ≤ ℓ := le_trans (Nat.one_le_iff_ne_zero.2 (by positivity)) hℓ
  have hH : ℓ + ((c + 1) * ℓ + 1) + 1 ≤ 4 * (c + 1) * ℓ := by nlinarith
  calc cikkPPolyBound n ℓ e ((c + 1) * ℓ + 1) s
      ≤ (2 ^ 41 * (ℓ + ((c + 1) * ℓ + 1) + 1) ^ 2 * (n + s + 2 ^ e + 1) ^ 6) ^ 8 :=
        cikkPPolyBound_le n ℓ e _ s
    _ ≤ (2 ^ 41 * (4 * (c + 1) * ℓ) ^ 2 * (ℓ ^ j) ^ 6) ^ 8 := by gcongr
    _ = (2 ^ 45 * (c + 1) ^ 2) ^ 8 * ℓ ^ (48 * j + 16) := by ring
    _ ≤ ℓ * ℓ ^ (48 * j + 16) := Nat.mul_le_mul_right _ hℓ
    _ = ℓ ^ (48 * j + 17) := by ring

/-- At `g = (c + 1) ℓ + 1`, with `n + s + 2 ^ e + 1 ≤ ℓ ^ j` and `1 ≤ ℓ`, the generator's circuits
have at most `2 ^ 40 (c + 1)² ℓ ^ (6 j + 2)` gates. -/
private theorem cikkSize_le_pow {n ℓ e s c j : ℕ} (hX : n + s + 2 ^ e + 1 ≤ ℓ ^ j) (hℓ : 1 ≤ ℓ) :
    cikkK e ((c + 1) * ℓ + 1) * s +
        6 * (cikkK e ((c + 1) * ℓ + 1) * n + cikkK e ((c + 1) * ℓ + 1)) ^ 2 + 3 ≤
      2 ^ 40 * (c + 1) ^ 2 * ℓ ^ (6 * j + 2) := by
  have hG : (c + 1) * ℓ + 1 + 1 ≤ 4 * (c + 1) * ℓ := by nlinarith
  calc _ ≤ 2 ^ 36 * ((c + 1) * ℓ + 1 + 1) ^ 2 * (n + s + 2 ^ e + 1) ^ 6 := cikkSize_le _ _ _ _
    _ ≤ 2 ^ 36 * (4 * (c + 1) * ℓ) ^ 2 * (ℓ ^ j) ^ 6 := by gcongr
    _ = _ := by ring

/-- Density `2 ^ (-c ℓ)` is density `2 ^ (ℓ + 1 - g)` at `g = (c + 1) ℓ + 1`. -/
private theorem two_pow_two_pow_mul_le_of_le {ℓ c m : ℕ} (h : 2 ^ 2 ^ ℓ ≤ 2 ^ (c * ℓ) * m) :
    2 ^ 2 ^ ℓ * 2 ^ (ℓ + 1) ≤ 2 ^ ((c + 1) * ℓ + 1) * m :=
  calc 2 ^ 2 ^ ℓ * 2 ^ (ℓ + 1) ≤ 2 ^ (c * ℓ) * m * 2 ^ (ℓ + 1) := Nat.mul_le_mul_right _ h
    _ = 2 ^ ((c + 1) * ℓ + 1) * m := by ring

/-! ### Resources at `g = (c + 1) ℓ + 1` -/

/-- At `g = (c + 1) ℓ + 1`, the CIKK learner makes at most `(h + 1) 2 ^ ((10 c + 12) ℓ + 6 e + 69)`
queries. -/
theorem queriesAtMost_cikkLearner_mul_add_one (n ℓ e c h : ℕ) (test : BitString (2 ^ ℓ) → Bool) :
    (cikkLearner n ℓ e ((c + 1) * ℓ + 1) h test).QueriesAtMost
      ((h + 1) * 2 ^ ((10 * c + 12) * ℓ + 6 * e + 69)) := by
  have h := queriesAtMost_cikkLearner_two_pow n ℓ e ((c + 1) * ℓ + 1) h test
  rwa [show 2 * ℓ + 10 * ((c + 1) * ℓ + 1) + 6 * e + 59 = (10 * c + 12) * ℓ + 6 * e + 69 by ring]
    at h

/-- At `g = (c + 1) ℓ + 1`, if the test has a De Morgan circuit with at most `2 ^ (c' ℓ)` gates,
every hypothesis of the CIKK learner has one with at most `2 ^ ((11 c + c' + 14) ℓ + 9 e + 92)`
gates. -/
theorem complexity_eval_cikkLearner_mul_add_one_le {n ℓ e c c' h : ℕ}
    {test : BitString (2 ^ ℓ) → Bool}
    (htest : complexity interpretation (single test) ≤ 2 ^ (c' * ℓ)) (f : BooleanFunction n) (ω) :
    complexity interpretation (single ((cikkLearner n ℓ e ((c + 1) * ℓ + 1) h test ω).eval f)) ≤
      2 ^ ((11 * c + c' + 14) * ℓ + 9 * e + 92) := by
  have h1 : complexity interpretation (single test) + 1 ≤ 2 ^ (c' * ℓ + 1) := by
    have := Nat.one_le_two_pow (n := c' * ℓ)
    rw [pow_succ]
    omega
  calc _ ≤ 2 ^ (11 * ((c + 1) * ℓ + 1) + 9 * e + 3 * ℓ + 80) *
          (complexity interpretation (single test) + 1) :=
        complexity_eval_cikkLearner_le_two_pow n ℓ e _ h test f ω
    _ ≤ 2 ^ (11 * ((c + 1) * ℓ + 1) + 9 * e + 3 * ℓ + 80) * 2 ^ (c' * ℓ + 1) :=
        Nat.mul_le_mul_left _ h1
    _ = 2 ^ ((11 * c + c' + 14) * ℓ + 9 * e + 92) := by ring

/-! ### Learning from a natural property -/

/-- **Learning from a large property of high circuit complexity** -/
theorem learns_cikkLearner_of_large_of_pow_lt_complexity {D : ∀ ℓ, Set (BooleanFunction ℓ)}
    {c d ℓ₀ : ℕ} (hlarge : ∀ ℓ ≥ ℓ₀, 2 ^ 2 ^ ℓ ≤ 2 ^ (c * ℓ) * (D ℓ).ncard)
    (huse : ∀ ℓ ≥ ℓ₀, ∀ F ∈ D ℓ, ℓ ^ d < complexity interpretation (single F))
    {n s e h ℓ : ℕ} (hℓ : ℓ₀ ≤ ℓ) (hP : cikkPPolyBound n ℓ e ((c + 1) * ℓ + 1) s ≤ ℓ ^ d) :
    (cikkLearner n ℓ e ((c + 1) * ℓ + 1) h (truthTableTest (D ℓ))).Learns
      (cikkSeed n ℓ e ((c + 1) * ℓ + 1) h) {f | complexity interpretation (single f) ≤ s}
      (1 / 2 ^ e) (1 / 2 ^ h) :=
  learns_cikkLearner_of_lt_complexity s e _ h (two_pow_two_pow_mul_le_of_le (hlarge ℓ hℓ))
    fun F hF => hP.trans_lt (huse ℓ hℓ F hF)

/-- **Learning from a natural property useful against P/poly** -/
theorem exists_learns_cikkLearner_of_isNatural_of_isUseful_PPoly
    {R : ∀ n, Set (BooleanFunction n)} (hnat : IsNatural PPoly R) (huse : IsUseful PPoly R) :
    ∃ D : ∀ n, Set (BooleanFunction n), (∀ n, D n ⊆ R n) ∧ ∃ c c',
      (∀ ℓ, 1 ≤ ℓ → complexity interpretation (single (truthTableTest (D ℓ))) ≤ 2 ^ (c' * ℓ)) ∧
      ∀ j, ∃ ℓ₀, ∀ {n s e h ℓ : ℕ}, ℓ₀ ≤ ℓ → n + s + 2 ^ e + 1 ≤ ℓ ^ j →
        (cikkLearner n ℓ e ((c + 1) * ℓ + 1) h (truthTableTest (D ℓ))).Learns
          (cikkSeed n ℓ e ((c + 1) * ℓ + 1) h) {f | complexity interpretation (single f) ≤ s}
          (1 / 2 ^ e) (1 / 2 ^ h) := by
  obtain ⟨D, hDR, ⟨c, hc⟩, hDP⟩ := hnat
  obtain ⟨c', hc'⟩ := exists_complexity_truthTableTest_le hDP
  refine ⟨D, hDR, c, c', hc', fun j => ?_⟩
  obtain ⟨ℓ₁, hℓ₁⟩ := eventually_atTop.1 hc
  obtain ⟨ℓ₂, hℓ₂⟩ := eventually_atTop.1
    (isUseful_PPoly_iff.1 huse (fun ℓ => ℓ ^ (48 * j + 17)) (by fun_prop))
  refine ⟨max (max ℓ₁ ℓ₂) ((2 ^ 45 * (c + 1) ^ 2) ^ 8), fun {n s e h ℓ} hℓ hX => ?_⟩
  refine learns_cikkLearner_of_large_of_pow_lt_complexity (ℓ₀ := max ℓ₁ ℓ₂)
    (fun ℓ hℓ => hℓ₁ ℓ (le_of_max_le_left hℓ))
    (fun ℓ hℓ F hF => hℓ₂ ℓ (le_of_max_le_right hℓ) F (hDR ℓ hF)) (le_of_max_le_left hℓ)
    (cikkPPolyBound_le_pow hX (le_of_max_le_right hℓ))

variable {σ : Signature} {I : Interpretation σ Bool}

/-- **Learning from a large property useful against a constant-depth class** -/
theorem exists_learns_cikkLearner_of_isLarge_of_isUseful_constDepth
    (φ : Unbounded.extSignature.Hom σ) [φ.Preserves (Unbounded.extInterpretation (modGate 2)) I]
    {R : ∀ n, Set (BooleanFunction n)} (hlarge : IsLarge R) (huse : IsUseful (ConstDepth I) R)
    (hne : (ConstDepth I).Nonempty) :
    ∃ c, ∀ d j, ∃ ℓ₀, ∀ {n s e h ℓ : ℕ}, ℓ₀ ≤ ℓ → n + s + 2 ^ e + 1 ≤ ℓ ^ j →
      (cikkLearner n ℓ e ((c + 1) * ℓ + 1) h (truthTableTest (R ℓ))).Learns
        (cikkSeed n ℓ e ((c + 1) * ℓ + 1) h)
        {f | ∃ C : Circuit σ n 1, C.Computes I (single f) ∧ C.depth ≤ d ∧ C.size ≤ s}
        (1 / 2 ^ e) (1 / 2 ^ h) := by
  obtain ⟨c, hc⟩ := hlarge
  refine ⟨c, fun d j => ?_⟩
  obtain ⟨ℓ₁, hℓ₁⟩ := eventually_atTop.1 hc
  obtain ⟨ℓ₂, hℓ₂⟩ := eventually_atTop.1 (huse.eventually_constDepth hne (d + 7)
    (fun ℓ => 2 ^ 40 * (c + 1) ^ 2 * ℓ ^ (6 * j + 2)) (by fun_prop))
  refine ⟨max (max ℓ₁ ℓ₂) 1, fun {n s e h ℓ} hℓ hX => ?_⟩
  have hℓ1 : 1 ≤ ℓ := le_of_max_le_right hℓ
  have hℓ' : max ℓ₁ ℓ₂ ≤ ℓ := le_of_max_le_left hℓ
  exact learns_cikkLearner_of_hom φ d s e _ h
    (two_pow_two_pow_mul_le_of_le (hℓ₁ ℓ (le_of_max_le_left hℓ')))
    fun G hGd hGs F hF => hℓ₂ ℓ (le_of_max_le_right hℓ') G hGd
      (hGs.trans (cikkSize_le_pow hX hℓ1)) F hF

/-- **Learning AC⁰[2] from a large property useful against it** -/
theorem exists_learns_cikkLearner_of_isLarge_of_isUseful_AC0Mod_two
    {R : ∀ n, Set (BooleanFunction n)} (hlarge : IsLarge R) (huse : IsUseful (AC0Mod 2) R) :
    ∃ c, ∀ d j, ∃ ℓ₀, ∀ {n s e h ℓ : ℕ}, ℓ₀ ≤ ℓ → n + s + 2 ^ e + 1 ≤ ℓ ^ j →
      (cikkLearner n ℓ e ((c + 1) * ℓ + 1) h (truthTableTest (R ℓ))).Learns
        (cikkSeed n ℓ e ((c + 1) * ℓ + 1) h)
        {f | ∃ C : Circuit Unbounded.extSignature n 1,
          C.Computes (Unbounded.extInterpretation (modGate 2)) (single f) ∧ C.depth ≤ d ∧
            C.size ≤ s}
        (1 / 2 ^ e) (1 / 2 ^ h) :=
  exists_learns_cikkLearner_of_isLarge_of_isUseful_constDepth (Signature.Hom.id _) hlarge huse
    ⟨_, modGate_mem_AC0Mod 2⟩

end Cslib.MachineLearning.UniformLearning
