/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.OracleFormula
public import CslibFrontier.Computability.MCSP.FormulaMagnification

/-!
# Locality of the Oliveira–Santhanam formula construction

Chen, Hirahara, Oliveira, Pich, Rajgopal and Santhanam observe that the known hardness magnification
reductions are *local*: they compute the hard problem with few oracle gates of small fan-in on
cheap projections of the input [ChenHiraharaOliveiraPichRajgopalSanthanam2020, Appendix A.2,
Proposition 63, p. 52]. This file proves their \[OS18\] bullet for the library's
Oliveira–Santhanam formula construction (`FormulaMagnification.lean`): the approximate MCSP
promise problem is in `[N, poly(s / δ), 1]–Formula[N · poly(s / δ)]`.

The oracle is `succinctMCSPOracle`, the encoded `SuccinctMCSP` yes-instances. It is one language
for all input lengths, as Definition 11 requires. On `N = 2 ^ n` input bits the formula is a
conjunction of `2 ^ n` oracle gates. Each gate reads a word of constants and single input
leaves: the encoding of a `SuccinctMCSP` instance that samples the truth table at a fixed set of
seed points (`exists_seeds_approxMCSP`). No oracle gate lies below another, so the adaptivity is
one.

The paper's bound on oracle gates is exactly `N`. The library's De Morgan form
`exists_formula_separating_approxMCSP_of_agrees` still states `(2 ^ n + 1) * B`; both are derived
from the same seed lemma, which supplies `2 ^ n` seeds.

## Main definitions

* `Cslib.Circuits.Boolean.succinctMCSPOracle`: the oracle language.
* `Cslib.ApproxMCSP.noSetReal`: the no-instances of `MCSP[(s, 0), (s, δ)]` for a real error `δ`
  [ChenHiraharaOliveiraPichRajgopalSanthanam2020, Section 2.3, Definition 6, p. 13].

## Main results

* `Cslib.Circuits.Boolean.exists_oracleFormula_separating_approxMCSP`: at each input length
  `2 ^ n`, at most `2 ^ n` oracle gates of fan-in at most `approxMCSPQueryEncLength n s k`,
  adaptivity one, and leaf size at most `2 ^ n` times the fan-in.
* `Cslib.Circuits.Boolean.localFormulaClass_approxMCSP`: the same as membership in
  `LocalFormulaClass`.
* `Cslib.Circuits.Boolean.approxMCSPQueryEncLength_le_poly`: the fan-in is at most
  `98 * (k * (s + 1)) ^ 3` when `n ≤ s`.
* `Cslib.Circuits.Boolean.localFormulaClass_approxMCSP_real_poly`: Proposition 63's \[OS18\]
  bullet with a real error `δ`, with explicit polynomials in `s` and `⌈1 / δ⌉₊`.

The paper requires `n ≤ s(n) ≤ 2 ^ n / poly(n)`, `0 < δ(n) < 1 / 2` and a constructive `s`.
Only `n ≤ s(n)` and `0 < δ(n)` are used here; constructivity plays no role in this nonuniform
statement. As the paper remarks, the uniform complexity of the oracle gates is not considered.

## References

* [L. Chen, S. Hirahara, I. C. Oliveira, J. Pich, N. Rajgopal, R. Santhanam, *Beyond Natural
  Proofs: Hardness Magnification and Locality*][ChenHiraharaOliveiraPichRajgopalSanthanam2020]
* [I. C. Oliveira, R. Santhanam, *Hardness Magnification for Natural
  Problems*][OliveiraSanthanam2018]
-/

public section

namespace Cslib.Circuits.Boolean

open MCSP

/-- The oracle language of the Oliveira–Santhanam construction: the encoded `SuccinctMCSP`
yes-instances. -/
abbrev succinctMCSPOracle : Language Bool :=
  SuccinctMCSP.enc '' SuccinctMCSP

/-- The oracle gate on `succinctWord n S s` answers whether the sampled instance is a
`SuccinctMCSP` yes-instance. -/
theorem eval_query_succinctWord_eq_true_iff (n : ℕ) (S : Finset (BitString n)) (s : ℕ)
    (T : BitString (2 ^ n)) :
    (OracleFormula.query (succinctWord n S s)).eval (oracleInterpretation succinctMCSPOracle) T =
        true ↔
      SuccinctMCSP.Instance.ofFunction ((MCSP.truthTable n).symm T) S s ∈ SuccinctMCSP := by
  rw [OracleFormula.eval_query_eq_true_iff]
  change evalWord (succinctWord n S s) T ∈ succinctMCSPOracle ↔ _
  rw [evalWord_succinctWord]
  exact SuccinctMCSP.enc.injective.mem_set_image

open Classical in
/-- **The Oliveira–Santhanam construction is local, at one input length**
[ChenHiraharaOliveiraPichRajgopalSanthanam2020, Appendix A.2, Proposition 63, \[OS18\] bullet,
p. 52]. If `1 ≤ k n` and `s₁ n ≤ s₂ n`, some oracle formula on `2 ^ n` inputs with at most
`2 ^ n` oracle gates, each of fan-in at most `approxMCSPQueryEncLength n (s₂ n) (k n)`, at most
one oracle gate on any path, and at most `2 ^ n` times that fan-in leaves, accepts
`GapMCSP.yesSet s₁` and rejects `ApproxMCSP.noSet s₂ k` under `succinctMCSPOracle`. -/
theorem exists_oracleFormula_separating_approxMCSP {s₁ s₂ k : ℕ → ℕ} {n : ℕ}
    (hk : 1 ≤ k n) (hs : s₁ n ≤ s₂ n) :
    ∃ E : OracleFormula (2 ^ n),
      E.leafSize ≤ 2 ^ n * approxMCSPQueryEncLength n (s₂ n) (k n) ∧
      E.queryCount ≤ 2 ^ n ∧
      E.maxQueryArity ≤ approxMCSPQueryEncLength n (s₂ n) (k n) ∧
      E.adaptivity ≤ 1 ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s₁ →
        E.eval (oracleInterpretation succinctMCSPOracle) T = true) ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ ApproxMCSP.noSet s₂ k →
        E.eval (oracleInterpretation succinctMCSPOracle) T = false) := by
  obtain ⟨ωs, hyes, hno⟩ := exists_seeds_approxMCSP (s₁ := s₁) hk hs
    (card_computableFunctions_le_two_pow n (s₂ n))
  set ℓ := approxMCSPQueryEncLength n (s₂ n) (k n)
  let w : Fin (2 ^ n) → List (Formula signature (2 ^ n)) := fun j =>
    succinctWord n (Finset.univ.image (ωs j)) (s₂ n)
  have hw : ∀ j, (w j).length ≤ ℓ := fun j => by
    simp only [w, length_succinctWord]
    refine ofFunctionEncLength_le_approxMCSPQueryEncLength ?_
    exact Finset.card_image_le.trans (by simp)
  let Es : List (OracleFormula (2 ^ n)) := List.ofFn fun j => OracleFormula.query (w j)
  refine ⟨OracleFormula.all Es, ?_, ?_, ?_, ?_, fun T hT => ?_, fun T hT => ?_⟩
  · rw [OracleFormula.leafSize_all]
    refine (List.sum_le_length_nsmul _ ℓ ?_).trans (by simp [Es])
    intro x hx
    obtain ⟨E, hE, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hE
    exact (OracleFormula.leafSize_query_le
      fun _ h => leafSize_le_one_of_mem_succinctWord h).trans (hw j)
  · simp [Es, Function.comp_def]
  · refine OracleFormula.maxQueryArity_all_le fun E hE => ?_
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hE
    simpa using hw j
  · refine OracleFormula.adaptivity_all_le fun E hE => ?_
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hE
    simp
  · rw [OracleFormula.eval_all, decide_eq_true_eq]
    intro E hE
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hE
    exact (eval_query_succinctWord_eq_true_iff _ _ _ T).mpr (hyes T hT j)
  · rw [OracleFormula.eval_all, decide_eq_false_iff_not, not_forall]
    obtain ⟨j, hj⟩ := hno T hT
    refine ⟨OracleFormula.query (w j), fun h => hj ?_⟩
    exact (eval_query_succinctWord_eq_true_iff _ _ _ T).mp (h (List.mem_ofFn.mpr ⟨j, rfl⟩))

/-- A truth-table word has power-of-two length. -/
private theorem exists_length_eq_two_pow_of_mem_truthTableLanguage
    {C : ∀ n, Set (BooleanFunction n)} {w : List Bool} (hw : w ∈ truthTableLanguage C) :
    ∃ n, w.length = 2 ^ n := by
  obtain ⟨n, h, -⟩ := hw
  exact ⟨n, h⟩

/-- **The Oliveira–Santhanam construction in `LocalFormulaClass` form**
[ChenHiraharaOliveiraPichRajgopalSanthanam2020, Appendix A.2, Proposition 63, \[OS18\] bullet,
p. 52]. With `n = Nat.log 2 m` at input length `m`, approximate MCSP is in
`[m, ℓ, 1]–Formula[m · ℓ]` for the fan-in `ℓ = approxMCSPQueryEncLength n (s₂ n) (k n)`.
Input lengths that are not powers of two have no yes- or no-instances. -/
theorem localFormulaClass_approxMCSP {s₁ s₂ k : ℕ → ℕ} (hk : ∀ n, 1 ≤ k n)
    (hs : ∀ n, s₁ n ≤ s₂ n) :
    LocalFormulaClass (fun m => m)
      (fun m => approxMCSPQueryEncLength (Nat.log 2 m) (s₂ (Nat.log 2 m)) (k (Nat.log 2 m)))
      (fun _ => 1)
      (fun m => m * approxMCSPQueryEncLength (Nat.log 2 m) (s₂ (Nat.log 2 m)) (k (Nat.log 2 m)))
      (GapMCSP.yesSet s₁) (ApproxMCSP.noSet s₂ k) := by
  refine OracleModel.LocalClass.of_two_pow succinctMCSPOracle
    (fun _ => exists_length_eq_two_pow_of_mem_truthTableLanguage)
    (fun _ => exists_length_eq_two_pow_of_mem_truthTableLanguage)
    (fun _ _ => ⟨OracleFormula.tt, ?_⟩) fun n => ?_
  · simp [formulaModel]
  · obtain ⟨E, hS, hq, hℓ, ha, hyes, hno⟩ :=
      exists_oracleFormula_separating_approxMCSP (s₁ := s₁) (hk n) (hs n)
    simp only [Nat.log_pow Nat.one_lt_two]
    exact ⟨E, hS, hq, hℓ, ha, hyes, hno⟩

/-- An explicit polynomial bound on the fan-in of the oracle gates, `poly(s * k)`, when
`n ≤ s`. -/
theorem approxMCSPQueryEncLength_le_poly {n s k : ℕ} (hn : n ≤ s) (hk : 1 ≤ k) :
    approxMCSPQueryEncLength n s k ≤ 98 * (k * (s + 1)) ^ 3 := by
  have hlog := computableFunctionsLogBound_le_poly n s
  have hlog' : computableFunctionsLogBound n s + 2 ≤ 7 * (s + 1) ^ 2 := by nlinarith
  have hk' : 1 ≤ k * (s + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  unfold approxMCSPQueryEncLength SuccinctMCSP.ofFunctionEncLength
  have h1 : k * (computableFunctionsLogBound n s + 2) ≤ 7 * k * (s + 1) ^ 2 := by nlinarith
  have h2 : 8 * n + 10 ≤ 10 * (s + 1) := by omega
  have h3 : k * (computableFunctionsLogBound n s + 2) * (8 * n + 10) ≤
      70 * (k * (s + 1)) ^ 3 := by
    calc k * (computableFunctionsLogBound n s + 2) * (8 * n + 10)
        ≤ (7 * k * (s + 1) ^ 2) * (10 * (s + 1)) := Nat.mul_le_mul h1 h2
      _ = 70 * k * (s + 1) ^ 3 := by ring
      _ ≤ 70 * (k * (s + 1)) ^ 3 := by
        rw [mul_pow, ← mul_assoc]
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.le_self_pow (by decide) k))
  have h4 : 4 * n + 3 + s ≤ 28 * (k * (s + 1)) ^ 3 := by
    have : s + 1 ≤ k * (s + 1) := Nat.le_mul_of_pos_left _ hk
    have : k * (s + 1) ≤ (k * (s + 1)) ^ 3 := Nat.le_self_pow (by decide) _
    omega
  omega

end Cslib.Circuits.Boolean

namespace Cslib.ApproxMCSP

open MCSP Circuits.Boolean

/-- The no-instances of `MCSP[(s, 0), (s, δ)]` with a real error `δ`
[ChenHiraharaOliveiraPichRajgopalSanthanam2020, Section 2.3, Definition 6, p. 13]: truth tables of
functions `f` such that no function of circuit complexity at most `s n` agrees with `f` on at least
a `(1 - δ n)`-fraction of inputs. -/
def noSetReal (s : ℕ → ℕ) (δ : ℕ → ℝ) : Language Bool :=
  truthTableLanguage fun n =>
    {f | ∀ g ∈ computableFunctions n (s n),
      (((Finset.univ.filter fun x => g x = f x).card : ℕ) : ℝ) < (1 - δ n) * 2 ^ n}

/-- With `k n = ⌈1 / δ n⌉₊`, the real-error no-instances are integer-parameter no-instances. -/
theorem noSetReal_le_noSet {s : ℕ → ℕ} {δ : ℕ → ℝ} (hδ : ∀ n, 0 < δ n) :
    noSetReal s δ ≤ noSet s fun n => ⌈1 / δ n⌉₊ := by
  rintro w ⟨n, h, hf⟩
  refine ⟨n, h, fun g hg => ?_⟩
  have hlt := hf g hg
  generalize (Finset.univ.filter fun x => g x = _).card = a at hlt ⊢
  have hk1 : 1 ≤ ⌈1 / δ n⌉₊ := Nat.ceil_pos.mpr (by have := hδ n; positivity)
  have hkδ : 1 ≤ (⌈1 / δ n⌉₊ : ℝ) * δ n := by
    rw [← div_le_iff₀ (hδ n)]
    exact Nat.le_ceil (1 / δ n)
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  have hreal : (⌈1 / δ n⌉₊ : ℝ) * a ≤ ((⌈1 / δ n⌉₊ : ℝ) - 1) * 2 ^ n := by
    have hk0 : (0 : ℝ) ≤ ⌈1 / δ n⌉₊ := Nat.cast_nonneg _
    have h1 : (⌈1 / δ n⌉₊ : ℝ) * a ≤ ⌈1 / δ n⌉₊ * ((1 - δ n) * 2 ^ n) :=
      mul_le_mul_of_nonneg_left hlt.le hk0
    have h2 : (⌈1 / δ n⌉₊ : ℝ) * ((1 - δ n) * 2 ^ n) ≤ ((⌈1 / δ n⌉₊ : ℝ) - 1) * 2 ^ n := by
      have : (⌈1 / δ n⌉₊ : ℝ) * ((1 - δ n) * 2 ^ n) =
          ((⌈1 / δ n⌉₊ : ℝ) - ⌈1 / δ n⌉₊ * δ n) * 2 ^ n := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (by linarith) hpow.le
    exact h1.trans h2
  have hcast : ((⌈1 / δ n⌉₊ - 1 : ℕ) : ℝ) = (⌈1 / δ n⌉₊ : ℝ) - 1 := by
    rw [Nat.cast_sub hk1, Nat.cast_one]
  exact_mod_cast (show ((⌈1 / δ n⌉₊ * a : ℕ) : ℝ) ≤ (((⌈1 / δ n⌉₊ - 1) * 2 ^ n : ℕ) : ℝ) by
    push_cast [hcast]
    exact hreal)

end Cslib.ApproxMCSP

namespace Cslib.Circuits.Boolean

/-- **Proposition 63, \[OS18\] bullet, with a real error**
[ChenHiraharaOliveiraPichRajgopalSanthanam2020, Appendix A.2, p. 52]: for `0 < δ n`,
`MCSP[(s, 0), (s, δ)]` is in `[N, ℓ, 1]–Formula[N · ℓ]` with
`ℓ = approxMCSPQueryEncLength n (s n) ⌈1 / δ n⌉₊`. -/
theorem localFormulaClass_approxMCSP_real {s : ℕ → ℕ} {δ : ℕ → ℝ} (hδ : ∀ n, 0 < δ n) :
    LocalFormulaClass (fun m => m)
      (fun m => approxMCSPQueryEncLength (Nat.log 2 m) (s (Nat.log 2 m)) ⌈1 / δ (Nat.log 2 m)⌉₊)
      (fun _ => 1)
      (fun m => m *
        approxMCSPQueryEncLength (Nat.log 2 m) (s (Nat.log 2 m)) ⌈1 / δ (Nat.log 2 m)⌉₊)
      (GapMCSP.yesSet s) (ApproxMCSP.noSetReal s δ) :=
  (localFormulaClass_approxMCSP (s₁ := s) (s₂ := s) (k := fun n => ⌈1 / δ n⌉₊)
    (fun n => Nat.ceil_pos.mpr (by have := hδ n; positivity)) fun _ => le_rfl).anti le_rfl
    (ApproxMCSP.noSetReal_le_noSet hδ)

/-- **Proposition 63, \[OS18\] bullet, with explicit polynomials**
[ChenHiraharaOliveiraPichRajgopalSanthanam2020, Appendix A.2, p. 52]: if `0 < δ n` and
`n ≤ s n`, then `MCSP[(s, 0), (s, δ)]` is in `[N, ℓ, 1]–Formula[N · ℓ]` with
`ℓ = 98 * (⌈1 / δ n⌉₊ * (s n + 1)) ^ 3`, which is `poly(s / δ)`. -/
theorem localFormulaClass_approxMCSP_real_poly {s : ℕ → ℕ} {δ : ℕ → ℝ} (hδ : ∀ n, 0 < δ n)
    (hs : ∀ n, n ≤ s n) :
    LocalFormulaClass (fun m => m)
      (fun m => 98 * (⌈1 / δ (Nat.log 2 m)⌉₊ * (s (Nat.log 2 m) + 1)) ^ 3)
      (fun _ => 1)
      (fun m => m * (98 * (⌈1 / δ (Nat.log 2 m)⌉₊ * (s (Nat.log 2 m) + 1)) ^ 3))
      (GapMCSP.yesSet s) (ApproxMCSP.noSetReal s δ) := by
  have hb : ∀ m, approxMCSPQueryEncLength (Nat.log 2 m) (s (Nat.log 2 m))
      ⌈1 / δ (Nat.log 2 m)⌉₊ ≤ 98 * (⌈1 / δ (Nat.log 2 m)⌉₊ * (s (Nat.log 2 m) + 1)) ^ 3 :=
    fun m => approxMCSPQueryEncLength_le_poly (hs _)
      (Nat.ceil_pos.mpr (by have := hδ (Nat.log 2 m); positivity))
  exact (localFormulaClass_approxMCSP_real hδ).mono le_rfl hb le_rfl
    fun m => Nat.mul_le_mul_left m (hb m)

end Cslib.Circuits.Boolean

