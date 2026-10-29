/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.CountingNativeEndpoint
import Complexity.Computability.Complexity.FineGrained.CountingScaleBounds
import Complexity.Logics.Propositional.CNF.ModelCount.DenseRelabel
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Internal.OCombinators

/-!
# Subexponential model counting for bounded-width CNF formulas

For every fixed clause width `k`, one native machine computes the number of satisfying
assignments `CNF.modelCount φ` of every formula `φ` with clauses of at most `k` literals. It
runs in time `2 ^ (A * interpolationScale n)` times a polynomial in the encoding length, where
`n = φ.numVars`, and in space polynomial in the encoding length.

This restates `CountingNativeEndpoint.exists_declaredCounter` on the plain formula: the machine
relabels the variables densely, declares their number, and runs the declared counter. The
resource bounds are folded into `ComputableInO`.

More generally:
* `CountingNativeEndpoint.exists_counter_of_polyTime_toDeclared` composes
  `CountingNativeEndpoint.exists_declaredCounter` with any polynomial-time reduction
  `g : α → ℕ × CNF ℕ` and polynomial-time validity guard `valid : α → Bool`.
* `CountingNativeEndpoint.exists_shiftedCounter_of_polyTime_toCNF` composes
  `CountingNativeEndpoint.exists_modelCounter` with any polynomial-time CNF compilation
  `φ : α → CNF ℕ`, unary binary-power shift `shift : α → ℕ`, validity guard `valid : α → Bool`,
  and linear variable-count bound `(φ x).numVars ≤ C * μ x + D`, multiplying `(φ x).modelCount`
  by `2 ^ shift x` in binary while rescaling the subexponential rate to `μ x`.

## Main results

* `CountingNativeEndpoint.exists_counter_of_polyTime_toDeclared`: compose the declared `k`-CNF
  counter with any polynomial-time reduction and validity guard.
* `CountingNativeEndpoint.exists_modelCounter`: the bounded-width model counter.
* `CountingNativeEndpoint.exists_shiftedCounter_of_polyTime_toCNF`: compose the bounded-width
  model counter with a `2 ^ shift` factor and a linear `numVars ≤ C * μ + D` rescaling.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Proposition 6.4.
-/

namespace Cslib.Complexity.CountingNativeEndpoint

open Cslib.Logic.PL Turing.MultiTapeTM SubexponentialSAT

/-- General composition of `CountingNativeEndpoint.exists_declaredCounter` with any polynomial-time
reduction `g : α → ℕ × CNF ℕ` and polynomial-time validity guard `valid : α → Bool`. -/
public theorem exists_counter_of_polyTime_toDeclared {α : Type} {encA : α ↪ List Bool} (k : ℕ)
    {g : α → ℕ × CNF ℕ} (hg : ComputableInPolyTime g encA (encPair encUnary encCNF))
    {valid : α → Bool} (hvalid : ComputableInPolyTime valid encA encBool)
    (hvalid_imp : ∀ x, valid x = true → CNF.validDeclaredInput k (g x).1 (g x).2 = true) :
    ∃ (count : α → ℕ) (T S : α → ℕ) (A c e a b : ℕ),
      ComputableInO count encA encNat T S ∧
      (∀ x, count x = if valid x then (g x).2.modelCountOn (Finset.range (g x).1) else 0) ∧
      (∀ x, (T x : ℝ) ≤ c * ((2 : ℝ) ^ ((A : ℝ) * interpolationScale (g x).1) *
        (((encA x).length : ℝ) + 1) ^ e) + c) ∧
      (∀ x, S x ≤ a * ((encA x).length + 1) ^ b) := by
  obtain ⟨count₀, T₀, S₀, A, c₀, e₀, a₀, b₀, hcount₀, hspec₀, hT₀, hS₀⟩ :=
    exists_declaredCounter k
  obtain ⟨dg, _, hdg⟩ := hg.exists_degree
  obtain ⟨dv, _, hdv⟩ := hvalid.exists_degree
  obtain ⟨p, q, hp⟩ := hg.polyBounded_length.exists_le
  have hcomp := hcount₀.comp hdg.inO
  have hite := hdv.inO.ite hcomp (ComputableInO.const (encIn := encA) 0)
  let P (x : α) := ((encA x).length + 1) ^ dv + ((encA x).length + 1) ^ dg + (encA x).length
  let T (x : α) := P x + T₀ (g x)
  let S (x : α) := P x + S₀ (g x)
  refine ⟨fun x => if valid x then count₀ (g x) else 0, T, S, A,
    3 + c₀ * (p + 1) ^ e₀, dv + dg + 1 + q * e₀,
    3 + a₀ * (p + 1) ^ b₀, dv + dg + 1 + q * b₀,
    (hite.mono 1 (fun x => ?_) (fun x => ?_)).of_enc_eq (fun _ => rfl),
    fun x => ?_, fun x => ?_, fun x => ?_⟩
  · dsimp only [T, P]
    split_ifs <;> omega
  · dsimp only [S, P]
    split_ifs <;> omega
  · dsimp only
    split_ifs with hx
    · have hvalid' := hvalid_imp x hx
      simp [hspec₀ (g x), hvalid']
    · rfl
  · let Y : ℕ := (encA x).length + 1
    have hY1 : 1 ≤ Y := Nat.le_add_left 1 _
    have hlen : (encPair encUnary encCNF (g x)).length + 1 ≤ (p + 1) * Y ^ q := by
      have h1 : (encPair encUnary encCNF (g x)).length ≤ p * Y ^ q := hp x
      have h2 : 1 ≤ Y ^ q := Nat.one_le_pow _ _ hY1
      nlinarith
    have hpow : ((encPair encUnary encCNF (g x)).length + 1) ^ e₀ ≤
        (p + 1) ^ e₀ * Y ^ (q * e₀) := by
      calc _ ≤ ((p + 1) * Y ^ q) ^ e₀ := Nat.pow_le_pow_left hlen e₀
        _ = _ := by rw [mul_pow, pow_mul]
    let E := dv + dg + 1 + q * e₀
    have hP_le : P x ≤ 3 * Y ^ E := by
      have h1 : Y ^ dv ≤ Y ^ E := Nat.pow_le_pow_right hY1 (by dsimp [E]; omega)
      have h2 : Y ^ dg ≤ Y ^ E := Nat.pow_le_pow_right hY1 (by dsimp [E]; omega)
      have hE0 : E ≠ 0 := by dsimp [E]; omega
      have h3 : (encA x).length ≤ Y ^ E :=
        (Nat.le_succ _).trans (Nat.le_self_pow hE0 Y)
      change Y ^ dv + Y ^ dg + (encA x).length ≤ 3 * Y ^ E
      omega
    have hqe : Y ^ (q * e₀) ≤ Y ^ E := Nat.pow_le_pow_right hY1 (by dsimp [E]; omega)
    let X : ℝ := (2 : ℝ) ^ ((A : ℝ) * interpolationScale (g x).1)
    let YR : ℝ := ((encA x).length : ℝ) + 1
    have hYR_eq : (Y : ℝ) = YR := by dsimp [Y, YR]; push_cast; rfl
    have hX1 : (1 : ℝ) ≤ X :=
      Real.one_le_rpow (by norm_num) (mul_nonneg (Nat.cast_nonneg A) (interpolationScale_nonneg _))
    have hT₀_le : (T₀ (g x) : ℝ) ≤
        ((c₀ * (p + 1) ^ e₀ : ℕ) : ℝ) * (X * YR ^ E) + c₀ := by
      have h0 := hT₀ (g x)
      have hpow_le : ((encPair encUnary encCNF (g x)).length + 1) ^ e₀ ≤
          (p + 1) ^ e₀ * Y ^ E := hpow.trans (Nat.mul_le_mul_left _ hqe)
      have hpowR : (((encPair encUnary encCNF (g x)).length : ℝ) + 1) ^ e₀ ≤
          (((p + 1) ^ e₀ : ℕ) : ℝ) * YR ^ E := by
        rw [← hYR_eq]
        exact_mod_cast hpow_le
      have h1 := mul_le_mul_of_nonneg_left hpowR (by positivity : (0 : ℝ) ≤ X)
      have h2 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg c₀)
      have hcast : ((c₀ * (p + 1) ^ e₀ : ℕ) : ℝ) = (c₀ : ℝ) * (((p + 1) ^ e₀ : ℕ) : ℝ) := by
        push_cast; rfl
      rw [hcast]
      linarith
    have hP_R : (P x : ℝ) ≤ 3 * (X * YR ^ E) := by
      have hPR : (P x : ℝ) ≤ 3 * YR ^ E := by
        rw [← hYR_eq]
        exact_mod_cast hP_le
      have hYR_nonneg : (0 : ℝ) ≤ YR ^ E := by dsimp [YR]; positivity
      have hXY : YR ^ E ≤ X * YR ^ E := le_mul_of_one_le_left hYR_nonneg hX1
      linarith
    have hc_le : (c₀ : ℝ) ≤ ((3 + c₀ * (p + 1) ^ e₀ : ℕ) : ℝ) := by
      have : 1 ≤ (p + 1) ^ e₀ := Nat.one_le_pow _ _ (Nat.le_add_left 1 p)
      exact_mod_cast (by nlinarith : c₀ ≤ 3 + c₀ * (p + 1) ^ e₀)
    have hadd : (3 : ℝ) + ((c₀ * (p + 1) ^ e₀ : ℕ) : ℝ) = ((3 + c₀ * (p + 1) ^ e₀ : ℕ) : ℝ) := by
      push_cast; rfl
    change ((P x + T₀ (g x) : ℕ) : ℝ) ≤
      ((3 + c₀ * (p + 1) ^ e₀ : ℕ) : ℝ) * (X * YR ^ E) + ((3 + c₀ * (p + 1) ^ e₀ : ℕ) : ℝ)
    rw [Nat.cast_add, ← hadd, add_mul]
    linarith
  · let Y : ℕ := (encA x).length + 1
    have hY1 : 1 ≤ Y := Nat.le_add_left 1 _
    have hlen : (encPair encUnary encCNF (g x)).length + 1 ≤ (p + 1) * Y ^ q := by
      have h1 : (encPair encUnary encCNF (g x)).length ≤ p * Y ^ q := hp x
      have h2 : 1 ≤ Y ^ q := Nat.one_le_pow _ _ hY1
      nlinarith
    have hpow : ((encPair encUnary encCNF (g x)).length + 1) ^ b₀ ≤
        (p + 1) ^ b₀ * Y ^ (q * b₀) := by
      calc _ ≤ ((p + 1) * Y ^ q) ^ b₀ := Nat.pow_le_pow_left hlen b₀
        _ = _ := by rw [mul_pow, pow_mul]
    let B := dv + dg + 1 + q * b₀
    have hP_le : P x ≤ 3 * Y ^ B := by
      have h1 : Y ^ dv ≤ Y ^ B := Nat.pow_le_pow_right hY1 (by dsimp [B]; omega)
      have h2 : Y ^ dg ≤ Y ^ B := Nat.pow_le_pow_right hY1 (by dsimp [B]; omega)
      have hB0 : B ≠ 0 := by dsimp [B]; omega
      have h3 : (encA x).length ≤ Y ^ B :=
        (Nat.le_succ _).trans (Nat.le_self_pow hB0 Y)
      change Y ^ dv + Y ^ dg + (encA x).length ≤ 3 * Y ^ B
      omega
    have hqb : Y ^ (q * b₀) ≤ Y ^ B := Nat.pow_le_pow_right hY1 (by dsimp [B]; omega)
    have hS₀_le : S₀ (g x) ≤ a₀ * (p + 1) ^ b₀ * Y ^ B := by
      calc S₀ (g x) ≤ a₀ * ((encPair encUnary encCNF (g x)).length + 1) ^ b₀ := hS₀ (g x)
        _ ≤ a₀ * ((p + 1) ^ b₀ * Y ^ B) :=
            Nat.mul_le_mul_left a₀ (hpow.trans (Nat.mul_le_mul_left _ hqb))
        _ = a₀ * (p + 1) ^ b₀ * Y ^ B := by rw [Nat.mul_assoc]
    change P x + S₀ (g x) ≤ (3 + a₀ * (p + 1) ^ b₀) * Y ^ B
    rw [Nat.add_mul]
    omega

/-- Dense relabeling followed by declaring the number of variables. -/
private theorem computableInPolyTime_declareDense :
    ComputableInPolyTime (fun φ : CNF ℕ => (φ.denseRelabel.numVars, φ.denseRelabel)) encCNF
      (encPair encUnary encCNF) := by
  have h : ComputableInPolyTime (fun ψ : CNF ℕ => (ψ.numVars, ψ)) encCNF
      (encPair encUnary encCNF) := by fun_prop
  exact h.comp SAT.computableInPolyTime_denseRelabel

/-- **Subexponential bounded-width model counting.** For each width `k`, one machine computes
`φ.modelCount` on every formula `φ` whose clauses have at most `k` literals, in time
`2 ^ (A * interpolationScale φ.numVars)` times a polynomial in the encoding length, and in
polynomial space. -/
public theorem exists_modelCounter (k : ℕ) :
    ∃ (count : CNF ℕ → ℕ) (A e b : ℕ),
      (∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ k) → count φ = φ.modelCount) ∧
      ComputableInO count encCNF encNat
        (fun φ => ⌈(2 : ℝ) ^ ((A : ℝ) * interpolationScale φ.numVars)⌉₊ *
          ((encCNF φ).length + 1) ^ e)
        (fun φ => ((encCNF φ).length + 1) ^ b) := by
  obtain ⟨count, T, S, A, c, e, a, b, hcount, hspec, hT, hS⟩ := exists_declaredCounter k
  set g : CNF ℕ → ℕ × CNF ℕ := fun φ => (φ.denseRelabel.numVars, φ.denseRelabel)
  obtain ⟨d, _, hd⟩ := computableInPolyTime_declareDense.exists_degree
  obtain ⟨p, q, hp⟩ := computableInPolyTime_declareDense.polyBounded_length.exists_le
  refine ⟨fun φ => count (g φ), A, q * e + d, q * b + d, fun φ hφ => ?_,
    (hcount.comp hd.inO).mono
      (c * (p + 1) ^ e + 1 + c + a * (p + 1) ^ b + 1) (fun φ => ?_) (fun φ => ?_)⟩
  · have hw : ∀ cl ∈ φ.denseRelabel, cl.length ≤ k :=
      (CNF.all_length_le_denseRelabel φ).mpr hφ
    have hv : CNF.validDeclaredInput k φ.denseRelabel.numVars φ.denseRelabel = true :=
      CNF.validDeclaredInput_eq_true_iff.mpr
        ⟨hw, by rw [CNF.vars_denseRelabel_toFinset, CNF.numVars_denseRelabel]⟩
    simp only [g]
    rw [hspec, hv]
    simp only [↓reduceIte, CNF.numVars_denseRelabel, CNF.modelCountOn_denseRelabel]
  all_goals
    set Y := (encCNF φ).length + 1 with hY
    have hY1 : 1 ≤ Y := Nat.le_add_left 1 _
    have hlen : (encPair encUnary encCNF (g φ)).length + 1 ≤ (p + 1) * Y ^ q := by
      have h1 : (encPair encUnary encCNF (g φ)).length ≤ p * Y ^ q := hp φ
      have h2 : 1 ≤ Y ^ q := Nat.one_le_pow _ _ hY1
      nlinarith
  · -- time
    set X : ℝ := (2 : ℝ) ^ ((A : ℝ) * interpolationScale φ.numVars) with hX
    set N := ⌈X⌉₊
    have hXN : X ≤ N := Nat.le_ceil X
    have hN1 : 1 ≤ N := Nat.one_le_ceil_iff.mpr (Real.rpow_pos_of_pos (by norm_num) _)
    have hpow : ((encPair encUnary encCNF (g φ)).length + 1) ^ e ≤ (p + 1) ^ e * Y ^ (q * e) := by
      calc _ ≤ ((p + 1) * Y ^ q) ^ e := Nat.pow_le_pow_left hlen e
        _ = _ := by rw [mul_pow, pow_mul]
    have hTg : T (g φ) ≤ c * (p + 1) ^ e * (N * Y ^ (q * e)) + c := by
      have h : (T (g φ) : ℝ) ≤
          c * (X * (((encPair encUnary encCNF (g φ)).length : ℝ) + 1) ^ e) + c := by
        have h := hT (g φ)
        rwa [show (g φ).1 = φ.numVars from CNF.numVars_denseRelabel φ] at h
      have hpowR : (((encPair encUnary encCNF (g φ)).length : ℝ) + 1) ^ e ≤
          (p + 1) ^ e * Y ^ (q * e) := by exact_mod_cast hpow
      have h1 := mul_le_mul hXN hpowR (by positivity) (by positivity)
      have h2 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg c)
      have : (T (g φ) : ℝ) ≤ c * (p + 1) ^ e * (N * Y ^ (q * e)) + c := by nlinarith
      exact_mod_cast this
    have hqe : Y ^ (q * e) ≤ Y ^ (q * e + d) := Nat.pow_le_pow_right hY1 (by omega)
    have hd' : Y ^ d ≤ N * Y ^ (q * e + d) :=
      (Nat.pow_le_pow_right hY1 (by omega)).trans (Nat.le_mul_of_pos_left _ hN1)
    have hmul := Nat.mul_le_mul_left (c * (p + 1) ^ e) (Nat.mul_le_mul_left N hqe)
    change Y ^ d + T (g φ) ≤ _ * (N * Y ^ (q * e + d) + 1)
    generalize N * Y ^ (q * e + d) = Z at hd' hmul ⊢
    generalize c * (p + 1) ^ e = u at hTg hmul ⊢
    generalize a * (p + 1) ^ b = v
    nlinarith [Nat.zero_le (c * Z), Nat.zero_le (v * Z), Nat.zero_le (u * Z)]
  · -- space
    have hpow : ((encPair encUnary encCNF (g φ)).length + 1) ^ b ≤ (p + 1) ^ b * Y ^ (q * b) := by
      calc _ ≤ ((p + 1) * Y ^ q) ^ b := Nat.pow_le_pow_left hlen b
        _ = _ := by rw [mul_pow, pow_mul]
    have hSg : S (g φ) ≤ a * (p + 1) ^ b * Y ^ (q * b + d) :=
      (hS (g φ)).trans (by
        rw [mul_assoc]
        exact Nat.mul_le_mul_left a (hpow.trans (Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right hY1 (by omega)))))
    have hd' : Y ^ d ≤ Y ^ (q * b + d) := Nat.pow_le_pow_right hY1 (by omega)
    change Y ^ d + S (g φ) ≤ _ * (Y ^ (q * b + d) + 1)
    generalize Y ^ (q * b + d) = Z at hSg hd' ⊢
    generalize a * (p + 1) ^ b = v at hSg ⊢
    generalize c * (p + 1) ^ e = u
    nlinarith [Nat.zero_le (c * Z), Nat.zero_le (v * Z), Nat.zero_le (u * Z)]

/-- Compose `CountingNativeEndpoint.exists_modelCounter` with a polynomial-time CNF compilation
`φ : α → CNF ℕ`, a polynomial-time unary binary-exponent shift `shift : α → ℕ`, a polynomial-time
validity guard `valid : α → Bool`, and a linear variable-count bound `(φ x).numVars ≤ C * μ x + D`
under `valid x = true`, multiplying `(φ x).modelCount` in binary by `2 ^ shift x` while rescaling
the `interpolationScale` exponent to `μ x`. -/
public theorem exists_shiftedCounter_of_polyTime_toCNF {α : Type} {encA : α ↪ List Bool} (k : ℕ)
    {φ : α → CNF ℕ} (hφ : ComputableInPolyTime φ encA encCNF)
    {shift : α → ℕ} (hshift : ComputableInPolyTime shift encA encUnary)
    {valid : α → Bool} (hvalid : ComputableInPolyTime valid encA encBool)
    (μ : α → ℕ) (C D : ℕ)
    (hvalid_imp : ∀ x, valid x = true →
      (∀ cl ∈ φ x, cl.length ≤ k) ∧ (φ x).numVars ≤ C * μ x + D) :
    ∃ (count : α → ℕ) (A e b : ℕ),
      (∀ x, count x = if valid x then 2 ^ shift x * (φ x).modelCount else 0) ∧
      ComputableInO count encA encNat
        (fun x => ⌈(2 : ℝ) ^ ((A : ℝ) * interpolationScale (μ x))⌉₊ *
          ((encA x).length + 1) ^ e)
        (fun x => ((encA x).length + 1) ^ b) := by
  open ComputableInPolyTime in
  set fCNF : α → CNF ℕ := fun x => if valid x then φ x else []
  have hfCNF_poly : ComputableInPolyTime fCNF encA encCNF :=
    hvalid.ite hφ (const [])
  set fPow : α → ℕ := fun x => if valid x then 2 ^ shift x else 0
  have hfPow_poly : ComputableInPolyTime fPow encA encNat :=
    hvalid.ite (binary_two_pow.comp hshift) (const 0)
  obtain ⟨d₁, _, hfCNF_deg⟩ := hfCNF_poly.exists_degree
  obtain ⟨p, q, hfCNF_len⟩ := hfCNF_poly.polyBounded_length.exists_le
  obtain ⟨d₂, _, hfPow_deg⟩ := hfPow_poly.exists_degree
  obtain ⟨d₃, _, hmul_deg⟩ := (binary_mul' (fst encNat encNat) (snd encNat encNat)).exists_degree
  obtain ⟨countCNF, A₀, e₀, b₀, hcountCNF_spec, hcountCNF_inO⟩ := exists_modelCounter k
  have hsub := hcountCNF_inO.comp hfCNF_deg.inO
  have hpair := hfPow_deg.inO.prod hsub
  obtain ⟨c_pair, hpair_len⟩ := hpair.length_le
  have htot := hmul_deg.inO.comp hpair
  obtain ⟨K, _, hK_bound⟩ := ceil_two_pow_interpolationScale_le_of_linear A₀ C D
  let A : ℕ := A₀ * 8 ^ (2 * C)
  let B₁ : ℕ := d₁ + d₂ + q * b₀
  let M : ℕ := c_pair * (3 + (p + 1) ^ b₀) + 1
  let e : ℕ := B₁ + q * e₀ + B₁ * d₃
  let b : ℕ := B₁ + B₁ * d₃
  let C_bound : ℕ := 2 + K * (p + 1) ^ e₀ + (p + 1) ^ b₀ + M ^ d₃ + 1
  refine ⟨fun x => fPow x * countCNF (fCNF x), A, e, b, fun x => ?_,
    htot.mono C_bound (fun x => ?_) (fun x => ?_)⟩
  · dsimp only [fPow, fCNF]
    split_ifs with hvx
    · rw [hcountCNF_spec (φ x) (hvalid_imp x hvx).1]
    · simp only [Nat.zero_mul]
  all_goals
    set Y : ℕ := (encA x).length + 1
    have hY1 : 1 ≤ Y := Nat.le_add_left 1 _
    have hφ_len : (encCNF (fCNF x)).length + 1 ≤ (p + 1) * Y ^ q := by
      have h1 : (encCNF (fCNF x)).length ≤ p * Y ^ q := hfCNF_len x
      have h2 : 1 ≤ Y ^ q := Nat.one_le_pow q Y hY1
      nlinarith
    have hφ_b₀ : ((encCNF (fCNF x)).length + 1) ^ b₀ ≤ (p + 1) ^ b₀ * Y ^ (q * b₀) := by
      calc ((encCNF (fCNF x)).length + 1) ^ b₀
          ≤ ((p + 1) * Y ^ q) ^ b₀ := Nat.pow_le_pow_left hφ_len b₀
        _ = (p + 1) ^ b₀ * Y ^ (q * b₀) := by rw [mul_pow, pow_mul]
    have hSpair_le : Y ^ d₂ + (Y ^ d₁ + ((encCNF (fCNF x)).length + 1) ^ b₀) ≤
        (2 + (p + 1) ^ b₀) * Y ^ B₁ := by
      have hd₂ : Y ^ d₂ ≤ Y ^ B₁ := Nat.pow_le_pow_right hY1 (by dsimp only [B₁]; omega)
      have hd₁ : Y ^ d₁ ≤ Y ^ B₁ := Nat.pow_le_pow_right hY1 (by dsimp only [B₁]; omega)
      have hqb₀ : Y ^ (q * b₀) ≤ Y ^ B₁ := Nat.pow_le_pow_right hY1 (by dsimp only [B₁]; omega)
      have h3 := hφ_b₀.trans (Nat.mul_le_mul_left _ hqb₀)
      nlinarith
    have hpair_d₃ : ((encPair encNat encNat (fPow x, countCNF (fCNF x))).length + 1) ^ d₃ ≤
        M ^ d₃ * Y ^ (B₁ * d₃) := by
      have h1 : (encPair encNat encNat (fPow x, countCNF (fCNF x))).length ≤
          c_pair * (Y ^ d₂ + (Y ^ d₁ + ((encCNF (fCNF x)).length + 1) ^ b₀) + 1) := hpair_len x
      have hYB₁ : 1 ≤ Y ^ B₁ := Nat.one_le_pow B₁ Y hY1
      have hS1 : Y ^ d₂ + (Y ^ d₁ + ((encCNF (fCNF x)).length + 1) ^ b₀) + 1 ≤
          (3 + (p + 1) ^ b₀) * Y ^ B₁ := by
        calc Y ^ d₂ + (Y ^ d₁ + ((encCNF (fCNF x)).length + 1) ^ b₀) + 1
            ≤ (2 + (p + 1) ^ b₀) * Y ^ B₁ + Y ^ B₁ := Nat.add_le_add hSpair_le hYB₁
          _ = (3 + (p + 1) ^ b₀) * Y ^ B₁ := by ring
      have h2 : (encPair encNat encNat (fPow x, countCNF (fCNF x))).length + 1 ≤ M * Y ^ B₁ := by
        calc (encPair encNat encNat (fPow x, countCNF (fCNF x))).length + 1
            ≤ c_pair * ((3 + (p + 1) ^ b₀) * Y ^ B₁) + Y ^ B₁ :=
              Nat.add_le_add (h1.trans (Nat.mul_le_mul_left c_pair hS1)) hYB₁
          _ = M * Y ^ B₁ := by dsimp only [M]; ring
      calc ((encPair encNat encNat (fPow x, countCNF (fCNF x))).length + 1) ^ d₃
          ≤ (M * Y ^ B₁) ^ d₃ := Nat.pow_le_pow_left h2 d₃
        _ = M ^ d₃ * Y ^ (B₁ * d₃) := by rw [mul_pow, pow_mul]
  · set N : ℕ := ⌈(2 : ℝ) ^ ((A : ℝ) * interpolationScale (μ x))⌉₊
    have hN1 : 1 ≤ N := Nat.one_le_ceil_iff.mpr (Real.rpow_pos_of_pos (by norm_num) _)
    have hnum_le : (fCNF x).numVars ≤ C * μ x + D := by
      dsimp only [fCNF]
      split_ifs with hvx
      · exact (hvalid_imp x hvx).2
      · simp only [CNF.numVars, CNF.vars, List.flatten_nil, List.map_nil, List.toFinset_nil,
          Finset.card_empty, Nat.zero_le]
    have hscale : ⌈(2 : ℝ) ^ ((A₀ : ℝ) * interpolationScale (fCNF x).numVars)⌉₊ ≤ K * N :=
      hK_bound hnum_le
    have hφ_e₀ : ((encCNF (fCNF x)).length + 1) ^ e₀ ≤ (p + 1) ^ e₀ * Y ^ (q * e₀) := by
      calc ((encCNF (fCNF x)).length + 1) ^ e₀
          ≤ ((p + 1) * Y ^ q) ^ e₀ := Nat.pow_le_pow_left hφ_len e₀
        _ = (p + 1) ^ e₀ * Y ^ (q * e₀) := by rw [mul_pow, pow_mul]
    have hsub_T : ⌈(2 : ℝ) ^ ((A₀ : ℝ) * interpolationScale (fCNF x).numVars)⌉₊ *
        ((encCNF (fCNF x)).length + 1) ^ e₀ ≤ K * (p + 1) ^ e₀ * (N * Y ^ e) := by
      have hqe₀ : Y ^ (q * e₀) ≤ Y ^ e := Nat.pow_le_pow_right hY1 (by dsimp only [e]; omega)
      have h1 := Nat.mul_le_mul hscale (hφ_e₀.trans (Nat.mul_le_mul_left _ hqe₀))
      calc ⌈(2 : ℝ) ^ ((A₀ : ℝ) * interpolationScale (fCNF x).numVars)⌉₊ *
            ((encCNF (fCNF x)).length + 1) ^ e₀
          ≤ (K * N) * ((p + 1) ^ e₀ * Y ^ e) := h1
        _ = K * (p + 1) ^ e₀ * (N * Y ^ e) := by ring
    have hd₂ : Y ^ d₂ ≤ N * Y ^ e :=
      (Nat.pow_le_pow_right hY1 (by dsimp only [e, B₁]; omega)).trans
        (Nat.le_mul_of_pos_left _ hN1)
    have hd₁ : Y ^ d₁ ≤ N * Y ^ e :=
      (Nat.pow_le_pow_right hY1 (by dsimp only [e, B₁]; omega)).trans
        (Nat.le_mul_of_pos_left _ hN1)
    have hd₃ : ((encPair encNat encNat (fPow x, countCNF (fCNF x))).length + 1) ^ d₃ ≤
        M ^ d₃ * (N * Y ^ e) := by
      have hBe : Y ^ (B₁ * d₃) ≤ N * Y ^ e :=
        (Nat.pow_le_pow_right hY1 (by dsimp only [e]; omega)).trans
          (Nat.le_mul_of_pos_left _ hN1)
      exact hpair_d₃.trans (Nat.mul_le_mul_left _ hBe)
    change Y ^ d₂ + (Y ^ d₁ + ⌈(2 : ℝ) ^ ((A₀ : ℝ) * interpolationScale (fCNF x).numVars)⌉₊ *
      ((encCNF (fCNF x)).length + 1) ^ e₀) +
      ((encPair encNat encNat (fPow x, countCNF (fCNF x))).length + 1) ^ d₃ ≤
      C_bound * (N * Y ^ e + 1)
    dsimp only [C_bound]
    calc Y ^ d₂ + (Y ^ d₁ + ⌈(2 : ℝ) ^ ((A₀ : ℝ) * interpolationScale (fCNF x).numVars)⌉₊ *
          ((encCNF (fCNF x)).length + 1) ^ e₀) +
          ((encPair encNat encNat (fPow x, countCNF (fCNF x))).length + 1) ^ d₃
        ≤ N * Y ^ e + (N * Y ^ e + K * (p + 1) ^ e₀ * (N * Y ^ e)) + M ^ d₃ * (N * Y ^ e) :=
          Nat.add_le_add (Nat.add_le_add hd₂ (Nat.add_le_add hd₁ hsub_T)) hd₃
      _ = (2 + K * (p + 1) ^ e₀ + M ^ d₃) * (N * Y ^ e) := by ring
      _ ≤ (2 + K * (p + 1) ^ e₀ + (p + 1) ^ b₀ + M ^ d₃ + 1) * (N * Y ^ e + 1) :=
          Nat.mul_le_mul (by omega) (Nat.le_succ _)
  · have hB₁_b : Y ^ B₁ ≤ Y ^ b := Nat.pow_le_pow_right hY1 (by dsimp only [b]; omega)
    have hBd₃_b : Y ^ (B₁ * d₃) ≤ Y ^ b := Nat.pow_le_pow_right hY1 (by dsimp only [b]; omega)
    have hs1 := hSpair_le.trans (Nat.mul_le_mul_left _ hB₁_b)
    have hs2 := hpair_d₃.trans (Nat.mul_le_mul_left _ hBd₃_b)
    change Y ^ d₂ + (Y ^ d₁ + ((encCNF (fCNF x)).length + 1) ^ b₀) +
      ((encPair encNat encNat (fPow x, countCNF (fCNF x))).length + 1) ^ d₃ ≤
      C_bound * (Y ^ b + 1)
    dsimp only [C_bound]
    calc Y ^ d₂ + (Y ^ d₁ + ((encCNF (fCNF x)).length + 1) ^ b₀) +
          ((encPair encNat encNat (fPow x, countCNF (fCNF x))).length + 1) ^ d₃
        ≤ (2 + (p + 1) ^ b₀) * Y ^ b + M ^ d₃ * Y ^ b := Nat.add_le_add hs1 hs2
      _ = (2 + (p + 1) ^ b₀ + M ^ d₃) * Y ^ b := by ring
      _ ≤ (2 + K * (p + 1) ^ e₀ + (p + 1) ^ b₀ + M ^ d₃ + 1) * (Y ^ b + 1) :=
          Nat.mul_le_mul (by omega) (Nat.le_succ _)

end Cslib.Complexity.CountingNativeEndpoint
