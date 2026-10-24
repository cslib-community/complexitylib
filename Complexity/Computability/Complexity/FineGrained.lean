/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Hierarchy.Time
public import Complexity.Computability.Complexity.Problems.ThreeSAT
public import Complexity.Logics.Propositional.CNF.ModelCount
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain

/-!
# The exponential time hypotheses

Fine-grained complexity measures running time in a parameter of the instance, such as the number
`n` of variables of a formula, rather than in the length `L` of its encoding. The time class
`Cslib.Complexity.DTIME` bounds the time by a function of `L`; here
`Cslib.Complexity.DecidableInTimeO A enc T` bounds it by `O(T a)` for any real function `T` of the
instance `a`, on the same machines. A bound that is a function of the length gives back `DTIME`
(`Cslib.Complexity.mem_DTIME_iff_decidableInTimeO`).

`Cslib.Complexity.DecidableInExpTime A enc μ δ` says that `A` is decidable within time
`2 ^ (δ μ a)` times a polynomial in `L`, for a parameter `μ`. The polynomial in `L` is the cost of
reading and processing the instance; the parameter is never hidden in the encoding length. For
formulas `μ` is usually the number of distinct variables (`Cslib.Logic.PL.CNF.numVars`), which is
at most `L`, and can be much smaller.

* `Cslib.Complexity.KSAT k` is `k`-SAT, the satisfiable formulas whose clauses have at most `k`
  literals, and `Cslib.Complexity.satExponent k` is its exponent `s_k` [ImpagliazzoPaturi2001]: the
  infimum of the `δ ≥ 0` for which `k`-SAT is decidable within time `2 ^ (δ n)` times a polynomial.
* `Cslib.Complexity.ETH`, **the exponential time hypothesis** [ImpagliazzoPaturi2001]: for some
  `δ > 0`, 3SAT is not decidable within time `2 ^ (δ n)` times any polynomial in `L`.
* `Cslib.Complexity.SETH`, **the strong exponential time hypothesis**: for every `ε > 0` some
  `k`-SAT is not decidable within time `2 ^ ((1 - ε) n)` times any polynomial in `L`.
* `Cslib.Complexity.OV`, the orthogonal vectors problem, and `Cslib.Complexity.OVH`, **the
  orthogonal vectors hypothesis** in its moderate-dimension form: for every `ε > 0`, `OV` is not
  decidable within time `N ^ (2 - ε)` times any polynomial in the dimension `d`, on `N` vectors.

The negation of `ETH` is `Cslib.Complexity.DecidableInSubexpTime`: decidability within time
`2 ^ (δ n)` times a polynomial for every `δ > 0`, by a decider that may depend on `δ`
(`Cslib.Complexity.ETH_iff_not_decidableInSubexpTime`).

## Main definitions

* `Cslib.Complexity.DecidableInTimeO`, `Cslib.Complexity.DecidableInExpTime`,
  `Cslib.Complexity.DecidableInSubexpTime`: time bounds in parameters of the instance.
* `Cslib.Complexity.KSAT`, `Cslib.Complexity.satExponent`: `k`-SAT and its exponent.
* `Cslib.Complexity.ETH`, `Cslib.Complexity.SETH`: the exponential time hypotheses.
* `Cslib.Complexity.OV`, `Cslib.Complexity.encOV`, `Cslib.Complexity.OVH`: the orthogonal vectors
  problem and hypothesis.

## Main results

* `Cslib.Complexity.mem_DTIME_iff_decidableInTimeO`: `DTIME` is `DecidableInTimeO` for bounds in
  the length of the encoded instance.
* `Cslib.Complexity.DecidableInTimeO.exists_computableInO`,
  `Cslib.Complexity.DecidableInTimeO.of_computableInO`: deciders within time `O(T)` are the
  Boolean functions computable within time `O(T)`, which compose.
* `Cslib.Complexity.DecidableInTimeO.inter`: restricting to a set decided in polynomial time.
* `Cslib.Complexity.DecidableInExpTime.mono`: larger exponents allow more problems.
* `Cslib.Complexity.ETH_iff_not_decidableInSubexpTime`.

## References

* [R. Impagliazzo, R. Paturi, *On the complexity of k-SAT*][ImpagliazzoPaturi2001]
* [R. Williams, *A new algorithm for optimal 2-constraint satisfaction and its
  implications*][Williams2005]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing Turing.MultiTapeTM

variable {α : Type*} {enc : α ↪ List Bool} {A B : Set α} {T T' : α → ℝ}

/-! ### Time bounds in parameters of the instance -/

/-- `A` is decidable within time `O(T a)` on the instance `a`: within time `c * T a + c`, for a
constant `c`, by a machine with a binary alphabet and finitely many states reading `enc a`, with
any space bound. Unlike `Cslib.Complexity.DTIME`, the bound is any real function of the instance,
not only a function of the length of `enc a`. -/
def DecidableInTimeO (A : Set α) (enc : α ↪ List Bool) (T : α → ℝ) : Prop :=
  ∃ c : ℕ, ∃ t s : α → ℕ, (∀ a, (t a : ℝ) ≤ c * T a + c) ∧ DecidableInTimeAndSpace A enc t s

/-- Weakening the bound of `Cslib.Complexity.DecidableInTimeO` up to constants. -/
theorem DecidableInTimeO.mono (h : DecidableInTimeO A enc T) (c : ℕ)
    (hT : ∀ a, T a ≤ c * T' a + c) (hT' : ∀ a, 0 ≤ T' a) : DecidableInTimeO A enc T' := by
  obtain ⟨c₀, t, s, ht, h⟩ := h
  refine ⟨c₀ * c + c₀, t, s, fun a => (ht a).trans ?_, h⟩
  have h₁ := mul_le_mul_of_nonneg_left (hT a) (Nat.cast_nonneg c₀ : (0 : ℝ) ≤ c₀)
  have h₂ := mul_nonneg (Nat.cast_nonneg c₀ : (0 : ℝ) ≤ c₀) (hT' a)
  push_cast
  nlinarith

/-- **`DTIME` in terms of `DecidableInTimeO`.** For a bound that is a function of the length of
the encoded instance, `Cslib.Complexity.DecidableInTimeO` is membership in
`Cslib.Complexity.DTIME`. -/
theorem mem_DTIME_iff_decidableInTimeO {t : ℕ → ℕ} :
    A ∈ DTIME enc t ↔ DecidableInTimeO A enc fun a => t (enc a).length := by
  constructor
  · rintro ⟨c₁, c₂, s, h⟩
    refine ⟨c₁ + c₂, _, _, fun a => ?_, h⟩
    push_cast
    nlinarith [(Nat.cast_nonneg (t (enc a).length) : (0 : ℝ) ≤ _),
      (Nat.cast_nonneg c₂ : (0 : ℝ) ≤ _), (Nat.cast_nonneg c₁ : (0 : ℝ) ≤ _)]
  · rintro ⟨c, t', s, ht', h⟩
    have ht : ∀ a, t' a ≤ c * t (enc a).length + c := fun a => by
      have := ht' a
      simp only at this
      exact_mod_cast this
    obtain ⟨k, h⟩ := ComputableInTimeAndSpace.exists_space_linear h
    exact ⟨c, c, fun n => k * (c * t n + c) + k,
      ComputableInTimeAndSpace.mono h ht fun a => by
        have := Nat.mul_le_mul_left k (ht a)
        simp only
        omega⟩

section Machines

/-! The machine combinators of the library are stated for `Type`. -/

variable {α : Type} {enc : α ↪ List Bool} {A B : Set α} {T : α → ℝ}

/-- A decider within time `O(T)` is a decider within time and space `O(t)`, for a bound `t`
within `O(T)`. -/
theorem DecidableInTimeO.exists_computableInO (h : DecidableInTimeO A enc T) :
    ∃ (g : α → Bool) (t : α → ℕ) (c : ℕ), ComputableInO g enc encBool t t ∧
      (∀ a, a ∈ A ↔ g a = true) ∧ ∀ a, (t a : ℝ) ≤ c * T a + c := by
  obtain ⟨c, t, s, ht, h⟩ := h
  obtain ⟨g, hg, hA⟩ := decidableInTimeAndSpace_iff.mp h
  obtain ⟨k, hg⟩ := ComputableInTimeAndSpace.exists_space_linear hg
  obtain ⟨d, hg⟩ := ComputableInTimeAndSpace.exists_computableTidilyInTimeAndSpace hg
  refine ⟨g, t, c, .of_tidy <| ComputableTidilyInO.of_bounds hg (2 + 3 * k + d + d * k + d)
    (fun a => ?_) (fun a => ?_) (fun a => ?_), hA, ht⟩
  all_goals
    have e : (2 + 3 * k + d + d * k + d) * (t a + 1) = 2 * t a + 3 * (k * t a + k) + d +
        (2 + d * t a + d * (k * t a + k + 1) + d * t a) := by ring
    try simp only [encBool_apply, List.length_singleton]
    omega

/-- A decider within time `O(t)`, for `t ≤ T`, decides within time `O(T)`. -/
theorem DecidableInTimeO.of_computableInO {g : α → Bool} {t S : α → ℕ}
    (hg : ComputableInO g enc encBool t S) (hA : ∀ a, a ∈ A ↔ g a = true)
    (hT : ∀ a, (t a : ℝ) ≤ T a) : DecidableInTimeO A enc T := by
  have hg := hg.tidy
  obtain ⟨c, hg, -⟩ := hg
  refine ⟨c, _, _, fun a => ?_,
    decidableInTimeAndSpace_iff.mpr ⟨g, hg.computableInTimeAndSpace, hA⟩⟩
  push_cast
  nlinarith [hT a, (Nat.cast_nonneg c : (0 : ℝ) ≤ c)]

/-- **Restriction to a set decided in polynomial time.** If `p` is computable in polynomial time
and `B` is decidable within time `O(T)`, then the instances of `B` satisfying `p` are decidable
within time `O(T)` on instances satisfying `p`, plus a polynomial in the length of the encoded
instance: the decider tests `p` first, and rejects at once when it fails. -/
theorem DecidableInTimeO.inter {p : α → Bool} (hp : ComputableInPolyTime p enc encBool)
    (hB : DecidableInTimeO B enc T) (hT : ∀ a, 0 ≤ T a) :
    ∃ e : ℕ, DecidableInTimeO ({a | p a = true} ∩ B) enc
      fun a => (if p a = true then T a else 0) + ((enc a).length + 1) ^ e := by
  have hp := hp.tidy
  obtain ⟨g, t, c, hg, hgB, ht⟩ := hB.exists_computableInO
  have hg := hg.tidy
  obtain ⟨d, _, hp⟩ := hp.exists_degree
  have h := hp.inO.ite hg (ComputableTidilyInO.const false)
  refine ⟨d + 1, DecidableInTimeO.mono (T := fun a => ((((enc a).length + 1) ^ d +
    if p a then t a else (enc a).length : ℕ) : ℝ))
    (DecidableInTimeO.of_computableInO (.of_tidy h) (fun a => ?_) fun a => le_rfl) (c + 2)
    (fun a => ?_) fun a => ?_⟩
  · simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, hgB]
    cases p a <;> simp
  · have hL : ((enc a).length : ℝ) + 1 ≤ ((enc a).length + 1) ^ (d + 1) := by
      have := one_le_pow₀ (M₀ := ℝ) (n := d) (by linarith [(Nat.cast_nonneg (enc a).length :
        (0 : ℝ) ≤ _)] : (1 : ℝ) ≤ (enc a).length + 1)
      rw [pow_succ]
      nlinarith [(Nat.cast_nonneg (enc a).length : (0 : ℝ) ≤ _)]
    have hd : (((enc a).length : ℝ) + 1) ^ d ≤ ((enc a).length + 1) ^ (d + 1) :=
      pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg (enc a).length : (0 : ℝ) ≤ _)])
        (Nat.le_succ d)
    have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg c
    have hpos : (0 : ℝ) ≤ ((enc a).length + 1) ^ (d + 1) := by positivity
    split_ifs with hpa
    · push_cast
      nlinarith [ht a, hT a]
    · push_cast
      nlinarith
  · split_ifs
    · exact add_nonneg (hT a) (by positivity)
    · positivity

end Machines

/-! ### Exponential and subexponential time -/

/-- `A` is decidable within time `2 ^ (δ μ a)` times a polynomial in the length of the encoded
instance: within time `O(2 ^ (δ μ a) * (L + 1) ^ e)` for some `e`, on instances `a` with encoding
of length `L`. -/
def DecidableInExpTime (A : Set α) (enc : α ↪ List Bool) (μ : α → ℕ) (δ : ℝ) : Prop :=
  ∃ e : ℕ, DecidableInTimeO A enc fun a => 2 ^ (δ * μ a) * ((enc a).length + 1) ^ e

/-- `A` is decidable in subexponential time in `μ`: within time `2 ^ (δ μ a)` times a polynomial in
the length of the encoded instance, for every `δ > 0`. The decider may depend on `δ`, so this is
weaker than a single decider within time `2 ^ o(μ a)`; it is the negation of the quantifier pattern
of the exponential time hypothesis. -/
def DecidableInSubexpTime (A : Set α) (enc : α ↪ List Bool) (μ : α → ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → DecidableInExpTime A enc μ δ

/-- Larger exponents allow more problems. -/
theorem DecidableInExpTime.mono {μ : α → ℕ} {δ δ' : ℝ} (h : DecidableInExpTime A enc μ δ)
    (hδ : δ ≤ δ') : DecidableInExpTime A enc μ δ' := by
  obtain ⟨e, h⟩ := h
  refine ⟨e, h.mono 1 (fun a => ?_) fun a => by positivity⟩
  have h₁ : (2 : ℝ) ^ (δ * μ a) ≤ 2 ^ (δ' * μ a) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg _))
  have h₂ := mul_le_mul_of_nonneg_right h₁ (by positivity : (0 : ℝ) ≤ ((enc a).length + 1) ^ e)
  push_cast
  linarith

section Machines

variable {α : Type} {enc : α ↪ List Bool} {A B : Set α}

/-- A decider within time `O(t)`, for `t` within a constant times `2 ^ (δ μ a)` times a
polynomial, decides within time `2 ^ (δ μ a)` times a polynomial. -/
theorem DecidableInExpTime.of_computableInO {μ : α → ℕ} {δ : ℝ} {g : α → Bool}
    {t S : α → ℕ} (hg : ComputableInO g enc encBool t S) (hA : ∀ a, a ∈ A ↔ g a = true)
    (c e : ℕ) (ht : ∀ a, (t a : ℝ) ≤ c * (2 ^ (δ * μ a) * ((enc a).length + 1) ^ e)) :
    DecidableInExpTime A enc μ δ :=
  ⟨e, (DecidableInTimeO.of_computableInO hg hA ht).mono c
    (fun a => le_add_of_nonneg_right (Nat.cast_nonneg c)) fun a => by positivity⟩

/-- **Restriction to a set decided in polynomial time**, for exponential bounds with `δ ≥ 0`. -/
theorem DecidableInExpTime.inter {μ : α → ℕ} {δ : ℝ} {p : α → Bool}
    (hp : ComputableInPolyTime p enc encBool) (h : DecidableInExpTime B enc μ δ)
    (hδ : 0 ≤ δ) : DecidableInExpTime ({a | p a = true} ∩ B) enc μ δ := by
  obtain ⟨e, h⟩ := h
  obtain ⟨e', h⟩ := h.inter hp fun a => by positivity
  refine ⟨e + e', h.mono 2 (fun a => ?_) fun a => by positivity⟩
  have hL : (1 : ℝ) ≤ (enc a).length + 1 := by
    linarith [(Nat.cast_nonneg (enc a).length : (0 : ℝ) ≤ _)]
  have h₁ : (1 : ℝ) ≤ 2 ^ (δ * μ a) := Real.one_le_rpow (by norm_num) (by positivity)
  have h₂ : (((enc a).length : ℝ) + 1) ^ e ≤ ((enc a).length + 1) ^ (e + e') :=
    pow_le_pow_right₀ hL (Nat.le_add_right e e')
  have h₃ : (((enc a).length : ℝ) + 1) ^ e' ≤ ((enc a).length + 1) ^ (e + e') :=
    pow_le_pow_right₀ hL (Nat.le_add_left e' e)
  have h₄ := mul_le_mul_of_nonneg_left h₂ (by positivity : (0 : ℝ) ≤ 2 ^ (δ * μ a))
  have h₅ : (((enc a).length : ℝ) + 1) ^ (e + e') ≤
      2 ^ (δ * μ a) * ((enc a).length + 1) ^ (e + e') :=
    le_mul_of_one_le_left (by positivity) h₁
  have h₆ : (if p a = true then 2 ^ (δ * μ a) * (((enc a).length : ℝ) + 1) ^ e else 0) ≤
      2 ^ (δ * μ a) * ((enc a).length + 1) ^ (e + e') := by
    split_ifs
    · exact h₄
    · positivity
  push_cast
  nlinarith

end Machines

/-! ### `k`-SAT and the exponential time hypotheses -/

/-- `k`-SAT: the satisfiable formulas whose clauses have at most `k` literals. -/
def KSAT (k : ℕ) : Set (CNF ℕ) := {φ | (∀ c ∈ φ, c.length ≤ k) ∧ φ.Satisfiable}

theorem KSAT_three : KSAT 3 = ThreeSAT := rfl

theorem KSAT_subset_SAT (k : ℕ) : KSAT k ⊆ SAT := fun _ h => h.2

/-- The exponent `s_k` of `k`-SAT [ImpagliazzoPaturi2001]: the infimum of the `δ ≥ 0` for which
`k`-SAT is decidable within time `2 ^ (δ n)` times a polynomial in the length of the encoded
formula, on formulas with `n` variables. Exhaustive search puts `1` in this set, so `s_k ∈ [0, 1]`
(`Cslib.Complexity.satExponent_le_one`). -/
noncomputable def satExponent (k : ℕ) : ℝ :=
  sInf {δ | 0 ≤ δ ∧ DecidableInExpTime (KSAT k) encCNF CNF.numVars δ}

/-- **The exponential time hypothesis** [ImpagliazzoPaturi2001]: for some `δ > 0`, 3SAT is not
decidable within time `2 ^ (δ n)` times any polynomial in the length of the encoded formula, on
formulas with `n` variables. -/
def ETH : Prop := ∃ δ : ℝ, 0 < δ ∧ ¬DecidableInExpTime ThreeSAT encCNF CNF.numVars δ

/-- **The strong exponential time hypothesis** [ImpagliazzoPaturi2001]: for every `ε > 0` there is
a width `k` such that `k`-SAT is not decidable within time `2 ^ ((1 - ε) n)` times any polynomial in
the length of the encoded formula, on formulas with `n` variables. -/
def SETH : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ¬DecidableInExpTime (KSAT k) encCNF CNF.numVars (1 - ε)

/-- The exponential time hypothesis says that 3SAT is not decidable in subexponential time in the
number of variables. -/
theorem ETH_iff_not_decidableInSubexpTime :
    ETH ↔ ¬DecidableInSubexpTime ThreeSAT encCNF CNF.numVars := by
  simp only [ETH, DecidableInSubexpTime, not_forall, exists_prop]

/-! ### Orthogonal vectors -/

/-- Two bit vectors are orthogonal when no coordinate is `true` in both. Missing coordinates of a
shorter vector count as `false`. -/
def OV.Orthogonal (a b : List Bool) : Prop := ∀ i, a.getD i false = false ∨ b.getD i false = false

/-- Orthogonality only depends on the coordinates of the first vector. -/
theorem OV.orthogonal_iff_forall_lt {a b : List Bool} :
    OV.Orthogonal a b ↔ ∀ i < a.length, a.getD i false = false ∨ b.getD i false = false :=
  ⟨fun h i _ => h i, fun h i => if hi : i < a.length then h i hi else
    Or.inl (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)]; rfl)⟩

instance (a b : List Bool) : Decidable (OV.Orthogonal a b) :=
  decidable_of_iff _ OV.orthogonal_iff_forall_lt.symm

/-- **The orthogonal vectors problem**: the pairs `(A, B)` of lists of bit vectors with an
orthogonal pair of vectors `a ∈ A` and `b ∈ B`. -/
def OV : Set (List (List Bool) × List (List Bool)) :=
  {p | ∃ a ∈ p.1, ∃ b ∈ p.2, OV.Orthogonal a b}

instance : DecidablePred (· ∈ OV) := fun p =>
  decidable_of_iff (∃ a ∈ p.1, ∃ b ∈ p.2, OV.Orthogonal a b) Iff.rfl

/-- Instances of the orthogonal vectors problem, encoded as pairs of lists of bit vectors. -/
def encOV : List (List Bool) × List (List Bool) ↪ List Bool :=
  encPair (encList encBits) (encList encBits)

/-- The dimension of an instance of the orthogonal vectors problem: the length of its longest
vector. -/
def OV.dim (p : List (List Bool) × List (List Bool)) : ℕ :=
  listMax List.length (p.1 ++ p.2)

/-- **The orthogonal vectors hypothesis**, in its moderate-dimension form: for every `ε > 0`, the
orthogonal vectors problem is not decidable within time `N ^ (2 - ε)` times any polynomial in the
dimension `d`, on instances of `N` vectors. The low-dimension form, for dimension `c log N` with a
constant `c` depending on `ε`, is stronger and is not stated here. -/
def OVH : Prop := ∀ ε : ℝ, 0 < ε → ∀ e : ℕ, ¬DecidableInTimeO OV encOV
  fun p => ((p.1.length + p.2.length : ℕ) : ℝ) ^ (2 - ε) * (OV.dim p + 1) ^ e

end Cslib.Complexity
