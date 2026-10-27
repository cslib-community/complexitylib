/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Formula.Poly
public import Complexity.Computability.Circuit.Boolean.Formula.Restriction
public import Complexity.Computability.Languages.Slice
public import Complexity.Computability.MCSP.Partial
public import Complexity.Computability.MCSP.SuccinctNP
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Complexity.Foundations.Combinatorics.FiniteCover.Basic
import Complexity.Foundations.Combinatorics.MajorityVote
import Cslib.Computability.Circuit.Boolean.Counting
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Sum

/-!
# Formula Magnification for Succinct, Partial, and Approximate MCSP

This module formalizes the De Morgan formula hardness magnification results of Oliveira and
Santhanam [OliveiraSanthanam2018]:
* **Lemma 16** ([OliveiraSanthanam2018, Section 3.1, Lemma 16, p. 14]): the two-stage magnification
  lemma connecting `Cslib.SuccinctMCSP` and `Cslib.PartialMCSP` to approximate MCSP
  (`Cslib.ApproxMCSP`, corresponding to `(1, 1 - δ)-MCSP[s]` in
  [OliveiraSanthanam2018, Appendix A, Definition 41, p. 34]) and `Cslib.GapMCSP`.
* **Contrapositive of Lemma 16 and Theorem 1(i) / Theorem 17(i)**
  ([OliveiraSanthanam2018, Section 1.2, Theorem 1 (i), p. 5; Section 3.1, Lemma 16 and
  Theorem 17 (i), pp. 14–15]): packaging Lemma 16 with `SuccinctMCSP ∈ NP`
  (`Cslib.SuccinctMCSP.mem_NP`) into `SuccinctMCSP ∉ FormulaPolyOn SuccinctMCSP.enc` and
  `NP SuccinctMCSP.enc ⊄ FormulaPolyOn SuccinctMCSP.enc` (`NP ⊄ Formula[poly]`), both in the
  general-parameter form underlying Theorem 17(i)/(iii) and specialized to polynomially bounded
  parameters `s₂, k` for Theorem 1(i) / Theorem 17(i).
* **Lemma 26 and one-sided Theorem 27** ([OliveiraSanthanam2018, Section 3.3, Lemma 26 and
  Theorem 27, p. 21]; compare [OliveiraSanthanam2018, Section 1.2, Theorem 5, p. 8]): deterministic
  counting form of Lemma 26 and one-sided zero-error average-case De Morgan formula magnification
  from `MCSP[s]` to `SuccinctMCSP` and `NP ⊄ FormulaPolyOn`.

## Source Statements (ECCC TR18-139)

Verbatim from [OliveiraSanthanam2018, Section 3.1, Lemma 16, p. 14]:

> **Lemma 16** (Magnification Lemma for Formulas). Let s : ℕ → ℕ and δ : ℕ → [0, 1/2) be
> constructive functions, where s(n) ≥ n. Consider the promise problem
> Π[s, δ] = (1, 1 − δ)-MCSP[s], where for every N = 2ⁿ,
> Π^yes_N = {y ∈ {0,1}^N | ∃ circuit of size ≤ s(n) that computes fn(y)},
> Π^no_N = {y ∈ {0,1}^N | ∄ circuit of size ≤ s(n) that (1 − δ(n))-approximates fn(y)}.
> Then, for every function ℓ : ℕ → ℕ, if Π[s, δ] cannot be computed by formulas of size
> N · ℓ(n), then there is a sequence {f_{m(n)}}_{n≥1} of m(n)-bit functions in NP that
> cannot be computed by formulas of size ≤ ℓ(n), where
> m(n) = Θ((n · s(n) · log s(n))/δ(n)).

Verbatim from [OliveiraSanthanam2018, Section 3.1, Theorem 17, p. 15] (also stated as
[OliveiraSanthanam2018, Section 1.2, Theorem 1, pp. 5–6], with proof *"Immediate from Lemma 16."*):

> **Theorem 17** (Magnification of Weak Formula Lower Bounds). For convenience, let
> Π[s, δ] = (1, 1 − δ)-MCSP[s]. The following implications hold.
> (i) Let s(n) = n^k and δ(n) = n^{−k}, where k ∈ ℕ. If Π[s, δ] ∉ Formula[N · (log N)^{O(1)}]
>     then there is L ∈ NP over m-bit inputs such that L ∉ Formula[poly(m)].
> (ii) For the same choice of parameters, if Π[s, δ] ∉ Formula[N^{1+ε}] for some ε > 0, then
>     there is L ∈ NP over m-bit inputs and δ > 0 such that L ∉ Formula[2^{m^δ}].
> (iii) Let s(n) = 2^{o(n)} and δ(n) = 2^{−o(n)}. If Π[s, δ] ∉ Formula[N^{1+ε}] for some ε > 0,
>     then there is L ∈ NP over m-bit inputs such that L ∉ Formula[poly(m)].

Verbatim from [OliveiraSanthanam2018, Section 1.2, Theorem 5, p. 8],
[OliveiraSanthanam2018, Section 3.3, Lemma 26 and Theorem 27, p. 21], and
[OliveiraSanthanam2018, Appendix A, Definition 43, p. 34]:

> **Theorem 5.** If MCSP[2^{√n}] on N-bit inputs cannot be solved on average with zero error by
> formulas of size o(N), then NP does not have polynomial size formulas.

> **Lemma 26.** Let n ≤ s(n) ≤ 2^{o(n)} and t(n) = 4s(n) log s(n). Let I be a random collection
> of t(n) pairs of the form (x_i, b_i), where each b_i ∼ {0, 1}, and all x_i are fixed but
> distinct elements of {0, 1}^n. Then, for every n sufficiently large,
> Pr_I[ There is a circuit of size ≤ s(n) consistent with I ] < 2^{−n}.

> **Theorem 27** (Magnification from sub-linear average-case lower bounds for MCSP). Let C be a
> typical circuit class, and consider MCSP[s] for a size parameter n ≤ s(n) ≤ 2^{o(n)}. Assume
> that there exists δ > 0 such that solving MCSP[s] on average on N-bit inputs requires C-circuits
> of size Ω(N^δ). Then there is a language L in NP such that L on inputs of length
> m = Θ(n · s(n) · log s(n)) requires C-circuits of size ℓ(m) = 2^{Ω(n)}.

> **Definition 43** (Average-case MCSP [HS17]). We say that MCSP-C[s] is computed on average by a
> device D (an algorithm or a family of circuits) if for every large enough n, the following holds:
> • D is never incorrect. For each y ∈ {0, 1}^{2^n}, D(y) ∈ {MCSP-C\[s\](y), “?”}.
> • D rarely outputs “?”. Pr_{z∼{0,1}^{2^n}}[D(z) ∈ {0, 1}] ≥ 1 − 1/n.
> We say that MCSP-C[s] is average-case hard for a class of devices A if no D ∈ A computes
> MCSP-C[s] on average.

Here [OliveiraSanthanam2018, Appendix A, Definition 41, p. 34] defines `(α, β)-MCSP[s]` for
`α, β ∈ (1/2, 1]` using "`γ`-approximates" to mean `Pr_x[ψ(x) = f(x)] ≥ γ`, so `(1, 1 - δ)-MCSP[s]`
is the `α = 1`, `β = 1 - δ` specialization. For average-case MCSP, Section 1.2 (p. 8) discusses
zero-error average-case algorithms informally (never wrong, `Pr[A(x) = ?] ≤ 1/2`), Definition 43
(Appendix A, p. 34) formalizes three-valued devices `D(y) ∈ {MCSP-C[s](y), "?"}` with
`Pr_z[D(z) ∈ {0, 1}] ≥ 1 - 1/n`, and the proof of Theorem 27 (Section 3.3, p. 21) constructs such a
device `C_n` from a `{0, 1}`-valued circuit `D_m` for `Succinct-MCSP[s, t]` by outputting `0` when
`D_m` outputs `0` and `"?"` otherwise. Our Lean hypotheses
(`exists_formula_zero_error_average_case_of_sample`,
`not_NP_subset_FormulaPolyOn_of_zero_error_average_case_hard`) are stated directly in terms of these
one-sided `{0, 1}`-valued formulas `F` (accepting all yes-instances in `GapMCSP.yesSet s` and
accepting at most `2 ^ (2 ^ n - r)` truth tables overall): any three-valued Definition 43 device `D`
induces the one-sided predicate `F(T) = decide (D(T) ≠ 0)` with `r = 1` once `1/n` plus the
yes-instance fraction is at most `1/2`, modulo the formula encoding of three-valued outputs.

## Comparison Between ECCC TR18-139 and This Module

1. **Circuit-Size Thresholds (`s` vs. `s₁ ≤ s₂`)**: ECCC Lemma 16 and Theorem 17 use a single
   circuit-size threshold `s(n)` for both `Π^yes_N` and `Π^no_N`. Here we allow distinct yes/no
   thresholds `s₁ n ≤ s₂ n` (`s₁ = s₂ = s` recovers the source setting).
2. **Error Parameter (`δ(n) ∈ [0, 1/2)` vs. `1 / k n` with `1 ≤ k n`)**: ECCC Lemma 16 takes a
   real-valued function `δ : ℕ → [0, 1/2)`. In the end-to-end theorems we parameterize the error
   by an integer function `k : ℕ → ℕ` with `1 ≤ k n` corresponding to `δ(n) = 1 / k n` (and also
   provide the real-parameter Stage 2 amplification `exists_seed_tuple_of_one_sided_error_real` and
   `exists_formula_separating_gapMCSP_of_succinctMCSP_real` using `⌈1 / δ⌉₊`).
3. **Strict vs. Non-Strict No-Instances**: In ECCC Definition 41 (Appendix A, p. 34), "`(1 - δ(n))`-
   approximates" means agreement on at least `(1 - δ(n)) ⋅ 2^n` inputs, so `Π^no_N` requires every
   circuit of size `≤ s(n)` to agree with `fn(y)` on strictly fewer than `(1 - δ(n)) ⋅ 2^n` inputs.
   Here `ApproxMCSP.noSet s₂ k` requires `k n * card(Agree) ≤ (k n - 1) * 2 ^ n` (non-strict `≤`),
   which contains the strict no-set, making the separation and contrapositive magnification
   theorems at least as strong.
4. **Target Representation (`Succinct-Π[s, t]` vs. `Finset` Samples in `SuccinctMCSP`)**: The proof
   of ECCC Lemma 16 (p. 14) reduces `Π[s, δ]` to `Succinct-Π[s, t]`, an explicit Succinct-MCSP
   encoding of `t(n) = 3 s(n) log s(n) / δ(n)` input-output samples (with possible repetition).
   Here `SuccinctMCSP.Instance.ofFunction` deduplicates a `Finset (BitString n)` sample `S` into a
   canonical sorted list of `m = S.card` samples of exact encoded length
   `SuccinctMCSP.ofFunctionEncLength n m (s₂ n) = 4 * n + 3 + m * (8 * n + 10) + s₂ n`. Because
   deduplicating `q = k n * (M + 2)` independent samples `ω : Fin q → BitString n` into
   `Finset.univ.image ω` can have any cardinality `m ≤ k n * (M + 2)`, our end-to-end theorems
   quantify over `m ≤ k n * (M + 2)` (with maximum encoded length `approxMCSPQueryEncLength`). We
   also provide `exists_formula_separating_gapMCSP_of_partialMCSP` bridging to
   `Cslib.PartialMCSP.Instance.restrictTable`.
5. **Circuit Model and Counting Bound (`s^{O(s)}` vs. `computableFunctionsLogBound`)**: ECCC Lemma
   16 and Lemma 26 count fan-in-two Boolean circuits of size at most `s(n)`. Here small functions
   are `computableFunctions n s` (defined via `Cslib.Circuits.complexity interpretation`), and
   `card_computableFunctions_le_two_pow` bounds `(computableFunctions n s).card ≤ 2 ^ M` with
   `M = computableFunctionsLogBound n s = (s + 1) * (2 * Nat.clog 2 (n + s + 1) + 3)` from
   `Cslib.Circuits.Boolean.card_computableFunctions_mul_factorial_le`.
6. **Conclusion (`FormulaPolyOn` and `NP ⊄ FormulaPolyOn` in Theorem 1/17 and Theorem 5/27)**:
   Generalizing the word-level formula projection
   (`exists_formula_ofFunction_SuccinctMCSP_of_agrees`) to any language `L : Language Bool`
   agreeing with `SuccinctMCSP` along `SuccinctMCSP.enc` connects Lemma 16 and Theorem 27 directly
   to `FormulaSIZEOn SuccinctMCSP.enc` and `FormulaPolyOn SuccinctMCSP.enc`
   (`Complexity.Computability.Circuit.Boolean.Formula.Poly`). Combining with `SuccinctMCSP.mem_NP`
   yields both the general-parameter magnification to
   `NP SuccinctMCSP.enc ⊄ FormulaPolyOn SuccinctMCSP.enc`
   (`not_NP_subset_FormulaPolyOn_of_approxMCSP_hard`) and the polynomially-bounded-parameter
   `N · (log N)^{O(1)}` magnification (`not_NP_subset_FormulaPolyOn_of_approxMCSP_poly_hard`,
   matching Theorem 1(i) / Theorem 17(i)), as well as the zero-error average-case magnification
   (`not_NP_subset_FormulaPolyOn_of_zero_error_average_case_hard`, matching Lemma 26 and Theorem 5 /
   Theorem 27).

## Main definitions

* `Cslib.Circuits.Boolean.evalWord`, `Cslib.Circuits.Boolean.succinctWord`: word-level formula
  projections for `SuccinctMCSP.enc`.
* `Cslib.ApproxMCSP.noSet`, `Cslib.ApproxMCSP`: the approximate `(1, 1 - 1 / k)-MCSP` promise
  problem [OliveiraSanthanam2018, Appendix A, Definition 41, p. 34].
* `Cslib.Circuits.Boolean.computableFunctionsLogBound`: explicit `s log(n + s)` exponent bound
  `(s + 1) * (2 * Nat.clog 2 (n + s + 1) + 3)` for `(computableFunctions n s).card`.
* `Cslib.Circuits.Boolean.approxMCSPQueryEncLength`,
  `Cslib.Circuits.Boolean.avgCaseMCSPQueryEncLength`: encoded query lengths for the worst-case
  (Lemma 16 / Theorem 17) and zero-error average-case (Lemma 26 / Theorem 27) reductions.

## Main results

* `Cslib.Circuits.Boolean.evalWord_succinctWord`,
  `Cslib.Circuits.Boolean.leafSize_le_one_of_mem_succinctWord`,
  `Cslib.Circuits.Boolean.exists_formula_ofFunction_SuccinctMCSP_of_agrees`,
  `Cslib.Circuits.Boolean.exists_formula_ofFunction_SuccinctMCSP`: leaf-size-preserving substitution
  into a slice formula of `SuccinctMCSP`.
* `Cslib.Circuits.Boolean.exists_formula_all_ofFunction_SuccinctMCSP_of_agrees`,
  `Cslib.Circuits.Boolean.exists_formula_all_ofFunction_SuccinctMCSP`,
  `Cslib.Circuits.Boolean.exists_formula_separating_gapMCSP_of_queryList`,
  `Cslib.Circuits.Boolean.exists_mem_lt_formulaSize_succinctMCSP_of_queryList`: deterministic
  multi-query formula projection (building block for
  [OliveiraSanthanam2018, Section 3.1, Lemma 16, p. 14]).
* `Cslib.Circuits.Boolean.two_pow_mul_pred_pow_lt`,
  `Cslib.Circuits.Boolean.exists_seed_tuple_of_one_sided_error`,
  `Cslib.Circuits.Boolean.exists_seed_tuple_of_one_sided_error_real`: finite-probability Adleman
  derandomization lemma from `Cslib.exists_cover_of_scaled_card_lt`.
* `Cslib.Circuits.Boolean.exists_formula_separating_gapMCSP_of_succinctMCSP`,
  `Cslib.Circuits.Boolean.exists_formula_separating_gapMCSP_of_succinctMCSP_real`,
  `Cslib.Circuits.Boolean.exists_lt_formulaSize_succinctMCSP_of_gapMCSP`,
  `Cslib.Circuits.Boolean.exists_formula_separating_gapMCSP_of_partialMCSP`: Stage 2 derandomization
  of an assumed one-sided sample projection
  ([OliveiraSanthanam2018, Section 3.1, Lemma 16, p. 14]).
* `Cslib.Circuits.Boolean.card_computableFunctions_le_two_pow`,
  `Cslib.Circuits.Boolean.card_le_two_mul_filter_notMem_succinctMCSP`,
  `Cslib.Circuits.Boolean.exists_formula_separating_approxMCSP_of_succinctMCSP`,
  `Cslib.Circuits.Boolean.exists_lt_formulaSize_succinctMCSP_of_approxMCSP`,
  `Cslib.Circuits.Boolean.exists_formula_separating_approxMCSP_of_succinctMCSP_inst`,
  `Cslib.Circuits.Boolean.exists_lt_formulaSize_succinctMCSP_of_approxMCSP_inst`: Stage 1 random
  sampling and end-to-end approximate `(1, 1 - 1 / k)-MCSP` formula magnification
  [OliveiraSanthanam2018, Section 3.1, Lemma 16, p. 14].
* `Cslib.Circuits.Boolean.exists_formula_separating_approxMCSP_of_mem_FormulaSIZEOn`,
  `Cslib.Circuits.Boolean.not_succinctMCSP_mem_FormulaPolyOn_of_approxMCSP_hard`,
  `Cslib.Circuits.Boolean.not_NP_subset_FormulaPolyOn_of_approxMCSP_hard`,
  `Cslib.Circuits.Boolean.exists_poly_formula_separating_approxMCSP_of_mem_FormulaPolyOn`,
  `Cslib.Circuits.Boolean.not_succinctMCSP_mem_FormulaPolyOn_of_approxMCSP_poly_hard`,
  `Cslib.Circuits.Boolean.not_NP_subset_FormulaPolyOn_of_approxMCSP_poly_hard`: packaging Lemma 16
  with `SuccinctMCSP.mem_NP` into `SuccinctMCSP ∉ FormulaPolyOn SuccinctMCSP.enc` and
  `NP ⊄ FormulaPolyOn` (general-parameter contrapositive of Lemma 16 underlying Theorem 17(i)/(iii),
  and Theorem 1(i) / Theorem 17(i) for polynomially bounded parameters)
  [OliveiraSanthanam2018, Section 1.2, Theorem 1 (i), p. 5; Section 3.1, Lemma 16 and
  Theorem 17 (i), pp. 14–15].
* `Cslib.Circuits.Boolean.card_filter_agreesOn_eq_two_pow`,
  `Cslib.Circuits.Boolean.card_filter_ofFunction_mem_succinctMCSP_le`,
  `Cslib.Circuits.Boolean.card_filter_ofFunction_mem_succinctMCSP_le_two_pow`,
  `Cslib.Circuits.Boolean.exists_formula_zero_error_average_case_of_sample`,
  `Cslib.Circuits.Boolean.exists_formula_zero_error_average_case_of_agrees`,
  `Cslib.Circuits.Boolean.exists_formula_zero_error_average_case_of_succinctMCSP`,
  `Cslib.Circuits.Boolean.lt_formulaSize_succinctMCSP_of_zero_error_average_case`,
  `Cslib.Circuits.Boolean.not_succinctMCSP_mem_FormulaPolyOn_of_zero_error_average_case_hard`,
  `Cslib.Circuits.Boolean.not_NP_subset_FormulaPolyOn_of_zero_error_average_case_hard`:
  one-sided zero-error average-case formula magnification from `MCSP[s]` to `SuccinctMCSP` and
  `NP ⊄ FormulaPolyOn` [OliveiraSanthanam2018, Section 3.3, Lemma 26 and Theorem 27, p. 21;
  compare Section 1.2, Theorem 5, p. 8].

## References

* [I. C. Oliveira, R. Santhanam, *Hardness Magnification for Natural
  Problems*][OliveiraSanthanam2018]
-/

@[expose] public section

namespace Cslib

open Circuits Circuits.Boolean Turing.MultiTapeTM

namespace Circuits.Boolean

/-! ### Word-level projections by leaf-size-`≤ 1` De Morgan formulas -/

/-- Evaluate a list of De Morgan formulas on a bitstring `T` to produce a binary word. -/
def evalWord {N : ℕ} (fs : List (Formula signature N)) (T : BitString N) : List Bool :=
  fs.map fun F => F.eval interpretation T

@[simp] theorem evalWord_nil {N : ℕ} (T : BitString N) :
    evalWord ([] : List (Formula signature N)) T = [] :=
  rfl

@[simp] theorem evalWord_cons {N : ℕ} (F : Formula signature N)
    (fs : List (Formula signature N)) (T : BitString N) :
    evalWord (F :: fs) T = F.eval interpretation T :: evalWord fs T :=
  rfl

@[simp] theorem evalWord_append {N : ℕ} (fs₁ fs₂ : List (Formula signature N)) (T : BitString N) :
    evalWord (fs₁ ++ fs₂) T = evalWord fs₁ T ++ evalWord fs₂ T := by
  simp only [evalWord, List.map_append]

@[simp] theorem length_evalWord {N : ℕ} (fs : List (Formula signature N)) (T : BitString N) :
    (evalWord fs T).length = fs.length := by
  simp only [evalWord, List.length_map]

/-- A fixed binary word `w` lifted to a list of constant De Morgan formulas on `N` inputs. -/
def constWord (N : ℕ) (w : List Bool) : List (Formula signature N) :=
  w.map Formula.const

@[simp] theorem evalWord_constWord {N : ℕ} (w : List Bool) (T : BitString N) :
    evalWord (constWord N w) T = w := by
  simp only [evalWord, constWord, List.map_map, Function.comp_def, Formula.eval_const, List.map_id']

/-- Lift `Turing.MultiTapeTM.frame` to a list of De Morgan formulas: each formula `F` becomes
`[Formula.const true, F]`, terminated by `[Formula.const false]`. -/
def frameWord {N : ℕ} (fs : List (Formula signature N)) : List (Formula signature N) :=
  fs.flatMap (fun F => [Formula.const true, F]) ++ [Formula.const false]

@[simp] theorem evalWord_frameWord {N : ℕ} (fs : List (Formula signature N)) (T : BitString N) :
    evalWord (frameWord fs) T = frame (evalWord fs T) := by
  induction fs with
  | nil => rfl
  | cons F fs ih =>
    have hcons : frameWord (F :: fs) = Formula.const true :: F :: frameWord fs := rfl
    rw [hcons, evalWord_cons, evalWord_cons, Formula.eval_const, ih, evalWord_cons, frame_cons]

/-- Lift `Turing.MultiTapeTM.encPair` to two lists of De Morgan formulas. -/
def pairWord {N : ℕ} (fs₁ fs₂ : List (Formula signature N)) : List (Formula signature N) :=
  frameWord fs₁ ++ fs₂

@[simp] theorem evalWord_pairWord {N : ℕ} (fs₁ fs₂ : List (Formula signature N))
    (T : BitString N) :
    evalWord (pairWord fs₁ fs₂) T = frame (evalWord fs₁ T) ++ evalWord fs₂ T := by
  simp only [pairWord, evalWord_append, evalWord_frameWord]

/-- The formula word on `2 ^ n` variables encoding a single sample `(List.ofFn y, f y)` where
`f = (MCSP.truthTable n).symm T`: the input bits `List.ofFn y` are constants and the output bit
`f y = T (BitString.equivFin n y)` is a single input leaf. -/
def sampleWord (n : ℕ) (y : BitString n) : List (Formula signature (2 ^ n)) :=
  pairWord (constWord (2 ^ n) (List.ofFn y)) [Formula.input (BitString.equivFin n y)]

@[simp] theorem evalWord_sampleWord (n : ℕ) (y : BitString n) (T : BitString (2 ^ n)) :
    evalWord (sampleWord n y) T =
      encPair encBits encBool (List.ofFn y, ((MCSP.truthTable n).symm T) y) := by
  simp only [sampleWord, evalWord_pairWord, evalWord_constWord, evalWord_cons, evalWord_nil,
    Formula.eval_input, encPair_apply, encBits_apply, encBool_apply, MCSP.truthTable_symm_apply]

/-- The formula word on `2 ^ n` variables whose evaluation on a truth table `T` equals
`SuccinctMCSP.enc (SuccinctMCSP.Instance.ofFunction ((MCSP.truthTable n).symm T) S s)`. -/
def succinctWord (n : ℕ) (S : Finset (BitString n)) (s : ℕ) : List (Formula signature (2 ^ n)) :=
  pairWord
    (pairWord (constWord (2 ^ n) (encUnary n))
      (((BitString.enum n).filter (· ∈ S)).flatMap fun y => frameWord (sampleWord n y)))
    (constWord (2 ^ n) (encUnary s))

private theorem evalWord_flatMap_sampleWord (n : ℕ) (l : List (BitString n))
    (T : BitString (2 ^ n)) :
    evalWord (l.flatMap fun y => frameWord (sampleWord n y)) T =
      encList (encPair encBits encBool)
        (l.map fun y => (List.ofFn y, ((MCSP.truthTable n).symm T) y)) := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.flatMap_cons, evalWord_append, evalWord_frameWord, evalWord_sampleWord, ih,
      List.map_cons, encList_cons]

/-- Evaluating `succinctWord n S s` on a truth table `T : BitString (2 ^ n)` produces the exact
encoding `SuccinctMCSP.enc (SuccinctMCSP.Instance.ofFunction ((MCSP.truthTable n).symm T) S s)`. -/
@[simp] theorem evalWord_succinctWord (n : ℕ) (S : Finset (BitString n)) (s : ℕ)
    (T : BitString (2 ^ n)) :
    evalWord (succinctWord n S s) T =
      SuccinctMCSP.enc
        (SuccinctMCSP.Instance.ofFunction ((MCSP.truthTable n).symm T) S s) := by
  rw [SuccinctMCSP.enc_apply, SuccinctMCSP.toRaw_apply, SuccinctMCSP.rawSamples_ofFunction]
  simp only [succinctWord, evalWord_pairWord, evalWord_constWord, evalWord_flatMap_sampleWord,
    encPair_apply, SuccinctMCSP.Instance.ofFunction]

private theorem leafSize_le_one_of_mem_constWord {N : ℕ} {w : List Bool}
    {F : Formula signature N} (hF : F ∈ constWord N w) : F.leafSize ≤ 1 := by
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp hF
  simp

private theorem leafSize_le_one_of_mem_frameWord {N : ℕ} {fs : List (Formula signature N)}
    (hfs : ∀ G ∈ fs, G.leafSize ≤ 1) {F : Formula signature N} (hF : F ∈ frameWord fs) :
    F.leafSize ≤ 1 := by
  rcases List.mem_append.mp hF with hF | hF
  · obtain ⟨G, hG, hFG⟩ := List.mem_flatMap.mp hF
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hFG
    rcases hFG with rfl | rfl
    · simp
    · exact hfs F hG
  · simp only [List.mem_singleton] at hF
    subst hF
    simp

private theorem leafSize_le_one_of_mem_pairWord {N : ℕ} {fs₁ fs₂ : List (Formula signature N)}
    (h₁ : ∀ G ∈ fs₁, G.leafSize ≤ 1) (h₂ : ∀ G ∈ fs₂, G.leafSize ≤ 1)
    {F : Formula signature N} (hF : F ∈ pairWord fs₁ fs₂) : F.leafSize ≤ 1 := by
  rcases List.mem_append.mp hF with hF | hF
  · exact leafSize_le_one_of_mem_frameWord h₁ hF
  · exact h₂ F hF

private theorem leafSize_le_one_of_mem_sampleWord {n : ℕ} {y : BitString n}
    {F : Formula signature (2 ^ n)} (hF : F ∈ sampleWord n y) : F.leafSize ≤ 1 := by
  refine leafSize_le_one_of_mem_pairWord (fun _ h => leafSize_le_one_of_mem_constWord h)
    (fun G hG => ?_) hF
  simp only [List.mem_singleton] at hG
  subst hG
  simp

/-- Every formula in `succinctWord n S s` has leaf size at most `1` (it is either a constant or a
single input leaf). -/
theorem leafSize_le_one_of_mem_succinctWord {n : ℕ} {S : Finset (BitString n)} {s : ℕ}
    {F : Formula signature (2 ^ n)} (hF : F ∈ succinctWord n S s) : F.leafSize ≤ 1 := by
  refine leafSize_le_one_of_mem_pairWord
    (fun G hG => leafSize_le_one_of_mem_pairWord
      (fun _ h => leafSize_le_one_of_mem_constWord h)
      (fun H hH => ?_) hG)
    (fun _ h => leafSize_le_one_of_mem_constWord h) hF
  obtain ⟨y, -, hHy⟩ := List.mem_flatMap.mp hH
  exact leafSize_le_one_of_mem_frameWord (fun _ h => leafSize_le_one_of_mem_sampleWord h) hHy

/-- The length of `succinctWord n S s` is `SuccinctMCSP.ofFunctionEncLength n S.card s`. -/
@[simp] theorem length_succinctWord (n : ℕ) (S : Finset (BitString n)) (s : ℕ) :
    (succinctWord n S s).length = SuccinctMCSP.ofFunctionEncLength n S.card s := by
  have h := congrArg List.length (evalWord_succinctWord n S s (fun _ => false))
  simpa only [length_evalWord, SuccinctMCSP.length_enc_ofFunction] using h

open Classical in
/-- **Leaf-size-preserving substitution into a language slice.** If every formula in
`fs : List (Formula signature N)` has leaf size at most `1`, then membership of `evalWord fs T` in
any language `L : Set (List Bool)` is computed by a De Morgan formula on `N` variables of leaf size
at most `formulaSize (Language.slice L fs.length)`. -/
theorem exists_formula_of_evalWord {N : ℕ} (fs : List (Formula signature N))
    (hfs : ∀ F ∈ fs, F.leafSize ≤ 1) (L : Set (List Bool)) :
    ∃ F : Formula signature N,
      (∀ T : BitString N, F.eval interpretation T = decide (evalWord fs T ∈ L)) ∧
      F.leafSize ≤ formulaSize (Language.slice L fs.length) := by
  obtain ⟨G, hG, hGleaf⟩ := exists_computes_leafSize_eq (Language.slice L fs.length)
  let sub : Fin fs.length → Formula signature N := fun i => fs[i.1]'i.2
  refine ⟨G.bind sub, fun T => ?_, ?_⟩
  · rw [Formula.eval_bind, hG]
    have heq : (List.ofFn fun i : Fin fs.length => (sub i).eval interpretation T) =
        evalWord fs T := by
      calc (List.ofFn fun i : Fin fs.length => (sub i).eval interpretation T)
          = (List.ofFn sub).map (fun F => F.eval interpretation T) :=
            (List.map_ofFn (f := sub) (g := fun F => F.eval interpretation T)).symm
        _ = fs.map (fun F => F.eval interpretation T) := by
            rw [show List.ofFn sub = fs from List.ofFn_getElem]
        _ = evalWord fs T := rfl
    change decide ((List.ofFn fun i : Fin fs.length => (sub i).eval interpretation T) ∈ L) = _
    rw [heq]
  · exact (G.leafSize_bind_le fun i => hfs (sub i) (List.getElem_mem i.2)).trans hGleaf.le

open Classical in
/-- **Single-query `SuccinctMCSP` formula projection for any agreeing language.** If
`L : Language Bool` agrees with `SuccinctMCSP` along `SuccinctMCSP.enc`
(`∀ x, x ∈ SuccinctMCSP ↔ SuccinctMCSP.enc x ∈ L`), then for any `n`, `S : Finset (BitString n)`,
and `s`, there is a De Morgan formula `F` on `2 ^ n` variables that decides whether
`SuccinctMCSP.Instance.ofFunction ((MCSP.truthTable n).symm T) S s ∈ SuccinctMCSP` and has leaf
size at most `formulaSize (L.slice (SuccinctMCSP.ofFunctionEncLength n S.card s))`. -/
theorem exists_formula_ofFunction_SuccinctMCSP_of_agrees {L : Language Bool}
    (hag : ∀ x, x ∈ SuccinctMCSP ↔ SuccinctMCSP.enc x ∈ L)
    (n : ℕ) (S : Finset (BitString n)) (s : ℕ) :
    ∃ F : Formula signature (2 ^ n),
      (∀ T : BitString (2 ^ n),
        F.eval interpretation T =
          decide (SuccinctMCSP.Instance.ofFunction
            ((MCSP.truthTable n).symm T) S s ∈ SuccinctMCSP)) ∧
      F.leafSize ≤
        formulaSize (L.slice (SuccinctMCSP.ofFunctionEncLength n S.card s)) := by
  obtain ⟨F, hFeval, hFleaf⟩ := exists_formula_of_evalWord (succinctWord n S s)
    (fun _ h => leafSize_le_one_of_mem_succinctWord h) L
  refine ⟨F, fun T => ?_, ?_⟩
  · rw [hFeval T, evalWord_succinctWord]
    exact decide_eq_decide.mpr (hag _).symm
  · rwa [length_succinctWord] at hFleaf

open Classical in
/-- **Single-query `SuccinctMCSP` formula projection.** For any `n`, `S : Finset (BitString n)`, and
`s`, there is a De Morgan formula `F` on `2 ^ n` variables that decides whether
`SuccinctMCSP.Instance.ofFunction ((MCSP.truthTable n).symm T) S s ∈ SuccinctMCSP` and has leaf
size at most the formula size of the `(ofFunctionEncLength n S.card s)`-bit slice of
`SuccinctMCSP.enc '' SuccinctMCSP`. -/
theorem exists_formula_ofFunction_SuccinctMCSP (n : ℕ) (S : Finset (BitString n)) (s : ℕ) :
    ∃ F : Formula signature (2 ^ n),
      (∀ T : BitString (2 ^ n),
        F.eval interpretation T =
          decide (SuccinctMCSP.Instance.ofFunction
            ((MCSP.truthTable n).symm T) S s ∈ SuccinctMCSP)) ∧
      F.leafSize ≤
        formulaSize (Language.slice (SuccinctMCSP.enc '' SuccinctMCSP)
          (SuccinctMCSP.ofFunctionEncLength n S.card s)) :=
  exists_formula_ofFunction_SuccinctMCSP_of_agrees
    (fun _ => SuccinctMCSP.enc.injective.mem_set_image.symm) n S s

/-! ### Deterministic multi-query formula projection (building block for Stage 2) -/

open Classical in
/-- **Multi-query `SuccinctMCSP` conjunction formula for any agreeing language.** If
`L : Language Bool` agrees with `SuccinctMCSP` along `SuccinctMCSP.enc`, then for any list
`qs : List (Finset (BitString n) × ℕ)` of sample sets and thresholds, there is a De Morgan formula
on `2 ^ n` variables that decides whether all queries `(S, s) ∈ qs` are in `SuccinctMCSP` and has
leaf size at most the sum of the corresponding slice formula sizes of `L`. -/
theorem exists_formula_all_ofFunction_SuccinctMCSP_of_agrees {L : Language Bool}
    (hag : ∀ x, x ∈ SuccinctMCSP ↔ SuccinctMCSP.enc x ∈ L) (n : ℕ)
    (qs : List (Finset (BitString n) × ℕ)) :
    ∃ F : Formula signature (2 ^ n),
      (∀ T : BitString (2 ^ n),
        F.eval interpretation T =
          decide (∀ p ∈ qs, SuccinctMCSP.Instance.ofFunction
            ((MCSP.truthTable n).symm T) p.1 p.2 ∈ SuccinctMCSP)) ∧
      F.leafSize ≤
        (qs.map fun p =>
          formulaSize (L.slice (SuccinctMCSP.ofFunctionEncLength n p.1.card p.2))).sum := by
  induction qs with
  | nil =>
    refine ⟨Formula.const true, fun T => ?_, by simp⟩
    simp
  | cons q qs ih =>
    obtain ⟨F₁, hF₁eval, hF₁leaf⟩ :=
      exists_formula_ofFunction_SuccinctMCSP_of_agrees hag n q.1 q.2
    obtain ⟨F₂, hF₂eval, hF₂leaf⟩ := ih
    refine ⟨F₁.and F₂, fun T => ?_, ?_⟩
    · rw [Formula.eval_and, hF₁eval T, hF₂eval T]
      simp
    · simp only [Formula.leafSize_and, List.map_cons, List.sum_cons]
      exact Nat.add_le_add hF₁leaf hF₂leaf

open Classical in
/-- **Multi-query `SuccinctMCSP` conjunction formula.** Given any list
`qs : List (Finset (BitString n) × ℕ)` of sample sets and thresholds, there is a De Morgan formula
on `2 ^ n` variables that decides whether all queries `(S, s) ∈ qs` are in `SuccinctMCSP` and has
leaf size at most the sum of the corresponding slice formula sizes. -/
theorem exists_formula_all_ofFunction_SuccinctMCSP (n : ℕ)
    (qs : List (Finset (BitString n) × ℕ)) :
    ∃ F : Formula signature (2 ^ n),
      (∀ T : BitString (2 ^ n),
        F.eval interpretation T =
          decide (∀ p ∈ qs, SuccinctMCSP.Instance.ofFunction
            ((MCSP.truthTable n).symm T) p.1 p.2 ∈ SuccinctMCSP)) ∧
      F.leafSize ≤
        (qs.map fun p =>
          formulaSize (Language.slice (SuccinctMCSP.enc '' SuccinctMCSP)
            (SuccinctMCSP.ofFunctionEncLength n p.1.card p.2))).sum :=
  exists_formula_all_ofFunction_SuccinctMCSP_of_agrees
    (fun _ => SuccinctMCSP.enc.injective.mem_set_image.symm) n qs

/-- **Deterministic multi-query formula projection for `GapMCSP`** (building block for
[OliveiraSanthanam2018, Section 3.1, Lemma 16, p. 14]). If a deterministic list `qs` of `(S, s)`
queries has `s₁ n ≤ s` for every `(S, s) ∈ qs` and rejects every `T ∈ GapMCSP.noSet s₂` on at least
one query in `qs`, and each queried slice of `SuccinctMCSP` has formula size at most `L`, then
`GapMCSP[s₁, s₂]` on `2 ^ n`-bit inputs is separated by a De Morgan formula of leaf size at most
`qs.length * L`. -/
theorem exists_formula_separating_gapMCSP_of_queryList {s₁ s₂ : ℕ → ℕ} {n L : ℕ}
    (qs : List (Finset (BitString n) × ℕ))
    (hs : ∀ p ∈ qs, s₁ n ≤ p.2)
    (hno : ∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.noSet s₂ →
      ∃ p ∈ qs, SuccinctMCSP.Instance.ofFunction
        ((MCSP.truthTable n).symm T) p.1 p.2 ∉ SuccinctMCSP)
    (hL : ∀ p ∈ qs,
      formulaSize (Language.slice (SuccinctMCSP.enc '' SuccinctMCSP)
        (SuccinctMCSP.ofFunctionEncLength n p.1.card p.2)) ≤ L) :
    ∃ F : Formula signature (2 ^ n),
      F.leafSize ≤ qs.length * L ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s₁ →
        F.eval interpretation T = true) ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.noSet s₂ →
        F.eval interpretation T = false) := by
  classical
  obtain ⟨F, hFeval, hFleaf⟩ := exists_formula_all_ofFunction_SuccinctMCSP n qs
  have hsum : (qs.map fun p =>
      formulaSize (Language.slice (SuccinctMCSP.enc '' SuccinctMCSP)
        (SuccinctMCSP.ofFunctionEncLength n p.1.card p.2))).sum ≤ qs.length * L := by
    have hmap := List.sum_le_length_nsmul
      (qs.map fun p => formulaSize (Language.slice (SuccinctMCSP.enc '' SuccinctMCSP)
        (SuccinctMCSP.ofFunctionEncLength n p.1.card p.2))) L (by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      exact hL p hp)
    simpa only [List.length_map, smul_eq_mul] using hmap
  refine ⟨F, hFleaf.trans hsum, fun T hyes => ?_, fun T hnoT => ?_⟩
  · rw [hFeval T, decide_eq_true_eq]
    intro p hp
    have hcomp : complexity interpretation (single ((MCSP.truthTable n).symm T)) ≤ p.2 :=
      (GapMCSP.ofFn_mem_yesSet_iff.mp hyes).trans (hs p hp)
    exact SuccinctMCSP.ofFunction_mem_of_complexity_le hcomp p.1
  · rw [hFeval T, decide_eq_false_iff_not, not_forall]
    obtain ⟨p, hp, hnot⟩ := hno T hnoT
    exact ⟨p, fun h => hnot (h hp)⟩

/-- **Contrapositive deterministic multi-query formula projection** (building block for
[OliveiraSanthanam2018, Section 3.1, Lemma 16, p. 14]). If every De Morgan formula separating
`GapMCSP.yesSet s₁` and `GapMCSP.noSet s₂` on `2 ^ n`-bit inputs has leaf size strictly greater than
`qs.length * L`, then at least one query `p ∈ qs` maps to a slice of `SuccinctMCSP` with formula
size strictly greater than `L`. -/
theorem exists_mem_lt_formulaSize_succinctMCSP_of_queryList {s₁ s₂ : ℕ → ℕ} {n L : ℕ}
    (qs : List (Finset (BitString n) × ℕ))
    (hs : ∀ p ∈ qs, s₁ n ≤ p.2)
    (hno : ∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.noSet s₂ →
      ∃ p ∈ qs, SuccinctMCSP.Instance.ofFunction
        ((MCSP.truthTable n).symm T) p.1 p.2 ∉ SuccinctMCSP)
    (hged : ∀ F : Formula signature (2 ^ n),
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s₁ →
        F.eval interpretation T = true) →
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.noSet s₂ →
        F.eval interpretation T = false) →
      qs.length * L < F.leafSize) :
    ∃ p ∈ qs,
      L < formulaSize (Language.slice (SuccinctMCSP.enc '' SuccinctMCSP)
        (SuccinctMCSP.ofFunctionEncLength n p.1.card p.2)) := by
  by_contra! hle
  obtain ⟨F, hFleaf, hyes, hno'⟩ :=
    exists_formula_separating_gapMCSP_of_queryList qs hs hno hle
  exact (hged F hyes hno').not_ge hFleaf

/-- Querying the full domain `Finset.univ` shows that the `2 ^ n`-bit slice of `GapMCSP.yesSet s`
has formula size no larger than the `(ofFunctionEncLength n (2 ^ n) (s n))`-bit slice of
`SuccinctMCSP.enc '' SuccinctMCSP`. -/
theorem formulaSize_slice_yesSet_le (s : ℕ → ℕ) (n : ℕ) :
    formulaSize ((GapMCSP.yesSet s).slice (2 ^ n)) ≤
      formulaSize (Language.slice (SuccinctMCSP.enc '' SuccinctMCSP)
        (SuccinctMCSP.ofFunctionEncLength n (2 ^ n) (s n))) := by
  classical
  obtain ⟨F, hFeval, hFleaf⟩ :=
    exists_formula_ofFunction_SuccinctMCSP n (Finset.univ : Finset (BitString n)) (s n)
  have hcard : (Finset.univ : Finset (BitString n)).card = 2 ^ n := by
    simp [BitString]
  rw [hcard] at hFleaf
  refine (formulaSize_le fun T => ?_).trans hFleaf
  rw [Bool.eq_iff_iff, hFeval T, Language.slice_eq_true_iff, decide_eq_true_iff,
    SuccinctMCSP.ofFunction_univ_mem_iff, GapMCSP.ofFn_mem_yesSet_iff]
  simp [MCSP.mem_iff, MCSP.Instance.function]

/-! ### Stage 2: Finite-probability Adleman derandomization of a one-sided sample projection -/

private theorem two_mul_pow_le_succ_pow (m : ℕ) :
    2 * m ^ (m + 1) ≤ (m + 1) ^ (m + 1) := by
  rw [add_pow, Finset.sum_range_succ, Finset.sum_range_succ]
  simp only [Nat.cast_id]
  have h1 : m ^ (m + 1) * 1 ^ (m + 1 - (m + 1)) * (m + 1).choose (m + 1) = m ^ (m + 1) := by
    simp
  have h2 : m ^ m * 1 ^ (m + 1 - m) * (m + 1).choose m = m ^ (m + 1) + m ^ m := by
    have hsub : m + 1 - m = 1 := Nat.add_sub_cancel_left m 1
    rw [hsub, Nat.choose_succ_self_right, one_pow, mul_one, mul_add, mul_one, pow_succ]
  rw [h1, h2]
  omega

/-- **Elementary exponential inequality for Adleman amplification:** for every `k ≥ 1` and `N : ℕ`,
`2 ^ N * (k - 1) ^ (k * (N + 1)) < k ^ (k * (N + 1))`, corresponding to the real inequality
`2 ^ N * (1 - 1 / k) ^ (k * (N + 1)) < 1`. -/
theorem two_pow_mul_pred_pow_lt {N k : ℕ} (hk : 1 ≤ k) :
    2 ^ N * (k - 1) ^ (k * (N + 1)) < k ^ (k * (N + 1)) := by
  set m := k - 1
  have hm : m + 1 = k := Nat.sub_add_cancel hk
  have hbase : 2 * m ^ k ≤ k ^ k := by
    simpa only [hm] using two_mul_pow_le_succ_pow m
  have hpow : (2 * m ^ k) ^ (N + 1) ≤ (k ^ k) ^ (N + 1) :=
    Nat.pow_le_pow_left hbase (N + 1)
  rw [mul_pow, ← pow_mul, ← pow_mul] at hpow
  rcases eq_or_ne m 0 with hm0 | hm0
  · have hkt : k * (N + 1) ≠ 0 := Nat.mul_ne_zero (by omega) (Nat.succ_ne_zero N)
    rw [hm0, zero_pow hkt, mul_zero]
    exact Nat.pos_of_ne_zero (pow_ne_zero _ (by omega))
  · have hmpos : 0 < m ^ (k * (N + 1)) := Nat.pos_of_ne_zero (pow_ne_zero _ hm0)
    have h2pos : 0 < 2 ^ N := by positivity
    have hlt : 2 ^ N * m ^ (k * (N + 1)) < 2 ^ (N + 1) * m ^ (k * (N + 1)) := by
      rw [pow_succ]
      nlinarith
    exact hlt.trans_le hpow

/-- **Finite-probability Adleman amplification lemma.** If `no ⊆ BitString N` is a set of negative
inputs and, for every `T ∈ no`, at least a `1 / k`-fraction of the seeds `ω : Ω` satisfy
`Good T ω` (`Fintype.card Ω ≤ k * (Finset.univ.filter (Good T)).card`), then there exists a tuple
`ωs : Fin (k * (N + 1)) → Ω` of `k * (N + 1)` seeds such that every `T ∈ no` is witnessed by at
least one `ωs j`. Derived from `Cslib.exists_cover_of_scaled_card_lt`. -/
theorem exists_seed_tuple_of_one_sided_error {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {N k : ℕ} (hk : 1 ≤ k) (no : Finset (BitString N))
    (Good : BitString N → Ω → Prop) [∀ T ω, Decidable (Good T ω)]
    (hgood : ∀ T ∈ no, Fintype.card Ω ≤ k * (Finset.univ.filter (Good T)).card) :
    ∃ ωs : Fin (k * (N + 1)) → Ω, ∀ T ∈ no, ∃ j : Fin (k * (N + 1)), Good T (ωs j) := by
  classical
  have hcover : ∃ ωs : Fin (k * (N + 1)) → Ω, ∀ T : no, ∃ j, Good T.1 (ωs j) := by
    apply exists_cover_of_scaled_card_lt (fun ω (T : no) => Good T.1 ω) (k - 1) k (k * (N + 1))
    · intro ⟨T, hT⟩
      rw [Fintype.card_subtype_compl, Fintype.card_subtype]
      dsimp only
      have hg := hgood T hT
      have hle : (Finset.univ.filter (Good T)).card ≤ Fintype.card Ω :=
        Finset.card_le_univ _
      have hk1 : k * Fintype.card Ω = (k - 1) * Fintype.card Ω + Fintype.card Ω := by
        conv_lhs => rw [← Nat.sub_add_cancel hk, add_mul, one_mul]
      have hsub : k * (Fintype.card Ω - (Finset.univ.filter (Good T)).card) +
          k * (Finset.univ.filter (Good T)).card = k * Fintype.card Ω := by
        rw [← mul_add, Nat.sub_add_cancel hle]
      change k * (Fintype.card Ω - (Finset.univ.filter (Good T)).card) ≤ (k - 1) * Fintype.card Ω
      omega
    · have hno_card : Fintype.card no ≤ 2 ^ N := by
        rw [Fintype.card_coe]
        exact (Finset.card_le_univ no).trans (by simp [BitString])
      exact (Nat.mul_le_mul_right _ hno_card).trans_lt (two_pow_mul_pred_pow_lt hk)
  obtain ⟨ωs, hωs⟩ := hcover
  exact ⟨ωs, fun T hT => hωs ⟨T, hT⟩⟩

/-- **Real-parameter Adleman amplification lemma.** If `0 < δ` and every `T ∈ no` satisfies
`δ * Fintype.card Ω ≤ (Finset.univ.filter (Good T)).card`, then `⌈1 / δ⌉₊ * (N + 1)` seeds suffice
to witness every `T ∈ no`. -/
theorem exists_seed_tuple_of_one_sided_error_real {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {N : ℕ} {δ : ℝ} (hδ : 0 < δ) (no : Finset (BitString N))
    (Good : BitString N → Ω → Prop) [∀ T ω, Decidable (Good T ω)]
    (hgood : ∀ T ∈ no, δ * (Fintype.card Ω : ℝ) ≤ ((Finset.univ.filter (Good T)).card : ℝ)) :
    ∃ ωs : Fin (⌈1 / δ⌉₊ * (N + 1)) → Ω,
      ∀ T ∈ no, ∃ j : Fin (⌈1 / δ⌉₊ * (N + 1)), Good T (ωs j) := by
  have hk : 1 ≤ ⌈1 / δ⌉₊ := Nat.ceil_pos.mpr (by positivity)
  refine exists_seed_tuple_of_one_sided_error hk no Good fun T hT => ?_
  have hceil : 1 / δ ≤ (⌈1 / δ⌉₊ : ℝ) := Nat.le_ceil (1 / δ)
  have h1 : (1 : ℝ) ≤ (⌈1 / δ⌉₊ : ℝ) * δ := by
    rwa [div_le_iff₀ hδ] at hceil
  have h2 : (Fintype.card Ω : ℝ) ≤ (⌈1 / δ⌉₊ : ℝ) * ((Finset.univ.filter (Good T)).card : ℝ) := by
    calc (Fintype.card Ω : ℝ)
        = 1 * (Fintype.card Ω : ℝ) := (one_mul _).symm
      _ ≤ ((⌈1 / δ⌉₊ : ℝ) * δ) * (Fintype.card Ω : ℝ) :=
          mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _)
      _ = (⌈1 / δ⌉₊ : ℝ) * (δ * (Fintype.card Ω : ℝ)) := by ring
      _ ≤ (⌈1 / δ⌉₊ : ℝ) * ((Finset.univ.filter (Good T)).card : ℝ) :=
          mul_le_mul_of_nonneg_left (hgood T hT) (Nat.cast_nonneg _)
  exact_mod_cast h2

open Classical in
/-- **Stage 2 derandomization of an assumed one-sided sample projection (integer parameter `k`)**
([OliveiraSanthanam2018, Section 3.1, Lemma 16, p. 14]).
Suppose `s₁ n ≤ s`, `S : Ω → Finset (BitString n)` is a family of sample sets indexed by a finite
nonempty seed space `Ω` such that for every `T : BitString (2 ^ n)` with
`List.ofFn T ∈ GapMCSP.noSet s₂`, at least a `1 / k`-fraction of the seeds `ω : Ω` yield a
no-instance `SuccinctMCSP.Instance.ofFunction ((MCSP.truthTable n).symm T) (S ω) s ∉ SuccinctMCSP`,
and each queried slice of `SuccinctMCSP` has formula size at most `L`. Then `GapMCSP[s₁, s₂]` on
`2 ^ n`-bit inputs is separated by a De Morgan formula of leaf size at most
`k * (2 ^ n + 1) * L`. -/
theorem exists_formula_separating_gapMCSP_of_succinctMCSP {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {s₁ s₂ : ℕ → ℕ} {n s k L : ℕ} (hk : 1 ≤ k) (hs : s₁ n ≤ s)
    (S : Ω → Finset (BitString n))
    (hno : ∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.noSet s₂ →
      Fintype.card Ω ≤
        k * (Finset.univ.filter fun ω =>
          SuccinctMCSP.Instance.ofFunction
            ((MCSP.truthTable n).symm T) (S ω) s ∉ SuccinctMCSP).card)
    (hL : ∀ ω : Ω,
      formulaSize (Language.slice (SuccinctMCSP.enc '' SuccinctMCSP)
        (SuccinctMCSP.ofFunctionEncLength n (S ω).card s)) ≤ L) :
    ∃ F : Formula signature (2 ^ n),
      F.leafSize ≤ k * (2 ^ n + 1) * L ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s₁ →
        F.eval interpretation T = true) ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.noSet s₂ →
        F.eval interpretation T = false) := by
  let noFinset : Finset (BitString (2 ^ n)) :=
    Finset.univ.filter fun T => List.ofFn T ∈ GapMCSP.noSet s₂
  obtain ⟨ωs, hωs⟩ := exists_seed_tuple_of_one_sided_error hk noFinset
    (fun T ω => SuccinctMCSP.Instance.ofFunction
      ((MCSP.truthTable n).symm T) (S ω) s ∉ SuccinctMCSP)
    (fun T hT => hno T (Finset.mem_filter.mp hT).2)
  let qs : List (Finset (BitString n) × ℕ) := List.ofFn fun j => (S (ωs j), s)
  have hlen : qs.length = k * (2 ^ n + 1) := List.length_ofFn
  rw [← hlen]
  refine exists_formula_separating_gapMCSP_of_queryList qs
    (fun p hp => ?_) (fun T hnoT => ?_) (fun p hp => ?_)
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
    exact hs
  · have hmem : T ∈ noFinset := Finset.mem_filter.mpr ⟨Finset.mem_univ T, hnoT⟩
    obtain ⟨j, hj⟩ := hωs T hmem
    exact ⟨(S (ωs j), s), List.mem_ofFn.mpr ⟨j, rfl⟩, hj⟩
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
    exact hL (ωs j)

open Classical in
/-- **Stage 2 derandomization of an assumed one-sided sample projection (real error `δ > 0`)**
([OliveiraSanthanam2018, Section 3.1, Lemma 16, p. 14]).
If `S : Ω → Finset (BitString n)` rejects each `T ∈ GapMCSP.noSet s₂` with probability at least
`δ > 0` over a uniform seed `ω ∈ Ω`, and every queried slice of `SuccinctMCSP` has formula size at
most `L`, then `GapMCSP[s₁, s₂]` on `2 ^ n`-bit inputs is separated by a De Morgan formula of leaf
size at most `⌈1 / δ⌉₊ * (2 ^ n + 1) * L`. -/
theorem exists_formula_separating_gapMCSP_of_succinctMCSP_real
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {s₁ s₂ : ℕ → ℕ} {n s L : ℕ} {δ : ℝ} (hδ : 0 < δ) (hs : s₁ n ≤ s)
    (S : Ω → Finset (BitString n))
    (hno : ∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.noSet s₂ →
      δ * (Fintype.card Ω : ℝ) ≤
        ((Finset.univ.filter fun ω =>
          SuccinctMCSP.Instance.ofFunction
            ((MCSP.truthTable n).symm T) (S ω) s ∉ SuccinctMCSP).card : ℝ))
    (hL : ∀ ω : Ω,
      formulaSize (Language.slice (SuccinctMCSP.enc '' SuccinctMCSP)
        (SuccinctMCSP.ofFunctionEncLength n (S ω).card s)) ≤ L) :
    ∃ F : Formula signature (2 ^ n),
      F.leafSize ≤ ⌈1 / δ⌉₊ * (2 ^ n + 1) * L ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s₁ →
        F.eval interpretation T = true) ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.noSet s₂ →
        F.eval interpretation T = false) := by
  let noFinset : Finset (BitString (2 ^ n)) :=
    Finset.univ.filter fun T => List.ofFn T ∈ GapMCSP.noSet s₂
  obtain ⟨ωs, hωs⟩ := exists_seed_tuple_of_one_sided_error_real hδ noFinset
    (fun T ω => SuccinctMCSP.Instance.ofFunction
      ((MCSP.truthTable n).symm T) (S ω) s ∉ SuccinctMCSP)
    (fun T hT => hno T (Finset.mem_filter.mp hT).2)
  let qs : List (Finset (BitString n) × ℕ) := List.ofFn fun j => (S (ωs j), s)
  have hlen : qs.length = ⌈1 / δ⌉₊ * (2 ^ n + 1) := List.length_ofFn
  rw [← hlen]
  refine exists_formula_separating_gapMCSP_of_queryList qs
    (fun p hp => ?_) (fun T hnoT => ?_) (fun p hp => ?_)
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
    exact hs
  · have hmem : T ∈ noFinset := Finset.mem_filter.mpr ⟨Finset.mem_univ T, hnoT⟩
    obtain ⟨j, hj⟩ := hωs T hmem
    exact ⟨(S (ωs j), s), List.mem_ofFn.mpr ⟨j, rfl⟩, hj⟩
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
    exact hL (ωs j)

open Classical in
/-- **Contrapositive Stage 2 derandomization for `GapMCSP[s₁, s₂]`**
([OliveiraSanthanam2018, Section 3.1, Lemma 16, p. 14]). If every De Morgan formula separating
`GapMCSP.yesSet s₁` and `GapMCSP.noSet s₂` on `2 ^ n`-bit inputs has leaf size strictly greater
than `k * (2 ^ n + 1) * L`, then under an assumed one-sided sample projection
`S : Ω → Finset (BitString n)` some seed `ω : Ω` produces a slice of `SuccinctMCSP` with formula
size strictly greater than `L`. -/
theorem exists_lt_formulaSize_succinctMCSP_of_gapMCSP {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {s₁ s₂ : ℕ → ℕ} {n s k L : ℕ} (hk : 1 ≤ k) (hs : s₁ n ≤ s)
    (S : Ω → Finset (BitString n))
    (hno : ∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.noSet s₂ →
      Fintype.card Ω ≤
        k * (Finset.univ.filter fun ω =>
          SuccinctMCSP.Instance.ofFunction
            ((MCSP.truthTable n).symm T) (S ω) s ∉ SuccinctMCSP).card)
    (hged : ∀ F : Formula signature (2 ^ n),
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s₁ →
        F.eval interpretation T = true) →
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.noSet s₂ →
        F.eval interpretation T = false) →
      k * (2 ^ n + 1) * L < F.leafSize) :
    ∃ ω : Ω,
      L < formulaSize (Language.slice (SuccinctMCSP.enc '' SuccinctMCSP)
        (SuccinctMCSP.ofFunctionEncLength n (S ω).card s)) := by
  by_contra! hle
  obtain ⟨F, hFleaf, hyes, hno'⟩ :=
    exists_formula_separating_gapMCSP_of_succinctMCSP hk hs S hno hle
  exact (hged F hyes hno').not_ge hFleaf

open Classical in
/-- **Stage 2 derandomization of an assumed one-sided sample projection phrased via `PartialMCSP`**
([OliveiraSanthanam2018, Section 3.1, Lemma 16, p. 14]).
If `s₁ n ≤ s`, `S : Ω → Finset (BitString n)` rejects every `T : BitString (2 ^ n)` with
`List.ofFn T ∈ GapMCSP.noSet s₂` in the sense that
`PartialMCSP.Instance.restrictTable T (S ω) s ∉ PartialMCSP` on at least a `1 / k`-fraction of
`ω : Ω`, and every queried slice of `SuccinctMCSP` has formula size at most `L`, then
`GapMCSP[s₁, s₂]` on `2 ^ n`-bit inputs is separated by a De Morgan formula of leaf size at most
`k * (2 ^ n + 1) * L`. -/
theorem exists_formula_separating_gapMCSP_of_partialMCSP {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {s₁ s₂ : ℕ → ℕ} {n s k L : ℕ} (hk : 1 ≤ k) (hs : s₁ n ≤ s)
    (S : Ω → Finset (BitString n))
    (hno : ∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.noSet s₂ →
      Fintype.card Ω ≤
        k * (Finset.univ.filter fun ω =>
          PartialMCSP.Instance.restrictTable T (S ω) s ∉ PartialMCSP).card)
    (hL : ∀ ω : Ω,
      formulaSize (Language.slice (SuccinctMCSP.enc '' SuccinctMCSP)
        (SuccinctMCSP.ofFunctionEncLength n (S ω).card s)) ≤ L) :
    ∃ F : Formula signature (2 ^ n),
      F.leafSize ≤ k * (2 ^ n + 1) * L ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s₁ →
        F.eval interpretation T = true) ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.noSet s₂ →
        F.eval interpretation T = false) := by
  refine exists_formula_separating_gapMCSP_of_succinctMCSP hk hs S (fun T hT => ?_) hL
  simpa only [PartialMCSP.restrictTable_mem_iff] using hno T hT

end Circuits.Boolean

/-! ### Approximate `(1, 1 - 1 / k)-MCSP` and Stage 1 random-sampling projection -/

namespace ApproxMCSP

open MCSP Circuits.Boolean

/-- The no-instances of approximate `(1, 1 - 1 / k)-MCSP[s]`
[OliveiraSanthanam2018, Appendix A, Definition 41, p. 34]: the truth tables of `n`-input Boolean
functions `f` such that every function `g` of circuit complexity at most `s n` agrees with `f` on at
most a `(1 - 1 / k n)`-fraction of inputs
(`k n * (Finset.univ.filter fun x => g x = f x).card ≤ (k n - 1) * 2 ^ n`). -/
def noSet (s k : ℕ → ℕ) : Language Bool :=
  truthTableLanguage fun n =>
    {f | ∀ g ∈ computableFunctions n (s n),
      k n * (Finset.univ.filter fun x => g x = f x).card ≤ (k n - 1) * 2 ^ n}

/-- A `2 ^ n`-bit truth table `T` belongs to `ApproxMCSP.noSet s k` if and only if every
`g ∈ computableFunctions n (s n)` agrees with `(MCSP.truthTable n).symm T` on at most a
`(1 - 1 / k n)`-fraction of inputs. -/
@[simp] theorem ofFn_mem_noSet_iff {s k : ℕ → ℕ} {n : ℕ} {T : BitString (2 ^ n)} :
    List.ofFn T ∈ noSet s k ↔
      ∀ g ∈ computableFunctions n (s n),
        k n * (Finset.univ.filter fun x => g x = (truthTable n).symm T x).card ≤
          (k n - 1) * 2 ^ n :=
  ofFn_mem_truthTableLanguage

/-- When `1 ≤ k n`, every approximate `(1, 1 - 1 / k)-MCSP[s]` no-instance on `2 ^ n` bits is also a
worst-case `GapMCSP.noSet s` no-instance. -/
theorem ofFn_mem_gapMCSP_noSet_of_mem_noSet {s k : ℕ → ℕ} {n : ℕ} (hk : 1 ≤ k n)
    {T : BitString (2 ^ n)} (hT : List.ofFn T ∈ noSet s k) :
    List.ofFn T ∈ GapMCSP.noSet s := by
  rw [GapMCSP.ofFn_mem_noSet_iff]
  by_contra! hle
  have hmem : (truthTable n).symm T ∈ computableFunctions n (s n) :=
    mem_computableFunctions_iff_complexity_le.mpr hle
  have hcard := ofFn_mem_noSet_iff.mp hT _ hmem
  have hall : (Finset.univ.filter fun x : BitString n =>
      (truthTable n).symm T x = (truthTable n).symm T x).card = 2 ^ n := by
    simp [BitString]
  rw [hall] at hcard
  have h2pos : 0 < 2 ^ n := by positivity
  have hk1 : k n * 2 ^ n = (k n - 1) * 2 ^ n + 2 ^ n := by
    conv_lhs => rw [← Nat.sub_add_cancel hk, add_mul, one_mul]
  omega

/-- When `1 ≤ k n` for all `n`, `ApproxMCSP.noSet s k` is contained in `GapMCSP.noSet s`. -/
theorem noSet_le_gapMCSP_noSet {s k : ℕ → ℕ} (hk : ∀ n, 1 ≤ k n) :
    noSet s k ≤ GapMCSP.noSet s := by
  rintro w ⟨n, hn, hf⟩
  refine ⟨n, hn, ?_⟩
  change s n < complexity interpretation
    (single ((truthTable n).symm (fun i => w[(i : ℕ)]'(i.isLt.trans_eq hn.symm))))
  by_contra! hle
  have hmem : (truthTable n).symm (fun i => w[(i : ℕ)]'(i.isLt.trans_eq hn.symm)) ∈
      computableFunctions n (s n) :=
    mem_computableFunctions_iff_complexity_le.mpr hle
  have hcard := hf _ hmem
  have hall : (Finset.univ.filter fun x : BitString n =>
      (truthTable n).symm (fun i => w[(i : ℕ)]'(i.isLt.trans_eq hn.symm)) x =
      (truthTable n).symm (fun i => w[(i : ℕ)]'(i.isLt.trans_eq hn.symm)) x).card = 2 ^ n := by
    simp [BitString]
  rw [hall] at hcard
  have h2pos : 0 < 2 ^ n := by positivity
  have hk1 : k n * 2 ^ n = (k n - 1) * 2 ^ n + 2 ^ n := by
    conv_lhs => rw [← Nat.sub_add_cancel (hk n), add_mul, one_mul]
  omega

/-- When `s₁ n ≤ s₂ n` and `1 ≤ k n` for all `n`, no truth table is both a `GapMCSP.yesSet s₁`
yes-instance and an `ApproxMCSP.noSet s₂ k` no-instance. -/
theorem disjoint_yesSet_noSet {s₁ s₂ k : ℕ → ℕ} (hs : ∀ n, s₁ n ≤ s₂ n) (hk : ∀ n, 1 ≤ k n) :
    Disjoint (GapMCSP.yesSet s₁) (noSet s₂ k) :=
  (GapMCSP.disjoint_yesSet_noSet hs).mono_right (noSet_le_gapMCSP_noSet hk)

end ApproxMCSP

/-- **`ApproxMCSP[s₁, s₂, k]`** (`(1, 1 - 1 / k)-MCSP`
[OliveiraSanthanam2018, Appendix A, Definition 41, p. 34]): the approximate MCSP promise problem
whose yes-instances are truth tables of `n`-input Boolean functions with circuit complexity at most
`s₁ n` and whose no-instances are truth tables of functions that disagree with every function of
circuit complexity at most `s₂ n` on at least a `1 / k n`-fraction of inputs, when `s₁ n ≤ s₂ n`
and `1 ≤ k n` for all `n`. -/
def ApproxMCSP (s₁ s₂ k : ℕ → ℕ) (hs : ∀ n, s₁ n ≤ s₂ n) (hk : ∀ n, 1 ≤ k n) :
    Complexity.PromiseProblem (List Bool) where
  yes := GapMCSP.yesSet s₁
  no := ApproxMCSP.noSet s₂ k
  disjoint := ApproxMCSP.disjoint_yesSet_noSet hs hk

namespace ApproxMCSP

variable {s₁ s₂ k : ℕ → ℕ}
variable (hs : ∀ n, s₁ n ≤ s₂ n) (hk : ∀ n, 1 ≤ k n)

@[simp] theorem yes_eq : (ApproxMCSP s₁ s₂ k hs hk).yes = GapMCSP.yesSet s₁ := rfl

@[simp] theorem no_eq : (ApproxMCSP s₁ s₂ k hs hk).no = noSet s₂ k := rfl

end ApproxMCSP

namespace Circuits.Boolean

/-- An explicit `s log(n + s)` upper bound on `log₂ (computableFunctions n s).card`, derived from
`card_computableFunctions_mul_factorial_le`. -/
def computableFunctionsLogBound (n s : ℕ) : ℕ :=
  (s + 1) * (2 * Nat.clog 2 (n + s + 1) + 3)

/-- The number of `n`-input Boolean functions of De Morgan circuit complexity at most `s` is at most
`2 ^ computableFunctionsLogBound n s`. -/
theorem card_computableFunctions_le_two_pow (n s : ℕ) :
    (computableFunctions n s).card ≤ 2 ^ computableFunctionsLogBound n s := by
  set L := Nat.clog 2 (n + s + 1)
  have hns : n + s + 1 ≤ 2 ^ L := Nat.le_pow_clog (by decide) (n + s + 1)
  have hs1 : s + 1 ≤ 2 ^ L := (by omega : s + 1 ≤ n + s + 1).trans hns
  have hns0 : n + s ≤ 2 ^ L := (by omega : n + s ≤ n + s + 1).trans hns
  have hbase : 5 * (n + s + 1) ^ 2 ≤ 2 ^ (2 * L + 3) := by
    calc 5 * (n + s + 1) ^ 2
        ≤ 8 * (2 ^ L) ^ 2 := Nat.mul_le_mul (by decide) (Nat.pow_le_pow_left hns 2)
      _ = 2 ^ (2 * L + 3) := by
        rw [← pow_mul, pow_add]
        ring
  have hpow : (5 * (n + s + 1) ^ 2) ^ s ≤ 2 ^ (s * (2 * L + 3)) := by
    calc (5 * (n + s + 1) ^ 2) ^ s
        ≤ (2 ^ (2 * L + 3)) ^ s := Nat.pow_le_pow_left hbase s
      _ = 2 ^ (s * (2 * L + 3)) := by rw [← pow_mul, mul_comm]
  have hends : (s + 1) * (n + s) ≤ 2 ^ (2 * L + 3) := by
    calc (s + 1) * (n + s)
        ≤ 2 ^ L * 2 ^ L := Nat.mul_le_mul hs1 hns0
      _ = 2 ^ (2 * L) := by rw [← pow_add, two_mul]
      _ ≤ 2 ^ (2 * L + 3) := Nat.pow_le_pow_right (by decide) (by omega)
  calc (computableFunctions n s).card
      ≤ (computableFunctions n s).card * s.factorial :=
        Nat.le_mul_of_pos_right _ (Nat.factorial_pos s)
    _ ≤ (s + 1) * (5 * (n + s + 1) ^ 2) ^ s * (n + s) :=
        card_computableFunctions_mul_factorial_le n s
    _ = ((s + 1) * (n + s)) * (5 * (n + s + 1) ^ 2) ^ s := by ring
    _ ≤ 2 ^ (2 * L + 3) * 2 ^ (s * (2 * L + 3)) := Nat.mul_le_mul hends hpow
    _ = 2 ^ computableFunctionsLogBound n s := by
        rw [← pow_add, computableFunctionsLogBound]
        congr 1
        ring

open Classical in
/-- **Oliveira–Santhanam Stage 1: random-sampling union bound over `computableFunctions n s`
[OliveiraSanthanam2018, Section 3.1, Lemma 16, p. 14].**
Suppose `1 ≤ k`, `(computableFunctions n s).card ≤ 2 ^ M`, and `q = k * (M + 2)`. If every function
`g ∈ computableFunctions n s` agrees with `f : BooleanFunction n` on at most a
`(1 - 1 / k)`-fraction of inputs
(`k * (Finset.univ.filter fun x => g x = f x).card ≤ (k - 1) * 2 ^ n`), then at least half of all
`q`-tuples `ω : Fin q → BitString n` yield a no-instance
`SuccinctMCSP.Instance.ofFunction f (Finset.univ.image ω) s ∉ SuccinctMCSP`. -/
theorem card_le_two_mul_filter_notMem_succinctMCSP {n s k M : ℕ} (hk : 1 ≤ k)
    (hcard : (computableFunctions n s).card ≤ 2 ^ M)
    {f : BooleanFunction n}
    (hf : ∀ g ∈ computableFunctions n s,
      k * (Finset.univ.filter fun x => g x = f x).card ≤ (k - 1) * 2 ^ n) :
    Fintype.card (Fin (k * (M + 2)) → BitString n) ≤
      2 * (Finset.univ.filter fun ω : Fin (k * (M + 2)) → BitString n =>
        SuccinctMCSP.Instance.ofFunction f (Finset.univ.image ω) s ∉ SuccinctMCSP).card := by
  classical
  set q := k * (M + 2)
  let Agree (g : BooleanFunction n) : Finset (BitString n) :=
    Finset.univ.filter fun x => g x = f x
  let BadFor (g : BooleanFunction n) : Finset (Fin q → BitString n) :=
    Fintype.piFinset fun _ : Fin q => Agree g
  let Bad : Finset (Fin q → BitString n) :=
    Finset.univ.filter fun ω : Fin q → BitString n =>
      SuccinctMCSP.Instance.ofFunction f (Finset.univ.image ω) s ∈ SuccinctMCSP
  let Good : Finset (Fin q → BitString n) :=
    Finset.univ.filter fun ω : Fin q → BitString n =>
      SuccinctMCSP.Instance.ofFunction f (Finset.univ.image ω) s ∉ SuccinctMCSP
  have hsub : Bad ⊆ (computableFunctions n s).biUnion BadFor := by
    intro ω hω
    have hmem : SuccinctMCSP.Instance.ofFunction f (Finset.univ.image ω) s ∈ SuccinctMCSP :=
      (Finset.mem_filter.mp hω).2
    obtain ⟨g, hg, hag⟩ :=
      SuccinctMCSP.ofFunction_mem_iff_exists_mem_computableFunctions.mp hmem
    refine Finset.mem_biUnion.mpr ⟨g, hg, Fintype.mem_piFinset.mpr fun i => ?_⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hag (ω i) (Finset.mem_image_of_mem ω (Finset.mem_univ i))⟩
  have hBadFor_le (g : BooleanFunction n) (hg : g ∈ computableFunctions n s) :
      k ^ q * (BadFor g).card ≤ (k - 1) ^ q * (2 ^ n) ^ q := by
    have hc : (BadFor g).card = (Agree g).card ^ q := by
      simp [BadFor, Fintype.card_piFinset]
    rw [hc, ← mul_pow, ← mul_pow]
    exact Nat.pow_le_pow_left (hf g hg) q
  have hBad_le : k ^ q * Bad.card ≤ 2 ^ M * (k - 1) ^ q * (2 ^ n) ^ q := by
    calc k ^ q * Bad.card
        ≤ k ^ q * ((computableFunctions n s).biUnion BadFor).card :=
          Nat.mul_le_mul_left _ (Finset.card_le_card hsub)
      _ ≤ k ^ q * ∑ g ∈ computableFunctions n s, (BadFor g).card :=
          Nat.mul_le_mul_left _ Finset.card_biUnion_le
      _ = ∑ g ∈ computableFunctions n s, k ^ q * (BadFor g).card := Finset.mul_sum _ _ _
      _ ≤ ∑ _g ∈ computableFunctions n s, (k - 1) ^ q * (2 ^ n) ^ q :=
          Finset.sum_le_sum fun g hg => hBadFor_le g hg
      _ = (computableFunctions n s).card * ((k - 1) ^ q * (2 ^ n) ^ q) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ = (computableFunctions n s).card * (k - 1) ^ q * (2 ^ n) ^ q := by ring
      _ ≤ 2 ^ M * (k - 1) ^ q * (2 ^ n) ^ q :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hcard)
  have hΩpos : 0 < (2 ^ n) ^ q := by positivity
  have hlt : k ^ q * (2 * Bad.card) < k ^ q * (2 ^ n) ^ q := by
    calc k ^ q * (2 * Bad.card)
        = 2 * (k ^ q * Bad.card) := by ring
      _ ≤ 2 * (2 ^ M * (k - 1) ^ q * (2 ^ n) ^ q) := Nat.mul_le_mul_left 2 hBad_le
      _ = 2 ^ (M + 1) * (k - 1) ^ (k * ((M + 1) + 1)) * (2 ^ n) ^ q := by
          rw [pow_succ']
          ring
      _ < k ^ (k * ((M + 1) + 1)) * (2 ^ n) ^ q :=
          Nat.mul_lt_mul_of_pos_right (two_pow_mul_pred_pow_lt (N := M + 1) hk) hΩpos
      _ = k ^ q * (2 ^ n) ^ q := rfl
  have h2Bad : 2 * Bad.card < Fintype.card (Fin q → BitString n) := by
    have hlt' : 2 * Bad.card < (2 ^ n) ^ q := lt_of_mul_lt_mul_left hlt (Nat.zero_le _)
    simpa [Fintype.card_pi, BitString] using hlt'
  have hpart : Bad.card + Good.card = Fintype.card (Fin q → BitString n) := by
    simpa only [Bad, Good, Finset.card_univ] using
      Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (p := fun ω : Fin q → BitString n =>
          SuccinctMCSP.Instance.ofFunction f (Finset.univ.image ω) s ∈ SuccinctMCSP)
  change Fintype.card (Fin q → BitString n) ≤ 2 * Good.card
  omega

/-- **End-to-end Oliveira–Santhanam formula construction for approximate `(1, 1 - 1 / k)-MCSP`
[OliveiraSanthanam2018, Section 3.1, Lemma 16, p. 14].**
Suppose `1 ≤ k n`, `s₁ n ≤ s₂ n`, `(computableFunctions n (s₂ n)).card ≤ 2 ^ M`, and every
`(ofFunctionEncLength n m (s₂ n))`-bit slice of `SuccinctMCSP.enc '' SuccinctMCSP` with
`m ≤ k n * (M + 2)` has De Morgan formula size at most `L`. Then there exists a De Morgan formula
`F` on `2 ^ n` variables of leaf size at most `(2 ^ n + 1) * L` that separates
`GapMCSP.yesSet s₁` from `ApproxMCSP.noSet s₂ k` on `2 ^ n`-bit truth tables. -/
theorem exists_formula_separating_approxMCSP_of_succinctMCSP
    {s₁ s₂ k : ℕ → ℕ} {n M L : ℕ} (hk : 1 ≤ k n) (hs : s₁ n ≤ s₂ n)
    (hcard : (computableFunctions n (s₂ n)).card ≤ 2 ^ M)
    (hL : ∀ m ≤ k n * (M + 2),
      formulaSize (Language.slice (SuccinctMCSP.enc '' SuccinctMCSP)
        (SuccinctMCSP.ofFunctionEncLength n m (s₂ n))) ≤ L) :
    ∃ F : Formula signature (2 ^ n),
      F.leafSize ≤ (2 ^ n + 1) * L ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s₁ →
        F.eval interpretation T = true) ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ ApproxMCSP.noSet s₂ k →
        F.eval interpretation T = false) := by
  classical
  set q := k n * (M + 2)
  let noFinset : Finset (BitString (2 ^ n)) :=
    Finset.univ.filter fun T => List.ofFn T ∈ ApproxMCSP.noSet s₂ k
  have hno_card : Fintype.card noFinset ≤ 2 ^ (2 ^ n) := by
    rw [Fintype.card_coe]
    exact (Finset.card_le_univ noFinset).trans (by simp [BitString])
  obtain ⟨ωs, hωs⟩ := exists_forall_exists_apply_mem (Ω := Fin q → BitString n) hno_card
    (fun T : noFinset => Finset.univ.filter fun ω : Fin q → BitString n =>
      SuccinctMCSP.Instance.ofFunction
        ((MCSP.truthTable n).symm T.1) (Finset.univ.image ω) (s₂ n) ∉ SuccinctMCSP)
    (fun ⟨T, hT⟩ => card_le_two_mul_filter_notMem_succinctMCSP hk hcard
      (ApproxMCSP.ofFn_mem_noSet_iff.mp (Finset.mem_filter.mp hT).2))
  let qs : List (Finset (BitString n) × ℕ) :=
    List.ofFn fun j => (Finset.univ.image (ωs j), s₂ n)
  obtain ⟨F, hFeval, hFleaf⟩ := exists_formula_all_ofFunction_SuccinctMCSP n qs
  have hsum : (qs.map fun p =>
      formulaSize (Language.slice (SuccinctMCSP.enc '' SuccinctMCSP)
        (SuccinctMCSP.ofFunctionEncLength n p.1.card p.2))).sum ≤ (2 ^ n + 1) * L := by
    have hmap := List.sum_le_length_nsmul
      (qs.map fun p => formulaSize (Language.slice (SuccinctMCSP.enc '' SuccinctMCSP)
        (SuccinctMCSP.ofFunctionEncLength n p.1.card p.2))) L (by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
      refine hL (Finset.univ.image (ωs j)).card ?_
      calc (Finset.univ.image (ωs j)).card
          ≤ (Finset.univ : Finset (Fin q)).card := Finset.card_image_le
        _ = q := by simp)
    simpa only [qs, List.length_map, List.length_ofFn, smul_eq_mul] using hmap
  refine ⟨F, hFleaf.trans hsum, fun T hyes => ?_, fun T hnoT => ?_⟩
  · rw [hFeval T, decide_eq_true_eq]
    intro p hp
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
    have hcomp : complexity interpretation (single ((MCSP.truthTable n).symm T)) ≤ s₂ n :=
      (GapMCSP.ofFn_mem_yesSet_iff.mp hyes).trans hs
    exact SuccinctMCSP.ofFunction_mem_of_complexity_le hcomp _
  · rw [hFeval T, decide_eq_false_iff_not, not_forall]
    have hmem : T ∈ noFinset := Finset.mem_filter.mpr ⟨Finset.mem_univ T, hnoT⟩
    obtain ⟨j, hj⟩ := hωs ⟨T, hmem⟩
    have hj' : SuccinctMCSP.Instance.ofFunction
        ((MCSP.truthTable n).symm T) (Finset.univ.image (ωs j)) (s₂ n) ∉ SuccinctMCSP :=
      (Finset.mem_filter.mp hj).2
    exact ⟨(Finset.univ.image (ωs j), s₂ n), fun h => hj' (h (List.mem_ofFn.mpr ⟨j, rfl⟩))⟩

/-- **Contrapositive end-to-end formula hardness magnification for approximate `(1, 1 - 1 / k)-MCSP`
[OliveiraSanthanam2018, Section 3.1, Lemma 16, p. 14].**
If `1 ≤ k n`, `s₁ n ≤ s₂ n`, `(computableFunctions n (s₂ n)).card ≤ 2 ^ M`, and every De Morgan
formula separating `GapMCSP.yesSet s₁` and `ApproxMCSP.noSet s₂ k` on `2 ^ n`-bit truth tables has
leaf size strictly greater than `(2 ^ n + 1) * L`, then there exists `m ≤ k n * (M + 2)` such
that the `(ofFunctionEncLength n m (s₂ n))`-bit slice of `SuccinctMCSP.enc '' SuccinctMCSP` has
De Morgan formula size strictly greater than `L`. -/
theorem exists_lt_formulaSize_succinctMCSP_of_approxMCSP
    {s₁ s₂ k : ℕ → ℕ} {n M L : ℕ} (hk : 1 ≤ k n) (hs : s₁ n ≤ s₂ n)
    (hcard : (computableFunctions n (s₂ n)).card ≤ 2 ^ M)
    (hged : ∀ F : Formula signature (2 ^ n),
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s₁ →
        F.eval interpretation T = true) →
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ ApproxMCSP.noSet s₂ k →
        F.eval interpretation T = false) →
      (2 ^ n + 1) * L < F.leafSize) :
    ∃ m ≤ k n * (M + 2),
      L < formulaSize (Language.slice (SuccinctMCSP.enc '' SuccinctMCSP)
        (SuccinctMCSP.ofFunctionEncLength n m (s₂ n))) := by
  by_contra! hle
  obtain ⟨F, hFleaf, hyes, hno⟩ :=
    exists_formula_separating_approxMCSP_of_succinctMCSP hk hs hcard hle
  exact (hged F hyes hno).not_ge hFleaf

/-- **Instantiated Oliveira–Santhanam formula construction for `ApproxMCSP`
[OliveiraSanthanam2018, Section 3.1, Lemma 16, p. 14]**, with `M` instantiated to
`computableFunctionsLogBound n (s₂ n)` via `card_computableFunctions_le_two_pow`. Every queried
slice has encoded length
`SuccinctMCSP.ofFunctionEncLength n m (s₂ n) = 4 * n + 3 + m * (8 * n + 10) + s₂ n` with
`m ≤ k n * (computableFunctionsLogBound n (s₂ n) + 2)`, i.e. `O(k n ⋅ n ⋅ s₂ n ⋅ log(n + s₂ n))`
bits, matching the slice length `m(n) = Θ((n ⋅ s(n) ⋅ log s(n)) / δ(n))` of Lemma 16 for
`δ(n) = 1 / k n`. -/
theorem exists_formula_separating_approxMCSP_of_succinctMCSP_inst
    {s₁ s₂ k : ℕ → ℕ} {n L : ℕ} (hs : ∀ m, s₁ m ≤ s₂ m) (hk : ∀ m, 1 ≤ k m)
    (hL : ∀ m ≤ k n * (computableFunctionsLogBound n (s₂ n) + 2),
      formulaSize (Language.slice (SuccinctMCSP.enc '' SuccinctMCSP)
        (SuccinctMCSP.ofFunctionEncLength n m (s₂ n))) ≤ L) :
    ∃ F : Formula signature (2 ^ n),
      F.leafSize ≤ (2 ^ n + 1) * L ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ (ApproxMCSP s₁ s₂ k hs hk).yes →
        F.eval interpretation T = true) ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ (ApproxMCSP s₁ s₂ k hs hk).no →
        F.eval interpretation T = false) :=
  exists_formula_separating_approxMCSP_of_succinctMCSP (hk n) (hs n)
    (card_computableFunctions_le_two_pow n (s₂ n)) hL

/-- **Instantiated contrapositive formula hardness magnification for `ApproxMCSP`
[OliveiraSanthanam2018, Section 3.1, Lemma 16, p. 14]**, with `M` instantiated to
`computableFunctionsLogBound n (s₂ n)` via `card_computableFunctions_le_two_pow`. The resulting hard
slice of `SuccinctMCSP.enc '' SuccinctMCSP` has encoded length
`SuccinctMCSP.ofFunctionEncLength n m (s₂ n) = 4 * n + 3 + m * (8 * n + 10) + s₂ n` with
`m ≤ k n * (computableFunctionsLogBound n (s₂ n) + 2)`, i.e. `O(k n ⋅ n ⋅ s₂ n ⋅ log(n + s₂ n))`
bits, matching `m(n) = Θ((n ⋅ s(n) ⋅ log s(n)) / δ(n))` in Lemma 16 for `δ(n) = 1 / k n`. -/
theorem exists_lt_formulaSize_succinctMCSP_of_approxMCSP_inst
    {s₁ s₂ k : ℕ → ℕ} {n L : ℕ} (hs : ∀ m, s₁ m ≤ s₂ m) (hk : ∀ m, 1 ≤ k m)
    (hged : ∀ F : Formula signature (2 ^ n),
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ (ApproxMCSP s₁ s₂ k hs hk).yes →
        F.eval interpretation T = true) →
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ (ApproxMCSP s₁ s₂ k hs hk).no →
        F.eval interpretation T = false) →
      (2 ^ n + 1) * L < F.leafSize) :
    ∃ m ≤ k n * (computableFunctionsLogBound n (s₂ n) + 2),
      L < formulaSize (Language.slice (SuccinctMCSP.enc '' SuccinctMCSP)
        (SuccinctMCSP.ofFunctionEncLength n m (s₂ n))) :=
  exists_lt_formulaSize_succinctMCSP_of_approxMCSP (hk n) (hs n)
    (card_computableFunctions_le_two_pow n (s₂ n)) hged

/-! ### Packaging Lemma 16 with `SuccinctMCSP ∈ NP` (Theorem 1 and Theorem 17) -/

/-- The maximum encoded bit length of a `SuccinctMCSP.Instance.ofFunction` query produced by the
Stage 1 random-sampling projection at input length `n`, circuit-size threshold `s`, and error
parameter `k`:
`SuccinctMCSP.ofFunctionEncLength n (k * (computableFunctionsLogBound n s + 2)) s`. -/
def approxMCSPQueryEncLength (n s k : ℕ) : ℕ :=
  SuccinctMCSP.ofFunctionEncLength n (k * (computableFunctionsLogBound n s + 2)) s

/-- Any query with `m ≤ k * (computableFunctionsLogBound n s + 2)` samples has encoded bit length at
most `approxMCSPQueryEncLength n s k`. -/
theorem ofFunctionEncLength_le_approxMCSPQueryEncLength {n m s k : ℕ}
    (hm : m ≤ k * (computableFunctionsLogBound n s + 2)) :
    SuccinctMCSP.ofFunctionEncLength n m s ≤ approxMCSPQueryEncLength n s k :=
  SuccinctMCSP.ofFunctionEncLength_mono n s hm

/-- **End-to-end Oliveira–Santhanam formula construction for any language agreeing with
`SuccinctMCSP` [OliveiraSanthanam2018, Section 3.1, Lemma 16, p. 14].**
If `L : Language Bool` agrees with `SuccinctMCSP` along `SuccinctMCSP.enc` and every
`(ofFunctionEncLength n m (s₂ n))`-bit slice of `L` with `m ≤ k n * (M + 2)` has De Morgan formula
size at most `B`, then there exists a De Morgan formula `F` on `2 ^ n` variables of leaf size at
most `(2 ^ n + 1) * B` separating `GapMCSP.yesSet s₁` from `ApproxMCSP.noSet s₂ k` on `2 ^ n`-bit
truth tables. -/
theorem exists_formula_separating_approxMCSP_of_agrees
    {L : Language Bool} (hag : ∀ x, x ∈ SuccinctMCSP ↔ SuccinctMCSP.enc x ∈ L)
    {s₁ s₂ k : ℕ → ℕ} {n M B : ℕ} (hk : 1 ≤ k n) (hs : s₁ n ≤ s₂ n)
    (hcard : (computableFunctions n (s₂ n)).card ≤ 2 ^ M)
    (hB : ∀ m ≤ k n * (M + 2),
      formulaSize (L.slice (SuccinctMCSP.ofFunctionEncLength n m (s₂ n))) ≤ B) :
    ∃ F : Formula signature (2 ^ n),
      F.leafSize ≤ (2 ^ n + 1) * B ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s₁ →
        F.eval interpretation T = true) ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ ApproxMCSP.noSet s₂ k →
        F.eval interpretation T = false) := by
  classical
  set q := k n * (M + 2)
  let noFinset : Finset (BitString (2 ^ n)) :=
    Finset.univ.filter fun T => List.ofFn T ∈ ApproxMCSP.noSet s₂ k
  have hno_card : Fintype.card noFinset ≤ 2 ^ (2 ^ n) := by
    rw [Fintype.card_coe]
    exact (Finset.card_le_univ noFinset).trans (by simp [BitString])
  obtain ⟨ωs, hωs⟩ := exists_forall_exists_apply_mem (Ω := Fin q → BitString n) hno_card
    (fun T : noFinset => Finset.univ.filter fun ω : Fin q → BitString n =>
      SuccinctMCSP.Instance.ofFunction
        ((MCSP.truthTable n).symm T.1) (Finset.univ.image ω) (s₂ n) ∉ SuccinctMCSP)
    (fun ⟨T, hT⟩ => card_le_two_mul_filter_notMem_succinctMCSP hk hcard
      (ApproxMCSP.ofFn_mem_noSet_iff.mp (Finset.mem_filter.mp hT).2))
  let qs : List (Finset (BitString n) × ℕ) :=
    List.ofFn fun j => (Finset.univ.image (ωs j), s₂ n)
  obtain ⟨F, hFeval, hFleaf⟩ := exists_formula_all_ofFunction_SuccinctMCSP_of_agrees hag n qs
  have hsum : (qs.map fun p =>
      formulaSize (L.slice (SuccinctMCSP.ofFunctionEncLength n p.1.card p.2))).sum ≤
        (2 ^ n + 1) * B := by
    have hmap := List.sum_le_length_nsmul
      (qs.map fun p => formulaSize (L.slice (SuccinctMCSP.ofFunctionEncLength n p.1.card p.2))) B
      (by
        intro x hx
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
        refine hB (Finset.univ.image (ωs j)).card ?_
        calc (Finset.univ.image (ωs j)).card
            ≤ (Finset.univ : Finset (Fin q)).card := Finset.card_image_le
          _ = q := by simp)
    simpa only [qs, List.length_map, List.length_ofFn, smul_eq_mul] using hmap
  refine ⟨F, hFleaf.trans hsum, fun T hyes => ?_, fun T hnoT => ?_⟩
  · rw [hFeval T, decide_eq_true_eq]
    intro p hp
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
    have hcomp : complexity interpretation (single ((MCSP.truthTable n).symm T)) ≤ s₂ n :=
      (GapMCSP.ofFn_mem_yesSet_iff.mp hyes).trans hs
    exact SuccinctMCSP.ofFunction_mem_of_complexity_le hcomp _
  · rw [hFeval T, decide_eq_false_iff_not, not_forall]
    have hmem : T ∈ noFinset := Finset.mem_filter.mpr ⟨Finset.mem_univ T, hnoT⟩
    obtain ⟨j, hj⟩ := hωs ⟨T, hmem⟩
    have hj' : SuccinctMCSP.Instance.ofFunction
        ((MCSP.truthTable n).symm T) (Finset.univ.image (ωs j)) (s₂ n) ∉ SuccinctMCSP :=
      (Finset.mem_filter.mp hj).2
    exact ⟨(Finset.univ.image (ωs j), s₂ n), fun h => hj' (h (List.mem_ofFn.mpr ⟨j, rfl⟩))⟩

/-- **If `SuccinctMCSP ∈ FormulaSIZEOn SuccinctMCSP.enc r` for a monotone bound `r`, then
`ApproxMCSP` has De Morgan formulas of leaf size `(2 ^ n + 1) * r(m(n))`**
([OliveiraSanthanam2018, Section 3.1, Lemma 16 and Theorem 17, pp. 14–15]). -/
theorem exists_formula_separating_approxMCSP_of_mem_FormulaSIZEOn
    {s₁ s₂ k r : ℕ → ℕ} (hs : ∀ m, s₁ m ≤ s₂ m) (hk : ∀ m, 1 ≤ k m)
    (hr : Monotone r) (hmem : SuccinctMCSP ∈ FormulaSIZEOn SuccinctMCSP.enc r) (n : ℕ) :
    ∃ F : Formula signature (2 ^ n),
      F.leafSize ≤ (2 ^ n + 1) * r (approxMCSPQueryEncLength n (s₂ n) (k n)) ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s₁ →
        F.eval interpretation T = true) ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ ApproxMCSP.noSet s₂ k →
        F.eval interpretation T = false) := by
  obtain ⟨L, hL, hag⟩ := hmem
  refine exists_formula_separating_approxMCSP_of_agrees hag (hk n) (hs n)
    (card_computableFunctions_le_two_pow n (s₂ n)) fun m hm => ?_
  exact (hL _).trans (hr (ofFunctionEncLength_le_approxMCSPQueryEncLength hm))

/-- **Contrapositive of Oliveira–Santhanam Lemma 16 (general parameters, for `SuccinctMCSP`)**
[OliveiraSanthanam2018, Section 3.1, Lemma 16 and Theorem 17 (i)/(iii), pp. 14–15].
If `s₁ n ≤ s₂ n` and `1 ≤ k n` for all `n`, and for every polynomial degree `c : ℕ` there exists an
input length `n` at which every De Morgan formula separating `GapMCSP.yesSet s₁` and
`ApproxMCSP.noSet s₂ k` on `2 ^ n`-bit truth tables has leaf size strictly greater than
`(2 ^ n + 1) * (c * (approxMCSPQueryEncLength n (s₂ n) (k n) + 1) ^ c)`, then
`SuccinctMCSP ∉ FormulaPolyOn SuccinctMCSP.enc`. -/
theorem not_succinctMCSP_mem_FormulaPolyOn_of_approxMCSP_hard
    {s₁ s₂ k : ℕ → ℕ} (hs : ∀ m, s₁ m ≤ s₂ m) (hk : ∀ m, 1 ≤ k m)
    (hhard : ∀ c : ℕ, ∃ n : ℕ, ∀ F : Formula signature (2 ^ n),
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s₁ →
        F.eval interpretation T = true) →
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ ApproxMCSP.noSet s₂ k →
        F.eval interpretation T = false) →
      (2 ^ n + 1) * (c * (approxMCSPQueryEncLength n (s₂ n) (k n) + 1) ^ c) < F.leafSize) :
    SuccinctMCSP ∉ FormulaPolyOn SuccinctMCSP.enc := by
  rw [mem_FormulaPolyOn_iff_exists_mem_FormulaSIZEOn]
  rintro ⟨c, hc⟩
  obtain ⟨n, hn⟩ := hhard c
  have hmono : Monotone (fun m => c * (m + 1) ^ c) := fun m₁ m₂ hm =>
    Nat.mul_le_mul_left c (Nat.pow_le_pow_left (Nat.add_le_add_right hm 1) c)
  obtain ⟨F, hFleaf, hyes, hno⟩ :=
    exists_formula_separating_approxMCSP_of_mem_FormulaSIZEOn hs hk hmono hc n
  exact (hn F hyes hno).not_ge hFleaf

/-- **Contrapositive of Oliveira–Santhanam Lemma 16 (`NP ⊄ Formula[poly]`, general parameters
underlying Theorem 17(i)/(iii))**
[OliveiraSanthanam2018, Section 3.1, Lemma 16 and Theorem 17 (i)/(iii), pp. 14–15].
Under the hypothesis of `not_succinctMCSP_mem_FormulaPolyOn_of_approxMCSP_hard`, combining Lemma 16
with `SuccinctMCSP.mem_NP` yields
`¬ (Complexity.NP SuccinctMCSP.enc ⊆ FormulaPolyOn SuccinctMCSP.enc)`. -/
theorem not_NP_subset_FormulaPolyOn_of_approxMCSP_hard
    {s₁ s₂ k : ℕ → ℕ} (hs : ∀ m, s₁ m ≤ s₂ m) (hk : ∀ m, 1 ≤ k m)
    (hhard : ∀ c : ℕ, ∃ n : ℕ, ∀ F : Formula signature (2 ^ n),
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s₁ →
        F.eval interpretation T = true) →
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ ApproxMCSP.noSet s₂ k →
        F.eval interpretation T = false) →
      (2 ^ n + 1) * (c * (approxMCSPQueryEncLength n (s₂ n) (k n) + 1) ^ c) < F.leafSize) :
    ¬ (Complexity.NP SuccinctMCSP.enc ⊆ FormulaPolyOn SuccinctMCSP.enc) :=
  fun hsub =>
    not_succinctMCSP_mem_FormulaPolyOn_of_approxMCSP_hard hs hk hhard
      (hsub SuccinctMCSP.mem_NP)

/-- Elementary polynomial upper bound on `computableFunctionsLogBound n s`: since
`Nat.clog 2 (n + s + 1) ≤ n + s + 1`, we have
`computableFunctionsLogBound n s ≤ (s + 1) * (2 * (n + s + 1) + 3)`. -/
theorem computableFunctionsLogBound_le_poly (n s : ℕ) :
    computableFunctionsLogBound n s ≤ (s + 1) * (2 * (n + s + 1) + 3) := by
  have hclog : Nat.clog 2 (n + s + 1) ≤ n + s + 1 :=
    (Nat.clog_le_iff_le_pow (by decide)).mpr (Nat.lt_two_pow_self).le
  dsimp only [computableFunctionsLogBound]
  exact Nat.mul_le_mul_left (s + 1)
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hclog) 3)

/-- When `s` is polynomially bounded, `fun n => computableFunctionsLogBound n (s n)` is polynomially
bounded. -/
theorem polynomiallyBounded_computableFunctionsLogBound {s : ℕ → ℕ}
    (hs : PolynomiallyBounded s) :
    PolynomiallyBounded (fun n => computableFunctionsLogBound n (s n)) := by
  have hpoly : PolynomiallyBounded (fun n => (s n + 1) * (2 * (n + s n + 1) + 3)) :=
    (hs.add (.const 1)).mul
      (((PolynomiallyBounded.const 2).mul
        ((PolynomiallyBounded.id.add hs).add (.const 1))).add (.const 3))
  exact hpoly.mono_of_le fun n => computableFunctionsLogBound_le_poly n (s n)

/-- When the circuit-size threshold `s` and inverse-error parameter `k` are polynomially bounded in
`n`, the maximum encoded query length `fun n => approxMCSPQueryEncLength n (s n) (k n)` is
polynomially bounded in `n`. -/
theorem polynomiallyBounded_approxMCSPQueryEncLength {s k : ℕ → ℕ}
    (hs : PolynomiallyBounded s) (hk : PolynomiallyBounded k) :
    PolynomiallyBounded (fun n => approxMCSPQueryEncLength n (s n) (k n)) := by
  have hq : PolynomiallyBounded (fun n => k n * (computableFunctionsLogBound n (s n) + 2)) :=
    hk.mul ((polynomiallyBounded_computableFunctionsLogBound hs).add (.const 2))
  have h8n : PolynomiallyBounded (fun n => 8 * n + 10) :=
    ((PolynomiallyBounded.const 8).mul PolynomiallyBounded.id).add (.const 10)
  have h4n : PolynomiallyBounded (fun n => 4 * n + 3) :=
    ((PolynomiallyBounded.const 4).mul PolynomiallyBounded.id).add (.const 3)
  exact (h4n.add (hq.mul h8n)).add hs

/-- **Polynomial-parameter forward upper bound for Theorem 1(i) / Theorem 17(i)**
[OliveiraSanthanam2018, Section 1.2, Theorem 1 (i), p. 5; Section 3.1, Theorem 17 (i), p. 15].
If `s₂` and `k` are polynomially bounded in `n` (for example `s₂(n) = n ^ d` and
`k(n) = (n + 1) ^ d`) and `SuccinctMCSP ∈ FormulaPolyOn SuccinctMCSP.enc`, then there is a
polynomial degree `c : ℕ` such that for every `n`, `ApproxMCSP s₁ s₂ k` on `2 ^ n`-bit inputs is
separated by a De Morgan formula of leaf size at most `(2 ^ n + 1) * (c * (n + 1) ^ c)`
(`N · (log N)^{O(1)}` where `N = 2 ^ n`). -/
theorem exists_poly_formula_separating_approxMCSP_of_mem_FormulaPolyOn
    {s₁ s₂ k : ℕ → ℕ} (hs : ∀ m, s₁ m ≤ s₂ m) (hk : ∀ m, 1 ≤ k m)
    (hs₂_poly : PolynomiallyBounded s₂) (hk_poly : PolynomiallyBounded k)
    (hmem : SuccinctMCSP ∈ FormulaPolyOn SuccinctMCSP.enc) :
    ∃ c : ℕ, ∀ n : ℕ, ∃ F : Formula signature (2 ^ n),
      F.leafSize ≤ (2 ^ n + 1) * (c * (n + 1) ^ c) ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s₁ →
        F.eval interpretation T = true) ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ ApproxMCSP.noSet s₂ k →
        F.eval interpretation T = false) := by
  obtain ⟨L, hL, hag⟩ := hmem
  have hcomp_mem : (L : Language Bool) ∈ FormulaPoly := hL
  obtain ⟨c₀, hc₀⟩ := mem_FormulaPoly_iff_exists_mem_FormulaSIZE.mp hcomp_mem
  have hr_poly : PolynomiallyBounded
      (fun n => c₀ * (approxMCSPQueryEncLength n (s₂ n) (k n) + 1) ^ c₀) := by
    have hbase : PolynomiallyBounded (fun m => c₀ * (m + 1) ^ c₀) :=
      (PolynomiallyBounded.const c₀).mul
        ((PolynomiallyBounded.id.add (.const 1)).pow c₀)
    exact hbase.comp (polynomiallyBounded_approxMCSPQueryEncLength hs₂_poly hk_poly)
  obtain ⟨c₁, d₁, hcd⟩ := polynomiallyBounded_iff_le.mp hr_poly
  let c := max c₁ d₁
  refine ⟨c, fun n => ?_⟩
  have hmono : Monotone (fun m => c₀ * (m + 1) ^ c₀) := fun m₁ m₂ hm =>
    Nat.mul_le_mul_left c₀ (Nat.pow_le_pow_left (Nat.add_le_add_right hm 1) c₀)
  obtain ⟨F, hFleaf, hyes, hno⟩ :=
    exists_formula_separating_approxMCSP_of_mem_FormulaSIZEOn hs hk hmono ⟨L, hc₀, hag⟩ n
  refine ⟨F, hFleaf.trans (Nat.mul_le_mul_left (2 ^ n + 1) ?_), hyes, hno⟩
  exact (hcd n).trans (Nat.mul_le_mul (le_max_left c₁ d₁)
    (Nat.pow_le_pow_right (Nat.succ_pos n) (le_max_right c₁ d₁)))

/-- **Oliveira–Santhanam Theorem 1(i) / Theorem 17(i) (for `SuccinctMCSP`)**
[OliveiraSanthanam2018, Section 1.2, Theorem 1 (i), p. 5; Section 3.1, Theorem 17 (i), p. 15].
If `s₂` and `k` are polynomially bounded in `n` (such as `s(n) = n ^ d` and `δ(n) = n ^ (-d)`), and
`ApproxMCSP[s₁, s₂, k]` on `N = 2 ^ n`-bit truth tables is not separated by De Morgan formulas of
leaf size `(2 ^ n + 1) * (c * (n + 1) ^ c)` (`Formula[N · (log N)^{O(1)}]`), then
`SuccinctMCSP ∉ FormulaPolyOn SuccinctMCSP.enc`. -/
theorem not_succinctMCSP_mem_FormulaPolyOn_of_approxMCSP_poly_hard
    {s₁ s₂ k : ℕ → ℕ} (hs : ∀ m, s₁ m ≤ s₂ m) (hk : ∀ m, 1 ≤ k m)
    (hs₂_poly : PolynomiallyBounded s₂) (hk_poly : PolynomiallyBounded k)
    (hhard : ∀ c : ℕ, ∃ n : ℕ, ∀ F : Formula signature (2 ^ n),
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s₁ →
        F.eval interpretation T = true) →
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ ApproxMCSP.noSet s₂ k →
        F.eval interpretation T = false) →
      (2 ^ n + 1) * (c * (n + 1) ^ c) < F.leafSize) :
    SuccinctMCSP ∉ FormulaPolyOn SuccinctMCSP.enc := by
  intro hmem
  obtain ⟨c, hc⟩ :=
    exists_poly_formula_separating_approxMCSP_of_mem_FormulaPolyOn hs hk hs₂_poly hk_poly hmem
  obtain ⟨n, hn⟩ := hhard c
  obtain ⟨F, hFleaf, hyes, hno⟩ := hc n
  exact (hn F hyes hno).not_ge hFleaf

/-- **Oliveira–Santhanam Theorem 1(i) / Theorem 17(i)
(`Π[s, δ] ∉ Formula[N · (log N)^{O(1)}] ⟹ NP ⊄ Formula[poly]`)**
[OliveiraSanthanam2018, Section 1.2, Theorem 1 (i), p. 5; Section 3.1, Theorem 17 (i), p. 15].
If `s₂` and `k` are polynomially bounded in `n` and `ApproxMCSP[s₁, s₂, k]` on `N = 2 ^ n`-bit truth
tables is not separated by De Morgan formulas of leaf size `(2 ^ n + 1) * (c * (n + 1) ^ c)`, then
`¬ (Complexity.NP SuccinctMCSP.enc ⊆ FormulaPolyOn SuccinctMCSP.enc)`. -/
theorem not_NP_subset_FormulaPolyOn_of_approxMCSP_poly_hard
    {s₁ s₂ k : ℕ → ℕ} (hs : ∀ m, s₁ m ≤ s₂ m) (hk : ∀ m, 1 ≤ k m)
    (hs₂_poly : PolynomiallyBounded s₂) (hk_poly : PolynomiallyBounded k)
    (hhard : ∀ c : ℕ, ∃ n : ℕ, ∀ F : Formula signature (2 ^ n),
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s₁ →
        F.eval interpretation T = true) →
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ ApproxMCSP.noSet s₂ k →
        F.eval interpretation T = false) →
      (2 ^ n + 1) * (c * (n + 1) ^ c) < F.leafSize) :
    ¬ (Complexity.NP SuccinctMCSP.enc ⊆ FormulaPolyOn SuccinctMCSP.enc) :=
  fun hsub =>
    not_succinctMCSP_mem_FormulaPolyOn_of_approxMCSP_poly_hard hs hk hs₂_poly hk_poly hhard
      (hsub SuccinctMCSP.mem_NP)

/-! ### Zero-Error Average-Case Formula Magnification (Lemma 26, Theorem 5, and Theorem 27) -/

open Classical in
/-- For any fixed `g : BooleanFunction n` and sample set `S : Finset (BitString n)`, the number of
truth tables `T : BitString (2 ^ n)` whose function `(MCSP.truthTable n).symm T` agrees with `g` on
every input in `S` is `2 ^ (2 ^ n - S.card)` (since the `S.card` values on `S` are fixed to `g` and
the remaining `2 ^ n - S.card` values are unconstrained). -/
theorem card_filter_agreesOn_eq_two_pow (n : ℕ) (S : Finset (BitString n))
    (g : BooleanFunction n) :
    (Finset.univ.filter fun T : BitString (2 ^ n) =>
      ∀ y ∈ S, (MCSP.truthTable n).symm T y = g y).card = 2 ^ (2 ^ n - S.card) := by
  have hbij : (Finset.univ.filter fun T : BitString (2 ^ n) =>
        ∀ y ∈ S, (MCSP.truthTable n).symm T y = g y).card =
      (Finset.univ.filter fun f : BooleanFunction n => ∀ y ∈ S, f y = g y).card := by
    refine Finset.card_bij (fun T _ => (MCSP.truthTable n).symm T)
      (fun T hT => ?_) (fun T₁ _ T₂ _ h => (MCSP.truthTable n).symm.injective h)
      (fun f hf => ⟨MCSP.truthTable n f, ?_, by simp⟩)
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hT).2⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      simpa using (Finset.mem_filter.mp hf).2
  have hpi : (Finset.univ.filter fun f : BooleanFunction n => ∀ y ∈ S, f y = g y) =
      Fintype.piFinset (fun y : BitString n =>
        if y ∈ S then ({g y} : Finset Bool) else Finset.univ) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    refine ⟨fun hf y => ?_, fun hf y hy => ?_⟩
    · split_ifs with hy
      · exact Finset.mem_singleton.mpr (hf y hy)
      · exact Finset.mem_univ (f y)
    · have hfy := hf y
      simp only [hy, ↓reduceIte, Finset.mem_singleton] at hfy
      exact hfy
  rw [hbij, hpi, Fintype.card_piFinset]
  simp only [apply_ite Finset.card, Finset.prod_ite, Finset.prod_const,
    Finset.card_singleton, one_pow, one_mul, Finset.filter_not, Finset.filter_mem_eq_inter,
    Finset.univ_inter, Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ,
    Fintype.card_bool]
  simp [BitString]

open Classical in
/-- **Oliveira–Santhanam Lemma 26 (finite-counting form)**
[OliveiraSanthanam2018, Section 3.3, Lemma 26, p. 21]: for any fixed subset
`S : Finset (BitString n)` of distinct `n`-bit inputs and any circuit-size threshold `s`, the number
of truth tables `T : BitString (2 ^ n)` whose restriction to `S` is consistent with a circuit of
size at most `s`
(`SuccinctMCSP.Instance.ofFunction ((MCSP.truthTable n).symm T) S s ∈ SuccinctMCSP`) is at most
`(computableFunctions n s).card * 2 ^ (2 ^ n - S.card)`. -/
theorem card_filter_ofFunction_mem_succinctMCSP_le (n : ℕ) (S : Finset (BitString n)) (s : ℕ) :
    (Finset.univ.filter fun T : BitString (2 ^ n) =>
      SuccinctMCSP.Instance.ofFunction
        ((MCSP.truthTable n).symm T) S s ∈ SuccinctMCSP).card ≤
    (computableFunctions n s).card * 2 ^ (2 ^ n - S.card) := by
  let AgreeOn (g : BooleanFunction n) : Finset (BitString (2 ^ n)) :=
    Finset.univ.filter fun T : BitString (2 ^ n) =>
      ∀ y ∈ S, (MCSP.truthTable n).symm T y = g y
  have hsub : (Finset.univ.filter fun T : BitString (2 ^ n) =>
      SuccinctMCSP.Instance.ofFunction
        ((MCSP.truthTable n).symm T) S s ∈ SuccinctMCSP) ⊆
      (computableFunctions n s).biUnion AgreeOn := by
    intro T hT
    obtain ⟨g, hg, hag⟩ :=
      SuccinctMCSP.ofFunction_mem_iff_exists_mem_computableFunctions.mp
        (Finset.mem_filter.mp hT).2
    exact Finset.mem_biUnion.mpr ⟨g, hg,
      Finset.mem_filter.mpr ⟨Finset.mem_univ T, fun y hy => (hag y hy).symm⟩⟩
  calc (Finset.univ.filter fun T : BitString (2 ^ n) =>
        SuccinctMCSP.Instance.ofFunction
          ((MCSP.truthTable n).symm T) S s ∈ SuccinctMCSP).card
      ≤ ((computableFunctions n s).biUnion AgreeOn).card := Finset.card_le_card hsub
    _ ≤ ∑ g ∈ computableFunctions n s, (AgreeOn g).card := Finset.card_biUnion_le
    _ = ∑ _g ∈ computableFunctions n s, 2 ^ (2 ^ n - S.card) :=
        Finset.sum_congr rfl fun g _ => card_filter_agreesOn_eq_two_pow n S g
    _ = (computableFunctions n s).card * 2 ^ (2 ^ n - S.card) := by
        rw [Finset.sum_const, smul_eq_mul]

open Classical in
/-- **Oliveira–Santhanam Lemma 26 (exponential-tail form)**
[OliveiraSanthanam2018, Section 3.3, Lemma 26, p. 21]: if `(computableFunctions n s).card ≤ 2 ^ M`
(in particular for `M = computableFunctionsLogBound n s`) and `M + r ≤ S.card`, then at most
`2 ^ (2 ^ n - r)` truth tables `T : BitString (2 ^ n)` satisfy
`SuccinctMCSP.Instance.ofFunction ((MCSP.truthTable n).symm T) S s ∈ SuccinctMCSP`
(so for `r = n`, at most a `2 ^ (-n)`-fraction of all `2 ^ (2 ^ n)` truth tables are consistent
with a circuit of size at most `s` on `S`). -/
theorem card_filter_ofFunction_mem_succinctMCSP_le_two_pow
    {n s M r : ℕ} {S : Finset (BitString n)}
    (hcard : (computableFunctions n s).card ≤ 2 ^ M) (hS : M + r ≤ S.card) :
    (Finset.univ.filter fun T : BitString (2 ^ n) =>
      SuccinctMCSP.Instance.ofFunction
        ((MCSP.truthTable n).symm T) S s ∈ SuccinctMCSP).card ≤
    2 ^ (2 ^ n - r) := by
  have hScard : S.card ≤ 2 ^ n :=
    (Finset.card_le_univ S).trans (by simp [BitString])
  have hexp : M + (2 ^ n - S.card) ≤ 2 ^ n - r := by omega
  calc (Finset.univ.filter fun T : BitString (2 ^ n) =>
        SuccinctMCSP.Instance.ofFunction
          ((MCSP.truthTable n).symm T) S s ∈ SuccinctMCSP).card
      ≤ (computableFunctions n s).card * 2 ^ (2 ^ n - S.card) :=
        card_filter_ofFunction_mem_succinctMCSP_le n S s
    _ ≤ 2 ^ M * 2 ^ (2 ^ n - S.card) := Nat.mul_le_mul_right _ hcard
    _ = 2 ^ (M + (2 ^ n - S.card)) := (pow_add 2 M (2 ^ n - S.card)).symm
    _ ≤ 2 ^ (2 ^ n - r) := Nat.pow_le_pow_right (by decide) hexp

/-- The encoded bit length of a `SuccinctMCSP.Instance.ofFunction` query on
`computableFunctionsLogBound n s + r` distinct `n`-bit inputs at circuit-size threshold `s`, used in
the zero-error average-case formula magnification of
[OliveiraSanthanam2018, Section 3.3, Theorem 27, p. 21]. -/
def avgCaseMCSPQueryEncLength (n s r : ℕ) : ℕ :=
  SuccinctMCSP.ofFunctionEncLength n (computableFunctionsLogBound n s + r) s

open Classical in
/-- **Zero-error average-case formula projection for a given sample set `S`**
([OliveiraSanthanam2018, Section 3.3, Lemma 26 and Theorem 27, p. 21]).
If `L : Language Bool` agrees with `SuccinctMCSP` along `SuccinctMCSP.enc` and
`S : Finset (BitString n)` satisfies `computableFunctionsLogBound n (s n) + r ≤ S.card`, then the
single-query projection formula `F` on `2 ^ n` variables has:
1. `F.leafSize ≤ formulaSize (L.slice (SuccinctMCSP.ofFunctionEncLength n S.card (s n)))`
   (no `2 ^ n` blowup in formula size),
2. zero error on Yes-instances:
   `∀ T, List.ofFn T ∈ GapMCSP.yesSet s → F.eval interpretation T = true`
   (so `F.eval interpretation T = false` certifies `List.ofFn T ∉ GapMCSP.yesSet s`), and
3. bounded acceptance on random truth tables: at most `2 ^ (2 ^ n - r)` truth tables
   `T : BitString (2 ^ n)` satisfy `F.eval interpretation T = true`. -/
theorem exists_formula_zero_error_average_case_of_sample
    {L : Language Bool} (hag : ∀ x, x ∈ SuccinctMCSP ↔ SuccinctMCSP.enc x ∈ L)
    {s : ℕ → ℕ} {n r : ℕ} (S : Finset (BitString n))
    (hS : computableFunctionsLogBound n (s n) + r ≤ S.card) :
    ∃ F : Formula signature (2 ^ n),
      F.leafSize ≤ formulaSize (L.slice (SuccinctMCSP.ofFunctionEncLength n S.card (s n))) ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s →
        F.eval interpretation T = true) ∧
      (Finset.univ.filter fun T : BitString (2 ^ n) =>
        F.eval interpretation T = true).card ≤ 2 ^ (2 ^ n - r) := by
  obtain ⟨F, hFeval, hFleaf⟩ :=
    exists_formula_ofFunction_SuccinctMCSP_of_agrees hag n S (s n)
  refine ⟨F, hFleaf, fun T hyes => ?_, ?_⟩
  · rw [hFeval T, decide_eq_true_eq]
    exact SuccinctMCSP.ofFunction_mem_of_complexity_le
      (GapMCSP.ofFn_mem_yesSet_iff.mp hyes) S
  · have hfilter : (Finset.univ.filter fun T : BitString (2 ^ n) =>
        F.eval interpretation T = true) =
      (Finset.univ.filter fun T : BitString (2 ^ n) =>
        SuccinctMCSP.Instance.ofFunction
          ((MCSP.truthTable n).symm T) S (s n) ∈ SuccinctMCSP) := by
      ext T
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hFeval T, decide_eq_true_eq]
    rw [hfilter]
    exact card_filter_ofFunction_mem_succinctMCSP_le_two_pow
      (card_computableFunctions_le_two_pow n (s n)) hS

open Classical in
/-- **Zero-error average-case formula projection at exact query length `avgCaseMCSPQueryEncLength`**
[OliveiraSanthanam2018, Section 3.3, Theorem 27, p. 21].
Whenever `computableFunctionsLogBound n (s n) + r ≤ 2 ^ n`, choosing a subset
`S : Finset (BitString n)` of cardinality `computableFunctionsLogBound n (s n) + r` yields a De
Morgan formula `F` on `2 ^ n` variables of leaf size at most
`formulaSize (L.slice (avgCaseMCSPQueryEncLength n (s n) r))` that accepts every
`T ∈ GapMCSP.yesSet s` and accepts at most `2 ^ (2 ^ n - r)` truth tables overall. -/
theorem exists_formula_zero_error_average_case_of_agrees
    {L : Language Bool} (hag : ∀ x, x ∈ SuccinctMCSP ↔ SuccinctMCSP.enc x ∈ L)
    {s : ℕ → ℕ} {n r : ℕ}
    (ht : computableFunctionsLogBound n (s n) + r ≤ 2 ^ n) :
    ∃ F : Formula signature (2 ^ n),
      F.leafSize ≤ formulaSize (L.slice (avgCaseMCSPQueryEncLength n (s n) r)) ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s →
        F.eval interpretation T = true) ∧
      (Finset.univ.filter fun T : BitString (2 ^ n) =>
        F.eval interpretation T = true).card ≤ 2 ^ (2 ^ n - r) := by
  have huniv : computableFunctionsLogBound n (s n) + r ≤
      (Finset.univ : Finset (BitString n)).card := by
    simpa [BitString] using ht
  obtain ⟨S, -, hScard⟩ := Finset.exists_subset_card_eq huniv
  obtain ⟨F, hFleaf, hyes, hcard⟩ :=
    exists_formula_zero_error_average_case_of_sample hag S hScard.ge
  rw [hScard] at hFleaf
  exact ⟨F, hFleaf, hyes, hcard⟩

open Classical in
/-- **Zero-error average-case formula projection for `SuccinctMCSP.enc '' SuccinctMCSP`**
[OliveiraSanthanam2018, Section 3.3, Theorem 27, p. 21]. -/
theorem exists_formula_zero_error_average_case_of_succinctMCSP
    {s : ℕ → ℕ} {n r : ℕ}
    (ht : computableFunctionsLogBound n (s n) + r ≤ 2 ^ n) :
    ∃ F : Formula signature (2 ^ n),
      F.leafSize ≤
        formulaSize (Language.slice (SuccinctMCSP.enc '' SuccinctMCSP)
          (avgCaseMCSPQueryEncLength n (s n) r)) ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s →
        F.eval interpretation T = true) ∧
      (Finset.univ.filter fun T : BitString (2 ^ n) =>
        F.eval interpretation T = true).card ≤ 2 ^ (2 ^ n - r) :=
  exists_formula_zero_error_average_case_of_agrees
    (fun _ => SuccinctMCSP.enc.injective.mem_set_image.symm) ht

open Classical in
/-- **Contrapositive zero-error average-case formula magnification (Oliveira–Santhanam Theorem 27 at
a single input length `n`)** [OliveiraSanthanam2018, Section 3.3, Theorem 27, p. 21].
If `computableFunctionsLogBound n (s n) + r ≤ 2 ^ n` and every De Morgan formula `F` on `2 ^ n`
variables that accepts all `GapMCSP.yesSet s` truth tables and accepts at most `2 ^ (2 ^ n - r)`
truth tables overall has leaf size strictly greater than `B`, then the
`(avgCaseMCSPQueryEncLength n (s n) r)`-bit slice of `SuccinctMCSP.enc '' SuccinctMCSP` has De
Morgan formula size strictly greater than `B`. -/
theorem lt_formulaSize_succinctMCSP_of_zero_error_average_case
    {s : ℕ → ℕ} {n r B : ℕ}
    (ht : computableFunctionsLogBound n (s n) + r ≤ 2 ^ n)
    (hhard : ∀ F : Formula signature (2 ^ n),
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s →
        F.eval interpretation T = true) →
      (Finset.univ.filter fun T : BitString (2 ^ n) =>
        F.eval interpretation T = true).card ≤ 2 ^ (2 ^ n - r) →
      B < F.leafSize) :
    B < formulaSize (Language.slice (SuccinctMCSP.enc '' SuccinctMCSP)
      (avgCaseMCSPQueryEncLength n (s n) r)) := by
  obtain ⟨F, hFleaf, hyes, hcard⟩ :=
    exists_formula_zero_error_average_case_of_succinctMCSP ht
  exact (hhard F hyes hcard).trans_le hFleaf

open Classical in
/-- **One-sided zero-error average-case formula magnification (Oliveira–Santhanam Theorem 27, for
`SuccinctMCSP`)**
[OliveiraSanthanam2018, Section 3.3, Theorem 27, p. 21; compare Section 1.2, Theorem 5, p. 8].
If for every polynomial degree `c : ℕ` there exists `n : ℕ` with
`computableFunctionsLogBound n (s n) + r n ≤ 2 ^ n` such that every one-sided De
Morgan formula for `GapMCSP.yesSet s` on `2 ^ n` variables (accepting all `GapMCSP.yesSet s`
instances and at most `2 ^ (2 ^ n - r n)` truth tables overall) has leaf size strictly greater than
`c * (avgCaseMCSPQueryEncLength n (s n) (r n) + 1) ^ c`, then
`SuccinctMCSP ∉ FormulaPolyOn SuccinctMCSP.enc`. -/
theorem not_succinctMCSP_mem_FormulaPolyOn_of_zero_error_average_case_hard
    {s r : ℕ → ℕ}
    (hhard : ∀ c : ℕ, ∃ n : ℕ,
      computableFunctionsLogBound n (s n) + r n ≤ 2 ^ n ∧
      ∀ F : Formula signature (2 ^ n),
        (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s →
          F.eval interpretation T = true) →
        (Finset.univ.filter fun T : BitString (2 ^ n) =>
          F.eval interpretation T = true).card ≤ 2 ^ (2 ^ n - r n) →
        c * (avgCaseMCSPQueryEncLength n (s n) (r n) + 1) ^ c < F.leafSize) :
    SuccinctMCSP ∉ FormulaPolyOn SuccinctMCSP.enc := by
  rw [mem_FormulaPolyOn_iff_exists_mem_FormulaSIZEOn]
  rintro ⟨c, L, hL, hag⟩
  obtain ⟨n, ht, hn⟩ := hhard c
  obtain ⟨F, hFleaf, hyes, hcard⟩ :=
    exists_formula_zero_error_average_case_of_agrees hag ht
  exact (hn F hyes hcard).not_ge (hFleaf.trans (hL _))

open Classical in
/-- **One-sided zero-error average-case formula magnification (Oliveira–Santhanam Theorem 27,
`NP ⊄ Formula[poly]`)**
[OliveiraSanthanam2018, Section 3.3, Theorem 27, p. 21; compare Section 1.2, Theorem 5, p. 8].
Under the hypothesis of `not_succinctMCSP_mem_FormulaPolyOn_of_zero_error_average_case_hard`,
combining Theorem 27 with `SuccinctMCSP.mem_NP` yields
`¬ (Complexity.NP SuccinctMCSP.enc ⊆ FormulaPolyOn SuccinctMCSP.enc)`. -/
theorem not_NP_subset_FormulaPolyOn_of_zero_error_average_case_hard
    {s r : ℕ → ℕ}
    (hhard : ∀ c : ℕ, ∃ n : ℕ,
      computableFunctionsLogBound n (s n) + r n ≤ 2 ^ n ∧
      ∀ F : Formula signature (2 ^ n),
        (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s →
          F.eval interpretation T = true) →
        (Finset.univ.filter fun T : BitString (2 ^ n) =>
          F.eval interpretation T = true).card ≤ 2 ^ (2 ^ n - r n) →
        c * (avgCaseMCSPQueryEncLength n (s n) (r n) + 1) ^ c < F.leafSize) :
    ¬ (Complexity.NP SuccinctMCSP.enc ⊆ FormulaPolyOn SuccinctMCSP.enc) :=
  fun hsub =>
    not_succinctMCSP_mem_FormulaPolyOn_of_zero_error_average_case_hard hhard
      (hsub SuccinctMCSP.mem_NP)

end Circuits.Boolean

end Cslib
