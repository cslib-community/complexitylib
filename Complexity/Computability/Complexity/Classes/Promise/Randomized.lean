/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Promise.Probabilistic
import Complexity.Computability.Complexity.Classes.SharpP.Probability
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Probabilistic.CoinTape
import Complexity.Computability.Probabilistic.PPT.Capture
import Complexity.Computability.Probabilistic.Sampling
import Complexity.Probability.PMF.Event
import Complexity.Probability.PMF.Uniform

/-!
# Randomized reductions with one-sided error on promise problems

For randomized hardness results in metacomplexity [Ilango, Section 2, p. 34:11][Ilango2020],
[Ilango, Loff and Oliveira, Section 4.2, Lemmas 15–16, pp. 22:20–22:23][IlangoLoffOliveira2020],
[Hirahara, ECCC TR22-119, Lemma 8.3, p. 26 and Theorem 8.5, pp. 30–31][Hirahara2022], a
**randomized polynomial-time many-one reduction with one-sided error**
(`PromiseProblem.RPReducible`, and the threshold-indexed generalization
`PromiseProblem.RPReducibleWithError`) is a uniform strict PPT program `R : α → ProbComp β` that
maps every yes-instance of `X` exclusively into `Y.yes` and maps every no-instance of `X` into
`Y.no` with probability at least `2 / 3` (or `s a`).

Following the terminology of [Ilango, Section 2, p. 34:11][Ilango2020], `RPReducible` errs only on
**no-instances** (the `coRP` error orientation): in metacomplexity reductions, upper bounds on
circuit or Kolmogorov complexity hold deterministically for every random choice on yes-instances
while lower bounds on no-instances hold with high probability. Consequently, `PromiseCoRP` and
`PromiseBPP` are closed under `RPReducible` (`PromiseProblem.RPReducible.mem_PromiseCoRP`,
`PromiseProblem.RPReducible.mem_PromiseBPP`, `PromiseProblem.NP_subset_coRP_of_forall_rpReducible`,
`PromiseProblem.NP_subset_BPP_of_forall_rpReducible`), whereas the dual `RP` error orientation (zero
error on no-instances, bounded error on yes-instances, as in [Valiant and Vazirani, pp. 86–87]
[ValiantVazirani1986]) is expressed via promise-problem complement as
`RPReducibleWithError encA encB s Xᶜ Yᶜ` (`PromiseProblem.rpReducibleWithError_compl_iff`,
`PromiseProblem.RPReducible.mem_PromiseRP_of_compl`).

Because outer measures are non-negative, the soundness inequality in `RPReducibleWithError` holds
vacuously at any no-instance `a` with `s a ≤ 0`; in particular, the additive composition lemma
`PromiseProblem.RPReducibleWithError.trans_add` (which produces threshold `s₁ a + s₂ - 1`) gives a
non-trivial soundness bound at `a` only when `1 < s₁ a + s₂`.

## Main definitions

* `Cslib.Complexity.PromiseProblem.RPReducibleWithError`,
  `Cslib.Complexity.PromiseProblem.RPReducible`: randomized polynomial-time many-one reductions
  with one-sided error on promise problems.

## Main results

* `Cslib.Complexity.PromiseProblem.rpReducibleWithError_iff_probability`,
  `Cslib.Complexity.PromiseProblem.rpReducible_iff_probability`,
  `Cslib.Complexity.PromiseProblem.rpReducibleWithError_iff_toOuterMeasure_eq_one`,
  `Cslib.Complexity.PromiseProblem.rpReducible_iff_toOuterMeasure_eq_one`,
  `Cslib.Complexity.PromiseProblem.rpReducible_iff_exists_seeded`,
  `Cslib.Complexity.PromiseProblem.rpReducibleWithError_compl_iff`: faithfulness and convention
  bridges.
* `Cslib.Complexity.PromiseProblem.RPReducibleWithError.mono`,
  `Cslib.Complexity.PromiseProblem.PolyTimeReducible.rpReducibleWithError`,
  `Cslib.Complexity.PromiseProblem.PolyTimeReducible.rpReducible`,
  `Cslib.Complexity.PolyTimeReducible.rpReducible_ofSet`,
  `Cslib.Complexity.PromiseProblem.RPReducibleWithError.refl`,
  `Cslib.Complexity.PromiseProblem.RPReducible.refl`,
  `Cslib.Complexity.PromiseProblem.RPReducibleWithError.of_subset`,
  `Cslib.Complexity.PromiseProblem.RPReducible.of_subset`: monotonicity, reflexivity, and lifting
  of deterministic reductions.
* `Cslib.Complexity.PromiseProblem.RPReducibleWithError.trans`,
  `Cslib.Complexity.PromiseProblem.RPReducibleWithError.trans_add`,
  `Cslib.Complexity.PromiseProblem.RPReducibleWithError.of_computableInPolyTime`,
  `Cslib.Complexity.PromiseProblem.PolyTimeReducible.trans_rpReducibleWithError`,
  `Cslib.Complexity.PromiseProblem.RPReducibleWithError.trans_polyTimeReducible`,
  `Cslib.Complexity.PromiseProblem.PolyTimeReducible.trans_rpReducible`,
  `Cslib.Complexity.PromiseProblem.RPReducible.trans_polyTimeReducible`: composition of randomized
  and deterministic reductions with multiplicative and additive error accounting.
* `Cslib.Complexity.PromiseProblem.RPReducible.mem_PromiseCoRP`,
  `Cslib.Complexity.PromiseProblem.RPReducible.mem_PromiseCoRP_of_mem_PromiseP`,
  `Cslib.Complexity.PromiseProblem.RPReducible.mem_coRP_of_ofSet`,
  `Cslib.Complexity.PromiseProblem.RPReducible.mem_PromiseBPP`,
  `Cslib.Complexity.PromiseProblem.RPReducible.mem_BPP_of_ofSet`,
  `Cslib.Complexity.PromiseProblem.RPReducible.mem_PromiseRP_of_compl`,
  `Cslib.Complexity.PromiseProblem.RPReducible.mem_PromiseBPP_of_compl`,
  `Cslib.Complexity.PromiseProblem.RPReducible.mem_RP_of_compl_ofSet`,
  `Cslib.Complexity.PromiseProblem.NP_subset_coRP_of_forall_rpReducible`,
  `Cslib.Complexity.PromiseProblem.NP_subset_BPP_of_forall_rpReducible`: closure of `PromiseCoRP`,
  `PromiseBPP` and `PromiseRP` under randomized one-sided reductions.

## References

* [O. Goldreich, *On promise problems: a survey*][Goldreich2006]
* [R. Ilango, *Approaching MCSP from Above and Below: Hardness for a Conditional Variant and
  AC⁰[p]*, Section 2, p. 34:11][Ilango2020]
* [R. Ilango, B. Loff, I. C. Oliveira, *NP-Hardness of Circuit Minimization for Multi-Output
  Functions*, Section 4.2, Lemmas 15–16, pp. 22:20–22:23][IlangoLoffOliveira2020]
* [S. Hirahara, *NP-Hardness of Learning Programs and Partial MCSP*, ECCC TR22-119, Section 8,
  Lemma 8.3 and Theorem 8.5][Hirahara2022]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
* [L. G. Valiant, V. V. Vazirani, *NP is as Easy as Detecting Unique
  Solutions*, pp. 86–87][ValiantVazirani1986]
-/

@[expose] public section

namespace Cslib.Complexity.PromiseProblem

open Turing.MultiTapeTM Probability

variable {α β γ : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
  {X : PromiseProblem α} {Y Y' : PromiseProblem β} {Z : PromiseProblem γ}

/-! ### Randomized reductions with one-sided error -/

/-- A **randomized polynomial-time many-one reduction with one-sided error** and soundness
threshold `s : α → ℝ` from a promise problem `X` to a promise problem `Y` (library generalization of
the fixed-threshold reduction of [Ilango, Section 2, p. 34:11][Ilango2020] to support general
constant or subconstant soundness thresholds as in
[Ilango, Loff and Oliveira, Section 4.2, Lemmas 15–16, pp. 22:20–22:23][IlangoLoffOliveira2020] and
[Hirahara, ECCC TR22-119, Lemma 8.3, p. 26 and Theorem 8.5, pp. 30–31][Hirahara2022]): a uniform
strict PPT program `R : α → ProbComp β` such that:

* **Completeness (no false negatives on `X.yes`):** for every `a ∈ X.yes`, every supported output
  of `R a` lies in `Y.yes`;
* **Soundness (`s a` on `X.no`):** for every `a ∈ X.no`, `R a` outputs an instance in `Y.no` with
  probability at least `s a`.

This is the `coRP` error orientation (error only on no-instances); the dual `RP` error orientation
(error only on yes-instances) is `RPReducibleWithError encA encB s Xᶜ Yᶜ`
(`rpReducibleWithError_compl_iff`). Because outer measures are non-negative, the soundness
condition at `a ∈ X.no` holds vacuously whenever `s a ≤ 0`. Instances outside `X.yes ∪ X.no` are
unconstrained. -/
def RPReducibleWithError (encA : α ↪ List Bool) (encB : β ↪ List Bool) (s : α → ℝ)
    (X : PromiseProblem α) (Y : PromiseProblem β) : Prop :=
  ∃ R : α → ProbComp β, IsPPTOn encA encB R ∧
    (∀ a ∈ X.yes, ∀ b ∈ (ProbComp.eval (R a)).support, b ∈ Y.yes) ∧
    ∀ a ∈ X.no, s a ≤ ((ProbComp.eval (R a)).toOuterMeasure Y.no).toReal

/-- A **randomized polynomial-time many-one reduction with one-sided error** from a promise problem
`X` to a promise problem `Y`, with the standard soundness threshold `2 / 3`
[Ilango, Section 2, p. 34:11][Ilango2020]: a uniform strict PPT program `R : α → ProbComp β`
mapping every yes-instance of `X` exclusively into `Y.yes` and mapping every no-instance of `X` into
`Y.no` with probability at least `2 / 3`. Following [Ilango2020], this has one-sided error on
no-instances (`coRP` orientation); see `RPReducible.mem_PromiseCoRP` and
`rpReducibleWithError_compl_iff`. -/
abbrev RPReducible (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (X : PromiseProblem α) (Y : PromiseProblem β) : Prop :=
  RPReducibleWithError encA encB (fun _ => 2 / 3) X Y

/-- Characterization of `RPReducibleWithError` using the `Pr[...]` event notation. -/
theorem rpReducibleWithError_iff_probability {s : α → ℝ} [DecidablePred (· ∈ Y.no)] :
    RPReducibleWithError encA encB s X Y ↔
      ∃ R : α → ProbComp β, IsPPTOn encA encB R ∧
        (∀ a ∈ X.yes, ∀ b ∈ (ProbComp.eval (R a)).support, b ∈ Y.yes) ∧
        ∀ a ∈ X.no, s a ≤ Pr[(fun b => decide (b ∈ Y.no)) <$> R a] := by
  simp only [RPReducibleWithError, ProbComp.probability_map_decide_mem]

/-- Characterization of `RPReducible` using the `Pr[...]` event notation. -/
theorem rpReducible_iff_probability [DecidablePred (· ∈ Y.no)] :
    RPReducible encA encB X Y ↔
      ∃ R : α → ProbComp β, IsPPTOn encA encB R ∧
        (∀ a ∈ X.yes, ∀ b ∈ (ProbComp.eval (R a)).support, b ∈ Y.yes) ∧
        ∀ a ∈ X.no, 2 / 3 ≤ Pr[(fun b => decide (b ∈ Y.no)) <$> R a] :=
  rpReducibleWithError_iff_probability

/-- Equivalence of support-based completeness and probability-one completeness for
`RPReducibleWithError`. -/
theorem rpReducibleWithError_iff_toOuterMeasure_eq_one {s : α → ℝ} :
    RPReducibleWithError encA encB s X Y ↔
      ∃ R : α → ProbComp β, IsPPTOn encA encB R ∧
        (∀ a ∈ X.yes, ((ProbComp.eval (R a)).toOuterMeasure Y.yes).toReal = 1) ∧
        ∀ a ∈ X.no, s a ≤ ((ProbComp.eval (R a)).toOuterMeasure Y.no).toReal := by
  simp only [RPReducibleWithError, ENNReal.toReal_eq_one_iff,
    PMF.toOuterMeasure_apply_eq_one_iff, Set.subset_def]

/-- Equivalence of support-based completeness and probability-one completeness for
`RPReducible` [Ilango, Section 2, p. 34:11][Ilango2020]. -/
theorem rpReducible_iff_toOuterMeasure_eq_one :
    RPReducible encA encB X Y ↔
      ∃ R : α → ProbComp β, IsPPTOn encA encB R ∧
        (∀ a ∈ X.yes, ((ProbComp.eval (R a)).toOuterMeasure Y.yes).toReal = 1) ∧
        ∀ a ∈ X.no, 2 / 3 ≤ ((ProbComp.eval (R a)).toOuterMeasure Y.no).toReal :=
  rpReducibleWithError_iff_toOuterMeasure_eq_one

/-- Lowering the soundness threshold preserves `RPReducibleWithError`. -/
theorem RPReducibleWithError.mono {s₁ s₂ : α → ℝ}
    (h : RPReducibleWithError encA encB s₁ X Y) (hs : ∀ a ∈ X.no, s₂ a ≤ s₁ a) :
    RPReducibleWithError encA encB s₂ X Y :=
  let ⟨R, hR, hyes, hno⟩ := h
  ⟨R, hR, hyes, fun a ha => (hs a ha).trans (hno a ha)⟩

/-- **Complement-duality identity for `RPReducibleWithError`** (library identity): a randomized
reduction between the complement promise problems `Xᶜ` and `Yᶜ` with threshold `s` is a randomized
reduction from `X` to `Y` in the dual one-sided error orientation, mapping no-instances exclusively
into `Y.no` and mapping yes-instances into `Y.yes` with probability at least `s a`. When `s a` is an
inverse-polynomial threshold such as `1 / (4 * n)`, this represents the unamplified one-sided
orientation of Valiant and Vazirani [Valiant and Vazirani, Section 1, Theorem 1.1, pp. 86–87]
[ValiantVazirani1986], [Goldreich, Section 6.2][Goldreich2006]. -/
theorem rpReducibleWithError_compl_iff {s : α → ℝ} :
    RPReducibleWithError encA encB s Xᶜ Yᶜ ↔
      ∃ R : α → ProbComp β, IsPPTOn encA encB R ∧
        (∀ a ∈ X.no, ∀ b ∈ (ProbComp.eval (R a)).support, b ∈ Y.no) ∧
        ∀ a ∈ X.yes, s a ≤ ((ProbComp.eval (R a)).toOuterMeasure Y.yes).toReal :=
  Iff.rfl

open Classical in
/-- **Seeded-function characterization of `RPReducible`** [Ilango, Section 2, p. 34:11][Ilango2020]:
`X` is `RPReducible` to `Y` if and only if there are a polynomial `p` and a function
`f : α × List Bool → β`, computable in polynomial time with respect to `encPair encA encBits` and
`encB`, such that for every `a ∈ X.yes` and every random string `r` of length `p(|a|)` we have
`f(a, r) ∈ Y.yes`, and for every `a ∈ X.no` at least two thirds of the random strings `r` of length
`p(|a|)` satisfy `f(a, r) ∈ Y.no`. -/
theorem rpReducible_iff_exists_seeded :
    RPReducible encA encB X Y ↔
      ∃ (p : Polynomial ℕ) (f : α × List Bool → β),
        ComputableInPolyTime f (encPair encA encBits) encB ∧
        (∀ a ∈ X.yes, ∀ r : Fin (p.eval (encA a).length) → Bool, f (a, List.ofFn r) ∈ Y.yes) ∧
        ∀ a ∈ X.no, 2 * 2 ^ p.eval (encA a).length ≤
          3 * (Finset.univ.filter fun r : Fin (p.eval (encA a).length) → Bool =>
            f (a, List.ofFn r) ∈ Y.no).card := by
  constructor
  · rintro ⟨R, hR, hyes, hno⟩
    obtain ⟨c, d, evalR, hevalR, hsupp, hlaw⟩ := hR.exists_total_seeded_evaluator
    refine ⟨Polynomial.C c * (Polynomial.X + 1) ^ d, fun x => evalR x.1 x.2, .of_tidy hevalR,
      fun a ha r => hyes a ha _ (hsupp a (List.ofFn r)), fun a ha => ?_⟩
    have hp : (Polynomial.C c * (Polynomial.X + 1) ^ d).eval (encA a).length =
        c * ((encA a).length + 1) ^ d := by simp
    rw [hp]
    have hprob := hno a ha
    rw [hlaw a _ le_rfl, BitString.toOuterMeasure_map_uniformList_toReal,
      le_div_iff₀ (by positivity)] at hprob
    have h3 : (2 : ℝ) * 2 ^ (c * ((encA a).length + 1) ^ d) ≤
        3 * ((Finset.univ.filter fun r : Fin (c * ((encA a).length + 1) ^ d) → Bool =>
          evalR a (List.ofFn r) ∈ Y.no).card : ℝ) := by
      linarith
    exact_mod_cast h3
  · rintro ⟨p, f, hf, hyes, hno⟩
    let R (a : α) : ProbComp β :=
      (fun w => f (a, w)) <$> BitString.sampleList (p.eval (encA a).length)
    have hR : IsPPTOn encA encB R :=
      IsPPTOn.of_seeded
        ((ComputableInPolyTime.unary_eval p).comp (ComputableInPolyTime.encoding_length encA)) hf
    refine ⟨R, hR, fun a ha b hb => ?_, fun a ha => ?_⟩
    · simp only [R, ProbComp.eval_map, BitString.eval_sampleList,
        PMF.mem_support_map_iff, BitString.mem_support_uniformList_iff] at hb
      obtain ⟨w, hw, rfl⟩ := hb
      have hr := hyes a ha fun i => w[i.val]'(by omega)
      rwa [show (List.ofFn fun i : Fin (p.eval (encA a).length) => w[i.val]'(by omega)) = w from
        List.ext_getElem (by simp [hw]) fun i _ _ => by simp] at hr
    · simp only [R, ProbComp.eval_map, BitString.eval_sampleList]
      rw [BitString.toOuterMeasure_map_uniformList_toReal, le_div_iff₀ (by positivity)]
      have h3 : (2 : ℝ) * 2 ^ p.eval (encA a).length ≤
          3 * ((Finset.univ.filter fun r : Fin (p.eval (encA a).length) → Bool =>
            f (a, List.ofFn r) ∈ Y.no).card : ℝ) := by
        exact_mod_cast hno a ha
      linarith

/-! ### Lifting deterministic reductions and structural closure -/

/-- Every deterministic polynomial-time reduction of promise problems lifts to a randomized
reduction with soundness `1` (zero error). -/
theorem PolyTimeReducible.rpReducibleWithError (h : PolyTimeReducible encA encB X Y) :
    RPReducibleWithError encA encB (fun _ => 1) X Y := by
  obtain ⟨f, hf, hyes, hno⟩ := h
  refine ⟨fun a => pure (f a), hf.isPPTOn, fun a ha b hb => ?_, fun a ha => ?_⟩
  · simp only [ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hb
    exact hb ▸ hyes ha
  · have hmem : f a ∈ Y.no := hno ha
    simp [ProbComp.eval_pure, hmem]

/-- Every deterministic polynomial-time reduction of promise problems is a randomized one-sided
reduction (`RPReducible`). -/
theorem PolyTimeReducible.rpReducible (h : PolyTimeReducible encA encB X Y) :
    RPReducible encA encB X Y :=
  h.rpReducibleWithError.mono fun _ _ => by norm_num

/-- Every deterministic polynomial-time reduction between decision problems gives an `RPReducible`
reduction between their promise problems. -/
theorem _root_.Cslib.Complexity.PolyTimeReducible.rpReducible_ofSet {A : Set α} {B : Set β}
    (h : Complexity.PolyTimeReducible encA encB A B) :
    RPReducible encA encB (ofSet A) (ofSet B) :=
  (polyTimeReducible_ofSet_iff.mpr h).rpReducible

/-- Every promise problem reduces to itself by a zero-error randomized reduction. -/
@[refl]
theorem RPReducibleWithError.refl (encA : α ↪ List Bool) (X : PromiseProblem α) :
    RPReducibleWithError encA encA (fun _ => 1) X X :=
  (PolyTimeReducible.refl encA X).rpReducibleWithError

/-- Every promise problem is `RPReducible` to itself. -/
@[refl]
theorem RPReducible.refl (encA : α ↪ List Bool) (X : PromiseProblem α) :
    RPReducible encA encA X X :=
  (PolyTimeReducible.refl encA X).rpReducible

/-- Enlarging the target promise preserves `RPReducibleWithError`. -/
theorem RPReducibleWithError.of_subset {s : α → ℝ}
    (h : RPReducibleWithError encA encB s X Y) (hyes : Y.yes ⊆ Y'.yes) (hno : Y.no ⊆ Y'.no) :
    RPReducibleWithError encA encB s X Y' := by
  obtain ⟨R, hR, hRyes, hRno⟩ := h
  refine ⟨R, hR, fun a ha b hb => hyes (hRyes a ha b hb), fun a ha => (hRno a ha).trans ?_⟩
  exact ENNReal.toReal_mono (PMF.toOuterMeasure_ne_top _ _)
    ((ProbComp.eval (R a)).toOuterMeasure.mono hno)

/-- Enlarging the target promise preserves `RPReducible`. -/
theorem RPReducible.of_subset (h : RPReducible encA encB X Y) (hyes : Y.yes ⊆ Y'.yes)
    (hno : Y.no ⊆ Y'.no) : RPReducible encA encB X Y' :=
  RPReducibleWithError.of_subset h hyes hno

/-- **Composition of randomized one-sided reductions (multiplicative soundness, library lemma)**:
composing a reduction from `X` to `Y` with soundness `s₁ a` and a reduction from `Y` to `Z` with
uniform soundness `s₂` yields a reduction from `X` to `Z` with soundness `s₁ a * s₂`. -/
theorem RPReducibleWithError.trans {s₁ : α → ℝ} {s₂ : ℝ}
    (hXY : RPReducibleWithError encA encB s₁ X Y)
    (hYZ : RPReducibleWithError encB encC (fun _ => s₂) Y Z)
    (hs₂ : 0 ≤ s₂) :
    RPReducibleWithError encA encC (fun a => s₁ a * s₂) X Z := by
  obtain ⟨R₁, hR₁, hyes₁, hno₁⟩ := hXY
  obtain ⟨R₂, hR₂, hyes₂, hno₂⟩ := hYZ
  refine ⟨fun a => R₁ a >>= R₂, hR₁.bind hR₂, fun a ha c hc => ?_, fun a ha => ?_⟩
  · simp only [ProbComp.eval_bind, PMF.mem_support_bind_iff] at hc
    obtain ⟨b, hb, hc⟩ := hc
    exact hyes₂ b (hyes₁ a ha b hb) c hc
  · rw [ProbComp.eval_bind]
    exact PMF.toOuterMeasure_bind_ge_mul (ProbComp.eval (R₁ a)) (fun b => ProbComp.eval (R₂ b))
      Y.no Z.no hs₂ (hno₁ a ha) fun b _ hb => hno₂ b hb

/-- **Composition of randomized one-sided reductions (additive error accounting, library lemma)**:
composing a reduction from `X` to `Y` with soundness `s₁ a` (error `1 - s₁ a`) and a reduction from
`Y` to `Z` with soundness `s₂` (error `1 - s₂`) yields a reduction from `X` to `Z` with soundness
`s₁ a + s₂ - 1`. Note that when `s₁ a + s₂ ≤ 1`, the resulting threshold `s₁ a + s₂ - 1 ≤ 0` holds
vacuously by non-negativity of outer measure. -/
theorem RPReducibleWithError.trans_add {s₁ : α → ℝ} {s₂ : ℝ}
    (hXY : RPReducibleWithError encA encB s₁ X Y)
    (hYZ : RPReducibleWithError encB encC (fun _ => s₂) Y Z)
    (hs₂ : s₂ ≤ 1) :
    RPReducibleWithError encA encC (fun a => s₁ a + s₂ - 1) X Z := by
  obtain ⟨R₁, hR₁, hyes₁, hno₁⟩ := hXY
  obtain ⟨R₂, hR₂, hyes₂, hno₂⟩ := hYZ
  refine ⟨fun a => R₁ a >>= R₂, hR₁.bind hR₂, fun a ha c hc => ?_, fun a ha => ?_⟩
  · simp only [ProbComp.eval_bind, PMF.mem_support_bind_iff] at hc
    obtain ⟨b, hb, hc⟩ := hc
    exact hyes₂ b (hyes₁ a ha b hb) c hc
  · rw [ProbComp.eval_bind]
    have hfail := PMF.toOuterMeasure_bind_failure_toReal_le
      (ProbComp.eval (R₁ a)) (fun b => ProbComp.eval (R₂ b)) Y.no Z.noᶜ
      (sub_nonneg.mpr hs₂) fun b _ hb => by
        have hadd := PMF.toOuterMeasure_toReal_add_compl (ProbComp.eval (R₂ b)) Z.no
        have h := hno₂ b hb
        linarith
    have hadd₁ := PMF.toOuterMeasure_toReal_add_compl (ProbComp.eval (R₁ a)) Y.no
    have hadd₂ := PMF.toOuterMeasure_toReal_add_compl
      ((ProbComp.eval (R₁ a)).bind fun b => ProbComp.eval (R₂ b)) Z.no
    have h₁ := hno₁ a ha
    linarith

/-- Precomposing an `RPReducibleWithError` reduction with an explicit deterministic polynomial-time
reduction `f` from `X` to `Y` pulls back its soundness threshold along `f`. -/
theorem RPReducibleWithError.of_computableInPolyTime {s : β → ℝ} {f : α → β}
    (hf : ComputableInPolyTime f encA encB) (hyes : Set.MapsTo f X.yes Y.yes)
    (hno : Set.MapsTo f X.no Y.no) (hYZ : RPReducibleWithError encB encC s Y Z) :
    RPReducibleWithError encA encC (fun a => s (f a)) X Z := by
  obtain ⟨R, hR, hRyes, hRno⟩ := hYZ
  exact ⟨fun a => R (f a), hR.preprocess hf,
    fun a ha c hc => hRyes (f a) (hyes ha) c hc, fun a ha => hRno (f a) (hno ha)⟩

/-- Precomposing an `RPReducibleWithError` reduction at a uniform threshold with a deterministic
polynomial-time reduction preserves its soundness threshold. Because `PolyTimeReducible`
existentially quantifies over the reduction function `f`, the output threshold cannot refer to
`f a`; for an instance-dependent threshold `fun a => s (f a)`, use
`RPReducibleWithError.of_computableInPolyTime` with an explicit `f`. -/
theorem PolyTimeReducible.trans_rpReducibleWithError {s : ℝ}
    (hXY : PolyTimeReducible encA encB X Y)
    (hYZ : RPReducibleWithError encB encC (fun _ => s) Y Z) :
    RPReducibleWithError encA encC (fun _ => s) X Z := by
  obtain ⟨f, hf, hyes, hno⟩ := hXY
  exact hYZ.of_computableInPolyTime hf hyes hno

/-- Postcomposing an `RPReducibleWithError` reduction with a deterministic polynomial-time reduction
preserves its soundness threshold. -/
theorem RPReducibleWithError.trans_polyTimeReducible {s : α → ℝ}
    (hXY : RPReducibleWithError encA encB s X Y) (hYZ : PolyTimeReducible encB encC Y Z) :
    RPReducibleWithError encA encC s X Z := by
  obtain ⟨R, hR, hyes, hno⟩ := hXY
  obtain ⟨g, hg, gyes, gno⟩ := hYZ
  refine ⟨fun a => g <$> R a, hR.map_with (hg.comp (.snd encA encB)),
    fun a ha c hc => ?_, fun a ha => ?_⟩
  · simp only [ProbComp.eval_map, PMF.mem_support_map_iff] at hc
    obtain ⟨b, hb, rfl⟩ := hc
    exact gyes (hyes a ha b hb)
  · simp only [ProbComp.eval_map, PMF.toOuterMeasure_map_apply]
    refine (hno a ha).trans (ENNReal.toReal_mono (PMF.toOuterMeasure_ne_top _ _) ?_)
    exact (ProbComp.eval (R a)).toOuterMeasure.mono gno.subset_preimage

/-- Precomposing an `RPReducible` reduction with a deterministic polynomial-time reduction yields
an `RPReducible` reduction. -/
theorem PolyTimeReducible.trans_rpReducible (hXY : PolyTimeReducible encA encB X Y)
    (hYZ : RPReducible encB encC Y Z) : RPReducible encA encC X Z :=
  hXY.trans_rpReducibleWithError hYZ

/-- Postcomposing an `RPReducible` reduction with a deterministic polynomial-time reduction yields
an `RPReducible` reduction. -/
theorem RPReducible.trans_polyTimeReducible (hXY : RPReducible encA encB X Y)
    (hYZ : PolyTimeReducible encB encC Y Z) : RPReducible encA encC X Z :=
  RPReducibleWithError.trans_polyTimeReducible hXY hYZ

/-! ### Closure of `PromiseCoRP`, `PromiseBPP` and `PromiseRP` under `RPReducible` -/

/-- Running a Boolean experiment twice independently and taking `&&` squares its acceptance
probability. -/
private def and2 (M : α → ProbComp Bool) (a : α) : ProbComp Bool :=
  M a >>= fun b₁ => (fun b₂ => b₁ && b₂) <$> M a

private theorem isPPTOn_and2 {M : α → ProbComp Bool} (hM : IsPPTOn encA encBool M) :
    IsPPTOn encA encBool (and2 M) := by
  unfold and2
  exact hM.bind_with ((hM.preprocess (.fst encA encBool)).map_with
    (f := fun p b₂ => p.2 && b₂) (by fun_prop))

private theorem probability_and2 (M : α → ProbComp Bool) (a : α) :
    Pr[and2 M a] = Pr[M a] * Pr[M a] := by
  change Pr[M a >>= fun b₁ => (fun b₂ => b₁ && b₂) <$> M a] = _
  rw [ProbComp.probability_bind, Fintype.sum_bool]
  simp only [Bool.true_and, Bool.false_and]
  have htrue : Pr[(fun b₂ : Bool => b₂) <$> M a] = Pr[M a] := by simp
  have hfalse : Pr[(fun _ : Bool => false) <$> M a] = 0 := by
    simp [ProbComp.eval_map, PMF.map_apply]
  rw [htrue, hfalse, mul_zero, add_zero]

/-- **`PromiseCoRP` is closed under `RPReducible`** (library lemma): if `X` reduces to `Y` by a
randomized one-sided reduction and `Y ∈ PromiseCoRP encB`, then `X ∈ PromiseCoRP encA`. -/
theorem RPReducible.mem_PromiseCoRP (hXY : RPReducible encA encB X Y)
    (hY : Y ∈ PromiseCoRP encB) : X ∈ PromiseCoRP encA := by
  obtain ⟨R, hR, hyesR, hnoR⟩ := hXY
  -- a solver for `Yᶜ` accepting every no-instance of `Y` with probability at least `3 / 4`
  obtain ⟨p, V, hV, hYV⟩ := mem_PromiseRP_iff_forall_solvesWithOneSidedErrorExponent.1 hY 2
  let M (b : β) : ProbComp Bool :=
    (fun w => V (b, w)) <$> BitString.sampleList (p.eval (encB b).length)
  have hM (b : β) (hb : b ∈ Y.no) : 3 / 4 ≤ Pr[M b] := by
    rw [probability_sampleList_verifier, le_div_iff₀ (by positivity)]
    have hsum := acceptCount_add_card_filter_eq_false (V := V) (a := b)
      (n := p.eval (encB b).length)
    have h := (hYV b).1 hb
    simp only [Polynomial.eval_ofNat] at h
    have h' : (3 : ℝ) * 2 ^ p.eval (encB b).length ≤ 4 * acceptCount V b (p.eval (encB b).length) :=
      by exact_mod_cast (by omega)
    linarith
  -- on a no-instance of `X`, the composition accepts with probability at least `2 / 3 * 3 / 4`
  refine compl_mem_PromiseRP_iff.1 (mem_PromiseRP_iff_exists_isPPTOn.2
    ⟨fun a => R a >>= M, hR.bind (IsPPTOn.of_seeded ((ComputableInPolyTime.unary_eval p).comp
      (ComputableInPolyTime.encoding_length encB)) hV), fun a ha => ?_, fun a ha hmem => ?_⟩)
  · have h := PMF.toOuterMeasure_bind_ge_mul (ProbComp.eval (R a)) (fun b => ProbComp.eval (M b))
      Y.no {true} (by norm_num : (0 : ℝ) ≤ 3 / 4) (hnoR a ha) fun b _ hb => by
        rw [PMF.toOuterMeasure_apply_singleton]
        exact hM b hb
    rw [← ProbComp.eval_bind, PMF.toOuterMeasure_apply_singleton] at h
    linarith
  · -- on a yes-instance of `X`, every output of the reduction is a yes-instance of `Y`
    simp only [M, ProbComp.eval_bind, ProbComp.eval_map, BitString.eval_sampleList,
      PMF.mem_support_bind_iff, PMF.mem_support_map_iff,
      BitString.mem_support_uniformList_iff] at hmem
    obtain ⟨b, hb, w, hw, hVw⟩ := hmem
    have := ((hYV.solvesWithOneSidedError fun _ => by simp).exists_certificate).2 b
      (hyesR a ha b hb) w hw
    rw [this] at hVw
    exact Bool.noConfusion hVw

/-- If `X` is `RPReducible` to `Y` and `Y ∈ PromiseP encB`, then `X ∈ PromiseCoRP encA`. -/
theorem RPReducible.mem_PromiseCoRP_of_mem_PromiseP (hXY : RPReducible encA encB X Y)
    (hY : Y ∈ PromiseP encB) : X ∈ PromiseCoRP encA :=
  hXY.mem_PromiseCoRP (PromiseP_subset_PromiseCoRP hY)

/-- If a decision problem `A` is `RPReducible` to `Y` and `Y ∈ PromiseCoRP encB`, then
`A ∈ coRP encA`. -/
theorem RPReducible.mem_coRP_of_ofSet {A : Set α} (hAY : RPReducible encA encB (ofSet A) Y)
    (hY : Y ∈ PromiseCoRP encB) : A ∈ coRP encA :=
  ofSet_mem_PromiseCoRP.mp (hAY.mem_PromiseCoRP hY)

/-- **`PromiseBPP` is closed under `RPReducible`** (library lemma; on the promise classes of
[Goldreich, Definition 1.2][Goldreich2006], amplifying as in
[Sipser, Lemma 10.5][Sipser2013]): if `X` reduces to `Y` by a randomized one-sided reduction and
`Y ∈ PromiseBPP encB`, then `X ∈ PromiseBPP encA`. -/
theorem RPReducible.mem_PromiseBPP (hXY : RPReducible encA encB X Y)
    (hY : Y ∈ PromiseBPP encB) : X ∈ PromiseBPP encA := by
  obtain ⟨R, hR, hyesR, hnoR⟩ := hXY
  -- a solver for `Y` with error at most `1 / 8`
  obtain ⟨p, V, hV, hYV⟩ := mem_PromiseBPP_iff_forall_solvesWithErrorExponent.1 hY 3
  let M (b : β) : ProbComp Bool :=
    (fun w => V (b, w)) <$> BitString.sampleList (p.eval (encB b).length)
  have hMyes (b : β) (hb : b ∈ Y.yes) : 7 / 8 ≤ Pr[M b] := by
    rw [probability_sampleList_verifier, le_div_iff₀ (by positivity)]
    have hsum := acceptCount_add_card_filter_eq_false (V := V) (a := b)
      (n := p.eval (encB b).length)
    have h := (hYV b).1 hb
    simp only [ErrorExponentAt, Bool.not_true, Polynomial.eval_ofNat] at h
    have h' : (7 : ℝ) * 2 ^ p.eval (encB b).length ≤ 8 * acceptCount V b (p.eval (encB b).length) :=
      by exact_mod_cast (by omega)
    linarith
  have hMno (b : β) (hb : b ∈ Y.no) : Pr[M b] ≤ 1 / 8 := by
    rw [probability_sampleList_verifier, div_le_iff₀ (by positivity)]
    have h := (hYV b).2 hb
    simp only [ErrorExponentAt, Bool.not_false, Polynomial.eval_ofNat] at h
    rw [← acceptCount] at h
    have h' : (8 : ℝ) * acceptCount V b (p.eval (encB b).length) ≤ 2 ^ p.eval (encB b).length :=
      by exact_mod_cast h
    linarith
  -- one run of `R` followed by `M` accepts yes-instances with probability at least `7 / 8` and
  -- no-instances with probability at most `1 / 3 + 1 / 8`; two runs must both accept
  let T (a : α) : ProbComp Bool := R a >>= M
  have hT : IsPPTOn encA encBool T := hR.bind (IsPPTOn.of_seeded
    ((ComputableInPolyTime.unary_eval p).comp (ComputableInPolyTime.encoding_length encB)) hV)
  refine mem_PromiseBPP_iff_exists_isPPTOn.mpr ⟨and2 T, isPPTOn_and2 hT, fun a ha => ?_,
    fun a ha => ?_⟩
  · have hT_yes : 7 / 8 ≤ Pr[T a] := by
      have hyes_one : ((ProbComp.eval (R a)).toOuterMeasure Y.yes).toReal = 1 :=
        (ENNReal.toReal_eq_one_iff _).mpr
          ((PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (hyesR a ha))
      have h := PMF.toOuterMeasure_bind_ge_mul (ProbComp.eval (R a)) (fun y => ProbComp.eval (M y))
        Y.yes {true} (by norm_num : (0 : ℝ) ≤ 7 / 8) hyes_one.ge
        fun y _ hy => by
          rw [PMF.toOuterMeasure_apply_singleton]
          exact hMyes y hy
      rwa [one_mul, ← ProbComp.eval_bind, PMF.toOuterMeasure_apply_singleton] at h
    rw [probability_and2]
    nlinarith
  · have hT_no : Pr[T a] ≤ 11 / 24 := by
      have hfail := PMF.toOuterMeasure_bind_failure_toReal_le
        (ProbComp.eval (R a)) (fun y => ProbComp.eval (M y)) Y.no {true}
        (by norm_num : (0 : ℝ) ≤ 1 / 8) fun y _ hy => by
          rw [PMF.toOuterMeasure_apply_singleton]
          exact hMno y hy
      rw [← ProbComp.eval_bind, PMF.toOuterMeasure_apply_singleton] at hfail
      have hadd := PMF.toOuterMeasure_toReal_add_compl (ProbComp.eval (R a)) Y.no
      have hno := hnoR a ha
      linarith
    have hT_nn : 0 ≤ Pr[T a] := ENNReal.toReal_nonneg
    have hand2 : Pr[and2 T a] ≤ 1 / 3 := by
      rw [probability_and2]
      nlinarith
    rw [ProbComp.probability_not]
    linarith

/-- If a decision problem `A` is `RPReducible` to `Y` and `Y ∈ PromiseBPP encB`, then
`A ∈ BPP encA`. -/
theorem RPReducible.mem_BPP_of_ofSet {A : Set α} (hAY : RPReducible encA encB (ofSet A) Y)
    (hY : Y ∈ PromiseBPP encB) : A ∈ BPP encA :=
  ofSet_mem_PromiseBPP.mp (hAY.mem_PromiseBPP hY)

/-- **`PromiseRP` is closed under dual (`Xᶜ` to `Yᶜ`) `RPReducible` reductions** (library lemma). -/
theorem RPReducible.mem_PromiseRP_of_compl (hXY : RPReducible encA encB Xᶜ Yᶜ)
    (hY : Y ∈ PromiseRP encB) : X ∈ PromiseRP encA :=
  compl_mem_PromiseCoRP_iff.mp (hXY.mem_PromiseCoRP (compl_mem_PromiseRP_iff.mp hY))

/-- **`PromiseBPP` is closed under dual (`Xᶜ` to `Yᶜ`) `RPReducible` reductions.** -/
theorem RPReducible.mem_PromiseBPP_of_compl (hXY : RPReducible encA encB Xᶜ Yᶜ)
    (hY : Y ∈ PromiseBPP encB) : X ∈ PromiseBPP encA := by
  simpa using compl_mem_PromiseBPP (hXY.mem_PromiseBPP (compl_mem_PromiseBPP hY))

/-- If a decision problem `A` reduces to `Y` in the dual one-sided error orientation
(`RPReducible encA encB (ofSet A)ᶜ Yᶜ`) and `Y ∈ PromiseRP encB`, then `A ∈ RP encA`. -/
theorem RPReducible.mem_RP_of_compl_ofSet {A : Set α}
    (hAY : RPReducible encA encB (ofSet A)ᶜ Yᶜ) (hY : Y ∈ PromiseRP encB) : A ∈ RP encA :=
  ofSet_mem_PromiseRP.mp (hAY.mem_PromiseRP_of_compl hY)

/-- If every problem in `NP encA` reduces to `Y` via `RPReducible` and `Y ∈ PromiseCoRP encB`,
then `NP encA ⊆ coRP encA` (library lemma). -/
theorem NP_subset_coRP_of_forall_rpReducible
    (hHard : ∀ A ∈ NP encA, RPReducible encA encB (ofSet A) Y) (hY : Y ∈ PromiseCoRP encB) :
    NP encA ⊆ coRP encA :=
  fun A hA => (hHard A hA).mem_coRP_of_ofSet hY

/-- If every problem in `NP encA` reduces to `Y` via `RPReducible` and `Y ∈ PromiseBPP encB`,
then `NP encA ⊆ BPP encA` (library lemma). -/
theorem NP_subset_BPP_of_forall_rpReducible
    (hHard : ∀ A ∈ NP encA, RPReducible encA encB (ofSet A) Y) (hY : Y ∈ PromiseBPP encB) :
    NP encA ⊆ BPP encA :=
  fun A hA => (hHard A hA).mem_BPP_of_ofSet hY

end Cslib.Complexity.PromiseProblem
