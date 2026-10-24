/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.BPP
public import Complexity.Computability.Complexity.Classes.Promise.Basic
public import Complexity.Computability.Complexity.Classes.RP
public import Complexity.Computability.Complexity.Problems.SAT
public import Complexity.Computability.Complexity.Reduction
public import Complexity.Computability.Probabilistic.PPT
public import Complexity.Languages.Probabilistic.Notation
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Complexity.Computability.Complexity.Classes.NP.Witness
import Complexity.Computability.Complexity.Classes.RP.Closure
import Complexity.Computability.Complexity.Classes.SharpP.Combinators
import Complexity.Computability.Complexity.Classes.SharpP.Probability
import Complexity.Computability.Complexity.CookLevin.Completeness
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Probabilistic.CoinTape
import Complexity.Computability.Probabilistic.PPT.Capture
import Complexity.Computability.Probabilistic.Sampling
import Complexity.Probability.PMF.Event
import Complexity.Probability.PMF.Uniform

/-!
# Reductions of promise problems, randomized reductions, and gap problems

Hardness of approximation is stated through **gap problems** [Arora and Barak, Chapter
11][AroraBarak09]. For a maximization objective `val`, the gap problem `gapMax val c s` is the
promise problem whose yes-instances have value at least `c` and whose no-instances have value at
most `s`, below `c`. When this gap problem is NP-hard, the maximization problem is **NP-hard to
approximate** within every ratio better than `s / c`: an algorithm estimating `val` from below
within such a ratio would tell the two kinds of instances apart.

Reductions between promise problems are the polynomial-time many-one reductions of
`Cslib.Complexity.PolyTimeReducible`, required to map yes-instances to yes-instances and
no-instances to no-instances; on decision problems they are exactly those reductions
(`PromiseProblem.polyTimeReducible_ofSet_iff`). Between gap problems they are the
**gap-preserving reductions** used to transfer inapproximability from one problem to another.
A promise problem is NP-hard when every problem in `NP` reduces to it; for decision problems this
is `Cslib.Complexity.NPHard` (`PromiseProblem.npHard_ofSet_iff`). An NP-hard promise problem solved
in polynomial time gives `P = NP` (`PromiseProblem.NPHard.P_eq_NP_of_mem_PromiseP`).

Reductions of promise problems are Karp reductions in the sense of Goldreich's survey
[Goldreich2006]: one function serves for every instance in the promise. This is stronger than
asking every problem separating the yes-instances from the no-instances to be NP-hard, which
`PromiseProblem.NPHard.npHard_of_subset` derives.

For randomized hardness results in metacomplexity [Ilango, Section 2, p. 34:11][Ilango2020],
[Ilango, Loff and Oliveira, Section 4.2, Lemmas 15–16, pp. 22:20–22:23][IlangoLoffOliveira2020],
[Hirahara, ECCC TR22-119, Lemma 8.3, p. 26 and Theorem 8.5, pp. 30–31][Hirahara2022], a
**randomized polynomial-time many-one reduction with one-sided error**
(`PromiseProblem.RPReducible`, and the library's threshold-indexed generalization
`PromiseProblem.RPReducibleWithError`) is a uniform strict PPT program `R : α → ProbComp β` that
maps every yes-instance of `X` exclusively into `Y.yes` and maps every no-instance of `X` into
`Y.no` with probability at least `2 / 3` (or `s a`). This orientation matches the metacomplexity
sources, where upper bounds on circuit or Kolmogorov complexity hold deterministically for every
random choice on yes-instances while lower bounds on no-instances hold with high probability.
Equivalence and convention bridges connect `RPReducible` and `RPReducibleWithError` to:

* the `Pr[...]` event notation (`PromiseProblem.rpReducible_iff_probability`),
* probability-one completeness (`PromiseProblem.rpReducible_iff_toOuterMeasure_eq_one`),
* explicit seeded polynomial-time functions reading a random string of polynomial length
  (`PromiseProblem.rpReducible_iff_exists_seeded`), and
* the dual one-sided error orientation through promise-problem complement
  (`PromiseProblem.rpReducibleWithError_compl_iff`, `PromiseProblem.rpReducible_compl_iff`), which
  for an inverse-polynomial threshold `s a` represents the unamplified one-sided orientation of
  Valiant and Vazirani [Valiant and Vazirani, pp. 86–87][ValiantVazirani1986].

The probabilistic promise classes `PromiseBPP`, `PromiseRP` and `PromiseCoRP` follow Goldreich's
semantic definitions [Goldreich, July 2005 author version, Definition 1.2, p. 4 and Section 6.2,
p. 18][Goldreich2006], requiring bounded or one-sided error only on instances in the promise, and
`PromiseBPP` and `PromiseCoRP` are closed under `RPReducible`
(`PromiseProblem.RPReducible.mem_PromiseBPP`, `PromiseProblem.RPReducible.mem_PromiseCoRP`).

## Main definitions

* `Cslib.Complexity.PromiseProblem.SolvesWithBoundedError`,
  `Cslib.Complexity.PromiseProblem.SolvesWithOneSidedError`: Goldreich's bounded-error and
  one-sided-error conditions on a promise problem.
* `Cslib.Complexity.PromiseBPP`, `Cslib.Complexity.PromiseRP`, `Cslib.Complexity.PromiseCoRP`:
  the probabilistic classes of promise problems.
* `Cslib.Complexity.PromiseProblem.PolyTimeReducible`: polynomial-time reductions of promise
  problems, which between gap problems are the gap-preserving reductions.
* `Cslib.Complexity.PromiseProblem.NPHard`: every problem in `NP` reduces to the promise problem.
* `Cslib.Complexity.PromiseProblem.RPReducibleWithError`,
  `Cslib.Complexity.PromiseProblem.RPReducible`: randomized polynomial-time many-one reductions
  with one-sided error on promise problems.
* `Cslib.Complexity.PromiseProblem.gapMax`, `Cslib.Complexity.PromiseProblem.gapMin`: the gap
  problems of a maximization and of a minimization objective.
* `Cslib.Complexity.PromiseProblem.restrict`: a promise problem restricted to a set of instances.

## Main results

* `Cslib.Complexity.ofSet_mem_PromiseBPP`, `Cslib.Complexity.ofSet_mem_PromiseRP`,
  `Cslib.Complexity.ofSet_mem_PromiseCoRP`, `Cslib.Complexity.promiseClass_BPP_subset_PromiseBPP`,
  `Cslib.Complexity.promiseClass_RP_subset_PromiseRP`,
  `Cslib.Complexity.promiseClass_coRP_subset_PromiseCoRP`: agreement with `BPP`, `RP` and `coRP`
  on decision problems and inclusion of `promiseClass`.
* `Cslib.Complexity.mem_PromiseBPP_iff_exists_isPPTOn`,
  `Cslib.Complexity.mem_PromiseRP_iff_exists_isPPTOn`,
  `Cslib.Complexity.mem_PromiseCoRP_iff_exists_isPPTOn`: characterizations by uniform strict PPT
  programs.
* `Cslib.Complexity.PromiseProblem.polyTimeReducible_ofSet_iff`,
  `Cslib.Complexity.PromiseProblem.npHard_ofSet_iff`: on decision problems, the notions are
  `Cslib.Complexity.PolyTimeReducible` and `Cslib.Complexity.NPHard`.
* `Cslib.Complexity.PromiseProblem.PolyTimeReducible.trans`,
  `Cslib.Complexity.PromiseProblem.NPHard.trans`: reductions compose and transfer hardness.
* `Cslib.Complexity.PromiseProblem.PolyTimeReducible.mem_PromiseP`,
  `Cslib.Complexity.PromiseProblem.PolyTimeReducible.mem_PromiseNP`,
  `Cslib.Complexity.PromiseProblem.PolyTimeReducible.mem_PromiseBPP`,
  `Cslib.Complexity.PromiseProblem.PolyTimeReducible.mem_PromiseRP`,
  `Cslib.Complexity.PromiseProblem.PolyTimeReducible.mem_PromiseCoRP`: closure of promise classes
  under deterministic reductions.
* `Cslib.Complexity.PromiseProblem.npHard_of_polyTimeReducible_SAT`: a reduction from `SAT`
  proves NP-hardness, by the Cook–Levin theorem.
* `Cslib.Complexity.PromiseProblem.NPHard.P_eq_NP_of_mem_PromiseP`: an NP-hard promise problem
  solvable in polynomial time gives `P = NP`.
* `Cslib.Complexity.PromiseProblem.PolyTimeReducible.rpReducible`,
  `Cslib.Complexity.PromiseProblem.RPReducible.refl`,
  `Cslib.Complexity.PromiseProblem.RPReducibleWithError.trans`,
  `Cslib.Complexity.PromiseProblem.RPReducibleWithError.trans_add`: reflexivity, lifting of
  deterministic reductions, and composition of randomized reductions with multiplicative and
  additive error accounting.
* `Cslib.Complexity.PromiseProblem.rpReducible_iff_probability`,
  `Cslib.Complexity.PromiseProblem.rpReducible_iff_toOuterMeasure_eq_one`,
  `Cslib.Complexity.PromiseProblem.rpReducible_iff_exists_seeded`,
  `Cslib.Complexity.PromiseProblem.rpReducibleWithError_compl_iff`,
  `Cslib.Complexity.PromiseProblem.rpReducible_compl_iff`: faithfulness and convention bridges.
* `Cslib.Complexity.PromiseProblem.RPReducible.mem_PromiseBPP`,
  `Cslib.Complexity.PromiseProblem.RPReducible.mem_PromiseCoRP`,
  `Cslib.Complexity.PromiseProblem.RPReducible.mem_PromiseRP_of_compl`: closure of `PromiseBPP`,
  `PromiseCoRP` and `PromiseRP` under randomized one-sided reductions.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Chapter 11][AroraBarak09]
* [O. Goldreich, *On promise problems: a survey*, July 2005 author version][Goldreich2006]
* [S. Even, A. Selman, Y. Yacobi, *The complexity of promise problems with applications to
  public-key cryptography*][EvenSelmanYacobi1984]
* [R. Ilango, *Approaching MCSP from Above and Below: Hardness for a Conditional Variant and
  AC⁰[p]*, Section 2, p. 34:11][Ilango2020]
* [R. Ilango, B. Loff, I. C. Oliveira, *NP-Hardness of Circuit Minimization for Multi-Output
  Functions*, Section 4.2, Lemmas 15–16, pp. 22:20–22:23][IlangoLoffOliveira2020]
* [S. Hirahara, *NP-Hardness of Learning Programs and Partial MCSP*, ECCC TR22-119, Section 8,
  Lemma 8.3 and Theorem 8.5][Hirahara2022]
* [L. G. Valiant, V. V. Vazirani, *NP is as Easy as Detecting Unique
  Solutions*, pp. 86–87][ValiantVazirani1986]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM Probability PromiseProblem

/-! ### Promise-BPP, promise-RP and promise-coRP -/

namespace PromiseProblem

variable {α : Type} {enc : α ↪ List Bool} {p : Polynomial ℕ} {V : α × List Bool → Bool}
  {Q : PromiseProblem α} {A : Set α}

/-- `V` solves the promise problem `Q` with bounded error, using random strings whose length is `p`
evaluated at the length of the encoded instance: for every yes-instance at least two thirds of the
random strings are accepted, and for every no-instance at least two thirds are rejected
[Goldreich, July 2005 author version, Definition 1.2, p. 4][Goldreich2006]. Nothing is required on
instances outside the promise. -/
def SolvesWithBoundedError (enc : α ↪ List Bool) (p : Polynomial ℕ)
    (V : α × List Bool → Bool) (Q : PromiseProblem α) : Prop :=
  (∀ a ∈ Q.yes, 2 * 2 ^ p.eval (enc a).length ≤
    3 * (Finset.univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
      V (a, List.ofFn r) = true).card) ∧
  ∀ a ∈ Q.no, 2 * 2 ^ p.eval (enc a).length ≤
    3 * (Finset.univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
      V (a, List.ofFn r) = false).card

/-- `V` solves the promise problem `Q` with one-sided error, using random strings whose length is
`p` evaluated at the length of the encoded instance: for every yes-instance at least half of the
random strings are accepted, and for every no-instance none is
[Goldreich, July 2005 author version, Section 6.2, p. 18][Goldreich2006]. Nothing is required on
instances outside the promise. -/
def SolvesWithOneSidedError (enc : α ↪ List Bool) (p : Polynomial ℕ)
    (V : α × List Bool → Bool) (Q : PromiseProblem α) : Prop :=
  (∀ a ∈ Q.yes, 2 ^ p.eval (enc a).length ≤
    2 * (Finset.univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
      V (a, List.ofFn r) = true).card) ∧
  ∀ a ∈ Q.no, ∀ r : Fin (p.eval (enc a).length) → Bool, V (a, List.ofFn r) = false

@[simp]
theorem solvesWithBoundedError_ofSet_iff :
    (ofSet A).SolvesWithBoundedError enc p V ↔ DecidesWithBoundedError enc p V A := by
  simp only [SolvesWithBoundedError, DecidesWithBoundedError, yes_ofSet, no_ofSet,
    Set.mem_compl_iff]
  exact ⟨fun h a => ⟨h.1 a, h.2 a⟩, fun h => ⟨fun a => (h a).1, fun a => (h a).2⟩⟩

@[simp]
theorem solvesWithOneSidedError_ofSet_iff :
    (ofSet A).SolvesWithOneSidedError enc p V ↔ DecidesWithOneSidedError enc p V A := by
  simp only [SolvesWithOneSidedError, DecidesWithOneSidedError, yes_ofSet, no_ofSet,
    Set.mem_compl_iff]
  exact ⟨fun h a => ⟨h.1 a, h.2 a⟩, fun h => ⟨fun a => (h a).1, fun a => (h a).2⟩⟩

/-- Negating the verifier solves the complement promise problem with bounded error. -/
theorem SolvesWithBoundedError.compl (h : Q.SolvesWithBoundedError enc p V) :
    Qᶜ.SolvesWithBoundedError enc p (fun x => !V x) := by
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · simpa using h.2 a ha
  · simpa using h.1 a ha

/-- A one-sided-error solver for a promise problem is a polynomial-time verifier on the promise. -/
theorem SolvesWithOneSidedError.exists_certificate (h : Q.SolvesWithOneSidedError enc p V) :
    (∀ a ∈ Q.yes, ∃ w : List Bool, w.length = p.eval (enc a).length ∧ V (a, w) = true) ∧
      ∀ a ∈ Q.no, ∀ w : List Bool, w.length = p.eval (enc a).length → V (a, w) = false := by
  refine ⟨fun a ha => ?_, fun a ha w hw => ?_⟩
  · have hpos := Nat.one_le_two_pow (n := p.eval (enc a).length)
    obtain ⟨r, hr⟩ : (Finset.univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
        V (a, List.ofFn r) = true).Nonempty := by
      rw [← Finset.card_pos]
      have := h.1 a ha
      omega
    exact ⟨List.ofFn r, List.length_ofFn, (Finset.mem_filter.1 hr).2⟩
  · have hno := h.2 a ha fun i => w[i.val]'(by omega)
    rwa [show (List.ofFn fun i : Fin (p.eval (enc a).length) => w[i.val]'(by omega)) = w from
      List.ext_getElem (by simp [hw]) fun i _ _ => by simp] at hno

end PromiseProblem

section PromiseProbabilistic

variable {α : Type} {enc : α ↪ List Bool} {Q : PromiseProblem α} {A : Set α}

/-- The promise problems solved with bounded error by polynomial-time algorithms reading
polynomially long random strings, with respect to the encoding `enc` of instances
[Goldreich, July 2005 author version, Definition 1.2, p. 4][Goldreich2006]. -/
def PromiseBPP (enc : α ↪ List Bool) : Set (PromiseProblem α) :=
  {Q | ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableInPolyTime V (encPair enc encBits) encBool ∧
      Q.SolvesWithBoundedError enc p V}

/-- The promise problems solved with one-sided error (no false positives on no-instances) by
polynomial-time algorithms reading polynomially long random strings
[Goldreich, July 2005 author version, Section 6.2, p. 18][Goldreich2006]. -/
def PromiseRP (enc : α ↪ List Bool) : Set (PromiseProblem α) :=
  {Q | ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableInPolyTime V (encPair enc encBits) encBool ∧
      Q.SolvesWithOneSidedError enc p V}

/-- The promise problems solved with one-sided error (no false negatives on yes-instances) by
polynomial-time algorithms reading polynomially long random strings: those whose complements are
in `PromiseRP` [Goldreich, July 2005 author version, Section 6.2, p. 18][Goldreich2006]. -/
def PromiseCoRP (enc : α ↪ List Bool) : Set (PromiseProblem α) :=
  {Q | Qᶜ ∈ PromiseRP enc}

theorem mem_PromiseBPP_iff : Q ∈ PromiseBPP enc ↔
    ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
      ComputableInPolyTime V (encPair enc encBits) encBool ∧
      Q.SolvesWithBoundedError enc p V :=
  Iff.rfl

private theorem mem_PromiseBPP_iff_tidy : Q ∈ PromiseBPP enc ↔
    ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
      ComputableTidilyInPolyTime V (encPair enc encBits) encBool ∧
      Q.SolvesWithBoundedError enc p V := by
  simp only [mem_PromiseBPP_iff, computableInPolyTime_iff_computableTidilyInPolyTime]

theorem mem_PromiseRP_iff : Q ∈ PromiseRP enc ↔
    ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
      ComputableInPolyTime V (encPair enc encBits) encBool ∧
      Q.SolvesWithOneSidedError enc p V :=
  Iff.rfl

private theorem mem_PromiseRP_iff_tidy : Q ∈ PromiseRP enc ↔
    ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
      ComputableTidilyInPolyTime V (encPair enc encBits) encBool ∧
      Q.SolvesWithOneSidedError enc p V := by
  simp only [mem_PromiseRP_iff, computableInPolyTime_iff_computableTidilyInPolyTime]

/-- A promise problem is in `PromiseCoRP` when a polynomial-time verifier accepts every random
string on every yes-instance and rejects at least half on every no-instance. -/
theorem mem_PromiseCoRP_iff : Q ∈ PromiseCoRP enc ↔
    ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
      ComputableInPolyTime V (encPair enc encBits) encBool ∧
      (∀ a ∈ Q.yes, ∀ r : Fin (p.eval (enc a).length) → Bool, V (a, List.ofFn r) = true) ∧
      ∀ a ∈ Q.no, 2 ^ p.eval (enc a).length ≤
        2 * (Finset.univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
          V (a, List.ofFn r) = false).card := by
  constructor
  · rintro ⟨p, V, hV, hyes, hno⟩
    refine ⟨p, fun x => !V x, .of_tidy (by have := hV.tidy; fun_prop),
      fun a ha r => by simp [hno a ha r], fun a ha => by simpa using hyes a ha⟩
  · rintro ⟨p, V, hV, hyes, hno⟩
    refine ⟨p, fun x => !V x, .of_tidy (by have := hV.tidy; fun_prop),
      fun a ha => by simpa using hno a ha, fun a ha r => by simp [hyes a ha r]⟩

@[simp]
theorem ofSet_mem_PromiseBPP : ofSet A ∈ PromiseBPP enc ↔ A ∈ BPP enc := by
  simp only [PromiseBPP, BPP, Set.mem_ofPred_eq, solvesWithBoundedError_ofSet_iff]

@[simp]
theorem ofSet_mem_PromiseRP : ofSet A ∈ PromiseRP enc ↔ A ∈ RP enc := by
  simp only [PromiseRP, RP, Set.mem_ofPred_eq, solvesWithOneSidedError_ofSet_iff]

@[simp]
theorem ofSet_mem_PromiseCoRP : ofSet A ∈ PromiseCoRP enc ↔ A ∈ coRP enc := by
  rw [PromiseCoRP, Set.mem_ofPred_eq, ← ofSet_compl, ofSet_mem_PromiseRP, mem_coRP]

/-- Every promise problem separated by a language in `BPP` is in `PromiseBPP`. -/
theorem promiseClass_BPP_subset_PromiseBPP : promiseClass (BPP enc) ⊆ PromiseBPP enc := by
  rintro Q ⟨B, ⟨p, V, hV, hB⟩, hyes, hno⟩
  exact ⟨p, V, hV, fun a ha => (hB a).1 (hyes ha),
    fun a ha => (hB a).2 (Set.disjoint_right.1 hno ha)⟩

/-- Every promise problem separated by a language in `RP` is in `PromiseRP`. -/
theorem promiseClass_RP_subset_PromiseRP : promiseClass (RP enc) ⊆ PromiseRP enc := by
  rintro Q ⟨B, ⟨p, V, hV, hB⟩, hyes, hno⟩
  exact ⟨p, V, hV, fun a ha => (hB a).1 (hyes ha),
    fun a ha => (hB a).2 (Set.disjoint_right.1 hno ha)⟩

/-- Every promise problem separated by a language in `coRP` is in `PromiseCoRP`. -/
theorem promiseClass_coRP_subset_PromiseCoRP : promiseClass (coRP enc) ⊆ PromiseCoRP enc := by
  rintro Q ⟨B, hB, hyes, hno⟩
  exact promiseClass_RP_subset_PromiseRP ⟨Bᶜ, hB,
    Set.subset_compl_iff_disjoint_left.2 hno, Set.disjoint_compl_left_iff_subset.2 hyes⟩

/-- `PromiseBPP` is closed under complement. -/
theorem compl_mem_PromiseBPP (hQ : Q ∈ PromiseBPP enc) : Qᶜ ∈ PromiseBPP enc :=
  let ⟨p, V, hV, h⟩ := hQ
  ⟨p, fun x => !V x, by have := hV.tidy; exact .of_tidy (by fun_prop), h.compl⟩

/-- A promise problem's complement is in `PromiseRP` exactly when the problem is in
`PromiseCoRP`. -/
theorem compl_mem_PromiseRP_iff : Qᶜ ∈ PromiseRP enc ↔ Q ∈ PromiseCoRP enc :=
  Iff.rfl

/-- A promise problem's complement is in `PromiseCoRP` exactly when the problem is in
`PromiseRP`. -/
theorem compl_mem_PromiseCoRP_iff : Qᶜ ∈ PromiseCoRP enc ↔ Q ∈ PromiseRP enc := by
  rw [← compl_mem_PromiseRP_iff, compl_compl]

theorem PromiseP_subset_PromiseRP : PromiseP enc ⊆ PromiseRP enc :=
  (promiseClass_mono P_subset_RP).trans promiseClass_RP_subset_PromiseRP

theorem PromiseP_subset_PromiseCoRP : PromiseP enc ⊆ PromiseCoRP enc :=
  (promiseClass_mono P_subset_coRP).trans promiseClass_coRP_subset_PromiseCoRP

theorem PromiseP_subset_PromiseBPP : PromiseP enc ⊆ PromiseBPP enc :=
  (promiseClass_mono P_subset_BPP).trans promiseClass_BPP_subset_PromiseBPP

theorem PromiseRP_subset_PromiseNP : PromiseRP enc ⊆ PromiseNP enc := by
  rintro Q ⟨p, V, hV, h⟩
  exact mem_PromiseNP_iff.2 ⟨p, V, hV, h.exists_certificate⟩

/-- A counted verifier's uniform rejection probability is its rejected fraction of all words. -/
private theorem uniformList_rejectCount_toReal (V : α × List Bool → Bool) (a : α) (n : ℕ) :
    (((BitString.uniformList n).map (fun word => V (a, word))) false).toReal =
      ((Finset.univ.filter fun r : Fin n → Bool => V (a, List.ofFn r) = false).card : ℝ) /
        2 ^ n := by
  rw [BitString.uniformList_map_apply]
  simp

/-- Converting a polynomial-time seeded verifier into a uniform strict PPT Boolean program. -/
private theorem isPPTOn_sampleList_verifier {p : Polynomial ℕ} {V : α × List Bool → Bool}
    (hV : ComputableTidilyInPolyTime V (encPair enc encBits) encBool) :
    IsPPTOn enc encBool (fun a => (fun w => V (a, w)) <$>
      BitString.sampleList (p.eval (enc a).length)) :=
  have hcount : ComputableTidilyInPolyTime (fun a => p.eval (enc a).length) enc encUnary :=
    (ComputableTidilyInPolyTime.unary_eval p).comp
      (ComputableTidilyInPolyTime.encoding_length enc)
  hcount.sampleList.map_with (.of_tidy hV)

/-- **Probabilistic-program characterization of `PromiseBPP`**: a promise problem is in
`PromiseBPP` exactly when a uniform strict PPT Boolean program accepts every yes-instance with
probability at least `2 / 3` and rejects every no-instance with probability at least `2 / 3`. -/
theorem mem_PromiseBPP_iff_exists_isPPTOn : Q ∈ PromiseBPP enc ↔
    ∃ M : α → ProbComp Bool, IsPPTOn enc encBool M ∧
      (∀ a ∈ Q.yes, 2 / 3 ≤ Pr[M a]) ∧
      ∀ a ∈ Q.no, 2 / 3 ≤ (ProbComp.eval (M a) false).toReal := by
  rw [mem_PromiseBPP_iff_tidy]
  constructor
  · rintro ⟨p, V, hV, hyes, hno⟩
    refine ⟨fun a => (fun w => V (a, w)) <$> BitString.sampleList (p.eval (enc a).length),
      isPPTOn_sampleList_verifier hV, fun a ha => ?_, fun a ha => ?_⟩
    · simp only [ProbComp.eval_map, BitString.eval_sampleList]
      rw [uniformList_acceptCount_toReal, le_div_iff₀ (by positivity)]
      have h : (2 : ℝ) * 2 ^ p.eval (enc a).length ≤
          3 * (acceptCount V a (p.eval (enc a).length) : ℝ) := by
        exact_mod_cast hyes a ha
      linarith
    · simp only [ProbComp.eval_map, BitString.eval_sampleList]
      rw [uniformList_rejectCount_toReal, le_div_iff₀ (by positivity)]
      have h : (2 : ℝ) * 2 ^ p.eval (enc a).length ≤
          3 * ((Finset.univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
            V (a, List.ofFn r) = false).card : ℝ) := by
        exact_mod_cast hno a ha
      linarith
  · rintro ⟨M, hM, hyes, hno⟩
    obtain ⟨c, d, evalM, hevalM, hlaw⟩ := hM.exists_seeded_evaluator
    refine ⟨Polynomial.C c * (Polynomial.X + 1) ^ d, fun x => evalM x.1 x.2, hevalM,
      fun a ha => ?_, fun a ha => ?_⟩
    · have hp : (Polynomial.C c * (Polynomial.X + 1) ^ d).eval (enc a).length =
          c * ((enc a).length + 1) ^ d := by simp
      rw [hp]
      have hprob := hyes a ha
      rw [hlaw a, uniformList_acceptCount_toReal (V := fun x => evalM x.1 x.2),
        le_div_iff₀ (by positivity)] at hprob
      have h3 : (2 : ℝ) * 2 ^ (c * ((enc a).length + 1) ^ d) ≤
          3 * (acceptCount (fun x => evalM x.1 x.2) a (c * ((enc a).length + 1) ^ d) : ℝ) := by
        linarith
      exact_mod_cast h3
    · have hp : (Polynomial.C c * (Polynomial.X + 1) ^ d).eval (enc a).length =
          c * ((enc a).length + 1) ^ d := by simp
      rw [hp]
      have hprob := hno a ha
      rw [hlaw a, uniformList_rejectCount_toReal (V := fun x => evalM x.1 x.2),
        le_div_iff₀ (by positivity)] at hprob
      have h3 : (2 : ℝ) * 2 ^ (c * ((enc a).length + 1) ^ d) ≤
          3 * ((Finset.univ.filter fun r : Fin (c * ((enc a).length + 1) ^ d) → Bool =>
            evalM a (List.ofFn r) = false).card : ℝ) := by
        linarith
      exact_mod_cast h3

/-- **Probabilistic-program characterization of `PromiseRP`**: a promise problem is in `PromiseRP`
exactly when a uniform strict PPT Boolean program accepts every yes-instance with probability at
least `1 / 2` and never accepts a no-instance. -/
theorem mem_PromiseRP_iff_exists_isPPTOn : Q ∈ PromiseRP enc ↔
    ∃ M : α → ProbComp Bool, IsPPTOn enc encBool M ∧
      (∀ a ∈ Q.yes, 1 / 2 ≤ Pr[M a]) ∧
      ∀ a ∈ Q.no, true ∉ (ProbComp.eval (M a)).support := by
  rw [mem_PromiseRP_iff_tidy]
  constructor
  · rintro ⟨p, V, hV, hyes, hno⟩
    refine ⟨fun a => (fun w => V (a, w)) <$> BitString.sampleList (p.eval (enc a).length),
      isPPTOn_sampleList_verifier hV, fun a ha => ?_, fun a ha hmem => ?_⟩
    · simp only [ProbComp.eval_map, BitString.eval_sampleList]
      rw [uniformList_acceptCount_toReal, le_div_iff₀ (by positivity)]
      have h : (2 : ℝ) ^ p.eval (enc a).length ≤
          2 * (acceptCount V a (p.eval (enc a).length) : ℝ) := by
        exact_mod_cast hyes a ha
      linarith
    · simp only [ProbComp.eval_map, BitString.eval_sampleList,
        PMF.mem_support_map_iff, BitString.mem_support_uniformList_iff] at hmem
      obtain ⟨w, hw, hVw⟩ := hmem
      have := (SolvesWithOneSidedError.exists_certificate ⟨hyes, hno⟩).2 a ha w hw
      rw [this] at hVw
      exact Bool.noConfusion hVw
  · rintro ⟨M, hM, hyes, hno⟩
    obtain ⟨c, d, evalM, hevalM, hsupp, hlaw⟩ := hM.exists_total_seeded_evaluator
    refine ⟨Polynomial.C c * (Polynomial.X + 1) ^ d, fun x => evalM x.1 x.2, hevalM,
      fun a ha => ?_, fun a ha r => ?_⟩
    · have hp : (Polynomial.C c * (Polynomial.X + 1) ^ d).eval (enc a).length =
          c * ((enc a).length + 1) ^ d := by simp
      rw [hp]
      have hprob := hyes a ha
      rw [hlaw a _ le_rfl, uniformList_acceptCount_toReal (V := fun x => evalM x.1 x.2),
        le_div_iff₀ (by positivity)] at hprob
      have h2 : (2 : ℝ) ^ (c * ((enc a).length + 1) ^ d) ≤
          2 * (acceptCount (fun x => evalM x.1 x.2) a (c * ((enc a).length + 1) ^ d) : ℝ) := by
        linarith
      exact_mod_cast h2
    · rw [← Bool.not_eq_true]
      intro htrue
      exact hno a ha (htrue ▸ hsupp a (List.ofFn r))

/-- **Probabilistic-program characterization of `PromiseCoRP`**: a promise problem is in
`PromiseCoRP` exactly when a uniform strict PPT Boolean program never rejects a yes-instance and
rejects every no-instance with probability at least `1 / 2`. -/
theorem mem_PromiseCoRP_iff_exists_isPPTOn : Q ∈ PromiseCoRP enc ↔
    ∃ M : α → ProbComp Bool, IsPPTOn enc encBool M ∧
      (∀ a ∈ Q.yes, false ∉ (ProbComp.eval (M a)).support) ∧
      ∀ a ∈ Q.no, 1 / 2 ≤ (ProbComp.eval (M a) false).toReal := by
  rw [PromiseCoRP, Set.mem_ofPred_eq, mem_PromiseRP_iff_exists_isPPTOn]
  constructor
  · rintro ⟨M, hM, hyes, hno⟩
    refine ⟨fun a => Bool.not <$> M a, hM.map (by fun_prop), fun a ha hmem => ?_, fun a ha => ?_⟩
    · simp only [ProbComp.eval_map, PMF.mem_support_map_iff,
        Bool.not_eq_false'] at hmem
      obtain ⟨b, hb, rfl⟩ := hmem
      exact hno a ha hb
    · have h : (ProbComp.eval (Bool.not <$> M a) false).toReal = Pr[M a] := by
        simp [ProbComp.eval_map, PMF.map_apply]
      rw [h]
      exact hyes a ha
  · rintro ⟨M, hM, hyes, hno⟩
    refine ⟨fun a => Bool.not <$> M a, hM.map (by fun_prop), fun a ha => ?_, fun a ha hmem => ?_⟩
    · have h : Pr[Bool.not <$> M a] = (ProbComp.eval (M a) false).toReal := by
        simp [ProbComp.eval_map, PMF.map_apply]
      rw [h]
      exact hno a ha
    · simp only [ProbComp.eval_map, PMF.mem_support_map_iff,
        Bool.not_eq_true'] at hmem
      obtain ⟨b, hb, rfl⟩ := hmem
      exact hyes a ha hb

theorem PromiseRP_subset_PromiseBPP : PromiseRP enc ⊆ PromiseBPP enc := by
  intro Q hQ
  obtain ⟨p, V, hV, hyes, hno⟩ := mem_PromiseRP_iff_tidy.mp hQ
  have hk : ComputableTidilyInPolyTime (fun a => p.eval (enc a).length) enc encUnary :=
    (ComputableTidilyInPolyTime.unary_eval p).comp
      (ComputableTidilyInPolyTime.encoding_length enc)
  refine ⟨p + p, orVerifier (fun a => p.eval (enc a).length) V V,
    .of_tidy (computableTidilyInPolyTime_orVerifier hk hV hV), fun a ha => ?_, fun a ha => ?_⟩
  · change 2 * 2 ^ (p + p).eval (enc a).length ≤
      3 * acceptCount (orVerifier (fun a => p.eval (enc a).length) V V) a
        ((p + p).eval (enc a).length)
    rw [Polynomial.eval_add]
    generalize hk₀ : p.eval (enc a).length = k
    have hc := acceptCount_orVerifier (fun a => p.eval (enc a).length) V V a k
    simp only [hk₀] at hc ⊢
    have n₁ := acceptCount_add_acceptCount_not V a k
    have hhalf : 2 ^ k ≤ 2 * acceptCount V a k := hk₀ ▸ hyes a ha
    have hrej : 2 * acceptCount (fun x => !V x) a k ≤ 2 ^ k := by omega
    have hprod : 4 * (acceptCount (fun x => !V x) a k * acceptCount (fun x => !V x) a k) ≤
        2 ^ (k + k) := by
      rw [pow_add]
      nlinarith [Nat.mul_le_mul hrej hrej]
    omega
  · rw [Polynomial.eval_add]
    have hall (r : Fin (p.eval (enc a).length + p.eval (enc a).length) → Bool) :
        orVerifier (fun a => p.eval (enc a).length) V V (a, List.ofFn r) = false := by
      simp only [orVerifier, Bool.or_eq_false_iff]
      have hcert := (SolvesWithOneSidedError.exists_certificate ⟨hyes, hno⟩).2 a ha
      exact ⟨hcert _ (by simp), hcert _ (by simp)⟩
    rw [Finset.filter_true_of_mem fun r _ => hall r]
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    omega

theorem PromiseCoRP_subset_PromiseBPP : PromiseCoRP enc ⊆ PromiseBPP enc := fun Q hQ => by
  simpa using compl_mem_PromiseBPP (PromiseRP_subset_PromiseBPP hQ)

end PromiseProbabilistic

namespace PromiseProblem

variable {α β γ : Type*} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
  {X : PromiseProblem α} {Y Y' : PromiseProblem β} {Z : PromiseProblem γ}

/-! ### Reductions -/

/-- A **polynomial-time reduction of promise problems** from `X` to `Y`: a function computable in
polynomial time with respect to `encA` and `encB` mapping the yes-instances of `X` to yes-instances
of `Y` and its no-instances to no-instances of `Y`. Instances outside the promise of `X` may go
anywhere. Between gap problems these are the gap-preserving reductions. -/
def PolyTimeReducible (encA : α ↪ List Bool) (encB : β ↪ List Bool) (X : PromiseProblem α)
    (Y : PromiseProblem β) : Prop :=
  ∃ f : α → β, ComputableInPolyTime f encA encB ∧ Set.MapsTo f X.yes Y.yes ∧
    Set.MapsTo f X.no Y.no

/-- On decision problems, reductions of promise problems are polynomial-time reductions. -/
theorem polyTimeReducible_ofSet_iff {A : Set α} {B : Set β} :
    PolyTimeReducible encA encB (ofSet A) (ofSet B) ↔ Complexity.PolyTimeReducible encA encB A B :=
  exists_congr fun _ => and_congr_right fun _ =>
    ⟨fun ⟨hyes, hno⟩ _ => ⟨fun ha => hyes ha, fun hfa => by_contra fun ha => hno ha hfa⟩,
      fun h => ⟨fun a ha => (h a).1 ha, fun a ha hfa => ha ((h a).2 hfa)⟩⟩

/-- Every promise problem reduces to itself. -/
@[refl]
theorem PolyTimeReducible.refl (encA : α ↪ List Bool) (X : PromiseProblem α) :
    PolyTimeReducible encA encA X X :=
  ⟨id, ComputableInPolyTime.id', Set.mapsTo_id _, Set.mapsTo_id _⟩

/-- Reductions of promise problems compose. -/
@[trans]
theorem PolyTimeReducible.trans (hXY : PolyTimeReducible encA encB X Y)
    (hYZ : PolyTimeReducible encB encC Y Z) : PolyTimeReducible encA encC X Z :=
  let ⟨f, hf, hyes, hno⟩ := hXY
  let ⟨g, hg, hyes', hno'⟩ := hYZ
  ⟨g ∘ f, hg.comp hf, hyes'.comp hyes, hno'.comp hno⟩

/-- A promise problem reduces, by the identity, to any problem with more yes-instances and more
no-instances: enlarging the promise can only make a problem harder. -/
theorem PolyTimeReducible.of_subset (hyes : Y.yes ⊆ Y'.yes) (hno : Y.no ⊆ Y'.no) :
    PolyTimeReducible encB encB Y Y' :=
  ⟨id, ComputableInPolyTime.id', fun _ h => hyes h, fun _ h => hno h⟩

/-- **`PromiseP` is closed under reductions.** -/
theorem PolyTimeReducible.mem_PromiseP (h : PolyTimeReducible encA encB X Y)
    (hY : Y ∈ PromiseP encB) : X ∈ PromiseP encA := by
  obtain ⟨f, hf, hyes, hno⟩ := h
  obtain ⟨g, hg, hgyes, hgno⟩ := mem_PromiseP_iff.1 hY
  exact mem_PromiseP_iff.2 ⟨g ∘ f, hg.comp hf, fun a ha => hgyes _ (hyes ha),
    fun a ha => hgno _ (hno ha)⟩

/-- A reduction of promise problems restricts to a polynomial-time reduction between the problems
that separate them: for every problem `B` containing the yes-instances of `Y` and no no-instance,
its preimage separates `X` and reduces to `B`. -/
theorem PolyTimeReducible.exists_polyTimeReducible (h : PolyTimeReducible encA encB X Y)
    {B : Set β} (hyes : Y.yes ⊆ B) (hno : Disjoint B Y.no) :
    ∃ A : Set α, X.yes ⊆ A ∧ Disjoint A X.no ∧ Complexity.PolyTimeReducible encA encB A B := by
  obtain ⟨f, hf, hfyes, hfno⟩ := h
  refine ⟨f ⁻¹' B, fun a ha => hyes (hfyes ha), Set.disjoint_left.2 fun a ha ha' =>
    Set.disjoint_left.1 hno ha (hfno ha'), f, hf, fun _ => Iff.rfl⟩

section Randomized

variable {α β γ : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
  {X : PromiseProblem α} {Y Y' : PromiseProblem β} {Z : PromiseProblem γ}

/-- **`PromiseNP` is closed under polynomial-time reductions.** -/
theorem PolyTimeReducible.mem_PromiseNP (h : PolyTimeReducible encA encB X Y)
    (hY : Y ∈ PromiseNP encB) : X ∈ PromiseNP encA := by
  obtain ⟨B, hB, hyes, hno⟩ := hY
  obtain ⟨A, hAyes, hAno, hAB⟩ := h.exists_polyTimeReducible hyes hno
  exact ⟨A, _root_.Cslib.Complexity.PolyTimeReducible.mem_NP hAB hB, hAyes, hAno⟩

/-- **`PromiseBPP` is closed under polynomial-time reductions.** -/
theorem PolyTimeReducible.mem_PromiseBPP (h : PolyTimeReducible encA encB X Y)
    (hY : Y ∈ PromiseBPP encB) : X ∈ PromiseBPP encA := by
  obtain ⟨f, hf, hfyes, hfno⟩ := h
  obtain ⟨M, hM, hyes, hno⟩ := mem_PromiseBPP_iff_exists_isPPTOn.mp hY
  exact mem_PromiseBPP_iff_exists_isPPTOn.mpr
    ⟨fun a => M (f a), hM.preprocess hf.tidy, fun a ha => hyes (f a) (hfyes ha),
      fun a ha => hno (f a) (hfno ha)⟩

/-- **`PromiseRP` is closed under polynomial-time reductions.** -/
theorem PolyTimeReducible.mem_PromiseRP (h : PolyTimeReducible encA encB X Y)
    (hY : Y ∈ PromiseRP encB) : X ∈ PromiseRP encA := by
  obtain ⟨f, hf, hfyes, hfno⟩ := h
  obtain ⟨M, hM, hyes, hno⟩ := mem_PromiseRP_iff_exists_isPPTOn.mp hY
  exact mem_PromiseRP_iff_exists_isPPTOn.mpr
    ⟨fun a => M (f a), hM.preprocess hf.tidy, fun a ha => hyes (f a) (hfyes ha),
      fun a ha => hno (f a) (hfno ha)⟩

/-- **`PromiseCoRP` is closed under polynomial-time reductions.** -/
theorem PolyTimeReducible.mem_PromiseCoRP (h : PolyTimeReducible encA encB X Y)
    (hY : Y ∈ PromiseCoRP encB) : X ∈ PromiseCoRP encA := by
  obtain ⟨f, hf, hfyes, hfno⟩ := h
  obtain ⟨M, hM, hyes, hno⟩ := mem_PromiseCoRP_iff_exists_isPPTOn.mp hY
  exact mem_PromiseCoRP_iff_exists_isPPTOn.mpr
    ⟨fun a => M (f a), hM.preprocess hf.tidy, fun a ha => hyes (f a) (hfyes ha),
      fun a ha => hno (f a) (hfno ha)⟩

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

Instances outside `X.yes ∪ X.no` are unconstrained. -/
def RPReducibleWithError (encA : α ↪ List Bool) (encB : β ↪ List Bool) (s : α → ℝ)
    (X : PromiseProblem α) (Y : PromiseProblem β) : Prop :=
  ∃ R : α → ProbComp β, IsPPTOn encA encB R ∧
    (∀ a ∈ X.yes, ∀ b ∈ (ProbComp.eval (R a)).support, b ∈ Y.yes) ∧
    ∀ a ∈ X.no, s a ≤ ((ProbComp.eval (R a)).toOuterMeasure Y.no).toReal

/-- A **randomized polynomial-time many-one reduction with one-sided error** from a promise problem
`X` to a promise problem `Y`, with the standard soundness threshold `2 / 3`
[Ilango, Section 2, p. 34:11][Ilango2020]: a uniform strict PPT program `R : α → ProbComp β`
mapping every yes-instance of `X` exclusively into `Y.yes` and mapping every no-instance of `X` into
`Y.no` with probability at least `2 / 3`. -/
def RPReducible (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (X : PromiseProblem α) (Y : PromiseProblem β) : Prop :=
  ∃ R : α → ProbComp β, IsPPTOn encA encB R ∧
    (∀ a ∈ X.yes, ∀ b ∈ (ProbComp.eval (R a)).support, b ∈ Y.yes) ∧
    ∀ a ∈ X.no, 2 / 3 ≤ ((ProbComp.eval (R a)).toOuterMeasure Y.no).toReal

/-- `RPReducible` is `RPReducibleWithError` at the constant soundness threshold `2 / 3`. -/
theorem rpReducible_iff_rpReducibleWithError :
    RPReducible encA encB X Y ↔ RPReducibleWithError encA encB (fun _ => 2 / 3) X Y :=
  Iff.rfl

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
        ∀ a ∈ X.no, 2 / 3 ≤ Pr[(fun b => decide (b ∈ Y.no)) <$> R a] := by
  simp only [RPReducible, ProbComp.probability_map_decide_mem]

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

/-- Weakening `RPReducible` from soundness threshold `2 / 3` [Ilango, Section 2, p. 34:11]
[Ilango2020] to `1 / 2` (library weakening lemma). -/
theorem RPReducible.rpReducibleWithError_half (h : RPReducible encA encB X Y) :
    RPReducibleWithError encA encB (fun _ => 1 / 2) X Y :=
  RPReducibleWithError.mono h fun _ _ => by norm_num

/-- **Complement-duality identity for `RPReducibleWithError`** (library identity): a randomized
reduction between the complement promise problems `Xᶜ` and `Yᶜ` with threshold `s` is a randomized
reduction from `X` to `Y` in the dual one-sided error orientation, mapping no-instances exclusively
into `Y.no` and mapping yes-instances into `Y.yes` with probability at least `s a`. When `s a` is an
inverse-polynomial threshold such as `1 / (4 * n)`, this represents the unamplified one-sided
orientation of Valiant and Vazirani [Valiant and Vazirani, Section 1, Theorem 1.1, pp. 86–87]
[ValiantVazirani1986], [Goldreich, July 2005 author version, Section 6.2, p. 18][Goldreich2006]. -/
theorem rpReducibleWithError_compl_iff {s : α → ℝ} :
    RPReducibleWithError encA encB s Xᶜ Yᶜ ↔
      ∃ R : α → ProbComp β, IsPPTOn encA encB R ∧
        (∀ a ∈ X.no, ∀ b ∈ (ProbComp.eval (R a)).support, b ∈ Y.no) ∧
        ∀ a ∈ X.yes, s a ≤ ((ProbComp.eval (R a)).toOuterMeasure Y.yes).toReal :=
  Iff.rfl

/-- **Complement-duality identity for `RPReducible`** (library identity): a randomized reduction
between the complement promise problems `Xᶜ` and `Yᶜ` at the constant soundness threshold `2 / 3` is
a randomized reduction from `X` to `Y` in the dual one-sided error orientation (mapping
yes-instances into `Y.yes` with probability at least `2 / 3` and mapping no-instances exclusively
into `Y.no`). Unlike Valiant and Vazirani [Valiant and Vazirani, pp. 86–87][ValiantVazirani1986],
which uses an inverse-polynomial YES success probability `1 / (4 * n)` (see
`rpReducibleWithError_compl_iff`), this identity fixes the constant threshold `2 / 3`. -/
theorem rpReducible_compl_iff :
    RPReducible encA encB Xᶜ Yᶜ ↔
      ∃ R : α → ProbComp β, IsPPTOn encA encB R ∧
        (∀ a ∈ X.no, ∀ b ∈ (ProbComp.eval (R a)).support, b ∈ Y.no) ∧
        ∀ a ∈ X.yes, 2 / 3 ≤ ((ProbComp.eval (R a)).toOuterMeasure Y.yes).toReal :=
  Iff.rfl

open Classical in
/-- The real probability that a function of a uniform bit string of length `n` lands in `S` is the
fraction of `n`-bit strings mapping into `S`. -/
private theorem toOuterMeasure_map_uniformList_toReal (f : List Bool → β) (n : ℕ) (S : Set β) :
    (((BitString.uniformList n).map f).toOuterMeasure S).toReal =
      ((Finset.univ.filter fun r : Fin n → Bool => f (List.ofFn r) ∈ S).card : ℝ) / 2 ^ n := by
  rw [BitString.uniformList, PMF.map_comp, PMF.toOuterMeasure_map_apply,
    PMF.toOuterMeasure_uniformOfFintype_toReal]
  simp [Function.comp_def, Set.mem_preimage]

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
    rw [hlaw a _ le_rfl, toOuterMeasure_map_uniformList_toReal,
      le_div_iff₀ (by positivity)] at hprob
    have h3 : (2 : ℝ) * 2 ^ (c * ((encA a).length + 1) ^ d) ≤
        3 * ((Finset.univ.filter fun r : Fin (c * ((encA a).length + 1) ^ d) → Bool =>
          evalR a (List.ofFn r) ∈ Y.no).card : ℝ) := by
      linarith
    exact_mod_cast h3
  · rintro ⟨p, f, hf, hyes, hno⟩
    have hcount : ComputableTidilyInPolyTime (fun a => p.eval (encA a).length) encA encUnary :=
      (ComputableTidilyInPolyTime.unary_eval p).comp
        (ComputableTidilyInPolyTime.encoding_length encA)
    let R (a : α) : ProbComp β :=
      (fun w => f (a, w)) <$> BitString.sampleList (p.eval (encA a).length)
    have hR : IsPPTOn encA encB R := hcount.sampleList.map_with hf
    refine ⟨R, hR, fun a ha b hb => ?_, fun a ha => ?_⟩
    · simp only [R, ProbComp.eval_map, BitString.eval_sampleList,
        PMF.mem_support_map_iff, BitString.mem_support_uniformList_iff] at hb
      obtain ⟨w, hw, rfl⟩ := hb
      have hr := hyes a ha fun i => w[i.val]'(by omega)
      rwa [show (List.ofFn fun i : Fin (p.eval (encA a).length) => w[i.val]'(by omega)) = w from
        List.ext_getElem (by simp [hw]) fun i _ _ => by simp] at hr
    · simp only [R, ProbComp.eval_map, BitString.eval_sampleList]
      rw [toOuterMeasure_map_uniformList_toReal, le_div_iff₀ (by positivity)]
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
  refine ⟨fun a => pure (f a), hf.tidy.isPPTOn, fun a ha b hb => ?_, fun a ha => ?_⟩
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
`s₁ a + s₂ - 1`. -/
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

/-- Precomposing an `RPReducibleWithError` reduction with a deterministic polynomial-time reduction
preserves its soundness threshold. -/
theorem PolyTimeReducible.trans_rpReducibleWithError {s : β → ℝ}
    (hXY : PolyTimeReducible encA encB X Y) (hYZ : RPReducibleWithError encB encC s Y Z) :
    RPReducibleWithError encA encC (fun a => s (hXY.choose a)) X Z := by
  have hf := hXY.choose_spec
  obtain ⟨R, hR, hyes, hno⟩ := hYZ
  exact ⟨fun a => R (hXY.choose a), hR.preprocess hf.1.tidy,
    fun a ha c hc => hyes _ (hf.2.1 ha) c hc, fun a ha => hno _ (hf.2.2 ha)⟩

/-- Postcomposing an `RPReducibleWithError` reduction with a deterministic polynomial-time reduction
preserves its soundness threshold. -/
theorem RPReducibleWithError.trans_polyTimeReducible {s : α → ℝ}
    (hXY : RPReducibleWithError encA encB s X Y) (hYZ : PolyTimeReducible encB encC Y Z) :
    RPReducibleWithError encA encC s X Z := by
  obtain ⟨R, hR, hyes, hno⟩ := hXY
  obtain ⟨g, hg, gyes, gno⟩ := hYZ
  refine ⟨fun a => g <$> R a, hR.map hg.tidy, fun a ha c hc => ?_, fun a ha => ?_⟩
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

/-- Three-vote majority of a Boolean experiment. -/
private def maj3 (M : β → ProbComp Bool) (b : β) : ProbComp Bool :=
  M b >>= fun b₁ => M b >>= fun b₂ =>
    (fun b₃ => (b₁ && b₂) || (b₁ && b₃) || (b₂ && b₃)) <$> M b

private theorem isPPTOn_maj3 {M : β → ProbComp Bool} (hM : IsPPTOn encB encBool M) :
    IsPPTOn encB encBool (maj3 M) := by
  unfold maj3
  have h2 : IsPPTOn (encPair encB encBool) encBool (fun p : β × Bool => M p.1) :=
    hM.preprocess (.fst encB encBool)
  have h3 : IsPPTOn (encPair (encPair encB encBool) encBool) encBool
      (fun p : (β × Bool) × Bool => M p.1.1) :=
    h2.preprocess (.fst (encPair encB encBool) encBool)
  exact hM.bind_with (h2.bind_with (h3.map_with
    (f := fun p b₃ => (p.1.2 && p.2) || (p.1.2 && b₃) || (p.2 && b₃)) (by fun_prop)))

private theorem probability_maj3 (M : β → ProbComp Bool) (b : β) :
    Pr[maj3 M b] = 3 * Pr[M b] ^ 2 - 2 * Pr[M b] ^ 3 := by
  change Pr[M b >>= fun b₁ => M b >>= fun b₂ =>
    (fun b₃ => (b₁ && b₂) || (b₁ && b₃) || (b₂ && b₃)) <$> M b] = _
  rw [ProbComp.probability_bind, Fintype.sum_bool,
    ProbComp.probability_bind, Fintype.sum_bool,
    ProbComp.probability_bind, Fintype.sum_bool]
  simp only [Bool.true_and, Bool.false_and, Bool.true_or, Bool.false_or, Bool.or_false]
  have h1 : Pr[(fun _ : Bool => true) <$> M b] = 1 := by
    have hmap : ProbComp.eval ((fun _ : Bool => true) <$> M b) = PMF.pure true := by
      rw [ProbComp.eval_map]
      exact PMF.map_const (ProbComp.eval (M b)) true
    simp [hmap]
  have h2 : Pr[(fun b₃ : Bool => b₃) <$> M b] = Pr[M b] := by simp
  have h3 : Pr[(fun _ : Bool => false) <$> M b] = 0 := by
    simp [ProbComp.eval_map, PMF.map_apply]
  have hfalse : (ProbComp.eval (M b) false).toReal = 1 - Pr[M b] :=
    PMF.toReal_false_eq_one_sub (ProbComp.eval (M b))
  rw [h1, h2, h3, hfalse]
  ring

/-- **`PromiseCoRP` is closed under `RPReducible`** (library lemma): if `X` reduces to `Y` by a
randomized one-sided reduction and `Y ∈ PromiseCoRP encB`, then `X ∈ PromiseCoRP encA`. -/
theorem RPReducible.mem_PromiseCoRP (hXY : RPReducible encA encB X Y)
    (hY : Y ∈ PromiseCoRP encB) : X ∈ PromiseCoRP encA := by
  obtain ⟨R, hR, hyesR, hnoR⟩ := hXY
  obtain ⟨M, hM, hyesM, hnoM⟩ := mem_PromiseCoRP_iff_exists_isPPTOn.mp hY
  let T (a : α) : ProbComp Bool := R a >>= M
  have hT : IsPPTOn encA encBool T := hR.bind hM
  refine mem_PromiseCoRP_iff_exists_isPPTOn.mpr ⟨and2 T, isPPTOn_and2 hT, fun a ha hmem => ?_,
    fun a ha => ?_⟩
  · simp only [and2, T, ProbComp.eval_bind, ProbComp.eval_map,
      PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hmem
    obtain ⟨b₁, ⟨y₁, hy₁, hb₁⟩, b₂, ⟨y₂, hy₂, hb₂⟩, hfalse⟩ := hmem
    cases b₁
    · exact hyesM y₁ (hyesR a ha y₁ hy₁) hb₁
    · cases b₂
      · exact hyesM y₂ (hyesR a ha y₂ hy₂) hb₂
      · exact Bool.noConfusion hfalse
  · have hT_false : 1 / 3 ≤ (ProbComp.eval (T a) false).toReal := by
      have h := PMF.toOuterMeasure_bind_ge_mul (ProbComp.eval (R a)) (fun y => ProbComp.eval (M y))
        Y.no {false} (by norm_num : (0 : ℝ) ≤ 1 / 2) (hnoR a ha)
        fun y _ hy => by
          rw [PMF.toOuterMeasure_apply_singleton]
          exact hnoM y hy
      rw [← ProbComp.eval_bind, PMF.toOuterMeasure_apply_singleton] at h
      linarith
    have hsumT := PMF.toReal_true_add_toReal_false (ProbComp.eval (T a))
    have hT_true : Pr[T a] ≤ 2 / 3 := by linarith
    have hT_nonneg : 0 ≤ Pr[T a] := ENNReal.toReal_nonneg
    have hand2 : Pr[and2 T a] ≤ 4 / 9 := by
      rw [probability_and2]
      nlinarith
    have hsum := PMF.toReal_true_add_toReal_false (ProbComp.eval (and2 T a))
    linarith

/-- If `X` is `RPReducible` to `Y` and `Y ∈ PromiseP encB`, then `X ∈ PromiseCoRP encA`. -/
theorem RPReducible.mem_PromiseCoRP_of_mem_PromiseP (hXY : RPReducible encA encB X Y)
    (hY : Y ∈ PromiseP encB) : X ∈ PromiseCoRP encA :=
  hXY.mem_PromiseCoRP (PromiseP_subset_PromiseCoRP hY)

/-- If a decision problem `A` is `RPReducible` to `Y` and `Y ∈ PromiseCoRP encB`, then
`A ∈ coRP encA`. -/
theorem RPReducible.mem_coRP_of_ofSet {A : Set α} (hAY : RPReducible encA encB (ofSet A) Y)
    (hY : Y ∈ PromiseCoRP encB) : A ∈ coRP encA :=
  ofSet_mem_PromiseCoRP.mp (hAY.mem_PromiseCoRP hY)

/-- **`PromiseBPP` is closed under `RPReducible`** (library lemma): if `X` reduces to `Y` by a
randomized one-sided reduction and `Y ∈ PromiseBPP encB`, then `X ∈ PromiseBPP encA`. -/
theorem RPReducible.mem_PromiseBPP (hXY : RPReducible encA encB X Y)
    (hY : Y ∈ PromiseBPP encB) : X ∈ PromiseBPP encA := by
  obtain ⟨R, hR, hyesR, hnoR⟩ := hXY
  obtain ⟨M₀, hM₀, hyesM₀, hnoM₀⟩ := mem_PromiseBPP_iff_exists_isPPTOn.mp hY
  let M : β → ProbComp Bool := maj3 (maj3 M₀)
  have hM : IsPPTOn encB encBool M := isPPTOn_maj3 (isPPTOn_maj3 hM₀)
  have hMyes (y : β) (hy : y ∈ Y.yes) : 9 / 11 ≤ Pr[M y] := by
    have h0 : 2 / 3 ≤ Pr[M₀ y] := hyesM₀ y hy
    have h1 : Pr[M₀ y] ≤ 1 := PMF.toReal_apply_le_one _ _
    have hm1 : 20 / 27 ≤ Pr[maj3 M₀ y] := by
      rw [probability_maj3]
      nlinarith [sq_nonneg (Pr[M₀ y] - 2 / 3), sq_nonneg (1 - Pr[M₀ y])]
    have hm1_le : Pr[maj3 M₀ y] ≤ 1 := PMF.toReal_apply_le_one _ _
    change 9 / 11 ≤ Pr[maj3 (maj3 M₀) y]
    rw [probability_maj3]
    nlinarith [sq_nonneg (Pr[maj3 M₀ y] - 20 / 27), sq_nonneg (1 - Pr[maj3 M₀ y])]
  have hMno (y : β) (hy : y ∈ Y.no) : Pr[M y] ≤ 2 / 11 := by
    have h0 : Pr[M₀ y] ≤ 1 / 3 := by
      have hsum := PMF.toReal_true_add_toReal_false (ProbComp.eval (M₀ y))
      have h := hnoM₀ y hy
      linarith
    have h0_nn : 0 ≤ Pr[M₀ y] := ENNReal.toReal_nonneg
    have hm1 : Pr[maj3 M₀ y] ≤ 7 / 27 := by
      rw [probability_maj3]
      nlinarith [sq_nonneg (Pr[M₀ y]), sq_nonneg (1 / 3 - Pr[M₀ y])]
    have hm1_nn : 0 ≤ Pr[maj3 M₀ y] := ENNReal.toReal_nonneg
    change Pr[maj3 (maj3 M₀) y] ≤ 2 / 11
    rw [probability_maj3]
    nlinarith [sq_nonneg (Pr[maj3 M₀ y]), sq_nonneg (7 / 27 - Pr[maj3 M₀ y])]
  let T (a : α) : ProbComp Bool := R a >>= M
  have hT : IsPPTOn encA encBool T := hR.bind hM
  refine mem_PromiseBPP_iff_exists_isPPTOn.mpr ⟨and2 T, isPPTOn_and2 hT, fun a ha => ?_,
    fun a ha => ?_⟩
  · have hT_yes : 9 / 11 ≤ Pr[T a] := by
      have hyes_one : ((ProbComp.eval (R a)).toOuterMeasure Y.yes).toReal = 1 :=
        (ENNReal.toReal_eq_one_iff _).mpr
          ((PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (hyesR a ha))
      have h := PMF.toOuterMeasure_bind_ge_mul (ProbComp.eval (R a)) (fun y => ProbComp.eval (M y))
        Y.yes {true} (by norm_num : (0 : ℝ) ≤ 9 / 11) hyes_one.ge
        fun y _ hy => by
          rw [PMF.toOuterMeasure_apply_singleton]
          exact hMyes y hy
      rwa [one_mul, ← ProbComp.eval_bind, PMF.toOuterMeasure_apply_singleton] at h
    rw [probability_and2]
    nlinarith [sq_nonneg (Pr[T a] - 9 / 11)]
  · have hT_no : Pr[T a] ≤ 17 / 33 := by
      have hfail := PMF.toOuterMeasure_bind_failure_toReal_le
        (ProbComp.eval (R a)) (fun y => ProbComp.eval (M y)) Y.no {true}
        (by norm_num : (0 : ℝ) ≤ 2 / 11) fun y _ hy => by
          rw [PMF.toOuterMeasure_apply_singleton]
          exact hMno y hy
      rw [← ProbComp.eval_bind, PMF.toOuterMeasure_apply_singleton] at hfail
      have hadd := PMF.toOuterMeasure_toReal_add_compl (ProbComp.eval (R a)) Y.no
      have hno := hnoR a ha
      linarith
    have hT_nn : 0 ≤ Pr[T a] := ENNReal.toReal_nonneg
    have hand2 : Pr[and2 T a] ≤ 289 / 1089 := by
      rw [probability_and2]
      nlinarith
    have hsum := PMF.toReal_true_add_toReal_false (ProbComp.eval (and2 T a))
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

end Randomized

/-! ### NP-hardness -/

/-- A promise problem is **NP-hard** when every problem in `NP`, with any encoding of its
instances, reduces to it: some polynomial-time function maps its members to yes-instances and its
non-members to no-instances. This is `HardUnder` for `PolyTimeReducible` from `ofSet`. -/
def NPHard (encB : β ↪ List Bool) (Y : PromiseProblem β) : Prop :=
  HardUnder (fun enc A Y => PolyTimeReducible enc encB (ofSet A) Y) @NP Y

/-- NP-hardness of a promise problem is hardness for `NP` under `PolyTimeReducible` from `ofSet`. -/
theorem npHard_iff_hardUnder :
    NPHard encB Y ↔ HardUnder (fun enc A Y => PolyTimeReducible enc encB (ofSet A) Y) @NP Y :=
  Iff.rfl

/-- On decision problems, NP-hardness as a promise problem is `Cslib.Complexity.NPHard`. -/
theorem npHard_ofSet_iff {B : Set β} : NPHard encB (ofSet B) ↔ Complexity.NPHard encB B :=
  ⟨fun h _ enc A hA => polyTimeReducible_ofSet_iff.1 (h enc A hA),
    fun h _ enc A hA => polyTimeReducible_ofSet_iff.2 (h enc A hA)⟩

/-- NP-hardness transfers along reductions. -/
theorem NPHard.trans (hX : NPHard encA X) (h : PolyTimeReducible encA encB X Y) : NPHard encB Y :=
  HardUnder.trans (fun _ _ h' h'' => h'.trans h'') hX h

/-- Enlarging the promise preserves NP-hardness. -/
theorem NPHard.mono (hY : NPHard encB Y) (hyes : Y.yes ⊆ Y'.yes) (hno : Y.no ⊆ Y'.no) :
    NPHard encB Y' :=
  hY.trans (.of_subset hyes hno)

/-- **A reduction from `SAT` proves NP-hardness**, by the Cook–Levin theorem. -/
theorem npHard_of_polyTimeReducible_SAT (h : PolyTimeReducible encCNF encB (ofSet SAT) Y) :
    NPHard encB Y :=
  NPHard.trans (npHard_ofSet_iff.2 CookLevin.SAT_npHard) h

/-- Every problem separating the yes-instances of an NP-hard promise problem from its
no-instances is NP-hard. -/
theorem NPHard.npHard_of_subset (hY : NPHard encB Y) {B : Set β} (hyes : Y.yes ⊆ B)
    (hno : Disjoint B Y.no) : Complexity.NPHard encB B :=
  npHard_ofSet_iff.1 (hY.trans (.of_subset hyes (Set.subset_compl_iff_disjoint_left.2 hno)))

/-- If an NP-hard promise problem is solved in polynomial time, then `NP ⊆ P` for every encoding
of instances. -/
theorem NPHard.NP_subset_P_of_mem_PromiseP (hY : NPHard encB Y) (h : Y ∈ PromiseP encB)
    {α : Type} (enc : α ↪ List Bool) : NP enc ⊆ P enc :=
  fun A hA => ofSet_mem_PromiseP.1 ((hY enc A hA).mem_PromiseP h)

/-- **An NP-hard promise problem solved in polynomial time gives `P = NP`**, for every encoding
of instances. -/
theorem NPHard.P_eq_NP_of_mem_PromiseP (hY : NPHard encB Y) (h : Y ∈ PromiseP encB)
    {α : Type} (enc : α ↪ List Bool) : P enc = NP enc :=
  P_subset_NP.antisymm (hY.NP_subset_P_of_mem_PromiseP h enc)

/-- If `P ≠ NP` for some encoding, no NP-hard promise problem is solved in polynomial time. -/
theorem NPHard.notMem_PromiseP (hY : NPHard encB Y) {α : Type} {enc : α ↪ List Bool}
    (h : P enc ≠ NP enc) : Y ∉ PromiseP encB :=
  fun hP => h (hY.P_eq_NP_of_mem_PromiseP hP enc)

/-! ### Gap problems -/

/-- The **gap problem** of a maximization objective `val`, with completeness threshold `c` and
soundness threshold `s`: the yes-instances have value at least `c`, the no-instances value at most
`s`. The thresholds may depend on the instance; an instance with `c x ≤ s x` is not a
no-instance, so that the two sets are disjoint. -/
def gapMax (val c s : α → ℝ) : PromiseProblem α where
  yes := {x | c x ≤ val x}
  no := {x | val x ≤ s x ∧ s x < c x}
  disjoint := Set.disjoint_left.2 fun _ hyes hno => (hno.1.trans_lt hno.2).not_ge hyes

variable {val c s : α → ℝ} {x : α}

@[simp]
theorem mem_yes_gapMax : x ∈ (gapMax val c s).yes ↔ c x ≤ val x :=
  Iff.rfl

@[simp]
theorem mem_no_gapMax : x ∈ (gapMax val c s).no ↔ val x ≤ s x ∧ s x < c x :=
  Iff.rfl

/-- With a strictly smaller soundness threshold, the no-instances are those of value at most
`s`. -/
theorem mem_no_gapMax_of_lt (h : s x < c x) : x ∈ (gapMax val c s).no ↔ val x ≤ s x :=
  and_iff_left h

/-- The **gap problem** of a minimization objective `val`, with completeness threshold `c` and
soundness threshold `s`: the yes-instances have value at most `c`, the no-instances value at least
`s`, above `c`. The thresholds may depend on the instance; an instance with `s x ≤ c x` is not a
no-instance, so that the two sets are disjoint. -/
def gapMin (val c s : α → ℝ) : PromiseProblem α where
  yes := {x | val x ≤ c x}
  no := {x | s x ≤ val x ∧ c x < s x}
  disjoint := Set.disjoint_left.2 fun _ hyes hno => (hyes.trans_lt hno.2).not_ge hno.1

@[simp]
theorem mem_yes_gapMin : x ∈ (gapMin val c s).yes ↔ val x ≤ c x :=
  Iff.rfl

@[simp]
theorem mem_no_gapMin : x ∈ (gapMin val c s).no ↔ s x ≤ val x ∧ c x < s x :=
  Iff.rfl

/-- With a strictly larger soundness threshold, the no-instances are those of value at least
`s`. -/
theorem mem_no_gapMin_of_lt (h : c x < s x) : x ∈ (gapMin val c s).no ↔ s x ≤ val x :=
  and_iff_left h

/-- The promise problem `Q` with its promise restricted to the instances in `S`. -/
def restrict (Q : PromiseProblem α) (S : Set α) : PromiseProblem α where
  yes := Q.yes ∩ S
  no := Q.no ∩ S
  disjoint := Q.disjoint.mono Set.inter_subset_left Set.inter_subset_left

@[simp]
theorem yes_restrict (Q : PromiseProblem α) (S : Set α) : (Q.restrict S).yes = Q.yes ∩ S :=
  rfl

@[simp]
theorem no_restrict (Q : PromiseProblem α) (S : Set α) : (Q.restrict S).no = Q.no ∩ S :=
  rfl

end PromiseProblem

end Cslib.Complexity
