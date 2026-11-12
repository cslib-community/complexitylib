/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.AcceptCount
public import CslibFrontier.Computability.Complexity.Classes.BPP
public import CslibFrontier.Computability.Complexity.Classes.RP
public import CslibFrontier.Computability.Complexity.FineGrained.Exponents
public import CslibFrontier.Computability.Complexity.FineGrained.FunctionRates
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Closed
public import CslibFrontier.Probability.BitString
import CslibFrontier.Computability.Complexity.Classes.Promise.Probabilistic
import CslibFrontier.Computability.Complexity.Classes.Time.SampleVerify
import CslibFrontier.Computability.Complexity.FineGrained.Bounds
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.BitString.Cut
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Foundations.Analysis.SublinearEnvelope
import CslibFrontier.Foundations.Data.BitString.Block
import CslibFrontier.Foundations.Data.BitString.List
import CslibFrontier.Foundations.Data.BitString.WordCount
import CslibFrontier.Foundations.Data.List.OfFn
import CslibFrontier.Foundations.Data.Nat.Power
import CslibFrontier.Probability.MajorityVote

/-!
# Parameterized randomized runtime rates, error models, `rETH`, and `rSETH`

Fine-grained randomized complexity studies how bounded-error and one-sided-error randomness affect
exponential runtime exponents `2 ^ (δ * μ a) · poly(L)` [ImpagliazzoPaturi2001;
ImpagliazzoPaturiZane2001; CalabroImpagliazzoPaturi2006]. This module packages error orientations
explicitly in a documented structure `Cslib.Complexity.ErrorModel` and develops parameterized
promise-problem runtime bounds:

* `Cslib.Complexity.ErrorModel` records `(yesErr, noErr)` with `0 ≤ yesErr`, `0 ≤ noErr`, and
  `yesErr + noErr < 1`, covering deterministic (`⟨0, 0⟩`), symmetric two-sided error
  (`ErrorModel.twoSided ε`, `ErrorModel.bounded` at `1 / 3`), one-sided `RP` error
  (`ErrorModel.oneSidedRP ε`, `ErrorModel.rp` at `1 / 2`), and one-sided `coRP` error
  (`ErrorModel.oneSidedCoRP ε`, `ErrorModel.coRP` at `1 / 2`).
* `Cslib.Complexity.SolvesPromiseInTimeO`, `SolvesPromiseInExpTime`, and
  `SolvesPromiseInSubexpTime` formalize deterministic parameterized promise solvers, agreeing with
  `DecidableInTimeO` on `PromiseProblem.ofSet A` and with `PromiseP` on polynomial length bounds.
* `Cslib.Complexity.SolvesWithErrorInTimeO`, `SolvesWithErrorInExpTime`, and
  `SolvesWithErrorInSubexpTime` formalize seeded randomized promise solvers `(ℓ, V)` whose unary
  coin-length preparation and verifier execution together take `O(T a)` time; they compile to
  halting fair-coin `MultiTapePTM` machines (`exists_ptm_of_solvesWithErrorInTimeO`) and agree with
  `PromiseBPP`, `PromiseRP`, and `PromiseCoRP` on polynomial length bounds.
* **Rate-preserving error amplification** (`solvesWithErrorInTimeO_twoSided_iff`,
  `solvesWithErrorInTimeO_oneSidedRP_iff`, `SolvesWithErrorInTimeO.oneSidedRP_to_twoSided`):
  repeating a seeded solver a constant number of times via linear-time `bitsTake` / `bitsDrop`
  slicing preserves `O(T a)` and every exponential rate `δ`, so any constant two-sided threshold
  `ε ∈ (0, 1 / 2)` (and any one-sided threshold `ε ∈ (0, 1)`) defines the exact same runtime rates
  and exponents.
* **Randomized `k`-SAT exponents and hypotheses** (`rSatExponent`, `rpSatExponent`, `rETH`,
  `rSETH`): `0 ≤ rSatExponent k ≤ rpSatExponent k ≤ satExponent k ≤ 1`,
  `rETH ↔ 0 < rSatExponent 3`, `rSETH ↔ Tendsto rSatExponent atTop (𝓝 1)`, `rETH → ETH`, and
  `rSETH → SETH`.

## Main definitions

* `Cslib.Complexity.ErrorModel`: structured `(yesErr, noErr)` error bounds (`yesErr + noErr < 1`).
* `Cslib.Complexity.SolvesPromiseInTimeO`, `Cslib.Complexity.SolvesPromiseInExpTime`,
  `Cslib.Complexity.SolvesPromiseInSubexpTime`: deterministic parameterized promise bounds.
* `Cslib.Complexity.SolvesWithErrorInTimeO`, `Cslib.Complexity.SolvesWithErrorInExpTime`,
  `Cslib.Complexity.SolvesWithErrorInSubexpTime`: randomized parameterized promise bounds.
* `Cslib.Complexity.rSatExponent`, `Cslib.Complexity.rpSatExponent`,
  `Cslib.Complexity.rETH`, `Cslib.Complexity.rSETH`: randomized `k`-SAT exponents and hypotheses.

## Main results

* `Cslib.Complexity.solvesWithErrorInTimeO_deterministic_iff`,
  `Cslib.Complexity.solvesWithErrorInExpTime_deterministic_iff`,
  `Cslib.Complexity.mem_PromiseBPP_iff_exists_solvesWithErrorInTimeO`,
  `Cslib.Complexity.mem_PromiseRP_iff_exists_solvesWithErrorInTimeO`,
  `Cslib.Complexity.exists_ptm_of_solvesWithErrorInTimeO`: bridges to deterministic solvers,
  polynomial promise classes, and closed fair-coin `MultiTapePTM` machines.
* `Cslib.Complexity.solvesWithErrorInTimeO_twoSided_iff`,
  `Cslib.Complexity.solvesWithErrorInTimeO_oneSidedRP_iff`,
  `Cslib.Complexity.SolvesWithErrorInTimeO.oneSidedRP_to_twoSided`: rate-preserving threshold
  invariance.
* `Cslib.Complexity.rSatExponent_le_rpSatExponent`,
  `Cslib.Complexity.rpSatExponent_le_satExponent`,
  `Cslib.Complexity.rETH_iff_rSatExponent_pos`, `Cslib.Complexity.rSETH_iff_tendsto`,
  `Cslib.Complexity.rETH.eth`, `Cslib.Complexity.rSETH.seth`: exponent hierarchy and
  characterizations.

## References

* [R. Impagliazzo, R. Paturi, *On the complexity of k-SAT*][ImpagliazzoPaturi2001]
* [R. Impagliazzo, R. Paturi, F. Zane, *Which problems have strongly exponential
  complexity?*][ImpagliazzoPaturiZane2001]
* [C. Calabro, R. Impagliazzo, R. Paturi, *A duality between clause width and clause density for
  SAT*][CalabroImpagliazzoPaturi2006]
* [O. Goldreich, *On promise problems: a survey*][Goldreich2006]
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing Turing.MultiTapeTM Filter Topology PromiseProblem
open scoped ENNReal

/-! ### Structured error models for randomized promise solvers -/

/-- Error profile of a randomized promise-problem solver: `yesErr` bounds the false-negative
fraction on yes-instances, `noErr` bounds the false-positive fraction on no-instances, and
`yesErr + noErr < 1` guarantees a strict separation `noErr < 1 - yesErr` between no-instance and
yes-instance acceptance probabilities. -/
@[ext]
structure ErrorModel where
  /-- Upper bound on the rejection probability on yes-instances. -/
  yesErr : ℝ
  /-- Upper bound on the acceptance probability on no-instances. -/
  noErr : ℝ
  /-- Rejection error bound is nonnegative. -/
  yesErr_nonneg : 0 ≤ yesErr
  /-- Acceptance error bound is nonnegative. -/
  noErr_nonneg : 0 ≤ noErr
  /-- Sum of yes-instance and no-instance error bounds is strictly below `1`. -/
  err_sum_lt_one : yesErr + noErr < 1

namespace ErrorModel

instance : PartialOrder ErrorModel where
  le E₁ E₂ := E₁.yesErr ≤ E₂.yesErr ∧ E₁.noErr ≤ E₂.noErr
  le_refl _ := ⟨le_rfl, le_rfl⟩
  le_trans _ _ _ h₁₂ h₂₃ := ⟨h₁₂.1.trans h₂₃.1, h₁₂.2.trans h₂₃.2⟩
  le_antisymm _ _ h₁₂ h₂₁ := ErrorModel.ext (le_antisymm h₁₂.1 h₂₁.1) (le_antisymm h₁₂.2 h₂₁.2)

@[simp] theorem le_def {E₁ E₂ : ErrorModel} :
    E₁ ≤ E₂ ↔ E₁.yesErr ≤ E₂.yesErr ∧ E₁.noErr ≤ E₂.noErr := Iff.rfl

/-- Zero error on both yes-instances and no-instances (deterministic solvers). -/
@[expose] def deterministic : ErrorModel where
  yesErr := 0
  noErr := 0
  yesErr_nonneg := le_rfl
  noErr_nonneg := le_rfl
  err_sum_lt_one := by norm_num

/-- Symmetric two-sided error `ε ∈ [0, 1 / 2)`. -/
@[expose] def twoSided (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε < 1 / 2) : ErrorModel where
  yesErr := ε
  noErr := ε
  yesErr_nonneg := h0
  noErr_nonneg := h0
  err_sum_lt_one := by linarith

/-- Standard bounded two-sided error `1 / 3` (`BPP` / `PromiseBPP`). -/
@[expose] noncomputable def bounded : ErrorModel :=
  twoSided (1 / 3) (by norm_num) (by norm_num)

/-- One-sided `RP` error `ε ∈ [0, 1)`: false-negative bound `ε` on yes-instances and zero false
positives on no-instances. -/
@[expose] def oneSidedRP (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε < 1) : ErrorModel where
  yesErr := ε
  noErr := 0
  yesErr_nonneg := h0
  noErr_nonneg := le_rfl
  err_sum_lt_one := by linarith

/-- Standard `RP` error (`yesErr = 1 / 2`, `noErr = 0`). -/
@[expose] noncomputable def rp : ErrorModel :=
  oneSidedRP (1 / 2) (by norm_num) (by norm_num)

/-- One-sided `coRP` error `ε ∈ [0, 1)`: zero false negatives on yes-instances and false-positive
bound `ε` on no-instances. -/
@[expose] def oneSidedCoRP (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε < 1) : ErrorModel where
  yesErr := 0
  noErr := ε
  yesErr_nonneg := le_rfl
  noErr_nonneg := h0
  err_sum_lt_one := by linarith

/-- Standard `coRP` error (`yesErr = 0`, `noErr = 1 / 2`). -/
@[expose] noncomputable def coRP : ErrorModel :=
  oneSidedCoRP (1 / 2) (by norm_num) (by norm_num)

/-- Dual error profile under promise-problem complement (`Qᶜ`). -/
@[expose] def symm (E : ErrorModel) : ErrorModel where
  yesErr := E.noErr
  noErr := E.yesErr
  yesErr_nonneg := E.noErr_nonneg
  noErr_nonneg := E.yesErr_nonneg
  err_sum_lt_one := by linarith [E.err_sum_lt_one]

@[simp] theorem symm_symm (E : ErrorModel) : E.symm.symm = E := rfl

@[simp] theorem symm_oneSidedRP (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε < 1) :
    (oneSidedRP ε h0 h1).symm = oneSidedCoRP ε h0 h1 := rfl

@[simp] theorem symm_oneSidedCoRP (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε < 1) :
    (oneSidedCoRP ε h0 h1).symm = oneSidedRP ε h0 h1 := rfl

@[simp] theorem symm_rp : rp.symm = coRP := rfl

@[simp] theorem symm_coRP : coRP.symm = rp := rfl

/-- `deterministic` is the least error profile. -/
theorem deterministic_le (E : ErrorModel) : deterministic ≤ E :=
  ⟨E.yesErr_nonneg, E.noErr_nonneg⟩

/-- One-sided `RP` error `ε` refines two-sided error `ε'` whenever `ε ≤ ε'`. -/
theorem oneSidedRP_le_twoSided {ε ε' : ℝ} {h0 : 0 ≤ ε} {h1 : ε < 1}
    {h0' : 0 ≤ ε'} {h1' : ε' < 1 / 2} (hle : ε ≤ ε') :
    oneSidedRP ε h0 h1 ≤ twoSided ε' h0' h1' :=
  ⟨hle, h0'⟩

/-- One-sided `coRP` error `ε` refines two-sided error `ε'` whenever `ε ≤ ε'`. -/
theorem oneSidedCoRP_le_twoSided {ε ε' : ℝ} {h0 : 0 ≤ ε} {h1 : ε < 1}
    {h0' : 0 ≤ ε'} {h1' : ε' < 1 / 2} (hle : ε ≤ ε') :
    oneSidedCoRP ε h0 h1 ≤ twoSided ε' h0' h1' :=
  ⟨h0', hle⟩

end ErrorModel

/-! ### Deterministic parameterized promise-problem bounds -/

section DeterministicPromise

variable {α β : Type} {enc : α ↪ List Bool} {encB : β ↪ List Bool}

/-- `Q` is solved deterministically within time `O(T a)` when a Boolean function computable within
`O(T a)` answers `true` on `Q.yes` and `false` on `Q.no`. -/
@[expose] def SolvesPromiseInTimeO (Q : PromiseProblem α) (enc : α ↪ List Bool) (T : α → ℝ) :
    Prop :=
  ∃ g : α → Bool, Q.SolvedBy g ∧ ComputableInTimeO g enc encBool T

/-- `Q` is solved deterministically within time `2 ^ (δ * μ a) · poly(L)`. -/
@[expose] def SolvesPromiseInExpTime (Q : PromiseProblem α) (enc : α ↪ List Bool) (μ : α → ℕ)
    (δ : ℝ) : Prop :=
  ∃ e : ℕ, SolvesPromiseInTimeO Q enc fun a => 2 ^ (δ * μ a) * ((enc a).length + 1) ^ e

/-- `Q` is solved deterministically in subexponential time in `μ`. -/
@[expose] def SolvesPromiseInSubexpTime (Q : PromiseProblem α) (enc : α ↪ List Bool) (μ : α → ℕ) :
    Prop :=
  ∀ δ : ℝ, 0 < δ → SolvesPromiseInExpTime Q enc μ δ

/-- Weakening the deterministic runtime bound up to constants. -/
theorem SolvesPromiseInTimeO.mono {Q : PromiseProblem α} {T T' : α → ℝ}
    (h : SolvesPromiseInTimeO Q enc T) (c : ℕ) (hT : ∀ a, T a ≤ c * T' a + c)
    (hT' : ∀ a, 0 ≤ T' a) : SolvesPromiseInTimeO Q enc T' := by
  obtain ⟨g, hQ, hg⟩ := h
  exact ⟨g, hQ, hg.mono c hT hT'⟩

/-- Larger exponents allow more deterministic promise solvers. -/
theorem SolvesPromiseInExpTime.mono {Q : PromiseProblem α} {μ : α → ℕ} {δ δ' : ℝ}
    (h : SolvesPromiseInExpTime Q enc μ δ) (hδ : δ ≤ δ') :
    SolvesPromiseInExpTime Q enc μ δ' := by
  obtain ⟨e, g, hQ, hg⟩ := h
  obtain ⟨e', hg'⟩ := ComputableInExpTime.mono (μ := μ) ⟨e, hg⟩ hδ
  exact ⟨e', g, hQ, hg'⟩

/-- Rescaling the parameter linearly rescales the deterministic exponential rate. -/
theorem SolvesPromiseInExpTime.mono_measure {Q : PromiseProblem α} {μ μ' : α → ℕ} {c : ℕ}
    (hμ : ∀ a, μ a ≤ c * μ' a + c) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : SolvesPromiseInExpTime Q enc μ δ) :
    SolvesPromiseInExpTime Q enc μ' (c * δ) := by
  obtain ⟨e, g, hQ, hg⟩ := h
  obtain ⟨e', hg'⟩ := ComputableInExpTime.mono_measure hμ hδ ⟨e, hg⟩
  exact ⟨e', g, hQ, hg'⟩

/-- Subexponential deterministic promise solving transfers along linear parameter bounds. -/
theorem SolvesPromiseInSubexpTime.mono_measure {Q : PromiseProblem α} {μ μ' : α → ℕ} {c : ℕ}
    (hμ : ∀ a, μ a ≤ c * μ' a + c) (h : SolvesPromiseInSubexpTime Q enc μ) :
    SolvesPromiseInSubexpTime Q enc μ' := fun δ hδ =>
  ((h (δ / (c + 1)) (by positivity)).mono_measure hμ (by positivity)).mono
    (natCast_mul_div_add_one_le hδ.le c)

/-- Transfer of `SolvesPromiseInExpTime` along a linear-parameter polynomial-time promise
reduction. -/
theorem SolvesPromiseInExpTime.of_promiseReduction {X : PromiseProblem α} {Y : PromiseProblem β}
    {μA : α → ℕ} {μB : β → ℕ} {r : α → β}
    (hr : ComputableInPolyTime r enc encB)
    (hyes : ∀ a ∈ X.yes, r a ∈ Y.yes) (hno : ∀ a ∈ X.no, r a ∈ Y.no)
    {c : ℕ} (hμ : ∀ a, μB (r a) ≤ c * μA a + c) {δ : ℝ} (hδ : 0 ≤ δ)
    (hY : SolvesPromiseInExpTime Y encB μB δ) :
    SolvesPromiseInExpTime X enc μA (c * δ) := by
  obtain ⟨e, g, hY_solves, hg⟩ := hY
  obtain ⟨e', hgr⟩ := ComputableInExpTime.of_reduction hr hμ hδ ⟨e, hg⟩
  exact ⟨e', g ∘ r, ⟨fun a ha => hY_solves.1 _ (hyes a ha),
    fun a ha => hY_solves.2 _ (hno a ha)⟩, hgr⟩

/-- Transfer of `SolvesPromiseInSubexpTime` along a linear-parameter promise reduction. -/
theorem SolvesPromiseInSubexpTime.of_promiseReduction {X : PromiseProblem α} {Y : PromiseProblem β}
    {μA : α → ℕ} {μB : β → ℕ} {r : α → β}
    (hr : ComputableInPolyTime r enc encB)
    (hyes : ∀ a ∈ X.yes, r a ∈ Y.yes) (hno : ∀ a ∈ X.no, r a ∈ Y.no)
    {c : ℕ} (hμ : ∀ a, μB (r a) ≤ c * μA a + c)
    (hY : SolvesPromiseInSubexpTime Y encB μB) :
    SolvesPromiseInSubexpTime X enc μA := fun δ hδ =>
  ((hY (δ / (c + 1)) (by positivity)).of_promiseReduction hr hyes hno hμ
    (by positivity)).mono (natCast_mul_div_add_one_le hδ.le c)

/-- On `PromiseProblem.ofSet A`, `SolvesPromiseInTimeO` agrees with `DecidableInTimeO`. -/
theorem solvesPromiseInTimeO_ofSet_iff {A : Set α} {T : α → ℝ} :
    SolvesPromiseInTimeO (ofSet A) enc T ↔ DecidableInTimeO A enc T := by
  rw [SolvesPromiseInTimeO, decidableInTimeO_iff_exists_computableInTimeO]
  exact exists_congr fun g => and_congr_left' solvedBy_ofSet

/-- On `PromiseProblem.ofSet A`, `SolvesPromiseInExpTime` agrees with `DecidableInExpTime`. -/
theorem solvesPromiseInExpTime_ofSet_iff {A : Set α} {μ : α → ℕ} {δ : ℝ} :
    SolvesPromiseInExpTime (ofSet A) enc μ δ ↔ DecidableInExpTime A enc μ δ :=
  exists_congr fun _ => solvesPromiseInTimeO_ofSet_iff

/-- On `PromiseProblem.ofSet A`, `SolvesPromiseInSubexpTime` agrees with `DecidableInSubexpTime`. -/
theorem solvesPromiseInSubexpTime_ofSet_iff {A : Set α} {μ : α → ℕ} :
    SolvesPromiseInSubexpTime (ofSet A) enc μ ↔ DecidableInSubexpTime A enc μ :=
  forall₂_congr fun _ _ => solvesPromiseInExpTime_ofSet_iff

/-- `PromiseP` is polynomial-degree `SolvesPromiseInTimeO`. -/
theorem mem_PromiseP_iff_exists_solvesPromiseInTimeO {Q : PromiseProblem α} :
    Q ∈ PromiseP enc ↔
      ∃ d : ℕ, SolvesPromiseInTimeO Q enc fun a => ((enc a).length + 1) ^ d := by
  rw [mem_PromiseP_iff]
  constructor
  · rintro ⟨g, hg, hQ⟩
    obtain ⟨d, _, hg'⟩ := hg.exists_degree
    refine ⟨d, g, hQ, ComputableInTimeO.of_computableInO hg'.inO fun a => ?_⟩
    push_cast
    exact le_rfl
  · rintro ⟨d, g, hQ, c, t, sp, ht, hg⟩
    have ht_nat : ∀ a, t a ≤ c * ((enc a).length + 1) ^ d + c := fun a => by
      have hta := ht a
      dsimp only at hta
      exact_mod_cast hta
    have hg_ts : ComputableInTimeAndSpace g enc encBool
        (fun a => c * ((enc a).length + 1) ^ d + c) sp :=
      hg.mono ht_nat fun _ => le_rfl
    have hpoly : ComputableInPolyTime g enc encBool :=
      hg_ts.computableInPolyTime (t := fun n => c * (n + 1) ^ d + c) (by fun_prop)
    exact ⟨g, hpoly, hQ⟩

/-- Any `PromiseP` solver has deterministic exponential rate `0` in any parameter `μ`. -/
theorem SolvesPromiseInExpTime.of_mem_PromiseP {Q : PromiseProblem α} {μ : α → ℕ}
    (hQ : Q ∈ PromiseP enc) : SolvesPromiseInExpTime Q enc μ 0 := by
  obtain ⟨d, h⟩ := mem_PromiseP_iff_exists_solvesPromiseInTimeO.mp hQ
  refine ⟨d, h.mono 1 (fun a => ?_) fun _ => by positivity⟩
  simp

end DeterministicPromise

/-! ### Seeded randomized promise-problem bounds -/

section RandomizedPromise

variable {α β : Type} {enc : α ↪ List Bool} {encB : β ↪ List Bool}

/-- `Q` is solved with error profile `E` within time `O(T a)` when a unary coin-length function
`ℓ : α → ℕ` and a deterministic seeded verifier `V : α × List Bool → Bool` run together in time
`O(T a)` across all seeds of length `ℓ a`, rejecting at most an `E.yesErr` fraction of seeds on
yes-instances and accepting at most an `E.noErr` fraction of seeds on no-instances. -/
@[expose] def SolvesWithErrorInTimeO (Q : PromiseProblem α) (enc : α ↪ List Bool)
    (E : ErrorModel) (T : α → ℝ) : Prop :=
  ∃ (ℓ : α → ℕ) (V : α × List Bool → Bool) (Tℓ Sℓ : α → ℕ) (Tv Sv : α × List Bool → ℕ) (c : ℕ),
    ComputableInO ℓ enc encUnary Tℓ Sℓ ∧
    ComputableInO V (encPair enc encBits) encBool Tv Sv ∧
    (∀ a w, w.length = ℓ a → ((enc a).length + Tℓ a + Tv (a, w) : ℝ) ≤ c * T a + c) ∧
    (∀ a ∈ Q.yes, (acceptCount (fun p => !V p) a (ℓ a) : ℝ) ≤ E.yesErr * (2 : ℝ) ^ ℓ a) ∧
    ∀ a ∈ Q.no, (acceptCount V a (ℓ a) : ℝ) ≤ E.noErr * (2 : ℝ) ^ ℓ a

/-- `Q` is solved with error profile `E` within time `2 ^ (δ * μ a) · poly(L)`. -/
@[expose] def SolvesWithErrorInExpTime (Q : PromiseProblem α) (enc : α ↪ List Bool)
    (E : ErrorModel) (μ : α → ℕ) (δ : ℝ) : Prop :=
  ∃ e : ℕ, SolvesWithErrorInTimeO Q enc E fun a => 2 ^ (δ * μ a) * ((enc a).length + 1) ^ e

/-- `Q` is solved with error profile `E` in subexponential time in `μ`. -/
@[expose] def SolvesWithErrorInSubexpTime (Q : PromiseProblem α) (enc : α ↪ List Bool)
    (E : ErrorModel) (μ : α → ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → SolvesWithErrorInExpTime Q enc E μ δ

/-- Relaxing the error bounds preserves `SolvesWithErrorInTimeO`. -/
theorem SolvesWithErrorInTimeO.mono_error {Q : PromiseProblem α} {E₁ E₂ : ErrorModel} {T : α → ℝ}
    (h : SolvesWithErrorInTimeO Q enc E₁ T) (hE : E₁ ≤ E₂) :
    SolvesWithErrorInTimeO Q enc E₂ T := by
  obtain ⟨ℓ, V, Tℓ, Sℓ, Tv, Sv, c, hℓ, hV, ht, hyes, hno⟩ := h
  refine ⟨ℓ, V, Tℓ, Sℓ, Tv, Sv, c, hℓ, hV, ht, fun a ha => (hyes a ha).trans ?_,
    fun a ha => (hno a ha).trans ?_⟩
  · exact mul_le_mul_of_nonneg_right hE.1 (by positivity)
  · exact mul_le_mul_of_nonneg_right hE.2 (by positivity)

/-- Weakening the runtime bound up to constants preserves `SolvesWithErrorInTimeO`. -/
theorem SolvesWithErrorInTimeO.mono {Q : PromiseProblem α} {E : ErrorModel} {T T' : α → ℝ}
    (h : SolvesWithErrorInTimeO Q enc E T) (c : ℕ) (hT : ∀ a, T a ≤ c * T' a + c)
    (hT' : ∀ a, 0 ≤ T' a) : SolvesWithErrorInTimeO Q enc E T' := by
  obtain ⟨ℓ, V, Tℓ, Sℓ, Tv, Sv, c₀, hℓ, hV, ht, hyes, hno⟩ := h
  refine ⟨ℓ, V, Tℓ, Sℓ, Tv, Sv, c₀ * c + c₀, hℓ, hV, fun a w hw => (ht a w hw).trans ?_,
    hyes, hno⟩
  have h1 := mul_le_mul_of_nonneg_left (hT a) (Nat.cast_nonneg c₀)
  have h2 := mul_nonneg (Nat.cast_nonneg c₀ : (0 : ℝ) ≤ c₀) (hT' a)
  push_cast
  nlinarith

/-- Larger exponents allow more randomized promise solvers. -/
theorem SolvesWithErrorInExpTime.mono {Q : PromiseProblem α} {E : ErrorModel} {μ : α → ℕ}
    {δ δ' : ℝ} (h : SolvesWithErrorInExpTime Q enc E μ δ) (hδ : δ ≤ δ') :
    SolvesWithErrorInExpTime Q enc E μ δ' := by
  obtain ⟨e, h⟩ := h
  exact ⟨e, h.mono 1 (fun a => (two_rpow_mul_pow_le_two_rpow_mul_pow
    (mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg _)) le_rfl).trans (by simp))
    fun _ => by positivity⟩

/-- Relaxing the error bounds preserves `SolvesWithErrorInExpTime`. -/
theorem SolvesWithErrorInExpTime.mono_error {Q : PromiseProblem α} {E₁ E₂ : ErrorModel}
    {μ : α → ℕ} {δ : ℝ} (h : SolvesWithErrorInExpTime Q enc E₁ μ δ) (hE : E₁ ≤ E₂) :
    SolvesWithErrorInExpTime Q enc E₂ μ δ :=
  let ⟨e, h⟩ := h; ⟨e, h.mono_error hE⟩

/-- Rescaling the parameter linearly rescales the randomized exponential rate. -/
theorem SolvesWithErrorInExpTime.mono_measure {Q : PromiseProblem α} {E : ErrorModel}
    {μ μ' : α → ℕ} {c : ℕ} (hμ : ∀ a, μ a ≤ c * μ' a + c) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : SolvesWithErrorInExpTime Q enc E μ δ) :
    SolvesWithErrorInExpTime Q enc E μ' (c * δ) :=
  let ⟨e, h⟩ := h
  ⟨e, h.mono _ (fun a => two_rpow_mul_pow_le_natCeil_mul_add hδ (hμ a)) fun _ => by positivity⟩

/-- Subexponential randomized promise solving transfers along linear parameter bounds. -/
theorem SolvesWithErrorInSubexpTime.mono_measure {Q : PromiseProblem α} {E : ErrorModel}
    {μ μ' : α → ℕ} {c : ℕ} (hμ : ∀ a, μ a ≤ c * μ' a + c)
    (h : SolvesWithErrorInSubexpTime Q enc E μ) :
    SolvesWithErrorInSubexpTime Q enc E μ' := fun δ hδ =>
  ((h (δ / (c + 1)) (by positivity)).mono_measure hμ (by positivity)).mono
    (natCast_mul_div_add_one_le hδ.le c)

private theorem computableInO_bool_not_linear :
    ComputableInO Bool.not encBool encBool (fun b => (encBool b).length)
      (fun b => (encBool b).length) := by
  obtain ⟨d, _, hnot⟩ := ComputableInPolyTime.bool_not.exists_degree
  refine hnot.inO.mono (2 ^ d) (fun b => ?_) fun b => ?_
  all_goals
    simp only [encBool_apply, List.length_singleton]
    exact Nat.le_mul_of_pos_right _ (by decide)

/-- Negating the verifier solves `Qᶜ` with the symmetric error profile `E.symm`. -/
theorem SolvesWithErrorInTimeO.compl {Q : PromiseProblem α} {E : ErrorModel} {T : α → ℝ}
    (h : SolvesWithErrorInTimeO Q enc E T) :
    SolvesWithErrorInTimeO Qᶜ enc E.symm T := by
  obtain ⟨ℓ, V, Tℓ, Sℓ, Tv, Sv, c, hℓ, hV, ht, hyes, hno⟩ := h
  refine ⟨ℓ, fun p => !V p, Tℓ, Sℓ, Tv, Sv, c, hℓ, computableInO_bool_not_linear.comp_linear hV,
    ht, fun a ha => ?_, fun a ha => ?_⟩
  · rw [acceptCount_congr (W := V) (fun w => Bool.not_not (V (a, w))) (ℓ a)]
    exact hno a ha
  · exact hyes a ha

/-- **Deterministic vs. zero-error randomized solvers.** When the target time bound is at least
the encoded input length (`(enc a).length ≤ T a`), `SolvesWithErrorInTimeO` at
`ErrorModel.deterministic` is equivalent to `SolvesPromiseInTimeO`. -/
theorem solvesWithErrorInTimeO_deterministic_iff {Q : PromiseProblem α} {T : α → ℝ}
    (hL : ∀ a, ((enc a).length : ℝ) ≤ T a) :
    SolvesWithErrorInTimeO Q enc ErrorModel.deterministic T ↔ SolvesPromiseInTimeO Q enc T := by
  have hT_nn : ∀ a, 0 ≤ T a := fun a => (Nat.cast_nonneg _).trans (hL a)
  constructor
  · rintro ⟨ℓ, V, Tℓ, Sℓ, Tv, Sv, c, hℓ, hV, ht, hyes, hno⟩
    let g (a : α) : Bool := V (a, List.replicate (ℓ a) true)
    have hpair : ComputableInO (fun a : α => (a, List.replicate (ℓ a) true)) enc
        (encPair enc encBits) (fun a => (enc a).length + Tℓ a)
        (fun a => (enc a).length + Sℓ a) := by
      have hid : ComputableInO (fun a : α => a) enc enc
          (fun a => (enc a).length) (fun a => (enc a).length) :=
        ComputableInO.of_eq fun _ => rfl
      have hℓ_bits : ComputableInO (fun a : α => List.replicate (ℓ a) true) enc encBits Tℓ Sℓ :=
        hℓ.of_enc_eq fun _ => rfl
      exact hid.prod hℓ_bits
    obtain ⟨cV, hg_ts, -⟩ := hV.comp hpair
    refine ⟨g, ⟨fun a ha => ?_, fun a ha => ?_⟩, cV * c + cV, _, _, fun a => ?_, hg_ts⟩
    · have h0 : acceptCount (fun p => !V p) a (ℓ a) = 0 := by
        have hle := hyes a ha
        simp only [ErrorModel.deterministic, zero_mul] at hle
        exact Nat.eq_zero_of_le_zero (by exact_mod_cast hle)
      by_contra hfalse
      have hne : (!V (a, List.replicate (ℓ a) true)) = true := by
        cases hval : V (a, List.replicate (ℓ a) true)
        · rfl
        · exact absurd hval hfalse
      have hpos : 0 < acceptCount (fun p => !V p) a (ℓ a) :=
        acceptCount_pos_iff.mpr ⟨List.replicate (ℓ a) true, List.length_replicate .., hne⟩
      omega
    · have h0 : acceptCount V a (ℓ a) = 0 := by
        have hle := hno a ha
        simp only [ErrorModel.deterministic, zero_mul] at hle
        exact Nat.eq_zero_of_le_zero (by exact_mod_cast hle)
      by_contra hne
      have htrue : V (a, List.replicate (ℓ a) true) = true :=
        Bool.eq_true_of_not_eq_false hne
      have hpos : 0 < acceptCount V a (ℓ a) :=
        acceptCount_pos_iff.mpr ⟨List.replicate (ℓ a) true, List.length_replicate .., htrue⟩
      omega
    · have hta := ht a (List.replicate (ℓ a) true) (List.length_replicate ..)
      have hsum : (((enc a).length + Tℓ a + Tv (a, List.replicate (ℓ a) true) + 1 : ℕ) : ℝ) ≤
          c * T a + c + 1 := by
        push_cast
        linarith
      have hmul := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg cV)
      have hnonneg := mul_nonneg (Nat.cast_nonneg cV : (0 : ℝ) ≤ cV) (hT_nn a)
      push_cast at hmul ⊢
      nlinarith
  · rintro ⟨g, hQ, hg_time⟩
    obtain ⟨tg, cg, hgO, htg⟩ := hg_time.exists_computableInO
    have hℓ : ComputableInO (fun _ : α => 0) enc encUnary
        (fun a => (enc a).length) (fun _ => 0) := ComputableInO.constZero 0
    have hV : ComputableInO (fun p : α × List Bool => g p.1) (encPair enc encBits) encBool
        (fun p => (encPair enc encBits p).length + tg p.1)
        (fun p => (encPair enc encBits p).length + tg p.1) :=
      hgO.comp (ComputableInO.fst enc encBits)
    refine ⟨fun _ => 0, fun p => g p.1, _, _, _, _, cg + 4, hℓ, hV, fun a w hw => ?_,
      fun a ha => ?_, fun a ha => ?_⟩
    · dsimp only at hw ⊢
      have hw0 : w = [] := List.length_eq_zero_iff.mp hw
      subst hw0
      have hpair_len : (encPair enc encBits (a, [])).length = 2 * (enc a).length + 1 := by
        simp
      rw [hpair_len]
      have h1 := hL a
      have h2 := htg a
      have h3 := hT_nn a
      push_cast
      linarith
    · simp [acceptCount_zero, hQ.1 a ha, ErrorModel.deterministic]
    · simp [acceptCount_zero, hQ.2 a ha, ErrorModel.deterministic]

/-- **Deterministic vs. zero-error exponential rates.** For `δ ≥ 0`, `SolvesWithErrorInExpTime` at
`ErrorModel.deterministic` is equivalent to `SolvesPromiseInExpTime`. -/
theorem solvesWithErrorInExpTime_deterministic_iff {Q : PromiseProblem α} {μ : α → ℕ} {δ : ℝ}
    (hδ : 0 ≤ δ) :
    SolvesWithErrorInExpTime Q enc ErrorModel.deterministic μ δ ↔
      SolvesPromiseInExpTime Q enc μ δ := by
  have hL (e : ℕ) (a : α) :
      ((enc a).length : ℝ) ≤ 2 ^ (δ * μ a) * ((enc a).length + 1) ^ (max e 1) := by
    have := pow_le_two_rpow_mul_pow (L := (enc a).length) (d := 1) (e := max e 1)
      (mul_nonneg hδ (Nat.cast_nonneg (μ a))) (le_max_right e 1)
    rw [pow_one] at this
    linarith
  have hmax (e : ℕ) (a : α) : (2 : ℝ) ^ (δ * μ a) * ((enc a).length + 1) ^ e ≤
      ((1 : ℕ) : ℝ) * (2 ^ (δ * μ a) * ((enc a).length + 1) ^ (max e 1)) + ((1 : ℕ) : ℝ) :=
    (two_rpow_mul_pow_le_two_rpow_mul_pow le_rfl (le_max_left e 1)).trans (by simp)
  constructor
  · rintro ⟨e, h⟩
    exact ⟨max e 1, (solvesWithErrorInTimeO_deterministic_iff (hL e)).mp
      (h.mono 1 (hmax e) fun _ => by positivity)⟩
  · rintro ⟨e, g, hQ, hg⟩
    exact ⟨max e 1, (solvesWithErrorInTimeO_deterministic_iff (hL e)).mpr
      ⟨g, hQ, hg.mono 1 (hmax e) fun _ => by positivity⟩⟩

/-- Every deterministic `2 ^ (δ * μ a) · poly(L)` promise solver (`δ ≥ 0`) solves `Q` under any
error profile `E`. -/
theorem SolvesPromiseInExpTime.solvesWithErrorInExpTime {Q : PromiseProblem α} {μ : α → ℕ}
    {δ : ℝ} (hδ : 0 ≤ δ) (h : SolvesPromiseInExpTime Q enc μ δ) (E : ErrorModel) :
    SolvesWithErrorInExpTime Q enc E μ δ :=
  ((solvesWithErrorInExpTime_deterministic_iff hδ).mpr h).mono_error (ErrorModel.deterministic_le E)

/-- Transfer of `SolvesWithErrorInExpTime` along a linear-parameter polynomial-time promise
reduction. -/
theorem SolvesWithErrorInExpTime.of_promiseReduction {X : PromiseProblem α} {Y : PromiseProblem β}
    {E : ErrorModel} {μA : α → ℕ} {μB : β → ℕ} {r : α → β}
    (hr : ComputableInPolyTime r enc encB)
    (hyes : ∀ a ∈ X.yes, r a ∈ Y.yes) (hno : ∀ a ∈ X.no, r a ∈ Y.no)
    {c : ℕ} (hμ : ∀ a, μB (r a) ≤ c * μA a + c) {δ : ℝ} (hδ : 0 ≤ δ)
    (hY : SolvesWithErrorInExpTime Y encB E μB δ) :
    SolvesWithErrorInExpTime X enc E μA (c * δ) := by
  obtain ⟨e, ℓ, V, Tℓ, Sℓ, Tv, Sv, k, hℓ, hV, ht, hYyes, hYno⟩ := hY
  obtain ⟨d, _, hr'⟩ := hr.exists_degree
  obtain ⟨l, hl⟩ := hr'.inO.length_le_time
  have hℓ' := hℓ.comp hr'.inO
  have hpair := (hr'.inO.comp (ComputableInO.fst enc encBits)).prod (ComputableInO.snd enc encBits)
  have hV' := hV.comp hpair
  obtain ⟨cℓ, hlen_ℓ⟩ := hℓ.length_le_time
  set D : ℕ := max d 1
  let K_real : ℝ := (12 + 4 * cℓ) * (k * 2 ^ (δ * c) * (2 * l + 1) ^ e + k + 1)
  refine ⟨D * (e + 1), ℓ ∘ r, fun p => V (r p.1, p.2), _, _, _, _, ⌈K_real⌉₊,
    hℓ', hV', fun a w hw => ?_, fun a ha => hYyes (r a) (hyes a ha),
    fun a ha => hYno (r a) (hno a ha)⟩
  set P : ℝ := (((enc a).length : ℝ) + 1) ^ D
  set X : ℝ := (2 : ℝ) ^ (c * δ * μA a)
  have hL1 : (1 : ℝ) ≤ ((enc a).length : ℝ) + 1 :=
    le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hP : 1 ≤ P := one_le_pow₀ hL1
  have hPd : (((enc a).length : ℝ) + 1) ^ d ≤ P := pow_le_pow_right₀ hL1 (le_max_left d 1)
  have hLP : ((enc a).length : ℝ) + 1 ≤ P :=
    le_self_pow₀ hL1 (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (le_max_right d 1)))
  have hX : 1 ≤ X := Real.one_le_rpow (by norm_num) (by positivity)
  have hn : ((encB (r a)).length : ℝ) ≤ l * (P + 1) := by
    have hn0 : ((encB (r a)).length : ℝ) ≤ l * ((((enc a).length : ℝ) + 1) ^ d + 1) := by
      exact_mod_cast hl a
    nlinarith [(Nat.cast_nonneg l : (0 : ℝ) ≤ l)]
  have hexp : (2 : ℝ) ^ (δ * μB (r a)) ≤ 2 ^ (δ * c) * X :=
    two_rpow_le_two_rpow_mul_of_le_mul_add hδ (hμ a)
  have hpow : (((encB (r a)).length : ℝ) + 1) ^ e ≤ (2 * l + 1) ^ e * P ^ e := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith) e
  set U : ℝ := k * 2 ^ (δ * c) * (2 * l + 1) ^ e + k + 1
  have hU1 : 1 ≤ U := by
    dsimp only [U]
    have : (0 : ℝ) ≤ k * 2 ^ (δ * c) * (2 * l + 1) ^ e + k := by positivity
    linarith
  have hXP1 : 1 ≤ X * P ^ (e + 1) := one_le_mul_of_one_le_of_one_le hX (one_le_pow₀ hP)
  have hPe : X * P ^ e ≤ X * P ^ (e + 1) :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hP (Nat.le_add_right e 1)) (by positivity)
  have hP_le : P ≤ X * P ^ (e + 1) :=
    (le_self_pow₀ hP (Nat.succ_ne_zero e)).trans (le_mul_of_one_le_left (by positivity) hX)
  have htra_base : ((encB (r a)).length + Tℓ (r a) + Tv (r a, w) : ℝ) + 1 ≤
      U * (X * P ^ e) := by
    have htra := ht (r a) w hw
    dsimp only at htra
    have hmul : (k : ℝ) * (2 ^ (δ * μB (r a)) * (((encB (r a)).length : ℝ) + 1) ^ e) ≤
        (k * 2 ^ (δ * c) * (2 * l + 1) ^ e) * (X * P ^ e) := by
      have hm0 := mul_le_mul_of_nonneg_left (mul_le_mul hexp hpow (by positivity) (by positivity))
        (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
      linarith [show (k : ℝ) * (2 ^ (δ * c) * X * ((2 * l + 1) ^ e * P ^ e)) =
        (k * 2 ^ (δ * c) * (2 * l + 1) ^ e) * (X * P ^ e) by ring]
    have hk1 : (k : ℝ) ≤ k * (X * P ^ e) :=
      le_mul_of_one_le_right (Nat.cast_nonneg k)
        (one_le_mul_of_one_le_of_one_le hX (one_le_pow₀ hP))
    have h1_le : (1 : ℝ) ≤ X * P ^ e := one_le_mul_of_one_le_of_one_le hX (one_le_pow₀ hP)
    dsimp only [U]
    linarith
  have hY_bound : ((encB (r a)).length + Tℓ (r a) + Tv (r a, w) : ℝ) ≤ U * (X * P ^ (e + 1)) :=
    (by linarith : _ ≤ U * (X * P ^ e)).trans (mul_le_mul_of_nonneg_left hPe (by positivity))
  have hℓ_le : (ℓ (r a) : ℝ) ≤ cℓ * (U * (X * P ^ (e + 1))) := by
    have h1 := hlen_ℓ (r a)
    rw [encUnary_apply, List.length_replicate] at h1
    have h1R : (ℓ (r a) : ℝ) ≤ cℓ * ((Tℓ (r a) : ℝ) + 1) := by exact_mod_cast h1
    have hTℓ_le : (Tℓ (r a) : ℝ) + 1 ≤ U * (X * P ^ (e + 1)) := by
      have h0 : (Tℓ (r a) : ℝ) + 1 ≤ U * (X * P ^ e) := by
        linarith [(Nat.cast_nonneg (encB (r a)).length : (0 : ℝ) ≤ _),
          (Nat.cast_nonneg (Tv (r a, w)) : (0 : ℝ) ≤ _)]
      exact h0.trans (mul_le_mul_of_nonneg_left hPe (by positivity))
    exact h1R.trans (mul_le_mul_of_nonneg_left hTℓ_le (Nat.cast_nonneg cℓ))
  have hpair_len : ((encPair enc encBits (a, w)).length : ℝ) =
      2 * (enc a).length + 1 + ℓ (r a) := by
    dsimp only [Function.comp_apply] at hw
    simp only [length_encPair, encBits, Function.Embedding.refl_apply, hw]
    push_cast
    ring
  have hPU : P ≤ U * (X * P ^ (e + 1)) := hP_le.trans (le_mul_of_one_le_left (by positivity) hU1)
  have htot : ((enc a).length : ℝ) + ((((enc a).length : ℝ) + 1) ^ d + Tℓ (r a)) +
      (((((encPair enc encBits (a, w)).length : ℝ) + (((enc a).length : ℝ) + 1) ^ d) +
        (encPair enc encBits (a, w)).length) + Tv (r a, w)) ≤
      K_real * (X * P ^ (e + 1)) := by
    rw [hpair_len]
    dsimp only [K_real, U] at *
    have hcℓ_nn : (0 : ℝ) ≤ cℓ := Nat.cast_nonneg cℓ
    have hpos_XP : (0 : ℝ) ≤ X * P ^ (e + 1) := by positivity
    nlinarith [(Nat.cast_nonneg (encB (r a)).length : (0 : ℝ) ≤ _)]
  have hceil : K_real * (X * P ^ (e + 1)) ≤ ⌈K_real⌉₊ * (X * P ^ (e + 1)) + ⌈K_real⌉₊ := by
    have h1 := mul_le_mul_of_nonneg_right (Nat.le_ceil K_real)
      (by positivity : (0 : ℝ) ≤ X * P ^ (e + 1))
    linarith [(Nat.cast_nonneg ⌈K_real⌉₊ : (0 : ℝ) ≤ _)]
  dsimp only [Function.comp_apply]
  push_cast
  rw [pow_mul]
  dsimp only [P, X] at htot hceil
  exact htot.trans hceil

/-- Transfer of `SolvesWithErrorInSubexpTime` along a linear-parameter promise reduction. -/
theorem SolvesWithErrorInSubexpTime.of_promiseReduction {X : PromiseProblem α}
    {Y : PromiseProblem β} {E : ErrorModel} {μA : α → ℕ} {μB : β → ℕ} {r : α → β}
    (hr : ComputableInPolyTime r enc encB)
    (hyes : ∀ a ∈ X.yes, r a ∈ Y.yes) (hno : ∀ a ∈ X.no, r a ∈ Y.no)
    {c : ℕ} (hμ : ∀ a, μB (r a) ≤ c * μA a + c)
    (hY : SolvesWithErrorInSubexpTime Y encB E μB) :
    SolvesWithErrorInSubexpTime X enc E μA := fun δ hδ =>
  ((hY (δ / (c + 1)) (by positivity)).of_promiseReduction hr hyes hno hμ
    (by positivity)).mono (natCast_mul_div_add_one_le hδ.le c)

/-! ### Bridges to `MultiTapePTM`, `PromiseBPP`, `PromiseRP`, and `PromiseCoRP` -/

/-- **Native `MultiTapePTM` compilation.** Every `SolvesWithErrorInTimeO Q enc E T` solver (with
`0 ≤ T a`) compiles to a closed fair-coin multi-tape machine that halts on every run within clock
`O(T a)` and outputs `[true]` / `[false]` achieving error profile `E`. -/
theorem exists_ptm_of_solvesWithErrorInTimeO {Q : PromiseProblem α} {E : ErrorModel} {T : α → ℝ}
    (hT : ∀ a, 0 ≤ T a) (h : SolvesWithErrorInTimeO Q enc E T) :
    ∃ (c : ℕ) (clock : α → ℕ) (k : ℕ) (State : Type) (_ : Finite State)
      (machine : MultiTapePTM k Bool State),
      (∀ a, (clock a : ℝ) ≤ c * T a + c) ∧
      (∀ a, ∀ final ∈ (ProbComp.eval
          (machine.runClosedConfigFrom (clock a) (machine.initialConfig (enc a)))).support,
          final.tapes.state = none) ∧
      (∀ a ∈ Q.yes,
        1 - E.yesErr ≤ ((ProbComp.eval (machine.runClosed (clock a) (enc a))) [true]).toReal ∧
        ((ProbComp.eval (machine.runClosed (clock a) (enc a))) [false]).toReal ≤ E.yesErr) ∧
      ∀ a ∈ Q.no,
        ((ProbComp.eval (machine.runClosed (clock a) (enc a))) [true]).toReal ≤ E.noErr := by
  obtain ⟨ℓ, V, Tℓ, Sℓ, Tv, Sv, c₀, hℓ, hV, ht, hyes, hno⟩ := h
  let boundNat (a : α) : ℕ := c₀ * ⌈T a⌉₊ + c₀
  have hboundNat (a : α) (w : List Bool) (hw : w.length = ℓ a) :
      (enc a).length + Tℓ a + Tv (a, w) ≤ boundNat a := by
    have hta := ht a w hw
    have hceil : c₀ * T a + c₀ ≤ (boundNat a : ℝ) := by
      dsimp only [boundNat]
      push_cast
      linarith [mul_le_mul_of_nonneg_left (Nat.le_ceil (T a)) (Nat.cast_nonneg c₀)]
    exact_mod_cast hta.trans hceil
  obtain ⟨c, k, State, _, P, hP⟩ := exists_machine_sampleVerify_of_bound hℓ hV hboundNat
  let clock (a : α) : ℕ := c * boundNat a + c
  have hprob (a : α) (b : Bool) :
      ((ProbComp.eval (P.runClosed (clock a) (enc a))) [b]).toReal =
        (acceptCount (fun p => V p == b) a (ℓ a) : ℝ) / (2 : ℝ) ^ ℓ a := by
    rw [(hP a).2, BitString.uniformList_map_apply]
    have heq : (Finset.univ.filter fun w : Fin (ℓ a) → Bool => [V (a, List.ofFn w)] = [b]).card =
        acceptCount (fun p => V p == b) a (ℓ a) := by
      simp only [acceptCount, List.cons.injEq, and_true, beq_iff_eq]
    rw [heq, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  refine ⟨c * (2 * c₀ + 1), clock, k, State, inferInstance, P, fun a => ?_, fun a => (hP a).1,
    fun a ha => ?_, fun a ha => ?_⟩
  · have hceil : (⌈T a⌉₊ : ℝ) ≤ T a + 1 := (Nat.ceil_lt_add_one (hT a)).le
    have hcc₀ : (0 : ℝ) ≤ c * c₀ := by positivity
    dsimp only [clock, boundNat]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hceil hcc₀, mul_nonneg hcc₀ (hT a),
      mul_nonneg (Nat.cast_nonneg c) (hT a)]
  · have hfalse : ((ProbComp.eval (P.runClosed (clock a) (enc a))) [false]).toReal ≤ E.yesErr := by
      rw [hprob a false, div_le_iff₀ (by positivity)]
      simpa only [beq_false] using hyes a ha
    refine ⟨?_, hfalse⟩
    rw [hprob a true, le_div_iff₀ (by positivity)]
    have hsum : (acceptCount V a (ℓ a) : ℝ) + acceptCount (fun p => !V p) a (ℓ a) =
        (2 : ℝ) ^ ℓ a := by
      exact_mod_cast acceptCount_add_acceptCount_not V a (ℓ a)
    have hyes_a := hyes a ha
    have heq_true : acceptCount (fun p => V p == true) a (ℓ a) = acceptCount V a (ℓ a) := by
      simp only [beq_true]
    rw [heq_true]
    linarith
  · rw [hprob a true, div_le_iff₀ (by positivity)]
    simpa only [beq_true] using hno a ha

/-- Pad or truncate a seed `w` to exact length `n` using ones: always has length `n`, and equals
`w.take n` whenever `n ≤ w.length`. -/
private def padTake (ℓ : α → ℕ) (p : α × List Bool) : List Bool :=
  (p.2 ++ List.replicate (ℓ p.1) true).take (ℓ p.1)

private theorem length_padTake (ℓ : α → ℕ) (p : α × List Bool) :
    (padTake ℓ p).length = ℓ p.1 := by
  simp [padTake]

private theorem padTake_of_le (ℓ : α → ℕ) (a : α) {w : List Bool} (hw : ℓ a ≤ w.length) :
    padTake ℓ (a, w) = w.take (ℓ a) := by
  simp [padTake, List.take_append_of_le_length hw]

private theorem computableInO_padTake {ℓ : α → ℕ} {Tℓ Sℓ : α → ℕ}
    (hℓ : ComputableInO ℓ enc encUnary Tℓ Sℓ) :
    ∃ Tpad Spad : α × List Bool → ℕ,
      ComputableInO (padTake ℓ) (encPair enc encBits) encBits Tpad Spad ∧
      ∀ p, Tpad p ≤ 4 * (encPair enc encBits p).length + 2 * Tℓ p.1 := by
  have hℓ_fst := hℓ.comp (ComputableInO.fst enc encBits)
  have happ : ComputableInO (fun p : α × List Bool => p.2 ++ List.replicate (ℓ p.1) true)
      (encPair enc encBits) encBits _ _ :=
    (ComputableInO.snd enc encBits).append hℓ_fst fun _ => rfl
  have htake := (ComputableInO.of_linear ComputableInDegree.bitsTake).comp_linear
    (happ.prod hℓ_fst)
  refine ⟨_, _, htake, fun p => ?_⟩
  omega

/-- **Polynomial-time sample-and-verify characterization for arbitrary `ErrorModel`s.**
`Q` is solved at error profile `E` within polynomial time `((enc a).length + 1) ^ d` for some `d`
if and only if there exist a polynomial coin-count bound `p : Polynomial ℕ` and a polynomial-time
verifier `V : α × List Bool → Bool` achieving error profile `E` on `p.eval (enc a).length` random
bits. -/
theorem exists_solvesWithErrorInTimeO_poly_iff {Q : PromiseProblem α} {E : ErrorModel} :
    (∃ d : ℕ, SolvesWithErrorInTimeO Q enc E fun a => ((enc a).length + 1) ^ d) ↔
      ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
        ComputableInPolyTime V (encPair enc encBits) encBool ∧
        (∀ a ∈ Q.yes,
          (acceptCount (fun q => !V q) a (p.eval (enc a).length) : ℝ) ≤
            E.yesErr * 2 ^ p.eval (enc a).length) ∧
        (∀ a ∈ Q.no,
          (acceptCount V a (p.eval (enc a).length) : ℝ) ≤
            E.noErr * 2 ^ p.eval (enc a).length) := by
  constructor
  · rintro ⟨d, ℓ, V, Tℓ, Sℓ, Tv, Sv, c, hℓ, hV, ht, hyes, hno⟩
    obtain ⟨cℓ, hlen_ℓ⟩ := hℓ.length_le_time
    let M : ℕ := cℓ * (2 * c + 2)
    let p : Polynomial ℕ := Polynomial.C M * (Polynomial.X + 1) ^ d
    have hp_eval (n : ℕ) : p.eval n = M * (n + 1) ^ d := by simp [p]
    have hℓ_le_p (a : α) : ℓ a ≤ p.eval (enc a).length := by
      have hta := ht a (List.replicate (ℓ a) false) (List.length_replicate ..)
      have hTℓ : Tℓ a + 1 ≤ (2 * c + 2) * ((enc a).length + 1) ^ d := by
        have h1 : 1 ≤ ((enc a).length + 1) ^ d := Nat.one_le_pow _ _ (Nat.succ_pos _)
        have h2 : Tℓ a ≤ c * ((enc a).length + 1) ^ d + c := by
          have : (Tℓ a : ℝ) ≤ c * (((enc a).length : ℝ) + 1) ^ d + c := by
            linarith [(Nat.cast_nonneg (enc a).length : (0 : ℝ) ≤ _),
              (Nat.cast_nonneg (Tv (a, List.replicate (ℓ a) false)) : (0 : ℝ) ≤ _)]
          exact_mod_cast this
        nlinarith
      have h1 := hlen_ℓ a
      rw [encUnary_apply, List.length_replicate] at h1
      rw [hp_eval]
      exact h1.trans (by dsimp only [M]; rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left cℓ hTℓ)
    obtain ⟨Tpad, Spad, hpadO, hTpad⟩ := computableInO_padTake hℓ
    let V' (q : α × List Bool) : Bool := V (q.1, padTake ℓ q)
    have hV'O := hV.comp ((ComputableInO.fst enc encBits).prod hpadO)
    obtain ⟨cV', hV'_ts, -⟩ := hV'O
    have hV'_poly : ComputableInPolyTime V' (encPair enc encBits) encBool := by
      let polyClock (N : ℕ) : ℕ := cV' * (5 * N + 3 * (2 * c + 2) * (N + 1) ^ d + 2)
      refine (hV'_ts.mono (fun q => ?_) fun _ => le_rfl).computableInPolyTime
        (t := polyClock) (by dsimp only [polyClock]; fun_prop)
      set N : ℕ := (encPair enc encBits q).length
      have ha_le : (enc q.1).length ≤ N := by
        simp only [N, length_encPair]
        omega
      have hpow : ((enc q.1).length + 1) ^ d ≤ (N + 1) ^ d :=
        Nat.pow_le_pow_left (Nat.add_le_add_right ha_le 1) d
      have hta := ht q.1 (padTake ℓ q) (length_padTake ℓ q)
      have hsum_nat : Tℓ q.1 + Tv (q.1, padTake ℓ q) ≤ (2 * c + 2) * (N + 1) ^ d := by
        have h1 : Tℓ q.1 + Tv (q.1, padTake ℓ q) ≤ c * ((enc q.1).length + 1) ^ d + c := by
          have : ((Tℓ q.1 + Tv (q.1, padTake ℓ q) : ℕ) : ℝ) ≤
              c * (((enc q.1).length : ℝ) + 1) ^ d + c := by
            push_cast
            linarith [(Nat.cast_nonneg (enc q.1).length : (0 : ℝ) ≤ _)]
          exact_mod_cast this
        have h2 : 1 ≤ (N + 1) ^ d := Nat.one_le_pow _ _ (Nat.succ_pos _)
        nlinarith
      have htp := hTpad q
      dsimp only [polyClock]
      rw [Nat.mul_assoc 3]
      exact Nat.mul_le_mul_left cV' (by dsimp only [N] at *; omega)
    have hscale_gen (W₀ W₁ : α × List Bool → Bool) (a : α)
        (hprefix : ∀ u : List Bool, u.length = ℓ a → ∀ rest : List Bool,
          W₁ (a, u ++ rest) = W₀ (a, u)) :
        acceptCount W₁ a (p.eval (enc a).length) =
          acceptCount W₀ a (ℓ a) * 2 ^ (p.eval (enc a).length - ℓ a) := by
      have hsplit : p.eval (enc a).length = ℓ a + (p.eval (enc a).length - ℓ a) :=
        (Nat.add_sub_of_le (hℓ_le_p a)).symm
      conv_lhs => rw [hsplit]
      rw [acceptCount_add]
      have hterm : ∀ u : Fin (ℓ a) → Bool,
          acceptCount (fun x => W₁ (x.1, List.ofFn u ++ x.2)) a
            (p.eval (enc a).length - ℓ a) =
          if W₀ (a, List.ofFn u) = true then 2 ^ (p.eval (enc a).length - ℓ a) else 0 := by
        intro u
        have hcongr : acceptCount (fun x => W₁ (x.1, List.ofFn u ++ x.2)) a
            (p.eval (enc a).length - ℓ a) =
            acceptCount (fun _ => W₀ (a, List.ofFn u)) a (p.eval (enc a).length - ℓ a) :=
          acceptCount_congr (fun rest => hprefix (List.ofFn u) List.length_ofFn rest) _
        rw [hcongr]
        cases W₀ (a, List.ofFn u) <;> simp
      exact (Finset.sum_congr rfl fun u _ => hterm u).trans
        (by rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]; rfl)
    refine ⟨p, V', hV'_poly, fun a ha => ?_, fun a ha => ?_⟩
    · have hsc := hscale_gen (fun q => !V q) (fun q => !V' q) a fun u hu rest => by
        have hlen : ℓ a ≤ (u ++ rest).length := by simp [hu]
        simp [V', padTake_of_le ℓ a hlen, List.take_left' hu]
      have hpow_eq : (2 : ℝ) ^ p.eval (enc a).length =
          (2 : ℝ) ^ ℓ a * (2 : ℝ) ^ (p.eval (enc a).length - ℓ a) := by
        rw [← pow_add, Nat.add_sub_of_le (hℓ_le_p a)]
      rw [hsc, hpow_eq]
      push_cast
      have hy := mul_le_mul_of_nonneg_right (hyes a ha)
        (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (p.eval (enc a).length - ℓ a))
      linarith
    · have hsc := hscale_gen V V' a fun u hu rest => by
        have hlen : ℓ a ≤ (u ++ rest).length := by simp [hu]
        simp [V', padTake_of_le ℓ a hlen, List.take_left' hu]
      have hpow_eq : (2 : ℝ) ^ p.eval (enc a).length =
          (2 : ℝ) ^ ℓ a * (2 : ℝ) ^ (p.eval (enc a).length - ℓ a) := by
        rw [← pow_add, Nat.add_sub_of_le (hℓ_le_p a)]
      rw [hsc, hpow_eq]
      push_cast
      have hn := mul_le_mul_of_nonneg_right (hno a ha)
        (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (p.eval (enc a).length - ℓ a))
      linarith
  · rintro ⟨p, V, hV, hyes, hno⟩
    have hℓ_poly : ComputableInPolyTime (fun a : α => p.eval (enc a).length) enc encUnary := by
      fun_prop
    obtain ⟨dℓ, _, hℓ_deg⟩ := hℓ_poly.exists_degree
    obtain ⟨dV, _, hV_deg⟩ := hV.exists_degree
    obtain ⟨cp, dp, hp⟩ := hℓ_poly.polyBounded_length.exists_le
    set D : ℕ := max (max dℓ 1) ((dp + 1) * dV)
    let C : ℕ := 3 + (2 * cp + 5) ^ dV
    refine ⟨D, fun a => p.eval (enc a).length, V, _, _, _, _, C,
      hℓ_deg.inO, hV_deg.inO, fun a w hw => ?_, hyes, hno⟩
    set L : ℕ := (enc a).length
    have hL1 : 1 ≤ L + 1 := Nat.le_add_left 1 L
    have hw_le : w.length ≤ cp * (L + 1) ^ dp := by
      have hpa := hp a
      rw [encUnary_apply, List.length_replicate] at hpa
      exact hw.trans_le hpa
    have hpair_le : (encPair enc encBits (a, w)).length + 1 ≤
        (2 * cp + 5) * (L + 1) ^ (dp + 1) := by
      have h1 : 2 * L + 3 ≤ 3 * (L + 1) ^ (dp + 1) := by
        have : L + 1 ≤ (L + 1) ^ (dp + 1) := Nat.le_self_pow (Nat.succ_ne_zero dp) _
        omega
      have h2 : cp * (L + 1) ^ dp ≤ cp * (L + 1) ^ (dp + 1) :=
        Nat.mul_le_mul_left cp (Nat.pow_le_pow_right hL1 (Nat.le_succ dp))
      simp only [length_encPair, encBits, Function.Embedding.refl_apply,
        Nat.add_mul, Nat.mul_assoc]
      dsimp only [L] at *
      omega
    have hTv : ((encPair enc encBits (a, w)).length + 1) ^ dV ≤
        (2 * cp + 5) ^ dV * (L + 1) ^ D := by
      calc ((encPair enc encBits (a, w)).length + 1) ^ dV
          ≤ ((2 * cp + 5) * (L + 1) ^ (dp + 1)) ^ dV := Nat.pow_le_pow_left hpair_le dV
        _ = (2 * cp + 5) ^ dV * (L + 1) ^ ((dp + 1) * dV) := by rw [Nat.mul_pow, ← Nat.pow_mul]
        _ ≤ (2 * cp + 5) ^ dV * (L + 1) ^ D :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hL1 (le_max_right _ _))
    have hdℓ : (L + 1) ^ dℓ ≤ (L + 1) ^ D :=
      Nat.pow_le_pow_right hL1 ((le_max_left dℓ 1).trans (le_max_left _ _))
    have hL_le : L ≤ (L + 1) ^ D :=
      (Nat.le_succ L).trans
        (Nat.le_self_pow (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one
          ((le_max_right dℓ 1).trans (le_max_left _ _)))) _)
    have hnat : L + (L + 1) ^ dℓ + ((encPair enc encBits (a, w)).length + 1) ^ dV ≤
        C * (L + 1) ^ D + C := by
      dsimp only [C]
      rw [Nat.add_mul]
      omega
    dsimp only [L] at hnat ⊢
    exact_mod_cast hnat

/-- **`PromiseBPP` in terms of `SolvesWithErrorInTimeO`.** A promise problem lies in `PromiseBPP`
if and only if it is solved at `ErrorModel.bounded` (`1 / 3`) within polynomial time
`((enc a).length + 1) ^ d`. -/
theorem mem_PromiseBPP_iff_exists_solvesWithErrorInTimeO {Q : PromiseProblem α} :
    Q ∈ PromiseBPP enc ↔
      ∃ d : ℕ, SolvesWithErrorInTimeO Q enc ErrorModel.bounded
        fun a => ((enc a).length + 1) ^ d := by
  rw [mem_PromiseBPP_iff, exists_solvesWithErrorInTimeO_poly_iff]
  refine exists_congr fun p => exists_congr fun V => and_congr_right fun _ => ?_
  constructor
  · intro hQ
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · have hy : 2 * 2 ^ p.eval (enc a).length ≤
          3 * acceptCount V a (p.eval (enc a).length) := (hQ a).1 ha
      have hsum := acceptCount_add_acceptCount_not V a (p.eval (enc a).length)
      have h3R : (3 : ℝ) * acceptCount (fun q => !V q) a (p.eval (enc a).length) ≤
          (2 : ℝ) ^ p.eval (enc a).length := by exact_mod_cast (show 3 * _ ≤ _ by omega)
      simp only [ErrorModel.bounded, ErrorModel.twoSided]
      linarith
    · have hn := (hQ a).2 ha
      have hsum := acceptCount_add_card_filter_eq_false (V := V) (a := a)
        (n := p.eval (enc a).length)
      have h3R : (3 : ℝ) * acceptCount V a (p.eval (enc a).length) ≤
          (2 : ℝ) ^ p.eval (enc a).length := by exact_mod_cast (show 3 * _ ≤ _ by omega)
      simp only [ErrorModel.bounded, ErrorModel.twoSided]
      linarith
  · rintro ⟨hyes, hno⟩ a
    refine ⟨fun ha => ?_, fun ha => ?_⟩
    · change 2 * 2 ^ p.eval (enc a).length ≤ 3 * acceptCount V a (p.eval (enc a).length)
      have hy := hyes a ha
      simp only [ErrorModel.bounded, ErrorModel.twoSided] at hy
      have hsum : (acceptCount V a (p.eval (enc a).length) : ℝ) +
          acceptCount (fun q => !V q) a (p.eval (enc a).length) =
          (2 : ℝ) ^ p.eval (enc a).length := by
        exact_mod_cast acceptCount_add_acceptCount_not V a (p.eval (enc a).length)
      have hR : (2 : ℝ) * (2 : ℝ) ^ p.eval (enc a).length ≤
          3 * acceptCount V a (p.eval (enc a).length) := by linarith
      exact_mod_cast hR
    · rw [BoundedErrorAt]
      have hn := hno a ha
      simp only [ErrorModel.bounded, ErrorModel.twoSided] at hn
      have hsum : (acceptCount V a (p.eval (enc a).length) : ℝ) +
          (Finset.univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
            V (a, List.ofFn r) = false).card =
          (2 : ℝ) ^ p.eval (enc a).length := by
        exact_mod_cast acceptCount_add_card_filter_eq_false (V := V) (a := a)
          (n := p.eval (enc a).length)
      have hR : (2 : ℝ) * (2 : ℝ) ^ p.eval (enc a).length ≤
          3 * (Finset.univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
            V (a, List.ofFn r) = false).card := by linarith
      exact_mod_cast hR

/-- **`PromiseRP` in terms of `SolvesWithErrorInTimeO`.** A promise problem lies in `PromiseRP`
if and only if it is solved at `ErrorModel.rp` (`yesErr = 1 / 2`, `noErr = 0`) within polynomial
time `((enc a).length + 1) ^ d`. -/
theorem mem_PromiseRP_iff_exists_solvesWithErrorInTimeO {Q : PromiseProblem α} :
    Q ∈ PromiseRP enc ↔
      ∃ d : ℕ, SolvesWithErrorInTimeO Q enc ErrorModel.rp
        fun a => ((enc a).length + 1) ^ d := by
  rw [mem_PromiseRP_iff, exists_solvesWithErrorInTimeO_poly_iff]
  refine exists_congr fun p => exists_congr fun V => and_congr_right fun _ => ?_
  constructor
  · intro hQ
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · have hy : 2 ^ p.eval (enc a).length ≤
          2 * acceptCount V a (p.eval (enc a).length) := (hQ a).1 ha
      have hsum := acceptCount_add_acceptCount_not V a (p.eval (enc a).length)
      have h2R : (2 : ℝ) * acceptCount (fun q => !V q) a (p.eval (enc a).length) ≤
          (2 : ℝ) ^ p.eval (enc a).length := by exact_mod_cast (show 2 * _ ≤ _ by omega)
      simp only [ErrorModel.rp, ErrorModel.oneSidedRP]
      linarith
    · have hn := (hQ a).2 ha
      have h0 : acceptCount V a (p.eval (enc a).length) = 0 := acceptCount_eq_zero_iff.2 hn
      simp only [h0, Nat.cast_zero, ErrorModel.rp, ErrorModel.oneSidedRP, zero_mul, le_rfl]
  · rintro ⟨hyes, hno⟩ a
    refine ⟨fun ha => ?_, fun ha r => ?_⟩
    · have hy := hyes a ha
      simp only [ErrorModel.rp, ErrorModel.oneSidedRP] at hy
      have hsum : (acceptCount V a (p.eval (enc a).length) : ℝ) +
          acceptCount (fun q => !V q) a (p.eval (enc a).length) =
          (2 : ℝ) ^ p.eval (enc a).length := by
        exact_mod_cast acceptCount_add_acceptCount_not V a (p.eval (enc a).length)
      have hR : (2 : ℝ) ^ p.eval (enc a).length ≤
          2 * acceptCount V a (p.eval (enc a).length) := by linarith
      exact_mod_cast hR
    · have hn := hno a ha
      simp only [ErrorModel.rp, ErrorModel.oneSidedRP, zero_mul] at hn
      have h0 : acceptCount V a (p.eval (enc a).length) = 0 :=
        Nat.eq_zero_of_le_zero (by exact_mod_cast hn)
      exact acceptCount_eq_zero_iff.1 h0 r

/-- **`PromiseCoRP` in terms of `SolvesWithErrorInTimeO`.** -/
theorem mem_PromiseCoRP_iff_exists_solvesWithErrorInTimeO {Q : PromiseProblem α} :
    Q ∈ PromiseCoRP enc ↔
      ∃ d : ℕ, SolvesWithErrorInTimeO Q enc ErrorModel.coRP
        fun a => ((enc a).length + 1) ^ d := by
  rw [← compl_mem_PromiseRP_iff, mem_PromiseRP_iff_exists_solvesWithErrorInTimeO]
  refine exists_congr fun d => ⟨fun h => ?_, fun h => ?_⟩
  · simpa only [compl_compl, ErrorModel.symm_rp] using h.compl
  · simpa only [ErrorModel.symm_coRP] using h.compl

/-! ### Rate-preserving error amplification (`O(T a)` and exact rate `δ`) -/

/-- Collect `K` Boolean votes from `K` consecutive `ℓ a`-bit slices of `p.2`, padding short seeds
with ones so every verifier call receives a seed of exact length `ℓ p.1`. -/
private def collectVotesConst : ℕ → (α → ℕ) → (α × List Bool → Bool) → α × List Bool → List Bool
  | 0, _, _, _ => []
  | K + 1, ℓ, V, p =>
    V (p.1, padTake ℓ p) :: collectVotesConst K ℓ V (p.1, p.2.drop (ℓ p.1))

@[simp] private theorem length_collectVotesConst (K : ℕ) (ℓ : α → ℕ)
    (V : α × List Bool → Bool) (p : α × List Bool) :
    (collectVotesConst K ℓ V p).length = K := by
  induction K generalizing p with
  | zero => rfl
  | succ K ih => simp [collectVotesConst, ih]

private theorem collectVotesConst_eq_map_listRows (K : ℕ) (ℓ : α → ℕ)
    (V : α × List Bool → Bool) (a : α) :
    ∀ w : List Bool, w.length = K * ℓ a →
      collectVotesConst K ℓ V (a, w) =
        (BitString.listRows K (ℓ a) w).map fun row => V (a, row) := by
  induction K with
  | zero =>
    intro w _
    simp [collectVotesConst, BitString.listRows]
  | succ K ih =>
    intro w hw
    have hle : ℓ a ≤ w.length := by
      rw [hw, Nat.succ_mul]
      exact Nat.le_add_left _ _
    have htake_len : (w.take (ℓ a)).length = ℓ a := List.length_take_of_le hle
    have hdrop_len : (w.drop (ℓ a)).length = K * ℓ a := by
      rw [List.length_drop, hw, Nat.succ_mul, Nat.add_sub_cancel]
    conv_rhs => rw [← List.take_append_drop (ℓ a) w,
      BitString.listRows_succ_append K (ℓ a) htake_len (w.drop (ℓ a)), List.map_cons]
    rw [collectVotesConst, padTake_of_le ℓ a hle, ih (w.drop (ℓ a)) hdrop_len]

private theorem collectVotesConst_ofFn (K : ℕ) (ℓ : α → ℕ) (V : α × List Bool → Bool) (a : α)
    (x : BitString (K * ℓ a)) :
    collectVotesConst K ℓ V (a, List.ofFn x) =
      List.ofFn fun i : Fin K => V (a, List.ofFn (BitString.block x i)) := by
  rw [collectVotesConst_eq_map_listRows K ℓ V a (List.ofFn x) List.length_ofFn,
    BitString.listRows_ofFn, List.map_ofFn, Function.comp_def]

private theorem computableInO_const_mul_unary (K : ℕ) {ℓ : α → ℕ} {Tℓ Sℓ : α → ℕ}
    (hℓ : ComputableInO ℓ enc encUnary Tℓ Sℓ) :
    ∃ TK SK : α → ℕ, ComputableInO (fun a => K * ℓ a) enc encUnary TK SK ∧
      ∀ a, TK a = (enc a).length + K * Tℓ a := by
  induction K with
  | zero =>
    refine ⟨fun a => (enc a).length, fun _ => 0, ?_, fun a => by simp⟩
    simpa only [Nat.zero_mul] using ComputableInO.constZero (encIn := enc) (encMid := encUnary) 0
  | succ K ih =>
    obtain ⟨TK, SK, hTK, hTK_eq⟩ := ih
    have happ := hTK.append hℓ (encOut := encUnary) (g := fun a => (K + 1) * ℓ a) fun a => by
      simp only [encUnary_apply, Nat.succ_mul, List.replicate_add]
    refine ⟨_, _, happ, fun a => ?_⟩
    rw [hTK_eq a, Nat.succ_mul, Nat.add_assoc]

private theorem computableInO_collectVotesConst (K : ℕ) {ℓ : α → ℕ}
    {V : α × List Bool → Bool} {Tℓ Sℓ : α → ℕ} {Tv Sv : α × List Bool → ℕ} {T : α → ℝ} {c : ℕ}
    (hℓ : ComputableInO ℓ enc encUnary Tℓ Sℓ)
    (hV : ComputableInO V (encPair enc encBits) encBool Tv Sv)
    (ht : ∀ a w, w.length = ℓ a → ((enc a).length + Tℓ a + Tv (a, w) : ℝ) ≤ c * T a + c) :
    ∃ (T_K S_K : α × List Bool → ℕ) (M_K : ℕ),
      ComputableInO (collectVotesConst K ℓ V) (encPair enc encBits) encBits T_K S_K ∧
      ∀ a w, w.length ≤ K * ℓ a → (T_K (a, w) : ℝ) ≤ M_K * (c * T a + c + 1) := by
  obtain ⟨cℓ, hlen_ℓ⟩ := hℓ.length_le_time
  have hbase_bound (a : α) : ((enc a).length + Tℓ a : ℝ) ≤ c * T a + c := by
    have h0 := ht a (List.replicate (ℓ a) false) (List.length_replicate ..)
    linarith [(Nat.cast_nonneg (Tv (a, List.replicate (ℓ a) false)) : (0 : ℝ) ≤ _)]
  have hZ_ge1 (a : α) : (1 : ℝ) ≤ c * T a + c + 1 := by
    have := hbase_bound a
    linarith [(Nat.cast_nonneg (enc a).length : (0 : ℝ) ≤ _),
      (Nat.cast_nonneg (Tℓ a) : (0 : ℝ) ≤ _)]
  have hℓ_bound (a : α) : (ℓ a : ℝ) ≤ cℓ * (c * T a + c + 1) := by
    have h1 := hlen_ℓ a
    rw [encUnary_apply, List.length_replicate] at h1
    have h1R : (ℓ a : ℝ) ≤ cℓ * ((Tℓ a : ℝ) + 1) := by exact_mod_cast h1
    have hTℓ1 : (Tℓ a : ℝ) + 1 ≤ c * T a + c + 1 := by
      have := hbase_bound a
      linarith [(Nat.cast_nonneg (enc a).length : (0 : ℝ) ≤ _)]
    exact h1R.trans (mul_le_mul_of_nonneg_left hTℓ1 (Nat.cast_nonneg cℓ))
  obtain ⟨Tpad, Spad, hpadO, hTpad⟩ := computableInO_padTake hℓ
  have hhead : ComputableInO (fun p : α × List Bool => V (p.1, padTake ℓ p))
      (encPair enc encBits) encBool
      (fun p => ((encPair enc encBits p).length + Tpad p) + Tv (p.1, padTake ℓ p))
      (fun p => ((encPair enc encBits p).length + Spad p) + Sv (p.1, padTake ℓ p)) :=
    hV.comp ((ComputableInO.fst enc encBits).prod hpadO)
  have hℓ_fst := hℓ.comp (ComputableInO.fst enc encBits)
  have hdrop := (ComputableInO.of_linear ComputableInDegree.bitsDrop).comp_linear
    ((ComputableInO.snd enc encBits).prod hℓ_fst)
  have hnext := (ComputableInO.fst enc encBits).prod hdrop
  induction K with
  | zero =>
    refine ⟨fun p => (encPair enc encBits p).length, fun _ => 0, 2,
      ComputableInO.constZero (encIn := encPair enc encBits) (encMid := encBits) [],
      fun a w hw => ?_⟩
    rw [Nat.zero_mul] at hw
    have hw0 : w = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hw)
    subst hw0
    dsimp only
    have hplen : (encPair enc encBits (a, [])).length = 2 * (enc a).length + 1 := by
      simp
    rw [hplen]
    have hb := hbase_bound a
    have hTℓ_nn : (0 : ℝ) ≤ Tℓ a := Nat.cast_nonneg _
    push_cast
    linarith
  | succ K ih =>
    obtain ⟨TK, SK, MK, hKO, hMK⟩ := ih
    have hstep := hhead.append (hKO.comp hnext) (encOut := encBits)
      (g := collectVotesConst (K + 1) ℓ V) fun _ => rfl
    let M_next : ℕ := MK + 36 + 10 * (K + 1) * cℓ
    refine ⟨_, _, M_next, hstep, fun a w hw => ?_⟩
    set Z : ℝ := c * T a + c + 1
    have hZ1 : 1 ≤ Z := hZ_ge1 a
    have hZ_nn : 0 ≤ Z := zero_le_one.trans hZ1
    have hwR : (w.length : ℝ) ≤ ((K + 1) * cℓ : ℕ) * Z := by
      have hw1 : (w.length : ℝ) ≤ (K + 1 : ℕ) * (ℓ a : ℝ) := by exact_mod_cast hw
      have hw2 := mul_le_mul_of_nonneg_left (hℓ_bound a) (Nat.cast_nonneg (K + 1))
      push_cast at hw1 hw2 ⊢
      dsimp only [Z] at hw2 ⊢
      linarith [show ((K + 1 : ℝ) * (cℓ * Z)) = ((K + 1) * cℓ) * Z by ring]
    have hplen : ((encPair enc encBits (a, w)).length : ℝ) ≤ (4 + (K + 1) * cℓ : ℕ) * Z := by
      have hp_eq : ((encPair enc encBits (a, w)).length : ℝ) =
          2 * (enc a).length + 1 + w.length := by
        simp only [length_encPair, encBits, Function.Embedding.refl_apply]
        push_cast
        ring
      rw [hp_eq]
      have hb := hbase_bound a
      have hTℓ_nn : (0 : ℝ) ≤ Tℓ a := Nat.cast_nonneg _
      push_cast at hwR ⊢
      dsimp only [Z] at hb hwR ⊢
      linarith
    have hpad_bound : (Tpad (a, w) : ℝ) ≤ (18 + 4 * (K + 1) * cℓ : ℕ) * Z := by
      have htp : (Tpad (a, w) : ℝ) ≤
          4 * (encPair enc encBits (a, w)).length + 2 * (Tℓ a : ℝ) := by
        exact_mod_cast hTpad (a, w)
      have hb := hbase_bound a
      have ha_nn : (0 : ℝ) ≤ (enc a).length := Nat.cast_nonneg _
      push_cast at hplen ⊢
      dsimp only [Z] at hb hplen ⊢
      linarith
    have hTv_pad : (Tv (a, padTake ℓ (a, w)) : ℝ) ≤ Z := by
      have hta := ht a (padTake ℓ (a, w)) (length_padTake ℓ (a, w))
      dsimp only [Z]
      linarith [(Nat.cast_nonneg (enc a).length : (0 : ℝ) ≤ _),
        (Nat.cast_nonneg (Tℓ a) : (0 : ℝ) ≤ _)]
    have hdrop_le : (w.drop (ℓ a)).length ≤ K * ℓ a := by
      rw [List.length_drop]
      rw [Nat.succ_mul] at hw
      omega
    have hTK_bound : (TK (a, w.drop (ℓ a)) : ℝ) ≤ MK * Z := hMK a (w.drop (ℓ a)) hdrop_le
    have hnext_time : (((encPair enc encBits (a, w)).length +
        ((encPair enc encBits (a, w)).length +
          ((encPair enc encBits (a, w)).length + Tℓ a))) : ℝ) ≤
        (13 + 3 * (K + 1) * cℓ : ℕ) * Z := by
      have hb := hbase_bound a
      have ha_nn : (0 : ℝ) ≤ (enc a).length := Nat.cast_nonneg _
      push_cast at hplen ⊢
      dsimp only [Z] at hb hplen ⊢
      linarith
    have hcℓ_Z : 0 ≤ ((K + 1) * cℓ : ℝ) * Z := by positivity
    change (((((encPair enc encBits (a, w)).length + Tpad (a, w)) + Tv (a, padTake ℓ (a, w))) +
      (((encPair enc encBits (a, w)).length +
        ((encPair enc encBits (a, w)).length +
          ((encPair enc encBits (a, w)).length + Tℓ a))) + TK (a, w.drop (ℓ a))) : ℕ) : ℝ) ≤ _
    dsimp only [M_next]
    push_cast at hplen hpad_bound hnext_time ⊢
    linarith

/-- **Rate-preserving two-sided error amplification.** Repeating a two-sided `ε₁`-error solver
`2 r` times and taking strict majority reduces the error to `(4 * ε₁ * (1 - ε₁)) ^ r ≤ ε₂` while
preserving `O(T a)` up to a constant factor. -/
theorem SolvesWithErrorInTimeO.amplify_twoSided {Q : PromiseProblem α} {T : α → ℝ}
    (hT : ∀ a, 0 ≤ T a) {ε₁ ε₂ : ℝ} {h0₁ : 0 ≤ ε₁} {h1₁ : ε₁ < 1 / 2}
    (h0₂ : 0 < ε₂) (h1₂ : ε₂ < 1 / 2)
    (h : SolvesWithErrorInTimeO Q enc (ErrorModel.twoSided ε₁ h0₁ h1₁) T) :
    SolvesWithErrorInTimeO Q enc (ErrorModel.twoSided ε₂ h0₂.le h1₂) T := by
  have hbase_lt : 4 * ε₁ * (1 - ε₁) < 1 := by
    have hsq : 0 < (1 - 2 * ε₁) ^ 2 := sq_pos_of_ne_zero (by linarith)
    nlinarith
  have hbase_nn : 0 ≤ 4 * ε₁ * (1 - ε₁) := by nlinarith
  obtain ⟨r, hr⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one hbase_nn hbase_lt).eventually
    (gt_mem_nhds h0₂)).exists
  obtain ⟨ℓ, V, Tℓ, Sℓ, Tv, Sv, c, hℓ, hV, ht, hyes, hno⟩ := h
  obtain ⟨Tℓ', Sℓ', hℓ'O, hTℓ'_eq⟩ := computableInO_const_mul_unary (2 * r) hℓ
  obtain ⟨Tvotes, Svotes, Mvotes, hvotesO, hTvotes⟩ :=
    computableInO_collectVotesConst (2 * r) hℓ hV ht
  have hmaj_poly : ComputableInPolyTime (fun votes : List Bool => decide (r < votes.countP id))
      encBits encBool := by fun_prop
  obtain ⟨dmaj, _, hmaj_deg⟩ := hmaj_poly.exists_degree
  let V_maj (p : α × List Bool) : Bool :=
    decide (r < (collectVotesConst (2 * r) ℓ V p).countP id)
  have hVmajO : ComputableInO V_maj (encPair enc encBits) encBool _ _ :=
    hmaj_deg.inO.comp hvotesO
  let C_total : ℕ := (2 + 2 * r + Mvotes) * (c + 1) + (2 * r + 1) ^ dmaj
  refine ⟨fun a => (2 * r) * ℓ a, V_maj, _, _, _, _, C_total, hℓ'O, hVmajO,
    fun a w hw => ?_, fun a ha => ?_, fun a ha => ?_⟩
  · have hbase_a : ((enc a).length + Tℓ a : ℝ) ≤ c * T a + c := by
      have h0 := ht a (List.replicate (ℓ a) false) (List.length_replicate ..)
      linarith [(Nat.cast_nonneg (Tv (a, List.replicate (ℓ a) false)) : (0 : ℝ) ≤ _)]
    have htv := hTvotes a w hw.le
    have hvlen : ((collectVotesConst (2 * r) ℓ V (a, w)).length + 1) ^ dmaj =
        (2 * r + 1) ^ dmaj := by
      rw [length_collectVotesConst]
    simp only [encBits, Function.Embedding.refl_apply, C_total]
    rw [hTℓ'_eq a, hvlen]
    have hTa := hT a
    have h1 : ((enc a).length : ℝ) + ((enc a).length + 2 * (r : ℝ) * Tℓ a) ≤
        (2 + 2 * (r : ℝ)) * (c * T a + c + 1) := by
      have hL : ((enc a).length : ℝ) ≤ c * T a + c + 1 := by
        linarith [(Nat.cast_nonneg (Tℓ a) : (0 : ℝ) ≤ _)]
      have hTℓ : (Tℓ a : ℝ) ≤ c * T a + c + 1 := by
        linarith [(Nat.cast_nonneg (enc a).length : (0 : ℝ) ≤ _)]
      have hm := mul_le_mul_of_nonneg_left hTℓ (by positivity : (0 : ℝ) ≤ 2 * (r : ℝ))
      linarith
    have h2 : (2 + 2 * (r : ℝ) + Mvotes) * (c * T a + c + 1) ≤
        ((2 + 2 * (r : ℝ) + Mvotes) * (c + 1)) * T a +
          (2 + 2 * (r : ℝ) + Mvotes) * (c + 1) := by
      have hpos : (0 : ℝ) ≤ (2 + 2 * (r : ℝ) + Mvotes) * T a := by positivity
      linarith [show (2 + 2 * (r : ℝ) + Mvotes) * (c * T a + c + 1) =
        ((2 + 2 * (r : ℝ) + Mvotes) * c) * T a + (2 + 2 * (r : ℝ) + Mvotes) * (c + 1) by ring,
        show ((2 + 2 * (r : ℝ) + Mvotes) * (c + 1)) * T a =
        ((2 + 2 * (r : ℝ) + Mvotes) * c) * T a + (2 + 2 * (r : ℝ) + Mvotes) * T a by ring]
    have h3 : (0 : ℝ) ≤ ((2 * (r : ℝ) + 1) ^ dmaj) * T a := by positivity
    push_cast at htv ⊢
    linarith
  · -- Yes-instance error bound via `card_filter_card_filter_le_of_err_lt_half`
    let G : Finset (Fin (ℓ a) → Bool) :=
      Finset.univ.filter fun u => V (a, List.ofFn u) = true
    have hG : (1 - ε₁) * (Fintype.card (Fin (ℓ a) → Bool) : ℝ) ≤ G.card := by
      have hy := hyes a ha
      simp only [ErrorModel.twoSided] at hy
      have hsum : (G.card : ℝ) + acceptCount (fun q => !V q) a (ℓ a) = (2 : ℝ) ^ ℓ a := by
        exact_mod_cast acceptCount_add_acceptCount_not V a (ℓ a)
      have hcard : (Fintype.card (Fin (ℓ a) → Bool) : ℝ) = (2 : ℝ) ^ ℓ a := by simp
      rw [hcard]
      linarith
    have hmom := card_filter_card_filter_le_of_err_lt_half G h0₁ h1₁ hG r
    have hcard_Omega : (Fintype.card (Fin (ℓ a) → Bool) : ℝ) ^ (2 * r) =
        (2 : ℝ) ^ ((2 * r) * ℓ a) := by
      simp [pow_mul, mul_comm]
    rw [hcard_Omega] at hmom
    have hbad_eq : acceptCount (fun q => !V_maj q) a ((2 * r) * ℓ a) =
        (Finset.univ.filter fun ω : Fin (2 * r) → (Fin (ℓ a) → Bool) =>
          (Finset.univ.filter fun i => ω i ∈ G).card ≤ r).card := by
      rw [acceptCount]
      refine Finset.card_equiv BitString.blocksEquiv fun x => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, V_maj,
        collectVotesConst_ofFn, List.countP_ofFn, Finset.card_filter, id_eq,
        Bool.not_eq_true', decide_eq_false_iff_not, not_lt, BitString.blocksEquiv_apply, G]
    rw [hbad_eq]
    simp only [ErrorModel.twoSided]
    exact hmom.trans (mul_le_mul_of_nonneg_right hr.le (by positivity))
  · -- No-instance error bound via `card_filter_card_filter_le_of_err_lt_half` on `V = false`
    let G : Finset (Fin (ℓ a) → Bool) :=
      Finset.univ.filter fun u => V (a, List.ofFn u) = false
    have hG : (1 - ε₁) * (Fintype.card (Fin (ℓ a) → Bool) : ℝ) ≤ G.card := by
      have hn := hno a ha
      simp only [ErrorModel.twoSided] at hn
      have hsum : (acceptCount V a (ℓ a) : ℝ) + G.card = (2 : ℝ) ^ ℓ a := by
        exact_mod_cast acceptCount_add_card_filter_eq_false (V := V) (a := a) (n := ℓ a)
      have hcard : (Fintype.card (Fin (ℓ a) → Bool) : ℝ) = (2 : ℝ) ^ ℓ a := by simp
      rw [hcard]
      linarith
    have hmom := card_filter_card_filter_le_of_err_lt_half G h0₁ h1₁ hG r
    have hcard_Omega : (Fintype.card (Fin (ℓ a) → Bool) : ℝ) ^ (2 * r) =
        (2 : ℝ) ^ ((2 * r) * ℓ a) := by
      simp [pow_mul, mul_comm]
    rw [hcard_Omega] at hmom
    have hbad_le : acceptCount V_maj a ((2 * r) * ℓ a) ≤
        (Finset.univ.filter fun ω : Fin (2 * r) → (Fin (ℓ a) → Bool) =>
          (Finset.univ.filter fun i => ω i ∈ G).card ≤ r).card := by
      rw [acceptCount, ← Finset.card_map BitString.blocksEquiv.toEmbedding]
      refine Finset.card_le_card fun ω hω => ?_
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, V_maj,
        collectVotesConst_ofFn, List.countP_ofFn, ← Finset.card_filter, id_eq,
        decide_eq_true_eq] at hx
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have hpart := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin (2 * r))))
        fun i => V (a, List.ofFn (BitString.block x i)) = true
      simp only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fin] at hpart
      have hG_card : (Finset.univ.filter
          fun i : Fin (2 * r) => BitString.blocksEquiv.toEmbedding x i ∈ G).card =
          (Finset.univ.filter fun i : Fin (2 * r) =>
            V (a, List.ofFn (BitString.block x i)) = false).card :=
        congrArg Finset.card (Finset.filter_congr fun i _ => by simp [G])
      rw [hG_card]
      omega
    have hbad_leR : (acceptCount V_maj a ((2 * r) * ℓ a) : ℝ) ≤
        (Finset.univ.filter fun ω : Fin (2 * r) → (Fin (ℓ a) → Bool) =>
          (Finset.univ.filter fun i => ω i ∈ G).card ≤ r).card := by exact_mod_cast hbad_le
    simp only [ErrorModel.twoSided]
    exact (hbad_leR.trans hmom).trans (mul_le_mul_of_nonneg_right hr.le (by positivity))

/-- **Two-sided threshold invariance.** Any two error bounds `ε₁, ε₂ ∈ (0, 1 / 2)` yield the exact
same `SolvesWithErrorInTimeO` predicate (for `0 ≤ T a`). -/
theorem solvesWithErrorInTimeO_twoSided_iff {Q : PromiseProblem α} {T : α → ℝ}
    (hT : ∀ a, 0 ≤ T a) {ε₁ ε₂ : ℝ} (h0₁ : 0 < ε₁) (h1₁ : ε₁ < 1 / 2)
    (h0₂ : 0 < ε₂) (h1₂ : ε₂ < 1 / 2) :
    SolvesWithErrorInTimeO Q enc (ErrorModel.twoSided ε₁ h0₁.le h1₁) T ↔
      SolvesWithErrorInTimeO Q enc (ErrorModel.twoSided ε₂ h0₂.le h1₂) T :=
  ⟨fun h => h.amplify_twoSided hT h0₂ h1₂, fun h => h.amplify_twoSided hT h0₁ h1₁⟩

/-- **Rate-preserving one-sided `RP` error amplification.** Taking the disjunction of `m` runs
reduces false-negative error from `ε₁ ∈ [0, 1)` to `ε₁ ^ m ≤ ε₂` while keeping zero false-positive
error and runtime `O(T a)`. -/
theorem SolvesWithErrorInTimeO.amplify_oneSidedRP {Q : PromiseProblem α} {T : α → ℝ}
    (hT : ∀ a, 0 ≤ T a) {ε₁ ε₂ : ℝ} {h0₁ : 0 ≤ ε₁} {h1₁ : ε₁ < 1}
    (h0₂ : 0 < ε₂) (h1₂ : ε₂ < 1)
    (h : SolvesWithErrorInTimeO Q enc (ErrorModel.oneSidedRP ε₁ h0₁ h1₁) T) :
    SolvesWithErrorInTimeO Q enc (ErrorModel.oneSidedRP ε₂ h0₂.le h1₂) T := by
  obtain ⟨m, hm⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one h0₁ h1₁).eventually
    (gt_mem_nhds h0₂)).exists
  obtain ⟨ℓ, V, Tℓ, Sℓ, Tv, Sv, c, hℓ, hV, ht, hyes, hno⟩ := h
  obtain ⟨Tℓ', Sℓ', hℓ'O, hTℓ'_eq⟩ := computableInO_const_mul_unary m hℓ
  obtain ⟨Tvotes, Svotes, Mvotes, hvotesO, hTvotes⟩ :=
    computableInO_collectVotesConst m hℓ hV ht
  have hany_poly : ComputableInPolyTime (fun votes : List Bool => votes.any id)
      encBits encBool := by fun_prop
  obtain ⟨dany, _, hany_deg⟩ := hany_poly.exists_degree
  let V_any (p : α × List Bool) : Bool := (collectVotesConst m ℓ V p).any id
  have hVanyO : ComputableInO V_any (encPair enc encBits) encBool _ _ :=
    hany_deg.inO.comp hvotesO
  let C_total : ℕ := (2 + m + Mvotes) * (c + 1) + (m + 1) ^ dany
  refine ⟨fun a => m * ℓ a, V_any, _, _, _, _, C_total, hℓ'O, hVanyO,
    fun a w hw => ?_, fun a ha => ?_, fun a ha => ?_⟩
  · have hbase_a : ((enc a).length + Tℓ a : ℝ) ≤ c * T a + c := by
      have h0 := ht a (List.replicate (ℓ a) false) (List.length_replicate ..)
      linarith [(Nat.cast_nonneg (Tv (a, List.replicate (ℓ a) false)) : (0 : ℝ) ≤ _)]
    have htv := hTvotes a w hw.le
    have hvlen : ((collectVotesConst m ℓ V (a, w)).length + 1) ^ dany = (m + 1) ^ dany := by
      rw [length_collectVotesConst]
    simp only [encBits, Function.Embedding.refl_apply, C_total]
    rw [hTℓ'_eq a, hvlen]
    have hTa := hT a
    have h1 : ((enc a).length : ℝ) + ((enc a).length + (m : ℝ) * Tℓ a) ≤
        (2 + (m : ℝ)) * (c * T a + c + 1) := by
      have hL : ((enc a).length : ℝ) ≤ c * T a + c + 1 := by
        linarith [(Nat.cast_nonneg (Tℓ a) : (0 : ℝ) ≤ _)]
      have hTℓ : (Tℓ a : ℝ) ≤ c * T a + c + 1 := by
        linarith [(Nat.cast_nonneg (enc a).length : (0 : ℝ) ≤ _)]
      have hm' := mul_le_mul_of_nonneg_left hTℓ (Nat.cast_nonneg m)
      linarith
    have h2 : (2 + (m : ℝ) + Mvotes) * (c * T a + c + 1) ≤
        ((2 + (m : ℝ) + Mvotes) * (c + 1)) * T a +
          (2 + (m : ℝ) + Mvotes) * (c + 1) := by
      have hpos : (0 : ℝ) ≤ (2 + (m : ℝ) + Mvotes) * T a := by positivity
      linarith [show (2 + (m : ℝ) + Mvotes) * (c * T a + c + 1) =
        ((2 + (m : ℝ) + Mvotes) * c) * T a + (2 + (m : ℝ) + Mvotes) * (c + 1) by ring,
        show ((2 + (m : ℝ) + Mvotes) * (c + 1)) * T a =
        ((2 + (m : ℝ) + Mvotes) * c) * T a + (2 + (m : ℝ) + Mvotes) * T a by ring]
    have h3 : (0 : ℝ) ≤ (((m : ℝ) + 1) ^ dany) * T a := by positivity
    push_cast at htv ⊢
    linarith
  · let R : Finset (Fin (ℓ a) → Bool) :=
      Finset.univ.filter fun u => V (a, List.ofFn u) = false
    have hcard_le : acceptCount (fun q => !V_any q) a (m * ℓ a) ≤ R.card ^ m := by
      rw [acceptCount, ← Fintype.card_piFinset_const,
        ← Finset.card_map BitString.blocksEquiv.toEmbedding]
      refine Finset.card_le_card fun ω hω => ?_
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, V_any,
        collectVotesConst_ofFn, Bool.not_eq_true', List.any_eq_false, List.mem_ofFn,
        forall_exists_index, forall_apply_eq_imp_iff, id_eq, Bool.not_eq_true] at hx
      simpa only [Fintype.mem_piFinset, R, Finset.mem_filter, Finset.mem_univ, true_and,
        Equiv.coe_toEmbedding, BitString.blocksEquiv_apply] using hx
    have hR_bound : (R.card : ℝ) ≤ ε₁ * (2 : ℝ) ^ ℓ a := by
      have hy := hyes a ha
      simp only [ErrorModel.oneSidedRP] at hy
      have heq : R.card = acceptCount (fun q => !V q) a (ℓ a) := by
        simp only [R, acceptCount, Bool.not_eq_true']
      rwa [heq]
    have hcardR : (acceptCount (fun q => !V_any q) a (m * ℓ a) : ℝ) ≤ (R.card : ℝ) ^ m := by
      exact_mod_cast hcard_le
    simp only [ErrorModel.oneSidedRP]
    calc (acceptCount (fun q => !V_any q) a (m * ℓ a) : ℝ)
        ≤ (R.card : ℝ) ^ m := hcardR
      _ ≤ (ε₁ * (2 : ℝ) ^ ℓ a) ^ m := pow_le_pow_left₀ (Nat.cast_nonneg _) hR_bound m
      _ = ε₁ ^ m * (2 : ℝ) ^ (m * ℓ a) := by rw [mul_pow, ← pow_mul, Nat.mul_comm]
      _ ≤ ε₂ * (2 : ℝ) ^ (m * ℓ a) := mul_le_mul_of_nonneg_right hm.le (by positivity)
  · have hn := hno a ha
    simp only [ErrorModel.oneSidedRP, zero_mul] at hn
    have h0 : acceptCount V a (ℓ a) = 0 := Nat.eq_zero_of_le_zero (by exact_mod_cast hn)
    have h0_any : acceptCount V_any a (m * ℓ a) = 0 := by
      rw [acceptCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x _
      dsimp only [V_any]
      rw [collectVotesConst_ofFn]
      simp only [List.any_eq_true, List.mem_ofFn, id_eq]
      rintro ⟨_, ⟨i, rfl⟩, htrue⟩
      have hpos : 0 < acceptCount V a (ℓ a) :=
        acceptCount_pos_iff.mpr ⟨List.ofFn (BitString.block x i), List.length_ofFn, htrue⟩
      omega
    simp [h0_any, ErrorModel.oneSidedRP]

/-- **One-sided `RP` threshold invariance.** Any two error bounds `ε₁, ε₂ ∈ (0, 1)` yield the exact
same `SolvesWithErrorInTimeO` predicate (for `0 ≤ T a`). -/
theorem solvesWithErrorInTimeO_oneSidedRP_iff {Q : PromiseProblem α} {T : α → ℝ}
    (hT : ∀ a, 0 ≤ T a) {ε₁ ε₂ : ℝ} (h0₁ : 0 < ε₁) (h1₁ : ε₁ < 1)
    (h0₂ : 0 < ε₂) (h1₂ : ε₂ < 1) :
    SolvesWithErrorInTimeO Q enc (ErrorModel.oneSidedRP ε₁ h0₁.le h1₁) T ↔
      SolvesWithErrorInTimeO Q enc (ErrorModel.oneSidedRP ε₂ h0₂.le h1₂) T :=
  ⟨fun h => h.amplify_oneSidedRP hT h0₂ h1₂, fun h => h.amplify_oneSidedRP hT h0₁ h1₁⟩

/-- **One-sided `coRP` threshold invariance.** -/
theorem solvesWithErrorInTimeO_oneSidedCoRP_iff {Q : PromiseProblem α} {T : α → ℝ}
    (hT : ∀ a, 0 ≤ T a) {ε₁ ε₂ : ℝ} (h0₁ : 0 < ε₁) (h1₁ : ε₁ < 1)
    (h0₂ : 0 < ε₂) (h1₂ : ε₂ < 1) :
    SolvesWithErrorInTimeO Q enc (ErrorModel.oneSidedCoRP ε₁ h0₁.le h1₁) T ↔
      SolvesWithErrorInTimeO Q enc (ErrorModel.oneSidedCoRP ε₂ h0₂.le h1₂) T := by
  constructor <;> intro h
  · have hc1 : SolvesWithErrorInTimeO Qᶜ enc (ErrorModel.oneSidedRP ε₁ h0₁.le h1₁) T := by
      simpa only [ErrorModel.symm_oneSidedCoRP] using h.compl
    simpa only [compl_compl, ErrorModel.symm_oneSidedRP] using
      (hc1.amplify_oneSidedRP hT h0₂ h1₂).compl
  · have hc2 : SolvesWithErrorInTimeO Qᶜ enc (ErrorModel.oneSidedRP ε₂ h0₂.le h1₂) T := by
      simpa only [ErrorModel.symm_oneSidedCoRP] using h.compl
    simpa only [compl_compl, ErrorModel.symm_oneSidedRP] using
      (hc2.amplify_oneSidedRP hT h0₁ h1₁).compl

/-- Any one-sided `RP` solver (`ε₁ ∈ [0, 1)`) amplifies to any two-sided threshold
`ε₂ ∈ (0, 1 / 2)` at the exact same `O(T a)` runtime. -/
theorem SolvesWithErrorInTimeO.oneSidedRP_to_twoSided {Q : PromiseProblem α} {T : α → ℝ}
    (hT : ∀ a, 0 ≤ T a) {ε₁ ε₂ : ℝ} {h0₁ : 0 ≤ ε₁} {h1₁ : ε₁ < 1}
    (h0₂ : 0 < ε₂) (h1₂ : ε₂ < 1 / 2)
    (h : SolvesWithErrorInTimeO Q enc (ErrorModel.oneSidedRP ε₁ h0₁ h1₁) T) :
    SolvesWithErrorInTimeO Q enc (ErrorModel.twoSided ε₂ h0₂.le h1₂) T :=
  (h.amplify_oneSidedRP hT h0₂ (by linarith)).mono_error
    (ErrorModel.oneSidedRP_le_twoSided le_rfl)

/-- Exponential-rate invariance for any two-sided thresholds `ε₁, ε₂ ∈ (0, 1 / 2)`. -/
theorem solvesWithErrorInExpTime_twoSided_iff {Q : PromiseProblem α} {μ : α → ℕ} {δ : ℝ}
    {ε₁ ε₂ : ℝ} (h0₁ : 0 < ε₁) (h1₁ : ε₁ < 1 / 2) (h0₂ : 0 < ε₂) (h1₂ : ε₂ < 1 / 2) :
    SolvesWithErrorInExpTime Q enc (ErrorModel.twoSided ε₁ h0₁.le h1₁) μ δ ↔
      SolvesWithErrorInExpTime Q enc (ErrorModel.twoSided ε₂ h0₂.le h1₂) μ δ :=
  exists_congr fun _ => solvesWithErrorInTimeO_twoSided_iff (fun _ => by positivity)
    h0₁ h1₁ h0₂ h1₂

/-- Exponential-rate invariance for any one-sided `RP` thresholds `ε₁, ε₂ ∈ (0, 1)`. -/
theorem solvesWithErrorInExpTime_oneSidedRP_iff {Q : PromiseProblem α} {μ : α → ℕ} {δ : ℝ}
    {ε₁ ε₂ : ℝ} (h0₁ : 0 < ε₁) (h1₁ : ε₁ < 1) (h0₂ : 0 < ε₂) (h1₂ : ε₂ < 1) :
    SolvesWithErrorInExpTime Q enc (ErrorModel.oneSidedRP ε₁ h0₁.le h1₁) μ δ ↔
      SolvesWithErrorInExpTime Q enc (ErrorModel.oneSidedRP ε₂ h0₂.le h1₂) μ δ :=
  exists_congr fun _ => solvesWithErrorInTimeO_oneSidedRP_iff (fun _ => by positivity)
    h0₁ h1₁ h0₂ h1₂

end RandomizedPromise

/-! ### Randomized `k`-SAT exponents, `rETH`, and `rSETH` -/

/-- Width transfer for randomized `k`-SAT solvers: a solver for `KSAT k'` with `k ≤ k'` yields a
solver for `KSAT k` at the same rate `δ ≥ 0` and error profile `E`. -/
theorem SolvesWithErrorInExpTime.KSAT_of_le {k k' : ℕ} (hk : k ≤ k') {E : ErrorModel} {δ : ℝ}
    (hδ : 0 ≤ δ)
    (h : SolvesWithErrorInExpTime (ofSet (KSAT k')) encCNF E CNF.numVars δ) :
    SolvesWithErrorInExpTime (ofSet (KSAT k)) encCNF E CNF.numVars δ := by
  let r (φ : CNF ℕ) : CNF ℕ := if φ.all (fun c => decide (c.length ≤ k)) then φ else [[]]
  have hr_poly : ComputableInPolyTime r encCNF encCNF :=
    (computableInPolyTime_all_length_le k).ite .id' (.const [[]])
  have hmem (φ : CNF ℕ) : φ ∈ KSAT k ↔ r φ ∈ KSAT k' := by
    simp only [r, KSAT, Set.mem_ofPred_eq]
    split_ifs with hw
    · simp only [List.all_eq_true, decide_eq_true_eq] at hw
      exact ⟨fun ⟨_, hsat⟩ => ⟨fun c hc => (hw c hc).trans hk, hsat⟩,
        fun ⟨_, hsat⟩ => ⟨hw, hsat⟩⟩
    · simp only [List.all_eq_true, decide_eq_true_eq] at hw
      refine ⟨fun ⟨hw', _⟩ => absurd hw' hw, fun ⟨_, ⟨σ, hσ⟩⟩ => ?_⟩
      have := (CNF.eval_eq_true_iff _ _).mp hσ [] (List.mem_singleton.mpr rfl)
      simp at this
  have hμ (φ : CNF ℕ) : (r φ).numVars ≤ 1 * φ.numVars + 1 := by
    dsimp only [r]
    split_ifs
    · omega
    · have h0 : CNF.numVars ([[]] : CNF ℕ) = 0 := by decide
      rw [h0]
      omega
  simpa only [Nat.cast_one, one_mul] using
    h.of_promiseReduction (X := ofSet (KSAT k)) hr_poly
      (fun φ hφ => (hmem φ).mp hφ)
      (fun φ hφ hmem' => hφ ((hmem φ).mpr hmem')) hμ hδ

/-- The bounded-error randomized `k`-SAT exponent `s^r_k`: the infimum (`Cslib.rateExponent`) of
`δ ≥ 0` for which `KSAT k` is solved with bounded two-sided error within time
`2 ^ (δ * n) · poly(L)`. -/
@[expose] noncomputable def rSatExponent (k : ℕ) : ℝ :=
  rateExponent (SolvesWithErrorInExpTime (ofSet (KSAT k)) encCNF ErrorModel.bounded CNF.numVars)

/-- The one-sided (`RP`) randomized `k`-SAT exponent `s^{RP}_k`: the infimum (`Cslib.rateExponent`)
of `δ ≥ 0` for which `KSAT k` is solved with `RP` error (`yesErr = 1 / 2`, `noErr = 0`) within time
`2 ^ (δ * n) · poly(L)`. -/
@[expose] noncomputable def rpSatExponent (k : ℕ) : ℝ :=
  rateExponent (SolvesWithErrorInExpTime (ofSet (KSAT k)) encCNF ErrorModel.rp CNF.numVars)

/-- **`rETH` (the randomized exponential time hypothesis):** for some `δ > 0`, `3`-SAT cannot be
solved with bounded two-sided error within time `2 ^ (δ * n) · poly(L)`. -/
@[expose] def rETH : Prop :=
  ∃ δ : ℝ, 0 < δ ∧
    ¬SolvesWithErrorInExpTime (ofSet ThreeSAT) encCNF ErrorModel.bounded CNF.numVars δ

/-- **`rSETH` (the randomized strong exponential time hypothesis):** for every `ε > 0` there is a
width `k` such that `k`-SAT cannot be solved with bounded two-sided error within time
`2 ^ ((1 - ε) * n) · poly(L)`. -/
@[expose] def rSETH : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ k : ℕ,
    ¬SolvesWithErrorInExpTime (ofSet (KSAT k)) encCNF ErrorModel.bounded CNF.numVars (1 - ε)

/-- `rSatExponent k` is independent of the choice of two-sided error threshold `ε ∈ (0, 1 / 2)`. -/
theorem rSatExponent_eq_rateExponent_twoSided (k : ℕ) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) :
    rSatExponent k = rateExponent (SolvesWithErrorInExpTime (ofSet (KSAT k)) encCNF
      (ErrorModel.twoSided ε h0.le h1) CNF.numVars) :=
  congrArg rateExponent <| funext fun _ =>
    propext (solvesWithErrorInExpTime_twoSided_iff (by norm_num) (by norm_num) h0 h1)

/-- `rpSatExponent k` is independent of the choice of one-sided `RP` threshold `ε ∈ (0, 1)`. -/
theorem rpSatExponent_eq_rateExponent_oneSidedRP (k : ℕ) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    rpSatExponent k = rateExponent (SolvesWithErrorInExpTime (ofSet (KSAT k)) encCNF
      (ErrorModel.oneSidedRP ε h0.le h1) CNF.numVars) :=
  congrArg rateExponent <| funext fun _ =>
    propext (solvesWithErrorInExpTime_oneSidedRP_iff (by norm_num) (by norm_num) h0 h1)

/-- **Exhaustive search** solves `KSAT k` in randomized time `2 ^ n * poly(L)` under any error
profile. -/
theorem KSAT_solvesWithErrorInExpTime_one (k : ℕ) (E : ErrorModel) :
    SolvesWithErrorInExpTime (ofSet (KSAT k)) encCNF E CNF.numVars 1 :=
  (solvesPromiseInExpTime_ofSet_iff.mpr (KSAT_decidableInExpTime_one k)).solvesWithErrorInExpTime
    zero_le_one E

/-- `rSatExponent k` is nonnegative. -/
theorem rSatExponent_nonneg (k : ℕ) : 0 ≤ rSatExponent k :=
  rateExponent_nonneg _

/-- `rpSatExponent k` is nonnegative. -/
theorem rpSatExponent_nonneg (k : ℕ) : 0 ≤ rpSatExponent k :=
  rateExponent_nonneg _

/-- `rSatExponent k ≤ 1` for every `k`. -/
theorem rSatExponent_le_one (k : ℕ) : rSatExponent k ≤ 1 :=
  rateExponent_le_one (KSAT_solvesWithErrorInExpTime_one k ErrorModel.bounded)

/-- `rpSatExponent k ≤ 1` for every `k`. -/
theorem rpSatExponent_le_one (k : ℕ) : rpSatExponent k ≤ 1 :=
  rateExponent_le_one (KSAT_solvesWithErrorInExpTime_one k ErrorModel.rp)

/-- `rSatExponent k` is bounded by every attainable bounded-error rate `δ ≥ 0`. -/
theorem rSatExponent_le {k : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (h : SolvesWithErrorInExpTime (ofSet (KSAT k)) encCNF ErrorModel.bounded CNF.numVars δ) :
    rSatExponent k ≤ δ :=
  rateExponent_le hδ h

/-- `rpSatExponent k` is bounded by every attainable `RP` rate `δ ≥ 0`. -/
theorem rpSatExponent_le {k : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (h : SolvesWithErrorInExpTime (ofSet (KSAT k)) encCNF ErrorModel.rp CNF.numVars δ) :
    rpSatExponent k ≤ δ :=
  rateExponent_le hδ h

/-- Below `rSatExponent k` there is no bounded-error `k`-SAT solver. -/
theorem not_solvesWithErrorInExpTime_of_lt_rSatExponent {k : ℕ} {δ : ℝ} (hδ₀ : 0 ≤ δ)
    (hδ : δ < rSatExponent k) :
    ¬SolvesWithErrorInExpTime (ofSet (KSAT k)) encCNF ErrorModel.bounded CNF.numVars δ :=
  not_of_lt_rateExponent hδ₀ hδ

/-- An unattainable bounded-error rate bounds `rSatExponent k` from below. -/
theorem le_rSatExponent_of_not_solvesWithErrorInExpTime {k : ℕ} {δ : ℝ}
    (h : ¬SolvesWithErrorInExpTime (ofSet (KSAT k)) encCNF ErrorModel.bounded CNF.numVars δ) :
    δ ≤ rSatExponent k :=
  le_rateExponent (fun _ _ hle h => h.mono hle)
    (KSAT_solvesWithErrorInExpTime_one k ErrorModel.bounded) h

/-- `rSatExponent` is monotone in the clause width `k`. -/
theorem rSatExponent_mono : Monotone rSatExponent := fun _ k' hk =>
  rateExponent_le_rateExponent (KSAT_solvesWithErrorInExpTime_one k' ErrorModel.bounded)
    fun _ hδ h => h.KSAT_of_le hk hδ

/-- `rpSatExponent` is monotone in the clause width `k`. -/
theorem rpSatExponent_mono : Monotone rpSatExponent := fun _ k' hk =>
  rateExponent_le_rateExponent (KSAT_solvesWithErrorInExpTime_one k' ErrorModel.rp)
    fun _ hδ h => h.KSAT_of_le hk hδ

/-- **Two-sided vs. one-sided `RP` exponent:** `rSatExponent k ≤ rpSatExponent k`. -/
theorem rSatExponent_le_rpSatExponent (k : ℕ) : rSatExponent k ≤ rpSatExponent k :=
  rateExponent_le_rateExponent (KSAT_solvesWithErrorInExpTime_one k ErrorModel.rp)
    fun _ _ ⟨e, h⟩ => ⟨e, h.oneSidedRP_to_twoSided (fun _ => by positivity)
      (by norm_num) (by norm_num)⟩

/-- **One-sided `RP` vs. deterministic exponent:** `rpSatExponent k ≤ satExponent k`. -/
theorem rpSatExponent_le_satExponent (k : ℕ) : rpSatExponent k ≤ satExponent k :=
  rateExponent_le_rateExponent (KSAT_decidableInExpTime_one k) fun _ hδ hdec =>
    (solvesPromiseInExpTime_ofSet_iff.mpr hdec).solvesWithErrorInExpTime hδ ErrorModel.rp

/-- **Two-sided vs. deterministic exponent:** `rSatExponent k ≤ satExponent k`. -/
theorem rSatExponent_le_satExponent (k : ℕ) : rSatExponent k ≤ satExponent k :=
  (rSatExponent_le_rpSatExponent k).trans (rpSatExponent_le_satExponent k)

/-- `rETH` holds iff `3`-SAT has no bounded-error subexponential solver in `numVars`. -/
theorem rETH_iff_not_solvesWithErrorInSubexpTime :
    rETH ↔
      ¬SolvesWithErrorInSubexpTime (ofSet ThreeSAT) encCNF ErrorModel.bounded CNF.numVars := by
  simp only [rETH, SolvesWithErrorInSubexpTime, not_forall, exists_prop]

/-- **`rETH` in terms of `rSatExponent`:** `rETH ↔ 0 < rSatExponent 3`. -/
theorem rETH_iff_rSatExponent_pos : rETH ↔ 0 < rSatExponent 3 :=
  (rateExponent_pos_iff (fun _ _ hle h => h.mono hle)
    (KSAT_solvesWithErrorInExpTime_one 3 ErrorModel.bounded)).symm

/-- **`rSETH` in terms of `rSatExponent`:** `rSETH ↔ rSatExponent k → 1`. -/
theorem rSETH_iff_tendsto : rSETH ↔ Tendsto rSatExponent atTop (𝓝 1) :=
  (tendsto_rateExponent_iff (P := fun k =>
      SolvesWithErrorInExpTime (ofSet (KSAT k)) encCNF ErrorModel.bounded CNF.numVars)
    (fun _ _ _ hle h => h.mono hle) (fun k => KSAT_solvesWithErrorInExpTime_one k _)
    rSatExponent_mono).symm

/-- Dropping any finite prefix `k < K` leaves `⨆ k, rSatExponent k` unchanged. -/
theorem iSup_ge_rSatExponent_eq_iSup (K : ℕ) :
    (⨆ k : {k : ℕ // K ≤ k}, rSatExponent k.val) = ⨆ k : ℕ, rSatExponent k :=
  iSup_ge_eq_iSup_of_monotone rSatExponent_mono rSatExponent_le_one K

/-- `rSETH` holds iff `⨆ k : ℕ, rSatExponent k = 1`. -/
theorem rSETH_iff_iSup_eq_one : rSETH ↔ (⨆ k : ℕ, rSatExponent k) = 1 :=
  rSETH_iff_tendsto.trans
    (tendsto_atTop_nhds_one_iff_iSup_eq_one rSatExponent_mono rSatExponent_le_one)

/-- `rSETH` holds iff `⨆ k ≥ 3, rSatExponent k = 1`. -/
theorem rSETH_iff_iSup_ge_three_eq_one :
    rSETH ↔ (⨆ k : {k : ℕ // 3 ≤ k}, rSatExponent k.val) = 1 := by
  rw [iSup_ge_rSatExponent_eq_iSup 3, rSETH_iff_iSup_eq_one]

/-- Randomized `ETH` implies deterministic `ETH` (`rETH → ETH`). -/
theorem rETH.eth (h : rETH) : ETH := by
  rw [rETH_iff_rSatExponent_pos] at h
  rw [ETH_iff_satExponent_pos]
  exact h.trans_le (rSatExponent_le_satExponent 3)

/-- Randomized `SETH` implies deterministic `SETH` (`rSETH → SETH`). -/
theorem rSETH.seth (h : rSETH) : SETH :=
  SETH_iff_tendsto.2 <| tendsto_of_tendsto_of_tendsto_of_le_of_le (rSETH_iff_tendsto.1 h)
    tendsto_const_nhds rSatExponent_le_satExponent satExponent_le_one

end Cslib.Complexity
