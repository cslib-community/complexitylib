/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.DDGTree
public import CslibFrontier.Probability.PMF.Coin

/-!
# Coin-reading trees on biased coins, and von Neumann's fair bit

A `Cslib.Probability.DDGTree` is a possibly infinite absorbing prefix labelling: it reads coin
flips one at a time and commits to an outcome when it reaches a leaf. `DDGTree.run` reads fair
bits. This file runs the same trees on independent flips of a coin with an arbitrary law
`c : PMF Bool`. `runWith c n T` is the outcome after `n` flips, or `none` if more are needed. The
output law `outputProbWith` is its monotone limit, and `expectedCostWith c w T = ∑ₙ w n P(T > n)`
is the expected total cost when reading flip number `n + 1` (index `n`) costs `w n`. With unit
weights it is the expected number of flips, `expectedFlipsWith`. For the fair coin all of these
agree with the fair-bit API (`run_eq_runWith`, `outputProb_eq_outputProbWith`,
`expectedFlips_eq_expectedFlipsWith`).

Such trees are the exact model of a sampler that loops until it stops. A program in
`Cslib.OracleComp` is a finite tree of calls, so it can express only a truncation of such a loop
(`Cslib.OracleComp.retry`), whose failure outcome is visible.

Von Neumann's extractor reads flips in pairs, outputs the first flip of the first unequal pair and
discards equal pairs. On independent flips of a coin of bias `0 < ρ < 1` it outputs an exactly
fair bit, with exactly `1 / (ρ (1 - ρ))` expected flips ([Arora and Barak, Lemma 7.15]).
The hypothesis `0 < ρ < 1` is necessary: a coin of bias `0` or `1` is deterministic, so a tree
reading it yields every outcome with probability `0` or `1`, and no tree outputs a fair bit
(`exists_generatesWith_coin_iff`).

## Main definitions

* `Cslib.Probability.DDGTree.runWith`, `.outputProbWith`, `.GeneratesWith`: running a tree on
  independent flips of a coin with law `c`, and its output law.
* `Cslib.Probability.DDGTree.expectedCostWith`, `.expectedFlipsWith`: expected weighted and plain
  number of flips.
* `Cslib.Probability.DDGTree.vonNeumann`: von Neumann's repeat-until-different tree.

## Main results

* `Cslib.Probability.DDGTree.run_eq_runWith`: the fair-bit run is the run on the fair coin.
* `Cslib.Probability.DDGTree.runWith_pure`: on a deterministic coin the tree is deterministic.
* `Cslib.Probability.DDGTree.vonNeumann_generatesWith_coin`: von Neumann's tree outputs a fair
  bit from a coin of bias `0 < ρ < 1`.
* `Cslib.Probability.DDGTree.expectedFlipsWith_coin_vonNeumann`: it reads exactly
  `1 / (ρ (1 - ρ))` flips in expectation.
* `Cslib.Probability.DDGTree.exists_generatesWith_coin_iff`: some tree outputs a fair bit from a
  coin of bias `ρ` exactly when `0 < ρ < 1`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Lemma 7.15
  (2007 draft numbering).
-/

public section

open scoped ENNReal unitInterval
open Filter Topology

namespace Cslib.Probability

namespace DDGTree

variable {α : Type*}

/-! ## Running on a biased coin -/

/-- The result of running `T` on `n` independent flips of a coin with law `c`: `some a` if it has
reached a leaf labelled `a`, and `none` if it needs more than `n` flips. -/
@[expose] noncomputable def runWith (c : PMF Bool) : ℕ → DDGTree α → PMF (Option α)
  | 0, T => PMF.pure (T.output [])
  | n + 1, T => c.bind fun b => runWith c n (T.child b)

/-- Probability that `T`, run on flips of a coin with law `c`, eventually outputs `a`. -/
@[expose] noncomputable def outputProbWith (c : PMF Bool) (T : DDGTree α) (a : α) : ℝ≥0∞ :=
  ⨆ n, T.runWith c n (some a)

/-- `T` generates `p` from flips of a coin with law `c`. -/
@[expose] def GeneratesWith (c : PMF Bool) (T : DDGTree α) (p : PMF α) : Prop :=
  ∀ a, T.outputProbWith c a = p a

/-- Expected total cost `∑ₙ w n P(T > n)` when reading flip number `n + 1` costs `w n`: that flip
is read exactly when the tree has not stopped after `n` flips. -/
@[expose] noncomputable def expectedCostWith (c : PMF Bool) (w : ℕ → ℝ≥0∞) (T : DDGTree α) :
    ℝ≥0∞ :=
  ∑' n, w n * T.runWith c n none

/-- Expected number `∑ₙ P(T > n)` of flips of a coin with law `c` read before a leaf. -/
@[expose] noncomputable def expectedFlipsWith (c : PMF Bool) (T : DDGTree α) : ℝ≥0∞ :=
  ∑' n, T.runWith c n none

variable (c : PMF Bool)

@[simp] theorem runWith_zero (T : DDGTree α) : T.runWith c 0 = PMF.pure (T.output []) := rfl

theorem runWith_succ (T : DDGTree α) (n : ℕ) :
    T.runWith c (n + 1) = c.bind fun b => (T.child b).runWith c n := rfl

theorem expectedFlipsWith_eq_expectedCostWith (T : DDGTree α) :
    T.expectedFlipsWith c = T.expectedCostWith c 1 := by
  simp [expectedFlipsWith, expectedCostWith]

/-- Fair bits are flips of the fair coin. -/
theorem run_eq_runWith (T : DDGTree α) (n : ℕ) :
    T.run n = T.runWith (PMF.uniformOfFintype Bool) n := by
  induction n generalizing T with
  | zero => simp
  | succ n ih => simp only [run_succ, runWith_succ, ih]

theorem outputProb_eq_outputProbWith (T : DDGTree α) (a : α) :
    T.outputProb a = T.outputProbWith (PMF.uniformOfFintype Bool) a := by
  simp [outputProb, outputProbWith, run_eq_runWith]

theorem generates_iff_generatesWith (T : DDGTree α) (p : PMF α) :
    T.Generates p ↔ T.GeneratesWith (PMF.uniformOfFintype Bool) p := by
  simp [Generates, GeneratesWith, outputProb_eq_outputProbWith]

theorem expectedFlips_eq_expectedFlipsWith (T : DDGTree α) :
    T.expectedFlips = T.expectedFlipsWith (PMF.uniformOfFintype Bool) := by
  simp [expectedFlips, expectedFlipsWith, run_eq_runWith]

/-- A tree whose root is a leaf labelled `a` outputs `a` without reading any flip. -/
theorem runWith_eq_pure_of_output_nil {T : DDGTree α} {a : α} (h : T.output [] = some a)
    (n : ℕ) : T.runWith c n = PMF.pure (some a) := by
  induction n generalizing T with
  | zero => simp [h]
  | succ n ih =>
    rw [runWith_succ]
    simp_rw [ih (show (T.child _).output [] = some a from
      (child_output T _ []).trans (output_eq_of_output_nil h _))]
    exact PMF.bind_const _ _

/-- Probabilities of a fixed outcome increase with the number of flips. -/
theorem runWith_le_runWith_succ (T : DDGTree α) (n : ℕ) (a : α) :
    T.runWith c n (some a) ≤ T.runWith c (n + 1) (some a) := by
  induction n generalizing T with
  | zero =>
    by_cases h : T.output [] = some a
    · rw [runWith_eq_pure_of_output_nil c h, runWith_eq_pure_of_output_nil c h]
    · simp [PMF.pure_apply, Ne.symm h]
  | succ n ih =>
    rw [runWith_succ, runWith_succ c T (n + 1), PMF.bind_apply, PMF.bind_apply]
    exact tsum_le_tsum fun b => by gcongr; exact ih _

theorem monotone_runWith (T : DDGTree α) (a : α) : Monotone fun n => T.runWith c n (some a) :=
  monotone_nat_of_le_succ fun n => T.runWith_le_runWith_succ c n a

theorem tendsto_runWith_outputProbWith (T : DDGTree α) (a : α) :
    Tendsto (fun n => T.runWith c n (some a)) atTop (𝓝 (T.outputProbWith c a)) :=
  tendsto_atTop_iSup (T.monotone_runWith c a)

/-- A finite expected number of flips forces the tree to halt almost surely. -/
theorem tendsto_runWith_none_of_expectedFlipsWith_ne_top {T : DDGTree α}
    (h : T.expectedFlipsWith c ≠ ⊤) : Tendsto (fun n => T.runWith c n none) atTop (𝓝 0) :=
  ENNReal.tendsto_atTop_zero_of_tsum_ne_top h

/-! ## Deterministic coins -/

/-- On a deterministic coin always showing `b`, the tree follows the single path `b b b ⋯`. -/
theorem runWith_pure (b : Bool) (T : DDGTree α) (n : ℕ) :
    T.runWith (PMF.pure b) n = PMF.pure (T.output (List.replicate n b)) := by
  induction n generalizing T with
  | zero => simp
  | succ n ih => simp [runWith_succ, ih, List.replicate_succ]

/-- On a deterministic coin every outcome has probability `0` or `1`. -/
theorem outputProbWith_pure_eq_zero_or_one (b : Bool) (T : DDGTree α) (a : α) :
    T.outputProbWith (PMF.pure b) a = 0 ∨ T.outputProbWith (PMF.pure b) a = 1 := by
  classical
  simp only [outputProbWith, runWith_pure, PMF.pure_apply]
  by_cases h : ∃ n, some a = T.output (List.replicate n b)
  · obtain ⟨n, hn⟩ := h
    refine Or.inr (le_antisymm (iSup_le fun _ => by split_ifs <;> simp) ?_)
    exact le_iSup_of_le n (by simp [hn])
  · simp only [not_exists] at h
    exact Or.inl (by simp [h])

/-- A deterministic coin cannot produce a fair bit. -/
theorem not_generatesWith_pure_uniform (b : Bool) (T : DDGTree Bool) :
    ¬ T.GeneratesWith (PMF.pure b) (PMF.uniformOfFintype Bool) := by
  intro h
  have hhalf : T.outputProbWith (PMF.pure b) true = 2⁻¹ := by
    simp [h true, PMF.uniformOfFintype_apply]
  rcases outputProbWith_pure_eq_zero_or_one b T true with h0 | h1
  · rw [h0] at hhalf
    exact (ENNReal.inv_ne_zero.mpr ENNReal.ofNat_ne_top) hhalf.symm
  · rw [h1] at hhalf
    exact ENNReal.one_lt_two.ne' (by simpa using congrArg (·⁻¹) hhalf)

end DDGTree

namespace PMF

open DDGTree

theorem coin_eq_pure_false {ρ : I} (h : (ρ : ℝ) = 0) : coin ρ = _root_.PMF.pure false := by
  ext b
  cases b <;> simp [coin_apply, h]

theorem coin_eq_pure_true {ρ : I} (h : (ρ : ℝ) = 1) : coin ρ = _root_.PMF.pure true := by
  ext b
  cases b <;> simp [coin_apply, h]

end PMF

namespace DDGTree

/-! ## Von Neumann's extractor -/

/-- Von Neumann's labelling: read flips in pairs, skip equal pairs, and output the first flip of the
first unequal pair. -/
@[expose] def vonNeumannOutput : List Bool → Option Bool
  | a :: b :: w => if a = b then vonNeumannOutput w else some a
  | _ => none

theorem vonNeumannOutput_append_singleton :
    ∀ (w : List Bool) (a x : Bool), vonNeumannOutput w = some a →
      vonNeumannOutput (w ++ [x]) = some a
  | [], _, _, h => by simp [vonNeumannOutput] at h
  | [_], _, _, h => by simp [vonNeumannOutput] at h
  | a :: b :: w, r, x, h => by
    by_cases hab : a = b
    · simp only [vonNeumannOutput, hab, ↓reduceIte, List.cons_append] at h ⊢
      exact vonNeumannOutput_append_singleton w r x h
    · simpa [vonNeumannOutput, hab] using h

/-- Von Neumann's repeat-until-different extractor. -/
@[expose] def vonNeumann : DDGTree Bool where
  output := vonNeumannOutput
  output_append_singleton := vonNeumannOutput_append_singleton

variable (c : PMF Bool)

theorem runWith_one_vonNeumann : vonNeumann.runWith c 1 = PMF.pure none := by
  have h : ∀ b, (vonNeumann.child b).output [] = none := fun _ => rfl
  rw [runWith_succ]
  simp only [runWith_zero, h]
  exact PMF.bind_const _ _

/-- Two more flips: an unequal pair stops with its first flip, an equal pair restarts. -/
theorem runWith_add_two_vonNeumann (n : ℕ) :
    vonNeumann.runWith c (n + 2) = c.bind fun a => c.bind fun b =>
      if a = b then vonNeumann.runWith c n else PMF.pure (some a) := by
  rw [runWith_succ]
  congr 1
  funext a
  rw [runWith_succ]
  congr 1
  funext b
  split_ifs with hab
  · congr 1
    refine DDGTree.ext (funext fun w => ?_)
    change vonNeumannOutput (a :: b :: w) = vonNeumannOutput w
    simp [vonNeumannOutput, hab]
  · have h : ((vonNeumann.child a).child b).output [] = some a := by
      change vonNeumannOutput [a, b] = some a
      simp [vonNeumannOutput, hab]
    exact runWith_eq_pure_of_output_nil c h n

theorem runWith_add_two_vonNeumann_none (n : ℕ) :
    vonNeumann.runWith c (n + 2) none =
      (c true * c true + c false * c false) * vonNeumann.runWith c n none := by
  rw [runWith_add_two_vonNeumann]
  simp only [PMF.bind_apply, tsum_bool]
  simp [PMF.pure_apply]
  ring

theorem runWith_add_two_vonNeumann_some (n : ℕ) (x : Bool) :
    vonNeumann.runWith c (n + 2) (some x) = c true * c false +
      (c true * c true + c false * c false) * vonNeumann.runWith c n (some x) := by
  rw [runWith_add_two_vonNeumann]
  cases x <;> simp only [PMF.bind_apply, tsum_bool] <;> simp [PMF.pure_apply] <;> ring

/-- Both outcomes are equally likely after any number of flips. -/
theorem runWith_vonNeumann_true_eq_false :
    ∀ n, vonNeumann.runWith c n (some true) = vonNeumann.runWith c n (some false)
  | 0 => by simp [vonNeumann, vonNeumannOutput]
  | 1 => by simp [runWith_one_vonNeumann]
  | n + 2 => by
    rw [runWith_add_two_vonNeumann_some, runWith_add_two_vonNeumann_some,
      runWith_vonNeumann_true_eq_false n]

/-- The loop is still running after `n` flips exactly when the first `⌊n / 2⌋` pairs are equal. -/
theorem runWith_vonNeumann_none :
    ∀ n, vonNeumann.runWith c n none = (c true * c true + c false * c false) ^ (n / 2)
  | 0 => by simp [vonNeumann, vonNeumannOutput]
  | 1 => by simp [runWith_one_vonNeumann]
  | n + 2 => by
    rw [runWith_add_two_vonNeumann_none, runWith_vonNeumann_none n,
      show (n + 2) / 2 = n / 2 + 1 by omega, pow_succ, mul_comm]

/-- The expected number of flips of the von Neumann loop is twice the expected number of pairs. -/
theorem expectedFlipsWith_vonNeumann :
    vonNeumann.expectedFlipsWith c = 2 * (1 - (c true * c true + c false * c false))⁻¹ := by
  rw [expectedFlipsWith, ← tsum_even_add_odd CompleteLattice.summable CompleteLattice.summable]
  simp only [runWith_vonNeumann_none, show ∀ k, 2 * k / 2 = k by omega,
    show ∀ k, (2 * k + 1) / 2 = k by omega, ENNReal.tsum_geometric]
  ring

variable {ρ : I}

private theorem coin_sq_add_sq (ρ : I) :
    PMF.coin ρ true * PMF.coin ρ true + PMF.coin ρ false * PMF.coin ρ false =
      ENNReal.ofReal (ρ ^ 2 + (1 - ρ) ^ 2) := by
  have h0 : (0 : ℝ) ≤ ρ := ρ.2.1
  have h1 : (0 : ℝ) ≤ 1 - ρ := sub_nonneg.mpr ρ.2.2
  rw [PMF.coin_apply, PMF.coin_apply, ite_eq_left rfl, ite_eq_right Bool.false_ne_true,
    ← ENNReal.ofReal_mul h0, ← ENNReal.ofReal_mul h1,
    ← ENNReal.ofReal_add (mul_nonneg h0 h0) (mul_nonneg h1 h1), sq, sq]

/-- **Von Neumann extraction, cost** ([Arora and Barak, Lemma 7.15]): on a coin of bias
`0 < ρ < 1` the loop reads exactly `1 / (ρ (1 - ρ))` flips in expectation. -/
theorem expectedFlipsWith_coin_vonNeumann (hρ0 : 0 < (ρ : ℝ)) (hρ1 : (ρ : ℝ) < 1) :
    vonNeumann.expectedFlipsWith (PMF.coin ρ) = ENNReal.ofReal (ρ * (1 - ρ))⁻¹ := by
  have hpos : 0 < (ρ : ℝ) * (1 - ρ) := mul_pos hρ0 (sub_pos.mpr hρ1)
  rw [expectedFlipsWith_vonNeumann, coin_sq_add_sq,
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by positivity),
    show (1 : ℝ) - (ρ ^ 2 + (1 - ρ) ^ 2) = 2 * (ρ * (1 - ρ)) by ring,
    ← ENNReal.ofReal_inv_of_pos (by positivity), mul_inv, ENNReal.ofReal_mul (by positivity),
    ← mul_assoc, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul zero_le_two,
    mul_inv_cancel₀ two_ne_zero, ENNReal.ofReal_one, one_mul]

theorem expectedFlipsWith_coin_vonNeumann_ne_top (hρ0 : 0 < (ρ : ℝ)) (hρ1 : (ρ : ℝ) < 1) :
    vonNeumann.expectedFlipsWith (PMF.coin ρ) ≠ ⊤ := by
  rw [expectedFlipsWith_coin_vonNeumann hρ0 hρ1]
  exact ENNReal.ofReal_ne_top

/-- **Von Neumann extraction** ([Arora and Barak, Lemma 7.15]): from independent flips of a coin
of bias `0 < ρ < 1` the repeat-until-different loop outputs an exactly fair bit. -/
theorem vonNeumann_generatesWith_coin (hρ0 : 0 < (ρ : ℝ)) (hρ1 : (ρ : ℝ) < 1) :
    vonNeumann.GeneratesWith (PMF.coin ρ) (PMF.uniformOfFintype Bool) := by
  set c := PMF.coin ρ
  set L := vonNeumann.outputProbWith c true
  have hL : ∀ x, vonNeumann.outputProbWith c x = L := by
    intro x
    cases x
    · simp only [L, outputProbWith, runWith_vonNeumann_true_eq_false]
    · rfl
  have hsum : ∀ n, vonNeumann.runWith c n (some true) + vonNeumann.runWith c n (some true) +
      vonNeumann.runWith c n none = 1 := by
    intro n
    have h := (vonNeumann.runWith c n).tsum_coe
    rw [tsum_fintype (L := SummationFilter.unconditional _), Fintype.sum_option,
      Fintype.sum_bool] at h
    rw [← h, runWith_vonNeumann_true_eq_false c n]
    ring
  have hlim : Tendsto (fun n => vonNeumann.runWith c n (some true) +
      vonNeumann.runWith c n (some true) + vonNeumann.runWith c n none) atTop (𝓝 (L + L + 0)) :=
    ((tendsto_runWith_outputProbWith c _ true).add
      (tendsto_runWith_outputProbWith c _ true)).add
      (tendsto_runWith_none_of_expectedFlipsWith_ne_top c
        (expectedFlipsWith_coin_vonNeumann_ne_top hρ0 hρ1))
  simp only [hsum, add_zero] at hlim
  have h2L : L * 2 = 1 := by
    rw [mul_two]
    exact (tendsto_nhds_unique tendsto_const_nhds hlim).symm
  intro x
  rw [hL x, PMF.uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat]
  exact ENNReal.eq_inv_of_mul_eq_one_left h2L

/-- The hypothesis `0 < ρ < 1` of von Neumann extraction is necessary and sufficient: some
coin-reading tree outputs an exactly fair bit from independent flips of a coin of bias `ρ` exactly
when `0 < ρ < 1`. -/
theorem exists_generatesWith_coin_iff :
    (∃ T : DDGTree Bool, T.GeneratesWith (PMF.coin ρ) (PMF.uniformOfFintype Bool)) ↔
      0 < (ρ : ℝ) ∧ (ρ : ℝ) < 1 := by
  refine ⟨fun ⟨T, hT⟩ => ?_, fun h => ⟨vonNeumann, vonNeumann_generatesWith_coin h.1 h.2⟩⟩
  by_contra hρ
  rcases not_and_or.mp hρ with h0 | h1
  · rw [PMF.coin_eq_pure_false (le_antisymm (not_lt.mp h0) ρ.2.1)] at hT
    exact not_generatesWith_pure_uniform false T hT
  · rw [PMF.coin_eq_pure_true (le_antisymm ρ.2.2 (not_lt.mp h1))] at hT
    exact not_generatesWith_pure_uniform true T hT

end DDGTree

end Cslib.Probability
