/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.FineGrained
public import CslibFrontier.Computability.Complexity.FineGrained.Schoening
public import CslibFrontier.Computability.Complexity.Problems.ThreeSAT
public import CslibFrontier.Computability.Complexity.Classes.Time
public import CslibFrontier.Computability.Probabilistic.ExponentialIterate
public import CslibFrontier.Algorithms.WordRAM.Schoening.TrialCount
public import CslibFrontier.Foundations.Analysis.SpecialFunctions.ExpBounds
public import CslibFrontier.Languages.Probabilistic.UniformNat
import CslibFrontier.Logics.Propositional.CNF.ModelCount.DenseRelabel
import CslibFrontier.Computability.Probabilistic.Adaptive
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Probabilistic.UniformNat
import CslibFrontier.Languages.Probabilistic.UniformNat.Support
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.EventBind
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Schöning's `k`-SAT algorithm on fair-coin multitape Turing machines

`Cslib.Complexity.Schoening` proves the `((k - 1) / k) ^ (k - 3) (k / (2 (k - 1))) ^ n / (3 n + 1)`
single-trial success bound for Schöning's local search under exact uniform clause-literal sampling,
and `Cslib.Algorithms.WordRAM.Schoening` realizes the amplified algorithm on the randomized word
RAM [Schoening1999].

A strict fair-coin multitape Turing machine (`Turing.MultiTapePTM`) draws only fair bits rather than
exact uniform residues modulo non-power-of-two clause lengths `m ≤ k`. Reducing `w` fair bits modulo
`m` (`Cslib.ProbComp.sampleModNat w m`) hits every residue `i < m` at least `2 ^ w / m` times, so
each transition dominates `(1 - k / 2 ^ w)` times the ideal uniform transition. Choosing
`w = 2 n + k + 3` (`O(n)` fair bits per step, `O(n ^ 2)` per trial) keeps the `3 n`-step
multiplicative loss `(1 - k / 2 ^ w) ^ (3 n) ≥ 1 / 2`, preserving the `((2 (k - 1)) / k) ^ n`
exponential base without rejection loops.

Running `2 * schoeningTrials k φ.numVars c` independent restarts via the binary-counter compiler
`Cslib.Probability.IsPPTOn.exists_multiTapePTM_repeatAnyBool_binary` gives one finite-control
fair-coin `MultiTapePTM` on `encCNF` that:

* halts on every branch within `O(((2 (k - 1)) / k) ^ n * (L + 1) ^ E)` steps
  (`n = φ.numVars`, `L = (encCNF φ).length`),
* uses polynomial workspace `O((L + 1) ^ E)` (`machine.toNTM.RunsInSpace`),
* has zero false positives (`PMF.pure [false]` whenever `φ ∉ KSAT k`),
* accepts every `φ ∈ KSAT k` with probability at least `1 - exp (-c)` (and at least `2 / 3` at
  `c = 2`, yielding `DecidesWithBoundedErrorInTime encCNF (KSAT k) T`).

## Main definitions

* `Cslib.Complexity.Schoening.fairFlipStep`, `Cslib.Complexity.Schoening.fairWalk`,
  `Cslib.Complexity.Schoening.fairTrial`: fair-coin Schöning walk and trial via `sampleModNat`.
* `Cslib.Complexity.Schoening.schoeningTrialProg`: strict PPT single-trial program on `CNF ℕ`.

## Main results

* `Cslib.Complexity.Schoening.half_mul_succeedProb_trial_le_fairTrial`: `w = 2 |V| + k + 3` fair
  bits per step preserve at least half of the ideal single-trial success probability.
* `Cslib.Complexity.Schoening.isPPTOn_schoeningTrialProg`: the single-trial program on `encCNF` is
  strict PPT.
* `Cslib.Complexity.Schoening.computableInPolyTime_two_mul_schoeningTrials`: the binary trial count
  `2 * schoeningTrials k φ.numVars c` is computable in polynomial time into `encNat`.
* `Cslib.Complexity.Schoening.exists_multiTapePTM_KSAT`: sub-`2 ^ n` worst-case halting time,
  polynomial workspace, zero false positives, and `1 - exp (-c)` soundness on `KSAT k` (`k ≥ 3`).
* `Cslib.Complexity.Schoening.exists_decidesWithBoundedErrorInTime_KSAT`,
  `Cslib.Complexity.Schoening.exists_decidesWithBoundedErrorInTime_ThreeSAT`: bounded-error
  multitape `k`-SAT and `3`-SAT deciders (`((2 (k - 1)) / k) ^ n` and `(4 / 3) ^ n`).

## References

* [U. Schöning, *A probabilistic algorithm for k-SAT and constraint satisfaction
  problems*][Schoening1999]
-/

public section

namespace Cslib.Complexity.Schoening

open scoped ENNReal
open Cslib.BitString Cslib.Logic.PL Cslib.Probability Cslib.Algorithms.WordRAM.Schoening
open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapePTM

/-! ### Fair-coin domination of the ideal Schöning walk -/

section FairWalk

variable {V : Type*} [DecidableEq V]

/-- Flip the variable at index `r ← sampleModNat w c.length` of `c` (leaving `σ` unchanged if `c`
is empty). -/
noncomputable def fairFlipStep (w : ℕ) (c : Clause V) (σ : V → Bool) : PMF (V → Bool) :=
  if h : c.length = 0 then PMF.pure σ else
    (ProbComp.eval (ProbComp.sampleModNat w c.length)).map fun r =>
      flipOn {(c.get ⟨r % c.length, Nat.mod_lt r (Nat.pos_of_ne_zero h)⟩).1} σ

/-- `t` steps of the fair-coin Schöning walk with bit width `w` per step. -/
noncomputable def fairWalk (w : ℕ) (φ : CNF V) : ℕ → (V → Bool) → PMF (V → Bool)
  | 0, σ => PMF.pure σ
  | t + 1, σ =>
    match firstUnsat φ σ with
    | none => PMF.pure σ
    | some c => (fairFlipStep w c σ).bind (fairWalk w φ t)

/-- One trial of the fair-coin Schöning walk: uniform initial assignment followed by `3 |V|` steps
of `fairWalk w`. -/
noncomputable def fairTrial [Fintype V] (w : ℕ) (φ : CNF V) : PMF (V → Bool) :=
  (PMF.uniformOfFintype (V → Bool)).bind (fairWalk w φ (3 * Fintype.card V))

/-- Pointwise lower bound on `sampleModNat w m`: every residue `i < m` has probability at least
`(1 - m / 2 ^ w) / m`. -/
theorem le_eval_sampleModNat_toReal {w m i : ℕ} (hi : i < m) :
    (1 - (m : ℝ) / (2 : ℝ) ^ w) * (m : ℝ)⁻¹ ≤
      (ProbComp.eval (ProbComp.sampleModNat w m) i).toReal := by
  have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) hi
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h2w : (0 : ℝ) < (2 : ℝ) ^ w := by positivity
  let Q := 2 ^ w / m
  let emb : Fin Q ↪ Fin (2 ^ w) :=
    ⟨fun q => ⟨q.val * m + i, by
      have hqm : (q.val + 1) * m ≤ Q * m := Nat.mul_le_mul_right m q.isLt
      have hdiv : Q * m ≤ 2 ^ w := Nat.div_mul_le_self (2 ^ w) m
      linarith⟩, by
      intro a b hab
      simp only [Fin.mk.injEq] at hab
      exact Fin.ext (Nat.mul_right_cancel hm (by omega))⟩
  have hmod (q : Fin Q) : (emb q).val % m = i := by
    change (q.val * m + i) % m = i
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
  have hcard : Q ≤ (Finset.univ.filter (fun x : Fin (2 ^ w) => x.val % m = i)).card := by
    calc Q = (Finset.univ.map emb).card := by simp only [Finset.card_map, Finset.card_fin]
      _ ≤ (Finset.univ.filter (fun x : Fin (2 ^ w) => x.val % m = i)).card := by
        apply Finset.card_le_card
        intro x hx
        obtain ⟨q, -, rfl⟩ := Finset.mem_map.mp hx
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmod q⟩
  have hpmf : (ProbComp.eval (ProbComp.sampleModNat w m) i).toReal =
      ((Finset.univ.filter (fun x : Fin (2 ^ w) => x.val % m = i)).card : ℝ) / (2 : ℝ) ^ w := by
    rw [ProbComp.eval_sampleModNat, PMF.map_apply, tsum_fintype]
    simp only [PMF.uniformOfFintype_apply, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
    have hfin : ∀ x : Fin (2 ^ w),
        (if i = x.val % m then (((2 : ℝ≥0∞) ^ w)⁻¹ : ℝ≥0∞) else 0) ≠ ⊤ := by
      intro x
      split_ifs
      · exact ENNReal.inv_ne_top.mpr (pow_ne_zero w two_ne_zero)
      · exact ENNReal.zero_ne_top
    rw [ENNReal.toReal_sum (fun x _ => hfin x)]
    calc ∑ x : Fin (2 ^ w), (if i = x.val % m then (((2 : ℝ≥0∞) ^ w)⁻¹ : ℝ≥0∞) else 0).toReal
        = ∑ x : Fin (2 ^ w), if x.val % m = i then ((2 : ℝ) ^ w)⁻¹ else 0 := by
          refine Finset.sum_congr rfl fun x _ => ?_
          by_cases hx : x.val % m = i
          · simp only [hx, ↓reduceIte, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
          · have hx' : i ≠ x.val % m := Ne.symm hx
            simp only [hx, hx', ↓reduceIte, ENNReal.toReal_zero]
      _ = ((Finset.univ.filter (fun x : Fin (2 ^ w) => x.val % m = i)).card : ℝ) *
            ((2 : ℝ) ^ w)⁻¹ := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      _ = ((Finset.univ.filter (fun x : Fin (2 ^ w) => x.val % m = i)).card : ℝ) / (2 : ℝ) ^ w :=
          div_eq_mul_inv _ _
  rw [hpmf]
  have hQ_ineq : (2 : ℝ) ^ w - m ≤ (Q : ℝ) * m := by
    have hrem : 2 ^ w < (Q + 1) * m := by
      dsimp only [Q]
      have h1 := Nat.div_add_mod (2 ^ w) m
      have h2 := Nat.mod_lt (2 ^ w) hm
      nlinarith
    have hremR : (2 : ℝ) ^ w ≤ ((Q : ℝ) + 1) * m := by exact_mod_cast hrem.le
    linarith
  have hQ_le : (Q : ℝ) ≤ (Finset.univ.filter (fun x : Fin (2 ^ w) => x.val % m = i)).card := by
    exact_mod_cast hcard
  calc (1 - (m : ℝ) / (2 : ℝ) ^ w) * (m : ℝ)⁻¹
      = ((2 : ℝ) ^ w - m) / ((m : ℝ) * (2 : ℝ) ^ w) := by field_simp
    _ ≤ ((Q : ℝ) * m) / ((m : ℝ) * (2 : ℝ) ^ w) := by gcongr
    _ = (Q : ℝ) / (2 : ℝ) ^ w := by field_simp
    _ ≤ ((Finset.univ.filter (fun x : Fin (2 ^ w) => x.val % m = i)).card : ℝ) / (2 : ℝ) ^ w := by
        gcongr

/-- Pointwise domination of one transition when `c.length ≤ k`. -/
theorem le_fairFlipStep_toReal {w k : ℕ} {c : Clause V} (hclen : c.length ≤ k)
    (σ τ : V → Bool) :
    (1 - (k : ℝ) / (2 : ℝ) ^ w) * (flipStep c σ τ).toReal ≤ (fairFlipStep w c σ τ).toReal := by
  classical
  have h2w : (0 : ℝ) < (2 : ℝ) ^ w := by positivity
  have hα_le : 1 - (k : ℝ) / (2 : ℝ) ^ w ≤ 1 := by
    have : (0 : ℝ) ≤ (k : ℝ) / (2 : ℝ) ^ w := by positivity
    linarith
  by_cases hc0 : c.length = 0
  · simp only [flipStep, fairFlipStep, hc0, ↓reduceDIte]
    exact mul_le_of_le_one_left ENNReal.toReal_nonneg hα_le
  · have hm : 0 < c.length := Nat.pos_of_ne_zero hc0
    have : NeZero c.length := ⟨hc0⟩
    have hm_le_k : (c.length : ℝ) ≤ k := by exact_mod_cast hclen
    have hα_m : 1 - (k : ℝ) / (2 : ℝ) ^ w ≤ 1 - (c.length : ℝ) / (2 : ℝ) ^ w := by
      have : (c.length : ℝ) / (2 : ℝ) ^ w ≤ (k : ℝ) / (2 : ℝ) ^ w := by gcongr
      linarith
    simp only [flipStep, fairFlipStep, hc0, ↓reduceDIte]
    have hunif : ((PMF.uniformOfFintype (Fin c.length)).map
        (fun i => flipOn {(c.get i).1} σ) τ).toReal =
        ∑ i : Fin c.length,
          if τ = flipOn {(c.get i).1} σ then (c.length : ℝ)⁻¹ else 0 := by
      rw [PMF.map_apply, tsum_fintype]
      simp only [PMF.uniformOfFintype_apply, Fintype.card_fin]
      rw [ENNReal.toReal_sum (fun i _ => by
        split_ifs
        · exact ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr hc0)
        · exact ENNReal.zero_ne_top)]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_zero]
    rw [hunif, Finset.mul_sum]
    have hfair :
        ∑ i : Fin c.length,
          (if τ = flipOn {(c.get i).1} σ then
            (ProbComp.eval (ProbComp.sampleModNat w c.length) i.val).toReal else 0) ≤
        ((ProbComp.eval (ProbComp.sampleModNat w c.length)).map
          (fun r => flipOn {(c.get ⟨r % c.length, Nat.mod_lt r hm⟩).1} σ) τ).toReal := by
      let f (r : ℕ) : ℝ≥0∞ :=
        if τ = flipOn {(c.get ⟨r % c.length, Nat.mod_lt r hm⟩).1} σ then
          ProbComp.eval (ProbComp.sampleModNat w c.length) r else 0
      have hmap_eq : ((ProbComp.eval (ProbComp.sampleModNat w c.length)).map
          (fun r => flipOn {(c.get ⟨r % c.length, Nat.mod_lt r hm⟩).1} σ) τ) = ∑' r : ℕ, f r := by
        rw [PMF.map_apply]
      have hsum_le : (∑ i : Fin c.length,
          if τ = flipOn {(c.get i).1} σ then
            ProbComp.eval (ProbComp.sampleModNat w c.length) i.val else 0) ≤
          ∑' r : ℕ, f r := by
        calc ∑ i : Fin c.length,
              (if τ = flipOn {(c.get i).1} σ then
                ProbComp.eval (ProbComp.sampleModNat w c.length) i.val else 0)
            = ∑ r ∈ Finset.range c.length, f r := by
              rw [← Fin.sum_univ_eq_sum_range]
              refine Finset.sum_congr rfl fun i _ => ?_
              dsimp only [f]
              have hmod : (⟨i.val % c.length, Nat.mod_lt i.val hm⟩ : Fin c.length) = i := by
                ext; exact Nat.mod_eq_of_lt i.isLt
              rw [hmod]
          _ ≤ ∑' r : ℕ, f r := sum_le_tsum (Finset.range c.length)
      have htsum_ne_top : (∑' r : ℕ, f r) ≠ ⊤ := by
        rw [← hmap_eq]
        exact PMF.apply_ne_top _ _
      rw [hmap_eq]
      have htoReal := (ENNReal.toReal_le_toReal
        (ENNReal.sum_ne_top.mpr fun i _ => by
          split_ifs
          · exact PMF.apply_ne_top _ _
          · exact ENNReal.zero_ne_top)
        htsum_ne_top).mpr hsum_le
      refine le_trans ?_ htoReal
      rw [ENNReal.toReal_sum (fun i _ => by
        split_ifs
        · exact PMF.apply_ne_top _ _
        · exact ENNReal.zero_ne_top)]
      refine le_of_eq (Finset.sum_congr rfl fun i _ => ?_)
      split_ifs <;> simp only [ENNReal.toReal_zero]
    refine le_trans ?_ hfair
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hτ : τ = flipOn {(c.get i).1} σ
    · simp only [hτ, ↓reduceIte]
      have hstep := le_eval_sampleModNat_toReal (w := w) i.isLt
      have hcpos : (0 : ℝ) ≤ (c.length : ℝ)⁻¹ := by positivity
      exact (mul_le_mul_of_nonneg_right hα_m hcpos).trans hstep
    · simp only [hτ, ↓reduceIte, mul_zero, le_refl]

/-- Pointwise domination across `t` steps of the walk. -/
theorem le_fairWalk_toReal [Finite V] {w k : ℕ} {φ : CNF V} (hlen : ∀ c ∈ φ, c.length ≤ k)
    (hkw : (k : ℝ) ≤ (2 : ℝ) ^ w) (t : ℕ) (σ τ : V → Bool) :
    (1 - (k : ℝ) / (2 : ℝ) ^ w) ^ t * (walk φ t σ τ).toReal ≤ (fairWalk w φ t σ τ).toReal := by
  cases nonempty_fintype V
  have h2w : (0 : ℝ) < (2 : ℝ) ^ w := by positivity
  have hα0 : 0 ≤ 1 - (k : ℝ) / (2 : ℝ) ^ w := by
    rw [sub_nonneg, div_le_one h2w]
    exact hkw
  have hα1 : 1 - (k : ℝ) / (2 : ℝ) ^ w ≤ 1 := by
    have : (0 : ℝ) ≤ (k : ℝ) / (2 : ℝ) ^ w := by positivity
    linarith
  induction t generalizing σ with
  | zero =>
    simp only [pow_zero, one_mul, walk, fairWalk, le_refl]
  | succ t ih =>
    simp only [walk, fairWalk]
    cases hfind : firstUnsat φ σ with
    | none =>
      exact mul_le_of_le_one_left ENNReal.toReal_nonneg (pow_le_one₀ hα0 hα1)
    | some c =>
      have hc_mem : c ∈ φ := List.mem_of_find?_eq_some hfind
      have hbind_walk : ((flipStep c σ).bind (walk φ t) τ).toReal =
          ∑ σ', (flipStep c σ σ').toReal * (walk φ t σ' τ).toReal := by
        have h := PMF.toOuterMeasure_bind_toReal (flipStep c σ) (walk φ t) {τ}
        simpa only [PMF.toOuterMeasure_apply_singleton] using h
      have hbind_fair : ((fairFlipStep w c σ).bind (fairWalk w φ t) τ).toReal =
          ∑ σ', (fairFlipStep w c σ σ').toReal * (fairWalk w φ t σ' τ).toReal := by
        have h := PMF.toOuterMeasure_bind_toReal (fairFlipStep w c σ) (fairWalk w φ t) {τ}
        simpa only [PMF.toOuterMeasure_apply_singleton] using h
      rw [hbind_walk, hbind_fair, pow_succ, Finset.mul_sum]
      refine Finset.sum_le_sum fun σ' _ => ?_
      have h1 := le_fairFlipStep_toReal (w := w) (hlen c hc_mem) σ σ'
      have h2 := ih σ'
      calc ((1 - (k : ℝ) / (2 : ℝ) ^ w) ^ t * (1 - (k : ℝ) / (2 : ℝ) ^ w)) *
            ((flipStep c σ σ').toReal * (walk φ t σ' τ).toReal)
          = ((1 - (k : ℝ) / (2 : ℝ) ^ w) * (flipStep c σ σ').toReal) *
              ((1 - (k : ℝ) / (2 : ℝ) ^ w) ^ t * (walk φ t σ' τ).toReal) := by ring
        _ ≤ (fairFlipStep w c σ σ').toReal * (fairWalk w φ t σ' τ).toReal :=
            mul_le_mul h1 h2 (mul_nonneg (pow_nonneg hα0 t) ENNReal.toReal_nonneg)
              ENNReal.toReal_nonneg

private theorem half_le_bernoulli_factor (n k : ℕ) :
    (1 / 2 : ℝ) ≤ (1 - (k : ℝ) / (2 : ℝ) ^ (2 * n + k + 3)) ^ (3 * n) := by
  let w := 2 * n + k + 3
  let δ : ℝ := (k : ℝ) / (2 : ℝ) ^ w
  have h2w : (0 : ℝ) < (2 : ℝ) ^ w := by positivity
  have hk_lt : k < 2 ^ w :=
    calc k < 2 ^ k := Nat.lt_two_pow_self
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) (by dsimp only [w]; omega)
  have hδ0 : 0 ≤ δ := by positivity
  have hδ1 : δ ≤ 1 := by
    dsimp only [δ]
    rw [div_le_one h2w]
    exact_mod_cast hk_lt.le
  have hprod_lt : (3 * n) * k < 2 ^ (2 * n + k + 2) := by
    have h3n : 3 * n < 2 ^ (2 * n + 2) := by
      have hn2 : n < 2 ^ n := Nat.lt_two_pow_self
      have hpow : 4 * 2 ^ n ≤ 2 ^ (2 * n + 2) := by
        calc 4 * 2 ^ n = 2 ^ (n + 2) := by ring
          _ ≤ 2 ^ (2 * n + 2) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have hk2 : k < 2 ^ k := Nat.lt_two_pow_self
    calc (3 * n) * k ≤ 2 ^ (2 * n + 2) * k := Nat.mul_le_mul_right k h3n.le
      _ < 2 ^ (2 * n + 2) * 2 ^ k := by
        rcases Nat.eq_zero_or_pos (2 ^ (2 * n + 2)) with h0 | hpos
        · exact absurd h0 (pow_ne_zero _ (by decide))
        · exact Nat.mul_lt_mul_of_pos_left hk2 hpos
      _ = 2 ^ (2 * n + k + 2) := by rw [← Nat.pow_add]; ring_nf
  have hprod_half : (3 * n : ℝ) * δ ≤ 1 / 2 := by
    dsimp only [δ, w]
    have hR : ((3 * n : ℝ) * k) ≤ (2 : ℝ) ^ (2 * n + k + 2) := by exact_mod_cast hprod_lt.le
    have hsplit : (2 : ℝ) ^ (2 * n + k + 3) = 2 * (2 : ℝ) ^ (2 * n + k + 2) := by
      rw [pow_succ']
    rw [hsplit]
    have hp : (0 : ℝ) < (2 : ℝ) ^ (2 * n + k + 2) := by positivity
    calc (3 * n : ℝ) * ((k : ℝ) / (2 * (2 : ℝ) ^ (2 * n + k + 2)))
        = ((3 * n : ℝ) * k) / (2 * (2 : ℝ) ^ (2 * n + k + 2)) := by ring
      _ ≤ (2 : ℝ) ^ (2 * n + k + 2) / (2 * (2 : ℝ) ^ (2 * n + k + 2)) := by gcongr
      _ = 1 / 2 := by field_simp
  have hbern := one_add_mul_le_pow (a := -δ) (by linarith) (3 * n)
  push_cast at hbern
  change _ ≤ (1 - δ) ^ (3 * n)
  calc (1 / 2 : ℝ) = 1 - 1 / 2 := by ring
    _ ≤ 1 - (3 * n : ℝ) * δ := by linarith
    _ = 1 + (3 * n : ℝ) * -δ := by ring
    _ ≤ (1 + -δ) ^ (3 * n) := hbern
    _ = (1 - δ) ^ (3 * n) := by ring

/-- **Fair-coin Schöning trial domination.** Using `w = 2 |V| + k + 3` fair bits per step preserves
at least half of the ideal single-trial success probability. -/
theorem half_mul_succeedProb_trial_le_fairTrial [Fintype V] {k : ℕ} {φ : CNF V}
    (hlen : ∀ c ∈ φ, c.length ≤ k) :
    (1 / 2 : ℝ) * succeedProb φ (trial φ) ≤
      succeedProb φ (fairTrial (2 * Fintype.card V + k + 3) φ) := by
  set n := Fintype.card V
  set w := 2 * n + k + 3
  have hkw : (k : ℝ) ≤ (2 : ℝ) ^ w := by
    have hk : k < 2 ^ k := Nat.lt_two_pow_self
    have hle : 2 ^ k ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) (by dsimp only [w]; omega)
    exact_mod_cast (hk.trans_le hle).le
  have hwalk_succ (σ : V → Bool) :
      (1 - (k : ℝ) / (2 : ℝ) ^ w) ^ (3 * n) * succeedProb φ (walk φ (3 * n) σ) ≤
        succeedProb φ (fairWalk w φ (3 * n) σ) := by
    rw [succeedProb, succeedProb,
      Cslib.Probability.PMF.toOuterMeasure_apply_toReal,
      Cslib.Probability.PMF.toOuterMeasure_apply_toReal,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun τ _ => ?_
    by_cases hτ : τ ∈ {τ : V → Bool | φ.eval τ = true}
    · simp only [hτ, ↓reduceIte]
      exact le_fairWalk_toReal hlen hkw (3 * n) σ τ
    · simp only [hτ, ↓reduceIte, mul_zero, le_refl]
  have htrial_dom :
      (1 - (k : ℝ) / (2 : ℝ) ^ w) ^ (3 * n) * succeedProb φ (trial φ) ≤
        succeedProb φ (fairTrial w φ) := by
    rw [trial, fairTrial, succeedProb, succeedProb,
      Cslib.Probability.PMF.toOuterMeasure_bind_toReal,
      Cslib.Probability.PMF.toOuterMeasure_bind_toReal, Finset.mul_sum]
    refine Finset.sum_le_sum fun σ _ => ?_
    have h := hwalk_succ σ
    have hu : 0 ≤ (PMF.uniformOfFintype (V → Bool) σ).toReal := ENNReal.toReal_nonneg
    calc (1 - (k : ℝ) / (2 : ℝ) ^ w) ^ (3 * n) *
          ((PMF.uniformOfFintype (V → Bool) σ).toReal *
            ((walk φ (3 * n) σ).toOuterMeasure {σ | φ.eval σ = true}).toReal)
        = (PMF.uniformOfFintype (V → Bool) σ).toReal *
            ((1 - (k : ℝ) / (2 : ℝ) ^ w) ^ (3 * n) * succeedProb φ (walk φ (3 * n) σ)) := by
          rw [succeedProb]; ring
      _ ≤ (PMF.uniformOfFintype (V → Bool) σ).toReal *
            ((fairWalk w φ (3 * n) σ).toOuterMeasure {σ | φ.eval σ = true}).toReal := by
          rw [← succeedProb]; exact mul_le_mul_of_nonneg_left h hu
  have hprob0 : 0 ≤ succeedProb φ (trial φ) := by
    rw [succeedProb]; exact ENNReal.toReal_nonneg
  exact (mul_le_mul_of_nonneg_right (half_le_bernoulli_factor n k) hprob0).trans htrial_dom

end FairWalk

/-! ### Strict PPT single-trial realization on `CNF ℕ` (`encCNF`) -/

section TrialProgram

/-- Boolean guard checking that every clause of `φ` is nonempty and has length at most `k`. -/
def guardKSAT (k : ℕ) (φ : CNF ℕ) : Bool :=
  φ.all fun c => !c.isEmpty && decide (c.length ≤ k)

/-- Read an assignment `ℕ → Bool` from a bit list by index (`false` out of bounds). -/
def bitsAssign (bits : List Bool) (v : ℕ) : Bool :=
  bits.getD v false

/-- Flip bit `v` of `bits`, preserving `bits.length`. -/
def flipBitAt (bits : List Bool) (v : ℕ) : List Bool :=
  (List.range bits.length).map fun i =>
    if i == v then !(bits.getD i false) else bits.getD i false

@[simp]
theorem length_flipBitAt (bits : List Bool) (v : ℕ) :
    (flipBitAt bits v).length = bits.length := by
  simp only [flipBitAt, List.length_map, List.length_range]

/-- First unsatisfied clause of `ψ` under `bitsAssign bits`, returning `[]` when none exists. -/
def firstUnsatClauseBits (ψ : CNF ℕ) (bits : List Bool) : Clause ℕ :=
  (ψ.filter fun c => !Clause.eval (bitsAssign bits) c).headD []

/-- One fair-coin walk step on a densely relabeled formula `ψ` with bit width `w`. -/
noncomputable def walkStepBits (ψ : CNF ℕ) (w : ℕ) (bits : List Bool) : ProbComp (List Bool) :=
  let c := firstUnsatClauseBits ψ bits
  if c.isEmpty then
    pure bits
  else do
    let r ← ProbComp.sampleModNat w c.length
    let idx := min c.length r
    let v := (c.getD idx (0, false)).1
    pure (flipBitAt bits v)

/-- Unchecked body of one Schöning trial on `φ : CNF ℕ`: densely relabel `φ`, sample `n = φ.numVars`
fair bits, run `3 n` steps of `walkStepBits` with width `2 n + k + 3`, and evaluate `ψ`. -/
noncomputable def schoeningBodyProg (k : ℕ) (φ : CNF ℕ) : ProbComp Bool := do
  let ψ := φ.denseRelabel
  let n := φ.numVars
  let w := 2 * n + k + 3
  let bits₀ ← BitString.sampleList n
  let bitsFinal ← OracleComp.iterate (3 * n) (walkStepBits ψ w) bits₀
  pure (CNF.eval (bitsAssign bitsFinal) ψ)

/-- **Certified single-trial Schöning program on `CNF ℕ`.** Rejects immediately with `false` if any
clause of `φ` is empty or longer than `k`; otherwise runs `schoeningBodyProg k φ`. -/
noncomputable def schoeningTrialProg (k : ℕ) (φ : CNF ℕ) : ProbComp Bool :=
  if guardKSAT k φ then schoeningBodyProg k φ else pure false

private theorem computableInPolyTime_guardKSAT (k : ℕ) :
    ComputableInPolyTime (guardKSAT k) encCNF encBool := by
  unfold guardKSAT
  fun_prop

private theorem computableInPolyTime_firstUnsatClauseBits :
    ComputableInPolyTime (fun p : CNF ℕ × List Bool => firstUnsatClauseBits p.1 p.2)
      (encPair (encCNFOver encUnary) encBits) (encClause encUnary) := by
  unfold firstUnsatClauseBits bitsAssign
  fun_prop

private theorem computableInPolyTime_flipBitAt :
    ComputableInPolyTime (fun p : List Bool × ℕ => flipBitAt p.1 p.2)
      (encPair encBits encUnary) encBits := by
  have hlist : ComputableInPolyTime
      (fun p : List Bool × ℕ =>
        (List.range p.1.length).map fun i =>
          if i == p.2 then !(p.1.getD i false) else p.1.getD i false)
      (encPair encBits encUnary) (encList encBool) := by
    fun_prop
  exact ComputableInPolyTime.listToBits.comp hlist

private theorem isPPTOn_walkStepBits :
    IsPPTOn (encPair (encPair (encCNFOver encUnary) encUnary) encBits) encBits
      (fun p : (CNF ℕ × ℕ) × List Bool => walkStepBits p.1.1 p.1.2 p.2) := by
  let InEnc := encPair (encPair (encCNFOver encUnary) encUnary) encBits
  have hc : ComputableInPolyTime
      (fun p : (CNF ℕ × ℕ) × List Bool => firstUnsatClauseBits p.1.1 p.2)
      InEnc (encClause encUnary) :=
    computableInPolyTime_firstUnsatClauseBits.comp
      (((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst _ _)).prod
        (ComputableInPolyTime.snd _ _))
  have hempty : ComputableInPolyTime
      (fun p : (CNF ℕ × ℕ) × List Bool => (firstUnsatClauseBits p.1.1 p.2).isEmpty)
      InEnc encBool := by
    fun_prop
  have hw : ComputableInPolyTime (fun p : (CNF ℕ × ℕ) × List Bool => p.1.2) InEnc encUnary :=
    (ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.fst _ _)
  have hclen_unary : ComputableInPolyTime
      (fun p : (CNF ℕ × ℕ) × List Bool => (firstUnsatClauseBits p.1.1 p.2).length)
      InEnc encUnary :=
    Clause.computableInPolyTime_length hc
  have hclen_bin : ComputableInPolyTime
      (fun p : (CNF ℕ × ℕ) × List Bool => (firstUnsatClauseBits p.1.1 p.2).length)
      InEnc encNat :=
    ComputableInPolyTime.unary_to_binary.comp hclen_unary
  have hmod : IsPPTOn InEnc encNat
      (fun p : (CNF ℕ × ℕ) × List Bool =>
        ProbComp.sampleModNat p.1.2 (firstUnsatClauseBits p.1.1 p.2).length) :=
    isPPTOn_sampleModNat hw hclen_bin
  have hpost : ComputableInPolyTime
      (fun q : ((CNF ℕ × ℕ) × List Bool) × ℕ =>
        let c := firstUnsatClauseBits q.1.1.1 q.1.2
        let idx := min c.length q.2
        let v := (c.getD idx (0, false)).1
        flipBitAt q.1.2 v)
      (encPair InEnc encNat) encBits := by
    have hc_q : ComputableInPolyTime
        (fun q : ((CNF ℕ × ℕ) × List Bool) × ℕ => firstUnsatClauseBits q.1.1.1 q.1.2)
        (encPair InEnc encNat) (encClause encUnary) :=
      hc.comp (ComputableInPolyTime.fst _ _)
    have hidx : ComputableInPolyTime
        (fun q : ((CNF ℕ × ℕ) × List Bool) × ℕ =>
          min (firstUnsatClauseBits q.1.1.1 q.1.2).length q.2)
        (encPair InEnc encNat) encUnary :=
      ComputableInPolyTime.binary_min_unary'
        (hclen_unary.comp (ComputableInPolyTime.fst _ _))
        (ComputableInPolyTime.snd _ _)
    have hv : ComputableInPolyTime
        (fun q : ((CNF ℕ × ℕ) × List Bool) × ℕ =>
          ((firstUnsatClauseBits q.1.1.1 q.1.2).getD
            (min (firstUnsatClauseBits q.1.1.1 q.1.2).length q.2) (0, false)).1)
        (encPair InEnc encNat) encUnary :=
      (ComputableInPolyTime.fst encUnary encBool).comp
        (ComputableInPolyTime.listGetDWithInput hc_q hidx (0, false))
    exact computableInPolyTime_flipBitAt.comp
      (((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.fst _ _)).prod hv)
  refine IsPPTOn.cond' hempty (ComputableInPolyTime.snd _ _).isPPTOn ?_
  simpa only [bind_pure_comp] using hmod.map_with hpost

private theorem length_eq_of_mem_support_walkStepBits {ψ : CNF ℕ} {w : ℕ} {bits next : List Bool}
    (hnext : next ∈ (ProbComp.eval (walkStepBits ψ w bits)).support) :
    next.length = bits.length := by
  dsimp only [walkStepBits] at hnext
  cases h : (firstUnsatClauseBits ψ bits).isEmpty with
  | true =>
    simp only [h, ↓reduceIte, ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hnext
    rw [hnext]
  | false =>
    simp only [h, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_bind, PMF.mem_support_bind_iff,
      ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hnext
    obtain ⟨_, _, rfl⟩ := hnext
    exact length_flipBitAt bits _

private theorem isPPTOn_iterateBitsOfStep {P : Type} (encP : P ↪ List Bool)
    {stepFn : P → List Bool → ProbComp (List Bool)}
    (hstepFn : IsPPTOn (encPair encP encBits) encBits (fun q => stepFn q.1 q.2))
    (hlen_eq : ∀ p bits next, next ∈ (ProbComp.eval (stepFn p bits)).support →
      next.length = bits.length) :
    IsPPTOn (encPair (encPair encP encUnary) encBits) encBits
      (fun x : (P × ℕ) × List Bool =>
        let hdr := x.1
        OracleComp.iterate hdr.2 (stepFn hdr.1) x.2) := by
  let In := (P × ℕ) × List Bool
  let encHdr : P × ℕ ↪ List Bool := encPair encP encUnary
  let encIn : In ↪ List Bool := encPair encHdr encBits
  let getCount (x : In) : ℕ :=
    let hdr := x.1
    hdr.2
  let getParam (x : In) : P :=
    let hdr := x.1
    hdr.1
  have hcount : ComputableInPolyTime getCount encIn encUnary :=
    (ComputableInPolyTime.snd encP encUnary).comp (ComputableInPolyTime.fst encHdr encBits)
  have hinit : ComputableInPolyTime (fun x : In => x.2) encIn encBits :=
    ComputableInPolyTime.snd encHdr encBits
  have hparam : ComputableInPolyTime (fun q : In × List Bool => (getParam q.1, q.2))
      (encPair encIn encBits) (encPair encP encBits) :=
    (((ComputableInPolyTime.fst encP encUnary).comp
      (ComputableInPolyTime.fst encHdr encBits)).comp
      (ComputableInPolyTime.fst encIn encBits)).prod
      (ComputableInPolyTime.snd encIn encBits)
  have hstep : IsPPTOn (encPair encIn encBits) encBits
      (fun q : In × List Bool => stepFn (getParam q.1) q.2) :=
    hstepFn.preprocess hparam
  refine (IsPPTOn.iterateWith_spec'
    (α := In) (State := List Bool)
    (input := encIn) (stateEncoding := encBits)
    (initial := fun x : In => x.2)
    (count := getCount)
    (step := fun (x : In) (bits : List Bool) => stepFn (getParam x) bits)
    hcount hinit hstep
    (fun x _ bits => bits.length = x.2.length)
    (fun _ => rfl)
    (fun x _ _ _ hlen _ hnext => (hlen_eq (getParam x) _ _ hnext).trans hlen)
    (size := fun x => (encIn x).length)
    PolyBounded.self
    (fun x _ bits _ hlen => by
      change bits.length ≤ (encIn x).length
      rw [hlen, length_encPair]
      exact Nat.le_add_left _ _)).1

private theorem isPPTOn_walkLoopPair (k : ℕ) :
    IsPPTOn (encPair encCNF encBits) encBits
      (fun p : CNF ℕ × List Bool =>
        OracleComp.iterate (3 * p.1.numVars)
          (walkStepBits p.1.denseRelabel (2 * p.1.numVars + k + 3)) p.2) := by
  have hgen := isPPTOn_iterateBitsOfStep (encPair (encCNFOver encUnary) encUnary)
    (stepFn := fun pw : CNF ℕ × ℕ => walkStepBits pw.1 pw.2)
    isPPTOn_walkStepBits
    (fun _ _ _ hnext => length_eq_of_mem_support_walkStepBits hnext)
  have hdense : ComputableInPolyTime (CNF.denseRelabel (V := ℕ)) encCNF (encCNFOver encUnary) :=
    CNF.computableInPolyTime_denseRelabel_unary encNat
  have hn : ComputableInPolyTime (CNF.numVars (V := ℕ)) encCNF encUnary :=
    SAT.computableInPolyTime_numVars
  have hw : ComputableInPolyTime (fun φ : CNF ℕ => 2 * φ.numVars + k + 3) encCNF encUnary :=
    ComputableInPolyTime.unary_add'
      (ComputableInPolyTime.unary_add'
        (ComputableInPolyTime.unary_mul' (.const 2) hn) (.const k))
      (.const 3)
  have h3n : ComputableInPolyTime (fun φ : CNF ℕ => 3 * φ.numVars) encCNF encUnary :=
    ComputableInPolyTime.unary_mul' (.const 3) hn
  have hφ : ComputableInPolyTime (fun p : CNF ℕ × List Bool => p.1)
      (encPair encCNF encBits) encCNF := ComputableInPolyTime.fst encCNF encBits
  have hprep : ComputableInPolyTime
      (fun p : CNF ℕ × List Bool =>
        (((p.1.denseRelabel, 2 * p.1.numVars + k + 3), 3 * p.1.numVars), p.2))
      (encPair encCNF encBits)
      (encPair (encPair (encPair (encCNFOver encUnary) encUnary) encUnary) encBits) :=
    (((hdense.comp hφ).prod (hw.comp hφ)).prod (h3n.comp hφ)).prod
      (ComputableInPolyTime.snd encCNF encBits)
  exact hgen.preprocess hprep

private theorem computableInPolyTime_evalDensePair :
    ComputableInPolyTime
      (fun q : CNF ℕ × List Bool => CNF.eval (bitsAssign q.2) q.1.denseRelabel)
      (encPair encCNF encBits) encBool := by
  have hψ : ComputableInPolyTime (fun q : CNF ℕ × List Bool => q.1.denseRelabel)
      (encPair encCNF encBits) (encCNFOver encUnary) :=
    (CNF.computableInPolyTime_denseRelabel_unary encNat).comp
      (ComputableInPolyTime.fst encCNF encBits)
  have hσ : ComputableInPolyTime
      (fun p : (CNF ℕ × List Bool) × ℕ => bitsAssign p.1.2 p.2)
      (encPair (encPair encCNF encBits) encUnary) encBool :=
    ComputableInPolyTime.bitsGetDWithInput
      ((ComputableInPolyTime.snd encCNF encBits).comp
        (ComputableInPolyTime.fst (encPair encCNF encBits) encUnary))
      (ComputableInPolyTime.snd (encPair encCNF encBits) encUnary) false
  exact CNF.computableInPolyTime_eval hψ hσ

private theorem isPPTOn_schoeningBodyProg (k : ℕ) :
    IsPPTOn encCNF encBool (schoeningBodyProg k) := by
  have hsample0 : IsPPTOn encCNF encBits (fun φ : CNF ℕ => BitString.sampleList φ.numVars) :=
    isPPTOn_sampleList.preprocess SAT.computableInPolyTime_numVars
  have hwalk : IsPPTOn encCNF encBits
      (fun φ : CNF ℕ => do
        let bits₀ ← BitString.sampleList φ.numVars
        OracleComp.iterate (3 * φ.numVars)
          (walkStepBits φ.denseRelabel (2 * φ.numVars + k + 3)) bits₀) :=
    hsample0.bind_with (isPPTOn_walkLoopPair k)
  refine (hwalk.map_with (f := fun φ bits => CNF.eval (bitsAssign bits) φ.denseRelabel)
    computableInPolyTime_evalDensePair).congr fun φ => ?_
  dsimp only [schoeningBodyProg]
  rw [ProbComp.eval_map, ProbComp.eval_bind, ProbComp.eval_bind, PMF.map_bind]
  apply Cslib.Probability.PMF.bind_congr_on_support
  intro bits₀ _
  rw [PMF.map, ProbComp.eval_bind]
  apply Cslib.Probability.PMF.bind_congr_on_support
  intro bitsF _
  rw [Function.comp_apply, ProbComp.eval_pure]

/-- **Strict PPT certificate for one Schöning trial on `CNF ℕ` (`encCNF`).** -/
theorem isPPTOn_schoeningTrialProg (k : ℕ) :
    IsPPTOn encCNF encBool (schoeningTrialProg k) :=
  IsPPTOn.cond' (computableInPolyTime_guardKSAT k) (isPPTOn_schoeningBodyProg k)
    (ComputableInPolyTime.const (encIn := encCNF) false).isPPTOn

/-! ### Connecting `schoeningTrialProg` to `fairTrial` on `CNF (Fin φ.numVars)` -/

private def toFinClause {n : ℕ} (c : Clause ℕ) (hc : ∀ l ∈ c, l.1 < n) : Clause (Fin n) :=
  c.attach.map fun ⟨l, hl⟩ => (⟨l.1, hc l hl⟩, l.2)

private def toFinCNF {n : ℕ} (ψ : CNF ℕ) (hvars : ∀ v ∈ ψ.vars, v < n) : CNF (Fin n) :=
  ψ.attach.map fun ⟨c, hc⟩ =>
    toFinClause c fun l hl => hvars l.1 (CNF.mem_vars.mpr ⟨c, hc, l.2, hl⟩)

private theorem length_toFinClause {n : ℕ} (c : Clause ℕ) (hc : ∀ l ∈ c, l.1 < n) :
    (toFinClause c hc).length = c.length := by
  simp only [toFinClause, List.length_map, List.length_attach]

private theorem getD_ofFn_eq {n : ℕ} (σ : Fin n → Bool) {v : ℕ} (hv : v < n) :
    (List.ofFn σ).getD v false = σ ⟨v, hv⟩ := by
  have hlen : v < (List.ofFn σ).length := by simpa only [List.length_ofFn] using hv
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, List.getElem_ofFn,
    Option.getD_some]

private theorem eval_toFinClause {n : ℕ} (c : Clause ℕ) (hc : ∀ l ∈ c, l.1 < n)
    (σ : Fin n → Bool) :
    Clause.eval σ (toFinClause c hc) = Clause.eval (bitsAssign (List.ofFn σ)) c := by
  apply Bool.eq_iff_iff.mpr
  simp only [Clause.eval_eq_true_iff, toFinClause, List.mem_map, List.mem_attach, true_and,
    Subtype.exists]
  constructor
  · rintro ⟨_, ⟨l, hl, rfl⟩, hev⟩
    refine ⟨l, hl, ?_⟩
    simpa only [Literal.eval, bitsAssign, getD_ofFn_eq σ (hc l hl)] using hev
  · rintro ⟨l, hl, hev⟩
    refine ⟨(⟨l.1, hc l hl⟩, l.2), ⟨l, hl, rfl⟩, ?_⟩
    simpa only [Literal.eval, bitsAssign, getD_ofFn_eq σ (hc l hl)] using hev

private theorem eval_toFinCNF {n : ℕ} (ψ : CNF ℕ) (hvars : ∀ v ∈ ψ.vars, v < n)
    (σ : Fin n → Bool) :
    CNF.eval σ (toFinCNF ψ hvars) = CNF.eval (bitsAssign (List.ofFn σ)) ψ := by
  apply Bool.eq_iff_iff.mpr
  simp only [CNF.eval_eq_true_iff, toFinCNF, List.mem_map, List.mem_attach, true_and,
    Subtype.exists]
  constructor
  · intro h c hc
    rw [← eval_toFinClause c (fun l hl => hvars l.1 (CNF.mem_vars.mpr ⟨c, hc, l.2, hl⟩)) σ]
    exact h _ ⟨c, hc, rfl⟩
  · rintro h _ ⟨c, hc, rfl⟩
    rw [eval_toFinClause]
    exact h c hc

private theorem satisfiable_toFinCNF {n : ℕ} (ψ : CNF ℕ) (hvars : ∀ v ∈ ψ.vars, v < n) :
    (toFinCNF ψ hvars).Satisfiable ↔ ψ.Satisfiable := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨bitsAssign (List.ofFn σ), by rwa [← eval_toFinCNF ψ hvars σ]⟩
  · rintro ⟨τ, hτ⟩
    refine ⟨fun i => τ i.val, ?_⟩
    rw [eval_toFinCNF]
    refine (CNF.eval_congr fun v hv => ?_).trans hτ
    simp only [bitsAssign, getD_ofFn_eq (fun i : Fin n => τ i.val) (hvars v hv)]

private theorem flipBitAt_ofFn {n : ℕ} (σ : Fin n → Bool) {v : ℕ} (hv : v < n) :
    flipBitAt (List.ofFn σ) v = List.ofFn (flipOn {⟨v, hv⟩} σ) := by
  refine List.ext_getElem (by simp only [length_flipBitAt, List.length_ofFn]) fun i h₁ h₂ => ?_
  have hi : i < n := by simpa only [List.length_ofFn] using h₂
  simp only [flipBitAt, List.length_ofFn, List.getElem_map, List.getElem_range, List.getElem_ofFn,
    getD_ofFn_eq σ hi, flipOn, Finset.mem_singleton, Fin.ext_iff]
  by_cases hiv : i = v
  · simp only [hiv, beq_self_eq_true, ↓reduceIte]
  · have hbeq : (i == v) = false := beq_false_of_ne hiv
    simp only [hbeq, Bool.false_eq_true, hiv, ↓reduceIte]

private theorem headD_filter_eq_nil_of_find?_eq_none {α : Type*} {l : List (List α)}
    {p : List α → Bool} (h : l.find? p = none) :
    (l.filter p).headD [] = [] := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    cases hpa : p a with
    | false =>
      simp only [List.find?_cons, hpa] at h
      rw [List.filter_cons_of_neg (by simp only [hpa, Bool.false_eq_true, not_false_eq_true])]
      exact ih h
    | true =>
      simp only [List.find?_cons, hpa, reduceCtorEq] at h

private theorem headD_filter_eq_of_find?_eq_some {α : Type*} {l : List (List α)}
    (hne : ∀ c ∈ l, c ≠ []) {p : List α → Bool} {c : List α} (h : l.find? p = some c) :
    (l.filter p).headD [] = c ∧ c ≠ [] := by
  induction l with
  | nil => simp only [List.find?_nil, reduceCtorEq] at h
  | cons a as ih =>
    cases hpa : p a with
    | true =>
      simp only [List.find?_cons, hpa, Option.some.injEq] at h
      subst h
      rw [List.filter_cons_of_pos hpa, List.headD_cons]
      exact ⟨rfl, hne a List.mem_cons_self⟩
    | false =>
      simp only [List.find?_cons, hpa] at h
      rw [List.filter_cons_of_neg (by simp only [hpa, Bool.false_eq_true, not_false_eq_true])]
      exact ih (fun x hx => hne x (List.mem_cons_of_mem a hx)) h

private theorem find?_attach {α : Type*} (l : List α) (p : α → Bool) :
    (l.attach.find? fun x => p x.1).map Subtype.val = l.find? p := by
  have hid : l = l.attach.map Subtype.val := (List.attach_map_subtype_val l).symm
  conv_rhs => rw [hid, List.find?_map]
  rfl

private theorem eval_walkStepBits_ofFn {n : ℕ} (ψ : CNF ℕ) (hvars : ∀ v ∈ ψ.vars, v < n)
    (hne : ∀ c ∈ ψ, c ≠ []) (w : ℕ) (σ : Fin n → Bool) :
    ProbComp.eval (walkStepBits ψ w (List.ofFn σ)) =
      (match firstUnsat (toFinCNF ψ hvars) σ with
        | none => PMF.pure σ
        | some c => fairFlipStep w c σ).map List.ofFn := by
  let p (c : Clause ℕ) : Bool := !Clause.eval (bitsAssign (List.ofFn σ)) c
  have hfind_eq : firstUnsat (toFinCNF ψ hvars) σ =
      (ψ.attach.find? (fun x => p x.1)).map
        (fun x => toFinClause x.1 fun l hl =>
          hvars l.1 (CNF.mem_vars.mpr ⟨x.1, x.2, l.2, hl⟩)) := by
    simp only [firstUnsat, toFinCNF, List.find?_map]
    congr 2 with ⟨c, hc⟩
    simp only [Function.comp_apply, eval_toFinClause, p]
  rw [hfind_eq]
  cases hfa : ψ.attach.find? (fun x => p x.1) with
  | none =>
    have hf : ψ.find? p = none := by rw [← find?_attach, hfa]; rfl
    have hfc : firstUnsatClauseBits ψ (List.ofFn σ) = [] :=
      headD_filter_eq_nil_of_find?_eq_none hf
    simp only [walkStepBits, hfc, List.isEmpty_nil, ↓reduceIte, Option.map_none,
      ProbComp.eval_pure, PMF.pure_map]
  | some x =>
    rcases x with ⟨c, hc_mem⟩
    have hf : ψ.find? p = some c := by rw [← find?_attach, hfa]; rfl
    obtain ⟨hfc, hc_ne⟩ := headD_filter_eq_of_find?_eq_some hne hf
    have hfc' : firstUnsatClauseBits ψ (List.ofFn σ) = c := hfc
    have hc_len_pos : 0 < c.length := List.length_pos_iff.mpr hc_ne
    have hc_len_ne : c.length ≠ 0 := hc_len_pos.ne'
    have hisEmpty : c.isEmpty = false := List.isEmpty_eq_false_iff.mpr hc_ne
    let hc_vars : ∀ l ∈ c, l.1 < n :=
      fun l hl => hvars l.1 (CNF.mem_vars.mpr ⟨c, hc_mem, l.2, hl⟩)
    have hfin_len : (toFinClause c hc_vars).length = c.length := length_toFinClause c hc_vars
    have hfin_ne : (toFinClause c hc_vars).length ≠ 0 := by rw [hfin_len]; exact hc_len_ne
    simp only [walkStepBits, hfc', hisEmpty, Bool.false_eq_true, ↓reduceIte, Option.map_some,
      fairFlipStep, hfin_ne, ↓reduceDIte, ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_comp]
    calc (ProbComp.eval (ProbComp.sampleModNat w c.length)).bind
          (fun r => PMF.pure (flipBitAt (List.ofFn σ) (c.getD (min c.length r) (0, false)).1))
        = (ProbComp.eval (ProbComp.sampleModNat w (toFinClause c hc_vars).length)).bind
          (fun r => PMF.pure (List.ofFn (flipOn
            {((toFinClause c hc_vars).get ⟨r % (toFinClause c hc_vars).length,
              Nat.mod_lt r (Nat.pos_of_ne_zero hfin_ne)⟩).1} σ))) := by
          simp only [hfin_len]
          apply Cslib.Probability.PMF.bind_congr_on_support
          intro r hr
          have hr_lt : r < c.length := ProbComp.lt_of_mem_support_sampleModNat hc_len_pos hr
          have hmin : min c.length r = r := Nat.min_eq_right hr_lt.le
          have hmod : r % c.length = r := Nat.mod_eq_of_lt hr_lt
          have hgetD : c.getD r (0, false) = c[r] := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr_lt, Option.getD_some]
          have hv_lt : c[r].1 < n :=
            hvars c[r].1 (CNF.mem_vars.mpr ⟨c, hc_mem, c[r].2, List.getElem_mem hr_lt⟩)
          rw [hmin, hgetD, flipBitAt_ofFn σ hv_lt]
          congr 3
          simp only [toFinClause, List.get_eq_getElem, List.getElem_map, List.getElem_attach, hmod]
      _ = (ProbComp.eval (ProbComp.sampleModNat w (toFinClause c hc_vars).length)).map _ := rfl

private theorem fairWalk_eq_pure_of_firstUnsat_none {V : Type*} [DecidableEq V]
    (w : ℕ) (φ : CNF V) (t : ℕ) {σ : V → Bool} (hnone : firstUnsat φ σ = none) :
    fairWalk w φ t σ = PMF.pure σ := by
  cases t with
  | zero => rfl
  | succ t => simp only [fairWalk, hnone]

private theorem eval_iterate_walkStepBits_ofFn {n : ℕ} (ψ : CNF ℕ) (hvars : ∀ v ∈ ψ.vars, v < n)
    (hne : ∀ c ∈ ψ, c ≠ []) (w t : ℕ) (σ : Fin n → Bool) :
    ProbComp.eval (OracleComp.iterate t (walkStepBits ψ w) (List.ofFn σ)) =
      (fairWalk w (toFinCNF ψ hvars) t σ).map List.ofFn := by
  induction t generalizing σ with
  | zero =>
    simp only [OracleComp.iterate_zero, ProbComp.eval_pure, fairWalk, PMF.pure_map]
  | succ t ih =>
    rw [OracleComp.iterate_succ_bind, ProbComp.eval_bind,
      eval_walkStepBits_ofFn ψ hvars hne w σ, PMF.bind_map]
    simp only [fairWalk]
    cases hfu : firstUnsat (toFinCNF ψ hvars) σ with
    | none =>
      simp only [PMF.pure_bind, Function.comp_apply, ih,
        fairWalk_eq_pure_of_firstUnsat_none w _ t hfu, PMF.pure_map]
    | some c =>
      rw [PMF.map_bind]
      apply Cslib.Probability.PMF.bind_congr_on_support
      intro σ' _
      exact ih σ'

private theorem eval_schoeningBodyProg_eq_map_fairTrial (k : ℕ) (φ : CNF ℕ)
    (hne : ∀ c ∈ φ.denseRelabel, c ≠ []) :
    let n := φ.numVars
    let w := 2 * n + k + 3
    let ψFin := toFinCNF φ.denseRelabel (fun _ hv => CNF.mem_vars_denseRelabel_lt φ hv)
    ProbComp.eval (schoeningBodyProg k φ) =
      (fairTrial w ψFin).map (fun σ => CNF.eval σ ψFin) := by
  intro n w ψFin
  dsimp only [schoeningBodyProg]
  rw [ProbComp.eval_bind, BitString.eval_sampleList, BitString.uniformList, PMF.bind_map]
  dsimp only [fairTrial]
  rw [Fintype.card_fin, PMF.map_bind]
  apply Cslib.Probability.PMF.bind_congr_on_support
  intro σ _
  rw [Function.comp_apply, ProbComp.eval_bind,
    eval_iterate_walkStepBits_ofFn φ.denseRelabel
      (fun _ hv => CNF.mem_vars_denseRelabel_lt φ hv) hne w (3 * n) σ,
    PMF.bind_map, PMF.map]
  apply Cslib.Probability.PMF.bind_congr_on_support
  intro τ _
  simp only [Function.comp_def, ProbComp.eval_pure]
  exact congrArg PMF.pure (eval_toFinCNF _ _ τ).symm

/-- **Zero false positives for `schoeningTrialProg`.** If `φ ∉ KSAT k`, one trial returns `true`
with probability `0`. -/
theorem eval_schoeningTrialProg_true_eq_zero_of_not_mem_KSAT {k : ℕ} {φ : CNF ℕ}
    (hnot : φ ∉ KSAT k) :
    ProbComp.eval (schoeningTrialProg k φ) true = 0 := by
  dsimp only [schoeningTrialProg]
  by_cases hg : guardKSAT k φ = true
  · simp only [hg, ↓reduceIte]
    have hlen : ∀ c ∈ φ, c.length ≤ k := by
      intro c hc
      simp only [guardKSAT, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hg
      exact (hg c hc).2
    have hunsat : ¬φ.Satisfiable := fun hsat => hnot ⟨hlen, hsat⟩
    have hunsat_dense : ¬φ.denseRelabel.Satisfiable := by
      rwa [CNF.satisfiable_denseRelabel]
    by_contra hpos
    have hmem : true ∈ (ProbComp.eval (schoeningBodyProg k φ)).support :=
      (PMF.mem_support_iff _ _).mpr hpos
    dsimp only [schoeningBodyProg] at hmem
    rw [ProbComp.eval_bind, PMF.mem_support_bind_iff] at hmem
    obtain ⟨bits₀, _, hmem⟩ := hmem
    rw [ProbComp.eval_bind, PMF.mem_support_bind_iff] at hmem
    obtain ⟨bitsF, _, hmem⟩ := hmem
    rw [ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hmem
    exact hunsat_dense ⟨bitsAssign bitsF, hmem.symm⟩
  · have hg' : guardKSAT k φ = false := Bool.eq_false_iff.mpr hg
    simp only [hg', Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure, PMF.pure_apply,
      Bool.true_eq_false]

/-- **Single-trial success lower bound on `KSAT k`.** For `k ≥ 3` and `φ ∈ KSAT k`, one execution
of `schoeningTrialProg k φ` returns `true` with probability at least half of Schöning's bound. -/
theorem succeedProb_le_schoeningTrialProg {k : ℕ} (hk : 3 ≤ k) {φ : CNF ℕ} (hφ : φ ∈ KSAT k) :
    (1 / 2 : ℝ) * ((((k : ℝ) - 1) / k) ^ (k - 3) *
        ((k : ℝ) / (2 * ((k : ℝ) - 1))) ^ φ.numVars / (3 * φ.numVars + 1)) ≤
      (ProbComp.eval (schoeningTrialProg k φ) true).toReal := by
  obtain ⟨hlen, hsat⟩ := hφ
  have hne_orig : ∀ c ∈ φ, c ≠ [] := by
    obtain ⟨σ, hσ⟩ := hsat
    intro c hc hnil
    rw [CNF.eval_eq_true_iff] at hσ
    have hce := hσ c hc
    rw [hnil, Clause.eval_nil] at hce
    exact Bool.false_ne_true hce
  have hg : guardKSAT k φ = true := by
    simp only [guardKSAT, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true',
      List.isEmpty_eq_false_iff, decide_eq_true_eq]
    exact fun c hc => ⟨hne_orig c hc, hlen c hc⟩
  have hne_dense : ∀ c ∈ φ.denseRelabel, c ≠ [] := by
    obtain ⟨σ, hσ⟩ := (CNF.satisfiable_denseRelabel φ).mpr hsat
    intro c hc hnil
    rw [CNF.eval_eq_true_iff] at hσ
    have hce := hσ c hc
    rw [hnil, Clause.eval_nil] at hce
    exact Bool.false_ne_true hce
  let n := φ.numVars
  let w := 2 * n + k + 3
  let ψFin := toFinCNF φ.denseRelabel (fun _ hv => CNF.mem_vars_denseRelabel_lt φ hv)
  have hsat_fin : ψFin.Satisfiable :=
    (satisfiable_toFinCNF φ.denseRelabel _).mpr ((CNF.satisfiable_denseRelabel φ).mpr hsat)
  have hlen_fin : ∀ c ∈ ψFin, c.length ≤ k := by
    intro c hc
    simp only [ψFin, toFinCNF, List.mem_map, List.mem_attach, true_and, Subtype.exists] at hc
    obtain ⟨c₀, hc₀, rfl⟩ := hc
    rw [length_toFinClause]
    exact ((CNF.all_length_le_denseRelabel φ).mpr hlen) c₀ hc₀
  have hbody_eq := eval_schoeningBodyProg_eq_map_fairTrial k φ hne_dense
  have htrue_eq : (ProbComp.eval (schoeningTrialProg k φ) true).toReal =
      succeedProb ψFin (fairTrial w ψFin) := by
    dsimp only [schoeningTrialProg]
    rw [hg]
    simp only [↓reduceIte]
    have hbody_eq' : ProbComp.eval (schoeningBodyProg k φ) =
        (fairTrial w ψFin).map (fun σ => CNF.eval σ ψFin) := hbody_eq
    rw [hbody_eq', succeedProb, PMF.map_apply, PMF.toOuterMeasure_apply]
    congr 2 with σ
    by_cases hσ : CNF.eval σ ψFin = true
    · simp only [hσ, ↓reduceIte, Set.mem_ofPred_eq, Set.indicator_of_mem]
    · have hσf : CNF.eval σ ψFin = false := Bool.eq_false_iff.mpr hσ
      simp only [hσf, Bool.true_eq_false, ↓reduceIte, Set.mem_ofPred_eq, Bool.false_eq_true,
        not_false_eq_true, Set.indicator_of_notMem]
  rw [htrue_eq]
  have h1 := trial_success_of_length_le hk hsat_fin hlen_fin
  simp only [Fintype.card_fin] at h1
  have h2 := half_mul_succeedProb_trial_le_fairTrial hlen_fin
  simp only [Fintype.card_fin] at h2
  exact (mul_le_mul_of_nonneg_left h1 (by positivity)).trans h2

end TrialProgram

/-! ### Polynomial-time binary trial count and multitape Schöning decider -/

section MachineDecider

/-- **Polynomial-time binary trial count.** For fixed `k ≥ 3` and confidence `c : ℕ`, computing
`2 * schoeningTrials k φ.numVars c` from `encCNF φ` into binary (`encNat`) runs in polynomial
time. -/
theorem computableInPolyTime_two_mul_schoeningTrials {k : ℕ} (hk : 3 ≤ k) (c : ℕ) :
    ComputableInPolyTime (fun φ : CNF ℕ => 2 * schoeningTrials k φ.numVars c) encCNF encNat := by
  have heq : (fun φ : CNF ℕ => 2 * schoeningTrials k φ.numVars c) =
      fun φ : CNF ℕ =>
        2 * ((((3 * φ.numVars + 1) * (2 * (k - 1)) ^ φ.numVars * k ^ (k - 3) +
            k ^ φ.numVars * (k - 1) ^ (k - 3) - 1) /
          (k ^ φ.numVars * (k - 1) ^ (k - 3))) * c) := by
    funext φ
    rw [schoeningTrials_eq hk]
  rw [heq]
  have hn_u : ComputableInPolyTime (CNF.numVars (V := ℕ)) encCNF encUnary :=
    SAT.computableInPolyTime_numVars
  have hn_b : ComputableInPolyTime (CNF.numVars (V := ℕ)) encCNF encNat :=
    ComputableInPolyTime.unary_to_binary.comp hn_u
  have h3n1 : ComputableInPolyTime (fun φ : CNF ℕ => 3 * φ.numVars + 1) encCNF encNat :=
    ComputableInPolyTime.binary_add'
      (ComputableInPolyTime.binary_mul' (.const 3) hn_b) (.const 1)
  have hpow1 : ComputableInPolyTime (fun φ : CNF ℕ => (2 * (k - 1)) ^ φ.numVars) encCNF encNat :=
    ComputableInPolyTime.binary_pow' (.const (2 * (k - 1))) hn_u
  have hpowk : ComputableInPolyTime (fun φ : CNF ℕ => k ^ φ.numVars) encCNF encNat :=
    ComputableInPolyTime.binary_pow' (.const k) hn_u
  have hterm1 : ComputableInPolyTime
      (fun φ : CNF ℕ => (3 * φ.numVars + 1) * (2 * (k - 1)) ^ φ.numVars * k ^ (k - 3))
      encCNF encNat :=
    ComputableInPolyTime.binary_mul'
      (ComputableInPolyTime.binary_mul' h3n1 hpow1) (.const (k ^ (k - 3)))
  have hden : ComputableInPolyTime
      (fun φ : CNF ℕ => k ^ φ.numVars * (k - 1) ^ (k - 3)) encCNF encNat :=
    ComputableInPolyTime.binary_mul' hpowk (.const ((k - 1) ^ (k - 3)))
  have hnum : ComputableInPolyTime
      (fun φ : CNF ℕ =>
        (3 * φ.numVars + 1) * (2 * (k - 1)) ^ φ.numVars * k ^ (k - 3) +
          k ^ φ.numVars * (k - 1) ^ (k - 3) - 1) encCNF encNat :=
    ComputableInPolyTime.binary_sub' (ComputableInPolyTime.binary_add' hterm1 hden) (.const 1)
  have hquot : ComputableInPolyTime
      (fun φ : CNF ℕ =>
        ((3 * φ.numVars + 1) * (2 * (k - 1)) ^ φ.numVars * k ^ (k - 3) +
          k ^ φ.numVars * (k - 1) ^ (k - 3) - 1) /
        (k ^ φ.numVars * (k - 1) ^ (k - 3))) encCNF encNat :=
    ComputableInPolyTime.binary_div' hnum hden
  exact ComputableInPolyTime.binary_mul' (.const 2)
    (ComputableInPolyTime.binary_mul' hquot (.const c))

private theorem numVars_le_length_encCNF (φ : CNF ℕ) :
    φ.numVars ≤ (encCNF φ).length := by
  calc φ.numVars = φ.vars.toFinset.card := rfl
    _ ≤ φ.vars.length := List.toFinset_card_le φ.vars
    _ ≤ (encCNF φ).length := SAT.length_vars_le φ

/-- **Schöning's `k`-SAT algorithm on a fair-coin multitape Turing machine.** For every `k ≥ 3`
and confidence parameter `c : ℕ`, there exist a finite-control fair-coin `MultiTapePTM`, a clock
`T : CNF ℕ → ℕ`, and polynomial constants `C E : ℕ` such that for every `φ : CNF ℕ`
(`n = φ.numVars`, `L = (encCNF φ).length`):

1. **Deterministic worst-case halting:** every branch halts within `T φ` steps
   (`machine.toNTM.RunsInTime (encCNF φ) (T φ)`),
2. **Sub-`2 ^ n` runtime:** `(T φ : ℝ) ≤ C * (((2 * (k - 1)) / k) ^ n * (L + 1) ^ E)`,
3. **Polynomial workspace:** `machine.toNTM.RunsInSpace (encCNF φ) (C * (L + 1) ^ E)`,
4. **Zero false positives:** if `φ ∉ KSAT k`, `ProbComp.eval (machine.runClosed (T φ) (encCNF φ)) =
   PMF.pure [false]`,
5. **Amplified soundness:** if `φ ∈ KSAT k`, the acceptance probability `[true]` is at least
   `1 - exp (-c)`. -/
theorem exists_multiTapePTM_KSAT {k : ℕ} (hk : 3 ≤ k) (c : ℕ) :
    ∃ (K : ℕ) (Control : Type) (_ : Finite Control)
      (machine : MultiTapePTM K Bool Control) (T : CNF ℕ → ℕ) (C E : ℕ),
      ∀ φ : CNF ℕ,
        (∀ final ∈ (ProbComp.eval
            (machine.runClosedConfigFrom (T φ) (machine.initialConfig (encCNF φ)))).support,
            final.tapes.state = none) ∧
          machine.toNTM.RunsInTime (encCNF φ) (T φ) ∧
          ((T φ : ℝ) ≤
            (C : ℝ) * (((2 * ((k : ℝ) - 1)) / k) ^ φ.numVars *
              ((encCNF φ).length + 1 : ℝ) ^ E)) ∧
          machine.toNTM.RunsInSpace (encCNF φ) (C * ((encCNF φ).length + 1) ^ E) ∧
          (φ ∉ KSAT k →
            ProbComp.eval (machine.runClosed (T φ) (encCNF φ)) = PMF.pure [false]) ∧
          (φ ∈ KSAT k →
            1 - Real.exp (-(c : ℝ)) ≤
              (ProbComp.eval (machine.runClosed (T φ) (encCNF φ)) [true]).toReal) := by
  let trials (φ : CNF ℕ) : ℕ := 2 * schoeningTrials k φ.numVars c
  obtain ⟨K, Control, hfin, machine, C₀, E₀, hM⟩ :=
    IsPPTOn.exists_multiTapePTM_repeatAnyBool_binary
      (isPPTOn_schoeningTrialProg k)
      (computableInPolyTime_two_mul_schoeningTrials hk c)
  let T (φ : CNF ℕ) : ℕ := C₀ * ((trials φ + 1) * ((encCNF φ).length + 1) ^ E₀)
  let C : ℕ := C₀ * (18 * c + 1)
  let E : ℕ := E₀ + 1
  refine ⟨K, Control, hfin, machine, T, C, E, fun φ => ?_⟩
  obtain ⟨hhalt, heval, hspace₀⟩ := hM φ
  have hrunsInTime : machine.toNTM.RunsInTime (encCNF φ) (T φ) :=
    machine.runsInTime_toNTM hhalt
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hr1 : 1 ≤ 2 * ((k : ℝ) - 1) / k := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hrn1 : 1 ≤ (2 * ((k : ℝ) - 1) / k) ^ φ.numVars := one_le_pow₀ hr1
  have hT_bound : (T φ : ℝ) ≤
      (C : ℝ) * (((2 * ((k : ℝ) - 1)) / k) ^ φ.numVars *
        ((encCNF φ).length + 1 : ℝ) ^ E) := by
    set n := φ.numVars
    set L := (encCNF φ).length
    set base := (2 * ((k : ℝ) - 1)) / k
    have hnL : (n : ℝ) ≤ L := by exact_mod_cast numVars_le_length_encCNF φ
    have htr_le := schoeningTrials_le hk n c
    have h9 : 9 * (n : ℝ) + 4 ≤ 9 * ((L : ℝ) + 1) := by linarith
    have hbase0 : 0 ≤ base ^ n := by positivity
    have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
    have htrials_R : (trials φ + 1 : ℝ) ≤ (18 * (c : ℝ) + 1) * base ^ n * (L + 1) := by
      have hmul1 : (9 * (n : ℝ) + 4) * base ^ n * c ≤ 9 * ((L : ℝ) + 1) * base ^ n * c :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h9 hbase0) hc0
      have h1_le : (1 : ℝ) ≤ base ^ n * (L + 1) := by
        have hL1 : (1 : ℝ) ≤ (L : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) L]
        nlinarith
      dsimp only [trials]
      push_cast
      have h2tr : 2 * (schoeningTrials k n c : ℝ) + 1 ≤
          2 * (9 * ((L : ℝ) + 1) * base ^ n * c) + base ^ n * ((L : ℝ) + 1) := by
        linarith [htr_le, hmul1, h1_le]
      calc 2 * (schoeningTrials k n c : ℝ) + 1
          ≤ 2 * (9 * ((L : ℝ) + 1) * base ^ n * c) + base ^ n * ((L : ℝ) + 1) := h2tr
        _ = (18 * (c : ℝ) + 1) * base ^ n * (L + 1) := by ring
    dsimp only [T, C, E]
    push_cast
    have hpowE : ((L : ℝ) + 1) ^ (E₀ + 1) = ((L : ℝ) + 1) * ((L : ℝ) + 1) ^ E₀ := by
      rw [pow_succ']
    rw [hpowE]
    have hfac : (0 : ℝ) ≤ (C₀ : ℝ) * ((L : ℝ) + 1) ^ E₀ := by positivity
    calc (C₀ : ℝ) * (((trials φ : ℝ) + 1) * ((L : ℝ) + 1) ^ E₀)
        = ((trials φ : ℝ) + 1) * ((C₀ : ℝ) * ((L : ℝ) + 1) ^ E₀) := by ring
      _ ≤ ((18 * (c : ℝ) + 1) * base ^ n * (L + 1)) * ((C₀ : ℝ) * ((L : ℝ) + 1) ^ E₀) :=
          mul_le_mul_of_nonneg_right htrials_R hfac
      _ = ((C₀ : ℝ) * (18 * (c : ℝ) + 1)) * (base ^ n * (((L : ℝ) + 1) * ((L : ℝ) + 1) ^ E₀)) :=
          by ring
  have hspace : machine.toNTM.RunsInSpace (encCNF φ) (C * ((encCNF φ).length + 1) ^ E) := by
    have hle : C₀ * ((encCNF φ).length + 1) ^ E₀ ≤ C * ((encCNF φ).length + 1) ^ E := by
      dsimp only [C, E]
      exact Nat.mul_le_mul (Nat.le_mul_of_pos_right _ (by omega))
        (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_succ _))
    exact fun p => (hspace₀ p).trans hle
  refine ⟨hhalt, hrunsInTime, hT_bound, hspace, ?_, ?_⟩
  · intro hnot
    rw [heval, eval_iterate_repeatAnyStep_eq_pure_false _ _
      (eval_schoeningTrialProg_true_eq_zero_of_not_mem_KSAT hnot),
      PMF.pure_map, encBool_apply]
  · intro hmem
    let μ := ProbComp.eval (OracleComp.iterate (trials φ)
      (repeatAnyStep (schoeningTrialProg k φ)) false)
    have hmap_true : (μ.map encBool) [true] = μ true := by
      rw [PMF.map_apply, tsum_fintype]
      simp only [Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
        Finset.sum_insert, Finset.sum_singleton, encBool_apply, List.cons.injEq, and_true,
        ↓reduceIte, add_zero]
    rw [heval, hmap_true]
    have hμ_true : (μ true).toReal = 1 - (μ false).toReal := by
      have hfalse := Cslib.Probability.PMF.toReal_false_eq_one_sub μ
      linarith
    rw [hμ_true]
    have hμ_false : (μ false).toReal =
        (1 - (ProbComp.eval (schoeningTrialProg k φ) true).toReal) ^ (trials φ) :=
      eval_iterate_repeatAnyStep_false_toReal (schoeningTrialProg k φ) (trials φ)
    rw [hμ_false]
    set p := (ProbComp.eval (schoeningTrialProg k φ) true).toReal
    have hp_le_one : p ≤ 1 := by
      simpa only [ENNReal.toReal_one] using
        ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
    set n := φ.numVars
    set P₀ := (((k : ℝ) - 1) / k) ^ (k - 3) * ((k : ℝ) / (2 * ((k : ℝ) - 1))) ^ n / (3 * n + 1)
      with hP₀
    have hP₀pos : 0 < P₀ := by
      rw [hP₀]
      have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
      have hk0 : (0 : ℝ) < k := by linarith
      positivity
    have hp_ge : (1 / 2 : ℝ) * P₀ ≤ p := succeedProb_le_schoeningTrialProg hk hmem
    have hinv : (3 * n + 1 : ℝ) * (2 * ((k : ℝ) - 1) / k) ^ n *
        ((k : ℝ) / ((k : ℝ) - 1)) ^ (k - 3) = P₀⁻¹ := by
      rw [hP₀]
      have hk0 : (k : ℝ) ≠ 0 := by linarith
      have hk10 : (k : ℝ) - 1 ≠ 0 := by linarith
      have h1 : (2 * ((k : ℝ) - 1) / k) * ((k : ℝ) / (2 * ((k : ℝ) - 1))) = 1 := by field_simp
      have h2 : ((k : ℝ) / ((k : ℝ) - 1)) * (((k : ℝ) - 1) / k) = 1 := by field_simp
      field_simp
      calc _ = ((2 * ((k : ℝ) - 1) / k) * ((k : ℝ) / (2 * ((k : ℝ) - 1)))) ^ n *
            (((k : ℝ) / ((k : ℝ) - 1)) * (((k : ℝ) - 1) / k)) ^ (k - 3) := by
            rw [mul_pow, mul_pow]; ring
        _ = 1 := by rw [h1, h2, one_pow, one_pow, one_mul]
    have hprod_ge : (c : ℝ) ≤ (trials φ : ℝ) * p := by
      dsimp only [trials]
      rw [schoeningTrials, hinv]
      push_cast
      calc (c : ℝ) = (P₀⁻¹ * c) * P₀ := by field_simp
        _ ≤ (⌈P₀⁻¹⌉₊ * c) * P₀ := by gcongr; exact Nat.le_ceil _
        _ = (2 * (⌈P₀⁻¹⌉₊ * c)) * ((1 / 2 : ℝ) * P₀) := by ring
        _ ≤ (2 * (⌈P₀⁻¹⌉₊ * c)) * p := by gcongr
    have hexp := Real.one_sub_pow_le_exp hp_le_one hprod_ge
    linarith

/-- **Bounded-error multitape `k`-SAT decider (`DecidesWithBoundedErrorInTime`).** Specializing
`exists_multiTapePTM_KSAT` to confidence `c = 2` (`exp (-2) ≤ 1 / 3`) yields a fair-coin
`MultiTapePTM` deciding `KSAT k` (`k ≥ 3`) with bounded error, zero false positives, polynomial
workspace, and `O(((2 (k - 1)) / k) ^ n * (L + 1) ^ E)` worst-case halting time. -/
theorem exists_decidesWithBoundedErrorInTime_KSAT {k : ℕ} (hk : 3 ≤ k) :
    ∃ (K : ℕ) (Control : Type) (_ : Finite Control)
      (machine : MultiTapePTM K Bool Control) (T : CNF ℕ → ℕ) (C E : ℕ),
      machine.DecidesWithBoundedErrorInTime encCNF (KSAT k) T ∧
      (∀ φ : CNF ℕ,
        ((T φ : ℝ) ≤
          (C : ℝ) * (((2 * ((k : ℝ) - 1)) / k) ^ φ.numVars *
            ((encCNF φ).length + 1 : ℝ) ^ E)) ∧
        machine.toNTM.RunsInSpace (encCNF φ) (C * ((encCNF φ).length + 1) ^ E) ∧
        (φ ∉ KSAT k →
          ProbComp.eval (machine.runClosed (T φ) (encCNF φ)) = PMF.pure [false])) := by
  obtain ⟨K, Control, hfin, machine, T, C, E, hspec⟩ := exists_multiTapePTM_KSAT hk 2
  refine ⟨K, Control, hfin, machine, T, C, E, ?_, fun φ => ?_⟩
  · intro φ
    obtain ⟨hhalt, -, -, -, hno, hyes⟩ := hspec φ
    refine ⟨hhalt, ?_⟩
    by_cases hmem : φ ∈ KSAT k
    · have hind : indicator (KSAT k) φ = true := by simp only [indicator, hmem, ↓reduceIte]
      rw [hind]
      have hexp2 := Real.exp_neg_two_le_one_third
      have hreal :
          (2 / 3 : ℝ) ≤ (ProbComp.eval (machine.runClosed (T φ) (encCNF φ)) [true]).toReal := by
        have hy := hyes hmem
        norm_num at hy
        linarith
      have h23_ne_top : (2 / 3 : ℝ≥0∞) ≠ ⊤ :=
        ENNReal.div_ne_top ENNReal.ofNat_ne_top (by norm_num)
      exact (ENNReal.toReal_le_toReal h23_ne_top (PMF.apply_ne_top _ _)).mp
        (by simpa only [ENNReal.toReal_div, ENNReal.toReal_ofNat] using hreal)
    · have hind : indicator (KSAT k) φ = false := by simp only [indicator, hmem, ↓reduceIte]
      rw [hind, hno hmem, PMF.pure_apply_self]
      have h23_ne_top : (2 / 3 : ℝ≥0∞) ≠ ⊤ :=
        ENNReal.div_ne_top ENNReal.ofNat_ne_top (by norm_num)
      exact (ENNReal.toReal_le_toReal h23_ne_top ENNReal.one_ne_top).mp
        (by simp only [ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_one]; norm_num)
  · obtain ⟨-, -, hT, hspace, hno, -⟩ := hspec φ
    exact ⟨hT, hspace, hno⟩

/-- **Schöning's `(4 / 3) ^ n` bounded-error multitape `3`-SAT decider.** -/
theorem exists_decidesWithBoundedErrorInTime_ThreeSAT :
    ∃ (K : ℕ) (Control : Type) (_ : Finite Control)
      (machine : MultiTapePTM K Bool Control) (T : CNF ℕ → ℕ) (C E : ℕ),
      machine.DecidesWithBoundedErrorInTime encCNF ThreeSAT T ∧
      (∀ φ : CNF ℕ,
        ((T φ : ℝ) ≤
          (C : ℝ) * ((4 / 3 : ℝ) ^ φ.numVars * ((encCNF φ).length + 1 : ℝ) ^ E)) ∧
        machine.toNTM.RunsInSpace (encCNF φ) (C * ((encCNF φ).length + 1) ^ E) ∧
        (φ ∉ ThreeSAT →
          ProbComp.eval (machine.runClosed (T φ) (encCNF φ)) = PMF.pure [false])) := by
  obtain ⟨K, Control, hfin, machine, T, C, E, hdec, hbounds⟩ :=
    exists_decidesWithBoundedErrorInTime_KSAT (le_refl 3)
  have hset : KSAT 3 = ThreeSAT := rfl
  rw [hset] at hdec
  refine ⟨K, Control, hfin, machine, T, C, E, hdec, fun φ => ?_⟩
  obtain ⟨hT, hspace, hno⟩ := hbounds φ
  have hbase : (2 * ((3 : ℝ) - 1)) / 3 = 4 / 3 := by norm_num
  rw [Nat.cast_ofNat, hbase] at hT
  exact ⟨hT, hspace, hno⟩

end MachineDecider

end Cslib.Complexity.Schoening
