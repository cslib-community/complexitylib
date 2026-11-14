/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.FPAUS
public import CslibFrontier.Computability.Complexity.Classes.FPAUS.SelfReducible
public import CslibFrontier.Computability.Complexity.Classes.Oracle
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Languages.Probabilistic.BoundedUniform
public import CslibFrontier.Languages.Probabilistic.Iteration
public import CslibFrontier.Probability.DDGTree.Rejection
import CslibFrontier.Computability.Complexity.Classes.Oracle.Closure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import Mathlib.Order.Interval.Finset.Fin
import CslibFrontier.Computability.Probabilistic.Adaptive
import CslibFrontier.Computability.Probabilistic.BoundedUniform
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Languages.Probabilistic.Oracle.Support
import CslibFrontier.Probability.Option
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Tactic.EncLen

/-!
# Exact uniform sampling from exact counts on self-reducible families

For a one-bit self-reducible witness family (`Cslib.Complexity.SelfReducible`), an exact witness
counter `count y = (W y).card` yields **exact** prefix bit-by-bit conditional sampling
[Jerrum, Valiant and Vazirani][JerrumValiantVazirani1986],
[Sinclair, Lecture 4, Section 4.2.3][Sinclair2025]:

1. **Exact `PMF` conditional prefix walk (`SelfReducible.exactWalk`, `SelfReducible.exactSample`)**:
   after evaluating `c = count x` once at the root (returning `none` immediately when `c = 0`),
   each positive-length node `y` evaluates only `c₁ = count (R.child y true)` and deduces
   `|W (R.child y false)| = c - c₁` from `SelfReducible.card_eq_add`. Drawing an exact uniform
   index `r : Fin c` branches to `true` when `r.val < c₁` (with count `c₁`) and to `false`
   otherwise (with count `c - c₁`). By induction on `R.len x`, the output distribution on
   `Option (List Bool)` equals `Cslib.Complexity.uniformWitness (W x)` **identically** (zero
   total-variation error), using at most `1 + R.len x` counter evaluations, all on instances of
   encoded length at most `(enc x).length`.
2. **Fair-bit cost of the exact walk (`SelfReducible.exactSampleExpectedBits`,
   `SelfReducible.exactSampleExpectedBits_le`)**: drawing each index `r : Fin c` with the
   discrete-distribution-generating tree `Probability.uniformFinTree c`, which generates the
   uniform distribution on `Fin c` (`Probability.uniformFinTree_generates`) with at most
   `2 * Nat.clog 2 c` expected fair flips (`Probability.expectedFlips_uniformFinTree_le`), and
   using `(W y).card ≤ 2 ^ R.len y` (`SelfReducible.card_le_two_pow_len`), the whole walk uses at
   most `(R.len x : ℝ) * (R.len x + 1)` expected fair flips (`0` when `W x = ∅`).
3. **Strict PPT and oracle-PPT capped conditional walk (`SelfReducible.boundedConditionalSample`,
   `SelfReducible.boundedConditionalOracleSample`)**: replacing each unbounded `Fin c` draw by
   `ProbComp.sampleUniformIntervalRetry c fuel`, at most `fuel = q + R.len x` attempts of
   `c.size` fair bits, keeps expected fair-coin cost at most `2 * c.size` per step
   (`ProbComp.expectedCost_sampleUniformIntervalRetry_le`), makes at most
   `1 + R.len x` counter calls (independent of the accuracy `q`), achieves total-variation
   distance at most `(1 / 2) ^ q` from `uniformWitness (W x)` (`IsFPAUS` when `count` is
   polynomial-time), and lifts to `IsOraclePPTOn` when `count` is computed relative to an oracle.

## Main definitions

* `Cslib.Complexity.SelfReducible.exactWalk`, `Cslib.Complexity.SelfReducible.exactSample`:
  exact prefix conditional sampling in `PMF`.
* `Cslib.Complexity.ConditionalWalkState`: loop state structure for bounded conditional walks.
* `Cslib.Complexity.SelfReducible.boundedConditionalSample`,
  `Cslib.Complexity.SelfReducible.boundedConditionalOracleSample`: strict PPT and oracle-PPT
  conditional prefix samplers.

## Main results

* `Cslib.Complexity.SelfReducible.card_le_two_pow_len`: `(W x).card ≤ 2 ^ R.len x`.
* `Cslib.Complexity.SelfReducible.exactSample_eq_uniformWitness`: exact distributional equality
  `R.exactSample count unif x = uniformWitness (W x)`.
* `Cslib.Complexity.SelfReducible.length_exactSampleQueries_le`,
  `Cslib.Complexity.SelfReducible.mem_exactSampleQueries_length_le`: at most `1 + R.len x`
  counter evaluations, all of encoded length at most `(enc x).length`.
* `Cslib.Complexity.SelfReducible.closeTo_boundedConditionalSample`,
  `Cslib.Complexity.SelfReducible.isFPAUS_boundedConditionalSample`,
  `Cslib.Complexity.SelfReducible.isOraclePPTOn_boundedConditionalOracleSample`,
  `Cslib.Complexity.SelfReducible.closeTo_boundedConditionalOracleSample`.

## References

* [M. R. Jerrum, L. G. Valiant, V. V. Vazirani, *Random generation of combinatorial structures from
  a uniform distribution*][JerrumValiantVazirani1986]
* [A. Sinclair, *CS294 Partition Functions*, Lecture 4, Section 4.2.3][Sinclair2025]
-/

public section

open scoped ENNReal

namespace Cslib.Complexity

open Cslib.ProbComp Cslib.Probability Turing.MultiTapeTM

/-! ### Loop state structure for conditional prefix walks -/

/-- State of the iterative bit-by-bit conditional prefix walk on instances `α`. -/
structure ConditionalWalkState (α : Type) where
  /-- Current self-reduction node. -/
  node : α
  /-- Exact witness count of `node`. -/
  countVal : ℕ
  /-- Prefix bits accumulated so far, in reverse order. -/
  revBits : List Bool
  /-- Whether no bounded draw has aborted and `countVal > 0` so far. -/
  active : Bool
  deriving DecidableEq, Repr

/-- Encoding of `ConditionalWalkState α`. -/
@[expose]
def encConditionalWalkState {α : Type} (enc : α ↪ List Bool) :
    ConditionalWalkState α ↪ List Bool :=
  ⟨fun s => encPair enc (encPair encNat (encPair encBits encBool))
      (s.node, s.countVal, s.revBits, s.active),
   fun x y h => by
     have h' := (encPair enc (encPair encNat (encPair encBits encBool))).injective h
     cases x; cases y; simp_all⟩

@[simp] theorem encConditionalWalkState_apply {α : Type} (enc : α ↪ List Bool)
    (s : ConditionalWalkState α) :
    encConditionalWalkState enc s =
      encPair enc (encPair encNat (encPair encBits encBool))
        (s.node, s.countVal, s.revBits, s.active) :=
  rfl

private theorem computableInDegree_conditionalWalkStateFields {α : Type} (enc : α ↪ List Bool) :
    ComputableInDegree
      (fun s : ConditionalWalkState α => (s.node, s.countVal, s.revBits, s.active))
      (encConditionalWalkState enc)
      (encPair enc (encPair encNat (encPair encBits encBool))) 1 1 :=
  ComputableInDegree.of_eq fun _ => rfl

@[scoped fun_prop]
theorem encConditionalWalkState_node_polyTime {α γ : Type} {enc : α ↪ List Bool}
    {encIn : γ ↪ List Bool} {g : γ → ConditionalWalkState α}
    (h : ComputableInPolyTime g encIn (encConditionalWalkState enc)) :
    ComputableInPolyTime (fun a => (g a).node) encIn enc :=
  (ComputableInDegree.fst'
    (computableInDegree_conditionalWalkStateFields enc)).computableInPolyTime.comp h

@[scoped fun_prop]
theorem encConditionalWalkState_countVal_polyTime {α γ : Type} {enc : α ↪ List Bool}
    {encIn : γ ↪ List Bool} {g : γ → ConditionalWalkState α}
    (h : ComputableInPolyTime g encIn (encConditionalWalkState enc)) :
    ComputableInPolyTime (fun a => (g a).countVal) encIn encNat :=
  (ComputableInDegree.fst' (ComputableInDegree.snd'
    (computableInDegree_conditionalWalkStateFields enc))).computableInPolyTime.comp h

@[scoped fun_prop]
theorem encConditionalWalkState_revBits_polyTime {α γ : Type} {enc : α ↪ List Bool}
    {encIn : γ ↪ List Bool} {g : γ → ConditionalWalkState α}
    (h : ComputableInPolyTime g encIn (encConditionalWalkState enc)) :
    ComputableInPolyTime (fun a => (g a).revBits) encIn encBits :=
  (ComputableInDegree.fst' (ComputableInDegree.snd' (ComputableInDegree.snd'
    (computableInDegree_conditionalWalkStateFields enc)))).computableInPolyTime.comp h

@[scoped fun_prop]
theorem encConditionalWalkState_active_polyTime {α γ : Type} {enc : α ↪ List Bool}
    {encIn : γ ↪ List Bool} {g : γ → ConditionalWalkState α}
    (h : ComputableInPolyTime g encIn (encConditionalWalkState enc)) :
    ComputableInPolyTime (fun a => (g a).active) encIn encBool :=
  (ComputableInDegree.snd' (ComputableInDegree.snd' (ComputableInDegree.snd'
    (computableInDegree_conditionalWalkStateFields enc)))).computableInPolyTime.comp h

@[scoped fun_prop]
theorem encConditionalWalkState_mk_polyTime {α γ : Type} {enc : α ↪ List Bool}
    {encIn : γ ↪ List Bool} {nd : γ → α} {cv : γ → ℕ} {rb : γ → List Bool} {act : γ → Bool}
    (hnd : ComputableInPolyTime nd encIn enc)
    (hcv : ComputableInPolyTime cv encIn encNat)
    (hrb : ComputableInPolyTime rb encIn encBits)
    (hact : ComputableInPolyTime act encIn encBool) :
    ComputableInPolyTime (fun a => ConditionalWalkState.mk (nd a) (cv a) (rb a) (act a))
      encIn (encConditionalWalkState enc) :=
  (hnd.prod (hcv.prod (hrb.prod hact))).of_enc_eq fun _ => rfl

/-! ### Self-reducible exact and bounded conditional samplers -/

namespace SelfReducible

variable {α : Type} {enc : α ↪ List Bool} {W : α → Finset (List Bool)}

/-- A self-reducible witness set of witness length `ℓ` has at most `2 ^ ℓ` witnesses. -/
theorem card_le_two_pow_len (R : SelfReducible enc W) (x : α) :
    (W x).card ≤ 2 ^ R.len x := by
  generalize hℓ : R.len x = ℓ
  induction ℓ generalizing x with
  | zero =>
    simpa using Finset.card_le_card (R.subset_singleton_nil hℓ)
  | succ k ih =>
    have hpos : 0 < R.len x := by omega
    rw [R.card_eq_add hpos, pow_succ']
    have h0 := ih (R.child x false) (by have := R.len_child x hpos false; omega)
    have h1 := ih (R.child x true) (by have := R.len_child x hpos true; omega)
    omega

/-- Recursive exact conditional prefix walk of `n` remaining bits from `y` with known positive
witness count `c`: query only `count (R.child y true)` and branch via `unif c`. -/
noncomputable def exactWalk (R : SelfReducible enc W) (count : α → ℕ)
    (unif : ∀ n : ℕ, [NeZero n] → PMF (Fin n)) :
    ℕ → α → ℕ → PMF (Option (List Bool))
  | 0, _, _ => PMF.pure (some [])
  | n + 1, y, c =>
    if hc : 0 < c then
      let c₁ := count (R.child y true)
      (@unif c ⟨Nat.ne_of_gt hc⟩).bind fun r =>
        if (r : ℕ) < c₁ then
          PMF.map (Option.map (true :: ·)) (exactWalk R count unif n (R.child y true) c₁)
        else
          PMF.map (Option.map (false :: ·)) (exactWalk R count unif n (R.child y false) (c - c₁))
    else PMF.pure none

/-- **Exact prefix conditional sampler** for a self-reducible witness family from an exact counter
`count`: returns `none` when `count x = 0`, and otherwise runs `exactWalk` for `R.len x` bits. -/
noncomputable def exactSample (R : SelfReducible enc W) (count : α → ℕ)
    (unif : ∀ n : ℕ, [NeZero n] → PMF (Fin n) := fun n _ => PMF.uniformOfFintype (Fin n))
    (x : α) : PMF (Option (List Bool)) :=
  let c := count x
  if 0 < c then R.exactWalk count unif (R.len x) x c else PMF.pure none

private theorem pmf_map_option_map_cons_some (p : PMF (Option (List Bool))) (b : Bool)
    (u : List Bool) :
    (PMF.map (Option.map (b :: ·)) p) (some (b :: u)) = p (some u) := by
  rw [PMF.map_apply, tsum_eq_single (some u)]
  · exact ite_eq_left rfl
  · intro o ho
    cases o with
    | none => exact ite_eq_right fun h => by cases h
    | some v =>
      exact ite_eq_right fun h => ho (by
        injection h with h; injection h with _ h; subst h; rfl)

private theorem pmf_map_option_map_cons_ne (p : PMF (Option (List Bool))) {b₁ b₂ : Bool}
    (hne : b₁ ≠ b₂) (u : List Bool) :
    (PMF.map (Option.map (b₁ :: ·)) p) (some (b₂ :: u)) = 0 := by
  rw [PMF.map_apply]
  exact tsum_eq_zero_iff.mpr fun o => by cases o <;> simp [hne.symm]

/-- Pointwise evaluation of `exactWalk` on `some w` when `count` agrees with `(W ·).card` on
instances no longer than `y`. -/
theorem exactWalk_apply_some (R : SelfReducible enc W) {count : α → ℕ}
    {unif : ∀ n : ℕ, [NeZero n] → PMF (Fin n)}
    (hunif : ∀ (n : ℕ) [NeZero n], unif n = PMF.uniformOfFintype (Fin n))
    {n : ℕ} {y : α} (hlen : R.len y = n) (hpos : 0 < (W y).card)
    (hcount : ∀ z, (enc z).length ≤ (enc y).length → count z = (W z).card)
    (w : List Bool) :
    R.exactWalk count unif n y (W y).card (some w) =
      if w ∈ W y then ((W y).card : ℝ≥0∞)⁻¹ else 0 := by
  induction n generalizing y w with
  | zero =>
    have hWy : W y = {[]} := R.eq_singleton_nil hlen hpos
    rw [exactWalk, hWy, Finset.card_singleton, Nat.cast_one, inv_one]
    by_cases hw : w = []
    · subst hw; simp
    · simp [hw]
  | succ k ih =>
    have hy_pos : 0 < R.len y := by omega
    have hsplit := R.card_eq_add hy_pos
    have hc1_eq : count (R.child y true) = (W (R.child y true)).card :=
      hcount _ (R.length_child_le y hy_pos true)
    have hc1_le : (W (R.child y true)).card ≤ (W y).card := by omega
    have hc0_eq : (W y).card - (W (R.child y true)).card = (W (R.child y false)).card := by omega
    have : NeZero (W y).card := ⟨Nat.ne_of_gt hpos⟩
    rw [exactWalk, dite_eq_left hpos]
    dsimp only
    rw [hunif (W y).card, hc1_eq, PMF.bind_apply]
    cases w with
    | nil =>
      have hnil : [] ∉ W y := fun hm => by
        have hlen_nil := R.length_eq y [] hm
        simp at hlen_nil
        omega
      rw [ite_eq_right hnil]
      refine tsum_eq_zero_iff.mpr fun r => ?_
      split_ifs <;> simp [PMF.map_apply]
    | cons b u =>
      rw [tsum_fintype]
      have hsum_eq :
          (∑ r : Fin (W y).card,
            PMF.uniformOfFintype (Fin (W y).card) r *
              (if (r : ℕ) < (W (R.child y true)).card then
                PMF.map (Option.map (true :: ·))
                  (R.exactWalk count unif k (R.child y true) (W (R.child y true)).card)
              else
                PMF.map (Option.map (false :: ·))
                  (R.exactWalk count unif k (R.child y false)
                    ((W y).card - (W (R.child y true)).card)))
                (some (b :: u))) =
            ((W (R.child y b)).card : ℝ≥0∞) *
              (((W y).card : ℝ≥0∞)⁻¹ *
                R.exactWalk count unif k (R.child y b) (W (R.child y b)).card (some u)) := by
        cases b
        · have hterm_false : ∀ r : Fin (W y).card,
              PMF.uniformOfFintype (Fin (W y).card) r *
                (if (r : ℕ) < (W (R.child y true)).card then
                  PMF.map (Option.map (fun xs => true :: xs))
                    (R.exactWalk count unif k (R.child y true) (W (R.child y true)).card)
                else
                  PMF.map (Option.map (fun xs => false :: xs))
                    (R.exactWalk count unif k (R.child y false)
                      ((W y).card - (W (R.child y true)).card)))
                  (some (false :: u)) =
              if ¬ (r : ℕ) < (W (R.child y true)).card then
                ((W y).card : ℝ≥0∞)⁻¹ *
                  R.exactWalk count unif k (R.child y false) (W (R.child y false)).card (some u)
              else 0 := fun r => by
            rw [PMF.uniformOfFintype_apply, Fintype.card_fin]
            by_cases hr : (r : ℕ) < (W (R.child y true)).card
            · simp [hr, pmf_map_option_map_cons_ne _ Bool.false_ne_true.symm u]
            · simp [hr, hc0_eq]
          simp_rw [hterm_false]
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
          congr 1
          rcases hc1_le.eq_or_lt with h_eq | h_lt
          · have h0 : (W (R.child y false)).card = 0 := by omega
            simp [h0, h_eq]
          · have hIci : Finset.univ.filter
                (fun r : Fin (W y).card => ¬ (r : ℕ) < (W (R.child y true)).card) =
                Finset.Ici ⟨(W (R.child y true)).card, h_lt⟩ := by
              ext r; simp [Fin.le_def]
            rw [hIci, Fin.card_Ici, hc0_eq]
        · have hterm_true : ∀ r : Fin (W y).card,
              PMF.uniformOfFintype (Fin (W y).card) r *
                (if (r : ℕ) < (W (R.child y true)).card then
                  PMF.map (Option.map (true :: ·))
                    (R.exactWalk count unif k (R.child y true) (W (R.child y true)).card)
                else
                  PMF.map (Option.map (false :: ·))
                    (R.exactWalk count unif k (R.child y false)
                      ((W y).card - (W (R.child y true)).card)))
                  (some (true :: u)) =
              if (r : ℕ) < (W (R.child y true)).card then
                ((W y).card : ℝ≥0∞)⁻¹ *
                  R.exactWalk count unif k (R.child y true) (W (R.child y true)).card (some u)
              else 0 := fun r => by
            simp_rw [PMF.uniformOfFintype_apply, Fintype.card_fin]
            split_ifs with hr
            · simp
            · simp [pmf_map_option_map_cons_ne _ Bool.false_ne_true u]
          simp_rw [hterm_true]
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
          rcases hc1_le.eq_or_lt with h_eq | h_lt
          · congr 1
            have huniv : Finset.univ.filter
                (fun r : Fin (W y).card => (r : ℕ) < (W (R.child y true)).card) =
                Finset.univ := by
              ext r; simp [h_eq]
            rw [huniv, Finset.card_fin, h_eq]
          · congr 1
            have hIio : Finset.univ.filter
                (fun r : Fin (W y).card => (r : ℕ) < (W (R.child y true)).card) =
                Finset.Iio ⟨(W (R.child y true)).card, h_lt⟩ := by
              ext r; simp [Fin.lt_def]
            rw [hIio, Fin.card_Iio]
      rw [hsum_eq]
      rcases Nat.eq_zero_or_pos (W (R.child y b)).card with hcb | hcb_pos
      · have hnot : b :: u ∉ W y := by
          rw [R.cons_mem_iff y hy_pos b u]
          rw [Finset.card_eq_zero] at hcb
          simp [hcb]
        simp [hcb, hnot]
      · rw [ih (y := R.child y b) (by have := R.len_child y hy_pos b; omega) hcb_pos
          (fun z hz => hcount z (hz.trans (R.length_child_le y hy_pos b))) u]
        simp only [← R.cons_mem_iff y hy_pos b u]
        by_cases hmem : b :: u ∈ W y
        · simp only [hmem, ↓reduceIte]
          calc ((W (R.child y b)).card : ℝ≥0∞) *
                (((W y).card : ℝ≥0∞)⁻¹ * ((W (R.child y b)).card : ℝ≥0∞)⁻¹)
              = (((W (R.child y b)).card : ℝ≥0∞) *
                  ((W (R.child y b)).card : ℝ≥0∞)⁻¹) * ((W y).card : ℝ≥0∞)⁻¹ := by ring
            _ = 1 * ((W y).card : ℝ≥0∞)⁻¹ := by
                rw [ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hcb_pos))
                  (ENNReal.natCast_ne_top _)]
            _ = ((W y).card : ℝ≥0∞)⁻¹ := one_mul _
        · simp [hmem]

/-- **Exact uniformity from exact counts.** Whenever `unif` samples each positive `Fin n`
uniformly and `count z = (W z).card` on instances of encoded length at most `(enc x).length`,
`R.exactSample count unif x` equals `uniformWitness (W x)` identically. -/
theorem exactSample_eq_uniformWitness (R : SelfReducible enc W) {count : α → ℕ}
    {unif : ∀ n : ℕ, [NeZero n] → PMF (Fin n)}
    (hunif : ∀ (n : ℕ) [NeZero n], unif n = PMF.uniformOfFintype (Fin n))
    {x : α} (hcount : ∀ z, (enc z).length ≤ (enc x).length → count z = (W z).card) :
    R.exactSample count unif x = uniformWitness (W x) := by
  have hcx : count x = (W x).card := hcount x (le_refl _)
  rcases (W x).eq_empty_or_nonempty with hempty | hne
  · simp [exactSample, hcx, hempty]
  · have hpos : 0 < (W x).card := Finset.card_pos.mpr hne
    have hsome_val : ∀ w, R.exactSample count unif x (some w) =
        uniformWitness (W x) (some w) := by
      intro w
      rw [exactSample, hcx, ite_eq_left hpos, R.exactWalk_apply_some hunif rfl hpos hcount w,
        uniformWitness_of_nonempty hne, PMF.map_apply]
      by_cases hw : w ∈ W x
      · rw [ite_eq_left hw, tsum_eq_single w]
        · simp [PMF.uniformOfFinset_apply, hw]
        · intro v hv; simp [hv.symm]
      · rw [ite_eq_right hw]
        refine (tsum_eq_zero_iff.mpr fun v => ?_).symm
        by_cases hvw : w = v
        · subst hvw; simp [PMF.uniformOfFinset_apply, hw]
        · simp [hvw]
    have hnone_zero : R.exactSample count unif x none = 0 := by
      have htot := (R.exactSample count unif x).tsum_coe
      have htot_u := (uniformWitness (W x)).tsum_coe
      rw [tsum_option_eq] at htot htot_u
      have hu_none : uniformWitness (W x) none = 0 := by
        rw [uniformWitness_of_nonempty hne, PMF.map_apply]
        exact tsum_eq_zero_iff.mpr fun v => by simp
      simp_rw [hsome_val] at htot
      rw [hu_none, zero_add] at htot_u
      rw [htot_u] at htot
      have h0 : R.exactSample count unif x none + 1 = 0 + 1 := by rw [htot, zero_add]
      exact (ENNReal.add_left_inj ENNReal.one_ne_top).mp h0
    ext o
    cases o with
    | none =>
      rw [hnone_zero, uniformWitness_of_nonempty hne, PMF.map_apply]
      exact (tsum_eq_zero_iff.mpr fun v => by simp).symm
    | some w => exact hsome_val w

/-- Zero total-variation distance corollary of `exactSample_eq_uniformWitness`. -/
theorem closeTo_zero_exactSample (R : SelfReducible enc W) {count : α → ℕ}
    {unif : ∀ n : ℕ, [NeZero n] → PMF (Fin n)}
    (hunif : ∀ (n : ℕ) [NeZero n], unif n = PMF.uniformOfFintype (Fin n))
    {x : α} (hcount : ∀ z, (enc z).length ≤ (enc x).length → count z = (W z).card) :
    CloseTo (R.exactSample count unif x) (uniformWitness (W x)) 0 := by
  rw [R.exactSample_eq_uniformWitness hunif hcount]
  exact CloseTo.refl _

/-! ### Pathwise counter-query trace and expected fair-bit bound -/

/-- Counter queries issued along an execution of `exactWalk` driven by index choices `draws`. -/
@[expose]
def exactWalkQueries (R : SelfReducible enc W) (count : α → ℕ) :
    ℕ → α → ℕ → List ℕ → List α
  | 0, _, _, _ => []
  | n + 1, y, c, draws =>
    if 0 < c then
      let y₁ := R.child y true
      let c₁ := count y₁
      let r := draws.headD 0
      if r < c₁ then
        y₁ :: exactWalkQueries R count n y₁ c₁ draws.tail
      else
        y₁ :: exactWalkQueries R count n (R.child y false) (c - c₁) draws.tail
    else []

/-- Counter queries issued by `exactSample` along index choices `draws`: `x` at the root, plus
at most one child query per witness bit. -/
@[expose]
def exactSampleQueries (R : SelfReducible enc W) (count : α → ℕ) (x : α)
    (draws : List ℕ) : List α :=
  let c := count x
  if 0 < c then x :: R.exactWalkQueries count (R.len x) x c draws else [x]

/-- `exactSample` evaluates `count` at most `1 + R.len x` times along every draw sequence. -/
theorem length_exactSampleQueries_le (R : SelfReducible enc W) (count : α → ℕ) (x : α)
    (draws : List ℕ) :
    (R.exactSampleQueries count x draws).length ≤ 1 + R.len x := by
  have hwalk : ∀ n y c ds, (R.exactWalkQueries count n y c ds).length ≤ n := by
    intro n
    induction n with
    | zero => simp [exactWalkQueries]
    | succ k ih =>
      intro y c ds
      simp only [exactWalkQueries]
      split_ifs <;> simp only [List.length_cons, List.length_nil]
      · exact Nat.succ_le_succ (ih _ _ _)
      · exact Nat.succ_le_succ (ih _ _ _)
      · omega
  simp only [exactSampleQueries]
  split_ifs
  · simp only [List.length_cons]
    have := hwalk (R.len x) x (count x) draws
    omega
  · simp

/-- Every instance queried along `exactSampleQueries` has encoded length at most
`(enc x).length`. -/
theorem mem_exactSampleQueries_length_le (R : SelfReducible enc W) (count : α → ℕ) (x : α)
    (draws : List ℕ) {z : α} (hz : z ∈ R.exactSampleQueries count x draws) :
    (enc z).length ≤ (enc x).length := by
  have hwalk : ∀ n y c ds, R.len y = n →
      ∀ u ∈ R.exactWalkQueries count n y c ds, (enc u).length ≤ (enc y).length := by
    intro n
    induction n with
    | zero => simp [exactWalkQueries]
    | succ k ih =>
      intro y c ds hlen u hu
      have hy_pos : 0 < R.len y := by omega
      simp only [exactWalkQueries] at hu
      split_ifs at hu with hc hr
      · rcases List.mem_cons.mp hu with rfl | htl_t
        · exact R.length_child_le y hy_pos true
        · exact (ih (R.child y true) (count (R.child y true)) ds.tail
            (by have := R.len_child y hy_pos true; omega) u htl_t).trans
            (R.length_child_le y hy_pos true)
      · rcases List.mem_cons.mp hu with rfl | htl_f
        · exact R.length_child_le y hy_pos true
        · exact (ih (R.child y false) (c - count (R.child y true)) ds.tail
            (by have := R.len_child y hy_pos false; omega) u htl_f).trans
            (R.length_child_le y hy_pos false)
      · simp at hu
  simp only [exactSampleQueries] at hz
  split_ifs at hz
  · rcases List.mem_cons.mp hz with rfl | htl
    · exact le_refl _
    · exact hwalk (R.len x) x (count x) draws rfl z htl
  · rw [List.mem_singleton] at hz
    subst hz
    exact le_refl _

/-- Expected fair-flip cost of `exactWalk` when each index `r : Fin c` is drawn with the
discrete-distribution-generating tree `Probability.uniformFinTree c` (which generates the uniform
distribution on `Fin c`, `Probability.uniformFinTree_generates`): the expected flips of the tree,
plus the expected cost of the branch taken. -/
noncomputable def exactWalkExpectedBits (R : SelfReducible enc W) (count : α → ℕ) :
    ℕ → α → ℕ → ℝ
  | 0, _, _ => 0
  | n + 1, y, c =>
    if hc : 0 < c then
      let c₁ := count (R.child y true)
      letI : NeZero c := ⟨Nat.ne_of_gt hc⟩
      (Probability.uniformFinTree c).expectedFlips.toReal +
        ∑ r : Fin c, (PMF.uniformOfFintype (Fin c) r).toReal *
          (if (r : ℕ) < c₁ then
            exactWalkExpectedBits R count n (R.child y true) c₁
          else
            exactWalkExpectedBits R count n (R.child y false) (c - c₁))
    else 0

/-- Expected fair-flip cost of `exactSample` with `Probability.uniformFinTree` draws. -/
noncomputable def exactSampleExpectedBits (R : SelfReducible enc W) (count : α → ℕ) (x : α) :
    ℝ :=
  let c := count x
  if 0 < c then R.exactWalkExpectedBits count (R.len x) x c else 0

/-- **Expected fair-flip bound for exact prefix sampling.** With `Probability.uniformFinTree`
draws (at most `2 * ⌈log₂ c⌉` expected flips each), `exactSample` consumes `0` flips when
`W x = ∅` and at most `R.len x * (R.len x + 1)` expected fair flips in general. -/
theorem exactSampleExpectedBits_le (R : SelfReducible enc W)
    {count : α → ℕ} {x : α}
    (hcount : ∀ z, (enc z).length ≤ (enc x).length → count z = (W z).card) :
    (W x = ∅ → R.exactSampleExpectedBits count x = 0) ∧
      R.exactSampleExpectedBits count x ≤ (R.len x : ℝ) * (R.len x + 1) := by
  have hcx : count x = (W x).card := hcount x (le_refl _)
  constructor
  · intro hempty
    simp [exactSampleExpectedBits, hcx, hempty]
  · have hwalk : ∀ n y, R.len y = n →
        (∀ z, (enc z).length ≤ (enc y).length → count z = (W z).card) →
        0 ≤ R.exactWalkExpectedBits count n y (W y).card ∧
          R.exactWalkExpectedBits count n y (W y).card ≤ (n : ℝ) * (n + 1) := by
      intro n
      induction n with
      | zero =>
        intro y _ _
        simp [exactWalkExpectedBits]
      | succ k ih =>
        intro y hlen hc_y
        have hy_pos : 0 < R.len y := by omega
        by_cases hpos : 0 < (W y).card
        · have : NeZero (W y).card := ⟨Nat.ne_of_gt hpos⟩
          have hc1_eq : count (R.child y true) = (W (R.child y true)).card :=
            hc_y _ (R.length_child_le y hy_pos true)
          have hsplit := R.card_eq_add hy_pos
          have hc0_eq : (W y).card - (W (R.child y true)).card = (W (R.child y false)).card := by
            omega
          obtain ⟨h1_nn, h1_le⟩ := ih (R.child y true)
            (by have := R.len_child y hy_pos true; omega)
            (fun z hz => hc_y z (hz.trans (R.length_child_le y hy_pos true)))
          obtain ⟨h0_nn, h0_le⟩ := ih (R.child y false)
            (by have := R.len_child y hy_pos false; omega)
            (fun z hz => hc_y z (hz.trans (R.length_child_le y hy_pos false)))
          rw [exactWalkExpectedBits, dite_eq_left hpos]
          dsimp only
          rw [hc1_eq, hc0_eq]
          constructor
          · refine add_nonneg ENNReal.toReal_nonneg (Finset.sum_nonneg fun r _ => ?_)
            refine mul_nonneg ENNReal.toReal_nonneg ?_
            split_ifs <;> assumption
          · have hcard_le : (W y).card ≤ 2 ^ (k + 1) := by
              simpa [hlen] using R.card_le_two_pow_len y
            have hclog : Nat.clog 2 (W y).card ≤ k + 1 :=
              (Nat.clog_le_iff_le_pow (by decide)).mpr hcard_le
            have hbits : (Probability.uniformFinTree (W y).card).expectedFlips.toReal ≤
                2 * ((k + 1 : ℕ) : ℝ) := by
              have h : (Probability.uniformFinTree (W y).card).expectedFlips ≤
                  ENNReal.ofReal (2 * ((k + 1 : ℕ) : ℝ)) := by
                refine (Probability.expectedFlips_uniformFinTree_le (W y).card).trans ?_
                rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
                  ENNReal.ofReal_natCast]
                gcongr
              exact ENNReal.toReal_le_of_le_ofReal (by positivity) h
            have hsum_le : (∑ r : Fin (W y).card,
                (PMF.uniformOfFintype (Fin (W y).card) r).toReal *
                  (if (r : ℕ) < (W (R.child y true)).card then
                    R.exactWalkExpectedBits count k (R.child y true) (W (R.child y true)).card
                  else
                    R.exactWalkExpectedBits count k (R.child y false)
                      (W (R.child y false)).card))
                ≤ (k : ℝ) * (k + 1) := by
              calc _ ≤ ∑ r : Fin (W y).card,
                    (PMF.uniformOfFintype (Fin (W y).card) r).toReal * ((k : ℝ) * (k + 1)) := by
                    refine Finset.sum_le_sum fun r _ => ?_
                    refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
                    split_ifs <;> assumption
                _ = (∑ r : Fin (W y).card, (PMF.uniformOfFintype (Fin (W y).card) r).toReal) *
                      ((k : ℝ) * (k + 1)) := (Finset.sum_mul _ _ _).symm
                _ = 1 * ((k : ℝ) * (k + 1)) := by
                    congr 1
                    simp only [PMF.uniformOfFintype_apply, Fintype.card_fin, Finset.sum_const,
                      Finset.card_univ, nsmul_eq_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
                    exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hpos))
                _ = (k : ℝ) * (k + 1) := one_mul _
            calc (Probability.uniformFinTree (W y).card).expectedFlips.toReal + _
                ≤ 2 * ((k + 1 : ℕ) : ℝ) + (k : ℝ) * (k + 1) := add_le_add hbits hsum_le
              _ = ((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1) := by push_cast; ring
        · rw [exactWalkExpectedBits, dite_eq_right hpos]
          exact ⟨le_refl _, by positivity⟩
    simp only [exactSampleExpectedBits, hcx]
    split_ifs with hpos
    · exact (hwalk (R.len x) x rfl hcount).2
    · positivity

/-! ### Bounded-trial `ProbComp` and `IsOraclePPTOn` conditional samplers -/

/-- Recursive bounded-trial conditional walk in `ProbComp`: each level draws from
`sampleUniformIntervalRetry c fuel` and aborts (`none`) only if all `fuel` trials reject. -/
noncomputable def boundedConditionalWalk (R : SelfReducible enc W) (count : α → ℕ) (fuel : ℕ) :
    ℕ → α → ℕ → ProbComp (Option (List Bool))
  | 0, y, c => pure (if 0 < c && decide ([] ∈ W y) then some [] else none)
  | n + 1, y, c =>
    if 0 < c then do
      let c₁ := count (R.child y true)
      match ← sampleUniformIntervalRetry c fuel with
      | none => pure none
      | some r =>
        if r < c₁ then
          (Option.map (true :: ·)) <$>
            boundedConditionalWalk R count fuel n (R.child y true) c₁
        else
          (Option.map (false :: ·)) <$>
            boundedConditionalWalk R count fuel n (R.child y false) (c - c₁)
    else pure none

/-- Advance a `ConditionalWalkState` given child count `c₁` and optional draw `ro`. -/
def advanceConditionalState (R : SelfReducible enc W) (s : ConditionalWalkState α)
    (c₁ : ℕ) (ro : Option ℕ) : ConditionalWalkState α :=
  match ro with
  | none => ⟨s.node, s.countVal, s.revBits, false⟩
  | some r =>
    if r < c₁ then ⟨R.child s.node true, c₁, true :: s.revBits, decide (0 < c₁)⟩
    else ⟨R.child s.node false, s.countVal - c₁, false :: s.revBits, decide (0 < s.countVal - c₁)⟩

/-- One step of the iterative bounded conditional walk. -/
noncomputable def conditionalWalkStep (R : SelfReducible enc W) (count : α → ℕ) (fuel : ℕ)
    (s : ConditionalWalkState α) : ProbComp (ConditionalWalkState α) :=
  if s.active && decide (0 < s.countVal) then
    let c₁ := count (R.child s.node true)
    R.advanceConditionalState s c₁ <$> sampleUniformIntervalRetry s.countVal fuel
  else pure s

/-- Read out the final witness from a finished `ConditionalWalkState`. -/
def finishConditionalWalk (_R : SelfReducible enc W) (s : ConditionalWalkState α) :
    Option (List Bool) :=
  if s.active && decide (0 < s.countVal) && decide ([] ∈ W s.node) then
    some s.revBits.reverse
  else none

/-- **Bounded conditional prefix sampler** on `(x, q)`: evaluates `count x`, then runs `R.len x`
iterative steps with per-step retry budget `fuel = q + R.len x`. -/
noncomputable def boundedConditionalSample (R : SelfReducible enc W) (count : α → ℕ)
    (x : α) (q : ℕ) : ProbComp (Option (List Bool)) :=
  let c := count x
  let fuel := q + R.len x
  R.finishConditionalWalk <$>
    OracleComp.iterate (R.len x) (R.conditionalWalkStep count fuel) ⟨x, c, [], decide (0 < c)⟩

private theorem conditionalWalkStep_inactive (R : SelfReducible enc W) (count : α → ℕ) (fuel : ℕ)
    (nd : α) (cv : ℕ) (rb : List Bool) :
    R.conditionalWalkStep count fuel ⟨nd, cv, rb, false⟩ = pure ⟨nd, cv, rb, false⟩ := rfl

private theorem iterate_conditionalWalkStep_inactive (R : SelfReducible enc W) (count : α → ℕ)
    (fuel n : ℕ) (nd : α) (cv : ℕ) (rb : List Bool) :
    OracleComp.iterate n (R.conditionalWalkStep count fuel) ⟨nd, cv, rb, false⟩ =
      pure ⟨nd, cv, rb, false⟩ :=
  OracleComp.iterate_eq_pure n _ _ (R.conditionalWalkStep_inactive count fuel nd cv rb)

/-- Iterative `conditionalWalkStep` agrees with recursive `boundedConditionalWalk`. -/
theorem map_finish_iterate_conditionalWalkStep (R : SelfReducible enc W) (count : α → ℕ)
    (fuel n : ℕ) (y : α) (c : ℕ) (rb : List Bool) :
    R.finishConditionalWalk <$>
      OracleComp.iterate n (R.conditionalWalkStep count fuel) ⟨y, c, rb, decide (0 < c)⟩ =
      Option.map (rb.reverse ++ ·) <$> R.boundedConditionalWalk count fuel n y c := by
  induction n generalizing y c rb with
  | zero =>
    by_cases hc : 0 < c <;> by_cases hnil : [] ∈ W y <;>
      simp [boundedConditionalWalk, finishConditionalWalk, hc, hnil, OracleComp.iterate]
  | succ k ih =>
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · simp [iterate_conditionalWalkStep_inactive, boundedConditionalWalk, finishConditionalWalk]
    · rw [OracleComp.iterate_succ_bind]
      simp only [boundedConditionalWalk, conditionalWalkStep, hc, decide_true, Bool.and_self,
        ↓reduceIte, bind_map_left, map_bind]
      refine congrArg (sampleUniformIntervalRetry c fuel >>= ·) (funext fun ro => ?_)
      cases ro with
      | none =>
        simp [advanceConditionalState, iterate_conditionalWalkStep_inactive, finishConditionalWalk]
      | some r =>
        by_cases hr : r < count (R.child y true)
        · simp only [advanceConditionalState, hr, ↓reduceIte]
          rw [ih, Functor.map_map]
          refine congrArg (· <$> _) (funext fun o => ?_)
          cases o <;> simp [List.reverse_cons, List.append_assoc]
        · simp only [advanceConditionalState, hr, ↓reduceIte]
          rw [ih, Functor.map_map]
          refine congrArg (· <$> _) (funext fun o => ?_)
          cases o <;> simp [List.reverse_cons, List.append_assoc]

theorem boundedConditionalSample_eq_walk (R : SelfReducible enc W) (count : α → ℕ) (x : α)
    (q : ℕ) :
    R.boundedConditionalSample count x q =
      R.boundedConditionalWalk count (q + R.len x) (R.len x) x (count x) := by
  rw [boundedConditionalSample, R.map_finish_iterate_conditionalWalkStep]
  simp only [List.reverse_nil, List.nil_append, Option.map_id_fun', id_map]

/-- Pointwise witness probability lower bound for `boundedConditionalWalk`. -/
theorem le_eval_boundedConditionalWalk_some (R : SelfReducible enc W) {count : α → ℕ}
    {fuel n : ℕ} {y : α} (hlen : R.len y = n)
    (hcount : ∀ z, (enc z).length ≤ (enc y).length → count z = (W z).card)
    {w : List Bool} (hw : w ∈ W y) :
    ENNReal.ofReal (((1 - (1 / 2 : ℝ) ^ fuel) ^ n) / (W y).card) ≤
      ProbComp.eval (R.boundedConditionalWalk count fuel n y (W y).card) (some w) := by
  have hpos : 0 < (W y).card := Finset.card_pos.mpr ⟨w, hw⟩
  induction n generalizing y w with
  | zero =>
    have hWy : W y = {[]} := R.eq_singleton_nil hlen hpos
    have hw_nil : w = [] := Finset.mem_singleton.mp (hWy ▸ hw)
    subst hw_nil
    simp [boundedConditionalWalk, hWy]
  | succ k ih =>
    have hy_pos : 0 < R.len y := by omega
    have hlen_w := R.length_eq y w hw
    cases w with
    | nil => simp at hlen_w; omega
    | cons b u =>
      have hc1_eq : count (R.child y true) = (W (R.child y true)).card :=
        hcount _ (R.length_child_le y hy_pos true)
      have hsplit := R.card_eq_add hy_pos
      have hc0_eq : (W y).card - (W (R.child y true)).card = (W (R.child y false)).card := by
        omega
      rw [boundedConditionalWalk, ite_eq_left hpos, ProbComp.eval_bind, PMF.bind_apply]
      rw [hc1_eq, hc0_eq]
      have hu_mem : u ∈ W (R.child y b) := (R.cons_mem_iff y hy_pos b u).mp hw
      have hcb_pos : 0 < (W (R.child y b)).card := Finset.card_pos.mpr ⟨u, hu_mem⟩
      have hsub := ih (y := R.child y b) (by have := R.len_child y hy_pos b; omega)
        (fun z hz => hcount z (hz.trans (R.length_child_le y hy_pos b))) hu_mem hcb_pos
      have h1_nn : 0 ≤ 1 - (1 / 2 : ℝ) ^ fuel := by
        have hpow : (1 / 2 : ℝ) ^ fuel ≤ 1 :=
          (pow_le_pow_left₀ (by positivity) (by norm_num : (1 / 2 : ℝ) ≤ 1) fuel).trans (by simp)
        linarith
      have hsplit_pow : ENNReal.ofReal ((1 - (1 / 2 : ℝ) ^ fuel) ^ (k + 1) / (W y).card) =
          (((W (R.child y b)).card : ℝ≥0∞) *
            ENNReal.ofReal ((1 - (1 / 2 : ℝ) ^ fuel) / (W y).card)) *
            ENNReal.ofReal ((1 - (1 / 2 : ℝ) ^ fuel) ^ k / (W (R.child y b)).card) := by
        have hcb_cast : ((W (R.child y b)).card : ℝ≥0∞) =
            ENNReal.ofReal ((W (R.child y b)).card : ℝ) :=
          (ENNReal.ofReal_natCast _).symm
        rw [hcb_cast, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have hcb_ne : ((W (R.child y b)).card : ℝ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (Nat.ne_of_gt hcb_pos)
        rw [pow_succ']
        field_simp
      have hdraw : ∀ r < (W y).card, ENNReal.ofReal ((1 - (1 / 2 : ℝ) ^ fuel) / (W y).card) ≤
          ProbComp.eval (sampleUniformIntervalRetry (W y).card fuel) (some r) := fun r hr => by
        rw [eval_sampleUniformIntervalRetry]
        exact le_eval_sampleUniformInterval_some hpos fuel hr
      cases b
      · set c₁ := (W (R.child y true)).card
        set c₀ := (W (R.child y false)).card
        refine le_trans ?_
          (sum_le_tsum ((Finset.Ico c₁ (W y).card).map ⟨some, Option.some_injective ℕ⟩))
        rw [Finset.sum_map]
        have hcongr : ∑ r ∈ Finset.Ico c₁ (W y).card,
            ProbComp.eval (sampleUniformIntervalRetry (W y).card fuel)
              ((⟨some, Option.some_injective ℕ⟩ : ℕ ↪ Option ℕ) r) *
              ProbComp.eval
                (match (⟨some, Option.some_injective ℕ⟩ : ℕ ↪ Option ℕ) r with
                | none => pure none
                | some r =>
                  if r < c₁ then
                    (Option.map (true :: ·)) <$>
                      R.boundedConditionalWalk count fuel k (R.child y true) c₁
                  else
                    (Option.map (false :: ·)) <$>
                      R.boundedConditionalWalk count fuel k (R.child y false) c₀)
                (some (false :: u)) =
            ∑ r ∈ Finset.Ico c₁ (W y).card,
              ProbComp.eval (sampleUniformIntervalRetry (W y).card fuel) (some r) *
                ProbComp.eval (R.boundedConditionalWalk count fuel k (R.child y false) c₀)
                  (some u) := by
          refine Finset.sum_congr rfl fun r hr => ?_
          dsimp only [Function.Embedding.coeFn_mk]
          have hnot_lt : ¬ r < c₁ := by rw [Finset.mem_Ico] at hr; omega
          rw [ite_eq_right hnot_lt, ProbComp.eval_map, pmf_map_option_map_cons_some]
        rw [hcongr, ← Finset.sum_mul, hsplit_pow]
        refine mul_le_mul' ?_ hsub
        have hcard_Ico : (Finset.Ico c₁ (W y).card).card = c₀ := by
          rw [Nat.card_Ico]
          omega
        rw [← hcard_Ico, ← nsmul_eq_mul, ← Finset.sum_const]
        exact Finset.sum_le_sum fun r hr => hdraw r (Finset.mem_Ico.mp hr).2
      · set c₁ := (W (R.child y true)).card
        have hc1_le : c₁ ≤ (W y).card := by omega
        refine le_trans ?_
          (sum_le_tsum ((Finset.range c₁).map ⟨some, Option.some_injective ℕ⟩))
        rw [Finset.sum_map]
        have hcongr : ∑ r ∈ Finset.range c₁,
            ProbComp.eval (sampleUniformIntervalRetry (W y).card fuel)
              ((⟨some, Option.some_injective ℕ⟩ : ℕ ↪ Option ℕ) r) *
              ProbComp.eval
                (match (⟨some, Option.some_injective ℕ⟩ : ℕ ↪ Option ℕ) r with
                | none => pure none
                | some r =>
                  if r < c₁ then
                    (Option.map (true :: ·)) <$>
                      R.boundedConditionalWalk count fuel k (R.child y true) c₁
                  else
                    (Option.map (false :: ·)) <$>
                      R.boundedConditionalWalk count fuel k (R.child y false)
                        ((W (R.child y false)).card))
                (some (true :: u)) =
            ∑ r ∈ Finset.range c₁,
              ProbComp.eval (sampleUniformIntervalRetry (W y).card fuel) (some r) *
                ProbComp.eval (R.boundedConditionalWalk count fuel k (R.child y true) c₁)
                  (some u) := by
          refine Finset.sum_congr rfl fun r hr => ?_
          dsimp only [Function.Embedding.coeFn_mk]
          have hlt_c1 : r < c₁ := Finset.mem_range.mp hr
          rw [ite_eq_left hlt_c1, ProbComp.eval_map, pmf_map_option_map_cons_some]
        rw [hcongr, ← Finset.sum_mul, hsplit_pow]
        refine mul_le_mul' ?_ hsub
        conv_lhs => rw [← Finset.card_range c₁, ← nsmul_eq_mul, ← Finset.sum_const]
        exact Finset.sum_le_sum fun r hr => hdraw r ((Finset.mem_range.mp hr).trans_le hc1_le)

/-- **Output-law accuracy of `boundedConditionalSample`.** Whenever `count` agrees with `(W ·).card`
on instances no longer than `x`, `boundedConditionalSample count x q` lies within total-variation
distance `(1 / 2) ^ q` of `uniformWitness (W x)`. -/
theorem closeTo_boundedConditionalSample (R : SelfReducible enc W) {count : α → ℕ} {x : α}
    (hcount : ∀ z, (enc z).length ≤ (enc x).length → count z = (W z).card) (q : ℕ) :
    CloseTo (ProbComp.eval (R.boundedConditionalSample count x q)) (uniformWitness (W x))
      (ENNReal.ofReal ((1 / 2 : ℝ) ^ q)) := by
  have hcx : count x = (W x).card := hcount x (le_refl _)
  rw [R.boundedConditionalSample_eq_walk, hcx]
  refine closeTo_uniformWitness_of_le (by positivity) (fun w hw => ?_) (fun hempty w => ?_)
  · set ℓ := R.len x
    have hδ0 : 0 ≤ (1 / 2 : ℝ) ^ (q + ℓ) := by positivity
    have hδ1 : (1 / 2 : ℝ) ^ (q + ℓ) ≤ 1 :=
      (pow_le_pow_left₀ (by positivity) (by norm_num : (1 / 2 : ℝ) ≤ 1) (q + ℓ)).trans (by simp)
    have hbern : 1 - (ℓ : ℝ) * (1 / 2 : ℝ) ^ (q + ℓ) ≤ (1 - (1 / 2 : ℝ) ^ (q + ℓ)) ^ ℓ := by
      have h := one_add_mul_le_pow (a := -(1 / 2 : ℝ) ^ (q + ℓ)) (by linarith) ℓ
      simpa only [mul_neg, ← sub_eq_add_neg] using h
    have hℓ_le : (ℓ : ℝ) ≤ 2 ^ ℓ := by exact_mod_cast Nat.lt_two_pow_self.le
    have hprod : (ℓ : ℝ) * (1 / 2 : ℝ) ^ (q + ℓ) ≤ (1 / 2 : ℝ) ^ q := by
      rw [pow_add, ← mul_assoc]
      have h1 : (ℓ : ℝ) * (1 / 2 : ℝ) ^ ℓ ≤ 1 := by
        rw [one_div, inv_pow, ← div_eq_mul_inv]
        exact (div_le_one (by positivity)).mpr hℓ_le
      calc (ℓ : ℝ) * (1 / 2 : ℝ) ^ q * (1 / 2 : ℝ) ^ ℓ
          = ((ℓ : ℝ) * (1 / 2 : ℝ) ^ ℓ) * (1 / 2 : ℝ) ^ q := by ring
        _ ≤ 1 * (1 / 2 : ℝ) ^ q := mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = (1 / 2 : ℝ) ^ q := one_mul _
    have hstep : ENNReal.ofReal ((1 - (1 / 2 : ℝ) ^ q) / (W x).card) ≤
        ENNReal.ofReal (((1 - (1 / 2 : ℝ) ^ (q + ℓ)) ^ ℓ) / (W x).card) := by
      refine ENNReal.ofReal_le_ofReal ?_
      exact div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
    exact hstep.trans (R.le_eval_boundedConditionalWalk_some rfl hcount hw)
  · rw [hempty, Finset.card_empty]
    cases hℓ : R.len x <;> simp [boundedConditionalWalk]

open ComputableInPolyTime in
private theorem computableInPolyTime_advanceConditionalState (R : SelfReducible enc W) :
    ComputableInPolyTime
      (fun x : (ConditionalWalkState α × ℕ) × Option ℕ =>
        R.advanceConditionalState x.1.1 x.1.2 x.2)
      (encPair (encPair (encConditionalWalkState enc) encNat) (encOption encNat))
      (encConditionalWalkState enc) := by
  have hst := (fst (encConditionalWalkState enc) encNat).comp
    (fst (encPair (encConditionalWalkState enc) encNat) (encOption encNat))
  have hc1 := (snd (encConditionalWalkState enc) encNat).comp
    (fst (encPair (encConditionalWalkState enc) encNat) (encOption encNat))
  have hro := snd (encPair (encConditionalWalkState enc) encNat) (encOption encNat)
  have hnd := encConditionalWalkState_node_polyTime hst
  have hcv := encConditionalWalkState_countVal_polyTime hst
  have hrb := encConditionalWalkState_revBits_polyTime hst
  have hsome_cond : ComputableInPolyTime
      (fun x : (ConditionalWalkState α × ℕ) × Option ℕ => decide (x.2.isSome = true))
      (encPair (encPair (encConditionalWalkState enc) encNat) (encOption encNat))
      encBool := by
    have hs : ComputableInPolyTime Option.isSome (encOption encNat) encBool := by fun_prop
    exact (hs.comp hro).of_enc_eq fun ⟨_, ro⟩ => by cases ro <;> rfl
  have hr_val : ComputableInPolyTime
      (fun x : (ConditionalWalkState α × ℕ) × Option ℕ => x.2.getD 0)
      (encPair (encPair (encConditionalWalkState enc) encNat) (encOption encNat))
      encNat := by
    have hg : ComputableInPolyTime (fun o : Option ℕ => o.getD 0) (encOption encNat) encNat := by
      fun_prop
    exact hg.comp hro
  have habort := encConditionalWalkState_mk_polyTime hnd hcv hrb (const false)
  have htrueBr := encConditionalWalkState_mk_polyTime
    (R.child_polytime.comp (hnd.prod (const true))) hc1
    ((ComputableInPolyTime.of_tidy
      (ComputableTidilyInPolyTime.bitsCons (.const true) hrb.tidy)))
    (binary_lt' (const 0) hc1)
  have hc0 := binary_sub' hcv hc1
  have hfalseBr := encConditionalWalkState_mk_polyTime
    (R.child_polytime.comp (hnd.prod (const false))) hc0
    ((ComputableInPolyTime.of_tidy
      (ComputableTidilyInPolyTime.bitsCons (.const false) hrb.tidy)))
    (binary_lt' (const 0) hc0)
  have hlt : ComputableInPolyTime
      (fun x : (ConditionalWalkState α × ℕ) × Option ℕ => decide (x.2.getD 0 < x.1.2))
      (encPair (encPair (encConditionalWalkState enc) encNat) (encOption encNat)) encBool :=
    binary_lt' hr_val hc1
  have hgo := ComputableInPolyTime.ite'
    (c := fun x : (ConditionalWalkState α × ℕ) × Option ℕ => x.2.getD 0 < x.1.2)
    hlt htrueBr hfalseBr
  exact (ComputableInPolyTime.ite'
    (c := fun x : (ConditionalWalkState α × ℕ) × Option ℕ => x.2.isSome = true)
    hsome_cond hgo habort).of_enc_eq fun ⟨⟨s, c₁⟩, ro⟩ => by
    cases ro with
    | none => rfl
    | some r =>
      dsimp only [advanceConditionalState, Option.isSome_some, Option.getD_some]
      by_cases h : r < c₁ <;> simp [h]

open ComputableInPolyTime in
private theorem computableInPolyTime_finishConditionalWalk (R : SelfReducible enc W) :
    ComputableInPolyTime R.finishConditionalWalk
      (encConditionalWalkState enc) (encOption encBits) := by
  have hcond_b := bool_and'
    (bool_and' (encConditionalWalkState_active_polyTime id')
      (binary_lt' (const 0) (encConditionalWalkState_countVal_polyTime id')))
    (R.nil_mem_polytime.comp (encConditionalWalkState_node_polyTime id'))
  have hcond : ComputableInPolyTime
      (fun s : ConditionalWalkState α =>
        decide ((s.active && decide (0 < s.countVal) && decide ([] ∈ W s.node)) = true))
      (encConditionalWalkState enc) encBool :=
    hcond_b.of_enc_eq fun s => by
      dsimp only [Function.comp]
      cases s.active && decide (0 < s.countVal) && decide ([] ∈ W s.node) <;> rfl
  have hyes : ComputableInPolyTime
      (fun s : ConditionalWalkState α => (some s.revBits.reverse : Option (List Bool)))
      (encConditionalWalkState enc) (encOption encBits) := by
    have hid : ComputableInPolyTime id
        (encConditionalWalkState enc) (encConditionalWalkState enc) := id'
    have hrev := (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.bitsReverse).comp
      (encConditionalWalkState_revBits_polyTime hid)
    fun_prop
  exact (ComputableInPolyTime.ite'
    (c := fun s : ConditionalWalkState α =>
      (s.active && decide (0 < s.countVal) && decide ([] ∈ W s.node)) = true)
    hcond hyes (const none)).of_enc_eq fun s => by
    unfold finishConditionalWalk
    cases s.active && decide (0 < s.countVal) && decide ([] ∈ W s.node) <;> rfl

open ComputableInPolyTime in
private theorem boundedConditionalSample_polyTime_helpers (R : SelfReducible enc W) :
    ComputableInPolyTime (fun p : α × ℕ => p.2 + R.len p.1) (encPair enc encUnary) encUnary ∧
    ComputableInPolyTime (fun pair : (α × ℕ) × ConditionalWalkState α =>
      pair.2.active && decide (0 < pair.2.countVal))
      (encPair (encPair enc encUnary) (encConditionalWalkState enc)) encBool ∧
    ComputableInPolyTime (fun pair : (α × ℕ) × ConditionalWalkState α => R.child pair.2.node true)
      (encPair (encPair enc encUnary) (encConditionalWalkState enc)) enc := by
  have hfuel : ComputableInPolyTime (fun p : α × ℕ => p.2 + R.len p.1)
      (encPair enc encUnary) encUnary :=
    unary_add' (snd enc encUnary) (R.len_polytime.comp (fst enc encUnary))
  have hst := snd (encPair enc encUnary) (encConditionalWalkState enc)
  have hnd := encConditionalWalkState_node_polyTime hst
  have hcv := encConditionalWalkState_countVal_polyTime hst
  have hact := encConditionalWalkState_active_polyTime hst
  have hcond : ComputableInPolyTime
      (fun pair : (α × ℕ) × ConditionalWalkState α =>
        pair.2.active && decide (0 < pair.2.countVal))
      (encPair (encPair enc encUnary) (encConditionalWalkState enc)) encBool :=
    bool_and' hact (binary_lt' (const 0) hcv)
  have hy1 := R.child_polytime.comp (hnd.prod (const true))
  exact ⟨hfuel, hcond, hy1⟩

open ComputableInPolyTime in
open ComputableInPolyTime in
open ComputableInPolyTime in
/-- **Strict PPT certificate for `boundedConditionalSample`** when `count` is polynomial-time. -/
theorem isPPTOn_boundedConditionalSample (R : SelfReducible enc W) {count : α → ℕ}
    (hcount : ComputableInPolyTime count enc encNat) :
    IsPPTOn (encPair enc encUnary) (encOption encBits)
      (Function.uncurry (R.boundedConditionalSample count)) := by
  obtain ⟨hfuel, hcond, hy1⟩ := R.boundedConditionalSample_polyTime_helpers
  have hst := snd (encPair enc encUnary) (encConditionalWalkState enc)
  have hstep : IsPPTOn (encPair (encPair enc encUnary) (encConditionalWalkState enc))
      (encConditionalWalkState enc)
      (fun pair => R.conditionalWalkStep count (pair.1.2 + R.len pair.1.1) pair.2) := by
    have hcv := encConditionalWalkState_countVal_polyTime hst
    have hc1 := hcount.comp hy1
    have hdraw := isPPTOn_sampleUniformIntervalRetry hcv
      (hfuel.comp (fst (encPair enc encUnary) (encConditionalWalkState enc)))
    have hadv : ComputableInPolyTime
        (fun x : ((α × ℕ) × ConditionalWalkState α) × Option ℕ =>
          R.advanceConditionalState x.1.2 (count (R.child x.1.2.node true)) x.2)
        (encPair (encPair (encPair enc encUnary) (encConditionalWalkState enc)) (encOption encNat))
        (encConditionalWalkState enc) := by
      have hp1 := fst (encPair (encPair enc encUnary) (encConditionalWalkState enc))
        (encOption encNat)
      exact (R.computableInPolyTime_advanceConditionalState).comp
        (((hst.comp hp1).prod (hc1.comp hp1)).prod
          (snd (encPair (encPair enc encUnary) (encConditionalWalkState enc)) (encOption encNat)))
    exact (IsPPTOn.cond' hcond (hdraw.map_with hadv) hst.isPPTOn).congr fun pair => by
      unfold conditionalWalkStep
      cases pair.2.active && decide (0 < pair.2.countVal) <;> rfl
  have hinit : ComputableInPolyTime
      (fun p : α × ℕ => ConditionalWalkState.mk p.1 (count p.1) [] (decide (0 < count p.1)))
      (encPair enc encUnary) (encConditionalWalkState enc) := by
    have hcx := hcount.comp (fst enc encUnary)
    exact encConditionalWalkState_mk_polyTime (fst enc encUnary) hcx (const [])
      (binary_lt' (const 0) hcx)
  obtain ⟨tC, _, htC, _, hmC⟩ := hcount
  obtain ⟨cC, dC, hlenC⟩ := polynomiallyBounded_iff_le.mp htC
  obtain ⟨tL, _, htL, _, hmL⟩ := R.len_polytime
  obtain ⟨cL, dL, hlenL⟩ := polynomiallyBounded_iff_le.mp htL
  have hcount_loop : ComputableInPolyTime (fun p : α × ℕ => R.len p.1)
      (encPair enc encUnary) encUnary := R.len_polytime.comp (fst enc encUnary)
  have hpx_cert : ComputableInPolyTime (fun p : α × ℕ => p.1) (encPair enc encUnary) enc :=
    fst enc encUnary
  have hsize : PolyBounded (fun p : α × ℕ => (encPair enc encUnary p).length)
      (fun p => 16 * ((enc p.1).length +
        cC * ((enc p.1).length + 1) ^ dC +
        cL * ((enc p.1).length + 1) ^ dL + 4)) := by
    growth_poly
  have hit := IsPPTOn.iterateWith_spec' (input := encPair enc encUnary)
    (stateEncoding := encConditionalWalkState enc)
    (count := fun p => R.len p.1)
    (initial := fun p => ConditionalWalkState.mk p.1 (count p.1) [] (decide (0 < count p.1)))
    (step := fun p => R.conditionalWalkStep count (p.2 + R.len p.1))
    hcount_loop hinit hstep
    (fun p i st => (enc st.node).length ≤ (enc p.1).length ∧
      st.revBits.length ≤ i ∧
      (encNat st.countVal).length ≤ cC * ((enc p.1).length + 1) ^ dC ∧
      (st.active = true → 0 < st.countVal ∧ st.revBits.length = i ∧
        R.len st.node + i = R.len p.1))
    (fun p => ⟨le_refl _, le_refl _, (hmC.length_le p.1).trans (hlenC _),
      fun hact => ⟨of_decide_eq_true hact, rfl, Nat.add_zero _⟩⟩)
    (fun p i st hi ⟨hnd_le, hrb_le, hcv_le, hact_inv⟩ next hnext => by
      unfold conditionalWalkStep at hnext
      by_cases hgo : (st.active && decide (0 < st.countVal)) = true
      · have hst_act : st.active = true := (Bool.and_eq_true _ _).mp hgo |>.1
        obtain ⟨_, hrb_eq, hlen_sum⟩ := hact_inv hst_act
        have hlen_pos : 0 < R.len st.node := by omega
        rw [ite_eq_left hgo, ProbComp.eval_map, PMF.mem_support_map_iff] at hnext
        obtain ⟨ro, _, rfl⟩ := hnext
        cases ro with
        | none =>
          exact ⟨hnd_le, hrb_le.trans (Nat.le_succ i), hcv_le, fun h => Bool.noConfusion h⟩
        | some r =>
          by_cases hr : r < count (R.child st.node true)
          · simp only [advanceConditionalState, hr, ↓reduceIte]
            have hch_len := (R.length_child_le st.node hlen_pos true).trans hnd_le
            refine ⟨hch_len, by simp [hrb_eq], ?_, fun hact' => ?_⟩
            · exact (hmC.length_le _).trans ((hlenC _).trans
                (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.succ_le_succ hch_len) _)))
            · have := R.len_child st.node hlen_pos true
              exact ⟨of_decide_eq_true hact', by simp [hrb_eq], by omega⟩
          · simp only [advanceConditionalState, hr, ↓reduceIte]
            have hch_len := (R.length_child_le st.node hlen_pos false).trans hnd_le
            refine ⟨hch_len, by simp [hrb_eq], ?_, fun hact' => ?_⟩
            · have hsub_le : (encNat (st.countVal - count (R.child st.node true))).length ≤
                  (encNat st.countVal).length := by
                simp only [encNat_apply, Nat.size_eq_bits_len]
                exact Nat.size_le_size (Nat.sub_le _ _)
              exact hsub_le.trans hcv_le
            · have := R.len_child st.node hlen_pos false
              exact ⟨of_decide_eq_true hact', by simp [hrb_eq], by omega⟩
      · have hnot_act : st.active = false := by
          cases h : st.active
          · rfl
          · exfalso
            have hc_pos := (hact_inv h).1
            simp [h, hc_pos] at hgo
        rw [ite_eq_right hgo, ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hnext
        subst hnext
        exact ⟨hnd_le, hrb_le.trans (Nat.le_succ i), hcv_le,
          fun h => Bool.noConfusion (hnot_act.symm.trans h)⟩)
    hsize
    (fun p i st hi ⟨hnd_le, hrb_le, hcv_le, _⟩ => by
      have hrb_max : st.revBits.length ≤ cL * ((enc p.1).length + 1) ^ dL := by
        have h1 : R.len p.1 = (encUnary (R.len p.1)).length := by simp
        have h2 := (hmL.length_le p.1).trans (hlenL _)
        omega
      simp only [encConditionalWalkState_apply]
      enc_len)
  exact (hit.1.map R.computableInPolyTime_finishConditionalWalk).congr fun ⟨_, _⟩ => rfl

/-- **Exact polynomial-time counting gives an FPAUS** via prefix conditional sampling. -/
theorem isFPAUS_boundedConditionalSample (R : SelfReducible enc W) {count : α → ℕ}
    (hcount_poly : ComputableInPolyTime count enc encNat)
    (hcount_eq : ∀ x, count x = (W x).card) :
    IsFPAUS enc W (R.boundedConditionalSample count) :=
  ⟨R.isPPTOn_boundedConditionalSample hcount_poly,
    fun _ q => R.closeTo_boundedConditionalSample (fun z _ => hcount_eq z) q⟩

theorem mem_FPAUS_of_exact_polyTime_count (R : SelfReducible enc W) {count : α → ℕ}
    (hcount_poly : ComputableInPolyTime count enc encNat)
    (hcount_eq : ∀ x, count x = (W x).card) :
    W ∈ FPAUS enc :=
  ⟨R.boundedConditionalSample count, R.isFPAUS_boundedConditionalSample hcount_poly hcount_eq⟩

/-! ### Oracle-counter lift (`IsOraclePPTOn`) -/

/-- One step of the oracle-backed bounded conditional walk: evaluate
`countProg (R.child s.node true)` via the external oracle and draw from
`sampleUniformIntervalRetry s.countVal fuel` via private coins. -/
noncomputable def conditionalWalkOracleStep (R : SelfReducible enc W)
    (countProg : α → WordQueryComp Unit ℕ) (fuel : ℕ)
    (s : ConditionalWalkState α) : WordOracleComp Unit (ConditionalWalkState α) :=
  if s.active && decide (0 < s.countVal) then do
    let c₁ ← OracleComp.interpret ProbOracleComp.query (countProg (R.child s.node true))
    let ro ← ProbOracleComp.sample (sampleUniformIntervalRetry s.countVal fuel)
    return R.advanceConditionalState s c₁ ro
  else pure s

/-- **Oracle-backed bounded conditional prefix sampler**: queries `countProg x` at the root and
iterates `conditionalWalkOracleStep` for `R.len x` steps with per-step budget `q + R.len x`. -/
noncomputable def boundedConditionalOracleSample (R : SelfReducible enc W)
    (countProg : α → WordQueryComp Unit ℕ) (x : α) (q : ℕ) :
    WordOracleComp Unit (Option (List Bool)) := do
  let c ← OracleComp.interpret ProbOracleComp.query (countProg x)
  let fuel := q + R.len x
  R.finishConditionalWalk <$>
    OracleComp.iterate (R.len x) (R.conditionalWalkOracleStep countProg fuel)
      ⟨x, c, [], decide (0 < c)⟩

private theorem interpret_sumHandler_query_pure {β : Type}
    (answer : Unit × List Bool → List Bool) (w : WordQueryComp Unit β) :
    OracleComp.interpret (OracleComp.sumHandler ProbComp.unifFin (fun req => pure (answer req)))
      (OracleComp.interpret ProbOracleComp.query w) =
      pure (OracleComp.interpret (m := Id) answer w) := by
  induction w with
  | pure a => rfl
  | liftBind req cont ih =>
    change OracleComp.interpret
        (OracleComp.sumHandler ProbComp.unifFin (fun r => pure (answer r)))
        (ProbOracleComp.query req >>= fun a => OracleComp.interpret ProbOracleComp.query (cont a)) =
      pure (OracleComp.interpret (m := Id) answer (cont (answer req)))
    rw [OracleComp.interpret_bind, ProbOracleComp.interpret_query, pure_bind, ih]

/-- Interpreting `boundedConditionalOracleSample` against a deterministic word handler `answer`
produces the exact same `ProbComp` as `boundedConditionalSample` with counter
`y ↦ OracleComp.interpret (m := Id) answer (countProg y)`. -/
theorem interpret_boundedConditionalOracleSample (R : SelfReducible enc W)
    (answer : Unit × List Bool → List Bool) (countProg : α → WordQueryComp Unit ℕ)
    (x : α) (q : ℕ) :
    OracleComp.interpret (OracleComp.sumHandler ProbComp.unifFin (fun req => pure (answer req)))
        (R.boundedConditionalOracleSample countProg x q) =
      R.boundedConditionalSample
        (fun y => OracleComp.interpret (m := Id) answer (countProg y)) x q := by
  let handler := OracleComp.sumHandler ProbComp.unifFin
    (fun req : Unit × List Bool => (pure (answer req) : ProbComp (List Bool)))
  let count : α → ℕ := fun y => OracleComp.interpret (m := Id) answer (countProg y)
  have hstep : ∀ fuel s,
      OracleComp.interpret handler (R.conditionalWalkOracleStep countProg fuel s) =
        R.conditionalWalkStep count fuel s := by
    intro fuel s
    unfold conditionalWalkOracleStep conditionalWalkStep
    split_ifs
    · rw [OracleComp.interpret_bind, interpret_sumHandler_query_pure, pure_bind,
        OracleComp.interpret_bind]
      simp only [handler, ProbOracleComp.interpret_sample,
        OracleComp.interpret_pure, bind_pure_comp]
      exact congrArg _ (ProbComp.interpret_unifFin _)
    · rfl
  simp only [boundedConditionalOracleSample, boundedConditionalSample]
  rw [OracleComp.interpret_bind, interpret_sumHandler_query_pure, pure_bind,
    OracleComp.interpret_map, OracleComp.interpret_iterate]
  dsimp only [handler] at hstep
  simp_rw [hstep]
  rfl

/-- Evaluating `boundedConditionalOracleSample` against `languageOracle A` agrees in `PMF` with
`ProbComp.eval (R.boundedConditionalSample count x q)`, hence lies within `(1 / 2) ^ q` of
`uniformWitness (W x)` whenever `countProg` computes `(W ·).card` relative to `A` on instances no
longer than `x`. -/
theorem closeTo_boundedConditionalOracleSample (R : SelfReducible enc W) (A : Set (List Bool))
    (countProg : α → WordQueryComp Unit ℕ) {x : α}
    (hcount : ∀ z, (enc z).length ≤ (enc x).length →
      OracleComp.interpret (m := Id) (languageOracle A) (countProg z) = (W z).card)
    (q : ℕ) :
    CloseTo
      (OracleComp.interpret
        (OracleComp.sumHandler ProbComp.unifOracle
          (fun req => PMF.pure (languageOracle A req)))
        (R.boundedConditionalOracleSample countProg x q))
      (uniformWitness (W x))
      (ENNReal.ofReal ((1 / 2 : ℝ) ^ q)) := by
  have heval : OracleComp.interpret
      (OracleComp.sumHandler ProbComp.unifOracle
        (fun req => PMF.pure (languageOracle A req)))
      (R.boundedConditionalOracleSample countProg x q) =
      ProbComp.eval (R.boundedConditionalSample
        (fun y => OracleComp.interpret (m := Id) (languageOracle A) (countProg y)) x q) := by
    have h1 := ProbOracleComp.eval_interpret
      (fun req => (pure (languageOracle A req) : ProbComp (List Bool)))
      (R.boundedConditionalOracleSample countProg x q)
    simp only [ProbComp.eval_pure] at h1
    rw [← h1, R.interpret_boundedConditionalOracleSample]
  rw [heval]
  exact R.closeTo_boundedConditionalSample hcount q

open ComputableInPolyTime in
/-- **Strict oracle PPT certificate for `boundedConditionalOracleSample`** from any strict oracle
PPT counter program `countProg`. -/
theorem isOraclePPTOn_boundedConditionalOracleSample (R : SelfReducible enc W)
    {countProg : α → WordQueryComp Unit ℕ}
    (hcount : IsOraclePPTOn enc encNat
      (fun y => OracleComp.interpret ProbOracleComp.query (countProg y))) :
    IsOraclePPTOn (encPair enc encUnary) (encOption encBits)
      (Function.uncurry (R.boundedConditionalOracleSample countProg)) := by
  obtain ⟨cC, dC, hlen_run⟩ := hcount.length_le
  have hcount_len : ∀ y, ∀ res ∈ OracleComp.support
      (OracleComp.interpret ProbOracleComp.query (countProg y)),
      (encNat res).length ≤ cC * ((enc y).length + 1) ^ dC := by
    intro y res hres
    obtain ⟨State, oracle, s, s', hrun⟩ :=
      (ProbOracleComp.mem_support_iff_exists (hne := fun _ => ⟨[]⟩)).mp hres
    exact hlen_run y State oracle s s' res hrun
  obtain ⟨tL, _, htL, _, hmL⟩ := R.len_polytime
  obtain ⟨cL, dL, hlenL⟩ := polynomiallyBounded_iff_le.mp htL
  obtain ⟨hfuel, hcond, hy1⟩ := R.boundedConditionalSample_polyTime_helpers
  have hstep_oracle : IsOraclePPTOn (encPair (encPair enc encUnary) (encConditionalWalkState enc))
      (encConditionalWalkState enc)
      (fun pair => R.conditionalWalkOracleStep countProg
        (pair.1.2 + R.len pair.1.1) pair.2) := by
    have hst_o := snd (encPair enc encUnary) (encConditionalWalkState enc)
    have hcv_o := encConditionalWalkState_countVal_polyTime hst_o
    have hc1 : IsOraclePPTOn (encPair (encPair enc encUnary) (encConditionalWalkState enc)) encNat
        (fun pair => OracleComp.interpret ProbOracleComp.query
          (countProg (R.child pair.2.node true))) :=
      hcount.preprocess' hy1
    have hp1 := fst (encPair (encPair enc encUnary) (encConditionalWalkState enc)) encNat
    have hdraw_ppt := isPPTOn_sampleUniformIntervalRetry (hcv_o.comp hp1)
      ((hfuel.comp (fst (encPair enc encUnary) (encConditionalWalkState enc))).comp hp1)
    have hdraw_oracle : IsOraclePPTOn (Operation := Unit)
        (encPair (encPair (encPair enc encUnary) (encConditionalWalkState enc)) encNat)
        (encConditionalWalkState enc)
        (fun pc : ((α × ℕ) × ConditionalWalkState α) × ℕ => do
          let ro ← ProbOracleComp.sample
            (sampleUniformIntervalRetry pc.1.2.countVal (pc.1.1.2 + R.len pc.1.1.1))
          pure (R.advanceConditionalState pc.1.2 pc.2 ro)) := by
      have hp2 := fst
        (encPair (encPair (encPair enc encUnary) (encConditionalWalkState enc)) encNat)
        (encOption encNat)
      have hsnd1 := snd (encPair (encPair enc encUnary) (encConditionalWalkState enc)) encNat
      have hadv := (R.computableInPolyTime_advanceConditionalState).comp
        ((((hst_o.comp hp1).comp hp2).prod (hsnd1.comp hp2)).prod
          (snd (encPair (encPair (encPair enc encUnary) (encConditionalWalkState enc)) encNat)
            (encOption encNat)))
      exact (((hdraw_ppt.isOraclePPTOn (Operation := Unit)).map_with'
        (f := fun (pc : ((α × ℕ) × ConditionalWalkState α) × ℕ) (ro : Option ℕ) =>
          R.advanceConditionalState pc.1.2 pc.2 ro) hadv).congr fun pc State oracle s => by
        dsimp only [Function.comp]
        rw [← bind_pure_comp])
    have hyes := hc1.bind_with
      (second := fun (pair : (α × ℕ) × ConditionalWalkState α) (c₁ : ℕ) => do
        let ro ← ProbOracleComp.sample
          (sampleUniformIntervalRetry pair.2.countVal (pair.1.2 + R.len pair.1.1))
        pure (R.advanceConditionalState pair.2 c₁ ro))
      hdraw_oracle
    exact (IsOraclePPTOn.cond' hcond hyes hst_o.isOraclePPTOn).congr fun pair State oracle s => by
      unfold conditionalWalkOracleStep
      cases pair.2.active && decide (0 < pair.2.countVal) <;> rfl
  -- Run the `R.len x`-step loop given `(p, c)` where `c` is the root count
  have hbody : IsOraclePPTOn (encPair (encPair enc encUnary) encNat) (encOption encBits)
      (fun pc : (α × ℕ) × ℕ =>
        R.finishConditionalWalk <$>
          OracleComp.iterate (R.len pc.1.1)
            (R.conditionalWalkOracleStep countProg (pc.1.2 + R.len pc.1.1))
            ⟨pc.1.1, pc.2, [], decide (0 < pc.2)⟩) := by
    have hp_fst := fst (encPair enc encUnary) encNat
    have hp_snd := snd (encPair enc encUnary) encNat
    have hcount_loop : ComputableInPolyTime (fun pc : (α × ℕ) × ℕ => R.len pc.1.1)
        (encPair (encPair enc encUnary) encNat) encUnary :=
      R.len_polytime.comp ((fst enc encUnary).comp hp_fst)
    have hinit : ComputableInPolyTime
        (fun pc : (α × ℕ) × ℕ =>
          ConditionalWalkState.mk pc.1.1 pc.2 [] (decide (0 < pc.2)))
        (encPair (encPair enc encUnary) encNat) (encConditionalWalkState enc) :=
      encConditionalWalkState_mk_polyTime ((fst enc encUnary).comp hp_fst) hp_snd (const [])
        (binary_lt' (const 0) hp_snd)
    have hstep_pc : IsOraclePPTOn
        (encPair (encPair (encPair enc encUnary) encNat) (encConditionalWalkState enc))
        (encConditionalWalkState enc)
        (fun pair => R.conditionalWalkOracleStep countProg
          (pair.1.1.2 + R.len pair.1.1.1) pair.2) := by
      have hprep : ComputableInPolyTime
          (fun pair : ((α × ℕ) × ℕ) × ConditionalWalkState α => (pair.1.1, pair.2))
          (encPair (encPair (encPair enc encUnary) encNat) (encConditionalWalkState enc))
          (encPair (encPair enc encUnary) (encConditionalWalkState enc)) :=
        (hp_fst.comp (fst _ _)).prod (snd _ _)
      exact hstep_oracle.preprocess' hprep
    have hx_cert : ComputableInPolyTime (fun pc : (α × ℕ) × ℕ => pc.1.1)
        (encPair (encPair enc encUnary) encNat) enc :=
      (fst enc encUnary).comp hp_fst
    have hsize_pc : PolyBounded
        (fun pc : (α × ℕ) × ℕ => (encPair (encPair enc encUnary) encNat pc).length)
        (fun pc => 16 * ((enc pc.1.1).length + (encNat pc.2).length +
          cC * ((enc pc.1.1).length + 1) ^ dC +
          cL * ((enc pc.1.1).length + 1) ^ dL + 4)) := by
      growth_poly
    have hit := IsOraclePPTOn.iterateWith_spec'
      (input := encPair (encPair enc encUnary) encNat)
      (stateEncoding := encConditionalWalkState enc)
      (count := fun pc => R.len pc.1.1)
      (initial := fun pc => ConditionalWalkState.mk pc.1.1 pc.2 [] (decide (0 < pc.2)))
      (step := fun pc => R.conditionalWalkOracleStep countProg (pc.1.2 + R.len pc.1.1))
      hcount_loop hinit hstep_pc
      (fun pc i st => (enc st.node).length ≤ (enc pc.1.1).length ∧
        st.revBits.length ≤ i ∧
        (encNat st.countVal).length ≤
          max (encNat pc.2).length (cC * ((enc pc.1.1).length + 1) ^ dC) ∧
        (st.active = true → 0 < st.countVal ∧ st.revBits.length = i ∧
          R.len st.node + i = R.len pc.1.1))
      (fun pc => ⟨le_refl _, le_refl _, le_max_left _ _,
        fun hact => ⟨of_decide_eq_true hact, rfl, Nat.add_zero _⟩⟩)
      (fun pc i st hi ⟨hnd_le, hrb_le, hcv_le, hact_inv⟩ next hnext => by
        unfold conditionalWalkOracleStep at hnext
        by_cases hgo : (st.active && decide (0 < st.countVal)) = true
        · have hst_act : st.active = true := (Bool.and_eq_true _ _).mp hgo |>.1
          obtain ⟨_, hrb_eq, hlen_sum⟩ := hact_inv hst_act
          have hlen_pos : 0 < R.len st.node := by omega
          rw [ite_eq_left hgo] at hnext
          obtain ⟨c₁, hc₁_sup, hnext'⟩ := OracleComp.mem_supportWith_bind_iff.mp hnext
          obtain ⟨ro, _, hnext''⟩ := OracleComp.mem_supportWith_bind_iff.mp hnext'
          have hnext_eq := OracleComp.eq_of_mem_supportWith_pure hnext''
          subst hnext_eq
          cases ro with
          | none =>
            exact ⟨hnd_le, hrb_le.trans (Nat.le_succ i), hcv_le, fun h => Bool.noConfusion h⟩
          | some r =>
            by_cases hr : r < c₁
            · simp only [advanceConditionalState, hr, ↓reduceIte]
              have hch_len := (R.length_child_le st.node hlen_pos true).trans hnd_le
              refine ⟨hch_len, by simp [hrb_eq], ?_, fun hact' => ?_⟩
              · refine le_max_of_le_right ?_
                exact (hcount_len _ c₁ hc₁_sup).trans
                  (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.succ_le_succ hch_len) _))
              · have := R.len_child st.node hlen_pos true
                exact ⟨of_decide_eq_true hact', by simp [hrb_eq], by omega⟩
            · simp only [advanceConditionalState, hr, ↓reduceIte]
              have hch_len := (R.length_child_le st.node hlen_pos false).trans hnd_le
              refine ⟨hch_len, by simp [hrb_eq], ?_, fun hact' => ?_⟩
              · have hsub_le : (encNat (st.countVal - c₁)).length ≤
                    (encNat st.countVal).length := by
                  simp only [encNat_apply, Nat.size_eq_bits_len]
                  exact Nat.size_le_size (Nat.sub_le _ _)
                exact hsub_le.trans hcv_le
              · have := R.len_child st.node hlen_pos false
                exact ⟨of_decide_eq_true hact', by simp [hrb_eq], by omega⟩
        · have hnot_act : st.active = false := by
            cases h : st.active
            · rfl
            · exfalso
              have hc_pos := (hact_inv h).1
              simp [h, hc_pos] at hgo
          rw [ite_eq_right hgo] at hnext
          have hnext_eq := OracleComp.eq_of_mem_supportWith_pure hnext
          subst hnext_eq
          exact ⟨hnd_le, hrb_le.trans (Nat.le_succ i), hcv_le,
            fun h => Bool.noConfusion (hnot_act.symm.trans h)⟩)
      hsize_pc
      (fun pc i st hi ⟨hnd_le, hrb_le, hcv_le, _⟩ => by
        have hcv_sum : (encNat st.countVal).length ≤
            (encNat pc.2).length + cC * ((enc pc.1.1).length + 1) ^ dC := by omega
        have hrb_max : st.revBits.length ≤ cL * ((enc pc.1.1).length + 1) ^ dL := by
          have h1 : R.len pc.1.1 = (encUnary (R.len pc.1.1)).length := by simp
          have h2 := (hmL.length_le pc.1.1).trans (hlenL _)
          omega
        simp only [encConditionalWalkState_apply]
        enc_len)
    exact hit.1.map' R.computableInPolyTime_finishConditionalWalk
  have hroot : IsOraclePPTOn (encPair enc encUnary) encNat
      (fun p : α × ℕ => OracleComp.interpret ProbOracleComp.query (countProg p.1)) :=
    hcount.preprocess' (fst enc encUnary)
  exact (hroot.bind_with (second := fun (p : α × ℕ) (c : ℕ) =>
      R.finishConditionalWalk <$>
        OracleComp.iterate (R.len p.1)
          (R.conditionalWalkOracleStep countProg (p.2 + R.len p.1))
          ⟨p.1, c, [], decide (0 < c)⟩) hbody).congr fun ⟨_, _⟩ _ _ _ => rfl

/-- **Exact oracle counting gives a strict oracle-PPT almost-uniform sampler.** Whenever `count`
computes `(W ·).card` in polynomial time relative to `A` (`ComputableInPolyTimeWithOracle A`),
there is a `WordOracleComp Unit` sampler that is `IsOraclePPTOn` and whose evaluation against
`languageOracle A` lies within total-variation distance `(1 / 2) ^ q` of `uniformWitness (W x)`. -/
theorem exists_oraclePPTSampler_of_oracle_count (R : SelfReducible enc W) (A : Set (List Bool))
    {count : α → ℕ}
    (hcount_oracle : ComputableInPolyTimeWithOracle A count enc encNat)
    (hcount_eq : ∀ x, count x = (W x).card) :
    ∃ sampler : α → ℕ → WordOracleComp Unit (Option (List Bool)),
      IsOraclePPTOn (encPair enc encUnary) (encOption encBits) (Function.uncurry sampler) ∧
      ∀ x q, CloseTo
        (OracleComp.interpret
          (OracleComp.sumHandler ProbComp.unifOracle
            (fun req => PMF.pure (languageOracle A req)))
          (sampler x q))
        (uniformWitness (W x))
        (ENNReal.ofReal ((1 / 2 : ℝ) ^ q)) := by
  obtain ⟨countProg, hcert, heq⟩ := hcount_oracle
  exact ⟨R.boundedConditionalOracleSample countProg,
    R.isOraclePPTOn_boundedConditionalOracleSample hcert,
    fun x q => R.closeTo_boundedConditionalOracleSample A countProg
      (fun z _ => (heq z).trans (hcount_eq z)) q⟩

end SelfReducible

end Cslib.Complexity
