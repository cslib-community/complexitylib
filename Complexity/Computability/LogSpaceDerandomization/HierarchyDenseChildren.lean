/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Computability.LogSpaceDerandomization.HierarchyCanonicalTargets
public import Complexity.Foundations.Probability.CoordinateFactorization

/-!
# Genuine dense children on the shared hierarchy environment

The deterministic base matrix and its actual dense preparation define the direct and
source-reset right children. Their joint source/usage normalizer integrates every source
spectator. Consequently the right value at `(z,y)` depends only on the terminal frame,
even though its request resets the complete source tuple to the midpoint channel.
These identities preserve the raw ranks, usage rate and inherited copy suffixes.
-/

public section
open Finset Cslib Cslib.Probability
open scoped BigOperators
noncomputable section

namespace Matrix.HierarchyParams.H4RankEnvironment
attribute [local instance] Classical.propDecidable
variable {P J : ℕ} [Fact P.Prime] {V : Type} [Fintype V]
  (D : ZMod P) (ident : V → ZMod P)
  {n : ℕ} (r : HierarchyTask.Request n (Fin J) (ZMod P)) (hr : Admissible r)

/-- Genuine dense preparation from the deterministic hierarchy base, on its actual rank
frame. It is independent of the sampled source before taking the joint normalizer. -/
@[expose] def densePreparation (h ρ : ℝ → ℝ) (K : ℕ) (C : Matrix V V ℝ)
    (σ : Environment P J) : Matrix V V ℝ :=
  DenseRowRecipe.preparation h ρ K r.terminal.rate
    (splitTerminal D ident r) C (σ r.terminal.role)

/-- The actual dense joint normalizer integrates the source, including every spectator.
Only nonemptiness of the actual source slice is used; no source seed is frozen. -/
theorem dense_normalizer (h ρ : ℝ → ℝ) (K : ℕ) (C : Matrix V V ℝ) (x y : V)
    (hx : ({a | splitSource D ident r hr a x} : Finset _).Nonempty) :
    rowSliceMean (fun σ v => r.source.retains (channels D) σ (ident v))
      (fun σ v => r.usage.retains (channels D) σ (ident v))
      (densePreparation D ident r h ρ K C) x y =
    atomNormalizer (splitTerminal D ident r) (splitUsage D ident r) h ρ K
      r.terminal.rate C x y := by
  rw [← normalizer_full D ident r hr]
  change (𝔼 p ∈ ({a | splitSource D ident r hr a x} : Finset _) ×ˢ
    ({a | splitUsage D ident r a y} : Finset _),
    DenseRowRecipe.preparation h ρ K r.terminal.rate (splitTerminal D ident r) C
      (((Equiv.piSplitAt r.terminal.role (fun _ : Fin J => FrameChannel P 4 1)).symm
        (p.2, p.1)) r.terminal.role) x y) = _
  simp only [Equiv.piSplitAt, Equiv.coe_fn_symm_mk, ↓reduceDIte]
  rw [expect_product]
  simpa only [DenseRowRecipe.preparation, atomNormalizer] using
    (expect_const hx (atomNormalizer (splitTerminal D ident r) (splitUsage D ident r)
      h ρ K r.terminal.rate C x y))

/-- Actual normalized dense request with deterministic raw base and genuine preparation.
This is the existing request evaluator, rather than a child with a prescribed mean. -/
@[expose] def denseChild (cutoff h ρ : ℝ → ℝ) (K : ℕ) (C : Matrix V V ℝ)
    (σ : Environment P J) : Matrix V V ℝ :=
  normalizedRequest D ident r cutoff ρ K (fun _ => C)
    (densePreparation D ident r h ρ K C) σ

/-- Source release is pointwise after the genuine joint normalization is identified.
The right child keeps exactly its terminal rank and usage predicates and suffix. -/
theorem denseChild_eq (cutoff h ρ : ℝ → ℝ) (K : ℕ) (C : Matrix V V ℝ)
    (σ : Environment P J) (x y : V)
    (hx : ({a | splitSource D ident r hr a x} : Finset _).Nonempty) :
    denseChild D ident r cutoff h ρ K C σ x y =
      denseAtom (splitTerminal D ident r) (splitUsage D ident r)
        cutoff h ρ K r.terminal.rate C (σ r.terminal.role) x y := by
  rw [denseChild, normalizedRequest_formula D ident r hr,
    dense_normalizer D ident r hr h ρ K C x y hx]
  simp only [denseAtom, splitTerminal, splitUsage, coordinate,
    CorrectionRowTask.Channel.retains, channels, hr.2.1]
  split_ifs <;> simp_all

/-- In particular source-reset and free spectator coordinates cannot affect a genuine
dense right child when its terminal frame is unchanged. -/
theorem denseChild_terminal (cutoff h ρ : ℝ → ℝ) (K : ℕ) (C : Matrix V V ℝ)
    (σ τ : Environment P J) (ht : σ r.terminal.role = τ r.terminal.role) (x y : V)
    (hx : ({a | splitSource D ident r hr a x} : Finset _).Nonempty) :
    denseChild D ident r cutoff h ρ K C σ x y =
      denseChild D ident r cutoff h ρ K C τ x y := by
  rw [denseChild_eq D ident r hr cutoff h ρ K C σ x y hx,
    denseChild_eq D ident r hr cutoff h ρ K C τ x y hx, ht]

include hr in
/-- Actual terminal one-child normalization with cross-rate frame counts. The finite
endpoint event may be broader than usage; its literal density supplies importance. -/
theorem dense_terminal_mean (hD : D ≠ 0) (hid : Function.Injective ident)
    (H : Horizon P) {k u : ℕ} (hk : k ≤ H.maxExponent)
    (ht : r.terminal.rate = rate k) (hu : r.usage.rate = rate u)
    (cutoff h ρ : ℝ → ℝ) (K : ℕ) (C : Matrix V V ℝ)
    (q : FrameChannel P 4 1 → Prop) [DecidablePred q]
    (x y : V) (hsub : ∀ A, splitUsage D ident r A y → q A)
    (hkh : ∀ v, cutoff v ≠ 0 → h v = 1)
    (hρ0 : ∀ v, 0 ≤ ρ v) (hρ1 : ∀ v, ρ v ≤ 1) {η : ℝ}
    (hη : 0 < η) (hρη : ∀ v, v ≤ η → ρ v = 1)
    (hC0 : ∀ w, 0 ≤ C x w) {M : ℝ} (hCM : ∑ w, C x w ≤ M)
    (hK : 2 * (1 + 32 * M / η) ≤ K) :
    (𝔼 A ∈ ({A | q A} : Finset _),
      r.terminal.rate * ((dens {A | q A} : ℝ) /
        dens {A | splitUsage D ident r A y}) *
      denseAtom (splitTerminal D ident r) (splitUsage D ident r)
        cutoff h ρ K r.terminal.rate C A x y) =
    r.terminal.rate * cutoff (C x y / r.terminal.rate) := by
  have hpos : 0 < (dens {A | splitUsage D ident r A y} : ℝ) := by
    rw [split_usage_density D ident r hu]
    have hP : (0 : ℝ) < P := by exact_mod_cast (Fact.out : P.Prime).pos
    have hside : (0 : ℝ) < side P u := by
      exact_mod_cast side_pos P u (Fact.out : P.Prime).pos
    positivity
  have hne : ({A | splitUsage D ident r A y} : Finset _).Nonempty :=
    dens_ne_zero.mp (by exact_mod_cast (ne_of_gt hpos))
  exact expect_denseAtom_change_usage
    (Y := splitTerminal D ident r) (Ya := fun A _ => q A)
    (Yt := splitUsage D ident r) hsub hne hkh hρ0 hρ1 hη hρη
    (ht ▸ rate_pos k) hC0 hCM (by norm_num : (0 : ℝ) ≤ 32) hK
    (split_usage_pair D ident r hr hD hid H hk ht hu y)

include hr in
/-- Actual dense direct mean on the inherited source and terminal event. Source
spectators integrate out after genuine normalization, with its literal density ratio. -/
theorem denseChild_mean_on_terminal_event
    (hD : D ≠ 0) (hid : Function.Injective ident) (H : Horizon P)
    {s k u : ℕ} (hsH : s ≤ H.maxExponent) (hs : r.source.rate = rate s)
    (hk : k ≤ H.maxExponent) (ht : r.terminal.rate = rate k)
    (hu : r.usage.rate = rate u)
    (cutoff h ρ : ℝ → ℝ) (K : ℕ) (C : Matrix V V ℝ)
    (q : FrameChannel P 4 1 → Prop) [DecidablePred q]
    (x y : V) (hsub : ∀ A, splitUsage D ident r A y → q A)
    (hkh : ∀ v, cutoff v ≠ 0 → h v = 1)
    (hρ0 : ∀ v, 0 ≤ ρ v) (hρ1 : ∀ v, ρ v ≤ 1) {η : ℝ}
    (hη : 0 < η) (hρη : ∀ v, v ≤ η → ρ v = 1)
    (hC0 : ∀ w, 0 ≤ C x w) (hCM : ∑ w, C x w ≤ 1)
    (hK : 2 * (1 + 32 / η) ≤ K) :
    (𝔼 σ ∈ ({σ : Environment P J |
      r.source.retains (channels D) σ (ident x) ∧ q (σ r.terminal.role)} : Finset _),
      (r.terminal.rate * ((dens {σ : Environment P J | q (σ r.terminal.role)} : ℝ) /
        dens {σ : Environment P J | r.usage.retains (channels D) σ (ident y)})) *
      denseChild D ident r cutoff h ρ K C σ x y) =
      r.terminal.rate * cutoff (C x y / r.terminal.rate) := by
  have hx := source_nonempty D ident r hr hD hid H hsH hs x
  have hpos : 0 < (dens {σ : Environment P J |
      r.source.retains (channels D) σ (ident x)} : ℝ) := by
    rw [channel_density D r.source s hs]
    have hside : (0 : ℝ) < side P s := by
      exact_mod_cast side_pos P s (Fact.out : P.Prime).pos
    have hP : (0 : ℝ) < P := by exact_mod_cast (Fact.out : P.Prime).pos
    positivity
  have hfull : ({σ : Environment P J |
      r.source.retains (channels D) σ (ident x)} : Finset _).Nonempty :=
    dens_ne_zero.mp (by exact_mod_cast hpos.ne')
  simp_rw [denseChild_eq D ident r hr cutoff h ρ K C _ x y hx]
  have hf := expect_pi_split_mul_filter r.source.role r.terminal.role hr.1
    (fun A => coordinate D r.source A (ident x)) q (fun _ => (1 : ℝ))
    (fun A => denseAtom (splitTerminal D ident r) (splitUsage D ident r)
      cutoff h ρ K r.terminal.rate C A x y)
  change (𝔼 σ ∈ ({σ : Environment P J |
    r.source.retains (channels D) σ (ident x) ∧ q (σ r.terminal.role)} : Finset _),
    1 * denseAtom (splitTerminal D ident r) (splitUsage D ident r)
      cutoff h ρ K r.terminal.rate C (σ r.terminal.role) x y) =
    (𝔼 σ ∈ ({σ : Environment P J |
      r.source.retains (channels D) σ (ident x)} : Finset _), (1 : ℝ)) * _ at hf
  simp only [one_mul, expect_const hfull] at hf
  rw [← mul_expect, hf, mul_expect]
  have hd : (dens {σ : Environment P J |
      r.usage.retains (channels D) σ (ident y)} : ℝ) =
      dens {A | splitUsage D ident r A y} := by
    rw [channel_density D r.usage u hu, split_usage_density D ident r hu]
  rw [dens_filter_pi_eval r.terminal.role q, hd]
  exact dense_terminal_mean D ident r hr hD hid H hk ht hu cutoff h ρ K C q x y
    hsub hkh hρ0 hρ1 hη hρη hC0 hCM (by simpa only [mul_one] using hK)

end Matrix.HierarchyParams.H4RankEnvironment
