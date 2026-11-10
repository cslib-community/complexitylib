/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.LogSpaceDerandomization.PairwiseIndependentHash.RowFourthMoment
public import CslibFrontier.Computability.LogSpaceDerandomization.PairwiseIndependentHash.FrameRetention
public import CslibFrontier.Computability.LogSpaceDerandomization.HierarchyAccess
public import CslibFrontier.Computability.LogSpaceDerandomization.FourthRootHierarchyParams
public import CslibFrontier.Computability.LogSpaceDerandomization.DetectedHierarchy
public import CslibFrontier.Foundations.Probability.ProductDensity
public import CslibFrontier.Computability.LogSpaceDerandomization.PairwiseIndependentHash.AtomChannels
public import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Tactic

/-!
# Full rank environments for finite hierarchy prefixes

One supplied prime serves every stage of this H=4, r=1 client on the q=16 rate grid.
The environment contains all independent rank roles and no salt coordinates. Conditioning
splits the same environment; spectator coordinates remain full slices. The exact-route torus
has modulus one. Finite exponent and identifier horizons are explicit hypotheses.

`rawIncomingNormalized_noise` applies the component-walk fourth-moment theorem to the actual
signed raw residual with incoming-gated normalized correction children. Its right-hand side
retains the raw input fourth moment. It does not prove incoming I / h / τ margins, true-mean or
reward approximation, statistical induction, a native implementation, or a class equality.
This is an original concrete application of the existing frame and row-moment APIs.

## Main definitions

* `Environment`: the entire product of rank frames.
* `Horizon`: finite exponent and identifier admissibility.
* `pairEquiv`: all-coordinate representation of a retained pair.
* `graph`: the transported lazy component walk, with M=1.
* `rawIncomingNormalized`: actual incoming-normalized signed residual sample.

## Main results

* `graph_walk`: exact transported one-step operator identity.
* `hierarchy_radix_prefix`: matrix invariants under finite horizon premises.
* `rawIncomingNormalized_noise`: contraction from the raw input fourth moment.
-/

public section
namespace Matrix.HierarchyParams.H4RankEnvironment
open Finset Cslib Cslib.Probability RotationMap Matrix Matrix.HierarchyParams
open scoped BigOperators

variable {P J : ℕ} [Fact P.Prime]
variable {V : Type*}

instance : Nonempty (Frame P 4 1) := Frame.nonempty (by decide)

/-- The full product of independent four-dimensional rank frames. -/
abbrev Environment (P J : ℕ) := Fin J → FrameChannel P 4 1
/-- An actual hierarchy channel on the fixed rank roles and field-valued suffixes. -/
abbrev Channel (P J : ℕ) := CorrectionRowTask.Channel (Fin J) (List (ZMod P))

/-- Operational source-grid rate: exponent k means 16 ^ -k. -/
@[expose] noncomputable def rate (k : ℕ) : ℝ := ((2 : ℝ) ^ k)⁻¹ ^ 4
/-- Natural side; ceiling division gives the exact finite-grid side. -/
@[expose] def side (P k : ℕ) : ℕ := P ⌈/⌉ (2 ^ k)

/-- Ceiling division agrees with the semantic real ceiling on the exponent grid. -/
theorem side_eq_ceil (P k : ℕ) : side P k = ⌈(P : ℝ) * ((2 : ℝ) ^ k)⁻¹⌉₊ := by
  apply Nat.le_antisymm
  · apply (ceilDiv_le_iff_le_mul (by positivity : 0 < (2: ℕ) ^ k)).2
    have h := Nat.le_ceil ((P : ℝ) / (2: ℝ) ^ k)
    have hh := (div_le_iff₀ (by positivity : 0 < (2: ℝ) ^ k)).1 h
    rw [div_eq_mul_inv] at hh
    exact_mod_cast (by simpa only [mul_comm] using hh :
      (P : ℝ) ≤ (2: ℝ) ^ k * ⌈(P : ℝ) * ((2: ℝ) ^ k)⁻¹⌉₊)
  · apply Nat.ceil_le.2
    rw [← div_eq_mul_inv, div_le_iff₀ (by positivity : 0 < (2: ℝ) ^ k)]
    have h := le_smul_ceilDiv (by positivity : 0 < (2: ℕ) ^ k) (b := P)
    have hh : (P : ℝ) ≤ (2: ℝ) ^ k * (side P k : ℕ) := by exact_mod_cast h
    simpa only [mul_comm] using hh

/-- The supplied prime is admissible only through the declared finite horizon. -/
structure Horizon (P : ℕ) where
  /-- Largest admitted rate exponent. -/
  maxExponent : ℕ
  /-- Largest admitted natural identifier. -/
  maxIdentifier : ℕ
  /-- The smallest queried side has an admissible real lower bound. -/
  side_admissible : 2 ^ maxExponent ≤ P
  /-- Natural identifiers fit before field reduction. -/
  identifier_admissible : maxIdentifier < P

/-- Every grid side is positive for a positive supplied modulus. -/
theorem side_pos (P k : ℕ) (hP : 0 < P) : 0 < side P k := by
  have h := le_smul_ceilDiv (by positivity : 0 < (2: ℕ) ^ k) (b := P)
  by_contra hn
  have hz : side P k = 0 := by omega
  change P ≤ 2 ^ k * side P k at h
  rw [hz, mul_zero] at h
  omega

/-- Grid sides never exceed the supplied modulus. -/
theorem side_le (P k : ℕ) : side P k ≤ P := by
  apply (ceilDiv_le_iff_le_mul (by positivity : 0 < 2 ^ k)).2
  exact Nat.le_mul_of_pos_left _ (by positivity)

/-- Retention with exact natural exponents, existing padded identifiers, fixed roles. -/
@[expose] def retains (D : ZMod P) (role : Fin J) (k : ℕ) (suffix : List (ZMod P))
    (σ : Environment P J) (x : ZMod P) : Prop :=
  frameRetains P 4 (side P k) (σ role) (CopyPadding.identifier D suffix x)

/-- Actual Request channels use real rates; the natural side is specified separately
by a grid certificate, rather than computed using a runtime fourth root. -/
@[expose] noncomputable def gridChannel (role : Fin J) (k : ℕ) (suffix : List (ZMod P)) :
    Channel P J :=
  ⟨role, rate k, suffix⟩

/-- Every unconditioned role is a full side-P slice at the public identifier zero. -/
@[expose] def pairSide (s t : Fin J) (Ls Lt : ℕ) (j : Fin J) : ℕ :=
  if j = s then Ls else if j = t then Lt else P

/-- Condition source and terminal at their identifiers; spectators use public identifier zero. -/
@[expose] def pairId (s t : Fin J) (a b : ZMod P) (j : Fin J) : ZMod P :=
  if j = s then a else if j = t then b else 0

/-- Source retention in the full rank environment. -/
@[expose] def X (s : Fin J) (Ls : ℕ) (a : V → ZMod P)
    (σ : Environment P J) (x : V) : Prop :=
  frameRetains P 4 Ls (σ s) (a x)

/-- Terminal retention in the same full rank environment. -/
@[expose] def Y (t : Fin J) (Lt : ℕ) (b : V → ZMod P)
    (σ : Environment P J) (z : V) : Prop :=
  frameRetains P 4 Lt (σ t) (b z)

noncomputable instance (s : Fin J) (L : ℕ) (a : V → ZMod P)
    (σ : Environment P J) (x : V) : Decidable (X s L a σ x) := Classical.propDecidable _
noncomputable instance (s : Fin J) (L : ℕ) (a : V → ZMod P)
    (σ : Environment P J) (x : V) : Decidable (Y s L a σ x) := Classical.propDecidable _

/-- Every frame is retained by the full side-P box. -/
theorem full_retains (A : FrameChannel P 4 1) (a : ZMod P) :
    frameRetains P 4 P A a := by
  exact mem_retentionBox.2 fun i => ZMod.val_lt _

/-- Exact full-coordinate equivalence. No role is omitted or averaged externally. -/
@[expose] noncomputable def pairEquiv (s t : Fin J) (hst : s ≠ t) (Ls Lt : ℕ)
    (a b : V → ZMod P) (x z : V) :
    RetainedPairSlice (X s Ls a) (Y t Lt b) x z ≃
      ((∀ j, RetentionSlice P 4 1 (pairSide (P := P) s t Ls Lt j) (pairId s t (a x) (b z) j)) ×
        (Fin 4 → ZMod 1)) where
  toFun σ := (fun j => ⟨σ.val j, by
    have hs := (mem_filter.1 σ.property).2.1
    have ht := (mem_filter.1 σ.property).2.2
    by_cases hj : j = s
    · subst j
      simpa [pairSide, pairId, X] using hs
    · by_cases hjt : j = t
      · subst j
        simpa [pairSide, pairId, hst.symm, Y] using ht
      · simpa [pairSide, pairId, hj, hjt] using full_retains (σ.val j) 0⟩, 0)
  invFun u := ⟨fun j => (u.1 j).val, by
    apply mem_filter.2
    refine ⟨mem_univ _, ?_, ?_⟩
    · simpa [X, pairSide, pairId] using (u.1 s).property
    · simpa [Y, pairSide, pairId, hst.symm] using (u.1 t).property⟩
  left_inv σ := by rfl
  right_inv u := by
    apply Prod.ext
    · rfl
    · exact Subsingleton.elim _ _

omit [Fact P.Prime] in
/-- Every coordinate side is bounded by the shared prime. -/
theorem pairSide_le (s t : Fin J) (Ls Lt : ℕ) (hs : Ls ≤ P) (ht : Lt ≤ P) :
    ∀ j, pairSide (P := P) s t Ls Lt j ≤ P := by
  intro j
  simp only [pairSide]
  split_ifs <;> first | assumption | exact le_rfl

instance pairSide_neZero (s t : Fin J) (Ls Lt : ℕ) [NeZero Ls] [NeZero Lt] :
    ∀ j, NeZero (pairSide (P := P) s t Ls Lt j) := by
  intro j
  dsimp [pairSide]
  split_ifs <;> infer_instance

/-- Actual graph on retained environments: one independent rank coordinate moves;
the exact-route M=1 coordinate is the unique point. -/
@[expose] noncomputable def graph (s t : Fin J) (hst : s ≠ t) (Ls Lt : ℕ)
    [NeZero Ls] [NeZero Lt] (hs : Ls ≤ P) (ht : Lt ≤ P)
    (a b : V → ZMod P) (x z : V) :=
  (((ofPerms (componentMove 4 1 (fun _ : Fin J => P) (pairSide (P := P) s t Ls Lt))).lazy.reindex
    (componentEquiv 1 (pairSide_le s t Ls Lt hs ht) (pairId s t (a x) (b z))).symm).reindex
      (pairEquiv s t hst Ls Lt a b x z).symm)

/-- The full retained-pair / operator obligations are discharged for this concrete
rank environment, uniformly in the one supplied prime and both natural sides. -/
theorem noise [Fintype V] (s t : Fin J) (hst : s ≠ t) (Ls Lt : ℕ)
    [NeZero Ls] [NeZero Lt] (hs : Ls ≤ P) (ht : Lt ≤ P)
    (a b : V → ZMod P) {N u : ℝ} (hNu : 0 ≤ N * u)
    (steps : ℕ) (F : Environment P J → V → V → ℝ) :
    rowNormPow 4 N u (X s Ls a) (Y t Lt b) (fun σ x z =>
      conditionalWalk (X s Ls a) (Y t Lt b) (graph s t hst Ls Lt hs ht a b)
        (fun _ _ => steps) F σ x z - rowSliceMean (X s Ls a) (Y t Lt b) F x z) ≤
    32 * (1 - 1 / (155648 * (J + 1) * (4: ℝ) ^ 4)) ^ (2 * steps) *
      rowNormPow 4 N u (X s Ls a) (Y t Lt b) F := by
  apply rowNormPow_conditionalWalk_component_le (H := 4) (M := 1)
    (P := fun _ : Fin J => P) (L := pairSide (P := P) s t Ls Lt)
    (X s Ls a) (Y t Lt b) (by decide) (pairSide_le s t Ls Lt hs ht)
    (fun x z => pairId s t (a x) (b z)) (graph s t hst Ls Lt hs ht a b)
    (fun x z _ => pairEquiv s t hst Ls Lt a b x z) (fun _ _ _ => rfl) hNu

/-- Semantic extension to the actual real-rate Request interface. Executable clients
supply the natural exponent; this extension is used only in the mathematical model. -/
@[expose] noncomputable def semanticSide (P : ℕ) (b : ℝ) : ℕ :=
  ⌈(P : ℝ) * b ^ ((4: ℝ)⁻¹)⌉₊

/-- The semantic fourth-root side agrees with natural ceiling division on the rate grid. -/
theorem semanticSide_grid (P k : ℕ) : semanticSide P (rate k) = side P k := by
  have hroot : (rate k) ^ ((4: ℝ)⁻¹) = ((2: ℝ) ^ k)⁻¹ := by
    simpa only [rate, Nat.cast_ofNat] using
      (Real.pow_rpow_inv_natCast (x := ((2: ℝ) ^ k)⁻¹) (n := 4) (by positivity) (by decide))
  rw [semanticSide, hroot]
  exact (side_eq_ceil P k).symm

/-- Interpret actual real-rate hierarchy channels on the full rank environment. -/
@[expose] noncomputable def channels (D : ZMod P) (role : Fin J) (b : ℝ)
    (suffix : List (ZMod P)) (σ : Environment P J) (x : ZMod P) : Prop :=
  frameRetains P 4 (semanticSide P b) (σ role) (CopyPadding.identifier D suffix x)

noncomputable instance (D : ZMod P) (role : Fin J) (b : ℝ)
    (suffix : List (ZMod P)) (σ : Environment P J) (x : ZMod P) :
    Decidable (channels D role b suffix σ x) := Classical.propDecidable _

/-- An actual grid channel has the natural exponent retention predicate. -/
theorem grid_retains (D : ZMod P) (role : Fin J) (k : ℕ)
    (suffix : List (ZMod P)) (σ : Environment P J) (x : ZMod P) :
    (gridChannel role k suffix).retains (channels D) σ x ↔
      retains D role k suffix σ x := by
  simp only [gridChannel, CorrectionRowTask.Channel.retains, channels,
    semanticSide_grid, retains]

/-- Every finite grid rate is positive. -/
theorem rate_pos (k : ℕ) : 0 < rate k := by unfold rate; positivity

/-- Increasing the exponent narrows the grid rate. -/
theorem rate_antitone : Antitone rate := by
  intro a b hab
  unfold rate
  apply pow_le_pow_left₀ (by positivity)
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hab)

/-- Usage minima correspond to maxima of natural exponents. -/
theorem rate_min (k l : ℕ) : min (rate k) (rate l) = rate (max k l) := by
  rcases le_total k l with h | h
  · rw [max_eq_right h, min_eq_right (rate_antitone h)]
  · rw [max_eq_left h, min_eq_left (rate_antitone h)]

omit [Fact P.Prime] in
/-- The declared exponent horizon supplies the frame side lower bound. -/
theorem horizon_admissible (H : Horizon P) {k : ℕ} (hk : k ≤ H.maxExponent) :
    1 ≤ (P: ℝ) * ((2: ℝ) ^ k)⁻¹ := by
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  norm_num only [one_mul]
  exact_mod_cast (le_trans (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hk) H.side_admissible)

/-- Frame detector constants are exactly (1, 16, 32, 8), independently of P and stage. -/
theorem retention {D : ZMod P} (hD : D ≠ 0) (suffix : List (ZMod P))
    (H : Horizon P) {k : ℕ} (hk : k ≤ H.maxExponent) :
    RetentionChannels
      (fun A : FrameChannel P 4 1 => fun x => frameRetains P 4 (side P k) A
        (CopyPadding.identifier D suffix x))
      (fun A : FrameChannel P 4 1 => fun x => frameRetains P 4 (side P k) A
        (CopyPadding.identifier D suffix x))
      (rate k) ((((side P k : ℕ): ℝ) / P) ^ 4) 1 16 32 8 := by
  have h := retentionChannels_frameRetains_of_lt
    (CopyPadding.identifier_injective hD suffix) (H := 4) (r := 1)
    (by decide) (by decide) (horizon_admissible H hk)
    (show ((2: ℝ) ^ k)⁻¹ ≤ 1 from inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))
  simpa only [← side_eq_ceil, rate, show (2: ℝ) ^ 4 = 16 by norm_num,
    show (2: ℝ) ^ (4 + 1) = 32 by norm_num] using h

/-- Exact full-environment marginal density, valid also for unconditioned roles. -/
theorem density (role : Fin J) (L : ℕ) (hL : L ≤ P) (a : ZMod P) :
    (dens {σ : Environment P J | frameRetains P 4 L (σ role) a} : ℝ) = ((L: ℝ) / P) ^ 4 := by
  classical
  rw [dens_filter_pi_eval role (fun A : FrameChannel P 4 1 => frameRetains P 4 L A a)]
  have h := congrArg (fun q : ℚ≥0 => (q: ℝ))
    (dens_eval_mem_retentionBox (P := P) (H := 4) (r := 1) (by decide) hL a)
  push_cast at h
  simpa only [nnratCast_dens] using h

/-- Concrete mixed rank / usage pair law from frame conditioning, not unrestricted
seed independence. Usage may have any other positive side; only rank's admissible
source-grid exponent contributes 32 * rate(k). -/
theorem mixed_pair_density (role : Fin J) (H : Horizon P) {k : ℕ}
    (hk : k ≤ H.maxExponent) (Lt : ℕ) (hLt : Lt ≤ P) {w y : ZMod P} (hwy : w ≠ y) :
    (dens {σ : Environment P J |
      frameRetains P 4 (side P k) (σ role) w ∧ frameRetains P 4 Lt (σ role) y} : ℝ) ≤
      32 * rate k * dens {σ : Environment P J | frameRetains P 4 Lt (σ role) y} := by
  classical
  rw [dens_filter_pi_eval role (fun A : FrameChannel P 4 1 =>
    frameRetains P 4 (side P k) A w ∧ frameRetains P 4 Lt A y), density role Lt hLt]
  have hp := dens_eval_mem_and_eval_mem_le (P := P) (H := 4) (r := 1)
    (by decide) (side_le P k) hLt hwy
  have hq := one_div_two_le_frameDensity (P := P) (H := 4) (r := 1) (by decide)
  have hq0 : 0 < frameDensity P 4 1 := by linarith
  have hh := (affineRetains_rates (P := P) (H := 4) (horizon_admissible H hk)
    (show ((2: ℝ) ^ k)⁻¹ ≤ 1 from inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))).2.2.1
  rw [← side_eq_ceil] at hh
  norm_num only at hh
  change ((side P k: ℝ) / P) ^ 4 ≤ 16 * rate k at hh
  apply hp.trans
  rw [div_le_iff₀ hq0]
  have hr := rate_pos k
  have hπ : 0 ≤ ((Lt: ℝ) / P) ^ 4 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hh hπ,
    mul_le_mul_of_nonneg_left hq (show 0 ≤ 32 * rate k * ((Lt: ℝ) / P) ^ 4 by positivity)]

/-- The mixed rank/usage density bound as a count bound, with injective copy padding. -/
theorem mixed_pair_count (role : Fin J) (H : Horizon P) {k : ℕ}
    (hk : k ≤ H.maxExponent) (Lt : ℕ) (hLt : Lt ≤ P)
    {D : ZMod P} (hD : D ≠ 0) (suffix : List (ZMod P)) {w y : ZMod P} (hwy : w ≠ y) :
    (#{σ : Environment P J |
      frameRetains P 4 Lt (σ role) (CopyPadding.identifier D suffix y) ∧
      frameRetains P 4 (side P k) (σ role) (CopyPadding.identifier D suffix w)} : ℝ) ≤
      32 * rate k * #{σ : Environment P J |
        frameRetains P 4 Lt (σ role) (CopyPadding.identifier D suffix y)} := by
  classical
  exact card_filter_and_le_of_dens_le
    (mixed_pair_density role H hk Lt hLt ((CopyPadding.identifier_injective hD suffix).ne hwy))

/-- Independent role coordinates remain independent for all mixed rates and suffixes. -/
theorem independent (s t : Fin J) (hst : t ≠ s) (Ls Lt : ℕ)
    (a b : ZMod P) :
    dens {σ : Environment P J | frameRetains P 4 Ls (σ s) a ∧
      frameRetains P 4 Lt (σ t) b} =
      dens {A : FrameChannel P 4 1 | frameRetains P 4 Ls A a} *
      dens {A : FrameChannel P 4 1 | frameRetains P 4 Lt A b} := by
  classical
  exact dens_filter_pi_eval_and_pi_eval (Role := Fin J) (A := FrameChannel P 4 1) hst
    (fun A => frameRetains P 4 Ls A a) (fun A => frameRetains P 4 Lt A b)

/-- Copy traversal agrees with the actual radix-copy identifier, including inherited padding. -/
theorem copy_retains (D : ℕ) (ch : Channel P J) (σ : Environment P J)
    (n m l : ℕ) (hD : D = m + 1) (x : Fin (n * (m + 1) ^ l)) (j : Fin (m + 1)) :
    (ch.throughCopy (j: ZMod P)).retains (channels (D: ZMod P)) σ (x: ZMod P) ↔
      ch.retains (channels (D: ZMod P)) σ
        ((((radixCopyEquiv n m l).symm (toLex (x, j))).val : ℕ): ZMod P) := by
  subst D
  change frameRetains P 4 _ _ _ ↔ frameRetains P 4 _ _ _
  dsimp only [CorrectionRowTask.Channel.throughCopy]
  push_cast
  rw [CopyPadding.identifier_radixCopy]

/-- A fixed independent role product, reused unchanged at every stage. -/
structure RoleProfile (J : ℕ) where
  /-- Rank coordinate conditioning the source vertex. -/
  source : Fin J
  /-- Independent rank coordinate used at product midpoints. -/
  midpoint : Fin J
  /-- Rank coordinate conditioning the terminal vertex. -/
  terminal : Fin J
  source_midpoint : source ≠ midpoint
  source_terminal : source ≠ terminal
  midpoint_terminal : midpoint ≠ terminal

/-- Three distinct roles for source, midpoint and terminal. -/
@[expose] def threeRoles : RoleProfile 3 := ⟨0, 1, 2, by decide, by decide, by decide⟩

/-- Precisely the role / suffix frame condition needed by a normalized row request. -/
@[expose] def Admissible {k : ℕ} (r : HierarchyTask.Request k (Fin J) (ZMod P)) : Prop :=
  r.source.role ≠ r.terminal.role ∧ r.usage.role = r.terminal.role ∧
    r.usage.suffix = r.terminal.suffix

omit [Fact P.Prime] in
/-- Actual residual requests preserve distinct roles, including source release to
midpoint in the right child and the separate negative endpoint correction. -/
theorem raw_admissible {k : ℕ} (R : RoleProfile J) (l bin : ℕ)
    (ks km kt kb : ℕ) (ss sm st : List (ZMod P))
    (r : HierarchyTask.Request k (Fin J) (ZMod P))
    (hr : r ∈ (HierarchyTask.rawRequests l bin .residual
      (gridChannel R.source ks ss) (gridChannel R.midpoint km sm)
      (gridChannel R.terminal kt st) (rate kb)).calls) : Admissible r := by
  have hsm := R.source_midpoint
  have hst := R.source_terminal
  have hmt := R.midpoint_terminal
  simp only [HierarchyTask.rawRequests, HierarchyTask.RawRequests.calls,
    Option.toList_some, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with (rfl | rfl | rfl) | rfl <;>
    simp [Admissible, gridChannel, hsm, hst, hmt]

omit [Fact P.Prime] in
/-- Every actual residual request stays on the natural-exponent grid; usage min
is max of exponents, and does not allocate another role. -/
theorem raw_grid {k : ℕ} (R : RoleProfile J) (l bin : ℕ)
    (ks km kt kb : ℕ) (ss sm st : List (ZMod P))
    (r : HierarchyTask.Request k (Fin J) (ZMod P))
    (hr : r ∈ (HierarchyTask.rawRequests l bin .residual
      (gridChannel R.source ks ss) (gridChannel R.midpoint km sm)
      (gridChannel R.terminal kt st) (rate kb)).calls) :
    ∃ es et eu, r.source.rate = rate es ∧ r.terminal.rate = rate et ∧
      r.usage.rate = rate eu := by
  simp only [HierarchyTask.rawRequests, HierarchyTask.RawRequests.calls,
    Option.toList_some, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with (rfl | rfl | rfl) | rfl
  · exact ⟨ks, kb, max kt kb, rfl, rfl, rate_min kt kb⟩
  · exact ⟨ks, km, km, rfl, rfl, rfl⟩
  · exact ⟨km, kb, max kt kb, rfl, rfl, rate_min kt kb⟩
  · exact ⟨ks, km, max kt km, rfl, rfl, rate_min kt km⟩

omit [Fact P.Prime] in
/-- Copy source / terminal symbols prepend to the inherited suffix, on the actual
weight and residual-normalized constructors. -/
theorem copy_admissible {k : ℕ} (R : RoleProfile J) (l bin : ℕ)
    (ks kt kf kb : ℕ) (ss st : List (ZMod P)) (i j : ZMod P)
    (r : HierarchyTask.Request k (Fin J) (ZMod P))
    (hr : r ∈ HierarchyTask.routedCopyRequests l bin
      (gridChannel R.source ks ss) (gridChannel R.terminal kt st) (rate kf) (rate kb) i j) :
    Admissible r ∧ r.source.suffix = i :: ss ∧ r.terminal.suffix = j :: st := by
  have hst := R.source_terminal
  simp only [HierarchyTask.routedCopyRequests, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact ⟨⟨hst, rfl, rfl⟩, rfl, rfl⟩

/-- Local channel predicate for the existing source / terminal product normalization. -/
@[expose] noncomputable def coordinate (D : ZMod P) (ch : Channel P J)
    (A : FrameChannel P 4 1) (v : ZMod P) : Prop :=
  frameRetains P 4 (semanticSide P ch.rate) A (CopyPadding.identifier D ch.suffix v)

noncomputable instance (D : ZMod P) (ch : Channel P J)
    (A : FrameChannel P 4 1) (v : ZMod P) : Decidable (coordinate D ch A v) :=
  Classical.propDecidable _

noncomputable instance {k : ℕ} (r : HierarchyTask.Request k (Fin J) (ZMod P)) :
    Decidable (Admissible r) := Classical.propDecidable _

/-- Actual DenseRowRecipe.normalized, with the terminal coordinate split off.
All spectator roles remain in Γ, including future-stage roles. The preparatory
child is a whole function on the same global rank environment. -/
@[expose] noncomputable def normalizedRequest [Fintype V] {k : ℕ} (D : ZMod P) (ident : V → ZMod P)
    (r : HierarchyTask.Request k (Fin J) (ZMod P)) (cutoff gate : ℝ → ℝ) (K : ℕ)
    (raw : Environment P J → Matrix V V ℝ)
    (prep : Environment P J → Matrix V V ℝ)
    (σ : Environment P J) (x y : V) : ℝ :=
  if h : Admissible r then
    let split := Equiv.piSplitAt r.terminal.role (fun _ : Fin J => FrameChannel P 4 1)
    DenseRowRecipe.normalized cutoff gate K r.terminal.rate
      (fun rest x => coordinate D r.source (rest ⟨r.source.role, h.1⟩) (ident x))
      (fun A v => coordinate D r.terminal A (ident v))
      (fun A v => coordinate D r.usage A (ident v)) (raw σ)
      (fun p => prep (split.symm (p.2, p.1)))
      ((split σ).2, (split σ).1) x y
  else 0

/-- One real signed raw residual sample, whose four children use the actual
normalized recipe, its original raw ranks and clipped preparatory denominator. -/
noncomputable def rawNormalized [Fintype V] {k : ℕ} (D : ZMod P) (ident : V → ZMod P)
    (R : RoleProfile J)
    (l bin ks km kt kb : ℕ) (ss sm st : List (ZMod P))
    (cutoff gate : ℝ → ℝ) (K : ℕ)
    (raw : HierarchyTask.Request k (Fin J) (ZMod P) →
      Environment P J → Matrix V V ℝ)
    (prep : HierarchyTask.Request k (Fin J) (ZMod P) →
      Environment P J → Matrix V V ℝ)
    (σ : Environment P J) : Matrix V V ℝ :=
  HierarchyTask.rawSample (fun role b suffix σ v => channels D role b suffix σ (ident v))
    l bin .residual
    (gridChannel R.source ks ss) (gridChannel R.midpoint km sm)
    (gridChannel R.terminal kt st) (rate kb)
    (fun r => normalizedRequest D ident r cutoff gate K (raw r) (prep r) σ)

instance side_neZero (k : ℕ) : NeZero (side P k) :=
  ⟨(side_pos P k (Fact.out : P.Prime).pos).ne'⟩

/-- Full integrated contraction for the actual normalized-child raw sample.
There is one prime, one fixed role product, and torus M=1. No desired noise or
conditional-moment hypothesis is supplied by the client. -/
theorem rawNormalized_noise [Fintype V] {k : ℕ} (D : ZMod P) (ident : V → ZMod P)
    (R : RoleProfile J)
    (l bin ks km kt kb : ℕ) (ss sm st : List (ZMod P))
    (cutoff gate : ℝ → ℝ) (K : ℕ)
    (raw : HierarchyTask.Request k (Fin J) (ZMod P) →
      Environment P J → Matrix V V ℝ)
    (prep : HierarchyTask.Request k (Fin J) (ZMod P) →
      Environment P J → Matrix V V ℝ)
    {N u : ℝ} (hNu : 0 ≤ N * u) (steps : ℕ) :
    let a := fun v => CopyPadding.identifier D ss (ident v)
    let b := fun v => CopyPadding.identifier D st (ident v)
    let F := rawNormalized D ident R l bin ks km kt kb ss sm st cutoff gate K raw prep
    let G := graph R.source R.terminal R.source_terminal (side P ks) (side P kt)
      (side_le P ks) (side_le P kt) a b
    rowNormPow 4 N u (X R.source (side P ks) a) (Y R.terminal (side P kt) b)
      (fun σ x z => conditionalWalk (X R.source (side P ks) a)
        (Y R.terminal (side P kt) b) G (fun _ _ => steps) F σ x z -
        rowSliceMean (X R.source (side P ks) a) (Y R.terminal (side P kt) b) F x z) ≤
      32 * (1 - 1 / (155648 * (J + 1) * (4: ℝ) ^ 4)) ^ (2 * steps) *
        rowNormPow 4 N u (X R.source (side P ks) a) (Y R.terminal (side P kt) b) F := by
  exact noise R.source R.terminal R.source_terminal _ _ (side_le P ks) (side_le P kt) _ _
    hNu steps _

/-- The frame counterpart of DenseSamplingLaws.ofAffine, on the actual entire
role product and with the correct cross-rate constant 32. -/
noncomputable def denseLaws (D : ZMod P) (hD : D ≠ 0) (role : Fin J)
    (suffix : List (ZMod P)) (H : Horizon P) (k : ℕ) (hk : k ≤ H.maxExponent)
    (Lt La : ℕ) (hLt0 : 0 < Lt) (hLtP : Lt ≤ P) (hLa : Lt ≤ La)
    (cutoff h gate : ℝ → ℝ) (K : ℕ) (M η : ℝ)
    (hsupport : ∀ d, cutoff d ≠ 0 → h d = 1)
    (hg0 : ∀ r, 0 ≤ gate r) (hg1 : ∀ r, gate r ≤ 1)
    (hη : 0 < η) (hone : ∀ r, r ≤ η → gate r = 1)
    (hK : 2 * (1 + 32 * M / η) ≤ K) :
    DenseSamplingLaws
      (fun (σ : Environment P J) v => frameRetains P 4 (side P k) (σ role)
        (CopyPadding.identifier D suffix v))
      (fun (σ : Environment P J) v => frameRetains P 4 La (σ role)
        (CopyPadding.identifier D suffix v))
      (fun (σ : Environment P J) v => frameRetains P 4 Lt (σ role)
        (CopyPadding.identifier D suffix v))
      cutoff (rate k) M where
  h := h
  ρ := gate
  K := K
  η := η
  c := 32
  usage_subset σ v hv := by
    apply mem_retentionBox.2
    exact fun i => ((mem_retentionBox.1 hv) i).trans_le hLa
  usage_nonempty v := by
    classical
    apply dens_ne_zero.mp
    intro hz
    have hh := density role Lt hLtP (CopyPadding.identifier D suffix v)
    rw [hz] at hh
    have hp : (0: ℝ) < P := by exact_mod_cast (Fact.out : P.Prime).pos
    have hlt : (0: ℝ) < Lt := by exact_mod_cast hLt0
    have : (0: ℝ) < ((Lt: ℝ) / P) ^ 4 := by positivity
    rw [← hh] at this
    norm_num at this
  support := hsupport
  gate_nonneg := hg0
  gate_le_one := hg1
  η_pos := hη
  gate_one := hone
  c_nonneg := by norm_num
  rank_bound := hK
  pair _ _ hwy := mixed_pair_count (P := P) (J := J) role H hk Lt hLtP hD suffix hwy

/-- Explicit rational polynomial cutoff and row gate for an actual dense client.
These are fully exposed arithmetic formulas, not opaque functions from a witness. -/
@[expose] noncomputable def cutoff (d : ℝ) : ℝ := polynomialSwitch4 (1 / 2) 1 d
/-- Explicit polynomial row gate, full through rank one and closed from rank two. -/
@[expose] noncomputable def gate (r : ℝ) : ℝ := 1 - polynomialSwitch4 1 2 r

/-- The polynomial row gate is nonnegative. -/
theorem gate_nonneg (r : ℝ) : 0 ≤ gate r := sub_nonneg.2 (polynomialSwitch4_le_one _ _ _)
/-- The polynomial row gate is at most one. -/
theorem gate_le_one (r : ℝ) : gate r ≤ 1 := sub_le_self _ (polynomialSwitch4_nonneg _ _ _)
/-- The polynomial row gate is one below its safe threshold. -/
theorem gate_one {r : ℝ} (hr : r ≤ 1) : gate r = 1 := by
  rw [gate, polynomialSwitch4_of_le (by norm_num) hr, sub_zero]

/-- An explicit, nonvacuous dense client: rank 66, safe threshold 1, raw row
mass at most 1. This proves its true normalization through concrete frame laws.
It is not the hierarchy incoming / access-margin theorem. -/
noncomputable def explicitDense (D : ZMod P) (hD : D ≠ 0) (role : Fin J)
    (suffix : List (ZMod P)) (H : Horizon P) (k : ℕ) (hk : k ≤ H.maxExponent)
    (Lt La : ℕ) (hLt0 : 0 < Lt) (hLtP : Lt ≤ P) (hLa : Lt ≤ La) :=
  denseLaws D hD role suffix H k hk Lt La hLt0 hLtP hLa cutoff (fun _ => 1) gate
    66 1 1 (fun _ _ => rfl) gate_nonneg gate_le_one (by norm_num)
    (fun _ hr => gate_one hr) (by norm_num)

/-- Primitive frame laws give a true atom's conditional mean; no mean certificate
is a field of the environment model. Arbitrary prime, mixed usage and inherited
suffixes are retained in the statement. -/
theorem explicitDense_mean (D : ZMod P) (hD : D ≠ 0) (role : Fin J)
    (suffix : List (ZMod P)) (H : Horizon P) (k : ℕ) (hk : k ≤ H.maxExponent)
    (Lt La : ℕ) (hLt0 : 0 < Lt) (hLtP : Lt ≤ P) (hLa : Lt ≤ La)
    (G : Matrix (ZMod P) (ZMod P) ℝ)
    (hG : ∀ x y, 0 ≤ G x y) (hG1 : ∀ x, ∑ y, G x y ≤ 1) (x y : ZMod P) :
    let A := explicitDense D hD role suffix H k hk Lt La hLt0 hLtP hLa
    (𝔼 σ ∈ ({σ : Environment P J | frameRetains P 4 La (σ role)
      (CopyPadding.identifier D suffix y)} : Finset _), A.direct G σ x y) =
        rate k * cutoff (G x y / rate k) := by
  exact (explicitDense D hD role suffix H k hk Lt La hLt0 hLtP hLa).expect_direct
    (rate_pos k) hG hG1 x y

/-- Equal rank environments give identical actual raw / normalized samples,
regardless of any external deterministic record. No random salt coordinate is
present in either sample or conditional averaging space. This concerns this
client; the eventual recursive estimator must prove the analogous factorization. -/
theorem rawNormalized_rank_dependency [Fintype V] {k : ℕ} {Input : Type*}
    (ranks : Input → Environment P J) (D : ZMod P) (ident : V → ZMod P)
    (R : RoleProfile J)
    (l bin ks km kt kb : ℕ) (ss sm st : List (ZMod P))
    (raw : HierarchyTask.Request k (Fin J) (ZMod P) →
      Environment P J → Matrix V V ℝ)
    (prep : HierarchyTask.Request k (Fin J) (ZMod P) →
      Environment P J → Matrix V V ℝ)
    {a b : Input} (hab : ∀ j, ranks a j = ranks b j) :
    rawNormalized D ident R l bin ks km kt kb ss sm st cutoff gate 66 raw prep (ranks a) =
      rawNormalized D ident R l bin ks km kt kb ss sm st cutoff gate 66 raw prep (ranks b) := by
  rw [show ranks a = ranks b from funext hab]

/-- The normalization split is exactly the single full-environment conditional
mean, not a product of two independent copies of the full environment. -/
theorem normalizer_full {k : ℕ} (D : ZMod P) (ident : V → ZMod P)
    (r : HierarchyTask.Request k (Fin J) (ZMod P)) (hr : Admissible r)
    (prep : Environment P J → Matrix V V ℝ) (x y : V) :
    let split := Equiv.piSplitAt r.terminal.role (fun _ : Fin J => FrameChannel P 4 1)
    CorrectionRowRecipe.normalizer
      (fun rest x => coordinate D r.source (rest ⟨r.source.role, hr.1⟩) (ident x))
      (fun A v => coordinate D r.usage A (ident v)) (fun p => prep (split.symm (p.2, p.1))) x y =
    rowSliceMean (fun σ v => r.source.retains (channels D) σ (ident v))
      (fun σ v => r.usage.retains (channels D) σ (ident v)) prep x y := by
  classical
  dsimp only
  unfold CorrectionRowRecipe.normalizer rowSliceMean
  let e := (Equiv.piSplitAt r.terminal.role (fun _ : Fin J => FrameChannel P 4 1)).trans
    (Equiv.prodComm _ _)
  symm
  apply Finset.expect_equiv e
  · intro σ
    simp [mem_filter, mem_univ, mem_product, e, Equiv.trans_apply,
      Equiv.prodComm_apply, Equiv.piSplitAt_apply, coordinate,
      CorrectionRowTask.Channel.retains, channels, hr.2.1]
  · intro σ _
    change prep σ x y = prep (e.symm (e σ)) x y
    rw [Equiv.symm_apply_apply]

/-- Identity-matrix rows witness a nonzero actual normalized dense sample,
for every supplied prime and horizon, rather than an empty conditioning model. -/
theorem explicitDense_nonzero (D : ZMod P) (hD : D ≠ 0) (role : Fin J)
    (suffix : List (ZMod P)) (H : Horizon P) (x : ZMod P) :
    let A := explicitDense D hD role suffix H 0 (Nat.zero_le _)
      P P (Fact.out : P.Prime).pos le_rfl le_rfl
    (𝔼 σ ∈ ({σ : Environment P J | frameRetains P 4 P (σ role)
      (CopyPadding.identifier D suffix x)} : Finset _), A.direct 1 σ x x) = 1 := by
  have hh := explicitDense_mean D hD role suffix H 0 (Nat.zero_le _)
    P P (Fact.out : P.Prime).pos le_rfl le_rfl (1 : Matrix (ZMod P) (ZMod P) ℝ)
    (fun a b => by
      change 0 ≤ if a = b then (1: ℝ) else 0
      split_ifs <;> norm_num)
    (fun a => by
      change (∑ b : ZMod P, if a = b then (1: ℝ) else 0) ≤ 1
      simp) x x
  simpa only [rate, pow_zero, inv_one, one_pow, Matrix.one_apply_eq, div_one, one_mul,
    cutoff, polynomialSwitch4_of_ge (by norm_num : (1: ℝ) / 2 < 1) le_rfl] using hh

/-- Every valid natural padded identifier below the finite horizon stays below
P before reduction, so modular equality does not identify distinct such integers. -/
theorem bounded_identifier_injective (H : Horizon P) {N : ℕ} (hN : N ≤ H.maxIdentifier + 1)
    {D : ZMod P} (hD : D ≠ 0) (suffix : List (ZMod P)) :
    Function.Injective (fun x : Fin N => CopyPadding.identifier D suffix (x: ZMod P)) := by
  apply (CopyPadding.identifier_injective hD suffix).comp
  intro x y h
  have hHP := H.identifier_admissible
  have hx : x.val < P := by omega
  have hy : y.val < P := by omega
  have hh := congrArg ZMod.val h
  simp only [ZMod.val_natCast_of_lt hx, ZMod.val_natCast_of_lt hy] at hh
  exact Fin.ext hh

/-- All full-environment coordinates are recovered pointwise, including the
unconditioned roles represented as public-id full slices. -/
theorem pairEquiv_coordinate (s t : Fin J) (hst : s ≠ t) (Ls Lt : ℕ)
    (a b : V → ZMod P) (x z : V)
    (σ : RetainedPairSlice (X s Ls a) (Y t Lt b) x z) (j : Fin J) :
    ((pairEquiv s t hst Ls Lt a b x z σ).1 j).val = σ.val j := rfl

/-- Natural radix padding before any field reduction. -/
@[expose] def padNat (D : ℕ) (suffix : List ℕ) (x : ℕ) : ℕ :=
  suffix.foldl (fun x j => D * x + j) x

/-- Natural copy padding commutes with reduction to the supplied field. -/
theorem padNat_cast (D x : ℕ) (suffix : List ℕ) :
    (padNat D suffix x : ZMod P) =
      CopyPadding.identifier (D: ZMod P) (suffix.map fun j => (j: ZMod P)) (x: ZMod P) := by
  induction suffix generalizing x with
  | nil => rfl
  | cons j suffix ih =>
    change (padNat D suffix (D * x + j) : ZMod P) =
      CopyPadding.identifier (D: ZMod P) (suffix.map fun j => (j: ZMod P))
        ((D: ZMod P) * (x: ZMod P) + (j: ZMod P))
    simpa only [Nat.cast_add, Nat.cast_mul] using ih (D * x + j)

/-- A bounded suffix preserves the natural radix domain bound. -/
theorem padNat_bound {D n x : ℕ} (hx : x < n) (suffix : List ℕ)
    (hd : ∀ j ∈ suffix, j < D) : padNat D suffix x < n * D ^ suffix.length := by
  induction suffix generalizing n x with
  | nil => simpa [padNat] using hx
  | cons j suffix ih =>
    have hj := hd j (by simp)
    have hstart : D * x + j < n * D := by nlinarith
    have hh := ih hstart (fun j hj => hd j (by simp [hj]))
    simpa only [padNat, List.foldl_cons, List.length_cons, pow_succ,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hh

omit [Fact P.Prime] in
/-- Finite-horizon no-wrap condition charges both stage growth and copy suffix
length before the prime is supplied. It says nothing about unbounded stages. -/
theorem padNat_lt_prime (H : Horizon P) {D n x : ℕ} (hx : x < n) (suffix : List ℕ)
    (hd : ∀ j ∈ suffix, j < D) (hb : n * D ^ suffix.length ≤ H.maxIdentifier + 1) :
    padNat D suffix x < P := by
  have hpad := padNat_bound hx suffix hd
  have hP := H.identifier_admissible
  omega

/-- The fourth-power dyadic grid is the hierarchy source grid with q=16. -/
theorem rate_eq_source_grid (k : ℕ) : rate k = (16: ℝ)⁻¹ ^ k := by
  rw [rate, inv_pow, ← pow_mul, Nat.mul_comm, pow_mul, inv_pow]
  norm_num

/-- The hierarchy detector interface lifted to fixed independent role coordinates.
Both padded identifier maps may differ, but must be injective on this stage. -/
theorem retention_environment_ident {V : Type*} (s t : Fin J)
    (is it : V → ZMod P) (his : Function.Injective is) (hit : Function.Injective it)
    (H : Horizon P) {k : ℕ} (hk : k ≤ H.maxExponent) :
    RetentionChannels
      (fun (σ : Environment P J) v => frameRetains P 4 (side P k) (σ s) (is v))
      (fun (σ : Environment P J) v => frameRetains P 4 (side P k) (σ t) (it v))
      (rate k) (((side P k: ℝ) / P) ^ 4) 1 16 32 8 := by
  classical
  have ha : ((2: ℝ) ^ k)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hs := retentionChannels_frameRetains_of_lt his (H := 4) (r := 1)
    (by decide) (by decide) (horizon_admissible H hk) ha
  have ht := retentionChannels_frameRetains_of_lt hit (H := 4) (r := 1)
    (by decide) (by decide) (horizon_admissible H hk) ha
  norm_num only [← side_eq_ceil] at hs ht
  refine ⟨fun v => density s _ (side_le P k) _, fun v => density t _ (side_le P k) _,
    hs.lower, hs.upper, ?_, ?_⟩
  · intro w y hwy
    rw [dens_filter_pi_eval t (fun A : FrameChannel P 4 1 =>
      frameRetains P 4 (side P k) A (it w) ∧ frameRetains P 4 (side P k) A (it y)),
      dens_filter_pi_eval t (fun A : FrameChannel P 4 1 =>
        frameRetains P 4 (side P k) A (it y))]
    exact ht.pair w y hwy
  · intro A hA
    rw [dens_filter_pi_eval s (fun B : FrameChannel P 4 1 =>
      2 * (#{v ∈ A | frameRetains P 4 (side P k) B (is v)} : ℝ) <
        #A * ((side P k: ℝ) / P) ^ 4)]
    exact hs.tail A hA

/-- Concrete finite-horizon hierarchy entry bound with the frame constants.
It applies the general hierarchy theorem, never the unrestricted-affine corollary.
No admissibility is claimed beyond the stages strictly before l. -/
theorem hierarchy_prefix_bound (HP : HierarchyParams 16 1 16 32 8)
    {V : ℕ → Type*} [∀ i, Fintype (V i)] [∀ i, LinearOrder (V i)]
    (e : ∀ i, V (i + 1) ≃ Lex (V i × Fin (HP.m + 1)))
    (he : ∀ i a b, e i a < e i b → a < b)
    (R : RoleProfile J) (ids idt : ∀ i, V i → ZMod P)
    (H : Horizon P) (l : ℕ) (hl : l ≤ H.maxExponent + 1)
    (his : ∀ i < l, Function.Injective (ids i))
    (hit : ∀ i < l, Function.Injective (idt i))
    (S : Matrix (V 0) (V 0) ℝ) (hS : S.IsStrictUpperTriangular)
    (hS0 : ∀ x y, 0 ≤ S x y) (hS1 : S *ᵥ 1 ≤ 1) :
    let X := fun i (σ : Environment P J) v => frameRetains P 4 (side P i) (σ R.source) (ids i v)
    let Y := fun i (σ : Environment P J) v => frameRetains P 4 (side P i) (σ R.terminal) (idt i v)
    (hierarchy HP e X Y S l).IsStrictUpperTriangular ∧
      (∀ x y, 0 ≤ hierarchy HP e X Y S l x y) ∧
      hierarchy HP e X Y S l *ᵥ 1 ≤ 1 ∧
      ∀ x y, hierarchy HP e X Y S l x y ≤ rate l := by
  classical
  dsimp only
  rw [rate_eq_source_grid]
  apply hierarchy_invariant he (π := fun i => ((side P i: ℝ) / P) ^ 4)
    (by norm_num) (by norm_num) hS hS0 hS1 l
  intro i hi
  have hh := retention_environment_ident R.source R.terminal (ids i) (idt i)
    (his i hi) (hit i hi) H (show i ≤ H.maxExponent by omega)
  rwa [rate_eq_source_grid] at hh

/-- Exact density of any actual channel whose real rate has a natural grid
certificate; no density oracle remains in importance weights. -/
theorem channel_density (D : ZMod P) (ch : Channel P J) (k : ℕ)
    (hk : ch.rate = rate k) (v : ZMod P) :
    (dens {σ : Environment P J | ch.retains (channels D) σ v} : ℝ) =
      ((side P k: ℝ) / P) ^ 4 := by
  classical
  simp only [CorrectionRowTask.Channel.retains, channels, hk, semanticSide_grid]
  exact density ch.role _ (side_le P k) _

/-- Actual importance ratios are ratios of the two exact frame densities. -/
theorem usageRatio_grid {k : ℕ} (D : ZMod P) (endpoint : Channel P J)
    (r : HierarchyTask.Request k (Fin J) (ZMod P)) (ke ku : ℕ)
    (he : endpoint.rate = rate ke) (hu : r.usage.rate = rate ku) (y : ZMod P) :
    HierarchyTask.usageRatio (channels D) endpoint r y =
      ((side P ke: ℝ) / P) ^ 4 / ((side P ku: ℝ) / P) ^ 4 := by
  rw [HierarchyTask.usageRatio, channel_density D endpoint ke he,
    channel_density D r.usage ku hu]

/-- Joint padding invariance includes every independent role, at the same P. -/
theorem padding_law {D : ZMod P} (hD : D ≠ 0) (suffix : List (ZMod P))
    (E : (Fin J → ZMod P → Fin 4 → ZMod P) → Prop) [DecidablePred E] :
    dens {σ : Environment P J | E (fun c x => (σ c).eval (CopyPadding.identifier D suffix x))} =
      dens {σ : Environment P J | E (fun c => (σ c).eval)} := by
  have h := dens_pi_eval_comp_affine (H := 4) (r := 1) (pow_ne_zero suffix.length hD)
    (CopyPadding.identifier D suffix 0) E
  have he : ({σ : Environment P J | E (fun c x =>
      (σ c).eval (CopyPadding.identifier D suffix x))} : Finset _) =
      ({σ : Environment P J | E (fun c x =>
        (σ c).eval (D ^ suffix.length * x + CopyPadding.identifier D suffix 0))} : Finset _) := by
    ext σ
    simp only [mem_filter, mem_univ, true_and]
    exact iff_of_eq (congrArg E (funext fun c => funext fun x =>
      congrArg (σ c).eval (CopyPadding.identifier_affine D suffix x)))
  rw [he]
  exact h

/-- A fully concrete radix hierarchy prefix under one global supplied prime.
Stage cardinalities and queried exponent horizon are explicit finite premises. -/
theorem hierarchy_radix_prefix (HP : HierarchyParams 16 1 16 32 8)
    (R : RoleProfile J) (H : Horizon P) (n l : ℕ) (hl : l ≤ H.maxExponent + 1)
    (ss st : ℕ → List (ZMod P)) (hD : (HP.m + 1 : ZMod P) ≠ 0)
    (hcard : ∀ i < l, n * (HP.m + 1) ^ i ≤ H.maxIdentifier + 1)
    (S : Matrix (Fin (n * (HP.m + 1) ^ 0)) (Fin (n * (HP.m + 1) ^ 0)) ℝ)
    (hS : S.IsStrictUpperTriangular) (hS0 : ∀ x y, 0 ≤ S x y) (hS1 : S *ᵥ 1 ≤ 1) :
    let V := fun i => Fin (n * (HP.m + 1) ^ i)
    let ids := fun i (v : V i) => CopyPadding.identifier (HP.m + 1 : ZMod P) (ss i) (v: ZMod P)
    let idt := fun i (v : V i) => CopyPadding.identifier (HP.m + 1 : ZMod P) (st i) (v: ZMod P)
    let X := fun i (σ : Environment P J) v => frameRetains P 4 (side P i) (σ R.source) (ids i v)
    let Y := fun i (σ : Environment P J) v => frameRetains P 4 (side P i) (σ R.terminal) (idt i v)
    let C := hierarchy HP (radixCopyEquiv n HP.m) X Y S l
    C.IsStrictUpperTriangular ∧ (∀ x y, 0 ≤ C x y) ∧ C *ᵥ 1 ≤ 1 ∧
      ∀ x y, C x y ≤ rate l := by
  classical
  exact hierarchy_prefix_bound HP (radixCopyEquiv n HP.m) (fun _ _ _ => radixCopyEquiv_lt _ _ _)
    R _ _ H l hl
    (fun i hi => bounded_identifier_injective H (hcard i hi) hD (ss i))
    (fun i hi => bounded_identifier_injective H (hcard i hi) hD (st i)) S hS hS0 hS1

/-- The public-id full slice for a spectator role is an equality, not a
nonempty witness hiding a frozen coordinate. -/
theorem free_role (s t j : Fin J) (hjs : j ≠ s) (hjt : j ≠ t)
    (Ls Lt : ℕ) (a b : ZMod P) :
    pairSide (P := P) s t Ls Lt j = P ∧ pairId s t a b j = 0 := by
  simp [pairSide, pairId, hjs, hjt]

/-- Explicit one-step operator identity for the graph actually used by noise:
transport an ordinary lazy component move, then recover every rank role. -/
theorem graph_walk (s t : Fin J) (hst : s ≠ t) (Ls Lt : ℕ)
    [NeZero Ls] [NeZero Lt] (hs : Ls ≤ P) (ht : Lt ≤ P)
    (a b : V → ZMod P) (x z : V)
    (f : RetainedPairSlice (X s Ls a) (Y t Lt b) x z → ℝ)
    (σ : RetainedPairSlice (X s Ls a) (Y t Lt b) x z) :
    (graph s t hst Ls Lt hs ht a b x z).walk f σ =
      (ofPerms (componentMove 4 1 (fun _ : Fin J => P) (pairSide (P := P) s t Ls Lt))).lazy.walk
        (fun c => f ((pairEquiv s t hst Ls Lt a b x z).symm
          ((componentEquiv 1 (pairSide_le s t Ls Lt hs ht) (pairId s t (a x) (b z))).symm c)))
        (componentEquiv 1 (pairSide_le s t Ls Lt hs ht) (pairId s t (a x) (b z))
          (pairEquiv s t hst Ls Lt a b x z σ)) := rfl

/-- Normalized-main formula on this client's actual single environment. Raw
ranks are evaluated before clipping; the denominator is the actual preparatory
conditional mean clipped to [1 / 2, 1]. -/
theorem normalizedRequest_formula [Fintype V] {k : ℕ} (D : ZMod P) (ident : V → ZMod P)
    (r : HierarchyTask.Request k (Fin J) (ZMod P)) (hr : Admissible r)
    (cutoff gate : ℝ → ℝ) (K : ℕ)
    (raw prep : Environment P J → Matrix V V ℝ)
    (σ : Environment P J) (x y : V) :
    normalizedRequest D ident r cutoff gate K raw prep σ x y =
      if r.usage.retains (channels D) σ (ident y) then
        cutoff (raw σ x y / r.terminal.rate) *
          rowGate gate K r.terminal.rate (raw σ)
            {v | r.terminal.retains (channels D) σ (ident v)} x /
          max (1 / 2) (min 1 (rowSliceMean
            (fun τ v => r.source.retains (channels D) τ (ident v))
            (fun τ v => r.usage.retains (channels D) τ (ident v)) prep x y))
      else 0 := by
  classical
  rw [normalizedRequest, dite_eq_left hr]
  dsimp only
  rw [DenseRowRecipe.normalized, normalizer_full D ident r hr prep x y]
  simp only [Equiv.piSplitAt_apply, coordinate, CorrectionRowTask.Channel.retains,
    channels, hr.2.1]
  congr 6

/-- The source grid has exactly the requested adjacent-bin ratio. -/
theorem adjacent_rate_ratio (k : ℕ) : rate k / rate (k + 1) = 16 := by
  rw [rate_eq_source_grid, rate_eq_source_grid, pow_succ]
  have h : (16: ℝ)⁻¹ ^ k ≠ 0 := by positivity
  field_simp

omit [Fact P.Prime] in
/-- Raw call construction preserves a supplied finite exponent horizon. This
is local call closure, not closure of every estimator guard / enumeration query. -/
theorem raw_grid_bounded {k : ℕ} (R : RoleProfile J) (l bin K ks km kt kb : ℕ)
    (hs : ks ≤ K) (hm : km ≤ K) (ht : kt ≤ K) (hb : kb ≤ K)
    (ss sm st : List (ZMod P)) (r : HierarchyTask.Request k (Fin J) (ZMod P))
    (hr : r ∈ (HierarchyTask.rawRequests l bin .residual
      (gridChannel R.source ks ss) (gridChannel R.midpoint km sm)
      (gridChannel R.terminal kt st) (rate kb)).calls) :
    ∃ es et eu, es ≤ K ∧ et ≤ K ∧ eu ≤ K ∧ r.source.rate = rate es ∧
      r.terminal.rate = rate et ∧ r.usage.rate = rate eu := by
  simp only [HierarchyTask.rawRequests, HierarchyTask.RawRequests.calls,
    Option.toList_some, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl) | rfl
  · exact ⟨ks, kb, max kt kb, hs, hb, max_le ht hb, rfl, rfl, rate_min kt kb⟩
  · exact ⟨ks, km, km, hs, hm, hm, rfl, rfl, rfl⟩
  · exact ⟨km, kb, max kt kb, hm, hb, max_le ht hb, rfl, rfl, rate_min kt kb⟩
  · exact ⟨ks, km, max kt km, hs, hm, max_le ht hm, rfl, rfl, rate_min kt km⟩

/-- A finite horizon is satisfiable for every supplied prime. Larger horizons
retain their explicit side and identifier premises rather than a global claim. -/
@[expose] def zeroHorizon : Horizon P where
  maxExponent := 0
  maxIdentifier := P-1
  side_admissible := by simpa only [pow_zero] using (Fact.out : P.Prime).one_le
  identifier_admissible := Nat.sub_lt (Fact.out : P.Prime).pos (by decide)

/-- Actual incoming-gated main correction normalization on the entire rank
environment, with raw row / incoming ranks and the inherited source / usage mean.
This evaluates the recipe; it does not assert its later incoming-margin laws. -/
@[expose] noncomputable def correctionRequest [Fintype V] {k : ℕ}
    (D : ZMod P) (ident : V → ZMod P)
    (r : HierarchyTask.Request k (Fin J) (ZMod P))
    (I : ℝ → ℝ → ℝ) (τ ρ Q γ : ℝ → ℝ) (K Kc : ℕ)
    (raw prep : Environment P J → Matrix V V ℝ)
    (maximum : Environment P J → V → ℝ) (σ : Environment P J) (x y : V) : ℝ :=
  if h : Admissible r then
    let split := Equiv.piSplitAt r.terminal.role (fun _ : Fin J => FrameChannel P 4 1)
    CorrectionRowRecipe.normalized I τ ρ Q γ K Kc r.terminal.rate
      (fun rest x => coordinate D r.source (rest ⟨r.source.role, h.1⟩) (ident x))
      (fun A v => coordinate D r.terminal A (ident v))
      (fun A v => coordinate D r.usage A (ident v)) (raw σ)
      (fun p => prep (split.symm (p.2, p.1))) (maximum σ)
      ((split σ).2, (split σ).1) x y
  else 0

/-- Actual residual calls use dense base bins, incoming-gated main correction
children, and a literal zero at correction iteration zero. No callback supplies
the environment model, slice representation, walk identity or noise bound. -/
@[expose] noncomputable def rawIncomingNormalized [Fintype V] {k : ℕ}
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (D : ZMod P) (ident : V → ZMod P)
    (R : RoleProfile J)
    (l bin ks km kt kb : ℕ) (ss sm st : List (ZMod P))
    (I : ℝ → ℝ → ℝ) (τ : ℝ → ℝ) (Kc : ℕ) (binCutoff : ℝ → ℝ)
    (raw prep : HierarchyTask.Request k (Fin J) (ZMod P) →
      Environment P J → Matrix V V ℝ)
    (maximum : HierarchyTask.Request k (Fin J) (ZMod P) → Environment P J → V → ℝ)
    (σ : Environment P J) : Matrix V V ℝ :=
  HierarchyTask.rawSample (fun role b suffix σ v => channels D role b suffix σ (ident v))
    l bin .residual (gridChannel R.source ks ss) (gridChannel R.midpoint km sm)
    (gridChannel R.terminal kt st) (rate kb) (fun r =>
      match r.task with
      | .row _ (.correction _) => 0
      | .row _ (.normalized _) => correctionRequest D ident r I τ HP.ρ
          HP.toHierarchyParams.atomCutoff HP.γ HP.K Kc (raw r) (prep r) (maximum r) σ
      | _ => normalizedRequest D ident r binCutoff HP.ρ HP.K (raw r) (prep r) σ)

/-- Integrated contraction for actual raw residual requests with incoming-gated
normalized main children, including source-released product-right and negative
correction. Every earlier raw / preparatory / pilot child may depend on all rank roles.
The bound retains the raw input fourth moment, not an assumed output certificate. -/
theorem rawIncomingNormalized_noise [Fintype V] {k : ℕ}
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (D : ZMod P) (ident : V → ZMod P)
    (R : RoleProfile J)
    (l bin ks km kt kb : ℕ) (ss sm st : List (ZMod P))
    (I : ℝ → ℝ → ℝ) (τ : ℝ → ℝ) (Kc : ℕ) (binCutoff : ℝ → ℝ)
    (raw prep : HierarchyTask.Request k (Fin J) (ZMod P) →
      Environment P J → Matrix V V ℝ)
    (maximum : HierarchyTask.Request k (Fin J) (ZMod P) → Environment P J → V → ℝ)
    {N u : ℝ} (hNu : 0 ≤ N * u) (steps : ℕ) :
    let a := fun v => CopyPadding.identifier D ss (ident v)
    let b := fun v => CopyPadding.identifier D st (ident v)
    let F := rawIncomingNormalized HP D ident R l bin ks km kt kb ss sm st
      I τ Kc binCutoff raw prep maximum
    let G := graph R.source R.terminal R.source_terminal (side P ks) (side P kt)
      (side_le P ks) (side_le P kt) a b
    rowNormPow 4 N u (X R.source (side P ks) a) (Y R.terminal (side P kt) b)
      (fun σ x z => conditionalWalk (X R.source (side P ks) a)
        (Y R.terminal (side P kt) b) G (fun _ _ => steps) F σ x z -
        rowSliceMean (X R.source (side P ks) a) (Y R.terminal (side P kt) b) F x z) ≤
      32 * (1 - 1 / (155648 * (J + 1) * (4: ℝ) ^ 4)) ^ (2 * steps) *
        rowNormPow 4 N u (X R.source (side P ks) a) (Y R.terminal (side P kt) b) F := by
  exact noise R.source R.terminal R.source_terminal _ _ (side_le P ks) (side_le P kt) _ _
    hNu steps _

/-- Exact-route dependence for the incoming-gated client itself. -/
theorem rawIncomingNormalized_rank_dependency [Fintype V] {k : ℕ} {Input : Type*}
    (ranks : Input → Environment P J) (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (D : ZMod P) (ident : V → ZMod P)
    (R : RoleProfile J)
    (l bin ks km kt kb : ℕ) (ss sm st : List (ZMod P))
    (I : ℝ → ℝ → ℝ) (τ : ℝ → ℝ) (Kc : ℕ) (binCutoff : ℝ → ℝ)
    (raw prep : HierarchyTask.Request k (Fin J) (ZMod P) →
      Environment P J → Matrix V V ℝ)
    (maximum : HierarchyTask.Request k (Fin J) (ZMod P) → Environment P J → V → ℝ)
    {a b : Input} (hab : ∀ j, ranks a j = ranks b j) :
    rawIncomingNormalized HP D ident R l bin ks km kt kb ss sm st
      I τ Kc binCutoff raw prep maximum (ranks a) =
    rawIncomingNormalized HP D ident R l bin ks km kt kb ss sm st
      I τ Kc binCutoff raw prep maximum (ranks b) := by
  rw [show ranks a = ranks b from funext hab]

end Matrix.HierarchyParams.H4RankEnvironment
