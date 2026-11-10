/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.LogSpaceDerandomization.HierarchyTasks
public import CslibFrontier.Computability.LogSpaceDerandomization.ScheduledFineProductMean
public import CslibFrontier.Computability.LogSpaceDerandomization.PairwiseIndependentHash.AtomChannels
public import CslibFrontier.Probability.PairwiseIndependentHash.FrameSubstitution

/-!
# Routed bins of the actual correction-and-copy hierarchy

The cutoff `routedBinCutoff` is (5.9) of [OpenAI2026LogSpace, Section 5.2], revision
`7ef5c0cc`: destination routing is evaluated at the raw residual entry, before averaging.
`DenseSamplingLaws` contains only gate and pair-count conditions, and constructs the actual
`denseAtom`. Its direct importance-weighted mean follows from those conditions. Finite bin
sums use the existing partition of unity; their coverage condition is explicit, including zeros.
The hierarchy client gives the next actual matrix on each fixed source/destination symbol part.
This module supplies true-input means. The shared arbitrary-child cutoffs live in
`DenseRowRecipes`; global preparatory and normalized requests live in `HierarchyAccess`.
No parallel routed transition matrix or assumed mean certificate is introduced.

Requests retain whole functions, source/end/usage rates and independent roles. Copy traversal
prepends a symbol before the inherited suffix. The product's right request resets the source to
the midpoint channel. Its actual inputs are the existing `HierarchyTask` values and its rank
inequalities use that task order. The scheduled coarse/fine payment lemmas consume those ranks.
This is a direct/routed-residual client, not full recursive stochastic task assembly: residual
raw estimation, estimated routing fractions, preparation access, complete mean prefixes, paired
raw differences, full-coordinate conditional walks/noise, compression and statistical-budget
recursion remain open. Gate contracts do not establish root regularity. Scheduled bounds retain
fourth moments (the source uses eighth moments) and integer scale offsets. No native workspace
or complexity claim is made for these finite noncomputable functions.
-/

public section

open Finset
open scoped BigOperators

namespace Matrix

variable {V Ω : Type*} [Fintype V] [Fintype Ω]
  (Y Ya Yt : Ω → V → Prop)
  [∀ s v, Decidable (Y s v)] [∀ s v, Decidable (Ya s v)] [∀ s v, Decidable (Yt s v)]
  (k : ℝ → ℝ) (b M : ℝ)

/-- Primitive dense-bin laws. The true input's nonnegativity and row mass are proved by
clients; neither a desired mean nor a noise bound is a field. -/
structure DenseSamplingLaws where
  /-- Preparation support cutoff. -/
  h : ℝ → ℝ
  /-- Row gate. -/
  ρ : ℝ → ℝ
  /-- Row rank. -/
  K : ℕ
  /-- Safe row threshold. -/
  η : ℝ
  /-- Conditional terminal pair constant. -/
  c : ℝ
  /-- Usage lies inside the parent's conditioning channel. -/
  usage_subset : ∀ s y, Yt s y → Ya s y
  /-- Every usage conditioning event is nonempty. -/
  usage_nonempty : ∀ y, ({s | Yt s y} : Finset Ω).Nonempty
  /-- Preparation is one on the cutoff support. -/
  support : ∀ d, k d ≠ 0 → h d = 1
  /-- Nonnegative gate. -/
  gate_nonneg : ∀ r, 0 ≤ ρ r
  /-- Gate bounded by one. -/
  gate_le_one : ∀ r, ρ r ≤ 1
  /-- Positive safe threshold. -/
  η_pos : 0 < η
  /-- Gate full through the safe threshold. -/
  gate_one : ∀ r, r ≤ η → ρ r = 1
  /-- Nonnegative pair constant. -/
  c_nonneg : 0 ≤ c
  /-- Rank sufficient for true normalization. -/
  rank_bound : 2 * (1 + c * M / η) ≤ K
  /-- Cross-rate count conditional on the actual usage hit. -/
  pair : ∀ y w, w ≠ y → (#{s | Yt s y ∧ Y s w} : ℝ) ≤ c * b * #{s | Yt s y}

namespace DenseSamplingLaws

variable {Y Ya Yt k b M} (A : DenseSamplingLaws Y Ya Yt k b M)

/-- Actual atom; row and endpoint stay function arguments. -/
@[expose] noncomputable def atom (G : Matrix V V ℝ) : Ω → Matrix V V ℝ :=
  denseAtom Y Yt k A.h A.ρ A.K b G

/-- The raw direct term in original matrix units, on the broad terminal slice. -/
@[expose] noncomputable def direct (G : Matrix V V ℝ) (s : Ω) (x y : V) : ℝ :=
  b * ((dens {s | Ya s y} : ℝ) / dens {s | Yt s y}) * A.atom G s x y

/-- True direct mean, derived from row gates and cross-rate channel laws. -/
theorem expect_direct (hb : 0 < b) {G : Matrix V V ℝ}
    (hG : ∀ x y, 0 ≤ G x y) (hGM : ∀ x, ∑ y, G x y ≤ M) (x y : V) :
    (𝔼 s ∈ ({s | Ya s y} : Finset Ω), A.direct G s x y) = b * k (G x y / b) :=
  expect_denseAtom_change_usage (fun s => A.usage_subset s y) (A.usage_nonempty y)
    A.support A.gate_nonneg A.gate_le_one A.η_pos A.gate_one hb (hG x) (hGM x)
    A.c_nonneg A.rank_bound (A.pair y)

/-- Independent source conditioning leaves a true direct bin unchanged. The source argument
is still available to estimated child functions, rather than being stored in their task tuple. -/
theorem expect_direct_source {Γ : Type*} [Fintype Γ] (X : Γ → V → Prop)
    [∀ s x, Decidable (X s x)] (hb : 0 < b) {G : Matrix V V ℝ}
    (hG : ∀ x y, 0 ≤ G x y) (hGM : ∀ x, ∑ y, G x y ≤ M)
    (x y : V) (hx : ({s | X s x} : Finset Γ).Nonempty) :
    (𝔼 s ∈ ({s | X s x} : Finset Γ) ×ˢ ({t | Ya t y} : Finset Ω),
      A.direct G s.2 x y) = b * k (G x y / b) := by
  rw [expect_product]
  simp_rw [A.expect_direct hb hG hGM x y]
  exact expect_const hx _

end DenseSamplingLaws

/-- Affine channels supply the actual dense sampling conditions at distinct rank, usage and
parent conditioning sides. Only injectivity of the padded identifier is required, not an
arbitrary equivalence of all-coordinate environments. -/
noncomputable def DenseSamplingLaws.ofAffine {p H : ℕ} [Fact p.Prime]
    {ident : V → ZMod p} (hident : Function.Injective ident) {a : ℝ}
    (hpa : 1 ≤ p * a) (ha : a ≤ 1) {Lt La : ℕ} (hLt0 : 0 < Lt)
    (hLt : Lt ≤ ⌈p * a⌉₊) (hLa : Lt ≤ La)
    (k h ρ : ℝ → ℝ) (K : ℕ) (M η : ℝ)
    (hsupport : ∀ d, k d ≠ 0 → h d = 1) (hρ0 : ∀ r, 0 ≤ ρ r)
    (hρ1 : ∀ r, ρ r ≤ 1) (hη : 0 < η) (hone : ∀ r, r ≤ η → ρ r = 1)
    (hK : 2 * (1 + 2 ^ H * M / η) ≤ K) :
    DenseSamplingLaws
      (fun s v => Cslib.Probability.affineRetains p H ⌈p * a⌉₊ s (ident v))
      (fun s v => Cslib.Probability.affineRetains p H La s (ident v))
      (fun s v => Cslib.Probability.affineRetains p H Lt s (ident v)) k (a ^ H) M where
  h := h
  ρ := ρ
  K := K
  η := η
  c := 2 ^ H
  usage_subset _ _ := Cslib.Probability.affineRetains_of_le hLa
  usage_nonempty y := by
    apply dens_ne_zero.mp
    rw [Cslib.Probability.dens_affineRetains
      (hLt.trans (Cslib.Probability.affineRetains_rates (H := H) hpa ha).1)]
    have hp : (0 : ℚ≥0) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    positivity
  support := hsupport
  gate_nonneg := hρ0
  gate_le_one := hρ1
  η_pos := hη
  gate_one := hone
  c_nonneg := by positivity
  rank_bound := hK
  pair _ _ hw := Cslib.Probability.card_affineRetains_and_affineRetains_le
    hident hpa ha (hLt.trans (Cslib.Probability.affineRetains_rates (H := H) hpa ha).1) hw

namespace HierarchyParams.CorrectionSampling

variable {q cπ Cπ Cpair Cvar : ℝ} {P : HierarchyParams q cπ Cπ Cpair Cvar}
  {V Γ Ζ Ω ι κ : Type*} [Fintype V] [Fintype Γ] [Fintype Ζ] [Fintype Ω]
  [Fintype ι] [Fintype κ]
  {X : ι → V → Prop} {Y : κ → V → Prop} {Xs : Γ → V → Prop}
  {Z Zt : Ζ → V → Prop} {Yr Ya Yt : Ω → V → Prop}
  [∀ s v, Decidable (X s v)] [∀ s v, Decidable (Y s v)] [∀ s v, Decidable (Xs s v)]
  [∀ s v, Decidable (Z s v)] [∀ s v, Decidable (Zt s v)]
  [∀ s v, Decidable (Yr s v)] [∀ s v, Decidable (Ya s v)] [∀ s v, Decidable (Yt s v)]
  {f b : ℝ} {C : Matrix V V ℝ} {i : ℕ}
  (A : P.CorrectionSampling X Y Xs Z Zt f C i)
  {k : ℝ → ℝ} (B : DenseSamplingLaws Yr Ya Yt k b 1)

/-- The real raw product recipe accepts whole earlier functions; its right row is called at
`z`. There is no old-source or fixed-endpoint parameter in that child. -/
@[expose] noncomputable def binProductRecipe (F : Γ × Ζ → Matrix V V ℝ)
    (H : Ω → Matrix V V ℝ) (draw : (Γ × Ζ) × Ω) (x y : V) : ℝ :=
  let (left, right) := draw
  b * ((dens {s | Ya s y} : ℝ) / dens {s | Yt s y}) * (f / A.π) *
    ∑ z, F left x z * H right z y

/-- True product mean from the actual correction and bin gate laws. In particular the
shared midpoint source role does not survive in the true right atom after its membership
condition has been fixed. Estimated factors need joint comparisons, not this factorization. -/
theorem expect_binProductRecipe (hf : 0 < f) (hb : 0 < b)
    (hC : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1) (x y : V)
    (hx : ({s | Xs s x} : Finset Γ).Nonempty) :
    (𝔼 draw ∈ (({s | Xs s x} : Finset Γ) ×ˢ (univ : Finset Ζ)) ×ˢ
      ({s | Ya s y} : Finset Ω),
        A.binProductRecipe (Ya := Ya) (Yt := Yt) (b := b) A.atom (B.atom C) draw x y) =
      ∑ z, P.correctionIter X Y f C (i + 1) x z * (b * k (C z y / b)) := by
  have hrow (z : V) : ∑ w, C z w ≤ 1 := by
    simpa only [mulVec, dotProduct, Pi.one_apply, mul_one] using hC1 z
  simp only [binProductRecipe, mul_sum]
  rw [expect_sum_comm]
  apply sum_congr rfl
  intro z _
  calc
    _ = 𝔼 draw ∈ (({s | Xs s x} : Finset Γ) ×ˢ (univ : Finset Ζ)) ×ˢ
        ({s | Ya s y} : Finset Ω),
        ((f / A.π) * A.atom draw.1 x z) * B.direct C draw.2 z y := by
      apply expect_congr rfl
      intro draw _
      dsimp only [DenseSamplingLaws.direct]
      ring
    _ = _ := by
      rw [expect_product]
      dsimp only
      rw [← expect_mul_expect, A.expect_atom hf hC hC1 hx, B.expect_direct hb hC hrow]

end HierarchyParams.CorrectionSampling

namespace CopyPadding

/-- Native hash padding: append each digit from left to right. -/
@[expose] def identifier {p : ℕ} (D : ZMod p) (suffix : List (ZMod p)) (x : ZMod p) : ZMod p :=
  suffix.foldl (fun x j => D * x + j) x

/-- Prepending the copy symbol means appending it to the native identifier first. -/
theorem identifier_cons {p : ℕ} (D j : ZMod p) (suffix : List (ZMod p)) (x : ZMod p) :
    identifier D (j :: suffix) x = identifier D suffix (D * x + j) := rfl

/-- Native radix-copy identifiers obey exactly the same prepend-before-suffix recipe. -/
theorem identifier_radixCopy {p : ℕ} (n m l : ℕ)
    (x : Fin (n * (m + 1) ^ l)) (j : Fin (m + 1)) (suffix : List (ZMod p)) :
    identifier (m + 1 : ZMod p) ((j : ZMod p) :: suffix) (x : ZMod p) =
      identifier (m + 1 : ZMod p) suffix
        (((radixCopyEquiv n m l).symm (toLex (x, j))).val : ZMod p) := by
  rw [identifier_cons]
  congr 1
  have h := radixCopyEquiv_val n m l ((radixCopyEquiv n m l).symm (toLex (x, j)))
  simp only [Equiv.apply_symm_apply, ofLex_toLex] at h
  rw [h]
  push_cast
  ring

/-- A common fixed suffix is the affine substitution used by the channel invariance law. -/
theorem identifier_affine {p : ℕ} (D : ZMod p) (suffix : List (ZMod p)) (x : ZMod p) :
    identifier D suffix x = D ^ suffix.length * x + identifier D suffix 0 := by
  induction suffix generalizing x with
  | nil => simp [identifier]
  | cons j suffix ih =>
    rw [identifier_cons, identifier_cons, ih (D * x + j), ih (D * 0 + j)]
    simp only [List.length_cons, pow_succ]
    ring

/-- Padding preserves distinct identifiers when the radix is nonzero modulo the prime. -/
theorem identifier_injective {p : ℕ} [Fact p.Prime] {D : ZMod p} (hD : D ≠ 0)
    (suffix : List (ZMod p)) : Function.Injective (identifier D suffix) := by
  intro x y h
  have heq := (identifier_affine D suffix x).symm.trans
    (h.trans (identifier_affine D suffix y))
  exact mul_left_cancel₀ (pow_ne_zero _ hD) (add_right_cancel heq)

/-- The exact joint frame law for native padding follows from affine substitution.
This is distributional invariance, not pointwise equality of arbitrary environments. -/
theorem dens_frame_padding {p H r : ℕ} [Fact p.Prime] {D : ZMod p} (hD : D ≠ 0)
    (suffix : List (ZMod p))
    (E : (ZMod p → Fin H → ZMod p) → Prop) [DecidablePred E] :
    dens {A : Cslib.Probability.FrameChannel p H r |
      E (fun x => A.eval (identifier D suffix x))} =
      dens {A : Cslib.Probability.FrameChannel p H r | E A.eval} := by
  have hset : ({A : Cslib.Probability.FrameChannel p H r |
      E (fun x => A.eval (identifier D suffix x))} : Finset _) =
      ({A : Cslib.Probability.FrameChannel p H r |
        E (fun x => A.eval (D ^ suffix.length * x + identifier D suffix 0))} : Finset _) := by
    ext A
    simp only [mem_filter, mem_univ, true_and]
    exact iff_of_eq (congrArg E (funext fun x =>
      congrArg A.eval (identifier_affine D suffix x)))
  rw [hset]
  exact Cslib.Probability.dens_eval_comp_affine (pow_ne_zero _ hD) _ E

end CopyPadding

namespace HierarchyParams.CorrectionRowTask.Channel

/-- Append the native copy digit before every already inherited suffix digit. -/
@[expose] def throughCopy {Role Symbol : Type*} (ch : CorrectionRowTask.Channel Role (List Symbol))
    (j : Symbol) : CorrectionRowTask.Channel Role (List Symbol) :=
  { ch with suffix := j :: ch.suffix }

/-- A second descent prepends its symbol before the first one; neither inherited digit is lost. -/
theorem throughCopy_twice {Role Symbol : Type*}
    (ch : CorrectionRowTask.Channel Role (List Symbol)) (i j : Symbol) :
    ((ch.throughCopy i).throughCopy j).suffix = j :: i :: ch.suffix := rfl

end HierarchyParams.CorrectionRowTask.Channel

namespace HierarchyParams.HierarchyTask

open CorrectionRowTask

/-- Whole-function request in the existing global task order, with concrete channel tuples. -/
structure Request (k : ℕ) (Role Symbol : Type*) where
  /-- Actual bounded constructor, not a duplicate matrix hierarchy. -/
  task : HierarchyTask k
  /-- Source role, rate and fixed suffix. -/
  source : Channel Role (List Symbol)
  /-- Endpoint conditioning role, rate and fixed suffix. -/
  terminal : Channel Role (List Symbol)
  /-- Endpoint usage role, rate and fixed suffix. -/
  usage : Channel Role (List Symbol)

/-- Raw input calls in direct/left/right order. Endpoint and midpoint remain arguments of
these whole child functions; the right child resets the source tuple completely. -/
@[expose] def inputRequests {k : ℕ} {Role Symbol : Type*} (l : ℕ) (i : Fin k)
    (source midpoint terminal usage : Channel Role (List Symbol)) :
    List (Request k Role Symbol) :=
  [⟨.row l .base, source, terminal, usage⟩,
   ⟨.row l (.correction i.castSucc), source, midpoint, midpoint⟩,
   ⟨.row l .base, midpoint, terminal, usage⟩]

/-- Fixed-symbol projection calls the actual parent base/correction/weights. Its source and
terminal channels prepend their respective symbols; the midpoint has no copy symbol appended.
The weight is evaluated on the broad parent source domain by the copy recipe. -/
@[expose] def copyRequests {k : ℕ} {Role Symbol : Type*} (l : ℕ)
    (source midpoint terminal usage : Channel Role (List Symbol)) (i j : Symbol) :
    List (Request k Role Symbol) :=
  [⟨.row l .base, source.throughCopy i, terminal.throughCopy j, usage.throughCopy j⟩,
   ⟨.row l (.correction (Fin.last k)), source.throughCopy i, midpoint, midpoint⟩,
   ⟨.row l .base, midpoint, terminal.throughCopy j, usage.throughCopy j⟩,
   ⟨.row l .weights, { source.throughCopy i with rate := midpoint.rate },
     terminal.throughCopy j, usage.throughCopy j⟩]

/-- The bin rank uses rate `b`; usage uses `min a b` on the same endpoint role and suffix.
The midpoint remains at the stage rate. These are the actual tuples of (7.1)–(7.2). -/
@[expose] def binInputRequests {k : ℕ} {Role Symbol : Type*} (l : ℕ) (i : Fin k)
    (source midpoint endpoint : Channel Role (List Symbol)) (b : ℝ) :
    List (Request k Role Symbol) :=
  inputRequests l i source midpoint { endpoint with rate := b }
    { endpoint with rate := min endpoint.rate b }

/-- Projection uses the same bin/usage convention, with different source/destination symbols. -/
@[expose] def binCopyRequests {k : ℕ} {Role Symbol : Type*} (l : ℕ)
    (source midpoint endpoint : Channel Role (List Symbol)) (b : ℝ) (i j : Symbol) :
    List (Request k Role Symbol) :=
  copyRequests l source midpoint { endpoint with rate := b }
    { endpoint with rate := min endpoint.rate b } i j

/-- The raw-input requests decrease the existing global rank, including the repeated base call. -/
theorem inputRequests_rank_lt {k : ℕ} {Role Symbol : Type*} (l : ℕ) (i : Fin k)
    (source midpoint terminal usage : Channel Role (List Symbol))
    (r : Request k Role Symbol) (hr : r ∈ inputRequests l i source midpoint terminal usage) :
    r.task.rank < (row l (.input i)).rank := by
  simp only [inputRequests, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;>
    apply rank_lt_of_dependency <;> apply Dependency.rowChild <;>
    simp [CorrectionRowTask.children, BoundedRowTask.localTask]

/-- All fixed-symbol copy calls precede the existing actual next-matrix constructor. -/
theorem copyRequests_rank_lt {k : ℕ} {Role Symbol : Type*} (l : ℕ)
    (source midpoint terminal usage : Channel Role (List Symbol)) (i j : Symbol)
    (r : Request k Role Symbol) (hr : r ∈ copyRequests l source midpoint terminal usage i j) :
    r.task.rank < (nextMatrix (k := k) l).rank := by
  simp only [copyRequests, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact row_rank_lt_nextMatrix _ _

/-- Computed cross-stage ranks pay the scheduled coarse or fine child root bound.
The actual source reset is supplied by the request's source tuple; no independence of errors
is required. The two branches are the existing scheduled mean-comparison payments. -/
theorem scheduled_request_error_le {k : ℕ} {Role Symbol : Type*}
    (parent : HierarchyTask k) (r : Request k Role Symbol) (hr : r.task.rank < parent.rank)
    {A C a b c₁ u E : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (ha : 0 < a) (hb : 0 < b)
    (hc₁ : 0 < c₁) (hba : c₁ * b ≤ r.terminal.rate) (hu : 0 < u) (huur : u ≤ r.source.rate)
    (M d c : ℕ) (hc : 0 < c) (offset : ℤ)
    (hscale : Real.logb 2 (b / a) = (offset : ℝ))
    (hE : E ≤ (C * (2 : ℝ) ^ (-Cslib.LogSpaceEstimation.precision (16 * c) A
      (Cslib.LogSpaceEstimation.lastBudget M d c offset) r.task.rank
        r.terminal.rate r.source.rate)) ^ 4) :
    (if 0 ≤ offset then b / a else (b / a) ^ 3) * (r.source.rate / u) * E ≤
      (C * (2 : ℝ) ^ (-Real.logb 2 c₁ / 2) *
        ((2 : ℝ) ^ (-Cslib.LogSpaceEstimation.precision (16 * c) A M parent.rank a u - A +
          (d : ℝ) / (16 * c) + 1 / 16) * Cslib.LogSpaceEstimation.scaleMajorant offset)) ^ 4 := by
  split_ifs with hh
  · exact Cslib.LogSpaceEstimation.scheduled_coarse_error_le hA hC M d c
      parent.rank r.task.rank hc offset hh hr ha hb hc₁ hba hu huur hscale hE
  · exact Cslib.LogSpaceEstimation.scheduled_fine_error_le hA hC M d c
      parent.rank r.task.rank hc offset (lt_of_not_ge hh) hr ha hb hc₁ hba hu huur hscale hE

end HierarchyParams.HierarchyTask

section Hierarchy

variable {q cπ Cπ Cpair Cvar : ℝ} (P : HierarchyParams q cπ Cπ Cpair Cvar)
  {V : ℕ → Type*} [∀ l, Fintype (V l)] [∀ l, LinearOrder (V l)]
  (e : ∀ l, V (l + 1) ≃ Lex (V l × Fin (P.m + 1)))
  {ι κ : ℕ → Type*} [∀ l, Fintype (ι l)] [∀ l, Fintype (κ l)]
  (X : ∀ l, ι l → V l → Prop) (Y : ∀ l, κ l → V l → Prop)
  [∀ l s v, Decidable (X l s v)] [∀ l s v, Decidable (Y l s v)]
  (S : Matrix (V 0) (V 0) ℝ)

/-- The raw argument of a routed bin is the residual of the actual detected hierarchy. -/
noncomputable abbrev hierarchyResidual (l : ℕ) : Matrix (V l) (V l) ℝ :=
  P.residual (X l) (Y l) (q⁻¹ ^ l) (hierarchy P e X Y S l)

omit [∀ l, LinearOrder (V l)] in
/-- Summing true routed direct bins gives the next actual hierarchy matrix, on every fixed
copy-symbol part. Row/gate laws are explicit; no desired conditional mean is assumed. -/
theorem sum_expect_hierarchy_routed_bins {Ω : Type*} [Fintype Ω]
    (l n : ℕ) (χ : ℝ → ℝ) (b : ℕ → ℝ) (hb : ∀ i, 0 < b i)
    (hχ : ∀ t, 1 ≤ t → χ t = 1)
    (Yr Ya Yt : Fin (P.m + 1) → Ω → V l → Prop)
    [∀ j s v, Decidable (Yr j s v)] [∀ j s v, Decidable (Ya j s v)]
    [∀ j s v, Decidable (Yt j s v)]
    (a d : V (l + 1)) (M : ℝ)
    (A : ∀ (j : Fin (P.m + 1)) i, DenseSamplingLaws (Yr j) (Ya j) (Yt j)
      (routedBinCutoff χ b i (fun w => copyFraction (P.copyCutoff (q⁻¹ ^ l)) P.m w
        j)) (b i) M)
    (hD : ∀ x y, 0 ≤ hierarchyResidual P e X Y S l x y)
    (hDM : ∀ x, ∑ y, hierarchyResidual P e X Y S l x y ≤ M)
    (hcover : hierarchyResidual P e X Y S l (ofLex (e l a)).1 (ofLex (e l d)).1 = 0 ∨
      b n ≤ hierarchyResidual P e X Y S l (ofLex (e l a)).1 (ofLex (e l d)).1) :
    (∑ i ∈ range (n + 1), P.weight (X l) (Y l) (q⁻¹ ^ l) (hierarchy P e X Y S l)
      (ofLex (e l a)).2 (ofLex (e l a)).1 *
      (𝔼 s ∈ ({s | Ya (ofLex (e l d)).2 s (ofLex (e l d)).1} : Finset Ω),
        (A (ofLex (e l d)).2 i).direct (hierarchyResidual P e X Y S l) s
          (ofLex (e l a)).1 (ofLex (e l d)).1)) = hierarchy P e X Y S (l + 1) a d := by
  simp_rw [DenseSamplingLaws.expect_direct (A _ _) (hb _) hD hDM]
  rw [← mul_sum, sum_routedBinCutoff n hb hχ hcover]
  simp only [hierarchy_succ, HierarchyParams.next_eq, submatrix_apply, copyStage, copySplit,
    of_apply]
  ring

end Hierarchy
end Matrix
