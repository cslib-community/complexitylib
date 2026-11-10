/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.LogSpaceDerandomization.RoutedHierarchyBins
import Mathlib.Tactic.Linarith

/-!
# Signed residuals and bounded routed-bin evaluation

The raw residual is `C - E + EC`, including the negative direct correction at scale `f`
[OpenAI2026LogSpace, Section 7.2, after (7.2)], revision `7ef5c0cc`. Its four children are
whole functions; the right product child is evaluated at the midpoint. No positivity is
asserted for estimated residuals. The top-bin extension clips the entire defining expression,
including its routing argument, as prescribed in Section 5.2, (5.8)–(5.9). Other bins are
extended by zero below zero and retain their original upper support.

The dense preparation and normalization evaluator accepts arbitrary completed raw and
preparatory children. Ranks inspect the raw matrix before scalar clipping. True-input
agreement and means are derived from the actual hierarchy residual bounds and primitive
sampling laws, rather than stored mean certificates. This is finite mathematical evaluation;
statistical error induction and finite-accuracy access enumeration are not proved here.
The negative correction has its own scale-`f` rank channel, separate from the bin rank channel.
The true residual fits the cap `k + 2` at top scale one, since it is nonnegative with row mass
at most one. Fine bins retain their true upper support; their uniform bound uses the
adjacent-scale ratio.

## Main definitions

* `CorrectionRowRecipe.residual`: signed completed raw function on four distinct children.
* `boundedRoutedBinCutoff`: bounded top-bin and zero-extended fine-bin scalar evaluation.
* `ResidualBinTask.value`: raw, preparatory and normalized evaluation on child functions.

## Main results

* `HierarchyParams.CorrectionSampling.expect_residualSample`: signed primitive-law means.
* `ResidualBinTask.expect_value_true`: true residual-bin evaluator mean from hierarchy bounds.

Estimated copy-weight/routing-fraction root-error comparisons and the full threshold ladder
with root/complement regularity are still needed for mean prefixes. The structural rank and
range identities do not provide statistical-budget induction. Paired raw differences,
full-coordinate walks/noise, compression, strong recursion and native workspace/class equality
remain outside this bounded client.
-/

public section

open Finset
open scoped BigOperators

namespace Matrix
namespace HierarchyParams

variable {q cπ Cπ Cpair Cvar : ℝ} (P : HierarchyParams q cπ Cπ Cpair Cvar)
  {V ι κ : Type*} [Fintype V] [Fintype ι] [Fintype κ]
  (X : ι → V → Prop) (Y : κ → V → Prop)
  [∀ s v, Decidable (X s v)] [∀ s v, Decidable (Y s v)]
  {f : ℝ} {C : Matrix V V ℝ}

/-- The true residual fits a fixed top cap when the top scale is one. The bound follows
from the hierarchy input bounds (each residual entry is nonnegative with row mass at most one),
not from a desired mean or error estimate. -/
theorem boundedRoutedBinCutoff_residual (hf : 0 < f)
    (hC : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1)
    (χ : ℝ → ℝ) (b : ℕ → ℝ) (hb : ∀ i, 0 < b i) (hb0 : b 0 = 1)
    (i : ℕ) (route : ℝ → ℝ) (x y : V) :
    boundedRoutedBinCutoff χ b ((P.k : ℝ) + 2) i route
        (CorrectionRowRecipe.residual C (P.correction X Y f C) (P.correction X Y f C) C x y / b i) =
      routedBinCutoff χ b i route (P.residual X Y f C x y / b i) := by
  rw [CorrectionRowRecipe.residual_eq, ← P.residual_eq]
  have hd := div_nonneg (P.residual_nonneg (X := X) (Y := Y) hf hC x y) (hb i).le
  by_cases hi : i = 0
  · subst i
    apply boundedRoutedBinCutoff_eq hd
    rw [hb0, div_one]
    have hu : P.residual X Y f C x y ≤ 1 :=
      (Finset.single_le_sum (fun y' _ => P.residual_nonneg (X := X) (Y := Y) hf hC x y')
        (Finset.mem_univ y)).trans (P.residual_sum_le_one X Y hf hC1 x)
    have hk : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
    linarith
  · simp [boundedRoutedBinCutoff, hi, not_lt.mpr hd]

end HierarchyParams

namespace HierarchyParams.CorrectionSampling

variable {q cπ Cπ Cpair Cvar : ℝ} {P : HierarchyParams q cπ Cπ Cpair Cvar}
  {V ι κ Γ Ω : Type*} [Fintype V] [Fintype ι] [Fintype κ] [Fintype Γ] [Fintype Ω]
  {X : ι → V → Prop} {Y : κ → V → Prop} {Xs : Γ → V → Prop}
  {Z Zt Ya : Ω → V → Prop}
  [∀ s v, Decidable (X s v)] [∀ s v, Decidable (Y s v)]
  [∀ s v, Decidable (Xs s v)] [∀ s v, Decidable (Z s v)]
  [∀ s v, Decidable (Zt s v)] [∀ s v, Decidable (Ya s v)]
  {f : ℝ} {C : Matrix V V ℝ} {i : ℕ}
  (A : P.CorrectionSampling X Y Xs Z Zt f C i)

/-- The special negative term of Section 7.2: direct correction at scale `f`, with the
endpoint usage density ratio. There is no midpoint density factor in this term. -/
@[expose] noncomputable def negativeRecipe (Ya Yt : Ω → V → Prop)
    [∀ s v, Decidable (Ya s v)] [∀ s v, Decidable (Yt s v)]
    (F : Γ × Ω → Matrix V V ℝ) (σ : Γ × Ω) (x y : V) : ℝ :=
  -(f * ((dens {s | Ya s y} : ℝ) / dens {s | Yt s y}) * F σ x y)

/-- Its true conditional mean is explicitly negative. The correction's primitive sampling
laws use its own raw input and multiplier, and usage is nested in the broad endpoint slice. -/
theorem expect_negativeRecipe (hf : 0 < f) (hC : ∀ x y, 0 ≤ C x y)
    (hC1 : C *ᵥ 1 ≤ 1) (hsub : ∀ s y, Zt s y → Ya s y)
    (x y : V) (hx : ({s | Xs s x} : Finset Γ).Nonempty) :
    (𝔼 σ ∈ ({s | Xs s x} : Finset Γ) ×ˢ ({s | Ya s y} : Finset Ω),
      negativeRecipe (f := f) Ya Zt A.atom σ x y) =
      -P.correctionIter X Y f C (i + 1) x y := by
  have hs := P.isCorrectionSeq_correctionIter (X := X) (Y := Y) hf hC
  have hm := A.toCorrectionSamplingLaws.expect_atom hf (hs.input_nonneg hC i)
    (fun x => (hs.sum_input_le hC1 i x).1) hx y
  have hchange :
      (𝔼 σ ∈ ({s | Xs s x} : Finset Γ) ×ˢ ({s | Ya s y} : Finset Ω),
        ((dens {s | Ya s y} : ℝ) / dens {s | Zt s y}) * A.atom σ x y) =
      𝔼 σ ∈ ({s | Xs s x} : Finset Γ) ×ˢ ({s | Zt s y} : Finset Ω), A.atom σ x y := by
    rw [expect_product, expect_product]
    apply expect_congr rfl
    intro s _
    apply expect_mul_dens_div_of_subset
      (fun t ht => mem_filter.mpr ⟨mem_univ _, hsub _ _ (mem_filter.mp ht).2⟩)
      (A.usage_nonempty y)
    intro t _ ht
    have hnot : ¬Zt t y := by simpa only [mem_filter, mem_univ, true_and] using ht
    simp [atom, correctionAtom, hnot]
  calc
    _ = (-f) * (𝔼 σ ∈ ({s | Xs s x} : Finset Γ) ×ˢ ({s | Ya s y} : Finset Ω),
        ((dens {s | Ya s y} : ℝ) / dens {s | Zt s y}) * A.atom σ x y) := by
      rw [mul_expect]
      apply expect_congr rfl
      intro σ _
      simp only [negativeRecipe]
      ring
    _ = (-f) * (𝔼 σ ∈ ({s | Xs s x} : Finset Γ) ×ˢ ({s | Zt s y} : Finset Ω),
        A.atom σ x y) := congrArg (fun v => (-f) * v) hchange
    _ = _ := by
      change (-f) * (𝔼 σ ∈ ({s | Xs s x} : Finset Γ) ×ˢ
        ({s | Zt s y} : Finset Ω), correctionAtom _ _ _ _ _ _ _ _ _ _ _ _ _ σ x y) = _
      rw [hm, P.correctionIter_succ_apply]
      ring


section SignedSample

variable {Ζ : Type*} [Fintype Ζ]
  {Mid Midt : Ζ → V → Prop} {Yr Yt Nr Nt : Ω → V → Prop}
  [∀ s v, Decidable (Mid s v)] [∀ s v, Decidable (Midt s v)]
  [∀ s v, Decidable (Yr s v)] [∀ s v, Decidable (Yt s v)]
  [∀ s v, Decidable (Nr s v)] [∀ s v, Decidable (Nt s v)]
  {b : ℝ} {k : ℝ → ℝ}
  (L : P.CorrectionSampling X Y Xs Mid Midt f C i)

/-- One direct/product bin contribution and the special negative correction. Summing bins
includes the negative correction exactly once. Earlier tables are whole functions; negative
and product-left factors have distinct endpoint/midpoint roles and usage slices. -/
@[expose] noncomputable def residualSample
    (Ya Yt Nt : Ω → V → Prop)
    [∀ s v, Decidable (Ya s v)] [∀ s v, Decidable (Yt s v)] [∀ s v, Decidable (Nt s v)]
    (b : ℝ) (F : Γ × Ζ → Matrix V V ℝ) (B : Ω → Matrix V V ℝ)
    (N : Γ × Ω → Matrix V V ℝ) (draw : (Γ × Ζ) × Ω) (x y : V) : ℝ :=
  let ((source, midpoint), terminal) := draw
  b * ((dens {s | Ya s y} : ℝ) / dens {s | Yt s y}) * B terminal x y +
    L.binProductRecipe (Ya := Ya) (Yt := Yt) (b := b) F B ((source, midpoint), terminal) x y +
    negativeRecipe (f := f) Ya Nt N (source, terminal) x y

/-- The stochastic signed sample is exactly the completed four-child raw recipe used by
preparation and normalization. Density factors belong to the appropriate whole child;
the negative endpoint child and product-left midpoint child are kept separate. -/
theorem residualSample_eq_raw
    (Ya Yt Nt : Ω → V → Prop)
    [∀ s v, Decidable (Ya s v)] [∀ s v, Decidable (Yt s v)] [∀ s v, Decidable (Nt s v)]
    (b : ℝ) (F : Γ × Ζ → Matrix V V ℝ) (B : Ω → Matrix V V ℝ)
    (N : Γ × Ω → Matrix V V ℝ) (s : Γ) (t : Ζ) (u : Ω) (x y : V) :
    L.residualSample Ya Yt Nt b F B N ((s, t), u) x y =
      CorrectionRowRecipe.residual
        (fun x y => b * ((dens {s | Ya s y} : ℝ) / dens {s | Yt s y}) * B u x y)
        (fun x y => f * ((dens {s | Ya s y} : ℝ) / dens {s | Nt s y}) * N (s, u) x y)
        (fun x z => (f / L.π) * F (s, t) x z)
        (fun z y => b * ((dens {s | Ya s y} : ℝ) / dens {s | Yt s y}) * B u z y) x y := by
  simp only [residualSample, binProductRecipe, negativeRecipe, CorrectionRowRecipe.residual,
    mul_sum]
  have heq : ∑ z, b * ((dens {s | Ya s y} : ℝ) / dens {s | Yt s y}) *
      (f / L.π) * (F (s, t) x z * B u z y) =
      ∑ z, (f / L.π * F (s, t) x z) *
        (b * ((dens {s | Ya s y} : ℝ) / dens {s | Yt s y}) * B u z y) := by
    apply sum_congr rfl
    intro z _
    ring
  rw [heq]
  ring

/-- All three signed means follow from primitive laws on the actual tuples. This is one
bin contribution; the partition API sums positive contributions and `-E` is included once.
No independence of estimated factors is asserted. -/
theorem expect_residualSample
    (B : DenseSamplingLaws Yr Ya Yt k b 1)
    (N : P.CorrectionSampling X Y Xs Nr Nt f C i)
    (hf : 0 < f) (hb : 0 < b) (hC : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1)
    (hsub : ∀ s y, Nt s y → Ya s y)
    (x y : V) (hx : ({s | Xs s x} : Finset Γ).Nonempty) :
    (𝔼 draw ∈ (({s | Xs s x} : Finset Γ) ×ˢ (univ : Finset Ζ)) ×ˢ
        ({s | Ya s y} : Finset Ω),
      L.residualSample Ya Yt Nt b L.atom (B.atom C) N.atom draw x y) =
      b * k (C x y / b) +
        (∑ z, P.correctionIter X Y f C (i + 1) x z * (b * k (C z y / b))) -
        P.correctionIter X Y f C (i + 1) x y := by
  have hΖ : Nonempty Ζ := ⟨(L.usage_nonempty x).choose⟩
  have hrow (z : V) : ∑ w, C z w ≤ 1 := by
    simpa only [mulVec, dotProduct, Pi.one_apply, mul_one] using hC1 z
  have hd :
      (𝔼 draw ∈ (({s | Xs s x} : Finset Γ) ×ˢ (univ : Finset Ζ)) ×ˢ
        ({s | Ya s y} : Finset Ω), B.direct C draw.2 x y) = b * k (C x y / b) := by
    rw [expect_product]
    simp_rw [B.expect_direct hb hC hrow x y]
    exact expect_const (hx.product univ_nonempty) _
  have hn :
      (𝔼 draw ∈ (({s | Xs s x} : Finset Γ) ×ˢ (univ : Finset Ζ)) ×ˢ
        ({s | Ya s y} : Finset Ω),
        let ((s, _), t) := draw
        negativeRecipe (f := f) Ya Nt N.atom (s, t) x y) =
        -P.correctionIter X Y f C (i + 1) x y := by
    simp_rw [expect_product]
    simp_rw [expect_const (univ_nonempty : (univ : Finset Ζ).Nonempty)]
    have hm := N.expect_negativeRecipe hf hC hC1 hsub x y hx
    rw [expect_product] at hm
    exact hm
  simp only [residualSample, expect_add_distrib]
  change (𝔼 draw ∈
    (({s | Xs s x} : Finset Γ) ×ˢ (univ : Finset Ζ)) ×ˢ
      ({s | Ya s y} : Finset Ω), B.direct C (draw : (Γ × Ζ) × Ω).2 x y) + _ + _ = _
  rw [hd, L.expect_binProductRecipe B hf hb hC hC1 x y hx, hn]
  ring

end SignedSample

end HierarchyParams.CorrectionSampling
namespace ResidualBinTask

/-- Completed residual, its broad preparation, then its usage-normalized bin. -/
inductive Phase where
  | raw | preparation | normalized

variable {V Γ Ω : Type*} [Fintype V] [Fintype Γ] [Fintype Ω]

/-- A real evaluator for substituted child functions, including signed residual preparation
and normalization. The preparatory child is separately supplied to the normalized phase so
an estimate of that earlier output can be substituted. Ranks use this draw's completed raw
residual; only the scalar row function clips. -/
@[expose] noncomputable def value (χ : ℝ → ℝ) (b : ℕ → ℝ) (cap : ℝ) (i : ℕ)
    (route h ρ : ℝ → ℝ) (K : ℕ)
    (X : Γ → V → Prop) (Y Yt : Ω → V → Prop)
    [∀ s v, Decidable (X s v)] [∀ s v, Decidable (Y s v)] [∀ s v, Decidable (Yt s v)]
    (base negative left right prep : Γ × Ω → Matrix V V ℝ)
    (p : Phase) (σ : Γ × Ω) : Matrix V V ℝ :=
  let raw := CorrectionRowRecipe.residual (base σ) (negative σ) (left σ) (right σ)
  match p with
  | .raw => raw
  | .preparation => DenseRowRecipe.preparation h ρ K (b i) Y raw σ.2
  | .normalized => DenseRowRecipe.normalized (boundedRoutedBinCutoff χ b cap i route)
      ρ K (b i) X Y Yt raw prep σ

/-- True preparation and normalization on a real residual agree with the actual dense atom.
The exact residual is the existing hierarchy operation, rather than a second hierarchy. -/
theorem value_true {q cπ Cπ Cpair Cvar : ℝ}
    (P : HierarchyParams q cπ Cπ Cpair Cvar)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (X₀ : ι → V → Prop) (Y₀ : κ → V → Prop)
    [∀ s v, Decidable (X₀ s v)] [∀ s v, Decidable (Y₀ s v)]
    (f : ℝ) (C : Matrix V V ℝ) (χ : ℝ → ℝ) (b : ℕ → ℝ) (cap : ℝ) (i : ℕ)
    (route h ρ : ℝ → ℝ) (K : ℕ)
    (X : Γ → V → Prop) (Y Yt : Ω → V → Prop)
    [∀ s v, Decidable (X s v)] [∀ s v, Decidable (Y s v)] [∀ s v, Decidable (Yt s v)]
    (σ : Γ × Ω) (x y : V) (hx : ({s | X s x} : Finset Γ).Nonempty) :
    let base := fun _ : Γ × Ω => C
    let correction := fun _ : Γ × Ω => P.correction X₀ Y₀ f C
    let prep := value χ b cap i route h ρ K X Y Yt base correction correction base base .preparation
    value χ b cap i route h ρ K X Y Yt base correction correction base prep .normalized σ x y =
      denseAtom Y Yt (boundedRoutedBinCutoff χ b cap i route) h ρ K (b i)
        (P.residual X₀ Y₀ f C) σ.2 x y := by
  dsimp only [value]
  rw [CorrectionRowRecipe.residual_eq, P.residual_eq]
  exact DenseRowRecipe.normalized_eq_denseAtom _ _ _ _ _ _ _ _ _ _ _ _ hx

/-- True conditional mean for the actual residual client. Input bounds and the cap are
checked against the actual finite correction hierarchy; gate/pair laws supply normalization.
Preparation uses the broad rank channel and averages on the narrower usage slice. -/
theorem expect_value_true {q cπ Cπ Cpair Cvar : ℝ}
    (P : HierarchyParams q cπ Cπ Cpair Cvar)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (X₀ : ι → V → Prop) (Y₀ : κ → V → Prop)
    [∀ s v, Decidable (X₀ s v)] [∀ s v, Decidable (Y₀ s v)]
    {f : ℝ} (C : Matrix V V ℝ) (hf : 0 < f)
    (hC : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1)
    (χ : ℝ → ℝ) (b : ℕ → ℝ) (hb : ∀ i, 0 < b i) (hb0 : b 0 = 1)
    (i : ℕ) (route : ℝ → ℝ)
    (X : Γ → V → Prop) (Y Ya Yt : Ω → V → Prop)
    [∀ s v, Decidable (X s v)] [∀ s v, Decidable (Y s v)]
    [∀ s v, Decidable (Ya s v)] [∀ s v, Decidable (Yt s v)]
    (A : DenseSamplingLaws Y Ya Yt
      (boundedRoutedBinCutoff χ b ((P.k : ℝ) + 2) i route) (b i) 1)
    (x y : V) (hx : ({s | X s x} : Finset Γ).Nonempty) :
    let base := fun _ : Γ × Ω => C
    let correction := fun _ : Γ × Ω => P.correction X₀ Y₀ f C
    let prep := value χ b ((P.k : ℝ) + 2) i route A.h A.ρ A.K X Y Yt
      base correction correction base base .preparation
    (𝔼 σ ∈ ({s | X s x} : Finset Γ) ×ˢ ({s | Ya s y} : Finset Ω),
      (b i * ((dens {s | Ya s y} : ℝ) / dens {s | Yt s y})) *
        value χ b ((P.k : ℝ) + 2) i route A.h A.ρ A.K X Y Yt
          base correction correction base prep .normalized σ x y) =
      b i * routedBinCutoff χ b i route (P.residual X₀ Y₀ f C x y / b i) := by
  dsimp only
  simp_rw [value_true P X₀ Y₀ f C χ b ((P.k : ℝ) + 2) i route A.h A.ρ A.K X Y Yt _ x y hx]
  have hm := A.expect_direct_source X (hb i)
    (P.residual_nonneg (X := X₀) (Y := Y₀) hf hC)
    (P.residual_sum_le_one X₀ Y₀ hf hC1) x y hx
  dsimp only [DenseSamplingLaws.direct, DenseSamplingLaws.atom] at hm
  rw [hm]
  congr 1
  simpa only [CorrectionRowRecipe.residual_eq, ← P.residual_eq] using
    P.boundedRoutedBinCutoff_residual X₀ Y₀ hf hC hC1 χ b hb hb0 i route x y

end ResidualBinTask

namespace HierarchyParams.HierarchyTask

open CorrectionRowTask

/-- Actual direct, left, right and special negative requests for a residual sample. The
negative child uses the endpoint role at scale `f`, with usage `min(a,f)`; it is not the left
child on the midpoint role. The right child resets its source to the full midpoint tuple. -/
@[expose] def residualRequests {k : ℕ} {Role Symbol : Type*} (l : ℕ)
    (source midpoint endpoint : Channel Role (List Symbol)) (b : ℝ) :
    List (Request k Role Symbol) :=
  [⟨.row l .base, source, { endpoint with rate := b },
      { endpoint with rate := min endpoint.rate b }⟩,
   ⟨.row l (.correction (Fin.last k)), source, midpoint, midpoint⟩,
   ⟨.row l .base, midpoint, { endpoint with rate := b },
      { endpoint with rate := min endpoint.rate b }⟩,
   ⟨.row l (.correction (Fin.last k)), source, { endpoint with rate := midpoint.rate },
      { endpoint with rate := min endpoint.rate midpoint.rate }⟩]

/-- Each actual residual child decreases the existing matrix-output structural rank. -/
theorem residualRequests_rank_lt {k : ℕ} {Role Symbol : Type*} (l : ℕ)
    (source midpoint endpoint : Channel Role (List Symbol)) (b : ℝ)
    (r : Request k Role Symbol) (hr : r ∈ residualRequests l source midpoint endpoint b) :
    r.task.rank < (nextMatrix (k := k) l).rank := by
  simp only [residualRequests, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact row_rank_lt_nextMatrix _ _

end HierarchyParams.HierarchyTask
end Matrix
