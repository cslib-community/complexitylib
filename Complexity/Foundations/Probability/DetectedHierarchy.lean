/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyParams

/-!
# The correction-and-copy hierarchy

This file iterates the stages of `Complexity.Foundations.Probability.HierarchyParams` and proves
the finite-matrix stage bound of the OpenAI preprint (2026-09-23), Proposition 4.7
[OpenAI2026LogSpace], from the construction using the reduced algebraic-stage parameters and
the retention-channel interface. The preprint's full threshold ladder and later-estimation
root/complement regularity for `Q` and all step cutoffs remain separate requirements.

Start with a strictly upper triangular, nonnegative, substochastic matrix `S` on a finite linearly
ordered set `V 0`. Stage `l + 1` lives on a finite linearly ordered set `V (l + 1)` identified
with the copies `Lex (V l × Fin (m + 1))` by an equivalence `e l` that reflects the order
[OpenAI2026LogSpace, Section 4.5: `V_(l+1) = V_l × {0, …, D₀ - 1}`, ordered by parent and then
copy symbol]. Taking the family as a parameter lets a client choose identifiers, for instance
numbers in radix `D₀`, on which its channels act. The transition matrices `Matrix.hierarchy` are
`C_0 = S` and `C_(l+1) = C⁺_l` transported by `e l`, where `C⁺_l` is the next matrix of the stage
at rate `f_l = q⁻¹ ^ l` with that stage's retention channels `X l`, `Y l`. The detectors are exact
expectations over the channel seeds, so the hierarchy, its corrections
(`Matrix.hierarchyCorrection`), its projections (`Matrix.hierarchyProj`) and the transported
rewards are deterministic functions of `S`, the parameters and the channel laws: no event over
the seeds has to be excluded, and the channel interface is the only probabilistic input.

**The stage bound** (`Matrix.sub_hierarchyReward_le`). Let `q = 2 ^ (c + 1)`, let the channels
of every stage `l` satisfy `Cslib.Probability.RetentionChannels` at rate `q⁻¹ ^ l` with the
bundled constants, and let `(1 - S) p = e₀` with `0 ≤ p ≤ 1`. Then at the all-primary copy
`Matrix.primaryCopy P e x l` of a base vertex `x`,

`0 ≤ p x - W_l (x̄_l) ≤ |V 0| (2 ^ c)⁻¹ ^ l`,

where `W_l = B_l e₀` is the transported reward (`Matrix.rewardTransport`). Along the way, every
stage is strictly upper triangular, nonnegative and substochastic with entries at most `q⁻¹ ^ l`
(`Matrix.hierarchy_invariant`), and its active vertices at most double from stage to stage.

## Main definitions

* `Matrix.hierarchy`, `Matrix.hierarchyCorrection`, `Matrix.hierarchyProj`: the stages.
* `Matrix.primaryCopy`: the all-primary copy of a base vertex.
* `Matrix.radixCopyEquiv`: radix identifiers for copies, reusing `finProdFinEquiv`.

## Main results

* `Matrix.hierarchy_invariant`: every stage is a valid input of the next one.
* `Matrix.radixCopyEquiv_lt`: the radix identification reflects the parent-then-copy order.
* `Matrix.sub_hierarchyReward_le`: the stage bound `0 ≤ p x - W_l (x̄_l) ≤ |V 0| (2 ^ c)⁻¹ ^ l`.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 4.5 and Proposition 4.7 (preprint, not peer reviewed)
-/

public section

open Finset Cslib.Probability

namespace Matrix

/-- **Radix identifiers for copies**: `Fin (n (m + 1) ^ (l + 1))` as the copies of
`Fin (n (m + 1) ^ l)`, where the number `y + (m + 1) x` is the copy `y` of the parent `x`. This is
the preprint's appending of a radix-`D₀` digit [OpenAI2026LogSpace, Section 4.5]. -/
def radixCopyEquiv (n m l : ℕ) :
    Fin (n * (m + 1) ^ (l + 1)) ≃ Lex (Fin (n * (m + 1) ^ l) × Fin (m + 1)) :=
  (finCongr (by ring)).trans (finProdFinEquiv.symm.trans toLex)

theorem radixCopyEquiv_val (n m l : ℕ) (a : Fin (n * (m + 1) ^ (l + 1))) :
    a.val = (ofLex (radixCopyEquiv n m l a)).2.val +
      (m + 1) * (ofLex (radixCopyEquiv n m l a)).1.val := by
  have h := finProdFinEquiv_apply_val (ofLex (radixCopyEquiv n m l a))
  simp only [radixCopyEquiv, Equiv.trans_apply, ofLex_toLex, Equiv.apply_symm_apply,
    finCongr_apply, Fin.val_cast] at h
  exact h

/-- The radix identification reflects the order: copies are ordered by parent, then by symbol. -/
theorem radixCopyEquiv_lt (n m l : ℕ) {a b : Fin (n * (m + 1) ^ (l + 1))}
    (h : radixCopyEquiv n m l a < radixCopyEquiv n m l b) : a < b := by
  rw [Fin.lt_def, radixCopyEquiv_val n m l a, radixCopyEquiv_val n m l b]
  rcases Prod.Lex.lt_iff.mp h with h1 | ⟨h1, h2⟩
  · have hx : (ofLex (radixCopyEquiv n m l a)).1.val + 1 ≤
        (ofLex (radixCopyEquiv n m l b)).1.val := h1
    have hy := (ofLex (radixCopyEquiv n m l a)).2.isLt
    nlinarith
  · rw [h1]
    have : (ofLex (radixCopyEquiv n m l a)).2.val < (ofLex (radixCopyEquiv n m l b)).2.val := h2
    omega

variable {q cπ Cπ Cpair Cvar : ℝ} (P : HierarchyParams q cπ Cπ Cpair Cvar) {V : ℕ → Type*}
  [∀ l, Fintype (V l)] [∀ l, LinearOrder (V l)] (e : ∀ l, V (l + 1) ≃ Lex (V l × Fin (P.m + 1)))
  {ι κ : ℕ → Type*} [∀ l, Fintype (ι l)] [∀ l, Fintype (κ l)] (X : ∀ l, ι l → V l → Prop)
  (Y : ∀ l, κ l → V l → Prop) [∀ l s v, Decidable (X l s v)] [∀ l t v, Decidable (Y l t v)]
  (S : Matrix (V 0) (V 0) ℝ)

/-- **The transition matrices of the hierarchy**: `C_0 = S`, and `C_(l+1)` is the next matrix of
stage `l` at rate `q⁻¹ ^ l`, with the channels `X l`, `Y l`, transported to `V (l + 1)` by `e l`
[OpenAI2026LogSpace, Section 4.5]. -/
noncomputable def hierarchy : ∀ l, Matrix (V l) (V l) ℝ
  | 0 => S
  | l + 1 => (P.next (X l) (Y l) (q⁻¹ ^ l) (hierarchy l)).submatrix (e l) (e l)

/-- The correction `E_l` of stage `l`. -/
noncomputable def hierarchyCorrection (l : ℕ) : Matrix (V l) (V l) ℝ :=
  P.correction (X l) (Y l) (q⁻¹ ^ l) (hierarchy P e X Y S l)

/-- The weighted projection `P_r` from stage `l + 1` to stage `l`. -/
noncomputable def hierarchyProj (l : ℕ) : Matrix (V (l + 1)) (V l) ℝ :=
  (P.proj (X l) (Y l) (q⁻¹ ^ l) (hierarchy P e X Y S l)).submatrix (e l) id

/-- The **all-primary copy** `x̄_l` of a base vertex `x`: every copy symbol is `0`. -/
def primaryCopy (x : V 0) : ∀ l, V l
  | 0 => x
  | l + 1 => (e l).symm (toLex (primaryCopy x l, 0))

variable {P e X Y S}

/-- **Every stage is a valid input of the next**: if `S` is strictly upper triangular,
nonnegative and substochastic and the equivalences reflect the order, then so is every stage
`l`, with entries at most `q⁻¹ ^ l`, provided the channels of the stages before `l` satisfy the
interface [OpenAI2026LogSpace, Proposition 4.5]. -/
theorem hierarchy_invariant (he : ∀ l a b, e l a < e l b → a < b) {π : ℕ → ℝ} (hq : 0 < q)
    (hCπ : 0 < Cπ) (hS : S.IsStrictUpperTriangular) (hS0 : ∀ x y, 0 ≤ S x y)
    (hS1 : S *ᵥ 1 ≤ 1) (l : ℕ)
    (hch : ∀ l' < l, RetentionChannels (X l') (Y l') (q⁻¹ ^ l') (π l') cπ Cπ Cpair Cvar) :
    (hierarchy P e X Y S l).IsStrictUpperTriangular ∧ (∀ x y, 0 ≤ hierarchy P e X Y S l x y) ∧
      hierarchy P e X Y S l *ᵥ 1 ≤ 1 ∧ ∀ x y, hierarchy P e X Y S l x y ≤ q⁻¹ ^ l := by
  induction l with
  | zero =>
    refine ⟨hS, hS0, hS1, fun x y => ?_⟩
    have hrow : ∑ z, S x z ≤ 1 := by
      have := hS1 x
      simpa only [mulVec, dotProduct, Pi.one_apply, mul_one] using this
    rw [pow_zero]
    exact (single_le_sum (fun z _ => hS0 x z) (mem_univ y)).trans hrow
  | succ l ih =>
    obtain ⟨hC, hC0, hC1, hCf⟩ := ih fun l' hl' => hch l' (by omega)
    have hf : 0 < q⁻¹ ^ l := by positivity
    have hnext := P.next_isStrictUpperTriangular (X := X l) (Y := Y l) hf hC
    have hrow := P.next_mulVec_one_le (X := X l) (Y := Y l) hf hC0 hC1
    refine ⟨fun a b hab => hnext fun h => hab (he l a b h),
      fun a b => P.next_nonneg hf hC0 _ _, fun a => ?_, fun a b => ?_⟩
    · have h1 := hrow (e l a)
      simp only [mulVec, dotProduct, Pi.one_apply, mul_one] at h1 ⊢
      calc ∑ b, hierarchy P e X Y S (l + 1) a b
          = ∑ c, P.next (X l) (Y l) (q⁻¹ ^ l) (hierarchy P e X Y S l) (e l a) c :=
            Fintype.sum_equiv (e l) _ _ fun _ => rfl
        _ ≤ 1 := h1
    · have := (P.stage_rates (hch l (by omega)) hCπ hf hC hC0 hCf hC1 (A := univ)
        (fun _ _ _ => ⟨mem_univ _, mem_univ _⟩)).1 (e l a) (e l b)
      calc hierarchy P e X Y S (l + 1) a b ≤ q⁻¹ ^ l / q := this
        _ = q⁻¹ ^ (l + 1) := by rw [pow_succ, div_eq_mul_inv]

/-- The active vertices of a matrix: those with a nonzero entry in their row or column. -/
private noncomputable def active {W : Type*} [Fintype W] (C : Matrix W W ℝ) : Finset W := by
  classical exact univ.filter fun x => ∃ y, C x y ≠ 0 ∨ C y x ≠ 0

private theorem mem_active {W : Type*} [Fintype W] {C : Matrix W W ℝ} {x y : W}
    (h : C x y ≠ 0) : x ∈ active C ∧ y ∈ active C := by
  classical
  simp only [active, mem_filter, mem_univ, true_and]
  exact ⟨⟨y, Or.inl h⟩, ⟨x, Or.inr h⟩⟩

/-- **The stage bound from the construction** [OpenAI2026LogSpace, Proposition 4.7]. Let
`q = 2 ^ (c + 1)`, let `S` be strictly upper triangular, nonnegative and substochastic, let the
equivalences `e l` reflect the order, let the channels of every stage `l` satisfy the interface at
rate `q⁻¹ ^ l`, and let `(1 - S) p = e₀` with `0 ≤ p ≤ 1`. Then the reward `W_l = B_l e₀`,
transported along the hierarchy, satisfies `0 ≤ p x - W_l (x̄_l) ≤ |V 0| (2 ^ c)⁻¹ ^ l` at the
all-primary copy of every base vertex `x`. -/
theorem sub_hierarchyReward_le (he : ∀ l a b, e l a < e l b → a < b) {π : ℕ → ℝ} {c : ℕ}
    (hq : q = 2 ^ (c + 1))
    (hch : ∀ l, RetentionChannels (X l) (Y l) (q⁻¹ ^ l) (π l) cπ Cπ Cpair Cvar) (hCπ : 0 < Cπ)
    (hS : S.IsStrictUpperTriangular) (hS0 : ∀ x y, 0 ≤ S x y) (hS1 : S *ᵥ 1 ≤ 1)
    {p e₀ : V 0 → ℝ} (hp : (1 - S) *ᵥ p = e₀) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : V 0) (l : ℕ) :
    0 ≤ p x - (rewardTransport (hierarchyProj P e X Y S) (hierarchyCorrection P e X Y S) l *ᵥ
        e₀) (primaryCopy P e x l) ∧
      p x - (rewardTransport (hierarchyProj P e X Y S) (hierarchyCorrection P e X Y S) l *ᵥ e₀)
        (primaryCopy P e x l) ≤ Fintype.card (V 0) * ((2 : ℝ) ^ c)⁻¹ ^ l := by
  have hq0 : 0 < q := by rw [hq]; positivity
  have hinv := fun l => hierarchy_invariant he hq0 hCπ hS hS0 hS1 l fun l' _ => hch l'
  have hf : ∀ l, 0 < q⁻¹ ^ l := fun l => by positivity
  have hrates := fun l => P.stage_rates (hch l) hCπ (hf l) (hinv l).1 (hinv l).2.1
    (hinv l).2.2.2 (hinv l).2.2.1 (A := active (hierarchy P e X Y S l))
    fun _ _ h => mem_active h
  refine sub_rewardTransport_mulVec_le_of_rates (V := V) (C := hierarchy P e X Y S)
    (E := hierarchyCorrection P e X Y S) (P := hierarchyProj P e X Y S)
    (fun l a w => P.proj_nonneg _ _) (fun l a => P.proj_mulVec_one_le (e l a))
    (fun l => (hinv l).2.1) (fun l => ?_) hp hp0 hp1 (z := primaryCopy P e x)
    (fun l w => ?_) (fun a b => by simpa using (hinv 0).2.2.2 a b) (fun l _ a b => ?_)
    (fun l => active (hierarchy P e X Y S l)) (fun l _ _ h => (mem_active h).2)
    (card_le_univ _) (fun l => ?_) l
  · -- the intertwining, transported by `e l`
    have hl : hierarchy P e X Y S (l + 1) * hierarchyProj P e X Y S l =
        (P.next (X l) (Y l) (q⁻¹ ^ l) (hierarchy P e X Y S l) *
          P.proj (X l) (Y l) (q⁻¹ ^ l) (hierarchy P e X Y S l)).submatrix (e l) id :=
      (submatrix_mul _ _ _ _ _ (e l).bijective).symm
    have hr : hierarchyProj P e X Y S l * (hierarchy P e X Y S l -
        hierarchyCorrection P e X Y S l +
          hierarchyCorrection P e X Y S l * hierarchy P e X Y S l) =
        (P.proj (X l) (Y l) (q⁻¹ ^ l) (hierarchy P e X Y S l) *
          P.residual (X l) (Y l) (q⁻¹ ^ l) (hierarchy P e X Y S l)).submatrix (e l) id := by
      rw [HierarchyParams.residual_eq]
      ext a z
      rfl
    rw [hl, hr, (hrates l).2.1]
  · -- primary copies project to their parents
    simp only [hierarchyProj, primaryCopy, submatrix_apply, id, Equiv.apply_symm_apply]
    exact P.proj_primary _ w
  · calc hierarchy P e X Y S (l + 1) a b ≤ q⁻¹ ^ (l + 1) := (hinv (l + 1)).2.2.2 a b
      _ = ((2 : ℝ) ^ (c + 1))⁻¹ ^ (l + 1) := by rw [hq]
  · -- the active vertices of the next stage map injectively into the copy cover
    classical
    refine (card_le_card_of_injOn (fun a => ofLex (e l a)) (fun a ha => mem_coe.mpr ?_)
      (fun a _ b _ h => (e l).injective (ofLex.injective h))).trans (hrates l).2.2.2
    rw [mem_coe] at ha
    simp only [active, mem_filter, mem_univ, true_and] at ha
    obtain ⟨b, hb | hb⟩ := ha
    · exact ((hrates l).2.2.1 (e l a) (e l b) hb).1
    · exact ((hrates l).2.2.1 (e l b) (e l a) hb).2

end Matrix
