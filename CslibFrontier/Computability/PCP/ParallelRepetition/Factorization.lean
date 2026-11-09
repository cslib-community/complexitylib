/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.ParallelRepetition.CoordinateModel
public import CslibFrontier.Probability.CorrelatedSampling.Embeddability

/-!
# The factorization in Holenstein's embedding lemma

The proof of Holenstein's Lemma 6.4 [Holenstein, Lemma 6.4][Holenstein2009] embeds the questions
`(X, Y)` of a game in the questions `(X̃ⁿ, Ỹⁿ)` of its `n`-fold repetition conditioned on the event
`W_C` that strategies `ha` and `hb` win every coordinate in `C`, with `(X̃_j, Ỹ_j) = (X, Y)` at a
free coordinate `j ∉ C`. It does so in two stages, in the coordinate model of
`CslibFrontier/Computability/PCP/ParallelRepetition/CoordinateModel.lean`, where `S` is the variable
`shared j` and every law is an image of `condLaw`.

1. Corollary 5.3 embeds `(X, Y)` in `((X̃_j, S̃), (Ỹ_j, S̃))`, with an error bounded through
   (6.5)–(6.16).
2. Lemma 5.4 embeds `((X̃_j, S̃), (Ỹ_j, S̃))` exactly in `((X̃_j, S̃, X̃ⁿ), (Ỹ_j, S̃, Ỹⁿ))`, and
   Alice and Bob then forget `S̃` [Holenstein, proof of Lemma 6.4, (6.17)–(6.19)][Holenstein2009].

This file proves the second stage and composes it with the first.

Lemma 5.4 needs the conditioned law in the product form (5.5): given `(x_j, s)` and `(y_j, s)`,
Alice's questions `xⁿ` and Bob's questions `yⁿ` are drawn independently, each from a law that
depends on one side only. Holenstein obtains this from the Markov chains (6.18) and (6.19): his
Claim 6.2 gives the chain (6.17) before conditioning, and his Claim 6.3 carries the chains derived
from it to the conditioned law. Here the product form is proved directly from the masses of the
conditioned law (`exists_map_condLaw_apply_eq_mul`): the mass of
`(((x_j, s), (y_j, s)), (xⁿ, yⁿ))` is `c ((x_j, s), (y_j, s)) · f ((x_j, s), xⁿ) ·
g ((y_j, s), yⁿ)`. The mass of the question pairs splits between Alice and Bob for three reasons.

* At each free coordinate `i ≠ j`, `S` reveals one half of the pair, which fixes that half; the
  mass of the pair is then a function of `S` and the other half, which one party holds.
* On `C`, `S` holds the question pairs.
* `W_C` depends only on the questions and answers on `C`, and `S` holds both.

Lemma 5.4 in this product form is `isEmbeddable_map_fst_of_apply_eq_mul`, which gives the exact
embedding (`isEmbeddable_map_condLaw_tuples`). Composing it with an embedding of the first stage,
and forgetting `S`, gives `isEmbeddable_filter_questions_of_shared`. Its premise is an embedding in
the law of `((x_j, y_j), (S, S))` under `W_C`, which Corollary 5.3 (`isEmbeddable_diag_of_dist_le`)
provides. Its conclusion is the premise of strategy extraction,
`TwoProverGame.winProbOn_insert_le`.

## Main results

* `Cslib.PCP.ParallelRepetition.exists_map_condLaw_apply_eq_mul`: the product form (5.5) of the
  conditioned law.
* `Cslib.PCP.ParallelRepetition.isEmbeddable_map_condLaw_tuples`: the exact embedding of the second
  stage.
* `Cslib.PCP.ParallelRepetition.isEmbeddable_filter_questions_of_shared`: an embedding of the first
  stage gives an embedding of the questions of `G` in the conditioned repetition, with the same
  error.

## References

* [T. Holenstein, *Parallel repetition: simplifications and the no-signaling case*][Holenstein2009]
-/

public section

namespace Cslib.PCP.ParallelRepetition

open Finset
open Cslib.Probability.CorrelatedSampling (IsEmbeddable isEmbeddable_map_fst_of_apply_eq_mul)
open scoped ENNReal

variable {X Y A B : Type*}

/-! ### One free coordinate other than `j` -/

section Weights

variable (G : TwoProverGame X Y A B)

open Classical in
/-- Alice's factor at a free coordinate `i ≠ j` whose revealed half is `h`, as a function of her
question there. If `h` is her question `x'`, her question must be `x'`; if `h` is Bob's question
`y'`, the factor is the mass of the pair `(x, y')`. -/
private noncomputable def aliceWeight : X ⊕ Y → X → ℝ≥0∞
  | .inl x', x => if x = x' then 1 else 0
  | .inr y', x => G.questions (x, y')

open Classical in
/-- Bob's factor at a free coordinate `i ≠ j` whose revealed half is `h`, as a function of his
question there. -/
private noncomputable def bobWeight : X ⊕ Y → Y → ℝ≥0∞
  | .inl x', y => G.questions (x', y)
  | .inr y', y => if y = y' then 1 else 0

private theorem aliceWeight_ne_top (h : X ⊕ Y) (x : X) : aliceWeight G h x ≠ ∞ := by
  cases h with
  | inl x' =>
    simp only [aliceWeight]
    split_ifs <;> simp
  | inr y' => exact PMF.apply_ne_top _ _

private theorem bobWeight_ne_top (h : X ⊕ Y) (y : Y) : bobWeight G h y ≠ ∞ := by
  cases h with
  | inl x' => exact PMF.apply_ne_top _ _
  | inr y' =>
    simp only [bobWeight]
    split_ifs <;> simp

open Classical in
/-- At a free coordinate `i ≠ j`, the mass of the pair `p` times the number of bits that reveal the
half `h` of `p` splits into Alice's and Bob's factors. -/
private theorem mul_sum_reveal (h : X ⊕ Y) (p : X × Y) :
    G.questions p * (∑ b : Bool, if h = reveal b p then (1 : ℝ≥0∞) else 0) =
      aliceWeight G h p.1 * bobWeight G h p.2 := by
  obtain ⟨x, y⟩ := p
  rw [mul_comm, Fintype.sum_bool, reveal_true, reveal_false]
  cases h with
  | inl x' =>
    simp only [aliceWeight, bobWeight, Sum.inl.injEq, reduceCtorEq, ite_false, add_zero]
    by_cases hx : x' = x
    · subst hx
      simp
    · simp [hx, Ne.symm hx]
  | inr y' =>
    simp only [aliceWeight, bobWeight, Sum.inr.injEq, reduceCtorEq, ite_false, zero_add]
    by_cases hy : y' = y
    · subst hy
      simp
    · simp [hy, Ne.symm hy]

end Weights

/-! ### The product form of the conditioned law -/

section Factors

variable {n : ℕ} {C : Finset (Fin n)} (G : TwoProverGame X Y A B)
  (ha : (Fin n → X) → Fin n → A) (hb : (Fin n → Y) → Fin n → B) (j : {i // i ∉ C})

open Classical in
/-- Alice's factor of the conditioned law: her question at `j` is `x`, her questions and answers on
`C` are those in `s`, and her questions at the other free coordinates have the weights
`aliceWeight` of the halves in `s`. -/
private noncomputable def aliceFactor : X × Shared X Y A B C j → (Fin n → X) → ℝ≥0∞ :=
  fun (x, s) xs =>
    if xs j = x ∧ ∀ i : C, (s.questions i).1 = xs i ∧ (s.answers i).1 = ha xs i then
      ∏ i : {i : {i // i ∉ C} // i ≠ j}, aliceWeight G (s.halves i) (xs i)
    else 0

open Classical in
/-- Bob's factor of the conditioned law. -/
private noncomputable def bobFactor : Y × Shared X Y A B C j → (Fin n → Y) → ℝ≥0∞ :=
  fun (y, t) ys =>
    if ys j = y ∧ ∀ i : C, (t.questions i).2 = ys i ∧ (t.answers i).2 = hb ys i then
      ∏ i : {i : {i // i ∉ C} // i ≠ j}, bobWeight G (t.halves i) (ys i)
    else 0

private theorem aliceFactor_ne_top (a : X × Shared X Y A B C j) (xs : Fin n → X) :
    aliceFactor G ha j a xs ≠ ∞ := by
  obtain ⟨x, s⟩ := a
  simp only [aliceFactor]
  split_ifs
  · exact ENNReal.prod_ne_top fun i _ => aliceWeight_ne_top G _ _
  · exact ENNReal.zero_ne_top

private theorem bobFactor_ne_top (b : Y × Shared X Y A B C j) (ys : Fin n → Y) :
    bobFactor G hb j b ys ≠ ∞ := by
  obtain ⟨y, t⟩ := b
  simp only [bobFactor]
  split_ifs
  · exact ENNReal.prod_ne_top fun i _ => bobWeight_ne_top G _ _
  · exact ENNReal.zero_ne_top

variable [Fintype X] [Fintype Y]

open Classical in
/-- The common factor of the conditioned law: both parties hold the same `S`, which wins `C`; the
mass of the pair at `j` and of the pairs on `C`; and the normalization. The `2` counts the values of
the bit at `j`, which `S` forgets. -/
private noncomputable def pairFactor :
    X × Shared X Y A B C j → Y × Shared X Y A B C j → ℝ≥0∞ :=
  fun (x, s) (y, t) =>
    if s = t ∧ ∀ i : C,
        G.accepts (s.questions i).1 (s.questions i).2 (s.answers i).1 (s.answers i).2 then
      2 * (2 ^ #Cᶜ)⁻¹ * (∑' ω, (winsOnSample G C ha hb).indicator (sampleLaw G C) ω)⁻¹ *
        G.questions (x, y) * ∏ i : C, G.questions (s.questions i)
    else 0

variable {G ha hb}

/-- The masses of the conditioned law of `(((x_j, S), (y_j, S)), (x, y))`. -/
private theorem map_condLaw_apply
    (hC : ∃ q ∈ G.winsOn ha hb C, q ∈ (G.pow n).questions.support) (x : X)
    (s : Shared X Y A B C j) (y : Y) (t : Shared X Y A B C j) (xs : Fin n → X)
    (ys : Fin n → Y) :
    ((condLaw G C ha hb hC).map fun ω =>
      ((((ω.2 j).1, shared ha hb j ω), ((ω.2 j).2, shared ha hb j ω)),
        (Prod.fst ∘ ω.2, Prod.snd ∘ ω.2))) (((x, s), (y, t)), (xs, ys)) =
      pairFactor G ha hb j (x, s) (y, t) * aliceFactor G ha j (x, s) xs *
        bobFactor G hb j (y, t) ys := by
  classical
  -- Write the question tuples as the components of one tuple of pairs `q`.
  obtain ⟨q, rfl, rfl⟩ : ∃ q : Fin n → X × Y, Prod.fst ∘ q = xs ∧ Prod.snd ∘ q = ys :=
    ⟨fun i => (xs i, ys i), rfl, rfl⟩
  obtain ⟨sq, sh, sa⟩ := s
  -- A sample with the pairs `q` has a mass that does not depend on its bits.
  have hcond : ∀ d, condLaw G C ha hb hC (d, q) =
      (if q ∈ winsOnPairs G C ha hb then (2 ^ #Cᶜ)⁻¹ * ∏ i, G.questions (q i) else 0) *
        (∑' ω, (winsOnSample G C ha hb).indicator (sampleLaw G C) ω)⁻¹ := by
    intro d
    rw [condLaw, PMF.filter_apply, Set.indicator_apply, sampleLaw_apply]
    rfl
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Prod.mk.injEq]
  -- Only the pairs `q` contribute.
  rw [Finset.sum_eq_single q]
  rotate_left
  · intro q' _ hq'
    refine Finset.sum_eq_zero fun d _ => ite_eq_right ?_
    rintro ⟨-, hxs, hys⟩
    exact hq' (funext fun i => Prod.ext (congrFun hxs i).symm (congrFun hys i).symm)
  · intro h
    exact absurd (Finset.mem_univ _) h
  simp only [hcond, and_true, pairFactor, aliceFactor, bobFactor, Function.comp_apply]
  -- Unless Alice's, Bob's and the common conditions hold, both sides vanish.
  by_cases hA : (q j).1 = x ∧ ∀ i : C, (sq i).1 = (q i).1 ∧ (sa i).1 = ha (Prod.fst ∘ q) i
  swap
  · rw [ite_eq_right hA, mul_zero, zero_mul]
    refine Finset.sum_eq_zero fun d _ => ite_eq_right ?_
    rintro ⟨⟨rfl, hs⟩, -⟩
    simp only [shared, revealed, Shared.ofRevealed, Shared.mk.injEq] at hs
    obtain ⟨rfl, -, rfl⟩ := hs
    exact hA ⟨rfl, fun i => ⟨rfl, rfl⟩⟩
  by_cases hB : (q j).2 = y ∧
      ∀ i : C, (t.questions i).2 = (q i).2 ∧ (t.answers i).2 = hb (Prod.snd ∘ q) i
  swap
  · rw [ite_eq_right hB, mul_zero]
    refine Finset.sum_eq_zero fun d _ => ite_eq_right ?_
    rintro ⟨-, rfl, rfl⟩
    exact hB ⟨rfl, fun i => ⟨rfl, rfl⟩⟩
  obtain ⟨rfl, hAC⟩ := hA
  obtain ⟨rfl, hBC⟩ := hB
  by_cases hst : (⟨sq, sh, sa⟩ : Shared X Y A B C j) = t
  swap
  · have hP : ¬((⟨sq, sh, sa⟩ : Shared X Y A B C j) = t ∧
        ∀ i : C, G.accepts (sq i).1 (sq i).2 (sa i).1 (sa i).2) := fun h => hst h.1
    rw [ite_eq_right hP, zero_mul, zero_mul]
    refine Finset.sum_eq_zero fun d _ => ite_eq_right ?_
    rintro ⟨⟨-, hs⟩, -, ht⟩
    exact hst (hs.trans ht.symm)
  subst hst
  -- Now `S` holds the pairs and the answers on `C`, and only its halves depend on the bits.
  have hsq : sq = fun i : C => q i := funext fun i => Prod.ext (hAC i).1 (hBC i).1
  have hsa : sa = answers C ha hb q := funext fun i => Prod.ext (hAC i).2 (hBC i).2
  subst hsq hsa
  have hW : q ∈ winsOnPairs G C ha hb ↔
      ∀ i : C, G.accepts (q i).1 (q i).2 (ha (Prod.fst ∘ q) i) (hb (Prod.snd ∘ q) i) :=
    ⟨fun h i => h i i.2, fun h i hi => h ⟨i, hi⟩⟩
  simp only [shared, revealed, Shared.ofRevealed, Shared.mk.injEq, answers, hW, true_and, and_true,
    and_self, funext_iff, implies_true, ↓reduceIte]
  by_cases hacc : ∀ i : C, G.accepts (q i).1 (q i).2 (ha (Prod.fst ∘ q) i) (hb (Prod.snd ∘ q) i)
  swap
  · simp only [hacc, ↓reduceIte, zero_mul, ite_self, Finset.sum_const_zero]
  simp only [hacc, implies_true, ↓reduceIte, Prod.mk.eta]
  -- The bits at the free coordinates other than `j` are determined by the halves of `S`.
  have hbits (φ : {i : {i // i ∉ C} // i ≠ j} → Bool → ℝ≥0∞) :
      ∑ d : {i // i ∉ C} → Bool, ∏ i, φ i (d i) = 2 * ∏ i, ∑ b, φ i b := by
    rw [Fintype.sum_equiv (Equiv.piSplitAt j fun _ => Bool) (fun d => ∏ i, φ i (d i))
      (fun e => ∏ i, φ i (e.2 i)) fun _ => rfl, Fintype.sum_prod_type]
    dsimp only
    rw [Fintype.prod_sum, Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul,
      Nat.cast_ofNat]
  have hsum (c : ℝ≥0∞) : ∑ d : {i // i ∉ C} → Bool,
      (if ∀ i, sh i = reveal (d i) (q i) then c else 0) =
        2 * (∏ i, ∑ b : Bool, if sh i = reveal b (q i) then 1 else 0) * c := by
    simp only [← boole_mul _ c, ← Finset.sum_mul, ← Fintype.prod_boole]
    exact congrArg (· * c) (hbits fun i b => if sh i = reveal b (q i) then 1 else 0)
  rw [hsum]
  -- Each pair splits into Alice's and Bob's factors.
  have hprod : (∏ i, G.questions (q i)) *
      ∏ i : {i : {i // i ∉ C} // i ≠ j}, (∑ b : Bool, if sh i = reveal b (q i) then 1 else 0) =
        (∏ i : C, G.questions (q i)) * G.questions (q j) *
          ((∏ i, aliceWeight G (sh i) (q i).1) * ∏ i, bobWeight G (sh i) (q i).2) := by
    rw [← Finset.prod_mul_prod_compl C, ← Finset.prod_coe_sort C,
      Finset.prod_subtype Cᶜ (fun _ => Finset.mem_compl) fun i => G.questions (q i),
      Fintype.prod_eq_mul_prod_subtype_ne (fun i : {i // i ∉ C} => G.questions (q i)) j,
      ← Finset.prod_mul_distrib, mul_assoc, mul_assoc, ← Finset.prod_mul_distrib, mul_assoc]
    simp only [mul_sum_reveal]
  calc _ = 2 * (2 ^ #Cᶜ)⁻¹ * (∑' ω, (winsOnSample G C ha hb).indicator (sampleLaw G C) ω)⁻¹ *
        ((∏ i, G.questions (q i)) * ∏ i : {i : {i // i ∉ C} // i ≠ j},
          ∑ b : Bool, if sh i = reveal b (q i) then 1 else 0) := by
        ring
    _ = _ := by
        rw [hprod]
        ring

/-- **The product form (5.5) of the conditioned law** [Holenstein, proof of Lemma 6.4,
(6.17)–(6.19), and (5.5)][Holenstein2009]. Under `W_C`, the mass of
`(((x_j, S), (y_j, S)), (x, y))` factors as
`c ((x_j, S), (y_j, S)) · f ((x_j, S), x) · g ((y_j, S), y)`, where `S = shared j` and `(x, y)`
are the question tuples. So given Alice's view `(x_j, S)` and Bob's view `(y_j, S)`, the tuples `x`
and `y` are independent, and each depends on its own view only: this is Holenstein's pair of Markov
chains (6.18)–(6.19), in the form (5.5) that Lemma 5.4 uses. -/
theorem exists_map_condLaw_apply_eq_mul
    (hC : ∃ q ∈ G.winsOn ha hb C, q ∈ (G.pow n).questions.support) :
    ∃ (c : X × Shared X Y A B C j → Y × Shared X Y A B C j → ℝ≥0∞)
      (f : X × Shared X Y A B C j → (Fin n → X) → ℝ≥0∞)
      (g : Y × Shared X Y A B C j → (Fin n → Y) → ℝ≥0∞),
      (∀ a x, f a x ≠ ∞) ∧ (∀ b y, g b y ≠ ∞) ∧ ∀ a b x y,
        ((condLaw G C ha hb hC).map fun ω =>
          ((((ω.2 j).1, shared ha hb j ω), ((ω.2 j).2, shared ha hb j ω)),
            (Prod.fst ∘ ω.2, Prod.snd ∘ ω.2))) ((a, b), (x, y)) =
          c a b * f a x * g b y := by
  refine ⟨pairFactor G ha hb j, aliceFactor G ha j, bobFactor G hb j, aliceFactor_ne_top G ha j,
    bobFactor_ne_top G hb j, ?_⟩
  rintro ⟨x, s⟩ ⟨y, t⟩ xs ys
  exact map_condLaw_apply j hC x s y t xs ys

/-- **The second stage of Holenstein's embedding** [Holenstein, proof of Lemma 6.4, (6.17)–(6.19)
and Lemma 5.4][Holenstein2009]. Under `W_C`, the law of `((x_j, S), (y_j, S))` embeds exactly in
the law of `(((x_j, S), (y_j, S)), (x, y))`, where `S = shared j` and `(x, y)` are the question
tuples: from Alice's view `(x_j, S)` and Bob's view `(y_j, S)`, the parties sample `x` and `y`
locally. The input law is the law of `((x_j, y_j), (S, S))`, the output of the first stage,
regrouped as `IsEmbeddable.trans` requires; after `rw [PMF.map_comp]`, it is the second premise of
`IsEmbeddable.trans` for that output. -/
theorem isEmbeddable_map_condLaw_tuples [Fintype A] [Fintype B]
    (hC : ∃ q ∈ G.winsOn ha hb C, q ∈ (G.pow n).questions.support) :
    IsEmbeddable
      ((condLaw G C ha hb hC).map fun ω =>
        (((ω.2 j).1, shared ha hb j ω), ((ω.2 j).2, shared ha hb j ω)))
      ((condLaw G C ha hb hC).map fun ω =>
        ((((ω.2 j).1, shared ha hb j ω), ((ω.2 j).2, shared ha hb j ω)),
          (Prod.fst ∘ ω.2, Prod.snd ∘ ω.2)))
      0 := by
  obtain ⟨c, f, g, hf, hg, hJ⟩ := exists_map_condLaw_apply_eq_mul j hC
  have h := isEmbeddable_map_fst_of_apply_eq_mul _ c f g hf hg hJ
  rw [PMF.map_comp] at h
  exact h

/-- **The two stages of Holenstein's embedding, composed** [Holenstein, proof of
Lemma 6.4][Holenstein2009]. Let `S = shared j`. If a law `P₀` embeds with error `ε` in the law of
`((x_j, y_j), (S, S))` under `W_C`, as Corollary 5.3 (`isEmbeddable_diag_of_dist_le`) provides, then
`P₀` embeds with error `ε` in the questions `(x, y)` of the repetition conditioned on `W_C`, with
`(x_j, y_j)` as the input coordinate. This is the premise of strategy extraction
(`TwoProverGame.winProbOn_insert_le`). -/
theorem isEmbeddable_filter_questions_of_shared [Fintype A] [Fintype B]
    (hC : ∃ q ∈ G.winsOn ha hb C, q ∈ (G.pow n).questions.support) {P₀ : PMF (X × Y)} {ε : ℝ}
    (h : IsEmbeddable P₀
      ((condLaw G C ha hb hC).map fun ω => (ω.2 j, (shared ha hb j ω, shared ha hb j ω))) ε) :
    IsEmbeddable P₀
      (((G.pow n).questions.filter (G.winsOn ha hb C) hC).map fun (x, y) => ((x j, y j), (x, y)))
      ε := by
  -- The second stage, from the regrouped output of the first.
  have h₂ : IsEmbeddable (((condLaw G C ha hb hC).map fun ω =>
      (ω.2 j, (shared ha hb j ω, shared ha hb j ω))).map fun ((x, y), (s, t)) => ((x, s), (y, t)))
      ((condLaw G C ha hb hC).map fun ω =>
        ((((ω.2 j).1, shared ha hb j ω), ((ω.2 j).2, shared ha hb j ω)),
          (Prod.fst ∘ ω.2, Prod.snd ∘ ω.2))) 0 := by
    rw [PMF.map_comp]
    exact isEmbeddable_map_condLaw_tuples j hC
  -- Compose, and forget `S`.
  have h₃ := (h.trans h₂).map (fun (_ : X) (su : Shared X Y A B C j × (Fin n → X)) => su.2)
    (fun (_ : Y) (tv : Shared X Y A B C j × (Fin n → Y)) => tv.2)
  rw [add_zero] at h₃
  convert h₃ using 2
  rw [← map_condLaw_questions hC]
  simp only [PMF.map_comp]
  rfl

end Factors

end Cslib.PCP.ParallelRepetition
