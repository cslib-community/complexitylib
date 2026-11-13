/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.UniformNat
public import CslibFrontier.Crypto.Computational.InaccessibleEntropy.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Probability.BitString.List
import CslibFrontier.Probability.Concentration
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.Product
import CslibFrontier.Computability.Probabilistic.PPT.Capture

/-!
# Gap amplification for inaccessible entropy via parallel repetition

Given a deterministic function $f_0 : \alpha \to \beta$ on a finite uniform domain $\alpha$, its
$t$-fold direct product $f_0^t : (\mathrm{Fin}\;t \to \alpha) \to (\mathrm{Fin}\;t \to \beta)$
(`repHashFin t f₀`) multiplies preimage fiber sizes across coordinates, turning `realSampleEntropy`
and $\log_2 |L_0^t(z)|$ (`repAccessibleSet t L₀`) into sums of $t$ independent bounded coordinate
scores. Following `[HHRVW2020]`, Section 5.1.1, Lemma 5.3 (pp. 26–27):

1. **Real-entropy concentration** (`repHashFin_realSampleEntropy_le_prob`, Lemma 5.3(i), p. 26):
   by Hoeffding's lower-tail bound (`PMF.pi_sum_le_mean_sub`), `realSampleEntropy (repHashFin t f₀)`
   falls below $t \cdot H(X \mid f_0(X)) - \Delta$ with probability at most
   $\exp(-2 \Delta^2 / (t B^2))$ whenever $\log_2 |\alpha| \le B$.
2. **Accessible-set concentration** (`repAccessibleSet_logb_card_ge_prob`, Lemma 5.3(ii),
   Equation (5.1), p. 27): by Hoeffding's upper-tail bound (`PMF.pi_sum_ge_mean_add`),
   $\log_2 |L_0^t(z)|$ exceeds $t \cdot \mathbb{E}[\log_2 |L_0(X)|] + \Delta$ with probability at
   most $\exp(-2 \Delta^2 / (t B^2))$.
3. **Planted-coordinate escape reduction** (`repEscapeInverter`, `isPPT_repEscapeInverter`,
   `repEscape_le_dyadicSize_mul_escape`, Lemma 5.3(ii), pp. 26–27): planting a single challenge
   input at a uniformly sampled dyadic index (`ProbComp.sampleDyadicIndex`) via
   `BitString.replaceRow` (`BitString.uniformList_replaceRow`) reduces escaping $L_0^t$ to escaping
   $L_0$ with concrete multiplicative loss `dyadicSize (t n) ≤ 2 * (t n + 1)`.

## Main definitions

* `Cslib.Crypto.repHashFin`, `Cslib.Crypto.repAccessibleSet`: finite $t$-fold direct product and
  product accessible preimage sets.
* `Cslib.Crypto.repEvalWord`, `Cslib.Crypto.repBitAccessibleSet`: word-level evaluator and flat
  `BitString (t * inLen₀)` accessible sets via `BitString.blocksEquiv`.
* `Cslib.Crypto.repEscapeInverter`: uniform strict-PPT planted-coordinate escape reduction.

## Main results

* `Cslib.Crypto.realSampleEntropy_repHashFin`, `Cslib.Crypto.logb_card_repAccessibleSet`:
  additivity of real sample entropy and accessible log-cardinality across coordinates.
* `Cslib.Crypto.repHashFin_realSampleEntropy_le_prob`,
  `Cslib.Crypto.repAccessibleSet_logb_card_ge_prob`: Hoeffding concentration bounds for Lemma 5.3.
* `Cslib.Crypto.computableInPolyTime_repEvalWord`: plain polynomial-time certificate for
  `repEvalWord`.
* `Cslib.Crypto.isPPT_repEscapeInverter`: plain uniform strict-PPT certificate for
  `repEscapeInverter`.
* `Cslib.Crypto.repEscape_le_dyadicSize_mul_escape`: concrete finite-$n$ reduction from $t$-fold
  accessible escape to single-coordinate accessible escape.

## References

* [I. Haitner, T. Holenstein, O. Reingold, S. Vadhan, H. Wee, *Inaccessible Entropy II: IE
  Functions and Universal One-Way Hashing*, Section 5.1.1, Lemma 5.3, pp. 26–27][HHRVW2020]
-/

public section

namespace Cslib.Crypto

open Cslib.Probability Finset Turing.MultiTapeTM
open scoped BigOperators ENNReal NNReal

/-! ### Finite $t$-fold direct product and product accessible sets -/

/-- Finite $t$-fold direct product $f_0^t(z)_i = f_0(z_i)$ (`[HHRVW2020]`, Section 5.1.1,
Lemma 5.3, p. 26). -/
@[expose] def repHashFin (t : ℕ) {α β : Type*} (f₀ : α → β) (z : Fin t → α) : Fin t → β :=
  fun i => f₀ (z i)

/-- Product accessible set $L_0^t(z) = \prod_{i < t} L_0(z_i)$ (`[HHRVW2020]`, Section 5.1.1,
p. 27). -/
@[expose] def repAccessibleSet (t : ℕ) {α : Type*} (L₀ : α → Finset α)
    (z : Fin t → α) : Finset (Fin t → α) :=
  Fintype.piFinset fun i => L₀ (z i)

@[simp] theorem mem_repAccessibleSet {t : ℕ} {α : Type*}
    (L₀ : α → Finset α) (z z' : Fin t → α) :
    z' ∈ repAccessibleSet t L₀ z ↔ ∀ i, z' i ∈ L₀ (z i) :=
  Fintype.mem_piFinset

theorem self_mem_repAccessibleSet {t : ℕ} {α : Type*} {L₀ : α → Finset α}
    (hself : ∀ x, x ∈ L₀ x) (z : Fin t → α) :
    z ∈ repAccessibleSet t L₀ z :=
  Fintype.mem_piFinset.mpr fun i => hself (z i)

theorem fiberSet_repHashFin (t : ℕ) {α β : Type*} [Fintype α] [DecidableEq β]
    (f₀ : α → β) (y : Fin t → β) :
    fiberSet (repHashFin t f₀) y = Fintype.piFinset fun i => fiberSet f₀ (y i) := by
  ext x
  simp only [mem_fiberSet, repHashFin, Fintype.mem_piFinset, funext_iff]

theorem repAccessibleSet_subset_fiber {t : ℕ} {α β : Type*} [Fintype α]
    [DecidableEq β] {f₀ : α → β} {L₀ : α → Finset α}
    (hsub : ∀ x, L₀ x ⊆ fiberSet f₀ (f₀ x)) (z : Fin t → α) :
    repAccessibleSet t L₀ z ⊆ fiberSet (repHashFin t f₀) (repHashFin t f₀ z) := by
  intro z' hz'
  rw [fiberSet_repHashFin, Fintype.mem_piFinset]
  intro i
  exact hsub (z i) ((mem_repAccessibleSet L₀ z z').mp hz' i)

theorem card_fiberSet_repHashFin (t : ℕ) {α β : Type*} [Fintype α] [DecidableEq β]
    (f₀ : α → β) (y : Fin t → β) :
    #(fiberSet (repHashFin t f₀) y) = ∏ i : Fin t, #(fiberSet f₀ (y i)) := by
  classical
  rw [fiberSet_repHashFin, Fintype.card_piFinset]

theorem card_repAccessibleSet (t : ℕ) {α : Type*} (L₀ : α → Finset α)
    (z : Fin t → α) :
    #(repAccessibleSet t L₀ z) = ∏ i : Fin t, #(L₀ (z i)) :=
  Fintype.card_piFinset _

/-- Real sample entropy is additive across independent coordinates of `repHashFin`. -/
theorem realSampleEntropy_repHashFin (t : ℕ) {α β : Type*} [Fintype α] [DecidableEq β]
    (f₀ : α → β) (z : Fin t → α) :
    realSampleEntropy (repHashFin t f₀) z = ∑ i : Fin t, realSampleEntropy f₀ (z i) := by
  simp only [realSampleEntropy, card_fiberSet_repHashFin, repHashFin, Nat.cast_prod, Real.logb]
  rw [Real.log_prod (fun i _ => by exact_mod_cast (card_fiberSet_pos f₀ (z i)).ne'), sum_div]

/-- Accessible log-cardinality is additive across coordinates when every $L_0(x)$ is nonempty. -/
theorem logb_card_repAccessibleSet (t : ℕ) {α : Type*} {L₀ : α → Finset α}
    (hne : ∀ x, (L₀ x).Nonempty) (z : Fin t → α) :
    Real.logb 2 #(repAccessibleSet t L₀ z) = ∑ i : Fin t, Real.logb 2 #(L₀ (z i)) := by
  simp only [card_repAccessibleSet, Nat.cast_prod, Real.logb]
  rw [Real.log_prod (fun i _ => by exact_mod_cast (card_pos.mpr (hne (z i))).ne'), sum_div]

/-! ### Hoeffding concentration bounds (Lemma 5.3(i)–(ii)) -/

/-- **`[HHRVW2020]`, Section 5.1.1, Lemma 5.3(i) (p. 26)**: under uniform sampling on
$\mathrm{Fin}\;t \to \alpha$, `realSampleEntropy (repHashFin t f₀)` falls below
$t \cdot H(X \mid f_0(X)) - \Delta$ with probability at most $\exp(-2 \Delta^2 / (t B^2))$. -/
theorem repHashFin_realSampleEntropy_le_prob (t : ℕ) {α β : Type*}
    [Fintype α] [Nonempty α] [Finite β] [DecidableEq β] (f₀ : α → β)
    {B Δ : ℝ} (hB_nonneg : 0 ≤ B) (hB : Real.logb 2 (Fintype.card α) ≤ B) (hΔ : 0 ≤ Δ) :
    ((PMF.uniformOfFintype (Fin t → α)).toOuterMeasure
      {z | realSampleEntropy (repHashFin t f₀) z ≤
        t * PMF.conditionalEntropy ((PMF.uniformOfFintype α).map fun x => (f₀ x, x)) - Δ}).toReal ≤
      Real.exp (-2 * Δ ^ 2 / (t * B ^ 2)) := by
  have hconc := PMF.pi_sum_le_mean_sub
    (fun _ : Fin t => PMF.uniformOfFintype α)
    (fun _ (x : α) => realSampleEntropy f₀ x) hB_nonneg
    (fun _ x _ => ⟨realSampleEntropy_nonneg f₀ x, (realSampleEntropy_le_log_card f₀ x).trans hB⟩)
    hΔ
  rw [PMF.pi_uniformOfFintype, Fintype.card_fin] at hconc
  have hmean : (∑ _i : Fin t, ∑ x : α,
      ((PMF.uniformOfFintype α) x).toReal * realSampleEntropy f₀ x) =
      t * PMF.conditionalEntropy ((PMF.uniformOfFintype α).map fun x => (f₀ x, x)) := by
    simp only [expected_realSampleEntropy_eq_conditionalEntropy f₀, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have hevent : {z : Fin t → α | realSampleEntropy (repHashFin t f₀) z ≤
      t * PMF.conditionalEntropy ((PMF.uniformOfFintype α).map fun x => (f₀ x, x)) - Δ} =
      {z : Fin t → α | ∑ i : Fin t, realSampleEntropy f₀ (z i) ≤
        (∑ _i : Fin t, ∑ x : α, ((PMF.uniformOfFintype α) x).toReal * realSampleEntropy f₀ x) -
          Δ} := by
    ext z
    simp only [Set.mem_ofPred_eq, realSampleEntropy_repHashFin, hmean]
  rwa [hevent]

/-- **`[HHRVW2020]`, Section 5.1.1, Lemma 5.3(ii), Equation (5.1) (p. 27)**: when
$x \in L_0(x) \subseteq \alpha$ for all $x$, $\log_2 |L_0^t(z)|$ exceeds
$t \cdot \mathbb{E}[\log_2 |L_0(X)|] + \Delta$ with probability at most
$\exp(-2 \Delta^2 / (t B^2))$. -/
theorem repAccessibleSet_logb_card_ge_prob (t : ℕ) {α : Type*}
    [Fintype α] [Nonempty α] (L₀ : α → Finset α)
    (hself : ∀ x, x ∈ L₀ x)
    {B Δ : ℝ} (hB_nonneg : 0 ≤ B) (hB : Real.logb 2 (Fintype.card α) ≤ B) (hΔ : 0 ≤ Δ) :
    ((PMF.uniformOfFintype (Fin t → α)).toOuterMeasure
      {z | t * accessibleSetExpectation L₀ + Δ ≤ Real.logb 2 #(repAccessibleSet t L₀ z)}).toReal ≤
      Real.exp (-2 * Δ ^ 2 / (t * B ^ 2)) := by
  have hne : ∀ x, (L₀ x).Nonempty := fun x => ⟨x, hself x⟩
  have hscore (x : α) : Real.logb 2 #(L₀ x) ∈ Set.Icc 0 B := by
    refine ⟨Real.logb_nonneg (by norm_num) (by exact_mod_cast card_pos.mpr (hne x)), ?_⟩
    exact (Real.logb_le_logb_of_le (by norm_num)
      (by exact_mod_cast card_pos.mpr (hne x))
      (by exact_mod_cast card_le_univ (L₀ x))).trans hB
  have hconc := PMF.pi_sum_ge_mean_add
    (fun _ : Fin t => PMF.uniformOfFintype α)
    (fun _ (x : α) => Real.logb 2 #(L₀ x)) hB_nonneg (fun _ x _ => hscore x) hΔ
  rw [PMF.pi_uniformOfFintype, Fintype.card_fin] at hconc
  have hmean : (∑ _i : Fin t, ∑ x : α,
      ((PMF.uniformOfFintype α) x).toReal * Real.logb 2 #(L₀ x)) =
      t * accessibleSetExpectation L₀ := by
    simp only [accessibleSetExpectation, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hevent : {z : Fin t → α |
      t * accessibleSetExpectation L₀ + Δ ≤ Real.logb 2 #(repAccessibleSet t L₀ z)} =
      {z : Fin t → α |
        (∑ _i : Fin t, ∑ x : α, ((PMF.uniformOfFintype α) x).toReal * Real.logb 2 #(L₀ x)) + Δ ≤
          ∑ i : Fin t, Real.logb 2 #(L₀ (z i))} := by
    ext z
    simp only [Set.mem_ofPred_eq, logb_card_repAccessibleSet t hne, hmean]
  rwa [hevent]

/-! ### Word-level evaluator and flat `BitString` bridge -/

/-- Word-level evaluator of the $t$-fold parallel repetition: slice `w` into `t` rows of width
`inLen₀`, evaluate `evalWord₀` on each row, and concatenate the outputs. -/
@[expose] def repEvalWord (t inLen₀ : ℕ) (evalWord₀ : List Bool → List Bool)
    (w : List Bool) : List Bool :=
  (List.range t).flatMap fun i => evalWord₀ (Cslib.BitString.listRow inLen₀ i w)

/-- Plain polynomial-time certificate for `repEvalWord` when `t`, `inLen₀`, and `n` are supplied in
unary. -/
@[fun_prop]
theorem computableInPolyTime_repEvalWord {α : Type} {encode : α ↪ List Bool}
    {t inLen₀ n : α → ℕ} {evalWord₀ : ℕ → List Bool → List Bool} {w : α → List Bool}
    (ht : ComputableInPolyTime t encode encUnary)
    (hin₀ : ComputableInPolyTime inLen₀ encode encUnary)
    (hn : ComputableInPolyTime n encode encUnary)
    (heval₀ : ComputableInPolyTime (fun p : ℕ × List Bool => evalWord₀ p.1 p.2)
      (encPair encUnary encBits) encBits)
    (hw : ComputableInPolyTime w encode encBits) :
    ComputableInPolyTime
      (fun a => repEvalWord (t a) (inLen₀ a) (evalWord₀ (n a)) (w a))
      encode encBits := by
  unfold repEvalWord
  apply ComputableInPolyTime.flatMapToBitsWithInput
    (ComputableInPolyTime.unary_range' ht)
  have hfst := ComputableInPolyTime.fst encode encUnary
  have hsnd := ComputableInPolyTime.snd encode encUnary
  have hrow := ComputableInPolyTime.bitsRowWithInput (hin₀.comp hfst) hsnd (hw.comp hfst)
  exact heval₀.comp ((hn.comp hfst).prod hrow)

theorem length_repEvalWord {t inLen₀ outLen₀ : ℕ} {evalWord₀ : List Bool → List Bool}
    (hlen : ∀ u, u.length = inLen₀ → (evalWord₀ u).length = outLen₀) (w : List Bool) :
    (repEvalWord t inLen₀ evalWord₀ w).length = t * outLen₀ := by
  have hmap : List.map (fun i => (evalWord₀ (Cslib.BitString.listRow inLen₀ i w)).length)
      (List.range t) = List.replicate t outLen₀ := by
    rw [List.eq_replicate_iff]
    refine ⟨by simp, fun len hmem => ?_⟩
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hmem
    exact hlen _ (Cslib.BitString.length_listRow inLen₀ i w)
  rw [repEvalWord, List.length_flatMap, hmap, List.sum_replicate, smul_eq_mul]

theorem listRow_repEvalWord {t inLen₀ outLen₀ : ℕ} {evalWord₀ : List Bool → List Bool}
    (hlen : ∀ u, u.length = inLen₀ → (evalWord₀ u).length = outLen₀) (w : List Bool)
    {j : ℕ} (hj : j < t) :
    Cslib.BitString.listRow outLen₀ j (repEvalWord t inLen₀ evalWord₀ w) =
      evalWord₀ (Cslib.BitString.listRow inLen₀ j w) := by
  have h := Cslib.BitString.listRow_flatMap_append
    (width := outLen₀)
    (fun i => evalWord₀ (Cslib.BitString.listRow inLen₀ i w))
    (List.range t)
    (fun i _ => hlen _ (Cslib.BitString.length_listRow inLen₀ i w))
    [] j (by simpa using hj)
  simpa [repEvalWord] using h

/-- Exact agreement between `wordToFinMap` of `repEvalWord` and `repHashFin` conjugated by
`BitString.blocksEquiv`. -/
theorem wordToFinMap_repEvalWord {t inLen₀ outLen₀ : ℕ} {evalWord₀ : List Bool → List Bool}
    (hlen : ∀ u, u.length = inLen₀ → (evalWord₀ u).length = outLen₀)
    (z : BitString (t * inLen₀)) :
    wordToFinMap (t * inLen₀) (t * outLen₀) (repEvalWord t inLen₀ evalWord₀) z =
      Cslib.BitString.blocksEquiv.symm
        (repHashFin t (wordToFinMap inLen₀ outLen₀ evalWord₀)
          (Cslib.BitString.blocksEquiv z)) := by
  have hwords : repEvalWord t inLen₀ evalWord₀ (List.ofFn z) =
      List.ofFn (Cslib.BitString.blocksEquiv.symm
        (repHashFin t (wordToFinMap inLen₀ outLen₀ evalWord₀)
          (Cslib.BitString.blocksEquiv z))) := by
    rw [Cslib.BitString.ofFn_blocksEquiv_symm, repEvalWord, List.flatMap_def]
    congr 1
    apply List.ext_getElem (by simp)
    intro i hi₁ hi₂
    simp only [List.length_map, List.length_range] at hi₁
    let idx : Fin t := ⟨i, hi₁⟩
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
    have hrow : Cslib.BitString.listRow inLen₀ i (List.ofFn z) =
        List.ofFn (Cslib.BitString.blocksEquiv z idx) := by
      simpa only [Cslib.BitString.ofList_ofFn, Cslib.BitString.blocksEquiv_apply] using
        Cslib.BitString.listRow_eq_ofFn inLen₀ idx (List.ofFn z)
    rw [hrow, repHashFin, wordToFinMap,
      Cslib.BitString.ofFn_ofList (hlen _ List.length_ofFn)]
  rw [wordToFinMap, hwords, Cslib.BitString.ofList_ofFn]

/-- Flat `BitString (t * inLen₀)` view of `repAccessibleSet t L₀`. -/
@[expose] def repBitAccessibleSet (t inLen₀ : ℕ)
    (L₀ : BitString inLen₀ → Finset (BitString inLen₀))
    (z : BitString (t * inLen₀)) : Finset (BitString (t * inLen₀)) :=
  (repAccessibleSet t L₀ (Cslib.BitString.blocksEquiv z)).map
    Cslib.BitString.blocksEquiv.symm.toEmbedding

@[simp] theorem mem_repBitAccessibleSet {t inLen₀ : ℕ}
    (L₀ : BitString inLen₀ → Finset (BitString inLen₀))
    (z z' : BitString (t * inLen₀)) :
    z' ∈ repBitAccessibleSet t inLen₀ L₀ z ↔
      ∀ i : Fin t, Cslib.BitString.blocksEquiv z' i ∈ L₀ (Cslib.BitString.blocksEquiv z i) := by
  rw [repBitAccessibleSet, mem_map_equiv]
  simp only [Equiv.symm_symm, mem_repAccessibleSet]

@[simp] theorem card_repBitAccessibleSet (t inLen₀ : ℕ)
    (L₀ : BitString inLen₀ → Finset (BitString inLen₀))
    (z : BitString (t * inLen₀)) :
    #(repBitAccessibleSet t inLen₀ L₀ z) =
      #(repAccessibleSet t L₀ (Cslib.BitString.blocksEquiv z)) :=
  card_map _

theorem self_mem_repBitAccessibleSet {t inLen₀ : ℕ}
    {L₀ : BitString inLen₀ → Finset (BitString inLen₀)}
    (hself : ∀ x, x ∈ L₀ x) (z : BitString (t * inLen₀)) :
    z ∈ repBitAccessibleSet t inLen₀ L₀ z :=
  (mem_repBitAccessibleSet L₀ z z).mpr fun _ => hself _

theorem repBitAccessibleSet_subset_fiber {t inLen₀ outLen₀ : ℕ}
    {evalWord₀ : List Bool → List Bool}
    (hlen : ∀ u, u.length = inLen₀ → (evalWord₀ u).length = outLen₀)
    {L₀ : BitString inLen₀ → Finset (BitString inLen₀)}
    (hsub : ∀ x, L₀ x ⊆ fiberSet (wordToFinMap inLen₀ outLen₀ evalWord₀)
      (wordToFinMap inLen₀ outLen₀ evalWord₀ x))
    (z : BitString (t * inLen₀)) :
    repBitAccessibleSet t inLen₀ L₀ z ⊆
      fiberSet (wordToFinMap (t * inLen₀) (t * outLen₀) (repEvalWord t inLen₀ evalWord₀))
        (wordToFinMap (t * inLen₀) (t * outLen₀) (repEvalWord t inLen₀ evalWord₀) z) := by
  intro z' hz'
  rw [mem_fiberSet, wordToFinMap_repEvalWord hlen, wordToFinMap_repEvalWord hlen]
  congr 1 with i : 1
  dsimp only [repHashFin]
  exact (mem_fiberSet _ _ _).mp (hsub _ ((mem_repBitAccessibleSet L₀ z z').mp hz' i))

theorem realSampleEntropy_wordToFinMap_repEvalWord {t inLen₀ outLen₀ : ℕ}
    {evalWord₀ : List Bool → List Bool}
    (hlen : ∀ u, u.length = inLen₀ → (evalWord₀ u).length = outLen₀)
    (z : BitString (t * inLen₀)) :
    realSampleEntropy
        (wordToFinMap (t * inLen₀) (t * outLen₀) (repEvalWord t inLen₀ evalWord₀)) z =
      realSampleEntropy
        (repHashFin t (wordToFinMap inLen₀ outLen₀ evalWord₀))
        (Cslib.BitString.blocksEquiv z) := by
  let f₀ := wordToFinMap inLen₀ outLen₀ evalWord₀
  let f₁ := wordToFinMap (t * inLen₀) (t * outLen₀) (repEvalWord t inLen₀ evalWord₀)
  have hcard : #(fiberSet f₁ (f₁ z)) =
      #(fiberSet (repHashFin t f₀) (repHashFin t f₀ (Cslib.BitString.blocksEquiv z))) := by
    refine Finset.card_bij (fun z' _ => Cslib.BitString.blocksEquiv z') ?_ ?_ ?_
    · intro z' hz'
      rw [mem_fiberSet] at hz' ⊢
      exact Cslib.BitString.blocksEquiv.symm.injective
        (by simpa only [f₁, f₀, wordToFinMap_repEvalWord hlen] using hz')
    · intro z₁ _ z₂ _ heq
      exact Cslib.BitString.blocksEquiv.injective heq
    · intro u hu
      refine ⟨Cslib.BitString.blocksEquiv.symm u, ?_,
        Cslib.BitString.blocksEquiv.apply_symm_apply u⟩
      rw [mem_fiberSet] at hu ⊢
      simp only [f₁, f₀, wordToFinMap_repEvalWord hlen, Equiv.apply_symm_apply, hu]
  simp only [realSampleEntropy, f₁, f₀, hcard]

/-- Flat `BitString` lower-tail Hoeffding bound for `repEvalWord` (`[HHRVW2020]`, Lemma 5.3(i),
p. 26). -/
theorem repEvalWord_realSampleEntropy_le_prob {t inLen₀ outLen₀ : ℕ}
    {evalWord₀ : List Bool → List Bool}
    (hlen : ∀ u, u.length = inLen₀ → (evalWord₀ u).length = outLen₀)
    {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    let f₀ := wordToFinMap inLen₀ outLen₀ evalWord₀
    let f₁ := wordToFinMap (t * inLen₀) (t * outLen₀) (repEvalWord t inLen₀ evalWord₀)
    ((PMF.uniformOfFintype (BitString (t * inLen₀))).toOuterMeasure
      {z | realSampleEntropy f₁ z ≤
        t * PMF.conditionalEntropy ((PMF.uniformOfFintype (BitString inLen₀)).map fun x =>
          (f₀ x, x)) - Δ}).toReal ≤
      Real.exp (-2 * Δ ^ 2 / (t * (inLen₀ : ℝ) ^ 2)) := by
  intro f₀ f₁
  have h := repHashFin_realSampleEntropy_le_prob t f₀ (Nat.cast_nonneg inLen₀)
    (by simp [Real.logb_pow]) hΔ
  rw [← PMF.uniformOfFintype_map_equiv Cslib.BitString.blocksEquiv,
    PMF.toOuterMeasure_map_apply] at h
  have hevent : (Cslib.BitString.blocksEquiv ⁻¹'
      {u : Fin t → BitString inLen₀ | realSampleEntropy (repHashFin t f₀) u ≤
        t * PMF.conditionalEntropy ((PMF.uniformOfFintype (BitString inLen₀)).map fun x =>
          (f₀ x, x)) - Δ}) =
      {z : BitString (t * inLen₀) | realSampleEntropy f₁ z ≤
        t * PMF.conditionalEntropy ((PMF.uniformOfFintype (BitString inLen₀)).map fun x =>
          (f₀ x, x)) - Δ} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, f₁, f₀,
      realSampleEntropy_wordToFinMap_repEvalWord hlen]
  rwa [hevent] at h

/-- Flat `BitString` upper-tail Hoeffding bound for `repBitAccessibleSet` (`[HHRVW2020]`,
Lemma 5.3(ii), Equation (5.1), p. 27). -/
theorem repBitAccessibleSet_logb_card_ge_prob (t inLen₀ : ℕ)
    (L₀ : BitString inLen₀ → Finset (BitString inLen₀))
    (hself : ∀ x, x ∈ L₀ x) {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    ((PMF.uniformOfFintype (BitString (t * inLen₀))).toOuterMeasure
      {z | t * accessibleSetExpectation L₀ + Δ ≤
        Real.logb 2 #(repBitAccessibleSet t inLen₀ L₀ z)}).toReal ≤
      Real.exp (-2 * Δ ^ 2 / (t * (inLen₀ : ℝ) ^ 2)) := by
  have h := repAccessibleSet_logb_card_ge_prob t L₀ hself (Nat.cast_nonneg inLen₀)
    (by simp [Real.logb_pow]) hΔ
  rw [← PMF.uniformOfFintype_map_equiv Cslib.BitString.blocksEquiv,
    PMF.toOuterMeasure_map_apply] at h
  have hevent : (Cslib.BitString.blocksEquiv ⁻¹'
      {u : Fin t → BitString inLen₀ |
        t * accessibleSetExpectation L₀ + Δ ≤ Real.logb 2 #(repAccessibleSet t L₀ u)}) =
      {z : BitString (t * inLen₀) |
        t * accessibleSetExpectation L₀ + Δ ≤
          Real.logb 2 #(repBitAccessibleSet t inLen₀ L₀ z)} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, card_repBitAccessibleSet]
  rwa [hevent] at h

/-! ### Planted-coordinate escape reduction (Lemma 5.3(ii)) -/

private theorem computableInPolyTime_replaceRow {α : Type} {encode : α ↪ List Bool}
    {width count j : α → ℕ} {x word : α → List Bool}
    (hwidth : ComputableInPolyTime width encode encUnary)
    (hcount : ComputableInPolyTime count encode encUnary)
    (hj : ComputableInPolyTime j encode encUnary)
    (hx : ComputableInPolyTime x encode encBits)
    (hword : ComputableInPolyTime word encode encBits) :
    ComputableInPolyTime
      (fun a => Cslib.BitString.replaceRow (width a) (count a) (j a) (x a) (word a))
      encode encBits := by
  unfold Cslib.BitString.replaceRow
  apply ComputableInPolyTime.flatMapToBitsWithInput
    (ComputableInPolyTime.unary_range' hcount)
  have hfst := ComputableInPolyTime.fst encode encUnary
  have hsnd := ComputableInPolyTime.snd encode encUnary
  exact ComputableInPolyTime.ite_decide
    (ComputableInPolyTime.unary_eq' hsnd (hj.comp hfst))
    (hx.comp hfst)
    (ComputableInPolyTime.bitsRowWithInput (hwidth.comp hfst) hsnd (hword.comp hfst))

/-- Planted-coordinate escape reduction (`[HHRVW2020]`, Section 5.1.1, Lemma 5.3(ii), pp. 26–27):
sample an exact dyadic index `idx < dyadicSize (t n)`, plant the single-coordinate challenge
`xWord.take (inLen₀ n)` into row `idx` of a uniform `(t n * inLen₀ n)`-bit dummy word, run `A`,
and extract row `idx` of `A`'s output. -/
@[expose] noncomputable def repEscapeInverter (t inLen₀ : ℕ → ℕ)
    (A : ℕ → List Bool → ProbComp (List Bool)) (n : ℕ) (xWord : List Bool) :
    ProbComp (List Bool) := do
  let idx ← ProbComp.sampleDyadicIndex (t n)
  let dummy ← Cslib.BitString.sampleList (t n * inLen₀ n)
  let zWord := Cslib.BitString.replaceRow (inLen₀ n) (t n) idx (xWord.take (inLen₀ n)) dummy
  let raw ← A n zWord
  return Cslib.BitString.listRow (inLen₀ n) idx raw

/-- Plain uniform strict-PPT certificate for `repEscapeInverter`. -/
theorem isPPT_repEscapeInverter {t inLen₀ : ℕ → ℕ}
    {A : ℕ → List Bool → ProbComp (List Bool)}
    (ht : ComputableInPolyTime t encUnary encUnary)
    (hin₀ : ComputableInPolyTime inLen₀ encUnary encUnary)
    (hA : IsPPT encBits A) :
    IsPPT encBits (repEscapeInverter t inLen₀ A) := by
  let enc0 := encPair encUnary encBits
  let enc1 := encPair enc0 encUnary
  let enc2 := encPair enc1 encBits
  have h0_n := ComputableInPolyTime.fst encUnary encBits
  have h0_x := ComputableInPolyTime.snd encUnary encBits
  have h1_p := ComputableInPolyTime.fst enc0 encUnary
  have h1_idx := ComputableInPolyTime.snd enc0 encUnary
  have h1_n := h0_n.comp h1_p
  have h2_q := ComputableInPolyTime.fst enc1 encBits
  have h2_p := h1_p.comp h2_q
  have h2_n := h0_n.comp h2_p
  have h2_idx := h1_idx.comp h2_q
  have h2_in₀ := hin₀.comp h2_n
  have hzWord := computableInPolyTime_replaceRow h2_in₀ (ht.comp h2_n) h2_idx
    (ComputableInPolyTime.bitsTakeWithInput (h0_x.comp h2_p) h2_in₀)
    (ComputableInPolyTime.snd enc1 encBits)
  have h3_r := ComputableInPolyTime.fst enc2 encBits
  exact ((isPPTOn_sampleDyadicIndex (ht.comp h0_n)).bind_with
    (((ComputableInPolyTime.unary_mul' (ht.comp h1_n) (hin₀.comp h1_n)).sampleList).bind_with
      ((hA.on.preprocess (h2_n.prod hzWord)).bind_with
        (ComputableInPolyTime.isPPTOn
          (ComputableInPolyTime.bitsRowWithInput (h2_in₀.comp h3_r) (h2_idx.comp h3_r)
            (ComputableInPolyTime.snd enc2 encBits)))))).isPPT

private noncomputable def repEscapeIdxTerm (t inLen₀ : ℕ → ℕ)
    (evalWord₀ : ℕ → List Bool → List Bool)
    (L₀ : (n : ℕ) → BitString (inLen₀ n) → Finset (BitString (inLen₀ n)))
    (A : ℕ → List Bool → ProbComp (List Bool)) (n idx : ℕ) : ℝ :=
  let w₀ := inLen₀ n
  let rCount := t n
  (((do
    let xWord ← Cslib.BitString.uniformList w₀
    let dummy ← Cslib.BitString.uniformList (rCount * w₀)
    let zWord := Cslib.BitString.replaceRow w₀ rCount idx (xWord.take w₀) dummy
    let raw ← ProbComp.eval (A n zWord)
    let xRaw := Cslib.BitString.listRow w₀ idx raw
    return decide (xRaw.length = w₀ ∧ evalWord₀ n xRaw = evalWord₀ n xWord ∧
      Cslib.BitString.ofList w₀ xRaw ∉ L₀ n (Cslib.BitString.ofList w₀ xWord))) : PMF Bool)
    true).toReal

private theorem repEscapeInverter_succProbability_eq (t inLen₀ : ℕ → ℕ)
    (evalWord₀ : ℕ → List Bool → List Bool)
    (L₀ : (n : ℕ) → BitString (inLen₀ n) → Finset (BitString (inLen₀ n)))
    (A : ℕ → List Bool → ProbComp (List Bool)) (n : ℕ) :
    (Game.succProbability (ProbComp.eval
      (accessibleEscapeGame evalWord₀ inLen₀ L₀ (repEscapeInverter t inLen₀ A) n)) : ℝ) =
      ∑ k : Fin (dyadicSize (t n)),
        (dyadicSize (t n) : ℝ)⁻¹ * repEscapeIdxTerm t inLen₀ evalWord₀ L₀ A n k.val := by
  have heval :
      ProbComp.eval (accessibleEscapeGame evalWord₀ inLen₀ L₀
        (repEscapeInverter t inLen₀ A) n) =
      (PMF.uniformOfFintype (Fin (dyadicSize (t n)))).bind fun k =>
        (Cslib.BitString.uniformList (inLen₀ n)).bind fun xWord =>
          (Cslib.BitString.uniformList (t n * inLen₀ n)).bind fun dummy =>
            let zWord := Cslib.BitString.replaceRow (inLen₀ n) (t n) k.val
              (xWord.take (inLen₀ n)) dummy
            ProbComp.eval (A n zWord) >>= fun raw =>
              let xRaw := Cslib.BitString.listRow (inLen₀ n) k.val raw
              PMF.pure (decide (xRaw.length = inLen₀ n ∧ evalWord₀ n xRaw = evalWord₀ n xWord ∧
                Cslib.BitString.ofList (inLen₀ n) xRaw ∉
                  L₀ n (Cslib.BitString.ofList (inLen₀ n) xWord))) := by
    simp only [accessibleEscapeGame, repEscapeInverter, ProbComp.eval_bind,
      Cslib.BitString.eval_sampleList, ProbComp.eval_sampleDyadicIndex, ProbComp.eval_pure,
      PMF.monad_bind_eq_bind, PMF.bind_bind, PMF.bind_map, PMF.pure_bind, Function.comp_def]
    rw [PMF.bind_comm]
  simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal, heval, PMF.bind_apply_toReal,
    PMF.uniformOfFintype_apply, Fintype.card_fin, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    repEscapeIdxTerm, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]

/-- **`[HHRVW2020]`, Section 5.1.1, Lemma 5.3(ii) (pp. 26–27)**: for any adversary `A`, escaping
`repBitAccessibleSet (t n)` in `accessibleEscapeGame` occurs with probability at most
`dyadicSize (t n)` times the single-coordinate escape probability of
`repEscapeInverter t inLen₀ A`. -/
theorem repEscape_le_dyadicSize_mul_escape (t inLen₀ outLen₀ : ℕ → ℕ)
    (evalWord₀ : ℕ → List Bool → List Bool)
    (L₀ : (n : ℕ) → BitString (inLen₀ n) → Finset (BitString (inLen₀ n)))
    (A : ℕ → List Bool → ProbComp (List Bool)) (n : ℕ)
    (hlen : ∀ u : List Bool, u.length = inLen₀ n → (evalWord₀ n u).length = outLen₀ n) :
    (Game.succProbability (ProbComp.eval
      (accessibleEscapeGame
        (fun k => repEvalWord (t k) (inLen₀ k) (evalWord₀ k))
        (fun k => t k * inLen₀ k)
        (fun k => repBitAccessibleSet (t k) (inLen₀ k) (L₀ k)) A n)) : ℝ) ≤
      (dyadicSize (t n) : ℝ) *
        (Game.succProbability (ProbComp.eval
          (accessibleEscapeGame evalWord₀ inLen₀ L₀ (repEscapeInverter t inLen₀ A) n)) : ℝ) := by
  classical
  let w₀ := inLen₀ n
  let rCount := t n
  let repPred (zWord raw : List Bool) : Prop :=
    raw.length = rCount * w₀ ∧
      repEvalWord rCount w₀ (evalWord₀ n) raw = repEvalWord rCount w₀ (evalWord₀ n) zWord ∧
      Cslib.BitString.ofList (rCount * w₀) raw ∉
        repBitAccessibleSet rCount w₀ (L₀ n) (Cslib.BitString.ofList (rCount * w₀) zWord)
  let rowPred (idx : ℕ) (zWord raw : List Bool) : Prop :=
    let xWord := Cslib.BitString.listRow w₀ idx zWord
    let xRaw := Cslib.BitString.listRow w₀ idx raw
    xRaw.length = w₀ ∧ evalWord₀ n xRaw = evalWord₀ n xWord ∧
      Cslib.BitString.ofList w₀ xRaw ∉ L₀ n (Cslib.BitString.ofList w₀ xWord)
  have hrow_witness (zWord raw : List Bool) (hesc : repPred zWord raw) :
      ∃ j : Fin rCount, rowPred j.val zWord raw := by
    rcases hesc with ⟨_, heval_raw, hnot_acc⟩
    rw [mem_repBitAccessibleSet, not_forall] at hnot_acc
    obtain ⟨j, hj_not⟩ := hnot_acc
    refine ⟨j, Cslib.BitString.length_listRow w₀ j.val raw, ?_, ?_⟩
    · rw [← listRow_repEvalWord hlen raw j.isLt, ← listRow_repEvalWord hlen zWord j.isLt,
        heval_raw]
    · have hblk (u : List Bool) :
          Cslib.BitString.blocksEquiv (Cslib.BitString.ofList (rCount * w₀) u) j =
            Cslib.BitString.ofList w₀ (Cslib.BitString.listRow w₀ j.val u) := by
        rw [Cslib.BitString.listRow_eq_ofFn w₀ j u, Cslib.BitString.ofList_ofFn,
          Cslib.BitString.blocksEquiv_apply]
      rwa [← hblk zWord, ← hblk raw]
  let μ : PMF (List Bool × List Bool) :=
    (Cslib.BitString.uniformList (rCount * w₀)).bind fun zWord =>
      (ProbComp.eval (A n zWord)).map fun raw => (zWord, raw)
  have hle_ennreal :
      (μ.map (fun p => decide (repPred p.1 p.2))) true ≤
        ∑ j ∈ range rCount, (μ.map (fun p => decide (rowPred j p.1 p.2))) true := by
    refine (PMF.map_true_mono μ (F := fun p => (List.range rCount).any
      (fun j => decide (rowPred j p.1 p.2))) fun p _ h => ?_).trans
      (PMF.map_any_range_true_le_sum μ rCount fun j p => decide (rowPred j p.1 p.2))
    obtain ⟨j, hj⟩ := hrow_witness p.1 p.2 (of_decide_eq_true h)
    exact List.any_eq_true.mpr ⟨j.val, List.mem_range.mpr j.isLt, decide_eq_true hj⟩
  have hlhs_eq :
      ProbComp.eval
        (accessibleEscapeGame
          (fun k => repEvalWord (t k) (inLen₀ k) (evalWord₀ k))
          (fun k => t k * inLen₀ k)
          (fun k => repBitAccessibleSet (t k) (inLen₀ k) (L₀ k)) A n) =
        μ.map (fun p => decide (repPred p.1 p.2)) := by
    simp only [accessibleEscapeGame, μ, repPred, rCount, w₀, ProbComp.eval_bind,
      Cslib.BitString.eval_sampleList, ProbComp.eval_pure, PMF.map,
      PMF.bind_bind, PMF.pure_bind, Function.comp_def]
  have hj_eq (j : Fin rCount) :
      ((μ.map (fun p => decide (rowPred j.val p.1 p.2))) true).toReal =
        repEscapeIdxTerm t inLen₀ evalWord₀ L₀ A n j.val := by
    have hmap : μ.map (fun p => decide (rowPred j.val p.1 p.2)) =
        (Cslib.BitString.uniformList (rCount * w₀)).bind fun zWord =>
          ProbComp.eval (A n zWord) >>= fun raw =>
            PMF.pure (decide (rowPred j.val zWord raw)) := by
      simp only [μ, PMF.map, PMF.monad_bind_eq_bind, PMF.bind_bind, PMF.pure_bind,
        Function.comp_def]
    rw [hmap]
    dsimp only [repEscapeIdxTerm, rCount, w₀]
    simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
    conv_lhs => rw [← Cslib.BitString.uniformList_replaceRow w₀ rCount j, PMF.bind_bind]
    congr 2
    refine PMF.bind_congr_on_support _ _ _ fun xWord hx => ?_
    have hx_len : xWord.length = w₀ := Cslib.BitString.length_of_mem_support_uniformList hx
    have htake : xWord.take (inLen₀ n) = xWord := List.take_of_length_le hx_len.le
    rw [PMF.bind_map]
    refine PMF.bind_congr_on_support _ _ _ fun dummy _ => ?_
    simp only [Function.comp_def, htake, rowPred,
      Cslib.BitString.listRow_replaceRow hx_len dummy j.isLt, ↓reduceIte]
    rfl
  have hlhs_le :
      (Game.succProbability (ProbComp.eval
        (accessibleEscapeGame
          (fun k => repEvalWord (t k) (inLen₀ k) (evalWord₀ k))
          (fun k => t k * inLen₀ k)
          (fun k => repBitAccessibleSet (t k) (inLen₀ k) (L₀ k)) A n)) : ℝ) ≤
        ∑ j : Fin rCount, repEscapeIdxTerm t inLen₀ evalWord₀ L₀ A n j.val := by
    rw [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal, hlhs_eq]
    have htr := ENNReal.toReal_mono
      (ENNReal.sum_ne_top.mpr fun _ _ => PMF.apply_ne_top _ _) hle_ennreal
    rw [ENNReal.toReal_sum (fun _ _ => PMF.apply_ne_top _ _), ← Fin.sum_univ_eq_sum_range] at htr
    simpa only [hj_eq] using htr
  have hsub_sum :
      (∑ j : Fin rCount, repEscapeIdxTerm t inLen₀ evalWord₀ L₀ A n j.val) ≤
        ∑ k : Fin (dyadicSize rCount), repEscapeIdxTerm t inLen₀ evalWord₀ L₀ A n k.val := by
    rw [Fin.sum_univ_eq_sum_range, Fin.sum_univ_eq_sum_range]
    exact sum_le_sum_of_subset_of_nonneg (range_mono (lt_dyadicSize rCount).le)
      fun _ _ _ => ENNReal.toReal_nonneg
  have hdyad_pos : (0 : ℝ) < dyadicSize rCount := by exact_mod_cast dyadicSize_pos rCount
  calc
    (Game.succProbability (ProbComp.eval
      (accessibleEscapeGame
        (fun k => repEvalWord (t k) (inLen₀ k) (evalWord₀ k))
        (fun k => t k * inLen₀ k)
        (fun k => repBitAccessibleSet (t k) (inLen₀ k) (L₀ k)) A n)) : ℝ)
      ≤ ∑ k : Fin (dyadicSize rCount), repEscapeIdxTerm t inLen₀ evalWord₀ L₀ A n k.val :=
        hlhs_le.trans hsub_sum
    _ = (dyadicSize (t n) : ℝ) *
        (Game.succProbability (ProbComp.eval
          (accessibleEscapeGame evalWord₀ inLen₀ L₀ (repEscapeInverter t inLen₀ A) n)) : ℝ) := by
        rw [repEscapeInverter_succProbability_eq, ← mul_sum, ← mul_assoc,
          mul_inv_cancel₀ hdyad_pos.ne', one_mul]

end Cslib.Crypto
