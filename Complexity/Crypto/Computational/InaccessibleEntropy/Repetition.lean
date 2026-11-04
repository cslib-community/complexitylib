/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.UniformNat
public import Complexity.Crypto.Computational.InaccessibleEntropy.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import Complexity.Probability.BitString.List
import Complexity.Probability.Concentration
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF.Event
import Complexity.Probability.PMF.Map
import Complexity.Probability.PMF.Uniform
import Complexity.Probability.Product
import Complexity.Tactic.PPT

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
  congr 1
  funext i
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

private theorem logb_two_card_bitString (n₀ : ℕ) :
    Real.logb 2 (Fintype.card (BitString n₀)) ≤ (n₀ : ℝ) := by
  have hcard : Fintype.card (BitString n₀) = 2 ^ n₀ := by simp [BitString]
  rw [hcard, Nat.cast_pow, Nat.cast_ofNat,
    Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one]

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
    (logb_two_card_bitString inLen₀) hΔ
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
    (logb_two_card_bitString inLen₀) hΔ
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

@[local fun_prop]
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
  unfold repEscapeInverter
  ppt

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
  let m₀ := outLen₀ n
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
  -- Step 1: Every `repPred` escape witnesses `rowPred j.val` for some `j : Fin rCount`.
  have hrow_witness (zWord raw : List Bool) (hesc : repPred zWord raw) :
      ∃ j : Fin rCount, rowPred j.val zWord raw := by
    rcases hesc with ⟨hlen_raw, heval_raw, hnot_acc⟩
    rw [mem_repBitAccessibleSet, not_forall] at hnot_acc
    obtain ⟨j, hj_not⟩ := hnot_acc
    refine ⟨j, Cslib.BitString.length_listRow w₀ j.val raw, ?_, ?_⟩
    · rw [← listRow_repEvalWord hlen raw j.isLt, ← listRow_repEvalWord hlen zWord j.isLt,
        heval_raw]
    · have hblk_z : Cslib.BitString.blocksEquiv (Cslib.BitString.ofList (rCount * w₀) zWord) j =
          Cslib.BitString.ofList w₀ (Cslib.BitString.listRow w₀ j.val zWord) := by
        rw [Cslib.BitString.listRow_eq_ofFn w₀ j zWord, Cslib.BitString.ofList_ofFn,
          Cslib.BitString.blocksEquiv_apply]
      have hblk_raw : Cslib.BitString.blocksEquiv (Cslib.BitString.ofList (rCount * w₀) raw) j =
          Cslib.BitString.ofList w₀ (Cslib.BitString.listRow w₀ j.val raw) := by
        rw [Cslib.BitString.listRow_eq_ofFn w₀ j raw, Cslib.BitString.ofList_ofFn,
          Cslib.BitString.blocksEquiv_apply]
      rwa [← hblk_z, ← hblk_raw]
  -- Step 2: Union bound over `j : Fin rCount` at each `zWord`.
  have hpointwise (zWord : List Bool) :
      ((ProbComp.eval (A n zWord) >>= fun raw => PMF.pure (decide (repPred zWord raw)))
        true).toReal ≤
      ∑ j : Fin rCount,
        ((ProbComp.eval (A n zWord) >>= fun raw =>
          PMF.pure (decide (rowPred j.val zWord raw))) true).toReal := by
    let pA := ProbComp.eval (A n zWord)
    have hlhs : ((pA >>= fun raw => PMF.pure (decide (repPred zWord raw))) true).toReal =
        ∑' raw, (pA raw).toReal * (if repPred zWord raw then 1 else 0) := by
      rw [show (pA >>= _) = pA.bind _ from rfl, PMF.bind_apply_toReal_tsum]
      refine tsum_congr fun raw => congrArg ((pA raw).toReal * ·) ?_
      by_cases h : repPred zWord raw <;> simp [h]
    have hrhs : (∑ j : Fin rCount,
        ((pA >>= fun raw => PMF.pure (decide (rowPred j.val zWord raw))) true).toReal) =
        ∑' raw, ∑ j : Fin rCount,
          (pA raw).toReal * (if rowPred j.val zWord raw then 1 else 0) := by
      have hterm (j : Fin rCount) :
          ((pA >>= fun raw => PMF.pure (decide (rowPred j.val zWord raw))) true).toReal =
            ∑' raw, (pA raw).toReal * (if rowPred j.val zWord raw then 1 else 0) := by
        rw [show (pA >>= _) = pA.bind _ from rfl, PMF.bind_apply_toReal_tsum]
        refine tsum_congr fun raw => congrArg ((pA raw).toReal * ·) ?_
        by_cases h : rowPred j.val zWord raw <;> simp [h]
      simp_rw [hterm]
      refine (Summable.tsum_finsetSum fun j _ => ?_).symm
      refine Summable.of_nonneg_of_le (fun raw => by split_ifs <;> positivity)
        (fun raw => by split_ifs <;> simp [ENNReal.toReal_nonneg]) (PMF.summable_toReal pA)
    rw [hlhs, hrhs]
    refine Summable.tsum_le_tsum (fun raw => ?_)
      (Summable.of_nonneg_of_le (fun raw => by split_ifs <;> positivity)
        (fun raw => by split_ifs <;> simp [ENNReal.toReal_nonneg]) (PMF.summable_toReal pA))
      (summable_sum fun j _ => Summable.of_nonneg_of_le (fun raw => by split_ifs <;> positivity)
        (fun raw => by split_ifs <;> simp [ENNReal.toReal_nonneg]) (PMF.summable_toReal pA))
    by_cases hesc : repPred zWord raw
    · obtain ⟨j, hj⟩ := hrow_witness zWord raw hesc
      simp only [hesc, ↓reduceIte, mul_one]
      refine le_trans ?_ (single_le_sum (f := fun j : Fin rCount =>
          (pA raw).toReal * (if rowPred j.val zWord raw then 1 else 0))
        (fun _ _ => by split_ifs <;> positivity) (mem_univ j))
      simp [hj]
    · simp only [hesc, ↓reduceIte, mul_zero]
      exact sum_nonneg fun _ _ => by split_ifs <;> positivity
  -- Step 3: Average `hpointwise` over `zWord ← uniformList (rCount * w₀)`.
  have hlhs_le :
      (Game.succProbability (ProbComp.eval
        (accessibleEscapeGame
          (fun k => repEvalWord (t k) (inLen₀ k) (evalWord₀ k))
          (fun k => t k * inLen₀ k)
          (fun k => repBitAccessibleSet (t k) (inLen₀ k) (L₀ k)) A n)) : ℝ) ≤
      ∑ j : Fin rCount,
        (((Cslib.BitString.uniformList (rCount * w₀)).bind fun zWord =>
          ProbComp.eval (A n zWord) >>= fun raw =>
            PMF.pure (decide (rowPred j.val zWord raw))) true).toReal := by
    have heq : (Game.succProbability (ProbComp.eval
        (accessibleEscapeGame
          (fun k => repEvalWord (t k) (inLen₀ k) (evalWord₀ k))
          (fun k => t k * inLen₀ k)
          (fun k => repBitAccessibleSet (t k) (inLen₀ k) (L₀ k)) A n)) : ℝ) =
        ∑ z : BitString (rCount * w₀),
          ((PMF.uniformOfFintype (BitString (rCount * w₀))) z).toReal *
            ((ProbComp.eval (A n (List.ofFn z)) >>= fun raw =>
              PMF.pure (decide (repPred (List.ofFn z) raw))) true).toReal := by
      simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal, accessibleEscapeGame,
        ProbComp.eval_bind, Cslib.BitString.eval_sampleList, ProbComp.eval_pure,
        Cslib.BitString.uniformList, PMF.bind_map, PMF.bind_apply_toReal]
      rfl
    have hrhs_sum (j : Fin rCount) :
        (((Cslib.BitString.uniformList (rCount * w₀)).bind fun zWord =>
          ProbComp.eval (A n zWord) >>= fun raw =>
            PMF.pure (decide (rowPred j.val zWord raw))) true).toReal =
        ∑ z : BitString (rCount * w₀),
          ((PMF.uniformOfFintype (BitString (rCount * w₀))) z).toReal *
            ((ProbComp.eval (A n (List.ofFn z)) >>= fun raw =>
              PMF.pure (decide (rowPred j.val (List.ofFn z) raw))) true).toReal := by
      simp only [Cslib.BitString.uniformList, PMF.bind_map, PMF.bind_apply_toReal]
      rfl
    rw [heq]
    simp_rw [hrhs_sum]
    rw [← sum_comm]
    refine sum_le_sum fun z _ => ?_
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left (hpointwise (List.ofFn z)) ENNReal.toReal_nonneg
  -- Step 4: Match each `j : Fin rCount` term with the `idx = j.val` branch of `repEscapeInverter`.
  let idxTerm (idx : ℕ) : ℝ :=
    (((Cslib.BitString.uniformList w₀).bind fun xWord =>
      (Cslib.BitString.uniformList (rCount * w₀)).bind fun dummy =>
        let zWord := Cslib.BitString.replaceRow w₀ rCount idx (xWord.take w₀) dummy
        ProbComp.eval (A n zWord) >>= fun raw =>
          let xRaw := Cslib.BitString.listRow w₀ idx raw
          PMF.pure (decide (xRaw.length = w₀ ∧ evalWord₀ n xRaw = evalWord₀ n xWord ∧
            Cslib.BitString.ofList w₀ xRaw ∉ L₀ n (Cslib.BitString.ofList w₀ xWord))))
      true).toReal
  have hj_eq (j : Fin rCount) :
      (((Cslib.BitString.uniformList (rCount * w₀)).bind fun zWord =>
        ProbComp.eval (A n zWord) >>= fun raw =>
          PMF.pure (decide (rowPred j.val zWord raw))) true).toReal = idxTerm j.val := by
    dsimp only [idxTerm]
    conv_lhs => rw [← Cslib.BitString.uniformList_replaceRow w₀ rCount j, PMF.bind_bind]
    congr 2
    refine PMF.bind_congr_on_support _ _ _ fun xWord hx => ?_
    have hx_len : xWord.length = w₀ := Cslib.BitString.length_of_mem_support_uniformList hx
    rw [PMF.bind_map]
    refine PMF.bind_congr_on_support _ _ _ fun dummy _ => ?_
    simp only [Function.comp_def, List.take_of_length_le hx_len.le, rowPred,
      Cslib.BitString.listRow_replaceRow hx_len dummy j.isLt, ↓reduceIte]
  have hinv_eq :
      (Game.succProbability (ProbComp.eval
        (accessibleEscapeGame evalWord₀ inLen₀ L₀ (repEscapeInverter t inLen₀ A) n)) : ℝ) =
      ∑ k : Fin (dyadicSize rCount),
        (dyadicSize rCount : ℝ)⁻¹ * idxTerm k.val := by
    have heval :
        ProbComp.eval (accessibleEscapeGame evalWord₀ inLen₀ L₀
          (repEscapeInverter t inLen₀ A) n) =
        (PMF.uniformOfFintype (Fin (dyadicSize rCount))).bind fun k =>
          (Cslib.BitString.uniformList w₀).bind fun xWord =>
            (Cslib.BitString.uniformList (rCount * w₀)).bind fun dummy =>
              let zWord := Cslib.BitString.replaceRow w₀ rCount k.val (xWord.take w₀) dummy
              ProbComp.eval (A n zWord) >>= fun raw =>
                let xRaw := Cslib.BitString.listRow w₀ k.val raw
                PMF.pure (decide (xRaw.length = w₀ ∧ evalWord₀ n xRaw = evalWord₀ n xWord ∧
                  Cslib.BitString.ofList w₀ xRaw ∉ L₀ n (Cslib.BitString.ofList w₀ xWord))) := by
      simp only [accessibleEscapeGame, repEscapeInverter, ProbComp.eval_bind,
        Cslib.BitString.eval_sampleList, ProbComp.eval_sampleDyadicIndex, ProbComp.eval_pure,
        PMF.monad_bind_eq_bind, PMF.bind_bind, PMF.bind_map, PMF.pure_bind, Function.comp_def]
      rw [PMF.bind_comm]
    simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal, heval, PMF.bind_apply_toReal,
      PMF.uniformOfFintype_apply, Fintype.card_fin, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    rfl
  have hsub_sum :
      (∑ j : Fin rCount, idxTerm j.val) ≤ ∑ k : Fin (dyadicSize rCount), idxTerm k.val := by
    let emb : Fin rCount ↪ Fin (dyadicSize rCount) := Fin.castLEEmb (lt_dyadicSize rCount).le
    have hmap : (∑ j : Fin rCount, idxTerm j.val) =
        ∑ k ∈ univ.map emb, idxTerm k.val := by
      rw [sum_map]
      rfl
    rw [hmap]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => ENNReal.toReal_nonneg
  have hdyad_pos : (0 : ℝ) < dyadicSize rCount := by exact_mod_cast dyadicSize_pos rCount
  calc
    (Game.succProbability (ProbComp.eval
      (accessibleEscapeGame
        (fun k => repEvalWord (t k) (inLen₀ k) (evalWord₀ k))
        (fun k => t k * inLen₀ k)
        (fun k => repBitAccessibleSet (t k) (inLen₀ k) (L₀ k)) A n)) : ℝ)
      ≤ ∑ j : Fin rCount, idxTerm j.val := by
        simpa only [hj_eq] using hlhs_le
    _ ≤ ∑ k : Fin (dyadicSize rCount), idxTerm k.val := hsub_sum
    _ = (dyadicSize rCount : ℝ) *
        ∑ k : Fin (dyadicSize rCount), (dyadicSize rCount : ℝ)⁻¹ * idxTerm k.val := by
        rw [← mul_sum, ← mul_assoc, mul_inv_cancel₀ hdyad_pos.ne', one_mul]
    _ = (dyadicSize (t n) : ℝ) *
        (Game.succProbability (ProbComp.eval
          (accessibleEscapeGame evalWord₀ inLen₀ L₀ (repEscapeInverter t inLen₀ A) n)) : ℝ) := by
        rw [hinv_eq]

end Cslib.Crypto
