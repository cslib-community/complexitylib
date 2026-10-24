/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.WeightedThreshold.CapacityCircuit
import Complexity.Foundations.Data.Finset.Quantile

/-!
# Median-cut and coordinate-split restrictions for weighted threshold programs

This module proves the coordinate-split and median-cut rectangle-extraction lemmas for weighted
threshold programs. Given a coordinate split `U : Finset (Fin n)` and subsets `A ⊆ U` and `B ⊆ Uᶜ`
of inputs fixed to `false`, we restrict the remaining coordinates `P ⊆ (U → Bool)` and
`Q ⊆ (↥Uᶜ → Bool)` gate by gate in topological order so that every gate of the program becomes
constant on the induced combinatorial rectangle:

* If a gate's active input support meets both `U \ A` and `Uᶜ \ B`, we cut both `P` and `Q` at
  the medians of their half-sums (`exists_median`), halving each side at most once.
* If a gate's active input support meets only one side, its threshold condition depends only on
  that side, so we halve only that side.
* If a gate's input support is contained in `A ∪ B`, its weighted input sum vanishes on `P × Q`,
  and neither side is shrunk.

Specializing `A = ∅` and `B = ∅` gives the general median-cut rectangle lemma
(`exists_rectangle_of_cut`), the cut theorem (`lt_of_split`), and the balanced cut-weight bound
`n ≤ 2 * ((inputGates p).card + k)` (`le_two_mul_add`). Specializing to gates that do not cross
`U` gives the coordinate-split restriction (`exists_rectangle_of_split`).

## Main definitions

* `Cslib.Circuits.Boolean.WeightedThreshold.inputSupport`: the set of original inputs with nonzero
  aggregated weight at a gate.
* `Cslib.Circuits.Boolean.WeightedThreshold.glue`: combines partial assignments on `U` and `Uᶜ`
  into a full input `Fin n → Bool`.

## Main results

* `Cslib.Circuits.Boolean.WeightedThreshold.exists_median`: every finite set of points with a
  real-valued weight function has a median threshold splitting at least half the points to each
  side.
* `Cslib.Circuits.Boolean.WeightedThreshold.exists_rectangle_of_cut_with_fixed`: unified
  median-cut and coordinate-fixing rectangle extraction.
* `Cslib.Circuits.Boolean.WeightedThreshold.exists_rectangle_of_cut`,
  `Cslib.Circuits.Boolean.WeightedThreshold.exists_rectangle_of_split`: median-cut and
  unsplit-gate rectangle extraction.
* `Cslib.Circuits.Boolean.WeightedThreshold.lt_of_split`,
  `Cslib.Circuits.Boolean.WeightedThreshold.circuit_lt_of_split`: the cut theorem.
* `Cslib.Circuits.Boolean.WeightedThreshold.le_two_mul_add`,
  `Cslib.Circuits.Boolean.WeightedThreshold.circuit_le_two_mul_add`: the balanced cut bound.

## References

* [S. Schlesinger, *Algebraic circuit formalizations in Complexitylib*,
  Threshold/Internal/Cut and Split][Schlesinger2026Algebraic]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.WeightedThreshold

open Finset

variable {n g : ℕ}

/-! ### Aggregated input support -/

/-- The original inputs with nonzero aggregated coefficient at `gate`. -/
noncomputable def inputSupport (p : Program signature n g) (gate : Fin g) : Finset (Fin n) :=
  univ.filter fun i => inputWeight p gate i ≠ 0

/-- An input `i` belongs to `inputSupport p gate` if and only if `inputWeight p gate i ≠ 0`. -/
@[simp]
theorem mem_inputSupport (p : Program signature n g) (gate : Fin g) (i : Fin n) :
    i ∈ inputSupport p gate ↔ inputWeight p gate i ≠ 0 := by
  classical
  simp [inputSupport]

/-- A gate belongs to `inputGates p` iff its aggregated input support is nonempty. -/
theorem mem_inputGates_iff_inputSupport_nonempty (p : Program signature n g) (gate : Fin g) :
    gate ∈ inputGates p ↔ (inputSupport p gate).Nonempty := by
  simp [Finset.Nonempty]

/-- A gate's aggregated input support is nonempty iff it belongs to `inputGates p`. -/
theorem inputSupport_ne_empty_iff (p : Program signature n g) (gate : Fin g) :
    inputSupport p gate ≠ ∅ ↔ gate ∈ inputGates p := by
  rw [← nonempty_iff_ne_empty, mem_inputGates_iff_inputSupport_nonempty]

/-! ### Gluing across a coordinate split -/

/-- Combine partial assignments on `U` and `Uᶜ` into a total input on `Fin n`. -/
def glue (U : Finset (Fin n)) (p : U → Bool) (q : ↥Uᶜ → Bool) : Fin n → Bool :=
  fun i => if h : i ∈ U then p ⟨i, h⟩ else q ⟨i, mem_compl.mpr h⟩

/-- If `f` is monochromatic on the rectangle `glue U '' (P × Q)` and two-sided
`K`-rectangle-free, then `P.card < K` or `Q.card < K`. -/
theorem card_lt_or_card_lt_of_rectangleFree {f : Cslib.BooleanFunction n} {K : ℕ}
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K)
    (U : Finset (Fin n)) (P : Finset (U → Bool)) (Q : Finset (↥Uᶜ → Bool)) (b : Bool)
    (hconst : ∀ p ∈ P, ∀ q ∈ Q, f (glue U p q) = b) :
    P.card < K ∨ Q.card < K := by
  let emb : (↥Uᶜ → Bool) ↪ (↥(↑U : Set (Fin n))ᶜ → Bool) :=
    ⟨fun q i => q ⟨i.1, mem_compl.mpr i.2⟩, fun q₁ q₂ h =>
      funext fun i => congrFun h ⟨i.1, mem_compl.mp i.2⟩⟩
  have hrect : Frontier.rectangle (↑U : Set (Fin n)) (↑P : Set (U → Bool))
      (↑(Q.map emb) : Set (↥(↑U : Set (Fin n))ᶜ → Bool)) ⊆ {x | f x = b} := by
    intro x hx
    have hxP : (↑U : Set (Fin n)).domRestrict x ∈ P := hx.1
    have hxQ : (↑U : Set (Fin n))ᶜ.domRestrict x ∈ Q.map emb := hx.2
    rcases mem_map.mp hxQ with ⟨q, hq, hqeq⟩
    have hglue : glue U ((↑U : Set (Fin n)).domRestrict x) q = x := by
      funext i
      by_cases hi : i ∈ U
      · simp [glue, hi]
      · have hqi : q ⟨i, mem_compl.mpr hi⟩ = x i := congrFun hqeq ⟨i, hi⟩
        simpa [glue, hi] using hqi
    change f x = b
    rw [← hglue]
    exact hconst _ hxP q hq
  have hncard := (hf b).ncard_lt_or _ _ _ hrect
  rwa [Set.ncard_coe_finset, Set.ncard_coe_finset, card_map] at hncard

/-! ### Weighted sums and gluing -/

private theorem weightedSum_glue (U : Finset (Fin n)) (w : Fin n → ℝ)
    (p : U → Bool) (q : ↥Uᶜ → Bool) :
    weightedSum w (glue U p q) =
      weightedSum w (glue U p fun _ => false) +
      weightedSum w (glue U (fun _ => false) q) := by
  simp only [weightedSum, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  by_cases hi : i ∈ U <;> simp [glue, hi]

private theorem weightedSum_eq_zero_of_zero (w : Fin n → ℝ) (x : Fin n → Bool)
    (h : ∀ i, w i ≠ 0 → x i = false) :
    weightedSum w x = 0 := by
  refine sum_eq_zero fun i _ => ?_
  by_cases hw : w i = 0
  · simp [hw]
  · simp [h i hw]

private theorem eval_gate_eq_of_lt (prog : Program signature n g)
    (x : Fin n → Bool) (v : Fin g → Bool) (j : Fin g)
    (hv : ∀ k : Fin g, k < j → prog.eval interpretation x k = v k) :
    prog.eval interpretation x j =
      decide ((prog.lines j).op.threshold ≤
        weightedSum (inputWeight prog j) x +
          ∑ k : Fin g, if k < j then gateWeight prog j k * (v k).toNat else 0) := by
  rw [eval_gate_eq]
  congr 2
  rw [weightedSum]
  congr 1
  refine sum_congr rfl fun k _ => ?_
  by_cases hk : k < j
  · simp [hk, hv k hk]
  · simp [hk, gateWeight_eq_zero_of_le prog j k (le_of_not_gt hk)]

/-! ### Medians and halving -/

/-- Every finite set `P` equipped with a real-valued function `f` has a threshold `μ` such that
at least half of `P` satisfies `f x ≤ μ` and at least half satisfies `μ ≤ f x`. -/
theorem exists_median {α : Type*} (P : Finset α) (f : α → ℝ) :
    ∃ μ : ℝ, P.card ≤ 2 * (P.filter fun p => f p ≤ μ).card ∧
      P.card ≤ 2 * (P.filter fun p => μ ≤ f p).card := by
  rcases P.eq_empty_or_nonempty with rfl | hP
  · exact ⟨0, by simp⟩
  · obtain ⟨p, _, hlo, hhi⟩ := P.exists_median hP f
    exact ⟨f p, hlo, hhi⟩

private theorem exists_half {α : Type*} (P : Finset α) (f : α → Bool) :
    ∃ b : Bool, P.card ≤ 2 * (P.filter fun p => f p = b).card := by
  have h := card_filter_add_card_filter_not (s := P) (fun p => f p = true)
  have hf : (P.filter fun p => ¬ f p = true) = P.filter fun p => f p = false := by
    ext p
    simp
  rw [hf] at h
  by_contra hno
  push Not at hno
  have h1 := hno true
  have h2 := hno false
  omega

private theorem half_step {a b c : ℕ} (hab : a ≤ b * 2 ^ c) {b' : ℕ} (hb : b ≤ 2 * b') :
    a ≤ b' * 2 ^ (c + 1) := by
  calc
    a ≤ b * 2 ^ c := hab
    _ ≤ (2 * b') * 2 ^ c := Nat.mul_le_mul_right _ hb
    _ = b' * 2 ^ (c + 1) := by ring

/-- Convert a multiplicative power-of-two bound `2 ^ m ≤ card * 2 ^ t` with `t + k ≤ m` and
`K ≤ 2 ^ k` into `K ≤ card`. -/
theorem le_card_of_pow_le {m card t k K : ℕ} (hpow : 2 ^ m ≤ card * 2 ^ t)
    (hm : t + k ≤ m) (hK : K ≤ 2 ^ k) : K ≤ card := by
  have h1 : 2 ^ k * 2 ^ t ≤ card * 2 ^ t := by
    calc
      2 ^ k * 2 ^ t = 2 ^ (t + k) := by rw [← pow_add, add_comm]
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) hm
      _ ≤ card * 2 ^ t := hpow
  exact le_trans hK (Nat.le_of_mul_le_mul_right h1 (by positivity))

/-! ### Initial subcubes with fixed coordinates -/

private theorem exists_initial (S A : Finset (Fin n)) (hA : A ⊆ S) :
    ∃ P : Finset (S → Bool),
      2 ^ (S.card - A.card) ≤ P.card ∧
      ∀ p ∈ P, ∀ i : S, (i : Fin n) ∈ A → p i = false := by
  classical
  let ext : (↥(S \ A) → Bool) → (S → Bool) := fun f i =>
    if h : (i : Fin n) ∈ S \ A then f ⟨i, h⟩ else false
  have hinj : Function.Injective ext := by
    intro f f' hff
    funext i
    have := congrFun hff ⟨i.1, (mem_sdiff.mp i.2).1⟩
    simp only [ext] at this
    rwa [dite_eq_left i.2, dite_eq_left i.2] at this
  refine ⟨univ.image ext, ?_, ?_⟩
  · rw [card_image_of_injective _ hinj, card_univ, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_coe, card_sdiff_of_subset hA]
  · intro p hp i hi
    obtain ⟨f, -, rfl⟩ := mem_image.mp hp
    simp [ext, hi]

/-! ### Unified median-cut and coordinate-fixing invariant -/

private noncomputable def touchBelow (prog : Program signature n g)
    (S D : Finset (Fin n)) (m : ℕ) : ℕ :=
  (univ.filter fun j : Fin g => j.val < m ∧ ¬ inputSupport prog j ∩ S ⊆ D).card

private theorem touchBelow_zero (prog : Program signature n g) (S D : Finset (Fin n)) :
    touchBelow prog S D 0 = 0 := by
  classical
  rw [touchBelow, card_eq_zero, filter_eq_empty_iff]
  intro j _
  simp

private theorem touchBelow_top (prog : Program signature n g) (S D : Finset (Fin n)) :
    touchBelow prog S D g =
      (univ.filter fun j : Fin g => ¬ inputSupport prog j ∩ S ⊆ D).card := by
  classical
  unfold touchBelow
  congr 1
  ext j
  simp

private theorem touchBelow_succ (prog : Program signature n g) (S D : Finset (Fin n))
    {m : ℕ} (j₀ : Fin g) (hj₀ : j₀.val = m) :
    touchBelow prog S D (m + 1) =
      touchBelow prog S D m + (if ¬ inputSupport prog j₀ ∩ S ⊆ D then 1 else 0) := by
  classical
  unfold touchBelow
  by_cases h : ¬ inputSupport prog j₀ ∩ S ⊆ D
  · rw [ite_eq_left h]
    have hins : (univ.filter fun j : Fin g => j.val < m + 1 ∧ ¬ inputSupport prog j ∩ S ⊆ D) =
        insert j₀ (univ.filter fun j : Fin g => j.val < m ∧ ¬ inputSupport prog j ∩ S ⊆ D) := by
      ext j
      simp only [mem_filter, mem_univ, true_and, mem_insert]
      constructor
      · rintro ⟨hjm, hjS⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hjm with hlt | heq
        · exact Or.inr ⟨hlt, hjS⟩
        · exact Or.inl (Fin.ext (heq.trans hj₀.symm))
      · rintro (rfl | ⟨hlt, hjS⟩)
        · exact ⟨by omega, h⟩
        · exact ⟨by omega, hjS⟩
    have hnotmem : j₀ ∉ univ.filter
        fun j : Fin g => j.val < m ∧ ¬ inputSupport prog j ∩ S ⊆ D := by
      simp [hj₀]
    rw [hins, card_insert_of_notMem hnotmem]
  · rw [ite_eq_right h, add_zero]
    congr 1
    ext j
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hjm, hjS⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hjm with hlt | heq
      · exact ⟨hlt, hjS⟩
      · have : j = j₀ := Fin.ext (heq.trans hj₀.symm)
        subst this
        exact (h hjS).elim
    · rintro ⟨hlt, hjS⟩
      exact ⟨by omega, hjS⟩

private def CutInv (prog : Program signature n g) (U A B : Finset (Fin n)) (m : ℕ) : Prop :=
  ∃ (P : Finset (U → Bool)) (Q : Finset (↥Uᶜ → Bool)) (v : Fin g → Bool),
    (∀ p ∈ P, ∀ i : U, (i : Fin n) ∈ A → p i = false) ∧
    (∀ q ∈ Q, ∀ i : ↥Uᶜ, (i : Fin n) ∈ B → q i = false) ∧
    (∀ p ∈ P, ∀ q ∈ Q, ∀ k : Fin g, k.val < m →
      prog.eval interpretation (glue U p q) k = v k) ∧
    2 ^ (U.card - A.card) ≤ P.card * 2 ^ touchBelow prog U A m ∧
    2 ^ (Uᶜ.card - B.card) ≤ Q.card * 2 ^ touchBelow prog Uᶜ B m

private theorem cutInv_zero (prog : Program signature n g) {U A B : Finset (Fin n)}
    (hA : A ⊆ U) (hB : B ⊆ Uᶜ) :
    CutInv prog U A B 0 := by
  obtain ⟨P, hPcard, hPzero⟩ := exists_initial U A hA
  obtain ⟨Q, hQcard, hQzero⟩ := exists_initial Uᶜ B hB
  refine ⟨P, Q, fun _ => false, hPzero, hQzero,
    fun _ _ _ _ k hk => absurd hk (Nat.not_lt_zero _),
    by simpa [touchBelow_zero] using hPcard,
    by simpa [touchBelow_zero] using hQcard⟩

private theorem cutInv_succ (prog : Program signature n g) (U A B : Finset (Fin n))
    {m : ℕ} (hm : m < g) (h : CutInv prog U A B m) :
    CutInv prog U A B (m + 1) := by
  classical
  obtain ⟨P, Q, v, hPzero, hQzero, hv, hP, hQ⟩ := h
  set j₀ : Fin g := ⟨m, hm⟩
  set c : ℝ :=
    (∑ k : Fin g, if k < j₀ then gateWeight prog j₀ k * (v k).toNat else 0) -
      (prog.lines j₀).op.threshold
  set α : (U → Bool) → ℝ :=
    fun p => weightedSum (inputWeight prog j₀) (glue U p fun _ => false)
  set β : (↥Uᶜ → Bool) → ℝ :=
    fun q => weightedSum (inputWeight prog j₀) (glue U (fun _ => false) q)
  have hgate : ∀ p ∈ P, ∀ q ∈ Q,
      prog.eval interpretation (glue U p q) j₀ = decide (0 ≤ α p + β q + c) := by
    intro p hp q hq
    rw [eval_gate_eq_of_lt prog (glue U p q) v j₀
      (fun k hk => hv p hp q hq k (Fin.lt_def.mp hk)),
      weightedSum_glue]
    apply decide_eq_decide.mpr
    dsimp only [α, β, c]
    constructor <;> intro <;> linarith
  have htU := touchBelow_succ prog U A j₀ rfl
  have htV := touchBelow_succ prog Uᶜ B j₀ rfl
  have hext : ∀ (b : Bool) (P' : Finset (U → Bool)) (Q' : Finset (↥Uᶜ → Bool)),
      P' ⊆ P → Q' ⊆ Q →
      (∀ p ∈ P', ∀ q ∈ Q', prog.eval interpretation (glue U p q) j₀ = b) →
      ∀ p ∈ P', ∀ q ∈ Q', ∀ k : Fin g, k.val < m + 1 →
        prog.eval interpretation (glue U p q) k = Function.update v j₀ b k := by
    intro b P' Q' hP' hQ' hb p hp q hq k hk
    by_cases hkj : k = j₀
    · subst hkj
      rw [Function.update_self]
      exact hb p hp q hq
    · rw [Function.update_of_ne hkj]
      have hkm : k.val ≠ m := fun h => hkj (Fin.ext h)
      exact hv p (hP' hp) q (hQ' hq) k (by omega)
  have hαzero : ¬ (¬ inputSupport prog j₀ ∩ U ⊆ A) → ∀ p ∈ P, α p = 0 := by
    intro hU p hp
    rw [not_not] at hU
    refine weightedSum_eq_zero_of_zero _ _ fun i hi => ?_
    by_cases hiU : i ∈ U
    · have hiA : i ∈ A := hU (mem_inter.mpr ⟨(mem_inputSupport prog j₀ i).mpr hi, hiU⟩)
      simpa [glue, hiU] using hPzero p hp ⟨i, hiU⟩ hiA
    · simp [glue, hiU]
  have hβzero : ¬ (¬ inputSupport prog j₀ ∩ Uᶜ ⊆ B) → ∀ q ∈ Q, β q = 0 := by
    intro hV q hq
    rw [not_not] at hV
    refine weightedSum_eq_zero_of_zero _ _ fun i hi => ?_
    by_cases hiU : i ∈ U
    · simp [glue, hiU]
    · have hiUc : i ∈ Uᶜ := mem_compl.mpr hiU
      have hiB : i ∈ B := hV (mem_inter.mpr ⟨(mem_inputSupport prog j₀ i).mpr hi, hiUc⟩)
      simpa [glue, hiU] using hQzero q hq ⟨i, hiUc⟩ hiB
  by_cases hU : ¬ inputSupport prog j₀ ∩ U ⊆ A <;>
    by_cases hV : ¬ inputSupport prog j₀ ∩ Uᶜ ⊆ B
  · rw [ite_eq_left hU] at htU
    rw [ite_eq_left hV] at htV
    obtain ⟨μP, hPlo, hPhi⟩ := exists_median P α
    obtain ⟨μQ, hQlo, hQhi⟩ := exists_median Q β
    by_cases hμ : 0 ≤ μP + μQ + c
    · refine ⟨P.filter fun p => μP ≤ α p, Q.filter fun q => μQ ≤ β q, Function.update v j₀ true,
        fun p hp => hPzero p (mem_filter.mp hp).1,
        fun q hq => hQzero q (mem_filter.mp hq).1,
        hext true _ _ (filter_subset _ _) (filter_subset _ _) fun p hp q hq => ?_,
        by rw [htU]; exact half_step hP hPhi,
        by rw [htV]; exact half_step hQ hQhi⟩
      obtain ⟨hp, hpμ⟩ := mem_filter.mp hp
      obtain ⟨hq, hqμ⟩ := mem_filter.mp hq
      rw [hgate p hp q hq, decide_eq_true_eq]
      linarith
    · refine ⟨P.filter fun p => α p ≤ μP, Q.filter fun q => β q ≤ μQ, Function.update v j₀ false,
        fun p hp => hPzero p (mem_filter.mp hp).1,
        fun q hq => hQzero q (mem_filter.mp hq).1,
        hext false _ _ (filter_subset _ _) (filter_subset _ _) fun p hp q hq => ?_,
        by rw [htU]; exact half_step hP hPlo,
        by rw [htV]; exact half_step hQ hQlo⟩
      obtain ⟨hp, hpμ⟩ := mem_filter.mp hp
      obtain ⟨hq, hqμ⟩ := mem_filter.mp hq
      rw [hgate p hp q hq, decide_eq_false_iff_not]
      intro h0
      exact hμ (by linarith)
  · rw [ite_eq_left hU] at htU
    rw [ite_eq_right hV, add_zero] at htV
    obtain ⟨b, hb⟩ := exists_half P fun p => decide (0 ≤ α p + c)
    refine ⟨P.filter fun p => decide (0 ≤ α p + c) = b, Q, Function.update v j₀ b,
      fun p hp => hPzero p (mem_filter.mp hp).1, hQzero,
      hext b _ Q (filter_subset _ _) subset_rfl fun p hp q hq => ?_,
      by rw [htU]; exact half_step hP hb, by rwa [htV]⟩
    obtain ⟨hp, hpb⟩ := mem_filter.mp hp
    rw [hgate p hp q hq, hβzero hV q hq, add_zero]
    exact hpb
  · rw [ite_eq_right hU, add_zero] at htU
    rw [ite_eq_left hV] at htV
    obtain ⟨b, hb⟩ := exists_half Q fun q => decide (0 ≤ β q + c)
    refine ⟨P, Q.filter fun q => decide (0 ≤ β q + c) = b, Function.update v j₀ b,
      hPzero, fun q hq => hQzero q (mem_filter.mp hq).1,
      hext b P _ subset_rfl (filter_subset _ _) fun p hp q hq => ?_,
      by rwa [htU], by rw [htV]; exact half_step hQ hb⟩
    obtain ⟨hq, hqb⟩ := mem_filter.mp hq
    rw [hgate p hp q hq, hαzero hU p hp, zero_add]
    exact hqb
  · rw [ite_eq_right hU, add_zero] at htU
    rw [ite_eq_right hV, add_zero] at htV
    refine ⟨P, Q, Function.update v j₀ (decide (0 ≤ c)), hPzero, hQzero,
      hext _ P Q subset_rfl subset_rfl fun p hp q hq => ?_,
      by rwa [htU], by rwa [htV]⟩
    rw [hgate p hp q hq, hαzero hU p hp, hβzero hV q hq, zero_add, zero_add]

private theorem cutInv_all (prog : Program signature n g) {U A B : Finset (Fin n)}
    (hA : A ⊆ U) (hB : B ⊆ Uᶜ) :
    ∀ m ≤ g, CutInv prog U A B m := by
  intro m hm
  induction m with
  | zero => exact cutInv_zero prog hA hB
  | succ m ih => exact cutInv_succ prog U A B (by omega) (ih (by omega))

/-! ### Rectangle extraction and cut bounds -/

/-- **Unified median-cut and coordinate-fixing rectangle extraction.** For any split `U` and
sets `A ⊆ U` and `B ⊆ Uᶜ` of coordinates fixed to `false` on `U` and `Uᶜ`, there is a
combinatorial rectangle `P × Q` on which the entire gate-evaluation vector `p.eval interpretation`
is constant, with `P` losing at most `|A|` coordinates initially and one factor of `2` per gate
whose support on `U` is not contained in `A` (and symmetrically for `Q`). -/
theorem exists_rectangle_of_cut_with_fixed (p : Program signature n g)
    (U A B : Finset (Fin n)) (hA : A ⊆ U) (hB : B ⊆ Uᶜ) :
    ∃ (P : Finset (U → Bool)) (Q : Finset (↥Uᶜ → Bool)) (v : Fin g → Bool),
      (∀ x ∈ P, ∀ y ∈ Q, p.eval interpretation (glue U x y) = v) ∧
      2 ^ (U.card - A.card) ≤
        P.card * 2 ^ (univ.filter fun j => ¬ inputSupport p j ∩ U ⊆ A).card ∧
      2 ^ (Uᶜ.card - B.card) ≤
        Q.card * 2 ^ (univ.filter fun j => ¬ inputSupport p j ∩ Uᶜ ⊆ B).card := by
  obtain ⟨P, Q, v, _, _, hv, hP, hQ⟩ := cutInv_all p hA hB g le_rfl
  rw [touchBelow_top] at hP hQ
  refine ⟨P, Q, v, fun x hx y hy => funext fun k => hv x hx y hy k k.isLt, hP, hQ⟩

/-- **The cut lemma.** For every coordinate split `U`, there is a rectangle `P × Q` on which
`f` is constant, with `2 ^ |U| ≤ |P| · 2 ^ #{j : inputSupport p j ∩ U ≠ ∅}` and symmetrically
for `Uᶜ`. -/
theorem exists_rectangle_of_cut (p : Program signature n g)
    (readout : (Fin g → Bool) → Bool) {f : Cslib.BooleanFunction n}
    (hreadout : ∀ x, readout (p.eval interpretation x) = f x) (U : Finset (Fin n)) :
    ∃ (P : Finset (U → Bool)) (Q : Finset (↥Uᶜ → Bool)) (b : Bool),
      (∀ x ∈ P, ∀ y ∈ Q, f (glue U x y) = b) ∧
      2 ^ U.card ≤ P.card * 2 ^ (univ.filter fun j => (inputSupport p j ∩ U).Nonempty).card ∧
      2 ^ Uᶜ.card ≤ Q.card * 2 ^ (univ.filter fun j => (inputSupport p j ∩ Uᶜ).Nonempty).card := by
  obtain ⟨P, Q, v, hv, hP, hQ⟩ :=
    exists_rectangle_of_cut_with_fixed p U ∅ ∅ (empty_subset U) (empty_subset Uᶜ)
  refine ⟨P, Q, readout v, fun x hx y hy => ?_, ?_, ?_⟩
  · rw [← hreadout, hv x hx y hy]
  · simpa [subset_empty, nonempty_iff_ne_empty] using hP
  · simpa [subset_empty, nonempty_iff_ne_empty] using hQ

/-- **Coordinate-split rectangle extraction.** When every gate's input support is contained in
`U` or in `Uᶜ`, fixing `A ⊆ U` and `B ⊆ Uᶜ` to `false` yields a monochromatic rectangle `P × Q`
that loses at most one factor of `2` per gate on `U` with support not contained in `A` (and
symmetrically for `Uᶜ` and `B`). -/
theorem exists_rectangle_of_split (p : Program signature n g)
    (readout : (Fin g → Bool) → Bool) {f : Cslib.BooleanFunction n}
    (hreadout : ∀ x, readout (p.eval interpretation x) = f x)
    (U A B : Finset (Fin n)) (hA : A ⊆ U) (hB : B ⊆ Uᶜ)
    (hsplit : ∀ j, inputSupport p j ⊆ U ∨ inputSupport p j ⊆ Uᶜ) :
    ∃ (P : Finset (U → Bool)) (Q : Finset (↥Uᶜ → Bool)) (b : Bool),
      (∀ x ∈ P, ∀ y ∈ Q, f (glue U x y) = b) ∧
      2 ^ (U.card - A.card) ≤
        P.card * 2 ^ (univ.filter fun j =>
          inputSupport p j ⊆ U ∧ ¬ inputSupport p j ⊆ A).card ∧
      2 ^ (Uᶜ.card - B.card) ≤
        Q.card * 2 ^ (univ.filter fun j =>
          inputSupport p j ⊆ Uᶜ ∧ ¬ inputSupport p j ⊆ B).card := by
  classical
  obtain ⟨P, Q, v, hv, hP, hQ⟩ := exists_rectangle_of_cut_with_fixed p U A B hA hB
  have hfilterU : (univ.filter fun j => ¬ inputSupport p j ∩ U ⊆ A) =
      univ.filter fun j => inputSupport p j ⊆ U ∧ ¬ inputSupport p j ⊆ A := by
    ext j
    simp only [mem_filter, mem_univ, true_and]
    rcases hsplit j with hjU | hjUc
    · rw [inter_eq_left.mpr hjU]
      exact ⟨fun h => ⟨hjU, h⟩, fun h => h.2⟩
    · have hemp : inputSupport p j ∩ U = ∅ :=
        disjoint_iff_inter_eq_empty.mp (disjoint_compl_left.mono_left hjUc)
      rw [hemp]
      simp only [empty_subset, not_true_eq_false, false_iff, not_and]
      intro hjU'
      have hsub : inputSupport p j ⊆ ∅ := by
         rw [← hemp]
         exact subset_inter Subset.rfl hjU'
      exact not_not.mpr (hsub.trans (empty_subset A))
  have hfilterUc : (univ.filter fun j => ¬ inputSupport p j ∩ Uᶜ ⊆ B) =
      univ.filter fun j => inputSupport p j ⊆ Uᶜ ∧ ¬ inputSupport p j ⊆ B := by
    ext j
    simp only [mem_filter, mem_univ, true_and]
    rcases hsplit j with hjU | hjUc
    · have hemp : inputSupport p j ∩ Uᶜ = ∅ :=
        disjoint_iff_inter_eq_empty.mp (disjoint_compl_right.mono_left hjU)
      rw [hemp]
      simp only [empty_subset, not_true_eq_false, false_iff, not_and]
      intro hjUc'
      have hsub : inputSupport p j ⊆ ∅ := by
        rw [← hemp]
        exact subset_inter Subset.rfl hjUc'
      exact not_not.mpr (hsub.trans (empty_subset B))
    · rw [inter_eq_left.mpr hjUc]
      exact ⟨fun h => ⟨hjUc, h⟩, fun h => h.2⟩
  refine ⟨P, Q, readout v, fun x hx y hy => by rw [← hreadout, hv x hx y hy], ?_, ?_⟩
  · rwa [← hfilterU]
  · rwa [← hfilterUc]

/-- Gates whose input support meets `S` belong to `inputGates p`. -/
theorem card_filter_inter_nonempty_le_card_inputGates (p : Program signature n g)
    (S : Finset (Fin n)) :
    (univ.filter fun j => (inputSupport p j ∩ S).Nonempty).card ≤ (inputGates p).card := by
  classical
  apply card_le_card
  intro j hj
  rw [mem_filter] at hj
  rw [mem_inputGates_iff_inputSupport_nonempty]
  exact hj.2.mono inter_subset_left

/-- **The cut theorem.** If `p` computes a two-sided `K`-rectangle-free function `f` through
`readout` with `K ≤ 2 ^ k`, then for every coordinate split `U`, one side has fewer than `k`
more coordinates than gates whose input support meets that side. -/
theorem lt_of_split (p : Program signature n g)
    (readout : (Fin g → Bool) → Bool) {f : Cslib.BooleanFunction n} {K : ℕ}
    (hreadout : ∀ x, readout (p.eval interpretation x) = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K)
    (U : Finset (Fin n)) {k : ℕ} (hK : K ≤ 2 ^ k) :
    U.card < (univ.filter fun j => (inputSupport p j ∩ U).Nonempty).card + k ∨
    Uᶜ.card < (univ.filter fun j => (inputSupport p j ∩ Uᶜ).Nonempty).card + k := by
  obtain ⟨P, Q, b, hb, hP, hQ⟩ := exists_rectangle_of_cut p readout hreadout U
  by_contra hno
  push Not at hno
  obtain ⟨h1, h2⟩ := hno
  have hPK : K ≤ P.card := le_card_of_pow_le hP h1 hK
  have hQK : K ≤ Q.card := le_card_of_pow_le hQ h2 hK
  rcases card_lt_or_card_lt_of_rectangleFree hf U P Q b hb with h | h <;> omega

/-- The cut theorem for a single-output weighted threshold circuit whose output selects a gate. -/
theorem circuit_lt_of_split (c : Circuit signature n 1)
    (houtput : ∃ gate, c.outputs 0 = .gate gate) {f : Cslib.BooleanFunction n} {K : ℕ}
    (hcomputes : ∀ x, c.eval interpretation x 0 = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K)
    (U : Finset (Fin n)) {k : ℕ} (hK : K ≤ 2 ^ k) :
    U.card < (univ.filter fun j => (inputSupport c.program j ∩ U).Nonempty).card + k ∨
    Uᶜ.card < (univ.filter fun j => (inputSupport c.program j ∩ Uᶜ).Nonempty).card + k := by
  obtain ⟨gate, hgate⟩ := houtput
  apply lt_of_split c.program (fun z => z gate) ?_ hf U hK
  simpa only [Circuit.eval_of_output_eq_gate hgate] using hcomputes

/-- **The balanced cut bound.** If `p` computes a two-sided `K`-rectangle-free function `f`
through `readout` with `K ≤ 2 ^ k`, then `n ≤ 2 * ((inputGates p).card + k)`. -/
theorem le_two_mul_add (p : Program signature n g)
    (readout : (Fin g → Bool) → Bool) {f : Cslib.BooleanFunction n} {K : ℕ}
    (hreadout : ∀ x, readout (p.eval interpretation x) = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K)
    {k : ℕ} (hK : K ≤ 2 ^ k) :
    n ≤ 2 * ((inputGates p).card + k) := by
  classical
  let U : Finset (Fin n) :=
    (univ : Finset (Fin (n / 2))).map (Fin.castLEEmb (Nat.div_le_self n 2))
  have hU : U.card = n / 2 := by simp [U]
  have hUc : Uᶜ.card = n - n / 2 := by rw [card_compl, Fintype.card_fin, hU]
  have h1 := card_filter_inter_nonempty_le_card_inputGates p U
  have h2 := card_filter_inter_nonempty_le_card_inputGates p Uᶜ
  rcases lt_of_split p readout hreadout hf U hK with h | h <;> omega

/-- The balanced cut bound for a single-output weighted threshold circuit whose output selects a
gate. -/
theorem circuit_le_two_mul_add (c : Circuit signature n 1)
    (houtput : ∃ gate, c.outputs 0 = .gate gate) {f : Cslib.BooleanFunction n} {K : ℕ}
    (hcomputes : ∀ x, c.eval interpretation x 0 = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K)
    {k : ℕ} (hK : K ≤ 2 ^ k) :
    n ≤ 2 * ((inputGates c.program).card + k) := by
  obtain ⟨gate, hgate⟩ := houtput
  apply le_two_mul_add c.program (fun z => z gate) ?_ hf hK
  simpa only [Circuit.eval_of_output_eq_gate hgate] using hcomputes

end Cslib.Circuits.Boolean.WeightedThreshold
