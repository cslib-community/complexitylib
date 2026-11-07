/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Probability.Coding.PrefixFreeEntropy
import Complexity.Probability.PMF.Expect
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi

/-!
# Prefix-Free Set-Separator Codes (`arXiv:2306.02253`, Theorem 5.2)

Given a finite universe `Fin S` and any distribution `μ` over disjoint subset pairs
`(A, B) : Finset (Fin S) × Finset (Fin S)`, this module constructs a deterministic prefix-free
binary code `enc` together with a decoding predicate `sep : List Bool → Fin S → Bool` such that:

1. `Set.range enc` satisfies `InformationTheory.IsPrefixFree`, so `enc (A, B)` can be concatenated
   with subsequent protocol fields without length headers via
   `InformationTheory.IsPrefixFree.bind_append`.
2. For every disjoint pair `(A, B)`, `sep (enc (A, B))` evaluates to `true` on `A` and `false` on
   `B` (so `sepSet sep (enc (A, B))` contains `A` and is disjoint from `B`).
3. Under `μ`, the expected bit length of `enc` is at most
   `2 * E_μ[|A| + |B|] + 7`.

## Source attribution and formalization adaptation

* **Pinned source:** Tianxiao Li, Jingxun Liang, Huacheng Yu, and Renfei Zhou, *"Tight Cell-Probe
  Lower Bounds for Dynamic Succinct Dictionaries"*, in *Proceedings of the 2023 IEEE 64th Annual
  Symposium on Foundations of Computer Science* (FOCS 2023), pp. 1842–1862
  (`arXiv:2306.02253v3`, Section 5.1, Theorem 5.2, PDF p. 23 / printed p. 22, and its application
  to cell sets `S_B` and `S_A \ S_B` in Section 5.1 Step 3, PDF p. 23 / printed p. 22, and
  Section 5.2 Eq. (11), PDF p. 25 / printed p. 24).
* **Source statement (paraphrase):** Theorem 5.2 cites Bernard Chazelle, Joe Kilian, Ronitt
  Rubinfeld, and Ayellet Tal, *"The Bloomier Filter: An Efficient Data Structure for Static Support
  Lookup Tables"*, SODA 2004, pp. 30–39, stating that for any two disjoint subsets `A, B` of a
  finite universe there exists a separating set `S*` (`A ⊆ S*` and `B ∩ S* = ∅`) encodable within
  at most `β (|A| + |B|)` bits in expectation for all `|A| + |B| > 0`, for a global constant
  `β > 0`.
* **Intentional proof and statement adaptation (original):** Rather than formalizing hypergraph
  peeling from Chazelle–Kilian–Rubinfeld–Tal (`β = log₂ e ≈ 1.443` under shared randomness), we
  exploit that receiver Bob in the cell-probe communication game has unbounded free computation and
  knows the input distribution `μ`. Sampling `T = 2 ^ (2 * S + 2)` independent uniform bitmasks on
  `Fin S`, encoding the 1-based index of the first separating mask via `true :: eliasGamma (j₀ + 1)`
  (or `false :: List.ofFn (fun i => decide (i ∈ A))` of length `S + 1` if none separates), and
  averaging over the random codebook fixes a single deterministic prefix-free code `(enc, sep)` for
  `μ` with explicit linear factor `β = 2` and additive constant `C = 7` bits across all pairs
  (including `|A| + |B| = 0`).

## Main definitions

* `Cslib.Probability.Coding.sepSet`: separating `Finset (Fin S)` decoded from a separator predicate
  and codeword.

## Main results

* `Cslib.Probability.Coding.exists_prefixFree_separator_code`: existence of a deterministic
  prefix-free separator code with expected bit length `≤ 2 * E_μ[|A| + |B|] + 7`.
* `Cslib.Probability.Coding.subset_sepSet_and_disjoint`: `sepSet` turns pointwise Boolean
  separation into `A ⊆ sepSet sep w ∧ Disjoint B (sepSet sep w)`.
-/

public section

namespace Cslib.Probability.Coding

open InformationTheory Cslib.Probability.PMF
open scoped BigOperators ENNReal

/-- Finite separating set `{x : Fin S | sep w x = true}` decoded from a separator codeword `w`. -/
@[expose] def sepSet {S : ℕ} (sep : List Bool → Fin S → Bool) (w : List Bool) : Finset (Fin S) :=
  Finset.univ.filter fun x => sep w x = true

/-- Pointwise Boolean separation on `(A, B)` implies `A ⊆ sepSet sep w` and
`Disjoint B (sepSet sep w)`. -/
theorem subset_sepSet_and_disjoint {S : ℕ} {sep : List Bool → Fin S → Bool} {w : List Bool}
    {A B : Finset (Fin S)}
    (hA : ∀ x ∈ A, sep w x = true) (hB : ∀ y ∈ B, sep w y = false) :
    A ⊆ sepSet sep w ∧ Disjoint B (sepSet sep w) := by
  refine ⟨fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ x, hA x hx⟩, ?_⟩
  rw [Finset.disjoint_left]
  intro y hy hmem
  have htrue : sep w y = true := (Finset.mem_filter.mp hmem).2
  rw [hB y hy] at htrue
  cases htrue

/-! ### Codebook construction for a fixed mask table `θ` -/

private def separates {S : ℕ} (r : Fin S → Bool) (A B : Finset (Fin S)) : Bool :=
  decide ((∀ x ∈ A, r x = true) ∧ (∀ y ∈ B, r y = false))

private theorem separates_eq_true_iff {S : ℕ} {r : Fin S → Bool} {A B : Finset (Fin S)} :
    separates r A B = true ↔ (∀ x ∈ A, r x = true) ∧ (∀ y ∈ B, r y = false) :=
  decide_eq_true_iff

private def firstHit : {T : ℕ} → (Fin T → Bool) → Option (Fin T)
  | 0, _ => none
  | _ + 1, p =>
    if p 0 then some 0
    else (firstHit (fun j => p j.succ)).map Fin.succ

private theorem firstHit_eq_some {T : ℕ} {p : Fin T → Bool} {j₀ : Fin T}
    (h : firstHit p = some j₀) : p j₀ = true := by
  induction T with
  | zero => exact j₀.elim0
  | succ T ih =>
    unfold firstHit at h
    split_ifs at h with hp0
    · cases h
      exact hp0
    · obtain ⟨j', hj', rfl⟩ := Option.map_eq_some_iff.mp h
      exact ih hj'

private theorem firstHit_lt_eq_false {T : ℕ} {p : Fin T → Bool} {j₀ i : Fin T}
    (h : firstHit p = some j₀) (hlt : i.val < j₀.val) : p i = false := by
  induction T with
  | zero => exact j₀.elim0
  | succ T ih =>
    unfold firstHit at h
    split_ifs at h with hp0
    · cases h
      simp at hlt
    · obtain ⟨j', hj', rfl⟩ := Option.map_eq_some_iff.mp h
      cases i using Fin.cases with
      | zero => exact Bool.eq_false_iff.mpr hp0
      | succ i' =>
        simp only [Fin.val_succ, Nat.add_lt_add_iff_right] at hlt
        exact ih hj' hlt

private theorem firstHit_eq_none {T : ℕ} {p : Fin T → Bool}
    (h : firstHit p = none) (i : Fin T) : p i = false := by
  induction T with
  | zero => exact i.elim0
  | succ T ih =>
    unfold firstHit at h
    split_ifs at h with hp0
    rw [Option.map_eq_none_iff] at h
    cases i using Fin.cases with
    | zero => exact Bool.eq_false_iff.mpr hp0
    | succ i' => exact ih h i'

private def encOf {S T : ℕ} (θ : Fin T → Fin S → Bool)
    (ab : Finset (Fin S) × Finset (Fin S)) : List Bool :=
  match firstHit (fun j => separates (θ j) ab.1 ab.2) with
  | some j₀ => true :: eliasGamma (j₀.val + 1)
  | none => false :: List.ofFn (fun i : Fin S => decide (i ∈ ab.1))

private def sepOf {S T : ℕ} (θ : Fin T → Fin S → Bool) : List Bool → Fin S → Bool
  | true :: code =>
    let idx := decodeEliasGamma code - 1
    if h : idx < T then θ ⟨idx, h⟩ else fun _ => false
  | false :: bits => fun i => bits.getD i.val false
  | [] => fun _ => false

private theorem isPrefixFree_range_encOf {S T : ℕ} (θ : Fin T → Fin S → Bool) :
    IsPrefixFree (Set.range (encOf θ)) := by
  rintro _ ⟨ab₁, rfl⟩ _ ⟨ab₂, rfl⟩ hpref
  unfold encOf at hpref ⊢
  cases h₁ : firstHit (fun j => separates (θ j) ab₁.1 ab₁.2) <;>
    cases h₂ : firstHit (fun j => separates (θ j) ab₂.1 ab₂.2) <;>
    simp only [h₁, h₂] at hpref ⊢
  · rcases hpref with ⟨r, hr⟩
    have hlen := congrArg List.length hr
    simp only [List.length_append, List.length_cons, List.length_ofFn] at hlen
    have hr_nil : r = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [← hr, hr_nil, List.append_nil]
  · cases List.cons_prefix_cons.mp hpref |>.1
  · cases List.cons_prefix_cons.mp hpref |>.1
  · have hsub : eliasGamma (_ + 1) <+: eliasGamma (_ + 1) := (List.cons_prefix_cons.mp hpref).2
    rw [isPrefixFree_range_eliasGamma _ ⟨_, rfl⟩ _ ⟨_, rfl⟩ hsub]

private theorem sepOf_encOf {S T : ℕ} (θ : Fin T → Fin S → Bool)
    {A B : Finset (Fin S)} (hdisj : Disjoint A B) :
    (∀ x ∈ A, sepOf θ (encOf θ (A, B)) x = true) ∧
      (∀ y ∈ B, sepOf θ (encOf θ (A, B)) y = false) := by
  unfold encOf
  cases h : firstHit (fun j => separates (θ j) A B) with
  | none =>
    refine ⟨fun x hx => ?_, fun y hy => ?_⟩
    · simp [sepOf, hx]
    · have hyA : y ∉ A := Finset.disjoint_right.mp hdisj hy
      simp [sepOf, hyA]
  | some j₀ =>
    have hsep := separates_eq_true_iff.mp (firstHit_eq_some h)
    have hdec : decodeEliasGamma (eliasGamma (j₀.val + 1)) - 1 = j₀.val := by
      rw [decodeEliasGamma_eliasGamma (by omega)]
      omega
    have heval : sepOf θ (true :: eliasGamma (j₀.val + 1)) = θ j₀ := by
      funext i
      simp only [sepOf, hdec, dite_eq_left j₀.isLt, Fin.eta]
    rw [heval]
    exact hsep

/-! ### Expected codeword length under a random uniform codebook -/

private theorem card_filter_separates {S : ℕ} {A B : Finset (Fin S)} (hdisj : Disjoint A B) :
    (Finset.univ.filter fun r : Fin S → Bool => separates r A B = true).card =
      2 ^ (S - (A.card + B.card)) := by
  let U_rem : Finset (Fin S) := (A ∪ B)ᶜ
  let extend : ({i : Fin S // i ∈ U_rem} → Bool) → Fin S → Bool :=
    fun f i => if hi : i ∈ U_rem then f ⟨i, hi⟩ else decide (i ∈ A)
  have hbij : (Finset.univ : Finset ({i : Fin S // i ∈ U_rem} → Bool)).card =
      (Finset.univ.filter fun r : Fin S → Bool => separates r A B = true).card := by
    refine Finset.card_bij (fun f _ => extend f) ?_ ?_ ?_
    · intro f _
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, separates_eq_true_iff.mpr ⟨fun x hx => ?_, fun y hy => ?_⟩⟩
      · have hx_not : x ∉ U_rem := by simp [U_rem, hx]
        simp [extend, hx_not, hx]
      · have hy_not : y ∉ U_rem := by simp [U_rem, hy]
        have hyA : y ∉ A := Finset.disjoint_right.mp hdisj hy
        simp [extend, hy_not, hyA]
    · intro f₁ _ f₂ _ heq
      funext ⟨i, hi⟩
      have hi_eq := congrFun heq i
      simpa [extend, hi] using hi_eq
    · intro r hr
      obtain ⟨hA, hB⟩ := separates_eq_true_iff.mp (Finset.mem_filter.mp hr).2
      refine ⟨fun x => r x.1, Finset.mem_univ _, ?_⟩
      funext i
      by_cases hi : i ∈ U_rem
      · simp [extend, hi]
      · have hiAB : i ∈ A ∪ B := by
          dsimp only [U_rem] at hi
          rwa [Finset.mem_compl, not_not] at hi
        rcases Finset.mem_union.mp hiAB with hiA | hiB
        · simp [extend, hi, hiA, hA i hiA]
        · have hiA : i ∉ A := Finset.disjoint_right.mp hdisj hiB
          simp [extend, hi, hiA, hB i hiB]
  rw [← hbij, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
  congr 1
  rw [Finset.card_compl, Fintype.card_fin, Finset.card_union_of_disjoint hdisj]

private theorem sum_row_separates_false {S : ℕ} {A B : Finset (Fin S)} (hdisj : Disjoint A B) :
    (∑ r : Fin S → Bool,
      ((PMF.uniformOfFintype (Fin S → Bool)) r).toReal *
        (if separates r A B = false then (1 : ℝ) else 0)) =
      1 - (2⁻¹ : ℝ) ^ (A.card + B.card) := by
  set k := A.card + B.card
  have hk_le : k ≤ S := by
    have hle := Finset.card_le_univ (A ∪ B)
    rwa [Finset.card_union_of_disjoint hdisj, Fintype.card_fin] at hle
  have hsum_true : (∑ r : Fin S → Bool,
      ((PMF.uniformOfFintype (Fin S → Bool)) r).toReal *
        (if separates r A B = true then (1 : ℝ) else 0)) = (2⁻¹ : ℝ) ^ k := by
    simp only [PMF.uniformOfFintype_apply, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
      Nat.cast_pow, Nat.cast_ofNat, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
      mul_ite, mul_one, mul_zero, Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, nsmul_eq_mul]
    rw [card_filter_separates hdisj, Nat.cast_pow, Nat.cast_ofNat]
    have hpow_split : (2 : ℝ) ^ S = (2 : ℝ) ^ (S - k) * (2 : ℝ) ^ k := by
      rw [← pow_add, Nat.sub_add_cancel hk_le]
    rw [hpow_split, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul, inv_pow]
  have hsum_one : ∑ r : Fin S → Bool, ((PMF.uniformOfFintype (Fin S → Bool)) r).toReal = 1 :=
    sum_toReal (PMF.uniformOfFintype (Fin S → Bool))
  have hsplit (r : Fin S → Bool) :
      ((PMF.uniformOfFintype (Fin S → Bool)) r).toReal *
        (if separates r A B = false then (1 : ℝ) else 0) =
      ((PMF.uniformOfFintype (Fin S → Bool)) r).toReal -
      ((PMF.uniformOfFintype (Fin S → Bool)) r).toReal *
        (if separates r A B = true then (1 : ℝ) else 0) := by
    cases separates r A B <;> simp
  simp_rw [hsplit, Finset.sum_sub_distrib, hsum_one, hsum_true]

private theorem sum_codebook_prefix_false {S T : ℕ} {A B : Finset (Fin S)}
    (hdisj : Disjoint A B) {m : ℕ} (hm : m ≤ T) :
    (∑ θ : Fin T → Fin S → Bool,
      ((PMF.uniformOfFintype (Fin T → Fin S → Bool)) θ).toReal *
        (if ∀ j : Fin T, j.val < m → separates (θ j) A B = false then (1 : ℝ) else 0)) =
      (1 - (2⁻¹ : ℝ) ^ (A.card + B.card)) ^ m := by
  let rowPMF := PMF.uniformOfFintype (Fin S → Bool)
  let cbPMF := PMF.uniformOfFintype (Fin T → Fin S → Bool)
  have hmass (θ : Fin T → Fin S → Bool) :
      (cbPMF θ).toReal = ∏ j : Fin T, (rowPMF (θ j)).toReal := by
    simp [cbPMF, rowPMF, PMF.uniformOfFintype_apply, Fintype.card_fin,
      Fintype.card_bool, ENNReal.toReal_inv, ENNReal.toReal_pow, ← inv_pow]
  have hind (θ : Fin T → Fin S → Bool) :
      (if ∀ j : Fin T, j.val < m → separates (θ j) A B = false then (1 : ℝ) else 0) =
        ∏ j : Fin T,
          (if j.val < m then (if separates (θ j) A B = false then (1 : ℝ) else 0) else 1) := by
    by_cases hall : ∀ j : Fin T, j.val < m → separates (θ j) A B = false
    · rw [ite_eq_left hall]
      symm
      refine Finset.prod_eq_one fun j _ => ?_
      by_cases hj : j.val < m
      · rw [ite_eq_left hj, ite_eq_left (hall j hj)]
      · rw [ite_eq_right hj]
    · rw [ite_eq_right hall]
      obtain ⟨j₀, hj₀, htrue⟩ :
          ∃ j : Fin T, ∃ (_ : j.val < m), separates (θ j) A B ≠ false := by
        simpa only [not_forall] using hall
      symm
      refine Finset.prod_eq_zero (Finset.mem_univ j₀) ?_
      rw [ite_eq_left hj₀, ite_eq_right htrue]
  let g (j : Fin T) (r : Fin S → Bool) : ℝ :=
    (rowPMF r).toReal * (if j.val < m then (if separates r A B = false then 1 else 0) else 1)
  have hterm (θ : Fin T → Fin S → Bool) :
      (cbPMF θ).toReal *
        (if ∀ j : Fin T, j.val < m → separates (θ j) A B = false then (1 : ℝ) else 0) =
      ∏ j : Fin T, g j (θ j) := by
    rw [hmass θ, hind θ, ← Finset.prod_mul_distrib]
  change (∑ θ : Fin T → Fin S → Bool,
    (cbPMF θ).toReal *
      (if ∀ j : Fin T, j.val < m → separates (θ j) A B = false then (1 : ℝ) else 0)) = _
  simp_rw [hterm]
  rw [← Fintype.prod_sum]
  have hfactor (j : Fin T) :
      ∑ r : Fin S → Bool, g j r =
        if j.val < m then 1 - (2⁻¹ : ℝ) ^ (A.card + B.card) else 1 := by
    by_cases hj : j.val < m
    · rw [ite_eq_left hj]
      dsimp only [g]
      simp_rw [ite_eq_left hj]
      exact sum_row_separates_false hdisj
    · rw [ite_eq_right hj]
      dsimp only [g]
      simp_rw [ite_eq_right hj, mul_one]
      exact sum_toReal rowPMF
  simp_rw [hfactor]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  have hcard : (Finset.univ.filter fun j : Fin T => j.val < m).card = m := by
    refine Eq.trans ?_ (Finset.card_range m)
    refine Finset.card_bij (fun j _ => j.val) ?_ ?_ ?_
    · intro j hj
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
    · intro j₁ _ j₂ _ hval
      exact Fin.ext hval
    · intro x hx
      have hxm : x < m := Finset.mem_range.mp hx
      exact ⟨⟨x, lt_of_lt_of_le hxm hm⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxm⟩, rfl⟩
  rw [hcard]

private theorem one_sub_pow_le_inv {p : ℝ} (hp1 : p ≤ 1) (m : ℕ)
    (hmp : 0 < (m : ℝ) * p) : (1 - p) ^ m ≤ ((m : ℝ) * p)⁻¹ := by
  have hexp1 : 1 - p ≤ Real.exp (-p) := by
    have h := Real.add_one_le_exp (-p)
    linarith
  have hpow : (1 - p) ^ m ≤ Real.exp (-(m : ℝ) * p) := by
    calc (1 - p) ^ m ≤ (Real.exp (-p)) ^ m := pow_le_pow_left₀ (by linarith) hexp1 m
      _ = Real.exp (-(m : ℝ) * p) := by rw [← Real.exp_nat_mul]; ring_nf
  have hexp2 : (m : ℝ) * p ≤ Real.exp ((m : ℝ) * p) := by
    have h := Real.add_one_le_exp ((m : ℝ) * p)
    linarith
  calc (1 - p) ^ m ≤ Real.exp (-(m : ℝ) * p) := hpow
    _ = (Real.exp ((m : ℝ) * p))⁻¹ := by rw [neg_mul, Real.exp_neg]
    _ ≤ ((m : ℝ) * p)⁻¹ := inv_anti₀ hmp hexp2

private theorem nat_log_le_add_sum_ge {v k L : ℕ} (hv1 : 1 ≤ v) (hvL : v ≤ 2 ^ L) :
    Nat.log 2 v ≤ k + ∑ s ∈ Finset.range (L - k), (if 2 ^ (k + 1 + s) ≤ v then 1 else 0) := by
  set ℓ := Nat.log 2 v
  have hℓL : ℓ ≤ L := by
    calc ℓ ≤ Nat.log 2 (2 ^ L) := Nat.log_mono_right hvL
      _ = L := Nat.log_pow Nat.one_lt_two L
  rcases le_or_gt ℓ k with hle | hgt
  · omega
  · have hsub : Finset.range (ℓ - k) ⊆ Finset.range (L - k) :=
      Finset.range_mono (by omega)
    have hsum_ge : ℓ - k ≤
        ∑ s ∈ Finset.range (L - k), (if 2 ^ (k + 1 + s) ≤ v then 1 else 0) := by
      calc ℓ - k
          = ∑ s ∈ Finset.range (ℓ - k), 1 := by simp
        _ = ∑ s ∈ Finset.range (ℓ - k), (if 2 ^ (k + 1 + s) ≤ v then 1 else 0) := by
            refine Finset.sum_congr rfl fun s hs => ?_
            have hs_lt : s < ℓ - k := Finset.mem_range.mp hs
            have hpow : 2 ^ (k + 1 + s) ≤ v :=
              (Nat.le_log_iff_pow_le Nat.one_lt_two (by omega)).mp (by omega)
            rw [ite_eq_left hpow]
        _ ≤ ∑ s ∈ Finset.range (L - k), (if 2 ^ (k + 1 + s) ≤ v then 1 else 0) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.zero_le _
    omega

private theorem expected_length_encOf_le {S : ℕ} {A B : Finset (Fin S)} (hdisj : Disjoint A B) :
    let T := 2 ^ (2 * S + 2)
    (∑ θ : Fin T → Fin S → Bool,
      ((PMF.uniformOfFintype (Fin T → Fin S → Bool)) θ).toReal *
        ((encOf θ (A, B)).length : ℝ)) ≤
      2 * ((A.card + B.card : ℕ) : ℝ) + 7 := by
  set L := 2 * S + 2
  set T := 2 ^ L
  set k := A.card + B.card
  have hk_le : k ≤ S := by
    have hle := Finset.card_le_univ (A ∪ B)
    rwa [Finset.card_union_of_disjoint hdisj, Fintype.card_fin] at hle
  let fail (m : ℕ) (θ : Fin T → Fin S → Bool) : ℝ :=
    if ∀ j : Fin T, j.val < m → separates (θ j) A B = false then 1 else 0
  have hfail_nonneg (m : ℕ) (θ : Fin T → Fin S → Bool) : 0 ≤ fail m θ := by
    dsimp only [fail]; split_ifs <;> norm_num
  have hpointwise (θ : Fin T → Fin S → Bool) :
      ((encOf θ (A, B)).length : ℝ) ≤
        2 + 2 * (k : ℝ) +
          2 * (∑ s ∈ Finset.range (L - k), fail (2 ^ (k + s)) θ) +
          (S + 1 : ℝ) * fail T θ := by
    unfold encOf
    cases hhit : firstHit (fun j => separates (θ j) A B) with
    | none =>
      have hall : ∀ j : Fin T, separates (θ j) A B = false := firstHit_eq_none hhit
      have hfT : fail T θ = 1 := ite_eq_left fun j _ => hall j
      have hsum_nn : 0 ≤ ∑ s ∈ Finset.range (L - k), fail (2 ^ (k + s)) θ :=
        Finset.sum_nonneg fun s _ => hfail_nonneg _ θ
      simp only [List.length_cons, List.length_ofFn, Nat.cast_add, Nat.cast_one, hfT, mul_one]
      have hk_nn : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    | some j₀ =>
      have hj_le : j₀.val + 1 ≤ 2 ^ L := j₀.isLt
      have hlog_nat := nat_log_le_add_sum_ge (k := k) (L := L) (by omega) hj_le
      have hlog_real : (Nat.log 2 (j₀.val + 1) : ℝ) ≤
          (k : ℝ) + ∑ s ∈ Finset.range (L - k),
            (if 2 ^ (k + 1 + s) ≤ j₀.val + 1 then (1 : ℝ) else 0) := by
        exact_mod_cast hlog_nat
      have hind_le : ∑ s ∈ Finset.range (L - k),
            (if 2 ^ (k + 1 + s) ≤ j₀.val + 1 then (1 : ℝ) else 0) ≤
          ∑ s ∈ Finset.range (L - k), fail (2 ^ (k + s)) θ := by
        refine Finset.sum_le_sum fun s _ => ?_
        split_ifs with hpow
        · have h2 : 2 ^ (k + s) ≤ j₀.val := by
            have hpow' : 2 * 2 ^ (k + s) ≤ j₀.val + 1 := by
              simpa [Nat.pow_succ', Nat.add_right_comm k 1 s] using hpow
            have hpos : 1 ≤ 2 ^ (k + s) := Nat.one_le_two_pow
            omega
          have hfail_one : fail (2 ^ (k + s)) θ = 1 :=
            ite_eq_left fun j hj => firstHit_lt_eq_false hhit (lt_of_lt_of_le hj h2)
          rw [hfail_one]
        · exact hfail_nonneg _ θ
      have hfT_nn : 0 ≤ (S + 1 : ℝ) * fail T θ :=
        mul_nonneg (by positivity) (hfail_nonneg T θ)
      simp only [List.length_cons, length_eliasGamma, Nat.cast_add, Nat.cast_mul,
        Nat.cast_ofNat, Nat.cast_one]
      linarith
  let cbPMF := PMF.uniformOfFintype (Fin T → Fin S → Bool)
  set p : ℝ := (2⁻¹ : ℝ) ^ k
  have hp1 : p ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hsum_pt : ∑ θ, (cbPMF θ).toReal * ((encOf θ (A, B)).length : ℝ) ≤
      2 + 2 * (k : ℝ) +
        2 * (∑ s ∈ Finset.range (L - k), ∑ θ, (cbPMF θ).toReal * fail (2 ^ (k + s)) θ) +
        (S + 1 : ℝ) * (∑ θ, (cbPMF θ).toReal * fail T θ) := by
    calc ∑ θ, (cbPMF θ).toReal * ((encOf θ (A, B)).length : ℝ)
        ≤ ∑ θ, (cbPMF θ).toReal *
            (2 + 2 * (k : ℝ) +
              2 * (∑ s ∈ Finset.range (L - k), fail (2 ^ (k + s)) θ) +
              (S + 1 : ℝ) * fail T θ) :=
          Finset.sum_le_sum fun θ _ =>
            mul_le_mul_of_nonneg_left (hpointwise θ) ENNReal.toReal_nonneg
      _ = 2 + 2 * (k : ℝ) +
            2 * (∑ s ∈ Finset.range (L - k), ∑ θ, (cbPMF θ).toReal * fail (2 ^ (k + s)) θ) +
            (S + 1 : ℝ) * (∑ θ, (cbPMF θ).toReal * fail T θ) := by
          simp only [mul_add, Finset.sum_add_distrib]
          simp only [← Finset.sum_mul, sum_toReal cbPMF, one_mul,
            mul_left_comm _ (2 : ℝ), mul_left_comm _ (S + 1 : ℝ), ← Finset.mul_sum]
          congr 2
          congr 1
          simp_rw [Finset.mul_sum]
          exact Finset.sum_comm
  have htail_sum : ∑ s ∈ Finset.range (L - k), (∑ θ, (cbPMF θ).toReal * fail (2 ^ (k + s)) θ) ≤
      2 := by
    have hterm_le : ∀ s ∈ Finset.range (L - k),
        (∑ θ, (cbPMF θ).toReal * fail (2 ^ (k + s)) θ) ≤ (2⁻¹ : ℝ) ^ s := by
      intro s hs
      have hks_lt : k + s < L := by
        have := Finset.mem_range.mp hs
        omega
      have hm_le : 2 ^ (k + s) ≤ T := Nat.pow_le_pow_right Nat.two_pos hks_lt.le
      rw [sum_codebook_prefix_false hdisj hm_le]
      have hmp_eq : ((2 ^ (k + s) : ℕ) : ℝ) * p = (2 : ℝ) ^ s := by
        push_cast
        simp only [p, pow_add]
        rw [mul_right_comm, ← mul_pow, mul_inv_cancel₀ (by norm_num), one_pow, one_mul]
      have hmp_pos : 0 < ((2 ^ (k + s) : ℕ) : ℝ) * p := by
        rw [hmp_eq]; positivity
      refine (one_sub_pow_le_inv hp1 (2 ^ (k + s)) hmp_pos).trans_eq ?_
      rw [hmp_eq, inv_pow]
    calc ∑ s ∈ Finset.range (L - k), (∑ θ, (cbPMF θ).toReal * fail (2 ^ (k + s)) θ)
        ≤ ∑ s ∈ Finset.range (L - k), (2⁻¹ : ℝ) ^ s := Finset.sum_le_sum hterm_le
      _ = ((2⁻¹ : ℝ) ^ (L - k) - 1) / (2⁻¹ - 1) := geom_sum_eq (by norm_num) (L - k)
      _ ≤ 2 := by
        have hpos : (0 : ℝ) ≤ (2⁻¹ : ℝ) ^ (L - k) := by positivity
        have hdiv : ((2⁻¹ : ℝ) ^ (L - k) - 1) / (2⁻¹ - 1) =
            2 - 2 * (2⁻¹ : ℝ) ^ (L - k) := by ring
        rw [hdiv]
        linarith
  have hfallback_le : (S + 1 : ℝ) * (∑ θ, (cbPMF θ).toReal * fail T θ) ≤ 1 := by
    rw [sum_codebook_prefix_false hdisj le_rfl]
    have hTp_eq : (T : ℝ) * p = (2 : ℝ) ^ (L - k) := by
      have hL_split : (2 : ℝ) ^ L = (2 : ℝ) ^ (L - k) * (2 : ℝ) ^ k := by
        rw [← pow_add, Nat.sub_add_cancel (by omega : k ≤ L)]
      simp only [T, p, Nat.cast_pow, Nat.cast_ofNat, hL_split]
      rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ (by norm_num), one_pow, mul_one]
    have hTp_pos : 0 < (T : ℝ) * p := by rw [hTp_eq]; positivity
    have hpow_S : (S + 1 : ℝ) ≤ (2 : ℝ) ^ (L - k) := by
      have hnat : S + 1 ≤ 2 ^ (L - k) := by
        calc S + 1 ≤ 2 ^ (S + 1) := Nat.lt_two_pow_self.le
          _ ≤ 2 ^ (L - k) := Nat.pow_le_pow_right Nat.two_pos (by omega)
      exact_mod_cast hnat
    have hinv := one_sub_pow_le_inv hp1 T hTp_pos
    rw [hTp_eq] at hinv
    calc (S + 1 : ℝ) * (1 - p) ^ T
        ≤ (S + 1 : ℝ) * ((2 : ℝ) ^ (L - k))⁻¹ :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ ≤ (2 : ℝ) ^ (L - k) * ((2 : ℝ) ^ (L - k))⁻¹ :=
          mul_le_mul_of_nonneg_right hpow_S (by positivity)
      _ = 1 := mul_inv_cancel₀ (by positivity)
  linarith

/-- **Self-contained prefix-free set-separator code** (adapting Li–Liang–Yu–Zhou FOCS 2023,
`arXiv:2306.02253v3`, Section 5.1, Theorem 5.2, without hypergraph peeling): for any distribution
`μ` over disjoint pairs `(A, B)` of subsets of `Fin S`, there exist a deterministic prefix-free
encoding `enc` (`IsPrefixFree (Set.range enc)`) and decoding predicate `sep` separating all
disjoint pairs with expected codeword length `≤ 2 * E_μ[|A| + |B|] + 7`. -/
theorem exists_prefixFree_separator_code (S : ℕ)
    (μ : PMF (Finset (Fin S) × Finset (Fin S)))
    (hdisj : ∀ ab ∈ μ.support, Disjoint ab.1 ab.2) :
    ∃ (enc : Finset (Fin S) × Finset (Fin S) → List Bool)
      (sep : List Bool → Fin S → Bool),
      IsPrefixFree (Set.range enc) ∧
      (∀ A B : Finset (Fin S), Disjoint A B →
        (∀ x ∈ A, sep (enc (A, B)) x = true) ∧
        (∀ y ∈ B, sep (enc (A, B)) y = false)) ∧
      ∑ ab, (μ ab).toReal * ((enc ab).length : ℝ) ≤
        2 * (∑ ab, (μ ab).toReal * ((ab.1.card + ab.2.card : ℕ) : ℝ)) + 7 := by
  let T := 2 ^ (2 * S + 2)
  let cbPMF := PMF.uniformOfFintype (Fin T → Fin S → Bool)
  let score (θ : Fin T → Fin S → Bool) : ℝ :=
    ∑ ab, (μ ab).toReal * ((encOf θ ab).length : ℝ)
  set bound : ℝ := 2 * (∑ ab, (μ ab).toReal * ((ab.1.card + ab.2.card : ℕ) : ℝ)) + 7
  have havg : ∑ θ, (cbPMF θ).toReal * score θ ≤ bound := by
    calc ∑ θ, (cbPMF θ).toReal * score θ
        = ∑ ab, (μ ab).toReal *
            (∑ θ, (cbPMF θ).toReal * ((encOf θ ab).length : ℝ)) := by
          simp only [score, Finset.mul_sum, mul_left_comm ((cbPMF _).toReal)]
          exact Finset.sum_comm
      _ ≤ ∑ ab, (μ ab).toReal * (2 * ((ab.1.card + ab.2.card : ℕ) : ℝ) + 7) := by
          refine Finset.sum_le_sum fun ab _ => ?_
          by_cases hab : ab ∈ μ.support
          · exact mul_le_mul_of_nonneg_left
              (expected_length_encOf_le (hdisj ab hab)) ENNReal.toReal_nonneg
          · have h0 : (μ ab).toReal = 0 := by simp [(PMF.apply_eq_zero_iff μ ab).mpr hab]
            simp [h0]
      _ = bound := by
          simp only [bound, mul_add, mul_left_comm _ (2 : ℝ), Finset.sum_add_distrib,
            ← Finset.sum_mul, sum_toReal μ, one_mul, ← Finset.mul_sum]
  have hexists_θ : ∃ θ : Fin T → Fin S → Bool, score θ ≤ bound := by
    by_contra! hgt
    have hlt : bound < ∑ θ, (cbPMF θ).toReal * score θ := by
      have hpos : ∀ θ ∈ (Finset.univ : Finset (Fin T → Fin S → Bool)),
          (cbPMF θ).toReal * bound < (cbPMF θ).toReal * score θ := by
        intro θ _
        have hm_pos : 0 < (cbPMF θ).toReal := by
          simp [cbPMF, PMF.uniformOfFintype_apply, Fintype.card_fin,
            Fintype.card_bool, ENNReal.toReal_inv, ENNReal.toReal_pow]
        exact mul_lt_mul_of_pos_left (hgt θ) hm_pos
      calc bound = ∑ θ, (cbPMF θ).toReal * bound := by
              rw [← Finset.sum_mul, sum_toReal cbPMF, one_mul]
        _ < ∑ θ, (cbPMF θ).toReal * score θ :=
              Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty hpos
    linarith
  obtain ⟨θ₀, hθ₀⟩ := hexists_θ
  exact ⟨encOf θ₀, sepOf θ₀, isPrefixFree_range_encOf θ₀, fun A B hAB => sepOf_encOf θ₀ hAB, hθ₀⟩

end Cslib.Probability.Coding
