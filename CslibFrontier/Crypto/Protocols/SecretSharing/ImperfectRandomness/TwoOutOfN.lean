/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.SecretSharing.ImperfectRandomness
public import CslibFrontier.Crypto.Protocols.SecretSharing.ImperfectRandomness.OddSources
public import Mathlib.FieldTheory.Finite.GaloisField
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map
import Mathlib.Tactic

/-!
# Two-out-of-n sharing from imperfect randomness

The actual construction in STOC submission 886, [Aggarwal2026], Section 4, equations (5)–(6),
PDF pp. 8–9. There are `n - 1` central branches and `n` side branches. Only the owner of a
side branch receives a tagged index. Sources are exactly `OddSources.source`, with all central
branches chosen at indices in `T` and all side branches elsewhere.

The algebra uses subtraction over a general field; in `GaloisField 2 b` subtraction is addition,
so these are the paper's formulas. Fixed noncomputable bijections provide literal bit encodings;
no bit-operation running time is asserted.

## Main results

* `reconstruct_share`, `authorized_correctness`: every authorized coalition reconstructs
  on every ambient key.
* `share_expect`, `unauthorized_privacy`: exact single-share multiplicities and joint privacy.
* `binary_theorem4_1`: full Theorem 4.1 at every admissible `n,b`, including literal
  message/share bits, all four numbered items and tight extraction error.
* `binary_construction`: the correctness/privacy and size/entropy part of this bundle.
* `extraction_parameters`, `binary_index_parameters`: all actual constructor hypotheses
  for applying the generic odd-branch extraction lower bound and tight upper bound.

## References

* [Aggarwal2026], Theorem 4.1 and Lemmas 4.2–4.3.
-/

public section

namespace Cslib.Crypto.Protocols.SecretSharing.ImperfectRandomness.TwoOutOfN

open Finset Cslib.Probability
open scoped Cslib.Probability.PMF

/-- The distinct central and side branches of equation (5). -/
abbrev Branch (n : ℕ) := Fin (n - 1) ⊕ Fin n

/-- A branch together with its field index. -/
abbrev Key (n : ℕ) (V : Type*) := Branch n × V

/-- All central branches, preserving their multiplicity as distinct keys. -/
@[expose] def central (n : ℕ) : Finset (Branch n) := univ.map ⟨Sum.inl, Sum.inl_injective⟩

/-- Membership in the central class distinguishes the two branch constructors. -/
@[simp] theorem mem_central {n : ℕ} (c : Branch n) : c ∈ central n ↔ c.isLeft := by
  cases c <;> simp [central]

/-- Exactly `n - 1` central branches. -/
@[simp] theorem card_central (n : ℕ) : (central n).card = n - 1 := by
  simp [central]

/-- The branch universe has the odd cardinality in Theorem 4.1. -/
theorem card_branch {n : ℕ} (hn : 2 ≤ n) : Fintype.card (Branch n) = 2 * n - 1 := by
  simp only [Branch, Fintype.card_sum, Fintype.card_fin]
  omega

/-- There are `n` side branches. -/
theorem card_side (n : ℕ) : (univ \ central n).card = n := by
  rw [card_sdiff_of_subset (subset_univ _), card_univ, card_central]
  simp only [Branch, Fintype.card_sum, Fintype.card_fin]
  omega

/-- The central choice is nonempty at every permitted threshold. -/
theorem central_nonempty {n : ℕ} (hn : 2 ≤ n) : (central n).Nonempty := by
  rw [← card_pos, card_central]
  omega

/-- The side choice is nonempty at every permitted threshold. -/
theorem side_nonempty {n : ℕ} (hn : 2 ≤ n) : (univ \ central n).Nonempty := by
  rw [← card_pos, card_side]
  omega

/-- The actual source law of equation (6), using the common source family. -/
@[expose] noncomputable def source {n : ℕ} (hn : 2 ≤ n) {V : Type*}
    [Fintype V] [DecidableEq V] [Nonempty V] (T : Finset V) : PMF (Key n V) :=
  OddSources.source (central n) (central_nonempty hn) (side_nonempty hn) T

/-- A central key gives every party an ordinary share; a side key tags only its owner. -/
@[expose] def share {n : ℕ} {V : Type*} [Field V] (α : Fin n → V)
    (j : Fin n) (m : V) : Key n V → Share V
  | (.inl _, i) => .inl (α j * i + m)
  | (.inr p, i) => if j = p then .inr i else .inl (α j * i + m)

/-- Reconstruction from two shares. The both-tagged case never occurs for distinct parties. -/
@[expose] def reconstruct {V : Type*} [Field V] (a b : V) : Share V → Share V → V
  | .inl x, .inl y => x - a * ((x - y) / (a - b))
  | .inr i, .inl y => y - b * i
  | .inl x, .inr i => x - a * i
  | .inr _, .inr _ => 0

/-- Lemma 4.2: every pair of distinct parties reconstructs, even outside the chosen source. -/
theorem reconstruct_share {n : ℕ} {V : Type*} [Field V] {α : Fin n → V}
    (hα : Function.Injective α) {j l : Fin n} (hjl : j ≠ l) (m : V) (k : Key n V) :
    reconstruct (α j) (α l) (share α j m k) (share α l m k) = m := by
  have hd : α j - α l ≠ 0 := sub_ne_zero.mpr (fun h => hjl (hα h))
  have hi (i : V) : (α j * i + m - (α l * i + m)) / (α j - α l) = i := by
    apply (div_eq_iff hd).mpr
    ring
  rcases k with ⟨c | p, i⟩
  · simp only [share, reconstruct, hi]
    ring
  · by_cases hj : j = p
    · have hl : l ≠ p := by intro h; exact hjl (hj.trans h.symm)
      simp only [share, hj, hl, ite_true, ite_false, reconstruct]
      ring
    · by_cases hl : l = p
      · simp only [share, hj, hl, ite_true, ite_false, reconstruct]
        ring
      · simp only [share, hj, hl, ite_false, reconstruct, hi]
        ring

/-- Every permitted finite field has enough distinct nonzero slopes: there is no additional
slope-existence hypothesis in the binary construction. -/
theorem exists_slopes {n : ℕ} {V : Type*} [Field V] [Fintype V]
    (h : n < Fintype.card V) : ∃ α : Fin n → V, Function.Injective α ∧ ∀ j, α j ≠ 0 := by
  classical
  have hc : Fintype.card {x : V // x ≠ 0} = Fintype.card V - 1 := by
    simp [Fintype.card_subtype_compl]
  have hle : Fintype.card (Fin n) ≤ Fintype.card {x : V // x ≠ 0} := by
    rw [Fintype.card_fin, hc]
    omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hle
  exact ⟨fun j => (e j).val, fun _ _ h => e.injective (Subtype.ext h), fun j => (e j).property⟩


/-- Exact support size in equation (6). -/
theorem card_keys {n : ℕ} (hn : 2 ≤ n) {V : Type*} [Fintype V] [DecidableEq V]
    (T : Finset V) : (OddSources.keys (central n) T).card = n * Fintype.card V - T.card := by
  rw [OddSources.card_keys, card_central]
  have hs : Fintype.card (Branch n) - (n - 1) = n := by
    simp only [Branch, Fintype.card_sum, Fintype.card_fin]
    omega
  rw [hs]
  have ht := card_le_univ T
  have hsub : Fintype.card V - T.card + T.card = Fintype.card V := Nat.sub_add_cancel ht
  have he : (n - 1) * T.card + n * (Fintype.card V - T.card) + T.card =
      n * Fintype.card V := by
    have hn1 : n - 1 + 1 = n := by omega
    nlinarith
  omega

/-- Lower and upper support bounds of Theorem 4.1, item 2. -/
theorem card_keys_bounds {n : ℕ} (hn : 2 ≤ n) {V : Type*} [Fintype V]
    [DecidableEq V] (T : Finset V) :
    (n - 1) * Fintype.card V ≤ (OddSources.keys (central n) T).card ∧
      (OddSources.keys (central n) T).card ≤ n * Fintype.card V := by
  rw [card_keys hn]
  have ht := card_le_univ T
  have he : n * Fintype.card V = (n - 1) * Fintype.card V + Fintype.card V := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    ring
  omega

/-- Exact key-space cardinality, counting distinct central keys separately. -/
theorem card_key {n : ℕ} (hn : 2 ≤ n) (V : Type*) [Fintype V] :
    Fintype.card (Key n V) = (2 * n - 1) * Fintype.card V := by
  rw [Fintype.card_prod, card_branch hn]

/-- Every source is flat on exactly the advertised support. -/
theorem source_flat {n : ℕ} (hn : 2 ≤ n) {V : Type*}
    [Fintype V] [DecidableEq V] [Nonempty V] (T : Finset V) :
    source hn T = PMF.uniformOfFinset (OddSources.keys (central n) T)
      (OddSources.keys_nonempty _ (central_nonempty hn) (side_nonempty hn) T) := rfl

private theorem sum_keys {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (T : Finset V) (f : Key n V → ℝ) :
    (∑ k ∈ OddSources.keys (central n) T, f k) =
      ∑ i : V, if i ∈ T then ∑ c : Fin (n - 1), f (.inl c, i)
        else ∑ p : Fin n, f (.inr p, i) := by
  rw [OddSources.sum_keys]
  simp [central]

private theorem sum_share {n : ℕ} {V : Type*} [Field V] [Fintype V]
    [DecidableEq V] (T : Finset V) (α : Fin n → V) (hα : ∀ j, α j ≠ 0)
    (j : Fin n) (m : V) (score : Share V → ℝ) :
    (∑ k ∈ OddSources.keys (central n) T, score (share α j m k)) =
      (n - 1 : ℕ) * (∑ x : V, score (.inl x)) +
        ∑ i ∈ univ \ T, score (.inr i) := by
  rw [sum_keys]
  have hs (i : V) :
      (∑ p : Fin n, score (share α j m (.inr p, i))) =
        (n - 1 : ℕ) * score (.inl (α j * i + m)) + score (.inr i) := by
    rw [← sum_erase_add _ _ (mem_univ j)]
    simp only [share, ite_true]
    have he : (∑ p ∈ univ.erase j,
        score (if j = p then .inr i else .inl (α j * i + m))) =
        (n - 1 : ℕ) * score (.inl (α j * i + m)) := by
      have hh : ∀ p ∈ univ.erase j, j ≠ p := by
        intro p hp heq
        exact (mem_erase.mp hp).1 heq.symm
      rw [sum_congr rfl (fun p hp => ite_eq_right (hh p hp) |> congrArg score)]
      simp only [sum_const, card_erase_of_mem (mem_univ j), card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    rw [he]
  have hp := Equiv.sum_comp ((Equiv.mulLeft₀ (α j) (hα j)).trans (Equiv.addRight m))
    (fun x : V => score (.inl x))
  change (∑ i : V, score (.inl (α j * i + m))) = _ at hp
  calc
    _ = (n - 1 : ℕ) * (∑ i : V, score (.inl (α j * i + m))) +
        ∑ i ∈ univ \ T, score (.inr i) := by
      simp_rw [hs]
      simp only [share, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [mul_sum, show univ \ T = univ.filter (fun i : V => i ∉ T) by ext; simp,
        sum_filter, ← sum_add_distrib]
      apply sum_congr rfl
      intro i _
      by_cases hi : i ∈ T <;> simp [hi]
    _ = _ := by rw [hp]

/-- Lemma 4.3: each party's actual share law is independent of the message, for every source. -/
theorem singleton_privacy {n : ℕ} (hn : 2 ≤ n) {V : Type*} [Field V] [Fintype V]
    [DecidableEq V] (α : Fin n → V) (hα : ∀ j, α j ≠ 0) (j : Fin n)
    (T : Finset V) (m m' : V) :
    (source hn T).map (share α j m) = (source hn T).map (share α j m') := by
  classical
  ext x
  apply (ENNReal.toReal_eq_toReal_iff' ((source hn T).map (share α j m) |>.apply_ne_top x)
    ((source hn T).map (share α j m') |>.apply_ne_top x)).mp
  have h : (∑ k ∈ OddSources.keys (central n) T,
      (if share α j m k = x then (1 : ℝ) else 0)) =
      ∑ k ∈ OddSources.keys (central n) T,
        (if share α j m' k = x then (1 : ℝ) else 0) := by
    exact (sum_share T α hα j m (fun y => if y = x then 1 else 0)).trans
      (sum_share T α hα j m' (fun y => if y = x then 1 else 0)).symm
  have h' := congrArg (fun z : ℝ => z / (OddSources.keys (central n) T).card) h
  rw [PMF.map_apply_toReal, PMF.map_apply_toReal]
  simpa only [source, ← OddSources.source_expect (central n) (central_nonempty hn)
    (side_nonempty hn), mul_ite, mul_one, mul_zero, eq_comm] using h'


/-- The complete joint view of a coalition; party identities remain part of its coordinates. -/
@[expose] def view {n : ℕ} {V : Type*} [Field V] (α : Fin n → V)
    (J : Finset (Fin n)) (m : V) (k : Key n V) : J → Share V :=
  fun j => share α j.val m k

/-- Perfect correctness for every authorized coalition, not just pairs. -/
theorem authorized_correctness {n : ℕ} {V : Type*} [Field V] {α : Fin n → V}
    (hα : Function.Injective α) (J : Finset (Fin n)) (hJ : 2 ≤ J.card) :
    ∃ rec : (J → Share V) → V, ∀ m k, rec (view α J m k) = m := by
  obtain ⟨j, hj, l, hl, hjl⟩ := Finset.one_lt_card.mp (by omega : 1 < J.card)
  refine ⟨fun z => reconstruct (α j) (α l) (z ⟨j, hj⟩) (z ⟨l, hl⟩), ?_⟩
  intro m k
  exact reconstruct_share hα hjl m k

/-- Perfect joint privacy for every unauthorized coalition, including the empty coalition. -/
theorem unauthorized_privacy {n : ℕ} (hn : 2 ≤ n) {V : Type*} [Field V] [Fintype V]
    [DecidableEq V] (α : Fin n → V) (hα : ∀ j, α j ≠ 0)
    (J : Finset (Fin n)) (hJ : J.card < 2) (T : Finset V) (m m' : V) :
    (source hn T).map (view α J m) = (source hn T).map (view α J m') := by
  classical
  have he : ∃ j : Fin n, ∀ p ∈ J, p = j := by
    by_cases h : J.Nonempty
    · obtain ⟨j, hj⟩ := h
      exact ⟨j, fun p hp => (Finset.card_le_one.mp (by omega : J.card ≤ 1)) p hp j hj⟩
    · exact ⟨⟨0, by omega⟩, fun p hp => False.elim (h ⟨p, hp⟩)⟩
  obtain ⟨j, hj⟩ := he
  have hv (m : V) : view α J m = (fun s : Share V => fun _ : J => s) ∘ share α j m := by
    funext k p
    simp only [view, Function.comp_apply, hj p.val p.property]
  rw [hv, hv, ← PMF.map_comp, ← PMF.map_comp, singleton_privacy hn α hα j T m m']

/-- The exact single-share mass formula of Lemma 4.3, expressed as normalized scores.
In particular, untagged values have multiplicity `n - 1`; tagged indices outside `T` have one. -/
theorem share_expect {n : ℕ} (hn : 2 ≤ n) {V : Type*} [Field V] [Fintype V]
    [DecidableEq V] (α : Fin n → V) (hα : ∀ j, α j ≠ 0) (j : Fin n)
    (T : Finset V) (m : V) (score : Share V → ℝ) :
    (∑ k, (source hn T k).toReal * score (share α j m k)) =
      ((n - 1 : ℕ) * (∑ x : V, score (.inl x)) +
        ∑ i ∈ univ \ T, score (.inr i)) / (OddSources.keys (central n) T).card := by
  rw [source, OddSources.source_expect (central n) (central_nonempty hn) (side_nonempty hn),
    sum_share T α hα]

/-- Every ordinary share value has exactly the probability asserted in Lemma 4.3. -/
theorem share_apply_inl {n : ℕ} (hn : 2 ≤ n) {V : Type*} [Field V] [Fintype V]
    [DecidableEq V] (α : Fin n → V) (hα : ∀ j, α j ≠ 0) (j : Fin n)
    (T : Finset V) (m x : V) :
    (((source hn T).map (share α j m)) (.inl x)).toReal =
      (n - 1 : ℕ) / (OddSources.keys (central n) T).card := by
  classical
  have h := share_expect hn α hα j T m (fun z => if z = .inl x then 1 else 0)
  rw [PMF.map_apply_toReal]
  simpa only [mul_ite, mul_one, mul_zero, Sum.inl.injEq, reduceCtorEq,
    ite_false, sum_const_zero, add_zero, sum_ite_eq', sum_ite_eq, mem_univ, ite_true,
    eq_comm] using h

/-- A tagged index has mass `1/Z_T` outside `T`, and zero inside `T`. -/
theorem share_apply_inr {n : ℕ} (hn : 2 ≤ n) {V : Type*} [Field V] [Fintype V]
    [DecidableEq V] (α : Fin n → V) (hα : ∀ j, α j ≠ 0) (j : Fin n)
    (T : Finset V) (m i : V) :
    (((source hn T).map (share α j m)) (.inr i)).toReal =
      (if i ∈ T then 0 else 1) / (OddSources.keys (central n) T).card := by
  classical
  have h := share_expect hn α hα j T m (fun z => if z = .inr i then 1 else 0)
  rw [PMF.map_apply_toReal]
  simpa only [mul_ite, mul_one, mul_zero, Sum.inr.injEq, reduceCtorEq,
    ite_false, sum_const_zero, mul_zero, zero_add, sum_ite_eq', sum_ite_eq, mem_sdiff,
    mem_univ, true_and, ite_not, eq_comm] using h

/-- The min-entropy bound before substituting binary field cardinality. -/
theorem source_minEntropy {n : ℕ} (hn : 2 ≤ n) {V : Type*} [Fintype V]
    [DecidableEq V] [Nonempty V] (T : Finset V) :
    Real.logb 2 (((n - 1) * Fintype.card V : ℕ) : ℝ) ≤ PMF.minEntropy (source hn T) := by
  rw [source, OddSources.minEntropy_source]
  apply Real.logb_le_logb_of_le (by norm_num)
  · exact_mod_cast Nat.mul_pos (by omega : 0 < n - 1) (Fintype.card_pos (α := V))
  · exact_mod_cast (card_keys_bounds hn T).1

/-- All branch hypotheses for the generic parity lower bound and balanced-index upper bound. -/
theorem extraction_parameters {n : ℕ} (hn : 2 ≤ n) :
    (central n).Nonempty ∧ (univ \ central n).Nonempty ∧
      (central n).card = n - 1 ∧ (univ \ central n).card = n ∧
      Odd (Fintype.card (Branch n)) ∧
      (univ \ central n).card = (central n).card + 1 := by
  refine ⟨central_nonempty hn, side_nonempty hn, card_central n, card_side n, ?_, ?_⟩
  · rw [card_branch hn]
    exact ⟨n - 1, by omega⟩
  · rw [card_side, card_central]
    omega

/-- Binary fields have the even index cardinality needed for a balanced extractor. -/
theorem binary_index_parameters (n b : ℕ) (hn : 2 ≤ n) (hb : n < 2 ^ b) :
    let : Fintype (GaloisField 2 b) := Fintype.ofFinite _
    Fintype.card (GaloisField 2 b) = 2 ^ b ∧ Even (Fintype.card (GaloisField 2 b)) ∧
      ∃ α : Fin n → GaloisField 2 b, Function.Injective α ∧ ∀ j, α j ≠ 0 := by
  classical
  let : Fintype (GaloisField 2 b) := Fintype.ofFinite _
  have hb0 : b ≠ 0 := by intro h; simp [h] at hb; omega
  have hc : Fintype.card (GaloisField 2 b) = 2 ^ b := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 b hb0]
  refine ⟨hc, ?_, exists_slopes (hc ▸ hb)⟩
  rw [hc]
  refine ⟨2 ^ (b - 1), ?_⟩
  rw [← Nat.mul_two, ← pow_succ]
  congr 1
  omega


/-- Literal bit shares obtained by fixed bijections on messages and tagged field elements. -/
@[expose] def bitShare {n b : ℕ} {V : Type*} [Field V] (α : Fin n → V)
    (em : V ≃ (Fin b → Bool)) (es : Share V ≃ (Fin (b + 1) → Bool))
    (j : Fin n) (m : Fin b → Bool) (k : Key n V) : Fin (b + 1) → Bool :=
  es (share α j (em.symm m) k)

/-- A coalition's complete view of the literal encoded shares. -/
@[expose] def bitView {n b : ℕ} {V : Type*} [Field V] (α : Fin n → V)
    (em : V ≃ (Fin b → Bool)) (es : Share V ≃ (Fin (b + 1) → Bool))
    (J : Finset (Fin n)) (m : Fin b → Bool) (k : Key n V) : J → (Fin (b + 1) → Bool) :=
  fun j => bitShare α em es j.val m k

/-- Encoding preserves authorized reconstruction on all ambient keys. -/
theorem bit_authorized_correctness {n b : ℕ} {V : Type*} [Field V]
    {α : Fin n → V} (hα : Function.Injective α)
    (em : V ≃ (Fin b → Bool)) (es : Share V ≃ (Fin (b + 1) → Bool))
    (J : Finset (Fin n)) (hJ : 2 ≤ J.card) :
    ∃ rec : (J → (Fin (b + 1) → Bool)) → (Fin b → Bool),
      ∀ m k, rec (bitView α em es J m k) = m := by
  obtain ⟨rec, hr⟩ := authorized_correctness hα J hJ
  refine ⟨fun z => em (rec (fun j => es.symm (z j))), ?_⟩
  intro m k
  have hv : (fun j => es.symm (bitView α em es J m k j)) = view α J (em.symm m) k := by
    funext j
    exact es.symm_apply_apply _
  change em (rec (fun j => es.symm (bitView α em es J m k j))) = m
  rw [hv, hr, em.apply_symm_apply]

/-- Encoding preserves the joint law of every unauthorized coalition. -/
theorem bit_unauthorized_privacy {n b : ℕ} (hn : 2 ≤ n) {V : Type*}
    [Field V] [Fintype V] [DecidableEq V] (α : Fin n → V) (hα : ∀ j, α j ≠ 0)
    (em : V ≃ (Fin b → Bool)) (es : Share V ≃ (Fin (b + 1) → Bool))
    (J : Finset (Fin n)) (hJ : J.card < 2) (T : Finset V) (m m' : Fin b → Bool) :
    (source hn T).map (bitView α em es J m) =
      (source hn T).map (bitView α em es J m') := by
  have h := congrArg (fun p : PMF (J → Share V) => p.map (fun z j => es (z j)))
    (unauthorized_privacy hn α hα J hJ T (em.symm m) (em.symm m'))
  change (source hn T).map (fun k (j : J) => es (share α j.val (em.symm m) k)) =
    (source hn T).map (fun k (j : J) => es (share α j.val (em.symm m') k))
  simpa only [PMF.map_comp, Function.comp_def, view] using h

open scoped Classical in
/-- The actual construction and items 1–2 of Theorem 4.1 at every permitted `n,b`.
The source laws are unchanged by message/share encoding. Extraction items 3–4 are separate
from this intermediate theorem; `binary_theorem4_1` includes all four items. The generic
complementary-branch hypotheses are discharged by `extraction_parameters` and
`binary_index_parameters`. -/
theorem binary_construction (n b : ℕ) (hn : 2 ≤ n) (hb : n < 2 ^ b) :
    let V := GaloisField 2 b
    let : Fintype V := Fintype.ofFinite _
    ∃ (em : V ≃ (Fin b → Bool)) (es : Share V ≃ (Fin (b + 1) → Bool))
      (α : Fin n → V), Function.Injective α ∧ (∀ j, α j ≠ 0) ∧
      Fintype.card (Key n V) = (2 * n - 1) * 2 ^ b ∧
      (∀ (J : Finset (Fin n)), 2 ≤ J.card →
        ∃ rec : (J → (Fin (b + 1) → Bool)) → (Fin b → Bool),
          ∀ m k, rec (bitView α em es J m k) = m) ∧
      (∀ (J : Finset (Fin n)), J.card < 2 → ∀ T m m',
        (source hn T).map (bitView α em es J m) =
          (source hn T).map (bitView α em es J m')) ∧
      (∀ T : Finset V, (n - 1) * 2 ^ b ≤ (OddSources.keys (central n) T).card ∧
        (OddSources.keys (central n) T).card ≤ n * 2 ^ b) ∧
      (∀ T : Finset V, (b : ℝ) + Real.logb 2 (n - 1 : ℕ) ≤
        PMF.minEntropy (source hn T)) := by
  classical
  let V := GaloisField 2 b
  let : Fintype V := Fintype.ofFinite _
  obtain ⟨hc, _, α, hα, hα0⟩ := binary_index_parameters n b hn hb
  change Fintype.card V = 2 ^ b at hc
  let em : V ≃ (Fin b → Bool) := Fintype.equivOfCardEq (by simpa using hc)
  let es : Share V ≃ (Fin (b + 1) → Bool) := Fintype.equivOfCardEq (by
    simp only [Share, Fintype.card_sum, hc, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, pow_succ]
    omega)
  refine ⟨em, es, α, hα, hα0, ?_, ?_, ?_, ?_, ?_⟩
  · rw [card_key hn, hc]
  · exact fun J hJ => bit_authorized_correctness hα em es J hJ
  · exact fun J hJ T m m' => bit_unauthorized_privacy hn α hα0 em es J hJ T m m'
  · intro T
    have hk := card_keys_bounds (V := V) hn T
    rw [hc] at hk
    exact hk
  · intro T
    have he := source_minEntropy hn T
    rw [Nat.cast_mul, hc, Nat.cast_pow, Nat.cast_ofNat,
      Real.logb_mul (by exact_mod_cast (by omega : n - 1 ≠ 0)) (by positivity),
      Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at he
    simpa only [add_comm] using he



/-- The generic odd-branch constant is exactly the constant in Theorem 4.1. -/
theorem extraction_constant {n : ℕ} (hn : 2 ≤ n) :
    (1 : ℝ) / (2 * Fintype.card (Branch n)) = 1 / (4 * (n : ℝ) - 2) := by
  rw [card_branch hn, Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  congr 1
  ring

/-- Theorem 4.1, item 3: every extractor of every positive output length fails on an actual
allowed source, without computational restrictions on the extractor. -/
theorem no_string_extractor {n : ℕ} (hn : 2 ≤ n) {V : Type*} [Fintype V]
    [DecidableEq V] [Nonempty V] (ℓ : ℕ) (hℓ : 0 < ℓ)
    (ext : Key n V → (Fin ℓ → Bool)) :
    ∃ T : Finset V, (1 : ℝ) / (4 * (n : ℝ) - 2) ≤
      dist ((source hn T).map ext) (PMF.uniformOfFintype (Fin ℓ → Bool)) := by
  have h := OddSources.no_string_extractor (central n) (central_nonempty hn)
    (side_nonempty hn) (extraction_parameters hn).2.2.2.2.1 ℓ hℓ ext
  simpa only [source, extraction_constant hn] using h

/-- Theorem 4.1, item 4: a balanced function of the actual index achieves the optimal bound
on all sources, with equality on one source. There is no assumed balancing witness. -/
theorem exists_tight_index_extractor {n : ℕ} (hn : 2 ≤ n) {V : Type*} [Fintype V]
    [DecidableEq V] [Nonempty V] (heven : Even (Fintype.card V)) :
    ∃ g : V → Bool,
      (univ.filter fun i => g i = true).card = (univ.filter fun i => g i = false).card ∧
      (∀ T, dist ((source hn T).map (fun k => g k.2))
        (PMF.uniformOfFintype Bool) ≤ (1 : ℝ) / (4 * (n : ℝ) - 2)) ∧
      (∃ T, dist ((source hn T).map (fun k => g k.2))
        (PMF.uniformOfFintype Bool) = (1 : ℝ) / (4 * (n : ℝ) - 2)) := by
  have hclasses : (central n).card = n - 1 ∧ (univ \ central n).card = (n - 1) + 1 := by
    rw [card_central, card_side]
    omega
  have h := OddSources.exists_tight_index_extractor (central n) (central_nonempty hn)
    (side_nonempty hn) (n - 1) (Or.inl hclasses) heven
  simpa only [source, extraction_constant hn] using h

open scoped Classical in
/-- Full Theorem 4.1 of STOC submission 886, at every `n ≥ 2` and `2^b > n`.
A single fixed scheme on literal message/share bits has perfect authorized correctness and
joint unauthorized privacy for the entire actual source class. All four numbered items are
included: exact key/share alphabets, flat supports and entropy, failure of every positive-length
extractor, and an index-only bit extractor attaining the bound. No unproved linking premise is
assumed. Fixed encoding bijections carry no bit-level runtime claim. -/
theorem binary_theorem4_1 (n b : ℕ) (hn : 2 ≤ n) (hb : n < 2 ^ b) :
    let V := GaloisField 2 b
    let : Fintype V := Fintype.ofFinite _
    ∃ (em : V ≃ (Fin b → Bool)) (es : Share V ≃ (Fin (b + 1) → Bool))
      (α : Fin n → V), Function.Injective α ∧ (∀ j, α j ≠ 0) ∧
      Fintype.card (Key n V) = (2 * n - 1) * 2 ^ b ∧
      (∀ (J : Finset (Fin n)), 2 ≤ J.card →
        ∃ rec : (J → (Fin (b + 1) → Bool)) → (Fin b → Bool),
          ∀ m k, rec (bitView α em es J m k) = m) ∧
      (∀ (J : Finset (Fin n)), J.card < 2 → ∀ T m m',
        (source hn T).map (bitView α em es J m) =
          (source hn T).map (bitView α em es J m')) ∧
      (∀ T : Finset V, source hn T = PMF.uniformOfFinset (OddSources.keys (central n) T)
          (OddSources.keys_nonempty _ (central_nonempty hn) (side_nonempty hn) T) ∧
        (n - 1) * 2 ^ b ≤ (OddSources.keys (central n) T).card ∧
        (OddSources.keys (central n) T).card ≤ n * 2 ^ b) ∧
      (∀ T : Finset V, (b : ℝ) + Real.logb 2 (n - 1 : ℕ) ≤
        PMF.minEntropy (source hn T)) ∧
      (∀ ℓ : ℕ, 0 < ℓ → ∀ ext : Key n V → (Fin ℓ → Bool),
        ∃ T, (1 : ℝ) / (4 * (n : ℝ) - 2) ≤
          dist ((source hn T).map ext) (PMF.uniformOfFintype (Fin ℓ → Bool))) ∧
      (∃ g : V → Bool,
        (∀ T, dist ((source hn T).map (fun k => g k.2))
          (PMF.uniformOfFintype Bool) ≤ (1 : ℝ) / (4 * (n : ℝ) - 2)) ∧
        (∃ T, dist ((source hn T).map (fun k => g k.2))
          (PMF.uniformOfFintype Bool) = (1 : ℝ) / (4 * (n : ℝ) - 2))) := by
  classical
  let V := GaloisField 2 b
  let : Fintype V := Fintype.ofFinite _
  obtain ⟨em, es, α, hα, hα0, hk, hr, hp, hs, he⟩ := binary_construction n b hn hb
  have hev : Even (Fintype.card V) := (binary_index_parameters n b hn hb).2.1
  obtain ⟨g, _, hu, ht⟩ := exists_tight_index_extractor hn hev
  exact ⟨em, es, α, hα, hα0, hk, hr, hp,
    fun T => ⟨source_flat hn T, (hs T).1, (hs T).2⟩, he,
    fun ℓ hℓ ext => no_string_extractor hn ℓ hℓ ext, g, hu, ht⟩

end Cslib.Crypto.Protocols.SecretSharing.ImperfectRandomness.TwoOutOfN
