/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Crypto.Protocols.SecretSharing.ImperfectRandomness.OddSources
public import Complexity.Crypto.Protocols.SecretSharing.ImperfectRandomness.ZeroSumPads
public import Mathlib.FieldTheory.Finite.GaloisField
public import Complexity.Probability.MinEntropy
import Mathlib.Tactic

/-!
# All-out-of-r sharing with imperfect randomness

The construction of STOC submission 886 [Aggarwal2026], Section 5, equations
(7)–(9), Theorem 5.1 and Lemmas 5.2–5.3 (PDF pp. 10–11). An active subset is
nonempty, the pads are the actual zero-sum pads on `V^n`, and the source is the
common `OddSources.source`, with odd active subsets at indices in `T`.

## Main definitions

* `source`, `share`, `reconstruct`: the source family and the tagged sharing scheme.
* `view`, `viewKeys`, `coalitionView`: complete joint observations and equation (9).
* `encodedShare`, `encodedReconstruct`: sharing on literal bit-string alphabets.

## Main results

* `reconstruct_shares`: correctness for every ambient key.
* `view_law`, `coalition_privacy`: the exact uniform view and all proper coalitions.
* `card_keys`, `source_minEntropy_at_bit_size`: exact support size and entropy.
* `binary_construction`: coefficients, encodings, correctness and privacy for every
  `r=n+1 ≥ 2`, `b ≥ r`, without assuming any desired pad or privacy properties.

Field operations have their algebraic meaning; fixed choices of bases and
coordinate bijections carry no bit-runtime assertion.
-/

public section

namespace Cslib.Crypto.Protocols.SecretSharing.ImperfectRandomness.AllOutOfR

open Finset

variable {V : Type*} {n : ℕ}

/-- Every nonempty set of active parties is an ambient branch. -/
abbrev Branch (n : ℕ) := {S : Finset (Fin (n + 1)) // S.Nonempty}

/-- A key is a nonempty active set and an actual pad index. -/
abbrev Key (V : Type*) (n : ℕ) := Branch n × Index V n

/-- The extra Boolean is the visible activation tag (`true` means active). -/
abbrev Share (V : Type*) := Bool × V

/-- The odd class used by the common complementary source family. -/
@[expose] def oddBranches (n : ℕ) : Finset (Branch n) :=
  univ.filter fun S => Odd S.val.card

/-- The activation pattern visible to all parties except `j`. -/
@[expose] def pattern (j : Fin (n + 1)) (S : Finset (Fin (n + 1))) : Finset (Others j) :=
  univ.filter fun i => i.val ∈ S

/-- Embed a visible pattern back into the complete party set. -/
@[expose] def liftPattern (j : Fin (n + 1)) (R : Finset (Others j)) :
    Finset (Fin (n + 1)) := R.image Subtype.val

@[simp] theorem mem_pattern (j : Fin (n + 1)) (S : Finset (Fin (n + 1)))
    (i : Others j) : i ∈ pattern j S ↔ i.val ∈ S := by simp [pattern]

@[simp] theorem mem_liftPattern (j : Fin (n + 1)) (R : Finset (Others j))
    (i : Others j) : i.val ∈ liftPattern j R ↔ i ∈ R := by
  simp [liftPattern, Subtype.val_injective.eq_iff]

@[simp] theorem omitted_not_mem_liftPattern (j : Fin (n + 1)) (R : Finset (Others j)) :
    j ∉ liftPattern j R := by
  simp only [liftPattern, mem_image, not_exists, not_and]
  exact fun i _ h => i.property h

/-- A visible pattern has the same cardinality after embedding. -/
theorem card_liftPattern (j : Fin (n + 1)) (R : Finset (Others j)) :
    (liftPattern j R).card = R.card := card_image_of_injective _ Subtype.val_injective

/-- Two full patterns with identical visible parts and parity are identical. -/
theorem eq_of_pattern_parity (j : Fin (n + 1)) {S S' : Finset (Fin (n + 1))}
    (h : pattern j S = pattern j S') (hp : Odd S.card ↔ Odd S'.card) : S = S' := by
  have he : S.erase j = S'.erase j := by
    ext i
    by_cases hi : i = j
    · simp [hi]
    · have hh := congrArg (fun R => (⟨i, hi⟩ : Others j) ∈ R) h
      simpa [hi, ne_comm] using (Iff.of_eq hh)
  have hj : j ∈ S ↔ j ∈ S' := by
    have hc := congrArg Finset.card he
    by_cases hs : j ∈ S <;> by_cases hs' : j ∈ S'
    · tauto
    · rw [card_erase_of_mem hs, erase_eq_of_notMem hs'] at hc
      have hspos := card_pos.mpr ⟨j, hs⟩
      have heq : S.card = S'.card + 1 := by omega
      rw [heq, Nat.odd_add_one] at hp
      tauto
    · rw [erase_eq_of_notMem hs, card_erase_of_mem hs'] at hc
      have hspos := card_pos.mpr ⟨j, hs'⟩
      have heq : S'.card = S.card + 1 := by omega
      rw [heq, Nat.odd_add_one] at hp
      tauto
    · tauto
  ext i
  by_cases hi : i = j
  · simpa [hi] using hj
  · have hh := congrArg (fun R => i ∈ R) he
    simpa [hi, ne_comm] using (Iff.of_eq hh)

/-- Complete a visible pattern with prescribed parity by choosing the omitted tag. -/
@[expose] def completePattern (j : Fin (n + 1)) (R : Finset (Others j)) (odd : Bool) :
    Finset (Fin (n + 1)) :=
  if (Odd R.card ↔ odd = true) then liftPattern j R else insert j (liftPattern j R)

/-- Completing a pattern does not change its visible part. -/
@[simp] theorem pattern_completePattern (j : Fin (n + 1)) (R : Finset (Others j))
    (odd : Bool) : pattern j (completePattern j R odd) = R := by
  ext i
  simp only [mem_pattern, completePattern]
  split_ifs <;> simp [i.property]

/-- Completion has exactly the specified parity. -/
@[simp] theorem odd_completePattern (j : Fin (n + 1)) (R : Finset (Others j))
    (odd : Bool) : Odd (completePattern j R odd).card ↔ odd = true := by
  simp only [completePattern]
  split_ifs with h
  · simpa only [card_liftPattern] using h
  · rw [card_insert_of_notMem (omitted_not_mem_liftPattern j R), card_liftPattern,
      Nat.odd_add_one]
    tauto

/-- Completion is nonempty exactly when it can be an ambient branch. -/
theorem completePattern_nonempty (j : Fin (n + 1)) (R : Finset (Others j))
    (odd : Bool) (h : R.Nonempty ∨ odd = true) : (completePattern j R odd).Nonempty := by
  rcases h with h | h
  · obtain ⟨i, hi⟩ := h
    have := (mem_pattern j (completePattern j R odd) i).mp
      (by simpa only [pattern_completePattern] using hi)
    exact ⟨i, this⟩
  · have ho := (odd_completePattern j R odd).mpr h
    by_contra he
    rw [not_nonempty_iff_eq_empty.mp he, card_empty] at ho
    exact (by decide : ¬Odd 0) ho

/-- The odd branches are in bijection with all visible patterns. -/
theorem card_oddBranches (n : ℕ) : (oddBranches n).card = 2 ^ n := by
  classical
  let j := Fin.last n
  have hcard : (oddBranches n).card = (univ : Finset (Finset (Others j))).card := by
    apply card_bij (fun S _ => pattern j S.val)
    · simp
    · intro S hS S' hS' h
      apply Subtype.ext
      apply eq_of_pattern_parity j h
      simpa only [oddBranches, mem_filter, mem_univ, true_and] using
        (show Odd S.val.card ↔ Odd S'.val.card from
          ⟨fun _ => (mem_filter.mp hS').2, fun _ => (mem_filter.mp hS).2⟩)
    · intro R _
      let S : Branch n := ⟨completePattern j R true,
        completePattern_nonempty j R true (Or.inr rfl)⟩
      exact ⟨S, by simp [oddBranches, S], pattern_completePattern j R true⟩
  rw [hcard, card_univ, Fintype.card_finset, card_others]

/-- There are exactly `2^(n+1)-1` nonempty subsets of the parties. -/
theorem card_branch (n : ℕ) : Fintype.card (Branch n) = 2 ^ (n + 1) - 1 := by
  classical
  simp [Branch, Finset.nonempty_iff_ne_empty, Fintype.card_subtype_compl]

/-- The even class has one fewer member than the odd class. -/
theorem card_evenBranches (n : ℕ) : (univ \ oddBranches n).card = 2 ^ n - 1 := by
  rw [card_sdiff_of_subset (subset_univ _), card_univ, card_branch, card_oddBranches,
    pow_succ]
  have := Nat.one_le_two_pow (n := n)
  omega

/-- Odd branches exist, including a singleton active set. -/
theorem oddBranches_nonempty (n : ℕ) : (oddBranches n).Nonempty := by
  exact ⟨⟨{Fin.last n}, singleton_nonempty _⟩, by simp [oddBranches]⟩

/-- A pair of active parties witnesses a nonempty even branch. -/
theorem evenBranches_nonempty (hn : 1 ≤ n) : (univ \ oddBranches n).Nonempty := by
  let a : Fin (n + 1) := ⟨0, by omega⟩
  have ha : a ≠ Fin.last n := by simp [a, Fin.ext_iff]; omega
  exact ⟨⟨{a, Fin.last n}, by simp⟩, by simp [oddBranches, ha]⟩

/-- The actual sources from equation (8), without extra dealer randomness. -/
@[expose] noncomputable def source [Fintype V] [DecidableEq V] [Nonempty V]
    (hn : 1 ≤ n) (T : Finset (Index V n)) : PMF (Key V n) :=
  OddSources.source (oddBranches n) (oddBranches_nonempty n) (evenBranches_nonempty hn) T

/-- Equation (7): inactive parties get their tagged pad; active parties add `γ_j m`. -/
@[expose] def share [Field V] (γ : Fin (n + 1) → V) (m : V) (k : Key V n)
    (j : Fin (n + 1)) : Share V :=
  (decide (j ∈ k.1.val), pad k.2 j + if j ∈ k.1.val then γ j * m else 0)

/-- Reconstruction reads the active set from the tags and divides the value sum by
its coefficient sum. -/
@[expose] def reconstruct [Field V] (γ : Fin (n + 1) → V)
    (x : Fin (n + 1) → Share V) : V :=
  (∑ j, (x j).2) / (∑ j ∈ univ.filter (fun j => (x j).1), γ j)

/-- The coefficient of a nonempty subset of an independent family cannot vanish. -/
theorem coefficient_ne_zero [Field V] [Algebra (ZMod 2) V]
    {γ : Fin (n + 1) → V} (hγ : LinearIndependent (ZMod 2) γ)
    (S : Branch n) : ∑ j ∈ S.val, γ j ≠ 0 := by
  intro h
  obtain ⟨j, hj⟩ := S.property
  have h' : ∑ i ∈ S.val, (1 : ZMod 2) • γ i = 0 := by simpa using h
  have hz := linearIndependent_iff'.mp hγ S.val (fun _ => 1) h' j hj
  exact one_ne_zero hz

/-- Lemma 5.2's sum identity, on every ambient key. -/
theorem sum_share [Field V] (γ : Fin (n + 1) → V) (m : V) (k : Key V n) :
    (∑ j, (share γ m k j).2) = (∑ j ∈ k.1.val, γ j) * m := by
  simp only [share, sum_add_distrib, sum_pad, zero_add]
  rw [← sum_filter, ← sum_mul]
  congr 2
  ext j
  simp

/-- All parties reconstruct for every ambient key, not merely source-supported keys. -/
theorem reconstruct_shares [Field V] [Algebra (ZMod 2) V]
    {γ : Fin (n + 1) → V} (hγ : LinearIndependent (ZMod 2) γ)
    (m : V) (k : Key V n) : reconstruct γ (share γ m k) = m := by
  have hs : univ.filter (fun j => (share γ m k j).1) = k.1.val := by
    ext j
    simp [share]
  rw [reconstruct, sum_share, hs, mul_div_cancel_left₀ _ (coefficient_ne_zero hγ k.1)]

/-- A joint view consists of the observed active set and all observed values. -/
abbrev View (V : Type*) {n : ℕ} (j : Fin (n + 1)) :=
  Finset (Others j) × (Others j → V)

/-- Joint observation of every party except `j`. This records every share and tag. -/
@[expose] def view [Field V] (γ : Fin (n + 1) → V) (m : V) (j : Fin (n + 1))
    (k : Key V n) : View V j :=
  (pattern j k.1.val, fun i => (share γ m k i.val).2)

/-- A nonempty activation set invisible to the coalition is exactly the omitted singleton. -/
theorem pattern_eq_empty_iff (j : Fin (n + 1)) (S : Branch n) :
    pattern j S.val = ∅ ↔ S.val = {j} := by
  constructor
  · intro h
    apply subset_antisymm
    · intro i hi
      by_cases hij : i = j
      · simp [hij]
      · have hm : (⟨i, hij⟩ : Others j) ∈ pattern j S.val := by simpa using hi
        rw [h] at hm
        exact False.elim (notMem_empty _ hm)
    · obtain ⟨i, hi⟩ := S.property
      have hij : i = j := by
        by_contra hij
        have hm : (⟨i, hij⟩ : Others j) ∈ pattern j S.val := by simpa using hi
        rw [h] at hm
        exact notMem_empty _ hm
      simpa [hij] using hi
  · intro h
    ext i
    simp [h, i.property]

/-- A supported key is uniquely determined by the entire joint view. -/
theorem view_injective_on [Field V] [Fintype V] [DecidableEq V]
    (γ : Fin (n + 1) → V) (m : V) (j : Fin (n + 1)) (T : Finset (Index V n)) :
    Set.InjOn (view γ m j) (OddSources.keys (oddBranches n) T) := by
  intro k hk k' hk' h
  have hp : pattern j k.1.val = pattern j k'.1.val := congrArg Prod.fst h
  have hu : k.2 = k'.2 := by
    apply padProjection_injective j
    funext i
    have hm : i.val ∈ k.1.val ↔ i.val ∈ k'.1.val := by
      simpa only [mem_pattern] using
        Iff.of_eq (congrArg (fun R => i ∈ R) hp)
    have hz := congrFun (congrArg Prod.snd h) i
    simp only [view, share] at hz
    by_cases hi : i.val ∈ k.1.val
    · have hi' := hm.mp hi
      simpa [hi, hi', padProjection] using hz
    · have hi' : i.val ∉ k'.1.val := fun h' => hi (hm.mpr h')
      simpa [hi, hi', padProjection] using hz
  have hs : k.1 = k'.1 := by
    apply Subtype.ext
    apply eq_of_pattern_parity j hp
    have ha := OddSources.mem_keys (oddBranches n) T k |>.mp hk
    have ha' := OddSources.mem_keys (oddBranches n) T k' |>.mp hk'
    simp only [oddBranches, mem_filter, mem_univ, true_and] at ha ha'
    exact ha.trans ((by rw [hu] : k.2 ∈ T ↔ k'.2 ∈ T).trans ha'.symm)
  exact Prod.ext hs hu

/-- Exactly the message-independent support in equation (9). -/
@[expose] def viewKeys [Field V] [Fintype V] [DecidableEq V]
    (j : Fin (n + 1)) (T : Finset (Index V n)) : Finset (View V j) :=
  univ.filter fun x => x.1.Nonempty ∨
    (x.1 = ∅ ∧ x.2 ∈ T.image (padProjection j))

/-- A source-supported view belongs to equation (9). -/
theorem view_mem_viewKeys [Field V] [Fintype V] [DecidableEq V]
    (γ : Fin (n + 1) → V) (m : V) (j : Fin (n + 1)) (T : Finset (Index V n))
    (k : Key V n) (hk : k ∈ OddSources.keys (oddBranches n) T) :
    view γ m j k ∈ viewKeys j T := by
  by_cases hp : (pattern j k.1.val).Nonempty
  · simp [viewKeys, view, hp]
  · have he : pattern j k.1.val = ∅ := not_nonempty_iff_eq_empty.mp hp
    have hs := (pattern_eq_empty_iff j k.1).mp he
    have ht : k.2 ∈ T := by
      have hh := (OddSources.mem_keys (oddBranches n) T k).mp hk
      exact hh.mp (by simp [oddBranches, hs])
    have hz : (view γ m j k).2 = padProjection j k.2 := by
      funext i
      simp [view, share, hs, i.property, padProjection]
    simp only [viewKeys, mem_filter, mem_univ, true_and]
    exact Or.inr ⟨he, hz ▸ mem_image.mpr ⟨k.2, ht, rfl⟩⟩

/-- Every point of (9) is attained by a supported key, with no message constraint. -/
theorem exists_key_of_mem_viewKeys [Field V] [Fintype V] [DecidableEq V]
    (γ : Fin (n + 1) → V) (m : V) (j : Fin (n + 1)) (T : Finset (Index V n))
    (x : View V j) (hx : x ∈ viewKeys j T) :
    ∃ k ∈ OddSources.keys (oddBranches n) T, view γ m j k = x := by
  obtain ⟨u, hu⟩ := (padProjection_bijective (V := V) j).surjective
    (fun i => x.2 i - if i ∈ x.1 then γ i.val * m else 0)
  have hempty : x.1 = ∅ → u ∈ T := by
    intro he
    have hxp := (mem_filter.mp hx).2
    have hz : x.2 ∈ T.image (padProjection j) := by simpa [he] using hxp
    obtain ⟨v, hv, hveq⟩ := mem_image.mp hz
    have hueq : padProjection j u = padProjection j v := by
      rw [hu, hveq]
      simp [he]
    exact padProjection_injective j hueq ▸ hv
  have hnon : x.1.Nonempty ∨ decide (u ∈ T) = true := by
    by_cases he : x.1.Nonempty
    · exact Or.inl he
    · exact Or.inr (by simpa using hempty (not_nonempty_iff_eq_empty.mp he))
  let S : Branch n := ⟨completePattern j x.1 (decide (u ∈ T)),
    completePattern_nonempty j x.1 _ hnon⟩
  refine ⟨(S, u), ?_, ?_⟩
  · simp [OddSources.mem_keys, oddBranches, S]
  · apply Prod.ext
    · exact pattern_completePattern j x.1 _
    · funext i
      have hi : i.val ∈ S.val ↔ i ∈ x.1 := by
        rw [← mem_pattern, show pattern j S.val = x.1 from pattern_completePattern j x.1 _]
      have hui := congrFun hu i
      simp only [padProjection] at hui
      simp only [view, share]
      rw [hui, if_congr hi rfl rfl]
      exact sub_add_cancel _ _

/-- Equation (9) is the bijective image of the source support under the joint view. -/
theorem image_view_keys [Field V] [Fintype V] [DecidableEq V]
    (γ : Fin (n + 1) → V) (m : V) (j : Fin (n + 1)) (T : Finset (Index V n)) :
    (OddSources.keys (oddBranches n) T).image (view γ m j) = viewKeys j T := by
  ext x
  constructor
  · rintro hx
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hx
    exact view_mem_viewKeys γ m j T k hk
  · exact fun hx => mem_image.mpr (exists_key_of_mem_viewKeys γ m j T x hx)

/-- Equation (9) has a nonempty support for every source. -/
theorem viewKeys_nonempty [Field V] [Fintype V] [DecidableEq V]
    (hn : 1 ≤ n) (j : Fin (n + 1)) (T : Finset (Index V n)) :
    (viewKeys (V := V) j T).Nonempty := by
  rw [← image_view_keys (fun _ => (0 : V)) 0 j T]
  exact (OddSources.keys_nonempty (oddBranches n) (oddBranches_nonempty n)
    (evenBranches_nonempty hn) T).image _

open Cslib.Probability in
/-- Lemma 5.3 as an equality of actual PMFs: the whole joint view is uniform on (9). -/
theorem view_law [Field V] [Fintype V] [DecidableEq V]
    (hn : 1 ≤ n) (γ : Fin (n + 1) → V) (m : V) (j : Fin (n + 1))
    (T : Finset (Index V n)) :
    (source hn T).map (view γ m j) =
      PMF.uniformOfFinset (viewKeys j T) (viewKeys_nonempty hn j T) := by
  classical
  have hc : (viewKeys j T).card = (OddSources.keys (oddBranches n) T).card := by
    rw [← image_view_keys γ m j T]
    exact card_image_of_injOn (view_injective_on γ m j T)
  ext x
  rw [PMF.map_apply, tsum_fintype, PMF.uniformOfFinset_apply, hc]
  by_cases hx : x ∈ viewKeys j T
  · obtain ⟨k, hk, rfl⟩ := exists_key_of_mem_viewKeys γ m j T x hx
    rw [ite_eq_left hx, sum_eq_single k]
    · simp [source, OddSources.source, hk]
    · intro k' _ hne
      by_cases hk' : k' ∈ OddSources.keys (oddBranches n) T
      · have hneq : view γ m j k ≠ view γ m j k' := fun he =>
          hne (view_injective_on γ m j T hk' hk he.symm)
        simp [hneq]
      · simp [source, OddSources.source, hk']
    · simp
  · rw [ite_eq_right hx]
    apply sum_eq_zero
    intro k _
    by_cases hk : k ∈ OddSources.keys (oddBranches n) T
    · have hneq : x ≠ view γ m j k := fun he =>
        hx (he ▸ view_mem_viewKeys γ m j T k hk)
      simp [hneq]
    · simp [source, OddSources.source, hk]

/-- The joint view of any `n` parties is independent of the message. -/
theorem view_privacy [Field V] [Fintype V] [DecidableEq V]
    (hn : 1 ≤ n) (γ : Fin (n + 1) → V) (j : Fin (n + 1))
    (T : Finset (Index V n)) (m m' : V) :
    (source hn T).map (view γ m j) = (source hn T).map (view γ m' j) := by
  rw [view_law, view_law]

/-- Project a joint view to a coalition avoiding the omitted party. -/
@[expose] def projectView (j : Fin (n + 1)) (J : Finset (Fin (n + 1)))
    (hj : j ∉ J) (x : View V j) : J → Share V :=
  fun i => (decide ((⟨i.val, fun he => hj (he ▸ i.property)⟩ : Others j) ∈ x.1),
    x.2 ⟨i.val, fun he => hj (he ▸ i.property)⟩)

/-- A proper coalition observes every one of its shares and activation tags. -/
@[expose] def coalitionView [Field V] (γ : Fin (n + 1) → V) (m : V)
    (J : Finset (Fin (n + 1))) (k : Key V n) : J → Share V :=
  fun i => share γ m k i.val

/-- All proper coalitions have joint perfect privacy, by projection from Lemma 5.3. -/
theorem coalition_privacy [Field V] [Fintype V] [DecidableEq V]
    (hn : 1 ≤ n) (γ : Fin (n + 1) → V) (T : Finset (Index V n))
    (J : Finset (Fin (n + 1))) (hJ : J ≠ univ) (m m' : V) :
    (source hn T).map (coalitionView γ m J) =
      (source hn T).map (coalitionView γ m' J) := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, j ∉ J := by
    by_contra h
    apply hJ
    ext j
    simp only [mem_univ, iff_true]
    exact not_not.mp (not_exists.mp h j)
  have hp (m : V) : projectView j J hj ∘ view γ m j = coalitionView γ m J := by
    funext k i
    simp [projectView, view, coalitionView, share]
  have h := congrArg (fun p : PMF (View V j) => p.map (projectView j J hj))
    (view_privacy hn γ j T m m')
  simpa only [PMF.map_comp, hp] using h

/-- The exact key-set cardinality, before choosing a binary field. -/
theorem card_key [Fintype V] (n : ℕ) :
    Fintype.card (Key V n) = (2 ^ (n + 1) - 1) * Fintype.card V ^ n := by
  simp [Key, Index, card_branch]

/-- Equation (8): exact support size, not only upper and lower estimates. -/
theorem card_keys [Fintype V] [DecidableEq V] (T : Finset (Index V n)) :
    (OddSources.keys (oddBranches n) T).card =
      (2 ^ n - 1) * Fintype.card (Index V n) + T.card := by
  have he : Fintype.card (Branch n) - (oddBranches n).card = 2 ^ n - 1 := by
    rw [← card_evenBranches n, card_sdiff_of_subset (subset_univ _), card_univ]
  rw [OddSources.card_keys, he, card_oddBranches]
  have ht := card_le_univ T
  have ha := Nat.one_le_two_pow (n := n)
  have hmul : 2 ^ n * T.card = (2 ^ n - 1) * T.card + T.card := by
    have := Nat.sub_add_cancel ha
    nlinarith
  have hsub := Nat.mul_sub_left_distrib (2 ^ n - 1)
    (Fintype.card (Index V n)) T.card
  have hle := Nat.mul_le_mul_left (2 ^ n - 1) ht
  omega

/-- Every flat support has between `(2^n-1)N` and `2^n N` points. -/
theorem card_keys_bounds [Fintype V] [DecidableEq V] (T : Finset (Index V n)) :
    (2 ^ n - 1) * Fintype.card (Index V n) ≤
      (OddSources.keys (oddBranches n) T).card ∧
    (OddSources.keys (oddBranches n) T).card ≤ 2 ^ n * Fintype.card (Index V n) := by
  rw [card_keys]
  have ht := card_le_univ T
  have ha := Nat.one_le_two_pow (n := n)
  constructor
  · omega
  · have := Nat.sub_add_cancel ha
    nlinarith

open Cslib.Probability in
/-- Flat-source min-entropy in bits, valid for the actual common source. -/
theorem source_minEntropy [Field V] [Fintype V] [DecidableEq V]
    (hn : 1 ≤ n) (T : Finset (Index V n)) :
    Real.logb 2 ((2 ^ n - 1) * Fintype.card (Index V n) : ℕ) ≤
      PMF.minEntropy (source hn T) := by
  have ha : 0 < 2 ^ n - 1 := by
    have hh := pow_le_pow_right₀ (by omega : 1 ≤ 2) hn
    norm_num at hh
    omega
  have hpos : 0 < (2 ^ n - 1) * Fintype.card (Index V n) :=
    Nat.mul_pos ha Fintype.card_pos
  rw [source, OddSources.source, PMF.minEntropy_uniformOfFinset]
  apply Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hpos)
  exact_mod_cast (card_keys_bounds (V := V) T).1

/-- Theorem 5.1's exact key size over a field of `2^b` elements. -/
theorem card_key_at_bit_size [Fintype V] {b : ℕ} (hV : Fintype.card V = 2 ^ b) :
    Fintype.card (Key V n) = (2 ^ (n + 1) - 1) * 2 ^ (n * b) := by
  rw [card_key, hV, ← pow_mul, Nat.mul_comm b n]

/-- A share has exactly the cardinality of a `(b+1)`-bit string. -/
theorem card_share_at_bit_size [Fintype V] {b : ℕ} (hV : Fintype.card V = 2 ^ b) :
    Fintype.card (Share V) = 2 ^ (b + 1) := by
  simp [Share, hV, pow_succ, Nat.mul_comm]

open Cslib.Probability in
/-- The exact entropy lower bound of Theorem 5.1, item 2. -/
theorem source_minEntropy_at_bit_size [Field V] [Fintype V] [DecidableEq V]
    (hn : 1 ≤ n) {b : ℕ} (hV : Fintype.card V = 2 ^ b)
    (T : Finset (Index V n)) :
    (n * b : ℕ) + Real.logb 2 (2 ^ n - 1 : ℕ) ≤ PMF.minEntropy (source hn T) := by
  have h := source_minEntropy (V := V) hn T
  have ha : 0 < 2 ^ n - 1 := by
    have hh := pow_le_pow_right₀ (by omega : 1 ≤ 2) hn
    norm_num at hh
    omega
  have hp : (0 : ℝ) < (2 : ℝ) ^ (n * b) := by positivity
  have hc : Fintype.card (Index V n) = 2 ^ (n * b) := by
    simp [Index, hV, ← pow_mul, Nat.mul_comm]
  rw [hc, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    Real.logb_mul (by exact_mod_cast (ne_of_gt ha)) (ne_of_gt hp), Real.logb_pow,
    Real.logb_self_eq_one (by norm_num), mul_one, add_comm] at h
  exact h

/-- The visible support has the same exact size as the source, as stated in Lemma 5.3. -/
theorem card_viewKeys [Field V] [Fintype V] [DecidableEq V]
    (j : Fin (n + 1)) (T : Finset (Index V n)) :
    (viewKeys j T).card = (2 ^ n - 1) * Fintype.card (Index V n) + T.card := by
  rw [← image_view_keys (fun _ => (0 : V)) 0 j T,
    card_image_of_injOn (view_injective_on _ _ _ _), card_keys]

open Cslib.Probability in
/-- Exact source sizes and flatness on binary fields (Theorem 5.1, items 1–2). -/
theorem flat_sources_at_bit_size [Field V] [Fintype V] [DecidableEq V]
    (hn : 1 ≤ n) {b : ℕ} (hV : Fintype.card V = 2 ^ b) (T : Finset (Index V n)) :
    ∃ (K : Finset (Key V n)) (hK : K.Nonempty),
      source hn T = PMF.uniformOfFinset K hK ∧
      K.card = (2 ^ n - 1) * 2 ^ (n * b) + T.card ∧
      (2 ^ n - 1) * 2 ^ (n * b) ≤ K.card ∧ K.card ≤ 2 ^ n * 2 ^ (n * b) := by
  have hc : Fintype.card (Index V n) = 2 ^ (n * b) := by
    simp [Index, hV, ← pow_mul, Nat.mul_comm]
  refine ⟨OddSources.keys (oddBranches n) T,
    OddSources.keys_nonempty _ (oddBranches_nonempty n) (evenBranches_nonempty hn) T,
    rfl, ?_, ?_⟩
  · rw [card_keys, hc]
  · simpa only [hc] using card_keys_bounds (V := V) T

/-- The index space has even size, permitting the generic sharp balanced-index bound. -/
theorem even_card_index [Fintype V] (hn : 1 ≤ n) {b : ℕ} (hb : 1 ≤ b)
    (hV : Fintype.card V = 2 ^ b) : Even (Fintype.card (Index V n)) := by
  have hc : Fintype.card (Index V n) = 2 ^ (n * b) := by
    simp [Index, hV, ← pow_mul, Nat.mul_comm]
  rw [hc]
  exact even_two.pow_of_ne_zero (ne_of_gt (Nat.mul_pos (by omega) (by omega)))

/-- The full coalition cannot be private for two distinct messages: reconstruction
recovers the secret on every key. This rules out an accidental vacuous privacy notion. -/
theorem full_view_not_private [Field V] [Algebra (ZMod 2) V]
    {γ : Fin (n + 1) → V} (hγ : LinearIndependent (ZMod 2) γ)
    (p : PMF (Key V n)) {m m' : V} (hmm' : m ≠ m') :
    p.map (share γ m) ≠ p.map (share γ m') := by
  intro h
  have hh := congrArg (fun q : PMF (Fin (n + 1) → Share V) => q.map (reconstruct γ)) h
  simp only [PMF.map_comp, Function.comp_def, reconstruct_shares hγ] at hh
  rw [Function.const_def, Function.const_def, PMF.map_const, PMF.map_const] at hh
  have hv := congrArg (fun q : PMF V => q m) hh
  simp [PMF.pure_apply, hmm', eq_comm] at hv

/-- The branch alphabet has odd size, as required by the generic parity obstruction. -/
theorem odd_card_branch (n : ℕ) : Odd (Fintype.card (Branch n)) := by
  rw [card_branch]
  have he : Even (2 ^ (n + 1)) := even_two.pow_of_ne_zero (by omega)
  rw [Nat.odd_sub Nat.one_le_two_pow]
  simp [Nat.not_odd_iff_even.mpr he]

/-- A proper subset of the odd/even branch alphabet is selected at every index. -/
theorem branch_class_proper (hn : 1 ≤ n) :
    (oddBranches n).Nonempty ∧ (univ \ oddBranches n).Nonempty :=
  ⟨oddBranches_nonempty n, evenBranches_nonempty hn⟩

/-- Actual bit-string sharing through fixed message and share bijections. -/
@[expose] def encodedShare [Field V] {b : ℕ}
    (em : V ≃ (Fin b → Bool)) (es : Share V ≃ (Fin (b + 1) → Bool))
    (γ : Fin (n + 1) → V) (m : Fin b → Bool) (k : Key V n)
    (j : Fin (n + 1)) : Fin (b + 1) → Bool := es (share γ (em.symm m) k j)

/-- Decode all shares using the same fixed bijections. -/
@[expose] def encodedReconstruct [Field V] {b : ℕ}
    (em : V ≃ (Fin b → Bool)) (es : Share V ≃ (Fin (b + 1) → Bool))
    (γ : Fin (n + 1) → V) (x : Fin (n + 1) → (Fin (b + 1) → Bool)) :
    Fin b → Bool := em (reconstruct γ (fun j => es.symm (x j)))

/-- Literal bit-string encoding preserves correctness on every ambient key. -/
theorem encoded_correct [Field V] [Algebra (ZMod 2) V] {b : ℕ}
    (em : V ≃ (Fin b → Bool)) (es : Share V ≃ (Fin (b + 1) → Bool))
    {γ : Fin (n + 1) → V} (hγ : LinearIndependent (ZMod 2) γ)
    (m : Fin b → Bool) (k : Key V n) :
    encodedReconstruct em es γ (encodedShare em es γ m k) = m := by
  simp [encodedShare, encodedReconstruct, reconstruct_shares hγ]

/-- Literal bit-string encoding preserves joint privacy of every proper coalition. -/
theorem encoded_privacy [Field V] [Fintype V] [DecidableEq V] {b : ℕ}
    (hn : 1 ≤ n) (em : V ≃ (Fin b → Bool)) (es : Share V ≃ (Fin (b + 1) → Bool))
    (γ : Fin (n + 1) → V) (T : Finset (Index V n))
    (J : Finset (Fin (n + 1))) (hJ : J ≠ univ) (m m' : Fin b → Bool) :
    (source hn T).map (fun k => fun i : J => encodedShare em es γ m k i.val) =
      (source hn T).map (fun k => fun i : J => encodedShare em es γ m' k i.val) := by
  have h := congrArg (fun p : PMF (J → Share V) => p.map (fun x i => es (x i)))
    (coalition_privacy hn γ T J hJ (em.symm m) (em.symm m'))
  simpa only [PMF.map_comp, Function.comp_def, coalitionView, encodedShare] using h

/-- Independent coefficients exist in the specified Galois field for every `b ≥ n+1`.
They are selected from an actual finite-dimensional basis. -/
theorem exists_coefficients {b : ℕ} (hb : n + 1 ≤ b) :
    ∃ γ : Fin (n + 1) → GaloisField 2 b, LinearIndependent (ZMod 2) γ := by
  have hd : Module.finrank (ZMod 2) (GaloisField 2 b) = b :=
    GaloisField.finrank 2 (by omega)
  let f : Fin (n + 1) → Fin (Module.finrank (ZMod 2) (GaloisField 2 b)) :=
    fun i => ⟨i.val, by rw [hd]; omega⟩
  exact ⟨_, (Module.finBasis (ZMod 2) (GaloisField 2 b)).linearIndependent.comp f
    (fun i j h => Fin.ext
      (congrArg (fun x : Fin (Module.finrank (ZMod 2) (GaloisField 2 b)) => x.val) h))⟩

open scoped Classical in
open Cslib.Probability in
/-- The constructive sharing portion of Theorem 5.1 for every `r=n+1 ≥ 2`, `b ≥ r`.
The coefficients and encodings are produced, not assumed. The extraction bounds
are supplied separately by the common odd-source obstruction and balanced-index theorem. -/
theorem binary_construction (n b : ℕ) (hn : 1 ≤ n) (hb : n + 1 ≤ b) :
    let V := GaloisField 2 b
    let : Fintype V := Fintype.ofFinite _
    ∃ (γ : Fin (n + 1) → V) (em : V ≃ (Fin b → Bool))
      (es : Share V ≃ (Fin (b + 1) → Bool)),
      LinearIndependent (ZMod 2) γ ∧
      Fintype.card (Key V n) = (2 ^ (n + 1) - 1) * 2 ^ (n * b) ∧
      (∀ m k, encodedReconstruct em es γ (encodedShare em es γ m k) = m) ∧
      (∀ (T : Finset (Index V n)) (J : Finset (Fin (n + 1))), J ≠ univ →
        ∀ m m',
        (source hn T).map (fun k => fun i : J => encodedShare em es γ m k i.val) =
          (source hn T).map (fun k => fun i : J => encodedShare em es γ m' k i.val)) ∧
      (∀ T : Finset (Index V n),
        (n * b : ℕ) + Real.logb 2 (2 ^ n - 1 : ℕ) ≤ PMF.minEntropy (source hn T)) := by
  classical
  let V := GaloisField 2 b
  let : Fintype V := Fintype.ofFinite _
  have hV : Fintype.card V = 2 ^ b := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 b (by omega)]
  obtain ⟨γ, hγ⟩ := exists_coefficients hb
  let em : V ≃ (Fin b → Bool) := Fintype.equivOfCardEq (by simpa using hV)
  let es : Share V ≃ (Fin (b + 1) → Bool) :=
    Fintype.equivOfCardEq (by simpa using card_share_at_bit_size hV)
  exact ⟨γ, em, es, hγ, card_key_at_bit_size hV, encoded_correct em es hγ,
    fun T J hJ => encoded_privacy hn em es γ T J hJ,
    source_minEntropy_at_bit_size hn hV⟩

end Cslib.Crypto.Protocols.SecretSharing.ImperfectRandomness.AllOutOfR
