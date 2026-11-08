/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Pebbling.ReversiblePath

/-!
# Reachable configurations of reversible pebbling on the path

Li, Tromp and Vitányi characterize every configuration reachable in Bennett's reversible pebble
game on the directed path ([LiTrompVitanyi1998], Section 7, Theorem 1 and Corollary 1). Here the
game is `reversiblePebbleGame pathDigraph n`, and a configuration `C` leaves `f = n - #C` pebbles
free.

* A placed pebble `x` is *available* (`PathAvailable C f x`) if the path start, or another pebble
  of `C`, lies at most `2 ^ f` positions to its left. Bennett's procedure then removes `x` with
  the `f` free pebbles and changes nothing else, and its reverse places `x`
  (`PathAvailable.exists_mTr_remove`, `PathAvailable.exists_mTr_place`). LTV count such a removal
  as one big step (`PathRemoval`).
* `C` is *weakly solvable* if some sequence of big steps frees every pebble, and *strongly
  solvable* if no sequence of big steps gets stuck before every pebble is free. LTV's Theorem 1
  says that the two notions coincide (`PathWeaklySolvable.pathStronglySolvable`).
* A *removal numbering* numbers the pebbles of `C` by `f, …, n - 1` so that pebble `i` has a
  higher-numbered pebble, or the path start, at most `2 ^ i` positions to its left
  (`IsPathRemovalNumbering`). LTV's Corollary 1 says that `C` is reachable from `∅` exactly when it
  has one (`exists_reversiblePebbleGame_pathDigraph_mTr_iff`).

**Index conventions.** As in `Complexity.Computability.Pebbling.ReversiblePath`, vertex `v` is
LTV's node `v + 1`. Their permanently pebbled node `0` is not counted and becomes the path start,
at position `-1`; LTV number it `∞`. So "the path start lies at most `2 ^ i` positions to the left
of `x`" reads `x + 1 ≤ 2 ^ i`.

**Proof.** A weakly solvable configuration is reachable, since its big steps played backwards are
runs. Conversely, each move of the game places or removes a pebble whose predecessor is pebbled,
hence an available pebble. Placing one keeps the configuration weakly solvable. Removing one keeps
it weakly solvable by Theorem 1, which is `IsPathRemovalNumbering.erase_of_pathAvailable`. Pebbles
numbered below the removed pebble move up by one. A pebble whose witness was the removed pebble
follows the chain of witnesses to the left (`IsPathRemovalNumbering.chain`). The distances along
the chain add up to at most `2 ^ (i + 1)`, which is LTV's estimate.

**Deciding reachability.** By Theorem 1, removing the least available pebble until none is left
frees every pebble exactly when the configuration is weakly solvable (`pathGreedySolvable`). This
makes reachability and the existence of a removal numbering decidable, and `decide` checks small
instances.

## Main definitions

* `Cslib.Pebbling.PathAvailable C f x`: the pebble on `x` can be removed with `f` free pebbles.
* `Cslib.Pebbling.PathRemoval n`: one big step, removing an available pebble.
* `Cslib.Pebbling.PathWeaklySolvable n C`, `Cslib.Pebbling.PathStronglySolvable n C`: weak and
  strong solvability.
* `Cslib.Pebbling.IsPathRemovalNumbering n C σ`, `Cslib.Pebbling.HasPathRemovalNumbering n C`:
  removal numberings.
* `Cslib.Pebbling.pathGreedySolvable`: the greedy test.

## Main results

* `Cslib.Pebbling.PathAvailable.exists_mTr_place`, `Cslib.Pebbling.PathAvailable.exists_mTr_remove`:
  big steps are runs of the game.
* `Cslib.Pebbling.PathWeaklySolvable.pathStronglySolvable`: LTV's Theorem 1.
* `Cslib.Pebbling.pathWeaklySolvable_iff_hasPathRemovalNumbering`: weak solvability is the
  existence of a removal numbering.
* `Cslib.Pebbling.exists_reversiblePebbleGame_pathDigraph_mTr_iff`: LTV's Corollary 1.
* `Cslib.Pebbling.add_one_add_two_pow_le_of_reversiblePebbleGame_pathDigraph_mTr`: with `f` free
  pebbles, every pebble `v` satisfies `v + 1 + 2 ^ f ≤ 2 ^ n`.

## References

* [M. Li, J. Tromp, P. Vitányi, *Reversible simulation of irreversible computation by pebble
  games*][LiTrompVitanyi1998], Section 7, Theorem 1 and Corollaries 1 and 2.
-/

public section

namespace Cslib.Pebbling

/-! ## Available pebbles and solvability -/

/-- The pebble on `x` is *available* in the configuration `C` with `f` free pebbles: the path
start, or another pebble of `C`, lies at most `2 ^ f` positions to its left. The path start is at
position `-1`. -/
@[expose] def PathAvailable (C : Finset ℕ) (f x : ℕ) : Prop :=
  x + 1 ≤ 2 ^ f ∨ ∃ y ∈ C, y < x ∧ x ≤ y + 2 ^ f

instance (C : Finset ℕ) (f x : ℕ) : Decidable (PathAvailable C f x) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- One big step of [LiTrompVitanyi1998], Section 7, with `n` pebbles: remove a pebble that is
available with the `n - #C` free pebbles. -/
def PathRemoval (n : ℕ) (C D : Finset ℕ) : Prop :=
  ∃ x ∈ C, PathAvailable C (n - C.card) x ∧ D = C.erase x

/-- `C` is *weakly solvable* with `n` pebbles: it fits in the budget and some sequence of big steps
frees every pebble. -/
def PathWeaklySolvable (n : ℕ) (C : Finset ℕ) : Prop :=
  C.card ≤ n ∧ Relation.ReflTransGen (PathRemoval n) C ∅

/-- `C` is *strongly solvable* with `n` pebbles: it fits in the budget and every configuration that
big steps reach from `C` is empty or allows another big step. Each big step removes a pebble, so
every maximal sequence of big steps frees every pebble. -/
def PathStronglySolvable (n : ℕ) (C : Finset ℕ) : Prop :=
  C.card ≤ n ∧ ∀ D, Relation.ReflTransGen (PathRemoval n) C D → D = ∅ ∨ ∃ E, PathRemoval n D E

/-- `σ` is a *removal numbering* of `C` with `n` pebbles: it numbers the pebbles of `C` by
`n - #C, …, n - 1` so that each pebble `x` has a higher-numbered pebble, or the path start, at
most `2 ^ σ x` positions to its left ([LiTrompVitanyi1998], Corollary 1). The numbering is an
order in which big steps can remove the pebbles. -/
structure IsPathRemovalNumbering (n : ℕ) (C : Finset ℕ) (σ : ℕ → ℕ) : Prop where
  /-- Distinct pebbles get distinct numbers. -/
  injOn : Set.InjOn σ C
  /-- Numbers are at least the number of free pebbles. -/
  le : ∀ x ∈ C, n - C.card ≤ σ x
  /-- Numbers are below the budget. -/
  lt : ∀ x ∈ C, σ x < n
  /-- The path start, or a higher-numbered pebble, is close enough on the left. -/
  near : ∀ x ∈ C, x + 1 ≤ 2 ^ σ x ∨ ∃ y ∈ C, y < x ∧ σ x < σ y ∧ x ≤ y + 2 ^ σ x

/-- `C` has a removal numbering with `n` pebbles. -/
def HasPathRemovalNumbering (n : ℕ) (C : Finset ℕ) : Prop :=
  ∃ σ, IsPathRemovalNumbering n C σ

/-! ## Big steps are runs -/

/-- **The big step.** An available pebble can be placed using the free pebbles: the
configuration `C` is reachable from `C.erase x`. -/
theorem PathAvailable.exists_mTr_place {n x : ℕ} {C : Finset ℕ} (hx : x ∈ C) (hcard : C.card ≤ n)
    (havail : PathAvailable C (n - C.card) x) :
    ∃ ms, (reversiblePebbleGame pathDigraph n).MTr (C.erase x) ms C := by
  set f := n - C.card with hf
  have hce := Finset.card_erase_of_mem hx
  have hpos := Finset.card_pos.2 ⟨x, hx⟩
  have hn : n = (C.erase x).card + f + 1 := by omega
  rw [hn]
  have hx' : x ∉ C.erase x := Finset.notMem_erase x C
  -- Any witness lies in `C.erase x`.
  have havail' : x + 1 ≤ 2 ^ f ∨ ∃ y ∈ C.erase x, y < x ∧ x ≤ y + 2 ^ f := by
    rcases havail with h | ⟨y, hy, hyx, hxy⟩
    · exact .inl h
    · exact .inr ⟨y, Finset.mem_erase.2 ⟨by omega, hy⟩, hyx, hxy⟩
  suffices ∃ ms, (reversiblePebbleGame pathDigraph ((C.erase x).card + f + 1)).MTr (C.erase x)
      ms (insert x (C.erase x)) by rwa [Finset.insert_erase hx] at this
  set D := C.erase x
  by_cases hlow : (D.filter (· < x)).Nonempty
  · set y := (D.filter (· < x)).max' hlow with hy
    have hyD : y ∈ D := (Finset.mem_filter.1 (Finset.max'_mem _ hlow)).1
    have hyx : y < x := (Finset.mem_filter.1 (Finset.max'_mem _ hlow)).2
    have hle : ∀ z ∈ D, z < x → z ≤ y := fun z hz hzx =>
      Finset.le_max' _ z (Finset.mem_filter.2 ⟨hz, hzx⟩)
    refine exists_mTr_insert_pathDigraph f (a := y + 1) (by omega) ?_ (fun z hz => ?_)
      (fun u hu => ?_)
    · rcases havail' with h | ⟨w, hw, hwx, hxw⟩
      · omega
      · have := hle w hw hwx; omega
    · by_cases hzx : z < x
      · exact .inl (by have := hle z hz hzx; omega)
      · exact .inr (by have : z ≠ x := fun h => hx' (h ▸ hz); omega)
    · rw [pathDigraph_adj] at hu
      rw [show u = y by omega]
      exact hyD
  · have hnone : ∀ z ∈ D, ¬ z < x := fun z hz hzx => hlow ⟨z, Finset.mem_filter.2 ⟨hz, hzx⟩⟩
    refine exists_mTr_insert_pathDigraph f (a := 0) (Nat.zero_le x) ?_ (fun z hz => ?_)
      (fun u hu => absurd hu pathDigraph_source)
    · rcases havail' with h | ⟨w, hw, hwx, -⟩
      · omega
      · exact absurd hwx (hnone w hw)
    · exact .inr (by have := hnone z hz; have : z ≠ x := fun h => hx' (h ▸ hz); omega)

/-- An available pebble can be removed using the free pebbles. -/
theorem PathAvailable.exists_mTr_remove {n x : ℕ} {C : Finset ℕ} (hx : x ∈ C) (hcard : C.card ≤ n)
    (havail : PathAvailable C (n - C.card) x) :
    ∃ ms, (reversiblePebbleGame pathDigraph n).MTr C ms (C.erase x) := by
  obtain ⟨ms, hms⟩ := havail.exists_mTr_place hx hcard
  exact ⟨_, reversiblePebbleGame_mTr_reverse pathDigraph_irrefl hms
    (Finset.card_erase_le.trans hcard)⟩

/-! ## Numberings -/

namespace IsPathRemovalNumbering

variable {n : ℕ} {C : Finset ℕ} {σ : ℕ → ℕ}

theorem card_le (h : IsPathRemovalNumbering n C σ) : C.card ≤ n := by
  have := Finset.card_le_card_of_injOn σ (t := Finset.range n)
    (fun x hx => Finset.mem_range.2 (h.lt x hx)) h.injOn
  rwa [Finset.card_range] at this

/-- Some pebble carries the least number `n - #C`. -/
theorem exists_eq (h : IsPathRemovalNumbering n C σ) (hne : C.Nonempty) :
    ∃ x ∈ C, σ x = n - C.card := by
  have hsub : C.image σ ⊆ Finset.Ico (n - C.card) n := fun y hy => by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    exact Finset.mem_Ico.2 ⟨h.le x hx, h.lt x hx⟩
  have hcard : (Finset.Ico (n - C.card) n).card ≤ (C.image σ).card := by
    rw [Finset.card_image_of_injOn h.injOn, Nat.card_Ico]
    omega
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hmem : n - C.card ∈ Finset.Ico (n - C.card) n := by
    have := h.card_le
    have := Finset.card_pos.2 hne
    exact Finset.mem_Ico.2 ⟨le_rfl, by omega⟩
  rw [← heq] at hmem
  obtain ⟨x, hx, hσx⟩ := Finset.mem_image.1 hmem
  exact ⟨x, hx, hσx⟩

/-- The pebble with the least number is available. -/
theorem pathAvailable (h : IsPathRemovalNumbering n C σ) {x : ℕ} (hx : x ∈ C)
    (hσx : σ x = n - C.card) : PathAvailable C (n - C.card) x := by
  rcases h.near x hx with h' | ⟨y, hy, hyx, -, hxy⟩
  · exact .inl (hσx ▸ h')
  · exact .inr ⟨y, hy, hyx, hσx ▸ hxy⟩

/-- Removing the pebble with the least number leaves a removal numbering. -/
theorem erase (h : IsPathRemovalNumbering n C σ) {x : ℕ} (hx : x ∈ C)
    (hσx : σ x = n - C.card) : IsPathRemovalNumbering n (C.erase x) σ := by
  have hcard := Finset.card_erase_of_mem hx
  have hpos := Finset.card_pos.2 ⟨x, hx⟩
  have hle := h.card_le
  refine ⟨h.injOn.mono (Finset.coe_subset.2 (Finset.erase_subset x C)), fun z hz => ?_,
    fun z hz => h.lt z (Finset.mem_of_mem_erase hz), fun z hz => ?_⟩
  · have hzC := Finset.mem_of_mem_erase hz
    have hzx := Finset.ne_of_mem_erase hz
    have h1 := h.le z hzC
    have h2 : σ z ≠ σ x := fun e => hzx (h.injOn hzC hx e)
    omega
  · have hzC := Finset.mem_of_mem_erase hz
    have hzx := Finset.ne_of_mem_erase hz
    have h2 : σ z ≠ σ x := fun e => hzx (h.injOn hzC hx e)
    rcases h.near z hzC with h' | ⟨y, hy, hyz, hσ, hzy⟩
    · exact .inl h'
    · refine .inr ⟨y, Finset.mem_erase.2 ⟨fun e => ?_, hy⟩, hyz, hσ, hzy⟩
      subst e
      have := h.le z hzC
      omega

/-- Adding an available pebble with the least number gives a removal numbering. -/
theorem update {x : ℕ} (h : IsPathRemovalNumbering n (C.erase x) σ) (hx : x ∈ C)
    (hcard : C.card ≤ n) (havail : PathAvailable C (n - C.card) x) :
    IsPathRemovalNumbering n C (Function.update σ x (n - C.card)) := by
  have hce := Finset.card_erase_of_mem hx
  have hpos := Finset.card_pos.2 ⟨x, hx⟩
  have hold : ∀ z ∈ C, z ≠ x → n - C.card < σ z := fun z hz hzx => by
    have := h.le z (Finset.mem_erase.2 ⟨hzx, hz⟩)
    omega
  refine ⟨fun z hz w hw e => ?_, fun z hz => ?_, fun z hz => ?_, fun z hz => ?_⟩
  · simp only [Finset.mem_coe] at hz hw
    by_cases hzx : z = x
    · by_cases hwx : w = x
      · rw [hzx, hwx]
      · rw [hzx, Function.update_self, Function.update_of_ne hwx] at e
        have := hold w hw hwx
        omega
    · by_cases hwx : w = x
      · rw [hwx, Function.update_self, Function.update_of_ne hzx] at e
        have := hold z hz hzx
        omega
      · rw [Function.update_of_ne hzx, Function.update_of_ne hwx] at e
        exact h.injOn (Finset.mem_erase.2 ⟨hzx, hz⟩) (Finset.mem_erase.2 ⟨hwx, hw⟩) e
  · by_cases hzx : z = x
    · rw [hzx, Function.update_self]
    · rw [Function.update_of_ne hzx]
      exact (hold z hz hzx).le
  · by_cases hzx : z = x
    · rw [hzx, Function.update_self]
      omega
    · rw [Function.update_of_ne hzx]
      exact h.lt z (Finset.mem_erase.2 ⟨hzx, hz⟩)
  · by_cases hzx : z = x
    · subst hzx
      rw [Function.update_self]
      rcases havail with h' | ⟨y, hy, hyz, hzy⟩
      · exact .inl h'
      · have hyx : y ≠ z := fun e => by omega
        refine .inr ⟨y, hy, hyz, ?_, hzy⟩
        rw [Function.update_of_ne hyx]
        exact hold y hy hyx
    · rw [Function.update_of_ne hzx]
      rcases h.near z (Finset.mem_erase.2 ⟨hzx, hz⟩) with h' | ⟨y, hy, hyz, hσ, hzy⟩
      · exact .inl h'
      · refine .inr ⟨y, Finset.mem_of_mem_erase hy, hyz, ?_, hzy⟩
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hy)]
        exact hσ

/-- Following the witnesses to the left from a pebble `y` numbered below `j`, either the path
start or a pebble numbered at least `j` is close: the distances along the chain add up to at most
`2 ^ j - 2 ^ σ y`. -/
theorem chain (h : IsPathRemovalNumbering n C σ) {j : ℕ} :
    ∀ y ∈ C, σ y < j →
      y + 1 + 2 ^ σ y ≤ 2 ^ j ∨ ∃ w ∈ C, w < y ∧ j ≤ σ w ∧ y + 2 ^ σ y ≤ w + 2 ^ j := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro hy hσy
    have hpow : 2 ^ (σ y + 1) ≤ 2 ^ j := Nat.pow_le_pow_right Nat.two_pos hσy
    have hpow' : 2 ^ (σ y + 1) = 2 ^ σ y + 2 ^ σ y := by rw [pow_succ]; omega
    rcases h.near y hy with h' | ⟨w, hw, hwy, hσw, hyw⟩
    · exact .inl (by omega)
    · by_cases hwj : j ≤ σ w
      · exact .inr ⟨w, hw, hwy, hwj, by omega⟩
      · have hpw : 2 ^ (σ y + 1) ≤ 2 ^ σ w := Nat.pow_le_pow_right Nat.two_pos hσw
        rcases ih w hwy hw (by omega) with h'' | ⟨w', hw', hw'w, hjw', hww'⟩
        · exact .inl (by omega)
        · exact .inr ⟨w', hw', by omega, hjw', by omega⟩

/-- A pebble numbered `i` lies at a vertex `y` with `y + 1 + 2 ^ i ≤ 2 ^ n`. -/
theorem add_one_add_pow_le (h : IsPathRemovalNumbering n C σ) {y : ℕ} (hy : y ∈ C) :
    y + 1 + 2 ^ σ y ≤ 2 ^ n := by
  rcases h.chain y hy (h.lt y hy) with h' | ⟨w, hw, -, hnw, -⟩
  · exact h'
  · exact absurd (h.lt w hw) (by omega)

/-- **The key step of [LiTrompVitanyi1998], Theorem 1.** Removing any available pebble `x`
leaves a removal numbering: the pebbles numbered below `x` move up by one. -/
theorem erase_of_pathAvailable (h : IsPathRemovalNumbering n C σ) {x : ℕ} (hx : x ∈ C)
    (havail : PathAvailable C (n - C.card) x) :
    IsPathRemovalNumbering n (C.erase x) (fun z => if σ z < σ x then σ z + 1 else σ z) := by
  set f := n - C.card with hf
  set g := σ x with hg
  set σ' : ℕ → ℕ := fun z => if σ z < g then σ z + 1 else σ z with hσ'
  have hce := Finset.card_erase_of_mem hx
  have hpos := Finset.card_pos.2 ⟨x, hx⟩
  have hcard := h.card_le
  have hfg : f ≤ g := h.le x hx
  have hgn : g < n := h.lt x hx
  have hne : ∀ z ∈ C.erase x, σ z ≠ g := fun z hz e =>
    Finset.ne_of_mem_erase hz (h.injOn (Finset.mem_of_mem_erase hz) hx e)
  have hσ'lt : ∀ z, σ z < g → σ' z = σ z + 1 := fun z hz => ite_eq_left hz
  have hσ'ge : ∀ z, ¬ σ z < g → σ' z = σ z := fun z hz => ite_eq_right hz
  refine ⟨fun z hz w hw e => ?_, fun z hz => ?_, fun z hz => ?_, fun z hz => ?_⟩
  · simp only [Finset.mem_coe] at hz hw
    have hzg := hne z hz
    have hwg := hne w hw
    have hz' := Finset.mem_of_mem_erase hz
    have hw' := Finset.mem_of_mem_erase hw
    refine h.injOn hz' hw' ?_
    by_cases h1 : σ z < g <;> by_cases h2 : σ w < g
    · rw [hσ'lt z h1, hσ'lt w h2] at e; omega
    · rw [hσ'lt z h1, hσ'ge w h2] at e; omega
    · rw [hσ'ge z h1, hσ'lt w h2] at e; omega
    · rw [hσ'ge z h1, hσ'ge w h2] at e; omega
  · have := h.le z (Finset.mem_of_mem_erase hz)
    have := hne z hz
    by_cases h1 : σ z < g
    · rw [hσ'lt z h1]; omega
    · rw [hσ'ge z h1]; omega
  · have := h.lt z (Finset.mem_of_mem_erase hz)
    by_cases h1 : σ z < g
    · rw [hσ'lt z h1]; omega
    · rw [hσ'ge z h1]; omega
  · have hzC := Finset.mem_of_mem_erase hz
    have hzx := Finset.ne_of_mem_erase hz
    have hzg := hne z hz
    by_cases h1 : σ z < g
    · rw [hσ'lt z h1]
      have hpj : 2 ^ (σ z + 1) = 2 ^ σ z + 2 ^ σ z := by rw [pow_succ]; omega
      have hpf : 2 ^ f ≤ 2 ^ σ z := Nat.pow_le_pow_right Nat.two_pos (h.le z hzC)
      -- A pebble numbered above `z`, other than `x`, is numbered above `σ z + 1` afterwards.
      have hup : ∀ w ∈ C, w ≠ x → σ z < σ w → σ z + 1 < σ' w := by
        intro w hw hwx hjw
        have hwg : σ w ≠ g := fun e => hwx (h.injOn hw hx e)
        by_cases h2 : σ w < g
        · rw [hσ'lt w h2]; omega
        · rw [hσ'ge w h2]; omega
      rcases h.near z hzC with h' | ⟨y, hy, hyz, hσ, hzy⟩
      · exact .inl (by omega)
      by_cases hyx : y = x
      · subst hyx
        rcases havail with h' | ⟨x', hx', hx'y, hyx'⟩
        · exact .inl (by omega)
        have hx'y' : x' ≠ y := by omega
        have hpf' : 2 ^ f ≤ 2 ^ σ x' := Nat.pow_le_pow_right Nat.two_pos (h.le x' hx')
        rcases lt_trichotomy (σ x') (σ z) with hlt | heq | hgt
        · rcases h.chain x' hx' hlt with h'' | ⟨w, hw, hwx', hjw, hx'w⟩
          · exact .inl (by omega)
          · have hwz : σ w ≠ σ z := fun e => by
              have := h.injOn hw hzC e
              omega
            exact .inr ⟨w, Finset.mem_erase.2 ⟨by omega, hw⟩, by omega,
              hup w hw (by omega) (by omega), by omega⟩
        · exact absurd (h.injOn hx' hzC heq) (by omega)
        · exact .inr ⟨x', Finset.mem_erase.2 ⟨hx'y', hx'⟩, by omega, hup x' hx' hx'y' hgt,
            by omega⟩
      · exact .inr ⟨y, Finset.mem_erase.2 ⟨hyx, hy⟩, hyz, hup y hy hyx hσ, by omega⟩
    · -- Pebbles numbered above `x` keep their numbers and their witnesses.
      rw [hσ'ge z h1]
      rcases h.near z hzC with h' | ⟨y, hy, hyz, hσ, hzy⟩
      · exact .inl h'
      · have hyx : y ≠ x := fun e => by subst e; omega
        refine .inr ⟨y, Finset.mem_erase.2 ⟨hyx, hy⟩, hyz, ?_, hzy⟩
        rw [hσ'ge y (by omega)]
        exact hσ

end IsPathRemovalNumbering

/-! ## Weak and strong solvability -/

/-- The empty configuration is weakly solvable. -/
theorem pathWeaklySolvable_empty (n : ℕ) : PathWeaklySolvable n ∅ :=
  ⟨by simp, .refl⟩

theorem PathWeaklySolvable.card_le {n : ℕ} {C : Finset ℕ} (h : PathWeaklySolvable n C) :
    C.card ≤ n :=
  h.1

/-- Adding a pebble to a weakly solvable configuration, where it is available, gives a weakly
solvable configuration. -/
theorem PathWeaklySolvable.of_erase {n x : ℕ} {C : Finset ℕ} (h : PathWeaklySolvable n (C.erase x))
    (hx : x ∈ C) (hcard : C.card ≤ n) (havail : PathAvailable C (n - C.card) x) :
    PathWeaklySolvable n C :=
  ⟨hcard, .head ⟨x, hx, havail, rfl⟩ h.2⟩

/-- Numbering the pebbles in the order of a solving sequence of big steps gives a removal
numbering. -/
theorem PathWeaklySolvable.hasPathRemovalNumbering {n : ℕ} {C : Finset ℕ}
    (h : PathWeaklySolvable n C) : HasPathRemovalNumbering n C := by
  obtain ⟨hcard, h⟩ := h
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨id, by simp, by simp, by simp, by simp⟩
  | head hstep _ ih =>
    obtain ⟨x, hx, havail, rfl⟩ := hstep
    obtain ⟨σ, hσ⟩ := ih ((Finset.card_erase_le).trans hcard)
    exact ⟨_, hσ.update hx hcard havail⟩

/-- Removing the pebbles in the order of a removal numbering is a solving sequence of big steps. -/
theorem HasPathRemovalNumbering.pathWeaklySolvable {n : ℕ} {C : Finset ℕ}
    (h : HasPathRemovalNumbering n C) : PathWeaklySolvable n C := by
  obtain ⟨σ, hσ⟩ := h
  induction hk : C.card generalizing C with
  | zero => rw [Finset.card_eq_zero.1 hk]; exact pathWeaklySolvable_empty n
  | succ k ih =>
    obtain ⟨x, hx, hσx⟩ := hσ.exists_eq (Finset.card_pos.1 (by omega))
    exact (ih (hσ.erase hx hσx) (by rw [Finset.card_erase_of_mem hx]; omega)).of_erase hx
      hσ.card_le (hσ.pathAvailable hx hσx)

theorem pathWeaklySolvable_iff_hasPathRemovalNumbering {n : ℕ} {C : Finset ℕ} :
    PathWeaklySolvable n C ↔ HasPathRemovalNumbering n C :=
  ⟨PathWeaklySolvable.hasPathRemovalNumbering, HasPathRemovalNumbering.pathWeaklySolvable⟩

/-- **The key step of [LiTrompVitanyi1998], Theorem 1.** Removing any available pebble from a
weakly solvable configuration gives a weakly solvable configuration. -/
theorem PathWeaklySolvable.erase {n x : ℕ} {C : Finset ℕ} (h : PathWeaklySolvable n C)
    (hx : x ∈ C) (havail : PathAvailable C (n - C.card) x) :
    PathWeaklySolvable n (C.erase x) := by
  obtain ⟨σ, hσ⟩ := h.hasPathRemovalNumbering
  exact HasPathRemovalNumbering.pathWeaklySolvable ⟨_, hσ.erase_of_pathAvailable hx havail⟩

/-- **[LiTrompVitanyi1998], Theorem 1.** Every weakly solvable configuration is strongly
solvable. -/
theorem PathWeaklySolvable.pathStronglySolvable {n : ℕ} {C : Finset ℕ}
    (h : PathWeaklySolvable n C) : PathStronglySolvable n C := by
  refine ⟨h.card_le, fun D hD => ?_⟩
  have hD : PathWeaklySolvable n D := by
    induction hD with
    | refl => exact h
    | tail _ hstep ih =>
      obtain ⟨x, hx, havail, rfl⟩ := hstep
      exact ih.erase hx havail
  rcases hD.2.cases_head with he | ⟨E, hE, -⟩
  · exact .inl he
  · exact .inr ⟨E, hE⟩

/-- A strongly solvable configuration is weakly solvable. -/
theorem PathStronglySolvable.pathWeaklySolvable {n : ℕ} {C : Finset ℕ}
    (h : PathStronglySolvable n C) : PathWeaklySolvable n C := by
  obtain ⟨hcard, h⟩ := h
  induction hk : C.card generalizing C with
  | zero => rw [Finset.card_eq_zero.1 hk]; exact pathWeaklySolvable_empty n
  | succ k ih =>
    rcases h C .refl with he | ⟨E, x, hx, havail, rfl⟩
    · simp [he] at hk
    · refine (ih ((Finset.card_erase_le).trans hcard)
        (fun D hD => h D (.head ⟨x, hx, havail, rfl⟩ hD))
        (by rw [Finset.card_erase_of_mem hx]; omega)).of_erase hx hcard havail

theorem pathWeaklySolvable_iff_pathStronglySolvable {n : ℕ} {C : Finset ℕ} :
    PathWeaklySolvable n C ↔ PathStronglySolvable n C :=
  ⟨PathWeaklySolvable.pathStronglySolvable, PathStronglySolvable.pathWeaklySolvable⟩

/-! ## Reachable configurations -/

/-- A weakly solvable configuration is reachable: play its big steps backwards. -/
theorem PathWeaklySolvable.exists_mTr {n : ℕ} {C : Finset ℕ} (h : PathWeaklySolvable n C) :
    ∃ ms, (reversiblePebbleGame pathDigraph n).MTr ∅ ms C := by
  obtain ⟨hcard, h⟩ := h
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[], .refl⟩
  | @head E _ hstep _ ih =>
    obtain ⟨x, hx, havail, rfl⟩ := hstep
    obtain ⟨ms, hms⟩ := ih ((Finset.card_erase_le).trans hcard)
    obtain ⟨ms', hms'⟩ := havail.exists_mTr_place hx hcard
    exact ⟨ms ++ ms', LTS.MTr.comp _ hms hms'⟩

/-- A pebble whose predecessor is pebbled, or the source, is available. -/
theorem pathAvailable_of_forall_adj {C : Finset ℕ} {x : ℕ} (f : ℕ)
    (h : ∀ u, pathDigraph.Adj u x → u ∈ C) : PathAvailable C f x := by
  cases x with
  | zero => exact .inl (Nat.one_le_two_pow)
  | succ y =>
    exact .inr ⟨y, h y (pathDigraph_adj.2 rfl), Nat.lt_succ_self y,
      Nat.add_le_add_left Nat.one_le_two_pow y⟩

/-- One move of the game keeps a configuration weakly solvable. -/
theorem PathWeaklySolvable.of_tr {n : ℕ} {C D : Finset ℕ} {m : Move ℕ}
    (h : PathWeaklySolvable n C) (htr : (reversiblePebbleGame pathDigraph n).Tr C m D) :
    PathWeaklySolvable n D := by
  obtain ⟨hstep, hcard⟩ := htr
  cases hstep with
  | @place x hx hpred =>
    have h' : PathWeaklySolvable n ((insert x C).erase x) := by rwa [Finset.erase_insert hx]
    exact h'.of_erase (Finset.mem_insert_self x C) hcard (pathAvailable_of_forall_adj _
      fun u hu => Finset.mem_insert_of_mem (hpred u hu))
  | @remove x hx hpred => exact h.erase hx (pathAvailable_of_forall_adj _ hpred)

/-- Every reachable configuration is weakly solvable. -/
theorem pathWeaklySolvable_of_mTr {n : ℕ} {ms : List (Move ℕ)} {C : Finset ℕ}
    (h : (reversiblePebbleGame pathDigraph n).MTr ∅ ms C) : PathWeaklySolvable n C := by
  suffices ∀ E, PathWeaklySolvable n E → ∀ ms D,
      (reversiblePebbleGame pathDigraph n).MTr E ms D → PathWeaklySolvable n D from
    this ∅ (pathWeaklySolvable_empty n) ms C h
  intro E hE ms D hED
  induction hED with
  | refl => exact hE
  | stepL htr _ ih => exact ih (hE.of_tr htr)

/-- The reachable configurations are the weakly solvable ones. -/
theorem exists_reversiblePebbleGame_pathDigraph_mTr_iff_pathWeaklySolvable {n : ℕ}
    {C : Finset ℕ} :
    (∃ ms, (reversiblePebbleGame pathDigraph n).MTr ∅ ms C) ↔ PathWeaklySolvable n C :=
  ⟨fun ⟨_, h⟩ => pathWeaklySolvable_of_mTr h, PathWeaklySolvable.exists_mTr⟩

/-- **Reachable configurations of reversible pebbling on the path ([LiTrompVitanyi1998],
Corollary 1).** With `n` pebbles, a configuration `C` is reachable from `∅` iff its pebbles can be
numbered `n - #C, …, n - 1` so that each pebble `x` has a higher-numbered pebble, or the path
start, at most `2 ^ σ x` positions to its left. -/
theorem exists_reversiblePebbleGame_pathDigraph_mTr_iff {n : ℕ} {C : Finset ℕ} :
    (∃ ms, (reversiblePebbleGame pathDigraph n).MTr ∅ ms C) ↔ HasPathRemovalNumbering n C :=
  exists_reversiblePebbleGame_pathDigraph_mTr_iff_pathWeaklySolvable.trans
    pathWeaklySolvable_iff_hasPathRemovalNumbering

/-- With `n` pebbles and `f = n - #C` free pebbles, every pebble `v` of a reachable configuration
`C` satisfies `v + 1 + 2 ^ f ≤ 2 ^ n`. With `f = 0` this is the bound `v + 2 ≤ 2 ^ n` of
`add_two_le_of_reversiblePebbleGame_pathDigraph_mTr`, and with `C = {v}` it is
`persistentReversiblePebblable_pathDigraph_iff`'s `2 * (v + 1) ≤ 2 ^ n`. -/
theorem add_one_add_two_pow_le_of_reversiblePebbleGame_pathDigraph_mTr {n : ℕ}
    {ms : List (Move ℕ)} {C : Finset ℕ} (h : (reversiblePebbleGame pathDigraph n).MTr ∅ ms C)
    {v : ℕ} (hv : v ∈ C) : v + 1 + 2 ^ (n - C.card) ≤ 2 ^ n := by
  obtain ⟨σ, hσ⟩ := exists_reversiblePebbleGame_pathDigraph_mTr_iff.1 ⟨ms, h⟩
  have := Nat.pow_le_pow_right Nat.two_pos (hσ.le v hv)
  have := hσ.add_one_add_pow_le hv
  omega

/-! ## Deciding reachability -/

/-- The greedy test with `n` pebbles and `k` rounds: remove the least available pebble until
none is available, and report whether every pebble was removed. -/
@[expose] def pathGreedySolvable (n : ℕ) : ℕ → Finset ℕ → Bool
  | 0, C => decide (C = ∅)
  | k + 1, C =>
    if hC : (C.filter fun x => PathAvailable C (n - C.card) x).Nonempty then
      pathGreedySolvable n k (C.erase ((C.filter fun x => PathAvailable C (n - C.card) x).min' hC))
    else decide (C = ∅)

/-- **Correctness of the greedy test.** With at least `#C` rounds, the greedy test accepts exactly
the weakly solvable configurations. By Theorem 1, removing an available pebble never loses
solvability. -/
theorem pathGreedySolvable_iff {n : ℕ} :
    ∀ (k : ℕ) (C : Finset ℕ), C.card ≤ k → C.card ≤ n →
      (pathGreedySolvable n k C = true ↔ PathWeaklySolvable n C)
  | 0, C, hk, hn => by
    rw [Finset.card_eq_zero.1 (Nat.le_zero.1 hk)]
    simp only [pathGreedySolvable, decide_true, true_iff]
    exact pathWeaklySolvable_empty n
  | k + 1, C, hk, hn => by
    unfold pathGreedySolvable
    split_ifs with hC
    · have hxm := Finset.mem_filter.1 (Finset.min'_mem _ hC)
      generalize (C.filter fun x => PathAvailable C (n - C.card) x).min' hC = x at hxm ⊢
      have hce := Finset.card_erase_of_mem hxm.1
      rw [pathGreedySolvable_iff k (C.erase x) (by omega) (by omega)]
      exact ⟨fun h => h.of_erase hxm.1 hn hxm.2, fun h => h.erase hxm.1 hxm.2⟩
    · rw [decide_eq_true_iff]
      refine ⟨fun h => h ▸ pathWeaklySolvable_empty n, fun h => ?_⟩
      rcases h.2.cases_head with he | ⟨E, ⟨x, hx, havail, -⟩, -⟩
      · exact he
      · exact absurd ⟨x, Finset.mem_filter.2 ⟨hx, havail⟩⟩ hC

instance (n : ℕ) (C : Finset ℕ) : Decidable (PathWeaklySolvable n C) :=
  decidable_of_iff (C.card ≤ n ∧ pathGreedySolvable n C.card C = true)
    ⟨fun h => (pathGreedySolvable_iff _ C le_rfl h.1).1 h.2,
      fun h => ⟨h.card_le, (pathGreedySolvable_iff _ C le_rfl h.card_le).2 h⟩⟩

/-- By Corollary 1, reachability on the path is decidable through removal numberings. -/
instance (n : ℕ) (C : Finset ℕ) : Decidable (HasPathRemovalNumbering n C) :=
  decidable_of_iff _ pathWeaklySolvable_iff_hasPathRemovalNumbering

end Cslib.Pebbling
