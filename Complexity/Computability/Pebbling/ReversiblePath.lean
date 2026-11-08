/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Pebbling.Path
public import Complexity.Computability.Pebbling.Reversible
public import Mathlib.Data.Nat.Log

/-!
# Reversible pebbling of the directed path

Bennett's recursive strategy reversibly pebbles the directed path `0 → 1 → ⋯` with logarithmically
many pebbles, and this is optimal. With `k` pebbles,

* a configuration containing `v` is reachable iff `v + 2 ≤ 2 ^ k`;
* the configuration `{v}` is reachable iff `2 * (v + 1) ≤ 2 ^ k`.

So the reversible pebbling price of `v` is `⌈log₂ (v + 2)⌉` and its persistent price is
`⌈log₂ (v + 1)⌉ + 1`, while the black pebbling price of every vertex other than the source is `2`
(`blackPebblingPrice_pathDigraph_succ`).

**Bennett's strategy.** `bennettMoves a k` pebbles the block `a, …, a + 2 ^ k - 1` of the path,
given a pebble on `a - 1` (or `a = 0`), and leaves only `a + 2 ^ k - 1` pebbled. For `k = 0` it
places a pebble on `a`. For the block of length `2 ^ (k + 1)`, `bennettMoves a (k + 1)` first runs
`bennettMoves a k` to pebble the midpoint `a + 2 ^ k - 1`, then `bennettMoves (a + 2 ^ k) k` to
pebble the end, then plays the first run backwards to remove the midpoint. So `bennettMoves a k`
uses `k + 1` extra pebbles and `3 ^ k` moves (`bennettMoves_mTr`, `length_bennettMoves`). In
particular `k + 1` pebbles reversibly pebble a path of `2 ^ k` vertices in `3 ^ k` moves, ending
with only the last vertex pebbled (`exists_mTr_bennett_pathDigraph`). These are the procedures
`pebble(s, n)` and `unpebble(s, n)` of [LiTrompVitanyi1998], Section 7, in the form that ends
with a single pebble.

**The lower bound.** Write `R_k` for the configurations reachable with `k` pebbles. We prove by
induction on `k` that every `x` in a configuration of `R_k` has `x + 2 ≤ 2 ^ k`
(`add_two_le_of_reversiblePebbleGame_pathDigraph_mTr`), together with the bound
`2 * (c + 1) ≤ 2 ^ k` on its least element `c`
(`two_mul_min_add_one_le_of_reversiblePebbleGame_pathDigraph_mTr`).

* For the least element `c + 1`, play the run backwards from the configuration to `∅` and
  restrict it to the vertices below `c + 1`. The restricted run uses at most `k - 1` pebbles while
  `c + 1` is pebbled, and must remove `c + 1` at some point, which needs a pebble on `c`.
* For the other elements, restrict the run from `∅` to the vertices at least `2 ^ (k - 1)`,
  shifted down by `2 ^ (k - 1)`. By the bound on the least element, a nonempty configuration of
  `R_k` has an element below `2 ^ (k - 1)`, so the shifted run uses at most `k - 1` pebbles.

This proves the bound of [LiTrompVitanyi1998], Corollary 2 and Theorem 2(i), by a different
route: they first characterize all reachable configurations (Theorem 1 and Corollary 1).

**Index conventions.** Vertex `v` of `pathDigraph` is node `v + 1` of [LiTrompVitanyi1998], whose
node `0` carries a permanent pebble that is not counted; the source `0` here plays the role of
their freely toggled node `1`. Their Corollary 2, that the maximum reachable node with `n` pebbles
is `2 ^ n - 1`, is `reversiblePebblable_pathDigraph_iff`.

## Main definitions

* `Cslib.Pebbling.bennettMoves a k`: Bennett's strategy on the block of length `2 ^ k` at `a`.

## Main results

* `Cslib.Pebbling.bennettMoves_mTr`, `Cslib.Pebbling.length_bennettMoves`: Bennett's strategy
  uses `k + 1` extra pebbles and `3 ^ k` moves.
* `Cslib.Pebbling.exists_mTr_bennett_pathDigraph`: `k + 1` pebbles reversibly pebble a path of
  `2 ^ k` vertices in `3 ^ k` moves.
* `Cslib.Pebbling.add_two_le_of_reversiblePebbleGame_pathDigraph_mTr`: every pebble reachable
  with `k` pebbles is at a vertex `v` with `v + 2 ≤ 2 ^ k`.
* `Cslib.Pebbling.reversiblePebblable_pathDigraph_iff`,
  `Cslib.Pebbling.persistentReversiblePebblable_pathDigraph_iff`: the exact characterizations.
* `Cslib.Pebbling.reversiblePebblingPrice_pathDigraph`,
  `Cslib.Pebbling.persistentReversiblePebblingPrice_pathDigraph`: the prices as `Nat.clog 2`.
* `Cslib.Pebbling.persistentReversiblePebblingPrice_pathDigraph_two_pow_sub_one`,
  `Cslib.Pebbling.reversiblePebblingPrice_pathDigraph_two_pow_sub_one`: Bennett's `k + 1`
  pebbles are optimal for the last vertex of a path of `2 ^ k` vertices, in both forms.

## References

* [C. H. Bennett, *Time/space trade-offs for reversible computation*][Bennett1989].
* [M. Li, J. Tromp, P. Vitányi, *Reversible simulation of irreversible computation by pebble
  games*][LiTrompVitanyi1998], Sections 6 and 7, Corollary 2 and Theorem 2(i).
-/

public section

namespace Cslib.Pebbling

/-! ## Bennett's strategy -/

/-- Bennett's strategy on the block `a, …, a + 2 ^ k - 1` of the directed path: pebble the
midpoint of the block recursively, pebble the second half recursively from it, then play the
first run backwards to remove the midpoint. -/
@[expose] def bennettMoves (a : ℕ) : ℕ → List (Move ℕ)
  | 0 => [.place a]
  | k + 1 => bennettMoves a k ++ bennettMoves (a + 2 ^ k) k ++
      (bennettMoves a k).reverse.map Move.swap

@[simp] theorem length_bennettMoves (a k : ℕ) : (bennettMoves a k).length = 3 ^ k := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    simp only [bennettMoves, List.length_append, List.length_map, List.length_reverse, ih]
    rw [pow_succ]
    omega

/-- **Bennett's strategy.** If the configuration `C` has no pebble on the block
`a, …, a + 2 ^ k - 1` and a pebble on `a - 1` (or `a = 0`), then `bennettMoves a k` pebbles
`a + 2 ^ k - 1` and changes nothing else, using `k + 1` pebbles beyond those of `C`. -/
theorem bennettMoves_mTr (k : ℕ) {a : ℕ} {C : Finset ℕ} (hC : ∀ x ∈ C, x < a ∨ a + 2 ^ k ≤ x)
    (ha : ∀ u, pathDigraph.Adj u a → u ∈ C) :
    (reversiblePebbleGame pathDigraph (C.card + k + 1)).MTr C (bennettMoves a k)
      (insert (a + 2 ^ k - 1) C) := by
  induction k generalizing a C with
  | zero =>
    have hnot : a ∉ C := fun h => by
      have := hC a h
      rw [pow_zero] at this
      omega
    rw [pow_zero, Nat.add_sub_cancel]
    exact LTS.MTr.single _ ⟨.place hnot ha, (Finset.card_insert_le _ _).trans (by omega)⟩
  | succ k ih =>
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; omega
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    set m := a + 2 ^ k - 1 with hm
    set top := a + 2 ^ (k + 1) - 1 with htop
    have hmC : m ∉ C := fun h => by have := hC m h; omega
    have htopC : top ∉ C := fun h => by have := hC top h; omega
    have hmtop : m ≠ top := by omega
    -- Pebble the midpoint.
    have h₁ := ih (a := a) (C := C) (fun x hx => by have := hC x hx; omega) ha
    -- Pebble the end from the midpoint.
    have h₂ := ih (a := a + 2 ^ k) (C := insert m C)
      ((Finset.forall_mem_insert _ _ _).2 ⟨by omega, fun x hx => by have := hC x hx; omega⟩)
      (fun u hu => Finset.mem_insert.2 (.inl (by rw [pathDigraph_adj] at hu; omega)))
    -- Remove the midpoint by playing the first run backwards, with the end pebbled.
    have h₃ := reversiblePebbleGame_mTr_reverse pathDigraph_irrefl
      (ih (a := a) (C := insert top C)
        ((Finset.forall_mem_insert _ _ _).2 ⟨by omega, fun x hx => by have := hC x hx; omega⟩)
        (fun u hu => Finset.mem_insert_of_mem (ha u hu)))
      (by rw [Finset.card_insert_of_notMem htopC]; omega)
    rw [Finset.card_insert_of_notMem hmC] at h₂
    rw [Finset.card_insert_of_notMem htopC] at h₃
    have e₂ : a + 2 ^ k + 2 ^ k - 1 = top := by omega
    rw [e₂, Finset.insert_comm] at h₂
    rw [show bennettMoves a (k + 1) = bennettMoves a k ++ bennettMoves (a + 2 ^ k) k ++
      (bennettMoves a k).reverse.map Move.swap from rfl]
    exact LTS.MTr.comp _ (LTS.MTr.comp _ (reversiblePebbleGame_mTr_mono (by omega) h₁)
      (reversiblePebbleGame_mTr_mono (by omega) h₂)) (reversiblePebbleGame_mTr_mono (by omega) h₃)

/-- **Bennett's theorem on paths.** `k + 1` pebbles reversibly pebble the path of `2 ^ k`
vertices `0, …, 2 ^ k - 1` in `3 ^ k` moves, ending with only the last vertex pebbled. -/
theorem exists_mTr_bennett_pathDigraph (k : ℕ) : ∃ ms : List (Move ℕ), ms.length = 3 ^ k ∧
    (reversiblePebbleGame pathDigraph (k + 1)).MTr ∅ ms {2 ^ k - 1} := by
  refine ⟨bennettMoves 0 k, length_bennettMoves 0 k, ?_⟩
  have h := bennettMoves_mTr k (a := 0) (C := ∅) (by simp) fun _ hu => absurd hu pathDigraph_source
  rwa [Finset.card_empty, zero_add, zero_add, insert_empty_eq] at h

/-! ## Upper bounds -/

/-- Pebbling any vertex `v` of the block `a, …, a + 2 ^ k - 1` from `C`, ending with `insert v C`,
with `k + 1` extra pebbles. -/
theorem exists_mTr_insert_pathDigraph (k : ℕ) {a v : ℕ} {C : Finset ℕ} (hav : a ≤ v)
    (hv : v + 1 ≤ a + 2 ^ k) (hC : ∀ x ∈ C, x < a ∨ v < x)
    (ha : ∀ u, pathDigraph.Adj u a → u ∈ C) :
    ∃ ms, (reversiblePebbleGame pathDigraph (C.card + k + 1)).MTr C ms (insert v C) := by
  induction k generalizing a C with
  | zero =>
    rw [pow_zero] at hv
    obtain rfl : v = a := by omega
    have hnot : v ∉ C := fun h => by have := hC v h; omega
    exact ⟨_, LTS.MTr.single _ ⟨.place hnot ha, (Finset.card_insert_le _ _).trans (by omega)⟩⟩
  | succ k ih =>
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; omega
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    by_cases hlow : v + 1 ≤ a + 2 ^ k
    · obtain ⟨ms, hms⟩ := ih hav hlow hC ha
      exact ⟨ms, reversiblePebbleGame_mTr_mono (by omega) hms⟩
    · set m := a + 2 ^ k - 1 with hm
      have hmC : m ∉ C := fun h => by have := hC m h; omega
      have h₁ := bennettMoves_mTr k (a := a) (C := C) (fun x hx => by have := hC x hx; omega) ha
      obtain ⟨ms₂, h₂⟩ := ih (a := a + 2 ^ k) (C := insert m C) (by omega) (by omega)
        ((Finset.forall_mem_insert _ _ _).2 ⟨by omega, fun x hx => by have := hC x hx; omega⟩)
        (fun u hu => Finset.mem_insert.2 (.inl (by rw [pathDigraph_adj] at hu; omega)))
      have hvC : v ∉ C := fun h => by have := hC v h; omega
      have h₃ := reversiblePebbleGame_mTr_reverse pathDigraph_irrefl
        (bennettMoves_mTr k (a := a) (C := insert v C)
          ((Finset.forall_mem_insert _ _ _).2 ⟨by omega, fun x hx => by have := hC x hx; omega⟩)
          (fun u hu => Finset.mem_insert_of_mem (ha u hu)))
        (by rw [Finset.card_insert_of_notMem hvC]; omega)
      rw [Finset.card_insert_of_notMem hmC, Finset.insert_comm] at h₂
      rw [Finset.card_insert_of_notMem hvC] at h₃
      exact ⟨_, LTS.MTr.comp _ (LTS.MTr.comp _ (reversiblePebbleGame_mTr_mono (by omega) h₁)
        (reversiblePebbleGame_mTr_mono (by omega) h₂))
        (reversiblePebbleGame_mTr_mono (by omega) h₃)⟩

/-- Visiting any vertex `v` with `v + 2 ≤ a + 2 ^ k`, starting from the block at `a`, with `k`
extra pebbles. -/
private theorem exists_mTr_mem_pathDigraph (k : ℕ) {a v : ℕ} {C : Finset ℕ} (hav : a ≤ v)
    (hv : v + 2 ≤ a + 2 ^ k) (hC : ∀ x ∈ C, x < a) (ha : ∀ u, pathDigraph.Adj u a → u ∈ C) :
    ∃ ms D, (reversiblePebbleGame pathDigraph (C.card + k)).MTr C ms D ∧ v ∈ D := by
  induction k generalizing a C with
  | zero => rw [pow_zero] at hv; omega
  | succ k ih =>
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; omega
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    by_cases hlow : v + 2 ≤ a + 2 ^ k
    · obtain ⟨ms, D, hms, hvD⟩ := ih hav hlow hC ha
      exact ⟨ms, D, reversiblePebbleGame_mTr_mono (by omega) hms, hvD⟩
    · set m := a + 2 ^ k - 1 with hm
      have hmC : m ∉ C := fun h => by have := hC m h; omega
      have h₁ := bennettMoves_mTr k (a := a) (C := C) (fun x hx => .inl (hC x hx)) ha
      by_cases hvm : v = m
      · exact ⟨_, _, reversiblePebbleGame_mTr_mono (by omega) h₁,
          hvm ▸ Finset.mem_insert_self m C⟩
      obtain ⟨ms₂, D, h₂, hvD⟩ := ih (a := a + 2 ^ k) (C := insert m C) (by omega) (by omega)
        ((Finset.forall_mem_insert _ _ _).2 ⟨by omega, fun x hx => by have := hC x hx; omega⟩)
        (fun u hu => Finset.mem_insert.2 (.inl (by rw [pathDigraph_adj] at hu; omega)))
      rw [Finset.card_insert_of_notMem hmC] at h₂
      exact ⟨_, D, LTS.MTr.comp _ (reversiblePebbleGame_mTr_mono (by omega) h₁)
        (reversiblePebbleGame_mTr_mono (by omega) h₂), hvD⟩

theorem reversiblePebblable_pathDigraph {k v : ℕ} (h : v + 2 ≤ 2 ^ k) :
    ReversiblePebblable pathDigraph k v := by
  obtain ⟨ms, D, hms, hvD⟩ := exists_mTr_mem_pathDigraph k (a := 0) (C := ∅) (Nat.zero_le v)
    (by omega) (by simp) fun _ hu => absurd hu pathDigraph_source
  rw [Finset.card_empty, zero_add] at hms
  exact ⟨ms, D, hms, hvD⟩

theorem persistentReversiblePebblable_pathDigraph {k v : ℕ} (h : 2 * (v + 1) ≤ 2 ^ k) :
    PersistentReversiblePebblable pathDigraph k v := by
  cases k with
  | zero => rw [pow_zero] at h; omega
  | succ k =>
    rw [pow_succ] at h
    obtain ⟨ms, hms⟩ := exists_mTr_insert_pathDigraph k (a := 0) (C := ∅) (Nat.zero_le v)
      (by omega) (by simp) fun _ hu => absurd hu pathDigraph_source
    rw [Finset.card_empty, zero_add, insert_empty_eq] at hms
    exact ⟨ms, hms⟩

/-! ## Lower bounds -/

/-- The vertices at least `d`, shifted down by `d`. -/
private def shiftDown (d : ℕ) (C : Finset ℕ) : Finset ℕ :=
  (C.filter (d ≤ ·)).image (· - d)

private theorem mem_shiftDown {d x : ℕ} {C : Finset ℕ} : x ∈ shiftDown d C ↔ x + d ∈ C := by
  simp only [shiftDown, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨y, ⟨hy, hdy⟩, rfl⟩
    rwa [Nat.sub_add_cancel hdy]
  · exact fun h => ⟨x + d, ⟨h, Nat.le_add_left d x⟩, Nat.add_sub_cancel x d⟩

private theorem card_shiftDown_le (d : ℕ) (C : Finset ℕ) :
    (shiftDown d C).card ≤ (C.filter (d ≤ ·)).card :=
  Finset.card_image_le

/-- Shifting a move down by `d` gives either a move or no change. -/
private theorem RevStep.shift {d : ℕ} {C D : Finset ℕ} {m : Move ℕ}
    (h : RevStep pathDigraph C m D) :
    shiftDown d D = shiftDown d C ∨
      ∃ m', RevStep pathDigraph (shiftDown d C) m' (shiftDown d D) := by
  cases h with
  | @place v hv h =>
    by_cases hdv : d ≤ v
    · refine .inr ⟨.place (v - d), ?_⟩
      have e : shiftDown d (insert v C) = insert (v - d) (shiftDown d C) := by
        ext x
        simp only [mem_shiftDown, Finset.mem_insert]
        exact or_congr_left (by omega)
      rw [e]
      refine .place (fun hm => hv ?_) fun u hu => ?_
      · rw [mem_shiftDown, Nat.sub_add_cancel hdv] at hm
        exact hm
      · rw [pathDigraph_adj] at hu
        rw [mem_shiftDown]
        exact h _ (by rw [pathDigraph_adj]; omega)
    · refine .inl ?_
      ext x
      simp only [mem_shiftDown, Finset.mem_insert, or_iff_right_iff_imp]
      omega
  | @remove v hv h =>
    by_cases hdv : d ≤ v
    · refine .inr ⟨.remove (v - d), ?_⟩
      have e : shiftDown d (C.erase v) = (shiftDown d C).erase (v - d) := by
        ext x
        simp only [mem_shiftDown, Finset.mem_erase]
        exact and_congr_left' (by omega)
      rw [e]
      refine .remove (by rw [mem_shiftDown, Nat.sub_add_cancel hdv]; exact hv) fun u hu => ?_
      rw [pathDigraph_adj] at hu
      rw [mem_shiftDown]
      exact h _ (by rw [pathDigraph_adj]; omega)
    · refine .inl ?_
      ext x
      simp only [mem_shiftDown, Finset.mem_erase, and_iff_right_iff_imp]
      omega

/-- The least pebble of a configuration reachable with `k + 1` pebbles is at a vertex `c` with
`2 * (c + 1) ≤ 2 ^ (k + 1)`, given the bound `x + 2 ≤ 2 ^ k` for `k` pebbles. -/
private theorem minBound_succ {k : ℕ}
    (hmax : ∀ ms C x, (reversiblePebbleGame pathDigraph k).MTr ∅ ms C → x ∈ C → x + 2 ≤ 2 ^ k)
    {ms : List (Move ℕ)} {C : Finset ℕ} (h : (reversiblePebbleGame pathDigraph (k + 1)).MTr ∅ ms C)
    (hne : C.Nonempty) : 2 * (C.min' hne + 1) ≤ 2 ^ (k + 1) := by
  rw [pow_succ]
  obtain ⟨c, hc⟩ : ∃ c, C.min' hne = c := ⟨_, rfl⟩
  rw [hc]
  cases c with
  | zero => have := Nat.two_pow_pos k; omega
  | succ c =>
    have hcC : c + 1 ∈ C := hc ▸ C.min'_mem hne
    -- Play the run backwards, from `C` to `∅`, restricted to the vertices below `c + 1`.
    have hrev := reversiblePebbleGame_mTr_reverse pathDigraph_irrefl h (by simp)
    have claim : ∀ E D ms', (reversiblePebbleGame pathDigraph (k + 1)).MTr E ms' D → D = ∅ →
        c + 1 ∈ E → (∃ ms'', (reversiblePebbleGame pathDigraph k).MTr ∅ ms''
          (E.filter (· < c + 1))) →
        ∃ ms'' D', (reversiblePebbleGame pathDigraph k).MTr ∅ ms'' D' ∧ c ∈ D' := by
      intro E D ms' hED
      induction hED with
      | refl => rintro rfl hE; simp at hE
      | @stepL E₁ m E₂ ms' E₃ htr _ ih =>
        rintro rfl hE ⟨ms₁, h₁⟩
        by_cases hE₂ : c + 1 ∈ E₂
        · obtain ⟨ms₂, h₂⟩ : ∃ ms₂, (reversiblePebbleGame pathDigraph k).MTr ∅ ms₂
              (E₂.filter (· < c + 1)) := by
            rcases htr.1.filter (p := (· < c + 1)) (fun u v huv hv => by
              rw [pathDigraph_adj] at huv; omega) with he | ⟨m', hm'⟩
            · exact ⟨ms₁, he ▸ h₁⟩
            · refine ⟨ms₁ ++ [m'], LTS.MTr.stepR _ h₁ ⟨hm', ?_⟩⟩
              have hlt : (E₂.filter (· < c + 1)).card < E₂.card :=
                Finset.card_lt_card (Finset.filter_ssubset.2 ⟨c + 1, hE₂, by omega⟩)
              have := htr.2
              omega
          exact ih rfl hE₂ ⟨ms₂, h₂⟩
        · have hpred := htr.1.forall_adj_of_mem_iff (x := c + 1) (by simp [hE, hE₂])
          exact ⟨ms₁, _, h₁, Finset.mem_filter.2 ⟨hpred c (by simp), by omega⟩⟩
    have hfilter : C.filter (· < c + 1) = ∅ := Finset.filter_eq_empty_iff.2 fun x hx => by
      have := hc ▸ C.min'_le x hx
      omega
    obtain ⟨ms'', D', h'', hcD'⟩ := claim C ∅ _ hrev rfl hcC ⟨[], hfilter ▸ .refl⟩
    have := hmax ms'' D' c h'' hcD'
    omega

/-- The bound `x + 2 ≤ 2 ^ (k + 1)` for `k + 1` pebbles, from the bound for `k` pebbles. -/
private theorem maxBound_succ {k : ℕ}
    (hmax : ∀ ms C x, (reversiblePebbleGame pathDigraph k).MTr ∅ ms C → x ∈ C → x + 2 ≤ 2 ^ k)
    {ms : List (Move ℕ)} {C : Finset ℕ} {x : ℕ}
    (h : (reversiblePebbleGame pathDigraph (k + 1)).MTr ∅ ms C) (hx : x ∈ C) :
    x + 2 ≤ 2 ^ (k + 1) := by
  have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; omega
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  -- Along the run, the part at least `2 ^ k`, shifted down, is reachable with `k` pebbles.
  have key : ∀ E ms' D, (reversiblePebbleGame pathDigraph (k + 1)).MTr E ms' D →
      (∃ ms₀, (reversiblePebbleGame pathDigraph (k + 1)).MTr ∅ ms₀ E) →
      (∃ ms₁, (reversiblePebbleGame pathDigraph k).MTr ∅ ms₁ (shiftDown (2 ^ k) E)) →
      ∃ ms₁, (reversiblePebbleGame pathDigraph k).MTr ∅ ms₁ (shiftDown (2 ^ k) D) := by
    intro E ms' D hED
    induction hED with
    | refl => exact fun _ h => h
    | @stepL E₁ m E₂ ms' E₃ htr _ ih =>
      rintro ⟨ms₀, h₀⟩ ⟨ms₁, h₁⟩
      have h₀' : (reversiblePebbleGame pathDigraph (k + 1)).MTr ∅ (ms₀ ++ [m]) E₂ :=
        LTS.MTr.stepR _ h₀ htr
      refine ih ⟨_, h₀'⟩ ?_
      rcases htr.1.shift (d := 2 ^ k) with he | ⟨m', hm'⟩
      · exact ⟨ms₁, he ▸ h₁⟩
      · refine ⟨ms₁ ++ [m'], LTS.MTr.stepR _ h₁ ⟨hm', ?_⟩⟩
        refine (card_shiftDown_le _ _).trans ?_
        by_cases hlow : ∃ y ∈ E₂, y < 2 ^ k
        · obtain ⟨y, hy, hyk⟩ := hlow
          have hlt : (E₂.filter (2 ^ k ≤ ·)).card < E₂.card :=
            Finset.card_lt_card (Finset.filter_ssubset.2 ⟨y, hy, by omega⟩)
          have := htr.2
          omega
        · obtain rfl | hne := E₂.eq_empty_or_nonempty
          · simp
          · have hmin := minBound_succ hmax h₀' hne
            exact absurd ⟨_, E₂.min'_mem hne, by omega⟩ hlow
  have e₀ : shiftDown (2 ^ k) (∅ : Finset ℕ) = ∅ := by simp [shiftDown]
  obtain ⟨ms₁, h₁⟩ := key ∅ ms C h ⟨[], .refl⟩ ⟨[], e₀ ▸ .refl⟩
  by_cases hxk : x < 2 ^ k
  · omega
  · have := hmax ms₁ _ (x - 2 ^ k) h₁
      (by rw [mem_shiftDown, Nat.sub_add_cancel (by omega)]; exact hx)
    omega

/-- **The lower bound.** Every pebble of a configuration reachable with `k` pebbles on the
directed path lies at a vertex `v` with `v + 2 ≤ 2 ^ k` ([LiTrompVitanyi1998], Corollary 2). -/
theorem add_two_le_of_reversiblePebbleGame_pathDigraph_mTr {k : ℕ} {ms : List (Move ℕ)}
    {C : Finset ℕ}
    (h : (reversiblePebbleGame pathDigraph k).MTr ∅ ms C) {v : ℕ} (hv : v ∈ C) :
    v + 2 ≤ 2 ^ k := by
  induction k generalizing ms C v with
  | zero =>
    have := card_le_of_reversiblePebbleGame_mTr h (by simp)
    exact absurd (Finset.card_pos.2 ⟨v, hv⟩) (by omega)
  | succ k ih => exact maxBound_succ (fun _ _ _ h hx => ih h hx) h hv

/-- The least pebble of a nonempty configuration reachable with `k` pebbles on the directed path
lies at a vertex `c` with `2 * (c + 1) ≤ 2 ^ k`. -/
theorem two_mul_min_add_one_le_of_reversiblePebbleGame_pathDigraph_mTr {k : ℕ} {ms : List (Move ℕ)}
    {C : Finset ℕ} (h : (reversiblePebbleGame pathDigraph k).MTr ∅ ms C) (hne : C.Nonempty) :
    2 * (C.min' hne + 1) ≤ 2 ^ k := by
  cases k with
  | zero =>
    have := card_le_of_reversiblePebbleGame_mTr h (by simp)
    exact absurd (Finset.card_pos.2 hne) (by omega)
  | succ k =>
    exact minBound_succ
      (fun _ _ _ h hx => add_two_le_of_reversiblePebbleGame_pathDigraph_mTr h hx) h hne

/-! ## Exact prices -/

/-- **Reversible pebbling of the path.** With `k` pebbles, a configuration containing `v` is
reachable iff `v + 2 ≤ 2 ^ k`. -/
theorem reversiblePebblable_pathDigraph_iff {k v : ℕ} :
    ReversiblePebblable pathDigraph k v ↔ v + 2 ≤ 2 ^ k :=
  ⟨fun ⟨_, _, h, hv⟩ => add_two_le_of_reversiblePebbleGame_pathDigraph_mTr h hv,
    reversiblePebblable_pathDigraph⟩

/-- **Persistent reversible pebbling of the path.** With `k` pebbles, the configuration `{v}` is
reachable iff `2 * (v + 1) ≤ 2 ^ k`. -/
theorem persistentReversiblePebblable_pathDigraph_iff {k v : ℕ} :
    PersistentReversiblePebblable pathDigraph k v ↔ 2 * (v + 1) ≤ 2 ^ k := by
  refine ⟨fun ⟨_, h⟩ => ?_, persistentReversiblePebblable_pathDigraph⟩
  have := two_mul_min_add_one_le_of_reversiblePebbleGame_pathDigraph_mTr h
    (Finset.singleton_nonempty v)
  rwa [Finset.min'_singleton] at this

/-- The reversible pebbling price of vertex `v` of the directed path is `⌈log₂ (v + 2)⌉`. -/
theorem reversiblePebblingPrice_pathDigraph (v : ℕ) :
    reversiblePebblingPrice pathDigraph v = Nat.clog 2 (v + 2) :=
  reversiblePebblingPrice_eq
    (reversiblePebblable_pathDigraph_iff.2 (Nat.le_pow_clog Nat.one_lt_two _))
    fun _ h => (Nat.clog_le_iff_le_pow Nat.one_lt_two).2 (reversiblePebblable_pathDigraph_iff.1 h)

/-- The persistent reversible pebbling price of vertex `v` of the directed path is
`⌈log₂ (v + 1)⌉ + 1`. -/
theorem persistentReversiblePebblingPrice_pathDigraph (v : ℕ) :
    persistentReversiblePebblingPrice pathDigraph v = Nat.clog 2 (v + 1) + 1 := by
  refine persistentReversiblePebblingPrice_eq
    (persistentReversiblePebblable_pathDigraph_iff.2 ?_) fun s h => ?_
  · rw [pow_succ]
    have := Nat.le_pow_clog (b := 2) Nat.one_lt_two (v + 1)
    omega
  · have h := persistentReversiblePebblable_pathDigraph_iff.1 h
    cases s with
    | zero => rw [pow_zero] at h; omega
    | succ s =>
      rw [pow_succ] at h
      exact Nat.succ_le_succ ((Nat.clog_le_iff_le_pow Nat.one_lt_two).2 (by omega))

/-- **Optimality of Bennett's strategy, visiting form.** The last vertex `2 ^ k - 1` of a path of
`2 ^ k` vertices has reversible price `k + 1`: with `k` pebbles it cannot even be visited. -/
theorem reversiblePebblingPrice_pathDigraph_two_pow_sub_one (k : ℕ) :
    reversiblePebblingPrice pathDigraph (2 ^ k - 1) = k + 1 := by
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  refine reversiblePebblingPrice_eq (reversiblePebblable_pathDigraph_iff.2 ?_) fun s h => ?_
  · rw [pow_succ]
    omega
  · have h := reversiblePebblable_pathDigraph_iff.1 h
    by_contra hs
    have := Nat.pow_le_pow_right Nat.two_pos (show s ≤ k by omega)
    omega

/-- **Optimality of Bennett's strategy.** Ending with only the last vertex `2 ^ k - 1` of a path of
`2 ^ k` vertices pebbled costs exactly `k + 1` pebbles, the budget of
`exists_mTr_bennett_pathDigraph`. -/
theorem persistentReversiblePebblingPrice_pathDigraph_two_pow_sub_one (k : ℕ) :
    persistentReversiblePebblingPrice pathDigraph (2 ^ k - 1) = k + 1 := by
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  refine persistentReversiblePebblingPrice_eq
    (persistentReversiblePebblable_pathDigraph_iff.2 ?_) fun s h => ?_
  · rw [pow_succ]
    omega
  · have h := persistentReversiblePebblable_pathDigraph_iff.1 h
    by_contra hs
    have := Nat.pow_le_pow_right Nat.two_pos (show s ≤ k by omega)
    omega

end Cslib.Pebbling
