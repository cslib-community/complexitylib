/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.EhrenfeuchtFraisse.Hintikka
public import Mathlib.ModelTheory.Order
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Finset.Sort

/-!
# Ehrenfeucht–Fraïssé games on finite linear orders

Finite linear orders are structures in Mathlib's language of orders `FirstOrder.Language.order`,
whose only symbol is the binary relation `≤`, interpreted by the order of the type
(`Language.order.OrderedStructure`). Duplicator wins the `n`-round Ehrenfeucht–Fraïssé game on two
finite linear orders exactly when they have the same number of elements or both have at least
`2 ^ n - 1` elements (`duplicatorWins_iff_card`). By the Ehrenfeucht–Fraïssé theorem, a sentence
of quantifier rank `n` therefore has the same truth value in all finite linear orders with at
least `2 ^ n - 1` elements (`realize_iff_of_two_pow_le_card`), and the bound cannot be lowered
(`exists_sentence_of_card_ne`). In particular, **EVEN is not first-order definable on finite
linear orders**, even when only orders above a size threshold are considered
(`not_exists_sentence_realize_iff_even`).

Libkin states the sufficient condition with the threshold `2 ^ n` for both orders; the sharp form
proved here, with threshold `2 ^ n - 1` and its converse, is the characterization of
`n`-equivalence of finite linear orders in Kolaitis's survey [Kolaitis2007]. Duplicator's strategy
keeps every gap between consecutive pebbles (and the two virtual endpoints) either equal in both
orders or at least `2 ^ r` in both, `r` being the number of rounds left; Spoiler wins from any
other position by splitting the longer of two different gaps.

## Use in ordered descriptive complexity

Ordered descriptive complexity in this library follows Immerman: structures on `Fin n` carry the
numeric vocabulary `≤`, `BIT`, `0`, `1`, `max` (`Complexity.Logics.FirstOrder.Ordered.Basic`).
The results here concern the pure order vocabulary FO(≤). The constants `0`, `1`, `max` are
FO(≤)-definable, but `BIT` is not: EVEN is defined in FO(≤, BIT) by the least significant bit of
`max`, so the nondefinability of EVEN shows that `BIT` adds expressive power over `≤`. To apply
these results to a query on ordered structures, state it for Mathlib's `Language.order` (for
example on `Fin n` with `orderStructure`), and use `realize_iff_of_two_pow_le_card` to show that
no sentence has the required truth values on two large orders. The game itself
(`Complexity.Logics.FirstOrder.EhrenfeuchtFraisse.Basic`) is for relational vocabularies; numeric
constants must first be replaced by their defining formulas.

## Main results

* `Cslib.Logic.FO.FiniteLinearOrder.duplicatorWins_iff_card`: Duplicator wins the `n`-round
  game on two finite linear orders iff they have equal size or both have size at least
  `2 ^ n - 1`.
* `Cslib.Logic.FO.FiniteLinearOrder.realize_iff_of_two_pow_le_card`: no sentence of quantifier
  rank at most `n` distinguishes two finite linear orders of size at least `2 ^ n - 1`.
* `Cslib.Logic.FO.FiniteLinearOrder.exists_sentence_of_card_ne`: the bound is sharp.
* `Cslib.Logic.FO.FiniteLinearOrder.not_exists_sentence_realize_iff_even`: EVEN is not
  first-order definable on finite linear orders.

## References

* [P. G. Kolaitis, *On the expressive power of logics on finite models*][Kolaitis2007], Chapter 2
  of *Finite Model Theory and Its Applications* (the sharp characterization of `n`-equivalent
  finite linear orders).
* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004], Chapter 3 (linear orders of
  size at least `2 ^ n` are indistinguishable in `n` rounds; EVEN is not definable over orders).
-/

public section

open FirstOrder Language Structure

namespace Cslib.Logic.FO.FiniteLinearOrder

/-! ### Gaps -/

/-- Two gaps are indistinguishable at threshold `P`: they are equal, or both at least `P`, or both
at most `-P`. -/
private def GapClose (P x y : ℤ) : Prop := x = y ∨ (P ≤ x ∧ P ≤ y) ∨ (x ≤ -P ∧ y ≤ -P)

private theorem GapClose.mono {P Q x y : ℤ} (hPQ : Q ≤ P) (h : GapClose P x y) :
    GapClose Q x y := by
  unfold GapClose at *; omega

private theorem GapClose.neg {P x y : ℤ} (h : GapClose P x y) : GapClose P (-x) (-y) := by
  unfold GapClose at *; omega

private theorem GapClose.symm {P x y : ℤ} (h : GapClose P x y) : GapClose P y x := by
  unfold GapClose at *; omega

private theorem GapClose.add {P x y x' y' : ℤ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hx' : 0 ≤ x')
    (hy' : 0 ≤ y') (h : GapClose P x y) (h' : GapClose P x' y') :
    GapClose P (x + x') (y + y') := by
  unfold GapClose at *; omega

/-- **Splitting a gap.** If two positive gaps `G` and `H` are indistinguishable at threshold `2P`,
then every split of `G` into two positive parts is matched by a split of `H` into two positive
parts, part by part indistinguishable at threshold `P`. -/
private theorem GapClose.split {P G H u : ℤ} (hP : 1 ≤ P) (hH : 0 < H)
    (h : GapClose (2 * P) G H) (hu : 0 < u) (huG : u < G) :
    ∃ v, 0 < v ∧ v < H ∧ GapClose P u v ∧ GapClose P (G - u) (H - v) := by
  unfold GapClose at *
  rcases h with h | h | h
  · exact ⟨u, by omega, by omega, by omega, by omega⟩
  · by_cases hu' : u < P
    · exact ⟨u, by omega, by omega, by omega, by omega⟩
    · by_cases hu'' : G - u < P
      · exact ⟨H - (G - u), by omega, by omega, by omega, by omega⟩
      · exact ⟨P, by omega, by omega, by omega, by omega⟩
  · omega

/-! ### Coordinates -/

variable {M : Type*} {N : Type*} [_root_.LinearOrder M] [_root_.LinearOrder N]

/-- An order embedding of `M` onto the integers `0, …, m - 1`. -/
private structure Coords (M : Type*) [_root_.LinearOrder M] (m : ℕ) where
  pos : M → ℤ
  lt_iff : ∀ x y, pos x < pos y ↔ x < y
  nonneg : ∀ x, 0 ≤ pos x
  lt_card : ∀ x, pos x < m
  surj : ∀ z : ℤ, 0 ≤ z → z < m → ∃ x, pos x = z

private theorem Coords.le_iff {m : ℕ} (C : Coords M m) (x y : M) : C.pos x ≤ C.pos y ↔ x ≤ y := by
  rw [← not_lt, ← not_lt, C.lt_iff]

private theorem Coords.eq_iff {m : ℕ} (C : Coords M m) (x y : M) : C.pos x = C.pos y ↔ x = y := by
  rw [le_antisymm_iff, le_antisymm_iff, C.le_iff, C.le_iff]

private theorem Coords.bounds {m : ℕ} (C : Coords M m) (x : M) : 0 ≤ C.pos x ∧ C.pos x < m :=
  ⟨C.nonneg x, C.lt_card x⟩

private theorem Coords.nonempty [Finite M] : Nonempty (Coords M (Nat.card M)) := by
  have := Fintype.ofFinite M
  let e := Fintype.orderIsoFinOfCardEq M (Nat.card_eq_fintype_card (α := M)).symm
  refine ⟨⟨fun x => ((e.symm x : Fin _) : ℕ), fun x y => ?_, fun x => by positivity,
    fun x => by exact_mod_cast (e.symm x).2, fun z hz hzm => ?_⟩⟩
  · rw [Nat.cast_lt, Fin.val_fin_lt, e.symm.lt_iff_lt]
  · refine ⟨e ⟨z.toNat, by omega⟩, ?_⟩
    simp only [OrderIso.symm_apply_apply]
    omega

/-! ### Positions -/

/-- The coordinates of the pebbles of a position, with the two virtual endpoints `-1` and `m`. -/
private def ext {m k : ℕ} (C : Coords M m) (a : Fin k → M) : Option (Option (Fin k)) → ℤ
  | none => -1
  | some none => m
  | some (some i) => C.pos (a i)

private theorem ext_bounds {m k : ℕ} (C : Coords M m) (a : Fin k → M)
    (p : Option (Option (Fin k))) :
    -1 ≤ ext C a p ∧ ext C a p ≤ m := by
  rcases p with _ | _ | i
  · simp [ext]
  · simp [ext]
  · exact ⟨by have := C.nonneg (a i); simp only [ext]; omega,
      by have := C.lt_card (a i); simp only [ext]; omega⟩

/-- The invariant of Duplicator's strategy with `r` rounds to play: every gap between two pebbles
(or virtual endpoints) is indistinguishable at threshold `2 ^ r`. -/
private def Good {m m' k : ℕ} (C : Coords M m) (D : Coords N m') (r : ℕ) (a : Fin k → M)
    (b : Fin k → N) : Prop :=
  ∀ p q, GapClose (2 ^ r) (ext C a q - ext C a p) (ext D b q - ext D b p)

private theorem Good.mono {m m' k r s : ℕ} {C : Coords M m} {D : Coords N m'} {a : Fin k → M}
    {b : Fin k → N} (hrs : s ≤ r) (h : Good C D r a b) : Good C D s a b :=
  fun p q => (h p q).mono (by exact_mod_cast Nat.pow_le_pow_right (by norm_num) hrs)

private theorem good_zero_tuple {m m' r : ℕ} (C : Coords M m) (D : Coords N m') (h : m = m' ∨
    (2 ^ r ≤ m + 1 ∧ 2 ^ r ≤ m' + 1)) :
    Good C D r (default : Fin 0 → M) (default : Fin 0 → N) := by
  have h' : (m : ℤ) = m' ∨ ((2 : ℤ) ^ r ≤ m + 1 ∧ (2 : ℤ) ^ r ≤ m' + 1) := by
    rcases h with h | h
    · exact .inl (by exact_mod_cast h)
    · exact .inr ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
  rintro (_ | _ | i) (_ | _ | j)
  all_goals try first | exact i.elim0 | exact j.elim0
  all_goals simp only [ext, GapClose, sub_self, true_or]
  all_goals omega

/-! ### Extending a position -/

/-- The pebbles and endpoints of a position, as pebbles and endpoints of its one-point
extensions. -/
private def lift {k : ℕ} : Option (Option (Fin k)) → Option (Option (Fin (k + 1)))
  | none => none
  | some none => some none
  | some (some i) => some (some i.castSucc)

private theorem ext_lift {m k : ℕ} (C : Coords M m) (a : Fin k → M) (c : M)
    (p : Option (Option (Fin k))) :
    ext C (Fin.snoc a c : Fin (k + 1) → M) (lift p) = ext C a p := by
  rcases p with _ | _ | i <;> simp [lift, ext]

private theorem ext_last {m k : ℕ} (C : Coords M m) (a : Fin k → M) (c : M) :
    ext C (Fin.snoc a c : Fin (k + 1) → M) (some (some (Fin.last k))) = C.pos c := by
  simp [ext]

private theorem eq_lift_or_eq_last {k : ℕ} (p : Option (Option (Fin (k + 1)))) :
    (∃ p', p = lift p') ∨ p = some (some (Fin.last k)) := by
  rcases p with _ | _ | i
  · exact .inl ⟨none, rfl⟩
  · exact .inl ⟨some none, rfl⟩
  · induction i using Fin.lastCases with
    | last => exact .inr rfl
    | cast i => exact .inl ⟨some (some i), rfl⟩

private theorem good_succ_iff {m m' k r : ℕ} {C : Coords M m} {D : Coords N m'} {a : Fin k → M}
    {b : Fin k → N} : Good C D (r + 1) a b ↔
      ∀ p q, GapClose (2 * 2 ^ r) (ext C a q - ext C a p) (ext D b q - ext D b p) := by
  simp only [Good, pow_succ, mul_comm]

private theorem Good.snoc {m m' k r : ℕ} {C : Coords M m} {D : Coords N m'} {a : Fin k → M}
    {b : Fin k → N} (h : Good C D (r + 1) a b) (c : M) (d : N)
    (hnew : ∀ p, GapClose (2 ^ r) (C.pos c - ext C a p) (D.pos d - ext D b p)) :
    Good C D r (Fin.snoc a c : Fin (k + 1) → M) (Fin.snoc b d : Fin (k + 1) → N) := by
  intro p q
  rcases eq_lift_or_eq_last p with ⟨p, rfl⟩ | rfl <;>
    rcases eq_lift_or_eq_last q with ⟨q, rfl⟩ | rfl <;>
    simp only [ext_lift, ext_last]
  · exact (h p q).mono (by exact_mod_cast Nat.pow_le_pow_right (by norm_num) (Nat.le_succ r))
  · exact hnew p
  · have := (hnew q).neg
    rwa [neg_sub, neg_sub] at this
  · simp [GapClose]

/-- **Forth.** A position satisfying the invariant with `r + 1` rounds to play can be extended,
for every move of Spoiler in the first order, to a position satisfying it with `r` rounds. -/
private theorem Good.forth {m m' k r : ℕ} {C : Coords M m} {D : Coords N m'} {a : Fin k → M}
    {b : Fin k → N} (h : Good C D (r + 1) a b) (c : M) :
    ∃ d, Good C D r (Fin.snoc a c : Fin (k + 1) → M) (Fin.snoc b d : Fin (k + 1) → N) := by
  have hP : (1 : ℤ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
  have h' := good_succ_iff.1 h
  have hc0 := C.nonneg c
  have hcm := C.lt_card c
  by_cases hx : ∃ p, ext C a p = C.pos c
  · obtain ⟨p₀, hp₀⟩ := hx
    rcases p₀ with _ | _ | i
    · simp only [ext] at hp₀; omega
    · simp only [ext] at hp₀; omega
    · refine ⟨b i, h.snoc c (b i) fun p => ?_⟩
      have := h' p (some (some i))
      simp only [ext] at hp₀ this ⊢
      rw [← hp₀]
      unfold GapClose at this ⊢
      omega
  · simp only [not_exists] at hx
    classical
    obtain ⟨pl, hpl, hplmax⟩ : ∃ pl, ext C a pl < C.pos c ∧
        ∀ p, ext C a p < C.pos c → ext C a p ≤ ext C a pl := by
      have hne : (Finset.univ.filter fun p => ext C a p < C.pos c).Nonempty :=
        ⟨none, Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp only [ext]; omega⟩⟩
      obtain ⟨pl, hmem, hmax⟩ := Finset.exists_max_image _ (ext C a) hne
      exact ⟨pl, (Finset.mem_filter.1 hmem).2,
        fun p hp => hmax p (Finset.mem_filter.2 ⟨Finset.mem_univ _, hp⟩)⟩
    obtain ⟨pr, hpr, hprmin⟩ : ∃ pr, C.pos c < ext C a pr ∧
        ∀ p, C.pos c < ext C a p → ext C a pr ≤ ext C a p := by
      have hne : (Finset.univ.filter fun p => C.pos c < ext C a p).Nonempty :=
        ⟨some none, Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp only [ext]; omega⟩⟩
      obtain ⟨pr, hmem, hmin⟩ := Finset.exists_min_image _ (ext C a) hne
      exact ⟨pr, (Finset.mem_filter.1 hmem).2,
        fun p hp => hmin p (Finset.mem_filter.2 ⟨Finset.mem_univ _, hp⟩)⟩
    have hG := h' pl pr
    have hHpos : 0 < ext D b pr - ext D b pl := by unfold GapClose at hG; omega
    obtain ⟨v, hv0, hvH, hv1, hv2⟩ :=
      GapClose.split (u := C.pos c - ext C a pl) hP hHpos hG (by omega) (by omega)
    have hbl := ext_bounds D b pl
    have hbr := ext_bounds D b pr
    obtain ⟨d, hd⟩ := D.surj (ext D b pl + v) (by omega) (by omega)
    refine ⟨d, h.snoc c d fun p => ?_⟩
    rw [hd]
    rcases lt_or_gt_of_ne (hx p) with hlt | hgt
    · have hle := hplmax p hlt
      have hp := h' p pl
      unfold GapClose at hp hv1 ⊢
      omega
    · have hle := hprmin p hgt
      have hp := h' pr p
      unfold GapClose at hp hv2 ⊢
      omega

private theorem Good.symm {m m' k r : ℕ} {C : Coords M m} {D : Coords N m'} {a : Fin k → M}
    {b : Fin k → N} (h : Good C D r a b) : Good D C r b a :=
  fun p q => (h p q).symm

/-- **Back.** -/
private theorem Good.back {m m' k r : ℕ} {C : Coords M m} {D : Coords N m'} {a : Fin k → M}
    {b : Fin k → N} (h : Good C D (r + 1) a b) (d : N) :
    ∃ c, Good C D r (Fin.snoc a c : Fin (k + 1) → M) (Fin.snoc b d : Fin (k + 1) → N) :=
  (h.symm.forth d).imp fun _ hc => hc.symm

/-! ### The game on linear orders -/

variable [Language.order.Structure M] [Language.order.OrderedStructure M]
  [Language.order.Structure N] [Language.order.OrderedStructure N]

private theorem relMap_order_iff {k l : ℕ} (R : Language.order.Relations l) (f : Fin l → Fin k)
    (a : Fin k → M) : RelMap R (a ∘ f) ↔ ∃ h : l = 2, a (f (h ▸ 0)) ≤ a (f (h ▸ 1)) := by
  cases R
  exact (relMap_leSymb (L := Language.order) _).trans ⟨fun h => ⟨rfl, h⟩, fun ⟨_, h⟩ => h⟩

private theorem Good.partialIso {m m' k r : ℕ} {C : Coords M m} {D : Coords N m'} {a : Fin k → M}
    {b : Fin k → N} (h : Good C D r a b) : PartialIso Language.order a b := by
  have h0 : Good C D 0 a b := h.mono (Nat.zero_le r)
  have hij : ∀ i j, (C.pos (a i) ≤ C.pos (a j) ↔ D.pos (b i) ≤ D.pos (b j)) := fun i j => by
    have := h0 (some (some i)) (some (some j))
    simp only [ext, pow_zero, GapClose] at this
    omega
  refine ⟨fun i j => ?_, fun R f => ?_⟩
  · rw [← C.eq_iff, ← D.eq_iff, le_antisymm_iff, le_antisymm_iff, hij, hij]
  · rw [relMap_order_iff, relMap_order_iff]
    refine exists_congr fun hl => ?_
    subst hl
    rw [← C.le_iff, ← D.le_iff]
    exact hij _ _

private theorem relMap_le_iff {k : ℕ} (a : Fin k → M) (i j : Fin k) :
    RelMap (leSymb : Language.order.Relations 2) (a ∘ ![i, j]) ↔ a i ≤ a j :=
  relMap_leSymb _

private theorem partialIso_good_zero {m m' k : ℕ} {C : Coords M m} {D : Coords N m'} {a : Fin k → M}
    {b : Fin k → N} (h : PartialIso Language.order a b) : Good C D 0 a b := by
  have hle : ∀ i j, C.pos (a i) ≤ C.pos (a j) ↔ D.pos (b i) ≤ D.pos (b j) := fun i j => by
    have := h.relMap_iff leSymb ![i, j]
    rw [relMap_le_iff, relMap_le_iff] at this
    rw [C.le_iff, D.le_iff]
    exact this
  have heq : ∀ i j, C.pos (a i) = C.pos (a j) ↔ D.pos (b i) = D.pos (b j) := fun i j => by
    rw [C.eq_iff, D.eq_iff]
    exact h.eq_iff i j
  rintro (_ | _ | i) (_ | _ | j)
  all_goals simp only [ext, pow_zero, GapClose, sub_self, true_or]
  · omega
  · have := C.bounds (a j); have := D.bounds (b j); omega
  · omega
  · have := C.bounds (a j); have := D.bounds (b j); omega
  · have := C.bounds (a i); have := D.bounds (b i); omega
  · have := C.bounds (a i); have := D.bounds (b i); omega
  · have := hle i j; have := hle j i; have := heq i j; omega

/-- Duplicator's winning positions satisfy the invariant: Spoiler wins from a position with a gap
that is too short against a different gap, by splitting the longer one. -/
private theorem DuplicatorWins.good {m m' : ℕ} {C : Coords M m} {D : Coords N m'} :
    ∀ {r k : ℕ} {a : Fin k → M} {b : Fin k → N}, DuplicatorWins Language.order r a b →
      Good C D r a b
  | 0, _, _, _, h => partialIso_good_zero h.partialIso
  | r + 1, k, a, b, h => by
    obtain ⟨hp, hforth, hback⟩ := duplicatorWins_succ.1 h
    have hP : (1 : ℤ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
    have h0 := partialIso_good_zero (C := C) (D := D) hp
    have key : ∀ p q, ext C a p < ext C a q →
        GapClose (2 * 2 ^ r) (ext C a q - ext C a p) (ext D b q - ext D b p) := by
      intro p q hpq
      have h0pq := h0 p q
      simp only [pow_zero] at h0pq
      have hbp := ext_bounds D b p
      have hbq := ext_bounds D b q
      have hap := ext_bounds C a p
      have haq := ext_bounds C a q
      by_contra hne
      unfold GapClose at h0pq hne
      rcases lt_or_gt_of_ne (show ext C a q - ext C a p ≠ ext D b q - ext D b p by omega)
        with hGH | hGH
      · -- Spoiler splits the longer gap in `N`.
        obtain ⟨v, hv1, hv2, hv⟩ : ∃ v : ℤ, 1 ≤ v ∧ ext C a q - ext C a p - 2 ^ r + 1 ≤ v ∧
            (v = 1 ∨ v = ext C a q - ext C a p - 2 ^ r + 1) :=
          ⟨max 1 (ext C a q - ext C a p - 2 ^ r + 1), le_max_left _ _, le_max_right _ _,
            max_choice _ _⟩
        obtain ⟨y, hy⟩ := D.surj (ext D b p + v) (by omega) (by omega)
        obtain ⟨x, hx⟩ := hback y
        have hg := DuplicatorWins.good (C := C) (D := D) hx
        have g1 := hg (lift p) (some (some (Fin.last k)))
        have g2 := hg (some (some (Fin.last k))) (lift q)
        rw [ext_lift, ext_lift, ext_last, ext_last, hy] at g1 g2
        unfold GapClose at g1 g2
        omega
      · -- Spoiler splits the longer gap in `M`.
        obtain ⟨v, hv1, hv2, hv⟩ : ∃ v : ℤ, 1 ≤ v ∧ ext D b q - ext D b p - 2 ^ r + 1 ≤ v ∧
            (v = 1 ∨ v = ext D b q - ext D b p - 2 ^ r + 1) :=
          ⟨max 1 (ext D b q - ext D b p - 2 ^ r + 1), le_max_left _ _, le_max_right _ _,
            max_choice _ _⟩
        obtain ⟨x, hx⟩ := C.surj (ext C a p + v) (by omega) (by omega)
        obtain ⟨y, hy⟩ := hforth x
        have hg := DuplicatorWins.good (C := C) (D := D) hy
        have g1 := hg (lift p) (some (some (Fin.last k)))
        have g2 := hg (some (some (Fin.last k))) (lift q)
        rw [ext_lift, ext_lift, ext_last, ext_last, hx] at g1 g2
        unfold GapClose at g1 g2
        omega
    refine good_succ_iff.2 fun p q => ?_
    rcases lt_trichotomy (ext C a p) (ext C a q) with hpq | hpq | hpq
    · exact key p q hpq
    · have h0pq := h0 p q
      simp only [pow_zero, GapClose] at h0pq
      left
      omega
    · have := (key q p hpq).neg
      rwa [neg_sub, neg_sub] at this

private theorem isBackAndForth_good {m m' : ℕ} (C : Coords M m) (D : Coords N m') :
    IsBackAndForth Language.order fun r _ a b => Good C D r a b :=
  ⟨Good.partialIso, Good.forth, Good.back⟩

private theorem duplicatorWins_iff_good {m m' r k : ℕ} (C : Coords M m) (D : Coords N m')
    {a : Fin k → M} {b : Fin k → N} : DuplicatorWins Language.order r a b ↔ Good C D r a b :=
  ⟨DuplicatorWins.good, (isBackAndForth_good C D).duplicatorWins⟩

/-- **Ehrenfeucht–Fraïssé games on finite linear orders** [Kolaitis2007]. Duplicator wins the
`n`-round game on two finite linear orders exactly when they have the same size or both have at
least `2 ^ n - 1` elements. -/
theorem duplicatorWins_iff_card [Finite M] [Finite N] {n : ℕ} {a : Fin 0 → M} {b : Fin 0 → N} :
    DuplicatorWins Language.order n a b ↔
      Nat.card M = Nat.card N ∨ (2 ^ n ≤ Nat.card M + 1 ∧ 2 ^ n ≤ Nat.card N + 1) := by
  obtain rfl := Subsingleton.elim a default
  obtain rfl := Subsingleton.elim b default
  obtain ⟨C⟩ := Coords.nonempty (M := M)
  obtain ⟨D⟩ := Coords.nonempty (M := N)
  rw [duplicatorWins_iff_good C D]
  refine ⟨fun h => ?_, good_zero_tuple C D⟩
  have := h none (some none)
  simp only [ext, GapClose] at this
  have h2 : (0 : ℤ) < 2 ^ n := by positivity
  rcases this with h1 | h1 | h1
  · exact .inl (by omega)
  · exact .inr ⟨by exact_mod_cast (show (2 : ℤ) ^ n ≤ Nat.card M + 1 by omega),
      by exact_mod_cast (show (2 : ℤ) ^ n ≤ Nat.card N + 1 by omega)⟩
  · omega

/-- No first-order sentence of quantifier rank at most `n` distinguishes two finite linear orders
with at least `2 ^ n - 1` elements each. -/
theorem realize_iff_of_two_pow_le_card [Finite M] [Finite N] {n : ℕ}
    (hM : 2 ^ n ≤ Nat.card M + 1) (hN : 2 ^ n ≤ Nat.card N + 1) {φ : Language.order.Sentence}
    (hφ : quantifierRank φ ≤ n) : M ⊨ φ ↔ N ⊨ φ :=
  duplicatorWins_iff_forall_sentence.1
    ((duplicatorWins_iff_card (a := default) (b := default)).2 (.inr ⟨hM, hN⟩)) φ hφ

/-- The bound is sharp: two finite linear orders of different sizes, one of them with fewer than
`2 ^ n - 1` elements, are distinguished by a sentence of quantifier rank at most `n`. -/
theorem exists_sentence_of_card_ne [Finite M] [Finite N] {n : ℕ} (hne : Nat.card M ≠ Nat.card N)
    (h : Nat.card M + 1 < 2 ^ n ∨ Nat.card N + 1 < 2 ^ n) :
    ∃ φ : Language.order.Sentence, quantifierRank φ ≤ n ∧ M ⊨ φ ∧ ¬ N ⊨ φ := by
  have hw : ¬ DuplicatorWins Language.order n (default : Fin 0 → M) (default : Fin 0 → N) := by
    rw [duplicatorWins_iff_card]
    omega
  rw [duplicatorWins_iff_forall_sentence] at hw
  simp only [not_forall] at hw
  obtain ⟨φ, hφ, h⟩ := hw
  by_cases hM : M ⊨ φ
  · exact ⟨φ, hφ, hM, fun hN => h (iff_of_true hM hN)⟩
  · refine ⟨φ.not, by rw [quantifierRank_not]; exact hφ, (Sentence.realize_not M).2 hM,
      fun hN => ?_⟩
    exact h (iff_of_false hM ((Sentence.realize_not N).1 hN))

/-- **EVEN is not first-order definable on finite linear orders** [Libkin2004]: for every size
threshold `t`, no sentence in the language of orders holds in exactly those finite linear orders
with at least `t` elements that have an even number of elements. -/
theorem not_exists_sentence_realize_iff_even (t : ℕ) :
    ¬ ∃ φ : Language.order.Sentence, ∀ (M : Type) [_root_.LinearOrder M] [Finite M]
      [Language.order.Structure M] [Language.order.OrderedStructure M],
      t ≤ Nat.card M → (M ⊨ φ ↔ Even (Nat.card M)) := by
  rintro ⟨φ, hφ⟩
  obtain ⟨n, hn, htn⟩ : ∃ n, quantifierRank φ ≤ n ∧ t ≤ n :=
    ⟨max (quantifierRank φ) t, le_max_left _ _, le_max_right _ _⟩
  have ht : t ≤ 2 ^ n := htn.trans Nat.lt_two_pow_self.le
  let := orderStructure (Fin (2 ^ n))
  let := orderStructure (Fin (2 ^ n + 1))
  have : Language.order.OrderedStructure (Fin (2 ^ n)) := ⟨fun _ => Iff.rfl⟩
  have : Language.order.OrderedStructure (Fin (2 ^ n + 1)) := ⟨fun _ => Iff.rfl⟩
  have h := realize_iff_of_two_pow_le_card (M := Fin (2 ^ n)) (N := Fin (2 ^ n + 1))
    (by rw [Nat.card_fin]; omega) (by rw [Nat.card_fin]; omega) hn
  rw [hφ _ (by rw [Nat.card_fin]; omega), hφ _ (by rw [Nat.card_fin]; omega), Nat.card_fin,
    Nat.card_fin, Nat.even_add_one] at h
  exact iff_not_self h

end Cslib.Logic.FO.FiniteLinearOrder
