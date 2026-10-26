/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Communication.Lifting.Density
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The density-restoring partition

This file proves the two partition lemmas behind the simulation in the proof of the lifting
theorem [Mertz and Pitassi, §3.1][MertzPitassi2020] [Göös, Pitassi and Watson 2017,
§3][GoosPitassiWatson2017].

**Phase I** (`Communication.Lifting.exists_pieces`). A set `X` of pointer vectors splits into
disjoint *pieces* covering at least half of it. Each piece `P` is fixed to some `α` on a set `I`
of coordinates and is `τ`-dense on the rest of `F`. The coordinates `I` are a maximal set on
which the remaining vectors are too concentrated, so `P` holds at least a `τ ^ (-#I) / 2`
fraction of `X` [Mertz and Pitassi, Algorithm 1, Claims 3.4 and 3.5][MertzPitassi2020].

**Choosing a piece** (`Communication.Lifting.exists_piece_forall_le_card_filter`). Suppose `X`
is half of a dense set and Bob's set `Y` is large. Then some piece `(I, α, P)` leaves every value
`β` of the gadget on `I` possible for at least a `(4 τ) ^ (-#I)` fraction of `Y`
[Mertz and Pitassi, Lemma 3.6][MertzPitassi2020]. Otherwise each piece has a value `β` that few
`y` allow. Summing over the pieces, at least half of `Y` allows none of these values, and the
full-range lemma gives a contradiction. We sum the bounds using the sizes of the pieces rather
than counting the possible pairs `(I, α)`, so the threshold is `(4 τ) ^ (-#I)` instead of
`m ^ (-2 #I)`.

**Phase II** (`Communication.Lifting.exists_fix_blocks`). Bob's inputs allowing the value `β`
can be fixed on the blocks of `I` at the cost of a factor `2 ^ (m #I)`.

## Main definitions

* `Cslib.Communication.Lifting.Piece`: a piece of a density-restoring partition.

## Main results

* `Cslib.Communication.Lifting.exists_pieces`: the density-restoring partition.
* `Cslib.Communication.Lifting.exists_piece_forall_le_card_filter`: choosing a piece.
* `Cslib.Communication.Lifting.exists_fix_blocks`: fixing Bob's blocks.

## References

* [I. Mertz and T. Pitassi, *Lifting: As Easy As 1, 2, 3*][MertzPitassi2020]
* [M. Göös, T. Pitassi and T. Watson, *Query-to-communication lifting for
  BPP*][GoosPitassiWatson2017]
-/

@[expose] public section

namespace Cslib.Communication.Lifting

open Finset

variable {n m : ℕ}

/-- A piece of a density-restoring partition: the pointer vectors `P`, all fixed to `α` on the
coordinates `I`. -/
structure Piece (n m : ℕ) where
  /-- The fixed coordinates. -/
  I : Finset (Fin n)
  /-- The fixed values. -/
  α : Fin n → Fin m
  /-- The pointer vectors. -/
  P : Finset (Fin n → Fin m)

/-- The pieces of a density-restoring partition of `X` with density `τ` on `F`. -/
structure IsPartition (τ : ℝ) (F : Finset (Fin n)) (X : Finset (Fin n → Fin m))
    (L : List (Piece n m)) : Prop where
  subset : ∀ q ∈ L, q.P ⊆ X
  pairwise : L.Pairwise fun q q' => Disjoint q.P q'.P
  I_subset : ∀ q ∈ L, q.I ⊆ F
  fixed : ∀ q ∈ L, ∀ x ∈ q.P, ∀ i ∈ q.I, x i = q.α i
  dense : ∀ q ∈ L, IsDense τ (F \ q.I) q.P
  card_le : ∀ q ∈ L, (#X : ℝ) ≤ 2 * #q.P * τ ^ #q.I
  cover : (#X : ℝ) ≤ 2 * (L.map fun q => (#q.P : ℝ)).sum

section PhaseI

variable {τ : ℝ} {F : Finset (Fin n)}

/-- The vectors of `W` that agree with `α` on `I`. -/
abbrev agreeOn (W : Finset (Fin n → Fin m)) (I : Finset (Fin n)) (α : Fin n → Fin m) :
    Finset (Fin n → Fin m) :=
  W.filter fun x => ∀ i ∈ I, x i = α i

/-- The vectors of `W` are too concentrated on `I`: more than a `τ ^ (-#I)` fraction agrees with
`α` there. -/
def Violates (τ : ℝ) (W : Finset (Fin n → Fin m)) (I : Finset (Fin n)) (α : Fin n → Fin m) :
    Prop :=
  (#W : ℝ) < #(agreeOn W I α) * τ ^ #I

/-- For disjoint `I` and `J`, agreeing with `if i ∈ I then α i else β i` on `I ∪ J` is agreeing
with `α` on `I` and with `β` on `J`. -/
private theorem agreeOn_union_ite {W : Finset (Fin n → Fin m)} {I J : Finset (Fin n)}
    (hdisj : Disjoint I J) (α β : Fin n → Fin m) :
    agreeOn W (I ∪ J) (fun i => if i ∈ I then α i else β i) =
      (agreeOn W I α).filter fun x => ∀ i ∈ J, x i = β i := by
  ext x
  simp only [agreeOn, mem_filter, mem_union]
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨⟨hx, fun i hi => by simpa [hi] using h i (Or.inl hi)⟩, fun i hi => ?_⟩
    have hiI : i ∉ I := fun h' => disjoint_left.mp hdisj h' hi
    simpa [hiI] using h i (Or.inr hi)
  · rintro ⟨⟨hx, hI⟩, hJ'⟩
    refine ⟨hx, fun i hi => ?_⟩
    by_cases hiI : i ∈ I
    · simp only [hiI, ite_true]
      exact hI i hiI
    · simp only [hiI, ite_false]
      exact hJ' i (hi.resolve_left hiI)

/-- **Claim 3.4 of Mertz and Pitassi.** Fixing a set `W` on a maximal concentrated set `I` of
coordinates leaves it dense on the other coordinates. -/
theorem isDense_agreeOn (hτ : 0 < τ) {W : Finset (Fin n → Fin m)} {I : Finset (Fin n)}
    {α : Fin n → Fin m} (hW : (#W : ℝ) ≤ #(agreeOn W I α) * τ ^ #I)
    (hmax : ∀ I' ⊆ F, ∀ α', Violates τ W I' α' → #I' ≤ #I) (hIF : I ⊆ F)
    (hstrict : I.Nonempty → Violates τ W I α) :
    IsDense τ (F \ I) (agreeOn W I α) := by
  intro J hJ hJne β
  by_contra hcon
  push Not at hcon
  set α' : Fin n → Fin m := fun i => if i ∈ I then α i else β i
  have hdisj : Disjoint I J := by
    rw [disjoint_iff_ne]
    rintro a ha b hb rfl
    exact (mem_sdiff.mp (hJ hb)).2 ha
  have hfilt : agreeOn W (I ∪ J) α' = (agreeOn W I α).filter fun x => ∀ i ∈ J, x i = β i :=
    agreeOn_union_ite hdisj α β
  have hviol : Violates τ W (I ∪ J) α' := by
    unfold Violates
    rw [hfilt, card_union_of_disjoint hdisj, pow_add]
    by_cases hI : I.Nonempty
    · have h1 := hstrict hI
      unfold Violates at h1
      calc (#W : ℝ) < #(agreeOn W I α) * τ ^ #I := h1
        _ ≤ #((agreeOn W I α).filter fun x => ∀ i ∈ J, x i = β i) * τ ^ #J * τ ^ #I := by
            gcongr
        _ = _ := by ring
    · rw [not_nonempty_iff_eq_empty] at hI
      subst hI
      simp only [card_empty, pow_zero, mul_one] at hW ⊢
      have hagree : agreeOn W ∅ α = W := by simp [agreeOn]
      rw [hagree] at hcon ⊢
      linarith
  have := hmax (I ∪ J) (union_subset hIF fun j hj => (mem_sdiff.mp (hJ hj)).1) α' hviol
  rw [card_union_of_disjoint hdisj] at this
  have : 0 < #J := card_pos.mpr hJne
  omega

/-- Either some `I ⊆ F` and `α` maximize `#I` among the pairs violating `τ`-density on `W`, or
`(∅, x₀)` satisfies the same maximality and lower-bound conditions. -/
private theorem exists_max_violates_or_empty {W : Finset (Fin n → Fin m)}
    (x₀ : Fin n → Fin m) (F : Finset (Fin n)) (τ : ℝ) :
    ∃ (I : Finset (Fin n)) (α : Fin n → Fin m), I ⊆ F ∧
      (#W : ℝ) ≤ #(agreeOn W I α) * τ ^ #I ∧
      (∀ I' ⊆ F, ∀ α', Violates τ W I' α' → #I' ≤ #I) ∧
      (I.Nonempty → Violates τ W I α) := by
  classical
  set C : Finset (Finset (Fin n) × (Fin n → Fin m)) :=
    (F.powerset ×ˢ univ).filter fun p => Violates τ W p.1 p.2
  by_cases hC : C.Nonempty
  · obtain ⟨⟨I, α⟩, hp, hpmax⟩ := exists_max_image C (fun p => #p.1) hC
    simp only [C, mem_filter, mem_product, mem_powerset, mem_univ, and_true] at hp
    refine ⟨I, α, hp.1, hp.2.le, fun I' hI' α' hv => hpmax (I', α') ?_, fun _ => hp.2⟩
    simp only [C, mem_filter, mem_product, mem_powerset, mem_univ, and_true]
    exact ⟨hI', hv⟩
  · refine ⟨∅, x₀, empty_subset _, by simp [agreeOn], fun I' hI' α' hv => ?_, by simp⟩
    have hmem : (I', α') ∈ C := by
      simp only [C, mem_filter, mem_product, mem_powerset, mem_univ, and_true]
      exact ⟨hI', hv⟩
    exact absurd ⟨_, hmem⟩ hC

/-- When `W` is nonempty and `#W ≤ #(agreeOn W I α) * τ ^ #I`, `agreeOn W I α` is nonempty and
removing it strictly reduces `#W`. -/
private theorem card_sdiff_agreeOn_lt {W : Finset (Fin n → Fin m)} {I : Finset (Fin n)}
    {α : Fin n → Fin m} (hWne : W.Nonempty) (hW : (#W : ℝ) ≤ #(agreeOn W I α) * τ ^ #I) :
    #(W \ agreeOn W I α) < #W := by
  have hWpos : (0 : ℝ) < #W := by exact_mod_cast card_pos.mpr hWne
  have hPne : (agreeOn W I α).Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro h
    rw [h, card_empty, Nat.cast_zero, zero_mul] at hW
    linarith
  exact card_lt_card (sdiff_ssubset (filter_subset _ _) hPne)

/-- **Phase I: the density-restoring partition** [Mertz and Pitassi, Algorithm 1, Claims 3.4 and
3.5][MertzPitassi2020]. Every set of pointer vectors has a density-restoring partition. -/
theorem exists_pieces (hτ : 0 < τ) (F : Finset (Fin n)) (X : Finset (Fin n → Fin m)) :
    ∃ L, IsPartition τ F X L := by
  classical
  -- the induction runs over the uncovered vectors `W`
  suffices h : ∀ k, ∀ W ⊆ X, #W = k → ∃ L : List (Piece n m),
      (∀ q ∈ L, q.P ⊆ W) ∧ L.Pairwise (fun q q' => Disjoint q.P q'.P) ∧
      (∀ q ∈ L, q.I ⊆ F) ∧ (∀ q ∈ L, ∀ x ∈ q.P, ∀ i ∈ q.I, x i = q.α i) ∧
      (∀ q ∈ L, IsDense τ (F \ q.I) q.P) ∧ (∀ q ∈ L, (#X : ℝ) ≤ 2 * #q.P * τ ^ #q.I) ∧
      (#X : ℝ) ≤ 2 * (#X - #W + (L.map fun q => (#q.P : ℝ)).sum) by
    obtain ⟨L, h1, h2, h3, h4, h5, h6, h7⟩ := h _ X subset_rfl rfl
    exact ⟨L, ⟨h1, h2, h3, h4, h5, h6, by linarith⟩⟩
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro W hWX hWk
  by_cases hsmall : 2 * (#W : ℝ) < #X ∨ W = ∅
  · refine ⟨[], by simp, by simp, by simp, by simp, by simp, by simp, ?_⟩
    rcases hsmall with hsmall | rfl
    · simp only [List.map_nil, List.sum_nil]
      linarith
    · simp only [card_empty, Nat.cast_zero, List.map_nil, List.sum_nil]
      linarith [show (0 : ℝ) ≤ #X by positivity]
  push Not at hsmall
  obtain ⟨hsmall, hWe⟩ := hsmall
  obtain ⟨x₀, hx₀⟩ := hWe
  -- choose a maximal concentrated set, or the empty set if there is none
  obtain ⟨I, α, hIF, hW, hmax, hstrict⟩ := exists_max_violates_or_empty (W := W) x₀ F τ
  set P := agreeOn W I α
  have hPW : P ⊆ W := filter_subset _ _
  obtain ⟨L, h1, h2, h3, h4, h5, h6, h7⟩ :=
    ih _ (hWk ▸ card_sdiff_agreeOn_lt ⟨x₀, hx₀⟩ hW) (W \ P) (sdiff_subset.trans hWX) rfl
  refine ⟨⟨I, α, P⟩ :: L, ?_,
    List.Pairwise.cons (fun q hq => disjoint_of_subset_right (h1 q hq) disjoint_sdiff) h2,
    List.forall_mem_cons.mpr ⟨hIF, h3⟩,
    List.forall_mem_cons.mpr ⟨fun x hx i hi => (mem_filter.mp hx).2 i hi, h4⟩,
    List.forall_mem_cons.mpr ⟨isDense_agreeOn hτ hW hmax hIF hstrict, h5⟩,
    List.forall_mem_cons.mpr ⟨by linarith, h6⟩, ?_⟩
  · exact List.forall_mem_cons.mpr ⟨hPW, fun q hq => (h1 q hq).trans sdiff_subset⟩
  · rw [card_sdiff_of_subset hPW, Nat.cast_sub (card_le_card hPW)] at h7
    simp only [List.map_cons, List.sum_cons]
    linarith

end PhaseI

section Choose

variable {τ : ℝ} {F : Finset (Fin n)}

/-- Pairwise disjoint pieces inside `S` have at most `#S` vectors in total. -/
theorem sum_card_le_of_pairwise {S : Finset (Fin n → Fin m)} :
    ∀ {L : List (Piece n m)}, (∀ q ∈ L, q.P ⊆ S) → L.Pairwise (fun q q' => Disjoint q.P q'.P) →
      (L.map fun q => (#q.P : ℝ)).sum ≤ #S := by
  intro L
  induction L generalizing S with
  | nil => intro _ _; simp
  | cons q L ih =>
    intro hsub hpw
    obtain ⟨hq, hpw⟩ := List.pairwise_cons.mp hpw
    have hrest : ∀ q' ∈ L, q'.P ⊆ S \ q.P := fun q' hq' =>
      subset_sdiff.mpr ⟨hsub q' (List.mem_cons_of_mem _ hq'), (hq q' hq').symm⟩
    have h := ih hrest hpw
    have hqS := hsub q List.mem_cons_self
    rw [card_sdiff_of_subset hqS, Nat.cast_sub (card_le_card hqS)] at h
    simp only [List.map_cons, List.sum_cons]
    linarith

/-- The union of a list of finite sets. -/
def unionOf {β : Type*} [DecidableEq β] (L : List (Finset β)) : Finset β :=
  L.foldr (· ∪ ·) ∅

theorem mem_unionOf {β : Type*} [DecidableEq β] {L : List (Finset β)} {y : β} :
    y ∈ unionOf L ↔ ∃ s ∈ L, y ∈ s := by
  induction L with
  | nil => simp [unionOf]
  | cons s L ih =>
    simp only [unionOf, List.foldr_cons, mem_union, List.mem_cons, exists_eq_or_imp] at ih ⊢
    rw [ih]

/-- A union of finite sets has at most the sum of their sizes. -/
theorem card_unionOf_le {β : Type*} [DecidableEq β] :
    ∀ L : List (Finset β), (#(unionOf L) : ℝ) ≤ (L.map fun s => (#s : ℝ)).sum
  | [] => by simp [unionOf]
  | s :: L => by
    have h := card_unionOf_le L
    have h' : #(unionOf (s :: L)) ≤ #s + #(unionOf L) := card_union_le _ _
    have h'' : (#(unionOf (s :: L)) : ℝ) ≤ #s + #(unionOf L) := by exact_mod_cast h'
    simp only [List.map_cons, List.sum_cons]
    linarith

/-- The inputs of `Y` on which the gadget takes the value `β` on `I` at the pointers `α`. -/
abbrev allowing (Y : Finset (Fin n → Fin m → Bool)) (I : Finset (Fin n)) (α : Fin n → Fin m)
    (β : Fin n → Bool) : Finset (Fin n → Fin m → Bool) :=
  Y.filter fun y => ∀ i ∈ I, y i (α i) = β i

/-- If a piece `q ∈ L` of a `τ`-partition of `X` fails to leave a `(4 * τ) ^ (-#q.I)` fraction of
`Y` for `β`, then at most `#Y * #q.P / (2 * #X)` inputs of `Y` allow `β`. -/
private theorem card_allowing_le_of_lt {X : Finset (Fin n → Fin m)}
    {Y : Finset (Fin n → Fin m → Bool)} {L : List (Piece n m)} (hτ : 0 < τ)
    (hL : IsPartition τ F X L) (hX : X.Nonempty) {q : Piece n m} (hq : q ∈ L)
    {β : Fin n → Bool} (h1 : (#(allowing Y q.I q.α β) : ℝ) * (4 * τ) ^ #q.I < #Y) :
    (#(allowing Y q.I q.α β) : ℝ) ≤ #Y * #q.P / (2 * #X) := by
  have hXpos : (0 : ℝ) < #X := by exact_mod_cast card_pos.mpr hX
  have hIne : q.I.Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro h
    rw [h] at h1
    simp [allowing] at h1
  have h2 := hL.card_le q hq
  have h4 : (4 : ℝ) ≤ 4 ^ #q.I := le_self_pow₀ (by norm_num) (card_ne_zero.mpr hIne)
  have hτI : (0 : ℝ) < τ ^ #q.I := by positivity
  rw [le_div_iff₀ (by positivity)]
  have hA : (0 : ℝ) ≤ #(allowing Y q.I q.α β) := by positivity
  have hYpos : (0 : ℝ) ≤ #Y := by positivity
  rw [mul_pow] at h1
  nlinarith [mul_le_mul_of_nonneg_left h4 (mul_nonneg hA hτI.le),
    mul_le_mul_of_nonneg_left h2 hYpos, mul_le_mul_of_nonneg_left h2 hA]

/-- Removing the union of bad pieces (each of size at most `#Y * #q.P / (2 * #X)`) from `Y`
leaves at least half of `Y`. -/
private theorem card_le_two_mul_card_sdiff_unionOf_allowing {X : Finset (Fin n → Fin m)}
    {Y : Finset (Fin n → Fin m → Bool)} {L : List (Piece n m)}
    (hL : IsPartition τ F X L) (hX : X.Nonempty) (βq : Piece n m → Fin n → Bool)
    (hsmall : ∀ q ∈ L, (#(allowing Y q.I q.α (βq q)) : ℝ) ≤ #Y * #q.P / (2 * #X)) :
    (#Y : ℝ) ≤ 2 * #(Y \ unionOf (L.map fun q => allowing Y q.I q.α (βq q))) := by
  have hXpos : (0 : ℝ) < #X := by exact_mod_cast card_pos.mpr hX
  set Ybad := unionOf (L.map fun q => allowing Y q.I q.α (βq q))
  set Ygood := Y \ Ybad
  have hbad : (#Ybad : ℝ) ≤ #Y / 2 := by
    refine (card_unionOf_le _).trans ?_
    rw [List.map_map]
    calc (L.map ((fun s => (#s : ℝ)) ∘ fun q => allowing Y q.I q.α (βq q))).sum
        ≤ (L.map fun q => (#Y * #q.P / (2 * #X) : ℝ)).sum :=
          List.sum_le_sum fun q hq => hsmall q hq
      _ = #Y / (2 * #X) * (L.map fun q => (#q.P : ℝ)).sum := by
          rw [← List.sum_map_mul_left]
          congr 1
          exact List.map_congr_left fun q _ => by ring
      _ ≤ #Y / (2 * #X) * #X := by
          gcongr
          exact sum_card_le_of_pairwise hL.subset hL.pairwise
      _ = #Y / 2 := by field_simp
  have h1 : #Y - #Ybad ≤ #Ygood := le_card_sdiff _ _
  have h2 : (#Y : ℝ) - #Ybad ≤ #Ygood := by
    have := Nat.sub_le_iff_le_add.mp h1
    have : (#Y : ℝ) ≤ #Ygood + #Ybad := by exact_mod_cast this
    linarith
  linarith

/-- The union `unionOf (L.map Piece.P)` of the pieces of a partition of `X` is a subset of `X`
containing at least half of `X`. -/
private theorem IsPartition.subset_and_card_le_two_mul_card_unionOf
    {X : Finset (Fin n → Fin m)} {L : List (Piece n m)} (hL : IsPartition τ F X L) :
    unionOf (L.map Piece.P) ⊆ X ∧ (#X : ℝ) ≤ 2 * #(unionOf (L.map Piece.P)) := by
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨s, hs, hxs⟩ := mem_unionOf.mp hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hs
    exact hL.subset q hq hxs
  · have hX'sum : (L.map fun q => (#q.P : ℝ)).sum ≤ #(unionOf (L.map Piece.P)) :=
      sum_card_le_of_pairwise
        (fun q hq x hx => mem_unionOf.mpr ⟨q.P, List.mem_map.mpr ⟨q, hq, rfl⟩, hx⟩) hL.pairwise
    exact hL.cover.trans (by linarith)

/-- **Choosing a piece** [Mertz and Pitassi, Lemma 3.6][MertzPitassi2020]. Let `X` hold at least
half of a `τ`-dense set and let `Y` have at most `D` bits of deficiency on the blocks of `F`,
with `64 #F (D + 2) ≤ τ`, both fixed outside `F`. Then some piece `(I, α, P)` of a
density-restoring partition of `X` leaves every value `β` of the gadget on `I` possible for at
least a `(4 τ) ^ (-#I)` fraction of `Y`. -/
theorem exists_piece_forall_le_card_filter {X X₀ : Finset (Fin n → Fin m)}
    {Y : Finset (Fin n → Fin m → Bool)} {L : List (Piece n m)} {D : ℕ} (hτ : 0 < τ)
    (hL : IsPartition τ F X L) (hX : X.Nonempty) (hX₀ : IsDense τ F X₀) (hXX₀ : X ⊆ X₀)
    (hcard : (#X₀ : ℝ) ≤ 2 * #X) (hXfix : ∀ x ∈ X, ∀ x' ∈ X, ∀ i ∉ F, x i = x' i)
    (hYfix : ∀ y ∈ Y, ∀ y' ∈ Y, ∀ i ∉ F, y i = y' i)
    (hY : (2 : ℝ) ^ (#F * m) ≤ 2 ^ D * #Y) (hτD : 64 * #F * (D + 2) ≤ τ) :
    ∃ q ∈ L, ∀ β : Fin n → Bool, (#Y : ℝ) ≤ #(allowing Y q.I q.α β) * (4 * τ) ^ #q.I := by
  by_contra hcon
  push Not at hcon
  choose! βq hβq using hcon
  have hXpos : (0 : ℝ) < #X := by exact_mod_cast card_pos.mpr hX
  -- each piece has few inputs allowing its bad value, so at least half of `Y` allows none
  set Ybad := unionOf (L.map fun q => allowing Y q.I q.α (βq q))
  set Ygood := Y \ Ybad
  have hgood : (#Y : ℝ) ≤ 2 * #Ygood :=
    card_le_two_mul_card_sdiff_unionOf_allowing hL hX βq
      fun q hq => card_allowing_le_of_lt hτ hL hX hq (hβq q hq)
  -- the vectors in the pieces
  set X' := unionOf (L.map Piece.P)
  obtain ⟨hX'X, hX'big⟩ := hL.subset_and_card_le_two_mul_card_unionOf
  have hX'ne : X'.Nonempty := by
    rw [← card_pos]
    have : (0 : ℝ) < #X' := by linarith
    exact_mod_cast this
  have hX'dense : IsDense (τ / 4) F X' :=
    hX₀.of_subset hτ.le (by norm_num) (hX'X.trans hXX₀) (by linarith)
  -- the full-range lemma finds an input allowing a bad value
  set βx : (Fin n → Fin m) → Fin n → Bool := fun x =>
    @dite _ (∃ q ∈ L, x ∈ q.P) (Classical.dec _) (fun h => βq h.choose) fun _ _ => false
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_forall_eq_of_isDense (r := τ / 4) (D := D + 1)
    (by positivity) hX'ne
    (fun x hx x' hx' i hi => hXfix x (hX'X hx) x' (hX'X hx') i hi)
    hX'dense (fun y hy y' hy' i hi => hYfix y (sdiff_subset hy) y' (sdiff_subset hy') i hi)
    (by rw [pow_succ]; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) D])
    (by push_cast; linarith) βx
  have hex : ∃ q ∈ L, x ∈ q.P := by
    obtain ⟨s, hs, hxs⟩ := mem_unionOf.mp hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hs
    exact ⟨q, hq, hxs⟩
  obtain ⟨hqL, hxq⟩ := hex.choose_spec
  refine (mem_sdiff.mp hy).2 (mem_unionOf.mpr ⟨_, List.mem_map.mpr ⟨hex.choose, hqL, rfl⟩,
    mem_filter.mpr ⟨(mem_sdiff.mp hy).1, ?_⟩⟩)
  intro i hi
  have := hxy i (hL.I_subset _ hqL hi)
  simp only [βx, dite_eq_left_of_eq_true (eq_true hex)] at this
  rwa [hL.fixed _ hqL x hxq i hi] at this

end Choose

section PhaseII

/-- **Phase II: fixing Bob's blocks.** The inputs of `Y` allowing the value `β` on `I` can be
fixed on the blocks of `I`, keeping at least a `2 ^ (-m #I)` fraction of them. -/
theorem exists_fix_blocks (Y : Finset (Fin n → Fin m → Bool)) (I : Finset (Fin n))
    (α : Fin n → Fin m) (β : Fin n → Bool) :
    ∃ η : Fin n → Fin m → Bool, (∀ i ∈ I, η i (α i) = β i) ∧
      (#(allowing Y I α β) : ℝ) ≤ #(Y.filter fun y => ∀ i ∈ I, y i = η i) * 2 ^ (m * #I) := by
  classical
  by_cases hA : (allowing Y I α β).Nonempty
  swap
  · rw [not_nonempty_iff_eq_empty] at hA
    refine ⟨fun i a => β i, fun i _ => rfl, by rw [hA]; simp⟩
  set f : (Fin n → Fin m → Bool) → (I → Fin m → Bool) := fun y i => y i
  obtain ⟨g, -, hg⟩ := exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (s := allowing Y I α β) (t := univ) (f := f) (fun _ _ => mem_univ _) univ_nonempty
    (b := (#(allowing Y I α β) : ℝ) / 2 ^ (m * #I)) (by
      have hc : (Fintype.card (I → Fin m → Bool) : ℝ) = 2 ^ (m * #I) := by
        simp [Fintype.card_pi, pow_mul]
      rw [nsmul_eq_mul, card_univ, hc, mul_div_cancel₀ _ (by positivity)])
  have hfib : ((allowing Y I α β).filter fun y => f y = g).Nonempty := by
    rw [← card_pos]
    have : (0 : ℝ) < #((allowing Y I α β).filter fun y => f y = g) :=
      lt_of_lt_of_le (div_pos (by exact_mod_cast card_pos.mpr hA) (by positivity)) hg
    exact_mod_cast this
  obtain ⟨y₀, hy₀⟩ := hfib
  obtain ⟨hy₀A, hy₀g⟩ := mem_filter.mp hy₀
  refine ⟨y₀, fun i hi => (mem_filter.mp hy₀A).2 i hi, ?_⟩
  have hsub : (allowing Y I α β).filter (fun y => f y = g) ⊆
      Y.filter fun y => ∀ i ∈ I, y i = y₀ i := by
    intro y hy
    obtain ⟨hyA, hyg⟩ := mem_filter.mp hy
    refine mem_filter.mpr ⟨(mem_filter.mp hyA).1, fun i hi => ?_⟩
    have := congrFun (hyg.trans hy₀g.symm) ⟨i, hi⟩
    exact this
  have hle : (#((allowing Y I α β).filter fun y => f y = g) : ℝ) ≤
      #(Y.filter fun y => ∀ i ∈ I, y i = y₀ i) := by exact_mod_cast card_le_card hsub
  rw [div_le_iff₀ (by positivity)] at hg
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (m * #I)]

end PhaseII

end Cslib.Communication.Lifting
