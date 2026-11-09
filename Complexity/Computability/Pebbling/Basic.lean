/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Foundations.Semantics.LTS.Basic
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Order.Lattice.Nat

/-!
# The black pebble game

The black pebble game on a directed graph `G` is played on configurations `C : Finset V` of
pebbled vertices, where `G.Adj u v` means that `u` is an immediate predecessor of `v`. A move
either places a pebble on a vertex whose predecessors all carry pebbles, or removes a pebble.
In particular a pebble can always be placed on a source. A vertex is pebblable with `s` pebbles
if some run from the empty configuration that never holds more than `s` pebbles pebbles it. The
black pebbling price of a vertex is the least such `s`, and `0` when no budget suffices.

We use Nordström's convention, without sliding: placing a pebble always uses a new pebble. Under
the sliding rule of [Savage1998] every price is one lower ([Nordstrom2015Survey],
Proposition 2.5).

## Main definitions

* `Cslib.Pebbling.Move`: the moves `place v` and `remove v`.
* `Cslib.Pebbling.BlackStep`: one legal move, with no pebble budget.
* `Cslib.Pebbling.blackPebbleGame G s`: the game with `s` pebbles, as a cslib `LTS`.
* `Cslib.Pebbling.BlackPebblable G s v`: `v` can be pebbled with `s` pebbles.
* `Cslib.Pebbling.blackPebblingPrice G v`: the least such `s`.

## Main results

* `Cslib.Pebbling.BlackPebblable.mono`: pebblability is monotone in the budget.
* `Cslib.Pebbling.BlackPebblable.of_forall_adj`: the composition rule.
* `Cslib.Pebbling.blackPebblable_fintypeCard`: on a finite graph with well-founded predecessor
  relation, every vertex is pebblable with one pebble per vertex.
* `Cslib.Pebbling.blackPebblingPrice_eq`: the price is determined by a matching upper and lower
  bound.

## References

* [J. Nordström, *Pebble games, proof complexity, and time-space trade-offs*][Nordstrom2013],
  Definition 2.10.
* [J. Nordström, *New wine into old wineskins*][Nordstrom2015Survey], Definition 1.1 and
  Proposition 2.5.
* [J. E. Savage, *Models of Computation*][Savage1998], Section 10.1.
-/

public section

namespace Cslib.Pebbling

/-! ## The game -/

/-- A move of the black pebble game. -/
inductive Move (V : Type*) where
  | place (v : V)
  | remove (v : V)

section Game

variable {V : Type*} [DecidableEq V] (G : Digraph V)

/-- One legal move of the black pebble game, without a budget. -/
inductive BlackStep : Finset V → Move V → Finset V → Prop where
  | place {C : Finset V} {v : V} (h : ∀ u, G.Adj u v → u ∈ C) :
      BlackStep C (.place v) (insert v C)
  | remove {C : Finset V} {v : V} : BlackStep C (.remove v) (C.erase v)

/-- The black pebble game with `s` pebbles. -/
@[expose] def blackPebbleGame (s : ℕ) : LTS (Finset V) (Move V) where
  Tr C m D := BlackStep G C m D ∧ D.card ≤ s

/-- `v` can be black-pebbled with at most `s` pebbles. -/
@[expose] def BlackPebblable (s : ℕ) (v : V) : Prop :=
  ∃ (ms : List (Move V)) (C : Finset V), (blackPebbleGame G s).MTr ∅ ms C ∧ v ∈ C

/-- The black pebbling price of `v`: the least `s` such that `v` is pebblable with `s` pebbles.

When no budget suffices (for example at a vertex with a self-loop, with infinitely many
predecessors, or with no open path from a source), the set is empty and the price is
`sInf ∅ = 0`. Statements about the price therefore need a pebblability witness, as in
`blackPebblingPrice_eq`; on a finite graph with well-founded predecessor relation every vertex
is pebblable (`blackPebblable_fintypeCard`). -/
noncomputable def blackPebblingPrice (v : V) : ℕ :=
  sInf {s | BlackPebblable G s v}

end Game

section API

variable {V : Type*} [DecidableEq V] {G : Digraph V}

theorem blackPebbleGame_tr {s : ℕ} {C D : Finset V} {m : Move V} :
    (blackPebbleGame G s).Tr C m D ↔ BlackStep G C m D ∧ D.card ≤ s := Iff.rfl

theorem BlackStep.eq_insert_of_mem {C D : Finset V} {m : Move V} (h : BlackStep G C m D)
    {x : V} (hxD : x ∈ D) (hxC : x ∉ C) : (∀ u, G.Adj u x → u ∈ C) ∧ D = insert x C := by
  cases h with
  | @place v h =>
    rcases Finset.mem_insert.1 hxD with rfl | hx
    · exact ⟨h, rfl⟩
    · exact absurd hx hxC
  | remove => exact absurd (Finset.mem_of_mem_erase hxD) hxC

theorem blackPebbleGame_mTr_mono {s t : ℕ} (hst : s ≤ t) {C D : Finset V} {ms : List (Move V)}
    (h : (blackPebbleGame G s).MTr C ms D) : (blackPebbleGame G t).MTr C ms D := by
  induction h with
  | refl => exact .refl
  | stepL h _ ih => exact .stepL ⟨h.1, h.2.trans hst⟩ ih

theorem card_le_of_blackPebbleGame_mTr {s : ℕ} {C D : Finset V} {ms : List (Move V)}
    (h : (blackPebbleGame G s).MTr C ms D) (hC : C.card ≤ s) : D.card ≤ s := by
  induction h with
  | refl => exact hC
  | stepL h _ ih => exact ih h.2

theorem BlackPebblable.mono {s t : ℕ} (hst : s ≤ t) {v : V} (h : BlackPebblable G s v) :
    BlackPebblable G t v := by
  obtain ⟨ms, C, hC, hv⟩ := h
  exact ⟨ms, C, blackPebbleGame_mTr_mono hst hC, hv⟩

theorem BlackPebblable.one_le {s : ℕ} {v : V} (h : BlackPebblable G s v) : 1 ≤ s := by
  obtain ⟨ms, C, hC, hv⟩ := h
  exact (Finset.card_pos.2 ⟨v, hv⟩).trans_le (card_le_of_blackPebbleGame_mTr hC (by simp))

/-- Removing the pebbles of `D` one at a time. -/
theorem exists_blackPebbleGame_mTr_sdiff {s : ℕ} {C : Finset V} (hC : C.card ≤ s)
    (D : Finset V) : ∃ ms, (blackPebbleGame G s).MTr C ms (C \ D) := by
  induction D using Finset.induction_on with
  | empty => exact ⟨[], by rw [Finset.sdiff_empty]; exact .refl⟩
  | @insert a D _ ih =>
    obtain ⟨ms, hms⟩ := ih
    rw [Finset.sdiff_insert]
    exact ⟨ms ++ [.remove a], LTS.MTr.stepR _ hms ⟨.remove,
      Finset.card_erase_le.trans ((Finset.card_le_card Finset.sdiff_subset).trans hC)⟩⟩

/-- A vertex is pebblable exactly when some run ends with a pebble on that vertex alone. -/
theorem blackPebblable_iff_exists_mTr_singleton {s : ℕ} {v : V} :
    BlackPebblable G s v ↔ ∃ ms, (blackPebbleGame G s).MTr ∅ ms {v} := by
  constructor
  · rintro ⟨ms, C, hC, hv⟩
    obtain ⟨ms', h'⟩ := exists_blackPebbleGame_mTr_sdiff (G := G)
      (card_le_of_blackPebbleGame_mTr hC (by simp)) (C.erase v)
    rw [Finset.sdiff_erase_self hv] at h'
    exact ⟨ms ++ ms', LTS.MTr.comp _ hC h'⟩
  · rintro ⟨ms, h⟩
    exact ⟨ms, {v}, h, Finset.mem_singleton_self v⟩

/-- Keeping the pebbles of `F` in place throughout a run costs at most `F.card` extra pebbles. -/
theorem exists_blackPebbleGame_mTr_union {s : ℕ} {C D : Finset V} {ms : List (Move V)}
    (h : (blackPebbleGame G s).MTr C ms D) (F : Finset V) :
    ∃ ms', (blackPebbleGame G (s + F.card)).MTr (C ∪ F) ms' (D ∪ F) := by
  induction h with
  | refl => exact ⟨[], .refl⟩
  | @stepL C₁ m C₂ ms C₃ hstep _ ih =>
    obtain ⟨ms', ih⟩ := ih
    obtain ⟨hstep, hcard⟩ := hstep
    have hcard' : (C₂ ∪ F).card ≤ s + F.card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_right hcard _)
    cases hstep with
    | @place v hv =>
      refine ⟨.place v :: ms', .stepL ⟨?_, hcard'⟩ ih⟩
      rw [Finset.insert_union]
      exact .place fun u hu => Finset.mem_union_left _ (hv u hu)
    | @remove v =>
      by_cases hvF : v ∈ F
      · rw [Finset.erase_union_of_mem hvF] at ih
        exact ⟨ms', ih⟩
      · have : C₁.erase v ∪ F = (C₁ ∪ F).erase v := by
          rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hvF]
        refine ⟨.remove v :: ms', .stepL ⟨?_, hcard'⟩ ih⟩
        rw [this]
        exact .remove

/-- Composition: if every predecessor of `v` lies in `ps` and can be pebbled with `s` pebbles,
then `v` can be pebbled with `t` pebbles whenever `#ps + 1 ≤ t` and `s + #ps ≤ t + 1`. -/
theorem BlackPebblable.of_forall_adj {s t : ℕ} {v : V} (ps : Finset V)
    (hps : ∀ u, G.Adj u v → u ∈ ps) (h : ∀ u ∈ ps, BlackPebblable G s u)
    (ht : ps.card + 1 ≤ t) (hst : s + ps.card ≤ t + 1) : BlackPebblable G t v := by
  have key : ∀ Q : Finset V, (∀ u ∈ Q, BlackPebblable G s u) →
      ∃ ms, (blackPebbleGame G (s + Q.card - 1)).MTr ∅ ms Q := by
    intro Q
    induction Q using Finset.induction_on with
    | empty => exact fun _ => ⟨[], .refl⟩
    | @insert a Q haQ ih =>
      intro hQ
      obtain ⟨ms₁, h₁⟩ := ih fun u hu => hQ u (Finset.mem_insert_of_mem hu)
      obtain ⟨ms₂, h₂⟩ :=
        blackPebblable_iff_exists_mTr_singleton.1 (hQ a (Finset.mem_insert_self a Q))
      obtain ⟨ms₃, h₃⟩ := exists_blackPebbleGame_mTr_union h₂ Q
      rw [Finset.empty_union, ← Finset.insert_eq] at h₃
      rw [Finset.card_insert_of_notMem haQ, show s + (Q.card + 1) - 1 = s + Q.card by omega]
      exact ⟨ms₁ ++ ms₃, LTS.MTr.comp _ (blackPebbleGame_mTr_mono (by omega) h₁) h₃⟩
  obtain ⟨ms, hms⟩ := key ps h
  refine ⟨ms ++ [.place v], insert v ps,
    LTS.MTr.stepR _ (blackPebbleGame_mTr_mono (by omega) hms) ⟨.place hps, ?_⟩,
    Finset.mem_insert_self v ps⟩
  exact (Finset.card_insert_le _ _).trans ht

/-- On a finite graph without infinite descending chains of predecessors, every vertex can be
pebbled with one pebble per vertex. -/
theorem blackPebblable_fintypeCard [Fintype V] (hG : WellFounded G.Adj) (v : V) :
    BlackPebblable G (Fintype.card V) v := by
  classical
  have hle : ∀ C : Finset V, C.card ≤ Fintype.card V := fun C => Finset.card_le_univ C
  have key : ∀ v (C : Finset V), ∃ ms D, (blackPebbleGame G (Fintype.card V)).MTr C ms D ∧
      C ⊆ D ∧ v ∈ D := by
    intro v
    induction v using hG.induction with
    | _ v ih =>
      intro C
      have hpred : ∀ Q : Finset V, (∀ u ∈ Q, G.Adj u v) →
          ∃ ms D, (blackPebbleGame G (Fintype.card V)).MTr C ms D ∧ C ⊆ D ∧ Q ⊆ D := by
        intro Q
        induction Q using Finset.induction_on with
        | empty => exact fun _ => ⟨[], C, .refl, subset_rfl, Finset.empty_subset _⟩
        | @insert a Q _ ihQ =>
          intro hQ
          obtain ⟨ms₁, D₁, h₁, hCD₁, hQD₁⟩ :=
            ihQ fun u hu => hQ u (Finset.mem_insert_of_mem hu)
          obtain ⟨ms₂, D₂, h₂, hD₁D₂, haD₂⟩ := ih a (hQ a (Finset.mem_insert_self a Q)) D₁
          exact ⟨ms₁ ++ ms₂, D₂, LTS.MTr.comp _ h₁ h₂, hCD₁.trans hD₁D₂,
            Finset.insert_subset haD₂ (hQD₁.trans hD₁D₂)⟩
      obtain ⟨ms, D, hD, hCD, hpD⟩ :=
        hpred (Finset.univ.filter fun u => G.Adj u v) fun u hu => (Finset.mem_filter.1 hu).2
      refine ⟨ms ++ [.place v], insert v D, LTS.MTr.stepR _ hD ⟨.place fun u hu => hpD ?_, hle _⟩,
        hCD.trans (Finset.subset_insert v D), Finset.mem_insert_self v D⟩
      exact Finset.mem_filter.2 ⟨Finset.mem_univ u, hu⟩
  obtain ⟨ms, D, hD, -, hvD⟩ := key v ∅
  exact ⟨ms, D, hD, hvD⟩

theorem blackPebblingPrice_le {s : ℕ} {v : V} (h : BlackPebblable G s v) :
    blackPebblingPrice G v ≤ s :=
  Nat.sInf_le h

theorem blackPebblable_blackPebblingPrice {s : ℕ} {v : V} (h : BlackPebblable G s v) :
    BlackPebblable G (blackPebblingPrice G v) v :=
  Nat.sInf_mem (s := {s | BlackPebblable G s v}) ⟨s, h⟩

theorem blackPebblable_iff_blackPebblingPrice_le {s : ℕ} {v : V} (h : ∃ s, BlackPebblable G s v) :
    BlackPebblable G s v ↔ blackPebblingPrice G v ≤ s := by
  obtain ⟨s₀, h₀⟩ := h
  exact ⟨blackPebblingPrice_le, fun hs => (blackPebblable_blackPebblingPrice h₀).mono hs⟩

/-- A vertex that no budget pebbles has price `0`. -/
theorem blackPebblingPrice_eq_zero_of_forall_not {v : V} (h : ∀ s, ¬ BlackPebblable G s v) :
    blackPebblingPrice G v = 0 := by
  rw [blackPebblingPrice, Set.eq_empty_of_forall_notMem (s := {s | BlackPebblable G s v}) h,
    Nat.sInf_empty]

/-- The price is `n` when `n` pebbles suffice and every successful budget is at least `n`. -/
theorem blackPebblingPrice_eq {n : ℕ} {v : V} (h : BlackPebblable G n v)
    (hle : ∀ s, BlackPebblable G s v → n ≤ s) : blackPebblingPrice G v = n :=
  le_antisymm (blackPebblingPrice_le h) (hle _ (blackPebblable_blackPebblingPrice h))

/-- On a finite graph with well-founded predecessor relation, the price of any vertex is at most
the number of vertices. -/
theorem blackPebblingPrice_le_fintypeCard [Fintype V] (hG : WellFounded G.Adj) (v : V) :
    blackPebblingPrice G v ≤ Fintype.card V :=
  blackPebblingPrice_le (blackPebblable_fintypeCard hG v)

/-- A source is pebblable with one pebble. -/
theorem blackPebblable_one_of_source {v : V} (hv : ∀ u, ¬ G.Adj u v) : BlackPebblable G 1 v :=
  BlackPebblable.of_forall_adj (s := 1) ∅ (fun u hu => absurd hu (hv u))
    (fun u hu => absurd hu (Finset.notMem_empty u)) (by simp) (by simp)

/-- A source has black pebbling price `1`. -/
theorem blackPebblingPrice_eq_one_of_source {v : V} (hv : ∀ u, ¬ G.Adj u v) :
    blackPebblingPrice G v = 1 :=
  blackPebblingPrice_eq (blackPebblable_one_of_source hv) fun _ h => h.one_le

end API

end Cslib.Pebbling
