/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.EhrenfeuchtFraisse.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.ModelTheory.Substructures
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Ehrenfeucht–Fraïssé games on monadic structures

A relational language is *monadic* when it has no relation symbols of arity at least two; it may
have unary and nullary symbols. The **color** of an element `m` of a structure is the set of unary
symbols that hold of `m` (`Cslib.Logic.FO.Monadic.color`).

Duplicator wins the `n`-round Ehrenfeucht–Fraïssé game on two monadic structures that satisfy the
same nullary symbols and, for every color, have equally many elements of that color or at least
`n` each (`Cslib.Logic.FO.Monadic.duplicatorWins_of_encard`). Duplicator's strategy keeps the
position a partial isomorphism in which, for every color, the numbers of unpebbled elements of
that color are equal or both at least the number of rounds left: answer a pebbled element by its
partner and an unpebbled element by an unpebbled element of the same color. This is the
back-and-forth pattern of `CslibFrontier.Logics.FirstOrder.EhrenfeuchtFraisse.FiniteLinearOrder`,
with color counts in place of gaps.

**The small model property.** Keeping at most `max q 1` elements of each color of a structure `M`
gives a substructure that satisfies the same sentences of quantifier rank at most `q` as `M`
(`Cslib.Logic.FO.Monadic.exists_substructure_realize`). With `k` unary symbols it has at most
`max q 1 * 2 ^ k` elements. So every sentence of a monadic language that has a nonempty model has
one on `Fin (n + 1)` with `n + 1 ≤ max q 1 * 2 ^ k` (`Cslib.Logic.FO.Monadic.exists_fin_realize`);
the factor `max q 1` rather than `q` keeps the model nonempty when `q = 0`. This is the
small-model property behind Löwenheim's theorem that the monadic class is decidable
[Lowenheim1915]. The explicit bound is proved here.

## Main definitions

* `Cslib.Logic.FO.Monadic.color`: the set of unary symbols holding of an element.

## Main results

* `Cslib.Logic.FO.Monadic.duplicatorWins_of_encard`: Duplicator wins on monadic structures with
  matching nullary symbols and color counts.
* `Cslib.Logic.FO.Monadic.realize_iff_of_encard`: such structures satisfy the same sentences of
  quantifier rank at most `n`.
* `Cslib.Logic.FO.Monadic.exists_substructure_realize`: a finite nonempty substructure of size at
  most `max q 1 * 2 ^ k` satisfying a given sentence of quantifier rank `q`.
* `Cslib.Logic.FO.Monadic.exists_fin_realize`: **the small model property** for monadic
  sentences.

## References

* [L. Löwenheim, *Über Möglichkeiten im Relativkalkül*][Lowenheim1915]
* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004], Chapter 3 (Ehrenfeucht–Fraïssé
  games).
-/

public section

open FirstOrder Language Structure

namespace Cslib.Logic.FO.Monadic

variable {L : Language} {M N : Type*} [L.Structure M] [L.Structure N]

variable (L) in
/-- The **color** of `m`: the set of unary relation symbols that hold of `m`. -/
def color (m : M) : Set (L.Relations 1) := {R | RelMap R ![m]}

@[simp] theorem mem_color {m : M} {R : L.Relations 1} : R ∈ color L m ↔ RelMap R ![m] := Iff.rfl

private theorem eq_vecCons {X : Type*} (x : Fin 1 → X) : x = ![x 0] :=
  funext fun i => by rw [Subsingleton.elim i 0]; rfl

/-- Embeddings preserve colors. -/
theorem _root_.FirstOrder.Language.Embedding.color_apply (f : M ↪[L] N) (m : M) :
    color L (f m) = color L m := by
  ext R
  rw [mem_color, mem_color, ← f.map_rel R ![m], eq_vecCons (f ∘ ![m])]
  rfl

/-! ### Duplicator's invariant -/

/-- The elements of color `C` that are not pebbled by `a`. -/
private def free {k : ℕ} (a : Fin k → M) (C : Set (L.Relations 1)) : Set M :=
  {m | color L m = C} \ Set.range a

/-- Two counts are indistinguishable with `r` rounds left: equal, or both at least `r`. -/
private def CountClose (r : ℕ) (x y : ℕ∞) : Prop := x = y ∨ (r ≤ x ∧ r ≤ y)

private theorem CountClose.symm {r : ℕ} {x y : ℕ∞} (h : CountClose r x y) : CountClose r y x :=
  h.imp Eq.symm And.symm

private theorem CountClose.mono {r s : ℕ} {x y : ℕ∞} (hrs : s ≤ r) (h : CountClose r x y) :
    CountClose s x y :=
  h.imp_right fun h => ⟨le_trans (by exact_mod_cast hrs) h.1, le_trans (by exact_mod_cast hrs) h.2⟩

private theorem CountClose.of_add_one {r : ℕ} {x y : ℕ∞} (h : CountClose (r + 1) (x + 1) (y + 1)) :
    CountClose r x y := by
  rcases h with h | ⟨hx, hy⟩
  · exact .inl (WithTop.add_right_cancel ENat.one_ne_top h)
  · refine .inr ⟨?_, ?_⟩
    · rwa [Nat.cast_add, Nat.cast_one, ENat.add_le_add_iff_right ENat.one_ne_top] at hx
    · rwa [Nat.cast_add, Nat.cast_one, ENat.add_le_add_iff_right ENat.one_ne_top] at hy

/-- Removing corresponding elements `c` and `d` from two sets with close counts. -/
private theorem CountClose.diff_singleton {r : ℕ} {F : Set M} {G : Set N} {c : M} {d : N}
    (hcd : c ∈ F ↔ d ∈ G) (h : CountClose (r + 1) F.encard G.encard) :
    CountClose r (F \ {c}).encard (G \ {d}).encard := by
  by_cases hc : c ∈ F
  · rw [← Set.encard_sdiff_singleton_add_one hc, ← Set.encard_sdiff_singleton_add_one (hcd.1 hc)]
      at h
    exact h.of_add_one
  · rw [Set.sdiff_singleton_eq_self hc, Set.sdiff_singleton_eq_self (mt hcd.2 hc)]
    exact h.mono (Nat.le_succ r)

variable (L) in
/-- **Duplicator's invariant** with `r` rounds left: the pebbles define a partial isomorphism
(equal pebbles correspond and corresponding pebbles have the same color), and for every color the
numbers of unpebbled elements of that color are close. -/
private structure Good (r : ℕ) {k : ℕ} (a : Fin k → M) (b : Fin k → N) : Prop where
  eq_iff : ∀ i j, a i = a j ↔ b i = b j
  color_eq : ∀ i, color L (a i) = color L (b i)
  count : ∀ C : Set (L.Relations 1), CountClose r (free a C).encard (free b C).encard

private theorem Good.symm {r k : ℕ} {a : Fin k → M} {b : Fin k → N} (h : Good L r a b) :
    Good L r b a :=
  ⟨fun i j => (h.eq_iff i j).symm, fun i => (h.color_eq i).symm, fun C => (h.count C).symm⟩

private theorem free_snoc {k : ℕ} (a : Fin k → M) (c : M) (C : Set (L.Relations 1)) :
    free (Fin.snoc a c : Fin (k + 1) → M) C = free a C \ {c} := by
  ext m
  simp only [free, Fin.range_snoc, Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-- Extending a position by a pair `(c, d)` that matches the pebbles and has matching colors. -/
private theorem Good.snoc {r k : ℕ} {a : Fin k → M} {b : Fin k → N} (h : Good L (r + 1) a b)
    {c : M} {d : N} (hcd : ∀ i, a i = c ↔ b i = d) (hcol : color L c = color L d) :
    Good L r (Fin.snoc a c : Fin (k + 1) → M) (Fin.snoc b d : Fin (k + 1) → N) := by
  have hmem : ∀ C, c ∈ free a C ↔ d ∈ free b C := fun C => by
    simp only [free, Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_range, not_exists]
    exact and_congr (by rw [hcol]) (forall_congr' fun i => not_congr (hcd i))
  refine ⟨fun i j => ?_, fun i => ?_, fun C => ?_⟩
  · induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
      simp only [Fin.snoc_last, Fin.snoc_castSucc] <;>
      first
        | exact hcd _
        | exact (eq_comm.trans (hcd _)).trans eq_comm
        | exact h.eq_iff _ _
  · induction i using Fin.lastCases <;> simp only [Fin.snoc_last, Fin.snoc_castSucc]
    · exact hcol
    · exact h.color_eq _
  · rw [free_snoc, free_snoc]
    exact (h.count C).diff_singleton (hmem C)

private theorem Good.forth {r k : ℕ} {a : Fin k → M} {b : Fin k → N} (h : Good L (r + 1) a b)
    (c : M) :
    ∃ d : N, Good L r (Fin.snoc a c : Fin (k + 1) → M) (Fin.snoc b d : Fin (k + 1) → N) := by
  by_cases hc : c ∈ Set.range a
  · obtain ⟨i, rfl⟩ := hc
    exact ⟨b i, h.snoc (fun j => h.eq_iff j i) (h.color_eq i)⟩
  · have hfree : c ∈ free a (color L c) := ⟨rfl, hc⟩
    have hpos : (free b (color L c)).Nonempty := by
      rw [← Set.encard_pos]
      rcases h.count (color L c) with h' | ⟨-, h'⟩
      · rw [← h']
        exact Set.encard_pos.2 ⟨c, hfree⟩
      · exact lt_of_lt_of_le (by exact_mod_cast Nat.succ_pos r) h'
    obtain ⟨d, hd, hdb⟩ := hpos
    refine ⟨d, h.snoc (fun i => iff_of_false (fun hi => hc ⟨i, hi⟩) fun hi => hdb ⟨i, hi⟩) hd.symm⟩

private theorem Good.back {r k : ℕ} {a : Fin k → M} {b : Fin k → N} (h : Good L (r + 1) a b)
    (d : N) :
    ∃ c : M, Good L r (Fin.snoc a c : Fin (k + 1) → M) (Fin.snoc b d : Fin (k + 1) → N) :=
  (h.symm.forth d).imp fun _ hc => hc.symm

/-- In a monadic language, a position satisfying the invariant is a partial isomorphism once the
two structures satisfy the same nullary symbols. -/
private theorem Good.partialIso (hmon : ∀ l, 2 ≤ l → IsEmpty (L.Relations l))
    (h0 : ∀ R : L.Relations 0, RelMap R (default : Fin 0 → M) ↔ RelMap R (default : Fin 0 → N))
    {r k : ℕ} {a : Fin k → M} {b : Fin k → N} (h : Good L r a b) : PartialIso L a b := by
  refine ⟨h.eq_iff, fun {l} R f => ?_⟩
  match l, R with
  | 0, R => rw [Subsingleton.elim (a ∘ f) default, Subsingleton.elim (b ∘ f) default]; exact h0 R
  | 1, R =>
    rw [eq_vecCons (a ∘ f), eq_vecCons (b ∘ f)]
    exact Set.ext_iff.1 (h.color_eq (f 0)) R
  | l + 2, R => exact (hmon (l + 2) (by omega)).elim R

/-! ### Duplicator wins -/

/-- **Ehrenfeucht–Fraïssé games on monadic structures.** In a language without relation symbols of
arity at least two, Duplicator wins the `n`-round game on `M` and `N` if they satisfy the same
nullary symbols and, for every color, have the same number of elements of that color or at least
`n` each. -/
theorem duplicatorWins_of_encard (hmon : ∀ l, 2 ≤ l → IsEmpty (L.Relations l))
    (h0 : ∀ R : L.Relations 0, RelMap R (default : Fin 0 → M) ↔ RelMap R (default : Fin 0 → N))
    {n : ℕ} (hcount : ∀ C : Set (L.Relations 1),
      {m : M | color L m = C}.encard = {m : N | color L m = C}.encard ∨
        (n ≤ {m : M | color L m = C}.encard ∧ n ≤ {m : N | color L m = C}.encard))
    (a : Fin 0 → M) (b : Fin 0 → N) : DuplicatorWins L n a b := by
  refine IsBackAndForth.duplicatorWins (I := fun r _ a b => Good L r a b)
    ⟨fun h => h.partialIso hmon h0, fun h => h.forth, fun h => h.back⟩
    ⟨fun i => i.elim0, fun i => i.elim0, fun C => ?_⟩
  simp only [free, Set.range_eq_empty, Set.sdiff_empty]
  exact hcount C

/-- Monadic structures with the same nullary symbols and, for every color, the same number of
elements of that color or at least `n` each satisfy the same sentences of quantifier rank at most
`n`. -/
theorem realize_iff_of_encard [L.IsRelational] (hmon : ∀ l, 2 ≤ l → IsEmpty (L.Relations l))
    (h0 : ∀ R : L.Relations 0, RelMap R (default : Fin 0 → M) ↔ RelMap R (default : Fin 0 → N))
    {n : ℕ} (hcount : ∀ C : Set (L.Relations 1),
      {m : M | color L m = C}.encard = {m : N | color L m = C}.encard ∨
        (n ≤ {m : M | color L m = C}.encard ∧ n ≤ {m : N | color L m = C}.encard))
    {φ : L.Sentence} (hφ : quantifierRank φ ≤ n) : M ⊨ φ ↔ N ⊨ φ :=
  (duplicatorWins_of_encard hmon h0 hcount default default).realize_iff hφ

/-! ### The small model property -/

/-- **Small substructures of monadic structures.** In a relational language with finitely many
unary and no higher-arity relation symbols, every sentence `φ` that holds in a nonempty structure
`M` holds in a finite nonempty substructure of `M` with at most `max q 1 * 2 ^ k` elements, where
`q` is the quantifier rank of `φ` and `k` the number of unary symbols. -/
theorem exists_substructure_realize [L.IsRelational] [Finite (L.Relations 1)]
    (hmon : ∀ l, 2 ≤ l → IsEmpty (L.Relations l)) [Nonempty M] {φ : L.Sentence} (h : M ⊨ φ) :
    ∃ S : L.Substructure M, Finite S ∧ Nonempty S ∧
      Nat.card S ≤ max (quantifierRank φ) 1 * 2 ^ Nat.card (L.Relations 1) ∧ S ⊨ φ := by
  classical
  set Q := max (quantifierRank φ) 1
  -- keep at most `Q` elements of each color
  have hT : ∀ C : Set (L.Relations 1), ∃ T ⊆ {m : M | color L m = C},
      T.encard = min (Q : ℕ∞) {m : M | color L m = C}.encard :=
    fun C => Set.exists_subset_encard_eq (min_le_right _ _)
  choose T hTsub hTcard using hT
  let s : Set M := {m | m ∈ T (color L m)}
  let S : L.Substructure M := ⟨s, fun f => isEmptyElim f⟩
  have hclass : ∀ C, {m : M | m ∈ s ∧ color L m = C} = T C := fun C => by
    ext m
    refine ⟨fun ⟨hm, hC⟩ => hC ▸ hm, fun hm => ?_⟩
    have hC : color L m = C := hTsub C hm
    exact ⟨by simp only [s, Set.mem_ofPred_eq, hC, hm], hC⟩
  have hcolorS : ∀ C, {x : S | color L x = C}.encard = (T C).encard := fun C => by
    rw [← hclass C, ← Subtype.val_injective.encard_image]
    congr 1
    ext m
    simp only [Set.mem_image, Set.mem_ofPred_eq, Subtype.exists, exists_and_right, exists_eq_right]
    have hc : ∀ hm : m ∈ S, color L (⟨m, hm⟩ : S) = color L m := fun hm =>
      S.subtype.color_apply ⟨m, hm⟩ |>.symm
    exact ⟨fun ⟨hm, hC⟩ => ⟨hm, (hc hm).symm.trans hC⟩, fun ⟨hm, hC⟩ => ⟨hm, (hc hm).trans hC⟩⟩
  have hsub : s ⊆ ⋃ C, T C := fun m hm => Set.mem_iUnion.2 ⟨_, hm⟩
  have hcard : s.encard ≤ (Q * 2 ^ Nat.card (L.Relations 1) : ℕ) := by
    have := Fintype.ofFinite (L.Relations 1)
    calc s.encard ≤ ∑ C, (T C).encard :=
          (Set.encard_mono hsub).trans (Set.encard_iUnion_le_of_fintype T)
      _ ≤ ∑ _C : Set (L.Relations 1), (Q : ℕ∞) :=
          Finset.sum_le_sum fun C _ => (hTcard C).trans_le (min_le_left _ _)
      _ = (Q * 2 ^ Nat.card (L.Relations 1) : ℕ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_set, nsmul_eq_mul,
            Nat.card_eq_fintype_card]
          push_cast
          exact mul_comm _ _
  have hfin : s.Finite := Set.finite_of_encard_le_coe hcard
  have hrealize : S ⊨ φ ↔ M ⊨ φ := by
    refine realize_iff_of_encard (n := Q) hmon (fun R => ?_) (fun C => ?_) (le_max_left _ _)
    · rw [← S.subtype.map_rel R default, Subsingleton.elim (S.subtype ∘ default) default]
    · rw [hcolorS, hTcard]
      rcases le_total (Q : ℕ∞) {m : M | color L m = C}.encard with hQ | hQ
      · rw [min_eq_left hQ]
        exact .inr ⟨le_rfl, hQ⟩
      · exact .inl (min_eq_right hQ)
  obtain ⟨m⟩ := ‹Nonempty M›
  obtain ⟨x, hx⟩ : (T (color L m)).Nonempty := by
    rw [← Set.encard_pos, hTcard]
    exact lt_min (by exact_mod_cast lt_of_lt_of_le zero_lt_one (le_max_right _ _))
      (Set.encard_pos.2 ⟨m, rfl⟩)
  have hxs : x ∈ s := by
    change x ∈ T (color L x)
    rw [hTsub _ hx]
    exact hx
  exact ⟨S, hfin.to_subtype, ⟨⟨x, hxs⟩⟩, (Set.encard_le_coe_iff_finite_ncard_le.1 hcard).2,
    hrealize.2 h⟩

/-- **The small model property for monadic sentences** [Lowenheim1915]. In a relational language
with finitely many unary and no higher-arity relation symbols, every sentence `φ` that holds in a
nonempty structure has a model on `Fin (n + 1)` with `n + 1 ≤ max q 1 * 2 ^ k`, where `q` is the
quantifier rank of `φ` and `k` the number of unary symbols. The explicit bound is proved here. -/
theorem exists_fin_realize [L.IsRelational] [Finite (L.Relations 1)]
    (hmon : ∀ l, 2 ≤ l → IsEmpty (L.Relations l)) [Nonempty M] {φ : L.Sentence} (h : M ⊨ φ) :
    ∃ n, n + 1 ≤ max (quantifierRank φ) 1 * 2 ^ Nat.card (L.Relations 1) ∧
      ∃ _ : L.Structure (Fin (n + 1)), Fin (n + 1) ⊨ φ := by
  obtain ⟨S, hfin, hne, hcard, hS⟩ := exists_substructure_realize hmon h
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_one_of_ne_zero (Nat.card_pos (α := S)).ne'
  let e := Finite.equivFinOfCardEq hn
  let _ := e.inducedStructure (L := L)
  exact ⟨n, hn ▸ hcard, e.inducedStructure,
    (StrongHomClass.realize_sentence e.inducedStructureEquiv φ).1 hS⟩

end Cslib.Logic.FO.Monadic
