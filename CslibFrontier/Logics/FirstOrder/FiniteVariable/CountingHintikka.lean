/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.FiniteVariable.BijectiveGame
public import CslibFrontier.Logics.FirstOrder.FiniteVariable.Hintikka
import CslibFrontier.Foundations.Data.Fintype.FiberEquiv

/-!
# Bijective pebble games and counting logic

On a finite structure, the `k`-variable counting rank-`n` type of a position `(S, a)` is finite
combinatorial data (`Cslib.Logic.FO.CountingType`): the atomic facts about the placed pebbles
and, if `n > 0`, for each pebble index `j` the **multiset** of rank-`(n - 1)` types reached by
moving pebble `j` to each element. The counting type replaces the set of reached types in
`Cslib.Logic.FO.PebbleType` by a multiset, which records how often each type is reached.

Two positions have the same counting type exactly when Duplicator wins the `n`-round bijective
`k`-pebble game between them (`countingType_eq_iff`): a bijection matching the moves of pebble `j`
type by type exists exactly when the two multisets agree (`Equiv.exists_apply_eq_iff_map_univ_eq`).
Every counting type is defined by a counting Hintikka formula of quantifier rank at most `n` whose
free variables are placed (`realize_countingHintikka`), which says how many moves of each pebble
reach each type. Together with the easy direction `BijPebbleWins.realize_iff`, this gives the
**game characterization of `C^k`**: on finite structures, Duplicator wins the `n`-round bijective
`k`-pebble game from `(S, a, b)` exactly when `a` and `b` satisfy the same `k`-variable counting
formulas of quantifier rank at most `n` with free variables in `S`
(`bijPebbleWins_iff_forall_realize_iff`), and the infinite game corresponds to all counting
formulas (`bijPebbleWinsForever_iff_forall_realize_iff`).

The hard direction needs finite structures, not only finitely many relation symbols. In the empty
language with one variable, `ℕ` and `ℝ` satisfy the same counting formulas, since every formula
defines the empty set or everything, so both sides count infinitely many witnesses. Yet there is no
bijection `ℕ ≃ ℝ`, so Spoiler wins the one-round bijective game. As explained at `PebbleWins`,
positions are total assignments, so for `k > 0` these statements say nothing about empty
structures.

## Main definitions

* `Cslib.Logic.FO.CountingType`, `Cslib.Logic.FO.countingType`: `k`-variable counting rank-`n`
  types and the type of a position in a finite structure.
* `Cslib.Logic.FO.countingHintikka`: the counting formula defining a counting type.

## Main results

* `Cslib.Logic.FO.countingType_eq_iff`: equal counting types are exactly winning positions of the
  `n`-round bijective `k`-pebble game.
* `Cslib.Logic.FO.realize_countingHintikka`: the counting Hintikka formula of a type defines it.
* `Cslib.Logic.FO.bijPebbleWins_of_forall_realize_iff`: **bijective pebble games, hard
  direction**.
* `Cslib.Logic.FO.bijPebbleWins_iff_forall_realize_iff`,
  `Cslib.Logic.FO.bijPebbleWinsForever_iff_forall_realize_iff`: **the game characterization of
  `C^k`** on finite structures, for finite games and for the infinite game.

## References

* [L. Hella, *Logical hierarchies in PTIME*][Hella1996] (unverified locator).
* [N. Immerman and E. Lander, *Describing graphs: a first-order approach to graph
  canonization*][ImmermanLander1990] (unverified locator).
* [J.-Y. Cai, M. Fürer, N. Immerman, *An optimal lower bound on the number of variables for graph
  identification*][CaiFurerImmerman1992], Theorem 4.5, for the variant of the game in which the
  players exchange sets of equal size, and Theorem 5.2, whose proof is by induction on the number
  of rounds as here.
* [N. Immerman, *Descriptive Complexity*][Immerman1999], Section 12.4 and Theorem 12.23
  (unverified locators).
* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004], Definition 8.12 and Theorem 8.13,
  the corresponding result for the bijective Ehrenfeucht–Fraïssé game and the infinitary counting
  logic `L*∞ω(Cnt)`.
-/

public section

universe u v w w'

open FirstOrder Language Structure

namespace Cslib.Logic.FO

variable {L : Language.{u, v}} {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N] {k : ℕ}

/-! ### Counting types of positions -/

variable (L) in
/-- The `k`-variable counting rank-`n` types, as combinatorial data: a rank-`0` type is a set of
atomic facts, and a rank-`(n + 1)` type is a set of atomic facts together with, for each pebble
index `j`, the multiset of rank-`n` types reached by moving pebble `j`. The body is exposed:
statements about types use its shape. -/
@[expose] def CountingType (k : ℕ) : ℕ → Type v
  | 0 => Set (AtomicIndex L k)
  | n + 1 => Set (AtomicIndex L k) × (Fin k → Multiset (CountingType k n))

/-- The `k`-variable counting rank-`n` type of the position `(S, a)` in a finite structure: the
atomic facts about the placed pebbles and, for `n + 1`, the multiset of types reached by moving
each pebble to each element. -/
def countingType [Fintype M] : ∀ (n : ℕ), Set (Fin k) → (Fin k → M) → CountingType L k n
  | 0, S, a => pebbleAtoms S a
  | n + 1, S, a => (pebbleAtoms S a,
      fun j => Finset.univ.val.map fun c : M => countingType n (insert j S) (Function.update a j c))

theorem countingType_zero [Fintype M] (S : Set (Fin k)) (a : Fin k → M) :
    countingType (L := L) 0 S a = pebbleAtoms S a := by
  rw [countingType]

theorem countingType_succ [Fintype M] {n : ℕ} (S : Set (Fin k)) (a : Fin k → M) :
    countingType (L := L) (n + 1) S a = (pebbleAtoms S a,
      fun j => Finset.univ.val.map fun c : M =>
        countingType n (insert j S) (Function.update a j c)) := by
  rw [countingType]

/-- Equality of rank-`(n + 1)` counting types is componentwise. -/
theorem CountingType.succ_ext_iff {n : ℕ} {T T' : CountingType L k (n + 1)} :
    T = T' ↔ T.1 = T'.1 ∧ ∀ j, T.2 j = T'.2 j :=
  Prod.ext_iff.trans (and_congr Iff.rfl funext_iff)

/-- Two positions in finite structures have the same `k`-variable counting rank-`n` type exactly
when Duplicator wins the `n`-round bijective `k`-pebble game between them. -/
theorem countingType_eq_iff [Fintype M] [Fintype N] :
    ∀ {n : ℕ} {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N},
      countingType (L := L) n S a = countingType n S b ↔ BijPebbleWins L n S a b
  | 0, S, a, b => by
    rw [bijPebbleWins_zero, countingType_zero, countingType_zero]
    exact pebbleAtoms_eq_iff
  | n + 1, S, a, b => by
    rw [bijPebbleWins_succ, CountingType.succ_ext_iff, countingType_succ, countingType_succ,
      pebbleAtoms_eq_iff]
    refine and_congr Iff.rfl (forall_congr' fun j => ?_)
    rw [← Equiv.exists_apply_eq_iff_map_univ_eq]
    refine exists_congr fun f => forall_congr' fun c => ?_
    rw [eq_comm, countingType_eq_iff]

/-! ### Counting Hintikka formulas -/

/-- In a finite structure, the number of values of `xⱼ` satisfying a predicate, counted by
`Set.encard`, is the cardinality of the corresponding subtype. -/
private theorem encard_setOf_eq_iff [Finite M] (p : M → Prop) (m : ℕ) :
    {c : M | p c}.encard = m ↔ Nat.card {c // p c} = m := by
  rw [← (Set.toFinite _).cast_ncard_eq, Nat.cast_inj, ← Nat.card_coe_set_eq]
  rfl

open scoped Classical in
/-- The `k`-variable counting Hintikka formula of a rank-`n` counting type of positions with placed
pebbles `S`: a counting formula of quantifier rank at most `n` with free variables in `S`,
satisfied in a finite structure exactly by the positions of that type. For `n + 1` it states the
atomic diagram and, for each pebble `j`, that every type `τ` in the multiset `T.2 j` is reached by
exactly as many moves of pebble `j` as its multiplicity, and that every move of pebble `j` reaches
a type in `T.2 j`. -/
noncomputable def countingHintikka [Finite (Σ l, L.Relations l)] :
    ∀ {n : ℕ}, Set (Fin k) → CountingType L k n → FiniteVariable.CountingFormula L k
  | 0, S, T => (pebbleAtomicDiagram S T).toCounting
  | _ + 1, S, T =>
    (pebbleAtomicDiagram S T.1).toCounting ⊓ FiniteVariable.CountingFormula.iInf fun j : Fin k =>
      FiniteVariable.CountingFormula.iInf (fun τ : (T.2 j).toFinset =>
          .exactly ((T.2 j).count τ.1) j (countingHintikka (insert j S) τ.1)) ⊓
        .all j (FiniteVariable.CountingFormula.iSup fun τ : (T.2 j).toFinset =>
          countingHintikka (insert j S) τ.1)

theorem realize_countingHintikka [Finite (Σ l, L.Relations l)] [Fintype M] :
    ∀ {n : ℕ} (S : Set (Fin k)) (T : CountingType L k n) (a : Fin k → M),
      (countingHintikka S T).Realize a ↔ countingType n S a = T
  | 0, S, T, a => by
    rw [countingHintikka, countingType_zero, FiniteVariable.Formula.realize_toCounting]
    exact realize_pebbleAtomicDiagram S T a
  | n + 1, S, T, a => by
    classical
    rw [CountingType.succ_ext_iff, countingType_succ, countingHintikka]
    simp only [FiniteVariable.CountingFormula.realize_inf,
      FiniteVariable.Formula.realize_toCounting, realize_pebbleAtomicDiagram,
      FiniteVariable.CountingFormula.realize_iInf, FiniteVariable.CountingFormula.realize_exactly,
      FiniteVariable.CountingFormula.realize_all, FiniteVariable.CountingFormula.realize_iSup,
      realize_countingHintikka, encard_setOf_eq_iff, Subtype.forall, Subtype.exists,
      Multiset.mem_toFinset, exists_prop, exists_eq_right']
    refine and_congr Iff.rfl (forall_congr' fun j => ?_)
    rw [Multiset.map_univ_eq_iff_card_fiber_eq]

theorem quantifierRank_countingHintikka_le [Finite (Σ l, L.Relations l)] :
    ∀ {n : ℕ} (S : Set (Fin k)) (T : CountingType L k n),
      (countingHintikka S T).quantifierRank ≤ n
  | 0, S, T => by
    rw [countingHintikka, FiniteVariable.Formula.quantifierRank_toCounting]
    exact (quantifierRank_pebbleAtomicDiagram S T).le
  | n + 1, S, T => by
    rw [countingHintikka, FiniteVariable.CountingFormula.quantifierRank_inf,
      FiniteVariable.Formula.quantifierRank_toCounting, quantifierRank_pebbleAtomicDiagram,
      max_le_iff]
    refine ⟨Nat.zero_le _, FiniteVariable.CountingFormula.quantifierRank_iInf_le fun j => ?_⟩
    rw [FiniteVariable.CountingFormula.quantifierRank_inf, max_le_iff,
      FiniteVariable.CountingFormula.quantifierRank_all]
    refine ⟨FiniteVariable.CountingFormula.quantifierRank_iInf_le fun τ => ?_,
      Nat.succ_le_succ (FiniteVariable.CountingFormula.quantifierRank_iSup_le fun τ =>
        quantifierRank_countingHintikka_le _ τ.1)⟩
    rw [FiniteVariable.CountingFormula.quantifierRank_exactly]
    exact Nat.succ_le_succ (quantifierRank_countingHintikka_le _ τ.1)

theorem freeVars_countingHintikka_subset [Finite (Σ l, L.Relations l)] :
    ∀ {n : ℕ} (S : Set (Fin k)) (T : CountingType L k n), ↑(countingHintikka S T).freeVars ⊆ S
  | 0, S, T => by
    rw [countingHintikka, FiniteVariable.Formula.freeVars_toCounting]
    exact freeVars_pebbleAtomicDiagram_subset S T
  | n + 1, S, T => by
    rw [countingHintikka, FiniteVariable.CountingFormula.freeVars_inf, Finset.coe_union,
      Set.union_subset_iff, FiniteVariable.Formula.freeVars_toCounting]
    refine ⟨freeVars_pebbleAtomicDiagram_subset S T.1,
      FiniteVariable.CountingFormula.freeVars_iInf_subset fun j => ?_⟩
    rw [FiniteVariable.CountingFormula.freeVars_inf, Finset.coe_union, Set.union_subset_iff,
      FiniteVariable.CountingFormula.freeVars_all, Finset.coe_erase, Set.sdiff_subset_iff,
      ← Set.insert_eq]
    refine ⟨FiniteVariable.CountingFormula.freeVars_iInf_subset fun τ => ?_,
      FiniteVariable.CountingFormula.freeVars_iSup_subset fun τ =>
        freeVars_countingHintikka_subset _ τ.1⟩
    rw [FiniteVariable.CountingFormula.freeVars_exactly, Finset.coe_erase, Set.sdiff_subset_iff,
      ← Set.insert_eq]
    exact freeVars_countingHintikka_subset _ τ.1

/-! ### The game characterization of `C^k` -/

/-- **Bijective pebble games, hard direction.** For a language with finitely many relation symbols
and finite structures, if `a` and `b` satisfy the same `k`-variable counting formulas of quantifier
rank at most `n` with free variables in `S`, then Duplicator wins the `n`-round bijective
`k`-pebble game from `(S, a, b)`. Only the counting Hintikka formula of the type of `(S, a)` is
used. -/
theorem bijPebbleWins_of_forall_realize_iff [Finite (Σ l, L.Relations l)] [Finite M] [Finite N]
    {n : ℕ} {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N}
    (h : ∀ φ : FiniteVariable.CountingFormula L k, φ.quantifierRank ≤ n → ↑φ.freeVars ⊆ S →
      (φ.Realize a ↔ φ.Realize b)) : BijPebbleWins L n S a b := by
  have := Fintype.ofFinite M
  have := Fintype.ofFinite N
  rw [← countingType_eq_iff]
  have hb := (h _ (quantifierRank_countingHintikka_le S (countingType (L := L) n S a))
    (freeVars_countingHintikka_subset S _)).1 ((realize_countingHintikka S _ a).2 rfl)
  exact ((realize_countingHintikka S _ b).1 hb).symm

/-- **The game characterization of `C^k`** ([Hella1996]; [CaiFurerImmerman1992], Theorem 4.5;
[Immerman1999], Theorem 12.23). For a language with finitely many relation symbols and finite
structures, Duplicator wins the `n`-round bijective `k`-pebble game from `(S, a, b)` exactly when
`a` and `b` satisfy the same `k`-variable counting formulas of quantifier rank at most `n` with
free variables in `S`. -/
theorem bijPebbleWins_iff_forall_realize_iff [Finite (Σ l, L.Relations l)] [Finite M] [Finite N]
    {n : ℕ} {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N} :
    BijPebbleWins L n S a b ↔ ∀ φ : FiniteVariable.CountingFormula L k, φ.quantifierRank ≤ n →
      ↑φ.freeVars ⊆ S → (φ.Realize a ↔ φ.Realize b) :=
  ⟨fun h _ hr hS => h.realize_iff hr hS, bijPebbleWins_of_forall_realize_iff⟩

/-- **The infinite bijective game and `C^k`.** For a language with finitely many relation symbols
and finite structures, Duplicator wins the infinite bijective `k`-pebble game from `(S, a, b)`
exactly when `a` and `b` satisfy the same `k`-variable counting formulas with free variables in
`S`. -/
theorem bijPebbleWinsForever_iff_forall_realize_iff [Finite (Σ l, L.Relations l)] [Finite M]
    [Finite N] {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N} :
    BijPebbleWinsForever L S a b ↔ ∀ φ : FiniteVariable.CountingFormula L k,
      ↑φ.freeVars ⊆ S → (φ.Realize a ↔ φ.Realize b) := by
  rw [bijPebbleWinsForever_iff_forall_bijPebbleWins]
  exact ⟨fun h _ hS => (h _).realize_iff le_rfl hS,
    fun h _ => bijPebbleWins_of_forall_realize_iff fun φ _ hS => h φ hS⟩

end Cslib.Logic.FO
