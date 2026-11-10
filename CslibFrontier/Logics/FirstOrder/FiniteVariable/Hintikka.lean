/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.EhrenfeuchtFraisse.Hintikka
public import CslibFrontier.Logics.FirstOrder.FiniteVariable.PebbleGame

/-!
# Pebble games and finite-variable logic

For a language with finitely many relation symbols, the `k`-variable rank-`n` type of a position
`(S, a)` is finite combinatorial data (`Cslib.Logic.FO.PebbleType`): the atomic facts about the
placed pebbles and, if `n > 0`, for each pebble index `i` the set of rank-`(n - 1)` types reached
by moving pebble `i`. Two positions have the same type exactly when Duplicator wins the `n`-round
`k`-pebble game between them (`pebbleType_eq_iff`), and every type is defined by a `k`-variable
Hintikka formula of quantifier rank at most `n` whose free variables are placed
(`realize_pebbleHintikka`, `quantifierRank_pebbleHintikka_le`, `freeVars_pebbleHintikka_subset`).
Together with the easy direction `PebbleWins.realize_iff`, this gives the **pebble-game
characterization of `FO^k`**: Duplicator wins the `n`-round `k`-pebble game from `(S, a, b)`
exactly when `a` and `b` satisfy the same `k`-variable formulas of quantifier rank at most `n` with
free variables in `S` (`pebbleWins_iff_forall_realize_iff`). On finite structures the infinite game
corresponds to all `k`-variable formulas (`pebbleWinsForever_iff_forall_realize_iff`).

The construction follows `CslibFrontier.Logics.FirstOrder.EhrenfeuchtFraisse.Hintikka` and reuses
its atomic formulas `Cslib.Logic.FO.AtomicIndex`. The difference is that a position of the pebble
game has a fixed number of pebbles and a set of placed ones, while a position of the
Ehrenfeucht–Fraïssé game grows by one element per round, so the types and Hintikka formulas are
indexed differently. Every atomic index is a `k`-variable atomic formula
(`AtomicIndex.toFiniteVariable`), and `partialIsoOn_iff_holds` is the placed-pebble form of
`partialIso_iff_holds`.

The hypothesis `[Finite (Σ l, L.Relations l)]` is used only by the Hintikka direction; the
structures are arbitrary, except that the infinite game needs finite structures. As explained at
`PebbleWins`, positions are total assignments, so for `k > 0` these statements say nothing about
empty structures.

## Main definitions

* `Cslib.Logic.FO.AtomicIndex.toFiniteVariable`: an atomic index as a `k`-variable formula.
* `Cslib.Logic.FO.PebbleType`, `Cslib.Logic.FO.pebbleType`: `k`-variable rank-`n` types and the
  type of a position.
* `Cslib.Logic.FO.pebbleAtomicDiagram`, `Cslib.Logic.FO.pebbleHintikka`: the defining formulas of
  atomic types and of `k`-variable rank-`n` types.

## Main results

* `Cslib.Logic.FO.pebbleType_eq_iff`: equal types are exactly winning positions of the `n`-round
  `k`-pebble game.
* `Cslib.Logic.FO.realize_pebbleHintikka`: the Hintikka formula of a type defines it.
* `Cslib.Logic.FO.pebbleWins_of_forall_realize_iff`: **pebble games, hard direction**.
* `Cslib.Logic.FO.pebbleWins_iff_forall_realize_iff`,
  `Cslib.Logic.FO.pebbleWinsForever_iff_forall_realize_iff`: **the pebble-game characterization of
  `FO^k`**, for finite games and, on finite structures, for the infinite game.
* `Cslib.Logic.FO.DuplicatorWins.pebbleWins`: a winning position of the Ehrenfeucht–Fraïssé game
  wins the pebble game with the same number of rounds.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Theorem 6.10: the characterization for
  `FO^k` of rank `m`, from a `k`-configuration, over a finite relational vocabulary and arbitrary
  structures, which is the setting here. Its proof uses the finiteness of rank-`m` formulas up to
  equivalence (Exercise 6.11); the Hintikka formulas here make that finiteness explicit.
* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004], Theorem 11.5 and Corollary 11.9,
  stated for `L^k_∞ω` on finite structures; the remark before Proposition 11.8 reduces rank `n` to
  `FO^k`, and Proposition 11.8 gives the infinite game.
-/

public section

universe u v w w'

open FirstOrder Language Structure

namespace Cslib.Logic.FO

variable {L : Language.{u, v}} {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N] {k : ℕ}

/-! ### Atomic types of placed pebbles -/

/-- The `k`-variable atomic formula with index `i`. -/
def AtomicIndex.toFiniteVariable : AtomicIndex L k → FiniteVariable.Formula L k
  | .inl ⟨(i, j)⟩ => .equal i j
  | .inr ⟨⟨_, R⟩, f⟩ => .rel R f

@[simp] theorem AtomicIndex.realize_toFiniteVariable (i : AtomicIndex L k) (a : Fin k → M) :
    i.toFiniteVariable.Realize a ↔ i.Holds a := by
  rcases i with ⟨⟨i, j⟩⟩ | ⟨⟨l, R⟩, f⟩
  · rw [toFiniteVariable, FiniteVariable.Formula.realize_equal, holds_inl]
  · rw [toFiniteVariable, FiniteVariable.Formula.realize_rel, holds_inr]

@[simp] theorem AtomicIndex.quantifierRank_toFiniteVariable (i : AtomicIndex L k) :
    i.toFiniteVariable.quantifierRank = 0 := by
  rcases i with ⟨⟨i, j⟩⟩ | ⟨⟨l, R⟩, f⟩
  · rw [toFiniteVariable, FiniteVariable.Formula.quantifierRank_equal]
  · rw [toFiniteVariable, FiniteVariable.Formula.quantifierRank_rel]

/-- The pebbles in `S` define a partial isomorphism exactly when both assignments satisfy the
same atomic formulas whose variables lie in `S`. -/
theorem partialIsoOn_iff_holds {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N} :
    PartialIsoOn L S a b ↔
      ∀ i : AtomicIndex L k, ↑i.toFiniteVariable.freeVars ⊆ S → (i.Holds a ↔ i.Holds b) := by
  constructor
  · rintro ⟨heq, hrel⟩ (⟨⟨i, j⟩⟩ | ⟨⟨l, R⟩, f⟩) hS
    · simp only [AtomicIndex.toFiniteVariable, FiniteVariable.Formula.freeVars_equal,
        Finset.coe_insert, Finset.coe_singleton, Set.insert_subset_iff,
        Set.singleton_subset_iff] at hS
      rw [AtomicIndex.holds_inl, AtomicIndex.holds_inl]
      exact heq i hS.1 j hS.2
    · simp only [AtomicIndex.toFiniteVariable, FiniteVariable.Formula.freeVars_rel,
        Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.range_subset_iff] at hS
      rw [AtomicIndex.holds_inr, AtomicIndex.holds_inr]
      exact hrel R f hS
  · intro h
    refine ⟨fun i hi j hj => ?_, fun R f hf => ?_⟩
    · have := h (.inl ⟨(i, j)⟩) (by
        simp only [AtomicIndex.toFiniteVariable, FiniteVariable.Formula.freeVars_equal,
          Finset.coe_insert, Finset.coe_singleton, Set.insert_subset_iff,
          Set.singleton_subset_iff]
        exact ⟨hi, hj⟩)
      rwa [AtomicIndex.holds_inl, AtomicIndex.holds_inl] at this
    · have := h (.inr ⟨⟨_, R⟩, f⟩) (by
        simp only [AtomicIndex.toFiniteVariable, FiniteVariable.Formula.freeVars_rel,
          Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.range_subset_iff]
        exact hf)
      rwa [AtomicIndex.holds_inr, AtomicIndex.holds_inr] at this

/-- With all pebbles placed, a partial isomorphism on the placed pebbles is a partial isomorphism
in the sense of the Ehrenfeucht–Fraïssé game. -/
theorem partialIsoOn_univ_iff {a : Fin k → M} {b : Fin k → N} :
    PartialIsoOn L Set.univ a b ↔ PartialIso L a b := by
  rw [partialIsoOn_iff_holds, partialIso_iff_holds]
  simp only [Set.subset_univ, forall_const]

/-! ### Types of positions -/

variable (L) in
/-- The `k`-variable rank-`n` types, as combinatorial data: a rank-`0` type is a set of atomic
facts, and a rank-`(n + 1)` type is a set of atomic facts together with, for each pebble index
`i`, the set of rank-`n` types reached by moving pebble `i`. The body is exposed: statements about
types use its shape. -/
@[expose] def PebbleType (k : ℕ) : ℕ → Type v
  | 0 => Set (AtomicIndex L k)
  | n + 1 => Set (AtomicIndex L k) × (Fin k → Set (PebbleType k n))

/-- For finitely many relation symbols, there are finitely many `k`-variable rank-`n` types. -/
instance PebbleType.finite [Finite (Σ l, L.Relations l)] (k : ℕ) : ∀ n, Finite (PebbleType L k n)
  | 0 => inferInstanceAs (Finite (Set _))
  | n + 1 =>
    have := PebbleType.finite k n
    inferInstanceAs (Finite (Set _ × (Fin k → Set _)))

/-- The `k`-variable rank-`n` type of the position `(S, a)`: the atomic facts about the placed
pebbles and, for `n + 1`, the types reached by moving each pebble. -/
def pebbleType : ∀ (n : ℕ), Set (Fin k) → (Fin k → M) → PebbleType L k n
  | 0, S, a => {i | ↑i.toFiniteVariable.freeVars ⊆ S ∧ i.Holds a}
  | n + 1, S, a => ({i | ↑i.toFiniteVariable.freeVars ⊆ S ∧ i.Holds a},
      fun j => Set.range fun c : M => pebbleType n (insert j S) (Function.update a j c))

theorem pebbleType_zero (S : Set (Fin k)) (a : Fin k → M) :
    pebbleType (L := L) 0 S a = {i | ↑i.toFiniteVariable.freeVars ⊆ S ∧ i.Holds a} := by
  rw [pebbleType]

theorem pebbleType_succ {n : ℕ} (S : Set (Fin k)) (a : Fin k → M) :
    pebbleType (L := L) (n + 1) S a = ({i | ↑i.toFiniteVariable.freeVars ⊆ S ∧ i.Holds a},
      fun j => Set.range fun c : M => pebbleType n (insert j S) (Function.update a j c)) := by
  rw [pebbleType]

/-- Equality of rank-`(n + 1)` types is componentwise. -/
theorem PebbleType.succ_ext_iff {n : ℕ} {T T' : PebbleType L k (n + 1)} :
    T = T' ↔ T.1 = T'.1 ∧ ∀ j, T.2 j = T'.2 j :=
  Prod.ext_iff.trans (and_congr Iff.rfl funext_iff)

private theorem atomic_eq_iff {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N} :
    {i : AtomicIndex L k | ↑i.toFiniteVariable.freeVars ⊆ S ∧ i.Holds a} =
        {i | ↑i.toFiniteVariable.freeVars ⊆ S ∧ i.Holds b} ↔ PartialIsoOn L S a b := by
  rw [partialIsoOn_iff_holds, Set.ext_iff]
  simp only [Set.mem_ofPred_eq, and_congr_right_iff]

/-- Two positions have the same `k`-variable rank-`n` type exactly when Duplicator wins the
`n`-round `k`-pebble game between them. -/
theorem pebbleType_eq_iff : ∀ {n : ℕ} {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N},
    pebbleType (L := L) n S a = pebbleType n S b ↔ PebbleWins L n S a b
  | 0, S, a, b => by
    rw [pebbleWins_zero, pebbleType_zero, pebbleType_zero]
    exact atomic_eq_iff
  | n + 1, S, a, b => by
    rw [pebbleWins_succ, PebbleType.succ_ext_iff, pebbleType_succ, pebbleType_succ, atomic_eq_iff]
    simp only [Set.Subset.antisymm_iff, Set.range_subset_iff, Set.mem_range, forall_and]
    refine and_congr Iff.rfl (and_congr ?_ ?_)
    · refine forall_congr' fun j => forall_congr' fun c => exists_congr fun d => ?_
      rw [eq_comm, pebbleType_eq_iff]
    · refine forall_congr' fun j => forall_congr' fun d => exists_congr fun c => ?_
      rw [pebbleType_eq_iff]

/-! ### Hintikka formulas -/

open scoped Classical in
/-- The conjunction of the atomic facts in `T` about the pebbles in `S` and the negations of
those not in `T`. Atomic facts in `T` that mention unplaced pebbles make the formula false. -/
noncomputable def pebbleAtomicDiagram [Finite (Σ l, L.Relations l)] (S : Set (Fin k))
    (T : Set (AtomicIndex L k)) : FiniteVariable.Formula L k :=
  FiniteVariable.Formula.iInf fun i : AtomicIndex L k =>
    if ↑i.toFiniteVariable.freeVars ⊆ S then
      (if i ∈ T then i.toFiniteVariable else i.toFiniteVariable.not)
    else (if i ∈ T then ⊥ else ⊤)

theorem realize_pebbleAtomicDiagram [Finite (Σ l, L.Relations l)] (S : Set (Fin k))
    (T : Set (AtomicIndex L k)) (a : Fin k → M) :
    (pebbleAtomicDiagram S T).Realize a ↔
      {i | ↑i.toFiniteVariable.freeVars ⊆ S ∧ i.Holds a} = T := by
  classical
  simp only [pebbleAtomicDiagram, FiniteVariable.Formula.realize_iInf, Set.ext_iff,
    Set.mem_ofPred_eq]
  refine forall_congr' fun i => ?_
  by_cases hS : ↑i.toFiniteVariable.freeVars ⊆ S <;> by_cases hT : i ∈ T <;> simp [hS, hT]

theorem quantifierRank_pebbleAtomicDiagram [Finite (Σ l, L.Relations l)] (S : Set (Fin k))
    (T : Set (AtomicIndex L k)) : (pebbleAtomicDiagram S T).quantifierRank = 0 := by
  classical
  refine Nat.le_zero.1 (FiniteVariable.Formula.quantifierRank_iInf_le fun i => ?_)
  by_cases hS : ↑i.toFiniteVariable.freeVars ⊆ S <;> by_cases hT : i ∈ T <;> simp [hS, hT]

theorem freeVars_pebbleAtomicDiagram_subset [Finite (Σ l, L.Relations l)] (S : Set (Fin k))
    (T : Set (AtomicIndex L k)) : ↑(pebbleAtomicDiagram S T).freeVars ⊆ S := by
  classical
  refine FiniteVariable.Formula.freeVars_iInf_subset fun i => ?_
  by_cases hS : ↑i.toFiniteVariable.freeVars ⊆ S <;> by_cases hT : i ∈ T <;> simp [hS, hT]

/-- The `k`-variable Hintikka formula of a rank-`n` type of positions with placed pebbles `S`: a
`k`-variable formula of quantifier rank at most `n` with free variables in `S`, satisfied exactly
by the positions of that type. For `n + 1` it states the atomic diagram and, for each pebble `j`,
that every type in `T.2 j` is reached by moving pebble `j` and that every move of pebble `j`
reaches one of them. -/
noncomputable def pebbleHintikka [Finite (Σ l, L.Relations l)] :
    ∀ {n : ℕ}, Set (Fin k) → PebbleType L k n → FiniteVariable.Formula L k
  | 0, S, T => pebbleAtomicDiagram S T
  | _ + 1, S, T =>
    pebbleAtomicDiagram S T.1 ⊓ FiniteVariable.Formula.iInf fun j : Fin k =>
      FiniteVariable.Formula.iInf (fun T' : T.2 j => .ex j (pebbleHintikka (insert j S) T'.1)) ⊓
        .all j (FiniteVariable.Formula.iSup fun T' : T.2 j => pebbleHintikka (insert j S) T'.1)

theorem realize_pebbleHintikka [Finite (Σ l, L.Relations l)] :
    ∀ {n : ℕ} (S : Set (Fin k)) (T : PebbleType L k n) (a : Fin k → M),
      (pebbleHintikka S T).Realize a ↔ pebbleType n S a = T
  | 0, S, T, a => by
    rw [pebbleHintikka, pebbleType_zero]
    exact realize_pebbleAtomicDiagram S T a
  | n + 1, S, T, a => by
    rw [PebbleType.succ_ext_iff, pebbleType_succ, pebbleHintikka]
    simp only [FiniteVariable.Formula.realize_inf, FiniteVariable.Formula.realize_iInf,
      FiniteVariable.Formula.realize_ex, FiniteVariable.Formula.realize_all,
      FiniteVariable.Formula.realize_iSup, realize_pebbleHintikka, realize_pebbleAtomicDiagram,
      Subtype.forall, Subtype.exists, exists_prop, exists_eq_right', Set.range_eq_iff, forall_and]
    exact and_congr Iff.rfl and_comm

theorem quantifierRank_pebbleHintikka_le [Finite (Σ l, L.Relations l)] :
    ∀ {n : ℕ} (S : Set (Fin k)) (T : PebbleType L k n), (pebbleHintikka S T).quantifierRank ≤ n
  | 0, S, T => by
    rw [pebbleHintikka]
    exact (quantifierRank_pebbleAtomicDiagram S T).le
  | n + 1, S, T => by
    rw [pebbleHintikka, FiniteVariable.Formula.quantifierRank_inf,
      quantifierRank_pebbleAtomicDiagram, max_le_iff]
    refine ⟨Nat.zero_le _, FiniteVariable.Formula.quantifierRank_iInf_le fun j => ?_⟩
    rw [FiniteVariable.Formula.quantifierRank_inf, max_le_iff,
      FiniteVariable.Formula.quantifierRank_all]
    refine ⟨FiniteVariable.Formula.quantifierRank_iInf_le fun T' => ?_,
      Nat.succ_le_succ (FiniteVariable.Formula.quantifierRank_iSup_le fun T' =>
        quantifierRank_pebbleHintikka_le _ T'.1)⟩
    rw [FiniteVariable.Formula.quantifierRank_ex]
    exact Nat.succ_le_succ (quantifierRank_pebbleHintikka_le _ T'.1)

theorem freeVars_pebbleHintikka_subset [Finite (Σ l, L.Relations l)] :
    ∀ {n : ℕ} (S : Set (Fin k)) (T : PebbleType L k n), ↑(pebbleHintikka S T).freeVars ⊆ S
  | 0, S, T => by
    rw [pebbleHintikka]
    exact freeVars_pebbleAtomicDiagram_subset S T
  | n + 1, S, T => by
    rw [pebbleHintikka, FiniteVariable.Formula.freeVars_inf, Finset.coe_union,
      Set.union_subset_iff]
    refine ⟨freeVars_pebbleAtomicDiagram_subset S T.1,
      FiniteVariable.Formula.freeVars_iInf_subset fun j => ?_⟩
    rw [FiniteVariable.Formula.freeVars_inf, Finset.coe_union, Set.union_subset_iff,
      FiniteVariable.Formula.freeVars_all, Finset.coe_erase, Set.sdiff_subset_iff,
      ← Set.insert_eq]
    refine ⟨FiniteVariable.Formula.freeVars_iInf_subset fun T' => ?_,
      FiniteVariable.Formula.freeVars_iSup_subset fun T' =>
        freeVars_pebbleHintikka_subset _ T'.1⟩
    rw [FiniteVariable.Formula.freeVars_ex, Finset.coe_erase, Set.sdiff_subset_iff,
      ← Set.insert_eq]
    exact freeVars_pebbleHintikka_subset _ T'.1

/-! ### The pebble-game characterization of `FO^k` -/

/-- **Pebble games, hard direction.** For a language with finitely many relation symbols, if `a`
and `b` satisfy the same `k`-variable formulas of quantifier rank at most `n` with free variables
in `S`, then Duplicator wins the `n`-round `k`-pebble game from `(S, a, b)`. Only the Hintikka
formula of the type of `(S, a)` is used. -/
theorem pebbleWins_of_forall_realize_iff [Finite (Σ l, L.Relations l)] {n : ℕ}
    {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N}
    (h : ∀ φ : FiniteVariable.Formula L k, φ.quantifierRank ≤ n → ↑φ.freeVars ⊆ S →
      (φ.Realize a ↔ φ.Realize b)) : PebbleWins L n S a b := by
  rw [← pebbleType_eq_iff]
  have hb := (h _ (quantifierRank_pebbleHintikka_le S (pebbleType (L := L) n S a))
    (freeVars_pebbleHintikka_subset S _)).1 ((realize_pebbleHintikka S _ a).2 rfl)
  exact ((realize_pebbleHintikka S _ b).1 hb).symm

/-- **The pebble-game characterization of `FO^k`** ([Immerman1999], Theorem 6.10; [Libkin2004],
Theorem 11.5 and Corollary 11.9 with the remark before Proposition 11.8). For a language with
finitely many relation symbols, Duplicator wins the `n`-round `k`-pebble game from `(S, a, b)`
exactly when `a` and `b` satisfy the same `k`-variable formulas of quantifier rank at most `n` with
free variables in `S`. -/
theorem pebbleWins_iff_forall_realize_iff [Finite (Σ l, L.Relations l)] {n : ℕ}
    {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N} :
    PebbleWins L n S a b ↔ ∀ φ : FiniteVariable.Formula L k, φ.quantifierRank ≤ n →
      ↑φ.freeVars ⊆ S → (φ.Realize a ↔ φ.Realize b) :=
  ⟨fun h _ hr hS => h.realize_iff hr hS, pebbleWins_of_forall_realize_iff⟩

/-- **The infinite pebble game and `FO^k`** ([Libkin2004], Theorem 11.5(b), Proposition 11.8 and
Corollary 11.9). For a language with finitely many relation symbols and finite structures,
Duplicator wins the infinite `k`-pebble game from `(S, a, b)` exactly when `a` and `b` satisfy the
same `k`-variable formulas with free variables in `S`. -/
theorem pebbleWinsForever_iff_forall_realize_iff [Finite (Σ l, L.Relations l)] [Finite M]
    [Finite N] {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N} :
    PebbleWinsForever L S a b ↔ ∀ φ : FiniteVariable.Formula L k, ↑φ.freeVars ⊆ S →
      (φ.Realize a ↔ φ.Realize b) := by
  rw [pebbleWinsForever_iff_forall_pebbleWins]
  exact ⟨fun h _ hS => (h _).realize_iff le_rfl hS,
    fun h _ => pebbleWins_of_forall_realize_iff fun φ _ hS => h φ hS⟩

/-- A winning position of the `n`-round Ehrenfeucht–Fraïssé game from `(a, b)` wins the `n`-round
`k`-pebble game from `(S, a, b)` for every set `S` of placed pebbles: `k`-variable formulas are
first-order formulas (`FiniteVariable.Formula.toFormula`). The proof goes through the logic, so it
assumes a relational language with finitely many relation symbols. -/
theorem DuplicatorWins.pebbleWins [L.IsRelational] [Finite (Σ l, L.Relations l)] {n : ℕ}
    {a : Fin k → M} {b : Fin k → N} (h : DuplicatorWins L n a b) (S : Set (Fin k)) :
    PebbleWins L n S a b := by
  refine pebbleWins_of_forall_realize_iff fun φ hr _ => ?_
  rw [← FiniteVariable.Formula.realize_toFormula, ← FiniteVariable.Formula.realize_toFormula]
  exact h.formula_realize_iff (by rwa [FiniteVariable.Formula.quantifierRank_toFormula])

end Cslib.Logic.FO
