/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.FiniteVariable.Counting
public import CslibFrontier.Logics.FirstOrder.FiniteVariable.PebbleGame
import CslibFrontier.Foundations.Data.Set.EqOnUpdate
import CslibFrontier.Foundations.Order.AntitoneSwap

/-!
# Bijective pebble games

Hella's bijective `k`-pebble game is the game for the counting logic `C^k`. Each round has two
parts: Spoiler picks a pebble index `i`, Duplicator answers with a bijection `f : M ≃ N`, and then
Spoiler places the `M`-pebble of pair `i` on any `c`, which puts the `N`-pebble of pair `i` on
`f c`. Duplicator wins a play when, after every round, the placed pairs define a partial
isomorphism. Because she answers with a bijection, Duplicator commits to one answer for every
point Spoiler may choose and must use every element of `N` exactly once.

Spoiler picks the pebble before Duplicator picks the bijection. This is Hella's order
([Hella1996]), and Duplicator can use the choice. If she had to commit to one bijection for every
pebble, the game would be strictly harder for her and would no longer characterize `C^k`. On the
cycle `C₆` and two disjoint triangles, which agree on `C²`, Spoiler would then win in three rounds:
he puts the two pebbles on vertices at distance two in `C₆`, which a bijection fixed in advance
sends to different triangles, and then moves one of them to their common neighbor.

Positions are as in `CslibFrontier.Logics.FirstOrder.FiniteVariable.PebbleGame`: a set
`S : Set (Fin k)` of placed pebbles with total assignments `a : Fin k → M`, `b : Fin k → N`, so
for `k > 0` the statements say nothing about empty structures.

`BijPebbleWins L n S a b` says that Duplicator wins the `n`-round game from the position, and
`BijPebbleWinsForever L S a b` that she wins the game that continues forever. A won bijective
game is a won pebble game (`BijPebbleWins.pebbleWins`), and with a round left it forces a
bijection `M ≃ N` (`BijPebbleWins.nonempty_equiv`). `BijPebbleWins.realize_iff` is the easy
direction of the game characterization of `C^k`: a winning position satisfies the same counting
formulas of quantifier rank at most `n` whose free variables are placed. The converse, for finite
structures, is in `CslibFrontier.Logics.FirstOrder.FiniteVariable.CountingHintikka`.

## Main definitions

* `Cslib.Logic.FO.BijPebbleWins`: Duplicator wins the `n`-round bijective `k`-pebble game.
* `Cslib.Logic.FO.IsBijPebbleBackAndForth`: invariants that Duplicator can maintain forever.
* `Cslib.Logic.FO.BijPebbleWinsForever`: Duplicator wins the infinite bijective `k`-pebble game.

## Main results

* `Cslib.Logic.FO.BijPebbleWins.mono`, `Cslib.Logic.FO.BijPebbleWins.of_subset`,
  `Cslib.Logic.FO.bijPebbleWins_congr`: monotonicity and independence of unplaced pebbles.
* `Cslib.Logic.FO.BijPebbleWins.refl`, `Cslib.Logic.FO.BijPebbleWins.symm`,
  `Cslib.Logic.FO.BijPebbleWins.trans`, `FirstOrder.Language.Equiv.bijPebbleWins`: the
  equivalence-relation laws and invariance under isomorphism.
* `Cslib.Logic.FO.BijPebbleWins.pebbleWins`: the bijective game is harder for Duplicator.
* `Cslib.Logic.FO.bijPebbleWinsForever_iff_forall_bijPebbleWins`: when `M` is finite, the
  infinite game is won exactly when every finite game is.
* `Cslib.Logic.FO.BijPebbleWins.realize_iff`, `Cslib.Logic.FO.BijPebbleWinsForever.realize_iff`:
  the easy direction of the game characterization of `C^k`.

## References

* [L. Hella, *Logical hierarchies in PTIME*][Hella1996] (unverified locator).
* [N. Immerman, *Descriptive Complexity*][Immerman1999], Section 12.4 (unverified locator).
* [J.-Y. Cai, M. Fürer, N. Immerman, *An optimal lower bound on the number of variables for graph
  identification*][CaiFurerImmerman1992], Section 4.1, for the equivalent game in which Spoiler and
  Duplicator exchange sets of equal size.
-/

public section

universe u v w w' w''

open FirstOrder Language Structure

namespace Cslib.Logic.FO

variable {L : Language.{u, v}} {M : Type w} {N : Type w'} {P : Type w''}
  [L.Structure M] [L.Structure N] [L.Structure P] {k : ℕ}

variable (L) in
/-- Duplicator wins the `n`-round bijective `k`-pebble game from the position `(S, a, b)`: the
placed pebbles define a partial isomorphism and, if a round remains, for every pebble index `i`
chosen by Spoiler there is a bijection `f : M ≃ N` such that, wherever Spoiler places the
`M`-pebble of pair `i`, say on `c`, the position with the `N`-pebble of pair `i` on `f c` is won
for the remaining rounds.

Spoiler picks the pebble index before Duplicator picks the bijection, which lets the bijection
depend on the index (see the module docstring). As for `PebbleWins`,
positions are total assignments, so the statement is vacuous for `k > 0` when `M` or `N` is
empty. -/
def BijPebbleWins : ℕ → Set (Fin k) → (Fin k → M) → (Fin k → N) → Prop
  | 0, S, a, b => PartialIsoOn L S a b
  | n + 1, S, a, b => PartialIsoOn L S a b ∧
      ∀ i, ∃ f : M ≃ N, ∀ c,
        BijPebbleWins n (insert i S) (Function.update a i c) (Function.update b i (f c))

theorem bijPebbleWins_zero {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N} :
    BijPebbleWins L 0 S a b ↔ PartialIsoOn L S a b := by
  rw [BijPebbleWins]

theorem bijPebbleWins_succ {n : ℕ} {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N} :
    BijPebbleWins L (n + 1) S a b ↔ PartialIsoOn L S a b ∧
      ∀ i, ∃ f : M ≃ N, ∀ c,
        BijPebbleWins L n (insert i S) (Function.update a i c) (Function.update b i (f c)) := by
  rw [BijPebbleWins]

theorem BijPebbleWins.partialIsoOn {n : ℕ} {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N}
    (h : BijPebbleWins L n S a b) : PartialIsoOn L S a b := by
  cases n with
  | zero => exact bijPebbleWins_zero.1 h
  | succ n => exact (bijPebbleWins_succ.1 h).1

/-- Duplicator's answer to Spoiler's choice of the pebble index `i`. -/
theorem BijPebbleWins.move {n : ℕ} {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N}
    (h : BijPebbleWins L (n + 1) S a b) (i : Fin k) :
    ∃ f : M ≃ N, ∀ c,
      BijPebbleWins L n (insert i S) (Function.update a i c) (Function.update b i (f c)) :=
  (bijPebbleWins_succ.1 h).2 i

/-- If Duplicator wins a bijective game with at least one round, with at least one pebble, the
structures are in bijection. -/
theorem BijPebbleWins.nonempty_equiv {n : ℕ} {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N}
    (h : BijPebbleWins L (n + 1) S a b) (i : Fin k) : Nonempty (M ≃ N) :=
  let ⟨f, _⟩ := h.move i
  ⟨f⟩

/-! ### Basic properties of the game -/

/-- Winning a game implies winning every shorter game. -/
theorem BijPebbleWins.mono : ∀ {m n : ℕ} {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N},
    m ≤ n → BijPebbleWins L n S a b → BijPebbleWins L m S a b
  | 0, _, _, _, _, _, h => bijPebbleWins_zero.2 h.partialIsoOn
  | _ + 1, _ + 1, _, _, _, hmn, h => bijPebbleWins_succ.2 ⟨h.partialIsoOn,
      fun i => (h.move i).imp fun _ hf c => (hf c).mono (by omega)⟩
  | _ + 1, 0, _, _, _, hmn, _ => absurd hmn (by omega)

/-- Lifting placed pebbles keeps the position winning. -/
theorem BijPebbleWins.of_subset :
    ∀ {n : ℕ} {S T : Set (Fin k)} {a : Fin k → M} {b : Fin k → N},
      S ⊆ T → BijPebbleWins L n T a b → BijPebbleWins L n S a b
  | 0, _, _, _, _, hST, h => bijPebbleWins_zero.2 (h.partialIsoOn.mono hST)
  | _ + 1, _, _, _, _, hST, h => bijPebbleWins_succ.2 ⟨h.partialIsoOn.mono hST,
      fun i => (h.move i).imp fun _ hf c => (hf c).of_subset (Set.insert_subset_insert hST)⟩

/-- Winning depends only on the positions of the placed pebbles. -/
theorem bijPebbleWins_congr :
    ∀ {n : ℕ} {S : Set (Fin k)} {a a' : Fin k → M} {b b' : Fin k → N},
      Set.EqOn a a' S → Set.EqOn b b' S → BijPebbleWins L n S a b → BijPebbleWins L n S a' b'
  | 0, _, _, _, _, _, ha, hb, h => bijPebbleWins_zero.2 (h.partialIsoOn.congr ha hb)
  | _ + 1, _, _, _, _, _, ha, hb, h => bijPebbleWins_succ.2 ⟨h.partialIsoOn.congr ha hb,
      fun i => (h.move i).imp fun f hf c =>
        bijPebbleWins_congr (ha.update_insert i c) (hb.update_insert i (f c)) (hf c)⟩

theorem BijPebbleWins.refl : ∀ (n : ℕ) (S : Set (Fin k)) (a : Fin k → M), BijPebbleWins L n S a a
  | 0, S, a => bijPebbleWins_zero.2 (PartialIsoOn.refl S a)
  | n + 1, S, a => bijPebbleWins_succ.2 ⟨PartialIsoOn.refl S a,
      fun _ => ⟨Equiv.refl M, fun _ => BijPebbleWins.refl n _ _⟩⟩

theorem BijPebbleWins.symm : ∀ {n : ℕ} {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N},
    BijPebbleWins L n S a b → BijPebbleWins L n S b a
  | 0, _, _, _, h => bijPebbleWins_zero.2 h.partialIsoOn.symm
  | _ + 1, _, a, b, h => by
    refine bijPebbleWins_succ.2 ⟨h.partialIsoOn.symm, fun i => ?_⟩
    obtain ⟨f, hf⟩ := h.move i
    refine ⟨f.symm, fun d => ?_⟩
    have := (hf (f.symm d)).symm
    rwa [Equiv.apply_symm_apply] at this

theorem BijPebbleWins.trans :
    ∀ {n : ℕ} {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N} {c : Fin k → P},
      BijPebbleWins L n S a b → BijPebbleWins L n S b c → BijPebbleWins L n S a c
  | 0, _, _, _, _, h₁, h₂ => bijPebbleWins_zero.2 (h₁.partialIsoOn.trans h₂.partialIsoOn)
  | _ + 1, _, _, _, _, h₁, h₂ => by
    refine bijPebbleWins_succ.2 ⟨h₁.partialIsoOn.trans h₂.partialIsoOn, fun i => ?_⟩
    obtain ⟨f, hf⟩ := h₁.move i
    obtain ⟨g, hg⟩ := h₂.move i
    exact ⟨f.trans g, fun x => (hf x).trans (hg (f x))⟩

/-- **The bijective game is harder for Duplicator.** A winning position of the bijective game
wins the ordinary pebble game with the same number of rounds: Duplicator answers a move `c` in `M`
by `f c` and a move `d` in `N` by `f.symm d`. -/
theorem BijPebbleWins.pebbleWins :
    ∀ {n : ℕ} {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N},
      BijPebbleWins L n S a b → PebbleWins L n S a b
  | 0, _, _, _, h => pebbleWins_zero.2 h.partialIsoOn
  | _ + 1, _, _, b, h => by
    refine pebbleWins_succ.2 ⟨h.partialIsoOn, fun i c => ?_, fun i d => ?_⟩
    · obtain ⟨f, hf⟩ := h.move i
      exact ⟨f c, (hf c).pebbleWins⟩
    · obtain ⟨f, hf⟩ := h.move i
      refine ⟨f.symm d, ?_⟩
      have := (hf (f.symm d)).pebbleWins
      rwa [Equiv.apply_symm_apply] at this

/-! ### Back-and-forth invariants and the infinite game -/

variable (L) in
/-- A back-and-forth invariant for the bijective `k`-pebble game: a set of positions, each a
partial isomorphism on its placed pebbles, such that for every pebble index some bijection keeps
every move inside the set. -/
structure IsBijPebbleBackAndForth (I : Set (Fin k) → (Fin k → M) → (Fin k → N) → Prop) :
    Prop where
  /-- Every position of the invariant is a partial isomorphism on its placed pebbles. -/
  partialIsoOn : ∀ {S a b}, I S a b → PartialIsoOn L S a b
  /-- For every pebble index, some bijection keeps every move inside the invariant. -/
  move : ∀ {S a b}, I S a b → ∀ i, ∃ f : M ≃ N, ∀ c,
    I (insert i S) (Function.update a i c) (Function.update b i (f c))

/-- Every position of a back-and-forth invariant is won by Duplicator in every finite game. -/
theorem IsBijPebbleBackAndForth.bijPebbleWins
    {I : Set (Fin k) → (Fin k → M) → (Fin k → N) → Prop} (hI : IsBijPebbleBackAndForth L I) :
    ∀ {n : ℕ} {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N}, I S a b →
      BijPebbleWins L n S a b
  | 0, _, _, _, h => bijPebbleWins_zero.2 (hI.partialIsoOn h)
  | _ + 1, _, _, _, h => bijPebbleWins_succ.2 ⟨hI.partialIsoOn h,
      fun i => (hI.move h i).imp fun _ hf c => hI.bijPebbleWins (hf c)⟩

variable (L) in
/-- Duplicator wins the bijective `k`-pebble game that continues forever from `(S, a, b)`: the
position belongs to a back-and-forth invariant. As for `BijPebbleWins`, the statement is vacuous
for `k > 0` when `M` or `N` is empty. -/
def BijPebbleWinsForever (S : Set (Fin k)) (a : Fin k → M) (b : Fin k → N) : Prop :=
  ∃ I : Set (Fin k) → (Fin k → M) → (Fin k → N) → Prop, IsBijPebbleBackAndForth L I ∧ I S a b

/-- Every position of a back-and-forth invariant is won by Duplicator in the infinite game. -/
theorem IsBijPebbleBackAndForth.bijPebbleWinsForever
    {I : Set (Fin k) → (Fin k → M) → (Fin k → N) → Prop} (hI : IsBijPebbleBackAndForth L I)
    {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N} (h : I S a b) :
    BijPebbleWinsForever L S a b :=
  ⟨I, hI, h⟩

/-- Winning the infinite game implies winning every finite game. -/
theorem BijPebbleWinsForever.bijPebbleWins {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N}
    (h : BijPebbleWinsForever L S a b) (n : ℕ) : BijPebbleWins L n S a b :=
  let ⟨_, hI, hS⟩ := h
  hI.bijPebbleWins hS

/-- Winning the infinite bijective game implies winning the infinite pebble game. -/
theorem BijPebbleWinsForever.pebbleWinsForever {S : Set (Fin k)} {a : Fin k → M}
    {b : Fin k → N} (h : BijPebbleWinsForever L S a b) : PebbleWinsForever L S a b := by
  obtain ⟨I, hI, hS⟩ := h
  refine IsPebbleBackAndForth.pebbleWinsForever (I := I)
    ⟨hI.partialIsoOn, fun h i c => ?_, fun h i d => ?_⟩ hS
  · obtain ⟨f, hf⟩ := hI.move h i
    exact ⟨f c, hf c⟩
  · obtain ⟨f, hf⟩ := hI.move h i
    refine ⟨f.symm d, ?_⟩
    have := hf (f.symm d)
    rwa [Equiv.apply_symm_apply] at this

/-- **The infinite bijective game on finite structures.** When `M` is finite, Duplicator wins the
bijective `k`-pebble game that continues forever exactly when she wins the `n`-round game for every
`n`. Finiteness of `N` is not needed: there are only finitely many bijections `M ≃ N` either way. -/
theorem bijPebbleWinsForever_iff_forall_bijPebbleWins [Finite M] {S : Set (Fin k)}
    {a : Fin k → M} {b : Fin k → N} :
    BijPebbleWinsForever L S a b ↔ ∀ n, BijPebbleWins L n S a b := by
  refine ⟨BijPebbleWinsForever.bijPebbleWins, fun h => ⟨fun S a b => ∀ n, BijPebbleWins L n S a b,
    ⟨fun h => (h 0).partialIsoOn, fun {S a b} h i => ?_⟩, h⟩⟩
  obtain ⟨f, hf⟩ := (Finite.forall_exists_iff_exists_forall_of_antitone (p := fun (f : M ≃ N) n =>
      ∀ c, BijPebbleWins L n (insert i S) (Function.update a i c) (Function.update b i (f c)))
    fun _ _ _ hmn hf c => (hf c).mono hmn).1 fun n => (h (n + 1)).move i
  exact ⟨f, fun c n => hf n c⟩

/-- Duplicator wins the infinite bijective game between a structure and an isomorphic copy, from a
position and its image. -/
theorem _root_.FirstOrder.Language.Equiv.bijPebbleWinsForever (e : M ≃[L] N) (S : Set (Fin k))
    (a : Fin k → M) : BijPebbleWinsForever L S a (e ∘ a) := by
  refine ⟨fun _ a b => b = e ∘ a, ⟨?_, ?_⟩, rfl⟩
  · rintro S a b rfl
    refine ⟨fun i _ j _ => e.injective.eq_iff.symm, fun R f _ => ?_⟩
    rw [Function.comp_assoc, e.map_rel]
  · rintro S a b rfl i
    exact ⟨e.toEquiv, fun c => (Function.comp_update e a i c).symm⟩

/-- Duplicator wins every finite bijective game between a structure and an isomorphic copy, from a
position and its image. -/
theorem _root_.FirstOrder.Language.Equiv.bijPebbleWins (e : M ≃[L] N) (n : ℕ) (S : Set (Fin k))
    (a : Fin k → M) : BijPebbleWins L n S a (e ∘ a) :=
  (e.bijPebbleWinsForever S a).bijPebbleWins n

/-! ### The easy direction of the game characterization of `C^k` -/

/-- **Bijective pebble games, easy direction.** If Duplicator wins the `n`-round bijective
`k`-pebble game from `(S, a, b)`, then `a` and `b` satisfy the same `k`-variable counting formulas
of quantifier rank at most `n` whose free variables are placed pebbles. No finiteness assumption
is needed: the bijection of each round carries the witnesses of a counting quantifier in `M` onto
those in `N`. -/
theorem BijPebbleWins.realize_iff {n : ℕ} {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N}
    (h : BijPebbleWins L n S a b) {φ : FiniteVariable.CountingFormula L k}
    (hr : φ.quantifierRank ≤ n) (hS : ↑φ.freeVars ⊆ S) : φ.Realize a ↔ φ.Realize b := by
  induction φ generalizing n S a b with
  | falsum => simp only [FiniteVariable.CountingFormula.realize_falsum]
  | equal i j =>
    simp only [FiniteVariable.CountingFormula.freeVars_equal, Finset.coe_insert,
      Finset.coe_singleton, Set.insert_subset_iff, Set.singleton_subset_iff] at hS
    simp only [FiniteVariable.CountingFormula.realize_equal]
    exact h.partialIsoOn.eq_iff i hS.1 j hS.2
  | rel R f =>
    simp only [FiniteVariable.CountingFormula.realize_rel]
    exact h.partialIsoOn.relMap_iff R f fun t => hS (by simp)
  | imp φ ψ ihφ ihψ =>
    simp only [FiniteVariable.CountingFormula.quantifierRank_imp, max_le_iff] at hr
    simp only [FiniteVariable.CountingFormula.freeVars_imp, Finset.coe_union,
      Set.union_subset_iff] at hS
    simp only [FiniteVariable.CountingFormula.realize_imp]
    exact imp_congr (ihφ h hr.1 hS.1) (ihψ h hr.2 hS.2)
  | atLeast m i φ ih =>
    simp only [FiniteVariable.CountingFormula.quantifierRank_atLeast] at hr
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [FiniteVariable.CountingFormula.freeVars_atLeast, Finset.coe_erase, Set.sdiff_subset_iff,
      ← Set.insert_eq] at hS
    obtain ⟨f, hf⟩ := h.move i
    have himage : f '' {c | φ.Realize (Function.update a i c)} =
        {d | φ.Realize (Function.update b i d)} := by
      ext d
      constructor
      · rintro ⟨c, hc, rfl⟩
        exact (ih (hf c) (by omega) hS).1 hc
      · intro hd
        refine ⟨f.symm d, (ih (hf (f.symm d)) (by omega) hS).2 ?_, f.apply_symm_apply d⟩
        rwa [f.apply_symm_apply]
    rw [FiniteVariable.CountingFormula.realize_atLeast,
      FiniteVariable.CountingFormula.realize_atLeast, ← himage, f.injective.encard_image]

/-- **Infinite bijective pebble games, easy direction.** If Duplicator wins the infinite bijective
`k`-pebble game from `(S, a, b)`, then `a` and `b` satisfy the same `k`-variable counting formulas
whose free variables are placed pebbles. -/
theorem BijPebbleWinsForever.realize_iff {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N}
    (h : BijPebbleWinsForever L S a b) {φ : FiniteVariable.CountingFormula L k}
    (hS : ↑φ.freeVars ⊆ S) : φ.Realize a ↔ φ.Realize b :=
  (h.bijPebbleWins _).realize_iff le_rfl hS

end Cslib.Logic.FO
