/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.FiniteVariable.Basic

/-!
# Pebble games

The `k`-pebble game on two `L`-structures `M` and `N` is played with `k` pairs of pebbles. In each
round Spoiler picks a pebble index `i`, places the `M`-pebble or the `N`-pebble of pair `i` on an
element of that structure (lifting it first if it was already placed), and Duplicator places the
other pebble of pair `i` in the other structure. Duplicator wins a play when, after every round,
the placed pairs define a partial isomorphism. Unlike the Ehrenfeucht–Fraïssé game, pebbles are
reused, and the game may continue for any number of rounds, even forever.

A position is a set `S : Set (Fin k)` of placed pebble indices together with assignments
`a : Fin k → M` and `b : Fin k → N`; only the values on `S` matter (`pebbleWins_congr`). Moving
pebble `i` to `c` and `d` gives the position `(insert i S, update a i c, update b i d)`. These are
exactly the assignments of the `k`-variable formulas of
`CslibFrontier.Logics.FirstOrder.FiniteVariable.Basic`, whose quantifier `all i` updates
variable `i`.

`PebbleWins L n S a b` says that Duplicator wins the `n`-round game from the position, and
`PebbleWinsForever L S a b` that she wins the game that continues forever, witnessed by a
back-and-forth invariant. `PebbleWins.realize_iff` is the easy direction of the pebble-game
characterization of `FO^k`: a winning position satisfies the same `k`-variable formulas of
quantifier rank at most `n` whose free variables are placed. The converse needs finitely many
relation symbols and is proved in `CslibFrontier.Logics.FirstOrder.FiniteVariable.Hintikka`.

## Main definitions

* `Cslib.Logic.FO.PartialIsoOn`: the pebbles in `S` define a partial isomorphism.
* `Cslib.Logic.FO.PebbleWins`: Duplicator wins the `n`-round `k`-pebble game from a position.
* `Cslib.Logic.FO.IsPebbleBackAndForth`: invariants that Duplicator can maintain forever.
* `Cslib.Logic.FO.PebbleWinsForever`: Duplicator wins the infinite `k`-pebble game.

## Main results

* `Cslib.Logic.FO.PebbleWins.mono`, `Cslib.Logic.FO.PebbleWins.of_subset`,
  `Cslib.Logic.FO.pebbleWins_congr`: monotonicity in the number of rounds and in the placed
  pebbles, and independence of unplaced pebbles.
* `Cslib.Logic.FO.PebbleWins.refl`, `Cslib.Logic.FO.PebbleWins.symm`,
  `Cslib.Logic.FO.PebbleWins.trans`, `FirstOrder.Language.Equiv.pebbleWins`: the
  equivalence-relation laws and invariance under isomorphism.
* `Cslib.Logic.FO.IsPebbleBackAndForth.pebbleWinsForever`: a back-and-forth invariant wins the
  infinite game.
* `Cslib.Logic.FO.PebbleWinsForever.pebbleWins`,
  `Cslib.Logic.FO.pebbleWinsForever_iff_forall_pebbleWins`: the infinite game is won exactly when
  every finite game is, on finite structures.
* `Cslib.Logic.FO.PebbleWins.realize_iff`, `Cslib.Logic.FO.PebbleWinsForever.realize_iff`: the
  easy direction of the pebble-game characterization of `FO^k`.

## References

* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004], Section 11.2, Definition 11.4
  and the remark before Proposition 11.8.
* [N. Immerman, *Descriptive Complexity*][Immerman1999], Definition 6.2.
-/

public section

universe u v w w' w''

open FirstOrder Language Structure

namespace Cslib.Logic.FO

variable {L : Language.{u, v}} {M : Type w} {N : Type w'} {P : Type w''}
  [L.Structure M] [L.Structure N] [L.Structure P] {k : ℕ}

/-! ### Partial isomorphisms on placed pebbles -/

variable (L) in
/-- The pebbles with indices in `S` define a partial isomorphism `a i ↦ b i`: the map is well
defined and injective, and it preserves and reflects every relation among placed pebbles. -/
structure PartialIsoOn (S : Set (Fin k)) (a : Fin k → M) (b : Fin k → N) : Prop where
  /-- Two placed pebbles coincide in `M` exactly when they coincide in `N`. -/
  eq_iff : ∀ i ∈ S, ∀ j ∈ S, a i = a j ↔ b i = b j
  /-- Every relation holds of placed pebbles in `M` exactly when it holds of them in `N`. -/
  relMap_iff : ∀ {l} (R : L.Relations l) (f : Fin l → Fin k), (∀ t, f t ∈ S) →
    (RelMap R (a ∘ f) ↔ RelMap R (b ∘ f))

theorem PartialIsoOn.refl (S : Set (Fin k)) (a : Fin k → M) : PartialIsoOn L S a a :=
  ⟨fun _ _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl⟩

theorem PartialIsoOn.symm {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N}
    (h : PartialIsoOn L S a b) : PartialIsoOn L S b a :=
  ⟨fun i hi j hj => (h.eq_iff i hi j hj).symm, fun R f hf => (h.relMap_iff R f hf).symm⟩

theorem PartialIsoOn.trans {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N} {c : Fin k → P}
    (h₁ : PartialIsoOn L S a b) (h₂ : PartialIsoOn L S b c) : PartialIsoOn L S a c :=
  ⟨fun i hi j hj => (h₁.eq_iff i hi j hj).trans (h₂.eq_iff i hi j hj),
    fun R f hf => (h₁.relMap_iff R f hf).trans (h₂.relMap_iff R f hf)⟩

theorem PartialIsoOn.mono {S T : Set (Fin k)} {a : Fin k → M} {b : Fin k → N} (hST : S ⊆ T)
    (h : PartialIsoOn L T a b) : PartialIsoOn L S a b :=
  ⟨fun i hi j hj => h.eq_iff i (hST hi) j (hST hj),
    fun R f hf => h.relMap_iff R f fun t => hST (hf t)⟩

/-- A partial isomorphism on `S` depends only on the values of the pebbles in `S`. -/
theorem PartialIsoOn.congr {S : Set (Fin k)} {a a' : Fin k → M} {b b' : Fin k → N}
    (ha : Set.EqOn a a' S) (hb : Set.EqOn b b' S) (h : PartialIsoOn L S a b) :
    PartialIsoOn L S a' b' := by
  refine ⟨fun i hi j hj => ?_, fun R f hf => ?_⟩
  · rw [← ha hi, ← ha hj, ← hb hi, ← hb hj]
    exact h.eq_iff i hi j hj
  · have ha' : a' ∘ f = a ∘ f := funext fun t => (ha (hf t)).symm
    have hb' : b' ∘ f = b ∘ f := funext fun t => (hb (hf t)).symm
    rw [ha', hb']
    exact h.relMap_iff R f hf

/-- With no pebbles placed, every position is a partial isomorphism, provided `L` has no nullary
relation symbols: these are sentences that the two structures would have to agree on. -/
theorem partialIsoOn_empty [IsEmpty (L.Relations 0)] (a : Fin k → M) (b : Fin k → N) :
    PartialIsoOn L ∅ a b := by
  refine ⟨fun _ hi => absurd hi (Set.notMem_empty _), fun {l} R f hf => ?_⟩
  cases l with
  | zero => exact isEmptyElim R
  | succ l => exact absurd (hf 0) (Set.notMem_empty _)

/-! ### The game -/

variable (L) in
/-- Duplicator wins the `n`-round `k`-pebble game from the position `(S, a, b)`, where `S` is the
set of placed pebble indices and `a`, `b` give their positions in `M` and `N`: the placed pebbles
define a partial isomorphism and, if a round remains, for every pebble index `i` and every
placement of the `M`-pebble (or `N`-pebble) of pair `i`, Duplicator can place the other pebble of
pair `i` so that she wins the remaining rounds.

The values of `a` and `b` outside `S` do not matter (`pebbleWins_congr`). Since positions are
total assignments `Fin k → M` and `Fin k → N`, a position exists only when `k = 0` or both
structures are nonempty: for `k > 0` and empty `M` or `N` the statement is vacuous, and results
about games starting with no pebbles placed (`S = ∅`) say nothing about empty structures. -/
def PebbleWins : ℕ → Set (Fin k) → (Fin k → M) → (Fin k → N) → Prop
  | 0, S, a, b => PartialIsoOn L S a b
  | n + 1, S, a, b => PartialIsoOn L S a b ∧
      (∀ i (c : M), ∃ d : N,
        PebbleWins n (insert i S) (Function.update a i c) (Function.update b i d)) ∧
      (∀ i (d : N), ∃ c : M,
        PebbleWins n (insert i S) (Function.update a i c) (Function.update b i d))

theorem pebbleWins_zero {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N} :
    PebbleWins L 0 S a b ↔ PartialIsoOn L S a b := by
  rw [PebbleWins]

theorem pebbleWins_succ {n : ℕ} {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N} :
    PebbleWins L (n + 1) S a b ↔ PartialIsoOn L S a b ∧
      (∀ i (c : M), ∃ d : N,
        PebbleWins L n (insert i S) (Function.update a i c) (Function.update b i d)) ∧
      (∀ i (d : N), ∃ c : M,
        PebbleWins L n (insert i S) (Function.update a i c) (Function.update b i d)) := by
  rw [PebbleWins]

theorem PebbleWins.partialIsoOn {n : ℕ} {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N}
    (h : PebbleWins L n S a b) : PartialIsoOn L S a b := by
  cases n with
  | zero => exact pebbleWins_zero.1 h
  | succ n => exact (pebbleWins_succ.1 h).1

theorem PebbleWins.forth {n : ℕ} {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N}
    (h : PebbleWins L (n + 1) S a b) (i : Fin k) (c : M) :
    ∃ d : N, PebbleWins L n (insert i S) (Function.update a i c) (Function.update b i d) :=
  (pebbleWins_succ.1 h).2.1 i c

theorem PebbleWins.back {n : ℕ} {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N}
    (h : PebbleWins L (n + 1) S a b) (i : Fin k) (d : N) :
    ∃ c : M, PebbleWins L n (insert i S) (Function.update a i c) (Function.update b i d) :=
  (pebbleWins_succ.1 h).2.2 i d

/-! ### Basic properties of the game -/

/-- Winning a game implies winning every shorter game. -/
theorem PebbleWins.mono : ∀ {m n : ℕ} {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N},
    m ≤ n → PebbleWins L n S a b → PebbleWins L m S a b
  | 0, _, _, _, _, _, h => pebbleWins_zero.2 h.partialIsoOn
  | _ + 1, _ + 1, _, _, _, hmn, h => pebbleWins_succ.2 ⟨h.partialIsoOn,
      fun i c => (h.forth i c).imp fun _ hd => hd.mono (by omega),
      fun i d => (h.back i d).imp fun _ hc => hc.mono (by omega)⟩
  | _ + 1, 0, _, _, _, hmn, _ => absurd hmn (by omega)

/-- Lifting placed pebbles keeps the position winning. -/
theorem PebbleWins.of_subset : ∀ {n : ℕ} {S T : Set (Fin k)} {a : Fin k → M} {b : Fin k → N},
    S ⊆ T → PebbleWins L n T a b → PebbleWins L n S a b
  | 0, _, _, _, _, hST, h => pebbleWins_zero.2 (h.partialIsoOn.mono hST)
  | _ + 1, _, _, _, _, hST, h => pebbleWins_succ.2 ⟨h.partialIsoOn.mono hST,
      fun i c => (h.forth i c).imp fun _ hd => hd.of_subset (Set.insert_subset_insert hST),
      fun i d => (h.back i d).imp fun _ hc => hc.of_subset (Set.insert_subset_insert hST)⟩

private theorem eqOn_update_insert {α : Type*} {S : Set (Fin k)} {a a' : Fin k → α}
    (h : Set.EqOn a a' S) (i : Fin k) (c : α) :
    Set.EqOn (Function.update a i c) (Function.update a' i c) (insert i S) := by
  intro j hj
  by_cases hji : j = i
  · subst hji
    simp only [Function.update_self]
  · rw [Function.update_of_ne hji, Function.update_of_ne hji]
    exact h ((Set.mem_insert_iff.1 hj).resolve_left hji)

/-- Winning depends only on the positions of the placed pebbles. -/
theorem pebbleWins_congr : ∀ {n : ℕ} {S : Set (Fin k)} {a a' : Fin k → M} {b b' : Fin k → N},
    Set.EqOn a a' S → Set.EqOn b b' S → PebbleWins L n S a b → PebbleWins L n S a' b'
  | 0, _, _, _, _, _, ha, hb, h => pebbleWins_zero.2 (h.partialIsoOn.congr ha hb)
  | _ + 1, _, _, _, _, _, ha, hb, h => pebbleWins_succ.2 ⟨h.partialIsoOn.congr ha hb,
      fun i c => (h.forth i c).imp fun d hd =>
        pebbleWins_congr (eqOn_update_insert ha i c) (eqOn_update_insert hb i d) hd,
      fun i d => (h.back i d).imp fun c hc =>
        pebbleWins_congr (eqOn_update_insert ha i c) (eqOn_update_insert hb i d) hc⟩

theorem PebbleWins.refl :
    ∀ (n : ℕ) (S : Set (Fin k)) (a : Fin k → M), PebbleWins L n S a a
  | 0, S, a => pebbleWins_zero.2 (PartialIsoOn.refl S a)
  | n + 1, S, a => pebbleWins_succ.2 ⟨PartialIsoOn.refl S a,
      fun _ c => ⟨c, PebbleWins.refl n _ _⟩, fun _ d => ⟨d, PebbleWins.refl n _ _⟩⟩

theorem PebbleWins.symm : ∀ {n : ℕ} {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N},
    PebbleWins L n S a b → PebbleWins L n S b a
  | 0, _, _, _, h => pebbleWins_zero.2 h.partialIsoOn.symm
  | _ + 1, _, _, _, h => pebbleWins_succ.2 ⟨h.partialIsoOn.symm,
      fun i d => (h.back i d).imp fun _ hc => hc.symm,
      fun i c => (h.forth i c).imp fun _ hd => hd.symm⟩

theorem PebbleWins.trans :
    ∀ {n : ℕ} {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N} {c : Fin k → P},
      PebbleWins L n S a b → PebbleWins L n S b c → PebbleWins L n S a c
  | 0, _, _, _, _, h₁, h₂ => pebbleWins_zero.2 (h₁.partialIsoOn.trans h₂.partialIsoOn)
  | _ + 1, _, _, _, _, h₁, h₂ => by
    refine pebbleWins_succ.2 ⟨h₁.partialIsoOn.trans h₂.partialIsoOn, fun i x => ?_, fun i z => ?_⟩
    · obtain ⟨y, hy⟩ := h₁.forth i x
      obtain ⟨z, hz⟩ := h₂.forth i y
      exact ⟨z, hy.trans hz⟩
    · obtain ⟨y, hy⟩ := h₂.back i z
      obtain ⟨x, hx⟩ := h₁.back i y
      exact ⟨x, hx.trans hy⟩

/-! ### Back-and-forth invariants and the infinite game -/

variable (L) in
/-- A back-and-forth invariant for the `k`-pebble game: a set of positions, each a partial
isomorphism on its placed pebbles, such that every move of Spoiler from a position in the set has
an answer leading back into the set. -/
structure IsPebbleBackAndForth (I : Set (Fin k) → (Fin k → M) → (Fin k → N) → Prop) : Prop where
  /-- Every position of the invariant is a partial isomorphism on its placed pebbles. -/
  partialIsoOn : ∀ {S a b}, I S a b → PartialIsoOn L S a b
  /-- Every move of Spoiler in `M` has an answer in `N` staying in the invariant. -/
  forth : ∀ {S a b}, I S a b → ∀ i (c : M), ∃ d : N,
    I (insert i S) (Function.update a i c) (Function.update b i d)
  /-- Every move of Spoiler in `N` has an answer in `M` staying in the invariant. -/
  back : ∀ {S a b}, I S a b → ∀ i (d : N), ∃ c : M,
    I (insert i S) (Function.update a i c) (Function.update b i d)

/-- Every position of a back-and-forth invariant is won by Duplicator in every finite game. -/
theorem IsPebbleBackAndForth.pebbleWins {I : Set (Fin k) → (Fin k → M) → (Fin k → N) → Prop}
    (hI : IsPebbleBackAndForth L I) :
    ∀ {n : ℕ} {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N}, I S a b → PebbleWins L n S a b
  | 0, _, _, _, h => pebbleWins_zero.2 (hI.partialIsoOn h)
  | _ + 1, _, _, _, h => pebbleWins_succ.2 ⟨hI.partialIsoOn h,
      fun i c => (hI.forth h i c).imp fun _ hd => hI.pebbleWins hd,
      fun i d => (hI.back h i d).imp fun _ hc => hI.pebbleWins hc⟩

variable (L) in
/-- Duplicator wins the `k`-pebble game that continues forever from the position `(S, a, b)`:
the position belongs to a back-and-forth invariant. As for `PebbleWins`, the statement is vacuous
for `k > 0` when `M` or `N` is empty. -/
def PebbleWinsForever (S : Set (Fin k)) (a : Fin k → M) (b : Fin k → N) : Prop :=
  ∃ I : Set (Fin k) → (Fin k → M) → (Fin k → N) → Prop, IsPebbleBackAndForth L I ∧ I S a b

/-- Every position of a back-and-forth invariant is won by Duplicator in the infinite game. -/
theorem IsPebbleBackAndForth.pebbleWinsForever
    {I : Set (Fin k) → (Fin k → M) → (Fin k → N) → Prop} (hI : IsPebbleBackAndForth L I)
    {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N} (h : I S a b) :
    PebbleWinsForever L S a b :=
  ⟨I, hI, h⟩

/-- Winning the infinite game implies winning every finite game. -/
theorem PebbleWinsForever.pebbleWins {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N}
    (h : PebbleWinsForever L S a b) (n : ℕ) : PebbleWins L n S a b :=
  let ⟨_, hI, hS⟩ := h
  hI.pebbleWins hS

/-- If, for each `n`, some answer `d` from a finite type wins the `n`-th of a sequence of games
that gets harder with `n`, then a single answer wins all of them. -/
private theorem exists_forall_of_forall_exists [Finite N] {p : ℕ → N → Prop}
    (hp : ∀ {m n : ℕ} {d : N}, m ≤ n → p n d → p m d) (h : ∀ n, ∃ d, p n d) : ∃ d, ∀ n, p n d := by
  have := Fintype.ofFinite N
  by_contra hne
  simp only [not_exists, not_forall] at hne
  choose f hf using hne
  obtain ⟨d, hd⟩ := h (Finset.univ.sup f)
  exact hf d (hp (Finset.le_sup (Finset.mem_univ d)) hd)

/-- **The infinite pebble game on finite structures.** On finite structures, Duplicator wins the
`k`-pebble game that continues forever exactly when she wins the `n`-round game for every `n`
[Libkin2004] (remark before Proposition 11.8). On infinite structures only the forward
implication holds in general. -/
theorem pebbleWinsForever_iff_forall_pebbleWins [Finite M] [Finite N] {S : Set (Fin k)}
    {a : Fin k → M} {b : Fin k → N} : PebbleWinsForever L S a b ↔ ∀ n, PebbleWins L n S a b := by
  refine ⟨PebbleWinsForever.pebbleWins, fun h => ⟨fun S a b => ∀ n, PebbleWins L n S a b,
    ⟨fun h => (h 0).partialIsoOn, fun h i c => ?_, fun h i d => ?_⟩, h⟩⟩
  · exact exists_forall_of_forall_exists (fun hmn hd => hd.mono hmn)
      fun n => (h (n + 1)).forth i c
  · exact exists_forall_of_forall_exists (fun hmn hc => hc.mono hmn)
      fun n => (h (n + 1)).back i d

/-- Duplicator wins the infinite game between a structure and an isomorphic copy, from a position
and its image. -/
theorem _root_.FirstOrder.Language.Equiv.pebbleWinsForever (e : M ≃[L] N) (S : Set (Fin k))
    (a : Fin k → M) : PebbleWinsForever L S a (e ∘ a) := by
  refine ⟨fun _ a b => b = e ∘ a, ⟨?_, ?_, ?_⟩, rfl⟩
  · rintro S a b rfl
    refine ⟨fun i _ j _ => e.injective.eq_iff.symm, fun R f _ => ?_⟩
    rw [Function.comp_assoc, e.map_rel]
  · rintro S a b rfl i c
    exact ⟨e c, (Function.comp_update e a i c).symm⟩
  · rintro S a b rfl i d
    exact ⟨e.symm d, by rw [Function.comp_update, e.apply_symm_apply]⟩

/-- Duplicator wins every finite game between a structure and an isomorphic copy, from a position
and its image. -/
theorem _root_.FirstOrder.Language.Equiv.pebbleWins (e : M ≃[L] N) (n : ℕ) (S : Set (Fin k))
    (a : Fin k → M) : PebbleWins L n S a (e ∘ a) :=
  (e.pebbleWinsForever S a).pebbleWins n

/-! ### The easy direction of the pebble-game characterization of `FO^k` -/

/-- **Pebble games, easy direction.** If Duplicator wins the `n`-round `k`-pebble game from
`(S, a, b)`, then `a` and `b` satisfy the same `k`-variable formulas of quantifier rank at most `n`
whose free variables are placed pebbles. No finiteness assumption is needed. -/
theorem PebbleWins.realize_iff {n : ℕ} {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N}
    (h : PebbleWins L n S a b) {φ : FiniteVariable.Formula L k} (hr : φ.quantifierRank ≤ n)
    (hS : ↑φ.freeVars ⊆ S) : φ.Realize a ↔ φ.Realize b := by
  induction φ generalizing n S a b with
  | falsum => simp only [FiniteVariable.Formula.realize_falsum]
  | equal i j =>
    simp only [FiniteVariable.Formula.freeVars_equal, Finset.coe_insert, Finset.coe_singleton,
      Set.insert_subset_iff, Set.singleton_subset_iff] at hS
    simp only [FiniteVariable.Formula.realize_equal]
    exact h.partialIsoOn.eq_iff i hS.1 j hS.2
  | rel R f =>
    simp only [FiniteVariable.Formula.realize_rel]
    exact h.partialIsoOn.relMap_iff R f fun t => hS (by simp)
  | imp φ ψ ihφ ihψ =>
    simp only [FiniteVariable.Formula.quantifierRank_imp, max_le_iff] at hr
    simp only [FiniteVariable.Formula.freeVars_imp, Finset.coe_union, Set.union_subset_iff] at hS
    simp only [FiniteVariable.Formula.realize_imp]
    exact imp_congr (ihφ h hr.1 hS.1) (ihψ h hr.2 hS.2)
  | all i φ ih =>
    simp only [FiniteVariable.Formula.quantifierRank_all] at hr
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [FiniteVariable.Formula.freeVars_all, Finset.coe_erase, Set.sdiff_subset_iff,
      ← Set.insert_eq] at hS
    simp only [FiniteVariable.Formula.realize_all]
    constructor
    · intro hA d
      obtain ⟨c, hc⟩ := h.back i d
      exact (ih hc (by omega) hS).1 (hA c)
    · intro hB c
      obtain ⟨d, hd⟩ := h.forth i c
      exact (ih hd (by omega) hS).2 (hB d)

/-- **Infinite pebble games, easy direction.** If Duplicator wins the infinite `k`-pebble game
from `(S, a, b)`, then `a` and `b` satisfy the same `k`-variable formulas whose free variables are
placed pebbles. -/
theorem PebbleWinsForever.realize_iff {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N}
    (h : PebbleWinsForever L S a b) {φ : FiniteVariable.Formula L k} (hS : ↑φ.freeVars ⊆ S) :
    φ.Realize a ↔ φ.Realize b :=
  (h.pebbleWins _).realize_iff le_rfl hS

end Cslib.Logic.FO
