/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.QuantifierRank
public import Mathlib.ModelTheory.Semantics
import Complexity.Logics.FirstOrder.Interpretation

/-!
# Ehrenfeucht–Fraïssé games

The `n`-round Ehrenfeucht–Fraïssé game on two `L`-structures `M` and `N` starts from a position: a
`k`-tuple `a` of pebbled elements of `M` and a `k`-tuple `b` of `N`. In each round Spoiler picks an
element of one structure and Duplicator answers with an element of the other; the chosen pair
is appended to the position. Duplicator wins a play when every position reached, the initial one
included, is a partial isomorphism: the map `a i ↦ b i` is well defined, injective, and preserves
and reflects every relation of `L`.

`DuplicatorWins L n a b` is the recursive characterization of the positions from which Duplicator
has a winning strategy in the `n`-round game; `duplicatorWins_iff_exists_strategy` relates it to
explicit strategies, and `IsBackAndForth.duplicatorWins` to back-and-forth systems, the usual
way to construct winning strategies. The game is defined for arbitrary languages and structures.
For relational languages, `DuplicatorWins.realize_iff` is the easy direction of the
Ehrenfeucht–Fraïssé theorem: a winning position satisfies the same formulas of quantifier rank at
most `n`. The converse needs a finite relational vocabulary and is proved in
`Complexity.Logics.FirstOrder.EhrenfeuchtFraisse.Hintikka`.

The pebbles are recorded as tuples `Fin k → M`, which `Fin.snoc` extends; these are the variable
assignments of Mathlib's `BoundedFormula` with `k` bound variables and no free variables, so the
game positions match the semantics of formulas without translation. Constants and function
symbols are not handled by the game: positions do not close under terms, so the easy direction
assumes `L.IsRelational`.

## Main definitions

* `Cslib.Logic.FO.PartialIso`: the pebbled tuples define a partial isomorphism.
* `Cslib.Logic.FO.DuplicatorWins`: Duplicator wins the `n`-round game from a position.
* `Cslib.Logic.FO.Strategy`, `Cslib.Logic.FO.Strategy.IsWinning`: Duplicator strategies and
  winning strategies. Both bodies are exposed, so clients can build strategies by recursion and
  check them with `Strategy.isWinning_zero` and `Strategy.isWinning_succ`.
* `Cslib.Logic.FO.IsBackAndForth`: back-and-forth systems indexed by the number of rounds left.

## Main results

* `Cslib.Logic.FO.duplicatorWins_iff_exists_strategy`: Duplicator wins exactly when she has a
  winning strategy.
* `Cslib.Logic.FO.IsBackAndForth.duplicatorWins`,
  `Cslib.Logic.FO.isBackAndForth_duplicatorWins`: back-and-forth systems consist of winning
  positions, and the winning positions form the largest one.
* `Cslib.Logic.FO.DuplicatorWins.mono`, `Cslib.Logic.FO.DuplicatorWins.refl`,
  `Cslib.Logic.FO.DuplicatorWins.symm`, `Cslib.Logic.FO.DuplicatorWins.trans`,
  `FirstOrder.Language.Equiv.duplicatorWins`: monotonicity in the number of rounds, the
  equivalence-relation laws and invariance under isomorphism.
* `Cslib.Logic.FO.DuplicatorWins.realize_iff`: **Ehrenfeucht–Fraïssé, easy direction**.

## References

* [A. Ehrenfeucht, *An application of games to the completeness problem for formalized
  theories*][Ehrenfeucht1961]
* [R. Fraïssé, *Sur quelques classifications des systèmes de relations*][Fraisse1954]
* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004], Chapter 3.
* [H.-D. Ebbinghaus and J. Flum, *Finite Model Theory*][EbbinghausFlum1999], Chapter 2.
-/

public section

universe u v w w' w''

open FirstOrder Language Structure

namespace Cslib.Logic.FO

variable {L : Language.{u, v}} {M : Type w} {N : Type w'} {P : Type w''}
  [L.Structure M] [L.Structure N] [L.Structure P]

/-! ### Partial isomorphisms -/

variable (L) in
/-- The pebbled tuples `a` and `b` define a partial isomorphism `a i ↦ b i`: the map is
well defined and injective, and it preserves and reflects every relation. -/
structure PartialIso {k : ℕ} (a : Fin k → M) (b : Fin k → N) : Prop where
  /-- Two pebbles coincide in `M` exactly when they coincide in `N`. -/
  eq_iff : ∀ i j, a i = a j ↔ b i = b j
  /-- Every relation holds of the pebbles in `M` exactly when it holds of them in `N`. -/
  relMap_iff : ∀ {l} (R : L.Relations l) (f : Fin l → Fin k), RelMap R (a ∘ f) ↔ RelMap R (b ∘ f)

theorem PartialIso.refl {k : ℕ} (a : Fin k → M) : PartialIso L a a :=
  ⟨fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩

theorem PartialIso.symm {k : ℕ} {a : Fin k → M} {b : Fin k → N} (h : PartialIso L a b) :
    PartialIso L b a :=
  ⟨fun i j => (h.eq_iff i j).symm, fun R f => (h.relMap_iff R f).symm⟩

theorem PartialIso.trans {k : ℕ} {a : Fin k → M} {b : Fin k → N} {c : Fin k → P}
    (h₁ : PartialIso L a b) (h₂ : PartialIso L b c) : PartialIso L a c :=
  ⟨fun i j => (h₁.eq_iff i j).trans (h₂.eq_iff i j),
    fun R f => (h₁.relMap_iff R f).trans (h₂.relMap_iff R f)⟩

/-! ### The game -/

variable (L) in
/-- Duplicator wins the `n`-round Ehrenfeucht–Fraïssé game from the position `(a, b)`: the
position is a partial isomorphism and, if a round remains, every move of Spoiler in either
structure has an answer from which Duplicator wins the remaining rounds. -/
def DuplicatorWins : ℕ → ∀ {k : ℕ}, (Fin k → M) → (Fin k → N) → Prop
  | 0, _, a, b => PartialIso L a b
  | n + 1, _, a, b => PartialIso L a b ∧
      (∀ c : M, ∃ d : N, DuplicatorWins n (Fin.snoc a c : Fin _ → M) (Fin.snoc b d : Fin _ → N)) ∧
      (∀ d : N, ∃ c : M, DuplicatorWins n (Fin.snoc a c : Fin _ → M) (Fin.snoc b d : Fin _ → N))

theorem duplicatorWins_zero {k : ℕ} {a : Fin k → M} {b : Fin k → N} :
    DuplicatorWins L 0 a b ↔ PartialIso L a b := by
  rw [DuplicatorWins]

theorem duplicatorWins_succ {n k : ℕ} {a : Fin k → M} {b : Fin k → N} :
    DuplicatorWins L (n + 1) a b ↔ PartialIso L a b ∧
      (∀ c : M, ∃ d : N,
        DuplicatorWins L n (Fin.snoc a c : Fin _ → M) (Fin.snoc b d : Fin _ → N)) ∧
      (∀ d : N, ∃ c : M,
        DuplicatorWins L n (Fin.snoc a c : Fin _ → M) (Fin.snoc b d : Fin _ → N)) := by
  rw [DuplicatorWins]

theorem DuplicatorWins.partialIso {n k : ℕ} {a : Fin k → M} {b : Fin k → N}
    (h : DuplicatorWins L n a b) : PartialIso L a b := by
  cases n with
  | zero => exact duplicatorWins_zero.1 h
  | succ n => exact (duplicatorWins_succ.1 h).1

theorem DuplicatorWins.forth {n k : ℕ} {a : Fin k → M} {b : Fin k → N}
    (h : DuplicatorWins L (n + 1) a b) (c : M) :
    ∃ d : N, DuplicatorWins L n (Fin.snoc a c : Fin _ → M) (Fin.snoc b d : Fin _ → N) :=
  (duplicatorWins_succ.1 h).2.1 c

theorem DuplicatorWins.back {n k : ℕ} {a : Fin k → M} {b : Fin k → N}
    (h : DuplicatorWins L (n + 1) a b) (d : N) :
    ∃ c : M, DuplicatorWins L n (Fin.snoc a c : Fin _ → M) (Fin.snoc b d : Fin _ → N) :=
  (duplicatorWins_succ.1 h).2.2 d

/-! ### Strategies -/

/-- A Duplicator strategy for the `n`-round game from the position `(a, b)`: for every move of
Spoiler, an answer in the other structure together with a strategy for the remaining rounds.
The body is exposed: clients build strategies and read off their answers. -/
@[expose] def Strategy : ℕ → ∀ {k : ℕ}, (Fin k → M) → (Fin k → N) → Type (max w w')
  | 0, _, _, _ => PUnit
  | n + 1, _, a, b =>
    (∀ c : M, Σ d : N, Strategy n (Fin.snoc a c : Fin _ → M) (Fin.snoc b d : Fin _ → N)) ×
      (∀ d : N, Σ c : M, Strategy n (Fin.snoc a c : Fin _ → M) (Fin.snoc b d : Fin _ → N))

/-- A strategy is winning when every position reached in a play following it, including the
initial one, is a partial isomorphism. The body is exposed so that clients can check that a
concrete strategy wins. -/
@[expose] def Strategy.IsWinning (L : Language.{u, v}) [L.Structure M] [L.Structure N] :
    ∀ {n k : ℕ} {a : Fin k → M} {b : Fin k → N}, Strategy n a b → Prop
  | 0, _, a, b, _ => PartialIso L a b
  | _ + 1, _, a, b, σ => PartialIso L a b ∧
      (∀ c, (σ.1 c).2.IsWinning L) ∧ ∀ d, (σ.2 d).2.IsWinning L

@[simp]
theorem Strategy.isWinning_zero {k : ℕ} {a : Fin k → M} {b : Fin k → N} (σ : Strategy 0 a b) :
    σ.IsWinning L ↔ PartialIso L a b := by
  rw [Strategy.IsWinning]

@[simp]
theorem Strategy.isWinning_succ {n k : ℕ} {a : Fin k → M} {b : Fin k → N}
    (σ : Strategy (n + 1) a b) :
    σ.IsWinning L ↔ PartialIso L a b ∧ (∀ c, (σ.1 c).2.IsWinning L) ∧
      ∀ d, (σ.2 d).2.IsWinning L := by
  rw [Strategy.IsWinning]

/-- Duplicator wins the `n`-round game exactly when she has a winning strategy. -/
theorem duplicatorWins_iff_exists_strategy :
    ∀ {n k : ℕ} {a : Fin k → M} {b : Fin k → N},
      DuplicatorWins L n a b ↔ ∃ σ : Strategy n a b, σ.IsWinning L
  | 0, _, _, _ => by
    rw [duplicatorWins_zero]
    exact ⟨fun h => ⟨PUnit.unit, h⟩, fun ⟨_, h⟩ => h⟩
  | n + 1, k, a, b => by
    rw [duplicatorWins_succ]
    constructor
    · rintro ⟨hp, hf, hb⟩
      choose d hd using fun c => duplicatorWins_iff_exists_strategy.1 (hf c).choose_spec
      choose c hc using fun d => duplicatorWins_iff_exists_strategy.1 (hb d).choose_spec
      exact ⟨(fun c' => ⟨_, d c'⟩, fun d' => ⟨_, c d'⟩), hp, hd, hc⟩
    · rintro ⟨σ, hp, hf, hb⟩
      exact ⟨hp, fun c => ⟨_, duplicatorWins_iff_exists_strategy.2 ⟨_, hf c⟩⟩,
        fun d => ⟨_, duplicatorWins_iff_exists_strategy.2 ⟨_, hb d⟩⟩⟩

/-! ### Back-and-forth systems -/

variable (L) in
/-- A back-and-forth system: a family `I j` of sets of positions, `j` being the number of rounds
still to play, each consisting of partial isomorphisms, such that every position of `I (j + 1)`
can be extended, for every move of Spoiler, to a position of `I j`. -/
structure IsBackAndForth (I : ℕ → ∀ {k : ℕ}, (Fin k → M) → (Fin k → N) → Prop) : Prop where
  /-- Every position of the system is a partial isomorphism. -/
  partialIso : ∀ {j k : ℕ} {a : Fin k → M} {b : Fin k → N}, I j a b → PartialIso L a b
  /-- Every move of Spoiler in `M` has an answer in `N` staying in the system. -/
  forth : ∀ {j k : ℕ} {a : Fin k → M} {b : Fin k → N}, I (j + 1) a b →
    ∀ c : M, ∃ d : N, I j (Fin.snoc a c : Fin _ → M) (Fin.snoc b d : Fin _ → N)
  /-- Every move of Spoiler in `N` has an answer in `M` staying in the system. -/
  back : ∀ {j k : ℕ} {a : Fin k → M} {b : Fin k → N}, I (j + 1) a b →
    ∀ d : N, ∃ c : M, I j (Fin.snoc a c : Fin _ → M) (Fin.snoc b d : Fin _ → N)

/-- Every position of a back-and-forth system with `n` rounds to play is won by Duplicator. -/
theorem IsBackAndForth.duplicatorWins {I : ℕ → ∀ {k : ℕ}, (Fin k → M) → (Fin k → N) → Prop}
    (hI : IsBackAndForth L I) : ∀ {n k : ℕ} {a : Fin k → M} {b : Fin k → N}, I n a b →
      DuplicatorWins L n a b
  | 0, _, _, _, h => duplicatorWins_zero.2 (hI.partialIso h)
  | _ + 1, _, _, _, h => duplicatorWins_succ.2 ⟨hI.partialIso h,
      fun c => (hI.forth h c).imp fun _ hd => hI.duplicatorWins hd,
      fun d => (hI.back h d).imp fun _ hc => hI.duplicatorWins hc⟩

variable (L M N) in
/-- The winning positions of Duplicator form the largest back-and-forth system. -/
theorem isBackAndForth_duplicatorWins :
    IsBackAndForth L (M := M) (N := N) fun n _ a b => DuplicatorWins L n a b where
  partialIso h := h.partialIso
  forth h := h.forth
  back h := h.back

/-! ### Basic properties of the game -/

theorem DuplicatorWins.mono : ∀ {m n k : ℕ} {a : Fin k → M} {b : Fin k → N}, m ≤ n →
    DuplicatorWins L n a b → DuplicatorWins L m a b
  | 0, _, _, _, _, _, h => duplicatorWins_zero.2 h.partialIso
  | _ + 1, _ + 1, _, _, _, hmn, h => duplicatorWins_succ.2 ⟨h.partialIso,
      fun c => (h.forth c).imp fun _ hd => hd.mono (by omega),
      fun d => (h.back d).imp fun _ hc => hc.mono (by omega)⟩
  | _ + 1, 0, _, _, _, hmn, _ => absurd hmn (by omega)

theorem DuplicatorWins.refl : ∀ (n : ℕ) {k : ℕ} (a : Fin k → M), DuplicatorWins L n a a
  | 0, _, a => duplicatorWins_zero.2 (PartialIso.refl a)
  | n + 1, _, a => duplicatorWins_succ.2 ⟨PartialIso.refl a,
      fun c => ⟨c, DuplicatorWins.refl n _⟩, fun d => ⟨d, DuplicatorWins.refl n _⟩⟩

theorem DuplicatorWins.symm : ∀ {n k : ℕ} {a : Fin k → M} {b : Fin k → N},
    DuplicatorWins L n a b → DuplicatorWins L n b a
  | 0, _, _, _, h => duplicatorWins_zero.2 h.partialIso.symm
  | _ + 1, _, _, _, h => duplicatorWins_succ.2 ⟨h.partialIso.symm,
      fun d => (h.back d).imp fun _ hc => hc.symm,
      fun c => (h.forth c).imp fun _ hd => hd.symm⟩

theorem DuplicatorWins.trans : ∀ {n k : ℕ} {a : Fin k → M} {b : Fin k → N} {c : Fin k → P},
    DuplicatorWins L n a b → DuplicatorWins L n b c → DuplicatorWins L n a c
  | 0, _, _, _, _, h₁, h₂ => duplicatorWins_zero.2 (h₁.partialIso.trans h₂.partialIso)
  | _ + 1, _, _, _, _, h₁, h₂ => by
    refine duplicatorWins_succ.2 ⟨h₁.partialIso.trans h₂.partialIso, fun x => ?_, fun z => ?_⟩
    · obtain ⟨y, hy⟩ := h₁.forth x
      obtain ⟨z, hz⟩ := h₂.forth y
      exact ⟨z, hy.trans hz⟩
    · obtain ⟨y, hy⟩ := h₂.back z
      obtain ⟨x, hx⟩ := h₁.back y
      exact ⟨x, hx.trans hy⟩

/-- Duplicator wins every game between a structure and an isomorphic copy, from a position and
its image. -/
theorem _root_.FirstOrder.Language.Equiv.duplicatorWins (e : M ≃[L] N) (n : ℕ) {k : ℕ}
    (a : Fin k → M) : DuplicatorWins L n a (e ∘ a) := by
  refine IsBackAndForth.duplicatorWins (I := fun _ _ a b => b = e ∘ a) ⟨?_, ?_, ?_⟩ rfl
  · rintro j k a b rfl
    refine ⟨fun i j => e.injective.eq_iff.symm, fun R f => ?_⟩
    rw [Function.comp_assoc, e.map_rel]
  · rintro j k a b rfl c
    exact ⟨e c, by rw [Fin.comp_snoc]⟩
  · rintro j k a b rfl d
    exact ⟨e.symm d, by rw [Fin.comp_snoc, e.apply_symm_apply]⟩

/-! ### The easy direction of the Ehrenfeucht–Fraïssé theorem -/

/-- The index of the variable of a term of a relational language with no free variables. -/
private def varIdx [L.IsRelational] {k : ℕ} (t : L.Term (Empty ⊕ Fin k)) : Fin k :=
  match termVar t with
  | .inr i => i

private theorem realize_eq_varIdx [L.IsRelational] {k : ℕ} (t : L.Term (Empty ⊕ Fin k))
    (a : Fin k → M) : t.realize (Sum.elim default a) = a (varIdx t) := by
  rw [realize_termVar, varIdx]
  rcases termVar t with x | i
  · exact x.elim
  · rfl

/-- **Ehrenfeucht–Fraïssé, easy direction.** For a relational language, if Duplicator wins the
`n`-round game from `(a, b)`, then `a` and `b` satisfy the same formulas of quantifier rank at
most `n`. No finiteness assumption is needed. -/
theorem DuplicatorWins.realize_iff [L.IsRelational] {n k : ℕ} {a : Fin k → M} {b : Fin k → N}
    (h : DuplicatorWins L n a b) {φ : L.BoundedFormula Empty k} (hφ : quantifierRank φ ≤ n) :
    φ.Realize default a ↔ φ.Realize default b := by
  induction φ generalizing n with
  | falsum => exact Iff.rfl
  | equal t₁ t₂ =>
    simp only [BoundedFormula.Realize, realize_eq_varIdx]
    exact h.partialIso.eq_iff _ _
  | rel R ts =>
    simp only [BoundedFormula.Realize, realize_eq_varIdx]
    exact h.partialIso.relMap_iff R (fun i => varIdx (ts i))
  | imp φ ψ ihφ ihψ =>
    rw [quantifierRank_imp, max_le_iff] at hφ
    exact imp_congr (ihφ h hφ.1) (ihψ h hφ.2)
  | all φ ih =>
    rw [quantifierRank_all] at hφ
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [BoundedFormula.realize_all]
    constructor
    · intro hA d
      obtain ⟨c, hc⟩ := h.back d
      exact (ih hc (by omega)).1 (hA c)
    · intro hB c
      obtain ⟨d, hd⟩ := h.forth c
      exact (ih hd (by omega)).2 (hB d)

end Cslib.Logic.FO
