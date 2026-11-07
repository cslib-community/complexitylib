/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.EhrenfeuchtFraisse.Basic
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Basic.Finite.Sigma
public import Mathlib.Basic.Finite.Sum
import Mathlib.Data.Set.Finite.Range

/-!
# Hintikka formulas and the Ehrenfeucht–Fraïssé theorem

For a language with finitely many relation symbols, the rank-`n` type of a `k`-tuple is finite
combinatorial data (`Cslib.Logic.FO.RankType`): its atomic diagram and, if `n > 0`, the set of
rank-`(n - 1)` types of its one-point extensions. Two tuples have the same rank-`n` type exactly
when Duplicator wins the `n`-round Ehrenfeucht–Fraïssé game between them (`rankType_eq_iff`),
and every rank-`n` type is defined by a Hintikka formula of quantifier rank at most `n`
(`realize_hintikka`, `quantifierRank_hintikka_le`). Together with the easy direction
`DuplicatorWins.realize_iff`, this gives the **Ehrenfeucht–Fraïssé theorem**: for a relational
language with finitely many relation symbols, Duplicator wins the `n`-round game from `(a, b)`
exactly when `a` and `b` satisfy the same formulas of quantifier rank at most `n`.

The hypothesis `[Finite (Σ l, L.Relations l)]` (finitely many relation symbols of all arities) is
used only by the Hintikka direction `duplicatorWins_of_forall_realize_iff`, which does not need
`L.IsRelational`; the easy direction needs `L.IsRelational` and no finiteness. The structures
themselves are arbitrary, finite or infinite.

Formulas are stated as `L.BoundedFormula Empty k`, whose `k` bound variables are the pebbles.
`duplicatorWins_iff_forall_formula` restates the theorem for formulas `φ : L.Formula (Fin k)` whose
free variables name the pebbles; the translation between the two forms preserves quantifier rank
(`quantifierRank_relabel`, `quantifierRank_toFormula`).

To show that a property of finite structures is not first-order definable, exhibit for each `n`
two structures, one with the property and one without, on which Duplicator wins the `n`-round
game (`DuplicatorWins.realize_iff`). For linear orders this is carried out in
`Complexity.Logics.FirstOrder.EhrenfeuchtFraisse.FiniteLinearOrder`.

## Main definitions

* `Cslib.Logic.FO.AtomicIndex`: the atomic formulas in `k` variables, as indices.
* `Cslib.Logic.FO.RankType`, `Cslib.Logic.FO.rankType`: rank-`n` types and the type of a tuple.
* `Cslib.Logic.FO.atomicDiagram`, `Cslib.Logic.FO.hintikka`: the defining formulas of atomic
  types and of rank-`n` types.

## Main results

* `Cslib.Logic.FO.rankType_eq_iff`: equal rank-`n` types are exactly winning positions of the
  `n`-round game.
* `Cslib.Logic.FO.realize_hintikka`, `Cslib.Logic.FO.quantifierRank_hintikka_le`: the Hintikka
  formula of a type defines it and has quantifier rank at most `n`.
* `Cslib.Logic.FO.duplicatorWins_of_forall_realize_iff`: **Ehrenfeucht–Fraïssé, hard direction**.
* `Cslib.Logic.FO.duplicatorWins_iff_forall_realize_iff`,
  `Cslib.Logic.FO.duplicatorWins_iff_forall_formula`,
  `Cslib.Logic.FO.duplicatorWins_iff_forall_sentence`: **the Ehrenfeucht–Fraïssé theorem**.
* `Cslib.Logic.FO.exists_finite_quantifierRank_le_realize_iff`: there are finitely many formulas
  of quantifier rank at most `n` in `k` variables up to logical equivalence.
* `Cslib.Logic.FO.elementarilyEquivalent_iff_forall_duplicatorWins`: elementary equivalence is
  winning every finite game.

## References

* [A. Ehrenfeucht, *An application of games to the completeness problem for formalized
  theories*][Ehrenfeucht1961]
* [R. Fraïssé, *Sur quelques classifications des systèmes de relations*][Fraisse1954]
* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004], Chapter 3 (the
  Ehrenfeucht–Fraïssé theorem and rank-`k` types).
* [H.-D. Ebbinghaus and J. Flum, *Finite Model Theory*][EbbinghausFlum1999], Chapter 2.
-/

public section

universe u v w w'

open FirstOrder Language Structure

namespace Cslib.Logic.FO

variable {L : Language.{u, v}} {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]

/-! ### Atomic types -/

variable (L) in
/-- The atomic formulas in `k` variables of a relational language, as indices: an equation
`xᵢ = xⱼ`, or a relation symbol applied to a tuple of variables. -/
abbrev AtomicIndex (k : ℕ) : Type v :=
  ULift.{v} (Fin k × Fin k) ⊕ Σ R : Σ l, L.Relations l, Fin R.1 → Fin k

instance AtomicIndex.finite [Finite (Σ l, L.Relations l)] (k : ℕ) : Finite (AtomicIndex L k) :=
  have : Finite (Σ R : Σ l, L.Relations l, Fin R.1 → Fin k) := inferInstance
  inferInstanceAs (Finite (_ ⊕ _))

/-- The atomic formula `xᵢ = xⱼ` or `R(x_{f 0}, …)` with index `i`, the variables being the bound
variables of a formula with no free variables. -/
def AtomicIndex.formula {k : ℕ} : AtomicIndex L k → L.BoundedFormula Empty k
  | .inl ⟨(i, j)⟩ => .equal (.var (.inr i)) (.var (.inr j))
  | .inr ⟨⟨_, R⟩, f⟩ => .rel R fun i => .var (.inr (f i))

/-- The atomic fact with index `i` holds of the tuple `a`. -/
def AtomicIndex.Holds {k : ℕ} (a : Fin k → M) : AtomicIndex L k → Prop
  | .inl ⟨(i, j)⟩ => a i = a j
  | .inr ⟨⟨_, R⟩, f⟩ => RelMap R (a ∘ f)

@[simp] theorem AtomicIndex.holds_inl {k : ℕ} (a : Fin k → M) (i j : Fin k) :
    AtomicIndex.Holds a (Sum.inl ⟨(i, j)⟩ : AtomicIndex L k) ↔ a i = a j := by
  rw [AtomicIndex.Holds]

@[simp] theorem AtomicIndex.holds_inr {k l : ℕ} (a : Fin k → M) (R : L.Relations l)
    (f : Fin l → Fin k) :
    AtomicIndex.Holds a (Sum.inr ⟨⟨l, R⟩, f⟩ : AtomicIndex L k) ↔ RelMap R (a ∘ f) := by
  rw [AtomicIndex.Holds]

@[simp] theorem AtomicIndex.realize_formula {k : ℕ} (i : AtomicIndex L k) (a : Fin k → M) :
    i.formula.Realize default a ↔ i.Holds a := by
  rcases i with ⟨⟨i, j⟩⟩ | ⟨⟨l, R⟩, f⟩
  · rfl
  · rfl

@[simp] theorem AtomicIndex.quantifierRank_formula {k : ℕ} (i : AtomicIndex L k) :
    quantifierRank i.formula = 0 := by
  rcases i with ⟨⟨i, j⟩⟩ | ⟨⟨l, R⟩, f⟩
  · exact quantifierRank_equal _ _
  · exact quantifierRank_rel _ _

/-- A position is a partial isomorphism exactly when both tuples satisfy the same atomic
formulas. -/
theorem partialIso_iff_holds {k : ℕ} {a : Fin k → M} {b : Fin k → N} :
    PartialIso L a b ↔ ∀ i : AtomicIndex L k, i.Holds a ↔ i.Holds b := by
  constructor
  · rintro ⟨heq, hrel⟩ (⟨⟨i, j⟩⟩ | ⟨⟨l, R⟩, f⟩)
    · exact heq i j
    · exact hrel R f
  · intro h
    exact ⟨fun i j => h (.inl ⟨(i, j)⟩), fun R f => h (.inr ⟨⟨_, R⟩, f⟩)⟩

/-! ### Rank types -/

variable (L) in
/-- The rank-`n` types of `k`-tuples, as combinatorial data: a rank-`0` type is a set of atomic
facts, and a rank-`(n + 1)` type is a set of atomic facts together with the set of rank-`n` types of
the one-point extensions. The body is exposed: statements about types use its shape. -/
@[expose] def RankType : ℕ → ℕ → Type v
  | 0, k => Set (AtomicIndex L k)
  | n + 1, k => Set (AtomicIndex L k) × Set (RankType n (k + 1))

/-- For finitely many relation symbols, there are finitely many rank-`n` types of `k`-tuples. -/
instance RankType.finite [Finite (Σ l, L.Relations l)] : ∀ n k, Finite (RankType L n k)
  | 0, _ => inferInstanceAs (Finite (Set _))
  | n + 1, k =>
    have := RankType.finite n (k + 1)
    inferInstanceAs (Finite (Set _ × Set _))

/-- The rank-`n` type of a tuple. -/
def rankType : ∀ (n : ℕ) {k : ℕ}, (Fin k → M) → RankType L n k
  | 0, _, a => {i | i.Holds a}
  | n + 1, _, a => ({i | i.Holds a}, Set.range fun c : M => rankType n (Fin.snoc a c : Fin _ → M))

theorem rankType_zero {k : ℕ} (a : Fin k → M) :
    rankType (L := L) 0 a = {i | i.Holds a} := by
  rw [rankType]

/-- Equality of rank-`(n + 1)` types is componentwise. -/
theorem RankType.succ_ext_iff {n k : ℕ} {T T' : RankType L (n + 1) k} :
    T = T' ↔ T.1 = T'.1 ∧ T.2 = T'.2 :=
  Prod.ext_iff

theorem rankType_succ {n k : ℕ} (a : Fin k → M) :
    rankType (L := L) (n + 1) a =
      ({i | i.Holds a}, Set.range fun c : M => rankType n (Fin.snoc a c : Fin _ → M)) := by
  rw [rankType]

/-- Two tuples have the same rank-`n` type exactly when Duplicator wins the `n`-round game. -/
theorem rankType_eq_iff : ∀ {n k : ℕ} {a : Fin k → M} {b : Fin k → N},
    rankType (L := L) n a = rankType n b ↔ DuplicatorWins L n a b
  | 0, k, a, b => by
    rw [duplicatorWins_zero, partialIso_iff_holds, rankType_zero, rankType_zero]
    exact Set.ext_iff
  | n + 1, k, a, b => by
    rw [duplicatorWins_succ, partialIso_iff_holds, RankType.succ_ext_iff, rankType_succ,
      rankType_succ, Set.ext_iff, Set.ext_iff]
    simp only [Set.mem_ofPred_eq, Set.mem_range]
    refine and_congr Iff.rfl ⟨fun h => ⟨fun c => ?_, fun d => ?_⟩, fun ⟨hf, hb⟩ T => ?_⟩
    · obtain ⟨d, hd⟩ := (h _).1 ⟨c, rfl⟩
      exact ⟨d, rankType_eq_iff.1 hd.symm⟩
    · obtain ⟨c, hc⟩ := (h _).2 ⟨d, rfl⟩
      exact ⟨c, rankType_eq_iff.1 hc⟩
    · constructor
      · rintro ⟨c, rfl⟩
        obtain ⟨d, hd⟩ := hf c
        exact ⟨d, (rankType_eq_iff.2 hd).symm⟩
      · rintro ⟨d, rfl⟩
        obtain ⟨c, hc⟩ := hb d
        exact ⟨c, rankType_eq_iff.2 hc⟩

/-! ### Hintikka formulas -/

open scoped Classical in
/-- The conjunction of the atomic facts in `T` and the negations of those not in `T`. -/
noncomputable def atomicDiagram [Finite (Σ l, L.Relations l)] {k : ℕ} (T : Set (AtomicIndex L k)) :
    L.BoundedFormula Empty k :=
  BoundedFormula.iInf fun i : AtomicIndex L k => if i ∈ T then i.formula else i.formula.not

theorem realize_atomicDiagram [Finite (Σ l, L.Relations l)] {k : ℕ} (T : Set (AtomicIndex L k))
    (a : Fin k → M) : (atomicDiagram T).Realize default a ↔ {i | i.Holds a} = T := by
  classical
  simp only [atomicDiagram, BoundedFormula.realize_iInf, Set.ext_iff, Set.mem_ofPred_eq]
  refine forall_congr' fun i => ?_
  by_cases hi : i ∈ T <;> simp [hi]

theorem quantifierRank_atomicDiagram [Finite (Σ l, L.Relations l)] {k : ℕ}
    (T : Set (AtomicIndex L k)) : quantifierRank (atomicDiagram T) = 0 := by
  classical
  refine Nat.le_zero.1 (quantifierRank_iInf_le fun i => ?_)
  by_cases hi : i ∈ T <;> simp [hi]

/-- The Hintikka formula of a rank-`n` type: a formula of quantifier rank at most `n` satisfied
exactly by the tuples of that type. For `n + 1` it states the atomic diagram, that every
rank-`n` type of the type is realized by a one-point extension, and that every one-point
extension realizes one of them. -/
noncomputable def hintikka [Finite (Σ l, L.Relations l)] :
    ∀ {n k : ℕ}, RankType L n k → L.BoundedFormula Empty k
  | 0, _, T => atomicDiagram T
  | _ + 1, _, T =>
    atomicDiagram T.1 ⊓ BoundedFormula.iInf (fun T' : T.2 => (hintikka T'.1).ex) ⊓
      (BoundedFormula.iSup fun T' : T.2 => hintikka T'.1).all

theorem realize_hintikka [Finite (Σ l, L.Relations l)] :
    ∀ {n k : ℕ} (T : RankType L n k) (a : Fin k → M),
      (hintikka T).Realize default a ↔ rankType n a = T
  | 0, _, T, a => by
    rw [hintikka, rankType_zero]
    exact realize_atomicDiagram T a
  | n + 1, k, T, a => by
    rw [RankType.succ_ext_iff, rankType_succ, hintikka]
    simp only [BoundedFormula.realize_inf, BoundedFormula.realize_iInf,
      BoundedFormula.realize_ex, BoundedFormula.realize_all, BoundedFormula.realize_iSup,
      realize_hintikka, realize_atomicDiagram, Subtype.forall, Subtype.exists, exists_prop,
      exists_eq_right', and_assoc]
    refine and_congr Iff.rfl ?_
    rw [Set.ext_iff]
    simp only [Set.mem_range]
    constructor
    · rintro ⟨h₁, h₂⟩ T
      exact ⟨fun ⟨c, hc⟩ => hc ▸ h₂ c, fun hT => h₁ T hT⟩
    · intro h
      exact ⟨fun T hT => (h T).2 hT, fun c => (h _).1 ⟨c, rfl⟩⟩

theorem quantifierRank_hintikka_le [Finite (Σ l, L.Relations l)] :
    ∀ {n k : ℕ} (T : RankType L n k), quantifierRank (hintikka T) ≤ n
  | 0, _, T => by
    rw [hintikka]
    exact (quantifierRank_atomicDiagram T).le
  | n + 1, k, T => by
    rw [hintikka]
    simp only [quantifierRank_inf, quantifierRank_all, quantifierRank_atomicDiagram, max_le_iff]
    refine ⟨⟨Nat.zero_le _, quantifierRank_iInf_le fun T => ?_⟩,
      Nat.succ_le_succ (quantifierRank_iSup_le fun T => quantifierRank_hintikka_le T.1)⟩
    rw [quantifierRank_ex]
    exact Nat.succ_le_succ (quantifierRank_hintikka_le T.1)

/-! ### The Ehrenfeucht–Fraïssé theorem -/

/-- **Ehrenfeucht–Fraïssé, hard direction.** For a language with finitely many relation symbols,
if `a` and `b` satisfy the same formulas of quantifier rank at most `n`, then Duplicator wins the
`n`-round game from `(a, b)`. Only the Hintikka formula of the type of `a` is used. -/
theorem duplicatorWins_of_forall_realize_iff [Finite (Σ l, L.Relations l)] {n k : ℕ}
    {a : Fin k → M} {b : Fin k → N}
    (h : ∀ φ : L.BoundedFormula Empty k, quantifierRank φ ≤ n →
      (φ.Realize default a ↔ φ.Realize default b)) : DuplicatorWins L n a b := by
  rw [← rankType_eq_iff]
  have hb := (h _ (quantifierRank_hintikka_le (rankType (L := L) n a))).1
    ((realize_hintikka _ a).2 rfl)
  exact ((realize_hintikka _ b).1 hb).symm

/-- **The Ehrenfeucht–Fraïssé theorem** [Libkin2004]. For a relational language with finitely
many relation symbols, Duplicator wins the `n`-round game from `(a, b)` exactly when `a` and `b`
satisfy the same formulas of quantifier rank at most `n`. -/
theorem duplicatorWins_iff_forall_realize_iff [L.IsRelational] [Finite (Σ l, L.Relations l)]
    {n k : ℕ} {a : Fin k → M} {b : Fin k → N} :
    DuplicatorWins L n a b ↔ ∀ φ : L.BoundedFormula Empty k, quantifierRank φ ≤ n →
      (φ.Realize default a ↔ φ.Realize default b) :=
  ⟨fun h _ hφ => h.realize_iff hφ, duplicatorWins_of_forall_realize_iff⟩

private theorem realize_toFormula_relabel {P : Type*} [L.Structure P] {k : ℕ}
    (φ : L.BoundedFormula Empty k) (a : Fin k → P) :
    (φ.toFormula.relabel (Sum.elim Empty.elim id : Empty ⊕ Fin k → Fin k)).Realize a ↔
      φ.Realize default a := by
  rw [Formula.realize_relabel, BoundedFormula.realize_toFormula,
    Subsingleton.elim ((a ∘ Sum.elim Empty.elim id) ∘ Sum.inl) default]
  rfl

/-- **The Ehrenfeucht–Fraïssé theorem for formulas with free variables.** For a relational
language with finitely many relation symbols, Duplicator wins the `n`-round game from `(a, b)`
exactly when `a` and `b` satisfy the same formulas `φ : L.Formula (Fin k)` of quantifier rank at
most `n`. -/
theorem duplicatorWins_iff_forall_formula [L.IsRelational] [Finite (Σ l, L.Relations l)]
    {n k : ℕ} {a : Fin k → M} {b : Fin k → N} :
    DuplicatorWins L n a b ↔ ∀ φ : L.Formula (Fin k), quantifierRank φ ≤ n →
      (φ.Realize a ↔ φ.Realize b) := by
  refine ⟨fun h _ hφ => h.formula_realize_iff hφ, fun h => ?_⟩
  refine duplicatorWins_of_forall_realize_iff fun ψ hψ => ?_
  rw [← realize_toFormula_relabel, ← realize_toFormula_relabel]
  exact h _ (by rwa [quantifierRank_formula_relabel, quantifierRank_toFormula])

/-- **The Ehrenfeucht–Fraïssé theorem for sentences.** For a relational language with finitely
many relation symbols, Duplicator wins the `n`-round game on `M` and `N` exactly when `M` and `N`
satisfy the same sentences of quantifier rank at most `n`. -/
theorem duplicatorWins_iff_forall_sentence [L.IsRelational] [Finite (Σ l, L.Relations l)]
    {n : ℕ} {a : Fin 0 → M} {b : Fin 0 → N} :
    DuplicatorWins L n a b ↔ ∀ φ : L.Sentence, quantifierRank φ ≤ n → (M ⊨ φ ↔ N ⊨ φ) := by
  obtain rfl := Subsingleton.elim a default
  obtain rfl := Subsingleton.elim b default
  exact duplicatorWins_iff_forall_realize_iff

/-! ### Consequences -/

/-- For a relational language with finitely many relation symbols, there are only finitely many
formulas of quantifier rank at most `n` in `k` variables up to logical equivalence: each is
equivalent, in every structure, to a disjunction of Hintikka formulas. -/
theorem exists_finite_quantifierRank_le_realize_iff [L.IsRelational] [Finite (Σ l, L.Relations l)]
    (n k : ℕ) :
    ∃ F : Set (L.BoundedFormula Empty k), F.Finite ∧ (∀ ψ ∈ F, quantifierRank ψ ≤ n) ∧
      ∀ φ : L.BoundedFormula Empty k, quantifierRank φ ≤ n → ∃ ψ ∈ F,
        ∀ (M : Type w) [L.Structure M] (a : Fin k → M),
          φ.Realize default a ↔ ψ.Realize default a := by
  let F := Set.range fun S : Set (RankType L n k) =>
    BoundedFormula.iSup fun T : S => hintikka T.1
  refine ⟨F, Set.finite_range _, ?_, fun φ hφ => ?_⟩
  · rintro _ ⟨S, rfl⟩
    exact quantifierRank_iSup_le fun T => quantifierRank_hintikka_le T.1
  · refine ⟨_, ⟨{T | ∀ (M : Type w) [L.Structure M] (a : Fin k → M), rankType n a = T →
      φ.Realize default a}, rfl⟩, fun M _ a => ?_⟩
    simp only [BoundedFormula.realize_iSup, realize_hintikka, Subtype.exists, Set.mem_ofPred_eq,
      exists_prop, exists_eq_right']
    exact ⟨fun h M' _ a' ha' => ((rankType_eq_iff.1 ha').realize_iff hφ).2 h,
      fun h => h M a rfl⟩

/-- For a relational language with finitely many relation symbols, two structures are
elementarily equivalent exactly when Duplicator wins the `n`-round game on them for every `n`. -/
theorem elementarilyEquivalent_iff_forall_duplicatorWins [L.IsRelational]
    [Finite (Σ l, L.Relations l)] {a : Fin 0 → M} {b : Fin 0 → N} :
    L.ElementarilyEquivalent M N ↔ ∀ n, DuplicatorWins L n a b := by
  simp only [elementarilyEquivalent_iff, duplicatorWins_iff_forall_sentence]
  exact ⟨fun h n φ _ => h φ, fun h φ => h _ φ le_rfl⟩

end Cslib.Logic.FO
