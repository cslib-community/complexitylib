/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.SecondOrder.Horn
public import CslibFrontier.Logics.FirstOrder.Operator.LeastFixedPoint.Definability
public import CslibFrontier.Logics.FirstOrder.Operator.Definability.Finite
public import CslibFrontier.Logics.FirstOrder.Operator.Quantifiers
import Mathlib.Data.Fintype.Order

/-!
# Existential second-order Horn sentences as least fixed points

Every SO∃-Horn sentence is equivalent to one FO(LFP) sentence over the same base vocabulary,
uniformly over all structures in which two closed terms `c₀` and `c₁` denote distinct elements.

The construction is the classical simultaneous-induction argument, specialized to Horn programs.
The least model of the definite clauses is the least fixed point of their immediate-consequence
operator (`ESO.Horn.Sentence.leastModel`). The finitely many relation variables, of possibly
different arities, are packed into a single fixed-point relation. A tuple `x` for the relation
variable `i` becomes a tagged tuple of width `t + a`, where `t` enumerates the relation
variables and `a` bounds their arities: a one-hot tag (`c₁` in coordinate `i`, `c₀` elsewhere)
followed by `x`, padded with `c₀`. Distinctness of `c₀` and `c₁` makes the tagging injective,
and Mathlib's rolling rule for least fixed points (`OrderHom.map_lfp_comp`) identifies the packed
least fixed point with the tagged least model. Goal clauses are then checked outside the
fixed-point binder, as allowed by `ESO.Horn.Sentence.realize_iff_leastModel`.

The translation needs no restriction on the guards: they are carried over as first-order
subformulas.

## Main results

* `Cslib.Logic.ESO.Horn.Sentence.exists_lfp_realize_iff`: every SO∃-Horn sentence has an
  equivalent FO(LFP) sentence on all structures where `c₀` and `c₁` are distinct.

## References

* [E. Grädel, *Finite Model Theory and Descriptive Complexity*][Gradel2007], Theorem 3.2.17
  (pp. 147–148), for the upper bound of the SO∃-Horn characterization of polynomial time. The
  textbook proof grounds the sentence to a propositional Horn formula; this module instead goes
  through FO(LFP), which reuses the library's native FO(LFP) model checker.
* [E. Grädel, *Capturing complexity classes by fragments of second-order logic*][Gradel1992],
  the original source. Section and theorem locators are unverified.
* [N. Immerman, *Descriptive Complexity*][Immerman1999], Chapter 4, for FO(LFP) and
  simultaneous inductions.
-/

public section

universe u v w t' w'

open FirstOrder Language

namespace Cslib.Logic.ESO.Horn.Sentence

open Cslib.Logic.FO

variable {L : Language.{u, v}} {Φ : Sentence L}

/-! ### Packing several relations into one tagged relation -/

section Tagging

variable {M : Type w} {t a : ℕ}

/-- The tagged tuple of width `t + a` that represents the tuple `x` of the relation variable
`i`: the one-hot tag of `e i` followed by `x`, padded with `c₀`. -/
private def tagTuple (e : Φ.Var → Fin t) (c₀ c₁ : M) (i : Φ.Var) (x : Fin (Φ.arity i) → M) :
    Fin (t + a) → M :=
  Fin.append (fun j => if j = e i then c₁ else c₀)
    fun p => if h : p.val < Φ.arity i then x ⟨p.val, h⟩ else c₀

/-- Tagging is injective when the tags are injective, the arities fit and `c₀ ≠ c₁`. -/
private theorem tagTuple_injective {e : Φ.Var → Fin t} (he : Function.Injective e) {c₀ c₁ : M}
    (hc : c₀ ≠ c₁) (ha : ∀ i, Φ.arity i ≤ a) {i i' : Φ.Var} {x : Fin (Φ.arity i) → M}
    {x' : Fin (Φ.arity i') → M} (h : tagTuple (a := a) e c₀ c₁ i x = tagTuple e c₀ c₁ i' x') :
    (⟨i, x⟩ : Σ i, Fin (Φ.arity i) → M) = ⟨i', x'⟩ := by
  have hi : i = i' := by
    by_contra hne
    have htag := congrFun h (Fin.castAdd a (e i))
    simp only [tagTuple, Fin.append_left, ↓reduceIte, he.ne hne] at htag
    exact hc htag.symm
  subst hi
  refine Sigma.ext rfl (heq_of_eq (funext fun p => ?_))
  have hp := congrFun h (Fin.natAdd t ⟨p.val, lt_of_lt_of_le p.isLt (ha i)⟩)
  simpa only [tagTuple, Fin.append_right, Fin.val_mk, p.isLt, ↓reduceDIte, Fin.eta] using hp

/-- Tagged tuples of a family of relations. -/
private def tagSet (e : Φ.Var → Fin t) (c₀ c₁ : M) (R : ∀ i, Set (Fin (Φ.arity i) → M)) :
    Set (Fin (t + a) → M) :=
  {y | ∃ i, ∃ x ∈ R i, tagTuple e c₀ c₁ i x = y}

/-- The relations encoded by a set of tagged tuples. -/
private def untagSet (e : Φ.Var → Fin t) (c₀ c₁ : M) (S : Set (Fin (t + a) → M)) :
    ∀ i, Set (Fin (Φ.arity i) → M) :=
  fun i => {x | tagTuple e c₀ c₁ i x ∈ S}

/-- A tagged tuple lies in a tagged family exactly when its tuple lies in the family. -/
private theorem mem_tagSet_iff {e : Φ.Var → Fin t} (he : Function.Injective e) {c₀ c₁ : M}
    (hc : c₀ ≠ c₁) (ha : ∀ i, Φ.arity i ≤ a) {R : ∀ i, Set (Fin (Φ.arity i) → M)} {i : Φ.Var}
    {x : Fin (Φ.arity i) → M} : tagTuple (a := a) e c₀ c₁ i x ∈ tagSet e c₀ c₁ R ↔ x ∈ R i := by
  constructor
  · rintro ⟨i', x', hx', hy⟩
    cases tagTuple_injective he hc ha hy
    exact hx'
  · exact fun hx => ⟨i, x, hx, rfl⟩

/-- Decoding a tagged family recovers it. -/
private theorem untagSet_tagSet {e : Φ.Var → Fin t} (he : Function.Injective e) {c₀ c₁ : M}
    (hc : c₀ ≠ c₁) (ha : ∀ i, Φ.arity i ≤ a) (R : ∀ i, Set (Fin (Φ.arity i) → M)) :
    untagSet e c₀ c₁ (tagSet (a := a) e c₀ c₁ R) = R :=
  funext fun _ => Set.ext fun _ => mem_tagSet_iff he hc ha

/-- Tagging as an order homomorphism. -/
private def tagHom (e : Φ.Var → Fin t) (c₀ c₁ : M) :
    (∀ i, Set (Fin (Φ.arity i) → M)) →o Set (Fin (t + a) → M) where
  toFun := tagSet e c₀ c₁
  monotone' R S hRS := by
    rintro y ⟨i, x, hx, hy⟩
    exact ⟨i, x, hRS i hx, hy⟩

/-- Decoding as an order homomorphism. -/
private def untagHom (e : Φ.Var → Fin t) (c₀ c₁ : M) :
    Set (Fin (t + a) → M) →o ∀ i, Set (Fin (Φ.arity i) → M) where
  toFun := untagSet e c₀ c₁
  monotone' _ _ hST _ _ hx := hST hx

/-- The packed immediate-consequence operator on tagged tuples. -/
private def tagStep [L.Structure M] (e : Φ.Var → Fin t) (c₀ c₁ : M) :
    Set (Fin (t + a) → M) →o Set (Fin (t + a) → M) :=
  (tagHom e c₀ c₁).comp ((Φ.consequence M).comp (untagHom e c₀ c₁))

/-- **Packing a simultaneous induction.** The least fixed point of the packed operator is the
tagged least model. -/
private theorem lfp_tagStep [L.Structure M] {e : Φ.Var → Fin t} (he : Function.Injective e)
    {c₀ c₁ : M} (hc : c₀ ≠ c₁) (ha : ∀ i, Φ.arity i ≤ a) :
    (tagStep (a := a) e c₀ c₁).lfp = tagSet e c₀ c₁ (Φ.leastModel M) := by
  have hid : ((Φ.consequence M).comp (untagHom e c₀ c₁)).comp (tagHom (a := a) e c₀ c₁) =
      Φ.consequence M := by
    refine OrderHom.ext _ _ (funext fun R => ?_)
    exact congrArg (Φ.consequence M) (untagSet_tagSet he hc ha R)
  rw [leastModel, ← hid]
  exact ((tagHom e c₀ c₁).map_lfp_comp _).symm

/-- One packed step: a tagged tuple is produced by a definite clause whose guard and body hold
for the decoded relations. -/
private theorem mem_tagStep_iff [L.Structure M] (e : Φ.Var → Fin t) (c₀ c₁ : M)
    (S : Set (Fin (t + a) → M)) (y : Fin (t + a) → M) :
    y ∈ tagStep e c₀ c₁ S ↔ ∃ C ∈ Φ.clauses, ∃ h, C.head = some h ∧ ∃ w : Fin C.width → M,
      C.guard.Realize w ∧ (∀ b ∈ C.body, tagTuple e c₀ c₁ b.rel (w ∘ b.args) ∈ S) ∧
        tagTuple e c₀ c₁ h.rel (w ∘ h.args) = y := by
  constructor
  · rintro ⟨i, x, ⟨C, hC, h, hh, w, hg, hb, he⟩, rfl⟩
    cases he
    exact ⟨C, hC, h, hh, w, hg, hb, rfl⟩
  · rintro ⟨C, hC, h, hh, w, hg, hb, rfl⟩
    exact ⟨h.rel, w ∘ h.args, ⟨C, hC, h, hh, w, hg, hb, rfl⟩, rfl⟩

end Tagging

/-! ### Definability of the packed operator -/

section Definability

open Operator

variable {ι : Type t'} {M : ι → Type w} [∀ m, L.Structure (M m)]
  {O : Type*} {shape : O → Shape} {policy : Policy shape} {I : ∀ m, Interpretation shape (M m)}
  {Γ : List ℕ} {ρ : ∀ m, RelEnv Γ (M m)} {mark : Marking Γ} {sign : Bool} {α : Type w'}

private theorem definable_exs {n : ℕ} {P : ∀ m, (α → M m) → (Fin n → M m) → Prop}
    (hP : Operator.Definable (L := L) policy M I ρ
      (fun m v => P m (v ∘ Sum.inl) (v ∘ Sum.inr))) :
    Operator.Definable (L := L) policy M I ρ (fun m v => ∃ xs, P m v xs) := by
  obtain ⟨φ, hφ, hP⟩ := hP
  refine ⟨φ.exs n, by rw [Formula.wellFormed_exs]; exact hφ, fun m v => ?_⟩
  rw [Formula.realize_exs]
  exact exists_congr fun xs => hP m (Sum.elim v xs)

private theorem polarityDefinable_exs {n : ℕ}
    {P : ∀ m, (α → M m) → (Fin n → M m) → Prop}
    (hP : Operator.PolarityDefinable (L := L) policy mark sign M I ρ
      (fun m v => P m (v ∘ Sum.inl) (v ∘ Sum.inr))) :
    Operator.PolarityDefinable (L := L) policy mark sign M I ρ (fun m v => ∃ xs, P m v xs) := by
  obtain ⟨φ, hφ, hp, hP⟩ := hP
  refine ⟨φ.exs n, by rw [Formula.wellFormed_exs]; exact hφ,
    by rw [Formula.checkPolarity_exs]; exact hp, fun m v => ?_⟩
  rw [Formula.realize_exs]
  exact exists_congr fun xs => hP m (Sum.elim v xs)

private theorem definable_forall_mem {β : Type*} (l : List β) {P : β → ∀ m, (α → M m) → Prop}
    (hP : ∀ b ∈ l, Operator.Definable (L := L) policy M I ρ (P b)) :
    Operator.Definable (L := L) policy M I ρ (fun m v => ∀ b ∈ l, P b m v) := by
  induction l with
  | nil => exact Operator.Definable.truth.congr fun _ _ => by simp
  | cons b l ih =>
    exact ((hP b (by simp)).conj (ih fun c hc => hP c (by simp [hc]))).congr fun _ _ => by simp

private theorem realize_relabel_empty {β : Type*} {N : Type*} [L.Structure N]
    (c : L.Term Empty) (v : β → N) :
    (c.relabel Empty.elim).realize v = c.realize (Empty.elim : Empty → N) := by
  rw [Term.realize_relabel]
  exact congrArg c.realize (Subsingleton.elim _ _)

variable {t a : ℕ}

/-- The term tuple that denotes a tagged tuple, with tag constants `c₀` and `c₁`. -/
private def tagTerms {β : Type*} (e : Φ.Var → Fin t) (c₀ c₁ : L.Term Empty) (i : Φ.Var)
    (args : Fin (Φ.arity i) → β) : Fin (t + a) → L.Term β :=
  Fin.append (fun j => if j = e i then c₁.relabel Empty.elim else c₀.relabel Empty.elim)
    fun p => if h : p.val < Φ.arity i then .var (args ⟨p.val, h⟩) else c₀.relabel Empty.elim

/-- The tagged term tuple denotes the tagged tuple. -/
private theorem realize_tagTerms {β : Type*} {N : Type*} [L.Structure N] (e : Φ.Var → Fin t)
    (c₀ c₁ : L.Term Empty) (i : Φ.Var) (args : Fin (Φ.arity i) → β) (v : β → N) :
    (fun p => (tagTerms (a := a) e c₀ c₁ i args p).realize v) =
      tagTuple e (c₀.realize Empty.elim) (c₁.realize Empty.elim) i (v ∘ args) := by
  funext p
  refine Fin.addCases (fun j => ?_) (fun j => ?_) p
  · simp only [tagTerms, tagTuple, Fin.append_left]
    split_ifs <;> exact realize_relabel_empty _ v
  · simp only [tagTerms, tagTuple, Fin.append_right]
    split_ifs
    · rfl
    · exact realize_relabel_empty _ v

/-- The packed operator has a positive defining formula. It is a finite disjunction over the
definite clauses; each disjunct existentially quantifies the clause variables, keeps the guard
as a first-order subformula, and requires the tagged body tuples to lie in the bound relation. -/
private theorem tagStep_polarityDefinable (e : Φ.Var → Fin t) (c₀ c₁ : L.Term Empty)
    (mark : Marking ((t + a) :: Γ)) :
    Operator.PolarityDefinable (L := L) policy mark true
      (fun j : (m : ι) × Set (Fin (t + a) → M m) => M j.1) (fun j => I j.1)
      (fun j => RelEnv.cons j.2 (ρ j.1))
      (fun j (v : α ⊕ Fin (t + a) → M j.1) => v ∘ Sum.inr ∈
        tagStep e (c₀.realize Empty.elim) (c₁.realize Empty.elim) j.2) := by
  refine (Operator.PolarityDefinable.exists_mem Φ.clauses
    (P := fun C (j : (m : ι) × Set (Fin (t + a) → M m)) (v : α ⊕ Fin (t + a) → M j.1) =>
      ∃ h, C.head = some h ∧ ∃ w : Fin C.width → M j.1, C.guard.Realize w ∧
        (∀ b ∈ C.body, tagTuple e (c₀.realize Empty.elim) (c₁.realize Empty.elim) b.rel
          (w ∘ b.args) ∈ j.2) ∧
        tagTuple e (c₀.realize Empty.elim) (c₁.realize Empty.elim) h.rel (w ∘ h.args) =
          v ∘ Sum.inr) fun C _ => ?_).congr fun j v => (mem_tagStep_iff _ _ _ _ _).symm
  cases hC : C.head with
  | none => exact Operator.PolarityDefinable.falsity.congr fun _ _ => by simp
  | some h =>
    refine Operator.PolarityDefinable.congr
      (P := fun (j : (m : ι) × Set (Fin (t + a) → M m)) (v : α ⊕ Fin (t + a) → M j.1) =>
      ∃ w : Fin C.width → M j.1,
      C.guard.Realize w ∧ (∀ b ∈ C.body, tagTuple e (c₀.realize Empty.elim)
        (c₁.realize Empty.elim) b.rel (w ∘ b.args) ∈ j.2) ∧
        tagTuple e (c₀.realize Empty.elim) (c₁.realize Empty.elim) h.rel (w ∘ h.args) =
          v ∘ Sum.inr) ?_ fun _ _ => by simp
    refine polarityDefinable_exs
      (P := fun (j : (m : ι) × Set (Fin (t + a) → M m)) (v : α ⊕ Fin (t + a) → M j.1)
        (w : Fin C.width → M j.1) => C.guard.Realize w ∧
      (∀ b ∈ C.body, tagTuple e (c₀.realize Empty.elim) (c₁.realize Empty.elim) b.rel
        (w ∘ b.args) ∈ j.2) ∧
      tagTuple e (c₀.realize Empty.elim) (c₁.realize Empty.elim) h.rel (w ∘ h.args) =
        v ∘ Sum.inr) ?_
    refine ((Operator.PolarityDefinable.ofFO (C.guard.relabel Sum.inr)).conj
      ((Operator.PolarityDefinable.forall_mem C.body fun b _ =>
        Operator.PolarityDefinable.rel (Γ := (t + a) :: Γ) .here
          (tagTerms e c₀ c₁ b.rel (Sum.inr ∘ b.args))).conj
      (Operator.PolarityDefinable.iAll fun p => Operator.PolarityDefinable.equal
        (tagTerms e c₀ c₁ h.rel (Sum.inr ∘ h.args) p)
        (.var (Sum.inl (Sum.inr p)))))).congr fun j v => ?_
    refine and_congr Formula.realize_relabel (and_congr (forall₂_congr fun b _ => ?_) ?_)
    · exact Iff.of_eq (congrArg (· ∈ j.2) (realize_tagTerms e c₀ c₁ b.rel _ v))
    · have hr := realize_tagTerms (a := a) e c₀ c₁ h.rel (Sum.inr ∘ h.args) v
      refine ⟨fun hp => funext fun p => (congrFun hr p).symm.trans (hp p),
        fun hp p => (congrFun hr p).trans (congrFun hp p)⟩

end Definability

/-! ### The equivalent FO(LFP) sentence -/

variable {ι : Type t'} {M : ι → Type w} [∀ m, L.Structure (M m)]

/-- **SO∃-Horn sentences are FO(LFP) sentences.** For closed terms `c₀` and `c₁` of the base
vocabulary, one checked FO(LFP) sentence is equivalent to `Φ` on every structure in which `c₀` and
`c₁` denote distinct elements. Two distinct elements are needed for the one-hot tags that pack
the relation variables into a single fixed point; on the canonical ordered structures, which
have at least two elements, the numeric constants `0` and `1` serve. -/
theorem exists_lfp_realize_iff (Φ : Sentence L) (c₀ c₁ : L.Term Empty)
    (hc : ∀ m, c₀.realize (M := M m) Empty.elim ≠ c₁.realize Empty.elim) :
    ∃ φ : LFP.Formula L [] Empty, ∀ m,
      φ.Realize (M := M m) Operator.RelEnv.empty Empty.elim ↔ Φ.Realize (M m) := by
  classical
  obtain ⟨t, ⟨e⟩⟩ := Finite.exists_equiv_fin Φ.Var
  obtain ⟨a, ha⟩ := Finite.exists_le Φ.arity
  have key : Operator.Definable (L := L) LFP.policy M (fun _ => LFP.interpretation)
      (fun _ => Operator.RelEnv.empty)
      (fun m (_ : Empty → M m) => Φ.Consistent (Φ.leastModel (M m))) := by
    refine (definable_forall_mem Φ.clauses (P := fun C m _ => C.head = none →
      C.Holds (Φ.leastModel (M m))) fun C _ => ?_).congr fun _ _ => Iff.rfl
    cases hC : C.head with
    | some h => exact Operator.Definable.truth.congr fun _ _ => by simp
    | none =>
      have hlfp (b : Atom Φ.arity (Fin C.width)) := LFP.definable_lfp (M := M)
        (ρ := fun _ => Operator.RelEnv.empty) (α := Empty ⊕ Fin C.width)
        (fun m _ => tagStep (a := a) e (c₀.realize (M := M m) Empty.elim)
          (c₁.realize Empty.elim))
        (tagTerms e c₀ c₁ b.rel (Sum.inr ∘ b.args))
        (tagStep_polarityDefinable (M := M) (policy := LFP.policy)
          (I := fun _ => LFP.interpretation) (ρ := fun _ => Operator.RelEnv.empty)
          (α := Empty ⊕ Fin C.width) e c₀ c₁ LFP.headMark)
      refine ((definable_exs (n := C.width) (P := fun m _ w => C.guard.Realize w ∧
        ∀ b ∈ C.body, w ∘ b.args ∈ Φ.leastModel (M m) b.rel)
        (((Operator.Definable.ofFO (C.guard.relabel Sum.inr)).conj
          (definable_forall_mem C.body fun b _ => hlfp b)).congr fun m v => ?_)).neg).congr
        fun m v => ?_
      · refine and_congr Formula.realize_relabel (forall₂_congr fun b _ => ?_)
        rw [realize_tagTerms e c₀ c₁ b.rel _ v, lfp_tagStep e.injective (hc m) ha]
        exact mem_tagSet_iff e.injective (hc m) ha
      · simp only [Clause.Holds, Atom.Holds, hC, Option.elim_none, not_exists, not_and,
          true_implies, imp_false]
  obtain ⟨φ, hφ, hreal⟩ := key
  exact ⟨⟨φ, hφ⟩, fun m => (hreal m Empty.elim).trans (realize_iff_leastModel Φ).symm⟩

end Cslib.Logic.ESO.Horn.Sentence
