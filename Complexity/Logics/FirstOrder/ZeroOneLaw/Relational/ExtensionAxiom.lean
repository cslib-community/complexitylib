/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.FirstOrder
public import Complexity.Logics.FirstOrder.Basic
public import Mathlib.ModelTheory.PartialEquiv
public import Mathlib.ModelTheory.Satisfiability
import Mathlib.Basic.Finite.Sigma
import Mathlib.ModelTheory.FinitelyGenerated

/-!
# Extension axioms for a finite relational vocabulary

Let `L` be a relational language with finitely many relation symbols. An **extension axiom** with
`k` given elements prescribes the atomic type of a new element over them: for every pattern
`p` assigning a truth value to each atomic fact on `Fin (k + 1)` that mentions the new element `0`
(`Cslib.Logic.FO.Relational.NewAtom`), it says that for all pairwise distinct `x₀, …, x_{k-1}`
there is an element `z`, distinct from every `xᵢ`, such that each such fact holds of
`z, x₀, …, x_{k-1}` exactly when `p` says so [Fagin1976] [Libkin2004, Chapter 12]. The
**extension theory** consists of all extension axioms.

Its models are infinite, and between any two of them the finite partial isomorphisms have the
back-and-forth property: a finite partial isomorphism extends to any new element by choosing a
witness of the extension axiom given by the atomic type of the new element. When `L` has no nullary
relation symbols, whose truth values the extension axioms leave open, two countable models are
therefore isomorphic (`Cslib.Logic.FO.Relational.aleph0_categorical_extensionTheory`).
Satisfiability and completeness of the theory are in
`Complexity.Logics.FirstOrder.ZeroOneLaw.Relational`.

For `L = Language.graph` these are the extension axioms of directed graphs with loops, not the
extension axioms of simple graphs in `Complexity.Logics.FirstOrder.ZeroOneLaw.ExtensionAxiom`.

## Main definitions

* `Cslib.Logic.FO.Relational.NewAtom`: the atomic facts mentioning the new element.
* `Cslib.Logic.FO.Relational.IsExtensionWitness`: a witness of the extension of a tuple by a
  pattern.
* `Cslib.Logic.FO.Relational.HasExtension`: the extension property for a fixed pattern.
* `Cslib.Logic.FO.Relational.extensionAxiom`: the extension axiom as a first-order sentence.
* `Cslib.Logic.FO.Relational.extensionTheory`: the set of all extension axioms.

## Main results

* `Cslib.Logic.FO.Relational.realize_extensionAxiom`: an extension axiom holds exactly when the
  extension property does.
* `Cslib.Logic.FO.Relational.model_extensionTheory_iff`: models of the theory are the structures
  with all extension properties.
* `Cslib.Logic.FO.Relational.infinite_of_model_extensionTheory`: such models are infinite.
* `Cslib.Logic.FO.Relational.isExtensionPair_of_hasExtension`: the forth step of the
  back-and-forth argument.
* `Cslib.Logic.FO.Relational.aleph0_categorical_extensionTheory`: without nullary relation
  symbols, the theory is `ℵ₀`-categorical.

## References

* [R. Fagin, *Probabilities on finite models*][Fagin1976]
* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004], Chapter 12.
-/

public section

open FirstOrder Language Structure BoundedFormula Cardinal Cslib.Circuits.Boolean.ModelChecking

namespace Cslib.Logic.FO.Relational

universe u v w

variable {L : Language.{u, v}}

/-- The atomic facts on `Fin (k + 1)` that mention the element `0`: the facts constrained by an
extension axiom with `k` given elements, where `0` stands for the new element. -/
@[expose]
def NewAtom (L : Language.{u, v}) (k : ℕ) : Type _ :=
  {a : Atom L (k + 1) // 0 ∈ Set.range a.2}

instance {k : ℕ} [Finite (Σ l, L.Relations l)] : Finite (NewAtom L k) :=
  have : Finite (Atom L (k + 1)) := inferInstanceAs (Finite (Σ _ : Σ l, L.Relations l, _))
  Subtype.finite

variable {M : Type w} [L.Structure M]

/-- `z` witnesses the extension of the tuple `x` by the pattern `p`: it differs from every `x i`,
and each atomic fact mentioning the new element holds of `z, x 0, …, x (k - 1)` exactly when `p`
says so. -/
@[expose]
def IsExtensionWitness {k : ℕ} (x : Fin k → M) (p : NewAtom L k → Bool) (z : M) : Prop :=
  (∀ i, z ≠ x i) ∧
    ∀ a : NewAtom L k, (RelMap a.1.1.2 ((Fin.cons z x : Fin (k + 1) → M) ∘ a.1.2) ↔ p a = true)

variable (M) in
/-- The extension property for the pattern `p`: every tuple of `k` distinct elements has a witness
of the extension by `p`. -/
@[expose]
def HasExtension {k : ℕ} (p : NewAtom L k → Bool) : Prop :=
  ∀ x : Fin k → M, Function.Injective x → ∃ z, IsExtensionWitness x p z

/-- The atomic formula of an atomic fact on `Fin (k + 1)`, with `0` read as the existentially
quantified variable and `i + 1` as the free variable `i`. -/
private noncomputable def atomFormula {k : ℕ} (a : Atom L (k + 1)) : L.Formula (Fin k ⊕ Fin 1) :=
  a.1.2.formula fun j => Term.var ((Fin.cons (Sum.inr 0) Sum.inl : Fin (k + 1) → Fin k ⊕ Fin 1)
    (a.2 j))

private theorem realize_atomFormula {k : ℕ} (a : Atom L (k + 1)) (x : Fin k → M)
    (zf : Fin 1 → M) :
    (atomFormula a).Realize (Sum.elim x zf) ↔
      RelMap a.1.2 ((Fin.cons (zf 0) x : Fin (k + 1) → M) ∘ a.2) := by
  rw [atomFormula, Formula.realize_rel]
  refine iff_of_eq (congrArg _ (funext fun j => ?_))
  simp only [Term.realize_var, Function.comp_apply]
  refine Fin.cases ?_ (fun i => ?_) (a.2 j)
  · rfl
  · rfl

/-- The matrix of an extension axiom. -/
private noncomputable def extensionBody [Finite (Σ l, L.Relations l)] {k : ℕ}
    (p : NewAtom L k → Bool) : L.Formula (Fin k) :=
  (Formula.iInf fun q : {q : Fin k × Fin k // q.1 ≠ q.2} => ∼(varEq q.1.1 q.1.2)) ⟹
    Formula.iExs (Fin 1)
      ((Formula.iInf fun i : Fin k => ∼(varEq (Sum.inr 0) (Sum.inl i))) ⊓
        Formula.iInf fun a : NewAtom L k =>
          if p a then atomFormula a.1 else ∼(atomFormula a.1))

/-- The **extension axiom** for the pattern `p`: every tuple of `k` distinct elements has a witness
of its extension by `p` [Fagin1976]. -/
noncomputable def extensionAxiom [Finite (Σ l, L.Relations l)] (k : ℕ)
    (p : NewAtom L k → Bool) : L.Sentence :=
  closeAll (Fin k) (extensionBody p)

private theorem realize_ite_atomFormula {k : ℕ} (a : Atom L (k + 1)) (b : Bool)
    (v : Fin k ⊕ Fin 1 → M) :
    (if b then atomFormula a else ∼(atomFormula a)).Realize v ↔
      ((atomFormula a).Realize v ↔ b = true) := by
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, Formula.realize_not, iff_false,
    iff_true]

theorem realize_extensionAxiom [Finite (Σ l, L.Relations l)] {k : ℕ} (p : NewAtom L k → Bool) :
    M ⊨ extensionAxiom k p ↔ HasExtension M p := by
  rw [extensionAxiom, realize_closeAll]
  refine forall_congr' fun x => ?_
  simp only [extensionBody, Formula.realize_imp, Formula.realize_iInf, Formula.realize_not,
    realize_varEq, Formula.realize_iExs, Formula.realize_inf, realize_ite_atomFormula,
    realize_atomFormula]
  constructor
  · intro h hx
    obtain ⟨zf, hz1, hz2⟩ := h fun q hq => q.2 (hx hq)
    exact ⟨zf 0, hz1, hz2⟩
  · intro h hx
    obtain ⟨z, hz1, hz2⟩ := h fun i j hij => by
      by_contra hne
      exact hx ⟨(i, j), hne⟩ hij
    exact ⟨fun _ => z, hz1, hz2⟩

variable (L) in
/-- The **extension theory** of a finite relational vocabulary: all extension axioms
[Fagin1976]. -/
noncomputable def extensionTheory [Finite (Σ l, L.Relations l)] : L.Theory :=
  Set.range fun q : (k : ℕ) × (NewAtom L k → Bool) => extensionAxiom q.1 q.2

theorem mem_extensionTheory [Finite (Σ l, L.Relations l)] {φ : L.Sentence} :
    φ ∈ extensionTheory L ↔ ∃ k, ∃ p : NewAtom L k → Bool, extensionAxiom k p = φ := by
  simp only [extensionTheory, Set.mem_range, Sigma.exists]

theorem model_extensionTheory_iff [Finite (Σ l, L.Relations l)] :
    M ⊨ extensionTheory L ↔ ∀ k (p : NewAtom L k → Bool), HasExtension M p := by
  simp only [Theory.model_iff, mem_extensionTheory, forall_exists_index]
  refine ⟨fun h k p => (realize_extensionAxiom p).1 (h _ k p rfl), ?_⟩
  rintro h _ k p rfl
  exact (realize_extensionAxiom p).2 (h k p)

/-- A structure with every extension property is infinite. -/
theorem infinite_of_hasExtension (h : ∀ k (p : NewAtom L k → Bool), HasExtension M p) :
    Infinite M := by
  by_contra hfin
  rw [not_infinite_iff_finite] at hfin
  have := Fintype.ofFinite M
  let e := (Fintype.equivFin M).symm
  obtain ⟨z, hz, -⟩ := h _ (fun _ => false) e e.injective
  exact hz (e.symm z) (e.apply_symm_apply z).symm

/-- Models of the extension theory are infinite. -/
theorem infinite_of_model_extensionTheory [Finite (Σ l, L.Relations l)]
    [M ⊨ extensionTheory L] : Infinite M :=
  infinite_of_hasExtension (model_extensionTheory_iff.1 ‹_›)

/-- **Forth step.** If `N` has every extension property, then every embedding of a finitely
generated (that is, finite) substructure of `M` into `N` extends to any further element of `M`. -/
theorem isExtensionPair_of_hasExtension [L.IsRelational] {N : Type*} [L.Structure N]
    (hN : ∀ k (p : NewAtom L k → Bool), HasExtension N p) : L.IsExtensionPair M N := by
  classical
  rw [isExtensionPair_iff_exists_embedding_closure_singleton_sup]
  intro S S_fg f m
  have hU : ∀ u : M, u ∈ (Substructure.closure L {m} ⊔ S) ↔ u = m ∨ u ∈ S := by
    intro u
    rw [← Substructure.closure_eq S, ← Substructure.closure_union,
      Substructure.mem_closure_iff_of_isRelational, Substructure.closure_eq]
    simp only [Set.mem_union, Set.mem_singleton_iff, SetLike.mem_coe]
  have : Finite S := Substructure.fg_iff_finite.1 S_fg
  have := Fintype.ofFinite S
  -- Enumerate `S` and ask for a witness of the atomic type of `m` over `S`.
  let e := (Fintype.equivFin S).symm
  let xs : Fin (Fintype.card S) → M := fun i => (e i : M)
  let x : Fin (Fintype.card S) → N := fun i => f (e i)
  have hx : Function.Injective x := f.injective.comp e.injective
  let p : NewAtom L (Fintype.card S) → Bool := fun a =>
    decide (RelMap a.1.1.2 ((Fin.cons m xs : Fin (Fintype.card S + 1) → M) ∘ a.1.2))
  obtain ⟨z, hzne, hzp⟩ := hN _ p x hx
  have hzf : ∀ a : S, f a ≠ z := fun a h => hzne (e.symm a) (by simp [x, ← h])
  let U : L.Substructure M := Substructure.closure L {m} ⊔ S
  -- Send `m` to `z` and every element of `S` to its image under `f`.
  let g : U → N := fun u => if h : (u : M) ∈ S then f ⟨u, h⟩ else z
  have hg_of_mem : ∀ (u : U) (h : (u : M) ∈ S), g u = f ⟨u, h⟩ := fun u h => dite_eq_left h
  have hg_of_not_mem : ∀ u : U, (u : M) ∉ S → g u = z := fun u h => dite_eq_right h
  have hm_of_not_mem : ∀ u : U, (u : M) ∉ S → (u : M) = m := fun u h =>
    ((hU u).1 u.2).resolve_right h
  have g_inj : Function.Injective g := by
    intro u w huw
    apply Subtype.ext
    by_cases hu : (u : M) ∈ S <;> by_cases hw : (w : M) ∈ S
    · rw [hg_of_mem u hu, hg_of_mem w hw] at huw
      exact Subtype.mk.inj (f.injective huw)
    · rw [hg_of_mem u hu, hg_of_not_mem w hw] at huw
      exact absurd huw (hzf _)
    · rw [hg_of_not_mem u hu, hg_of_mem w hw] at huw
      exact absurd huw.symm (hzf _)
    · rw [hm_of_not_mem u hu, hm_of_not_mem w hw]
  have g_rel : ∀ {l} (R : L.Relations l) (t : Fin l → U), RelMap R (g ∘ t) ↔ RelMap R t := by
    intro l R t
    change RelMap R (g ∘ t) ↔ RelMap R (Subtype.val ∘ t)
    by_cases hall : ∀ j, ((t j : U) : M) ∈ S
    · -- Every argument is in `S`: use `f`.
      let t' : Fin l → S := fun j => ⟨t j, hall j⟩
      have h1 : g ∘ t = f ∘ t' := funext fun j => hg_of_mem _ (hall j)
      have h2 : Subtype.val ∘ t = Subtype.val ∘ t' := rfl
      rw [h1, h2, f.map_rel]
      rfl
    · -- Some argument is `m`: use the witness `z`.
      push Not at hall
      obtain ⟨j₀, hj₀⟩ := hall
      let τ : Fin l → Fin (Fintype.card S + 1) := fun j =>
        if h : ((t j : U) : M) ∈ S then (e.symm ⟨t j, h⟩).succ else 0
      have hτ : (0 : Fin (Fintype.card S + 1)) ∈ Set.range τ := ⟨j₀, by simp [τ, hj₀]⟩
      let a : NewAtom L (Fintype.card S) := ⟨⟨⟨l, R⟩, τ⟩, hτ⟩
      have h1 : g ∘ t = (Fin.cons z x : Fin (Fintype.card S + 1) → N) ∘ τ := by
        funext j
        by_cases hj : ((t j : U) : M) ∈ S
        · simp [τ, hj, hg_of_mem _ hj, x]
        · simp [τ, hj, hg_of_not_mem _ hj]
      have h2 : Subtype.val ∘ t = (Fin.cons m xs : Fin (Fintype.card S + 1) → M) ∘ τ := by
        funext j
        by_cases hj : ((t j : U) : M) ∈ S
        · simp [τ, hj, xs]
        · change ((t j : U) : M) = (Fin.cons m xs : Fin (Fintype.card S + 1) → M) (τ j)
          rw [show τ j = 0 from dite_eq_right hj, Fin.cons_zero]
          exact hm_of_not_mem _ hj
      rw [h1, h2]
      exact (hzp a).trans (by simp [p, a])
  refine ⟨⟨⟨g, g_inj⟩, fun f' => isEmptyElim f', fun R t => g_rel R t⟩, ?_⟩
  ext a
  simp only [Embedding.comp_apply, Substructure.coe_inclusion]
  change f a = g _
  rw [hg_of_mem _ a.2]

/-- **The extension theory is `ℵ₀`-categorical**: any two countable models are isomorphic, by a
back-and-forth argument [Libkin2004, Chapter 12]. This needs that `L` has no nullary relation
symbols, whose truth values the extension axioms do not determine. -/
theorem aleph0_categorical_extensionTheory [L.IsRelational] [Finite (Σ l, L.Relations l)]
    [IsEmpty (L.Relations 0)] : (ℵ₀).Categorical.{u, v, w} (extensionTheory L) := by
  intro M N hM hN
  have : Countable M := Cardinal.mk_le_aleph0_iff.1 hM.le
  have : Countable N := Cardinal.mk_le_aleph0_iff.1 hN.le
  have hMe := model_extensionTheory_iff.1 M.is_model
  have hNe := model_extensionTheory_iff.1 N.is_model
  obtain ⟨f, -⟩ := equiv_between_cg cg_of_countable cg_of_countable default
    (isExtensionPair_of_hasExtension hNe) (isExtensionPair_of_hasExtension hMe)
  exact ⟨f⟩

end Cslib.Logic.FO.Relational
