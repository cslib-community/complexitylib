/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.SecondOrder.Horn
public import CslibFrontier.Logics.FirstOrder.Ordered.Successor
import Mathlib.Basic.Finite.Sigma
import Mathlib.Basic.Finite.Sum
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Guard elimination for SO∃-Horn sentences on successor structures

On canonical ordered structures with a primitive successor relation and endpoint constants `0` and
`max`, every SO∃-Horn sentence with arbitrary first-order guards is equivalent to one whose guards
are quantifier-free (`Sentence.IsQF`).

For each subformula `ψ` of a clause guard, `elimGuards` introduces positive and negative auxiliary
relation variables whose intended extensions are the tuples satisfying `ψ` and `¬ ψ`. Atomic
subformulas are opened into quantifier-free guards directly; implications split into positive and
negative Horn rules with guard `⊤`; existential negation `¬ ∀ y, ψ(v, y)` projects `neg_ψ(v, y)` to
`neg(v)`; and universal quantification `∀ y, ψ(v, y)` accumulates `∀ z ≤ y, ψ(v, z)` in an extra
relation variable along `succ` from `0` up to `max`. Each original clause then replaces its guard by
`⊤` and prepends the positive root atom of its guard to its body.

## Main definitions

* `Cslib.Logic.ESO.Horn.Sentence.elimGuards`: replace first-order guards by quantifier-free Horn
  clauses using auxiliary relation variables and primitive successor.

## Main results

* `Cslib.Logic.ESO.Horn.Sentence.isQF_elimGuards`: every guard of `Φ.elimGuards` is quantifier-free.
* `Cslib.Logic.ESO.Horn.Sentence.realize_elimGuards`: guard elimination preserves truth on `Fin n`
  for `2 ≤ n`.

## References

* [E. Grädel, *Finite Model Theory and Descriptive Complexity*][Gradel2007], Exercise 3.2.20
  (p. 148): SO∃-Horn sentences with arbitrary first-order guards reduce to the quantifier-free
  variant on ordered structures with successor and endpoint constants; the exercise does not
  consider `BIT`.
* [E. Grädel, *Capturing complexity classes by fragments of second-order logic*][Gradel1992],
  for SO∃-Horn logic on successor structures. Section and theorem locators are unverified.
-/

public section

open FirstOrder Language

namespace Cslib.Logic.ESO.Horn.Sentence

open FO.Ordered

variable {L : Language}

/-! ### Variable lifting and formula opening -/

private def mapAtom {V₁ V₂ : Type} {arity₂ : V₂ → ℕ} (f : V₁ → V₂) {β : Type}
    (a : Atom (arity₂ ∘ f) β) : Atom arity₂ β :=
  ⟨f a.rel, a.args⟩

private def mapClause {L' : Language} {V₁ V₂ : Type} {arity₂ : V₂ → ℕ} (f : V₁ → V₂)
    (C : Clause L' (arity₂ ∘ f)) : Clause L' arity₂ where
  width := C.width
  guard := C.guard
  body := C.body.map (mapAtom f)
  head := C.head.map (mapAtom f)

private theorem holds_mapClause {L' : Language} {M : Type*} [L'.Structure M]
    {V₁ V₂ : Type} {arity₂ : V₂ → ℕ} (f : V₁ → V₂)
    (C : Clause L' (arity₂ ∘ f)) (R : ∀ i, Set (Fin (arity₂ i) → M)) :
    (mapClause f C).Holds R ↔ C.Holds (fun j => R (f j)) := by
  refine forall_congr' fun v => imp_congr_right fun _ => imp_congr ?_ ?_
  · change (∀ a ∈ C.body.map (mapAtom f), a.Holds R v) ↔ _
    rw [List.forall_mem_map]
    rfl
  · change ((C.head.map (mapAtom f)).elim False fun a => a.Holds R v) ↔ _
    cases C.head <;> rfl

/-- Open the bound variables `Fin k` of a bounded formula into free variables `Fin (m + k)`. -/
private def openFormula {L' : Language} {m k : ℕ} (φ : L'.BoundedFormula (Fin m) k) :
    L'.Formula (Fin (m + k)) :=
  φ.toFormula.relabel finSumFinEquiv

private theorem isQF_toFormula {L' : Language} {α : Type*} {k : ℕ}
    {φ : L'.BoundedFormula α k} (h : φ.IsQF) : φ.toFormula.IsQF := by
  induction h with
  | falsum => exact .falsum
  | of_isAtomic h =>
    cases h with
    | equal => exact (BoundedFormula.IsAtomic.equal _ _).isQF
    | rel => exact (BoundedFormula.IsAtomic.rel _ _).isQF
  | imp _ _ ih₁ ih₂ => exact ih₁.imp ih₂

private theorem isQF_openFormula {L' : Language} {m k : ℕ}
    {φ : L'.BoundedFormula (Fin m) k} (h : φ.IsQF) : (openFormula φ).IsQF :=
  (isQF_toFormula h).relabel _

/-- Satisfaction of a subformula `φ` with `m` free variables and `k` bound variables under a flat
assignment `w : Fin (m + k) → M`. -/
private def evalSub {L' : Language} {M : Type*} [L'.Structure M] {m k : ℕ}
    (φ : L'.BoundedFormula (Fin m) k) (w : Fin (m + k) → M) : Prop :=
  φ.Realize (w ∘ Fin.castAdd k) (w ∘ Fin.natAdd m)

private theorem realize_openFormula {L' : Language} {M : Type*} [L'.Structure M] {m k : ℕ}
    (φ : L'.BoundedFormula (Fin m) k) (w : Fin (m + k) → M) :
    (openFormula φ).Realize w ↔ evalSub φ w := by
  rw [openFormula, Formula.realize_relabel, BoundedFormula.realize_toFormula]
  have hl : (w ∘ finSumFinEquiv) ∘ Sum.inl = w ∘ Fin.castAdd k :=
    funext fun i => congrArg w (finSumFinEquiv_apply_left i)
  have hr : (w ∘ finSumFinEquiv) ∘ Sum.inr = w ∘ Fin.natAdd m :=
    funext fun j => congrArg w (finSumFinEquiv_apply_right j)
  rw [hl, hr]
  rfl

private theorem evalSub_zero {L' : Language} {M : Type*} [L'.Structure M] {m : ℕ}
    (φ : L'.Formula (Fin m)) (w : Fin m → M) :
    evalSub (k := 0) φ w ↔ φ.Realize w := by
  have hl : w ∘ Fin.castAdd 0 = w := funext fun _ => rfl
  have hr : w ∘ (Fin.natAdd m : Fin 0 → Fin m) = default := Subsingleton.elim _ _
  change BoundedFormula.Realize φ (w ∘ Fin.castAdd 0) (w ∘ (Fin.natAdd m : Fin 0 → Fin m)) ↔
    BoundedFormula.Realize φ w default
  rw [hl, hr]

private theorem evalSub_imp {L' : Language} {M : Type*} [L'.Structure M] {m k : ℕ}
    (φ₁ φ₂ : L'.BoundedFormula (Fin m) k) (w : Fin (m + k) → M) :
    evalSub (φ₁.imp φ₂) w ↔ (evalSub φ₁ w → evalSub φ₂ w) :=
  BoundedFormula.realize_imp

private theorem evalSub_all {L' : Language} {M : Type*} [L'.Structure M] {m k : ℕ}
    (ψ : L'.BoundedFormula (Fin m) (k + 1)) (w : Fin (m + k) → M) :
    evalSub ψ.all w ↔ ∀ y : M, evalSub ψ (Fin.snoc w y) := by
  rw [evalSub, BoundedFormula.realize_all]
  refine forall_congr' fun y => ?_
  have hl : (Fin.snoc w y : Fin (m + k + 1) → M) ∘ Fin.castAdd (k + 1) = w ∘ Fin.castAdd k := by
    funext i
    have hi : Fin.castAdd (k + 1) i = Fin.castSucc (Fin.castAdd k i) := Fin.ext rfl
    rw [Function.comp_apply, hi, Fin.snoc_castSucc, Function.comp_apply]
  have hr : (Fin.snoc w y : Fin (m + k + 1) → M) ∘ Fin.natAdd m =
      Fin.snoc (w ∘ Fin.natAdd m) y := by
    funext j
    refine Fin.lastCases ?_ (fun j₀ => ?_) j
    · have hj : Fin.natAdd m (Fin.last k) = Fin.last (m + k) := Fin.ext rfl
      rw [Function.comp_apply, hj, Fin.snoc_last, Fin.snoc_last]
    · have hj : Fin.natAdd m (Fin.castSucc j₀) = Fin.castSucc (Fin.natAdd m j₀) := Fin.ext rfl
      rw [Function.comp_apply, hj, Fin.snoc_castSucc, Fin.snoc_castSucc, Function.comp_apply]
  change _ ↔ ψ.Realize ((Fin.snoc w y) ∘ Fin.castAdd (k + 1)) ((Fin.snoc w y) ∘ Fin.natAdd m)
  rw [hl, hr]

/-! ### Auxiliary relation variables and clauses per guard subformula -/

/-- Strict-subformula auxiliary variables of `φ`: empty at atoms, disjoint sums at implications,
and one prefix-accumulator variable `Unit` plus the child's variables at universal quantifiers. -/
private def InnerVar {L' : Language} {m : ℕ} :
    ∀ {k : ℕ}, L'.BoundedFormula (Fin m) k → Type
  | _, .falsum => Empty
  | _, .equal _ _ => Empty
  | _, .rel _ _ => Empty
  | _, .imp φ₁ φ₂ => (Bool ⊕ InnerVar φ₁) ⊕ (Bool ⊕ InnerVar φ₂)
  | _, .all ψ => Unit ⊕ (Bool ⊕ InnerVar ψ)

/-- All auxiliary variables of `φ`: `Sum.inl true` is `pos_φ`, `Sum.inl false` is `neg_φ`, and
`Sum.inr` ranges over `InnerVar φ`. -/
private abbrev AuxVar {L' : Language} {m k : ℕ} (φ : L'.BoundedFormula (Fin m) k) : Type :=
  Bool ⊕ InnerVar φ

private instance instFiniteInnerVar {L' : Language} {m : ℕ} :
    ∀ {k : ℕ} (φ : L'.BoundedFormula (Fin m) k), Finite (InnerVar φ)
  | _, .falsum => inferInstanceAs (Finite Empty)
  | _, .equal _ _ => inferInstanceAs (Finite Empty)
  | _, .rel _ _ => inferInstanceAs (Finite Empty)
  | _, .imp φ₁ φ₂ =>
    letI := instFiniteInnerVar φ₁
    letI := instFiniteInnerVar φ₂
    inferInstanceAs (Finite ((Bool ⊕ InnerVar φ₁) ⊕ (Bool ⊕ InnerVar φ₂)))
  | _, .all ψ =>
    letI := instFiniteInnerVar ψ
    inferInstanceAs (Finite (Unit ⊕ (Bool ⊕ InnerVar ψ)))

private def innerArity {L' : Language} {m : ℕ} :
    ∀ {k : ℕ} (φ : L'.BoundedFormula (Fin m) k), InnerVar φ → ℕ
  | _, .falsum => Empty.elim
  | _, .equal _ _ => Empty.elim
  | _, .rel _ _ => Empty.elim
  | k, .imp φ₁ φ₂ =>
    Sum.elim (Sum.elim (fun _ => m + k) (innerArity φ₁))
      (Sum.elim (fun _ => m + k) (innerArity φ₂))
  | k, .all ψ =>
    Sum.elim (fun _ => m + k + 1) (Sum.elim (fun _ => m + (k + 1)) (innerArity ψ))

private def auxArity {L' : Language} {m k : ℕ} (φ : L'.BoundedFormula (Fin m) k) :
    AuxVar φ → ℕ :=
  Sum.elim (fun _ => m + k) (innerArity φ)

/-- In a step clause of width `N + 2` representing `(v, y, y')`, pick out `(v, y')`. -/
private def stepRightArg (N : ℕ) : Fin (N + 1) → Fin (N + 2) :=
  Fin.lastCases (Fin.last (N + 1)) (Fin.castSucc ∘ Fin.castSucc)

private theorem comp_stepRightArg {M : Type*} {N : ℕ} (u : Fin (N + 2) → M) :
    u ∘ stepRightArg N =
      Fin.snoc (fun i => u (Fin.castSucc (Fin.castSucc i))) (u (Fin.last (N + 1))) := by
  funext p
  refine Fin.lastCases ?_ (fun i => ?_) p
  · simp only [Function.comp_apply, stepRightArg, Fin.lastCases_last, Fin.snoc_last]
  · simp only [Function.comp_apply, stepRightArg, Fin.lastCases_castSucc, Fin.snoc_castSucc]

/-- Definite clauses for a quantifier-free base case `φ`: `openFormula φ → pos_φ` and
`∼openFormula φ → neg_φ`. -/
private def qfAuxClauses {L' : Language} {m k : ℕ} (φ : L'.BoundedFormula (Fin m) k) :
    List (Clause L' (auxArity φ)) :=
  [ { width := m + k
      guard := openFormula φ
      body := []
      head := some ⟨.inl true, id⟩ },
    { width := m + k
      guard := (openFormula φ).not
      body := []
      head := some ⟨.inl false, id⟩ } ]

/-- Definite clauses computing `pos_φ` and `neg_φ` for every subformula `φ` on a successor
structure. -/
private noncomputable def auxClauses {m : ℕ} :
    ∀ {k : ℕ} (φ : (language (succLanguage L)).BoundedFormula (Fin m) k),
      List (Clause (language (succLanguage L)) (auxArity φ))
  | _, .falsum => qfAuxClauses .falsum
  | _, .equal t₁ t₂ => qfAuxClauses (.equal t₁ t₂)
  | _, .rel R ts => qfAuxClauses (.rel R ts)
  | k, .imp φ₁ φ₂ =>
    let left : AuxVar φ₁ → AuxVar (.imp φ₁ φ₂) := Sum.inr ∘ Sum.inl
    let right : AuxVar φ₂ → AuxVar (.imp φ₁ φ₂) := Sum.inr ∘ Sum.inr
    (auxClauses φ₁).map (mapClause left) ++
      (auxClauses φ₂).map (mapClause right) ++
      [ { width := m + k
          guard := ⊤
          body := [⟨left (.inl false), id⟩]
          head := some ⟨.inl true, id⟩ },
        { width := m + k
          guard := ⊤
          body := [⟨right (.inl true), id⟩]
          head := some ⟨.inl true, id⟩ },
        { width := m + k
          guard := ⊤
          body := [⟨left (.inl true), id⟩, ⟨right (.inl false), id⟩]
          head := some ⟨.inl false, id⟩ } ]
  | k, .all ψ =>
    let N := m + k
    let child : AuxVar ψ → AuxVar (.all ψ) := Sum.inr ∘ Sum.inr
    let accVar : AuxVar (.all ψ) := .inr (.inl ())
    (auxClauses ψ).map (mapClause child) ++
      [ { width := N + 1
          guard := ⊤
          body := [⟨child (.inl false), id⟩]
          head := some ⟨.inl false, Fin.castSucc⟩ },
        { width := N + 1
          guard := Term.equal (.var (Fin.last N)) (zero (succLanguage L))
          body := [⟨child (.inl true), id⟩]
          head := some ⟨accVar, id⟩ },
        { width := N + 2
          guard := succ L (.var (Fin.castSucc (Fin.last N))) (.var (Fin.last (N + 1)))
          body := [⟨accVar, Fin.castSucc⟩, ⟨child (.inl true), stepRightArg N⟩]
          head := some ⟨accVar, stepRightArg N⟩ },
        { width := N + 1
          guard := Term.equal (.var (Fin.last N)) (max (succLanguage L))
          body := [⟨accVar, id⟩]
          head := some ⟨.inl true, Fin.castSucc⟩ } ]

private theorem isQF_qfAuxClauses {L' : Language} {m k : ℕ}
    {φ : L'.BoundedFormula (Fin m) k} (hφ : φ.IsQF) :
    ∀ C ∈ qfAuxClauses φ, C.guard.IsQF := by
  simp only [qfAuxClauses, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true]
  exact ⟨isQF_openFormula hφ, (isQF_openFormula hφ).not⟩

private theorem isQF_auxClauses {m : ℕ} :
    ∀ {k : ℕ} (φ : (language (succLanguage L)).BoundedFormula (Fin m) k),
      ∀ C ∈ auxClauses φ, C.guard.IsQF
  | _, .falsum => isQF_qfAuxClauses .falsum
  | _, .equal t₁ t₂ => isQF_qfAuxClauses (BoundedFormula.IsAtomic.equal t₁ t₂).isQF
  | _, .rel R ts => isQF_qfAuxClauses (BoundedFormula.IsAtomic.rel R ts).isQF
  | _, .imp φ₁ φ₂ => by
    intro C hC
    rcases List.mem_append.mp hC with hC | hC
    · rcases List.mem_append.mp hC with hC | hC
      · obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.mp hC
        exact isQF_auxClauses φ₁ C₀ hC₀
      · obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.mp hC
        exact isQF_auxClauses φ₂ C₀ hC₀
    · rcases List.mem_cons.mp hC with rfl | hC
      · exact .top
      · rcases List.mem_cons.mp hC with rfl | hC
        · exact .top
        · obtain rfl := List.mem_singleton.mp hC
          exact .top
  | _, .all ψ => by
    intro C hC
    rcases List.mem_append.mp hC with hC | hC
    · obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.mp hC
      exact isQF_auxClauses ψ C₀ hC₀
    · rcases List.mem_cons.mp hC with rfl | hC
      · exact .top
      · rcases List.mem_cons.mp hC with rfl | hC
        · exact (BoundedFormula.IsAtomic.equal _ _).isQF
        · rcases List.mem_cons.mp hC with rfl | hC
          · exact isQF_succ L _ _
          · obtain rfl := List.mem_singleton.mp hC
            exact (BoundedFormula.IsAtomic.equal _ _).isQF

/-! ### Soundness and completeness of the auxiliary clauses -/

section Semantics

variable {n : ℕ} [Fact (2 ≤ n)] [L.Structure (Fin n)] {m : ℕ}

private def rootTarget {k : ℕ} (φ : (language (succLanguage L)).BoundedFormula (Fin m) k) :
    Bool → Set (Fin (m + k) → Fin n)
  | true => {w | evalSub φ w}
  | false => {w | ¬ evalSub φ w}

private def innerTarget :
    ∀ {k : ℕ} (φ : (language (succLanguage L)).BoundedFormula (Fin m) k) (v : InnerVar φ),
      Set (Fin (innerArity φ v) → Fin n)
  | _, .falsum, v => Empty.elim v
  | _, .equal _ _, v => Empty.elim v
  | _, .rel _ _, v => Empty.elim v
  | _, .imp φ₁ φ₂, v =>
    match v with
    | Sum.inl v₁ =>
      match v₁ with
      | Sum.inl b => rootTarget φ₁ b
      | Sum.inr w₁ => innerTarget φ₁ w₁
    | Sum.inr v₂ =>
      match v₂ with
      | Sum.inl b => rootTarget φ₂ b
      | Sum.inr w₂ => innerTarget φ₂ w₂
  | k, .all ψ, v =>
    match v with
    | Sum.inl () =>
      {u : Fin (m + k + 1) → Fin n |
        ∀ z : Fin n, z ≤ u (Fin.last (m + k)) → evalSub ψ (Fin.snoc (u ∘ Fin.castSucc) z)}
    | Sum.inr v₀ =>
      match v₀ with
      | Sum.inl b => rootTarget ψ b
      | Sum.inr w₀ => innerTarget ψ w₀

private def auxTarget {k : ℕ} (φ : (language (succLanguage L)).BoundedFormula (Fin m) k)
    (v : AuxVar φ) : Set (Fin (auxArity φ v) → Fin n) :=
  match v with
  | .inl b => rootTarget φ b
  | .inr v => innerTarget φ v

private theorem holds_qfAuxClauses_target {k : ℕ}
    (φ : (language (succLanguage L)).BoundedFormula (Fin m) k) :
    ∀ C ∈ qfAuxClauses φ, C.Holds (auxTarget (n := n) φ) := by
  simp only [qfAuxClauses, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true]
  refine ⟨fun w hg _ => ?_, fun w hg _ => ?_⟩
  · exact (realize_openFormula φ w).mp hg
  · rw [Formula.realize_not, realize_openFormula] at hg
    exact hg

/-- The intended extensions `auxTarget φ` satisfy all auxiliary clauses of `φ`. -/
private theorem holds_auxClauses_auxTarget :
    ∀ {k : ℕ} (φ : (language (succLanguage L)).BoundedFormula (Fin m) k),
      ∀ C ∈ auxClauses φ, C.Holds (auxTarget (n := n) φ)
  | _, .falsum => holds_qfAuxClauses_target .falsum
  | _, .equal t₁ t₂ => holds_qfAuxClauses_target (.equal t₁ t₂)
  | _, .rel R ts => holds_qfAuxClauses_target (.rel R ts)
  | _, .imp φ₁ φ₂ => by
    intro C hC
    rcases List.mem_append.mp hC with hC | hC
    · rcases List.mem_append.mp hC with hC | hC
      · obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.mp hC
        refine (holds_mapClause _ C₀ _).mpr ?_
        have heq : auxTarget (n := n) φ₁ =
            (fun j => auxTarget (n := n) (.imp φ₁ φ₂) (.inr (.inl j))) := by
          funext j
          cases j <;> rfl
        exact heq ▸ holds_auxClauses_auxTarget φ₁ C₀ hC₀
      · obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.mp hC
        refine (holds_mapClause _ C₀ _).mpr ?_
        have heq : auxTarget (n := n) φ₂ =
            (fun j => auxTarget (n := n) (.imp φ₁ φ₂) (.inr (.inr j))) := by
          funext j
          cases j <;> rfl
        exact heq ▸ holds_auxClauses_auxTarget φ₂ C₀ hC₀
    · rcases List.mem_cons.mp hC with rfl | hC
      · intro w _ hb
        have h₁ : ¬ evalSub φ₁ w := hb _ (List.mem_singleton.mpr rfl)
        change evalSub (φ₁.imp φ₂) w
        exact (evalSub_imp φ₁ φ₂ w).mpr fun hp => False.elim (h₁ hp)
      · rcases List.mem_cons.mp hC with rfl | hC
        · intro w _ hb
          have h₂ : evalSub φ₂ w := hb _ (List.mem_singleton.mpr rfl)
          change evalSub (φ₁.imp φ₂) w
          exact (evalSub_imp φ₁ φ₂ w).mpr fun _ => h₂
        · obtain rfl := List.mem_singleton.mp hC
          intro w _ hb
          have h₁ : evalSub φ₁ w := hb _ List.mem_cons_self
          have h₂ : ¬ evalSub φ₂ w := hb _ (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))
          change ¬ evalSub (φ₁.imp φ₂) w
          rw [evalSub_imp]
          exact fun himp => h₂ (himp h₁)
  | k, .all ψ => by
    intro C hC
    rcases List.mem_append.mp hC with hC | hC
    · obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.mp hC
      refine (holds_mapClause _ C₀ _).mpr ?_
      have heq : auxTarget (n := n) ψ =
          (fun j => auxTarget (n := n) (.all ψ) (.inr (.inr j))) := by
        funext j
        cases j <;> rfl
      exact heq ▸ holds_auxClauses_auxTarget ψ C₀ hC₀
    · rcases List.mem_cons.mp hC with rfl | hC
      · intro u _ hb
        have hψ : ¬ evalSub ψ u := hb _ (List.mem_singleton.mpr rfl)
        change ¬ evalSub ψ.all (u ∘ Fin.castSucc)
        rw [evalSub_all]
        intro hall
        have hu : Fin.snoc (u ∘ Fin.castSucc) (u (Fin.last (m + k))) = u := Fin.snoc_init_self u
        rw [← hu] at hψ
        exact hψ (hall _)
      · rcases List.mem_cons.mp hC with rfl | hC
        · dsimp only [Clause.Holds, Option.elim]
          intro u hg hb z hz
          change z ≤ u (Fin.last (m + k)) at hz
          have hψ : evalSub ψ u := hb _ (List.mem_singleton.mpr rfl)
          rw [Formula.realize_equal, Term.realize_var, Fin.ext_iff, realize_zero_val] at hg
          have hzeq : z = u (Fin.last (m + k)) := by
            apply Fin.ext
            rw [Fin.le_def, hg] at hz
            omega
          change evalSub ψ (Fin.snoc (u ∘ Fin.castSucc) z)
          rw [hzeq, show Fin.snoc (u ∘ Fin.castSucc) (u (Fin.last (m + k))) = u from
            Fin.snoc_init_self u]
          exact hψ
        · rcases List.mem_cons.mp hC with rfl | hC
          · dsimp only [Clause.Holds, Option.elim]
            intro u hg hb z hz
            change z ≤ (u ∘ stepRightArg (m + k)) (Fin.last (m + k)) at hz
            have hacc : ∀ z' : Fin n, z' ≤ u (Fin.castSucc (Fin.last (m + k))) →
                evalSub ψ (Fin.snoc ((u ∘ Fin.castSucc) ∘ Fin.castSucc) z') :=
              hb _ List.mem_cons_self
            have hψ : evalSub ψ (u ∘ stepRightArg (m + k)) :=
              hb _ (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))
            rw [realize_succ, Term.realize_var, Term.realize_var] at hg
            have hlast : (u ∘ stepRightArg (m + k)) (Fin.last (m + k)) =
                u (Fin.last (m + k + 1)) := by
              simp only [Function.comp_apply, stepRightArg, Fin.lastCases_last]
            have hinit : (u ∘ stepRightArg (m + k)) ∘ Fin.castSucc =
                fun i => u (Fin.castSucc (Fin.castSucc i)) := by
              funext i
              simp only [Function.comp_apply, stepRightArg, Fin.lastCases_castSucc]
            rw [hlast] at hz
            change evalSub ψ (Fin.snoc ((u ∘ stepRightArg (m + k)) ∘ Fin.castSucc) z)
            rw [hinit]
            have hz' : z.val ≤ (u (Fin.castSucc (Fin.last (m + k)))).val + 1 := by
              rw [Fin.le_def, ← hg] at hz
              exact hz
            rcases Nat.le_or_eq_of_le_succ hz' with hle | heq
            · exact hacc z hle
            · have hzeq : z = u (Fin.last (m + k + 1)) := Fin.ext (heq.trans hg)
              rw [hzeq, ← comp_stepRightArg u]
              exact hψ
          · obtain rfl := List.mem_singleton.mp hC
            intro u hg hb
            have hacc : ∀ z : Fin n, z ≤ u (Fin.last (m + k)) →
                evalSub ψ (Fin.snoc (u ∘ Fin.castSucc) z) :=
              hb _ (List.mem_singleton.mpr rfl)
            rw [Formula.realize_equal, Term.realize_var, Fin.ext_iff, realize_max_val] at hg
            change evalSub ψ.all (u ∘ Fin.castSucc)
            rw [evalSub_all]
            intro z
            refine hacc z ?_
            rw [Fin.le_def, hg]
            have hz := z.isLt
            omega

private theorem qfAuxClauses_complete {k : ℕ}
    {φ : (language (succLanguage L)).BoundedFormula (Fin m) k}
    {R : ∀ v, Set (Fin (auxArity φ v) → Fin n)}
    (hR : ∀ C ∈ qfAuxClauses φ, C.Holds R) (b : Bool) :
    rootTarget φ b ≤ R (.inl b) := by
  simp only [qfAuxClauses, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true] at hR
  obtain ⟨hpos, hneg⟩ := hR
  cases b
  · intro w hw
    exact hneg w (by rw [Formula.realize_not, realize_openFormula]; exact hw)
      (by simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true])
  · intro w hw
    exact hpos w ((realize_openFormula φ w).mpr hw)
      (by simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true])

/-- Every relation family closed under `auxClauses φ` contains `rootTarget φ` at the root
variables `Sum.inl b`. -/
private theorem rootTarget_le_of_holds_auxClauses :
    ∀ {k : ℕ} (φ : (language (succLanguage L)).BoundedFormula (Fin m) k)
      {R : ∀ v, Set (Fin (auxArity φ v) → Fin n)},
      (∀ C ∈ auxClauses φ, C.Holds R) → ∀ b, rootTarget φ b ≤ R (.inl b)
  | _, .falsum, _, hR => qfAuxClauses_complete (by rw [auxClauses] at hR; exact hR)
  | _, .equal _ _, _, hR => qfAuxClauses_complete (by rw [auxClauses] at hR; exact hR)
  | _, .rel _ _, _, hR => qfAuxClauses_complete (by rw [auxClauses] at hR; exact hR)
  | _, .imp φ₁ φ₂, R, hR => by
    rw [auxClauses] at hR
    have h₁ : ∀ C ∈ auxClauses φ₁, C.Holds (fun v => R (.inr (.inl v))) := fun C hC =>
      (holds_mapClause (Sum.inr ∘ Sum.inl) C R).mp <|
        hR _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hC)))
    have h₂ : ∀ C ∈ auxClauses φ₂, C.Holds (fun v => R (.inr (.inr v))) := fun C hC =>
      (holds_mapClause (Sum.inr ∘ Sum.inr) C R).mp <|
        hR _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hC)))
    have ih₁ := rootTarget_le_of_holds_auxClauses φ₁ h₁
    have ih₂ := rootTarget_le_of_holds_auxClauses φ₂ h₂
    have hc₁ := hR _ (List.mem_append_right _ List.mem_cons_self)
    have hc₂ := hR _ (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))
    have hc₃ := hR _ (List.mem_append_right _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    intro b w hw
    cases b
    · change ¬ evalSub (φ₁.imp φ₂) w at hw
      rw [evalSub_imp, Classical.not_imp] at hw
      exact hc₃ w (Formula.realize_top.mpr trivial) (by
        simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
          and_true]
        exact ⟨ih₁ true hw.1, ih₂ false hw.2⟩)
    · change evalSub (φ₁.imp φ₂) w at hw
      rw [evalSub_imp] at hw
      by_cases hp : evalSub φ₁ w
      · exact hc₂ w (Formula.realize_top.mpr trivial) (by
          simp only [List.forall_mem_singleton]
          exact ih₂ true (hw hp))
      · exact hc₁ w (Formula.realize_top.mpr trivial) (by
          simp only [List.forall_mem_singleton]
          exact ih₁ false hp)
  | k, .all ψ, R, hR => by
    rw [auxClauses] at hR
    have hψ : ∀ C ∈ auxClauses ψ, C.Holds (fun v => R (.inr (.inr v))) := fun C hC =>
      (holds_mapClause (Sum.inr ∘ Sum.inr) C R).mp <|
        hR _ (List.mem_append_left _ (List.mem_map_of_mem hC))
    have ih := rootTarget_le_of_holds_auxClauses ψ hψ
    have hneg := hR _ (List.mem_append_right _ List.mem_cons_self)
    have hbase := hR _ (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))
    have hstep := hR _ (List.mem_append_right _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    have hmax := hR _ (List.mem_append_right _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
    intro b w hw
    cases b
    · change ¬ evalSub ψ.all w at hw
      rw [evalSub_all, not_forall] at hw
      obtain ⟨y, hy⟩ := hw
      have hu := hneg (Fin.snoc w y) (Formula.realize_top.mpr trivial) (by
        simp only [List.forall_mem_singleton]
        exact ih false hy)
      change (Fin.snoc w y) ∘ Fin.castSucc ∈ R (.inl false) at hu
      rwa [show (Fin.snoc w y) ∘ Fin.castSucc = w from
        funext fun _ => Fin.snoc_castSucc _ _ _] at hu
    · change evalSub ψ.all w at hw
      rw [evalSub_all] at hw
      have hacc : ∀ (j : ℕ) (hj : j < n),
          Fin.snoc w ⟨j, hj⟩ ∈ R (.inr (.inl ())) := by
        intro j
        induction j with
        | zero =>
          intro hj
          exact hbase (Fin.snoc w ⟨0, hj⟩)
            (by rw [Formula.realize_equal, Term.realize_var, Fin.snoc_last, Fin.ext_iff,
                  realize_zero_val])
            (by simp only [List.forall_mem_singleton]
                exact ih true (hw ⟨0, hj⟩))
        | succ j ihj =>
          intro hj
          have hj₀ : j < n := Nat.lt_of_succ_lt hj
          let u : Fin (m + k + 2) → Fin n := Fin.snoc (Fin.snoc w ⟨j, hj₀⟩) ⟨j + 1, hj⟩
          have hgu : (succ L (.var (Fin.castSucc (Fin.last (m + k))))
              (.var (Fin.last (m + k + 1)))).Realize u := by
            rw [realize_succ, Term.realize_var, Term.realize_var]
            simp only [u, Fin.snoc_last, Fin.snoc_castSucc]
          have hleft : u ∘ Fin.castSucc = Fin.snoc w ⟨j, hj₀⟩ := by
            funext i
            exact Fin.snoc_castSucc (α := fun _ => Fin n) ⟨j + 1, hj⟩ (Fin.snoc w ⟨j, hj₀⟩) i
          have hright : u ∘ stepRightArg (m + k) = Fin.snoc w ⟨j + 1, hj⟩ := by
            rw [comp_stepRightArg]
            simp only [u, Fin.snoc_last, Fin.snoc_castSucc]
          have hu := hstep u hgu (by
            simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
              and_true]
            refine ⟨?_, ?_⟩
            · change u ∘ Fin.castSucc ∈ R (.inr (.inl ()))
              rw [hleft]
              exact ihj hj₀
            · change u ∘ stepRightArg (m + k) ∈ R (.inr (.inr (.inl true)))
              rw [hright]
              exact ih true (hw ⟨j + 1, hj⟩))
          change u ∘ stepRightArg (m + k) ∈ R (.inr (.inl ())) at hu
          rwa [hright] at hu
      have hn : 2 ≤ n := Fact.out
      let ymax : Fin n := ⟨n - 1, by omega⟩
      have humax := hmax (Fin.snoc w ymax)
        (by rw [Formula.realize_equal, Term.realize_var, Fin.snoc_last, Fin.ext_iff,
              realize_max_val])
        (by simp only [List.forall_mem_singleton]
            exact hacc (n - 1) ymax.isLt)
      change (Fin.snoc w ymax) ∘ Fin.castSucc ∈ R (.inl true) at humax
      rwa [show (Fin.snoc w ymax) ∘ Fin.castSucc = w from
        funext fun _ => Fin.snoc_castSucc _ _ _] at humax

end Semantics

/-! ### Sentence-level guard elimination -/

private abbrev ElimVar (Φ : Sentence (language (succLanguage L))) : Type :=
  Φ.Var ⊕ Σ idx : Fin Φ.clauses.length, AuxVar (Φ.clauses.get idx).guard

private def elimArity (Φ : Sentence (language (succLanguage L))) : ElimVar Φ → ℕ :=
  Sum.elim Φ.arity fun ⟨idx, v⟩ => auxArity (Φ.clauses.get idx).guard v

private noncomputable def elimClauseAt (Φ : Sentence (language (succLanguage L)))
    (idx : Fin Φ.clauses.length) : Clause (language (succLanguage L)) (elimArity Φ) where
  width := (Φ.clauses.get idx).width
  guard := ⊤
  body := ⟨.inr ⟨idx, .inl true⟩, id⟩ :: (Φ.clauses.get idx).body.map (mapAtom Sum.inl)
  head := (Φ.clauses.get idx).head.map (mapAtom Sum.inl)

private noncomputable def elimClausesList (Φ : Sentence (language (succLanguage L))) :
    List (Clause (language (succLanguage L)) (elimArity Φ)) :=
  (List.finRange Φ.clauses.length).flatMap fun idx =>
    (auxClauses (Φ.clauses.get idx).guard).map (mapClause fun v => .inr ⟨idx, v⟩) ++
      [elimClauseAt Φ idx]

/-- Eliminate quantifiers from all guards of an SO∃-Horn sentence over
`language (succLanguage L)`, introducing finitely many auxiliary relation variables and iterating
universal quantifiers along `succ` from `0` to `max`. -/
noncomputable def elimGuards (Φ : Sentence (language (succLanguage L))) :
    Sentence (language (succLanguage L)) where
  Var := ElimVar Φ
  arity := elimArity Φ
  clauses := elimClausesList Φ

private theorem mem_elimClausesList {Φ : Sentence (language (succLanguage L))}
    {C : Clause (language (succLanguage L)) (elimArity Φ)} :
    C ∈ elimClausesList Φ ↔
      ∃ idx : Fin Φ.clauses.length,
        (∃ D ∈ auxClauses (Φ.clauses.get idx).guard,
          mapClause (fun v => .inr ⟨idx, v⟩) D = C) ∨ C = elimClauseAt Φ idx := by
  simp only [elimClausesList, List.mem_flatMap, List.mem_finRange, true_and, List.mem_append,
    List.mem_singleton]
  exact exists_congr fun _ => or_congr List.mem_map Iff.rfl

private theorem holds_elimClauseAt {n : ℕ} [Fact (2 ≤ n)] [L.Structure (Fin n)]
    (Φ : Sentence (language (succLanguage L))) (idx : Fin Φ.clauses.length)
    (R : ∀ j : ElimVar Φ, Set (Fin (elimArity Φ j) → Fin n)) :
    (elimClauseAt Φ idx).Holds R ↔
      ∀ w : Fin (Φ.clauses.get idx).width → Fin n,
        w ∈ R (.inr ⟨idx, .inl true⟩) →
        (∀ a ∈ (Φ.clauses.get idx).body, a.Holds (fun i => R (.inl i)) w) →
        (Φ.clauses.get idx).head.elim False (fun a => a.Holds (fun i => R (.inl i)) w) := by
  constructor
  · intro hcl w hw hb
    have hbody : ∀ a ∈ (elimClauseAt Φ idx).body, a.Holds R w := by
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hw
      · obtain ⟨b, hb', rfl⟩ := List.mem_map.mp ha
        exact hb b hb'
    have hhead := hcl w (Formula.realize_top.mpr trivial) hbody
    change ((Φ.clauses.get idx).head.map (mapAtom (arity₂ := elimArity Φ) Sum.inl)).elim False
      (fun a => a.Holds R w) at hhead
    revert hhead
    cases (Φ.clauses.get idx).head <;> exact id
  · intro hcl w _ hb
    have hw : w ∈ R (.inr ⟨idx, .inl true⟩) := hb _ List.mem_cons_self
    have hbody : ∀ b ∈ (Φ.clauses.get idx).body, b.Holds (fun i => R (.inl i)) w :=
      fun b hb' => hb _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hb'))
    have hhead := hcl w hw hbody
    change ((Φ.clauses.get idx).head.map (mapAtom (arity₂ := elimArity Φ) Sum.inl)).elim False
      (fun a => a.Holds R w)
    revert hhead
    cases (Φ.clauses.get idx).head <;> exact id

/-- Every guard of `Φ.elimGuards` is quantifier-free. -/
theorem isQF_elimGuards (Φ : Sentence (language (succLanguage L))) : Φ.elimGuards.IsQF := by
  intro C hC
  change C ∈ elimClausesList Φ at hC
  obtain ⟨idx, ⟨C₀, hC₀, rfl⟩ | rfl⟩ := mem_elimClausesList.mp hC
  · exact isQF_auxClauses (Φ.clauses.get idx).guard C₀ hC₀
  · exact .top

/-- **Guard elimination preserves truth** on canonical ordered successor structures `Fin n` with
`2 ≤ n`. -/
theorem realize_elimGuards {n : ℕ} [Fact (2 ≤ n)] [L.Structure (Fin n)]
    (Φ : Sentence (language (succLanguage L))) :
    Φ.elimGuards.Realize (Fin n) ↔ Φ.Realize (Fin n) := by
  constructor
  · rintro ⟨R', hR'⟩
    let R₀ : ∀ j : ElimVar Φ, Set (Fin (elimArity Φ j) → Fin n) := R'
    refine ⟨fun i => R₀ (.inl i), fun C hC => ?_⟩
    obtain ⟨idx, rfl⟩ := List.mem_iff_get.mp hC
    have haux : ∀ D ∈ auxClauses (Φ.clauses.get idx).guard,
        D.Holds (fun v => R₀ (.inr ⟨idx, v⟩)) := fun D hD =>
      (holds_mapClause (fun v => Sum.inr ⟨idx, v⟩) D R₀).mp
        (hR' _ (mem_elimClausesList.mpr ⟨idx, .inl ⟨D, hD, rfl⟩⟩))
    have hroot := rootTarget_le_of_holds_auxClauses (Φ.clauses.get idx).guard haux true
    have hcl : (elimClauseAt Φ idx).Holds R₀ :=
      hR' _ (mem_elimClausesList.mpr ⟨idx, .inr rfl⟩)
    intro w hg hb
    exact (holds_elimClauseAt Φ idx R₀).mp hcl w
      (hroot ((evalSub_zero (Φ.clauses.get idx).guard w).mpr hg)) hb
  · rintro ⟨R, hR⟩
    let R' : ∀ j : ElimVar Φ, Set (Fin (elimArity Φ j) → Fin n) := fun
      | .inl i => R i
      | .inr ⟨idx, v⟩ => auxTarget (n := n) (Φ.clauses.get idx).guard v
    refine ⟨R', fun C hC => ?_⟩
    change C ∈ elimClausesList Φ at hC
    obtain ⟨idx, ⟨D, hD, rfl⟩ | rfl⟩ := mem_elimClausesList.mp hC
    · exact (holds_mapClause (fun v => Sum.inr ⟨idx, v⟩) D R').mpr
        (holds_auxClauses_auxTarget (Φ.clauses.get idx).guard D hD)
    · refine (holds_elimClauseAt Φ idx R').mpr fun w hroot hbody => ?_
      exact hR (Φ.clauses.get idx) (List.get_mem _ _) w
        ((evalSub_zero (Φ.clauses.get idx).guard w).mp hroot) hbody

end Cslib.Logic.ESO.Horn.Sentence
