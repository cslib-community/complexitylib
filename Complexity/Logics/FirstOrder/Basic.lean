/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Tactic.FirstOrder.Init
public import Mathlib.ModelTheory.Semantics
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# First-order formula and sentence combinators

This file provides reusable first-order formula and sentence combinators over `FirstOrder.Language`:
* universal and existential closure (`FO.closeAll`, `FO.closeEx`) over finite free-variable types,
* variable relabeling, equality, and unary/binary relation application (`FO.atVar`, `FO.varEq`,
  `FO.rel₁`, `FO.rel₂`),
* order-theoretic formulas (`FO.lt`, `FO.le`, `FO.isZero`, `FO.isMax`, `FO.succ`, `FO.isFirstOut`)
  with respect to a binary relation symbol interpreted as `<` on `Fin B`, and
* finite-domain cardinality sentences (`FO.cardEqSentence`, built from `Sentence.cardGe`) and finite
  Boolean combinations of sentences (`FO.truthTableSentence`).

## Main definitions

* `Cslib.Logic.FO.closeAll`, `Cslib.Logic.FO.closeEx`: universal and existential closure of a
  first-order formula over a finite type of free variables.
* `Cslib.Logic.FO.atVar`, `Cslib.Logic.FO.varEq`, `Cslib.Logic.FO.rel₁`, `Cslib.Logic.FO.rel₂`:
  atomic formula combinators.
* `Cslib.Logic.FO.lt`, `Cslib.Logic.FO.le`, `Cslib.Logic.FO.isZero`, `Cslib.Logic.FO.isMax`,
  `Cslib.Logic.FO.succ`, `Cslib.Logic.FO.isFirstOut`: order formulas on `Fin B`.
* `Cslib.Logic.FO.cardEqSentence`: sentence asserting `Nat.card M = n` on finite structures.
* `Cslib.Logic.FO.truthTableSentence`: finite Boolean combination of sentences indexed by `Fin m`.

## Main results

* `Cslib.Logic.FO.realize_closeAll`, `Cslib.Logic.FO.realize_closeEx`: satisfaction of universal and
  existential closures.
* `Cslib.Logic.FO.realize_isZero`, `Cslib.Logic.FO.realize_isMax`, `Cslib.Logic.FO.realize_succ`,
  `Cslib.Logic.FO.realize_isFirstOut`: satisfaction of order formulas on `Fin B`.
* `Cslib.Logic.FO.realize_cardGe_iff_le_card`, `Cslib.Logic.FO.realize_cardEqSentence`:
  characterizations of `Sentence.cardGe` and `cardEqSentence` via `Nat.card` on finite structures.
* `Cslib.Logic.FO.realize_truthTableSentence`: satisfaction of `truthTableSentence`.
* `Cslib.Logic.FO.relMap_pair_equiv`, `Cslib.Logic.FO.relMap_single_equiv`: isomorphisms preserve
  binary and unary relations.

## References

* [R. Fagin, *Generalized first-order spectra and polynomial-time recognizable sets*][Fagin1974]
* [N. Immerman, *Descriptive Complexity*][Immerman1999]
-/

@[expose] public section

universe u v w

open FirstOrder Language Structure BoundedFormula

namespace Cslib.Logic.FO

variable {L : Language.{u, v}}

/-! ### Closure and atomic combinators -/

/-- Universal closure of a formula over a finite type of free variables. -/
noncomputable def closeAll (V : Type) [Finite V] (φ : L.Formula V) : L.Sentence :=
  Formula.iAlls V (φ.relabel Sum.inr)

/-- Existential closure of a formula over a finite type of free variables. -/
noncomputable def closeEx (V : Type) [Finite V] (φ : L.Formula V) : L.Sentence :=
  Formula.iExs V (φ.relabel Sum.inr)

/-- The universal closure holds exactly when the formula holds under every assignment of its
free variables. -/
@[simp, fo_realize]
theorem realize_closeAll {M : Type w} [L.Structure M] (V : Type) [Finite V] (φ : L.Formula V) :
    (closeAll V φ).Realize M ↔ ∀ v : V → M, φ.Realize v := by
  simp only [closeAll, Sentence.Realize, Formula.realize_iAlls, Formula.realize_relabel]
  refine forall_congr' fun v => ?_
  have h : (Sum.elim (default : Empty → M) v ∘ Sum.inr) = v := by
    funext x; rfl
  rw [h]

/-- The existential closure holds exactly when the formula holds under some assignment of its
free variables. -/
@[simp, fo_realize]
theorem realize_closeEx {M : Type w} [L.Structure M] (V : Type) [Finite V] (φ : L.Formula V) :
    (closeEx V φ).Realize M ↔ ∃ v : V → M, φ.Realize v := by
  simp only [closeEx, Sentence.Realize, Formula.realize_iExs, Formula.realize_relabel]
  refine exists_congr fun v => ?_
  have h : (Sum.elim (default : Empty → M) v ∘ Sum.inr) = v := by
    funext x; rfl
  rw [h]

/-- Relabel a single-variable formula `φ : L.Formula (Fin 1)` to free variable `u : V`. -/
def atVar (φ : L.Formula (Fin 1)) {V : Type*} (u : V) : L.Formula V :=
  φ.relabel (fun _ => u)

/-- `atVar φ u` holds under `v` if and only if `φ` holds of the singleton tuple `![v u]`. -/
@[simp, fo_realize]
theorem realize_atVar {M : Type w} [L.Structure M] (φ : L.Formula (Fin 1)) {V : Type*}
    (v : V → M) (u : V) :
    (atVar φ u).Realize v ↔ φ.Realize ![v u] := by
  rw [atVar, Formula.realize_relabel]
  refine iff_of_eq (congrArg φ.Realize (funext fun i => ?_))
  rw [Subsingleton.elim i 0]
  rfl

/-- Equality of two free variables as a formula. -/
def varEq {V : Type*} (u w : V) : L.Formula V :=
  Term.equal (.var u) (.var w)

/-- Application of a unary relation symbol to a free variable. -/
def rel₁ {V : Type*} (r : L.Relations 1) (u : V) : L.Formula V :=
  Relations.formula₁ r (.var u)

/-- Application of a binary relation symbol to two free variables. -/
def rel₂ {V : Type*} (r : L.Relations 2) (u w : V) : L.Formula V :=
  Relations.formula₂ r (.var u) (.var w)

/-- `varEq u w` holds under `v` if and only if `v u = v w`. -/
@[simp, fo_realize]
theorem realize_varEq {M : Type w} [L.Structure M] {V : Type*} (v : V → M) (u w : V) :
    (varEq (L := L) u w).Realize v ↔ v u = v w := by
  simp [varEq]

/-- `rel₁ r u` holds under `v` if and only if `RelMap r ![v u]` holds. -/
@[simp, fo_realize]
theorem realize_rel₁ {M : Type w} [L.Structure M] {V : Type*} (v : V → M)
    (r : L.Relations 1) (u : V) :
    (rel₁ r u).Realize v ↔ RelMap r ![v u] := by
  simp [rel₁]

/-- `rel₂ r u w` holds under `v` if and only if `RelMap r ![v u, v w]` holds. -/
@[simp, fo_realize]
theorem realize_rel₂ {M : Type w} [L.Structure M] {V : Type*} (v : V → M)
    (r : L.Relations 2) (u w : V) :
    (rel₂ r u w).Realize v ↔ RelMap r ![v u, v w] := by
  simp [rel₂]

/-- The formula `⊤` holds, as a term. -/
theorem formula_realize_top {M : Type w} [L.Structure M] {V : Type*} {v : V → M} :
    (⊤ : L.Formula V).Realize v :=
  Formula.realize_top.2 trivial

/-- An isomorphism preserves a binary relation on pairs. -/
theorem relMap_pair_equiv {M N : Type*} [L.Structure M] [L.Structure N] (e : M ≃[L] N)
    (R : L.Relations 2) (a b : M) : RelMap R ![e a, e b] ↔ RelMap R ![a, b] := by
  rw [← e.map_rel R ![a, b] ]
  refine iff_of_eq (congrArg _ (funext fun i => ?_))
  refine Fin.cases rfl (fun j => ?_) i
  exact Fin.cases rfl (fun k => k.elim0) j

/-- An isomorphism preserves a unary relation. -/
theorem relMap_single_equiv {M N : Type*} [L.Structure M] [L.Structure N] (e : M ≃[L] N)
    (R : L.Relations 1) (a : M) : RelMap R ![e a] ↔ RelMap R ![a] := by
  rw [← e.map_rel R ![a] ]
  refine iff_of_eq (congrArg _ (funext fun i => ?_))
  exact Fin.cases rfl (fun k => k.elim0) i

/-! ### Order combinators on `Fin B` -/

/-- The strict order formula `u < w` with respect to a binary relation symbol `r`. -/
def lt (r : L.Relations 2) {V : Type*} (u w : V) : L.Formula V :=
  rel₂ r u w

/-- The weak order formula `u ≤ w` (`¬ (w < u)`) with respect to `r`. -/
def le (r : L.Relations 2) {V : Type*} (u w : V) : L.Formula V :=
  ∼(lt r w u)

/-- The formula `∀ z, ¬ (z < u)`, characterizing the minimum element `0` of `Fin B`. -/
def isZero (r : L.Relations 2) {V : Type*} (u : V) : L.Formula V :=
  ∀' ∼(r.boundedFormula₂ &0 (.var (.inl u)))

/-- The formula `∀ z, ¬ (u < z)`, characterizing the maximum element `B - 1` of `Fin B`. -/
def isMax (r : L.Relations 2) {V : Type*} (u : V) : L.Formula V :=
  ∀' ∼(r.boundedFormula₂ (.var (.inl u)) &0)

/-- The successor formula `u < w ∧ ∀ z, ¬ (u < z) ∨ ¬ (z < w)`, characterizing
`(w : ℕ) = (u : ℕ) + 1` on `Fin B`. -/
def succ (r : L.Relations 2) {V : Type*} (u w : V) : L.Formula V :=
  lt r u w ⊓ ∀' (∼(r.boundedFormula₂ (.var (.inl u)) &0) ⊔
    ∼(r.boundedFormula₂ &0 (.var (.inl w))))

/-- Given a domain formula `inDom : L.Formula (Fin 1)` holding of `< M`, the formula
`isFirstOut r inDom u` asserts `¬ inDom(u) ∧ ∀ k < u, inDom(k)`, holding solely of `M`. -/
noncomputable def isFirstOut (r : L.Relations 2) (inDom : L.Formula (Fin 1))
    {V : Type*} (u : V) : L.Formula V :=
  ∼(atVar inDom u) ⊓
    Formula.iAlls (Fin 1) (lt r (.inr 0) (.inl u) ⟹ atVar inDom (.inr 0))

section FinOrder

variable {B : ℕ} [L.Structure (Fin B)] {r : L.Relations 2}
  (hlt : ∀ x : Fin 2 → Fin B, RelMap r x ↔ x 0 < x 1)

include hlt

/-- On `Fin B`, with `r` interpreted as `<`, `lt r u w` holds under `v` iff `v u < v w`. -/
@[fo_realize]
theorem realize_lt {V : Type*} (v : V → Fin B) (u w : V) :
    (lt r u w).Realize v ↔ v u < v w := by
  simp [lt, hlt]

/-- On `Fin B`, with `r` interpreted as `<`, `le r u w` holds under `v` iff `v u ≤ v w`. -/
@[fo_realize]
theorem realize_le {V : Type*} (v : V → Fin B) (u w : V) :
    (le r u w).Realize v ↔ v u ≤ v w := by
  simp [le, realize_lt hlt]

/-- On `Fin B`, with `r` read as `<`, `isZero r u` holds exactly when `u` is assigned `0`. -/
@[fo_realize]
theorem realize_isZero {V : Type*} (v : V → Fin B) (u : V) :
    (isZero r u).Realize v ↔ (v u : ℕ) = 0 := by
  have h1 : (isZero r u).Realize v ↔ ∀ z : Fin B, ¬ (z < v u) := by
    simp [isZero, Formula.Realize, hlt, Fin.snoc]
  rw [h1]
  constructor
  · intro h
    by_contra hne
    have h0 : 0 < (v u : ℕ) := by omega
    have hB : 0 < B := h0.trans (v u).2
    have := h ⟨0, hB⟩
    simp only [Fin.lt_def] at this
    omega
  · intro h z
    simp only [Fin.lt_def, h]
    omega

/-- On `Fin B`, with `r` read as `<`, `isMax r u` holds exactly when `u` is assigned `B - 1`. -/
@[fo_realize]
theorem realize_isMax {V : Type*} (v : V → Fin B) (u : V) :
    (isMax r u).Realize v ↔ (v u : ℕ) = B - 1 := by
  have h1 : (isMax r u).Realize v ↔ ∀ z : Fin B, ¬ (v u < z) := by
    simp [isMax, Formula.Realize, hlt, Fin.snoc]
  rw [h1]
  have hu := (v u).2
  constructor
  · intro h
    by_contra hne
    have hlt' : (v u : ℕ) + 1 < B := by omega
    have := h ⟨(v u : ℕ) + 1, hlt'⟩
    simp only [Fin.lt_def] at this
    omega
  · intro h z
    have hz := z.2
    simp only [Fin.lt_def]
    omega

/-- On `Fin B`, with `r` read as `<`, `succ r u w` holds exactly when `w` is assigned the
successor of the value of `u`. -/
@[fo_realize]
theorem realize_succ {V : Type*} (v : V → Fin B) (u w : V) :
    (succ r u w).Realize v ↔ (v w : ℕ) = (v u : ℕ) + 1 := by
  have h1 : (succ r u w).Realize v ↔
      v u < v w ∧ ∀ z : Fin B, ¬ (v u < z) ∨ ¬ (z < v w) := by
    rw [succ, Formula.realize_inf, realize_lt hlt]
    simp [Formula.Realize, hlt, Fin.snoc]
  rw [h1]
  have hu := (v u).2
  have hw := (v w).2
  constructor
  · rintro ⟨hlt', hmid⟩
    rw [Fin.lt_def] at hlt'
    by_contra hne
    have hlt1 : (v u : ℕ) + 1 < (v w : ℕ) := by omega
    have hltB : (v u : ℕ) + 1 < B := hlt1.trans hw
    rcases hmid ⟨(v u : ℕ) + 1, hltB⟩ with h | h
    · simp only [Fin.lt_def] at h; omega
    · simp only [Fin.lt_def] at h; omega
  · intro h
    refine ⟨by simp only [Fin.lt_def, h]; omega, fun z => ?_⟩
    simp only [Fin.lt_def]
    omega

/-- On `Fin B`, with `r` read as `<` and a domain formula holding exactly below `M < B`,
`isFirstOut r inDom u` holds exactly when `u` is assigned `M`. -/
@[fo_realize]
theorem realize_isFirstOut {inDom : L.Formula (Fin 1)} {M : ℕ} (hMB : M < B)
    (hdom : ∀ j : Fin B, inDom.Realize ![j] ↔ (j : ℕ) < M) {V : Type*}
    (v : V → Fin B) (u : V) :
    (isFirstOut r inDom u).Realize v ↔ (v u : ℕ) = M := by
  simp only [isFirstOut, Formula.realize_inf, Formula.realize_not, Formula.realize_iAlls,
    Formula.realize_imp, realize_atVar, Sum.elim_inl, Sum.elim_inr, realize_lt hlt, hdom]
  constructor
  · rintro ⟨hge, hlt_all⟩
    by_contra hne
    have hgt : M < (v u : ℕ) := by omega
    have hM := hlt_all ![⟨M, hMB⟩] (by simpa [Fin.lt_def] using hgt)
    simp at hM
  · intro heq
    refine ⟨by omega, fun k hk => ?_⟩
    rw [Fin.lt_def] at hk
    omega

end FinOrder

/-! ### Finite-domain cardinality and truth-table sentences -/

variable {M : Type w} [L.Structure M]

/-- On a finite structure `M`, Mathlib's `Sentence.cardGe L n` holds iff `n ≤ Nat.card M`. -/
theorem realize_cardGe_iff_le_card [Finite M] (n : ℕ) :
    M ⊨ Sentence.cardGe L n ↔ n ≤ Nat.card M := by
  rw [Sentence.realize_cardGe, ← Nat.cast_card, Nat.cast_le]

/-- The first-order sentence `Sentence.cardGe L n ⊓ ∼(Sentence.cardGe L (n + 1))`, which holds on a
finite structure `M` iff `Nat.card M = n`. -/
def cardEqSentence (L : Language.{u, v}) (n : ℕ) : L.Sentence :=
  Sentence.cardGe L n ⊓ ∼(Sentence.cardGe L (n + 1))

/-- On a finite structure, `cardEqSentence L n` holds exactly when the structure has `n`
elements. -/
@[simp, fo_realize]
theorem realize_cardEqSentence [Finite M] (n : ℕ) :
    M ⊨ cardEqSentence L n ↔ Nat.card M = n := by
  rw [cardEqSentence, Sentence.realize_inf, Sentence.realize_not, realize_cardGe_iff_le_card,
    realize_cardGe_iff_le_card]
  omega

/-- Given `m` sentences `φ` and a predicate `P` on bit vectors `Fin m → Bool`, the first-order
sentence asserting that the truth values `i ↦ (M ⊨ φ i)` satisfy `P`. -/
noncomputable def truthTableSentence {m : ℕ} (φ : Fin m → L.Sentence)
    (P : (Fin m → Bool) → Prop) : L.Sentence :=
  BoundedFormula.iSup fun s : {s : Fin m → Bool // P s} =>
    BoundedFormula.iInf fun i : Fin m => if s.1 i then φ i else ∼(φ i)

open scoped Classical in
/-- `truthTableSentence φ P` holds exactly when the truth values of the sentences `φ i` satisfy
`P`. -/
@[simp, fo_realize]
theorem realize_truthTableSentence {m : ℕ} (φ : Fin m → L.Sentence)
    (P : (Fin m → Bool) → Prop) :
    M ⊨ truthTableSentence φ P ↔ P (fun i => decide (M ⊨ φ i)) := by
  simp only [truthTableSentence, Sentence.Realize, Formula.Realize, BoundedFormula.realize_iSup,
    BoundedFormula.realize_iInf, Subtype.exists]
  have hiff (s : Fin m → Bool) (i : Fin m) :
      BoundedFormula.Realize (if s i = true then φ i else ∼(φ i))
        (default : Empty → M) default ↔ s i = decide (M ⊨ φ i) := by
    cases s i
    · simpa [Sentence.Realize, Formula.Realize] using (@decide_eq_false_iff_not (M ⊨ φ i) _).symm
    · simpa [Sentence.Realize, Formula.Realize] using (@decide_eq_true_iff (M ⊨ φ i) _).symm
  simp only [hiff, ← funext_iff]
  exact ⟨fun ⟨s, hs, h⟩ => h ▸ hs, fun h => ⟨_, h, rfl⟩⟩

end Cslib.Logic.FO
