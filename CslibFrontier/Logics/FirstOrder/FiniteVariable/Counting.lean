/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.FiniteVariable.Basic
public import Mathlib.Data.Set.Card
import CslibFrontier.Foundations.Data.List.FoldrForall

/-!
# Finite-variable counting logic

The `k`-variable counting logic `C^k` extends `FO^k` by the counting quantifiers
`∃^{≥ m} xᵢ φ`, "at least `m` values of the variable `xᵢ` satisfy `φ`" ([CaiFurerImmerman1992],
Section 3.2). Over a fixed number of variables, counting quantifiers add expressive power: the
sentence `∃^{≥ 3} x₀ ⊤` uses one variable, but no one-variable first-order sentence separates a
three-element set from a two-element one.

`Cslib.Logic.FO.FiniteVariable.CountingFormula L k` is the syntax, with variables `Fin k` that may
be quantified again inside their own scope, exactly like `Cslib.Logic.FO.FiniteVariable.Formula`.
Truth uses `Set.encard`, so it is meaningful in infinite structures too: `atLeast m i φ` holds when
the set of values of `xᵢ` satisfying `φ` has at least `m` elements. The universal and existential
quantifiers are derived from `atLeast 1`, and `Formula.toCounting` embeds `FO^k` into `C^k`
preserving truth, quantifier rank and free variables.

## Main definitions

* `Cslib.Logic.FO.FiniteVariable.CountingFormula`: formulas of `C^k` over the relation symbols of
  `L`.
* `Cslib.Logic.FO.FiniteVariable.CountingFormula.Realize`: truth under an assignment `Fin k → M`.
* `Cslib.Logic.FO.FiniteVariable.CountingFormula.quantifierRank`,
  `Cslib.Logic.FO.FiniteVariable.CountingFormula.freeVars`: quantifier rank, in which a counting
  quantifier counts once, and free variables.
* `Cslib.Logic.FO.FiniteVariable.CountingFormula.all`,
  `Cslib.Logic.FO.FiniteVariable.CountingFormula.ex`,
  `Cslib.Logic.FO.FiniteVariable.CountingFormula.exactly`,
  `Cslib.Logic.FO.FiniteVariable.CountingFormula.iInf`,
  `Cslib.Logic.FO.FiniteVariable.CountingFormula.iSup`: derived quantifiers and connectives.
* `Cslib.Logic.FO.FiniteVariable.Formula.toCounting`: the embedding of `FO^k` into `C^k`.

## Main results

* `Cslib.Logic.FO.FiniteVariable.CountingFormula.realize_exactly`: `exactly m i φ` holds when
  exactly `m` values of `xᵢ` satisfy `φ`.
* `Cslib.Logic.FO.FiniteVariable.CountingFormula.realize_congr`: truth depends only on the values
  of the free variables.
* `Cslib.Logic.FO.FiniteVariable.Formula.realize_toCounting`,
  `Cslib.Logic.FO.FiniteVariable.Formula.quantifierRank_toCounting`,
  `Cslib.Logic.FO.FiniteVariable.Formula.freeVars_toCounting`: the embedding preserves truth,
  quantifier rank and free variables.

## References

* [J.-Y. Cai, M. Fürer, N. Immerman, *An optimal lower bound on the number of variables for graph
  identification*][CaiFurerImmerman1992], Section 3.2.
* [N. Immerman, *Descriptive Complexity*][Immerman1999], Section 12.3 (unverified locator).
-/

public section

universe u v w

open FirstOrder Language Structure

namespace Cslib.Logic.FO.FiniteVariable

variable (L : Language.{u, v}) (k : ℕ)

/-- Formulas of the `k`-variable counting logic `C^k` over the relation symbols of `L`. The
variables are `Fin k`, and `atLeast m i φ` quantifies the variable `i`, which may already be bound
or free in an enclosing formula. -/
inductive CountingFormula : Type v
  /-- Falsity. -/
  | falsum : CountingFormula
  /-- The equation `xᵢ = xⱼ`. -/
  | equal (i j : Fin k) : CountingFormula
  /-- The relation `R` applied to the variables `x_{f 0}, …, x_{f (l - 1)}`. -/
  | rel {l : ℕ} (R : L.Relations l) (f : Fin l → Fin k) : CountingFormula
  /-- Implication. -/
  | imp (φ ψ : CountingFormula) : CountingFormula
  /-- The counting quantifier `∃^{≥ m} xᵢ φ`: at least `m` values of `xᵢ` satisfy `φ`. -/
  | atLeast (m : ℕ) (i : Fin k) (φ : CountingFormula) : CountingFormula

variable {L k}

namespace CountingFormula

/-- Negation. -/
def not (φ : CountingFormula L k) : CountingFormula L k :=
  imp φ falsum

/-- Existential quantification of the variable `xᵢ`: at least one value satisfies `φ`. -/
def ex (i : Fin k) (φ : CountingFormula L k) : CountingFormula L k :=
  atLeast 1 i φ

/-- Universal quantification of the variable `xᵢ`: no value satisfies `¬φ`. -/
def all (i : Fin k) (φ : CountingFormula L k) : CountingFormula L k :=
  (ex i φ.not).not

instance : Bot (CountingFormula L k) :=
  ⟨falsum⟩

instance : Top (CountingFormula L k) :=
  ⟨falsum.not⟩

instance : Min (CountingFormula L k) :=
  ⟨fun φ ψ => (φ.imp ψ.not).not⟩

instance : Max (CountingFormula L k) :=
  ⟨fun φ ψ => φ.not.imp ψ⟩

/-- Exactly `m` values of the variable `xᵢ` satisfy `φ`. -/
def exactly (m : ℕ) (i : Fin k) (φ : CountingFormula L k) : CountingFormula L k :=
  atLeast m i φ ⊓ (atLeast (m + 1) i φ).not

/-- The conjunction of a finite family of formulas, through an arbitrary enumeration of the index
type, as for `Cslib.Logic.FO.FiniteVariable.Formula.iInf`. -/
noncomputable def iInf {β : Type*} [Finite β] (f : β → CountingFormula L k) :
    CountingFormula L k :=
  let _ := Fintype.ofFinite β
  ((Finset.univ : Finset β).toList.map f).foldr (· ⊓ ·) ⊤

/-- The disjunction of a finite family of formulas, as the negation of the conjunction of the
negations. -/
noncomputable def iSup {β : Type*} [Finite β] (f : β → CountingFormula L k) :
    CountingFormula L k :=
  (iInf fun b => (f b).not).not

/-- A property of formulas that holds of `⊤` and distributes over `⊓` holds of a finite
conjunction exactly when it holds of every conjunct. -/
private theorem apply_iInf_iff {β : Type*} [Finite β] {p : CountingFormula L k → Prop}
    (hinf : ∀ φ ψ, p (φ ⊓ ψ) ↔ p φ ∧ p ψ) (htop : p ⊤) (f : β → CountingFormula L k) :
    p (iInf f) ↔ ∀ b, p (f b) := by
  let := Fintype.ofFinite β
  exact List.apply_foldr_map_univ_toList_iff hinf htop f

/-! ### Semantics -/

/-- Truth of a counting formula in `M` under the assignment `a` of elements to the `k` variables.
The counting quantifier `atLeast m i φ` holds when the set of values `c` with
`φ.Realize (update a i c)` has at least `m` elements, counted by `Set.encard`. -/
def Realize {M : Type w} [L.Structure M] : CountingFormula L k → (Fin k → M) → Prop
  | falsum, _ => False
  | equal i j, a => a i = a j
  | rel R f, a => RelMap R (a ∘ f)
  | imp φ ψ, a => φ.Realize a → ψ.Realize a
  | atLeast m i φ, a => (m : ℕ∞) ≤ {c : M | φ.Realize (Function.update a i c)}.encard

variable {M : Type w} [L.Structure M]

@[simp] theorem realize_falsum (a : Fin k → M) :
    (falsum : CountingFormula L k).Realize a ↔ False := by
  rw [Realize]

@[simp] theorem realize_equal (i j : Fin k) (a : Fin k → M) :
    (equal i j : CountingFormula L k).Realize a ↔ a i = a j := by
  rw [Realize]

@[simp] theorem realize_rel {l : ℕ} (R : L.Relations l) (f : Fin l → Fin k) (a : Fin k → M) :
    (rel R f).Realize a ↔ RelMap R (a ∘ f) := by
  rw [Realize]

@[simp] theorem realize_imp (φ ψ : CountingFormula L k) (a : Fin k → M) :
    (imp φ ψ).Realize a ↔ (φ.Realize a → ψ.Realize a) := by
  rw [Realize]

@[simp] theorem realize_atLeast (m : ℕ) (i : Fin k) (φ : CountingFormula L k) (a : Fin k → M) :
    (atLeast m i φ).Realize a ↔
      (m : ℕ∞) ≤ {c : M | φ.Realize (Function.update a i c)}.encard := by
  rw [Realize]

@[simp] theorem realize_not (φ : CountingFormula L k) (a : Fin k → M) :
    φ.not.Realize a ↔ ¬φ.Realize a := by
  rw [not, realize_imp, realize_falsum]

@[simp] theorem realize_ex (i : Fin k) (φ : CountingFormula L k) (a : Fin k → M) :
    (ex i φ).Realize a ↔ ∃ c : M, φ.Realize (Function.update a i c) := by
  rw [ex, realize_atLeast, Nat.cast_one, Set.one_le_encard_iff_nonempty]
  rfl

@[simp] theorem realize_all (i : Fin k) (φ : CountingFormula L k) (a : Fin k → M) :
    (all i φ).Realize a ↔ ∀ c : M, φ.Realize (Function.update a i c) := by
  simp only [all, realize_not, realize_ex, not_exists, not_not]

@[simp] theorem realize_bot (a : Fin k → M) : (⊥ : CountingFormula L k).Realize a ↔ False :=
  realize_falsum a

@[simp] theorem realize_top (a : Fin k → M) : (⊤ : CountingFormula L k).Realize a ↔ True :=
  (realize_not _ a).trans (by simp only [realize_falsum, not_false_eq_true])

@[simp] theorem realize_inf (φ ψ : CountingFormula L k) (a : Fin k → M) :
    (φ ⊓ ψ).Realize a ↔ φ.Realize a ∧ ψ.Realize a := by
  change (φ.imp ψ.not).not.Realize a ↔ _
  simp only [realize_not, realize_imp, not_imp, not_not]

@[simp] theorem realize_sup (φ ψ : CountingFormula L k) (a : Fin k → M) :
    (φ ⊔ ψ).Realize a ↔ φ.Realize a ∨ ψ.Realize a := by
  change (φ.not.imp ψ).Realize a ↔ _
  simp only [realize_imp, realize_not, or_iff_not_imp_left]

@[simp] theorem realize_exactly (m : ℕ) (i : Fin k) (φ : CountingFormula L k) (a : Fin k → M) :
    (exactly m i φ).Realize a ↔
      {c : M | φ.Realize (Function.update a i c)}.encard = m := by
  rw [exactly, realize_inf, realize_not, realize_atLeast, realize_atLeast]
  generalize {c : M | φ.Realize (Function.update a i c)}.encard = e
  induction e using ENat.recTopCoe with
  | top => simp only [le_top, not_true_eq_false, and_false, ENat.top_ne_natCast]
  | coe e =>
    norm_cast
    omega

/-- On a finite structure, `atLeast m i φ` holds when at least `m` values of `xᵢ` satisfy `φ`,
counted by `Set.ncard`. -/
theorem realize_atLeast_iff_ncard [Finite M] (m : ℕ) (i : Fin k) (φ : CountingFormula L k)
    (a : Fin k → M) :
    (atLeast m i φ).Realize a ↔ m ≤ {c : M | φ.Realize (Function.update a i c)}.ncard := by
  rw [realize_atLeast, ← (Set.toFinite _).cast_ncard_eq, Nat.cast_le]

/-- On a finite structure, `exactly m i φ` holds when exactly `m` values of `xᵢ` satisfy `φ`,
counted by `Set.ncard`. -/
theorem realize_exactly_iff_ncard [Finite M] (m : ℕ) (i : Fin k) (φ : CountingFormula L k)
    (a : Fin k → M) :
    (exactly m i φ).Realize a ↔ {c : M | φ.Realize (Function.update a i c)}.ncard = m := by
  rw [realize_exactly, ← (Set.toFinite _).cast_ncard_eq, Nat.cast_inj]

@[simp] theorem realize_iInf {β : Type*} [Finite β] (f : β → CountingFormula L k)
    (a : Fin k → M) : (iInf f).Realize a ↔ ∀ b, (f b).Realize a :=
  apply_iInf_iff (p := fun φ => φ.Realize a) (fun φ ψ => realize_inf φ ψ a)
    ((realize_top a).2 trivial) f

@[simp] theorem realize_iSup {β : Type*} [Finite β] (f : β → CountingFormula L k)
    (a : Fin k → M) : (iSup f).Realize a ↔ ∃ b, (f b).Realize a := by
  simp only [iSup, realize_not, realize_iInf, not_forall, not_not]

/-! ### Quantifier rank -/

/-- The quantifier rank of a counting formula: the maximal nesting depth of its counting
quantifiers. -/
def quantifierRank : CountingFormula L k → ℕ
  | falsum => 0
  | equal _ _ => 0
  | rel _ _ => 0
  | imp φ ψ => max φ.quantifierRank ψ.quantifierRank
  | atLeast _ _ φ => φ.quantifierRank + 1

@[simp] theorem quantifierRank_falsum : (falsum : CountingFormula L k).quantifierRank = 0 := by
  rw [quantifierRank]

@[simp] theorem quantifierRank_equal (i j : Fin k) :
    (equal i j : CountingFormula L k).quantifierRank = 0 := by
  rw [quantifierRank]

@[simp] theorem quantifierRank_rel {l : ℕ} (R : L.Relations l) (f : Fin l → Fin k) :
    (rel R f).quantifierRank = 0 := by
  rw [quantifierRank]

@[simp] theorem quantifierRank_imp (φ ψ : CountingFormula L k) :
    (imp φ ψ).quantifierRank = max φ.quantifierRank ψ.quantifierRank := by
  rw [quantifierRank]

@[simp] theorem quantifierRank_atLeast (m : ℕ) (i : Fin k) (φ : CountingFormula L k) :
    (atLeast m i φ).quantifierRank = φ.quantifierRank + 1 := by
  rw [quantifierRank]

@[simp] theorem quantifierRank_not (φ : CountingFormula L k) :
    φ.not.quantifierRank = φ.quantifierRank := by
  rw [not, quantifierRank_imp, quantifierRank_falsum, Nat.max_zero]

@[simp] theorem quantifierRank_ex (i : Fin k) (φ : CountingFormula L k) :
    (ex i φ).quantifierRank = φ.quantifierRank + 1 :=
  quantifierRank_atLeast 1 i φ

@[simp] theorem quantifierRank_all (i : Fin k) (φ : CountingFormula L k) :
    (all i φ).quantifierRank = φ.quantifierRank + 1 := by
  rw [all, quantifierRank_not, quantifierRank_ex, quantifierRank_not]

@[simp] theorem quantifierRank_bot : (⊥ : CountingFormula L k).quantifierRank = 0 :=
  quantifierRank_falsum

@[simp] theorem quantifierRank_top : (⊤ : CountingFormula L k).quantifierRank = 0 :=
  (quantifierRank_not _).trans quantifierRank_falsum

@[simp] theorem quantifierRank_inf (φ ψ : CountingFormula L k) :
    (φ ⊓ ψ).quantifierRank = max φ.quantifierRank ψ.quantifierRank := by
  change (φ.imp ψ.not).not.quantifierRank = _
  rw [quantifierRank_not, quantifierRank_imp, quantifierRank_not]

@[simp] theorem quantifierRank_sup (φ ψ : CountingFormula L k) :
    (φ ⊔ ψ).quantifierRank = max φ.quantifierRank ψ.quantifierRank := by
  change (φ.not.imp ψ).quantifierRank = _
  rw [quantifierRank_imp, quantifierRank_not]

@[simp] theorem quantifierRank_exactly (m : ℕ) (i : Fin k) (φ : CountingFormula L k) :
    (exactly m i φ).quantifierRank = φ.quantifierRank + 1 := by
  rw [exactly, quantifierRank_inf, quantifierRank_not, quantifierRank_atLeast,
    quantifierRank_atLeast, max_self]

/-- A finite conjunction has quantifier rank at most `m` when each conjunct does. -/
theorem quantifierRank_iInf_le {β : Type*} [Finite β] {f : β → CountingFormula L k} {m : ℕ}
    (h : ∀ b, (f b).quantifierRank ≤ m) : (iInf f).quantifierRank ≤ m :=
  (apply_iInf_iff (p := fun φ => φ.quantifierRank ≤ m)
    (fun φ ψ => by rw [quantifierRank_inf, max_le_iff])
    (quantifierRank_top.trans_le (Nat.zero_le m)) f).2 h

/-- A finite disjunction has quantifier rank at most `m` when each disjunct does. -/
theorem quantifierRank_iSup_le {β : Type*} [Finite β] {f : β → CountingFormula L k} {m : ℕ}
    (h : ∀ b, (f b).quantifierRank ≤ m) : (iSup f).quantifierRank ≤ m := by
  rw [iSup, quantifierRank_not]
  exact quantifierRank_iInf_le fun b => (quantifierRank_not _).trans_le (h b)

/-! ### Free variables -/

/-- The free variables of a counting formula. -/
def freeVars : CountingFormula L k → Finset (Fin k)
  | falsum => ∅
  | equal i j => {i, j}
  | rel _ f => Finset.univ.image f
  | imp φ ψ => φ.freeVars ∪ ψ.freeVars
  | atLeast _ i φ => φ.freeVars.erase i

@[simp] theorem freeVars_falsum : (falsum : CountingFormula L k).freeVars = ∅ := by
  rw [freeVars]

@[simp] theorem freeVars_equal (i j : Fin k) :
    (equal i j : CountingFormula L k).freeVars = {i, j} := by
  rw [freeVars]

@[simp] theorem freeVars_rel {l : ℕ} (R : L.Relations l) (f : Fin l → Fin k) :
    (rel R f).freeVars = Finset.univ.image f := by
  rw [freeVars]

@[simp] theorem freeVars_imp (φ ψ : CountingFormula L k) :
    (imp φ ψ).freeVars = φ.freeVars ∪ ψ.freeVars := by
  rw [freeVars]

@[simp] theorem freeVars_atLeast (m : ℕ) (i : Fin k) (φ : CountingFormula L k) :
    (atLeast m i φ).freeVars = φ.freeVars.erase i := by
  rw [freeVars]

@[simp] theorem freeVars_not (φ : CountingFormula L k) : φ.not.freeVars = φ.freeVars := by
  rw [not, freeVars_imp, freeVars_falsum, Finset.union_empty]

@[simp] theorem freeVars_ex (i : Fin k) (φ : CountingFormula L k) :
    (ex i φ).freeVars = φ.freeVars.erase i :=
  freeVars_atLeast 1 i φ

@[simp] theorem freeVars_all (i : Fin k) (φ : CountingFormula L k) :
    (all i φ).freeVars = φ.freeVars.erase i := by
  rw [all, freeVars_not, freeVars_ex, freeVars_not]

@[simp] theorem freeVars_bot : (⊥ : CountingFormula L k).freeVars = ∅ :=
  freeVars_falsum

@[simp] theorem freeVars_top : (⊤ : CountingFormula L k).freeVars = ∅ :=
  (freeVars_not _).trans freeVars_falsum

@[simp] theorem freeVars_inf (φ ψ : CountingFormula L k) :
    (φ ⊓ ψ).freeVars = φ.freeVars ∪ ψ.freeVars := by
  change (φ.imp ψ.not).not.freeVars = _
  rw [freeVars_not, freeVars_imp, freeVars_not]

@[simp] theorem freeVars_sup (φ ψ : CountingFormula L k) :
    (φ ⊔ ψ).freeVars = φ.freeVars ∪ ψ.freeVars := by
  change (φ.not.imp ψ).freeVars = _
  rw [freeVars_imp, freeVars_not]

@[simp] theorem freeVars_exactly (m : ℕ) (i : Fin k) (φ : CountingFormula L k) :
    (exactly m i φ).freeVars = φ.freeVars.erase i := by
  rw [exactly, freeVars_inf, freeVars_not, freeVars_atLeast, freeVars_atLeast, Finset.union_self]

/-- The free variables of a finite conjunction lie in `S` when those of each conjunct do. -/
theorem freeVars_iInf_subset {β : Type*} [Finite β] {f : β → CountingFormula L k}
    {S : Set (Fin k)} (h : ∀ b, ↑(f b).freeVars ⊆ S) : ↑(iInf f).freeVars ⊆ S :=
  (apply_iInf_iff (p := fun φ => ↑φ.freeVars ⊆ S)
    (fun φ ψ => by rw [freeVars_inf, Finset.coe_union, Set.union_subset_iff])
    (by rw [freeVars_top, Finset.coe_empty]; exact Set.empty_subset S) f).2 h

/-- The free variables of a finite disjunction lie in `S` when those of each disjunct do. -/
theorem freeVars_iSup_subset {β : Type*} [Finite β] {f : β → CountingFormula L k}
    {S : Set (Fin k)} (h : ∀ b, ↑(f b).freeVars ⊆ S) : ↑(iSup f).freeVars ⊆ S := by
  rw [iSup, freeVars_not]
  exact freeVars_iInf_subset fun b => (freeVars_not (f b)).symm ▸ h b

/-- The truth of a counting formula depends only on the values of its free variables. -/
theorem realize_congr {φ : CountingFormula L k} {a a' : Fin k → M}
    (h : ∀ i ∈ φ.freeVars, a i = a' i) : φ.Realize a ↔ φ.Realize a' := by
  induction φ generalizing a a' with
  | falsum => exact Iff.rfl
  | equal i j =>
    simp only [freeVars_equal, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp,
      forall_eq] at h
    rw [realize_equal, realize_equal, h.1, h.2]
  | rel R f =>
    rw [realize_rel, realize_rel]
    have : a ∘ f = a' ∘ f := funext fun t => h _ (by simp)
    rw [this]
  | imp φ ψ ihφ ihψ =>
    simp only [freeVars_imp, Finset.mem_union] at h
    rw [realize_imp, realize_imp, ihφ fun i hi => h i (Or.inl hi),
      ihψ fun i hi => h i (Or.inr hi)]
  | atLeast m i φ ih =>
    simp only [freeVars_atLeast, Finset.mem_erase] at h
    rw [realize_atLeast, realize_atLeast]
    suffices hs : {c : M | φ.Realize (Function.update a i c)} =
        {c : M | φ.Realize (Function.update a' i c)} by rw [hs]
    refine Set.ext fun c => ih fun j hj => ?_
    by_cases hji : j = i
    · subst hji
      simp only [Function.update_self]
    · simp only [Function.update_of_ne hji, h j ⟨hji, hj⟩]

end CountingFormula

/-! ### `FO^k` is a fragment of `C^k` -/

namespace Formula

/-- The embedding of `FO^k` into `C^k`: the universal quantifier `all i φ` becomes
`CountingFormula.all i φ`, that is, "no value of `xᵢ` satisfies `¬φ`". -/
def toCounting : Formula L k → CountingFormula L k
  | falsum => .falsum
  | equal i j => .equal i j
  | rel R f => .rel R f
  | imp φ ψ => .imp φ.toCounting ψ.toCounting
  | all i φ => .all i φ.toCounting

variable {M : Type w} [L.Structure M]

/-- The embedding preserves truth. -/
@[simp] theorem realize_toCounting (φ : Formula L k) (a : Fin k → M) :
    φ.toCounting.Realize a ↔ φ.Realize a := by
  induction φ generalizing a with
  | falsum => rw [toCounting, CountingFormula.realize_falsum, realize_falsum]
  | equal i j => rw [toCounting, CountingFormula.realize_equal, realize_equal]
  | rel R f => rw [toCounting, CountingFormula.realize_rel, realize_rel]
  | imp φ ψ ihφ ihψ => rw [toCounting, CountingFormula.realize_imp, realize_imp, ihφ, ihψ]
  | all i φ ih =>
    rw [toCounting, CountingFormula.realize_all, realize_all]
    exact forall_congr' fun c => ih _

/-- The embedding preserves quantifier rank. -/
@[simp] theorem quantifierRank_toCounting (φ : Formula L k) :
    φ.toCounting.quantifierRank = φ.quantifierRank := by
  induction φ with
  | falsum => rw [toCounting, CountingFormula.quantifierRank_falsum, quantifierRank_falsum]
  | equal i j => rw [toCounting, CountingFormula.quantifierRank_equal, quantifierRank_equal]
  | rel R f => rw [toCounting, CountingFormula.quantifierRank_rel, quantifierRank_rel]
  | imp φ ψ ihφ ihψ =>
    rw [toCounting, CountingFormula.quantifierRank_imp, quantifierRank_imp, ihφ, ihψ]
  | all i φ ih => rw [toCounting, CountingFormula.quantifierRank_all, quantifierRank_all, ih]

/-- The embedding preserves free variables. -/
@[simp] theorem freeVars_toCounting (φ : Formula L k) :
    φ.toCounting.freeVars = φ.freeVars := by
  induction φ with
  | falsum => rw [toCounting, CountingFormula.freeVars_falsum, freeVars_falsum]
  | equal i j => rw [toCounting, CountingFormula.freeVars_equal, freeVars_equal]
  | rel R f => rw [toCounting, CountingFormula.freeVars_rel, freeVars_rel]
  | imp φ ψ ihφ ihψ => rw [toCounting, CountingFormula.freeVars_imp, freeVars_imp, ihφ, ihψ]
  | all i φ ih => rw [toCounting, CountingFormula.freeVars_all, freeVars_all, ih]

end Formula

end Cslib.Logic.FO.FiniteVariable
