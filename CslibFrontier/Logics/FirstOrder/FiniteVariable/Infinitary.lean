/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.ModelTheory.Graph
public import CslibFrontier.Logics.FirstOrder.FiniteVariable.BijectiveGame
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import CslibFrontier.Foundations.Data.Fintype.FiberEquiv
import CslibFrontier.Logics.FirstOrder.FiniteVariable.CountingHintikka
import Mathlib.Tactic.FinCases

/-!
# Infinitary finite-variable logics `L^k_{∞ω}` and `C^k_{∞ω}`

The infinitary `k`-variable logic `L^k_{∞ω}` extends the `k`-variable fragment `FO^k` by closing
formulas under arbitrary indexed disjunctions (and hence arbitrary indexed conjunctions) while
still restricting every subformula to the fixed variable set `Fin k`. Likewise `C^k_{∞ω}` extends
`C^k` with arbitrary indexed disjunctions alongside the counting quantifiers `∃^{≥ m} xᵢ φ`.

Because Lean types live in a universe hierarchy, `InfinitaryFormula.{w, u, v} L k` and
`InfinitaryCountingFormula.{w, u, v} L k` are parameterized by an index universe `w` for the index
types `ι : Type w` of `iSup`. Quantifier rank is bounded using a relational predicate
`QuantifierRankLE φ n` (`n : ℕ`), avoiding ordinal arithmetic while handling both finite-round
games and unbounded-rank formulas such as transitive closure.

## Main definitions

* `Cslib.Logic.FO.FiniteVariable.InfinitaryFormula`: formulas of `L^k_{∞ω}` with disjunctions
  indexed in `Type w`.
* `Cslib.Logic.FO.FiniteVariable.InfinitaryFormula.Realize`,
  `Cslib.Logic.FO.FiniteVariable.InfinitaryFormula.freeVars`,
  `Cslib.Logic.FO.FiniteVariable.InfinitaryFormula.QuantifierRankLE`: semantics, free variables,
  and finite quantifier-rank bounds for `L^k_{∞ω}`.
* `Cslib.Logic.FO.FiniteVariable.Formula.toInfinitary`: truth-, rank-, and free-variable-preserving
  embedding of `FO^k` into `L^k_{∞ω}`.
* `Cslib.Logic.FO.FiniteVariable.InfinitaryCountingFormula`: formulas of `C^k_{∞ω}` with counting
  quantifiers `atLeast m i φ` and disjunctions indexed in `Type w`.
* `Cslib.Logic.FO.FiniteVariable.CountingFormula.toInfinitary`,
  `Cslib.Logic.FO.FiniteVariable.InfinitaryFormula.toCounting`: embeddings from `C^k` and
  `L^k_{∞ω}` into `C^k_{∞ω}`.
* `Cslib.Logic.FO.FiniteVariable.walkFormula`,
  `Cslib.Logic.FO.FiniteVariable.reachableInfinitary`,
  `Cslib.Logic.FO.FiniteVariable.connectedInfinitary`: 3-variable sliding-pebble formulas defining
  fixed-length walks in `FO³` and reachability and connectivity in `L^3_{∞ω}`.
* `Cslib.Logic.FO.FiniteVariable.evenCardInfinitary`: the `C^1_{∞ω}` sentence defining even
  cardinality on finite structures.

## Main results

* `Cslib.Logic.FO.PebbleWins.realize_infinitaryFormula_iff`,
  `Cslib.Logic.FO.IsPebbleBackAndForth.realize_infinitaryFormula_iff`,
  `Cslib.Logic.FO.PebbleWinsForever.realize_infinitaryFormula_iff`: winning positions and
  back-and-forth invariants of the `k`-pebble game preserve `L^k_{∞ω}` formulas (including formulas
  of unbounded quantifier depth).
* `Cslib.Logic.FO.pebbleWins_iff_forall_infinitaryFormula_rankLE`,
  `Cslib.Logic.FO.exists_isPebbleBackAndForth_iff_forall_infinitaryFormula`,
  `Cslib.Logic.FO.pebbleWinsForever_iff_forall_infinitaryFormula`: pebble-game characterizations of
  `L^k_{∞ω}` over arbitrary languages and structures.
* `Cslib.Logic.FO.BijPebbleWins.realize_infinitaryCountingFormula_iff`,
  `Cslib.Logic.FO.IsBijPebbleBackAndForth.realize_infinitaryCountingFormula_iff`,
  `Cslib.Logic.FO.BijPebbleWinsForever.realize_infinitaryCountingFormula_iff`,
  `Cslib.Logic.FO.bijPebbleWins_iff_forall_infinitaryCountingFormula_rankLE`,
  `Cslib.Logic.FO.bijPebbleWinsForever_iff_forall_infinitaryCountingFormula`: bijective pebble-game
  characterizations of `C^k_{∞ω}`.
* `Cslib.Logic.FO.forall_realize_infinitaryFormula_iff_forall_realize`,
  `Cslib.Logic.FO.forall_realize_infinitaryCountingFormula_iff_forall_realize`: finite-model
  collapse of `L^k_{∞ω}` equivalence to `FO^k` equivalence and `C^k_{∞ω}` equivalence to `C^k`
  equivalence over finite relational vocabularies.
* `Cslib.Logic.FO.FiniteVariable.realize_reachableInfinitary`,
  `Cslib.Logic.FO.FiniteVariable.realize_connectedInfinitary_iff_preconnected`,
  `Cslib.Logic.FO.FiniteVariable.realize_connectedInfinitary_iff_connected`: graph reachability on
  all simple graphs and connectivity on all nonempty simple graphs (and
  `SimpleGraph.Preconnected` unconditionally) are definable in `L^3_{∞ω}`.
* `Cslib.Logic.FO.FiniteVariable.realize_evenCardInfinitary`,
  `Cslib.Logic.FO.pebbleWinsForever_fin_succ`,
  `Cslib.Logic.FO.not_exists_infinitaryFormula_even_card`: even cardinality is definable in
  `C^1_{∞ω}` on finite structures, yet not definable in `L^k_{∞ω}` for any `k`.

## References

* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004], Theorem 11.5 and Proposition 11.8.
* [P. G. Kolaitis and M. Y. Vardi, *Infinitary logic and 0-1 laws*][KolaitisVardi1992]
  (unverified locator).
* [J.-Y. Cai, M. Fürer, N. Immerman, *An optimal lower bound on the number of variables for graph
  identification*][CaiFurerImmerman1992], Section 3.2.
* [L. Hella, *Logical hierarchies in PTIME*][Hella1996] (unverified locator).
-/

public section

universe w u v w₁ w₂

open FirstOrder Language Structure

namespace Cslib.Logic.FO.FiniteVariable

/-! ### Infinitary `k`-variable logic `L^k_{∞ω}` -/

/-- Formulas of the infinitary `k`-variable logic `L^k_{∞ω}` over the relation symbols of `L`,
with indexed disjunctions ranging over index types in `Type w`. -/
inductive InfinitaryFormula (L : Language.{u, v}) (k : ℕ) : Type (max v (w + 1))
  /-- The equation `xᵢ = xⱼ`. -/
  | equal (i j : Fin k) : InfinitaryFormula L k
  /-- The relation `R` applied to the variables `x_{f 0}, …, x_{f (l - 1)}`. -/
  | rel {l : ℕ} (R : L.Relations l) (f : Fin l → Fin k) : InfinitaryFormula L k
  /-- Negation. -/
  | not (φ : InfinitaryFormula L k) : InfinitaryFormula L k
  /-- Arbitrary disjunction indexed by `ι : Type w`. -/
  | iSup {ι : Type w} (f : ι → InfinitaryFormula L k) : InfinitaryFormula L k
  /-- Existential quantification of the variable `xᵢ`. -/
  | ex (i : Fin k) (φ : InfinitaryFormula L k) : InfinitaryFormula L k

namespace InfinitaryFormula

variable {L : Language.{u, v}} {k : ℕ}

/-- Falsity, as the empty disjunction. -/
def bot : InfinitaryFormula.{w, u, v} L k :=
  iSup PEmpty.elim

/-- Truth, as the negation of falsity. -/
def top : InfinitaryFormula.{w, u, v} L k :=
  bot.not

/-- Binary disjunction. -/
def sup (φ ψ : InfinitaryFormula.{w, u, v} L k) : InfinitaryFormula.{w, u, v} L k :=
  iSup fun b : ULift.{w} Bool => cond b.down φ ψ

/-- Arbitrary conjunction indexed by `ι : Type w`, via De Morgan duality. -/
def iInf {ι : Type w} (f : ι → InfinitaryFormula.{w, u, v} L k) : InfinitaryFormula.{w, u, v} L k :=
  (iSup fun idx => (f idx).not).not

/-- Binary conjunction. -/
def inf (φ ψ : InfinitaryFormula.{w, u, v} L k) : InfinitaryFormula.{w, u, v} L k :=
  (sup φ.not ψ.not).not

/-- Implication. -/
def imp (φ ψ : InfinitaryFormula.{w, u, v} L k) : InfinitaryFormula.{w, u, v} L k :=
  sup φ.not ψ

/-- Universal quantification of the variable `xᵢ`. -/
def all (i : Fin k) (φ : InfinitaryFormula.{w, u, v} L k) : InfinitaryFormula.{w, u, v} L k :=
  (ex i φ.not).not

instance : Bot (InfinitaryFormula.{w, u, v} L k) := ⟨bot⟩
instance : Top (InfinitaryFormula.{w, u, v} L k) := ⟨top⟩
instance : Max (InfinitaryFormula.{w, u, v} L k) := ⟨sup⟩
instance : Min (InfinitaryFormula.{w, u, v} L k) := ⟨inf⟩

/-! #### Semantics of `L^k_{∞ω}` -/

/-- Truth of an `L^k_{∞ω}` formula in `M` under the assignment `a : Fin k → M`. -/
def Realize {M : Type w₁} [L.Structure M] :
    InfinitaryFormula.{w, u, v} L k → (Fin k → M) → Prop
  | equal i j, a => a i = a j
  | rel R f, a => RelMap R (a ∘ f)
  | not φ, a => ¬φ.Realize a
  | iSup f, a => ∃ idx, (f idx).Realize a
  | ex i φ, a => ∃ c : M, φ.Realize (Function.update a i c)

section Semantics

variable {M : Type w₁} [L.Structure M]

@[simp] theorem realize_equal (i j : Fin k) (a : Fin k → M) :
    (equal i j : InfinitaryFormula.{w, u, v} L k).Realize a ↔ a i = a j := by
  rw [Realize]

@[simp] theorem realize_rel {l : ℕ} (R : L.Relations l) (f : Fin l → Fin k) (a : Fin k → M) :
    (rel R f : InfinitaryFormula.{w, u, v} L k).Realize a ↔ RelMap R (a ∘ f) := by
  rw [Realize]

@[simp] theorem realize_not (φ : InfinitaryFormula.{w, u, v} L k) (a : Fin k → M) :
    φ.not.Realize a ↔ ¬φ.Realize a := by
  rw [Realize]

@[simp] theorem realize_iSup {ι : Type w} (f : ι → InfinitaryFormula.{w, u, v} L k)
    (a : Fin k → M) : (iSup f).Realize a ↔ ∃ idx, (f idx).Realize a := by
  rw [Realize]

@[simp] theorem realize_ex (i : Fin k) (φ : InfinitaryFormula.{w, u, v} L k) (a : Fin k → M) :
    (ex i φ).Realize a ↔ ∃ c : M, φ.Realize (Function.update a i c) := by
  rw [Realize]

@[simp] theorem realize_bot (a : Fin k → M) :
    (bot : InfinitaryFormula.{w, u, v} L k).Realize a ↔ False := by
  simp only [bot, realize_iSup, IsEmpty.exists_iff]

@[simp] theorem realize_bot_inst (a : Fin k → M) :
    (⊥ : InfinitaryFormula.{w, u, v} L k).Realize a ↔ False :=
  realize_bot a

@[simp] theorem realize_top (a : Fin k → M) :
    (top : InfinitaryFormula.{w, u, v} L k).Realize a ↔ True := by
  simp only [top, realize_not, realize_bot, not_false_eq_true]

@[simp] theorem realize_top_inst (a : Fin k → M) :
    (⊤ : InfinitaryFormula.{w, u, v} L k).Realize a ↔ True :=
  realize_top a

@[simp] theorem realize_sup (φ ψ : InfinitaryFormula.{w, u, v} L k) (a : Fin k → M) :
    (sup φ ψ).Realize a ↔ φ.Realize a ∨ ψ.Realize a := by
  rw [sup, realize_iSup, ULift.exists, Bool.exists_bool]
  exact or_comm

@[simp] theorem realize_max (φ ψ : InfinitaryFormula.{w, u, v} L k) (a : Fin k → M) :
    (φ ⊔ ψ).Realize a ↔ φ.Realize a ∨ ψ.Realize a :=
  realize_sup φ ψ a

@[simp] theorem realize_iInf {ι : Type w} (f : ι → InfinitaryFormula.{w, u, v} L k)
    (a : Fin k → M) : (iInf f).Realize a ↔ ∀ idx, (f idx).Realize a := by
  simp only [iInf, realize_not, realize_iSup, not_exists, not_not]

@[simp] theorem realize_inf (φ ψ : InfinitaryFormula.{w, u, v} L k) (a : Fin k → M) :
    (inf φ ψ).Realize a ↔ φ.Realize a ∧ ψ.Realize a := by
  simp only [inf, realize_not, realize_sup, not_or, not_not]

@[simp] theorem realize_min (φ ψ : InfinitaryFormula.{w, u, v} L k) (a : Fin k → M) :
    (φ ⊓ ψ).Realize a ↔ φ.Realize a ∧ ψ.Realize a :=
  realize_inf φ ψ a

@[simp] theorem realize_imp (φ ψ : InfinitaryFormula.{w, u, v} L k) (a : Fin k → M) :
    (imp φ ψ).Realize a ↔ (φ.Realize a → ψ.Realize a) := by
  simp only [imp, realize_sup, realize_not, imp_iff_not_or]

@[simp] theorem realize_all (i : Fin k) (φ : InfinitaryFormula.{w, u, v} L k) (a : Fin k → M) :
    (all i φ).Realize a ↔ ∀ c : M, φ.Realize (Function.update a i c) := by
  simp only [all, realize_not, realize_ex, not_exists, not_not]

end Semantics

/-! #### Free variables of `L^k_{∞ω}` -/

/-- The set of free variables of an `L^k_{∞ω}` formula. -/
def freeVars : InfinitaryFormula.{w, u, v} L k → Set (Fin k)
  | equal i j => {i, j}
  | rel _ f => Set.range f
  | not φ => φ.freeVars
  | iSup f => ⋃ idx, (f idx).freeVars
  | ex i φ => φ.freeVars \ {i}

@[simp] theorem freeVars_equal (i j : Fin k) :
    (equal i j : InfinitaryFormula.{w, u, v} L k).freeVars = {i, j} := by
  rw [freeVars]

@[simp] theorem freeVars_rel {l : ℕ} (R : L.Relations l) (f : Fin l → Fin k) :
    (rel R f : InfinitaryFormula.{w, u, v} L k).freeVars = Set.range f := by
  rw [freeVars]

@[simp] theorem freeVars_not (φ : InfinitaryFormula.{w, u, v} L k) :
    φ.not.freeVars = φ.freeVars := by
  rw [freeVars]

@[simp] theorem freeVars_iSup {ι : Type w} (f : ι → InfinitaryFormula.{w, u, v} L k) :
    (iSup f).freeVars = ⋃ idx, (f idx).freeVars := by
  rw [freeVars]

@[simp] theorem freeVars_ex (i : Fin k) (φ : InfinitaryFormula.{w, u, v} L k) :
    (ex i φ).freeVars = φ.freeVars \ {i} := by
  rw [freeVars]

@[simp] theorem freeVars_bot : (bot : InfinitaryFormula.{w, u, v} L k).freeVars = ∅ := by
  simp only [bot, freeVars_iSup, Set.iUnion_of_empty]

@[simp] theorem freeVars_bot_inst : (⊥ : InfinitaryFormula.{w, u, v} L k).freeVars = ∅ :=
  freeVars_bot

@[simp] theorem freeVars_top : (top : InfinitaryFormula.{w, u, v} L k).freeVars = ∅ := by
  rw [top, freeVars_not, freeVars_bot]

@[simp] theorem freeVars_top_inst : (⊤ : InfinitaryFormula.{w, u, v} L k).freeVars = ∅ :=
  freeVars_top

@[simp] theorem freeVars_sup (φ ψ : InfinitaryFormula.{w, u, v} L k) :
    (sup φ ψ).freeVars = φ.freeVars ∪ ψ.freeVars := by
  ext x
  simp only [sup, freeVars_iSup, Set.mem_iUnion, ULift.exists, Bool.exists_bool, Set.mem_union]
  exact or_comm

@[simp] theorem freeVars_max (φ ψ : InfinitaryFormula.{w, u, v} L k) :
    (φ ⊔ ψ).freeVars = φ.freeVars ∪ ψ.freeVars :=
  freeVars_sup φ ψ

@[simp] theorem freeVars_iInf {ι : Type w} (f : ι → InfinitaryFormula.{w, u, v} L k) :
    (iInf f).freeVars = ⋃ idx, (f idx).freeVars := by
  simp only [iInf, freeVars_not, freeVars_iSup]

@[simp] theorem freeVars_inf (φ ψ : InfinitaryFormula.{w, u, v} L k) :
    (inf φ ψ).freeVars = φ.freeVars ∪ ψ.freeVars := by
  simp only [inf, freeVars_not, freeVars_sup]

@[simp] theorem freeVars_min (φ ψ : InfinitaryFormula.{w, u, v} L k) :
    (φ ⊓ ψ).freeVars = φ.freeVars ∪ ψ.freeVars :=
  freeVars_inf φ ψ

@[simp] theorem freeVars_imp (φ ψ : InfinitaryFormula.{w, u, v} L k) :
    (imp φ ψ).freeVars = φ.freeVars ∪ ψ.freeVars := by
  simp only [imp, freeVars_sup, freeVars_not]

@[simp] theorem freeVars_all (i : Fin k) (φ : InfinitaryFormula.{w, u, v} L k) :
    (all i φ).freeVars = φ.freeVars \ {i} := by
  simp only [all, freeVars_not, freeVars_ex]

/-- Truth of an `L^k_{∞ω}` formula depends only on the values of its free variables. -/
theorem realize_congr {M : Type w₁} [L.Structure M] {φ : InfinitaryFormula.{w, u, v} L k}
    {a a' : Fin k → M} (h : ∀ i ∈ φ.freeVars, a i = a' i) : φ.Realize a ↔ φ.Realize a' := by
  induction φ generalizing a a' with
  | equal i j =>
    simp only [freeVars_equal, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp,
      forall_eq] at h
    rw [realize_equal, realize_equal, h.1, h.2]
  | rel R f =>
    rw [realize_rel, realize_rel]
    have hcomp : a ∘ f = a' ∘ f := funext fun t => h (f t) ⟨t, rfl⟩
    rw [hcomp]
  | not φ ih =>
    exact not_congr (ih h)
  | iSup f ih =>
    simp only [freeVars_iSup, Set.mem_iUnion, forall_exists_index] at h
    exact exists_congr fun idx => ih idx fun i hi => h i idx hi
  | ex i φ ih =>
    simp only [freeVars_ex, Set.mem_sdiff, Set.mem_singleton_iff] at h
    refine exists_congr fun c => ih fun j hj => ?_
    by_cases hji : j = i
    · subst hji
      simp only [Function.update_self]
    · simp only [Function.update_of_ne hji, h j ⟨hj, hji⟩]

/-! #### Finite quantifier-rank bounds for `L^k_{∞ω}` -/

/-- `φ.QuantifierRankLE n` means every quantifier nesting chain in `φ` has depth at most `n`.
Formulas with unbounded quantifier depth across an infinite disjunction satisfy `QuantifierRankLE n`
for no `n : ℕ`. -/
def QuantifierRankLE : InfinitaryFormula.{w, u, v} L k → ℕ → Prop
  | equal _ _, _ => True
  | rel _ _, _ => True
  | not φ, n => φ.QuantifierRankLE n
  | iSup f, n => ∀ idx, (f idx).QuantifierRankLE n
  | ex _ _, 0 => False
  | ex _ φ, n + 1 => φ.QuantifierRankLE n

@[simp] theorem quantifierRankLE_equal (i j : Fin k) (n : ℕ) :
    (equal i j : InfinitaryFormula.{w, u, v} L k).QuantifierRankLE n ↔ True := by
  rw [QuantifierRankLE]

@[simp] theorem quantifierRankLE_rel {l : ℕ} (R : L.Relations l) (f : Fin l → Fin k) (n : ℕ) :
    (rel R f : InfinitaryFormula.{w, u, v} L k).QuantifierRankLE n ↔ True := by
  rw [QuantifierRankLE]

@[simp] theorem quantifierRankLE_not (φ : InfinitaryFormula.{w, u, v} L k) (n : ℕ) :
    φ.not.QuantifierRankLE n ↔ φ.QuantifierRankLE n := by
  rw [QuantifierRankLE]

@[simp] theorem quantifierRankLE_iSup {ι : Type w} (f : ι → InfinitaryFormula.{w, u, v} L k)
    (n : ℕ) : (iSup f).QuantifierRankLE n ↔ ∀ idx, (f idx).QuantifierRankLE n := by
  rw [QuantifierRankLE]

@[simp] theorem quantifierRankLE_ex_zero (i : Fin k) (φ : InfinitaryFormula.{w, u, v} L k) :
    (ex i φ).QuantifierRankLE 0 ↔ False := by
  rw [QuantifierRankLE]

@[simp] theorem quantifierRankLE_ex_succ (i : Fin k) (φ : InfinitaryFormula.{w, u, v} L k)
    (n : ℕ) : (ex i φ).QuantifierRankLE (n + 1) ↔ φ.QuantifierRankLE n := by
  rw [QuantifierRankLE]

@[simp] theorem quantifierRankLE_bot (n : ℕ) :
    (bot : InfinitaryFormula.{w, u, v} L k).QuantifierRankLE n ↔ True := by
  simp only [bot, quantifierRankLE_iSup, IsEmpty.forall_iff]

@[simp] theorem quantifierRankLE_bot_inst (n : ℕ) :
    (⊥ : InfinitaryFormula.{w, u, v} L k).QuantifierRankLE n ↔ True :=
  quantifierRankLE_bot n

@[simp] theorem quantifierRankLE_top (n : ℕ) :
    (top : InfinitaryFormula.{w, u, v} L k).QuantifierRankLE n ↔ True := by
  simp only [top, quantifierRankLE_not, quantifierRankLE_bot]

@[simp] theorem quantifierRankLE_top_inst (n : ℕ) :
    (⊤ : InfinitaryFormula.{w, u, v} L k).QuantifierRankLE n ↔ True :=
  quantifierRankLE_top n

@[simp] theorem quantifierRankLE_sup (φ ψ : InfinitaryFormula.{w, u, v} L k) (n : ℕ) :
    (sup φ ψ).QuantifierRankLE n ↔ φ.QuantifierRankLE n ∧ ψ.QuantifierRankLE n := by
  rw [sup, quantifierRankLE_iSup, ULift.forall, Bool.forall_bool]
  exact and_comm

@[simp] theorem quantifierRankLE_max (φ ψ : InfinitaryFormula.{w, u, v} L k) (n : ℕ) :
    (φ ⊔ ψ).QuantifierRankLE n ↔ φ.QuantifierRankLE n ∧ ψ.QuantifierRankLE n :=
  quantifierRankLE_sup φ ψ n

@[simp] theorem quantifierRankLE_iInf {ι : Type w} (f : ι → InfinitaryFormula.{w, u, v} L k)
    (n : ℕ) : (iInf f).QuantifierRankLE n ↔ ∀ idx, (f idx).QuantifierRankLE n := by
  simp only [iInf, quantifierRankLE_not, quantifierRankLE_iSup]

@[simp] theorem quantifierRankLE_inf (φ ψ : InfinitaryFormula.{w, u, v} L k) (n : ℕ) :
    (inf φ ψ).QuantifierRankLE n ↔ φ.QuantifierRankLE n ∧ ψ.QuantifierRankLE n := by
  simp only [inf, quantifierRankLE_not, quantifierRankLE_sup]

@[simp] theorem quantifierRankLE_min (φ ψ : InfinitaryFormula.{w, u, v} L k) (n : ℕ) :
    (φ ⊓ ψ).QuantifierRankLE n ↔ φ.QuantifierRankLE n ∧ ψ.QuantifierRankLE n :=
  quantifierRankLE_inf φ ψ n

@[simp] theorem quantifierRankLE_imp (φ ψ : InfinitaryFormula.{w, u, v} L k) (n : ℕ) :
    (imp φ ψ).QuantifierRankLE n ↔ φ.QuantifierRankLE n ∧ ψ.QuantifierRankLE n := by
  simp only [imp, quantifierRankLE_sup, quantifierRankLE_not]

@[simp] theorem quantifierRankLE_all_zero (i : Fin k) (φ : InfinitaryFormula.{w, u, v} L k) :
    (all i φ).QuantifierRankLE 0 ↔ False := by
  simp only [all, quantifierRankLE_not, quantifierRankLE_ex_zero]

@[simp] theorem quantifierRankLE_all_succ (i : Fin k) (φ : InfinitaryFormula.{w, u, v} L k)
    (n : ℕ) : (all i φ).QuantifierRankLE (n + 1) ↔ φ.QuantifierRankLE n := by
  simp only [all, quantifierRankLE_not, quantifierRankLE_ex_succ]

theorem QuantifierRankLE.mono {φ : InfinitaryFormula.{w, u, v} L k} {m n : ℕ} (hmn : m ≤ n)
    (h : φ.QuantifierRankLE m) : φ.QuantifierRankLE n := by
  induction φ generalizing m n with
  | equal _ _ => trivial
  | rel _ _ => trivial
  | not φ ih => exact ih hmn h
  | iSup f ih => exact fun idx => ih idx hmn (h idx)
  | ex i φ ih =>
    cases m with
    | zero => exact False.elim h
    | succ m =>
      cases n with
      | zero => omega
      | succ n => exact ih (by omega) h

end InfinitaryFormula

/-! ### Embedding `FO^k` into `L^k_{∞ω}` -/

namespace Formula

variable {L : Language.{u, v}} {k : ℕ}

/-- Embedding of `FO^k` into `L^k_{∞ω}` at any index universe `w`. -/
def toInfinitary : Formula L k → InfinitaryFormula.{w, u, v} L k
  | falsum => ⊥
  | equal i j => .equal i j
  | rel R f => .rel R f
  | imp φ ψ => .imp φ.toInfinitary ψ.toInfinitary
  | all i φ => .all i φ.toInfinitary

@[simp] theorem realize_toInfinitary {M : Type w₁} [L.Structure M] (φ : Formula L k)
    (a : Fin k → M) :
    (φ.toInfinitary : InfinitaryFormula.{w, u, v} L k).Realize a ↔ φ.Realize a := by
  induction φ generalizing a with
  | falsum => simp only [toInfinitary, InfinitaryFormula.realize_bot_inst, realize_falsum]
  | equal i j => simp only [toInfinitary, InfinitaryFormula.realize_equal, realize_equal]
  | rel R f => simp only [toInfinitary, InfinitaryFormula.realize_rel, realize_rel]
  | imp φ ψ ihφ ihψ =>
    simp only [toInfinitary, InfinitaryFormula.realize_imp, realize_imp, ihφ, ihψ]
  | all i φ ih =>
    simp only [toInfinitary, InfinitaryFormula.realize_all, realize_all]
    exact forall_congr' fun c => ih _

@[simp] theorem freeVars_toInfinitary (φ : Formula L k) :
    (φ.toInfinitary : InfinitaryFormula.{w, u, v} L k).freeVars = ↑φ.freeVars := by
  induction φ with
  | falsum =>
    simp only [toInfinitary, InfinitaryFormula.freeVars_bot_inst, freeVars_falsum,
      Finset.coe_empty]
  | equal i j =>
    simp only [toInfinitary, InfinitaryFormula.freeVars_equal, freeVars_equal, Finset.coe_insert,
      Finset.coe_singleton]
  | rel R f =>
    simp only [toInfinitary, InfinitaryFormula.freeVars_rel, freeVars_rel, Finset.coe_image,
      Finset.coe_univ, Set.image_univ]
  | imp φ ψ ihφ ihψ =>
    simp only [toInfinitary, InfinitaryFormula.freeVars_imp, freeVars_imp, Finset.coe_union,
      ihφ, ihψ]
  | all i φ ih =>
    simp only [toInfinitary, InfinitaryFormula.freeVars_all, freeVars_all, Finset.coe_erase, ih]

@[simp] theorem quantifierRankLE_toInfinitary (φ : Formula L k) (n : ℕ) :
    (φ.toInfinitary : InfinitaryFormula.{w, u, v} L k).QuantifierRankLE n ↔
      φ.quantifierRank ≤ n := by
  induction φ generalizing n with
  | falsum =>
    simp only [toInfinitary, InfinitaryFormula.quantifierRankLE_bot_inst, quantifierRank_falsum,
      Nat.zero_le]
  | equal i j =>
    simp only [toInfinitary, InfinitaryFormula.quantifierRankLE_equal, quantifierRank_equal,
      Nat.zero_le]
  | rel R f =>
    simp only [toInfinitary, InfinitaryFormula.quantifierRankLE_rel, quantifierRank_rel,
      Nat.zero_le]
  | imp φ ψ ihφ ihψ =>
    simp only [toInfinitary, InfinitaryFormula.quantifierRankLE_imp, quantifierRank_imp,
      max_le_iff, ihφ, ihψ]
  | all i φ ih =>
    cases n with
    | zero =>
      simp only [toInfinitary, InfinitaryFormula.quantifierRankLE_all_zero, quantifierRank_all,
        false_iff]
      omega
    | succ n =>
      simp only [toInfinitary, InfinitaryFormula.quantifierRankLE_all_succ, quantifierRank_all,
        Nat.succ_le_succ_iff, ih]

end Formula

/-! ### Infinitary `k`-variable counting logic `C^k_{∞ω}` -/

/-- Formulas of the infinitary `k`-variable counting logic `C^k_{∞ω}` over the relation symbols of
`L`, with counting quantifiers `atLeast m i φ` (`∃^{≥ m} xᵢ φ`) and arbitrary disjunctions indexed
by types in `Type w`. -/
inductive InfinitaryCountingFormula (L : Language.{u, v}) (k : ℕ) : Type (max v (w + 1))
  /-- The equation `xᵢ = xⱼ`. -/
  | equal (i j : Fin k) : InfinitaryCountingFormula L k
  /-- The relation `R` applied to the variables `x_{f 0}, …, x_{f (l - 1)}`. -/
  | rel {l : ℕ} (R : L.Relations l) (f : Fin l → Fin k) : InfinitaryCountingFormula L k
  /-- Negation. -/
  | not (φ : InfinitaryCountingFormula L k) : InfinitaryCountingFormula L k
  /-- Arbitrary disjunction indexed by `ι : Type w`. -/
  | iSup {ι : Type w} (f : ι → InfinitaryCountingFormula L k) : InfinitaryCountingFormula L k
  /-- The counting quantifier `∃^{≥ m} xᵢ φ`: at least `m` values of `xᵢ` satisfy `φ`. -/
  | atLeast (m : ℕ) (i : Fin k) (φ : InfinitaryCountingFormula L k) : InfinitaryCountingFormula L k

namespace InfinitaryCountingFormula

variable {L : Language.{u, v}} {k : ℕ}

/-- Falsity, as the empty disjunction. -/
def bot : InfinitaryCountingFormula.{w, u, v} L k :=
  iSup PEmpty.elim

/-- Truth, as the negation of falsity. -/
def top : InfinitaryCountingFormula.{w, u, v} L k :=
  bot.not

/-- Binary disjunction. -/
def sup (φ ψ : InfinitaryCountingFormula.{w, u, v} L k) :
    InfinitaryCountingFormula.{w, u, v} L k :=
  iSup fun b : ULift.{w} Bool => cond b.down φ ψ

/-- Arbitrary conjunction indexed by `ι : Type w`. -/
def iInf {ι : Type w} (f : ι → InfinitaryCountingFormula.{w, u, v} L k) :
    InfinitaryCountingFormula.{w, u, v} L k :=
  (iSup fun idx => (f idx).not).not

/-- Binary conjunction. -/
def inf (φ ψ : InfinitaryCountingFormula.{w, u, v} L k) :
    InfinitaryCountingFormula.{w, u, v} L k :=
  (sup φ.not ψ.not).not

/-- Implication. -/
def imp (φ ψ : InfinitaryCountingFormula.{w, u, v} L k) :
    InfinitaryCountingFormula.{w, u, v} L k :=
  sup φ.not ψ

/-- Existential quantification of `xᵢ`, as `atLeast 1 i φ`. -/
def ex (i : Fin k) (φ : InfinitaryCountingFormula.{w, u, v} L k) :
    InfinitaryCountingFormula.{w, u, v} L k :=
  atLeast 1 i φ

/-- Universal quantification of `xᵢ`. -/
def all (i : Fin k) (φ : InfinitaryCountingFormula.{w, u, v} L k) :
    InfinitaryCountingFormula.{w, u, v} L k :=
  (ex i φ.not).not

/-- Exact counting quantifier `∃^{= m} xᵢ φ`: at least `m` and fewer than `m + 1` values of `xᵢ`
satisfy `φ`. -/
def exactly (m : ℕ) (i : Fin k) (φ : InfinitaryCountingFormula.{w, u, v} L k) :
    InfinitaryCountingFormula.{w, u, v} L k :=
  inf (atLeast m i φ) (atLeast (m + 1) i φ).not

instance : Bot (InfinitaryCountingFormula.{w, u, v} L k) := ⟨bot⟩
instance : Top (InfinitaryCountingFormula.{w, u, v} L k) := ⟨top⟩
instance : Max (InfinitaryCountingFormula.{w, u, v} L k) := ⟨sup⟩
instance : Min (InfinitaryCountingFormula.{w, u, v} L k) := ⟨inf⟩

/-! #### Semantics of `C^k_{∞ω}` -/

/-- Truth of a `C^k_{∞ω}` formula in `M` under the assignment `a : Fin k → M`, counting witnesses
by `Set.encard`. -/
def Realize {M : Type w₁} [L.Structure M] :
    InfinitaryCountingFormula.{w, u, v} L k → (Fin k → M) → Prop
  | equal i j, a => a i = a j
  | rel R f, a => RelMap R (a ∘ f)
  | not φ, a => ¬φ.Realize a
  | iSup f, a => ∃ idx, (f idx).Realize a
  | atLeast m i φ, a => (m : ℕ∞) ≤ {c : M | φ.Realize (Function.update a i c)}.encard

section Semantics

variable {M : Type w₁} [L.Structure M]

@[simp] theorem realize_equal (i j : Fin k) (a : Fin k → M) :
    (equal i j : InfinitaryCountingFormula.{w, u, v} L k).Realize a ↔ a i = a j := by
  rw [Realize]

@[simp] theorem realize_rel {l : ℕ} (R : L.Relations l) (f : Fin l → Fin k) (a : Fin k → M) :
    (rel R f : InfinitaryCountingFormula.{w, u, v} L k).Realize a ↔ RelMap R (a ∘ f) := by
  rw [Realize]

@[simp] theorem realize_not (φ : InfinitaryCountingFormula.{w, u, v} L k) (a : Fin k → M) :
    φ.not.Realize a ↔ ¬φ.Realize a := by
  rw [Realize]

@[simp] theorem realize_iSup {ι : Type w} (f : ι → InfinitaryCountingFormula.{w, u, v} L k)
    (a : Fin k → M) : (iSup f).Realize a ↔ ∃ idx, (f idx).Realize a := by
  rw [Realize]

@[simp] theorem realize_atLeast (m : ℕ) (i : Fin k)
    (φ : InfinitaryCountingFormula.{w, u, v} L k) (a : Fin k → M) :
    (atLeast m i φ).Realize a ↔
      (m : ℕ∞) ≤ {c : M | φ.Realize (Function.update a i c)}.encard := by
  rw [Realize]

@[simp] theorem realize_bot (a : Fin k → M) :
    (bot : InfinitaryCountingFormula.{w, u, v} L k).Realize a ↔ False := by
  simp only [bot, realize_iSup, IsEmpty.exists_iff]

@[simp] theorem realize_bot_inst (a : Fin k → M) :
    (⊥ : InfinitaryCountingFormula.{w, u, v} L k).Realize a ↔ False :=
  realize_bot a

@[simp] theorem realize_top (a : Fin k → M) :
    (top : InfinitaryCountingFormula.{w, u, v} L k).Realize a ↔ True := by
  simp only [top, realize_not, realize_bot, not_false_eq_true]

@[simp] theorem realize_top_inst (a : Fin k → M) :
    (⊤ : InfinitaryCountingFormula.{w, u, v} L k).Realize a ↔ True :=
  realize_top a

@[simp] theorem realize_sup (φ ψ : InfinitaryCountingFormula.{w, u, v} L k) (a : Fin k → M) :
    (sup φ ψ).Realize a ↔ φ.Realize a ∨ ψ.Realize a := by
  rw [sup, realize_iSup, ULift.exists, Bool.exists_bool]
  exact or_comm

@[simp] theorem realize_max (φ ψ : InfinitaryCountingFormula.{w, u, v} L k) (a : Fin k → M) :
    (φ ⊔ ψ).Realize a ↔ φ.Realize a ∨ ψ.Realize a :=
  realize_sup φ ψ a

@[simp] theorem realize_iInf {ι : Type w} (f : ι → InfinitaryCountingFormula.{w, u, v} L k)
    (a : Fin k → M) : (iInf f).Realize a ↔ ∀ idx, (f idx).Realize a := by
  simp only [iInf, realize_not, realize_iSup, not_exists, not_not]

@[simp] theorem realize_inf (φ ψ : InfinitaryCountingFormula.{w, u, v} L k) (a : Fin k → M) :
    (inf φ ψ).Realize a ↔ φ.Realize a ∧ ψ.Realize a := by
  simp only [inf, realize_not, realize_sup, not_or, not_not]

@[simp] theorem realize_min (φ ψ : InfinitaryCountingFormula.{w, u, v} L k) (a : Fin k → M) :
    (φ ⊓ ψ).Realize a ↔ φ.Realize a ∧ ψ.Realize a :=
  realize_inf φ ψ a

@[simp] theorem realize_imp (φ ψ : InfinitaryCountingFormula.{w, u, v} L k) (a : Fin k → M) :
    (imp φ ψ).Realize a ↔ (φ.Realize a → ψ.Realize a) := by
  simp only [imp, realize_sup, realize_not, imp_iff_not_or]

@[simp] theorem realize_ex (i : Fin k) (φ : InfinitaryCountingFormula.{w, u, v} L k)
    (a : Fin k → M) :
    (ex i φ).Realize a ↔ ∃ c : M, φ.Realize (Function.update a i c) := by
  rw [ex, realize_atLeast, Nat.cast_one, Set.one_le_encard_iff_nonempty]
  rfl

@[simp] theorem realize_all (i : Fin k) (φ : InfinitaryCountingFormula.{w, u, v} L k)
    (a : Fin k → M) :
    (all i φ).Realize a ↔ ∀ c : M, φ.Realize (Function.update a i c) := by
  simp only [all, realize_not, realize_ex, not_exists, not_not]

@[simp] theorem realize_exactly (m : ℕ) (i : Fin k)
    (φ : InfinitaryCountingFormula.{w, u, v} L k) (a : Fin k → M) :
    (exactly m i φ).Realize a ↔
      {c : M | φ.Realize (Function.update a i c)}.encard = m := by
  rw [exactly, realize_inf, realize_not, realize_atLeast, realize_atLeast]
  generalize {c : M | φ.Realize (Function.update a i c)}.encard = e
  induction e using ENat.recTopCoe with
  | top => simp only [le_top, not_true_eq_false, and_false, ENat.top_ne_natCast]
  | coe e =>
    norm_cast
    omega

theorem realize_atLeast_iff_ncard [Finite M] (m : ℕ) (i : Fin k)
    (φ : InfinitaryCountingFormula.{w, u, v} L k) (a : Fin k → M) :
    (atLeast m i φ).Realize a ↔ m ≤ {c : M | φ.Realize (Function.update a i c)}.ncard := by
  rw [realize_atLeast, ← (Set.toFinite _).cast_ncard_eq, Nat.cast_le]

theorem realize_exactly_iff_ncard [Finite M] (m : ℕ) (i : Fin k)
    (φ : InfinitaryCountingFormula.{w, u, v} L k) (a : Fin k → M) :
    (exactly m i φ).Realize a ↔ {c : M | φ.Realize (Function.update a i c)}.ncard = m := by
  rw [realize_exactly, ← (Set.toFinite _).cast_ncard_eq, Nat.cast_inj]

end Semantics

/-! #### Free variables of `C^k_{∞ω}` -/

/-- The set of free variables of a `C^k_{∞ω}` formula. -/
def freeVars : InfinitaryCountingFormula.{w, u, v} L k → Set (Fin k)
  | equal i j => {i, j}
  | rel _ f => Set.range f
  | not φ => φ.freeVars
  | iSup f => ⋃ idx, (f idx).freeVars
  | atLeast _ i φ => φ.freeVars \ {i}

@[simp] theorem freeVars_equal (i j : Fin k) :
    (equal i j : InfinitaryCountingFormula.{w, u, v} L k).freeVars = {i, j} := by
  rw [freeVars]

@[simp] theorem freeVars_rel {l : ℕ} (R : L.Relations l) (f : Fin l → Fin k) :
    (rel R f : InfinitaryCountingFormula.{w, u, v} L k).freeVars = Set.range f := by
  rw [freeVars]

@[simp] theorem freeVars_not (φ : InfinitaryCountingFormula.{w, u, v} L k) :
    φ.not.freeVars = φ.freeVars := by
  rw [freeVars]

@[simp] theorem freeVars_iSup {ι : Type w} (f : ι → InfinitaryCountingFormula.{w, u, v} L k) :
    (iSup f).freeVars = ⋃ idx, (f idx).freeVars := by
  rw [freeVars]

@[simp] theorem freeVars_atLeast (m : ℕ) (i : Fin k)
    (φ : InfinitaryCountingFormula.{w, u, v} L k) :
    (atLeast m i φ).freeVars = φ.freeVars \ {i} := by
  rw [freeVars]

@[simp] theorem freeVars_bot :
    (bot : InfinitaryCountingFormula.{w, u, v} L k).freeVars = ∅ := by
  simp only [bot, freeVars_iSup, Set.iUnion_of_empty]

@[simp] theorem freeVars_bot_inst :
    (⊥ : InfinitaryCountingFormula.{w, u, v} L k).freeVars = ∅ :=
  freeVars_bot

@[simp] theorem freeVars_top :
    (top : InfinitaryCountingFormula.{w, u, v} L k).freeVars = ∅ := by
  rw [top, freeVars_not, freeVars_bot]

@[simp] theorem freeVars_top_inst :
    (⊤ : InfinitaryCountingFormula.{w, u, v} L k).freeVars = ∅ :=
  freeVars_top

@[simp] theorem freeVars_sup (φ ψ : InfinitaryCountingFormula.{w, u, v} L k) :
    (sup φ ψ).freeVars = φ.freeVars ∪ ψ.freeVars := by
  ext x
  simp only [sup, freeVars_iSup, Set.mem_iUnion, ULift.exists, Bool.exists_bool, Set.mem_union]
  exact or_comm

@[simp] theorem freeVars_max (φ ψ : InfinitaryCountingFormula.{w, u, v} L k) :
    (φ ⊔ ψ).freeVars = φ.freeVars ∪ ψ.freeVars :=
  freeVars_sup φ ψ

@[simp] theorem freeVars_iInf {ι : Type w} (f : ι → InfinitaryCountingFormula.{w, u, v} L k) :
    (iInf f).freeVars = ⋃ idx, (f idx).freeVars := by
  simp only [iInf, freeVars_not, freeVars_iSup]

@[simp] theorem freeVars_inf (φ ψ : InfinitaryCountingFormula.{w, u, v} L k) :
    (inf φ ψ).freeVars = φ.freeVars ∪ ψ.freeVars := by
  simp only [inf, freeVars_not, freeVars_sup]

@[simp] theorem freeVars_min (φ ψ : InfinitaryCountingFormula.{w, u, v} L k) :
    (φ ⊓ ψ).freeVars = φ.freeVars ∪ ψ.freeVars :=
  freeVars_inf φ ψ

@[simp] theorem freeVars_imp (φ ψ : InfinitaryCountingFormula.{w, u, v} L k) :
    (imp φ ψ).freeVars = φ.freeVars ∪ ψ.freeVars := by
  simp only [imp, freeVars_sup, freeVars_not]

@[simp] theorem freeVars_ex (i : Fin k) (φ : InfinitaryCountingFormula.{w, u, v} L k) :
    (ex i φ).freeVars = φ.freeVars \ {i} :=
  freeVars_atLeast 1 i φ

@[simp] theorem freeVars_all (i : Fin k) (φ : InfinitaryCountingFormula.{w, u, v} L k) :
    (all i φ).freeVars = φ.freeVars \ {i} := by
  simp only [all, freeVars_not, freeVars_ex]

@[simp] theorem freeVars_exactly (m : ℕ) (i : Fin k)
    (φ : InfinitaryCountingFormula.{w, u, v} L k) :
    (exactly m i φ).freeVars = φ.freeVars \ {i} := by
  simp only [exactly, freeVars_inf, freeVars_not, freeVars_atLeast, Set.union_self]

/-- Truth of a `C^k_{∞ω}` formula depends only on the values of its free variables. -/
theorem realize_congr {M : Type w₁} [L.Structure M]
    {φ : InfinitaryCountingFormula.{w, u, v} L k} {a a' : Fin k → M}
    (h : ∀ i ∈ φ.freeVars, a i = a' i) : φ.Realize a ↔ φ.Realize a' := by
  induction φ generalizing a a' with
  | equal i j =>
    simp only [freeVars_equal, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp,
      forall_eq] at h
    rw [realize_equal, realize_equal, h.1, h.2]
  | rel R f =>
    rw [realize_rel, realize_rel]
    have hcomp : a ∘ f = a' ∘ f := funext fun t => h (f t) ⟨t, rfl⟩
    rw [hcomp]
  | not φ ih =>
    exact not_congr (ih h)
  | iSup f ih =>
    simp only [freeVars_iSup, Set.mem_iUnion, forall_exists_index] at h
    exact exists_congr fun idx => ih idx fun i hi => h i idx hi
  | atLeast m i φ ih =>
    simp only [freeVars_atLeast, Set.mem_sdiff, Set.mem_singleton_iff] at h
    rw [realize_atLeast, realize_atLeast]
    suffices hs : {c : M | φ.Realize (Function.update a i c)} =
        {c : M | φ.Realize (Function.update a' i c)} by rw [hs]
    refine Set.ext fun c => ih fun j hj => ?_
    by_cases hji : j = i
    · subst hji
      simp only [Function.update_self]
    · simp only [Function.update_of_ne hji, h j ⟨hj, hji⟩]

/-! #### Finite quantifier-rank bounds for `C^k_{∞ω}` -/

/-- `φ.QuantifierRankLE n` means every counting-quantifier nesting chain in `φ` has depth at most
`n`. -/
def QuantifierRankLE : InfinitaryCountingFormula.{w, u, v} L k → ℕ → Prop
  | equal _ _, _ => True
  | rel _ _, _ => True
  | not φ, n => φ.QuantifierRankLE n
  | iSup f, n => ∀ idx, (f idx).QuantifierRankLE n
  | atLeast _ _ _, 0 => False
  | atLeast _ _ φ, n + 1 => φ.QuantifierRankLE n

@[simp] theorem quantifierRankLE_equal (i j : Fin k) (n : ℕ) :
    (equal i j : InfinitaryCountingFormula.{w, u, v} L k).QuantifierRankLE n ↔ True := by
  rw [QuantifierRankLE]

@[simp] theorem quantifierRankLE_rel {l : ℕ} (R : L.Relations l) (f : Fin l → Fin k) (n : ℕ) :
    (rel R f : InfinitaryCountingFormula.{w, u, v} L k).QuantifierRankLE n ↔ True := by
  rw [QuantifierRankLE]

@[simp] theorem quantifierRankLE_not (φ : InfinitaryCountingFormula.{w, u, v} L k) (n : ℕ) :
    φ.not.QuantifierRankLE n ↔ φ.QuantifierRankLE n := by
  rw [QuantifierRankLE]

@[simp] theorem quantifierRankLE_iSup {ι : Type w}
    (f : ι → InfinitaryCountingFormula.{w, u, v} L k) (n : ℕ) :
    (iSup f).QuantifierRankLE n ↔ ∀ idx, (f idx).QuantifierRankLE n := by
  rw [QuantifierRankLE]

@[simp] theorem quantifierRankLE_atLeast_zero (m : ℕ) (i : Fin k)
    (φ : InfinitaryCountingFormula.{w, u, v} L k) :
    (atLeast m i φ).QuantifierRankLE 0 ↔ False := by
  rw [QuantifierRankLE]

@[simp] theorem quantifierRankLE_atLeast_succ (m : ℕ) (i : Fin k)
    (φ : InfinitaryCountingFormula.{w, u, v} L k) (n : ℕ) :
    (atLeast m i φ).QuantifierRankLE (n + 1) ↔ φ.QuantifierRankLE n := by
  rw [QuantifierRankLE]

@[simp] theorem quantifierRankLE_bot (n : ℕ) :
    (bot : InfinitaryCountingFormula.{w, u, v} L k).QuantifierRankLE n ↔ True := by
  simp only [bot, quantifierRankLE_iSup, IsEmpty.forall_iff]

@[simp] theorem quantifierRankLE_bot_inst (n : ℕ) :
    (⊥ : InfinitaryCountingFormula.{w, u, v} L k).QuantifierRankLE n ↔ True :=
  quantifierRankLE_bot n

@[simp] theorem quantifierRankLE_top (n : ℕ) :
    (top : InfinitaryCountingFormula.{w, u, v} L k).QuantifierRankLE n ↔ True := by
  simp only [top, quantifierRankLE_not, quantifierRankLE_bot]

@[simp] theorem quantifierRankLE_top_inst (n : ℕ) :
    (⊤ : InfinitaryCountingFormula.{w, u, v} L k).QuantifierRankLE n ↔ True :=
  quantifierRankLE_top n

@[simp] theorem quantifierRankLE_sup (φ ψ : InfinitaryCountingFormula.{w, u, v} L k) (n : ℕ) :
    (sup φ ψ).QuantifierRankLE n ↔ φ.QuantifierRankLE n ∧ ψ.QuantifierRankLE n := by
  rw [sup, quantifierRankLE_iSup, ULift.forall, Bool.forall_bool]
  exact and_comm

@[simp] theorem quantifierRankLE_max (φ ψ : InfinitaryCountingFormula.{w, u, v} L k) (n : ℕ) :
    (φ ⊔ ψ).QuantifierRankLE n ↔ φ.QuantifierRankLE n ∧ ψ.QuantifierRankLE n :=
  quantifierRankLE_sup φ ψ n

@[simp] theorem quantifierRankLE_iInf {ι : Type w}
    (f : ι → InfinitaryCountingFormula.{w, u, v} L k) (n : ℕ) :
    (iInf f).QuantifierRankLE n ↔ ∀ idx, (f idx).QuantifierRankLE n := by
  simp only [iInf, quantifierRankLE_not, quantifierRankLE_iSup]

@[simp] theorem quantifierRankLE_inf (φ ψ : InfinitaryCountingFormula.{w, u, v} L k) (n : ℕ) :
    (inf φ ψ).QuantifierRankLE n ↔ φ.QuantifierRankLE n ∧ ψ.QuantifierRankLE n := by
  simp only [inf, quantifierRankLE_not, quantifierRankLE_sup]

@[simp] theorem quantifierRankLE_min (φ ψ : InfinitaryCountingFormula.{w, u, v} L k) (n : ℕ) :
    (φ ⊓ ψ).QuantifierRankLE n ↔ φ.QuantifierRankLE n ∧ ψ.QuantifierRankLE n :=
  quantifierRankLE_inf φ ψ n

@[simp] theorem quantifierRankLE_imp (φ ψ : InfinitaryCountingFormula.{w, u, v} L k) (n : ℕ) :
    (imp φ ψ).QuantifierRankLE n ↔ φ.QuantifierRankLE n ∧ ψ.QuantifierRankLE n := by
  simp only [imp, quantifierRankLE_sup, quantifierRankLE_not]

@[simp] theorem quantifierRankLE_ex_zero (i : Fin k)
    (φ : InfinitaryCountingFormula.{w, u, v} L k) :
    (ex i φ).QuantifierRankLE 0 ↔ False :=
  quantifierRankLE_atLeast_zero 1 i φ

@[simp] theorem quantifierRankLE_ex_succ (i : Fin k)
    (φ : InfinitaryCountingFormula.{w, u, v} L k) (n : ℕ) :
    (ex i φ).QuantifierRankLE (n + 1) ↔ φ.QuantifierRankLE n :=
  quantifierRankLE_atLeast_succ 1 i φ n

@[simp] theorem quantifierRankLE_all_zero (i : Fin k)
    (φ : InfinitaryCountingFormula.{w, u, v} L k) :
    (all i φ).QuantifierRankLE 0 ↔ False := by
  simp only [all, quantifierRankLE_not, quantifierRankLE_ex_zero]

@[simp] theorem quantifierRankLE_all_succ (i : Fin k)
    (φ : InfinitaryCountingFormula.{w, u, v} L k) (n : ℕ) :
    (all i φ).QuantifierRankLE (n + 1) ↔ φ.QuantifierRankLE n := by
  simp only [all, quantifierRankLE_not, quantifierRankLE_ex_succ]

@[simp] theorem quantifierRankLE_exactly_zero (m : ℕ) (i : Fin k)
    (φ : InfinitaryCountingFormula.{w, u, v} L k) :
    (exactly m i φ).QuantifierRankLE 0 ↔ False := by
  simp only [exactly, quantifierRankLE_inf, quantifierRankLE_not, quantifierRankLE_atLeast_zero,
    and_self]

@[simp] theorem quantifierRankLE_exactly_succ (m : ℕ) (i : Fin k)
    (φ : InfinitaryCountingFormula.{w, u, v} L k) (n : ℕ) :
    (exactly m i φ).QuantifierRankLE (n + 1) ↔ φ.QuantifierRankLE n := by
  simp only [exactly, quantifierRankLE_inf, quantifierRankLE_not, quantifierRankLE_atLeast_succ,
    and_self]

theorem QuantifierRankLE.mono {φ : InfinitaryCountingFormula.{w, u, v} L k} {m n : ℕ}
    (hmn : m ≤ n) (h : φ.QuantifierRankLE m) : φ.QuantifierRankLE n := by
  induction φ generalizing m n with
  | equal _ _ => trivial
  | rel _ _ => trivial
  | not φ ih => exact ih hmn h
  | iSup f ih => exact fun idx => ih idx hmn (h idx)
  | atLeast c i φ ih =>
    cases m with
    | zero => exact False.elim h
    | succ m =>
      cases n with
      | zero => omega
      | succ n => exact ih (by omega) h

end InfinitaryCountingFormula

/-! ### Embeddings into `C^k_{∞ω}` -/

namespace CountingFormula

variable {L : Language.{u, v}} {k : ℕ}

/-- Embedding of `C^k` into `C^k_{∞ω}` at any index universe `w`. -/
def toInfinitary : CountingFormula L k → InfinitaryCountingFormula.{w, u, v} L k
  | falsum => ⊥
  | equal i j => .equal i j
  | rel R f => .rel R f
  | imp φ ψ => .imp φ.toInfinitary ψ.toInfinitary
  | atLeast m i φ => .atLeast m i φ.toInfinitary

@[simp] theorem realize_toInfinitary {M : Type w₁} [L.Structure M] (φ : CountingFormula L k)
    (a : Fin k → M) :
    (φ.toInfinitary : InfinitaryCountingFormula.{w, u, v} L k).Realize a ↔ φ.Realize a := by
  induction φ generalizing a with
  | falsum =>
    simp only [toInfinitary, InfinitaryCountingFormula.realize_bot_inst, realize_falsum]
  | equal i j =>
    simp only [toInfinitary, InfinitaryCountingFormula.realize_equal, realize_equal]
  | rel R f =>
    simp only [toInfinitary, InfinitaryCountingFormula.realize_rel, realize_rel]
  | imp φ ψ ihφ ihψ =>
    simp only [toInfinitary, InfinitaryCountingFormula.realize_imp, realize_imp, ihφ, ihψ]
  | atLeast m i φ ih =>
    simp only [toInfinitary, InfinitaryCountingFormula.realize_atLeast, realize_atLeast]
    have hs : {c : M | (φ.toInfinitary : InfinitaryCountingFormula.{w, u, v} L k).Realize
        (Function.update a i c)} = {c : M | φ.Realize (Function.update a i c)} :=
      Set.ext fun c => ih _
    rw [hs]

@[simp] theorem freeVars_toInfinitary (φ : CountingFormula L k) :
    (φ.toInfinitary : InfinitaryCountingFormula.{w, u, v} L k).freeVars = ↑φ.freeVars := by
  induction φ with
  | falsum =>
    simp only [toInfinitary, InfinitaryCountingFormula.freeVars_bot_inst, freeVars_falsum,
      Finset.coe_empty]
  | equal i j =>
    simp only [toInfinitary, InfinitaryCountingFormula.freeVars_equal, freeVars_equal,
      Finset.coe_insert, Finset.coe_singleton]
  | rel R f =>
    simp only [toInfinitary, InfinitaryCountingFormula.freeVars_rel, freeVars_rel,
      Finset.coe_image, Finset.coe_univ, Set.image_univ]
  | imp φ ψ ihφ ihψ =>
    simp only [toInfinitary, InfinitaryCountingFormula.freeVars_imp, freeVars_imp,
      Finset.coe_union, ihφ, ihψ]
  | atLeast m i φ ih =>
    simp only [toInfinitary, InfinitaryCountingFormula.freeVars_atLeast, freeVars_atLeast,
      Finset.coe_erase, ih]

@[simp] theorem quantifierRankLE_toInfinitary (φ : CountingFormula L k) (n : ℕ) :
    (φ.toInfinitary : InfinitaryCountingFormula.{w, u, v} L k).QuantifierRankLE n ↔
      φ.quantifierRank ≤ n := by
  induction φ generalizing n with
  | falsum =>
    simp only [toInfinitary, InfinitaryCountingFormula.quantifierRankLE_bot_inst,
      quantifierRank_falsum, Nat.zero_le]
  | equal i j =>
    simp only [toInfinitary, InfinitaryCountingFormula.quantifierRankLE_equal,
      quantifierRank_equal, Nat.zero_le]
  | rel R f =>
    simp only [toInfinitary, InfinitaryCountingFormula.quantifierRankLE_rel,
      quantifierRank_rel, Nat.zero_le]
  | imp φ ψ ihφ ihψ =>
    simp only [toInfinitary, InfinitaryCountingFormula.quantifierRankLE_imp, quantifierRank_imp,
      max_le_iff, ihφ, ihψ]
  | atLeast m i φ ih =>
    cases n with
    | zero =>
      simp only [toInfinitary, InfinitaryCountingFormula.quantifierRankLE_atLeast_zero,
        quantifierRank_atLeast, false_iff]
      omega
    | succ n =>
      simp only [toInfinitary, InfinitaryCountingFormula.quantifierRankLE_atLeast_succ,
        quantifierRank_atLeast, Nat.succ_le_succ_iff, ih]

end CountingFormula

namespace InfinitaryFormula

variable {L : Language.{u, v}} {k : ℕ}

/-- Embedding of `L^k_{∞ω}` into `C^k_{∞ω}` translating `ex i φ` as `atLeast 1 i φ`. -/
def toCounting : InfinitaryFormula.{w, u, v} L k → InfinitaryCountingFormula.{w, u, v} L k
  | equal i j => .equal i j
  | rel R f => .rel R f
  | not φ => φ.toCounting.not
  | iSup f => .iSup fun idx => (f idx).toCounting
  | ex i φ => .ex i φ.toCounting

@[simp] theorem realize_toCounting {M : Type w₁} [L.Structure M]
    (φ : InfinitaryFormula.{w, u, v} L k) (a : Fin k → M) :
    φ.toCounting.Realize a ↔ φ.Realize a := by
  induction φ generalizing a with
  | equal i j =>
    simp only [toCounting, InfinitaryCountingFormula.realize_equal, realize_equal]
  | rel R f =>
    simp only [toCounting, InfinitaryCountingFormula.realize_rel, realize_rel]
  | not φ ih =>
    simp only [toCounting, InfinitaryCountingFormula.realize_not, realize_not, ih]
  | iSup f ih =>
    simp only [toCounting, InfinitaryCountingFormula.realize_iSup, realize_iSup]
    exact exists_congr fun idx => ih idx a
  | ex i φ ih =>
    simp only [toCounting, InfinitaryCountingFormula.realize_ex, realize_ex]
    exact exists_congr fun c => ih _

@[simp] theorem freeVars_toCounting (φ : InfinitaryFormula.{w, u, v} L k) :
    φ.toCounting.freeVars = φ.freeVars := by
  induction φ with
  | equal i j =>
    simp only [toCounting, InfinitaryCountingFormula.freeVars_equal, freeVars_equal]
  | rel R f =>
    simp only [toCounting, InfinitaryCountingFormula.freeVars_rel, freeVars_rel]
  | not φ ih =>
    simp only [toCounting, InfinitaryCountingFormula.freeVars_not, freeVars_not, ih]
  | iSup f ih =>
    simp only [toCounting, InfinitaryCountingFormula.freeVars_iSup, freeVars_iSup, ih]
  | ex i φ ih =>
    simp only [toCounting, InfinitaryCountingFormula.freeVars_ex, freeVars_ex, ih]

@[simp] theorem quantifierRankLE_toCounting (φ : InfinitaryFormula.{w, u, v} L k) (n : ℕ) :
    φ.toCounting.QuantifierRankLE n ↔ φ.QuantifierRankLE n := by
  induction φ generalizing n with
  | equal i j =>
    simp only [toCounting, InfinitaryCountingFormula.quantifierRankLE_equal,
      quantifierRankLE_equal]
  | rel R f =>
    simp only [toCounting, InfinitaryCountingFormula.quantifierRankLE_rel, quantifierRankLE_rel]
  | not φ ih =>
    simp only [toCounting, InfinitaryCountingFormula.quantifierRankLE_not, quantifierRankLE_not,
      ih]
  | iSup f ih =>
    simp only [toCounting, InfinitaryCountingFormula.quantifierRankLE_iSup,
      quantifierRankLE_iSup, ih]
  | ex i φ ih =>
    cases n with
    | zero =>
      simp only [toCounting, InfinitaryCountingFormula.quantifierRankLE_ex_zero,
        quantifierRankLE_ex_zero]
    | succ n =>
      simp only [toCounting, InfinitaryCountingFormula.quantifierRankLE_ex_succ,
        quantifierRankLE_ex_succ, ih]

end InfinitaryFormula

end Cslib.Logic.FO.FiniteVariable

/-! ### Pebble-game characterizations of `L^k_{∞ω}` and `C^k_{∞ω}` -/

namespace Cslib.Logic.FO

open FiniteVariable

section PebbleCharacterization

variable {L : Language.{u, v}} {M : Type w₁} {N : Type w₂}
  [L.Structure M] [L.Structure N] {k : ℕ}

/-- **Pebble games and `L^k_{∞ω}`, easy direction (finite rounds).** A winning position of the
`n`-round `k`-pebble game preserves every `L^k_{∞ω}` formula of quantifier rank at most `n` whose
free variables lie in `S`, regardless of vocabulary size, structure cardinality, or disjunction
universe `w`. -/
theorem PebbleWins.realize_infinitaryFormula_iff {n : ℕ} {S : Set (Fin k)} {a : Fin k → M}
    {b : Fin k → N} (h : PebbleWins L n S a b) {φ : InfinitaryFormula.{w, u, v} L k}
    (hr : φ.QuantifierRankLE n) (hS : φ.freeVars ⊆ S) : φ.Realize a ↔ φ.Realize b := by
  induction φ generalizing n S a b with
  | equal i j =>
    simp only [InfinitaryFormula.freeVars_equal, Set.insert_subset_iff,
      Set.singleton_subset_iff] at hS
    exact h.partialIsoOn.eq_iff i hS.1 j hS.2
  | rel R f =>
    simp only [InfinitaryFormula.freeVars_rel, Set.range_subset_iff] at hS
    exact h.partialIsoOn.relMap_iff R f hS
  | not φ ih =>
    exact not_congr (ih h hr hS)
  | iSup f ih =>
    simp only [InfinitaryFormula.quantifierRankLE_iSup] at hr
    simp only [InfinitaryFormula.freeVars_iSup, Set.iUnion_subset_iff] at hS
    exact exists_congr fun idx => ih idx h (hr idx) (hS idx)
  | ex i φ ih =>
    cases n with
    | zero => exact False.elim hr
    | succ n =>
      simp only [InfinitaryFormula.quantifierRankLE_ex_succ] at hr
      rw [InfinitaryFormula.freeVars_ex, Set.sdiff_subset_iff, Set.singleton_union] at hS
      simp only [InfinitaryFormula.realize_ex]
      constructor
      · rintro ⟨c, hc⟩
        obtain ⟨d, hd⟩ := h.forth i c
        exact ⟨d, (ih hd hr hS).1 hc⟩
      · rintro ⟨d, hd⟩
        obtain ⟨c, hc⟩ := h.back i d
        exact ⟨c, (ih hc hr hS).2 hd⟩

/-- **Back-and-forth invariants and `L^k_{∞ω}`.** Any position in a `k`-pebble back-and-forth
invariant preserves every `L^k_{∞ω}` formula whose free variables lie in `S`, regardless of
structure cardinality or unbounded quantifier depth across infinite disjunctions. -/
theorem IsPebbleBackAndForth.realize_infinitaryFormula_iff
    {I : Set (Fin k) → (Fin k → M) → (Fin k → N) → Prop} (hI : IsPebbleBackAndForth L I)
    {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N} (hSab : I S a b)
    {φ : InfinitaryFormula.{w, u, v} L k} (hS : φ.freeVars ⊆ S) :
    φ.Realize a ↔ φ.Realize b := by
  induction φ generalizing S a b with
  | equal i j =>
    simp only [InfinitaryFormula.freeVars_equal, Set.insert_subset_iff,
      Set.singleton_subset_iff] at hS
    exact (hI.partialIsoOn hSab).eq_iff i hS.1 j hS.2
  | rel R f =>
    simp only [InfinitaryFormula.freeVars_rel, Set.range_subset_iff] at hS
    exact (hI.partialIsoOn hSab).relMap_iff R f hS
  | not φ ih =>
    exact not_congr (ih hSab hS)
  | iSup f ih =>
    simp only [InfinitaryFormula.freeVars_iSup, Set.iUnion_subset_iff] at hS
    exact exists_congr fun idx => ih idx hSab (hS idx)
  | ex i φ ih =>
    rw [InfinitaryFormula.freeVars_ex, Set.sdiff_subset_iff, Set.singleton_union] at hS
    simp only [InfinitaryFormula.realize_ex]
    constructor
    · rintro ⟨c, hc⟩
      obtain ⟨d, hd⟩ := hI.forth hSab i c
      exact ⟨d, (ih hd hS).1 hc⟩
    · rintro ⟨d, hd⟩
      obtain ⟨c, hc⟩ := hI.back hSab i d
      exact ⟨c, (ih hc hS).2 hd⟩

/-- Winning the infinite `k`-pebble game preserves every `L^k_{∞ω}` formula of finite quantifier
rank on arbitrary structures. -/
theorem PebbleWinsForever.realize_infinitaryFormula_iff_of_quantifierRankLE {S : Set (Fin k)}
    {a : Fin k → M} {b : Fin k → N} (h : PebbleWinsForever L S a b)
    {φ : InfinitaryFormula.{w, u, v} L k} {n : ℕ} (hr : φ.QuantifierRankLE n)
    (hS : φ.freeVars ⊆ S) : φ.Realize a ↔ φ.Realize b :=
  (h.pebbleWins n).realize_infinitaryFormula_iff hr hS

/-- **Infinite pebble games and `L^k_{∞ω}`, easy direction.** On arbitrary structures, a winning
position of the infinite `k`-pebble game preserves every `L^k_{∞ω}` formula whose free variables
lie in `S`, including formulas of unbounded quantifier depth. -/
theorem PebbleWinsForever.realize_infinitaryFormula_iff {S : Set (Fin k)}
    {a : Fin k → M} {b : Fin k → N} (h : PebbleWinsForever L S a b)
    {φ : InfinitaryFormula.{w, u, v} L k} (hS : φ.freeVars ⊆ S) :
    φ.Realize a ↔ φ.Realize b :=
  let ⟨_, hI, hSab⟩ := pebbleWinsForever_iff_exists_isPebbleBackAndForth.1 h
  hI.realize_infinitaryFormula_iff hSab hS

private theorem partialIsoOn_of_forall_infinitaryFormula {S : Set (Fin k)} {a : Fin k → M}
    {b : Fin k → N}
    (h : ∀ φ : InfinitaryFormula.{w, u, v} L k, φ.QuantifierRankLE 0 → φ.freeVars ⊆ S →
      (φ.Realize a ↔ φ.Realize b)) : PartialIsoOn L S a b := by
  refine ⟨fun i hi j hj => ?_, fun R f hf => ?_⟩
  · exact h (.equal i j) trivial
      (by simp only [InfinitaryFormula.freeVars_equal, Set.insert_subset_iff,
        Set.singleton_subset_iff]; exact ⟨hi, hj⟩)
  · exact h (.rel R f) trivial
      (by simp only [InfinitaryFormula.freeVars_rel, Set.range_subset_iff]; exact hf)

/-- **Pebble games and `L^k_{∞ω}`, hard direction (finite rounds, arbitrary structures).** Over
any language `L` and arbitrary structures `M : Type w₁` and `N : Type w₂`, agreement on all
`L^k_{∞ω}` formulas at index universe `max w₁ w₂` of quantifier rank at most `n` with free
variables in `S` implies that Duplicator wins the `n`-round `k`-pebble game from `(S, a, b)`. -/
theorem pebbleWins_of_forall_infinitaryFormula_rankLE {n : ℕ} {S : Set (Fin k)} {a : Fin k → M}
    {b : Fin k → N}
    (h : ∀ φ : InfinitaryFormula.{max w₁ w₂, u, v} L k, φ.QuantifierRankLE n → φ.freeVars ⊆ S →
      (φ.Realize a ↔ φ.Realize b)) : PebbleWins L n S a b := by
  classical
  induction n generalizing S a b with
  | zero =>
    exact pebbleWins_zero.2 (partialIsoOn_of_forall_infinitaryFormula h)
  | succ n ih =>
    refine pebbleWins_succ.2 ⟨partialIsoOn_of_forall_infinitaryFormula fun φ hr hS =>
        h φ (hr.mono (Nat.zero_le _)) hS, fun i c => ?_, fun i d => ?_⟩
    · by_contra hno
      simp only [not_exists] at hno
      have hsep : ∀ d : N, ∃ ψ : InfinitaryFormula.{max w₁ w₂, u, v} L k,
          ψ.QuantifierRankLE n ∧ ψ.freeVars ⊆ insert i S ∧
            ψ.Realize (Function.update a i c) ∧ ¬ψ.Realize (Function.update b i d) := by
        intro d
        have hd : ¬∀ ψ : InfinitaryFormula.{max w₁ w₂, u, v} L k,
            ψ.QuantifierRankLE n → ψ.freeVars ⊆ insert i S →
              (ψ.Realize (Function.update a i c) ↔ ψ.Realize (Function.update b i d)) :=
          fun hall => hno d (ih hall)
        simp only [not_forall] at hd
        obtain ⟨ψ, hr, hS', hiff⟩ := hd
        by_cases hψ : ψ.Realize (Function.update a i c)
        · exact ⟨ψ, hr, hS', hψ, fun hb => hiff ⟨fun _ => hb, fun _ => hψ⟩⟩
        · exact ⟨ψ.not, hr, hS', hψ, fun hnb => hiff ⟨fun ha => absurd ha hψ,
            fun hb => absurd hb hnb⟩⟩
      choose ψ hr hS' ha hb using hsep
      let Φ : InfinitaryFormula.{max w₁ w₂, u, v} L k :=
        .ex i (.iInf fun d : ULift.{w₁} N => ψ d.down)
      have hΦr : Φ.QuantifierRankLE (n + 1) := by
        simp only [Φ, InfinitaryFormula.quantifierRankLE_ex_succ,
          InfinitaryFormula.quantifierRankLE_iInf]
        exact fun d => hr d.down
      have hΦS : Φ.freeVars ⊆ S := by
        rw [InfinitaryFormula.freeVars_ex, Set.sdiff_subset_iff, Set.singleton_union,
          InfinitaryFormula.freeVars_iInf, Set.iUnion_subset_iff]
        exact fun d => hS' d.down
      have hΦa : Φ.Realize a := ⟨c, (InfinitaryFormula.realize_iInf _ _).2 fun d => ha d.down⟩
      obtain ⟨d, hd⟩ := (h Φ hΦr hΦS).1 hΦa
      exact hb d ((InfinitaryFormula.realize_iInf _ _).1 hd (ULift.up d))
    · by_contra hno
      simp only [not_exists] at hno
      have hsep : ∀ c : M, ∃ ψ : InfinitaryFormula.{max w₁ w₂, u, v} L k,
          ψ.QuantifierRankLE n ∧ ψ.freeVars ⊆ insert i S ∧
            ψ.Realize (Function.update b i d) ∧ ¬ψ.Realize (Function.update a i c) := by
        intro c
        have hc : ¬∀ ψ : InfinitaryFormula.{max w₁ w₂, u, v} L k,
            ψ.QuantifierRankLE n → ψ.freeVars ⊆ insert i S →
              (ψ.Realize (Function.update a i c) ↔ ψ.Realize (Function.update b i d)) :=
          fun hall => hno c (ih hall)
        simp only [not_forall] at hc
        obtain ⟨ψ, hr, hS', hiff⟩ := hc
        by_cases hψ : ψ.Realize (Function.update b i d)
        · exact ⟨ψ, hr, hS', hψ, fun ha => hiff ⟨fun _ => hψ, fun _ => ha⟩⟩
        · exact ⟨ψ.not, hr, hS', hψ, fun hna => hiff ⟨fun ha => absurd ha hna,
            fun hb => absurd hb hψ⟩⟩
      choose ψ hr hS' hb ha using hsep
      let Φ : InfinitaryFormula.{max w₁ w₂, u, v} L k :=
        .ex i (.iInf fun c : ULift.{w₂} M => ψ c.down)
      have hΦr : Φ.QuantifierRankLE (n + 1) := by
        simp only [Φ, InfinitaryFormula.quantifierRankLE_ex_succ,
          InfinitaryFormula.quantifierRankLE_iInf]
        exact fun c => hr c.down
      have hΦS : Φ.freeVars ⊆ S := by
        rw [InfinitaryFormula.freeVars_ex, Set.sdiff_subset_iff, Set.singleton_union,
          InfinitaryFormula.freeVars_iInf, Set.iUnion_subset_iff]
        exact fun c => hS' c.down
      have hΦb : Φ.Realize b := ⟨d, (InfinitaryFormula.realize_iInf _ _).2 fun c => hb c.down⟩
      obtain ⟨c, hc⟩ := (h Φ hΦr hΦS).2 hΦb
      exact ha c ((InfinitaryFormula.realize_iInf _ _).1 hc (ULift.up c))

/-- **Pebble-game characterization of bounded-rank `L^k_{∞ω}`** ([Libkin2004], Theorem 11.5(a)).
Over any language and arbitrary structures, Duplicator wins the `n`-round `k`-pebble game from
`(S, a, b)` if and only if `a` and `b` satisfy the same `L^k_{∞ω}` formulas of quantifier rank at
most `n` with free variables in `S`. -/
theorem pebbleWins_iff_forall_infinitaryFormula_rankLE {n : ℕ} {S : Set (Fin k)} {a : Fin k → M}
    {b : Fin k → N} :
    PebbleWins L n S a b ↔
      ∀ φ : InfinitaryFormula.{max w₁ w₂, u, v} L k, φ.QuantifierRankLE n → φ.freeVars ⊆ S →
        (φ.Realize a ↔ φ.Realize b) :=
  ⟨fun h _ hr hS => h.realize_infinitaryFormula_iff hr hS,
    pebbleWins_of_forall_infinitaryFormula_rankLE⟩

/-- Agreement on all `L^k_{∞ω}` formulas at index universe `max w₁ w₂` forms a `k`-pebble
back-and-forth invariant on arbitrary structures. -/
theorem exists_isPebbleBackAndForth_of_forall_infinitaryFormula {S : Set (Fin k)} {a : Fin k → M}
    {b : Fin k → N}
    (h : ∀ φ : InfinitaryFormula.{max w₁ w₂, u, v} L k, φ.freeVars ⊆ S →
      (φ.Realize a ↔ φ.Realize b)) :
    ∃ I, IsPebbleBackAndForth L I ∧ I S a b := by
  classical
  let I : Set (Fin k) → (Fin k → M) → (Fin k → N) → Prop := fun T x y =>
    ∀ φ : InfinitaryFormula.{max w₁ w₂, u, v} L k, φ.freeVars ⊆ T → (φ.Realize x ↔ φ.Realize y)
  refine ⟨I, ⟨fun hT => partialIsoOn_of_forall_infinitaryFormula (fun φ _ hS => hT φ hS),
    fun {T x y} hT i c => ?_, fun {T x y} hT i d => ?_⟩, h⟩
  · by_contra hno
    dsimp only [I] at hno
    simp only [not_exists, not_forall] at hno
    have hsep : ∀ d : N, ∃ ψ : InfinitaryFormula.{max w₁ w₂, u, v} L k,
        ψ.freeVars ⊆ insert i T ∧
          ψ.Realize (Function.update x i c) ∧ ¬ψ.Realize (Function.update y i d) := by
      intro d
      obtain ⟨ψ, hS', hiff⟩ := hno d
      by_cases hψ : ψ.Realize (Function.update x i c)
      · exact ⟨ψ, hS', hψ, fun hb => hiff ⟨fun _ => hb, fun _ => hψ⟩⟩
      · exact ⟨ψ.not, hS', hψ, fun hnb => hiff ⟨fun ha => absurd ha hψ,
          fun hb => absurd hb hnb⟩⟩
    choose ψ hS' hx hy using hsep
    let Φ : InfinitaryFormula.{max w₁ w₂, u, v} L k :=
      .ex i (.iInf fun d : ULift.{w₁} N => ψ d.down)
    have hΦT : Φ.freeVars ⊆ T := by
      rw [InfinitaryFormula.freeVars_ex, Set.sdiff_subset_iff, Set.singleton_union,
        InfinitaryFormula.freeVars_iInf, Set.iUnion_subset_iff]
      exact fun d => hS' d.down
    have hΦx : Φ.Realize x := ⟨c, (InfinitaryFormula.realize_iInf _ _).2 fun d => hx d.down⟩
    obtain ⟨d, hd⟩ := (hT Φ hΦT).1 hΦx
    exact hy d ((InfinitaryFormula.realize_iInf _ _).1 hd (ULift.up d))
  · by_contra hno
    dsimp only [I] at hno
    simp only [not_exists, not_forall] at hno
    have hsep : ∀ c : M, ∃ ψ : InfinitaryFormula.{max w₁ w₂, u, v} L k,
        ψ.freeVars ⊆ insert i T ∧
          ψ.Realize (Function.update y i d) ∧ ¬ψ.Realize (Function.update x i c) := by
      intro c
      obtain ⟨ψ, hS', hiff⟩ := hno c
      by_cases hψ : ψ.Realize (Function.update y i d)
      · exact ⟨ψ, hS', hψ, fun ha => hiff ⟨fun _ => hψ, fun _ => ha⟩⟩
      · exact ⟨ψ.not, hS', hψ, fun hna => hiff ⟨fun ha => absurd ha hna,
          fun hb => absurd hb hψ⟩⟩
    choose ψ hS' hy hx using hsep
    let Φ : InfinitaryFormula.{max w₁ w₂, u, v} L k :=
      .ex i (.iInf fun c : ULift.{w₂} M => ψ c.down)
    have hΦT : Φ.freeVars ⊆ T := by
      rw [InfinitaryFormula.freeVars_ex, Set.sdiff_subset_iff, Set.singleton_union,
        InfinitaryFormula.freeVars_iInf, Set.iUnion_subset_iff]
      exact fun c => hS' c.down
    have hΦy : Φ.Realize y := ⟨d, (InfinitaryFormula.realize_iInf _ _).2 fun c => hy c.down⟩
    obtain ⟨c, hc⟩ := (hT Φ hΦT).2 hΦy
    exact hx c ((InfinitaryFormula.realize_iInf _ _).1 hc (ULift.up c))

/-- **Back-and-forth characterization of `L^k_{∞ω}` on arbitrary structures** ([Libkin2004],
Theorem 11.5(b)). Over any language and arbitrary (possibly infinite) structures `M : Type w₁` and
`N : Type w₂`, `(S, a, b)` belongs to a `k`-pebble back-and-forth invariant if and only if `a` and
`b` satisfy the same `L^k_{∞ω}` formulas (at index universe `max w₁ w₂`) with free variables in
`S`. -/
theorem exists_isPebbleBackAndForth_iff_forall_infinitaryFormula {S : Set (Fin k)}
    {a : Fin k → M} {b : Fin k → N} :
    (∃ I, IsPebbleBackAndForth L I ∧ I S a b) ↔
      ∀ φ : InfinitaryFormula.{max w₁ w₂, u, v} L k, φ.freeVars ⊆ S →
        (φ.Realize a ↔ φ.Realize b) :=
  ⟨fun ⟨_, hI, hSab⟩ _ hS => hI.realize_infinitaryFormula_iff hSab hS,
    exists_isPebbleBackAndForth_of_forall_infinitaryFormula⟩

/-- **Infinite pebble games and `L^k_{∞ω}`, hard direction (arbitrary structures).** Agreement on
all `L^k_{∞ω}` formulas at index universe `max w₁ w₂` implies that Duplicator wins the infinite
`k`-pebble game. -/
theorem pebbleWinsForever_of_forall_infinitaryFormula {S : Set (Fin k)} {a : Fin k → M}
    {b : Fin k → N}
    (h : ∀ φ : InfinitaryFormula.{max w₁ w₂, u, v} L k, φ.freeVars ⊆ S →
      (φ.Realize a ↔ φ.Realize b)) : PebbleWinsForever L S a b := by
  obtain ⟨_, hI, hSab⟩ := exists_isPebbleBackAndForth_of_forall_infinitaryFormula h
  exact hI.pebbleWinsForever hSab

/-- **Pebble-game characterization of `L^k_{∞ω}` on arbitrary structures** ([Libkin2004],
Theorem 11.5(b)). Over any vocabulary `L` (even infinite) and arbitrary (possibly infinite)
structures `M : Type w₁` and `N : Type w₂`, Duplicator wins the infinite `k`-pebble game from
`(S, a, b)` if and only if `a` and `b` satisfy the same `L^k_{∞ω}` formulas (at index universe
`max w₁ w₂`) with free variables in `S`. -/
theorem pebbleWinsForever_iff_forall_infinitaryFormula {S : Set (Fin k)}
    {a : Fin k → M} {b : Fin k → N} :
    PebbleWinsForever L S a b ↔
      ∀ φ : InfinitaryFormula.{max w₁ w₂, u, v} L k, φ.freeVars ⊆ S →
        (φ.Realize a ↔ φ.Realize b) :=
  pebbleWinsForever_iff_exists_isPebbleBackAndForth.trans
    exists_isPebbleBackAndForth_iff_forall_infinitaryFormula

/-! ### Bijective pebble-game characterizations of `C^k_{∞ω}` -/

/-- **Bijective pebble games and `C^k_{∞ω}`, easy direction (finite rounds).** A winning position
of the `n`-round bijective `k`-pebble game preserves every `C^k_{∞ω}` formula of quantifier rank at
most `n` whose free variables lie in `S`, with no finiteness assumptions. -/
theorem BijPebbleWins.realize_infinitaryCountingFormula_iff {n : ℕ} {S : Set (Fin k)}
    {a : Fin k → M} {b : Fin k → N} (h : BijPebbleWins L n S a b)
    {φ : InfinitaryCountingFormula.{w, u, v} L k} (hr : φ.QuantifierRankLE n)
    (hS : φ.freeVars ⊆ S) : φ.Realize a ↔ φ.Realize b := by
  induction φ generalizing n S a b with
  | equal i j =>
    simp only [InfinitaryCountingFormula.freeVars_equal, Set.insert_subset_iff,
      Set.singleton_subset_iff] at hS
    exact h.partialIsoOn.eq_iff i hS.1 j hS.2
  | rel R f =>
    simp only [InfinitaryCountingFormula.freeVars_rel, Set.range_subset_iff] at hS
    exact h.partialIsoOn.relMap_iff R f hS
  | not φ ih =>
    exact not_congr (ih h hr hS)
  | iSup f ih =>
    simp only [InfinitaryCountingFormula.quantifierRankLE_iSup] at hr
    simp only [InfinitaryCountingFormula.freeVars_iSup, Set.iUnion_subset_iff] at hS
    exact exists_congr fun idx => ih idx h (hr idx) (hS idx)
  | atLeast m i φ ih =>
    cases n with
    | zero => exact False.elim hr
    | succ n =>
      simp only [InfinitaryCountingFormula.quantifierRankLE_atLeast_succ] at hr
      rw [InfinitaryCountingFormula.freeVars_atLeast, Set.sdiff_subset_iff,
        Set.singleton_union] at hS
      obtain ⟨f, hf⟩ := h.move i
      have himage : f '' {c | φ.Realize (Function.update a i c)} =
          {d | φ.Realize (Function.update b i d)} := by
        ext d
        constructor
        · rintro ⟨c, hc, rfl⟩
          exact (ih (hf c) hr hS).1 hc
        · intro hd
          refine ⟨f.symm d, (ih (hf (f.symm d)) hr hS).2 ?_, f.apply_symm_apply d⟩
          rwa [f.apply_symm_apply]
      rw [InfinitaryCountingFormula.realize_atLeast, InfinitaryCountingFormula.realize_atLeast,
        ← himage, f.injective.encard_image]

/-- **Bijective back-and-forth invariants and `C^k_{∞ω}`.** Any position in a bijective
`k`-pebble back-and-forth invariant preserves every `C^k_{∞ω}` formula whose free variables lie in
`S`, even of unbounded quantifier depth and with no finiteness assumptions. -/
theorem IsBijPebbleBackAndForth.realize_infinitaryCountingFormula_iff
    {I : Set (Fin k) → (Fin k → M) → (Fin k → N) → Prop} (hI : IsBijPebbleBackAndForth L I)
    {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N} (hSab : I S a b)
    {φ : InfinitaryCountingFormula.{w, u, v} L k} (hS : φ.freeVars ⊆ S) :
    φ.Realize a ↔ φ.Realize b := by
  induction φ generalizing S a b with
  | equal i j =>
    simp only [InfinitaryCountingFormula.freeVars_equal, Set.insert_subset_iff,
      Set.singleton_subset_iff] at hS
    exact (hI.partialIsoOn hSab).eq_iff i hS.1 j hS.2
  | rel R f =>
    simp only [InfinitaryCountingFormula.freeVars_rel, Set.range_subset_iff] at hS
    exact (hI.partialIsoOn hSab).relMap_iff R f hS
  | not φ ih =>
    exact not_congr (ih hSab hS)
  | iSup f ih =>
    simp only [InfinitaryCountingFormula.freeVars_iSup, Set.iUnion_subset_iff] at hS
    exact exists_congr fun idx => ih idx hSab (hS idx)
  | atLeast m i φ ih =>
    rw [InfinitaryCountingFormula.freeVars_atLeast, Set.sdiff_subset_iff,
      Set.singleton_union] at hS
    obtain ⟨f, hf⟩ := hI.move hSab i
    have himage : f '' {c | φ.Realize (Function.update a i c)} =
        {d | φ.Realize (Function.update b i d)} := by
      ext d
      constructor
      · rintro ⟨c, hc, rfl⟩
        exact (ih (hf c) hS).1 hc
      · intro hd
        refine ⟨f.symm d, (ih (hf (f.symm d)) hS).2 ?_, f.apply_symm_apply d⟩
        rwa [f.apply_symm_apply]
    rw [InfinitaryCountingFormula.realize_atLeast, InfinitaryCountingFormula.realize_atLeast,
      ← himage, f.injective.encard_image]

/-- Winning the infinite bijective `k`-pebble game preserves every `C^k_{∞ω}` formula of finite
quantifier rank on arbitrary structures. -/
theorem BijPebbleWinsForever.realize_infinitaryCountingFormula_iff_of_quantifierRankLE
    {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N} (h : BijPebbleWinsForever L S a b)
    {φ : InfinitaryCountingFormula.{w, u, v} L k} {n : ℕ} (hr : φ.QuantifierRankLE n)
    (hS : φ.freeVars ⊆ S) : φ.Realize a ↔ φ.Realize b :=
  (h.bijPebbleWins n).realize_infinitaryCountingFormula_iff hr hS

/-- **Infinite bijective pebble games and `C^k_{∞ω}`, easy direction.** On arbitrary structures, a
winning position of the infinite bijective `k`-pebble game preserves every `C^k_{∞ω}` formula whose
free variables lie in `S`, even of unbounded quantifier depth. -/
theorem BijPebbleWinsForever.realize_infinitaryCountingFormula_iff {S : Set (Fin k)}
    {a : Fin k → M} {b : Fin k → N} (h : BijPebbleWinsForever L S a b)
    {φ : InfinitaryCountingFormula.{w, u, v} L k} (hS : φ.freeVars ⊆ S) :
    φ.Realize a ↔ φ.Realize b :=
  let ⟨_, hI, hSab⟩ := bijPebbleWinsForever_iff_exists_isBijPebbleBackAndForth.1 h
  hI.realize_infinitaryCountingFormula_iff hSab hS

private def bijSumRel (L : Language.{u, v}) {M : Type w₁} {N : Type w₂}
    [L.Structure M] [L.Structure N] {k : ℕ} (n : ℕ) (S : Set (Fin k))
    (a : Fin k → M) (b : Fin k → N) (i : Fin k) : M ⊕ N → M ⊕ N → Prop
  | .inl c, .inl c' => BijPebbleWins L n (insert i S) (Function.update a i c)
      (Function.update a i c')
  | .inl c, .inr d => BijPebbleWins L n (insert i S) (Function.update a i c)
      (Function.update b i d)
  | .inr d, .inl c => BijPebbleWins L n (insert i S) (Function.update b i d)
      (Function.update a i c)
  | .inr d, .inr d' => BijPebbleWins L n (insert i S) (Function.update b i d)
      (Function.update b i d')

private def bijSumSetoid (L : Language.{u, v}) {M : Type w₁} {N : Type w₂}
    [L.Structure M] [L.Structure N] {k : ℕ} (n : ℕ) (S : Set (Fin k))
    (a : Fin k → M) (b : Fin k → N) (i : Fin k) : Setoid (M ⊕ N) where
  r := bijSumRel L n S a b i
  iseqv := {
    refl := fun
      | .inl _ => BijPebbleWins.refl _ _ _
      | .inr _ => BijPebbleWins.refl _ _ _
    symm := fun {x y} h => match x, y with
      | .inl _, .inl _ => h.symm
      | .inl _, .inr _ => h.symm
      | .inr _, .inl _ => h.symm
      | .inr _, .inr _ => h.symm
    trans := fun {x y z} h₁ h₂ => match x, y, z with
      | .inl _, .inl _, .inl _ => h₁.trans h₂
      | .inl _, .inl _, .inr _ => h₁.trans h₂
      | .inl _, .inr _, .inl _ => h₁.trans h₂
      | .inl _, .inr _, .inr _ => h₁.trans h₂
      | .inr _, .inl _, .inl _ => h₁.trans h₂
      | .inr _, .inl _, .inr _ => h₁.trans h₂
      | .inr _, .inr _, .inl _ => h₁.trans h₂
      | .inr _, .inr _, .inr _ => h₁.trans h₂
  }

/-- Agreement on quantifier-free `C^k_{∞ω}` formulas gives a partial isomorphism, through the
embedding of `L^k_{∞ω}` formulas. -/
private theorem partialIsoOn_of_forall_infinitaryCountingFormula {S : Set (Fin k)}
    {a : Fin k → M} {b : Fin k → N}
    (h : ∀ φ : InfinitaryCountingFormula.{w, u, v} L k, φ.QuantifierRankLE 0 →
      φ.freeVars ⊆ S → (φ.Realize a ↔ φ.Realize b)) : PartialIsoOn L S a b :=
  partialIsoOn_of_forall_infinitaryFormula fun φ hr hS => by
    simpa only [InfinitaryFormula.realize_toCounting] using
      h φ.toCounting ((φ.quantifierRankLE_toCounting 0).2 hr) (φ.freeVars_toCounting ▸ hS)

private theorem bijPebbleWins_of_forall_same_univ (L : Language.{u, v}) {k : ℕ} {n : ℕ}
    {M' N' : Type w₁} [L.Structure M'] [L.Structure N'] [Finite M'] [Finite N']
    {S : Set (Fin k)} {a : Fin k → M'} {b : Fin k → N'}
    (h : ∀ φ : InfinitaryCountingFormula.{w, u, v} L k, φ.QuantifierRankLE n → φ.freeVars ⊆ S →
      (φ.Realize a ↔ φ.Realize b)) : BijPebbleWins L n S a b := by
  classical
  induction n generalizing M' N' S a b with
  | zero =>
    exact bijPebbleWins_zero.2 (partialIsoOn_of_forall_infinitaryCountingFormula h)
  | succ n ih =>
    have h0 : PartialIsoOn L S a b := partialIsoOn_of_forall_infinitaryCountingFormula
      fun φ hr hS => h φ (hr.mono (Nat.zero_le _)) hS
    refine bijPebbleWins_succ.2 ⟨h0, fun i => ?_⟩
    let sX := bijSumSetoid L n S a b i
    let qM : M' → Quotient sX := fun c => Quotient.mk sX (.inl c)
    let qN : N' → Quotient sX := fun d => Quotient.mk sX (.inr d)
    suffices hex : ∃ f : M' ≃ N', ∀ c, qN (f c) = qM c by
      obtain ⟨f, hf⟩ := hex
      exact ⟨f, fun c => Quotient.exact (hf c).symm⟩
    rw [Equiv.exists_apply_eq_iff_card_fiber_eq]
    intro q
    refine Quotient.inductionOn q fun x => ?_
    let evalSum : M' ⊕ N' → InfinitaryCountingFormula.{w, u, v} L k → Prop := fun z ψ =>
      match z with
      | .inl c => ψ.Realize (Function.update a i c)
      | .inr d => ψ.Realize (Function.update b i d)
    have hbij_iff : ∀ z₁ z₂ : M' ⊕ N', bijSumRel L n S a b i z₁ z₂ ↔
        ∀ ψ : InfinitaryCountingFormula.{w, u, v} L k, ψ.QuantifierRankLE n →
          ψ.freeVars ⊆ insert i S → (evalSum z₁ ψ ↔ evalSum z₂ ψ) := by
      rintro (c₁ | d₁) (c₂ | d₂) <;>
        exact ⟨fun hb ψ hr hS' => hb.realize_infinitaryCountingFormula_iff hr hS', ih⟩
    let Bad := {y : M' ⊕ N' // ¬bijSumRel L n S a b i x y}
    have hsep : ∀ y : Bad, ∃ ψ : InfinitaryCountingFormula.{w, u, v} L k,
        ψ.QuantifierRankLE n ∧ ψ.freeVars ⊆ insert i S ∧
          evalSum x ψ ∧ ¬evalSum y.1 ψ := by
      rintro ⟨z, hz⟩
      have hnot := mt (hbij_iff x z).2 hz
      simp only [not_forall] at hnot
      obtain ⟨ψ, hr, hS', hiff⟩ := hnot
      by_cases hψ : evalSum x ψ
      · exact ⟨ψ, hr, hS', hψ, fun h₂ => hiff ⟨fun _ => h₂, fun _ => hψ⟩⟩
      · have hnot_x : evalSum x ψ.not := by cases x <;> exact hψ
        have hnot_z : ¬evalSum z ψ.not := by
          cases z <;> exact fun h₂ => hiff ⟨fun h₁ => absurd h₁ hψ, fun h₃ => absurd h₃ h₂⟩
        exact ⟨ψ.not, hr, hS', hnot_x, hnot_z⟩
    choose ψ hr hS' hx_sat hnot using hsep
    let _ : Fintype Bad := Fintype.ofFinite Bad
    let e : Bad ≃ Fin (Fintype.card Bad) := Fintype.equivFin Bad
    let Φ : InfinitaryCountingFormula.{w, u, v} L k :=
      .iInf fun idx : ULift.{w} (Fin (Fintype.card Bad)) => ψ (e.symm idx.down)
    have hΦr : Φ.QuantifierRankLE n :=
      (InfinitaryCountingFormula.quantifierRankLE_iInf _ _).2 fun idx => hr _
    have hΦS : Φ.freeVars ⊆ insert i S := by
      rw [InfinitaryCountingFormula.freeVars_iInf, Set.iUnion_subset_iff]
      exact fun idx => hS' _
    have hΦx : evalSum x Φ := by
      cases x <;> exact (InfinitaryCountingFormula.realize_iInf _ _).2 fun idx => hx_sat _
    have hΦ_iff : ∀ z : M' ⊕ N', evalSum z Φ ↔ bijSumRel L n S a b i z x := by
      intro z
      constructor
      · intro hΦz
        by_contra hnb
        have hnb' : ¬bijSumRel L n S a b i x z := fun hb => hnb (sX.symm hb)
        let y : Bad := ⟨z, hnb'⟩
        have hy : evalSum z (ψ (e.symm (e y))) := by
          cases z <;> exact (InfinitaryCountingFormula.realize_iInf _ _).1 hΦz (ULift.up (e y))
        rw [e.symm_apply_apply] at hy
        exact hnot y hy
      · intro hb
        exact ((hbij_iff z x).1 hb Φ hΦr hΦS).2 hΦx
    have hsetM : {c : M' | Φ.Realize (Function.update a i c)} =
        {c : M' | qM c = Quotient.mk sX x} := by
      ext c
      simp only [Set.mem_ofPred_eq, qM, Quotient.eq]
      exact hΦ_iff (.inl c)
    have hsetN : {d : N' | Φ.Realize (Function.update b i d)} =
        {d : N' | qN d = Quotient.mk sX x} := by
      ext d
      simp only [Set.mem_ofPred_eq, qN, Quotient.eq]
      exact hΦ_iff (.inr d)
    let m := {c : M' | qM c = Quotient.mk sX x}.ncard
    let Ψ : InfinitaryCountingFormula.{w, u, v} L k := .exactly m i Φ
    have hΨr : Ψ.QuantifierRankLE (n + 1) := by
      simpa only [Ψ, InfinitaryCountingFormula.quantifierRankLE_exactly_succ] using hΦr
    have hΨS : Ψ.freeVars ⊆ S := by
      rwa [InfinitaryCountingFormula.freeVars_exactly, Set.sdiff_subset_iff, Set.singleton_union]
    have hΨa : Ψ.Realize a := by
      rw [InfinitaryCountingFormula.realize_exactly_iff_ncard, hsetM]
    have hΨb : Ψ.Realize b := (h Ψ hΨr hΨS).1 hΨa
    rw [InfinitaryCountingFormula.realize_exactly_iff_ncard, hsetN] at hΨb
    have hcardM : Nat.card {c : M' // qM c = Quotient.mk sX x} = m :=
      Nat.card_coe_set_eq {c : M' | qM c = Quotient.mk sX x}
    have hcardN : Nat.card {d : N' // qN d = Quotient.mk sX x} =
        {d : N' | qN d = Quotient.mk sX x}.ncard :=
      Nat.card_coe_set_eq {d : N' | qN d = Quotient.mk sX x}
    rw [hcardM, hcardN, hΨb]

@[instance_reducible]
private def uliftStructure (L : Language.{u, v}) (M' : Type w₁) [L.Structure M'] :
    L.Structure (ULift.{w₂} M') where
  funMap f x := ULift.up (funMap f (ULift.down ∘ x))
  RelMap R x := RelMap R (ULift.down ∘ x)

private def uliftLanguageEquiv (L : Language.{u, v}) (M' : Type w₁) [L.Structure M'] :
    letI := uliftStructure.{u, v, w₁, w₂} L M'
    ULift.{w₂} M' ≃[L] M' :=
  letI := uliftStructure.{u, v, w₁, w₂} L M'
  { toEquiv := Equiv.ulift
    map_fun' := fun _ _ => rfl
    map_rel' := fun _ _ => Iff.rfl }

/-- **Bijective pebble games and `C^k_{∞ω}`, hard direction on finite structures.** Over any
language `L` (even with infinitely many relation symbols) and finite structures `M` and `N`,
agreement on `C^k_{∞ω}` formulas of quantifier rank at most `n` with free variables in `S` implies
that Duplicator wins the `n`-round bijective `k`-pebble game from `(S, a, b)`. -/
theorem bijPebbleWins_of_forall_infinitaryCountingFormula_rankLE [Finite M] [Finite N] {n : ℕ}
    {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N}
    (h : ∀ φ : InfinitaryCountingFormula.{w, u, v} L k, φ.QuantifierRankLE n → φ.freeVars ⊆ S →
      (φ.Realize a ↔ φ.Realize b)) : BijPebbleWins L n S a b := by
  let _ : L.Structure (ULift.{w₂} M) := uliftStructure L M
  let _ : L.Structure (ULift.{w₁} N) := uliftStructure L N
  let eM : ULift.{w₂} M ≃[L] M := uliftLanguageEquiv L M
  let eN : ULift.{w₁} N ≃[L] N := uliftLanguageEquiv L N
  have hM : BijPebbleWins L n S a (eM.symm ∘ a) := eM.symm.bijPebbleWins n S a
  have hN : BijPebbleWins L n S (eN.symm ∘ b) b := (eN.symm.bijPebbleWins n S b).symm
  have hMN : BijPebbleWins L n S (eM.symm ∘ a) (eN.symm ∘ b) :=
    bijPebbleWins_of_forall_same_univ.{w} L fun φ hr hS =>
      (hM.symm.realize_infinitaryCountingFormula_iff hr hS).trans
        ((h φ hr hS).trans (hN.symm.realize_infinitaryCountingFormula_iff hr hS))
  exact (hM.trans hMN).trans hN

/-- **Bijective pebble-game characterization of bounded-rank `C^k_{∞ω}`** on finite structures,
for any vocabulary `L` and any index universe `w`. -/
theorem bijPebbleWins_iff_forall_infinitaryCountingFormula_rankLE [Finite M] [Finite N] {n : ℕ}
    {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N} :
    BijPebbleWins L n S a b ↔
      ∀ φ : InfinitaryCountingFormula.{w, u, v} L k, φ.QuantifierRankLE n → φ.freeVars ⊆ S →
        (φ.Realize a ↔ φ.Realize b) :=
  ⟨fun h _ hr hS => h.realize_infinitaryCountingFormula_iff hr hS,
    bijPebbleWins_of_forall_infinitaryCountingFormula_rankLE⟩

/-- **Bijective pebble-game characterization of `C^k_{∞ω}`** on finite structures, for any
vocabulary `L` and any index universe `w`. -/
theorem bijPebbleWinsForever_iff_forall_infinitaryCountingFormula [Finite M] [Finite N]
    {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N} :
    BijPebbleWinsForever L S a b ↔
      ∀ φ : InfinitaryCountingFormula.{w, u, v} L k, φ.freeVars ⊆ S →
        (φ.Realize a ↔ φ.Realize b) := by
  refine ⟨fun h φ hS => h.realize_infinitaryCountingFormula_iff hS, fun h => ?_⟩
  rw [bijPebbleWinsForever_iff_forall_bijPebbleWins]
  exact fun n => bijPebbleWins_of_forall_infinitaryCountingFormula_rankLE.{w} fun φ _ hS => h φ hS

/-! ### Finite-model collapse (`L^k_{∞ω} ≡ FO^k` and `C^k_{∞ω} ≡ C^k`) -/

/-- **Finite-model collapse of `L^k_{∞ω}` equivalence to `FO^k` equivalence** ([Libkin2004],
Proposition 11.8). Over a finite relational vocabulary and finite structures, two positions agree
on all `L^k_{∞ω}` formulas (at any index universe `w`, including unbounded quantifier depth) if and
only if they agree on all finitary `FO^k` formulas. -/
theorem forall_realize_infinitaryFormula_iff_forall_realize [Finite (Σ l, L.Relations l)]
    [Finite M] [Finite N] {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N} :
    (∀ φ : InfinitaryFormula.{w, u, v} L k, φ.freeVars ⊆ S → (φ.Realize a ↔ φ.Realize b)) ↔
      ∀ φ : Formula L k, ↑φ.freeVars ⊆ S → (φ.Realize a ↔ φ.Realize b) := by
  rw [← pebbleWinsForever_iff_forall_realize_iff]
  refine ⟨fun h => ?_, fun h φ hS => h.realize_infinitaryFormula_iff hS⟩
  rw [pebbleWinsForever_iff_forall_realize_iff]
  intro φ hS
  have hInf := h (φ.toInfinitary : InfinitaryFormula.{w, u, v} L k)
    (by rwa [Formula.freeVars_toInfinitary])
  simpa only [Formula.realize_toInfinitary] using hInf

/-- **Finite-model collapse of `C^k_{∞ω}` equivalence to `C^k` equivalence.** Over a finite
relational vocabulary and finite structures, two positions agree on all `C^k_{∞ω}` formulas (at any
index universe `w`) if and only if they agree on all finitary `C^k` formulas. -/
theorem forall_realize_infinitaryCountingFormula_iff_forall_realize [Finite (Σ l, L.Relations l)]
    [Finite M] [Finite N] {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N} :
    (∀ φ : InfinitaryCountingFormula.{w, u, v} L k, φ.freeVars ⊆ S →
      (φ.Realize a ↔ φ.Realize b)) ↔
      ∀ φ : CountingFormula L k, ↑φ.freeVars ⊆ S → (φ.Realize a ↔ φ.Realize b) := by
  rw [← bijPebbleWinsForever_iff_forall_infinitaryCountingFormula.{w},
    bijPebbleWinsForever_iff_forall_realize_iff]

end PebbleCharacterization

/-! ### Expressiveness separations -/

namespace FiniteVariable

section Reachability

/-- The 3-variable sliding-pebble formula of `FO³` expressing the existence of a walk of exact
length `d` from `x₀` to `x₁` in a simple graph. For `d + 1`, pebble `2` marks a neighbor of `x₀`
and pebble `0` is rebound to `x₂` to recurse without introducing a fourth variable. -/
def walkFormula : ℕ → Formula Language.graph 3
  | 0 => .equal 0 1
  | d + 1 => .ex 2 (.rel adj ![0, 2] ⊓ .ex 0 (.equal 0 2 ⊓ walkFormula d))

theorem freeVars_walkFormula_subset (d : ℕ) :
    ↑(walkFormula d).freeVars ⊆ ({0, 1} : Set (Fin 3)) := by
  induction d with
  | zero =>
    simp only [walkFormula, Formula.freeVars_equal, Finset.coe_insert, Finset.coe_singleton,
      Set.Subset.rfl]
  | succ d _ =>
    intro i hi
    fin_cases i
    · exact Set.mem_insert 0 {1}
    · exact Set.mem_insert_of_mem 0 (Set.mem_singleton 1)
    · simp only [walkFormula, Finset.mem_coe, Formula.freeVars_ex, Finset.mem_erase] at hi
      exact absurd rfl hi.1

theorem quantifierRank_walkFormula (d : ℕ) : (walkFormula d).quantifierRank = 2 * d := by
  induction d with
  | zero => simp only [walkFormula, Formula.quantifierRank_equal, Nat.mul_zero]
  | succ d ih =>
    simp only [walkFormula, Formula.quantifierRank_ex, Formula.quantifierRank_inf,
      Formula.quantifierRank_rel, Formula.quantifierRank_equal, ih]
    omega

/-- `walkFormula d` holds in `G` at `a` if and only if there is a walk of length `d` in `G` from
`a 0` to `a 1`. -/
theorem realize_walkFormula {V : Type w₁} (G : SimpleGraph V) (d : ℕ) (a : Fin 3 → V) :
    (letI := G.structure; (walkFormula d).Realize a) ↔
      ∃ p : G.Walk (a 0) (a 1), p.length = d := by
  suffices hgen : ∀ (u v : V) (a : Fin 3 → V), a 0 = u → a 1 = v →
      ((letI := G.structure; (walkFormula d).Realize a) ↔ ∃ p : G.Walk u v, p.length = d) from
    hgen (a 0) (a 1) a rfl rfl
  induction d with
  | zero =>
    intro u v a hu hv
    let := G.structure
    simp only [walkFormula, Formula.realize_equal, hu, hv]
    constructor
    · rintro rfl
      exact ⟨SimpleGraph.Walk.nil, rfl⟩
    · rintro ⟨p, hp⟩
      exact SimpleGraph.Walk.eq_of_length_eq_zero hp
  | succ d ih =>
    intro u v a hu hv
    have hstep : (letI := G.structure; (walkFormula (d + 1)).Realize a) ↔
        ∃ z : V, G.Adj u z ∧
          (letI := G.structure; (walkFormula d).Realize (Function.update a 0 z)) := by
      let := G.structure
      simp only [walkFormula, Formula.realize_ex, Formula.realize_inf, Formula.realize_rel,
        Formula.realize_equal]
      refine exists_congr fun z => ?_
      have hadj : RelMap adj (Function.update a 2 z ∘ ![0, 2]) ↔ G.Adj u z := by
        have hcomp : Function.update a 2 z ∘ ![0, 2] = ![u, z] := by
          funext t
          fin_cases t
          · change Function.update a 2 z 0 = u
            rw [Function.update_of_ne (by decide : (0 : Fin 3) ≠ 2), hu]
          · change Function.update a 2 z 2 = z
            exact Function.update_self 2 z a
        rw [hcomp]
        rfl
      rw [hadj]
      refine and_congr Iff.rfl ?_
      have h02 : ∀ w : V, Function.update (Function.update a 2 z) 0 w 0 = w ∧
          Function.update (Function.update a 2 z) 0 w 2 = z := fun w => by
        refine ⟨by simp only [Function.update_self], ?_⟩
        rw [Function.update_of_ne (by decide : (2 : Fin 3) ≠ 0), Function.update_self]
      have hcongr : (walkFormula d).Realize (Function.update (Function.update a 2 z) 0 z) ↔
          (walkFormula d).Realize (Function.update a 0 z) := by
        refine Formula.realize_congr fun j hj => ?_
        rcases freeVars_walkFormula_subset d hj with rfl | rfl
        · simp only [Function.update_self]
        · rw [Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0),
            Function.update_of_ne (by decide : (1 : Fin 3) ≠ 2),
            Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0)]
      constructor
      · rintro ⟨w, hw, hwalk⟩
        rw [(h02 w).1, (h02 w).2] at hw
        subst hw
        exact hcongr.1 hwalk
      · intro hwalk
        exact ⟨z, by rw [(h02 z).1, (h02 z).2], hcongr.2 hwalk⟩
    rw [hstep]
    have hu' : ∀ z : V, Function.update a 0 z 0 = z := fun z => by
      simp only [Function.update_self]
    have hv' : ∀ z : V, Function.update a 0 z 1 = v := fun z => by
      rw [Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0), hv]
    constructor
    · rintro ⟨z, hadj, hwalk⟩
      obtain ⟨p, hp⟩ := (ih z v (Function.update a 0 z) (hu' z) (hv' z)).1 hwalk
      exact ⟨SimpleGraph.Walk.cons hadj p, by simp only [SimpleGraph.Walk.length_cons, hp]⟩
    · rintro ⟨p, hp⟩
      cases p with
      | nil => simp only [SimpleGraph.Walk.length_nil, Nat.zero_ne_add_one] at hp
      | @cons _ z _ hadj q =>
        simp only [SimpleGraph.Walk.length_cons, Nat.add_right_cancel_iff] at hp
        exact ⟨z, hadj, (ih z v (Function.update a 0 z) (hu' z) (hv' z)).2 ⟨q, hp⟩⟩

/-- The `L^3_{∞ω}` formula defining graph reachability between `x₀` and `x₁` as the countable
disjunction of `walkFormula d` over all walk lengths `d : ℕ`. -/
def reachableInfinitary : InfinitaryFormula.{w, 0, 0} Language.graph 3 :=
  .iSup fun d : ULift.{w} ℕ => (walkFormula d.down).toInfinitary

theorem freeVars_reachableInfinitary_subset :
    (reachableInfinitary : InfinitaryFormula.{w, 0, 0} Language.graph 3).freeVars ⊆
      ({0, 1} : Set (Fin 3)) := by
  rw [reachableInfinitary, InfinitaryFormula.freeVars_iSup, Set.iUnion_subset_iff]
  intro d
  rw [Formula.freeVars_toInfinitary]
  exact freeVars_walkFormula_subset d.down

/-- **Graph reachability is definable in `L^3_{∞ω}`** on all simple graphs (finite or infinite). -/
@[simp] theorem realize_reachableInfinitary {V : Type w₁} (G : SimpleGraph V) (a : Fin 3 → V) :
    (letI := G.structure;
      (reachableInfinitary : InfinitaryFormula.{w, 0, 0} Language.graph 3).Realize a) ↔
      G.Reachable (a 0) (a 1) := by
  have h1 : (letI := G.structure;
      (reachableInfinitary : InfinitaryFormula.{w, 0, 0} Language.graph 3).Realize a) ↔
      ∃ d : ℕ, (letI := G.structure; (walkFormula d).Realize a) := by
    let := G.structure
    simp only [reachableInfinitary, InfinitaryFormula.realize_iSup, ULift.exists,
      Formula.realize_toInfinitary]
  rw [h1]
  simp only [realize_walkFormula, SimpleGraph.Reachable]
  exact ⟨fun ⟨_, p, _⟩ => ⟨p⟩, fun ⟨p⟩ => ⟨p.length, p, rfl⟩⟩

/-- The closed `L^3_{∞ω}` formula (`freeVars = ∅`) expressing graph connectivity: every pair of
vertices `(x₀, x₁)` is connected by a walk. -/
def connectedInfinitary : InfinitaryFormula.{w, 0, 0} Language.graph 3 :=
  .all 0 (.all 1 reachableInfinitary)

@[simp] theorem freeVars_connectedInfinitary :
    (connectedInfinitary : InfinitaryFormula.{w, 0, 0} Language.graph 3).freeVars = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro i hi
  rw [connectedInfinitary, InfinitaryFormula.freeVars_all, InfinitaryFormula.freeVars_all,
    Set.mem_sdiff, Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_singleton_iff] at hi
  rcases freeVars_reachableInfinitary_subset hi.1.1 with rfl | rfl
  · exact hi.2 rfl
  · exact hi.1.2 rfl

/-- `connectedInfinitary` holds in `G` under an assignment `a` if and only if `G` is preconnected.
(Since `a : Fin 3 → V` already witnesses that `V` is nonempty, this is also equivalent to
`G.Connected`; see `realize_connectedInfinitary_iff_connected`.) -/
theorem realize_connectedInfinitary_iff_preconnected {V : Type w₁} (G : SimpleGraph V)
    (a : Fin 3 → V) :
    (letI := G.structure;
      (connectedInfinitary : InfinitaryFormula.{w, 0, 0} Language.graph 3).Realize a) ↔
      G.Preconnected := by
  have h1 : (letI := G.structure;
      (connectedInfinitary : InfinitaryFormula.{w, 0, 0} Language.graph 3).Realize a) ↔
      ∀ u v : V,
        (letI := G.structure;
          (reachableInfinitary : InfinitaryFormula.{w, 0, 0} Language.graph 3).Realize
            (Function.update (Function.update a 0 u) 1 v)) := by
    let := G.structure
    simp only [connectedInfinitary, InfinitaryFormula.realize_all]
  rw [h1]
  simp only [realize_reachableInfinitary,
    Function.update_of_ne (by decide : (0 : Fin 3) ≠ 1), Function.update_self]
  rfl

/-- **Graph connectivity is definable in `L^3_{∞ω}`** on all nonempty simple graphs. -/
@[simp] theorem realize_connectedInfinitary_iff_connected {V : Type w₁} (G : SimpleGraph V)
    (a : Fin 3 → V) :
    (letI := G.structure;
      (connectedInfinitary : InfinitaryFormula.{w, 0, 0} Language.graph 3).Realize a) ↔
      G.Connected := by
  have : Nonempty V := ⟨a 0⟩
  rw [realize_connectedInfinitary_iff_preconnected, SimpleGraph.connected_iff]
  exact ⟨fun h => ⟨h, inferInstance⟩, fun h => h.1⟩

end Reachability

section EvenCardinality

/-- The closed `C^1_{∞ω}` formula (`freeVars = ∅`, quantifier rank `≤ 1`) expressing that a finite
structure has an even number of elements: `⋁_{m ∈ ℕ} ∃^{= 2m} x₀ ⊤`. -/
def evenCardInfinitary (L : Language.{u, v}) : InfinitaryCountingFormula.{w, u, v} L 1 :=
  .iSup fun m : ULift.{w} ℕ => .exactly (2 * m.down) 0 ⊤

@[simp] theorem freeVars_evenCardInfinitary (L : Language.{u, v}) :
    (evenCardInfinitary L : InfinitaryCountingFormula.{w, u, v} L 1).freeVars = ∅ := by
  simp only [evenCardInfinitary, InfinitaryCountingFormula.freeVars_iSup,
    InfinitaryCountingFormula.freeVars_exactly, InfinitaryCountingFormula.freeVars_top_inst,
    Set.empty_sdiff, Set.iUnion_empty]

theorem quantifierRankLE_evenCardInfinitary (L : Language.{u, v}) :
    (evenCardInfinitary L : InfinitaryCountingFormula.{w, u, v} L 1).QuantifierRankLE 1 := by
  simp only [evenCardInfinitary, InfinitaryCountingFormula.quantifierRankLE_iSup,
    InfinitaryCountingFormula.quantifierRankLE_exactly_succ,
    InfinitaryCountingFormula.quantifierRankLE_top_inst, implies_true]

/-- **`EVEN` is definable in `C^1_{∞ω}` on finite structures.** -/
@[simp] theorem realize_evenCardInfinitary {L : Language.{u, v}} {M : Type w₁} [L.Structure M]
    [Finite M] (a : Fin 1 → M) :
    (evenCardInfinitary L : InfinitaryCountingFormula.{w, u, v} L 1).Realize a ↔
      Even (Nat.card M) := by
  have htop : {c : M | (⊤ : InfinitaryCountingFormula.{w, u, v} L 1).Realize
      (Function.update a 0 c)} = Set.univ :=
    Set.ext fun c => by simp only [Set.mem_ofPred_eq, InfinitaryCountingFormula.realize_top_inst,
      Set.mem_univ]
  simp only [evenCardInfinitary, InfinitaryCountingFormula.realize_iSup, ULift.exists,
    InfinitaryCountingFormula.realize_exactly_iff_ncard, htop, Set.ncard_univ]
  exact ⟨fun ⟨m, hm⟩ => ⟨m, by omega⟩, fun ⟨m, hm⟩ => ⟨m, by omega⟩⟩

end EvenCardinality

end FiniteVariable

section EmptyLanguageSeparation

private theorem forth_partialIsoOn_of_isEmpty_relations {L : Language.{u, v}}
    [∀ l, IsEmpty (L.Relations l)] {M : Type w₁} {N : Type w₂} [L.Structure M] [L.Structure N]
    {k : ℕ} (hN : (k : ℕ∞) ≤ (Set.univ : Set N).encard) {S : Set (Fin k)} {a : Fin k → M}
    {b : Fin k → N} (h : PartialIsoOn L S a b) (i : Fin k) (c : M) :
    ∃ d : N, PartialIsoOn L (insert i S) (Function.update a i c) (Function.update b i d) := by
  classical
  by_cases hex : ∃ j ∈ S, j ≠ i ∧ a j = c
  · obtain ⟨j, hjS, -, haj⟩ := hex
    exact ⟨b j, h.update_of_mem hjS haj⟩
  · push Not at hex
    have hcard_lt : (b '' (S \ {i})).encard < (Set.univ : Set N).encard := by
      have hsub : S \ {i} ⊆ ↑(Finset.univ.erase i) := fun j hj =>
        Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hj.2, Finset.mem_univ j⟩)
      have hcompl : (↑(Finset.univ.erase i) : Set (Fin k)).encard < (k : ℕ∞) := by
        rw [Set.encard_coe_eq_coe_finsetCard, Nat.cast_lt]
        exact (Finset.card_erase_lt_of_mem (Finset.mem_univ i)).trans_eq (Finset.card_fin k)
      exact ((Set.encard_image_le b _).trans (Set.encard_le_encard hsub)).trans_lt
        (hcompl.trans_le hN)
    have hne : b '' (S \ {i}) ≠ Set.univ := fun heq => by
      rw [heq] at hcard_lt
      exact lt_irrefl _ hcard_lt
    have hex_d : ∃ d : N, d ∉ b '' (S \ {i}) := by
      by_contra! hall
      exact hne (Set.eq_univ_of_forall hall)
    obtain ⟨d, hd⟩ := hex_d
    have hdb : ∀ j ∈ S, j ≠ i → d ≠ b j := fun j hjS hji hdj => hd ⟨j, ⟨hjS, hji⟩, hdj.symm⟩
    exact ⟨d, ⟨fun p hp q hq => h.update_eq_iff_of_fresh hex hdb hp hq, fun R => isEmptyElim R⟩⟩

/-- Over a language with no relation symbols, if both `M` and `N` have at least `k` elements,
`PartialIsoOn L` is a back-and-forth invariant for the `k`-pebble game: moving pebble `i` leaves
at most `k - 1` other placed pebbles, so a fresh element always exists on both sides. -/
theorem isPebbleBackAndForth_of_isEmpty_relations {L : Language.{u, v}}
    [∀ l, IsEmpty (L.Relations l)] {M : Type w₁} {N : Type w₂} [L.Structure M] [L.Structure N]
    {k : ℕ} (hM : (k : ℕ∞) ≤ (Set.univ : Set M).encard)
    (hN : (k : ℕ∞) ≤ (Set.univ : Set N).encard) :
    IsPebbleBackAndForth L (PartialIsoOn L (M := M) (N := N) (k := k)) := by
  refine ⟨fun h => h, fun h i c => forth_partialIsoOn_of_isEmpty_relations hN h i c,
    fun h i d => ?_⟩
  obtain ⟨c, hc⟩ := forth_partialIsoOn_of_isEmpty_relations hM h.symm i d
  exact ⟨c, hc.symm⟩

/-- Duplicator wins the infinite `k`-pebble game over `Language.empty` between `Fin (k + 1)` and
`Fin (k + 2)` from the empty position. -/
theorem pebbleWinsForever_fin_succ (k : ℕ) (a : Fin k → Fin (k + 1)) (b : Fin k → Fin (k + 2)) :
    letI : Language.empty.Structure (Fin (k + 1)) := Language.emptyStructure
    letI : Language.empty.Structure (Fin (k + 2)) := Language.emptyStructure
    PebbleWinsForever Language.empty ∅ a b := by
  let := (Language.emptyStructure : Language.empty.Structure (Fin (k + 1)))
  let := (Language.emptyStructure : Language.empty.Structure (Fin (k + 2)))
  have h1 : (k : ℕ∞) ≤ (Set.univ : Set (Fin (k + 1))).encard := by
    rw [← (Set.toFinite _).cast_ncard_eq, Set.ncard_univ, Nat.card_fin, Nat.cast_le]
    exact Nat.le_succ k
  have h2 : (k : ℕ∞) ≤ (Set.univ : Set (Fin (k + 2))).encard := by
    rw [← (Set.toFinite _).cast_ncard_eq, Set.ncard_univ, Nat.card_fin, Nat.cast_le]
    omega
  exact (isPebbleBackAndForth_of_isEmpty_relations h1 h2).pebbleWinsForever (partialIsoOn_empty a b)

/-- **`EVEN` is not definable in `L^k_{∞ω}` for any `k : ℕ`.** Unlike `C^1_{∞ω}`
(`realize_evenCardInfinitary`), no closed `L^k_{∞ω}` formula over the empty language separates
even-sized finite sets from odd-sized ones, because Duplicator wins the infinite `k`-pebble game
between `Fin (k + 1)` and `Fin (k + 2)`. -/
theorem not_exists_infinitaryFormula_even_card (k : ℕ) :
    ¬∃ φ : FiniteVariable.InfinitaryFormula.{w, 0, 0} Language.empty k, φ.freeVars = ∅ ∧
      ∀ (n : ℕ) (a : Fin k → Fin (n + 1)),
        (letI : Language.empty.Structure (Fin (n + 1)) := Language.emptyStructure;
          φ.Realize a) ↔ Even (n + 1) := by
  rintro ⟨φ, hfree, hφ⟩
  let a : Fin k → Fin (k + 1) := fun _ => 0
  let b : Fin k → Fin (k + 2) := fun _ => 0
  have hwin := pebbleWinsForever_fin_succ k a b
  have heq :
      (letI : Language.empty.Structure (Fin (k + 1)) := Language.emptyStructure; φ.Realize a) ↔
      (letI : Language.empty.Structure (Fin (k + 2)) := Language.emptyStructure; φ.Realize b) := by
    let := (Language.emptyStructure : Language.empty.Structure (Fin (k + 1)))
    let := (Language.emptyStructure : Language.empty.Structure (Fin (k + 2)))
    exact hwin.realize_infinitaryFormula_iff (by rw [hfree])
  rw [hφ k a, hφ (k + 1) b] at heq
  rw [Nat.even_add_one (n := k + 1)] at heq
  exact iff_not_self heq

end EmptyLanguageSeparation

end Cslib.Logic.FO
