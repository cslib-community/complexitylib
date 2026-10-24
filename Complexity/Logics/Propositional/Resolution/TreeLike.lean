/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Foundations.Logic.InferenceSystem
public import Complexity.Logics.Propositional.Resolution.Proof
public import Complexity.Computability.DecisionTree.Leaves
import Complexity.Logics.Propositional.Resolution.SizeWidth

/-!
# Tree-like resolution

A *tree-like* resolution derivation (`Cslib.Logic.PL.CNF.Derivation`) is a derivation by
resolution in which every derived clause is used once: a tree whose leaves are clauses of the
formula and whose inner nodes resolve the clauses of their two children. Its size is its number of
nodes (`Cslib.Logic.PL.CNF.Derivation.size`). A tree-like derivation unfolds a resolution proof in
which a line may be used many times, and conversely gives a proof with at most as many lines
(`Cslib.Logic.PL.CNF.Derivation.exists_isProof`).

**Tree-like resolution and DPLL search trees.** A decision tree whose leaves are clauses *finds a
falsified clause* of `φ` (`Cslib.DecisionTree.FindsFalsifiedClause`) if, on every assignment,
the leaf it reaches is a clause of `φ` that the assignment falsifies. This models the search-tree
certificates of [Davis, Logemann and Loveland][DavisLogemannLoveland1962], allowing repeated
queries.
The correspondence concerns certificates; no solver implementation or runtime bound is given.
A tree-like refutation is such a tree, with one leaf for each leaf of the refutation, querying
the variable resolved at each node
(`Cslib.Logic.PL.CNF.Derivation.findsFalsifiedClause_toDecisionTree`).
Conversely, a decision tree finding falsified clauses gives a tree-like refutation with fewer
nodes than twice its number of leaves
(`Cslib.DecisionTree.FindsFalsifiedClause.exists_derivation`): along a path, the clauses reached
below each node resolve on the variable queried there to a clause falsified by the answers above
it.

**Short tree-like refutations are narrow** [Ben-Sasson and Wigderson, Theorem 3.3]
[BenSassonWigderson2001]: a formula with clauses of width at most `k` and a tree-like refutation of
at most `2 ^ b` nodes is refutable in width at most `k + b`
(`Cslib.Logic.PL.CNF.RefutableInWidth.of_derivation`). The two subtrees of the root refute the two
restrictions of the formula by the variable resolved there; the smaller has at most half the
nodes, so by induction its restriction is refutable in width `k + b - 1`, and the other in width
`k + b`, which `Cslib.Logic.PL.CNF.RefutableInWidth.of_restrict` combines.

## Main definitions

* `Cslib.Logic.PL.CNF.Derivation`, `Cslib.Logic.PL.CNF.Derivation.size`: tree-like derivations
  and their number of nodes, providing `Cslib.Logic.InferenceSystem` (`{d | d ∈ φ}⇓c`) and
  `Cslib.Logic.HasInferenceSystem` (`⇓(φ, c)`) instances.
* `Cslib.Logic.PL.CNF.Derivation.toDecisionTree`: the decision tree of a tree-like derivation.
* `Cslib.DecisionTree.FindsFalsifiedClause`: decision trees finding falsified clauses.

## Main results

* `Cslib.Logic.PL.CNF.derives_iff_nonempty_derivation`,
  `Cslib.Logic.PL.CNF.derives_iff_derivableIn`,
  `Cslib.Logic.PL.CNF.derives_iff_derivable`: `φ.Derives c` is equivalent to
  `Nonempty (φ.Derivation c)` and to `InferenceSystem.DerivableIn` / `InferenceSystem.Derivable`.
* `Cslib.Logic.PL.CNF.Derivation.restrict`: restricting a tree-like derivation.
* `Cslib.Logic.PL.CNF.Derivation.findsFalsifiedClause_toDecisionTree`,
  `Cslib.DecisionTree.FindsFalsifiedClause.exists_derivation`: tree-like refutations and decision
  trees finding falsified clauses convert into each other.
* `Cslib.Logic.PL.CNF.RefutableInWidth.of_derivation`: short tree-like refutations are narrow.

## References

* [E. Ben-Sasson, A. Wigderson, *Short proofs are narrow—resolution made
  simple*][BenSassonWigderson2001]
* [M. Davis, G. Logemann, D. Loveland, *A machine program for
  theorem-proving*][DavisLogemannLoveland1962]
-/

@[expose] public section

namespace Cslib.Logic.PL

variable {V : Type*} [DecidableEq V]

/-- A **tree-like resolution derivation** of `c` from `φ`: a clause of `φ`, or the resolvent of
the conclusions of two tree-like derivations on a variable occurring positively in the first and
negatively in the second. -/
inductive CNF.Derivation (φ : CNF V) : Clause V → Type _
  /-- A clause of `φ`. -/
  | mem {c : Clause V} (hc : c ∈ φ) : CNF.Derivation φ c
  /-- The resolvent of the conclusions of two derivations. -/
  | resolvent {c₁ c₂ : Clause V} (v : V) (d₁ : CNF.Derivation φ c₁) (d₂ : CNF.Derivation φ c₂)
      (hv₁ : (v, true) ∈ c₁) (hv₂ : (v, false) ∈ c₂) : CNF.Derivation φ (c₁.resolvent c₂ v)

namespace CNF

variable {φ : CNF V} {c : Clause V}

namespace Derivation

/-- The number of nodes of a tree-like derivation. -/
def size : {c : Clause V} → φ.Derivation c → ℕ
  | _, mem _ => 1
  | _, resolvent _ d₁ d₂ _ _ => d₁.size + d₂.size + 1

/-- A leaf derivation of a clause of `φ` has size `1`. -/
@[simp] theorem size_mem (hc : c ∈ φ) : (mem hc).size = 1 := rfl

/-- The size of a resolution step is the sum of the sizes of its two subderivations plus `1`. -/
@[simp] theorem size_resolvent {c₁ c₂ : Clause V} (v : V) (d₁ : φ.Derivation c₁)
    (d₂ : φ.Derivation c₂) (hv₁ : (v, true) ∈ c₁) (hv₂ : (v, false) ∈ c₂) :
    (resolvent v d₁ d₂ hv₁ hv₂).size = d₁.size + d₂.size + 1 := rfl

/-- A tree-like derivation has a node. -/
theorem size_pos : {c : Clause V} → (d : φ.Derivation c) → 0 < d.size
  | _, mem _ => Nat.one_pos
  | _, resolvent .. => Nat.succ_pos _

/-- The conclusion of a tree-like derivation is derivable. -/
theorem derives : {c : Clause V} → φ.Derivation c → φ.Derives c
  | _, mem hc => .mem hc
  | _, resolvent v d₁ d₂ hv₁ hv₂ => .resolvent v d₁.derives d₂.derives hv₁ hv₂

/-- A tree-like derivation gives a proof with at most as many lines as it has nodes. -/
theorem exists_isProof : {c : Clause V} → (d : φ.Derivation c) →
    ∃ ls, φ.IsProof ls ∧ c ∈ ls ∧ ls.length ≤ d.size
  | _, mem hc => ⟨[_], IsProof.nil.mem hc, List.mem_singleton_self _, le_rfl⟩
  | _, resolvent v d₁ d₂ hv₁ hv₂ => by
    obtain ⟨ls₁, h₁, hc₁, hl₁⟩ := d₁.exists_isProof
    obtain ⟨ls₂, h₂, hc₂, hl₂⟩ := d₂.exists_isProof
    refine ⟨_, (h₁.append h₂).resolvent v (List.mem_append_left _ hc₁)
      (List.mem_append_right _ hc₂) hv₁ hv₂, List.mem_cons_self, ?_⟩
    simp only [List.length_cons, List.length_append, size_resolvent]
    omega

/-- A tree-like refutation of `s` nodes gives a refutation of at most `s` lines. -/
theorem refutableInSize (d : φ.Derivation []) : φ.RefutableInSize d.size :=
  let ⟨ls, h, hnil, hlen⟩ := d.exists_isProof
  ⟨ls, h, hnil, hlen⟩

/-- A clause derived from `φ` with `v` fixed does not mention `v`. -/
theorem fst_ne_of_restrict {v : V} {b : Bool} (d : (φ.restrict v b).Derivation c)
    {l : Literal V} (hl : l ∈ c) : l.1 ≠ v :=
  let ⟨_, h, hc, _⟩ := d.exists_isProof
  h.fst_ne_of_restrict hc hl

/-- **Restricting a tree-like derivation.** A tree-like derivation from `φ` of a clause without the
literal `(v, b)` becomes a tree-like derivation from `φ` with `v` fixed to `b`, with at most as many
nodes, of a clause with a subset of its literals. -/
theorem restrict (v : V) (b : Bool) (d : φ.Derivation c) (hvc : (v, b) ∉ c) :
    ∃ (c' : Clause V) (d' : (φ.restrict v b).Derivation c'), (∀ l ∈ c', l ∈ c) ∧
      d'.size ≤ d.size := by
  induction d with
  | mem hc =>
    exact ⟨_, .mem (mem_restrict.2 ⟨_, hc, hvc, rfl⟩), fun l hl => (List.mem_filter.1 hl).1,
      le_rfl⟩
  | @resolvent c₁ c₂ u d₁ d₂ hu₁ hu₂ ih₁ ih₂ =>
    by_cases hv₁ : (v, b) ∈ c₁
    · -- `v = u` and `b = true`: the second premise will do
      have huv : (v, b) = (u, true) := by
        by_contra hne
        exact hvc (Clause.mem_resolvent.2 (Or.inl ⟨hv₁, hne⟩))
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj huv
      obtain ⟨c₂', d₂', hsub₂, hsize₂⟩ :=
        ih₂ fun hv₂ => hvc (Clause.mem_resolvent.2 (Or.inr ⟨hv₂, by simp⟩))
      refine ⟨c₂', d₂', fun l hl => Clause.mem_resolvent.2 (Or.inr ⟨hsub₂ l hl, ?_⟩), ?_⟩
      · rintro rfl
        exact d₂'.fst_ne_of_restrict hl rfl
      · rw [size_resolvent]
        omega
    by_cases hv₂ : (v, b) ∈ c₂
    · have huv : (v, b) = (u, false) := by
        by_contra hne
        exact hvc (Clause.mem_resolvent.2 (Or.inr ⟨hv₂, hne⟩))
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj huv
      obtain ⟨c₁', d₁', hsub₁, hsize₁⟩ := ih₁ hv₁
      refine ⟨c₁', d₁', fun l hl => Clause.mem_resolvent.2 (Or.inl ⟨hsub₁ l hl, ?_⟩), ?_⟩
      · rintro rfl
        exact d₁'.fst_ne_of_restrict hl rfl
      · rw [size_resolvent]
        omega
    obtain ⟨c₁', d₁', hsub₁, hsize₁⟩ := ih₁ hv₁
    obtain ⟨c₂', d₂', hsub₂, hsize₂⟩ := ih₂ hv₂
    by_cases hu₁' : (u, true) ∈ c₁'
    · by_cases hu₂' : (u, false) ∈ c₂'
      · refine ⟨_, .resolvent u d₁' d₂' hu₁' hu₂', fun l hl => ?_, ?_⟩
        · rcases Clause.mem_resolvent.1 hl with ⟨hl, hne⟩ | ⟨hl, hne⟩
          · exact Clause.mem_resolvent.2 (Or.inl ⟨hsub₁ l hl, hne⟩)
          · exact Clause.mem_resolvent.2 (Or.inr ⟨hsub₂ l hl, hne⟩)
        · simp only [size_resolvent]
          omega
      · refine ⟨c₂', d₂', fun l hl => Clause.mem_resolvent.2 (Or.inr ⟨hsub₂ l hl, ?_⟩), ?_⟩
        · rintro rfl
          exact hu₂' hl
        · rw [size_resolvent]
          omega
    · refine ⟨c₁', d₁', fun l hl => Clause.mem_resolvent.2 (Or.inl ⟨hsub₁ l hl, ?_⟩), ?_⟩
      · rintro rfl
        exact hu₁' hl
      · rw [size_resolvent]
        omega

/-! ### Decision trees -/

/-- The decision tree of a tree-like derivation: a leaf for each clause of the formula used, and a
query of the resolved variable at each resolution step, answering `false` towards the premise
with the variable positive. -/
def toDecisionTree : {c : Clause V} → φ.Derivation c → DecisionTree V (Clause V)
  | _, mem (c := c) _ => .leaf c
  | _, resolvent v d₁ d₂ _ _ => .node v d₁.toDecisionTree d₂.toDecisionTree

/-- The decision tree of a tree-like derivation has one leaf for each leaf of the derivation. -/
theorem two_mul_leafCount_toDecisionTree :
    {c : Clause V} → (d : φ.Derivation c) → 2 * d.toDecisionTree.leafCount = d.size + 1
  | _, mem _ => rfl
  | _, resolvent _ d₁ d₂ _ _ => by
    have h₁ := d₁.two_mul_leafCount_toDecisionTree
    have h₂ := d₂.two_mul_leafCount_toDecisionTree
    simp only [toDecisionTree, DecisionTree.leafCount, size_resolvent]
    omega

/-- On an assignment falsifying the conclusion of a tree-like derivation, its decision tree reaches
a clause of the formula falsified by the assignment. -/
theorem eval_toDecisionTree : {c : Clause V} → (d : φ.Derivation c) → {σ : V → Bool} →
    c.eval σ = false →
      d.toDecisionTree.eval σ ∈ φ ∧ (d.toDecisionTree.eval σ).eval σ = false
  | _, mem hc, _, hσ => ⟨hc, hσ⟩
  | _, resolvent (c₁ := c₁) (c₂ := c₂) v d₁ d₂ _ _, σ, hσ => by
    have hσ' : ∀ l ∈ c₁.resolvent c₂ v, σ l.1 ≠ l.2 := fun l hl h =>
      Bool.false_ne_true (hσ.symm.trans ((Clause.eval_eq_true_iff _ _).2 ⟨l, hl, h⟩))
    simp only [toDecisionTree, DecisionTree.eval]
    cases hv : σ v
    · refine d₁.eval_toDecisionTree (Bool.eq_false_iff.2 fun h => ?_)
      obtain ⟨l, hl, hl'⟩ := (Clause.eval_eq_true_iff _ _).1 h
      by_cases hlv : l = (v, true)
      · subst hlv
        simp [hv] at hl'
      · exact hσ' l (Clause.mem_resolvent.2 (Or.inl ⟨hl, hlv⟩)) hl'
    · refine d₂.eval_toDecisionTree (Bool.eq_false_iff.2 fun h => ?_)
      obtain ⟨l, hl, hl'⟩ := (Clause.eval_eq_true_iff _ _).1 h
      by_cases hlv : l = (v, false)
      · subst hlv
        simp [hv] at hl'
      · exact hσ' l (Clause.mem_resolvent.2 (Or.inr ⟨hl, hlv⟩)) hl'

end Derivation

/-- A derivable clause has a tree-like derivation, unfolding each shared premise into its own
subtree. -/
theorem Derives.nonempty_derivation (h : φ.Derives c) : Nonempty (φ.Derivation c) := by
  induction h with
  | mem hc => exact ⟨.mem hc⟩
  | resolvent v _ _ hv₁ hv₂ ih₁ ih₂ =>
    obtain ⟨d₁⟩ := ih₁
    obtain ⟨d₂⟩ := ih₂
    exact ⟨.resolvent v d₁ d₂ hv₁ hv₂⟩

/-- A clause is derivable from `φ` if and only if it has a tree-like derivation from `φ`. -/
theorem derives_iff_nonempty_derivation : φ.Derives c ↔ Nonempty (φ.Derivation c) :=
  ⟨Derives.nonempty_derivation, fun ⟨d⟩ => d.derives⟩

/-- Tree-like resolution derivations from `φ` as a `Cslib.Logic.InferenceSystem` indexed by the
clauses of `φ` (`{d // d ∈ φ}⇓c`). -/
instance (φ : CNF V) : InferenceSystem {d // d ∈ φ} (Clause V) where
  derivation := φ.Derivation

/-- Tree-like resolution derivations from `φ` as a `Cslib.Logic.InferenceSystem` indexed by the
clause set `{d | d ∈ φ}` (`{d | d ∈ φ}⇓c`). -/
instance (φ : CNF V) : InferenceSystem ({d | d ∈ φ} : Set (Clause V)) (Clause V) where
  derivation := φ.Derivation

/-- Tree-like resolution derivations as a canonical `Cslib.Logic.HasInferenceSystem` on
formula–clause pairs (`⇓(φ, c)`). -/
instance : HasInferenceSystem (CNF V × Clause V) where
  derivation p := p.1.Derivation p.2

/-- Derivability by resolution is `Cslib.Logic.InferenceSystem.DerivableIn` for the clauses of
`φ`. -/
theorem derives_iff_derivableIn :
    φ.Derives c ↔ InferenceSystem.DerivableIn {d | d ∈ φ} c :=
  derives_iff_nonempty_derivation

/-- Derivability by resolution is `Cslib.Logic.InferenceSystem.Derivable` for the pair `(φ, c)`. -/
theorem derives_iff_derivable :
    φ.Derives c ↔ InferenceSystem.Derivable (φ, c) :=
  derives_iff_nonempty_derivation

end CNF

/-- A decision tree with clauses at its leaves **finds a falsified clause** of `φ` if, on every
assignment, the clause at the leaf it reaches is a clause of `φ` that the assignment falsifies.
These are the search trees of the DPLL procedure on `φ`. -/
def _root_.Cslib.DecisionTree.FindsFalsifiedClause (t : DecisionTree V (Clause V)) (φ : CNF V) :
    Prop :=
  ∀ σ : V → Bool, t.eval σ ∈ φ ∧ (t.eval σ).eval σ = false

namespace CNF

variable {φ : CNF V}

/-- **A tree-like refutation is a DPLL tree**: its decision tree finds a falsified clause. -/
theorem Derivation.findsFalsifiedClause_toDecisionTree (d : φ.Derivation []) :
    d.toDecisionTree.FindsFalsifiedClause φ :=
  fun _ => d.eval_toDecisionTree rfl

/-- The induction behind `DecisionTree.FindsFalsifiedClause.exists_derivation`: if `t` finds a
falsified clause of `φ` on the assignments extending the consistent literals `π`, then it
gives a tree-like derivation of a clause falsified by `π`, with at most twice as many nodes as `t`
has leaves. -/
private theorem exists_derivation_of_eval (φ : CNF V) :
    ∀ (t : DecisionTree V (Clause V)) (π : List (Literal V)),
      (∀ v, (v, true) ∈ π → (v, false) ∉ π) →
      (∀ σ : V → Bool, (∀ l ∈ π, σ l.1 = l.2) → t.eval σ ∈ φ ∧ (t.eval σ).eval σ = false) →
      ∃ (c : Clause V) (d : φ.Derivation c), (∀ l ∈ c, (l.1, !l.2) ∈ π) ∧
        d.size + 1 ≤ 2 * t.leafCount
  | .leaf c, π, hπ, ht => by
    -- the assignment setting the variables of `π` as `π` does, and the others to `false`
    let σ₀ : V → Bool := fun x => decide ((x, true) ∈ π)
    have hσ₀ : ∀ l ∈ π, σ₀ l.1 = l.2 := by
      rintro ⟨x, _ | _⟩ hl
      · simpa [σ₀] using fun h => hπ x h hl
      · simpa [σ₀] using hl
    refine ⟨c, .mem (ht σ₀ hσ₀).1, fun ⟨u, a⟩ hl => ?_, le_rfl⟩
    by_contra hna
    -- setting `u` to `a` extends `π` and satisfies `c`
    have hext : ∀ l ∈ π, Function.update σ₀ u a l.1 = l.2 := by
      rintro ⟨x, a'⟩ hl'
      by_cases hxu : x = u
      · subst hxu
        rw [Function.update_self]
        cases a <;> cases a' <;> simp_all
      · rw [Function.update_of_ne hxu]
        exact hσ₀ _ hl'
    have := (ht _ hext).2
    rw [Bool.eq_false_iff] at this
    exact this ((Clause.eval_eq_true_iff _ _).2 ⟨(u, a), hl, by simp⟩)
  | .node u t₀ t₁, π, hπ, ht => by
    have hcount : t₀.leafCount + t₁.leafCount = (DecisionTree.node u t₀ t₁).leafCount := rfl
    by_cases hu₁ : (u, true) ∈ π
    · obtain ⟨c, d, hc, hsize⟩ := exists_derivation_of_eval φ t₁ π hπ fun σ hσ => by
        simpa [DecisionTree.eval, hσ _ hu₁] using ht σ hσ
      exact ⟨c, d, hc, by omega⟩
    by_cases hu₀ : (u, false) ∈ π
    · obtain ⟨c, d, hc, hsize⟩ := exists_derivation_of_eval φ t₀ π hπ fun σ hσ => by
        simpa [DecisionTree.eval, hσ _ hu₀] using ht σ hσ
      exact ⟨c, d, hc, by omega⟩
    -- query `u` afresh: derive from both answers and resolve on `u` if necessary
    have hπ₀ : ∀ v, (v, true) ∈ (u, false) :: π → (v, false) ∉ (u, false) :: π := by
      intro v hv hv'
      simp only [List.mem_cons, Prod.mk.injEq, Bool.true_eq_false, and_false, false_or] at hv
      rcases List.mem_cons.1 hv' with h | h
      · obtain ⟨rfl, -⟩ := Prod.mk.inj h
        exact hu₁ hv
      · exact hπ v hv h
    have hπ₁ : ∀ v, (v, true) ∈ (u, true) :: π → (v, false) ∉ (u, true) :: π := by
      intro v hv hv'
      simp only [List.mem_cons, Prod.mk.injEq, Bool.false_eq_true, and_false, false_or] at hv'
      rcases List.mem_cons.1 hv with h | h
      · obtain ⟨rfl, -⟩ := Prod.mk.inj h
        exact hu₀ hv'
      · exact hπ v h hv'
    obtain ⟨c₀, d₀, hc₀, hsize₀⟩ := exists_derivation_of_eval φ t₀ ((u, false) :: π) hπ₀
      fun σ hσ => by
        have hσu : σ u = false := hσ _ List.mem_cons_self
        simpa [DecisionTree.eval, hσu] using ht σ fun l hl => hσ l (List.mem_cons_of_mem _ hl)
    obtain ⟨c₁, d₁, hc₁, hsize₁⟩ := exists_derivation_of_eval φ t₁ ((u, true) :: π) hπ₁
      fun σ hσ => by
        have hσu : σ u = true := hσ _ List.mem_cons_self
        simpa [DecisionTree.eval, hσu] using ht σ fun l hl => hσ l (List.mem_cons_of_mem _ hl)
    -- a literal of `c₀` other than `(u, true)` is falsified by `π`, and likewise for `c₁`
    have hc₀' : ∀ l ∈ c₀, l ≠ (u, true) → (l.1, !l.2) ∈ π := fun l hl hne => by
      rcases List.mem_cons.1 (hc₀ l hl) with h | h
      · obtain ⟨l₁, l₂⟩ := l
        simp only [Prod.mk.injEq, Bool.not_eq_eq_eq_not, Bool.not_false] at h
        exact absurd (by rw [h.1, h.2]) hne
      · exact h
    have hc₁' : ∀ l ∈ c₁, l ≠ (u, false) → (l.1, !l.2) ∈ π := fun l hl hne => by
      rcases List.mem_cons.1 (hc₁ l hl) with h | h
      · obtain ⟨l₁, l₂⟩ := l
        simp only [Prod.mk.injEq, Bool.not_eq_eq_eq_not, Bool.not_true] at h
        exact absurd (by rw [h.1, h.2]) hne
      · exact h
    by_cases hv₀ : (u, true) ∈ c₀
    · by_cases hv₁ : (u, false) ∈ c₁
      · refine ⟨_, .resolvent u d₀ d₁ hv₀ hv₁, fun l hl => ?_, ?_⟩
        · rcases Clause.mem_resolvent.1 hl with ⟨hl, hne⟩ | ⟨hl, hne⟩
          exacts [hc₀' l hl hne, hc₁' l hl hne]
        · rw [Derivation.size_resolvent]
          omega
      · exact ⟨c₁, d₁, fun l hl => hc₁' l hl fun h => hv₁ (h ▸ hl), by omega⟩
    · exact ⟨c₀, d₀, fun l hl => hc₀' l hl fun h => hv₀ (h ▸ hl), by omega⟩

end CNF

/-- **A DPLL tree is a tree-like refutation**: a decision tree finding a falsified clause of `φ`
gives a tree-like refutation of `φ` with fewer nodes than twice its number of leaves. -/
theorem _root_.Cslib.DecisionTree.FindsFalsifiedClause.exists_derivation {φ : CNF V}
    {t : DecisionTree V (Clause V)} (ht : t.FindsFalsifiedClause φ) :
    ∃ d : φ.Derivation [], d.size + 1 ≤ 2 * t.leafCount := by
  obtain ⟨c, d, hc, hsize⟩ := CNF.exists_derivation_of_eval φ t [] (by simp) fun σ _ => ht σ
  obtain rfl : c = [] := List.eq_nil_iff_forall_not_mem.2 fun l hl => by simpa using hc l hl
  exact ⟨d, hsize⟩

namespace CNF

variable {φ : CNF V}

/-! ### Short tree-like refutations are narrow -/

/-- **Short tree-like refutations are narrow** [Ben-Sasson and Wigderson, Theorem 3.3]
[BenSassonWigderson2001]. A formula whose clauses have width at most `k`, with a tree-like
refutation of at most `2 ^ b` nodes, is refutable in width at most `k + b`. -/
theorem RefutableInWidth.of_derivation {k b : ℕ} (hk : ∀ c ∈ φ, c.width ≤ k) {c : Clause V}
    (d : φ.Derivation c) (hc : c = []) (hd : d.size ≤ 2 ^ b) : φ.RefutableInWidth (k + b) := by
  induction hn : d.size using Nat.strong_induction_on generalizing φ c b with
  | _ n ih =>
  cases d with
  | mem hmem =>
    subst hc
    exact RefutableInWidth.mono ⟨[[]], IsProof.nil.mem hmem, List.mem_singleton_self _,
      by simp⟩ (Nat.zero_le _)
  | @resolvent c₁ c₂ v d₁ d₂ hv₁ hv₂ =>
    simp only [Derivation.size_resolvent] at hn hd
    -- the premises are the unit clauses of `v` and of its negation
    have hl₁ : ∀ l ∈ c₁, l = (v, true) := fun l hl => by
      by_contra hne
      have : l ∈ c₁.resolvent c₂ v := Clause.mem_resolvent.2 (Or.inl ⟨hl, hne⟩)
      rw [hc] at this
      exact List.not_mem_nil this
    have hl₂ : ∀ l ∈ c₂, l = (v, false) := fun l hl => by
      by_contra hne
      have : l ∈ c₁.resolvent c₂ v := Clause.mem_resolvent.2 (Or.inr ⟨hl, hne⟩)
      rw [hc] at this
      exact List.not_mem_nil this
    obtain ⟨c₁', d₁', hsub₁, hsize₁⟩ := d₁.restrict v false fun h => by simpa using hl₁ _ h
    obtain ⟨c₂', d₂', hsub₂, hsize₂⟩ := d₂.restrict v true fun h => by simpa using hl₂ _ h
    have hc₁' : c₁' = [] := List.eq_nil_iff_forall_not_mem.2 fun l hl =>
      d₁'.fst_ne_of_restrict hl (by rw [hl₁ l (hsub₁ l hl)])
    have hc₂' : c₂' = [] := List.eq_nil_iff_forall_not_mem.2 fun l hl =>
      d₂'.fst_ne_of_restrict hl (by rw [hl₂ l (hsub₂ l hl)])
    obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := by
      rcases b with _ | b
      · have := d₁.size_pos
        simp only [pow_zero] at hd
        omega
      · exact ⟨b, rfl⟩
    have hk' (γ : Bool) : ∀ c ∈ φ.restrict v γ, c.width ≤ k := fun c hc =>
      width_le_of_mem_restrict hk hc
    have hφ : ∀ c ∈ φ, c.width ≤ k + b + 1 := fun c hc => (hk c hc).trans (by omega)
    rw [pow_succ] at hd
    -- each subtree refutes a restriction; the smaller one has at most `2 ^ b` nodes
    have hwide₁ : (φ.restrict v false).RefutableInWidth (k + (b + 1)) :=
      ih _ (by omega) (hk' false) d₁' hc₁' (b := b + 1) (by rw [pow_succ]; omega) rfl
    have hwide₂ : (φ.restrict v true).RefutableInWidth (k + (b + 1)) :=
      ih _ (by omega) (hk' true) d₂' hc₂' (b := b + 1) (by rw [pow_succ]; omega) rfl
    rcases le_or_gt d₁.size (2 ^ b) with h₁ | h₁
    · exact RefutableInWidth.of_restrict (w := k + b) (b := false) hφ
        (ih _ (by omega) (hk' false) d₁' hc₁' (b := b) (by omega) rfl) hwide₂
    · exact RefutableInWidth.of_restrict (w := k + b) (b := true) hφ
        (ih _ (by omega) (hk' true) d₂' hc₂' (b := b) (by omega) rfl) hwide₁

end CNF

end Cslib.Logic.PL
