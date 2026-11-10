/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Operator.Quantifiers
public import CslibFrontier.Logics.FirstOrder.Operator.TransitiveClosure

/-!
# First-order logic with deterministic tuple transitive closure

The deterministic reduct of a relation `r` keeps an edge `x → y` only when `y` is the unique
`r`-successor of `x`. Deterministic transitive closure (DTC) is the reflexive transitive closure
of this reduct: starting at the source tuple, it follows the unique successor as long as one
exists.

**FO(DTC) reuses the syntax of FO(TC).** A formula of FO(DTC) is an
`Operator.Formula L TC.shape Γ α` read with `DTC.interpretation`; the same syntax tree read with
`TC.interpretation` is an FO(TC) formula. Only the meaning of the closure node differs, so
`TC.tc`, `TC.pair` and the width conventions of `TC.shape`, including width zero, apply
unchanged. Taking the deterministic reduct is not monotone in the body, so there is no `Policy`:
deterministic closure may occur at any polarity, nested to any depth.

`toTC` rewrites every closure body `φ(x, y)` into `φ(x, y) ∧ ¬ ∃ z, φ(x, z) ∧ z ≠ y`, which
expresses the deterministic reduct. Read with `TC.interpretation`, the result means what the
original formula means with `DTC.interpretation`; this embeds FO(DTC) in FO(TC).

## Main definitions

* `deterministicReduct`: the edges of a relation whose source has exactly that one successor.
* `interpretation`: deterministic closure on the operator syntax `TC.shape`.
* `functionalize`: a formula expressing the deterministic reduct of a closure body.
* `toTC`: the translation from FO(DTC) to FO(TC).

## Main results

* `realize_tc`, `realize_tc_pair`: semantics in terms of `Relation.ReflTransGen` of the reduct.
* `interpretation_iff_of_rightUnique`: on deterministic bodies, deterministic closure is closure.
* `realize_toTC`: `toTC` preserves meaning from DTC to TC semantics.

## References

* [N. Immerman, *Languages That Capture Complexity Classes*, Section 4][Immerman1987], defines
  the deterministic reduct and `DTC`, and states `L = (FO + DTC)` (Theorem 4.2).
* [N. Immerman, *Descriptive Complexity*, Chapter 9][Immerman1999]
-/

public section

universe u v w z

open FirstOrder Language Cslib.Logic.FO.Operator

namespace Cslib.Logic.FO.DTC

/-- The edges of `r` from a source whose only `r`-successor is the target. -/
@[expose] def deterministicReduct {β : Type*} (r : β → β → Prop) : β → β → Prop :=
  fun x y => r x y ∧ ∀ z, r x z → z = y

/-- Every edge of the deterministic reduct is an edge of the relation. -/
theorem deterministicReduct_le {β : Type*} {r : β → β → Prop} {x y : β}
    (h : deterministicReduct r x y) : r x y :=
  h.1

/-- Each source has at most one successor in the deterministic reduct. -/
theorem rightUnique_deterministicReduct {β : Type*} (r : β → β → Prop) :
    Relator.RightUnique (deterministicReduct r) :=
  fun _ _ _ hy hz => hz.2 _ hy.1

/-- A relation with at most one successor per source is its own deterministic reduct. -/
theorem deterministicReduct_eq_self {β : Type*} {r : β → β → Prop}
    (hr : Relator.RightUnique r) : deterministicReduct r = r := by
  funext x y
  exact propext ⟨fun h => h.1, fun h => ⟨h, fun _ hz => hr hz h⟩⟩

/-- Interpret the closure syntax `TC.shape` as reflexive reachability along unique successors.

The same syntax read with `TC.interpretation` is ordinary transitive closure. -/
@[expose] def interpretation {M : Type z} : Interpretation TC.shape M :=
  fun _ bodies args =>
    Relation.ReflTransGen
      (deterministicReduct fun xs ys => bodies (0 : Fin 1) RelEnv.empty (TC.pair xs ys))
      (TC.left args) (TC.right args)

/-- On bodies with at most one successor per source, deterministic closure is closure. -/
theorem interpretation_iff_of_rightUnique {M : Type z} {k : ℕ}
    (bodies : (i : Fin (TC.shape k).slots) → BodyValue ((TC.shape k).binder i) M)
    (h : Relator.RightUnique fun xs ys : Fin k → M =>
      bodies (0 : Fin 1) RelEnv.empty (TC.pair xs ys))
    (args : Fin (TC.shape k).arity → M) :
    interpretation k bodies args ↔ TC.interpretation k bodies args := by
  simp only [interpretation, TC.interpretation, deterministicReduct_eq_self h]

variable {L : Language.{u, v}} {Γ : List ℕ} {α : Type w} {M : Type z} [L.Structure M]

/-- Deterministic closure follows unique successors from the source to the target tuple. -/
@[simp, fo_realize] theorem realize_tc {k : ℕ}
    (body : Formula L TC.shape Γ (α ⊕ Fin (2 * k))) (args : Fin (2 * k) → L.Term α)
    (ρ : RelEnv Γ M) (v : α → M) :
    (TC.tc body args).Realize interpretation ρ v ↔
      Relation.ReflTransGen
        (deterministicReduct fun xs ys =>
          body.Realize interpretation ρ (Sum.elim v (TC.pair xs ys)))
        (fun i => (TC.left args i).realize v) (fun i => (TC.right args i).realize v) := Iff.rfl

/-- Deterministic closure applied to concatenated endpoint terms. -/
@[fo_realize] theorem realize_tc_pair {k : ℕ}
    (body : Formula L TC.shape Γ (α ⊕ Fin (2 * k))) (xs ys : Fin k → L.Term α)
    (ρ : RelEnv Γ M) (v : α → M) :
    (TC.tc body (TC.pair xs ys)).Realize interpretation ρ v ↔
      Relation.ReflTransGen
        (deterministicReduct fun us ws =>
          body.Realize interpretation ρ (Sum.elim v (TC.pair us ws)))
        (fun i => (xs i).realize v) (fun i => (ys i).realize v) := by
  simp only [realize_tc, TC.left_pair, TC.right_pair]

/-- The empty path makes every tuple deterministically reachable from itself. -/
theorem realize_tc_refl {k : ℕ} (body : Formula L TC.shape Γ (α ⊕ Fin (2 * k)))
    (xs : Fin k → L.Term α) (ρ : RelEnv Γ M) (v : α → M) :
    (TC.tc body (TC.pair xs xs)).Realize interpretation ρ v :=
  (realize_tc_pair body xs xs ρ v).2 .refl

/-! ### Translation into FO(TC) -/

/-- Composing with a function commutes with concatenating tuples. -/
private theorem comp_pair {A B : Type*} {k : ℕ} (g : A → B) (xs ys : Fin k → A) :
    g ∘ TC.pair xs ys = TC.pair (g ∘ xs) (g ∘ ys) := by
  funext i
  simp only [Function.comp_apply, TC.pair]
  refine Fin.addCases (fun j => ?_) (fun j => ?_) (Fin.cast (Nat.two_mul k) i) <;>
    simp only [Fin.append_left, Fin.append_right, Function.comp_apply]

/-- The variables of a closure body extended by a candidate successor: the body's own
variables are on the left, and the candidate successor tuple is on the right. -/
private abbrev Ext (α : Type w) (k : ℕ) := (α ⊕ Fin (2 * k)) ⊕ Fin k

/-- Substitute the candidate successor tuple for the target tuple of a closure body. -/
private def toCandidate {α : Type w} {k : ℕ} : α ⊕ Fin (2 * k) → Ext α k :=
  Sum.elim (fun a => .inl (.inl a))
    (TC.pair (fun i => .inl (.inr (Fin.cast (Nat.two_mul k).symm (Fin.castAdd k i))))
      (fun i => .inr i))

/-- The candidate successor equals the body's target tuple. -/
private def candidateEq {α : Type w} (k : ℕ) : L.Formula (Ext α k) :=
  ((List.finRange k).map fun i =>
    Term.equal (.var (.inr i)) (.var (.inl (.inr (Fin.cast (Nat.two_mul k).symm
      (Fin.natAdd k i)))))).foldr (· ⊓ ·) ⊤

private theorem realize_candidateEq {k : ℕ} (v : α → M) (xs ys zs : Fin k → M) :
    (candidateEq (L := L) (α := α) k).Realize (Sum.elim (Sum.elim v (TC.pair xs ys)) zs) ↔
      zs = ys := by
  have hy : ∀ i : Fin k, TC.pair xs ys (Fin.cast (Nat.two_mul k).symm (i.addNat k)) = ys i := by
    intro i
    have hi : Fin.cast (Nat.two_mul k).symm (i.addNat k) =
        Fin.cast (Nat.two_mul k).symm (Fin.natAdd k i) := Fin.ext (by simp [Nat.add_comm])
    rw [hi]
    exact congrFun (TC.right_pair xs ys) i
  simp [candidateEq, Language.Formula.Realize, Term.equal, hy, funext_iff]

private theorem comp_toCandidate {k : ℕ} (v : α → M) (xs ys zs : Fin k → M) :
    Sum.elim (Sum.elim v (TC.pair xs ys)) zs ∘ toCandidate = Sum.elim v (TC.pair xs zs) := by
  funext x
  rcases x with a | i
  · rfl
  · have hx : (fun j => TC.pair xs ys (Fin.cast (Nat.two_mul k).symm (Fin.castAdd k j))) = xs :=
      TC.left_pair xs ys
    simp only [toCandidate, Function.comp_apply, Sum.elim_inr]
    rw [← Function.comp_apply (f := Sum.elim (Sum.elim v (TC.pair xs ys)) zs), comp_pair]
    simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, hx]

/-- The deterministic reduct of a closure body `φ(x, y)`:
`φ(x, y) ∧ ¬ ∃ z, φ(x, z) ∧ z ≠ y`. -/
def functionalize {k : ℕ} (φ : Formula L TC.shape Γ (α ⊕ Fin (2 * k))) :
    Formula L TC.shape Γ (α ⊕ Fin (2 * k)) :=
  .conj φ (.neg (Formula.exs k (.conj (φ.relabel toCandidate) (.neg (.ofFO (candidateEq k))))))

/-- `functionalize` defines the deterministic reduct of the body relation, under any
interpretation of the operators inside the body. -/
theorem realize_functionalize (I : Interpretation TC.shape M) {k : ℕ}
    (φ : Formula L TC.shape Γ (α ⊕ Fin (2 * k))) (ρ : RelEnv Γ M) (v : α → M)
    (xs ys : Fin k → M) :
    (functionalize φ).Realize I ρ (Sum.elim v (TC.pair xs ys)) ↔
      deterministicReduct (fun us ws => φ.Realize I ρ (Sum.elim v (TC.pair us ws))) xs ys := by
  simp only [functionalize, Operator.Formula.realize_conj, Operator.Formula.realize_neg,
    Operator.Formula.realize_exs, Operator.Formula.realize_relabel, Operator.Formula.realize_ofFO,
    comp_toCandidate, realize_candidateEq, deterministicReduct, not_exists, not_and, not_not]

/-- Replace each closure body by its deterministic reduct, translating FO(DTC) to FO(TC). -/
def toTC : {Γ : List ℕ} → {α : Type w} →
    Formula L TC.shape Γ α → Formula L TC.shape Γ α
  | _, _, .ofFO φ => .ofFO φ
  | _, _, .rel r args => .rel r args
  | _, _, .neg φ => .neg (toTC φ)
  | _, _, .conj φ ψ => .conj (toTC φ) (toTC ψ)
  | _, _, .ex φ => .ex (toTC φ)
  | _, _, .op k body args => .op k (fun i => functionalize (toTC (body i))) args

/-- Read as FO(TC), the translation means what the original formula means as FO(DTC). -/
theorem realize_toTC (φ : Formula L TC.shape Γ α) (ρ : RelEnv Γ M) (v : α → M) :
    (toTC φ).Realize TC.interpretation ρ v ↔ φ.Realize interpretation ρ v := by
  induction φ with
  | ofFO φ => exact Iff.rfl
  | rel r args => exact Iff.rfl
  | neg φ ih => exact not_congr (ih ρ v)
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ ρ v) (ihψ ρ v)
  | ex φ ih => exact exists_congr fun x => ih ρ _
  | op k body args ih =>
    change Relation.ReflTransGen _ _ _ ↔ Relation.ReflTransGen _ _ _
    refine iff_of_eq (congrArg (fun R => Relation.ReflTransGen R _ _)
      (funext fun xs => funext fun ys => propext ?_))
    exact (realize_functionalize TC.interpretation _ _ v xs ys).trans
      (and_congr (ih _ _ _) (forall_congr' fun _ => imp_congr_left (ih _ _ _)))

end Cslib.Logic.FO.DTC
