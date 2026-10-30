/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.Resolution.Proof
public import Cslib.Computability.Circuit.Boolean.Synthesis
public import Complexity.Computability.Circuit.Monotone.Basic

/-!
# Feasible interpolation for resolution

Split the variables of an unsatisfiable formula into shared variables `x`, variables `y` private to
a formula `A(x, y)` and variables `z` private to a formula `B(x, z)`, and conjoin the two formulas
(`Cslib.Logic.PL.CNF.appendShared`). An *interpolant* (`Cslib.Logic.PL.CNF.IsInterpolant`) is a
Boolean function `f` of the shared variables with `A(x, y) → f(x)` and `f(x) → ¬B(x, z)`: it is
true on every assignment `a` of `x` that extends to a model of `A`, and false on every `a` that
extends to a model of `B`. In other words, `f a = false` certifies that `A(a, ·)` is unsatisfiable
and `f a = true` that `B(a, ·)` is. An interpolant exists exactly when `A ∧ B` is unsatisfiable
(`Cslib.Logic.PL.CNF.exists_isInterpolant_iff`). The point of *feasible interpolation* is that a
resolution refutation of `A ∧ B` yields an interpolant computed by a circuit whose size is linear
in the number of lines of the refutation
[Krajíček, Theorem 6.1][Krajicek1997], [Pudlák, Theorem 1][Pudlak1997]
(`Cslib.Logic.PL.CNF.IsProof.exists_interpolant`,
`Cslib.Logic.PL.CNF.RefutableInSize.exists_interpolant`).

The circuit follows the refutation line by line, as in Pudlák's construction. A clause of `A` gets
the constant `false` and a clause of `B` the constant `true`. The resolvent of `c₁ ∋ v` and
`c₂ ∋ ¬v` gets the disjunction of the gates of `c₁` and `c₂` if `v` is private to `A`, their
conjunction if `v` is private to `B`, and the selector `if x then g₂ else g₁` of their gates `g₁`,
`g₂` if `v` is a shared variable `x`. The value at a line tells on which side the line survives
once the shared variables are fixed: if the gate of a line `c` is `false` at `a`, then every model
`y` of `A(a, ·)` satisfies a literal of `c` on a shared or `A`-private variable, and dually if the
gate is `true`. At the empty clause this is the interpolation property. In the De Morgan basis the
selector costs four gates (one negation, two conjunctions and a disjunction) and every other line
one gate, so the circuit has at most four gates per line of the refutation, independently of the
number of variables.

**Monotone interpolation.** If the shared variables occur only positively in `A`, the selector
can be replaced by the monotone gate `(x ∨ g₁) ∧ g₂` [Pudlák, Theorem 2 and its proof][Pudlak1997];
if they occur only negatively in `B`, by the dual gate `(x ∧ g₂) ∨ g₁`. The interpolant is then
computed by a monotone circuit with at most two gates per line
(`Cslib.Logic.PL.CNF.IsProof.exists_monotone_interpolant_of_positive`,
`Cslib.Logic.PL.CNF.IsProof.exists_monotone_interpolant_of_negative`). For the first polarity,
`A` sees only the positive shared literals of a line, which loses nothing on its own clauses. The
monotone gate differs from the selector only at `x = false`, `g₁ = true`, `g₂ = false`; there `A`
sees `c₂` without its literal `¬x`, and so sees the resolvent. The second polarity is dual. A
lower bound on monotone circuits separating the two sets then bounds the size of resolution
refutations from below.

Line-based refutations (`Cslib.Logic.PL.CNF.IsProof`) are propositions, so the circuit is
obtained by induction on the refutation rather than computed from it; the existence statements
here certify its size and correctness, not the running time of extracting it.

## Main definitions

* `Cslib.Logic.PL.CNF.appendShared`: the conjunction `A(x, y) ∧ B(x, z)` as one formula over
  `X ⊕ (Y ⊕ Z)`.
* `Cslib.Logic.PL.CNF.IsInterpolant`: a Boolean function of the shared variables separating the
  assignments extendible to `A` from those extendible to `B`.

## Main results

* `Cslib.Logic.PL.CNF.eval_appendShared`: `A.appendShared B` is the conjunction of `A` and `B`.
* `Cslib.Logic.PL.CNF.IsInterpolant.not_satisfiable`,
  `Cslib.Logic.PL.CNF.exists_isInterpolant_iff`: an interpolant exists exactly when the
  conjunction is unsatisfiable.
* `Cslib.Logic.PL.CNF.IsProof.exists_interpolant`,
  `Cslib.Logic.PL.CNF.RefutableInSize.exists_interpolant`: **feasible interpolation**, a
  refutation with `s` lines gives an interpolant computed by a De Morgan circuit with at most
  `4 s` gates.
* `Cslib.Logic.PL.CNF.IsProof.exists_monotone_interpolant_of_positive`,
  `Cslib.Logic.PL.CNF.IsProof.exists_monotone_interpolant_of_negative`,
  `Cslib.Logic.PL.CNF.RefutableInSize.exists_monotone_interpolant_of_positive`,
  `Cslib.Logic.PL.CNF.RefutableInSize.exists_monotone_interpolant_of_negative`: **monotone
  feasible interpolation**, when the shared variables occur only positively in `A` or only
  negatively in `B`: a refutation with `s` lines gives an interpolant computed by a monotone
  circuit with at most `2 s` gates.

## References

* [J. Krajíček, *Interpolation theorems, lower bounds for proof systems, and independence results
  for bounded arithmetic*][Krajicek1997]
* [P. Pudlák, *Lower bounds for resolution and cutting plane proofs and monotone
  computations*][Pudlak1997]
-/

public section

namespace Cslib.Logic.PL

open Cslib.Circuits

variable {X Y Z : Type*}

/-! ### Formulas with shared variables -/

/-- The conjunction `A(x, y) ∧ B(x, z)` of a formula `A` over shared variables `X` and private
variables `Y` and a formula `B` over the same shared variables and private variables `Z`, as one
formula over `X ⊕ (Y ⊕ Z)`: the clauses of `A`, followed by those of `B`. -/
@[expose] def CNF.appendShared (A : CNF (X ⊕ Y)) (B : CNF (X ⊕ Z)) : CNF (X ⊕ (Y ⊕ Z)) :=
  A.relabel (Sum.map id Sum.inl) ++ B.relabel (Sum.map id Sum.inr)

/-- `A.appendShared B` holds when `A` holds on the shared and `A`-private variables and `B` on
the shared and `B`-private variables. -/
@[simp] theorem CNF.eval_appendShared (A : CNF (X ⊕ Y)) (B : CNF (X ⊕ Z)) (a : X → Bool)
    (y : Y → Bool) (z : Z → Bool) :
    (A.appendShared B).eval (Sum.elim a (Sum.elim y z)) =
      (A.eval (Sum.elim a y) && B.eval (Sum.elim a z)) := by
  have hA : Sum.elim a (Sum.elim y z) ∘ Sum.map id Sum.inl = Sum.elim a y := by
    funext u
    cases u <;> rfl
  have hB : Sum.elim a (Sum.elim y z) ∘ Sum.map id Sum.inr = Sum.elim a z := by
    funext u
    cases u <;> rfl
  rw [CNF.appendShared, CNF.eval_append, CNF.eval_relabel, CNF.eval_relabel, hA, hB]

/-- A Boolean function `f` of the shared variables is an **interpolant** of `A(x, y)` and
`B(x, z)` when `A(x, y) → f(x)` and `f(x) → ¬B(x, z)` are valid: `f` is true on every assignment
of the shared variables that extends to a model of `A`, and false on every one that extends to a
model of `B`. So `f a = false` certifies that `A(a, ·)` is unsatisfiable, and `f a = true` that
`B(a, ·)` is. -/
@[expose] def CNF.IsInterpolant (A : CNF (X ⊕ Y)) (B : CNF (X ⊕ Z)) (f : (X → Bool) → Bool) :
    Prop :=
  (∀ a y, A.eval (Sum.elim a y) = true → f a = true) ∧
    ∀ a z, B.eval (Sum.elim a z) = true → f a = false

/-- A conjunction `A(x, y) ∧ B(x, z)` with an interpolant is unsatisfiable. -/
theorem CNF.IsInterpolant.not_satisfiable {A : CNF (X ⊕ Y)} {B : CNF (X ⊕ Z)}
    {f : (X → Bool) → Bool} (h : A.IsInterpolant B f) : ¬ (A.appendShared B).Satisfiable := by
  rintro ⟨σ, hσ⟩
  have hσ' : σ = Sum.elim (σ ∘ Sum.inl) (Sum.elim (σ ∘ Sum.inr ∘ Sum.inl)
      (σ ∘ Sum.inr ∘ Sum.inr)) := by
    funext u
    rcases u with _ | _ | _ <;> rfl
  rw [hσ', CNF.eval_appendShared, Bool.and_eq_true] at hσ
  have := (h.1 _ _ hσ.1).symm.trans (h.2 _ _ hσ.2)
  exact Bool.noConfusion this

/-- **Craig interpolation for CNF formulas.** `A(x, y)` and `B(x, z)` have an interpolant exactly
when their conjunction is unsatisfiable; whether an assignment of the shared variables extends to
a model of `A` is one. This interpolant need not be easy to compute. -/
theorem CNF.exists_isInterpolant_iff {A : CNF (X ⊕ Y)} {B : CNF (X ⊕ Z)} :
    (∃ f, A.IsInterpolant B f) ↔ ¬ (A.appendShared B).Satisfiable := by
  classical
  refine ⟨fun ⟨_, h⟩ => h.not_satisfiable, fun h => ?_⟩
  refine ⟨fun a => decide (∃ y, A.eval (Sum.elim a y) = true),
    fun a y hA => decide_eq_true ⟨y, hA⟩, fun a z hB => decide_eq_false ?_⟩
  rintro ⟨y, hA⟩
  exact h ⟨Sum.elim a (Sum.elim y z), by rw [CNF.eval_appendShared, hA, hB, Bool.and_self]⟩

/-! ### Refutations guide circuit synthesis -/

section Synthesis

variable {V : Type*} {σ : Signature} {U : Type*} {I : Interpretation σ U} {n : ℕ}

/-- Adding a line related to `f` to lines related to functions in `T` gives lines related to
functions in `T ∪ {f}`. -/
private theorem forall_mem_cons_union {Good : Clause V → ((Fin n → U) → U) → Prop}
    {ls : List (Clause V)} {c : Clause V} {T : Set ((Fin n → U) → U)} {f : (Fin n → U) → U}
    (hls : ∀ e ∈ ls, ∃ g ∈ T, Good e g) (hc : Good c f) :
    ∀ e ∈ c :: ls, ∃ g ∈ T ∪ {f}, Good e g := by
  intro e he
  rcases List.mem_cons.1 he with rfl | he
  · exact ⟨f, Set.mem_union_right _ rfl, hc⟩
  · obtain ⟨g, hg, hge⟩ := hls e he
    exact ⟨g, Set.mem_union_left _ hg, hge⟩

variable [DecidableEq V]

/-- **Proof-guided synthesis.** Let `Good c f` relate clauses to functions. Suppose every clause
of `φ` is related to a function synthesized with `cost` gates, and whenever two clauses are related
to `f₁` and `f₂`, their resolvent is related to a function synthesized from `f₁` and `f₂` with
`cost` further gates. Then the lines of a proof from `φ` are related to functions synthesized
together with `cost` gates per line. -/
private theorem IsProof.exists_synthesis {φ : CNF V} {ls : List (Clause V)}
    (Good : Clause V → ((Fin n → U) → U) → Prop) {cost : ℕ}
    (hmem : ∀ c ∈ φ, ∃ f, Good c f ∧ Synthesis I (inputs n) {f} cost)
    (hres : ∀ (c₁ c₂ : Clause V) (v : V) (f₁ f₂ : (Fin n → U) → U), (v, true) ∈ c₁ →
      (v, false) ∈ c₂ → Good c₁ f₁ → Good c₂ f₂ →
        ∃ f, Good (c₁.resolvent c₂ v) f ∧ Synthesis I (inputs n ∪ {f₁, f₂}) {f} cost)
    (h : φ.IsProof ls) :
    ∃ T, Synthesis I (inputs n) T (cost * ls.length) ∧ ∀ c ∈ ls, ∃ f ∈ T, Good c f := by
  induction h with
  | nil => exact ⟨∅, Synthesis.of_subset (Set.empty_subset _), by simp⟩
  | @mem ls c _ hc ih =>
    obtain ⟨T, hT, hgood⟩ := ih
    obtain ⟨f, hf, hs⟩ := hmem c hc
    refine ⟨T ∪ {f}, ?_, forall_mem_cons_union hgood hf⟩
    rw [List.length_cons, Nat.mul_succ]
    exact hT.comp (hs.mono Set.subset_union_left Set.Subset.rfl le_rfl)
  | @resolvent ls c₁ c₂ v _ h₁ h₂ hv₁ hv₂ ih =>
    obtain ⟨T, hT, hgood⟩ := ih
    obtain ⟨f₁, hf₁, hg₁⟩ := hgood c₁ h₁
    obtain ⟨f₂, hf₂, hg₂⟩ := hgood c₂ h₂
    obtain ⟨f, hf, hs⟩ := hres c₁ c₂ v f₁ f₂ hv₁ hv₂ hg₁ hg₂
    have hsub : inputs n ∪ {f₁, f₂} ⊆ inputs n ∪ T :=
      Set.union_subset_union_right _ (Set.insert_subset_iff.2
        ⟨hf₁, Set.singleton_subset_iff.2 hf₂⟩)
    refine ⟨T ∪ {f}, ?_, forall_mem_cons_union hgood hf⟩
    rw [List.length_cons, Nat.mul_succ]
    exact hT.comp (hs.mono hsub Set.Subset.rfl le_rfl)

/-- Proof-guided synthesis of a circuit for a function related to the empty clause, when the
proof is a refutation. -/
private theorem IsProof.exists_circuit {φ : CNF V} {ls : List (Clause V)}
    (Good : Clause V → ((Fin n → U) → U) → Prop) {cost : ℕ}
    (hmem : ∀ c ∈ φ, ∃ f, Good c f ∧ Synthesis I (inputs n) {f} cost)
    (hres : ∀ (c₁ c₂ : Clause V) (v : V) (f₁ f₂ : (Fin n → U) → U), (v, true) ∈ c₁ →
      (v, false) ∈ c₂ → Good c₁ f₁ → Good c₂ f₂ →
        ∃ f, Good (c₁.resolvent c₂ v) f ∧ Synthesis I (inputs n ∪ {f₁, f₂}) {f} cost)
    (h : φ.IsProof ls) (hnil : [] ∈ ls) :
    ∃ f, Good [] f ∧ ∃ C : Circuit σ n 1, C.Computes I (single f) ∧
      C.size ≤ cost * ls.length := by
  obtain ⟨T, hT, hgood⟩ := IsProof.exists_synthesis Good hmem hres h
  obtain ⟨f, hf, hgf⟩ := hgood [] hnil
  exact ⟨f, hgf, (hT.mono Set.Subset.rfl (Set.singleton_subset_iff.2 hf) le_rfl).exists_circuit⟩

end Synthesis

/-! ### Partial assignments satisfying clauses -/

section Satisfies

variable {V : Type*}

/-- A partial assignment satisfies a clause when it makes one of its literals true. -/
private def Satisfies (ρ : V → Option Bool) (c : Clause V) : Prop :=
  ∃ l ∈ c, ρ l.1 = some l.2

/-- Nothing satisfies the empty clause. -/
private theorem not_satisfies_nil (ρ : V → Option Bool) : ¬ Satisfies ρ [] := by
  simp [Satisfies]

/-- A clause relabelled along `g` is satisfied by `ρ` if one of its literals `l` has
`ρ (g l.1) = some l.2`. -/
private theorem satisfies_relabel {W : Type*} {ρ : V → Option Bool} {g : W → V} {c : Clause W}
    {l : Literal W} (hl : l ∈ c) (hρ : ρ (g l.1) = some l.2) : Satisfies ρ (c.relabel g) :=
  ⟨(g l.1, l.2), List.mem_map_of_mem (f := Prod.map g id) hl, hρ⟩

variable [DecidableEq V]

/-- A partial assignment satisfying the first premise satisfies the resolvent, unless it satisfies
the first premise only through the resolved literal. -/
private theorem Satisfies.resolvent_left {ρ : V → Option Bool} {c₁ c₂ : Clause V} {v : V}
    (h : Satisfies ρ c₁) (hv : ρ v ≠ some true) : Satisfies ρ (c₁.resolvent c₂ v) := by
  obtain ⟨l, hl, hρ⟩ := h
  refine ⟨l, Clause.mem_resolvent.2 (Or.inl ⟨hl, ?_⟩), hρ⟩
  rintro rfl
  exact hv hρ

/-- A partial assignment satisfying the second premise satisfies the resolvent, unless it satisfies
the second premise only through the resolved literal. -/
private theorem Satisfies.resolvent_right {ρ : V → Option Bool} {c₁ c₂ : Clause V} {v : V}
    (h : Satisfies ρ c₂) (hv : ρ v ≠ some false) : Satisfies ρ (c₁.resolvent c₂ v) := by
  obtain ⟨l, hl, hρ⟩ := h
  refine ⟨l, Clause.mem_resolvent.2 (Or.inr ⟨hl, ?_⟩), hρ⟩
  rintro rfl
  exact hv hρ

/-- A partial assignment satisfying both premises satisfies the resolvent. -/
private theorem Satisfies.resolvent {ρ : V → Option Bool} {c₁ c₂ : Clause V} {v : V}
    (h₁ : Satisfies ρ c₁) (h₂ : Satisfies ρ c₂) : Satisfies ρ (c₁.resolvent c₂ v) := by
  by_cases hv : ρ v = some true
  · exact h₂.resolvent_right (by simp [hv])
  · exact h₁.resolvent_left hv

end Satisfies

section Interpolant

variable {n : ℕ}

/-! ### Partial assignments seen from each side -/

/-- The partial assignment fixing the shared variables by `a` and the `A`-private variables by
`y`. -/
private def leftPart (a : Fin n → Bool) (y : Y → Bool) : Fin n ⊕ (Y ⊕ Z) → Option Bool :=
  Sum.elim (some ∘ a) (Sum.elim (some ∘ y) fun _ => none)

/-- The partial assignment fixing the shared variables by `a` and the `B`-private variables by
`z`. -/
private def rightPart (a : Fin n → Bool) (z : Z → Bool) : Fin n ⊕ (Y ⊕ Z) → Option Bool :=
  Sum.elim (some ∘ a) (Sum.elim (fun _ => none) (some ∘ z))

/-- The partial assignment fixing the `A`-private variables by `y` and the shared variables that
`a` sets, leaving those that `a` clears free: it satisfies the positive shared literals true at
`a`, and no negative shared literal. -/
private def leftPos (a : Fin n → Bool) (y : Y → Bool) : Fin n ⊕ (Y ⊕ Z) → Option Bool :=
  Sum.elim (fun i => if a i then some true else none) (Sum.elim (some ∘ y) fun _ => none)

/-- The partial assignment fixing the `B`-private variables by `z` and the shared variables that
`a` clears, leaving those that `a` sets free: it satisfies the negative shared literals true at
`a`, and no positive shared literal. -/
private def rightNeg (a : Fin n → Bool) (z : Z → Bool) : Fin n ⊕ (Y ⊕ Z) → Option Bool :=
  Sum.elim (fun i => if a i then none else some false) (Sum.elim (fun _ => none) (some ∘ z))

/-! ### The invariant -/

/-- The invariant of the interpolant at a line `c` with gate `f`, relative to the partial
assignments `ρA` and `ρB` through which each side sees the line: if `f a = false`, every model
`y` of `A(a, ·)` makes `ρA a y` satisfy `c`; if `f a = true`, every model `z` of `B(a, ·)` makes
`ρB a z` satisfy `c`. -/
private def Good (ρA : (Fin n → Bool) → (Y → Bool) → Fin n ⊕ (Y ⊕ Z) → Option Bool)
    (ρB : (Fin n → Bool) → (Z → Bool) → Fin n ⊕ (Y ⊕ Z) → Option Bool)
    (A : CNF (Fin n ⊕ Y)) (B : CNF (Fin n ⊕ Z)) (c : Clause (Fin n ⊕ (Y ⊕ Z)))
    (f : (Fin n → Bool) → Bool) : Prop :=
  (∀ a y, A.eval (Sum.elim a y) = true → f a = false → Satisfies (ρA a y) c) ∧
    ∀ a z, B.eval (Sum.elim a z) = true → f a = true → Satisfies (ρB a z) c

variable {ρA : (Fin n → Bool) → (Y → Bool) → Fin n ⊕ (Y ⊕ Z) → Option Bool}
  {ρB : (Fin n → Bool) → (Z → Bool) → Fin n ⊕ (Y ⊕ Z) → Option Bool}
  {A : CNF (Fin n ⊕ Y)} {B : CNF (Fin n ⊕ Z)}

/-- At the empty clause the invariant is the interpolation property. -/
private theorem isInterpolant_of_good {f : (Fin n → Bool) → Bool} (h : Good ρA ρB A B [] f) :
    A.IsInterpolant B f := by
  refine ⟨fun a y hA => ?_, fun a z hB => ?_⟩
  · by_contra hf
    exact not_satisfies_nil _ (h.1 a y hA (Bool.eq_false_iff.2 hf))
  · by_contra hf
    exact not_satisfies_nil _ (h.2 a z hB (Bool.eq_true_of_not_eq_false hf))

/-- A clause of `A` gets the constant `false`, if `ρA a y` satisfies every literal of it true at
`(a, y)`. -/
private theorem good_false {d : Clause (Fin n ⊕ Y)} (hd : d ∈ A)
    (hρ : ∀ a y, ∀ l ∈ d, Sum.elim a y l.1 = l.2 → ρA a y (Sum.map id Sum.inl l.1) = some l.2) :
    Good ρA ρB A B (d.relabel (Sum.map id Sum.inl)) fun _ => false := by
  refine ⟨fun a y hA _ => ?_, fun _ _ _ hf => Bool.noConfusion hf⟩
  obtain ⟨l, hl, he⟩ := (Clause.eval_eq_true_iff _ _).1 ((CNF.eval_eq_true_iff _ _).1 hA d hd)
  exact satisfies_relabel hl (hρ a y l hl he)

/-- A clause of `B` gets the constant `true`, if `ρB a z` satisfies every literal of it true at
`(a, z)`. -/
private theorem good_true {d : Clause (Fin n ⊕ Z)} (hd : d ∈ B)
    (hρ : ∀ a z, ∀ l ∈ d, Sum.elim a z l.1 = l.2 → ρB a z (Sum.map id Sum.inr l.1) = some l.2) :
    Good ρA ρB A B (d.relabel (Sum.map id Sum.inr)) fun _ => true := by
  refine ⟨fun _ _ _ hf => Bool.noConfusion hf, fun a z hB _ => ?_⟩
  obtain ⟨l, hl, he⟩ := (Clause.eval_eq_true_iff _ _).1 ((CNF.eval_eq_true_iff _ _).1 hB d hd)
  exact satisfies_relabel hl (hρ a z l hl he)

variable [DecidableEq Y] [DecidableEq Z]

/-- A resolution on an `A`-private variable gets the disjunction of the premises' gates. -/
private theorem good_or (hρB : ∀ a z j, ρB a z (.inr (.inl j)) = none) {c₁ c₂ : Clause _}
    {f₁ f₂ : (Fin n → Bool) → Bool} (j : Y) (h₁ : Good ρA ρB A B c₁ f₁)
    (h₂ : Good ρA ρB A B c₂ f₂) :
    Good ρA ρB A B (c₁.resolvent c₂ (.inr (.inl j))) fun a => f₁ a || f₂ a := by
  refine ⟨fun a y hA hf => ?_, fun a z hB hf => ?_⟩
  · rw [Bool.or_eq_false_iff] at hf
    exact (h₁.1 a y hA hf.1).resolvent (h₂.1 a y hA hf.2)
  · rcases Bool.or_eq_true_iff.1 hf with hf | hf
    · exact (h₁.2 a z hB hf).resolvent_left (by simp [hρB])
    · exact (h₂.2 a z hB hf).resolvent_right (by simp [hρB])

/-- A resolution on a `B`-private variable gets the conjunction of the premises' gates. -/
private theorem good_and (hρA : ∀ a y k, ρA a y (.inr (.inr k)) = none) {c₁ c₂ : Clause _}
    {f₁ f₂ : (Fin n → Bool) → Bool} (k : Z) (h₁ : Good ρA ρB A B c₁ f₁)
    (h₂ : Good ρA ρB A B c₂ f₂) :
    Good ρA ρB A B (c₁.resolvent c₂ (.inr (.inr k))) fun a => f₁ a && f₂ a := by
  refine ⟨fun a y hA hf => ?_, fun a z hB hf => ?_⟩
  · rcases Bool.and_eq_false_iff.1 hf with hf | hf
    · exact (h₁.1 a y hA hf).resolvent_left (by simp [hρA])
    · exact (h₂.1 a y hA hf).resolvent_right (by simp [hρA])
  · rw [Bool.and_eq_true] at hf
    exact (h₁.2 a z hB hf.1).resolvent (h₂.2 a z hB hf.2)

/-- **Assembling the interpolant.** Fix how each side sees the lines (`ρA`, `ρB`), so that clauses
of `A` and of `B` satisfy the invariant with the constants `false` and `true`. If constants,
disjunctions and conjunctions cost at most `cost` gates, and a resolution on a shared variable has
a gate satisfying the invariant within `cost` gates, then a refutation with `s` lines gives an
interpolant computed with at most `cost * s` gates. -/
private theorem exists_circuit_of_good {σ : Signature} {I : Interpretation σ Bool} {cost : ℕ}
    (hρA : ∀ a y k, ρA a y (.inr (.inr k)) = none) (hρB : ∀ a z j, ρB a z (.inr (.inl j)) = none)
    (hA : ∀ d ∈ A, ∀ a y, ∀ l ∈ d, Sum.elim a y l.1 = l.2 →
      ρA a y (Sum.map id Sum.inl l.1) = some l.2)
    (hB : ∀ d ∈ B, ∀ a z, ∀ l ∈ d, Sum.elim a z l.1 = l.2 →
      ρB a z (Sum.map id Sum.inr l.1) = some l.2)
    (hconst : ∀ b, Synthesis I (inputs n) {fun _ => b} cost)
    (hor : ∀ f₁ f₂ : (Fin n → Bool) → Bool,
      Synthesis I (inputs n ∪ {f₁, f₂}) {fun a => f₁ a || f₂ a} cost)
    (hand : ∀ f₁ f₂ : (Fin n → Bool) → Bool,
      Synthesis I (inputs n ∪ {f₁, f₂}) {fun a => f₁ a && f₂ a} cost)
    (hshared : ∀ (i : Fin n) (c₁ c₂ : Clause (Fin n ⊕ (Y ⊕ Z))) (f₁ f₂ : (Fin n → Bool) → Bool),
      Good ρA ρB A B c₁ f₁ → Good ρA ρB A B c₂ f₂ →
        ∃ f, Good ρA ρB A B (c₁.resolvent c₂ (.inl i)) f ∧
          Synthesis I (inputs n ∪ {f₁, f₂}) {f} cost)
    {ls : List (Clause (Fin n ⊕ (Y ⊕ Z)))} (h : (A.appendShared B).IsProof ls) (hnil : [] ∈ ls) :
    ∃ C : Circuit σ n 1, C.size ≤ cost * ls.length ∧
      A.IsInterpolant B fun a => C.eval I a 0 := by
  have hmem (c : Clause (Fin n ⊕ (Y ⊕ Z))) (hc : c ∈ A.appendShared B) :
      ∃ f, Good ρA ρB A B c f ∧ Synthesis I (inputs n) {f} cost := by
    rcases List.mem_append.1 hc with hc | hc <;> obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    exacts [⟨_, good_false hd (hA d hd), hconst false⟩, ⟨_, good_true hd (hB d hd), hconst true⟩]
  have hres (c₁ c₂ : Clause (Fin n ⊕ (Y ⊕ Z))) (v : Fin n ⊕ (Y ⊕ Z))
      (f₁ f₂ : (Fin n → Bool) → Bool) (_ : (v, true) ∈ c₁) (_ : (v, false) ∈ c₂)
      (h₁ : Good ρA ρB A B c₁ f₁) (h₂ : Good ρA ρB A B c₂ f₂) :
      ∃ f, Good ρA ρB A B (c₁.resolvent c₂ v) f ∧
        Synthesis I (inputs n ∪ {f₁, f₂}) {f} cost := by
    rcases v with i | j | k
    exacts [hshared i c₁ c₂ f₁ f₂ h₁ h₂, ⟨_, good_or hρB j h₁ h₂, hor f₁ f₂⟩,
      ⟨_, good_and hρA k h₁ h₂, hand f₁ f₂⟩]
  obtain ⟨f, hf, C, hC, hsize⟩ := IsProof.exists_circuit (Good ρA ρB A B) hmem hres h hnil
  refine ⟨C, hsize, ?_⟩
  have hCf : (fun a => C.eval I a 0) = f := funext fun a => by rw [hC a, single_apply]
  exact hCf ▸ isInterpolant_of_good hf

/-- The two premises' gates are available to the gate of their resolvent. -/
private theorem synthesis_fst {σ : Signature} {I : Interpretation σ Bool}
    (f₁ f₂ : (Fin n → Bool) → Bool) : Synthesis I (inputs n ∪ {f₁, f₂}) {f₁} 0 :=
  Synthesis.of_mem (Or.inr (Or.inl rfl))

/-- The two premises' gates are available to the gate of their resolvent. -/
private theorem synthesis_snd {σ : Signature} {I : Interpretation σ Bool}
    (f₁ f₂ : (Fin n → Bool) → Bool) : Synthesis I (inputs n ∪ {f₁, f₂}) {f₂} 0 :=
  Synthesis.of_mem (Or.inr (Or.inr rfl))

/-- The shared variables are available to the gate of every resolvent. -/
private theorem synthesis_input {σ : Signature} {I : Interpretation σ Bool}
    (f₁ f₂ : (Fin n → Bool) → Bool) (i : Fin n) :
    Synthesis I (inputs n ∪ {f₁, f₂}) {fun a => a i} 0 :=
  Synthesis.of_mem (Or.inl ⟨i, rfl⟩)

/-! ### The general interpolant -/

/-- A resolution on a shared variable `xᵢ` gets the selector `if xᵢ then g₂ else g₁` of the
premises' gates: if `a i = false`, the literal `xᵢ` of `c₁` is false and the gate of `c₁` is
selected; otherwise the literal `¬xᵢ` of `c₂` is false and the gate of `c₂` is. -/
private theorem good_sel {c₁ c₂ : Clause _} {f₁ f₂ : (Fin n → Bool) → Bool} (i : Fin n)
    (h₁ : Good leftPart rightPart A B c₁ f₁) (h₂ : Good leftPart rightPart A B c₂ f₂) :
    Good leftPart rightPart A B (c₁.resolvent c₂ (.inl i))
      fun a => (!a i && f₁ a) || (a i && f₂ a) := by
  refine ⟨fun a y hA hf => ?_, fun a z hB hf => ?_⟩ <;>
    cases hi : a i <;> simp only [hi, Bool.not_false, Bool.not_true, Bool.true_and,
      Bool.false_and, Bool.or_false, Bool.false_or] at hf
  · exact (h₁.1 a y hA hf).resolvent_left (by simp [leftPart, hi])
  · exact (h₂.1 a y hA hf).resolvent_right (by simp [leftPart, hi])
  · exact (h₁.2 a z hB hf).resolvent_left (by simp [rightPart, hi])
  · exact (h₂.2 a z hB hf).resolvent_right (by simp [rightPart, hi])

/-- **Feasible interpolation for resolution** [Pudlák, Theorem 1][Pudlak1997],
[Krajíček, Theorem 6.1][Krajicek1997]. A resolution refutation of `A(x, y) ∧ B(x, z)` with `s`
lines gives an interpolant of `A` and `B` computed by a De Morgan circuit with at most `4 s`
gates. -/
theorem CNF.IsProof.exists_interpolant {ls : List (Clause (Fin n ⊕ (Y ⊕ Z)))}
    (h : (A.appendShared B).IsProof ls) (hnil : [] ∈ ls) :
    ∃ C : Circuit Boolean.signature n 1, C.size ≤ 4 * ls.length ∧
      A.IsInterpolant B fun a => C.eval Boolean.interpretation a 0 := by
  refine exists_circuit_of_good (ρA := leftPart) (ρB := rightPart) (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) (fun _ _ _ _ l _ he => ?_) (fun _ _ _ _ l _ he => ?_)
    (fun b => (Synthesis.const b).mono Set.Subset.rfl Set.Subset.rfl (by omega))
    (fun f₁ f₂ => ((synthesis_fst f₁ f₂).or (synthesis_snd f₁ f₂)).mono Set.Subset.rfl
      Set.Subset.rfl (by omega))
    (fun f₁ f₂ => ((synthesis_fst f₁ f₂).and (synthesis_snd f₁ f₂)).mono Set.Subset.rfl
      Set.Subset.rfl (by omega))
    (fun i _ _ f₁ f₂ h₁ h₂ => ⟨_, good_sel i h₁ h₂,
      (((synthesis_input f₁ f₂ i).not.and (synthesis_fst f₁ f₂)).or
        ((synthesis_input f₁ f₂ i).and (synthesis_snd f₁ f₂))).mono Set.Subset.rfl
        Set.Subset.rfl (by omega)⟩) h hnil
  · rcases l with ⟨_ | _, b⟩ <;> simpa [leftPart] using he
  · rcases l with ⟨_ | _, b⟩ <;> simpa [rightPart] using he

/-- **Feasible interpolation for resolution**, by refutation size: if `A(x, y) ∧ B(x, z)` has a
resolution refutation with at most `s` lines, then `A` and `B` have an interpolant computed by a
De Morgan circuit with at most `4 s` gates. -/
theorem CNF.RefutableInSize.exists_interpolant {s : ℕ} (h : (A.appendShared B).RefutableInSize s) :
    ∃ C : Circuit Boolean.signature n 1, C.size ≤ 4 * s ∧
      A.IsInterpolant B fun a => C.eval Boolean.interpretation a 0 := by
  obtain ⟨ls, h, hnil, hlen⟩ := h
  obtain ⟨C, hsize, hC⟩ := h.exists_interpolant hnil
  exact ⟨C, hsize.trans (Nat.mul_le_mul_left 4 hlen), hC⟩

/-! ### The monotone interpolant -/

/-- Monotone constants cost one gate. -/
private theorem synthesis_monotone_const {s : Set ((Fin n → Bool) → Bool)} (b : Bool) :
    Synthesis Monotone.interpretation s {fun _ => b} 1 :=
  Synthesis.nullary (I := Monotone.interpretation) (.const b) rfl

/-- A monotone conjunction costs one gate beyond its arguments. -/
private theorem synthesis_monotone_and {s : Set ((Fin n → Bool) → Bool)}
    {f g : (Fin n → Bool) → Bool} {a b : ℕ} (hf : Synthesis Monotone.interpretation s {f} a)
    (hg : Synthesis Monotone.interpretation s {g} b) :
    Synthesis Monotone.interpretation s {fun x => f x && g x} (a + b + 1) := by
  simpa [Monotone.interpretation] using hf.binary hg .and

/-- A monotone disjunction costs one gate beyond its arguments. -/
private theorem synthesis_monotone_or {s : Set ((Fin n → Bool) → Bool)}
    {f g : (Fin n → Bool) → Bool} {a b : ℕ} (hf : Synthesis Monotone.interpretation s {f} a)
    (hg : Synthesis Monotone.interpretation s {g} b) :
    Synthesis Monotone.interpretation s {fun x => f x || g x} (a + b + 1) := by
  simpa [Monotone.interpretation] using hf.binary hg .or

/-- When the shared variables occur only positively in `A`, a resolution on a shared variable `xᵢ`
gets the monotone gate `(xᵢ ∨ g₁) ∧ g₂`. It differs from the selector only when `a i = false`,
`g₁ = true` and `g₂ = false`; then the premise `c₂` is seen by `A` without its literal `¬xᵢ`, so
it serves for the resolvent as well. -/
private theorem good_posSel {c₁ c₂ : Clause _} {f₁ f₂ : (Fin n → Bool) → Bool} (i : Fin n)
    (h₁ : Good leftPos rightPart A B c₁ f₁) (h₂ : Good leftPos rightPart A B c₂ f₂) :
    Good leftPos rightPart A B (c₁.resolvent c₂ (.inl i)) fun a => (a i || f₁ a) && f₂ a := by
  refine ⟨fun a y hA hf => ?_, fun a z hB hf => ?_⟩
  · cases hi : a i
    · rcases Bool.and_eq_false_iff.1 hf with hf | hf
      · simp only [hi, Bool.false_or] at hf
        exact (h₁.1 a y hA hf).resolvent_left (by simp [leftPos, hi])
      · exact (h₂.1 a y hA hf).resolvent_right (by simp [leftPos, hi])
    · simp only [hi, Bool.true_or, Bool.true_and] at hf
      exact (h₂.1 a y hA hf).resolvent_right (by simp [leftPos, hi])
  · rw [Bool.and_eq_true] at hf
    cases hi : a i
    · simp only [hi, Bool.false_or] at hf
      exact (h₁.2 a z hB hf.1).resolvent_left (by simp [rightPart, hi])
    · exact (h₂.2 a z hB hf.2).resolvent_right (by simp [rightPart, hi])

/-- When the shared variables occur only negatively in `B`, a resolution on a shared variable `xᵢ`
gets the monotone gate `(xᵢ ∧ g₂) ∨ g₁`. It differs from the selector only when `a i = true`,
`g₁ = true` and `g₂ = false`; then the premise `c₁` is seen by `B` without its literal `xᵢ`, so
it serves for the resolvent as well. -/
private theorem good_negSel {c₁ c₂ : Clause _} {f₁ f₂ : (Fin n → Bool) → Bool} (i : Fin n)
    (h₁ : Good leftPart rightNeg A B c₁ f₁) (h₂ : Good leftPart rightNeg A B c₂ f₂) :
    Good leftPart rightNeg A B (c₁.resolvent c₂ (.inl i)) fun a => (a i && f₂ a) || f₁ a := by
  refine ⟨fun a y hA hf => ?_, fun a z hB hf => ?_⟩
  · rw [Bool.or_eq_false_iff] at hf
    cases hi : a i
    · exact (h₁.1 a y hA hf.2).resolvent_left (by simp [leftPart, hi])
    · simp only [hi, Bool.true_and] at hf
      exact (h₂.1 a y hA hf.1).resolvent_right (by simp [leftPart, hi])
  · cases hi : a i
    · simp only [hi, Bool.false_and, Bool.false_or] at hf
      exact (h₁.2 a z hB hf).resolvent_left (by simp [rightNeg, hi])
    · rcases Bool.or_eq_true_iff.1 hf with hf | hf
      · simp only [hi, Bool.true_and] at hf
        exact (h₂.2 a z hB hf).resolvent_right (by simp [rightNeg, hi])
      · exact (h₁.2 a z hB hf).resolvent_left (by simp [rightNeg, hi])

/-- The monotone basis supplies constants, disjunctions and conjunctions within two gates. -/
private theorem monotone_gates :
    (∀ b, Synthesis Monotone.interpretation (inputs n) {fun _ => b} 2) ∧
    (∀ f₁ f₂ : (Fin n → Bool) → Bool,
      Synthesis Monotone.interpretation (inputs n ∪ {f₁, f₂}) {fun a => f₁ a || f₂ a} 2) ∧
    ∀ f₁ f₂ : (Fin n → Bool) → Bool,
      Synthesis Monotone.interpretation (inputs n ∪ {f₁, f₂}) {fun a => f₁ a && f₂ a} 2 :=
  ⟨fun b => (synthesis_monotone_const b).mono Set.Subset.rfl Set.Subset.rfl (by omega),
    fun f₁ f₂ => (synthesis_monotone_or (synthesis_fst f₁ f₂) (synthesis_snd f₁ f₂)).mono
      Set.Subset.rfl Set.Subset.rfl (by omega),
    fun f₁ f₂ => (synthesis_monotone_and (synthesis_fst f₁ f₂) (synthesis_snd f₁ f₂)).mono
      Set.Subset.rfl Set.Subset.rfl (by omega)⟩

/-- **Monotone feasible interpolation for resolution**, when the shared variables occur only
positively in `A` [Pudlák, Theorem 2][Pudlak1997], [Krajíček, Theorem 6.1][Krajicek1997]. A
resolution refutation of `A(x, y) ∧ B(x, z)` with `s` lines gives an interpolant of `A` and `B`
computed by a monotone circuit with at most `2 s` gates. -/
theorem CNF.IsProof.exists_monotone_interpolant_of_positive
    {ls : List (Clause (Fin n ⊕ (Y ⊕ Z)))} (h : (A.appendShared B).IsProof ls) (hnil : [] ∈ ls)
    (hpos : ∀ d ∈ A, ∀ i b, (.inl i, b) ∈ d → b = true) :
    ∃ C : Circuit Monotone.signature n 1, C.size ≤ 2 * ls.length ∧
      A.IsInterpolant B fun a => C.eval Monotone.interpretation a 0 := by
  obtain ⟨hconst, hor, hand⟩ := monotone_gates (n := n)
  refine exists_circuit_of_good (ρA := leftPos) (ρB := rightPart) (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) (fun d hd a _ l hl he => ?_) (fun _ _ _ _ l _ he => ?_) hconst hor hand
    (fun i _ _ f₁ f₂ h₁ h₂ => ⟨_, good_posSel i h₁ h₂,
      (synthesis_monotone_and (synthesis_monotone_or (synthesis_input f₁ f₂ i)
        (synthesis_fst f₁ f₂)) (synthesis_snd f₁ f₂)).mono Set.Subset.rfl Set.Subset.rfl
        (by omega)⟩) h hnil
  · rcases l with ⟨i | _, b⟩
    · obtain rfl := hpos d hd i b hl
      simp only [Sum.elim_inl] at he
      simp [leftPos, he]
    · simpa [leftPos] using he
  · rcases l with ⟨_ | _, b⟩ <;> simpa [rightPart] using he

/-- **Monotone feasible interpolation for resolution**, when the shared variables occur only
negatively in `B` [Pudlák, Theorem 2][Pudlak1997], [Krajíček, Theorem 6.1][Krajicek1997]. A
resolution refutation of `A(x, y) ∧ B(x, z)` with `s` lines gives an interpolant of `A` and `B`
computed by a monotone circuit with at most `2 s` gates. -/
theorem CNF.IsProof.exists_monotone_interpolant_of_negative
    {ls : List (Clause (Fin n ⊕ (Y ⊕ Z)))} (h : (A.appendShared B).IsProof ls) (hnil : [] ∈ ls)
    (hneg : ∀ d ∈ B, ∀ i b, (.inl i, b) ∈ d → b = false) :
    ∃ C : Circuit Monotone.signature n 1, C.size ≤ 2 * ls.length ∧
      A.IsInterpolant B fun a => C.eval Monotone.interpretation a 0 := by
  obtain ⟨hconst, hor, hand⟩ := monotone_gates (n := n)
  refine exists_circuit_of_good (ρA := leftPart) (ρB := rightNeg) (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) (fun _ _ _ _ l _ he => ?_) (fun d hd a _ l hl he => ?_) hconst hor hand
    (fun i _ _ f₁ f₂ h₁ h₂ => ⟨_, good_negSel i h₁ h₂,
      (synthesis_monotone_or (synthesis_monotone_and (synthesis_input f₁ f₂ i)
        (synthesis_snd f₁ f₂)) (synthesis_fst f₁ f₂)).mono Set.Subset.rfl Set.Subset.rfl
        (by omega)⟩) h hnil
  · rcases l with ⟨_ | _, b⟩ <;> simpa [leftPart] using he
  · rcases l with ⟨i | _, b⟩
    · obtain rfl := hneg d hd i b hl
      simp only [Sum.elim_inl] at he
      simp [rightNeg, he]
    · simpa [rightNeg] using he

/-- **Monotone feasible interpolation for resolution**, by refutation size, when the shared
variables occur only positively in `A`. -/
theorem CNF.RefutableInSize.exists_monotone_interpolant_of_positive {s : ℕ}
    (h : (A.appendShared B).RefutableInSize s) (hpos : ∀ d ∈ A, ∀ i b, (.inl i, b) ∈ d → b = true) :
    ∃ C : Circuit Monotone.signature n 1, C.size ≤ 2 * s ∧
      A.IsInterpolant B fun a => C.eval Monotone.interpretation a 0 := by
  obtain ⟨ls, h, hnil, hlen⟩ := h
  obtain ⟨C, hsize, hC⟩ := h.exists_monotone_interpolant_of_positive hnil hpos
  exact ⟨C, hsize.trans (Nat.mul_le_mul_left 2 hlen), hC⟩

/-- **Monotone feasible interpolation for resolution**, by refutation size, when the shared
variables occur only negatively in `B`. -/
theorem CNF.RefutableInSize.exists_monotone_interpolant_of_negative {s : ℕ}
    (h : (A.appendShared B).RefutableInSize s)
    (hneg : ∀ d ∈ B, ∀ i b, (.inl i, b) ∈ d → b = false) :
    ∃ C : Circuit Monotone.signature n 1, C.size ≤ 2 * s ∧
      A.IsInterpolant B fun a => C.eval Monotone.interpretation a 0 := by
  obtain ⟨ls, h, hnil, hlen⟩ := h
  obtain ⟨C, hsize, hC⟩ := h.exists_monotone_interpolant_of_negative hnil hneg
  exact ⟨C, hsize.trans (Nat.mul_le_mul_left 2 hlen), hC⟩

end Interpolant

end Cslib.Logic.PL
