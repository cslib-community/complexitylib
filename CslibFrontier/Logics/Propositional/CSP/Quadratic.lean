/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Ring.BooleanRing

/-!
# Quadratic equations over `𝔽₂`

A quadratic equation $\sum_{i,j} a_{ij} u_i u_j = b$ over `𝔽₂` in 0/1 variables is stored
sparsely, as the list of the monomials `(i, j)` with $a_{ij} = 1$, and its right-hand side.
Evaluation sums the products in the existing Boolean ring, so a repeated monomial cancels in
pairs, as repeated variables of `Cslib.Logic.PL.AffineEquation` do. Since `u * u = u` on 0/1
values, the diagonal monomials `(i, i)` are the linear terms.

The second half gives the gadget behind the `NP`-hardness of QUADEQ
[Arora and Barak, draft, Exercise 2§18][AroraBarak07]. A clause $\ell_0 \lor \dots \lor \ell_{k-1}$
with index `i` gets auxiliary variables $z_{i,0},\dots,z_{i,k}$ and the equations

$$z_{i,0} = 1,\qquad z_{i,t+1} = z_{i,t}\cdot\lnot\ell_t\ (t < k),\qquad z_{i,k} = 0,$$

each quadratic because $\lnot\ell_t$ is affine in the variable of $\ell_t$. The middle equations
force $z_{i,t}$ to say that the first `t` literals are false, so the system is satisfiable exactly
when the formula is (`CNF.satisfiable_toQuadSystem`).

## Main definitions

* `Cslib.Logic.PL.QuadEquation`: a quadratic equation, with repeated monomials allowed.
* `Cslib.Logic.PL.QuadEquation.Holds`, `Cslib.Logic.PL.QuadSystem.Holds`,
  `Cslib.Logic.PL.QuadSystem.Satisfiable`: semantics.
* `Cslib.Logic.PL.QuadEquation.vars`: the variables in order of occurrence.
* `Cslib.Logic.PL.QuadEquation.relabel`: rename the variables.
* `Cslib.Logic.PL.CNF.toQuadSystem`: the quadratic system of a formula.

## Main results

* `Cslib.Logic.PL.QuadSystem.holds_congr`: satisfaction depends only on the occurring
  variables.
* `Cslib.Logic.PL.QuadSystem.satisfiable_relabel`: injective relabelling preserves
  satisfiability.
* `Cslib.Logic.PL.CNF.satisfiable_toQuadSystem`: a formula is satisfiable exactly when its
  quadratic system is.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, draft][AroraBarak07]
-/

public section

namespace Cslib.Logic.PL

variable {V W : Type*}

-- The derived equality decision is exposed so that module clients can `decide` equations.
@[expose] public section

/-- A quadratic equation $\sum_{i,j} a_{ij} u_i u_j = b$ over `𝔽₂`: the monomials `(i, j)` with
$a_{ij} = 1$, and the right-hand side `b`. -/
structure QuadEquation (V : Type*) where
  /-- The monomials summed, with repetitions; repeated monomials cancel in pairs. -/
  terms : List (V × V)
  /-- The right-hand side of the equation. -/
  rhs : Bool
deriving DecidableEq, Repr

end

/-- A finite conjunction of quadratic equations over `𝔽₂`. -/
abbrev QuadSystem (V : Type*) := List (QuadEquation V)

namespace QuadEquation

/-- The sum of the monomials under the 0/1 assignment `a` equals the right-hand side in the
Boolean ring. -/
@[expose] def Holds (e : QuadEquation V) (a : V → Bool) : Prop :=
  (e.terms.map fun p => a p.1 * a p.2).sum = e.rhs

/-- The variables of an equation, in order of occurrence, with repetitions. -/
@[expose] def vars (e : QuadEquation V) : List V := e.terms.flatMap fun p => [p.1, p.2]

/-- Rename the variables of an equation. -/
@[expose] def relabel (f : V → W) (e : QuadEquation V) : QuadEquation W :=
  ⟨e.terms.map (Prod.map f f), e.rhs⟩

/-- The variables of an equation are the components of its monomials. -/
theorem mem_vars {e : QuadEquation V} {v : V} :
    v ∈ e.vars ↔ ∃ p ∈ e.terms, v = p.1 ∨ v = p.2 := by
  simp [vars]

/-- Satisfaction depends only on the variables of the equation. -/
theorem holds_congr {e : QuadEquation V} {a b : V → Bool} (h : ∀ v ∈ e.vars, a v = b v) :
    e.Holds a ↔ e.Holds b := by
  have hmap : (e.terms.map fun p => a p.1 * a p.2) = e.terms.map fun p => b p.1 * b p.2 :=
    List.map_congr_left fun p hp => by
      rw [h p.1 (mem_vars.2 ⟨p, hp, .inl rfl⟩), h p.2 (mem_vars.2 ⟨p, hp, .inr rfl⟩)]
  rw [Holds, Holds, hmap]

/-- A relabelled equation holds exactly when the original holds under the composed
assignment. -/
@[simp] theorem holds_relabel (f : V → W) (e : QuadEquation V) (a : W → Bool) :
    (e.relabel f).Holds a ↔ e.Holds (a ∘ f) := by
  simp only [Holds, relabel, List.map_map]
  rfl

end QuadEquation

namespace QuadSystem

/-- Every equation of the system holds. -/
@[expose] def Holds (F : QuadSystem V) (a : V → Bool) : Prop := ∀ e ∈ F, e.Holds a

/-- Some 0/1 assignment satisfies every equation of the system. -/
@[expose] def Satisfiable (F : QuadSystem V) : Prop := ∃ a : V → Bool, F.Holds a

/-- The variables of a system, in order of occurrence, with repetitions. -/
@[expose] def vars (F : QuadSystem V) : List V := F.flatMap QuadEquation.vars

/-- Rename the variables of every equation. -/
@[expose] def relabel (f : V → W) (F : QuadSystem V) : QuadSystem W := F.map (.relabel f)

/-- Satisfaction of a system depends only on its variables. -/
theorem holds_congr {F : QuadSystem V} {a b : V → Bool} (h : ∀ v ∈ F.vars, a v = b v) :
    F.Holds a ↔ F.Holds b :=
  forall₂_congr fun e he =>
    QuadEquation.holds_congr fun v hv => h v (List.mem_flatMap.2 ⟨e, he, hv⟩)

/-- A relabelled system holds exactly when the original holds under the composed assignment. -/
theorem holds_relabel (f : V → W) (F : QuadSystem V) (a : W → Bool) :
    (F.relabel f).Holds a ↔ F.Holds (a ∘ f) := by
  simp [Holds, relabel]

/-- **Injective relabelling preserves satisfiability.** -/
theorem satisfiable_relabel {f : V → W} (hf : Function.Injective f) (F : QuadSystem V) :
    (F.relabel f).Satisfiable ↔ F.Satisfiable := by
  refine ⟨fun ⟨a, ha⟩ => ⟨a ∘ f, (holds_relabel f F a).1 ha⟩, fun ⟨a, ha⟩ => ?_⟩
  refine ⟨Function.extend f a fun _ => false, (holds_relabel f F _).2 ?_⟩
  rwa [show (Function.extend f a fun _ => false) ∘ f = a from
    funext fun v => hf.extend_apply a _ v]

end QuadSystem

/-! ### Quadratic equations of a formula -/

namespace CNF

/-- The auxiliary variable $z_{i,t}$: the first `t` literals of clause `i` are false. -/
abbrev auxVar (i t : ℕ) : V ⊕ ℕ × ℕ := .inr (i, t)

/-- The equation $z_{i,t} = c$, written as the monomial $z_{i,t} z_{i,t}$. -/
@[expose] def auxEq (i t : ℕ) (c : Bool) : QuadEquation (V ⊕ ℕ × ℕ) :=
  ⟨[(auxVar i t, auxVar i t)], c⟩

/-- The equation $z_{i,t+1} = z_{i,t}\cdot\lnot\ell$ for the literal $\ell = (v, b)$. Since
$\lnot\ell = u_v + b$, it reads $z_{i,t+1} + z_{i,t} u_v + b\, z_{i,t} z_{i,t} = 0$. -/
@[expose] def stepEq (i t : ℕ) (l : Literal V) : QuadEquation (V ⊕ ℕ × ℕ) :=
  ⟨(auxVar i (t + 1), auxVar i (t + 1)) :: (auxVar i t, .inl l.1) ::
    if l.2 then [(auxVar i t, auxVar i t)] else [], false⟩

/-- The equations of the clause `c` with index `i`: $z_{i,0} = 1$, $z_{i,k} = 0$ for its length
`k`, and $z_{i,t+1} = z_{i,t}\cdot\lnot\ell_t$ for each literal $\ell_t$. -/
@[expose] def clauseQuadSystem (i : ℕ) (c : Clause V) : QuadSystem (V ⊕ ℕ × ℕ) :=
  auxEq i 0 true :: auxEq i c.length false :: c.zipIdx.map fun p => stepEq i p.2 p.1

/-- **The quadratic system of a formula**: the equations of its clauses, the variable `v` of the
formula kept as `inl v`, and the auxiliary variables numbered by clause and position. -/
@[expose] def toQuadSystem (φ : CNF V) : QuadSystem (V ⊕ ℕ × ℕ) :=
  φ.zipIdx.flatMap fun p => clauseQuadSystem p.2 p.1

/-- The equation $z_{i,t}\,z_{i,t} = c$ says $z_{i,t} = c$. -/
@[simp] theorem holds_auxEq (i t : ℕ) (c : Bool) (a : V ⊕ ℕ × ℕ → Bool) :
    (auxEq i t c).Holds a ↔ a (auxVar i t) = c := by
  simp only [auxEq, QuadEquation.Holds, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero]
  cases a (auxVar i t) <;> exact Iff.rfl

/-- The step equation says $z_{i,t+1} = z_{i,t}\cdot\lnot\ell$. -/
theorem holds_stepEq (i t : ℕ) (l : Literal V) (a : V ⊕ ℕ × ℕ → Bool) :
    (stepEq i t l).Holds a ↔
      a (auxVar i (t + 1)) = (a (auxVar i t) && !Literal.eval (a ∘ Sum.inl) l) := by
  obtain ⟨v, b⟩ := l
  cases b <;>
    simp only [stepEq, QuadEquation.Holds, Literal.eval, Function.comp_apply, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, Bool.false_eq_true, ↓reduceIte] <;>
    generalize a (auxVar i (t + 1)) = x <;> generalize a (auxVar i t) = y <;>
    generalize a (Sum.inl v) = u <;> revert x y u <;> decide

/-- The chain $z_0 = 1$, $z_{t+1} = z_t\cdot\lnot\ell_t$ computes whether the first `t` literals
are all false. -/
private theorem chain_eq {σ : V → Bool} {c : Clause V} {z : ℕ → Bool} (h0 : z 0 = true)
    (hstep : ∀ t (h : t < c.length), z (t + 1) = (z t && !Literal.eval σ c[t])) :
    ∀ t ≤ c.length, z t = !Clause.eval σ (c.take t) := by
  intro t ht
  induction t with
  | zero => simpa using h0
  | succ t ih =>
    rw [hstep t (by omega), ih (by omega), List.take_add_one, List.getElem?_eq_getElem (by omega)]
    simp only [Clause.eval, Option.toList_some, List.any_append, List.any_cons, List.any_nil,
      Bool.or_false, Bool.not_or]

/-- The equations of a clause force it to hold under the assignment of the formula variables. -/
theorem eval_of_holds_clauseQuadSystem {i : ℕ} {c : Clause V} {a : V ⊕ ℕ × ℕ → Bool}
    (h : (clauseQuadSystem i c).Holds a) : Clause.eval (a ∘ Sum.inl) c = true := by
  have hmem (e) (he : e ∈ c.zipIdx.map fun p => stepEq i p.2 p.1) : e.Holds a :=
    h e (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
  have hchain := chain_eq (σ := a ∘ Sum.inl) (z := fun t => a (auxVar i t))
    ((holds_auxEq ..).1 (h _ List.mem_cons_self)) (fun t ht => (holds_stepEq ..).1 <|
      hmem _ (List.mem_map.2 ⟨(c[t], t), List.mem_zipIdx_iff_getElem?.2 (by simp [ht]), rfl⟩))
    c.length c.length.le_refl
  have hend := (holds_auxEq ..).1 (h _ (List.mem_cons_of_mem _ List.mem_cons_self))
  rw [List.take_length] at hchain
  simpa [hend] using hchain.symm

/-- If the auxiliary variables of a clause record its literal prefixes and the clause holds, then
its equations hold. -/
theorem holds_clauseQuadSystem {i : ℕ} {c : Clause V} {a : V ⊕ ℕ × ℕ → Bool}
    (haux : ∀ t, a (auxVar i t) = !Clause.eval (a ∘ Sum.inl) (c.take t))
    (hc : Clause.eval (a ∘ Sum.inl) c = true) : (clauseQuadSystem i c).Holds a := by
  intro e he
  simp only [clauseQuadSystem, List.mem_cons, List.mem_map] at he
  rcases he with rfl | rfl | ⟨⟨l, t⟩, hp, rfl⟩
  · simp [haux, Clause.eval]
  · simp [haux, hc]
  · have ht : c[t]? = some l := List.mem_zipIdx_iff_getElem?.1 hp
    have hlt : t < c.length := (List.getElem?_eq_some_iff.1 ht).1
    rw [holds_stepEq, haux, haux, List.take_add_one, ht]
    simp [Clause.eval]

/-- **A formula is satisfiable exactly when its quadratic system is.** -/
theorem satisfiable_toQuadSystem (φ : CNF V) : (toQuadSystem φ).Satisfiable ↔ φ.Satisfiable := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a ∘ Sum.inl, (CNF.eval_eq_true_iff _ _).2 fun c hc => ?_⟩
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hc
    exact eval_of_holds_clauseQuadSystem fun e he => ha e <| List.mem_flatMap.2
      ⟨(c, i), List.mem_zipIdx_iff_getElem?.2 hi, he⟩
  · rintro ⟨σ, hσ⟩
    let a : V ⊕ ℕ × ℕ → Bool :=
      Sum.elim σ fun p => !Clause.eval σ ((φ.getD p.1 []).take p.2)
    refine ⟨a, fun e he => ?_⟩
    obtain ⟨⟨c, i⟩, hp, he⟩ := List.mem_flatMap.1 he
    have hi : φ[i]? = some c := List.mem_zipIdx_iff_getElem?.1 hp
    have hc : Clause.eval (a ∘ Sum.inl) c = true :=
      (CNF.eval_eq_true_iff σ φ).1 hσ c (List.mem_of_getElem? hi)
    exact holds_clauseQuadSystem (a := a) (fun t => by simp [a, hi]) hc e he

end CNF

end Cslib.Logic.PL
