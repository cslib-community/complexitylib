/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.SemiCircuit.Equation
public import Mathlib.Data.Finset.Sum
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Ring

/-!
# Fair semi-circuits over the full binary basis

Following [Mishra and Santhanam, Section 2.3][MishraSanthanam2026], a *fair semi-circuit* is an
affine system of equations over `𝔽₂` followed by an acyclic circuit over the full binary basis
`B₂`. Its internal values are *parameters*, *auxiliary variables* and *gates*, all named by
natural numbers. The affine system consists of equations `∑ terms = rhs` in the parameters and
auxiliary variables, each with at most three terms; it is *fair* when every assignment to the
parameters extends to exactly one assignment of the auxiliary variables satisfying all equations
(`SemiCircuit.WellFormed.solvable`, `SemiCircuit.WellFormed.unique`), which is equivalent to the
invertibility of the auxiliary matrix of the source. Each gate applies an arbitrary operation
`Bool → Bool → Bool` to two arguments, each a constant or an internal value with a smaller name,
so the order of names is a topological order. The output is a literal.

Equations are named separately from internal values. A *child* of an internal value `t` is a gate
reading `t` or an equation containing `t` (`SemiCircuit.children`); a gate reading `t` twice is a
single child. The *degree* of `t` is its number of children (`SemiCircuit.deg`).

Rerouting replaces every occurrence of an internal value `v` by a literal
(`SemiCircuit.subst`), absorbing negations into the operations of gates and the right-hand sides
of equations. It preserves the value of every gate and the truth of every equation on assignments
giving `v` the value of the literal (`Gate.eval_subst`, `Equation.holds_subst`), and it changes no
child of any value other than `v` and the target of the literal (`SemiCircuit.children_subst`).

A gate with a constant argument or two equal arguments is *degenerate* and computes a constant or
a literal of an argument (`Gate.eval_lit`). Of the sixteen operations of `B₂`, the *affine* ones
(`IsAffineOp`) have no product term; every other operation has the form `(a + α)(b + β) + γ`
(`exists_and_form`). An affine gate whose arguments are parameters or auxiliary variables can be
moved into the affine system as an equation (`affEqn_holds`).

## Main definitions

* `Cslib.Circuits.Boolean.SemiCircuit`: semi-circuits, with `SemiCircuit.Consistent`
  assignments, `SemiCircuit.WellFormed`, `SemiCircuit.children`, `SemiCircuit.deg` and
  `SemiCircuit.size` (building on `SemiCircuit.Lit`, `SemiCircuit.Gate` and
  `SemiCircuit.IsAffineOp` in `Complexity/Computability/Circuit/Boolean/SemiCircuit/Gate.lean`, and
  `SemiCircuit.Equation` in
  `Complexity/Computability/Circuit/Boolean/SemiCircuit/Equation.lean`).
* `Cslib.Circuits.Boolean.SemiCircuit.subst`: rerouting an internal value to a literal.
* `Cslib.Circuits.Boolean.SemiCircuit.AffineIn`,
  `Cslib.Circuits.Boolean.SemiCircuit.LiftsTo`: affine dependence on the parameters and lifting
  consistent assignments.

## Main results

* `Cslib.Circuits.Boolean.SemiCircuit.consistent_subst`,
  `Cslib.Circuits.Boolean.SemiCircuit.consistent_of_subst`: rerouting preserves consistency.
* `Cslib.Circuits.Boolean.SemiCircuit.children_subst`: rerouting changes no other children.
* `Cslib.Circuits.Boolean.SemiCircuit.WellFormed.exists_affineIn`: on the solutions of the affine
  system, every auxiliary variable is an affine function of the parameters.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
* [M. G. Find, A. Golovnev, E. A. Hirsch and A. S. Kulikov, *A better-than-3n lower bound for the
  circuit complexity of an explicit function*][FindGolovnevHirschKulikov2016]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Finset SemiCircuit

/-! ### Semi-circuits -/

/-- A semi-circuit: parameters, auxiliary variables and gates named by natural numbers, the gates
and the equations of the affine system, and an output literal. Only the gates in `gates` and the
equations in `eqns` belong to the semi-circuit; `gate` and `eqn` are arbitrary elsewhere. -/
structure SemiCircuit where
  /-- The parameters. -/
  params : Finset ℕ
  /-- The auxiliary variables of the affine system. -/
  aux : Finset ℕ
  /-- The gates of the acyclic part. -/
  gates : Finset ℕ
  /-- The gate with each name. -/
  gate : ℕ → SemiCircuit.Gate
  /-- The names of the equations of the affine system. -/
  eqns : Finset ℕ
  /-- The equation with each name. -/
  eqn : ℕ → SemiCircuit.Equation
  /-- The output. -/
  out : SemiCircuit.Lit

namespace SemiCircuit

variable (C : SemiCircuit)

/-- The internal values: parameters, auxiliary variables and gates. -/
def live : Finset ℕ :=
  C.params ∪ C.aux ∪ C.gates

/-- All equations of the affine system hold. -/
def EqnsHold (val : ℕ → Bool) : Prop :=
  ∀ e ∈ C.eqns, (C.eqn e).Holds val

/-- Every gate has the value of its operation on its arguments. -/
def GatesHold (val : ℕ → Bool) : Prop :=
  ∀ J ∈ C.gates, val J = (C.gate J).eval val

/-- A consistent assignment of the internal values satisfies every equation and every gate. -/
def Consistent (val : ℕ → Bool) : Prop :=
  C.EqnsHold val ∧ C.GatesHold val

/-- The size: the number of gates plus the number of equations. -/
def size : ℕ :=
  C.gates.card + C.eqns.card

/-- The gates reading `t`. -/
def gateChildren (t : ℕ) : Finset ℕ :=
  C.gates.filter fun J => (C.gate J).Reads t

/-- The equations containing `t`. -/
def eqnChildren (t : ℕ) : Finset ℕ :=
  C.eqns.filter fun e => t ∈ (C.eqn e).terms

/-- The children of `t`: the gates reading it (on the left) and the equations containing it (on
the right). -/
def children (t : ℕ) : Finset (ℕ ⊕ ℕ) :=
  (C.gateChildren t).disjSum (C.eqnChildren t)

/-- The degree of `t`: its number of children. -/
def deg (t : ℕ) : ℕ :=
  (C.children t).card

theorem deg_eq (t : ℕ) : C.deg t = (C.gateChildren t).card + (C.eqnChildren t).card :=
  Finset.card_disjSum _ _

@[simp] theorem inl_mem_children {t J : ℕ} :
    Sum.inl J ∈ C.children t ↔ J ∈ C.gates ∧ (C.gate J).Reads t := by
  simp [children, gateChildren]

@[simp] theorem inr_mem_children {t e : ℕ} :
    Sum.inr e ∈ C.children t ↔ e ∈ C.eqns ∧ t ∈ (C.eqn e).terms := by
  simp [children, eqnChildren]

/-- A semi-circuit is well formed when its roles are disjoint, gates read constants or internal
values (gates only with smaller names), equations have at most three terms among the parameters
and auxiliary variables, the output reads a constant or an internal value, and the affine system
is fair: every assignment of the parameters extends to a solution, whose auxiliary values are
unique. -/
structure WellFormed : Prop where
  /-- Parameters and auxiliary variables are distinct. -/
  disjoint_params_aux : Disjoint C.params C.aux
  /-- Parameters and gates are distinct. -/
  disjoint_params_gates : Disjoint C.params C.gates
  /-- Auxiliary variables and gates are distinct. -/
  disjoint_aux_gates : Disjoint C.aux C.gates
  /-- A gate reads only gates with smaller names. -/
  reads_lt : ∀ J ∈ C.gates, ∀ i ∈ C.gates, (C.gate J).Reads i → i < J
  /-- A gate reads only constants and internal values. -/
  reads_live : ∀ J ∈ C.gates, ∀ i, (C.gate J).Reads i → i ∈ C.live
  /-- Equations contain only parameters and auxiliary variables. -/
  terms_subset : ∀ e ∈ C.eqns, (C.eqn e).terms ⊆ C.params ∪ C.aux
  /-- Every equation has at most three terms. -/
  card_terms_le : ∀ e ∈ C.eqns, (C.eqn e).terms.card ≤ 3
  /-- The output reads a constant or an internal value. -/
  out_live : ∀ i, C.out.arg = .node i → i ∈ C.live
  /-- Every assignment of the parameters extends to a solution of the affine system. -/
  solvable : ∀ u : ℕ → Bool, ∃ val, (∀ j ∈ C.params, val j = u j) ∧ C.EqnsHold val
  /-- The solution determines the auxiliary variables (fairness). -/
  unique : ∀ val val' : ℕ → Bool, (∀ j ∈ C.params, val j = val' j) → C.EqnsHold val →
    C.EqnsHold val' → ∀ v ∈ C.aux, val v = val' v

namespace WellFormed

variable {C} (hC : C.WellFormed) {i : ℕ}
include hC

theorem notMem_gates_of_mem_params (hi : i ∈ C.params) : i ∉ C.gates :=
  Finset.disjoint_left.1 hC.disjoint_params_gates hi

theorem notMem_aux_of_mem_params (hi : i ∈ C.params) : i ∉ C.aux :=
  Finset.disjoint_left.1 hC.disjoint_params_aux hi

theorem notMem_params_of_mem_gates (hi : i ∈ C.gates) : i ∉ C.params :=
  Finset.disjoint_right.1 hC.disjoint_params_gates hi

theorem notMem_aux_of_mem_gates (hi : i ∈ C.gates) : i ∉ C.aux :=
  Finset.disjoint_right.1 hC.disjoint_aux_gates hi

theorem notMem_params_of_mem_aux (hi : i ∈ C.aux) : i ∉ C.params :=
  Finset.disjoint_right.1 hC.disjoint_params_aux hi

theorem notMem_gates_of_mem_aux (hi : i ∈ C.aux) : i ∉ C.gates :=
  Finset.disjoint_left.1 hC.disjoint_aux_gates hi

/-- Gates do not occur in equations. -/
theorem notMem_terms_of_mem_gates {e : ℕ} (hi : i ∈ C.gates) (he : e ∈ C.eqns) :
    i ∉ (C.eqn e).terms := fun hie => by
  rcases Finset.mem_union.1 (hC.terms_subset e he hie) with h | h
  · exact hC.notMem_params_of_mem_gates hi h
  · exact hC.notMem_aux_of_mem_gates hi h

/-- A gate does not read itself. -/
theorem not_reads_self (hi : i ∈ C.gates) : ¬ (C.gate i).Reads i := fun h =>
  lt_irrefl i (hC.reads_lt i hi i hi h)

end WellFormed

/-! ### Rerouting -/

/-- Reroute the internal value `v` to the literal `ℓ` in every gate, equation and the output. -/
def subst (v : ℕ) (ℓ : Lit) : SemiCircuit where
  params := C.params
  aux := C.aux
  gates := C.gates
  gate J := (C.gate J).subst v ℓ
  eqns := C.eqns
  eqn e := (C.eqn e).subst v ℓ
  out := C.out.subst v ℓ

variable {C}

private theorem eqnsHold_subst {v : ℕ} {ℓ : Lit} {val : ℕ → Bool} (h : val v = ℓ.eval val) :
    (C.subst v ℓ).EqnsHold val ↔ C.EqnsHold val := by
  unfold EqnsHold
  simp only [subst, Equation.holds_subst h]

private theorem gatesHold_subst {v : ℕ} {ℓ : Lit} {val : ℕ → Bool} (h : val v = ℓ.eval val) :
    (C.subst v ℓ).GatesHold val ↔ C.GatesHold val := by
  unfold GatesHold
  simp only [subst, Gate.eval_subst h]

theorem consistent_subst {v : ℕ} {ℓ : Lit} {val : ℕ → Bool} (h : val v = ℓ.eval val) :
    (C.subst v ℓ).Consistent val ↔ C.Consistent val := by
  unfold Consistent
  rw [eqnsHold_subst h, gatesHold_subst h]

/-- Rerouting `v` changes no child of any internal value other than `v` and the target of the
literal. -/
theorem children_subst {v : ℕ} {ℓ : Lit} {z : ℕ} (hzv : z ≠ v) (hzℓ : ℓ.arg ≠ .node z) :
    (C.subst v ℓ).children z = C.children z := by
  ext (J | e)
  · simp only [inl_mem_children]
    exact and_congr_right fun _ => Gate.reads_subst_of_ne hzv hzℓ
  · simp only [inr_mem_children]
    exact and_congr_right fun _ => Equation.mem_subst_of_ne hzv hzℓ

/-- After rerouting `v` to `t`, the children of `t` are among the former children of `t` and
`v`. -/
theorem children_subst_subset (v : ℕ) (ℓ : Lit) (z : ℕ) :
    (C.subst v ℓ).children z ⊆ C.children z ∪ C.children v := by
  intro x hx
  rw [Finset.mem_union]
  rcases x with J | e
  · simp only [inl_mem_children] at hx ⊢
    rcases Gate.reads_of_reads_subst hx.2 with h | ⟨h, _⟩
    · exact Or.inl ⟨hx.1, h⟩
    · exact Or.inr ⟨hx.1, h⟩
  · simp only [inr_mem_children] at hx ⊢
    rcases Equation.mem_of_mem_subst hx.2 with h | ⟨h, _⟩
    · exact Or.inl ⟨hx.1, h⟩
    · exact Or.inr ⟨hx.1, h⟩

theorem size_subst (v : ℕ) (ℓ : Lit) : (C.subst v ℓ).size = C.size := rfl

/-! ### Solutions of the affine system -/

private theorem Equation.holds_add_add {E : Equation} {val val' val'' : ℕ → Bool} (h : E.Holds val)
    (h' : E.Holds val') (h'' : E.Holds val'') : E.Holds (val + val' + val'') := by
  unfold Equation.Holds at *
  simp only [Pi.add_apply, Finset.sum_add_distrib, h, h', h'']
  generalize E.rhs = r
  revert r; decide

private theorem eqnsHold_add_add {val val' val'' : ℕ → Bool} (h : C.EqnsHold val)
    (h' : C.EqnsHold val')
    (h'' : C.EqnsHold val'') : C.EqnsHold (val + val' + val'') :=
  fun e he => Equation.holds_add_add (h e he) (h' e he) (h'' e he)

theorem eqnsHold_congr {val val' : ℕ → Bool} (hC : C.WellFormed)
    (h : ∀ i ∈ C.params ∪ C.aux, val i = val' i) : C.EqnsHold val ↔ C.EqnsHold val' := by
  unfold EqnsHold Equation.Holds
  refine forall₂_congr fun e he => ?_
  rw [Finset.sum_congr rfl fun i hi => h i (hC.terms_subset e he hi)]

/-- Every assignment of the parameters of a well-formed semi-circuit extends to a consistent
assignment of all internal values: solve the affine system, then evaluate the gates in the order
of their names. -/
theorem WellFormed.exists_consistent (hC : C.WellFormed) (u : ℕ → Bool) :
    ∃ val, (∀ j ∈ C.params, val j = u j) ∧ C.Consistent val := by
  obtain ⟨val₀, hu, heq⟩ := hC.solvable u
  have key : ∀ k, ∃ val, (∀ i, i ∉ C.gates → val i = val₀ i) ∧
      ∀ J ∈ C.gates, J < k → val J = (C.gate J).eval val := by
    intro k
    induction k with
    | zero => exact ⟨val₀, fun _ _ => rfl, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
    | succ k ih =>
      obtain ⟨val, hval, hgate⟩ := ih
      by_cases hk : k ∈ C.gates
      · have heval : ∀ J ∈ C.gates, J ≤ k →
            (C.gate J).eval (Function.update val k ((C.gate k).eval val)) =
              (C.gate J).eval val := fun J hJ hJk => Gate.eval_congr fun i hi =>
          Function.update_of_ne (by
            rintro rfl
            exact absurd (hC.reads_lt J hJ i hk hi) (not_lt.2 hJk)) _ _
        refine ⟨Function.update val k ((C.gate k).eval val), fun i hi => ?_, ?_⟩
        · rw [Function.update_of_ne (by rintro rfl; exact hi hk)]
          exact hval i hi
        · intro J hJ hJk
          rcases (Nat.lt_succ_iff.1 hJk).lt_or_eq with h | rfl
          · rw [heval J hJ h.le, Function.update_of_ne h.ne, hgate J hJ h]
          · rw [heval J hJ le_rfl, Function.update_self]
      · exact ⟨val, hval, fun J hJ hJk => hgate J hJ
          (lt_of_le_of_ne (Nat.lt_succ_iff.1 hJk) (by rintro rfl; exact hk hJ))⟩
  obtain ⟨val, hval, hgate⟩ := key (C.gates.sup id + 1)
  have hng : ∀ i ∈ C.params ∪ C.aux, i ∉ C.gates := by
    intro i hi hg
    rcases Finset.mem_union.1 hi with hi | hi
    · exact Finset.disjoint_left.1 hC.disjoint_params_gates hi hg
    · exact Finset.disjoint_left.1 hC.disjoint_aux_gates hi hg
  refine ⟨val, fun j hj => (hval j (hng j (Finset.mem_union_left _ hj))).trans (hu j hj),
    (eqnsHold_congr hC fun i hi => hval i (hng i hi)).2 heq,
    fun J hJ => hgate J hJ (Nat.lt_succ_of_le (Finset.le_sup (f := id) hJ))⟩

/-- On the solutions of the affine system, the internal value `t` is the affine function
`c + ∑ j ∈ T, u j` of the parameters `u`. -/
def AffineIn (t : ℕ) (c : Bool) (T : Finset ℕ) : Prop :=
  T ⊆ C.params ∧ ∀ val, C.EqnsHold val → val t = c + ∑ j ∈ T, val j

/-- Every parameter is an affine function of the parameters. -/
theorem affineIn_param {x : ℕ} (hx : x ∈ C.params) : C.AffineIn x false {x} :=
  ⟨Finset.singleton_subset_iff.2 hx, fun val _ => by
    rw [Finset.sum_singleton]; cases val x <;> rfl⟩

/-- The affine expression of an internal value in the parameters is unique. -/
theorem AffineIn.unique (hC : C.WellFormed) {t : ℕ} {c c' : Bool} {T T' : Finset ℕ}
    (h : C.AffineIn t c T) (h' : C.AffineIn t c' T') : c = c' ∧ T = T' := by
  have key : ∀ u : ℕ → Bool, c + ∑ j ∈ T, u j = c' + ∑ j ∈ T', u j := by
    intro u
    obtain ⟨val, hu, heq⟩ := hC.solvable u
    rw [← Finset.sum_congr rfl fun j hj => hu j (h.1 hj),
      ← Finset.sum_congr rfl fun j hj => hu j (h'.1 hj), ← h.2 val heq, ← h'.2 val heq]
  have hc : c = c' := by simpa using key 0
  refine ⟨hc, Finset.ext fun j => ?_⟩
  have := key (Pi.single j true)
  rw [Finset.sum_pi_single', Finset.sum_pi_single', hc, add_right_inj] at this
  by_cases hj : j ∈ T <;> by_cases hj' : j ∈ T' <;> simp_all

/-! ### Affine functions of finitely many bits -/

/-- A function of bits that depends only on the coordinates in `M` and preserves sums of three
points is affine: a constant plus the sum of the coordinates in some `T ⊆ M`. -/
private theorem exists_affine_of_add_add {M : Finset ℕ} {g : (ℕ → Bool) → Bool}
    (hcongr : ∀ u u' : ℕ → Bool, (∀ j ∈ M, u j = u' j) → g u = g u')
    (hadd : ∀ u u' u'' : ℕ → Bool, g (u + u' + u'') = g u + g u' + g u'') :
    ∃ T ⊆ M, ∀ u, g u = g 0 + ∑ j ∈ T, u j := by
  classical
  let e : ℕ → ℕ → Bool := fun j => Pi.single j true
  have hsum : ∀ A : Finset ℕ, g (∑ j ∈ A, e j) = g 0 + ∑ j ∈ A, (g (e j) + g 0) := by
    intro A
    induction A using Finset.induction_on with
    | empty => simp
    | @insert j A hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj]
      have := hadd (e j) (∑ i ∈ A, e i) 0
      rw [add_zero] at this
      rw [this, ih]
      ring
  refine ⟨M.filter fun j => g (e j) + g 0 = true, Finset.filter_subset _ _, fun u => ?_⟩
  have hu : g u = g (∑ j ∈ M.filter (fun j => u j = true), e j) := by
    apply hcongr
    intro i hi
    rw [Finset.sum_apply, Finset.sum_pi_single]
    simp only [Finset.mem_filter, hi, true_and]
    cases u i <;> rfl
  rw [hu, hsum]
  congr 1
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  cases u j <;> cases g (e j) + g 0 <;> rfl

variable {C : SemiCircuit}

/-- Every auxiliary variable of a well-formed semi-circuit is an affine function of the
parameters on the solutions of the affine system. -/
theorem WellFormed.exists_affineIn (hC : C.WellFormed) {v : ℕ} (hv : v ∈ C.aux) :
    ∃ c T, C.AffineIn v c T := by
  classical
  let sol : (ℕ → Bool) → ℕ → Bool := fun u => (hC.solvable u).choose
  have hsol : ∀ u, (∀ j ∈ C.params, sol u j = u j) ∧ C.EqnsHold (sol u) :=
    fun u => (hC.solvable u).choose_spec
  have hval : ∀ val, C.EqnsHold val → val v = sol val v := fun val hval =>
    hC.unique _ _ (fun j hj => ((hsol val).1 j hj).symm) hval (hsol val).2 v hv
  obtain ⟨T, hT, hg⟩ := exists_affine_of_add_add (M := C.params) (g := fun u => sol u v)
    (fun u u' h => hC.unique _ _ (fun j hj => by rw [(hsol u).1 j hj, (hsol u').1 j hj, h j hj])
      (hsol u).2 (hsol u').2 v hv)
    (fun u u' u'' => by
      have := hC.unique (sol (u + u' + u'')) (sol u + sol u' + sol u'')
        (fun j hj => by simp only [Pi.add_apply, (hsol _).1 j hj])
        (hsol _).2 (eqnsHold_add_add (hsol u).2 (hsol u').2 (hsol u'').2) v hv
      simpa using this)
  exact ⟨sol 0 v, T, hT, fun val hv' => by rw [hval val hv', hg]⟩

/-- An auxiliary variable can depend only on parameters occurring in the affine system. -/
theorem AffineIn.mem_terms {t : ℕ} {c : Bool} {T : Finset ℕ} (hC : C.WellFormed)
    (h : C.AffineIn t c T) (ht : t ∉ C.params) {x : ℕ} (hx : x ∈ T) :
    ∃ e ∈ C.eqns, x ∈ (C.eqn e).terms := by
  by_contra hne
  push Not at hne
  obtain ⟨val, -, heq⟩ := hC.solvable 0
  have hxp := h.1 hx
  have hupd : ∀ i, i ≠ x → Function.update val x (!val x) i = val i :=
    fun i hi => Function.update_of_ne hi _ _
  have heq' : C.EqnsHold (Function.update val x (!val x)) := by
    intro e he
    unfold Equation.Holds
    rw [Finset.sum_congr rfl fun i hi => hupd i (by rintro rfl; exact hne e he hi)]
    exact heq e he
  have h1 := h.2 _ heq'
  rw [hupd t (by rintro rfl; exact ht hxp), h.2 val heq, ← Finset.add_sum_erase T _ hx,
    ← Finset.add_sum_erase T _ hx, Function.update_self,
    Finset.sum_congr rfl fun i hi => hupd i (Finset.ne_of_mem_erase hi)] at h1
  cases val x <;> simp at h1

/-- A parameter occurring in the affine system is a summand of some auxiliary variable. -/
theorem exists_affineIn_of_mem_terms (hC : C.WellFormed) {x e : ℕ} (hx : x ∈ C.params)
    (he : e ∈ C.eqns) (hxe : x ∈ (C.eqn e).terms) :
    ∃ Q ∈ C.aux, ∃ c T, C.AffineIn Q c T ∧ x ∈ T := by
  classical
  by_contra hne
  push Not at hne
  obtain ⟨val, -, heq⟩ := hC.solvable 0
  obtain ⟨val', hval', heq'⟩ := hC.solvable (Function.update val x (!val x))
  have hagree : ∀ i ∈ (C.eqn e).terms, i ≠ x → val i = val' i := by
    intro i hi hix
    rcases Finset.mem_union.1 (hC.terms_subset e he hi) with hi | hi
    · rw [hval' i hi, Function.update_of_ne hix]
    · obtain ⟨c, T, hT⟩ := hC.exists_affineIn hi
      have hxT : x ∉ T := fun h => hne i hi c T hT h
      rw [hT.2 val heq, hT.2 val' heq']
      congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hval' j (hT.1 hj), Function.update_of_ne (by rintro rfl; exact hxT hj)]
  have h1 := heq e he
  have h2 := heq' e he
  unfold Equation.Holds at h1 h2
  rw [← Finset.add_sum_erase _ _ hxe] at h1 h2
  rw [hval' x hx, Function.update_self] at h2
  rw [Finset.sum_congr rfl fun i hi => hagree i (Finset.mem_of_mem_erase hi)
    (Finset.ne_of_mem_erase hi), ← h2] at h1
  cases val x <;> simp at h1

/-! ### Changing unread values -/

/-- Changing the value of a name that no gate or equation reads and that is not a gate keeps
consistency. -/
theorem consistent_update_iff {x : ℕ} (hxg : x ∉ C.gates)
    (hgate : ∀ J ∈ C.gates, ¬ (C.gate J).Reads x) (heqn : ∀ e ∈ C.eqns, x ∉ (C.eqn e).terms)
    (val : ℕ → Bool) (b : Bool) : C.Consistent (Function.update val x b) ↔ C.Consistent val := by
  have hupd : ∀ i, i ≠ x → Function.update val x b i = val i := fun i hi =>
    Function.update_of_ne hi _ _
  refine and_congr (forall₂_congr fun e he => Equation.holds_congr fun i hi =>
    hupd i fun h => heqn e he (h ▸ hi)) (forall₂_congr fun J hJ => ?_)
  rw [hupd J fun h => hxg (h ▸ hJ), Gate.eval_congr fun i hi => hupd i fun h => hgate J hJ (h ▸ hi)]

/-- After rerouting `x`, which is not a gate, to a literal not reading it, a consistent assignment
gives a consistent assignment of the original semi-circuit once `x` takes the value of the
literal. -/
theorem consistent_of_subst {x : ℕ} {ℓ : Lit} (hxg : x ∉ C.gates) (hℓ : ℓ.arg ≠ .node x)
    {val : ℕ → Bool} (h : (C.subst x ℓ).Consistent val) :
    C.Consistent (Function.update val x (ℓ.eval val)) := by
  have hupd : ℓ.eval (Function.update val x (ℓ.eval val)) = ℓ.eval val :=
    Lit.eval_congr fun i hi => Function.update_of_ne (by rintro rfl; exact hℓ hi) _ _
  refine (consistent_subst (v := x) (ℓ := ℓ) (by rw [Function.update_self, hupd])).1 ?_
  exact (consistent_update_iff (C := C.subst x ℓ) hxg (fun J _ => Gate.not_reads_subst hℓ)
    (fun e _ => Equation.notMem_subst hℓ) val _).2 h

/-! ### Lifting consistent assignments -/

/-- Every consistent assignment of `C'` agrees on the parameters of `C` with a consistent
assignment of `C` having the same output. -/
def LiftsTo (C' C : SemiCircuit) : Prop :=
  ∀ val, C'.Consistent val →
    ∃ w, C.Consistent w ∧ (∀ j ∈ C.params, w j = val j) ∧ C'.out.eval val = C.out.eval w

end SemiCircuit

end Cslib.Circuits.Boolean
