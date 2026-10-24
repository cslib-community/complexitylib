/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Pi
public import Complexity.Foundations.Data.List.BalancedFold
public import Cslib.Computability.Circuit.Homomorphism
public import Cslib.Computability.Circuit.Simulation
public import Cslib.Computability.Circuit.Synthesis
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Piecewise
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Logic.Function.DependsOn
public import Mathlib.Order.SetNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Defs
import Complexity.Computability.Circuit.Simulation

/-!
# Formulas

A formula over a signature is a tree of operation symbols with inputs at its leaves, that is, a
circuit in which every gate is read once. It is evaluated under an interpretation like a circuit
(`Formula.eval`). Formulas are the free monad on the polynomial functor of the signature; a
dedicated inductive type gives them readable constructors and structural induction. Equality of
formulas is decidable, constructively, when equality of operation symbols is
(`Formula.decidableEq`), so concrete formulas can be compared by `decide`.

The *leaf size* `Formula.leafSize` counts the input leaves, the measure of formula lower bounds
[Jukna, Chapter 6][Jukna2012]. Nullary operations, such as constants, are not counted: constants
can be eliminated from a formula for a nonconstant function, so this changes no lower bound, and
it gives constant functions leaf size zero. `Formula.size` counts the operation nodes, constants
included. A formula of depth `d` with operations of arity at most `r` has at most `r ^ d` leaves
(`Formula.leafSize_le_pow_depth`) and, for `r ≥ 2`, fewer than `r ^ d` operation nodes
(`Formula.size_lt_pow_depth`); with `s` operation nodes it has at most `(r - 1) s + 1` leaves
(`Formula.leafSize_le`). The least depth of a formula computing a function, with given costs of the
operations, is `Formula.minDepthWith`; it is `⊤` when no formula computes the function, as happens
for monotone formulas. A formula is a circuit with one gate for each operation node and at most
its depth (`Formula.toCircuit`). Counting only the leaves labelled by inputs of a set `Y`
(`Formula.leafSizeIn`) splits the leaf size among disjoint blocks of inputs
(`Formula.sum_leafSizeIn_le_leafSize`), and a formula with no leaf in `Y` depends only on the
inputs outside `Y` (`Formula.dependsOn_eval_of_leafSizeIn_eq_zero`). An operation of arity two
folds a list of `k` formulas into a balanced tree (`Formula.balanced`, by `List.balancedFold`) of
depth `⌈log₂ k⌉` above them, the usual way to replace a gate of unbounded fan-in.

## Main definitions

* `Cslib.Circuits.Formula`: formulas over a signature.
* `Cslib.Circuits.Formula.eval`, `Cslib.Circuits.Formula.Computes`: evaluation.
* `Cslib.Circuits.Formula.leafSize`, `Cslib.Circuits.Formula.size`,
  `Cslib.Circuits.Formula.depth`: the number of input leaves, the number of operation nodes, and
  the depth.
* `Cslib.Circuits.Formula.leafSizeIn`: the number of input leaves in a set of inputs.
* `Cslib.Circuits.Formula.cost`: the sum of operation weights, with input leaves free.
* `Cslib.Circuits.Formula.depthWith`: the depth when each operation costs a given number of levels.
* `Cslib.Circuits.Formula.minDepthWith`: the least depth with costs of a formula computing a
  function, in `ℕ∞`.
* `Cslib.Circuits.Formula.gate₂`, `Cslib.Circuits.Formula.balanced`: an operation of arity two
  applied to two formulas, and the balanced tree of such an operation over a list of formulas.
* `Cslib.Circuits.Formula.bind`: substitution of formulas for the inputs; `Formula.rename`
  renames the inputs, and `Formula.lift` and `Formula.substLast` add an input and substitute for
  it.
* `Cslib.Circuits.Formula.toCircuit`: a formula as a single-output circuit.

## Main results

* `Cslib.Circuits.Formula.map_eval`: evaluation commutes with homomorphisms.
* `Cslib.Circuits.Formula.minDepthWith_le`, `Cslib.Circuits.Formula.le_minDepthWith_iff`,
  `Cslib.Circuits.Formula.exists_depthWith_eq_minDepthWith`: upper and lower bounds on the least
  depth, which is attained when some formula computes the function.
* `Cslib.Circuits.Formula.leafSize_le_pow_depth`, `Cslib.Circuits.Formula.leafSize_le`: leaf size
  under bounded fan-in.
* `Cslib.Circuits.Formula.size_lt_pow_depth`: size under bounded fan-in.
* `Cslib.Circuits.Formula.depth_bind_le`, `Cslib.Circuits.Formula.size_bind_le`: depth and size
  after substitution.
* `Cslib.Circuits.Formula.size_balanced_add_one`, `Cslib.Circuits.Formula.depthWith_balanced_le`:
  a balanced tree over `k ≥ 1` formulas adds `k - 1` nodes and `⌈log₂ k⌉` levels.
* `Cslib.Circuits.Formula.Computes.toCircuit`, `Cslib.Circuits.Formula.size_toCircuit`,
  `Cslib.Circuits.Formula.depth_toCircuit_le`: a formula is a circuit computing the same function,
  of the same size and at most the same depth.
* `Cslib.Circuits.Formula.cost_toCircuit`: compilation preserves arbitrary operation weights.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib.Circuits

universe v

/-- A formula over the signature `σ` with inputs `Fin n`: an input, or an operation applied to
formulas. -/
inductive Formula (σ : Signature.{v}) (n : ℕ) : Type v where
  /-- An input. -/
  | input (i : Fin n)
  /-- An operation applied to formulas for its arguments. -/
  | gate (op : σ.Op) (args : Fin (σ.Arity op) → Formula σ n)

namespace Formula

variable {σ : Signature.{v}} {n : ℕ} {U V : Type*}

/-- Formulas have decidable equality when operation symbols do: compare the operations at the
roots, then the arguments pointwise. -/
instance decidableEq [DecidableEq σ.Op] : DecidableEq (Formula σ n)
  | input i, input j => decidable_of_iff (i = j) (by simp)
  | input _, gate _ _ => isFalse fun h => by cases h
  | gate _ _, input _ => isFalse fun h => by cases h
  | gate op args, gate op' args' =>
    if hop : op = op' then by
      subst hop
      letI (j : Fin (σ.Arity op)) : Decidable (args j = args' j) := decidableEq (args j) (args' j)
      exact decidable_of_iff (∀ j, args j = args' j) (by simp [funext_iff])
    else isFalse fun h => by cases h; exact hop rfl

/-- Evaluate a formula under an interpretation. -/
def eval (F : Formula σ n) (I : Interpretation σ U) (x : Fin n → U) : U :=
  match F with
  | input i => x i
  | gate op args => I op fun j => (args j).eval I x

/-- An input leaf `input i` evaluates to `x i`. -/
@[simp] theorem eval_input (I : Interpretation σ U) (i : Fin n) (x : Fin n → U) :
    (input i : Formula σ n).eval I x = x i :=
  rfl

/-- An operation node `gate op args` evaluates by applying `I op` to the values of its
arguments. -/
@[simp] theorem eval_gate (I : Interpretation σ U) (op : σ.Op)
    (args : Fin (σ.Arity op) → Formula σ n) (x : Fin n → U) :
    (gate op args).eval I x = I op fun j => (args j).eval I x :=
  rfl

/-- Evaluating a formula commutes with a homomorphism. -/
theorem map_eval {I₁ : Interpretation σ U} {I₂ : Interpretation σ V} (h : Homomorphism I₁ I₂)
    (F : Formula σ n) (x : Fin n → U) : h.map (F.eval I₁ x) = F.eval I₂ (h.map ∘ x) := by
  induction F with
  | input i => rfl
  | gate op args ih =>
    rw [eval_gate, h.homomorphic, eval_gate]
    congr 1
    funext j
    exact ih j

/-- A formula computes `f` when it agrees with `f` on every input. -/
def Computes (F : Formula σ n) (I : Interpretation σ U) (f : (Fin n → U) → U) : Prop :=
  ∀ x, F.eval I x = f x

/-- A formula computes `f` exactly when its evaluation is `f`. -/
theorem computes_iff {F : Formula σ n} {I : Interpretation σ U} {f : (Fin n → U) → U} :
    F.Computes I f ↔ F.eval I = f :=
  funext_iff.symm

/-- The leaf size: the number of input leaves. Nullary operations, such as constants, are not
counted. -/
def leafSize : Formula σ n → ℕ
  | input _ => 1
  | gate _ args => ∑ j, (args j).leafSize

/-- The number of operation nodes, nullary ones included. -/
def size : Formula σ n → ℕ
  | input _ => 0
  | gate _ args => (∑ j, (args j).size) + 1

/-- The sum of operation weights, including nullary operations; input leaves are free. -/
def cost (weight : σ.Op → ℕ) : Formula σ n → ℕ
  | input _ => 0
  | gate op args => (∑ j, (args j).cost weight) + weight op

/-- The depth: inputs have depth zero, and an operation node is one deeper than its arguments, so
nullary operations have depth one, as gates do in circuits. -/
def depth : Formula σ n → ℕ
  | input _ => 0
  | gate _ args => (Finset.univ.sup fun j => (args j).depth) + 1

/-- An input leaf has leaf size `1`. -/
@[simp] theorem leafSize_input (i : Fin n) : (input i : Formula σ n).leafSize = 1 :=
  rfl

/-- The leaf size of an operation node is the sum of the leaf sizes of its arguments. -/
@[simp] theorem leafSize_gate (op : σ.Op) (args : Fin (σ.Arity op) → Formula σ n) :
    (gate op args).leafSize = ∑ j, (args j).leafSize :=
  rfl

/-- An input leaf has `0` operation nodes. -/
@[simp] theorem size_input (i : Fin n) : (input i : Formula σ n).size = 0 :=
  rfl

/-- The size of an operation node is the sum of the sizes of its arguments plus `1`. -/
@[simp] theorem size_gate (op : σ.Op) (args : Fin (σ.Arity op) → Formula σ n) :
    (gate op args).size = (∑ j, (args j).size) + 1 :=
  rfl

/-- An input leaf has cost `0`. -/
@[simp] theorem cost_input (weight : σ.Op → ℕ) (i : Fin n) :
    (input i : Formula σ n).cost weight = 0 := rfl

/-- The cost of an operation node is the sum of the costs of its arguments plus `weight op`. -/
@[simp] theorem cost_gate (weight : σ.Op → ℕ) (op : σ.Op)
    (args : Fin (σ.Arity op) → Formula σ n) :
    (gate op args).cost weight = (∑ j, (args j).cost weight) + weight op := rfl

/-- Unit operation weights count all operation nodes. -/
@[simp] theorem cost_one (F : Formula σ n) : F.cost (fun _ => 1) = F.size := by
  induction F with
  | input => rfl
  | gate op args ih => simp [cost, ih]

/-- An input leaf has depth `0`. -/
@[simp] theorem depth_input (i : Fin n) : (input i : Formula σ n).depth = 0 :=
  rfl

/-- The depth of an operation node is one more than the maximum depth of its arguments. -/
@[simp] theorem depth_gate (op : σ.Op) (args : Fin (σ.Arity op) → Formula σ n) :
    (gate op args).depth = (Finset.univ.sup fun j => (args j).depth) + 1 :=
  rfl

/-- With operations of arity at most `r`, a formula of depth `d` has at most `r ^ d` leaves. -/
theorem leafSize_le_pow_depth {r : ℕ} (hr : ∀ op, σ.Arity op ≤ r) (F : Formula σ n) :
    F.leafSize ≤ r ^ F.depth := by
  induction F with
  | input i => simp
  | gate op args ih =>
    set d := Finset.univ.sup fun j => (args j).depth
    rw [leafSize_gate, depth_gate, pow_succ]
    calc ∑ j, (args j).leafSize ≤ ∑ j, r ^ (args j).depth := Finset.sum_le_sum fun j _ => ih j
      _ ≤ Fintype.card (Fin (σ.Arity op)) • r ^ d :=
          Finset.sum_le_card_nsmul _ _ _ fun j _ => Nat.pow_le_pow_right
            (Nat.pos_of_ne_zero fun h => absurd (j.isLt.trans_le (hr op)) (by omega))
            (Finset.le_sup (f := fun j => (args j).depth) (Finset.mem_univ j))
      _ ≤ r ^ d * r := by
          rw [Fintype.card_fin, smul_eq_mul, mul_comm]
          exact Nat.mul_le_mul_left _ (hr op)

/-- With operations of arity at most `r`, where `2 ≤ r`, a formula of depth `d` has fewer than
`r ^ d` operation nodes. -/
theorem size_lt_pow_depth {r : ℕ} (hr : ∀ op, σ.Arity op ≤ r) (hr₂ : 2 ≤ r) (F : Formula σ n) :
    F.size < r ^ F.depth := by
  induction F with
  | input i => simp
  | gate op args ih =>
    set d := Finset.univ.sup fun j => (args j).depth
    have hd : 1 ≤ r ^ d := Nat.one_le_pow _ _ (by omega)
    have hsum : ∑ j, ((args j).size + 1) ≤ σ.Arity op * r ^ d := by
      calc ∑ j, ((args j).size + 1) ≤ ∑ _j : Fin (σ.Arity op), r ^ d :=
            Finset.sum_le_sum fun j _ => (ih j).trans_le (Nat.pow_le_pow_right (by omega)
              (Finset.le_sup (f := fun j => (args j).depth) (Finset.mem_univ j)))
        _ = σ.Arity op * r ^ d := by simp
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one] at hsum
    rw [size_gate, depth_gate, pow_succ, mul_comm]
    have hk := hr op
    rcases Nat.lt_or_ge (σ.Arity op) 2 with hk₂ | hk₂
    · calc (∑ j, (args j).size) + 1 ≤ r ^ d := by
            obtain h | h : σ.Arity op = 0 ∨ σ.Arity op = 1 := by omega
            · have : σ.Arity op * r ^ d = 0 := by rw [h, zero_mul]
              omega
            · have : σ.Arity op * r ^ d = r ^ d := by rw [h, one_mul]
              omega
        _ < 2 * r ^ d := by omega
        _ ≤ r * r ^ d := Nat.mul_le_mul_right _ hr₂
    · calc (∑ j, (args j).size) + 1 < (∑ j, (args j).size) + σ.Arity op := by omega
        _ ≤ σ.Arity op * r ^ d := hsum
        _ ≤ r * r ^ d := Nat.mul_le_mul_right _ hk

/-- With operations of arity at most `r`, a formula with `s` operation nodes has at most
`(r - 1) s + 1` leaves. -/
theorem leafSize_le {r : ℕ} (hr : ∀ op, σ.Arity op ≤ r) (F : Formula σ n) :
    F.leafSize ≤ (r - 1) * F.size + 1 := by
  induction F with
  | input i => simp
  | gate op args ih =>
    rw [leafSize_gate, size_gate]
    calc ∑ j, (args j).leafSize ≤ ∑ j, ((r - 1) * (args j).size + 1) :=
          Finset.sum_le_sum fun j _ => ih j
      _ = (r - 1) * ∑ j, (args j).size + σ.Arity op := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
          simp
      _ ≤ (r - 1) * ((∑ j, (args j).size) + 1) + 1 := by
          have := hr op
          rw [Nat.mul_succ]
          omega

/-- The number of input leaves labelled by inputs in `Y`. -/
def leafSizeIn (Y : Finset (Fin n)) : Formula σ n → ℕ
  | input i => if i ∈ Y then 1 else 0
  | gate _ args => ∑ j, (args j).leafSizeIn Y

/-- An input leaf `input i` has `1` leaf in `Y` when `i ∈ Y` and `0` otherwise. -/
@[simp] theorem leafSizeIn_input (Y : Finset (Fin n)) (i : Fin n) :
    (input i : Formula σ n).leafSizeIn Y = if i ∈ Y then 1 else 0 :=
  rfl

/-- The number of leaves of `gate op args` in `Y` is the sum over its arguments. -/
@[simp] theorem leafSizeIn_gate (Y : Finset (Fin n)) (op : σ.Op)
    (args : Fin (σ.Arity op) → Formula σ n) :
    (gate op args).leafSizeIn Y = ∑ j, (args j).leafSizeIn Y :=
  rfl

/-- Disjoint blocks of inputs share out the leaves. -/
theorem sum_leafSizeIn_le_leafSize {ι : Type*} {s : Finset ι} {Y : ι → Finset (Fin n)}
    (hY : (s : Set ι).PairwiseDisjoint Y) (F : Formula σ n) :
    ∑ i ∈ s, F.leafSizeIn (Y i) ≤ F.leafSize := by
  induction F with
  | input j =>
    simp only [leafSizeIn_input, leafSize_input, ← Finset.card_filter]
    refine Finset.card_le_one.2 fun a ha b hb => ?_
    by_contra hab
    exact Finset.disjoint_left.1 (hY (Finset.mem_filter.1 ha).1 (Finset.mem_filter.1 hb).1 hab)
      (Finset.mem_filter.1 ha).2 (Finset.mem_filter.1 hb).2
  | gate op args ih =>
    simp only [leafSizeIn_gate, leafSize_gate]
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun j _ => ih j

/-- Counting leaves in the set of all inputs gives the leaf size. -/
@[simp] theorem leafSizeIn_univ (F : Formula σ n) : F.leafSizeIn Finset.univ = F.leafSize := by
  induction F with
  | input i => simp
  | gate op args ih => simp [ih]

/-- No leaves lie in the empty set of inputs. -/
@[simp] theorem leafSizeIn_empty (F : Formula σ n) : F.leafSizeIn ∅ = 0 := by
  induction F with
  | input i => simp
  | gate op args ih => simp [ih]

/-- The leaves in a set of inputs are at most all leaves. -/
theorem leafSizeIn_le_leafSize (Y : Finset (Fin n)) (F : Formula σ n) :
    F.leafSizeIn Y ≤ F.leafSize := by
  simpa using F.sum_leafSizeIn_le_leafSize (s := {Y}) (Y := id) (by simp)

/-- The leaves in a set of inputs are the leaves at each of its inputs. -/
theorem sum_leafSizeIn_singleton (S : Finset (Fin n)) (F : Formula σ n) :
    ∑ i ∈ S, F.leafSizeIn {i} = F.leafSizeIn S := by
  induction F with
  | input j =>
    simp only [leafSizeIn_input, Finset.mem_singleton]
    rw [Finset.sum_ite_eq]
  | gate op args ih =>
    simp only [leafSizeIn_gate]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => ih j

/-- Every leaf reads an input in a set or in its complement. -/
theorem leafSizeIn_add_leafSizeIn_compl (S : Finset (Fin n)) (F : Formula σ n) :
    F.leafSizeIn S + F.leafSizeIn Sᶜ = F.leafSize := by
  induction F with
  | input j => by_cases h : j ∈ S <;> simp [h]
  | gate op args ih =>
    simp only [leafSizeIn_gate, leafSize_gate, ← Finset.sum_add_distrib, ih]

/-- A formula with no leaf in `Y` depends only on the inputs outside `Y`. -/
theorem dependsOn_eval_of_leafSizeIn_eq_zero {Y : Finset (Fin n)} {F : Formula σ n}
    (hF : F.leafSizeIn Y = 0) (I : Interpretation σ U) :
    DependsOn (F.eval I) (↑Y)ᶜ := by
  induction F with
  | input i =>
    have hi : i ∉ Y := by simpa using hF
    exact fun x y h => h i hi
  | gate op args ih =>
    rw [leafSizeIn_gate, Finset.sum_eq_zero_iff] at hF
    intro x y h
    simp only [eval_gate]
    congr 1
    funext j
    exact ih j (hF j (Finset.mem_univ j)) h

/-- A formula with no leaf in `Y` ignores the inputs in `Y`. -/
theorem eval_piecewise_eq_of_leafSizeIn_eq_zero {Y : Finset (Fin n)} {F : Formula σ n}
    (hF : F.leafSizeIn Y = 0) (I : Interpretation σ U) (x x' z : Fin n → U) :
    F.eval I (Y.piecewise x z) = F.eval I (Y.piecewise x' z) :=
  dependsOn_eval_of_leafSizeIn_eq_zero hF I fun i hi => by simp [show i ∉ Y by simpa using hi]

/-- A formula without input leaves computes a constant. -/
theorem eval_eq_of_leafSize_eq_zero {F : Formula σ n} (hF : F.leafSize = 0) (I : Interpretation σ U)
    (x y : Fin n → U) : F.eval I x = F.eval I y :=
  DependsOn.empty (by
    simpa using dependsOn_eval_of_leafSizeIn_eq_zero (Y := Finset.univ) (by simpa using hF) I) x y

/-- The depth when an operation node costs `cost op` levels instead of one: `depthWith 1` is the
depth, and charging nothing for negations gives the depth of formulas with free negations. -/
def depthWith (cost : σ.Op → ℕ) : Formula σ n → ℕ
  | input _ => 0
  | gate op args => (Finset.univ.sup fun j => (args j).depthWith cost) + cost op

/-- An input leaf has weighted depth `0`. -/
@[simp] theorem depthWith_input (cost : σ.Op → ℕ) (i : Fin n) :
    (input i : Formula σ n).depthWith cost = 0 :=
  rfl

/-- The weighted depth of `gate op args` is the maximum weighted depth of its arguments plus
`cost op`. -/
@[simp] theorem depthWith_gate (cost : σ.Op → ℕ) (op : σ.Op)
    (args : Fin (σ.Arity op) → Formula σ n) :
    (gate op args).depthWith cost = (Finset.univ.sup fun j => (args j).depthWith cost) + cost op :=
  rfl

/-- With unit operation costs, `depthWith` is `depth`. -/
@[simp] theorem depthWith_one (F : Formula σ n) : F.depthWith 1 = F.depth := by
  induction F with
  | input i => rfl
  | gate op args ih => simp [ih]

/-- Cheaper operations give a smaller depth. -/
theorem depthWith_mono {cost cost' : σ.Op → ℕ} (h : ∀ op, cost op ≤ cost' op) (F : Formula σ n) :
    F.depthWith cost ≤ F.depthWith cost' := by
  induction F with
  | input i => rfl
  | gate op args ih =>
    exact Nat.add_le_add (Finset.sup_mono_fun fun j _ => ih j) (h op)

/-- Costs of at most one never make a formula deeper. -/
theorem depthWith_le_depth {cost : σ.Op → ℕ} (hcost : ∀ op, cost op ≤ 1) (F : Formula σ n) :
    F.depthWith cost ≤ F.depth :=
  (F.depthWith_mono (cost' := 1) hcost).trans_eq F.depthWith_one

/-! ### Balanced trees -/

section Balanced

/-- An operation of arity two applied to two formulas. -/
def gate₂ (op : σ.Op) (hop : σ.Arity op = 2) (F G : Formula σ n) : Formula σ n :=
  gate op fun j => ![F, G] (j.cast hop)

variable {op : σ.Op} {hop : σ.Arity op = 2}

private theorem apply_vecCons_two {M N : Type*} (g : M → N) (a b : M) (i : Fin 2) :
    g (![a, b] i) = ![g a, g b] i := by
  match i with
  | 0 => rfl
  | 1 => rfl

/-- Evaluating `gate₂ op hop F G` applies `I op` to the values of `F` and `G`. -/
@[simp] theorem eval_gate₂ (I : Interpretation σ U) (F G : Formula σ n) (x : Fin n → U) :
    (gate₂ op hop F G).eval I x = I op fun j => ![F.eval I x, G.eval I x] (j.cast hop) := by
  rw [gate₂, eval_gate]
  exact congrArg (I op) (funext fun j => apply_vecCons_two (eval · I x) F G _)

private theorem sum_cast_two {k : ℕ} (h : k = 2) (a b : ℕ) :
    ∑ j : Fin k, ![a, b] (j.cast h) = a + b := by
  subst h
  simp [Fin.sum_univ_two]

private theorem sup_cast_two {k : ℕ} (h : k = 2) (a b : ℕ) :
    (Finset.univ.sup fun j : Fin k => ![a, b] (j.cast h)) = max a b := by
  subst h
  simp [Fin.univ_succ]

/-- The size of `gate₂ op hop F G` is `F.size + G.size + 1`. -/
@[simp] theorem size_gate₂ (F G : Formula σ n) :
    (gate₂ op hop F G).size = F.size + G.size + 1 := by
  rw [gate₂, size_gate, ← sum_cast_two hop F.size G.size]
  simp only [apply_vecCons_two size]

/-- The cost of `gate₂ op hop F G` is `F.cost weight + G.cost weight + weight op`. -/
@[simp] theorem cost_gate₂ (weight : σ.Op → ℕ) (F G : Formula σ n) :
    (gate₂ op hop F G).cost weight = F.cost weight + G.cost weight + weight op := by
  rw [gate₂, cost_gate, ← sum_cast_two hop (F.cost weight) (G.cost weight)]
  simp only [apply_vecCons_two (cost weight)]

/-- The leaf size of `gate₂ op hop F G` is `F.leafSize + G.leafSize`. -/
@[simp] theorem leafSize_gate₂ (F G : Formula σ n) :
    (gate₂ op hop F G).leafSize = F.leafSize + G.leafSize := by
  rw [gate₂, leafSize_gate, ← sum_cast_two hop]
  simp only [apply_vecCons_two leafSize]

/-- The weighted depth of `gate₂ op hop F G` is the maximum of the weighted depths of `F` and `G`
plus `cost op`. -/
@[simp] theorem depthWith_gate₂ (cost : σ.Op → ℕ) (F G : Formula σ n) :
    (gate₂ op hop F G).depthWith cost = max (F.depthWith cost) (G.depthWith cost) + cost op := by
  rw [gate₂, depthWith_gate, ← sup_cast_two hop]
  simp only [apply_vecCons_two (depthWith cost)]

/-- The balanced tree of an operation of arity two over a list of formulas
(`List.balancedFold`): `unit` for the empty list, the formula for a singleton, and for `k ≥ 2`
formulas the operation applied to the trees of the first `⌊k / 2⌋` formulas and of the others. -/
def balanced (op : σ.Op) (hop : σ.Arity op = 2) (unit : Formula σ n) (l : List (Formula σ n)) :
    Formula σ n :=
  l.balancedFold (gate₂ op hop) unit id

/-- The balanced tree over the empty list is `unit`. -/
@[simp] theorem balanced_nil (unit : Formula σ n) : balanced op hop unit [] = unit :=
  List.balancedFold_nil

/-- The balanced tree over a singleton list `[F]` is `F`. -/
@[simp] theorem balanced_singleton (unit F : Formula σ n) : balanced op hop unit [F] = F :=
  List.balancedFold_singleton F

/-- A balanced tree evaluates to the balanced fold of the values of its formulas. -/
theorem eval_balanced (I : Interpretation σ U) (unit : Formula σ n) (l : List (Formula σ n))
    (x : Fin n → U) :
    (balanced op hop unit l).eval I x =
      l.balancedFold (fun a b => I op fun j => ![a, b] (j.cast hop)) (unit.eval I x)
        (·.eval I x) :=
  List.balancedFold_hom (·.eval I x) (fun F G => eval_gate₂ I F G x) l

/-- A balanced tree over `k ≥ 1` formulas has `k - 1` operation nodes besides theirs. -/
theorem size_balanced_add_one (unit : Formula σ n) {l : List (Formula σ n)} (hl : l ≠ []) :
    (balanced op hop unit l).size + 1 = (l.map size).sum + l.length := by
  refine List.balancedFold_induction (p := fun (l : List (Formula σ n)) (F : Formula σ n) =>
      l ≠ [] → F.size + 1 = (l.map size).sum + l.length) (fun h => absurd rfl h)
    (fun F _ => by simp)
    (fun l₁ l₂ F G h₁ h₂ hF hG _ => ?_) l hl
  have := hF h₁
  have := hG h₂
  simp only [size_gate₂, List.map_append, List.sum_append, List.length_append]
  omega

/-- A balanced tree over `k ≥ 1` formulas has their leaves. -/
theorem leafSize_balanced (unit : Formula σ n) {l : List (Formula σ n)} (hl : l ≠ []) :
    (balanced op hop unit l).leafSize = (l.map leafSize).sum := by
  refine List.balancedFold_induction (p := fun (l : List (Formula σ n)) (F : Formula σ n) =>
      l ≠ [] → F.leafSize = (l.map leafSize).sum) (fun h => absurd rfl h) (fun F _ => by simp)
    (fun l₁ l₂ F G h₁ h₂ hF hG _ => ?_) l hl
  simp only [leafSize_gate₂, List.map_append, List.sum_append, hF h₁, hG h₂]

/-- A balanced tree is deeper than its formulas by `⌈log₂⌉` of their number times the cost of the
operation; `unit` only matters for the empty list. -/
theorem depthWith_balanced_le {cost : σ.Op → ℕ} (unit : Formula σ n) {l : List (Formula σ n)}
    {d : ℕ} (hl : ∀ F ∈ l, F.depthWith cost ≤ d) (hunit : l = [] → unit.depthWith cost ≤ d) :
    (balanced op hop unit l).depthWith cost ≤ d + cost op * Nat.clog 2 l.length :=
  List.apply_balancedFold_le (depthWith cost) (fun F G => (depthWith_gate₂ cost F G).le) hl hunit

end Balanced

/-! ### Least depth -/

section MinDepthWith

variable {I : Interpretation σ U} {cost : σ.Op → ℕ} {f : (Fin n → U) → U}

variable (I cost) in
/-- The least depth with costs `cost` of a formula computing `f` under `I`, or `⊤` if no formula
computes `f`. -/
noncomputable def minDepthWith (f : (Fin n → U) → U) : ℕ∞ :=
  ⨅ F : {F : Formula σ n // F.Computes I f}, (F.1.depthWith cost : ℕ∞)

/-- The least depth is at most the depth of every formula computing the function. -/
theorem minDepthWith_le {F : Formula σ n} (hF : F.Computes I f) :
    minDepthWith I cost f ≤ F.depthWith cost :=
  iInf_le_of_le ⟨F, hF⟩ le_rfl

/-- Lower bounds on the least depth are lower bounds on the depth of every formula computing the
function, including when there is none. -/
theorem le_minDepthWith_iff {k : ℕ∞} :
    k ≤ minDepthWith I cost f ↔ ∀ F : Formula σ n, F.Computes I f → k ≤ F.depthWith cost := by
  simp only [minDepthWith, le_iInf_iff, Subtype.forall]

/-- The least depth is finite exactly when some formula computes the function. -/
theorem minDepthWith_ne_top_iff :
    minDepthWith I cost f ≠ ⊤ ↔ ∃ F : Formula σ n, F.Computes I f := by
  rw [minDepthWith, ENat.iInf_natCast_ne_top, nonempty_subtype]

/-- When some formula computes the function, the least depth is attained. -/
theorem exists_depthWith_eq_minDepthWith (h : ∃ F : Formula σ n, F.Computes I f) :
    ∃ F : Formula σ n, F.Computes I f ∧ (F.depthWith cost : ℕ∞) = minDepthWith I cost f := by
  have : Nonempty {F : Formula σ n // F.Computes I f} := nonempty_subtype.2 h
  obtain ⟨⟨F, hF⟩, hmin⟩ := ENat.exists_eq_iInf
    fun F : {F : Formula σ n // F.Computes I f} => (F.1.depthWith cost : ℕ∞)
  exact ⟨F, hF, hmin⟩

end MinDepthWith

/-- A formula is synthesized with one gate for each operation node. -/
theorem synthesis_eval (I : Interpretation σ U) (F : Formula σ n) :
    Synthesis I (inputs n) {F.eval I} F.size := by
  induction F with
  | input i => exact Synthesis.of_mem ⟨i, rfl⟩
  | gate op args ih => exact Synthesis.gate_of_syntheses op _ _ ih

/-! ### Substitution -/

/-- Substitute the formula `s i` for every leaf labelled by input `i`: the bind of formulas as a
free monad. -/
def bind {m : ℕ} : Formula σ n → (Fin n → Formula σ m) → Formula σ m
  | input i, s => s i
  | gate op args, s => gate op fun j => (args j).bind s

variable {m : ℕ}

/-- Substituting `s` into an input leaf `input i` yields `s i`. -/
@[simp] theorem input_bind (i : Fin n) (s : Fin n → Formula σ m) : (input i).bind s = s i :=
  rfl

/-- Substituting `s` into an operation node substitutes `s` into each argument. -/
@[simp] theorem gate_bind (op : σ.Op) (args : Fin (σ.Arity op) → Formula σ n)
    (s : Fin n → Formula σ m) : (gate op args).bind s = gate op fun j => (args j).bind s :=
  rfl

/-- Evaluating `F.bind s` on `x` evaluates `F` on the values of the substituted formulas `s i`. -/
@[simp] theorem eval_bind (I : Interpretation σ U) (F : Formula σ n) (s : Fin n → Formula σ m)
    (x : Fin m → U) : (F.bind s).eval I x = F.eval I fun i => (s i).eval I x := by
  induction F with
  | input i => rfl
  | gate op args ih => simp only [gate_bind, eval_gate, ih]

/-- Substituting each input leaf for itself leaves a formula unchanged. -/
@[simp] theorem bind_input (F : Formula σ n) : F.bind input = F := by
  induction F with
  | input i => rfl
  | gate op args ih => simp only [gate_bind, ih]

/-- Substitution of formulas is associative. -/
@[simp] theorem bind_assoc {k : ℕ} (F : Formula σ n) (s : Fin n → Formula σ m)
    (t : Fin m → Formula σ k) : (F.bind s).bind t = F.bind fun i => (s i).bind t := by
  induction F with
  | input i => rfl
  | gate op args ih => simp only [gate_bind, ih]

/-- Substituting for each input a formula with at most one leaf does not raise the leaf size. -/
theorem leafSize_bind_le {s : Fin n → Formula σ m} (hs : ∀ i, (s i).leafSize ≤ 1)
    (F : Formula σ n) : (F.bind s).leafSize ≤ F.leafSize := by
  induction F with
  | input i => exact hs i
  | gate op args ih =>
    rw [gate_bind, leafSize_gate, leafSize_gate]
    exact Finset.sum_le_sum fun j _ => ih j

/-- Substituting formulas of depth at most `c` for the inputs raises the depth by at most `c`. -/
theorem depth_bind_le {s : Fin n → Formula σ m} {c : ℕ} (hs : ∀ i, (s i).depth ≤ c)
    (F : Formula σ n) : (F.bind s).depth ≤ F.depth + c := by
  induction F with
  | input i => simpa using hs i
  | gate op args ih =>
    rw [gate_bind, depth_gate, depth_gate]
    have : (Finset.univ.sup fun j => ((args j).bind s).depth) ≤
        (Finset.univ.sup fun j => (args j).depth) + c :=
      Finset.sup_le fun j _ => (ih j).trans (Nat.add_le_add_right
        (Finset.le_sup (f := fun j => (args j).depth) (Finset.mem_univ j)) c)
    omega

/-- Substituting formulas of at most `c` operation nodes for the inputs adds at most `c` nodes for
each leaf. -/
theorem size_bind_le {s : Fin n → Formula σ m} {c : ℕ} (hs : ∀ i, (s i).size ≤ c)
    (F : Formula σ n) : (F.bind s).size ≤ F.size + F.leafSize * c := by
  induction F with
  | input i => simpa using hs i
  | gate op args ih =>
    rw [gate_bind, size_gate, size_gate, leafSize_gate, Finset.sum_mul]
    have := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => ih j
    rw [Finset.sum_add_distrib] at this
    omega

/-- The formula reading input `f i` where `F` reads input `i`. -/
def rename (f : Fin n → Fin m) (F : Formula σ n) : Formula σ m :=
  F.bind fun i => input (f i)

/-- Renaming the inputs of `F` by `f` evaluates `F` on `x ∘ f`. -/
@[simp] theorem eval_rename (I : Interpretation σ U) (f : Fin n → Fin m) (F : Formula σ n)
    (x : Fin m → U) : (F.rename f).eval I x = F.eval I (x ∘ f) := by
  simp [rename, Function.comp_def]

/-- Renaming the inputs keeps the leaf size. -/
@[simp] theorem leafSize_rename (f : Fin n → Fin m) (F : Formula σ n) :
    (F.rename f).leafSize = F.leafSize := by
  induction F with
  | input i => rfl
  | gate op args ih => simp only [rename, gate_bind, leafSize_gate] at ih ⊢; simp only [ih]

/-- Renaming the inputs by `f` and then by `g` renames them by `g ∘ f`. -/
@[simp] theorem rename_rename {k : ℕ} (f : Fin n → Fin m) (g : Fin m → Fin k) (F : Formula σ n) :
    (F.rename f).rename g = F.rename (g ∘ f) := by
  simp [rename]

/-- A formula on `n` inputs as one on `n + 1` inputs that ignores the last. -/
def lift (F : Formula σ n) : Formula σ (n + 1) :=
  F.rename Fin.castSucc

/-- `C` with the formula `K` in place of its last input. -/
def substLast (C : Formula σ (n + 1)) (K : Formula σ n) : Formula σ n :=
  C.bind (Fin.snoc (α := fun _ => Formula σ n) input K)

/-- `F.lift` evaluates on `y` by restricting `y` to the first `n` inputs. -/
@[simp] theorem eval_lift (I : Interpretation σ U) (F : Formula σ n) (y : Fin (n + 1) → U) :
    F.lift.eval I y = F.eval I fun i => y i.castSucc :=
  eval_rename I _ F y

/-- Lifting a formula to `n + 1` inputs preserves its leaf size. -/
@[simp] theorem leafSize_lift (F : Formula σ n) : F.lift.leafSize = F.leafSize :=
  leafSize_rename _ F

/-- `C.substLast K` evaluates on `x` by extending `x` with `K.eval I x` at the last input. -/
@[simp] theorem eval_substLast (I : Interpretation σ U) (C : Formula σ (n + 1)) (K : Formula σ n)
    (x : Fin n → U) : (C.substLast K).eval I x = C.eval I (Fin.snoc x (K.eval I x)) := by
  rw [substLast, eval_bind]
  congr 1
  funext i
  induction i using Fin.lastCases with
  | last => simp
  | cast i => simp

/-- Substituting for the last input of `F.lift` recovers `F`. -/
@[simp] theorem lift_substLast (F : Formula σ n) (K : Formula σ n) : F.lift.substLast K = F := by
  simp [lift, rename, substLast]

/-- Substituting `K` for the last input in `input (Fin.last n)` yields `K`. -/
@[simp] theorem input_last_substLast (K : Formula σ n) : (input (Fin.last n)).substLast K = K := by
  simp [substLast]

/-- Substituting for the last input leaves an earlier input leaf `input i.castSucc` as `input i`. -/
@[simp] theorem input_castSucc_substLast (i : Fin n) (K : Formula σ n) :
    (input i.castSucc).substLast K = input i := by
  simp [substLast]

/-- Substituting into an operation node substitutes into its arguments. -/
theorem gate_substLast (op : σ.Op) (args : Fin (σ.Arity op) → Formula σ (n + 1))
    (K : Formula σ n) : (gate op args).substLast K = gate op fun j => (args j).substLast K :=
  rfl

/-! ### Formulas as circuits -/

/-- A formula as a circuit: an input leaf is a wire, and an operation node is a gate on the
circuits of its arguments, side by side. -/
def toCircuit : Formula σ n → Circuit σ n 1
  | input i => Circuit.wiring σ fun _ => i
  | gate op args => (Circuit.oneGate op id).comp (Circuit.pi fun a => (args a).toCircuit)

/-- The single output of `F.toCircuit` evaluates to `F.eval I x`. -/
@[simp] theorem eval_toCircuit (I : Interpretation σ U) (F : Formula σ n) (x : Fin n → U)
    (j : Fin 1) : F.toCircuit.eval I x j = F.eval I x := by
  induction F generalizing j with
  | input i => rfl
  | gate op args ih =>
    rw [toCircuit, Circuit.eval_comp, Circuit.eval_oneGate, Circuit.eval_pi, eval_gate]
    exact congrArg (I op) (funext fun a => ih a 0)

/-- The circuit of a formula computes what the formula computes. -/
theorem Computes.toCircuit {I : Interpretation σ U} {F : Formula σ n} {f : (Fin n → U) → U}
    (hF : F.Computes I f) : F.toCircuit.Computes I (single f) := fun x => by
  funext j
  rw [eval_toCircuit, computes_iff.1 hF]
  rfl

/-- Compilation preserves the sum of arbitrary operation weights exactly. -/
theorem cost_toCircuit (weight : σ.Op → ℕ) (F : Formula σ n) :
    F.toCircuit.program.cost weight = F.cost weight := by
  induction F with
  | input => rfl
  | gate op args ih =>
    rw [toCircuit, Circuit.cost_program_comp, Circuit.cost_program_pi,
      Circuit.cost_program_oneGate, cost_gate]
    simp only [ih]

/-- The circuit of a formula has one gate for each operation node. -/
@[simp] theorem size_toCircuit (F : Formula σ n) : F.toCircuit.size = F.size := by
  simpa only [Program.cost_const, one_mul, cost_one] using F.cost_toCircuit (fun _ => 1)

/-- With costs, the circuit of a formula is no deeper than the formula. -/
theorem depthWith_toCircuit_le (cost : σ.Op → ℕ) (F : Formula σ n) :
    F.toCircuit.depthWith cost ≤ F.depthWith cost := by
  induction F with
  | input i => exact (Circuit.depthWith_le_iff cost _).2 fun _ => le_rfl
  | gate op args ih =>
    rw [toCircuit, depthWith_gate, add_comm]
    exact (Circuit.depthWith_comp_le _ _ _).trans (Nat.add_le_add
      (Circuit.depthWith_oneGate _ _ _).le (Circuit.depthWith_pi_le _ _ fun a => (ih a).trans
        (Finset.le_sup (f := fun a => (args a).depthWith cost) (Finset.mem_univ a))))

/-- The circuit of a formula is no deeper than the formula. -/
theorem depth_toCircuit_le (F : Formula σ n) : F.toCircuit.depth ≤ F.depth := by
  simpa only [Circuit.depthWith_one, depthWith_one] using depthWith_toCircuit_le 1 F

end Formula

end Cslib.Circuits
