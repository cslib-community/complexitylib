/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Data.Finset.Card

/-!
# Gates over the full binary basis

The gates of fair semi-circuits (`Cslib.Circuits.Boolean.SemiCircuit`). An *argument* is a
constant or an internal value named by a natural number, a *literal* is an argument, possibly
negated, and a *gate* applies an operation `Bool → Bool → Bool` of the full binary basis `B₂` to
two arguments. Rerouting the internal value `v` to a literal (`Gate.subst`) absorbs the negation
into the operation and preserves the value of the gate on assignments giving `v` the value of the
literal (`Gate.eval_subst`).

A gate with a constant argument or two equal arguments is *degenerate* and computes a constant or
a literal of an argument (`Gate.eval_lit`). Of the sixteen operations of `B₂`, the *affine* ones
(`IsAffineOp`) have no product term; every other operation, an *AND-type* one, has the form
`(a + α)(b + β) + γ` (`exists_and_form`), takes both values (`exists_eq_of_not_isAffineOp'`), and
is constant on a line of `𝔽₂²` on which any other operation is constant (`exists_line_const`).
An affine operation that is neither constant nor a projection is XOR-type (`exists_xor_form`).

## Main definitions

* `Cslib.Circuits.Boolean.SemiCircuit.Arg`, `Cslib.Circuits.Boolean.SemiCircuit.Lit`,
  `Cslib.Circuits.Boolean.SemiCircuit.Gate`: arguments, literals and gates.
* `Cslib.Circuits.Boolean.SemiCircuit.Gate.subst`: rerouting an internal value to a literal.
* `Cslib.Circuits.Boolean.SemiCircuit.Gate.Degenerate`,
  `Cslib.Circuits.Boolean.SemiCircuit.Gate.lit`: degenerate gates and the literal they compute.
* `Cslib.Circuits.Boolean.SemiCircuit.IsAffineOp`,
  `Cslib.Circuits.Boolean.SemiCircuit.IsUnaryOp`: affine operations and projections.

## Main results

* `Cslib.Circuits.Boolean.SemiCircuit.Gate.eval_subst`: rerouting preserves evaluation.
* `Cslib.Circuits.Boolean.SemiCircuit.exists_and_form`,
  `Cslib.Circuits.Boolean.SemiCircuit.exists_xor_form`,
  `Cslib.Circuits.Boolean.SemiCircuit.exists_line_const`: the operations of `B₂`.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
* [M. G. Find, A. Golovnev, E. A. Hirsch and A. S. Kulikov, *A better-than-3n lower bound for the
  circuit complexity of an explicit function*][FindGolovnevHirschKulikov2016]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.SemiCircuit

open Finset

/-! ### Arguments, literals and gates -/

/-- An argument of a gate: a constant or the internal value with the given name. -/
inductive Arg where
  /-- A constant. -/
  | const (b : Bool)
  /-- An internal value. -/
  | node (i : ℕ)
  deriving DecidableEq

namespace Arg

/-- The value of an argument under an assignment of the internal values. -/
def eval (val : ℕ → Bool) : Arg → Bool
  | const b => b
  | node i => val i

@[simp] theorem eval_const (val : ℕ → Bool) (b : Bool) : (const b).eval val = b := rfl

@[simp] theorem eval_node (val : ℕ → Bool) (i : ℕ) : (node i).eval val = val i := rfl

/-- The argument `node v` replaced by the argument of the literal `ℓ`. -/
def substArg (a : Arg) (v : ℕ) (target : Arg) : Arg :=
  if a = node v then target else a

/-- Changing the assignment away from the internal values an argument reads keeps its value. -/
theorem eval_congr {a : Arg} {val val' : ℕ → Bool} (h : ∀ i, a = node i → val i = val' i) :
    a.eval val = a.eval val' := by
  cases a with
  | const b => rfl
  | node i => exact h i rfl

end Arg

/-- A literal: an argument, negated when `neg` holds. Outputs and reroutings are literals. -/
structure Lit where
  /-- The argument. -/
  arg : Arg
  /-- Whether the argument is negated. -/
  neg : Bool
  deriving DecidableEq

namespace Lit

/-- The value of a literal. -/
def eval (ℓ : Lit) (val : ℕ → Bool) : Bool :=
  ℓ.arg.eval val ^^ ℓ.neg

/-- The constant literal `b`. -/
def const (b : Bool) : Lit := ⟨.const b, false⟩

/-- The literal `t ⊕ c` of the internal value `t`. -/
def node (t : ℕ) (c : Bool) : Lit := ⟨.node t, c⟩

@[simp] theorem eval_const (b : Bool) (val : ℕ → Bool) : (const b).eval val = b := by
  simp [const, eval]

@[simp] theorem eval_node (t : ℕ) (c : Bool) (val : ℕ → Bool) :
    (node t c).eval val = (val t ^^ c) := rfl

/-- Reroute the internal value `v` in a literal to the literal `ℓ`. -/
def subst (o : Lit) (v : ℕ) (ℓ : Lit) : Lit :=
  if o.arg = .node v then ⟨ℓ.arg, o.neg ^^ ℓ.neg⟩ else o

theorem eval_subst {o : Lit} {v : ℕ} {ℓ : Lit} {val : ℕ → Bool} (h : val v = ℓ.eval val) :
    (o.subst v ℓ).eval val = o.eval val := by
  unfold subst
  split_ifs with ho
  · simp only [eval, ho, Arg.eval_node, h]
    cases ℓ.arg.eval val <;> cases o.neg <;> cases ℓ.neg <;> rfl
  · rfl

/-- The literal reads the internal value `t`. -/
def Reads (o : Lit) (t : ℕ) : Prop :=
  o.arg = .node t

theorem eval_congr {o : Lit} {val val' : ℕ → Bool} (h : ∀ i, o.Reads i → val i = val' i) :
    o.eval val = o.eval val' := by
  unfold eval
  rw [Arg.eval_congr h]

theorem not_reads_subst {o : Lit} {v : ℕ} {ℓ : Lit} (hℓ : ¬ ℓ.Reads v) :
    ¬ (o.subst v ℓ).Reads v := by
  unfold subst Reads
  split_ifs with ho
  · exact hℓ
  · exact ho

theorem reads_of_reads_subst {o : Lit} {v : ℕ} {ℓ : Lit} {z : ℕ} (h : (o.subst v ℓ).Reads z) :
    o.Reads z ∨ (o.Reads v ∧ ℓ.Reads z) := by
  unfold subst Reads at *
  split_ifs at h with ho
  · exact Or.inr ⟨ho, h⟩
  · exact Or.inl h

theorem subst_of_not_reads {o : Lit} {v : ℕ} {ℓ : Lit} (h : ¬ o.Reads v) : o.subst v ℓ = o :=
  ite_eq_right (show ¬ o.arg = .node v from h)

/-- A literal with `v` rerouted to a literal not reading `v` evaluates as the literal on the
assignment giving `v` the value of the rerouting literal. -/
theorem eval_subst_update {o : Lit} {v : ℕ} {ℓ : Lit} (hℓ : ¬ ℓ.Reads v) (val : ℕ → Bool) :
    (o.subst v ℓ).eval val = o.eval (Function.update val v (ℓ.eval val)) := by
  rw [← eval_subst (o := o) (show Function.update val v (ℓ.eval val) v = _ by
    rw [Function.update_self]
    exact eval_congr fun i hi => (Function.update_of_ne (by rintro rfl; exact hℓ hi) _ _).symm)]
  exact eval_congr fun i hi =>
    (Function.update_of_ne (by rintro rfl; exact not_reads_subst hℓ hi) _ _).symm

end Lit

/-- A gate of the acyclic part: an operation of the full binary basis `B₂` applied to two
arguments. -/
structure Gate where
  /-- The operation of the gate. -/
  op : Bool → Bool → Bool
  /-- The first argument. -/
  left : Arg
  /-- The second argument. -/
  right : Arg

namespace Gate

/-- The value of a gate, given the values of its arguments. -/
def eval (g : Gate) (val : ℕ → Bool) : Bool :=
  g.op (g.left.eval val) (g.right.eval val)

/-- The gate reads the internal value `t`. -/
def Reads (g : Gate) (t : ℕ) : Prop :=
  g.left = .node t ∨ g.right = .node t

instance (g : Gate) : DecidablePred g.Reads :=
  fun _ => inferInstanceAs (Decidable (_ ∨ _))

/-- A gate's value depends only on the internal values it reads. -/
theorem eval_congr {g : Gate} {val val' : ℕ → Bool} (h : ∀ i, g.Reads i → val i = val' i) :
    g.eval val = g.eval val' := by
  unfold eval
  rw [Arg.eval_congr (a := g.left) (fun i hi => h i (Or.inl hi)),
    Arg.eval_congr (a := g.right) (fun i hi => h i (Or.inr hi))]

/-- The negation absorbed into the operation when the argument `a` is rerouted. -/
def substNeg (a : Arg) (v : ℕ) (ℓ : Lit) : Bool :=
  if a = .node v then ℓ.neg else false

/-- Reroute the internal value `v` to the literal `ℓ`: arguments `node v` read the argument of
`ℓ`, and the negation of `ℓ` is absorbed into the operation. -/
def subst (g : Gate) (v : ℕ) (ℓ : Lit) : Gate where
  op x y := g.op (x ^^ substNeg g.left v ℓ) (y ^^ substNeg g.right v ℓ)
  left := g.left.substArg v ℓ.arg
  right := g.right.substArg v ℓ.arg

theorem eval_substArg {a : Arg} {v : ℕ} {ℓ : Lit} {val : ℕ → Bool} (h : val v = ℓ.eval val) :
    ((a.substArg v ℓ.arg).eval val ^^ substNeg a v ℓ) = a.eval val := by
  unfold Arg.substArg substNeg
  split_ifs with ha
  · rw [ha, Arg.eval_node, h, Lit.eval]
  · simp

/-- Rerouting `v` to a literal with the value of `v` preserves the value of every gate. -/
theorem eval_subst {g : Gate} {v : ℕ} {ℓ : Lit} {val : ℕ → Bool} (h : val v = ℓ.eval val) :
    (g.subst v ℓ).eval val = g.eval val := by
  simp only [eval, subst, eval_substArg h]

private theorem substArg_eq_node_of_ne {a : Arg} {v z : ℕ} {target : Arg} (hzv : z ≠ v)
    (hzt : target ≠ .node z) : a.substArg v target = .node z ↔ a = .node z := by
  unfold Arg.substArg
  by_cases ha : a = .node v
  · rw [ite_eq_left ha, ha]
    exact ⟨fun h => absurd h hzt, fun h => absurd (Arg.node.inj h) (Ne.symm hzv)⟩
  · rw [ite_eq_right ha]

private theorem eq_node_of_substArg_eq_node {a : Arg} {v z : ℕ} {target : Arg}
    (h : a.substArg v target = .node z) : a = .node z ∨ (a = .node v ∧ target = .node z) := by
  unfold Arg.substArg at h
  by_cases ha : a = .node v
  · rw [ite_eq_left ha] at h; exact Or.inr ⟨ha, h⟩
  · rw [ite_eq_right ha] at h; exact Or.inl h

theorem reads_subst_of_ne {g : Gate} {v : ℕ} {ℓ : Lit} {z : ℕ} (hzv : z ≠ v)
    (hzℓ : ℓ.arg ≠ .node z) : (g.subst v ℓ).Reads z ↔ g.Reads z := by
  unfold Reads subst
  simp only [substArg_eq_node_of_ne hzv hzℓ]

theorem reads_of_reads_subst {g : Gate} {v : ℕ} {ℓ : Lit} {z : ℕ} (h : (g.subst v ℓ).Reads z) :
    g.Reads z ∨ (g.Reads v ∧ ℓ.arg = .node z) := by
  unfold Reads subst at *
  rcases h with h | h <;> rcases eq_node_of_substArg_eq_node h with h' | ⟨h', h''⟩
  · exact Or.inl (Or.inl h')
  · exact Or.inr ⟨Or.inl h', h''⟩
  · exact Or.inl (Or.inr h')
  · exact Or.inr ⟨Or.inr h', h''⟩

theorem not_reads_subst {g : Gate} {v : ℕ} {ℓ : Lit} (hℓ : ℓ.arg ≠ .node v) :
    ¬ (g.subst v ℓ).Reads v := by
  intro h
  simp only [Reads, subst, Arg.substArg] at h
  rcases h with h | h <;> split_ifs at h with h' <;> first | exact hℓ h | exact h' h

theorem eval_subst_of_not_reads {g : Gate} {v : ℕ} {ℓ : Lit} (h : ¬ g.Reads v) (val : ℕ → Bool) :
    (g.subst v ℓ).eval val = g.eval val := by
  unfold Reads at h
  push Not at h
  simp only [eval, subst, Arg.substArg, substNeg, ite_eq_right h.1, ite_eq_right h.2,
    Bool.xor_false]

/-- A gate with `v` rerouted to a literal not reading `v` evaluates as the gate on the assignment
giving `v` the value of the literal. -/
theorem eval_subst_update {g : Gate} {v : ℕ} {ℓ : Lit} (hℓ : ℓ.arg ≠ .node v) (val : ℕ → Bool) :
    (g.subst v ℓ).eval val = g.eval (Function.update val v (ℓ.eval val)) := by
  have hℓu : ℓ.eval (Function.update val v (ℓ.eval val)) = ℓ.eval val :=
    Lit.eval_congr fun i hi => Function.update_of_ne (by rintro rfl; exact hℓ hi) _ _
  rw [← eval_subst (g := g) (show Function.update val v (ℓ.eval val) v = _ by
    rw [hℓu]; exact Function.update_self _ _ _)]
  exact eval_congr fun i hi =>
    (Function.update_of_ne (by rintro rfl; exact not_reads_subst hℓ hi) _ _).symm

@[simp] theorem eval_subst_const (g : Gate) (v : ℕ) (b : Bool) (val : ℕ → Bool) :
    (g.subst v (Lit.const b)).eval val = g.eval (Function.update val v b) := by
  rw [eval_subst_update (by simp [Lit.const]), Lit.eval_const]

/-- A gate reading two distinct internal values reads exactly them. -/
theorem args_of_reads {g : Gate} {z z' : ℕ} (hzz : z ≠ z') (hz : g.Reads z)
    (hz' : g.Reads z') : (g.left = .node z ∧ g.right = .node z') ∨
      (g.left = .node z' ∧ g.right = .node z) := by
  unfold Gate.Reads at hz hz'
  rcases hz with hz | hz <;> rcases hz' with hz' | hz'
  · exact absurd (Arg.node.inj (hz.symm.trans hz')) hzz
  · exact Or.inl ⟨hz, hz'⟩
  · exact Or.inr ⟨hz', hz⟩
  · exact absurd (Arg.node.inj (hz.symm.trans hz')) hzz

/-- A gate whose arguments are `x` and `y`, in either order, reads both. -/
theorem reads_of_args {g : Gate} {x y : ℕ} (h : (g.left = .node x ∧ g.right = .node y) ∨
    (g.left = .node y ∧ g.right = .node x)) : g.Reads x ∧ g.Reads y := by
  rcases h with ⟨hl, hr⟩ | ⟨hl, hr⟩
  exacts [⟨Or.inl hl, Or.inr hr⟩, ⟨Or.inr hr, Or.inl hl⟩]

/-- A gate reading two distinct internal values reads nothing else. -/
theorem eq_or_eq_of_reads {g : Gate} {a b i : ℕ} (hab : a ≠ b) (ha : g.Reads a)
    (hb : g.Reads b) (hi : g.Reads i) : i = a ∨ i = b := by
  rcases args_of_reads hab ha hb with ⟨hl, hr⟩ | ⟨hl, hr⟩ <;> rcases hi with hi | hi
  · exact Or.inl (Arg.node.inj (hi.symm.trans hl))
  · exact Or.inr (Arg.node.inj (hi.symm.trans hr))
  · exact Or.inr (Arg.node.inj (hi.symm.trans hl))
  · exact Or.inl (Arg.node.inj (hi.symm.trans hr))

/-- A gate reads at most two internal values. -/
theorem card_filter_reads_le (g : Gate) (s : Finset ℕ) : (s.filter g.Reads).card ≤ 2 := by
  by_contra h
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.1 (not_le.1 h)
  rcases eq_or_eq_of_reads hab (Finset.mem_filter.1 ha).2 (Finset.mem_filter.1 hb).2
    (Finset.mem_filter.1 hc).2 with h | h
  · exact hac h.symm
  · exact hbc h.symm

/-- The value of a gate reading the internal values `a` and `b`. -/
theorem eval_of_args {g : Gate} {a b : ℕ} (ha : g.left = .node a) (hb : g.right = .node b)
    (val : ℕ → Bool) : g.eval val = g.op (val a) (val b) := by
  rw [eval, ha, hb, Arg.eval_node, Arg.eval_node]

end Gate

/-! ### Degenerate gates -/

/-- The literal computed by a gate with a constant argument or two equal arguments. -/
def Gate.lit (g : Gate) : Lit :=
  match g.left with
  | .const b =>
    if g.op b false = g.op b true then Lit.const (g.op b false) else ⟨g.right, g.op b false⟩
  | .node t =>
    match g.right with
    | .const b =>
      if g.op false b = g.op true b then Lit.const (g.op false b) else ⟨.node t, g.op false b⟩
    | .node _ =>
      if g.op false false = g.op true true then Lit.const (g.op false false)
      else ⟨.node t, g.op false false⟩

/-- The gate has a constant argument or two equal arguments. -/
def Gate.Degenerate (g : Gate) : Prop :=
  (∃ b, g.left = .const b) ∨ (∃ b, g.right = .const b) ∨ g.left = g.right

/-- A Boolean function of one bit is a constant or a literal. -/
private theorem unary_cases (h : Bool → Bool) (x : Bool) :
    h x = if h false = h true then h false else (x ^^ h false) := by
  cases x <;> cases h0 : h false <;> cases h1 : h true <;> simp_all

/-- The literal computing the Boolean function `h` of one bit applied to the argument `a`. -/
def unaryLit (h : Bool → Bool) (a : Arg) : Lit :=
  if h false = h true then Lit.const (h false) else ⟨a, h false⟩

theorem eval_unaryLit (h : Bool → Bool) (a : Arg) (val : ℕ → Bool) :
    h (a.eval val) = (unaryLit h a).eval val := by
  rw [unary_cases h (a.eval val)]
  unfold unaryLit
  split_ifs <;> simp [Lit.eval, Lit.const]

theorem reads_of_unaryLit_reads {h : Bool → Bool} {a : Arg} {t : ℕ}
    (hr : (unaryLit h a).Reads t) : a = .node t := by
  unfold unaryLit at hr
  split_ifs at hr
  · simp [Lit.Reads, Lit.const] at hr
  · exact hr

theorem Gate.eval_lit {g : Gate} (hg : g.Degenerate) (val : ℕ → Bool) :
    g.eval val = g.lit.eval val := by
  obtain ⟨op, l, r⟩ := g
  unfold Degenerate at hg
  unfold eval
  cases l with
  | const b =>
    simp only [lit, Arg.eval_const]
    rw [unary_cases (op b) (r.eval val)]
    split_ifs <;> simp [Lit.eval, Lit.const]
  | node t =>
    cases r with
    | const b =>
      simp only [lit, Arg.eval_const, Arg.eval_node]
      rw [unary_cases (fun x => op x b) (val t)]
      split_ifs <;> simp [Lit.eval, Lit.const]
    | node t' =>
      simp only at hg
      rcases hg with ⟨b, hb⟩ | ⟨b, hb⟩ | hb
      · cases hb
      · cases hb
      · cases hb
        simp only [lit, Arg.eval_node]
        rw [unary_cases (fun x => op x x) (val t)]
        split_ifs <;> simp [Lit.eval, Lit.const]

theorem Gate.reads_of_lit_reads {g : Gate} {t : ℕ} (h : g.lit.Reads t) : g.Reads t := by
  obtain ⟨op, l, r⟩ := g
  unfold Reads
  cases l with
  | const b =>
    simp only [lit] at h
    split_ifs at h
    · simp [Lit.Reads, Lit.const] at h
    · exact Or.inr h
  | node s =>
    cases r with
    | const b =>
      simp only [lit] at h
      split_ifs at h
      · simp [Lit.Reads, Lit.const] at h
      · exact Or.inl h
    | node s' =>
      simp only [lit] at h
      split_ifs at h
      · simp [Lit.Reads, Lit.const] at h
      · exact Or.inl h

theorem Gate.degenerate_subst {g : Gate} (hg : g.Degenerate) (v : ℕ) (ℓ : Lit) :
    (g.subst v ℓ).Degenerate := by
  unfold Gate.Degenerate at *
  change (∃ b, g.left.substArg v ℓ.arg = .const b) ∨ (∃ b, g.right.substArg v ℓ.arg = .const b) ∨
    g.left.substArg v ℓ.arg = g.right.substArg v ℓ.arg
  rcases hg with ⟨b, hb⟩ | ⟨b, hb⟩ | hb
  · exact Or.inl ⟨b, by rw [hb]; rfl⟩
  · exact Or.inr (Or.inl ⟨b, by rw [hb]; rfl⟩)
  · exact Or.inr (Or.inr (by rw [hb]))

/-! ### Operations of the full binary basis -/

/-- An operation of `B₂` is affine when its multilinear expression has no product term. -/
def IsAffineOp (op : Bool → Bool → Bool) : Prop :=
  (op false false ^^ op true false ^^ op false true ^^ op true true) = false

instance (op : Bool → Bool → Bool) : Decidable (IsAffineOp op) :=
  inferInstanceAs (Decidable (_ = _))

/-- An AND-type operation becomes constant when either argument takes a suitable value. -/
private theorem exists_eq_of_not_isAffineOp {op : Bool → Bool → Bool} (h : ¬ IsAffineOp op) :
    (∃ b, op b false = op b true) ∧ (∃ b, op false b = op true b) := by
  unfold IsAffineOp at h
  constructor
  · by_cases h0 : op false false = op false true
    · exact ⟨false, h0⟩
    · by_cases h1 : op true false = op true true
      · exact ⟨true, h1⟩
      · exfalso
        apply h
        revert h0 h1
        generalize op false false = a; generalize op true false = b
        generalize op false true = c; generalize op true true = d
        revert a b c d; decide
  · by_cases h0 : op false false = op true false
    · exact ⟨false, h0⟩
    · by_cases h1 : op false true = op true true
      · exact ⟨true, h1⟩
      · exfalso
        apply h
        revert h0 h1
        generalize op false false = a; generalize op true false = b
        generalize op false true = c; generalize op true true = d
        revert a b c d; decide

/-- An AND-type gate reading two internal values becomes constant once the value `w` is fixed
suitably. -/
theorem Gate.exists_const_of_not_isAffineOp {g : Gate} (hg : ¬ IsAffineOp g.op) {a w : ℕ}
    (hargs : (g.left = .node a ∧ g.right = .node w) ∨ (g.left = .node w ∧ g.right = .node a)) :
    ∃ b c, ∀ val : ℕ → Bool, val w = b → g.eval val = c := by
  obtain ⟨⟨bl, hbl⟩, ⟨br, hbr⟩⟩ := exists_eq_of_not_isAffineOp hg
  rcases hargs with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · refine ⟨br, g.op false br, fun val hw => ?_⟩
    rw [Gate.eval_of_args hl hr, hw]
    cases val a
    · rfl
    · exact hbr.symm
  · refine ⟨bl, g.op bl false, fun val hw => ?_⟩
    rw [Gate.eval_of_args hl hr, hw]
    cases val a
    · rfl
    · exact hbl.symm

/-- The operation is a projection or a negated projection: `x ↦ c + x` or `y ↦ c + y`. -/
def IsUnaryOp (op : Bool → Bool → Bool) : Prop :=
  (op true false = !op false false ∧ op false true = op false false ∧
      op true true = !op false false) ∨
    (op true false = op false false ∧ op false true = !op false false ∧
      op true true = !op false false)

/-- An operation that is not a projection or a negated projection is constant on a diagonal
`{(c + a, a)}` for a suitable `c`, and likewise on `{(a, c + a)}`. -/
private theorem exists_diag_const (op : Bool → Bool → Bool) :
    ((∃ c, op c false = op (!c) true) ∧ (∃ c, op false c = op true (!c))) ∨ IsUnaryOp op := by
  by_cases h0 : op false false = op true true
  · exact Or.inl ⟨⟨false, h0⟩, ⟨false, h0⟩⟩
  · by_cases h1 : op true false = op false true
    · exact Or.inl ⟨⟨true, h1⟩, ⟨true, h1.symm⟩⟩
    · right
      unfold IsUnaryOp
      revert h0 h1
      generalize op false false = a₀; generalize op true false = b₀
      generalize op false true = c₀; generalize op true true = d₀
      revert a₀ b₀ c₀ d₀; decide

/-- An operation that is not a projection or a negated projection is constant on a diagonal: a
gate with such an operation reading `p` and `r` is constant once `p = r + c` for a suitable
`c`. -/
theorem Gate.exists_const_of_diag {g : Gate} (hg : ¬ IsUnaryOp g.op) {p r : ℕ}
    (hargs : (g.left = .node p ∧ g.right = .node r) ∨ (g.left = .node r ∧ g.right = .node p)) :
    ∃ c d, ∀ val : ℕ → Bool, val p = (val r ^^ c) → g.eval val = d := by
  rcases exists_diag_const g.op with ⟨⟨c₁, hc₁⟩, ⟨c₂, hc₂⟩⟩ | hun
  · rcases hargs with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · refine ⟨c₁, g.op c₁ false, fun val hp => ?_⟩
      rw [Gate.eval_of_args hl hr, hp]
      cases val r
      · simp
      · simpa using hc₁.symm
    · refine ⟨c₂, g.op false c₂, fun val hp => ?_⟩
      rw [Gate.eval_of_args hl hr, hp]
      cases val r
      · simp
      · simpa using hc₂.symm
  · exact absurd hun hg

/-- Every AND-type operation has the form `(a + α)(b + β) + γ`. -/
theorem exists_and_form {op : Bool → Bool → Bool} (h : ¬ IsAffineOp op) :
    ∃ α β γ : Bool, ∀ a b, op a b = (((a ^^ α) && (b ^^ β)) ^^ γ) := by
  have key : ∃ α β γ : Bool, op false false = ((α && β) ^^ γ) ∧
      op true false = (((!α) && β) ^^ γ) ∧ op false true = ((α && !β) ^^ γ) ∧
      op true true = (((!α) && !β) ^^ γ) := by
    unfold IsAffineOp at h
    revert h
    generalize op false false = a₀; generalize op true false = b₀
    generalize op false true = c₀; generalize op true true = d₀
    revert a₀ b₀ c₀ d₀; decide
  obtain ⟨α, β, γ, h0, h1, h2, h3⟩ := key
  refine ⟨α, β, γ, fun a b => ?_⟩
  cases a <;> cases b
  · rw [h0]; cases α <;> cases β <;> rfl
  · rw [h2]; cases α <;> cases β <;> rfl
  · rw [h1]; cases α <;> cases β <;> rfl
  · rw [h3]; cases α <;> cases β <;> rfl

/-- An AND-type operation takes both values. -/
theorem exists_eq_of_not_isAffineOp' {op : Bool → Bool → Bool} (h : ¬ IsAffineOp op) (δ : Bool) :
    ∃ a b, op a b = δ := by
  unfold IsAffineOp at h
  by_contra hne
  push Not at hne
  have key : ∀ δ a b c d : Bool, a ≠ δ → b ≠ δ → c ≠ δ → d ≠ δ →
      (a ^^ b ^^ c ^^ d) = false := by decide
  exact h (key δ _ _ _ _ (hne _ _) (hne _ _) (hne _ _) (hne _ _))

/-- An affine operation that is neither constant nor a projection or a negated projection is
XOR-type: `a + b + c`. -/
theorem exists_xor_form {op : Bool → Bool → Bool} (h : IsAffineOp op) (hu : ¬ IsUnaryOp op)
    (hc : ∃ a b, op a b ≠ op false false) : ∃ c, ∀ a b, op a b = (a ^^ b ^^ c) := by
  unfold IsAffineOp at h
  unfold IsUnaryOp at hu
  obtain ⟨a₁, b₁, hab⟩ := hc
  refine ⟨op false false, fun a b => ?_⟩
  revert h hu hab
  cases a₁ <;> cases b₁ <;> cases a <;> cases b <;>
  · generalize op false false = a₀; generalize op true false = b₀
    generalize op false true = c₀; generalize op true true = d₀
    revert a₀ b₀ c₀ d₀; decide

/-- Of two operations of two bits, one AND-type, both are constant on a common line of `𝔽₂²`:
`a = c`, `b = c` or `a = b + c` for a suitable constant `c`. -/
theorem exists_line_const {g h : Bool → Bool → Bool} (hg : ¬ IsAffineOp g) :
    (∃ c, (∀ b, g c b = g c false) ∧ ∀ b, h c b = h c false) ∨
    (∃ c, (∀ a, g a c = g false c) ∧ ∀ a, h a c = h false c) ∨
    (∃ c, (∀ b, g (b ^^ c) b = g c false) ∧ ∀ b, h (b ^^ c) b = h c false) := by
  unfold IsAffineOp at hg
  simp only [Bool.exists_bool, Bool.forall_bool, Bool.false_xor, Bool.true_xor, Bool.not_false,
    Bool.not_true]
  revert hg
  generalize g false false = a₀; generalize g true false = b₀
  generalize g false true = c₀; generalize g true true = d₀
  generalize h false false = a₁; generalize h true false = b₁
  generalize h false true = c₁; generalize h true true = d₁
  revert a₀ b₀ c₀ d₀ a₁ b₁ c₁ d₁; decide

/-- A gate reading the internal values `x` and `y` computes an operation of their values, which is
affine exactly when the operation of the gate is. -/
theorem Gate.exists_op_of_args {g : Gate} {x y : ℕ}
    (h : (g.left = .node x ∧ g.right = .node y) ∨ (g.left = .node y ∧ g.right = .node x)) :
    ∃ φ : Bool → Bool → Bool, (IsAffineOp φ ↔ IsAffineOp g.op) ∧
      ∀ val : ℕ → Bool, g.eval val = φ (val x) (val y) := by
  rcases h with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · exact ⟨g.op, Iff.rfl, fun val => Gate.eval_of_args hl hr val⟩
  · refine ⟨fun a b => g.op b a, ?_, fun val => Gate.eval_of_args hl hr val⟩
    unfold IsAffineOp
    beta_reduce
    generalize g.op false false = a₀; generalize g.op true false = b₀
    generalize g.op false true = c₀; generalize g.op true true = d₀
    revert a₀ b₀ c₀ d₀; decide

end Cslib.Circuits.Boolean.SemiCircuit
