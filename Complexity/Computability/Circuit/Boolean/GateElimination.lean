/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Parity
public import Complexity.Foundations.Data.BitString.PartialAssignment
public import Complexity.Computability.Circuit.Program
public import Mathlib.Logic.Relation

/-!
# Gate elimination: parity needs `3 (n - 1)` binary gates

A De Morgan circuit computing the parity of `n` bits has at least `3 (n - 1)` AND and OR gates,
however many negations and constants it uses (`three_mul_le_cost_of_computes_parity`). This is
Schnorr's bound [Schnorr1974], [Jukna, Section 1.6][Jukna2012]. It is attained by chaining
`x ⊕ y = (x ∨ y) ∧ ¬(x ∧ y)`, which spends three binary gates on each bit after the first
(`exists_computes_parity`), so `3 (n - 1)` is the exact count (`isLeast_cost_parity`). It is the
prototypical *gate-elimination* argument: fixing one bit suitably makes three binary gates
superfluous and leaves the parity of the other bits, possibly negated.

The proof does not rewrite circuits. For a restriction (partial assignment) `ρ` it counts the
*nonredundant* gates: AND and OR gates whose function, once the bits fixed by `ρ` are hardwired, is
neither constant, nor a literal, nor one of its arguments up to negation
(`GateElimination.NonRedundant`). Fixing more bits never makes a redundant gate nonredundant
(`GateElimination.nonRedundant_update_subset`). Every nonredundant gate survives the simplifications
of the textbook proof, so their number is a lower bound on the number of binary gates, and it is
what each step of the proof decreases.

The step follows Schnorr. Consider the nonredundant gates from which a chain of nonredundant gates,
negations and gates that compute one of their arguments up to negation leads to the output. The
first of them reads two different bits `xᵢ` and `xⱼ`, each of which, suitably fixed, makes it
constant. Another of them reads `xᵢ`: otherwise fixing `xⱼ` would make the output ignore `xᵢ`.
Fixing `xᵢ` then makes three of them redundant: the first gate, the other reader of `xᵢ`, and a
gate reading the first one, or reading the other reader of `xᵢ` if that is the same gate.

## Main definitions

* `Cslib.Circuits.Boolean.GateElimination.EqUpToNeg`,
  `Cslib.Circuits.Boolean.GateElimination.IsConstOrLiteral`: equality of Boolean functions up to
  negation, and functions that are constant or a literal.
* `Cslib.Circuits.Boolean.GateElimination.restricted`: the function of a wire under a restriction.
* `Cslib.Circuits.Boolean.GateElimination.NonRedundant`,
  `Cslib.Circuits.Boolean.GateElimination.nonRedundant`: the predicate and finite set of
  nonredundant binary gates under a restriction.

## Main results

* `Cslib.Circuits.Boolean.three_mul_le_cost_of_computes_parity`: a circuit computing the parity of
  `n` bits has at least `3 (n - 1)` AND and OR gates.
* `Cslib.Circuits.Boolean.isLeast_cost_parity`: and some circuit has exactly that many.
* `Cslib.Circuits.Boolean.three_mul_le_complexity_parity`: the circuit complexity of parity is at
  least `3 (n - 1)`.

## References

* [C.-P. Schnorr, *Zwei lineare untere Schranken für die Komplexität Boolescher
  Funktionen*][Schnorr1974]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Finset Function Relation BitString

variable {n g : ℕ}

namespace GateElimination

/-! ### Constants, literals and negations -/

section Functions

variable {φ ψ χ : BooleanFunction n} {i : Fin n}

/-- `φ` is `ψ` or its negation. -/
def EqUpToNeg (φ ψ : BooleanFunction n) : Prop :=
  ∃ c, ∀ x, φ x = (ψ x ^^ c)

/-- `φ` is constant or a literal. -/
def IsConstOrLiteral (φ : BooleanFunction n) : Prop :=
  IsConst φ ∨ ∃ i, EqUpToNeg φ (· i)

/-- Every Boolean function is equal to itself up to negation. -/
@[refl] theorem EqUpToNeg.refl (φ : BooleanFunction n) : EqUpToNeg φ φ :=
  ⟨false, fun _ => (Bool.xor_false _).symm⟩

/-- Equality up to negation is symmetric. -/
@[symm] theorem EqUpToNeg.symm (h : EqUpToNeg φ ψ) : EqUpToNeg ψ φ := by
  obtain ⟨c, h⟩ := h
  exact ⟨c, fun x => by rw [h x, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]⟩

/-- Equality up to negation is transitive. -/
@[trans] theorem EqUpToNeg.trans (h₁ : EqUpToNeg φ ψ) (h₂ : EqUpToNeg ψ χ) : EqUpToNeg φ χ := by
  obtain ⟨c, h₁⟩ := h₁
  obtain ⟨d, h₂⟩ := h₂
  exact ⟨d ^^ c, fun x => by rw [h₁ x, h₂ x, Bool.xor_assoc]⟩

private theorem EqUpToNeg.isConst (h : EqUpToNeg φ ψ) (hψ : IsConst ψ) : IsConst φ := by
  obtain ⟨c, h⟩ := h
  exact fun x y => by rw [h, h, hψ x y]

private theorem EqUpToNeg.isConstOrLiteral (h : EqUpToNeg φ ψ) (hψ : IsConstOrLiteral ψ) :
    IsConstOrLiteral φ :=
  hψ.imp h.isConst fun ⟨i, hi⟩ => ⟨i, h.trans hi⟩

private theorem EqUpToNeg.dependsOn {s : Set (Fin n)} (h : EqUpToNeg φ ψ) (hψ : DependsOn ψ s) :
    DependsOn φ s := by
  obtain ⟨c, h⟩ := h
  exact fun x y hxy => by rw [h, h, hψ hxy]

private theorem EqUpToNeg.comp_right (h : EqUpToNeg φ ψ) (f : BitString n → BitString n) :
    EqUpToNeg (φ ∘ f) (ψ ∘ f) := by
  obtain ⟨c, h⟩ := h
  exact ⟨c, fun x => h _⟩

private theorem isConstOrLiteral_literal (i : Fin n) :
    IsConstOrLiteral fun x : BitString n => x i :=
  Or.inr ⟨i, EqUpToNeg.refl _⟩

/-- A function of bit `i` alone is constant or a literal. -/
private theorem isConstOrLiteral_of_eq_comp (f : Bool → Bool) (h : ∀ x, φ x = f (x i)) :
    IsConstOrLiteral φ := by
  cases h0 : f false <;> cases h1 : f true
  · exact Or.inl fun x y => by rw [h, h]; cases x i <;> cases y i <;> simp [h0, h1]
  · exact Or.inr ⟨i, false, fun x => by simp only [h]; cases x i <;> simp [h0, h1]⟩
  · exact Or.inr ⟨i, true, fun x => by simp only [h]; cases x i <;> simp [h0, h1]⟩
  · exact Or.inl fun x y => by rw [h, h]; cases x i <;> cases y i <;> simp [h0, h1]

/-- Hardwiring bits keeps constants and literals. -/
private theorem IsConstOrLiteral.comp_fill (h : IsConstOrLiteral φ)
    (ρ : PartialAssignment (Fin n)) :
    IsConstOrLiteral (φ ∘ ρ.fill) := by
  rcases h with h | ⟨i, c, h⟩
  · exact Or.inl fun x y => h _ _
  · cases hi : ρ i with
    | none => exact Or.inr ⟨i, c, fun x => by simp [h, hi]⟩
    | some b => exact Or.inl fun x y => by simp [h, hi]

/-- A constant or a literal is bit `i` up to negation or ignores it. -/
private theorem IsConstOrLiteral.eqUpToNeg_or_dependsOn (h : IsConstOrLiteral φ) (i : Fin n) :
    EqUpToNeg φ (· i) ∨ DependsOn φ {i}ᶜ := by
  rcases h with h | ⟨u, hu⟩
  · exact Or.inr fun x y _ => h x y
  · by_cases hui : u = i
    · exact Or.inl (hui ▸ hu)
    · exact Or.inr (hu.dependsOn fun x y hxy => hxy u (by simpa using hui))

end Functions

/-! ### Gates -/

section Line

variable (ℓ : Line signature n g) (G : Wire n g → BooleanFunction n)

/-- The function of the gate `ℓ`, from the functions `G` of the wires. -/
private def lineFunction : BooleanFunction n :=
  fun x => interpretation ℓ.op fun s => G (ℓ.wires s) x

private theorem fin_two : ∀ s : Fin (signature.Arity Op.and), s = 0 ∨ s = 1 := by
  decide

/-- A negation or constant gate is constant or its argument up to negation. -/
private theorem isConst_or_eqUpToNeg_of_not_isBinary (h : ¬ℓ.op.IsBinary) :
    IsConst (lineFunction ℓ G) ∨ ∃ s, EqUpToNeg (lineFunction ℓ G) (G (ℓ.wires s)) := by
  obtain ⟨op, wires⟩ := ℓ
  cases op with
  | const c => exact Or.inl fun _ _ => rfl
  | not => exact Or.inr ⟨0, true, fun x => (Bool.xor_true _).symm⟩
  | and => exact absurd Op.isBinary_and h
  | or => exact absurd Op.isBinary_or h

/-- A binary gate with a constant argument is one of its arguments up to negation: the constant
one or the other one. -/
private theorem exists_eqUpToNeg_of_isConst (h : ℓ.op.IsBinary) {s : Fin (signature.Arity ℓ.op)}
    (hs : IsConst (G (ℓ.wires s))) : ∃ t, EqUpToNeg (lineFunction ℓ G) (G (ℓ.wires t)) := by
  obtain ⟨op, wires⟩ := ℓ
  obtain ⟨c, hc⟩ := isConst_iff_exists_forall_eq.1 hs
  rcases Op.isBinary_iff.1 h with rfl | rfl <;> rcases fin_two s with rfl | rfl <;>
    simp only at hc <;> cases c
  -- AND with a false argument is that argument; with a true one, the other argument.
  exacts [⟨0, false, fun x => by simp [lineFunction, interpretation, hc]⟩,
    ⟨1, false, fun x => by simp [lineFunction, interpretation, hc]⟩,
    ⟨1, false, fun x => by simp [lineFunction, interpretation, hc]⟩,
    ⟨0, false, fun x => by simp [lineFunction, interpretation, hc]⟩,
    ⟨1, false, fun x => by simp [lineFunction, interpretation, hc]⟩,
    ⟨0, false, fun x => by simp [lineFunction, interpretation, hc]⟩,
    ⟨0, false, fun x => by simp [lineFunction, interpretation, hc]⟩,
    ⟨1, false, fun x => by simp [lineFunction, interpretation, hc]⟩]

/-- A gate whose arguments are constant is constant. -/
private theorem isConst_of_forall_isConst (h : ∀ s, IsConst (G (ℓ.wires s))) :
    IsConst (lineFunction ℓ G) := fun x y => by
  simp only [lineFunction]
  congr 1
  funext s
  exact h s x y

/-- A gate whose arguments depend only on `S` depends only on `S`. -/
private theorem dependsOn_of_forall_dependsOn {S : Set (Fin n)}
    (h : ∀ s, DependsOn (G (ℓ.wires s)) S) : DependsOn (lineFunction ℓ G) S := fun x y hxy => by
  simp only [lineFunction]
  congr 1
  funext s
  exact h s hxy

/-- A binary gate on two constants or literals that is neither constant, nor a literal, nor one
of its arguments up to negation reads two different bits, each of which, suitably fixed, makes it
constant. -/
private theorem exists_two_literals (h : ℓ.op.IsBinary)
    (hG : ∀ s, IsConstOrLiteral (G (ℓ.wires s))) (hℓ : ¬IsConstOrLiteral (lineFunction ℓ G))
    (hs : ∀ s, ¬EqUpToNeg (lineFunction ℓ G) (G (ℓ.wires s))) :
    ∃ s i j, i ≠ j ∧ EqUpToNeg (G (ℓ.wires s)) (· i) ∧
      (∃ a d, ∀ x, x i = a → lineFunction ℓ G x = d) ∧
        ∃ b d, ∀ x, x j = b → lineFunction ℓ G x = d := by
  have lit : ∀ s, ∃ i, EqUpToNeg (G (ℓ.wires s)) (· i) := fun s =>
    (hG s).resolve_left fun hc =>
      let ⟨t, ht⟩ := exists_eqUpToNeg_of_isConst ℓ G h hc
      hs t ht
  obtain ⟨op, wires⟩ := ℓ
  rcases Op.isBinary_iff.1 h with rfl | rfl
  · obtain ⟨i, c, hi⟩ := lit 0
    obtain ⟨j, d, hj⟩ := lit 1
    simp only at hi hj
    have hij : i ≠ j := by
      rintro rfl
      exact hℓ (isConstOrLiteral_of_eq_comp (i := i) (fun t => (t ^^ c) && (t ^^ d)) fun x => by
        simp only [lineFunction, interpretation, hi, hj])
    exact ⟨0, i, j, hij, ⟨c, hi⟩,
      ⟨c, false, fun x hx => by simp [lineFunction, interpretation, hi, hx]⟩,
      ⟨d, false, fun x hx => by simp [lineFunction, interpretation, hj, hx]⟩⟩
  · obtain ⟨i, c, hi⟩ := lit 0
    obtain ⟨j, d, hj⟩ := lit 1
    simp only at hi hj
    have hij : i ≠ j := by
      rintro rfl
      exact hℓ (isConstOrLiteral_of_eq_comp (i := i) (fun t => (t ^^ c) || (t ^^ d)) fun x => by
        simp only [lineFunction, interpretation, hi, hj])
    exact ⟨0, i, j, hij, ⟨c, hi⟩,
      ⟨!c, true, fun x hx => by simp [lineFunction, interpretation, hi, hx]⟩,
      ⟨!d, true, fun x hx => by simp [lineFunction, interpretation, hj, hx]⟩⟩

end Line

/-! ### Restricted programs -/

section Restricted

variable (p : Program signature n g)

/-- The function computed at wire `w` once the bits fixed by `ρ` are hardwired. -/
def restricted (ρ : PartialAssignment (Fin n)) (w : Wire n g) : BooleanFunction n :=
  p.wireFunction interpretation w ∘ ρ.fill

/-- The restricted function at gate `k` applies the operation of line `k` to the restricted
functions of its input wires. -/
theorem restricted_gate_apply (ρ : PartialAssignment (Fin n)) (k : Fin g) (x : BitString n) :
    restricted p ρ (.gate k) x =
      interpretation (p.lines k).op fun s => restricted p ρ ((p.lines k).wires s) x := by
  simp only [restricted, comp_apply, Program.wireFunction_gate, Program.gateFunction_apply]
  rw [← p.lines_eval]
  rfl

private theorem restricted_gate (ρ : PartialAssignment (Fin n)) (k : Fin g) :
    restricted p ρ (.gate k) = lineFunction (p.lines k) (restricted p ρ) :=
  funext (restricted_gate_apply p ρ k)

private theorem isConstOrLiteral_restricted_input (ρ : PartialAssignment (Fin n)) (i : Fin n) :
    IsConstOrLiteral (restricted p ρ (.input i)) :=
  (isConstOrLiteral_literal i).comp_fill ρ

variable {p} {ρ : PartialAssignment (Fin n)} {i : Fin n}

/-- Fixing one more free bit is restricting the restricted function. -/
private theorem restricted_update (hi : ρ i = none) (b : Bool) (w : Wire n g) :
    restricted p (update ρ i (some b)) w =
      restricted p ρ w ∘ PartialAssignment.fill (update ρ i (some b)) := by
  funext x
  simp only [restricted, comp_apply, PartialAssignment.fill_fill_update hi]

private theorem restricted_update_of_ne_none (hi : ρ i ≠ none) (w : Wire n g) (x : BitString n)
    (c : Bool) : restricted p ρ w (update x i c) = restricted p ρ w x := by
  simp only [restricted, comp_apply, PartialAssignment.fill_update_of_ne_none hi]

/-- A wire that is another up to negation is constant when the other is, after fixing a bit. -/
private theorem isConst_update_of_eqUpToNeg (hi : ρ i = none) (a : Bool) {w w' : Wire n g}
    (h : EqUpToNeg (restricted p ρ w) (restricted p ρ w'))
    (hc : IsConst (restricted p (update ρ i (some a)) w')) :
    IsConst (restricted p (update ρ i (some a)) w) := by
  rw [restricted_update hi] at hc ⊢
  exact (h.comp_right _).isConst hc

/-- Fixing a free bit of the parity of all free bits leaves the parity of the others, possibly
negated. -/
private theorem restricted_update_of_parity {o : Wire n g} (hi : ρ i = none) (b : Bool) {c : Bool}
    (ho : ∀ x, restricted p ρ o x = (c ^^ parityOn ρ.free x)) (x : BitString n) :
    restricted p (update ρ i (some b)) o x =
      ((c ^^ b) ^^ parityOn (PartialAssignment.free (update ρ i (some b))) x) := by
  rw [restricted_update hi, comp_apply, ho,
    parityOn_eq_xor_erase (PartialAssignment.mem_free.2 hi), PartialAssignment.free_update,
    PartialAssignment.fill_of_eq_some (update_self ..), Bool.xor_assoc]
  congr 2
  refine parityOn_congr fun j hj => PartialAssignment.fill_of_eq_none ?_ x
  obtain ⟨hji, hj⟩ := mem_erase.1 hj
  rw [update_of_ne hji]
  exact PartialAssignment.mem_free.1 hj

end Restricted

/-! ### Nonredundant gates -/

section NonRedundant

variable (p : Program signature n g)

/-- Gate `k` is a *nonredundant* binary gate once the bits fixed by `ρ` are hardwired: an AND or
OR gate whose function is neither constant, nor a literal, nor one of its arguments up to
negation. -/
def NonRedundant (ρ : PartialAssignment (Fin n)) (k : Fin g) : Prop :=
  (p.lines k).op.IsBinary ∧ ¬IsConstOrLiteral (restricted p ρ (.gate k)) ∧
    ∀ s, ¬EqUpToNeg (restricted p ρ (.gate k)) (restricted p ρ ((p.lines k).wires s))

open scoped Classical in
/-- The nonredundant binary gates under `ρ`. -/
noncomputable def nonRedundant (ρ : PartialAssignment (Fin n)) : Finset (Fin g) :=
  {k | NonRedundant p ρ k}

variable {p} {ρ : PartialAssignment (Fin n)} {i : Fin n}

/-- Membership in `nonRedundant p ρ` is `NonRedundant p ρ`. -/
@[simp] theorem mem_nonRedundant {k : Fin g} : k ∈ nonRedundant p ρ ↔ NonRedundant p ρ k := by
  simp [nonRedundant]

variable (p ρ) in
/-- There are at most as many nonredundant gates as binary gates. -/
private theorem card_nonRedundant_le : #(nonRedundant p ρ) ≤ p.cost binaryCost := by
  rw [Program.cost_eq_sum]
  simp only [binaryCost_eq_ite, ← card_filter]
  exact card_le_card fun k hk => mem_filter.2 ⟨mem_univ _, (mem_nonRedundant.1 hk).1⟩

/-- Fixing one more bit only makes gates redundant. -/
theorem nonRedundant_update_subset (hi : ρ i = none) (b : Bool) :
    nonRedundant p (update ρ i (some b)) ⊆ nonRedundant p ρ := by
  intro k hk
  obtain ⟨hb, ht, hs⟩ := mem_nonRedundant.1 hk
  refine mem_nonRedundant.2 ⟨hb, fun h => ht ?_, fun s h => hs s ?_⟩
  · rw [restricted_update hi]
    exact h.comp_fill _
  · rw [restricted_update hi, restricted_update hi]
    exact h.comp_right _

/-- A gate that is not a nonredundant binary gate computes a constant, a literal, or one of its
arguments up to negation. -/
private theorem isConstOrLiteral_or_eqUpToNeg_of_not_nonRedundant {k : Fin g}
    (hk : ¬NonRedundant p ρ k) :
    IsConstOrLiteral (restricted p ρ (.gate k)) ∨
      ∃ s, EqUpToNeg (restricted p ρ (.gate k)) (restricted p ρ ((p.lines k).wires s)) := by
  by_cases hb : (p.lines k).op.IsBinary
  · simp only [NonRedundant, hb, true_and, not_and, not_forall, not_not] at hk
    by_cases ht : IsConstOrLiteral (restricted p ρ (.gate k))
    · exact Or.inl ht
    · exact Or.inr (hk ht)
  · rw [restricted_gate]
    exact (isConst_or_eqUpToNeg_of_not_isBinary _ _ hb).imp_left Or.inl

/-- A binary gate with a constant argument is redundant. -/
private theorem not_nonRedundant_of_isConst_wires {k : Fin g}
    {s : Fin (signature.Arity (p.lines k).op)}
    (h : IsConst (restricted p ρ ((p.lines k).wires s))) : ¬NonRedundant p ρ k := by
  rintro ⟨hb, -, hns⟩
  rw [restricted_gate] at hns
  obtain ⟨t, ht⟩ := exists_eqUpToNeg_of_isConst _ _ hb h
  exact hns t ht

end NonRedundant

/-! ### Wires that may matter -/

section Effective

variable (p : Program signature n g) (ρ : PartialAssignment (Fin n)) (o : Wire n g)

/-- Under `ρ`, wire `v` feeds wire `w` when `w` is a gate that reads `v` and is nonredundant or
computes `v` up to negation. -/
private def Feeds (v w : Wire n g) : Prop :=
  ∃ k s, w = .gate k ∧ v = (p.lines k).wires s ∧
    (NonRedundant p ρ k ∨ EqUpToNeg (restricted p ρ (.gate k)) (restricted p ρ v))

/-- The wires from which a chain of `Feeds` leads to `o`. This over-approximates the wires whose
value matters to `o`. -/
private def Effective (v : Wire n g) : Prop :=
  ReflTransGen (Feeds p ρ) v o

variable {p ρ o}

private theorem Effective.self : Effective p ρ o o :=
  ReflTransGen.refl

private theorem Effective.arg {k : Fin g} (hk : Effective p ρ o (.gate k))
    {s : Fin (signature.Arity (p.lines k).op)}
    (h : NonRedundant p ρ k ∨
      EqUpToNeg (restricted p ρ (.gate k)) (restricted p ρ ((p.lines k).wires s))) :
    Effective p ρ o ((p.lines k).wires s) :=
  ReflTransGen.head ⟨k, s, rfl, rfl, h⟩ hk

/-- A wire that may matter to `o` computes the function of `o` up to negation, or is read, up to
negation, by a nonredundant gate that may matter to `o`. -/
private theorem Effective.eqUpToNeg_or_exists {v : Wire n g} (h : Effective p ρ o v) :
    EqUpToNeg (restricted p ρ o) (restricted p ρ v) ∨
      ∃ k, NonRedundant p ρ k ∧ Effective p ρ o (.gate k) ∧
        ∃ s, EqUpToNeg (restricted p ρ ((p.lines k).wires s)) (restricted p ρ v) := by
  induction h using ReflTransGen.head_induction_on with
  | refl => exact Or.inl (EqUpToNeg.refl _)
  | head hfeeds hrest ih =>
    obtain ⟨k, s, rfl, rfl, hk⟩ := hfeeds
    rcases hk with hk | hk
    · exact Or.inr ⟨k, hk, hrest, s, EqUpToNeg.refl _⟩
    · rcases ih with ih | ⟨k', hk', hk'e, s', ih⟩
      · exact Or.inl (ih.trans hk)
      · exact Or.inr ⟨k', hk', hk'e, s', ih.trans hk⟩

/-- A wire that may matter to `o` and comes before every nonredundant gate that may matter to `o`
computes a constant or a literal. -/
private theorem Effective.isConstOrLiteral {v : Wire n g} (hv : Effective p ρ o v)
    (hlow : ∀ k, NonRedundant p ρ k → Effective p ρ o (.gate k) → ∀ j, v = .gate j → j < k) :
    IsConstOrLiteral (restricted p ρ v) := by
  induction v using p.wire_induction with
  | input i => exact isConstOrLiteral_restricted_input p ρ i
  | gate k ih =>
    have hk : ¬NonRedundant p ρ k := fun hk => lt_irrefl k (hlow k hk hv k rfl)
    rcases isConstOrLiteral_or_eqUpToNeg_of_not_nonRedundant hk with h | ⟨s, h⟩
    · exact h
    · exact h.isConstOrLiteral (ih s (hv.arg (Or.inr h)) fun k' hk' he j hj =>
        (p.lt_of_lines_wires_eq_gate k s j hj).trans (hlow k' hk' he k rfl))

/-- If fixing bit `j` makes gate `k₀` constant, and no nonredundant gate that may matter to `o`,
other than `k₀`, reads bit `i` up to negation, then every wire that may matter to `o` is bit `i`
up to negation, or ignores bit `i` once bit `j` is fixed. -/
private theorem Effective.eqUpToNeg_or_dependsOn {i j : Fin n} (hj : ρ j = none) (b : Bool)
    {k₀ : Fin g} (hk₀ : IsConst (restricted p (update ρ j (some b)) (.gate k₀)))
    (hread : ∀ k, NonRedundant p ρ k → Effective p ρ o (.gate k) → k ≠ k₀ →
      ∀ s, ¬EqUpToNeg (restricted p ρ ((p.lines k).wires s)) (· i))
    {v : Wire n g} (hv : Effective p ρ o v) :
    EqUpToNeg (restricted p ρ v) (· i) ∨ DependsOn (restricted p (update ρ j (some b)) v) {i}ᶜ := by
  induction v using p.wire_induction with
  | input u =>
    rw [restricted_update hj]
    exact ((isConstOrLiteral_restricted_input p ρ u).eqUpToNeg_or_dependsOn i).imp_right
      (PartialAssignment.dependsOn_comp_fill · _)
  | gate k ih =>
    by_cases hkk : k = k₀
    · subst hkk
      exact Or.inr fun x y _ => hk₀ x y
    by_cases hk : NonRedundant p ρ k
    · refine Or.inr ?_
      rw [restricted_gate]
      exact dependsOn_of_forall_dependsOn _ _ fun s =>
        (ih s (hv.arg (Or.inl hk))).resolve_left (hread k hk hv hkk s)
    · rcases isConstOrLiteral_or_eqUpToNeg_of_not_nonRedundant hk with h | ⟨s, h⟩
      · rw [restricted_update hj]
        exact (h.eqUpToNeg_or_dependsOn i).imp_right (PartialAssignment.dependsOn_comp_fill · _)
      · rcases ih s (hv.arg (Or.inr h)) with h' | h'
        · exact Or.inl (h.trans h')
        · refine Or.inr ?_
          rw [restricted_update hj] at h' ⊢
          exact (h.comp_right _).dependsOn h'

end Effective

/-! ### Eliminating three gates -/

section Step

variable {p : Program signature n g} {ρ : PartialAssignment (Fin n)} {o : Wire n g}

private theorem not_isConstOrLiteral_parityOn {s : Finset (Fin n)} (hs : 2 ≤ #s) (c : Bool) :
    ¬IsConstOrLiteral fun x => c ^^ parityOn s x := by
  rintro (h | ⟨u, hu⟩)
  · exact not_isConst_parityOn (card_pos.1 (by omega)) c h
  · obtain ⟨v, hv, hvu⟩ := exists_mem_ne hs u
    exact not_dependsOn_parityOn hv c (hu.dependsOn fun x y hxy => hxy u (by simpa using hvu.symm))

/-- The first nonredundant gate that may matter to `o` reads constants or literals. -/
private theorem exists_first (hF : ¬IsConstOrLiteral (restricted p ρ o)) :
    ∃ k₀, NonRedundant p ρ k₀ ∧ Effective p ρ o (.gate k₀) ∧
      ∀ s, IsConstOrLiteral (restricted p ρ ((p.lines k₀).wires s)) := by
  by_cases hne : ∃ k, NonRedundant p ρ k ∧ Effective p ρ o (.gate k)
  · obtain ⟨k₀, ⟨hN, hE⟩, hmin⟩ := WellFounded.has_min wellFounded_lt
      {k | NonRedundant p ρ k ∧ Effective p ρ o (.gate k)} hne
    refine ⟨k₀, hN, hE, fun s => (hE.arg (Or.inl hN)).isConstOrLiteral fun k hk he j hj => ?_⟩
    exact (p.lt_of_lines_wires_eq_gate k₀ s j hj).trans_le (not_lt.1 (hmin k ⟨hk, he⟩))
  · push Not at hne
    exact absurd (Effective.self.isConstOrLiteral fun k hk he => absurd he (hne k hk)) hF

/-- If fixing bit `j` makes the gate `k₀` constant, some other nonredundant gate that may matter
to the output reads bit `i`: otherwise, the output would ignore bit `i` once bit `j` is fixed. -/
private theorem exists_second_reader {c : Bool}
    (ho : ∀ x, restricted p ρ o x = (c ^^ parityOn ρ.free x)) (hV : 2 ≤ #ρ.free)
    {k₀ : Fin g} {i j : Fin n} {b : Bool} (hij : i ≠ j) (hi : ρ i = none) (hj : ρ j = none)
    (hk₀ : IsConst (restricted p (update ρ j (some b)) (.gate k₀))) :
    ∃ k₁, NonRedundant p ρ k₁ ∧ Effective p ρ o (.gate k₁) ∧ k₁ ≠ k₀ ∧
      ∃ s, EqUpToNeg (restricted p ρ ((p.lines k₁).wires s)) (· i) := by
  by_contra! hno
  rcases Effective.self.eqUpToNeg_or_dependsOn hj b hk₀ hno with h | h
  · exact not_isConstOrLiteral_parityOn hV c
      (funext ho ▸ h.isConstOrLiteral (isConstOrLiteral_literal i))
  · refine not_dependsOn_parityOn (s := PartialAssignment.free (update ρ j (some b))) (i := i)
      (by simp [hij, hi]) (c ^^ b) ?_
    rwa [funext (restricted_update_of_parity hj b ho)] at h

/-- If fixing bit `i` makes a gate that may matter to `o` constant, but not `o`, it makes redundant
a nonredundant gate that may matter to `o` and reads that gate up to negation. -/
private theorem exists_reader_of_isConst {i : Fin n} (hi : ρ i = none) (a : Bool) {k : Fin g}
    (hk : Effective p ρ o (.gate k)) (hc : IsConst (restricted p (update ρ i (some a)) (.gate k)))
    (hout : ¬IsConst (restricted p (update ρ i (some a)) o)) :
    ∃ k', NonRedundant p ρ k' ∧ Effective p ρ o (.gate k') ∧
      (∃ s, EqUpToNeg (restricted p ρ ((p.lines k').wires s)) (restricted p ρ (.gate k))) ∧
        ¬NonRedundant p (update ρ i (some a)) k' := by
  rcases hk.eqUpToNeg_or_exists with h | ⟨k', hk'N, hk'E, s, hs⟩
  · exact absurd (isConst_update_of_eqUpToNeg hi a h hc) hout
  · exact ⟨k', hk'N, hk'E, ⟨s, hs⟩,
      not_nonRedundant_of_isConst_wires (isConst_update_of_eqUpToNeg hi a hs hc)⟩

private theorem card_add_three_le {α : Type*} [DecidableEq α] {s t : Finset α} {a b c : α}
    (hst : s ⊆ t) (ha : a ∈ t \ s) (hb : b ∈ t \ s) (hc : c ∈ t \ s) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : #s + 3 ≤ #t := by
  have hsub : s ∪ {a, b, c} ⊆ t := union_subset hst (by
    simp [insert_subset_iff, (mem_sdiff.1 ha).1, (mem_sdiff.1 hb).1, (mem_sdiff.1 hc).1])
  have hdisj : Disjoint s {a, b, c} := disjoint_left.2 fun x hx hx' => by
    simp only [mem_insert, mem_singleton] at hx'
    rcases hx' with rfl | rfl | rfl
    exacts [(mem_sdiff.1 ha).2 hx, (mem_sdiff.1 hb).2 hx, (mem_sdiff.1 hc).2 hx]
  have := card_le_card hsub
  rwa [card_union_of_disjoint hdisj, card_eq_three.2 ⟨a, b, c, hab, hac, hbc, rfl⟩] at this

variable (p o) in
/-- **Schnorr's elimination step.** If, under `ρ`, the wire `o` computes the parity of all free
bits, possibly negated, and at least two bits are free, then fixing one free bit suitably makes at
least three nonredundant gates redundant. -/
private theorem exists_card_add_three_le {c : Bool}
    (ho : ∀ x, restricted p ρ o x = (c ^^ parityOn ρ.free x)) (hV : 2 ≤ #ρ.free) :
    ∃ i b, ρ i = none ∧
      #(nonRedundant p (update ρ i (some b))) + 3 ≤ #(nonRedundant p ρ) := by
  classical
  have hF : ¬IsConstOrLiteral (restricted p ρ o) :=
    (funext ho).symm ▸ not_isConstOrLiteral_parityOn hV c
  -- The first nonredundant gate that may matter reads two different bits.
  obtain ⟨k₀, hk₀N, hk₀E, hargs⟩ := exists_first hF
  have hk₀N' := hk₀N
  obtain ⟨hbin, hnt, hns⟩ := hk₀N'
  rw [restricted_gate] at hnt hns
  obtain ⟨s₀, i, j, hij, hs₀, ⟨a, d₁, hka⟩, ⟨b, d₂, hkb⟩⟩ :=
    exists_two_literals _ _ hbin hargs hnt hns
  rw [← restricted_gate] at hka hkb hnt
  have hi : ρ i = none := by
    by_contra h
    obtain ⟨e, he⟩ := hs₀
    have := restricted_update_of_ne_none (p := p) h ((p.lines k₀).wires s₀) (fun _ => false) true
    rw [he, he] at this
    simp at this
  have hfix {l : Fin n} (hl : ρ l = none) {e d : Bool}
      (h : ∀ x, x l = e → restricted p ρ (.gate k₀) x = d) :
      IsConst (restricted p (update ρ l (some e)) (.gate k₀)) :=
    IsConst.of_forall_eq d fun x => by
      rw [restricted_update hl, comp_apply]
      exact h _ (PartialAssignment.fill_of_eq_some (update_self ..) x)
  have hj : ρ j = none := by
    by_contra h
    refine hnt (Or.inl (IsConst.of_forall_eq d₂ fun x => ?_))
    rw [← restricted_update_of_ne_none h _ x b]
    exact hkb _ (update_self ..)
  -- Another nonredundant gate that may matter reads bit `i`.
  obtain ⟨k₁, hk₁N, hk₁E, hk₁₀, s₁, hs₁⟩ := exists_second_reader ho hV hij hi hj (hfix hj hkb)
  -- Fixing bit `i` makes the first gate, the other reader of bit `i`, and a third gate redundant.
  have hk₀' := hfix hi hka
  have hout : ¬IsConst (restricted p (update ρ i (some a)) o) := by
    rw [funext (restricted_update_of_parity hi a ho)]
    exact not_isConst_parityOn ⟨j, by simp [hij.symm, hj]⟩ _
  have hconst_i {w : Wire n g} (h : EqUpToNeg (restricted p ρ w) (· i)) :
      IsConst (restricted p (update ρ i (some a)) w) := by
    obtain ⟨e, he⟩ := h
    refine IsConst.of_forall_eq (a ^^ e) fun x => ?_
    simp only [restricted_update hi, comp_apply, he]
    rw [PartialAssignment.fill_of_eq_some (update_self ..)]
  obtain ⟨k₂, hk₂N, hk₂E, ⟨s₂, hs₂⟩, hk₂'⟩ := exists_reader_of_isConst hi a hk₀E hk₀' hout
  have hk₂₀ : k₂ ≠ k₀ := by
    rintro rfl
    exact hk₀N.2.2 s₂ hs₂.symm
  obtain ⟨k₃, hk₃N, hk₃', hk₃₀, hk₃₁⟩ : ∃ k, NonRedundant p ρ k ∧
      ¬NonRedundant p (update ρ i (some a)) k ∧ k ≠ k₀ ∧ k ≠ k₁ := by
    by_cases hk₂₁ : k₂ = k₁
    · subst hk₂₁
      -- The other reader of bit `i` also reads the first gate, so it becomes constant.
      have hsne : s₁ ≠ s₂ := by
        rintro rfl
        exact hk₀N.2.1 ((hs₂.symm.trans hs₁).isConstOrLiteral (isConstOrLiteral_literal i))
      have hc : IsConst (restricted p (update ρ i (some a)) (.gate k₂)) := by
        rw [restricted_gate]
        refine isConst_of_forall_isConst _ _ fun t => ?_
        rcases hk₂N.1.eq_or_eq hsne t with rfl | rfl
        · exact hconst_i hs₁
        · exact isConst_update_of_eqUpToNeg hi a hs₂ hk₀'
      obtain ⟨k₃, hk₃N, -, ⟨s₃, hs₃⟩, hk₃'⟩ := exists_reader_of_isConst hi a hk₂E hc hout
      refine ⟨k₃, hk₃N, hk₃', ?_, ?_⟩
      · rintro rfl
        exact hk₂N.2.1 (hs₃.symm.isConstOrLiteral (hargs s₃))
      · rintro rfl
        exact hk₃N.2.2 s₃ hs₃.symm
    · exact ⟨k₂, hk₂N, hk₂', hk₂₀, hk₂₁⟩
  refine ⟨i, a, hi, card_add_three_le (nonRedundant_update_subset hi a) (a := k₀) (b := k₁)
    (c := k₃) ?_ ?_ ?_ hk₁₀.symm hk₃₀.symm hk₃₁.symm⟩
  · exact mem_sdiff.2 ⟨mem_nonRedundant.2 hk₀N, fun h =>
      (mem_nonRedundant.1 h).2.1 (Or.inl hk₀')⟩
  · exact mem_sdiff.2 ⟨mem_nonRedundant.2 hk₁N, fun h =>
      not_nonRedundant_of_isConst_wires (hconst_i hs₁) (mem_nonRedundant.1 h)⟩
  · exact mem_sdiff.2 ⟨mem_nonRedundant.2 hk₃N, fun h => hk₃' (mem_nonRedundant.1 h)⟩

variable (p o) in
/-- Under a restriction leaving `m + 1` bits free for which the wire `o` computes their parity,
possibly negated, at least `3 m` gates are nonredundant. -/
private theorem three_mul_le_card_nonRedundant (m : ℕ) (ρ : PartialAssignment (Fin n)) (c : Bool)
    (hρ : #ρ.free = m + 1) (ho : ∀ x, restricted p ρ o x = (c ^^ parityOn ρ.free x)) :
    3 * m ≤ #(nonRedundant p ρ) := by
  induction m generalizing ρ c with
  | zero => simp
  | succ m ih =>
    obtain ⟨i, b, hi, hcard⟩ := exists_card_add_three_le p o ho (by omega)
    have := ih (update ρ i (some b)) (c ^^ b)
      (by
        rw [PartialAssignment.free_update, card_erase_of_mem (PartialAssignment.mem_free.2 hi)]
        omega)
      (restricted_update_of_parity hi b ho)
    omega

end Step

end GateElimination

open GateElimination in
/-- **Schnorr's bound.** A De Morgan circuit computing the parity of `n` bits has at least
`3 (n - 1)` AND and OR gates, however many negations and constants it uses. -/
theorem three_mul_le_cost_of_computes_parity {C : Circuit signature n 1}
    (hC : C.Computes interpretation (single (parity n))) :
    3 * (n - 1) ≤ C.program.cost binaryCost := by
  rcases n with _ | n
  · simp
  · refine (three_mul_le_card_nonRedundant C.program (C.outputs 0) n (fun _ => none) false
      (by simp) fun x => ?_).trans (card_nonRedundant_le _ _)
    simp only [restricted, comp_apply, PartialAssignment.fill_none, PartialAssignment.free_none,
      Bool.false_xor]
    exact congrFun (hC x) 0

/-- The least number of AND and OR gates in a De Morgan circuit computing the parity of `n` bits
is `3 (n - 1)`. -/
theorem isLeast_cost_parity (n : ℕ) :
    IsLeast {k | ∃ C : Circuit signature n 1,
      C.Computes interpretation (single (parity n)) ∧ C.program.cost binaryCost = k}
      (3 * (n - 1)) := by
  refine ⟨?_, fun k ⟨C, hC, hk⟩ => hk ▸ three_mul_le_cost_of_computes_parity hC⟩
  rcases n with _ | n
  · exact exists_computes_parity_zero
  · obtain ⟨C, hC, hcost, -⟩ := exists_computes_parity n
    exact ⟨C, hC, by simpa using hcost⟩

/-- A De Morgan circuit computing the parity of `n` bits has at least `3 (n - 1)` gates. -/
theorem three_mul_le_size_of_computes_parity {C : Circuit signature n 1}
    (hC : C.Computes interpretation (single (parity n))) : 3 * (n - 1) ≤ C.size :=
  (three_mul_le_cost_of_computes_parity hC).trans (Program.cost_binaryCost_le _)

/-- The De Morgan circuit complexity of the parity of `n` bits is at least `3 (n - 1)`. -/
theorem three_mul_le_complexity_parity (n : ℕ) :
    3 * (n - 1) ≤ complexity interpretation (single (parity n)) :=
  le_complexity_iff.2 fun _ hC => three_mul_le_size_of_computes_parity hC

end Cslib.Circuits.Boolean
