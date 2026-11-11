/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.MapOp
public import Cslib.Computability.Circuit.Boolean.Basic
public import Cslib.Computability.Circuit.Complexity
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# The constant-free De Morgan basis

The basis of fan-in-two AND, fan-in-two OR and NOT, with no constant gates, is the circuit model of
Ilango, Loff and Oliveira [IlangoLoffOliveira2020, p. 22:3]: "A Boolean circuit consists of fan-in
two AND gates, fan-in two OR gates, and NOT gates", and its size is "the number of AND, OR, and
NOT gates". Here `Circuit.size` counts every gate, so the size of a circuit over
`Boolean.DeMorgan.signature` is exactly that number. cslib's `Boolean.signature` is the same basis
with the two constants added; the map `Boolean.DeMorgan.toBoolean` embeds the first in the second,
keeping sizes (`Circuit.size_mapOp`) and the computed function.

Without constants and without inputs no gate can be built (`Program.size_eq_zero_of_deMorgan`), so
no function on zero inputs has a circuit: the basis is not complete in cslib's sense
(`Boolean.DeMorgan.not_isComplete`), and complexities over it are taken in `ℕ∞` (`ecomplexity`).

`Boolean.DeMorganBasis I` packages what results stated for both bases use: a meaning-keeping map
from the constant-free basis into the signature of `I`, which supplies binary AND, binary OR and
unary NOT gates, together with a bound of two on every arity and at most five operations. It has
instances for the constant-free basis and for cslib's `Boolean.interpretation`. Only the first has
the size measure of the source: in the second a constant costs one gate, while without constants
it costs two (`x ∧ ¬x`), so results over cslib's basis are library variants of the source's.

## Main definitions

* `Cslib.Circuits.Boolean.DeMorgan.signature`, `Cslib.Circuits.Boolean.DeMorgan.interpretation`:
  the constant-free De Morgan basis and its Boolean meaning.
* `Cslib.Circuits.Boolean.DeMorgan.toBoolean`: its map into cslib's `Boolean.signature`.
* `Cslib.Circuits.Boolean.DeMorganBasis`: interpretations with AND, OR and NOT gates, fan-in at
  most two and at most five operations.

## Main results

* `Cslib.Circuits.ecomplexity_le_of_preserves`: a meaning-keeping map of signatures does not
  increase complexity.
* `Cslib.Circuits.Boolean.DeMorgan.ecomplexity_boolean_le`: complexity with constants is at most
  complexity without them.
* `Cslib.Circuits.Program.size_eq_zero_of_deMorgan`,
  `Cslib.Circuits.Boolean.DeMorgan.ecomplexity_eq_top`,
  `Cslib.Circuits.Boolean.DeMorgan.not_isComplete`: without inputs there are no gates and nothing
  to compute.

## References

* [R. Ilango, B. Loff, I. C. Oliveira, *NP-Hardness of Circuit Minimization for Multi-Output
  Functions*][IlangoLoffOliveira2020]
-/

public section

namespace Cslib.Circuits

universe v u

/-- A map of signatures that keeps the meaning of every operation does not increase complexity:
translating a circuit gate by gate keeps its size and its function. -/
theorem ecomplexity_le_of_preserves {σ τ : Signature.{v}} {U : Type u} {I : Interpretation σ U}
    {J : Interpretation τ U} (φ : σ.Hom τ) [φ.Preserves I J] {n m : ℕ}
    (f : (Fin n → U) → Fin m → U) : ecomplexity J f ≤ ecomplexity I f := by
  refine le_ecomplexity_iff.2 fun c hc => ?_
  exact (ecomplexity_le_of_computes (c.mapOp φ) hc.mapOp).trans_eq (by rw [Circuit.size_mapOp])

namespace Boolean

namespace DeMorgan

/-- Operations of the constant-free De Morgan basis. -/
inductive Op where
  /-- Negation. -/
  | not
  /-- Binary conjunction. -/
  | and
  /-- Binary disjunction. -/
  | or
  deriving DecidableEq

/-- The three operations of the constant-free basis. -/
instance : Fintype Op :=
  ⟨{.not, .and, .or}, fun op => by cases op <;> simp⟩

/-- The constant-free De Morgan signature: NOT is unary, AND and OR are binary. -/
abbrev signature : Signature where
  Op := Op
  Arity
    | .not => 1
    | .and | .or => 2

/-- The Boolean meaning of the constant-free De Morgan basis. -/
@[expose] def interpretation : Interpretation signature Bool
  | .not, x => !x 0
  | .and, x => x 0 && x 1
  | .or, x => x 0 || x 1

@[simp] theorem interpretation_not (x : Fin 1 → Bool) : interpretation .not x = !x 0 := rfl

@[simp] theorem interpretation_and (x : Fin 2 → Bool) :
    interpretation .and x = (x 0 && x 1) := rfl

@[simp] theorem interpretation_or (x : Fin 2 → Bool) : interpretation .or x = (x 0 || x 1) := rfl

/-- Every operation of the constant-free basis has at most two arguments. -/
theorem arity_le_two (op : Op) : signature.Arity op ≤ 2 := by
  cases op <;> decide

/-- The constant-free basis as a part of cslib's De Morgan basis with constants. -/
@[expose] def toBoolean : signature.Hom Boolean.signature where
  toFun
    | .not => .not
    | .and => .and
    | .or => .or
  arity_eq op := by cases op <;> rfl

/-- The embedding keeps the meaning of every operation. -/
instance : toBoolean.Preserves interpretation Boolean.interpretation :=
  ⟨fun op _ => by cases op <;> rfl⟩

/-- Complexity with the two constants is at most complexity without them. -/
theorem ecomplexity_boolean_le {n m : ℕ} (f : (Fin n → Bool) → Fin m → Bool) :
    ecomplexity Boolean.interpretation f ≤ ecomplexity interpretation f :=
  ecomplexity_le_of_preserves toBoolean f

end DeMorgan

end Boolean

/-- Without constants and without inputs no gate has an argument, so a program over the
constant-free De Morgan basis on zero inputs has no gates. -/
theorem Program.size_eq_zero_of_deMorgan :
    ∀ {g : ℕ}, Program Boolean.DeMorgan.signature 0 g → g = 0
  | _, .empty => rfl
  | _, .gate p line => by
    obtain rfl := Program.size_eq_zero_of_deMorgan p
    obtain ⟨op, wires⟩ := line
    have w : Wire 0 0 := wires ⟨0, by cases op <;> decide⟩
    cases w with
    | input i => exact i.elim0
    | gate i => exact i.elim0

namespace Boolean.DeMorgan

/-- A function on zero inputs with at least one value has no circuit over the constant-free basis.
-/
theorem ecomplexity_eq_top {m : ℕ} (hm : 0 < m) (f : (Fin 0 → Bool) → Fin m → Bool) :
    ecomplexity interpretation f = ⊤ := by
  refine not_ne_iff.1 fun h => ?_
  obtain ⟨⟨program, outputs⟩, -⟩ := ecomplexity_ne_top_iff.1 h
  obtain rfl := Program.size_eq_zero_of_deMorgan program
  cases outputs ⟨0, hm⟩ with
  | input i => exact i.elim0
  | gate i => exact i.elim0

/-- The constant-free De Morgan basis is not complete: no circuit computes a function on zero
inputs. -/
theorem not_isComplete : ¬ interpretation.IsComplete := by
  intro h
  obtain ⟨c, hc⟩ := h.exists_computes_single (n := 0) fun _ => true
  have := ecomplexity_eq_top Nat.one_pos (single fun _ => true)
  exact (ecomplexity_le_of_computes c hc).not_gt (this ▸ WithTop.coe_lt_top _)

end Boolean.DeMorgan

namespace Boolean

/-- An interpretation over a *De Morgan basis*: a meaning-keeping map from the constant-free De
Morgan basis into its signature, which supplies binary AND, binary OR and unary NOT gates, with
every operation of arity at most two and at most five operations. Results proved under this class
hold for the constant-free basis of Ilango, Loff and Oliveira and for cslib's basis with constants
alike; only the first has the source's size measure. -/
class DeMorganBasis {σ : Signature.{v}} (I : Interpretation σ Bool) where
  /-- The AND, OR and NOT gates of the basis. -/
  hom : DeMorgan.signature.Hom σ
  /-- The gates mean AND, OR and NOT. -/
  preserves : hom.Preserves DeMorgan.interpretation I
  /-- Every operation has at most two arguments. -/
  arity_le_two : ∀ op, σ.Arity op ≤ 2
  /-- The basis has finitely many operations. -/
  finite_op : Finite σ.Op
  /-- The basis has at most five operations, as many as cslib's basis with its two constants, so
  that counting bounds over a De Morgan basis are uniform in the basis. -/
  card_op_le : Nat.card σ.Op ≤ 5

attribute [instance] DeMorganBasis.preserves

/-- The constant-free basis is a De Morgan basis. -/
instance : DeMorganBasis DeMorgan.interpretation where
  hom := .id _
  preserves := inferInstance
  arity_le_two := DeMorgan.arity_le_two
  finite_op := inferInstance
  card_op_le := by rw [Nat.card_eq_fintype_card]; decide

/-- cslib's De Morgan basis with constants is a De Morgan basis. -/
instance : DeMorganBasis Boolean.interpretation where
  hom := DeMorgan.toBoolean
  preserves := inferInstance
  arity_le_two op := by cases op <;> simp
  finite_op := inferInstance
  card_op_le := by rw [Nat.card_eq_fintype_card, Op.card]

end Boolean

end Cslib.Circuits
