/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Fusion.Basic

/-!
# Fusion covers under homomorphisms

A homomorphism of interpretations maps every semantic gate to the corresponding gate in the
image. A predicate on image values is preserved there exactly when its pullback is preserved
in the source. Thus every cover of the pulled-back predicates maps to a cover of the original
predicates, with the same indexed operations and exactly the same operation costs.

No injectivity or surjectivity is required. Minimum cover complexity can decrease: image covers
may use arguments outside the range of the homomorphism. Lower bounds on image covers therefore
transfer to source covers, and `coverComplexity_le_ecomplexityFrom` transfers them to circuits.
Witnesses and predicates use the existing Fusion API; no separate model wrapper is needed.

## Main definitions

* `Cslib.Circuits.Fusion.Atom.map`: apply a carrier map to an atom's arguments.
* `Cslib.Circuits.Fusion.Cover.map`: transport a cover through a homomorphism.

## Main results

* `Cslib.Circuits.Fusion.programAtoms_map`: extraction commutes with homomorphisms.
* `Cslib.Circuits.Fusion.Cover.cost_map`: transport preserves exact operation costs.
* `Cslib.Circuits.Fusion.coverComplexity_le_comap`: image lower bounds transfer to source covers.

## References

* Adapted from LowerBound/Fusion/Comap.lean in
  [S. Schlesinger, *Algebraic circuit formalizations in Complexitylib*][Schlesinger2026Algebraic].
-/

@[expose] public section

namespace Cslib.Circuits.Fusion

universe u v w z t

variable {σ : Signature.{u}} {U : Type v} {V : Type w} {W : Type z} {T : Type t}
  {I : Interpretation σ U} {J : Interpretation σ V} {P : W → V → Prop}

/-- Apply a carrier map to every argument of an atom, retaining its operation. -/
def Atom.map (a : Atom σ U) (f : U → V) : Atom σ V :=
  ⟨a.op, f ∘ a.arguments⟩

/-- Mapping an atom preserves its operation. -/
@[simp] theorem Atom.op_map (a : Atom σ U) (f : U → V) : (a.map f).op = a.op := rfl

/-- Mapping an atom composes its arguments with `f`. -/
@[simp] theorem Atom.arguments_map (a : Atom σ U) (f : U → V) :
    (a.map f).arguments = f ∘ a.arguments := rfl

/-- Mapping an atom by `id` is the identity. -/
@[simp] theorem Atom.map_id (a : Atom σ U) : a.map id = a := rfl

/-- Mapping an atom twice composes the carrier maps. -/
@[simp] theorem Atom.map_map (a : Atom σ U) (f : U → V) (g : V → T) :
    (a.map f).map g = a.map (g ∘ f) := rfl

/-- Preservation of an image predicate is equivalent to preservation of its pullback. -/
theorem Atom.preserves_map_iff (a : Atom σ U) (h : Homomorphism I J) (Q : V → Prop) :
    (a.map h.map).Preserves J Q ↔ a.Preserves I (Q ∘ h.map) := by
  unfold Atom.Preserves Atom.map
  rw [← h.homomorphic]
  rfl

/-- Semantic gate extraction commutes with a homomorphism, at every gate index. -/
theorem programAtoms_map {n g : ℕ} (p : Program σ n g) (h : Homomorphism I J)
    (input : Fin n → U) (k : Fin g) :
    (programAtoms p I input k).map h.map = programAtoms p J (h.map ∘ input) k := by
  unfold programAtoms Atom.map
  congr 1
  funext a
  exact congrFun (p.map_trace h input) ((p.lines k).wires a)

/-- Map a cover of pulled-back predicates to a cover of the original predicates. -/
def Cover.map (h : Homomorphism I J) (c : Cover I (fun t => P t ∘ h.map)) : Cover J P where
  size := c.size
  atoms i := (c.atoms i).map h.map
  isCover t hpres := c.isCover t fun i => ((c.atoms i).preserves_map_iff h (P t)).mp (hpres i)

/-- Mapping a cover preserves its size. -/
@[simp] theorem Cover.size_map (h : Homomorphism I J)
    (c : Cover I (fun t => P t ∘ h.map)) : (c.map h).size = c.size := rfl

/-- The `i`-th atom of a mapped cover is the mapped `i`-th atom. -/
@[simp] theorem Cover.atoms_map (h : Homomorphism I J)
    (c : Cover I (fun t => P t ∘ h.map)) (i : Fin c.size) :
    (c.map h).atoms i = (c.atoms i).map h.map := rfl

/-- Transport preserves arbitrary operation weights, including zero weights and repeated atoms. -/
@[simp] theorem Cover.cost_map (h : Homomorphism I J)
    (c : Cover I (fun t => P t ∘ h.map)) (weight : σ.Op → ℕ) :
    (c.map h).cost weight = c.cost weight := rfl

/-- Image cover complexity lower-bounds the complexity of covering pulled-back predicates. -/
theorem coverComplexity_le_comap (h : Homomorphism I J) (P : W → V → Prop)
    (weight : σ.Op → ℕ) :
    coverComplexity J P weight ≤ coverComplexity I (fun t => P t ∘ h.map) weight :=
  le_coverComplexity_iff.mpr fun c => coverComplexity_le (c.map h) weight

end Cslib.Circuits.Fusion
