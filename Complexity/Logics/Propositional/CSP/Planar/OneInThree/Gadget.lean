/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CSP.Planar.OneInThree
public import Complexity.Logics.Propositional.CSP.Planar.Construction.Gadget

/-!
# One-in-three gadgets over the original Boolean language

Interpret the construction trees from `NonSelfDual.witnesses`, then append the actual ternary
body and three copies of the actual NAND body on `(0,1)`, `(1,2)`, `(2,0)`. Each occurrence
has fresh auxiliaries. No macro symbols, pins or disequality symbols are added to the language.

The minor mathematics and triangle semantics are reused from the original reconstruction of
[DvorakKupec2015], Lemma 4, printed pp. 438–439. This endpoint establishes equality-free
primitive-positive definability only. Geometric realization, native reduction and the full
planar dichotomy remain separate obligations.
-/

public section

namespace Cslib.Logic.PL.CSP

open Cslib.BitString RelationMinor

variable {Rel : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}

namespace NonSelfDual

/-- Expand the ordered triangle into original-language bodies. The ternary body comes first,
followed by the NAND bodies on `(0,1)`, `(1,2)`, `(2,0)`, with separate auxiliary blocks. -/
@[expose] def triangleGadget {R : Set (Fin 3 → Bool)} [DecidablePred (· ∈ R)]
    (r : PPGadget arity sem R) (d : PPGadget arity sem nand)
    (hz : (0 : Fin 3 → Bool) ∉ R) (hu : ∀ i, Pi.single i true ∈ R) :
    PPGadget arity sem (oneHotRelation (Fin 3)) :=
  (((r.conj (d.relabelFree ![0, 1])).conj (d.relabelFree ![1, 2])).conj
    (d.relabelFree ![2, 0])).retarget fun a => by
      have hm := triangleBody_eval_iff R a (fun _ => false)
      have ht := (triangle R hz hu).correct a
      simp only [triangle, triangleBody_eval_iff] at ht
      have he : (∃ _ : Fin 0 → Bool, a ∈ R ∧
          (a = 0 ∨ a ∈ oneHotRelation (Fin 3))) ↔
          a ∈ R ∧ (a = 0 ∨ a ∈ oneHotRelation (Fin 3)) :=
        exists_const _
      rw [he] at ht
      rw [ht, ← hm]
      have hx : ![a 0, a 1, a 2] ∈ R ↔ a ∈ R :=
        Iff.of_eq (congrArg (fun x => x ∈ R)
          (List.ofFn_injective (by simp [List.ofFn_succ])))
      simp [triangleBody, eval, Constraint.eval, triangleSem, nand,
        Function.comp_def, and_assoc, hx]
      grind

/-- If the six Schaefer operations and unary complement all fail, one-in-three has an actual
equality-free gadget over the original language. No constants or minor oracle are assumed. -/
theorem exists_oneHotGadget (h : ¬HasSchaeferPolymorphism arity sem)
    (hn : ¬HasPolymorphism arity sem (fun a : Fin 1 → Bool => !(a 0))) :
    Nonempty (PPGadget arity sem (oneHotRelation (Fin 3))) := by
  classical
  obtain ⟨_, _, ⟨d⟩, R, ⟨r⟩, hz, hu⟩ := witnesses h hn
  exact ⟨triangleGadget r.gadget d.gadget hz hu⟩

end NonSelfDual

namespace RelationMinor

/-- Absence of the six Schaefer operations alone gives an original-language disequality
gadget. Unary complement need not fail, so this also serves the selfcomplementary branch. -/
theorem exists_disequalityGadget (h : ¬HasSchaeferPolymorphism arity sem) :
    Nonempty (PPGadget arity sem disequality) :=
  (disequality_of_not_hasSchaeferPolymorphism h).nonempty_ppGadget

end RelationMinor
end Cslib.Logic.PL.CSP
