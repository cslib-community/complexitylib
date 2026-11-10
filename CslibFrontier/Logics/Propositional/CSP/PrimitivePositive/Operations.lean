/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.PrimitivePositive

/-!
# Substitution of free ports in primitive-positive gadgets

The conjunction is changed only by relabeling its scopes. Free labels can be identified,
and selected old free ports can become fresh existential auxiliaries. Repeated scope variables
are permitted. These operations assert finite semantics only, with no planarity conclusion.
-/

public section

namespace Cslib.Logic.PL.CSP

variable {Rel : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
  {n m k : ℕ} {R : Set (Fin n → Bool)}

/-- Relabeling variables preserves each constraint's declared scope width. -/
theorem WellFormed.relabel {V W : Type} {F : CSP Rel V} (h : WellFormed arity F)
    (f : V → W) : WellFormed arity (F.relabel f) := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  simpa only [Constraint.relabel, List.length_map] using h d hd

namespace PPGadget

/-- Relabel the free ports, keeping the same auxiliary labels and the same constraints.
Noninjective maps perform variable identification, rather than adding an equality symbol. -/
@[expose] def relabelFree (g : PPGadget arity sem R) (f : Fin n → Fin m) :
    PPGadget arity sem {a | a ∘ f ∈ R} where
  numAux := g.numAux
  body := g.body.relabel (Sum.map f id)
  wellFormed := g.wellFormed.relabel _
  correct a := by
    change a ∘ f ∈ R ↔ _
    rw [g.correct]
    apply exists_congr
    intro b
    rw [eval_relabel]
    have he : (Sum.elim a b) ∘ Sum.map f id = Sum.elim (a ∘ f) b := by
      funext v
      cases v <;> rfl
    rw [he]

/-- The exact variable map for substitution. The `k` fresh hidden labels precede the old
auxiliaries; free labels are mapped by `f`, and every old auxiliary remains distinct. -/
@[expose] def substitutePort (a : ℕ) (f : Fin n → Fin m ⊕ Fin k) :
    Fin n ⊕ Fin a → Fin m ⊕ Fin (k + a) :=
  Sum.elim (fun i => (f i).map id (Fin.castAdd a))
    (fun i => .inr (i.natAdd k))

/-- Identify and hide free ports by the specified label map. No constraints are added or
removed. The first `k` auxiliaries are exactly the newly hidden ports. -/
@[expose] def substitute (g : PPGadget arity sem R) (f : Fin n → Fin m ⊕ Fin k) :
    PPGadget arity sem {a | ∃ z : Fin k → Bool, (Sum.elim a z) ∘ f ∈ R} where
  numAux := k + g.numAux
  body := g.body.relabel (substitutePort g.numAux f)
  wellFormed := g.wellFormed.relabel _
  correct a := by
    change (∃ z : Fin k → Bool, (Sum.elim a z) ∘ f ∈ R) ↔ _
    simp only [g.correct, eval_relabel]
    constructor
    · rintro ⟨z, b, hb⟩
      refine ⟨Fin.addCases z b, ?_⟩
      convert hb using 2
      funext v
      cases v with
      | inl i => cases hf : f i <;> simp [substitutePort, hf]
      | inr i => simp [substitutePort]
    · rintro ⟨b, hb⟩
      refine ⟨fun i => b (i.castAdd g.numAux), fun i => b (i.natAdd k), ?_⟩
      convert hb using 2
      funext v
      cases v with
      | inl i => cases hf : f i <;> simp [substitutePort, hf]
      | inr i => rfl

/-- Free-port relabeling retains the exact number of constraints. -/
@[simp] theorem length_relabelFree_body (g : PPGadget arity sem R) (f : Fin n → Fin m) :
    (g.relabelFree f).body.length = g.body.length := List.length_map _

/-- Hiding free ports retains the exact number of constraints. -/
@[simp] theorem length_substitute_body (g : PPGadget arity sem R)
    (f : Fin n → Fin m ⊕ Fin k) :
    (g.substitute f).body.length = g.body.length := List.length_map _

end PPGadget
end Cslib.Logic.PL.CSP
