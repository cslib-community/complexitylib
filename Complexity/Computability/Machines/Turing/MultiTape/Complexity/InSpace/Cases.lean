/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Cases

/-!
# Case analysis within linear work space

Case analysis on a tagged sum or option preserves space linear in the encoded input.
The implementations reuse the native case combinators, forgetting their time bounds.
-/

public section

namespace Turing.MultiTapeTM.ComputableInSpace

variable {π α β ε : Type} {encP : π ↪ List Bool} {encA : α ↪ List Bool}
  {encB : β ↪ List Bool} {encE : ε ↪ List Bool}

/-- Linear-space branches give linear-space case analysis on the second component. -/
theorem sumElimSnd {f : π × α → ε} {g : π × β → ε}
    (hf : ComputableInSpace f (encPair encP encA) encE
      fun p => (encPair encP encA p).length)
    (hg : ComputableInSpace g (encPair encP encB) encE
      fun p => (encPair encP encB p).length) :
    ComputableInSpace
      (fun p : π × (α ⊕ β) => p.2.elim (fun a => f (p.1, a)) (fun b => g (p.1, b)))
      (encPair encP (encSum encA encB)) encE
      (fun p => (encPair encP (encSum encA encB) p).length) := by
  obtain ⟨_, hf⟩ := hf.exists_inO
  obtain ⟨_, hg⟩ := hg.exists_inO
  refine (of_inO (ComputableInO.sumElimSnd hf hg)).weaken ⟨2, ?_⟩
  rintro ⟨p, a | b⟩ <;>
    simp only [length_encPair, encSum_inl, encSum_inr, List.length_cons,
      Sum.elim_inl, Sum.elim_inr] <;> omega

/-- Inspecting an option and running its selected linear-space branch uses linear space. -/
theorem optionElimSnd {f : π → ε} {g : π × α → ε}
    (hf : ComputableInSpace f encP encE fun p => (encP p).length)
    (hg : ComputableInSpace g (encPair encP encA) encE
      fun p => (encPair encP encA p).length) :
    ComputableInSpace
      (fun p : π × Option α => p.2.elim (f p.1) (fun a => g (p.1, a)))
      (encPair encP (encOption encA)) encE
      (fun p => (encPair encP (encOption encA) p).length) := by
  obtain ⟨_, hf⟩ := hf.exists_inO
  obtain ⟨_, hg⟩ := hg.exists_inO
  refine (of_inO (ComputableInO.optionElimSnd hf hg)).weaken ⟨2, ?_⟩
  rintro ⟨p, _ | a⟩ <;>
    simp only [length_encPair, encOption_none, encOption_some, List.length_nil,
      List.length_cons, Option.elim_none, Option.elim_some] <;> omega

/-- Case analysis on the first component preserves a shared second parameter. -/
theorem sumElimFst {f : α × π → ε} {g : β × π → ε}
    (hf : ComputableInSpace f (encPair encA encP) encE
      fun p => (encPair encA encP p).length)
    (hg : ComputableInSpace g (encPair encB encP) encE
      fun p => (encPair encB encP p).length) :
    ComputableInSpace
      (fun p : (α ⊕ β) × π => p.1.elim (fun a => f (a, p.2)) (fun b => g (b, p.2)))
      (encPair (encSum encA encB) encP) encE
      (fun p => (encPair (encSum encA encB) encP p).length) := by
  have hf' := budget_comp_linear hf (budget_prod (snd encP encA) (fst encP encA))
  have hg' := budget_comp_linear hg (budget_prod (snd encP encB) (fst encP encB))
  exact budget_comp_linear (sumElimSnd hf' hg')
    (budget_prod (snd (encSum encA encB) encP) (fst (encSum encA encB) encP))

/-- Linear-space case analysis without an auxiliary parameter. -/
theorem sumElim {f : α → ε} {g : β → ε}
    (hf : ComputableInSpace f encA encE fun a => (encA a).length)
    (hg : ComputableInSpace g encB encE fun b => (encB b).length) :
    ComputableInSpace (Sum.elim f g) (encSum encA encB) encE
      (fun s => (encSum encA encB s).length) := by
  have hf' := budget_comp_linear hf (snd encUnit encA)
  have hg' := budget_comp_linear hg (snd encUnit encB)
  have hcase := sumElimSnd hf' hg'
  have hid : ComputableInSpace (fun s : α ⊕ β => s) (encSum encA encB)
      (encSum encA encB) (fun s => (encSum encA encB s).length) :=
    of_inO ComputableInDegree.id'.inO_one
  exact (budget_comp_linear hcase
    (budget_prod (budget_const () (.refl _)) hid)).of_enc_eq fun s => by
      cases s <;> rfl

end Turing.MultiTapeTM.ComputableInSpace
