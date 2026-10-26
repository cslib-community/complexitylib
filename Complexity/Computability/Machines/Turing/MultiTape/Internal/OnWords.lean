/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelOnWords

/-! # Encoded function witnesses run on selected work tapes

These three generic machine lemmas are moved unchanged from Encodings.StepMachine. Their
statements concern machine-level tidiness, not an asymptotic computability calculus.
-/

namespace Turing.MultiTapeTM

section Tapes

variable {β δ : Type*} {k K : ℕ} {S : Type*} {tm : MultiTapeTM k Bool S} {encB : β ↪ List Bool}
  {encD : δ ↪ List Bool} {f : β → δ} {t s : β → ℕ}

/-- A tidy machine writing its output to tape `V`. -/
public lemma transformsTapes_outputToWord (h : ComputesFunTidilyInTimeAndSpace tm encB encD f t s)
    {e : Fin (k + 1) ↪ Fin K} {V : Fin K} (he : e (Fin.last k) = V) (b : β) :
    TransformsTapes (tm.outputToWord.extendTapes e) (fun inp ws => inp = encB b ∧ ws = fun _ => [])
      (fun _ _ ws' em => ws' = Function.update (fun _ => []) V (encD (f b)) ∧ em = [])
      (t b + (encD (f b)).length + 2) (s b + 2 * (encD (f b)).length + 2 * K + 3) := by
  have hk : k + 1 ≤ K := by simpa using Fintype.card_le_of_embedding e
  have h' := ((h b).outputToWord.imp
      (P' := fun inp ws => inp = encB b ∧ ws = Function.update (fun _ => []) (Fin.last k) [])
      (Q' := fun _ ws ws' em => ws' = Function.update ws (Fin.last k) (encD (f b)) ∧ em = [])
      (fun _ _ ⟨hin, hws⟩ => ⟨hin, by simp [hws]⟩)
      (fun _ _ _ _ ⟨_, hws⟩ ⟨hws', he⟩ => ⟨by simp [hws', hws], he⟩) le_rfl le_rfl
    ).extendTapes_update e
  rw [he] at h'
  exact h'.imp (fun _ _ ⟨hin, hws⟩ => ⟨hin, by simp [hws]⟩)
    (fun _ _ _ _ ⟨_, hws⟩ ⟨hws', he⟩ => ⟨by simp [hws', hws], he⟩) le_rfl (by omega)

/-- A tidy machine run on the word on tape `V`, emitting its output. -/
public lemma transformsTapes_inputFromWord_fun
    (h : ComputesFunTidilyInTimeAndSpace tm encB encD f t s)
    {e : Fin (k + 2) ↪ Fin K} {V : Fin K} (he : e (Fin.natAdd k 0) = V) (b : β) :
    TransformsTapes ((tm.inputFromWord true).extendTapes e)
      (fun _ ws => ws = Function.update (fun _ => []) V (encB b))
      (fun _ ws ws' em => ws' = ws ∧ em = encD (f b))
      (t b + 4) (s b + 2 * (encB b).length + 3 * K + 10) := by
  have hk : k + 2 ≤ K := by simpa using Fintype.card_le_of_embedding e
  have h' := ((h b).inputFromWord true).extendTapes_update e
  rw [he] at h'
  exact h'.imp (fun _ _ hws => ⟨trivial, hws⟩)
    (fun _ _ _ _ hws ⟨h, he⟩ => ⟨by rw [h, hws, Function.update_idem], he⟩) le_rfl (by omega)

/-- A tidy machine run on the word on tape `V`, writing its output to tape `O`. -/
public lemma transformsTapes_onWords (h : ComputesFunTidilyInTimeAndSpace tm encB encD f t s)
    {e : Fin (k + 1 + 2) ↪ Fin K} {V O : Fin K} (hi : e (Fin.natAdd (k + 1) 0) = V)
    (ho : e ((Fin.last k).castAdd 2) = O) (b : β) :
    TransformsTapes ((tm.onWords true).extendTapes e)
      (fun _ ws => ws = Function.update (fun _ => []) V (encB b))
      (fun _ ws ws' em => ws' = Function.update ws O (encD (f b)) ∧ em = [])
      (t b + (encD (f b)).length + 6)
      (s b + 2 * (encB b).length + 2 * (encD (f b)).length + 4 * K + 15) := by
  have hk : k + 1 + 2 ≤ K := by simpa using Fintype.card_le_of_embedding e
  have h' := (((h b).onWords true).imp
    (P' := fun _ ws => True ∧ ws = Function.update (fun _ => []) (Fin.natAdd (k + 1) 0) (encB b))
    (fun _ _ h => h.2) (fun _ _ _ _ _ h => h) le_rfl le_rfl).extendTapes_update e
  rw [hi, ho] at h'
  exact h'.imp (fun _ _ hws => ⟨trivial, hws⟩) (fun _ _ _ _ _ h => h) le_rfl (by omega)

end Tapes

end Turing.MultiTapeTM
