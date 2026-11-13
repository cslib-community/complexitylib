/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Operations

/-!
# Announcing a value from a finite type

A player can announce any value of their own input in a finite nonempty type `Z` with
`⌈log₂ |Z|⌉` bits: they send a fixed binary encoding of the value and both players decode it.
This is the short-output protocol used, for example, when a single input fixes a rectangle and
the other player names a valid answer, as in the heavy-atom case of
[ChukhinKulikovMihajlinSmal2026], proof of Lemma 5.2 (printed p. 10; PDF p. 11).

## Main results

* `Cslib.Communication.Protocol.exists_run_eq_left`: Alice announces a function of her input.
* `Cslib.Communication.Protocol.exists_run_eq_right`: Bob announces a function of his input.
-/

public section

namespace Cslib.Communication.Protocol

variable {X Y Z : Type*} [Fintype Z] [Nonempty Z]

/-- Alice announces `f x` in `⌈log₂ |Z|⌉` bits. -/
theorem exists_run_eq_left (f : X → Z) :
    ∃ q : Protocol X Y Z, q.depth ≤ Nat.clog 2 (Fintype.card Z) ∧ ∀ x y, q.run x y = f x := by
  obtain ⟨e⟩ : Nonempty (Z ↪ BitString (Nat.clog 2 (Fintype.card Z))) :=
    Function.Embedding.nonempty_of_card_le (BitString.card ▸ Nat.le_pow_clog one_lt_two _)
  refine ⟨aliceSend _ (fun x => e (f x)) fun m => output (Function.invFun e m),
    (depth_aliceSend_le (d := 0) fun _ => le_rfl).trans_eq (add_zero _), fun x y => ?_⟩
  rw [run_aliceSend, run_output, Function.leftInverse_invFun e.injective]

/-- Bob announces `f y` in `⌈log₂ |Z|⌉` bits. -/
theorem exists_run_eq_right (f : Y → Z) :
    ∃ q : Protocol X Y Z, q.depth ≤ Nat.clog 2 (Fintype.card Z) ∧ ∀ x y, q.run x y = f y := by
  obtain ⟨q, hq, hrun⟩ := exists_run_eq_left (Y := X) f
  exact ⟨q.swapPlayers, by simpa using hq, fun x y => by simp [hrun]⟩

end Cslib.Communication.Protocol
