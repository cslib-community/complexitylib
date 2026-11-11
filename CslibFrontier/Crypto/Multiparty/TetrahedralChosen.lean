/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Multiparty.Tetrahedral

/-!
# Chosen-input oblivious transfer from a tetrahedral shuffle

[Beaver2027], Section 2 and Theorem 4.1 (PDF pp. 2–3), invokes a unit-cost
random-OT to chosen-OT conversion. Here that conversion is explicit: Bob sends
his random selection XOR his desired selection, and Alice sends two masked bits.
One original S4 sample, one trit and three additional public bits suffice.

The complete views retain the underlying hand and original announcement, as
well as all conversion messages. `chosen_correctness` holds pointwise for every
input and shuffle. `chosen_alice_privacy` gives identical view laws for either
receiver choice; `chosen_bob_privacy` gives identical view laws for any sender
input pairs agreeing at the selected position. These exact counting identities
establish perfect passive privacy of this isolated protocol. They do not provide
the library's typed protocol composition theorem or the paper's MPC corollary.
-/

public section

namespace Cslib.Crypto.Tetrahedral

/-- Bob's one-bit announcement aligns his random selection with his chosen input. -/
@[expose] def choiceOffset (k : Fin 24) (choice : Bool) : Bool :=
  (receiverOutput k).1 ^^ choice

/-- Alice's two public one-time-pad ciphertexts. -/
@[expose] def chosenMasks (k : Fin 24) (bits : Bool × Bool) (offset : Bool) : Bool × Bool :=
  (bits.1 ^^ select (senderOutput k) offset,
   bits.2 ^^ select (senderOutput k) (!offset))

/-- Bob's recovered chosen bit. -/
@[expose] def chosenOutput (k : Fin 24) (bits : Bool × Bool) (choice : Bool) : Bool :=
  select (chosenMasks k bits (choiceOffset k choice)) choice ^^ (receiverOutput k).2

/-- Alice's complete view, with her fixed input pair supplied separately. -/
@[expose] def chosenAliceView (k : Fin 24) (bits : Bool × Bool) (choice : Bool) :=
  (aliceView k, choiceOffset k choice, chosenMasks k bits (choiceOffset k choice))

/-- Bob's complete view, with his fixed selection supplied separately. -/
@[expose] def chosenBobView (k : Fin 24) (bits : Bool × Bool) (choice : Bool) :=
  (bobView k, choiceOffset k choice, chosenMasks k bits (choiceOffset k choice))

/-- Correctness for every input pair, desired selection and actual shuffle. -/
theorem chosen_correctness : ∀ (bits : Bool × Bool) (choice : Bool) (k : Fin 24),
    chosenOutput k bits choice = select bits choice := by decide

private theorem view_law {α β : Type*} [Fintype α] [DecidableEq β]
    (f g : α → β)
    (hf : ∀ k, (Finset.univ.filter fun l => f l = f k).card =
      (Finset.univ.filter fun l => g l = f k).card)
    (hg : ∀ k, (Finset.univ.filter fun l => f l = g k).card =
      (Finset.univ.filter fun l => g l = g k).card) (v : β) :
    (Finset.univ.filter fun l => f l = v).card =
      (Finset.univ.filter fun l => g l = v).card := by
  classical
  by_cases h : ∃ k, f k = v
  · obtain ⟨k, rfl⟩ := h
    exact hf k
  by_cases h' : ∃ k, g k = v
  · obtain ⟨k, rfl⟩ := h'
    exact hg k
  have hf0 : (Finset.univ.filter fun l => f l = v) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro k _ he
    exact h ⟨k, he⟩
  have hg0 : (Finset.univ.filter fun l => g l = v) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro k _ he
    exact h' ⟨k, he⟩
  rw [hf0, hg0]

-- Enumerate only attainable views; `view_law` handles all other fibers.
-- All checking uses kernel reduction, never native verification.
set_option maxRecDepth 16384 in
private theorem alice_certificate : ∀ (bits : Bool × Bool) (choice choice' : Bool) (k : Fin 24),
    (Finset.univ.filter fun l =>
      chosenAliceView l bits choice = chosenAliceView k bits choice).card =
      (Finset.univ.filter fun l =>
        chosenAliceView l bits choice' = chosenAliceView k bits choice).card := by
  decide

/-- Alice's entire view distribution is independent of Bob's chosen selection. -/
theorem chosen_alice_privacy (bits : Bool × Bool) (choice choice' : Bool)
    (v : ((Fin 4 × Fin 4) × Fin 3 × (Bool × Bool)) × Bool × (Bool × Bool)) :
    (Finset.univ.filter fun k => chosenAliceView k bits choice = v).card =
      (Finset.univ.filter fun k => chosenAliceView k bits choice' = v).card := by
  apply view_law _ _ (alice_certificate bits choice choice')
    (fun k => (alice_certificate bits choice' choice k).symm)

-- Bob's certificate also traverses the finite input pairs and all 24 reference shuffles.
set_option maxRecDepth 16384 in
private theorem bob_certificate : ∀ (bits bits' : Bool × Bool) (choice : Bool) (k : Fin 24),
    select bits choice = select bits' choice →
      (Finset.univ.filter fun l => chosenBobView l bits choice = chosenBobView k bits choice).card =
        (Finset.univ.filter fun l =>
          chosenBobView l bits' choice = chosenBobView k bits choice).card := by
  decide

/-- Bob's entire view distribution depends on Alice's inputs only through the
chosen bit. This includes the original local card and original public trit. -/
theorem chosen_bob_privacy (bits bits' : Bool × Bool) (choice : Bool)
    (v : (Fin 4 × Fin 3 × (Bool × Bool)) × Bool × (Bool × Bool))
    (he : select bits choice = select bits' choice) :
    (Finset.univ.filter fun k => chosenBobView k bits choice = v).card =
      (Finset.univ.filter fun k => chosenBobView k bits' choice = v).card := by
  apply view_law _ _ (fun k => bob_certificate bits bits' choice k he)
    (fun k => (bob_certificate bits' bits choice k he.symm).symm)

end Cslib.Crypto.Tetrahedral
