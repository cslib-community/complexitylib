/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Prod

/-!
# Tetrahedral random oblivious transfer

The forward direction of [Beaver2027], Theorem 4.1 (PDF p. 3), using exactly
Figures 2 and 3. A sample is one of the 24 equiprobable permutations of four
*distinct* cards. Alice sees the ordered first two cards; Bob sees the third.
The public message is deterministic. Thus the views below contain every local
input, message and output (there are no further private coins).

The counting identities express perfect passive privacy, conditional on each
party's entire view, and the uniform ideal output triple. Multiplying counts
avoids division: probability is count divided by 24. This is a single invocation,
not a composable security or chosen-input OT theorem. In particular it does not
assert the reverse simulation or optimality in Section 5.

## Main definitions

* `shuffle`, `aliceTable`, `bobTable`: the literal S4 protocol and lookup tables.
* `aliceView`, `bobView`: complete passive views including local hand, public message and output.

## Main results

* `correctness`, `uniform_output`: selected-bit correctness and the uniform ideal output triple.
* `alice_privacy`, `bob_privacy`: exact finite counting identities for both passive views.

## References

* [D. Beaver, *Correlated Group Interactions*][Beaver2027], Theorem 4.1 and Figures 2–3.
-/

public section

namespace Cslib.Crypto.Tetrahedral

/-- The 24 possible full shuffles, in lexicographic order (Figure 5). -/
@[expose] def shuffle (k : Fin 24) : Fin 4 → Fin 4 :=
  (![
    ![0, 1, 2, 3],
    ![0, 1, 3, 2],
    ![0, 2, 1, 3],
    ![0, 2, 3, 1],
    ![0, 3, 1, 2],
    ![0, 3, 2, 1],
    ![1, 0, 2, 3],
    ![1, 0, 3, 2],
    ![1, 2, 0, 3],
    ![1, 2, 3, 0],
    ![1, 3, 0, 2],
    ![1, 3, 2, 0],
    ![2, 0, 1, 3],
    ![2, 0, 3, 1],
    ![2, 1, 0, 3],
    ![2, 1, 3, 0],
    ![2, 3, 0, 1],
    ![2, 3, 1, 0],
    ![3, 0, 1, 2],
    ![3, 0, 2, 1],
    ![3, 1, 0, 2],
    ![3, 1, 2, 0],
    ![3, 2, 0, 1],
    ![3, 2, 1, 0]]) k

/-- Every indexed shuffle really is a permutation. -/
theorem shuffle_injective : ∀ k, Function.Injective (shuffle k) := by decide

/-- No shuffle is sampled twice. -/
theorem shuffle_index_injective : Function.Injective shuffle := by decide

-- The finite function enumerator has 256 entries; kernel reduction traverses this list.
set_option maxRecDepth 4096 in
/-- All permutations occur: the indexed experiment is exactly uniform on S4. -/
theorem shuffle_complete : ∀ f : Fin 4 → Fin 4,
    Function.Injective f → ∃ k, shuffle k = f := by decide

/-- Alice's message (X=0, Y=1, Z=2) and two output bits, Figure 2.
Diagonal entries are arbitrary and never reached by a permutation. -/
@[expose] def aliceTable (a b : Fin 4) : Fin 3 × (Bool × Bool) :=
  (![![(0, (false, false)), (2, (true, true)), (0, (true, true)), (1, (true, false))],
     ![(1, (true, true)), (0, (false, false)), (1, (false, true)), (0, (false, false))],
     ![(2, (true, false)), (0, (false, true)), (0, (false, false)), (2, (false, false))],
     ![(0, (true, false)), (2, (false, true)), (1, (false, false)),
       (0, (false, false))]]) a b

/-- Bob's selection bit and received bit, Figure 3. -/
@[expose] def bobTable (msg : Fin 3) (c : Fin 4) : Bool × Bool :=
  (![![(false, false), (false, true), (true, false), (true, true)],
     ![(false, false), (true, false), (false, true), (true, true)],
     ![(false, false), (true, false), (true, true), (false, true)]]) msg c

/-- Alice's public announcement. -/
@[expose] def message (k : Fin 24) : Fin 3 :=
  (aliceTable (shuffle k 0) (shuffle k 1)).1

/-- Alice's two random output bits. -/
@[expose] def senderOutput (k : Fin 24) : Bool × Bool :=
  (aliceTable (shuffle k 0) (shuffle k 1)).2

/-- Bob's selection and received bit. -/
@[expose] def receiverOutput (k : Fin 24) : Bool × Bool :=
  bobTable (message k) (shuffle k 2)

/-- Selecting one of two bits. -/
@[expose] def select (bits : Bool × Bool) (s : Bool) : Bool :=
  if s then bits.2 else bits.1

/-- Alice's complete passive view: ordered hand, announcement and outputs. -/
@[expose] def aliceView (k : Fin 24) : (Fin 4 × Fin 4) × Fin 3 × (Bool × Bool) :=
  ((shuffle k 0, shuffle k 1), message k, senderOutput k)

/-- Bob's complete passive view: card, announcement, selection and received bit. -/
@[expose] def bobView (k : Fin 24) : Fin 4 × Fin 3 × (Bool × Bool) :=
  (shuffle k 2, message k, receiverOutput k)

/-- Correctness in every possible shuffle, not merely with high probability. -/
theorem correctness : ∀ k,
    (receiverOutput k).2 = select (senderOutput k) (receiverOutput k).1 := by decide

/-- Each ideal triple of two sender bits and selection occurs exactly three times.
Under a uniform shuffle it therefore has probability 3/24 = 1/8. -/
theorem uniform_output : ∀ (bits : Bool × Bool) (s : Bool),
    (Finset.univ.filter fun k => senderOutput k = bits ∧ (receiverOutput k).1 = s).card
      = 3 := by decide

-- The full view space has 192 elements, each checked against 24 shuffles.
set_option maxRecDepth 4096 in
/-- The selection is a fair bit conditional on Alice's *complete* view.
This gives her perfect privacy even after recording her ordered hand. -/
theorem alice_privacy : ∀ (v : (Fin 4 × Fin 4) × Fin 3 × (Bool × Bool)) (s : Bool),
    2 * (Finset.univ.filter fun k => aliceView k = v ∧ (receiverOutput k).1 = s).card
      = (Finset.univ.filter fun k => aliceView k = v).card := by decide

/-- The unselected sender bit is fair conditional on Bob's *complete* view. -/
theorem bob_privacy : ∀ (v : Fin 4 × Fin 3 × (Bool × Bool)) (b : Bool),
    2 * (Finset.univ.filter fun k => bobView k = v ∧
      select (senderOutput k) (!(receiverOutput k).1) = b).card
      = (Finset.univ.filter fun k => bobView k = v).card := by decide

end Cslib.Crypto.Tetrahedral
