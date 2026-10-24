/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.NP.GuessVerify
public import Complexity.Computability.Machines.Turing.MultiTape.Machine.ChoiceTable
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.ReplayInput

/-!
# NP is nondeterministic polynomial time

The verifier class `Cslib.Complexity.NP` consists exactly of the problems decided in polynomial
time by nondeterministic machines with a binary alphabet and finitely many states
[Arora and Barak, Theorem 2.6][AroraBarak09]. Guessing a certificate and verifying it gives one
inclusion (`Cslib.Complexity.decidableInPolyTime_of_mem_NP`). This file proves the converse by
checking an encoded accepting computation.

A computation path is encoded by its choices, as coins of the fixed finite choice table
`Turing.MultiTapeNTM.choiceTable`: a step taking the permitted action of zero-based index `j`
costs `j + 1` coins, at most `M = Nat.card` of the action type. If every computation path on
`enc a` with at least `c * ((enc a).length + 1) ^ d` steps has halted (stuck paths may be
shorter), accepting computations are encoded within `M * c * ((enc a).length + 1) ^ d` coins, and
padded to exactly this polynomial length, which a halted table ignores. The verifier
`Turing.MultiTapeNTM.checkChoices` replays the certificate with the choice table and accepts when
the table emits `[true]`: then the coins encode a computation path that halts with output
`[true]`. Every coin list selects permitted actions, except at a stuck configuration, which has
none; there the table rejects. Replaying a fixed finite fair-coin table from encoded coins and
input is polynomial-time (`Turing.MultiTapePTM.computableTidilyInPolyTime_runClosedCoins`), so
the verifier needs no machine built by hand.

## Main definitions

* `Turing.MultiTapeNTM.checkChoices`: the verifier of encoded accepting computations.

## Main results

* `Turing.MultiTapeNTM.computableInPolyTime_checkChoices`: the verifier is polynomial-time.
* `Turing.MultiTapeNTM.DecidesInTime.mem_iff_exists_checkChoices`: accepting computations
  have certificates of every length at least the action count times the time bound.
* `Turing.MultiTapeNTM.DecidesInTime.isVerifier`: a machine deciding a problem within
  `c * ((enc a).length + 1) ^ d` steps yields a verifier with certificates of length
  `M * c * ((enc a).length + 1) ^ d`.
* `Cslib.Complexity.mem_NP_of_decidableInPolyTime`: the converse inclusion.
* `Cslib.Complexity.mem_NP_iff_decidableInPolyTime`: `NP` is nondeterministic polynomial time.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Turing.MultiTapeNTM

open MultiTapeTM

variable {k : ℕ} {State : Type} [Finite State] {α : Type} {enc : α ↪ List Bool}

/-- **The verifier of encoded accepting computations.** It accepts when the certificate, read as
coins of the choice table, replays a computation path on the encoded instance that halts with
output `[true]`. -/
noncomputable def checkChoices (ntm : MultiTapeNTM k Bool State) (enc : α ↪ List Bool)
    (x : α × List Bool) : Bool :=
  decide (ntm.choiceTable.runClosedCoins x.2 (enc x.1) = [true])

/-- Checking an encoded computation is polynomial-time: it replays a fixed finite fair-coin
table. -/
@[fun_prop]
theorem computableInPolyTime_checkChoices (ntm : MultiTapeNTM k Bool State) :
    ComputableInPolyTime (ntm.checkChoices enc) (encPair enc encBits) encBool := by
  refine .of_tidy ?_
  have hswap : ComputableTidilyInPolyTime (fun x : α × List Bool => (x.2, enc x.1))
      (encPair enc encBits) (encPair encBits encBits) :=
    (ComputableTidilyInPolyTime.snd enc encBits).prod
      ((ComputableTidilyInPolyTime.of_eq (encMid := encBits) fun _ => rfl).comp
        (ComputableTidilyInPolyTime.fst enc encBits))
  exact ComputableTidilyInPolyTime.decide_eq'
    ((MultiTapePTM.computableTidilyInPolyTime_runClosedCoins ntm.choiceTable).comp hswap)
    (ComputableTidilyInPolyTime.const [true])

/-- **Accepting computations as certificates of any sufficient length.** If `ntm` decides `A`
within `t`, then `a ∈ A` exactly when some certificate of length `L` encodes an accepting
computation on `enc a`, for every `L` of at least `M * t a`, for the number `M` of actions. -/
theorem DecidesInTime.mem_iff_exists_checkChoices {ntm : MultiTapeNTM k Bool State} {A : Set α}
    {t : α → ℕ} (h : ntm.DecidesInTime enc A t) {a : α} {L : ℕ}
    (hL : Nat.card (Turing.Action k Bool State) * t a ≤ L) :
    a ∈ A ↔ ∃ w : List Bool, w.length = L ∧ ntm.checkChoices enc (a, w) = true := by
  rw [(h a).2]
  constructor
  · intro hacc
    obtain ⟨p, hp, hout⟩ := (accepts_iff_exists_time_eq (h a).1).mp hacc
    obtain ⟨coins, hlen, hcoins⟩ :=
      exists_runClosedCoins_choiceTable p ((h a).1 p hp.ge) hout
    rw [hp] at hlen
    refine ⟨coins ++ List.replicate (L - coins.length) false, by
      simp only [List.length_append, List.length_replicate]; omega, ?_⟩
    simp [checkChoices, hcoins]
  · rintro ⟨w, -, hw⟩
    exact accepts_of_runClosedCoins_choiceTable (coins := w) (by simpa [checkChoices] using hw)

/-- **Accepting computations as certificates.** A machine deciding `A` within
`c * ((enc a).length + 1) ^ d` steps (every computation path with at least that many steps has
halted) yields a verifier whose certificates have length exactly
`M * c * ((enc a).length + 1) ^ d`, for the number `M` of actions. -/
theorem DecidesInTime.isVerifier {ntm : MultiTapeNTM k Bool State} {A : Set α} {c d : ℕ}
    (h : ntm.DecidesInTime enc A fun a => c * ((enc a).length + 1) ^ d) :
    Cslib.Complexity.IsVerifier enc
      (Polynomial.C (Nat.card (Turing.Action k Bool State) * c) * (Polynomial.X + 1) ^ d)
      (ntm.checkChoices enc) A := by
  intro a
  have heval : (Polynomial.C (Nat.card (Turing.Action k Bool State) * c) *
      (Polynomial.X + 1) ^ d).eval (enc a).length =
      Nat.card (Turing.Action k Bool State) * (c * ((enc a).length + 1) ^ d) := by
    simp [mul_assoc]
  rw [heval]
  exact h.mem_iff_exists_checkChoices le_rfl

end Turing.MultiTapeNTM

namespace Cslib.Complexity

open Turing

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

/-- **Checking accepting computations**, the inclusion of nondeterministic polynomial time in
`NP` [Arora and Barak, Theorem 2.6][AroraBarak09]. -/
theorem mem_NP_of_decidableInPolyTime (h : MultiTapeNTM.DecidableInPolyTime A enc) :
    A ∈ NP enc := by
  obtain ⟨t, ht, k, State, hfinite, ntm, hdecides⟩ := h
  obtain ⟨c, d, hle⟩ := ht.exists_le
  exact ⟨_, ntm.checkChoices enc, (ntm.computableInPolyTime_checkChoices),
    (hdecides.mono hle).isVerifier⟩

/-- **`NP` is nondeterministic polynomial time** [Arora and Barak, Theorem 2.6][AroraBarak09]:
a problem has a polynomial-time verifier with certificates of polynomial length exactly when a
nondeterministic machine with a binary alphabet and finitely many states decides it in
polynomial time, relative to the same encoding of instances. -/
theorem mem_NP_iff_decidableInPolyTime :
    A ∈ NP enc ↔ MultiTapeNTM.DecidableInPolyTime A enc :=
  ⟨decidableInPolyTime_of_mem_NP, mem_NP_of_decidableInPolyTime⟩

end Cslib.Complexity
