/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CountingTerminal
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarryLookaheadCountingLayout
public import CslibFrontier.Computability.Circuit.Boolean.CarryLookahead.Query.Counting
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.WordGameRoundTime

/-!
# A native alternating evaluator for ordinary count bits

One finite machine plays the local carry-lookahead game on short metadata, then invokes the
actual carry-save counting evaluator for its selected operand bit. The round and terminal
machines share that metadata and preserve the long context on a disjoint tape block. Every
native transition, preparation, copy, and handoff is included in the clock.

The specification starts from explicit work-tape words. Constructing this initial storage from
an external input is a separate charged operation; no operand word is supplied to this machine.
-/

public section

namespace Turing.MultiTapeATM.CarryLookaheadCounting

open MultiTapeTM Cslib.Circuits.Boolean CarryLookahead.Query

/-- A uniform bound on the metadata at every reachable finishing-adder address. -/
@[expose] def metadataBound (w : ℕ) : ℕ :=
  4 * w.size + 6 * Nat.clog 2 (w + 1) + 26

/-- The common polynomial budget for a native routing round or terminal preparation. -/
@[expose] def overhead (c d w : ℕ) : ℕ := c * (metadataBound w + 1) ^ d

/-- All finishing-adder rounds and preparations plus the supplied actual root-evaluator clock. -/
@[expose] def clockOfRoot (c d w rootTime : ℕ) : ℕ :=
  (2 * Nat.clog 2 (w + 1) + 6) * (overhead c d w + 2) + overhead c d w + rootTime + 1

/-- All routing rounds, terminal preparation, and the actual carry-save counting branch. -/
@[expose] def clock (c d cRoot dRoot : ℕ) (context : List Bool) (n w : ℕ) : ℕ :=
  clockOfRoot c d w (CarrySaveCountingRoot.clock cRoot dRoot context n w)

/-- The count's canonical root storage beside the selected sum-bit claim and its control header.
The carry-save operand index is blank until the terminal machine computes and copies it. -/
@[expose] def initial (k r q : ℕ) (input context : List Bool) (n w bit : ℕ) (claim : Bool) :
    Cfg (CarryLookaheadCountingLayout.size k r q) Bool Unit input :=
  let p := Routing.ofClaim w (Nat.clog 2 (w + 1)) ⟨.sum bit, claim⟩
  WordGameLeaf.config (CarryLookaheadCountingLayout.control k r q) none
    (wordGameHeader (Routing.player p)) 0
    (CarryLookaheadCountingLayout.storage k r q input context n w p)

private theorem next_wellFormed {w rounds : ℕ} (u : Cslib.BitString (w + w + 1))
    (a : LocalValueGame.Claim Address) (ha : WellFormed w rounds a.wire) (bit : Bool) :
    WellFormed w rounds (LocalValueGame.next (decoder w rounds u) a bit).wire := by
  cases h : (decoder w rounds u).op a.wire <;>
    simp only [LocalValueGame.next, h]
  · exact ha.child u bit
  · exact ha.child u false
  · exact ha.child u bit
  · exact ha.child u bit

/-- Assemble one native finishing-adder machine around an actual terminal machine.
The machine and constants precede runtime data and root clocks. Its terminal contract is required
only at the queried parameters. -/
theorem exists_evaluator_of_terminal (predicate : List Bool × ℕ → Bool)
    {k r : ℕ} {S : Type} [Finite S]
    (terminal : MultiTapeATM (CountingTerminalLayout.size k r) Bool S) (cP dP : ℕ) :
    ∃ (q : ℕ) (Q : Type) (_ : Finite Q)
      (atm : MultiTapeATM (CarryLookaheadCountingLayout.size k r q) Bool Q) (c d : ℕ),
      ∀ (input context : List Bool) (n w rootTime : ℕ),
        (∀ (p : Routing.Position) (hw : p.width = w),
          let root := CarrySaveQuery.Counting.rootPair n w (fun j => predicate (context, j))
          let cfg := (CountingTerminalLayout.storage k r input context n w p []).withState
            (some terminal.toPTM.initial)
          terminal.HaltsWithin (CountingTerminal.clockOfRoot cP dP w p rootTime) cfg ∧
            (terminal.AcceptsWithin (CountingTerminal.clockOfRoot cP dP w p rootTime) cfg ↔
              Terminal.response (CarrySaveQuery.component root false)
                (CarrySaveQuery.component root true) p hw = true)) →
        ∀ (bit : Fin w) (claim : Bool),
          let start := (initial k r q input context n w bit.val claim).withState
            (some atm.toPTM.initial)
          atm.HaltsWithin (clockOfRoot c d w rootTime) start ∧
            (atm.AcceptsWithin (clockOfRoot c d w rootTime) start ↔
              CarrySaveQuery.Counting.count n w (fun j => predicate (context, j)) bit = claim) := by
  obtain ⟨q, SR, hSR, round, cQ, dQ, hround⟩ :=
    WordGameRound.exists_round Routing.encPosition Routing.step Routing.step_polyTime
  let := hSR
  let round' := round.extendTapes (CarryLookaheadCountingLayout.roundEmbedding k r q)
  let terminal' := terminal.extendTapes (CarryLookaheadCountingLayout.terminalEmbedding k r q)
  let control := CarryLookaheadCountingLayout.control k r q
  let atm := WordGameLeaf.machine round' terminal' control
  have hpoly : Cslib.PolynomiallyBounded
      (fun m => cQ * (m + 1) ^ dQ + (cP * (m + 1) ^ dP + 2) + 2 * m + 8) := by
    fun_prop
  obtain ⟨c, d, hc⟩ := Cslib.polynomiallyBounded_iff_le.mp hpoly
  refine ⟨q, _, inferInstance, atm, c, d, ?_⟩
  intro input context n w rootTime hterminal bit claim
  let rounds := Nat.clog 2 (w + 1)
  let root := CarrySaveQuery.Counting.rootPair n w (fun j => predicate (context, j))
  let u := Fin.append (Fin.append (CarrySaveQuery.component root false)
    (CarrySaveQuery.component root true)) ![false]
  let encode := Routing.ofClaim w rounds
  let store := fun a => CarryLookaheadCountingLayout.storage k r q input context n w (encode a)
  let next := LocalValueGame.next (decoder w rounds u)
  let leafClock := overhead c d w + rootTime
  let potential := fun a : LocalValueGame.Claim Address =>
    rank rounds a.wire * (overhead c d w + 2) + leafClock + 1
  have hlength (a : LocalValueGame.Claim Address) (ha : WellFormed w rounds a.wire) :
      (Routing.encPosition (encode a)).length ≤ metadataBound w :=
    Routing.length_ofClaim_le a ha
  have hroundCost (a : LocalValueGame.Claim Address) (ha : WellFormed w rounds a.wire) :
      cQ * ((Routing.encPosition (encode a)).length + 1) ^ dQ ≤ overhead c d w := by
    have hlen := hlength a ha
    have hpow := Nat.mul_le_mul_left cQ (Nat.pow_le_pow_left (by omega :
      (Routing.encPosition (encode a)).length + 1 ≤ metadataBound w + 1) dQ)
    have hbound := hc (metadataBound w)
    unfold overhead
    omega
  have hleafCost (a : LocalValueGame.Claim Address) (ha : WellFormed w rounds a.wire) :
      CountingTerminal.clockOfRoot cP dP w (encode a) rootTime ≤ leafClock := by
    have hlen := hlength a ha
    have hpow := Nat.mul_le_mul_left cP (Nat.pow_le_pow_left (by omega :
      (Routing.encPosition (encode a)).length + 1 ≤ metadataBound w + 1) dP)
    have hw : w.size ≤ metadataBound w := by unfold metadataBound; omega
    have hbound := hc (metadataBound w)
    unfold CountingTerminal.clockOfRoot leafClock overhead
    omega
  have hspec := WordGameLeaf.spec_of_potential round' terminal' control
    (fun a => Routing.player (encode a)) next store
    (fun a => WellFormed w rounds a.wire) (fun a => value w rounds u a.wire = a.value)
    potential ?_ ?_ ?_ (a := ⟨.sum bit.val, claim⟩)
    (by exact bit.isLt) (n := clockOfRoot c d w rootTime)
    (by simp [potential, leafClock, clockOfRoot, rank, rounds, Nat.add_assoc])
  · change atm.HaltsWithin _ _ ∧ (atm.AcceptsWithin _ _ ↔ _) at hspec ⊢
    rw [show atm.toPTM.initial = WordGameLeaf.State.dispatch from
      WordGameLeaf.machine_initial round' terminal' control]
    refine ⟨hspec.1, hspec.2.trans ?_⟩
    rw [value_count_sum_eq]
  · intro a ha hplayer
    let t := CountingTerminal.clockOfRoot cP dP w (encode a) rootTime
    obtain ⟨ht, hv⟩ := hterminal (encode a) rfl
    refine ⟨t, ?_, ?_, ?_⟩
    · exact (CarryLookaheadCountingLayout.haltsWithin_terminal_iff terminal q input context n w
        (encode a) (some terminal.toPTM.initial) [] t).mpr ht
    · exact (CarryLookaheadCountingLayout.acceptsWithin_terminal_iff terminal q input context n w
        (encode a) (some terminal.toPTM.initial) [] t).trans
          (hv.trans (Terminal.response_eq_true_iff w rounds
            (CarrySaveQuery.component root false) (CarrySaveQuery.component root true) a hplayer))
    · have ht := hleafCost a ha
      unfold potential
      omega
  · intro a ha player hplayer move
    let t := cQ * ((Routing.encPosition (encode a)).length + 1) ^ dQ
    have hr := CarryLookaheadCountingLayout.run_round round k r input context n w
      (encode a) (Routing.next (encode a) move) [player, move]
      (wordGameHeader (Routing.player (Routing.next (encode a) move))) t
      (hround input [] player move (encode a))
    have hn := Routing.next_ofClaim w rounds u a move
    change Routing.next (encode a) move = encode (next a move) at hn
    rw [hn] at hr
    refine ⟨t, hr, next_wellFormed u a ha move, ?_⟩
    have hrank : rank rounds (next a move).wire + 1 ≤ rank rounds a.wire := by
      have h := Routing.rank_next_lt w rounds u a hplayer move
      rw [Routing.next_ofClaim w rounds u] at h
      simpa [Routing.ofClaim] using h
    have hmul := Nat.mul_le_mul_right (overhead c d w + 2) hrank
    simp only [Nat.add_mul, Nat.one_mul] at hmul
    have ht := hroundCost a ha
    unfold potential
    omega
  · intro a _ player hplayer
    have h := Routing.value_iff_next w rounds u a hplayer
    simp_rw [Routing.next_ofClaim w rounds u] at h
    simpa only [Routing.ofClaim, Address.address_toData] using h

/-- A single finite native machine answers every ordinary bit of the predicate count.
Its clock is uniform in the queried bit and the claimed value, and includes the real terminal
counting computation on every branch. -/
theorem exists_evaluator (predicate : List Bool × ℕ → Bool)
    (hp : ComputableInPolyTime predicate (encPair encBits encNat) encBool) :
    ∃ (k r q : ℕ) (S : Type) (_ : Finite S)
      (atm : MultiTapeATM (CarryLookaheadCountingLayout.size k r q) Bool S)
      (c d cRoot dRoot : ℕ),
      ∀ (input context : List Bool) (n w : ℕ) (bit : Fin w) (claim : Bool),
        let start := (initial k r q input context n w bit.val claim).withState
          (some atm.toPTM.initial)
        atm.HaltsWithin (clock c d cRoot dRoot context n w) start ∧
          (atm.AcceptsWithin (clock c d cRoot dRoot context n w) start ↔
            CarrySaveQuery.Counting.count n w (fun j => predicate (context, j)) bit = claim) := by
  obtain ⟨k, r, SL, hSL, terminal, cP, dP, cRoot, dRoot, hterminal⟩ :=
    CountingTerminal.exists_evaluator predicate hp
  let : Finite SL := hSL
  obtain ⟨q, S, hS, atm, c, d, h⟩ :=
    exists_evaluator_of_terminal predicate terminal cP dP
  refine ⟨k, r, q, S, hS, atm, c, d, cRoot, dRoot, ?_⟩
  intro input context n w bit claim
  exact h input context n w (CarrySaveCountingRoot.clock cRoot dRoot context n w)
    (hterminal input context n w) bit claim

end Turing.MultiTapeATM.CarryLookaheadCounting
