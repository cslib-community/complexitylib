/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.CarryLookahead.Query.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic

/-!
# Native routing of carry-lookahead value claims

A position stores only the query parameters, address, and claimed bit. Operation classification
uses an empty input: input references stop routing and are answered separately by the terminal
handler. Every nonterminal step is a native polynomial-time function of this short metadata.
-/

public section

namespace Cslib.Circuits.Boolean.CarryLookahead.Query.Routing

open Turing.MultiTapeTM ComputableInPolyTime

/-- Runtime metadata for one carry-lookahead value query. -/
structure Position where
  /-- Binary operand width. -/
  width : ℕ
  /-- Unary number of carry-doubling rounds. -/
  rounds : ℕ
  /-- Current address with binary tag/index and unary round. -/
  address : AddressData
  /-- Claimed value of the current wire. -/
  claim : Bool
  deriving DecidableEq

/-- Framed query parameters and address, followed by the claimed bit. -/
enc_structure encPosition : Position where
  width : encNat, rounds : encUnary, address : encAddressData, claim : encBool

/-- Store a semantic claim in the runtime metadata layout. -/
@[expose] def ofClaim (w rounds : ℕ) (c : LocalValueGame.Claim Address) : Position :=
  ⟨w, rounds, c.wire.toData, c.value⟩

/-- Classify a gate without reading an operand. Input gates are terminal constants. -/
@[expose] def operation (p : Position) : Op := opData p.width [] p.address

/-- The owner of a nonterminal query: `true` is universal and `false` existential. -/
@[expose] def player (p : Position) : Option Bool :=
  match operation p with
  | .const _ => none
  | .not => some false
  | .and => some p.claim
  | .or => some (!p.claim)

/-- Follow the chosen edge; a NOT gate always takes its sole edge and negates the claim. -/
@[expose] def next (p : Position) (b : Bool) : Position :=
  { p with
    address := childData p.width p.rounds p.address (if operation p = .not then false else b)
    claim := if operation p = .not then !p.claim else p.claim }

/-- One routing round returns the next owner and its metadata. -/
@[expose] def step (q : Bool × Position) : Option Bool × Position :=
  let p := next q.2 q.1
  (player p, p)

/-- Operation classification has a native certificate charged only to the metadata. -/
theorem operation_polyTime : ComputableInPolyTime operation encPosition encOp :=
  opData_polyTime (by fun_prop) (by fun_prop) (by fun_prop)

/-- Computing the next owner takes polynomial time in the metadata encoding. -/
theorem player_polyTime : ComputableInPolyTime player encPosition (encOption encBool) := by
  have h := (of_finite (encIn := encPair encOp encBool) (encOut := encOption encBool)
    (fun q : Op × Bool => match q.1 with
      | .const _ => none | .not => some false | .and => some q.2 | .or => some (!q.2)))
  exact h.comp (operation_polyTime.pair (by fun_prop))

/-- Both child arithmetic and claim updates have a native metadata-only certificate. -/
theorem next_polyTime :
    ComputableInPolyTime (fun q : Bool × Position => next q.2 q.1)
      (encPair encBool encPosition) encPosition := by
  have ho := operation_polyTime.comp
    (show ComputableInPolyTime (Prod.snd : Bool × Position → Position)
      (encPair encBool encPosition) encPosition from by fun_prop)
  unfold next
  apply encPosition_mk_polyTime <;> try fun_prop
  apply childData_polyTime <;> fun_prop

/-- A complete metadata routing round is uniformly native polynomial time. -/
theorem step_polyTime :
    ComputableInPolyTime step (encPair encBool encPosition)
      (encPair (encOption encBool) encPosition) :=
  (player_polyTime.comp next_polyTime).pair next_polyTime

/-- Canonical metadata classification agrees with the decoder with all input bits set to zero. -/
theorem operation_ofClaim (w rounds : ℕ) (c : LocalValueGame.Claim Address) :
    operation (ofClaim w rounds c) = (decoder w rounds (fun _ => false)).op c.wire := by
  rcases c with ⟨a, v⟩
  cases a with
  | propagate r i =>
    simp only [operation, ofClaim, Address.toData, opData, decoder]
    rfl
  | _ => simp [operation, ofClaim, opData, Address.toData, decoder, readInput]

private theorem operation_not_iff (w rounds : ℕ) (u : BitString (w + w + 1))
    (c : LocalValueGame.Claim Address) :
    operation (ofClaim w rounds c) = .not ↔ (decoder w rounds u).op c.wire = .not := by
  rw [operation_ofClaim]
  rcases c with ⟨a, v⟩
  cases a <;> simp [decoder]

/-- Runtime routing agrees with the semantic claim transition for every actual operand. -/
theorem next_ofClaim (w rounds : ℕ) (u : BitString (w + w + 1))
    (c : LocalValueGame.Claim Address) (b : Bool) :
    next (ofClaim w rounds c) b =
      ofClaim w rounds (LocalValueGame.next (decoder w rounds u) c b) := by
  unfold next
  simp only [operation_not_iff w rounds u c]
  cases ho : (decoder w rounds u).op c.wire <;>
    simp [ofClaim, LocalValueGame.next, ho, childData_toData w rounds u]

/-- A nonterminal semantic claim has exactly the runtime owner. -/
theorem player_ofClaim (w rounds : ℕ) (u : BitString (w + w + 1))
    (c : LocalValueGame.Claim Address) (hc : ∀ b, (decoder w rounds u).op c.wire ≠ .const b) :
    player (ofClaim w rounds c) = some (LocalValueGame.player (decoder w rounds u) c) := by
  rcases c with ⟨a, v⟩
  cases a <;> simp only [player, operation_ofClaim, LocalValueGame.player, decoder] at hc ⊢ <;>
    (try split_ifs) <;> simp_all [ofClaim]

/-- A runtime owner rules out an actual input or constant leaf, independently of operand bits. -/
theorem nonterminal_of_player (w rounds : ℕ) (u : BitString (w + w + 1))
    (c : LocalValueGame.Claim Address) {p : Bool} (hp : player (ofClaim w rounds c) = some p) :
    ∀ b, (decoder w rounds u).op c.wire ≠ .const b := by
  rcases c with ⟨a, v⟩
  cases a <;> simp only [player, operation_ofClaim, decoder] at hp ⊢ <;>
    (try split_ifs at hp ⊢) <;> simp_all

/-- Each routing round at a nonterminal canonical position strictly decreases the semantic rank. -/
theorem rank_next_lt (w rounds : ℕ) (u : BitString (w + w + 1))
    (c : LocalValueGame.Claim Address) {p : Bool} (hp : player (ofClaim w rounds c) = some p)
    (b : Bool) :
    rank rounds (next (ofClaim w rounds c) b).address.address < rank rounds c.wire := by
  rw [next_ofClaim w rounds u]
  simpa [ofClaim] using LocalValueGame.rank_next_lt (descends w rounds u) c
    (nonterminal_of_player w rounds u c hp) b

/-- The local alternating choice expresses the actual wire-value equation. -/
theorem value_iff_next (w rounds : ℕ) (u : BitString (w + w + 1))
    (c : LocalValueGame.Claim Address) {p : Bool} (hp : player (ofClaim w rounds c) = some p) :
    value w rounds u c.wire = c.value ↔
      if p then
        ∀ b, value w rounds u (next (ofClaim w rounds c) b).address.address =
          (next (ofClaim w rounds c) b).claim
      else
        ∃ b, value w rounds u (next (ofClaim w rounds c) b).address.address =
          (next (ofClaim w rounds c) b).claim := by
  have hc := nonterminal_of_player w rounds u c hp
  rw [player_ofClaim w rounds u c hc] at hp
  cases Option.some.inj hp
  simp only [next_ofClaim w rounds u]
  simp only [ofClaim, Address.address_toData]
  exact LocalValueGame.value_eq_iff_next (value w rounds u) c
    (value_eq_eval w rounds u c.wire) hc

/-- Canonical well-formed metadata fits a logarithmic-width, unary-round budget. -/
theorem length_ofClaim_le {w rounds : ℕ} (c : LocalValueGame.Claim Address)
    (hc : WellFormed w rounds c.wire) :
    (encPosition (ofClaim w rounds c)).length ≤ 4 * w.size + 6 * rounds + 26 := by
  have ha := hc.length_encAddress
  change (encAddressData c.wire.toData).length ≤ _ at ha
  simp only [encPosition_apply, encPositionFields, ofClaim, length_encPair, encNat_apply,
    Nat.size_eq_bits_len, encUnary_apply, List.length_replicate, encBool_apply,
    List.length_singleton]
  omega

end Cslib.Circuits.Boolean.CarryLookahead.Query.Routing
