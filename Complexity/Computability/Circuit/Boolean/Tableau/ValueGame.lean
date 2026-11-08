/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Tableau.Correct
public import Complexity.Computability.Circuit.Boolean.Tableau.Space
public import Complexity.Computability.Machines.Turing.MultiTape.Alternating.WordGame
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Finite
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Sum
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.BitList
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Cases
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.ListSlice
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Size

/-!
# The circuit-value game on the tableau

A position of the circuit-value game on the tableau of a machine `tm` is a claim
(`Cslib.Circuits.Boolean.Tableau.ValueGame.Claim`): on the input `x`, after `T` steps, the wire `w`
of the tableau (`Cslib.Circuits.Boolean.Tableau.val`) carries the value `v`. A claim about an input
wire or a constant gate is terminal, and is won exactly when it is true. At a conjunction claimed
true or a disjunction claimed false the universal player picks an argument; at a conjunction
claimed false or a disjunction claimed true the existential player does; at a negation the claim
passes, flipped, to its argument. By induction on the wire, the existential player wins exactly
the true claims (`Cslib.Circuits.Boolean.Tableau.ValueGame.wins_position_iff`), and every play ends
within as many moves as the wire number, since every argument is an earlier wire.

The game is a word game (`Turing.MultiTapeATM.WordGame`): the position of a claim
(`Cslib.Circuits.Boolean.Tableau.ValueGame.position`) is the player, a move cell and the encoded
claim, and the update reads the claim and returns the position of the claim after the move. Through
the space-bounded gate decoder `Cslib.Circuits.Boolean.Tableau.gateCode_inSpace`, the update is
computed within linear space in the encoded claim
(`Cslib.Circuits.Boolean.Tableau.ValueGame.step_inSpace`). Claims encode their numbers in binary
(`Cslib.Circuits.Boolean.Tableau.ValueGame.encClaim`), so claims about a tableau of `2 ^ p n`
steps have polynomial length, and the game is played in alternating polynomial space:
this is the step `EXP ⊆ APSPACE` (`Cslib.Complexity.EXP_subset_APSPACE`) of
[Chandra, Kozen and Stockmeyer, Section 3][ChandraKozenStockmeyer1981], here on the tableau circuit
of [Ladner][Ladner1975].

## Main definitions

* `Cslib.Circuits.Boolean.Tableau.ValueGame.Claim`: a claimed value of a tableau wire.
* `Cslib.Circuits.Boolean.Tableau.ValueGame.position`,
  `Cslib.Circuits.Boolean.Tableau.ValueGame.update`: the positions and the update of the
  circuit-value game.
* `Cslib.Circuits.Boolean.Tableau.ValueGame.encClaim`: the encoding of claims, with binary
  numbers.

## Main results

* `Cslib.Circuits.Boolean.Tableau.ValueGame.wins_position_iff`: the existential player wins exactly
  the true claims.
* `Cslib.Circuits.Boolean.Tableau.ValueGame.ends_position`,
  `Cslib.Circuits.Boolean.Tableau.ValueGame.reach_position`: plays end, and reachable positions are
  positions of claims about tableau wires.
* `Cslib.Circuits.Boolean.Tableau.ValueGame.position_inSpace`,
  `Cslib.Circuits.Boolean.Tableau.ValueGame.step_inSpace`: positions and the update within linear
  space.

## References

* [A. K. Chandra, D. C. Kozen, L. J. Stockmeyer, *Alternation*][ChandraKozenStockmeyer1981]
* [R. E. Ladner, *The circuit value problem is log space complete for P*][Ladner1975]
-/

public section

namespace Cslib.Circuits.Boolean.Tableau

namespace ValueGame

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeATM WordGame

variable {k : ℕ} {State : Type} [Fintype State] [DecidableEq State]
  (tm : MultiTapeTM k Bool State)

/-! ### The circuit-value game on the tableau -/

/-- A claim `(x, T, w, v)`: on the input `x`, after `T` steps, the wire `w` of the tableau carries
the value `v`. -/
abbrev Claim := List Bool × ℕ × ℕ × Bool

namespace Claim

variable (c : Claim)

/-- The input `x` of a claim `(x, T, w, v)`. -/
abbrev input : List Bool := c.1

/-- The number of steps `T` of a claim `(x, T, w, v)`. -/
abbrev steps : ℕ := c.2.1

/-- The wire `w` of a claim `(x, T, w, v)`. -/
abbrev wire : ℕ := c.2.2.1

/-- The claimed value `v` of a claim `(x, T, w, v)`. -/
abbrev value : Bool := c.2.2.2

/-- The gate of the wire of a claim (meaningful when the wire is not an input). -/
noncomputable def gate : Op × List ℕ :=
  gateCode tm c.input.length c.steps (c.wire - c.input.length)

/-- The outcome of a terminal claim: an input wire or a constant gate. -/
noncomputable def outcome : Option Bool :=
  if c.wire < c.input.length then some (c.input.getD c.wire false == c.value)
  else match (gate tm c).1 with
    | .const b => some (b == c.value)
    | _ => none

/-- The player at a non-terminal claim: universal at a true conjunction and a false
disjunction. -/
noncomputable def player : Bool :=
  match (gate tm c).1 with
  | .and => c.value
  | .or => !c.value
  | _ => false

/-- The claim after the move `b`: the argument `b` of the gate (the only argument of a
negation), with the claimed value flipped at a negation. -/
noncomputable def next (b : Bool) : Claim :=
  (c.input, c.steps,
    (if b then (gate tm c).2.reverse.headD 0 else (gate tm c).2.headD 0),
    (if (gate tm c).1 = .not then !c.value else c.value))

end Claim

-- The word encoding of a claim (raw bits; the encoding is fixed later).
variable (encC : Claim ↪ List Bool)

/-- The position of a claim: `[true]` or `[]` at a terminal claim, else the player, a move cell and
the encoded claim. -/
noncomputable def position (c : Claim) : List Bool :=
  match Claim.outcome tm c with
  | some r => if r then [true] else []
  | none => Claim.player tm c :: false :: encC c

open scoped Classical in
/-- The update of the circuit-value game. -/
noncomputable def update (w : List Bool) : List Bool :=
  match w with
  | _ :: b :: r =>
    if h : ∃ c, encC c = r then position tm encC (Claim.next tm h.choose b) else []
  | _ => []

variable {tm encC}

/-- The update reads the claim of a position and returns the position of the claim after the
move. -/
theorem update_position_cons (c : Claim) (u b : Bool) :
    update tm encC (u :: b :: encC c) = position tm encC (Claim.next tm c b) := by
  have h : ∃ c', encC c' = encC c := ⟨c, rfl⟩
  simp only [update, h, ↓reduceDIte]
  rw [encC.injective h.choose_spec]

/-- A position of at least two cells comes from a non-terminal claim, whose encoding follows the
player and the move cell. -/
theorem position_eq_cons {c : Claim} {u x : Bool} {r : List Bool}
    (h : position tm encC c = u :: x :: r) : Claim.outcome tm c = none ∧ r = encC c := by
  cases ho : Claim.outcome tm c with
  | some o =>
    simp only [position, ho] at h
    cases o <;> simp at h
  | none =>
    simp only [position, ho, List.cons.injEq] at h
    exact ⟨rfl, h.2.2.symm⟩

/-- A terminal claim is won exactly when it is true. -/
theorem wins_position_terminal {c : Claim} {r : Bool} (h : Claim.outcome tm c = some r) :
    Wins (update tm encC) (position tm encC c) ↔ r = true := by
  simp only [position, h]
  cases r
  · simp [not_wins_nil]
  · simp [wins_singleton_iff]

/-- A non-terminal claim is won as a position of its player: some move wins for the existential
player, every move for the universal player. -/
theorem wins_position_nonterminal {c : Claim} (h : Claim.outcome tm c = none) :
    Wins (update tm encC) (position tm encC c) ↔
      if Claim.player tm c then ∀ b, Wins (update tm encC)
          (position tm encC (Claim.next tm c b))
        else ∃ b, Wins (update tm encC) (position tm encC (Claim.next tm c b)) := by
  have he : position tm encC c = Claim.player tm c :: false :: encC c := by simp only [position, h]
  rw [he]
  cases Claim.player tm c
  · simp only [wins_false_cons_cons_iff, update_position_cons, Bool.false_eq_true, ↓reduceIte]
  · simp only [wins_true_cons_cons_iff, update_position_cons, ↓reduceIte]

/-- **The circuit-value game computes the tableau**: from a claim about a wire, the existential
player wins exactly when the claim is true. -/
theorem wins_position_iff (x : List Bool) (T : ℕ) :
    ∀ w, w < x.length + numGates k State T → ∀ v,
      (Wins (update tm encC) (position tm encC (x, T, w, v)) ↔ val tm T x w = v) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hw v
  by_cases hin : w < x.length
  · have ho : Claim.outcome tm (x, T, w, v) = some (x.getD w false == v) := by
      simp [Claim.outcome, hin]
    rw [wins_position_terminal ho, val_input tm hin, List.getD_eq_getElem _ _ hin]
    simp
  · obtain ⟨g, rfl⟩ : ∃ g, w = x.length + g := ⟨w - x.length, by omega⟩
    have hg : g < numGates k State T := by omega
    have hgate : Claim.gate tm (x, T, x.length + g, v) = gateCode tm x.length T g := by
      simp [Claim.gate, Claim.input, Claim.steps, Claim.wire]
    obtain ⟨hlen, hlt⟩ := gateCode_wf tm (n := x.length) hg
    rw [val_add tm hg]
    have harg (i : ℕ) (hi : i ∈ (gateCode tm x.length T g).2) (v' : Bool) :
        Wins (update tm encC) (position tm encC (x, T, i, v')) ↔ val tm T x i = v' :=
      ih i (by have := hlt i hi; omega) (by have := hlt i hi; omega) v'
    generalize hG : gateCode tm x.length T g = G at hgate hlen hlt harg
    obtain ⟨op, args⟩ := G
    -- A constant gate is terminal; the other gates move to an argument.
    cases op with
    | const b =>
      have ho : Claim.outcome tm (x, T, x.length + g, v) = some (b == v) := by
        simp [Claim.outcome, Claim.input, Claim.wire, hgate]
      rw [wins_position_terminal ho]
      simp [interpretation]
    | not =>
      have ho : Claim.outcome tm (x, T, x.length + g, v) = none := by
        simp [Claim.outcome, Claim.input, Claim.wire, hgate]
      rw [wins_position_nonterminal ho]
      obtain ⟨a, rfl⟩ : ∃ a, args = [a] := by
        match args, hlen with
        | [a], _ => exact ⟨a, rfl⟩
      have hp : Claim.player tm (x, T, x.length + g, v) = false := by
        simp [Claim.player, hgate]
      have hn (b : Bool) : Claim.next tm (x, T, x.length + g, v) b = (x, T, a, !v) := by
        cases b <;> simp [Claim.next, hgate]
      simp only [hp, hn, harg a (by simp), Bool.false_eq_true, ↓reduceIte, exists_const]
      cases v <;> simp [interpretation]
    | and | or =>
      -- The move `b` picks the argument `b`; the player is universal exactly when every argument
      -- must carry the claimed value.
      have ho : Claim.outcome tm (x, T, x.length + g, v) = none := by
        simp [Claim.outcome, Claim.input, Claim.wire, hgate]
      rw [wins_position_nonterminal ho]
      obtain ⟨a₀, a₁, rfl⟩ : ∃ a₀ a₁, args = [a₀, a₁] := by
        match args, hlen with
        | [a₀, a₁], _ => exact ⟨a₀, a₁, rfl⟩
      have hn (b : Bool) : Claim.next tm (x, T, x.length + g, v) b =
          (x, T, if b then a₁ else a₀, v) := by
        cases b <;> simp [Claim.next, hgate]
      simp only [Claim.player, hgate, hn]
      have h₀ := harg a₀ (by simp)
      have h₁ := harg a₁ (by simp)
      cases v <;> cases e₀ : val tm T x a₀ <;> cases e₁ : val tm T x a₁ <;>
        simp [Bool.forall_bool, Bool.exists_bool, h₀, h₁, e₀, e₁, interpretation]

/-! ### Plays end, and reachable positions -/

private theorem next_arg_mem {c : Claim} (hne : (Claim.gate tm c).2 ≠ []) (b : Bool) :
    (Claim.next tm c b).wire ∈ (Claim.gate tm c).2 := by
  obtain ⟨l, hl⟩ : ∃ l, (Claim.gate tm c).2 = l := ⟨_, rfl⟩
  cases b
  · simp only [Claim.next, Bool.false_eq_true, ↓reduceIte, hl]
    rw [hl] at hne
    obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hne
    simp
  · simp only [Claim.next, ↓reduceIte, hl]
    rw [hl] at hne
    have : l.reverse ≠ [] := by simpa using hne
    obtain ⟨a, l', hl'⟩ := List.exists_cons_of_ne_nil this
    rw [hl']
    have : a ∈ l.reverse := by rw [hl']; simp
    simpa using List.mem_reverse.mp this

/-- At a non-terminal claim about a gate, every move goes to an earlier wire. -/
theorem next_lt {c : Claim} (ho : Claim.outcome tm c = none)
    (hw : c.wire < c.input.length + numGates k State c.steps) (b : Bool) :
    (Claim.next tm c b).wire < c.wire := by
  have hin : ¬ c.wire < c.input.length := by
    intro h
    simp [Claim.outcome, h] at ho
  have hg : c.wire - c.input.length < numGates k State c.steps := by omega
  obtain ⟨hlen, hlt⟩ := gateCode_wf tm (n := c.input.length) hg
  have hne : (Claim.gate tm c).2 ≠ [] := by
    intro h
    simp only [Claim.gate] at h
    rw [h] at hlen
    simp only [Claim.outcome, hin, ↓reduceIte, Claim.gate] at ho
    revert hlen ho
    cases (gateCode tm c.input.length c.steps (c.wire - c.input.length)).1 <;> simp
  have := hlt _ (next_arg_mem hne b)
  omega

variable (encC) in
/-- **Every play ends** within as many moves as the wire number. -/
theorem ends_position (x : List Bool) (T : ℕ) :
    ∀ w, w < x.length + numGates k State T → ∀ v,
      Ends (update tm encC) w (position tm encC (x, T, w, v)) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hw v
  cases ho : Claim.outcome tm (x, T, w, v) with
  | some r =>
    simp only [position, ho]
    cases r <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> cases w <;> trivial
  | none =>
    have he : position tm encC (x, T, w, v) =
        Claim.player tm (x, T, w, v) :: false :: encC (x, T, w, v) := by
      simp only [position, ho]
    have hlt : ∀ b, (Claim.next tm (x, T, w, v) b).wire < w := next_lt ho hw
    obtain ⟨m, rfl⟩ : ∃ m, w = m + 1 := ⟨w - 1, by have := hlt true; omega⟩
    rw [he]
    intro b
    rw [update_position_cons]
    have h := ih _ (hlt b) (by have := hlt b; omega) (Claim.next tm (x, T, m + 1, v) b).value
    exact Ends.mono (by have := hlt b; omega) h

variable (encC) in
/-- The positions reachable from a claim: terminal words and the positions of claims about
wires of the tableau. -/
theorem reach_position {x : List Bool} {T w₀ : ℕ} {v₀ : Bool}
    (hw₀ : w₀ < x.length + numGates k State T) {w : List Bool}
    (h : Reach (update tm encC) (position tm encC (x, T, w₀, v₀)) w) :
    ∃ w' v, w' < x.length + numGates k State T ∧ w = position tm encC (x, T, w', v) := by
  induction h with
  | start => exact ⟨w₀, v₀, hw₀, rfl⟩
  | move b _ ih =>
    obtain ⟨w', v, hw', he⟩ := ih
    obtain ⟨ho, rfl⟩ := position_eq_cons he.symm
    rw [update_position_cons]
    exact ⟨(Claim.next tm (x, T, w', v) b).wire, (Claim.next tm (x, T, w', v) b).value,
      by have : (Claim.next tm (x, T, w', v) b).wire < w' := next_lt ho hw' b; omega, rfl⟩

/-- A position is at most two cells longer than the encoding of its claim. -/
theorem length_position_le (c : Claim) : (position tm encC c).length ≤ (encC c).length + 2 := by
  unfold position
  split
  · split <;> simp
  · simp

/-! ### The update within linear space -/

/-- The encoding of claims: a claim `(x, T, w, v)` is encoded as the framed list of the input
bits (`encList encBool`, each bit framed), then the framed step count `T`, then the framed wire
`w`, then the claimed bit `v`. The numbers `T` and `w` are in binary (`encNat`, least significant
bit first), which keeps claims polynomially long for tableaux of `T = 2 ^ p n` steps. -/
abbrev encClaim : Claim ↪ List Bool :=
  encPair (encList encBool) (encPair encNat (encPair encNat encBool))

open ComputableInSpace

/-- The encoding of a claim grows with the wire. -/
theorem length_encClaim_mono {x : List Bool} {T w w' : ℕ} {v v' : Bool} (h : w ≤ w') :
    (encClaim (x, T, w, v)).length ≤ (encClaim (x, T, w', v')).length := by
  have hs : (encNat w).length ≤ (encNat w').length := by
    simp only [encNat_apply, Nat.size_eq_bits_len]
    exact Nat.size_le_size h
  simp only [length_encPair, encBool_apply, List.length_singleton]
  omega

variable (tm)

private theorem input_inSpace : ComputableInSpace Claim.input encClaim (encList encBool)
    fun c : Claim => (encClaim c).length :=
  fst _ _
private theorem steps_inSpace : ComputableInSpace Claim.steps encClaim encNat
    fun c : Claim => (encClaim c).length :=
  fst' (snd _ _)
private theorem wire_inSpace : ComputableInSpace Claim.wire encClaim encNat
    fun c : Claim => (encClaim c).length :=
  fst' (snd' (snd _ _))
private theorem value_inSpace : ComputableInSpace Claim.value encClaim encBool
    fun c : Claim => (encClaim c).length :=
  snd' (snd' (snd _ _))
private theorem length_inSpace : ComputableInSpace (fun c : Claim => c.input.length) encClaim
    encNat fun c : Claim => (encClaim c).length :=
  budget_length input_inSpace

/-- The gate of the wire of a claim is computed within linear space in the encoded claim. -/
theorem gate_inSpace :
    ComputableInSpace (Claim.gate tm) encClaim encGate fun c : Claim => (encClaim c).length :=
  gateCode_inSpace tm length_inSpace steps_inSpace (BigOLe.refl _)
    (budget_natSub wire_inSpace length_inSpace)

/-- The claim after a move is computed within linear space in the encoded claim. -/
theorem next_inSpace (b : Bool) :
    ComputableInSpace (fun c => Claim.next tm c b) encClaim encClaim
      fun c : Claim => (encClaim c).length := by
  have hargs := snd' (gate_inSpace tm)
  have hop := fst' (gate_inSpace tm)
  have hsel : ComputableInSpace
      (fun c : Claim => if b then (Claim.gate tm c).2.reverse.headD 0
        else (Claim.gate tm c).2.headD 0) encClaim encNat
    fun c : Claim => (encClaim c).length := by
    cases b
    · simpa using budget_headD 0 hargs
    · simpa using budget_headD 0 (budget_comp_linear (listReverse encNat) hargs)
  have hv : ComputableInSpace
      (fun c : Claim => if (Claim.gate tm c).1 = .not then !c.value else c.value)
      encClaim encBool
    fun c : Claim => (encClaim c).length :=
    budget_finite (fun p : Op × Bool => if p.1 = .not then !p.2 else p.2)
      (budget_prod hop value_inSpace)
  exact budget_prod input_inSpace (budget_prod steps_inSpace (budget_prod hsel hv))

/-- The outcome of a claim from finitely many data: whether the wire is an input, the input bit,
the operation of the gate and the claimed value. -/
private def outcomeOf (q : Bool × Bool × Op × Bool) : Option Bool :=
  if q.1 then some (q.2.1 == q.2.2.2)
  else match q.2.2.1 with
    | .const b => some (b == q.2.2.2)
    | _ => none

/-- The player of a claim from the operation of its gate and the claimed value. -/
private def playerOf (q : Op × Bool) : Bool :=
  match q.1 with
  | .and => q.2
  | .or => !q.2
  | _ => false

private theorem outcome_eq (c : Claim) : Claim.outcome tm c =
    outcomeOf (decide (c.wire < c.input.length), (c.input.drop c.wire).headD false,
      (Claim.gate tm c).1, c.value) := by
  unfold Claim.outcome outcomeOf
  by_cases h : c.wire < c.input.length
  · simp only [h, ↓reduceIte, decide_true]
    rw [List.drop_eq_getElem_cons h, List.getD_eq_getElem _ _ h]
    rfl
  · simp only [h, ↓reduceIte, decide_false, Bool.false_eq_true]

private theorem player_eq (c : Claim) :
    Claim.player tm c = playerOf ((Claim.gate tm c).1, c.value) := by
  unfold Claim.player playerOf
  cases (Claim.gate tm c).1 <;> rfl

private theorem position_eq (c : Claim) : position tm encC c =
    if (Claim.outcome tm c).isSome then
      (if (Claim.outcome tm c).getD false then [true] else [])
    else Claim.player tm c :: false :: encC c := by
  unfold position
  cases Claim.outcome tm c <;> rfl

/-- The position of a claim is computed within linear space in the encoded claim. -/
theorem position_inSpace :
    ComputableInSpace (position tm encClaim) encClaim encBits
      fun c : Claim => (encClaim c).length := by
  have hop := fst' (gate_inSpace tm)
  have hbit : ComputableInSpace (fun c : Claim => (c.input.drop c.wire).headD false) encClaim
      encBool fun c : Claim => (encClaim c).length :=
    budget_headD false
      (budget_comp_linear (listDrop encBool) (budget_prod input_inSpace wire_inSpace))
  have hq : ComputableInSpace
      (fun c : Claim => (decide (c.wire < c.input.length), (c.input.drop c.wire).headD false,
        (Claim.gate tm c).1, c.value)) encClaim
      (encPair encBool (encPair encBool (encPair (encFinite Op) encBool)))
      fun c : Claim => (encClaim c).length :=
    budget_prod (budget_natLt wire_inSpace length_inSpace)
      (budget_prod hbit (budget_prod (budget_finite id hop) value_inSpace))
  have hsome := budget_finite (encC := encBool) (fun q => (outcomeOf q).isSome) hq
  have hres : ComputableInSpace
      (fun c : Claim => if (Claim.outcome tm c).getD false then [true] else [])
      encClaim encBits fun c : Claim => (encClaim c).length :=
    (budget_finite (encC := encBits) (fun q => if (outcomeOf q).getD false then [true] else [])
      hq).of_enc_eq fun c => by simp only [outcome_eq]
  have hplayer := budget_finite (encC := encList encBool)
    (fun q : Op × Bool => [playerOf q, false]) (budget_prod hop value_inSpace)
  have hid : ComputableInSpace (fun c : Claim => encClaim c) encClaim encBits
      fun c : Claim => (encClaim c).length :=
    (of_inO ComputableInDegree.id'.inO_one).of_enc_eq fun _ => rfl
  have hcons := ((budget_comp_linear listToBits hplayer).append hid
    (g := fun c => Claim.player tm c :: false :: encClaim c) (encD := encBits)
    fun c => by simp [player_eq]).weaken (.add (.refl _) (.refl _))
  have hsome' : ComputableInSpace (fun c : Claim => (Claim.outcome tm c).isSome) encClaim encBool
      fun c : Claim => (encClaim c).length :=
    hsome.of_enc_eq fun c => by simp only [outcome_eq]
  exact (budget_ite hsome' hres hcons).of_enc_eq fun c => by rw [position_eq]

/-! ### Typed positions -/

/-- The positions `u :: b :: encClaim c`, typed by the player `u` (the outer summand) and the move
cell `b` (the inner summand). -/
abbrev Pos := (Claim ⊕ Claim) ⊕ (Claim ⊕ Claim)

/-- The encoding of typed positions: the tag bit of the outer sum is the player `u`, the tag bit of
the inner sum is the move cell `b`, and the encoded claim follows (`encPos_pos`). -/
abbrev encPos : Pos ↪ List Bool := encSum (encSum encClaim encClaim) (encSum encClaim encClaim)

/-- The update on a typed position `u :: b :: encClaim c`. -/
noncomputable def step : Pos → List Bool :=
  Sum.elim (Sum.elim (fun c => position tm encClaim (Claim.next tm c false))
      (fun c => position tm encClaim (Claim.next tm c true)))
    (Sum.elim (fun c => position tm encClaim (Claim.next tm c false))
      (fun c => position tm encClaim (Claim.next tm c true)))

/-- The update on typed positions is computed within linear space in the encoded position. -/
theorem step_inSpace :
    ComputableInSpace (step tm) encPos encBits fun p => (encPos p).length := by
  have h (b : Bool) : ComputableInSpace (fun c => position tm encClaim (Claim.next tm c b)) encClaim
      encBits fun c : Claim => (encClaim c).length :=
    budget_comp_linear (position_inSpace tm) (next_inSpace tm b)
  exact sumElim (sumElim (h false) (h true)) (sumElim (h false) (h true))

/-- The typed position of `u :: b :: encClaim c`. -/
def pos (u b : Bool) (c : Claim) : Pos :=
  match u, b with
  | false, false => .inl (.inl c)
  | false, true => .inl (.inr c)
  | true, false => .inr (.inl c)
  | true, true => .inr (.inr c)

/-- The encoding of the typed position of `u :: b :: encClaim c`. -/
theorem encPos_pos (u b : Bool) (c : Claim) : encPos (pos u b c) = u :: b :: encClaim c := by
  cases u <;> cases b <;> rfl

/-- The update on a typed position is the update of the circuit-value game. -/
theorem step_pos (u b : Bool) (c : Claim) :
    step tm (pos u b c) = position tm encClaim (Claim.next tm c b) := by
  cases u <;> cases b <;> rfl

end ValueGame

end Cslib.Circuits.Boolean.Tableau
