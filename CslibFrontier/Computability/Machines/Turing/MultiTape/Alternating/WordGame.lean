/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.DeterministicPhase

/-!
# Word games on an alternating machine

A **word game** has positions that are binary words. At a position `u :: x :: r` with at least two
symbols, the player `u` (`false` existential, `true` universal) chooses a move `b`, which replaces
the cell `x`, and the update `U` gives the next position `U (u :: b :: r)`. The game ends at a
position with fewer than two symbols, and the existential player wins at `[true]`. This format is
the library's packaging of the proof idea of the inclusion `DTIME(2 ^ O(s)) ⊆ ASPACE(s)`
[Chandra, Kozen and Stockmeyer, Section 3][ChandraKozenStockmeyer1981]
[Sipser, Section 10.3][Sipser2013]: the alternating machine stores one position and recomputes the
next one after each move.

* `Turing.MultiTapeATM.WordGame.Reach U w₀`: the positions reachable from `w₀`.
* `Turing.MultiTapeATM.WordGame.Wins U`: the positions won by the existential player, as a least
  fixed point, so a position is won only through finitely many moves.
* `Turing.MultiTapeATM.WordGame.Ends U n`: every play from the position ends within `n` moves.

The alternating machine `Turing.MultiTapeATM.wordGame P R N` plays the game on work tape `N`: it
runs a deterministic machine `P` that writes the initial position, then repeats a round. A round
reads the position; if it has fewer than two symbols, the machine halts, emitting `true` exactly at
`[true]`; otherwise the state of the player `u` writes the move over the cell `x` (a universal
state when `u = true`) and a deterministic machine `R` performs the update. The two moves of a
step differ only at the move.

Acceptance (`Turing.MultiTapeATM.Accepts`) is the least fixed point of the labelling, acceptance
within some finite number of moves, so an infinite branch never helps a configuration accept. It
therefore matches the least fixed point `WordGame.Wins` exactly
(`Turing.MultiTapeATM.wordGame_spec`). The space used is the space of `P` and of one round of `R`,
independent of the number of rounds; the running time is linear in the length of the longest play.
So a game on polynomially long positions with a polynomial-time update is decided in alternating
polynomial space even when its plays are exponentially long, which is the route from deterministic
exponential time to `APSPACE`.

## Main definitions

* `Turing.MultiTapeATM.WordGame.Reach`, `Turing.MultiTapeATM.WordGame.Wins`,
  `Turing.MultiTapeATM.WordGame.Ends`: reachable positions, won positions, and bounded plays.
* `Turing.MultiTapeATM.wordGame`: the alternating machine playing a word game.
* `Turing.MultiTapeATM.WordGame.StorageWins`, `.StorageRounds`: indexed games on persistent
  work tapes, with explicitly supplied native round implementations.
* `Turing.MultiTapeATM.WordGame.PrepSpec`, `Turing.MultiTapeATM.WordGame.RoundSpec`: the
  specifications of the preparing machine and of the round machine.

## Main results

* `Turing.MultiTapeATM.WordGame.wins_false_cons_cons_iff`,
  `Turing.MultiTapeATM.WordGame.wins_true_cons_cons_iff`: won positions of each player.
* `Turing.MultiTapeATM.WordGame.accepts_storage_iff` and `.haltsWithin_storage_of_potential`:
  acceptance and native branch time without copying positions or resetting other work cursors.
* `Turing.MultiTapeATM.runsInTime_wordGame_of_potential`: a decreasing potential pays for
  position- and move-dependent round times.
* `Turing.MultiTapeATM.wordGame_spec`: the machine stays within the space of the preparation and of
  one round, accepts exactly when the existential player wins, and halts within a time linear in
  the length of the longest play.
* `Turing.MultiTapeATM.runsInSpace_wordGame`, `Turing.MultiTapeATM.accepts_wordGame_iff`,
  `Turing.MultiTapeATM.runsInTime_wordGame`: the three parts of `wordGame_spec` separately.

## References

* [A. K. Chandra, D. C. Kozen, L. J. Stockmeyer, *Alternation*][ChandraKozenStockmeyer1981]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

public section

namespace Turing.MultiTapeATM

namespace WordGame

/-! ### Word games -/

/-- The positions reachable from `w₀`: at a position `u :: x :: r`, the move `b` leads to
`U (u :: b :: r)`. -/
inductive Reach (U : List Bool → List Bool) (w₀ : List Bool) : List Bool → Prop
  | start : Reach U w₀ w₀
  | move {u x : Bool} {r : List Bool} (b : Bool) :
      Reach U w₀ (u :: x :: r) → Reach U w₀ (U (u :: b :: r))

/-- The positions won by the existential player: `[true]`; a position `false :: x :: r` some move
of which leads to a won position; and a position `true :: x :: r` every move of which does. -/
inductive Wins (U : List Bool → List Bool) : List Bool → Prop
  | accept : Wins U [true]
  | existsMove {x : Bool} {r : List Bool} (b : Bool) :
      Wins U (U (false :: b :: r)) → Wins U (false :: x :: r)
  | forallMove {x : Bool} {r : List Bool} :
      (∀ b, Wins U (U (true :: b :: r))) → Wins U (true :: x :: r)

/-- Every play from the position ends within `n` moves. -/
@[expose] def Ends (U : List Bool → List Bool) : ℕ → List Bool → Prop
  | _, [] => True
  | _, [_] => True
  | 0, _ :: _ :: _ => False
  | n + 1, u :: _ :: r => ∀ b, Ends U n (U (u :: b :: r))

/-- A position of the existential player is won exactly when some move leads to a won position. -/
theorem wins_false_cons_cons_iff {U : List Bool → List Bool} {x : Bool} {r : List Bool} :
    Wins U (false :: x :: r) ↔ ∃ b, Wins U (U (false :: b :: r)) := by
  constructor
  · intro h
    cases h with
    | existsMove b h => exact ⟨b, h⟩
  · rintro ⟨b, h⟩
    exact .existsMove b h

/-- A position of the universal player is won exactly when every move leads to a won position. -/
theorem wins_true_cons_cons_iff {U : List Bool → List Bool} {x : Bool} {r : List Bool} :
    Wins U (true :: x :: r) ↔ ∀ b, Wins U (U (true :: b :: r)) := by
  constructor
  · intro h
    cases h with
    | forallMove h => exact h
  · intro h
    exact .forallMove h

/-- The empty position is lost. -/
theorem not_wins_nil {U : List Bool → List Bool} : ¬ Wins U [] := by
  intro h
  cases h

/-- A one-bit position is won exactly when the bit is `true`. -/
theorem wins_singleton_iff {U : List Bool → List Bool} {b : Bool} : Wins U [b] ↔ b = true := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact .accept

/-- A bound on the length of the plays may be raised. -/
theorem Ends.mono {U : List Bool → List Bool} :
    ∀ {m n : ℕ} {w : List Bool}, m ≤ n → Ends U m w → Ends U n w
  | _, _, [], _, _ => by simp [Ends]
  | _, _, [_], _, _ => by simp [Ends]
  | 0, _, _ :: _ :: _, _, h => h.elim
  | m + 1, n + 1, u :: x :: r, hmn, h => fun b => Ends.mono (by omega) (h b)
  | _ + 1, 0, _ :: _ :: _, hmn, _ => absurd hmn (by omega)

/-- A bound on the remaining moves also bounds plays from every reachable position. -/
theorem Ends.of_reach {U : List Bool → List Bool} {w₀ w : List Bool} {n : ℕ}
    (h : Ends U n w₀) (hw : Reach U w₀ w) : Ends U n w := by
  induction hw with
  | start => exact h
  | @move u x r b _ ih =>
    cases n with
    | zero => exact ih.elim
    | succ n => exact (ih b).mono (Nat.le_succ n)

/-- A natural-number potential decreasing after every move bounds the number of remaining moves.
The decrease is required for both players and only at positions reachable from the initial one. -/
theorem Ends.of_potential {U : List Bool → List Bool} {w₀ : List Bool}
    (potential : List Bool → ℕ)
    (hstep : ∀ u x r, Reach U w₀ (u :: x :: r) → ∀ b,
      potential (U (u :: b :: r)) < potential (u :: x :: r)) :
    Ends U (potential w₀) w₀ := by
  have h (n : ℕ) : ∀ w, potential w = n → Reach U w₀ w → Ends U n w := by
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro w hn hw
      rcases w with _ | ⟨u, _ | ⟨x, r⟩⟩
      · cases n <;> trivial
      · cases n <;> trivial
      · have hlt := hstep u x r hw
        cases n with
        | zero => have := hlt false; omega
        | succ n =>
          intro b
          exact (ih _ (by have := hlt b; omega) _ rfl (.move b hw)).mono (by
            have := hlt b
            omega)
  exact h _ w₀ rfl .start

/-! ### The machine -/

/-- The states of the word game machine: those of the preparing machine, those of the round
machine, the two dispatch states, and the move states of the two players. -/
inductive State (S₁ S₂ : Type) where
  | prep (q : S₁)
  | round (q : S₂)
  | disp0
  | disp1 (u : Bool)
  | move (u : Bool)

instance instFiniteState {S₁ S₂ : Type} [Finite S₁] [Finite S₂] : Finite (State S₁ S₂) :=
  Finite.of_injective (fun s : State S₁ S₂ => match s with
    | .prep q => (Sum.inl q : S₁ ⊕ S₂ ⊕ Option Bool ⊕ Bool)
    | .round q => .inr (.inl q)
    | .disp0 => .inr (.inr (.inl none))
    | .disp1 u => .inr (.inr (.inl (some u)))
    | .move u => .inr (.inr (.inr u))) (by
      rintro (_ | _ | _ | _ | _) (_ | _ | _ | _ | _) h <;> simp_all)

variable {k : ℕ} {S₁ S₂ : Type}

/-- The action that writes `w` on tape `N`, moves its head by `d`, and enters `q`. -/
private def act (N : Fin k) (w : Option (Option Bool)) (d : SignType) (out : Option Bool)
    (q : Option (State S₁ S₂)) : Turing.Action k Bool (State S₁ S₂) :=
  { inputTape := 0
    workTapes := Function.update (fun _ => (none, 0)) N (w, d)
    output := out
    state := q }

/-- Embed an action of a phase machine, sending its halting to `disp0`. -/
private def lift {S : Type} (f : S → State S₁ S₂) (a : Turing.Action k Bool S) :
    Turing.Action k Bool (State S₁ S₂) :=
  { a with state := some (a.state.elim .disp0 f) }

/-- The transition function of the deterministic machine of the move `b`. -/
private noncomputable def tr (P : MultiTapeTM k Bool S₁) (R : MultiTapeTM k Bool S₂)
    (N : Fin k) (b : Bool) :
    State S₁ S₂ → Option Bool → (Fin k → Option Bool) → Turing.Action k Bool (State S₁ S₂)
  | .prep q, inp, work => lift .prep (P.tr q inp work)
  | .round q, inp, work => lift .round (R.tr q inp work)
  | .disp0, _, work => match work N with
    | none => act N none 0 none none
    | some u => act N none 1 none (some (.disp1 u))
  | .disp1 u, _, work => match work N with
    | none => act N none 0 (if u then some true else none) none
    | some _ => act N none 0 none (some (.move u))
  | .move _, _, _ => act N (some (some b)) (-1) none (some (.round R.q₀))

/-- The deterministic machine of the move `b`. -/
private noncomputable def tm (P : MultiTapeTM k Bool S₁) (R : MultiTapeTM k Bool S₂)
    (N : Fin k) (b : Bool) : MultiTapeTM k Bool (State S₁ S₂) :=
  MultiTapeTM.ofTr (.prep P.q₀) (tr P R N b)

/-- The universal states: the move states of the universal player. -/
private def isUniversal : State S₁ S₂ → Bool
  | .move u => u
  | _ => false

end WordGame

/-- **The word game machine**: run `P`, then repeat: read the word `w` on tape `N`; if `w` has fewer
than two symbols, halt, emitting `true` exactly when `w = [true]`; otherwise the player `w[0]`
writes a move over `w[1]` and `R` runs. -/
noncomputable def wordGame {k : ℕ} {S₁ S₂ : Type} (P : MultiTapeTM k Bool S₁)
    (R : MultiTapeTM k Bool S₂) (N : Fin k) : MultiTapeATM k Bool (WordGame.State S₁ S₂) :=
  ofTMs (WordGame.tm P R N) WordGame.isUniversal

namespace WordGame

variable {k : ℕ} {S₁ S₂ : Type} {P : MultiTapeTM k Bool S₁} {R : MultiTapeTM k Bool S₂}
  {N : Fin k} {input : List Bool}

/-- A configuration of a phase machine as one of the word game machine. -/
@[expose] def liftCfg {S : Type} (f : S → State S₁ S₂) (c : Cfg k Bool S input) :
    Cfg k Bool (State S₁ S₂) input :=
  c.mapState fun st => some (st.elim .disp0 f)

/-- A running round phase preserves arbitrary work tapes and cursors. -/
theorem next_liftCfg_round (b : Bool) {c : Cfg k Bool S₂ input} (h : c.state ≠ none) :
    (wordGame P R N).next b (liftCfg .round c) = liftCfg .round (R.step c) := by
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp h
  have hstate : (liftCfg (S₁ := S₁) .round c).state = some (State.round q) := by
    simp [liftCfg, Cfg.mapState, hq]
  rw [wordGame, next_ofTMs, MultiTapeTM.step_of_state hstate, MultiTapeTM.step_of_state hq]
  simp only [tm, MultiTapeTM.tr_ofTr, tr]
  rfl

/-- A running preparation phase preserves arbitrary work tapes and cursors. -/
theorem next_liftCfg_prep (b : Bool) {c : Cfg k Bool S₁ input} (h : c.state ≠ none) :
    (wordGame P R N).next b (liftCfg .prep c) = liftCfg .prep (P.step c) := by
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp h
  have hstate : (liftCfg (S₂ := S₂) .prep c).state = some (State.prep q) := by
    simp [liftCfg, Cfg.mapState, hq]
  rw [wordGame, next_ofTMs, MultiTapeTM.step_of_state hstate, MultiTapeTM.step_of_state hq]
  simp only [tm, MultiTapeTM.tr_ofTr, tr]
  rfl

/-- Put `w` on control tape `N` with head `pos`, state `q`, and output `out`. The optional
storage snapshot supplies the input cursor and every other work tape and cursor; its state,
output, and fields at `N` are ignored. By default the other tapes are blank with heads at zero
and the input cursor is at its start. -/
@[expose] def cfg (N : Fin k) (q : Option (State S₁ S₂)) (w : List Bool) (pos : ℕ)
    (out : List Bool)
    (storage : Cfg k Bool Unit input := ⟨none, 1, fun _ _ => none, fun _ => 0, []⟩) :
    Cfg k Bool (State S₁ S₂) input :=
  ⟨q, storage.inputPos, Function.update storage.workTapes N (tapeOfList w),
    Function.update storage.workTapePos N (pos : ℤ), out⟩

private theorem cfg_zero (q : Option (State S₁ S₂)) (w : List Bool) (out : List Bool) :
    cfg (input := input) N q w 0 out =
      wordsCfg input q (Function.update (fun _ => []) N w) out := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> by_cases hi : i = N <;>
    simp [cfg, wordsCfg, hi]

variable (P R N) in
private theorem next_disp0_nil (b : Bool)
    (storage : Cfg k Bool Unit input := ⟨none, 1, fun _ _ => none, fun _ => 0, []⟩) :
    (wordGame P R N).next b (cfg (storage := storage) (input := input) N (some .disp0) [] 0 []) =
      cfg (storage := storage) N none [] 0 [] := by
  rw [wordGame, next_ofTMs, MultiTapeTM.step_of_state rfl]
  have hread : (cfg (storage := storage) (input := input) N
      (some (State.disp0 (S₁ := S₁) (S₂ := S₂))) [] 0
      []).workTapeSymbols N = none := by
    simp [Cfg.workTapeSymbols, cfg]
  simp only [tm, MultiTapeTM.tr_ofTr, tr, hread, act]
  refine Cfg.ext rfl (by simp [cfg, moveInputPos_zero]) ?_ ?_ (by simp [cfg]) <;>
    funext i <;> by_cases hi : i = N <;> simp [cfg, hi]

variable (P R N) in
private theorem next_disp0_cons (b u : Bool) (r : List Bool)
    (storage : Cfg k Bool Unit input := ⟨none, 1, fun _ _ => none, fun _ => 0, []⟩) :
    (wordGame P R N).next b (cfg (storage := storage) (input := input) N
      (some .disp0) (u :: r) 0 []) =
      cfg (storage := storage) N (some (.disp1 u)) (u :: r) 1 [] := by
  rw [wordGame, next_ofTMs, MultiTapeTM.step_of_state rfl]
  have hread : (cfg (storage := storage) (input := input) N
      (some (State.disp0 (S₁ := S₁) (S₂ := S₂))) (u :: r) 0
      []).workTapeSymbols N = some u := by
    simp [Cfg.workTapeSymbols, cfg, tapeOfList_zero]
  simp only [tm, MultiTapeTM.tr_ofTr, tr, hread, act]
  refine Cfg.ext rfl (by simp [cfg, moveInputPos_zero]) ?_ ?_ (by simp [cfg]) <;>
    funext i <;> by_cases hi : i = N <;> simp [cfg, hi]

variable (P R N) in
private theorem next_disp1_halt (b u : Bool) {w : List Bool} (hw : w[1]? = none)
    (storage : Cfg k Bool Unit input := ⟨none, 1, fun _ _ => none, fun _ => 0, []⟩) :
    (wordGame P R N).next b (cfg (storage := storage) (input := input) N (some (.disp1 u)) w 1 []) =
      cfg (storage := storage) N none w 1 (if u then [true] else []) := by
  rw [wordGame, next_ofTMs, MultiTapeTM.step_of_state rfl]
  have hread : (cfg (storage := storage) (input := input) N
      (some (State.disp1 (S₁ := S₁) (S₂ := S₂) u)) w 1
      []).workTapeSymbols N = none := by
    have h1 : tapeOfList w 1 = w[1]? := by simpa using tapeOfList_ofNat w 1
    simp [Cfg.workTapeSymbols, cfg, h1, hw]
  simp only [tm, MultiTapeTM.tr_ofTr, tr, hread, act]
  refine Cfg.ext rfl (by simp [cfg, moveInputPos_zero]) ?_ ?_ ?_
  · funext i
    by_cases hi : i = N <;> simp [cfg, hi]
  · funext i
    by_cases hi : i = N <;> simp [cfg, hi]
  · cases u <;> simp [cfg]

variable (P R N) in
private theorem next_disp1_move (b u x : Bool) {w : List Bool} (hw : w[1]? = some x)
    (storage : Cfg k Bool Unit input := ⟨none, 1, fun _ _ => none, fun _ => 0, []⟩) :
    (wordGame P R N).next b (cfg (storage := storage) (input := input) N (some (.disp1 u)) w 1 []) =
      cfg (storage := storage) N (some (.move u)) w 1 [] := by
  rw [wordGame, next_ofTMs, MultiTapeTM.step_of_state rfl]
  have hread : (cfg (storage := storage) (input := input) N
      (some (State.disp1 (S₁ := S₁) (S₂ := S₂) u)) w 1
      []).workTapeSymbols N = some x := by
    have h1 : tapeOfList w 1 = w[1]? := by simpa using tapeOfList_ofNat w 1
    simp [Cfg.workTapeSymbols, cfg, h1, hw]
  simp only [tm, MultiTapeTM.tr_ofTr, tr, hread, act]
  refine Cfg.ext rfl (by simp [cfg, moveInputPos_zero]) ?_ ?_ (by simp [cfg]) <;>
    funext i <;> by_cases hi : i = N <;> simp [cfg, hi]

variable (P R N) in
private theorem next_move (b u : Bool) {w : List Bool} (hw : 1 < w.length)
    (storage : Cfg k Bool Unit input := ⟨none, 1, fun _ _ => none, fun _ => 0, []⟩) :
    (wordGame P R N).next b (cfg (storage := storage) (input := input) N (some (.move u)) w 1 []) =
      cfg (storage := storage) N (some (.round R.q₀)) (w.set 1 b) 0 [] := by
  rw [wordGame, next_ofTMs, MultiTapeTM.step_of_state rfl]
  simp only [tm, MultiTapeTM.tr_ofTr, tr, act]
  refine Cfg.ext rfl (by simp [cfg, moveInputPos_zero]) ?_ ?_ (by simp [cfg]) <;>
    funext i <;> by_cases hi : i = N <;> simp [cfg, hi, tapeOfList_set w hw]

/-! ### Phases -/

/-- A deterministic phase finishes on arbitrary work storage; its transitions are independent
of the alternating choice until the handoff to dispatch. No tape normalization is required. -/
theorem exists_phase {S : Type} {M : MultiTapeTM k Bool S} (f : S → State S₁ S₂)
    (hstep : ∀ b (c : Cfg k Bool S input), c.state ≠ none →
      (wordGame P R N).next b (liftCfg f c) = liftCfg f (M.step c))
    {c : Cfg k Bool S input} {t : ℕ} (ht : (M.runFrom c t).state = none) :
    ∃ τ ≤ t, (∀ j < τ, ∀ b, (wordGame P R N).next b
        (((wordGame P R N).next false)^[j] (liftCfg f c)) =
        ((wordGame P R N).next false)^[j + 1] (liftCfg f c)) ∧
      (∀ j ≤ τ, (((wordGame P R N).next false)^[j] (liftCfg f c)).state ≠ none) ∧
      ((wordGame P R N).next false)^[τ] (liftCfg f c) = liftCfg f (M.runFrom c t) := by
  exact exists_deterministic_phase (wordGame P R N) (liftCfg f) hstep
    (fun _ => by simp [liftCfg]) ht

/-! ### Acceptance and halting -/

/-- `R` performs the update `U` after every move from a position reachable from `w₀`: started on
the position `u :: b :: r` on tape `N`, every other tape blank, it halts within `tR` steps on the
position `U (u :: b :: r)` and uses at most `sR` cells. -/
@[expose] def RoundSpec (R : MultiTapeTM k Bool S₂) (N : Fin k) (input : List Bool)
    (U : List Bool → List Bool) (w₀ : List Bool) (tR sR : ℕ) : Prop :=
  ∀ u x r, Reach U w₀ (u :: x :: r) → ∀ b,
    R.runFrom (wordsCfg input (some R.q₀) (Function.update (fun _ => []) N (u :: b :: r)) []) tR =
      wordsCfg input none (Function.update (fun _ => []) N (U (u :: b :: r))) [] ∧
    (MultiTapeNTM.RunPath.ofDeterministic R
      (wordsCfg input (some R.q₀) (Function.update (fun _ => []) N (u :: b :: r)) []) tR).space ≤
        sR

/-- Every reachable round computes the update and halts. Its time may depend on the position
and move; no common time or space bound is part of this semantic contract. -/
@[expose] def RoundComputes (R : MultiTapeTM k Bool S₂) (N : Fin k) (input : List Bool)
    (U : List Bool → List Bool) (w₀ : List Bool) : Prop :=
  ∀ u x r, Reach U w₀ (u :: x :: r) → ∀ b, ∃ t,
    R.runFrom (wordsCfg input (some R.q₀) (Function.update (fun _ => []) N (u :: b :: r)) []) t =
      wordsCfg input none (Function.update (fun _ => []) N (U (u :: b :: r))) []

/-- A uniformly bounded round implementation computes every reachable update. -/
theorem RoundSpec.computes {R : MultiTapeTM k Bool S₂} {N : Fin k} {input : List Bool}
    {U : List Bool → List Bool} {w₀ : List Bool} {tR sR : ℕ}
    (h : RoundSpec R N input U w₀ tR sR) : RoundComputes R N input U w₀ :=
  fun u x r hr b => ⟨tR, (h u x r hr b).1⟩

variable {U : List Bool → List Bool} {w₀ : List Bool} {tR sR : ℕ}

private theorem liftCfg_round_wordsCfg (q : Option S₂) (ws : Fin k → List Bool) :
    liftCfg (S₁ := S₁) .round (wordsCfg input q ws []) =
      wordsCfg input (some (q.elim .disp0 .round)) ws [] := rfl

/-- A round can change persistent storage without resetting other work heads. -/
theorem exists_round_storage {v v' : List Bool}
    (storage storage' : Cfg k Bool Unit input)
    (hrun : R.runFrom
      ((cfg (S₁ := S₁) (S₂ := S₂) N none v 0 [] storage).withState (some R.q₀)) tR =
      (cfg (S₁ := S₁) (S₂ := S₂) N none v' 0 [] storage').withState none) :
    ∃ τ ≤ tR, (∀ j < τ, ∀ b, (wordGame P R N).next b
      (((wordGame P R N).next false)^[j] (cfg N (some (.round R.q₀)) v 0 [] storage)) =
      ((wordGame P R N).next false)^[j + 1] (cfg N (some (.round R.q₀)) v 0 [] storage)) ∧
      (∀ j ≤ τ, (((wordGame P R N).next false)^[j]
        (cfg N (some (.round R.q₀)) v 0 [] storage)).state ≠ none) ∧
      ((wordGame P R N).next false)^[τ] (cfg N (some (.round R.q₀)) v 0 [] storage) =
        cfg N (some .disp0) v' 0 [] storage' := by
  have hstep : ∀ b (c : Cfg k Bool S₂ input), c.state ≠ none →
      (wordGame P R N).next b (liftCfg .round c) = liftCfg .round (R.step c) :=
    fun b c h => next_liftCfg_round b h
  obtain ⟨τ, hτ, h1, h2, h3⟩ := exists_phase .round hstep (hrun ▸ rfl : (R.runFrom
    ((cfg (S₁ := S₁) (S₂ := S₂) N none v 0 [] storage).withState (some R.q₀)) tR).state = none)
  rw [hrun] at h3
  exact ⟨τ, hτ, h1, h2, h3⟩

private theorem exists_round {v v' : List Bool}
    (hrun : R.runFrom (wordsCfg input (some R.q₀) (Function.update (fun _ => []) N v) []) tR =
      wordsCfg input none (Function.update (fun _ => []) N v') []) :
    ∃ τ ≤ tR, (∀ j < τ, ∀ b, (wordGame P R N).next b (((wordGame P R N).next false)^[j]
        (cfg (input := input) N (some (.round R.q₀)) v 0 [])) =
        ((wordGame P R N).next false)^[j + 1] (cfg N (some (.round R.q₀)) v 0 [])) ∧
      (∀ j ≤ τ, (((wordGame P R N).next false)^[j]
        (cfg (input := input) N (some (.round R.q₀)) v 0 [])).state ≠ none) ∧
      ((wordGame P R N).next false)^[τ] (cfg (input := input) N (some (.round R.q₀)) v 0 []) =
        cfg N (some .disp0) v' 0 [] := by
  exact exists_round_storage
    ⟨none, 1, fun _ _ => none, fun _ => 0, []⟩
    ⟨none, 1, fun _ _ => none, fun _ => 0, []⟩ (by
      simpa only [cfg_zero, wordsCfg, Cfg.withState] using hrun)

/-- The dispatch configuration on the position `w`. -/
private abbrev dcfg (N : Fin k) (w : List Bool) : Cfg k Bool (State S₁ S₂) input :=
  cfg N (some .disp0) w 0 []

/-- The finite winning plays of an indexed game whose header chooses the player. The
remaining position can live on persistent work tapes instead of being copied into the header. -/
inductive StorageWins {α : Type*} (header : α → List Bool) (next : α → Bool → α) : α → Prop
  | accept (a) : header a = [true] → StorageWins header next a
  | existsMove (a) (x : Bool) (r : List Bool) (b : Bool) :
      header a = false :: x :: r → StorageWins header next (next a b) →
      StorageWins header next a
  | forallMove (a) (x : Bool) (r : List Bool) : header a = true :: x :: r →
      (∀ b, StorageWins header next (next a b)) → StorageWins header next a

/-- Native correctness of each reachable round on persistent work storage. -/
@[expose] def StorageRounds {α : Type*} (R : MultiTapeTM k Bool S₂) (N : Fin k)
    (header : α → List Bool) (storage : α → Cfg k Bool Unit input)
    (next : α → Bool → α) (valid : α → Prop) : Prop :=
  ∀ a, valid a → ∀ u x r, header a = u :: x :: r → ∀ b,
    valid (next a b) ∧ ∃ t, R.runFrom
      ((cfg (S₁ := Unit) (S₂ := S₂) N none (u :: b :: r) 0 [] (storage a)).withState
        (some R.q₀)) t =
      (cfg (S₁ := Unit) (S₂ := S₂) N none (header (next a b)) 0 []
        (storage (next a b))).withState none

section StorageSemantics

variable {α : Type*} {header : α → List Bool} {storage : α → Cfg k Bool Unit input}
  {next : α → Bool → α} {valid : α → Prop}

private theorem acceptsWithin_of_storageWins (hR : StorageRounds R N header storage next valid)
    {a : α} (hw : StorageWins header next a) (ha : valid a) :
    ∃ n, (wordGame P R N).AcceptsWithin n (cfg N (some .disp0) (header a) 0 [] (storage a)) := by
  induction hw with
  | accept a he =>
    refine ⟨2, ?_⟩
    rw [he, acceptsWithin_succ_of_next_eq (next_disp0_cons P R N · true [] (storage a)),
      acceptsWithin_succ_of_next_eq (next_disp1_halt P R N · true rfl (storage a)),
      acceptsWithin_of_halted _ rfl]
    rfl
  | existsMove a x r b he hwin ih =>
    obtain ⟨hv, t, ht⟩ := hR a ha false x r he b
    obtain ⟨n, hn⟩ := ih hv
    obtain ⟨τ, -, hnext, hrun, hd⟩ := exists_round_storage (P := P) (storage a)
      (storage (next a b)) ht
    refine ⟨n + τ + 3, ?_⟩
    rw [he, acceptsWithin_succ_of_next_eq (next_disp0_cons P R N · false (x :: r) (storage a)),
      acceptsWithin_succ_of_next_eq (next_disp1_move P R N · false x rfl (storage a)),
      acceptsWithin_succ_of_existential _ rfl rfl]
    refine ⟨b, ?_⟩
    rw [next_move P R N b false (by simp) (storage a), List.set_cons_succ, List.set_cons_zero,
      acceptsWithin_iff_of_phase hnext hrun hd]
    simpa using hn
  | forallMove a x r he hwin ih =>
    have h (b : Bool) := ih b (hR a ha true x r he b).1
    choose n hn using h
    have hr (b : Bool) := exists_round_storage (P := P) (storage a) (storage (next a b))
      (hR a ha true x r he b).2.choose_spec
    choose τ hτ hnext hrun hd using hr
    refine ⟨max (n false + τ false) (n true + τ true) + 3, ?_⟩
    rw [he, acceptsWithin_succ_of_next_eq (next_disp0_cons P R N · true (x :: r) (storage a)),
      acceptsWithin_succ_of_next_eq (next_disp1_move P R N · true x rfl (storage a)),
      acceptsWithin_succ_of_universal _ rfl rfl]
    intro b
    rw [next_move P R N b true (by simp) (storage a), List.set_cons_succ, List.set_cons_zero,
      acceptsWithin_iff_of_phase (hnext b) (hrun b) (hd b)]
    have hle : n b + τ b ≤ max (n false + τ false) (n true + τ true) := by
      cases b
      · exact le_max_left _ _
      · exact le_max_right _ _
    exact ⟨by omega, (hn b).mono (by omega)⟩

private theorem storageWins_of_acceptsWithin (hR : StorageRounds R N header storage next valid)
    (n : ℕ) : ∀ a, valid a → (wordGame P R N).AcceptsWithin n
      (cfg N (some .disp0) (header a) 0 [] (storage a)) → StorageWins header next a := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a ha hacc
  rcases he : header a with _ | ⟨u, _ | ⟨x, r⟩⟩ <;> rw [he] at hacc
  · rcases n with _ | m
    · exact absurd hacc (not_acceptsWithin_zero _ rfl)
    · rw [acceptsWithin_succ_of_next_eq (next_disp0_nil P R N · (storage a)),
        acceptsWithin_of_halted _ rfl]
        at hacc
      simp [cfg] at hacc
  · rcases n with _ | _ | m
    · exact absurd hacc (not_acceptsWithin_zero _ rfl)
    · rw [acceptsWithin_succ_of_next_eq (next_disp0_cons P R N · u [] (storage a))] at hacc
      exact absurd hacc (not_acceptsWithin_zero _ rfl)
    · rw [acceptsWithin_succ_of_next_eq (next_disp0_cons P R N · u [] (storage a)),
        acceptsWithin_succ_of_next_eq (next_disp1_halt P R N · u rfl (storage a)),
        acceptsWithin_of_halted _ rfl] at hacc
      cases u
      · simp [cfg] at hacc
      · exact StorageWins.accept a he
  · rcases n with _ | _ | _ | m
    · exact absurd hacc (not_acceptsWithin_zero _ rfl)
    · rw [acceptsWithin_succ_of_next_eq (next_disp0_cons P R N · u (x :: r) (storage a))] at hacc
      exact absurd hacc (not_acceptsWithin_zero _ rfl)
    · rw [acceptsWithin_succ_of_next_eq (next_disp0_cons P R N · u (x :: r) (storage a)),
        acceptsWithin_succ_of_next_eq (next_disp1_move P R N · u x rfl (storage a))] at hacc
      exact absurd hacc (not_acceptsWithin_zero _ rfl)
    · rw [acceptsWithin_succ_of_next_eq (next_disp0_cons P R N · u (x :: r) (storage a)),
        acceptsWithin_succ_of_next_eq (next_disp1_move P R N · u x rfl (storage a))] at hacc
      cases u
      · rw [acceptsWithin_succ_of_existential _ rfl rfl] at hacc
        obtain ⟨b, hb⟩ := hacc
        obtain ⟨hv, t, ht⟩ := hR a ha false x r he b
        obtain ⟨τ, -, hnext, hrun, hd⟩ := exists_round_storage (P := P)
          (storage a) (storage (next a b)) ht
        rw [next_move P R N b false (by simp) (storage a), List.set_cons_succ, List.set_cons_zero,
          acceptsWithin_iff_of_phase hnext hrun hd] at hb
        exact StorageWins.existsMove a x r b he (ih (m - τ) (by omega) _ hv hb.2)
      · rw [acceptsWithin_succ_of_universal _ rfl rfl] at hacc
        refine StorageWins.forallMove a x r he fun b => ?_
        have hb := hacc b
        obtain ⟨hv, t, ht⟩ := hR a ha true x r he b
        obtain ⟨τ, -, hnext, hrun, hd⟩ := exists_round_storage (P := P)
          (storage a) (storage (next a b)) ht
        rw [next_move P R N b true (by simp) (storage a), List.set_cons_succ, List.set_cons_zero,
          acceptsWithin_iff_of_phase hnext hrun hd] at hb
        exact ih (m - τ) (by omega) _ hv hb.2

/-- The existing native word-game dispatcher implements an indexed game on persistent storage.
Every native round is explicitly supplied; the theorem assumes no oracle access to positions. -/
theorem accepts_storage_iff (hR : StorageRounds R N header storage next valid) (a : α)
    (ha : valid a) :
    (∃ n, (wordGame P R N).AcceptsWithin n
      (cfg N (some .disp0) (header a) 0 [] (storage a))) ↔ StorageWins header next a := by
  constructor
  · rintro ⟨n, hn⟩
    exact storageWins_of_acceptsWithin hR n a ha hn
  · exact fun h => acceptsWithin_of_storageWins hR h ha

private theorem storageWins_words_iff (w : List Bool) :
    StorageWins id (fun w b => U (w.set 1 b)) w ↔ Wins U w := by
  constructor
  · intro h
    induction h with
    | accept a he => change a = [true] at he; subst a; exact Wins.accept
    | existsMove a x r b he hw ih =>
      change a = false :: x :: r at he
      subst a
      exact Wins.existsMove b (by simpa using ih)
    | forallMove a x r he hw ih =>
      change a = true :: x :: r at he
      subst a
      exact Wins.forallMove fun b => by simpa using ih b
  · intro h
    induction h with
    | accept => exact .accept _ rfl
    | existsMove b hw ih => exact .existsMove _ _ _ b rfl (by simpa using ih)
    | forallMove hw ih => exact .forallMove _ _ _ rfl fun b => by simpa using ih b

private theorem storageRounds_words (hR : RoundComputes R N input U w₀) :
    StorageRounds (input := input) R N id (fun _ => ⟨none, 1, fun _ _ => none, fun _ => 0, []⟩)
      (fun w b => U (w.set 1 b)) (Reach U w₀) := by
  intro w hw u x r he b
  change w = u :: x :: r at he
  subst w
  refine ⟨by simpa using Reach.move b hw, ?_⟩
  obtain ⟨t, ht⟩ := hR u x r hw b
  exact ⟨t, by simpa only [List.set_cons_succ, List.set_cons_zero, id_eq,
    cfg_zero, wordsCfg, Cfg.withState] using ht⟩

private theorem acceptsWithin_of_wins (hR : RoundComputes R N input U w₀) {w : List Bool}
    (hw : Wins U w) (hreach : Reach U w₀ w) :
    ∃ n, (wordGame P R N).AcceptsWithin n (dcfg (input := input) N w) :=
  acceptsWithin_of_storageWins (storageRounds_words hR) ((storageWins_words_iff w).mpr hw) hreach

private theorem wins_of_acceptsWithin (hR : RoundComputes R N input U w₀) (n : ℕ) :
    ∀ w, Reach U w₀ w → (wordGame P R N).AcceptsWithin n (dcfg (input := input) N w) →
      Wins U w := fun w hw hn =>
  (storageWins_words_iff w).mp (storageWins_of_acceptsWithin (storageRounds_words hR) n w hw hn)

end StorageSemantics

/-- A potential pays for native rounds on persistent work storage. Only the control tape is
normalized at dispatch. Other tapes, their cursors, and the input cursor belong to `storage`.
Each round pays its actual deterministic time and three dispatch steps; terminals cost at most
two steps. The potential is proof-only and entails no free computational access. -/
theorem haltsWithin_storage_of_potential {α : Type*}
    (header : α → List Bool) (storage : α → Cfg k Bool Unit input)
    (next : α → Bool → α) (valid : α → Prop) (potential : α → ℕ)
    (hR : ∀ a, valid a → ∀ u x r, header a = u :: x :: r → ∀ b, ∃ t,
      R.runFrom
        ((cfg (S₁ := S₁) (S₂ := S₂) N none (u :: b :: r) 0 [] (storage a)).withState
          (some R.q₀)) t =
        (cfg (S₁ := S₁) (S₂ := S₂) N none (header (next a b)) 0 []
          (storage (next a b))).withState none ∧
      t + 3 + potential (next a b) ≤ potential a ∧ valid (next a b)) :
    ∀ a, valid a → (wordGame P R N).HaltsWithin (potential a + 2)
      (cfg N (some .disp0) (header a) 0 [] (storage a)) := by
  have h (n : ℕ) : ∀ a, potential a = n → valid a →
      (wordGame P R N).HaltsWithin (n + 2)
        (cfg N (some .disp0) (header a) 0 [] (storage a)) := by
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro a hn ha
      rcases he : header a with _ | ⟨u, _ | ⟨x, r⟩⟩
      · exact haltsWithin_succ.mpr fun b => by
          rw [next_disp0_nil P R N b (storage a)]
          exact haltsWithin_of_halted rfl
      · exact haltsWithin_succ.mpr fun b => by
          rw [next_disp0_cons P R N b u [] (storage a)]
          exact haltsWithin_succ.mpr fun b' => by
            rw [next_disp1_halt P R N b' u rfl (storage a)]
            exact haltsWithin_of_halted rfl
      · have hnpos : 1 ≤ n := by
          obtain ⟨t, _, ht, _⟩ := hR a ha u x r he false
          omega
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        refine haltsWithin_succ.mpr fun b₀ => ?_
        rw [next_disp0_cons P R N b₀ u (x :: r) (storage a)]
        refine haltsWithin_succ.mpr fun b₁ => ?_
        rw [next_disp1_move P R N b₁ u x rfl (storage a)]
        refine haltsWithin_succ.mpr fun b => ?_
        obtain ⟨t, hrunR, ht, hv⟩ := hR a ha u x r he b
        obtain ⟨τ, hτ, hnext, hrun, hd⟩ := exists_round_storage (P := P)
          (storage a) (storage (next a b)) hrunR
        rw [next_move P R N b u (by simp) (storage a), List.set_cons_succ,
          List.set_cons_zero, haltsWithin_iff_of_phase hnext hrun hd]
        exact ⟨by omega, (ih _ (by omega) _ rfl hv).mono (by omega)⟩
  exact fun a ha => h _ a rfl ha

private theorem haltsWithin_of_potential (potential : List Bool → ℕ)
    (hR : ∀ u x r, Reach U w₀ (u :: x :: r) → ∀ b, ∃ t,
      R.runFrom (wordsCfg input (some R.q₀)
          (Function.update (fun _ => []) N (u :: b :: r)) []) t =
        wordsCfg input none (Function.update (fun _ => []) N (U (u :: b :: r))) [] ∧
      t + 3 + potential (U (u :: b :: r)) ≤ potential (u :: x :: r)) :
    ∀ w, Reach U w₀ w →
      (wordGame P R N).HaltsWithin (potential w + 2) (dcfg (input := input) N w) := by
  apply haltsWithin_storage_of_potential (P := P) (R := R) (N := N) id
    (fun _ => ⟨none, 1, fun _ _ => none, fun _ => 0, []⟩)
    (fun w b => U (w.set 1 b)) (Reach U w₀) potential
  intro w hw u x r he b
  change w = u :: x :: r at he
  subst w
  obtain ⟨t, hr, ht⟩ := hR u x r hw b
  refine ⟨t, ?_, ?_, ?_⟩
  · simpa only [List.set_cons_succ, List.set_cons_zero, id_eq, cfg_zero,
      wordsCfg, Cfg.withState] using hr
  · simpa only [List.set_cons_succ, List.set_cons_zero] using ht
  · simpa only [List.set_cons_succ, List.set_cons_zero] using Reach.move b hw

private theorem haltsWithin_of_ends (hR : RoundSpec R N input U w₀ tR sR) (n : ℕ) :
    ∀ w, Reach U w₀ w → Ends U n w →
      (wordGame P R N).HaltsWithin (n * (tR + 3) + 2) (dcfg (input := input) N w) := by
  classical
  intro w hw hn
  let depth (v : List Bool) : ℕ := if h : ∃ m, Ends U m v then Nat.find h else 0
  have hdepth (v : List Bool) (hv : ∃ m, Ends U m v) :
      Ends U (depth v) v ∧ ∀ m, Ends U m v → depth v ≤ m := by
    simp only [depth, hv, ↓reduceDIte]
    exact ⟨Nat.find_spec hv, fun _ hm => Nat.find_min' hv hm⟩
  have hreach (v : List Bool) (hv : Reach U w v) : Reach U w₀ v := by
    induction hv with
    | start => exact hw
    | move b _ ih => exact .move b ih
  have hbudget := haltsWithin_of_potential (P := P) (R := R) (N := N)
    (input := input) (U := U) (w₀ := w) (fun v => depth v * (tR + 3))
    (fun u x r hr b => by
      have hd := (hdepth _ ⟨n, hn.of_reach hr⟩).1
      have hpos : 0 < depth (u :: x :: r) := by
        cases he : depth (u :: x :: r) with
        | zero => rw [he] at hd; exact hd.elim
        | succ m => omega
      obtain ⟨m, hm⟩ : ∃ m, depth (u :: x :: r) = m + 1 :=
        ⟨depth (u :: x :: r) - 1, by omega⟩
      rw [hm] at hd
      have hchild := (hdepth _ ⟨m, hd b⟩).2 m (hd b)
      refine ⟨tR, (hR u x r (hreach _ hr) b).1, ?_⟩
      have := Nat.mul_le_mul_right (tR + 3) hchild
      rw [hm, Nat.succ_mul]
      omega)
  exact (hbudget w .start).mono (by
    have := Nat.mul_le_mul_right (tR + 3) ((hdepth w ⟨n, hn⟩).2 n hn)
    omega)

/-! ### Space -/

/-- `P` writes the initial position `w₀` on tape `N`: started on `input`, it halts within `tP`
steps with `w₀` on tape `N` and every other tape blank, using at most `sP` cells. -/
@[expose] def PrepSpec (P : MultiTapeTM k Bool S₁) (N : Fin k) (input : List Bool) (w₀ : List Bool)
    (tP sP : ℕ) : Prop :=
  P.runFrom (Cfg.init P.q₀ input) tP =
      wordsCfg input none (Function.update (fun _ => []) N w₀) [] ∧
    (MultiTapeNTM.RunPath.ofDeterministic P (Cfg.init P.q₀ input) tP).space ≤ sP

/-- The configurations met by the word game machine: a configuration of the preparation within
`tP` steps, of a round from a reachable position within `tR` steps, a dispatch configuration on a
reachable position, or a halted configuration with its heads at `0` or `1`. -/
private inductive Good (P : MultiTapeTM k Bool S₁) (R : MultiTapeTM k Bool S₂) (N : Fin k)
    (input : List Bool) (U : List Bool → List Bool) (w₀ : List Bool) (tP tR : ℕ) :
    Cfg k Bool (State S₁ S₂) input → Prop
  | prep (j : ℕ) : j ≤ tP → Good P R N input U w₀ tP tR
      (liftCfg .prep (P.runFrom (Cfg.init P.q₀ input) j))
  | round {u x : Bool} {r : List Bool} (b : Bool) (j : ℕ) : Reach U w₀ (u :: x :: r) → j ≤ tR →
      Good P R N input U w₀ tP tR (liftCfg .round (R.runFrom
        (wordsCfg input (some R.q₀) (Function.update (fun _ => []) N (u :: b :: r)) []) j))
  | d0 (w : List Bool) : Reach U w₀ w → Good P R N input U w₀ tP tR (dcfg N w)
  | d1 (u : Bool) (r : List Bool) : Reach U w₀ (u :: r) →
      Good P R N input U w₀ tP tR (cfg N (some (.disp1 u)) (u :: r) 1 [])
  | dm {u x : Bool} {r : List Bool} : Reach U w₀ (u :: x :: r) →
      Good P R N input U w₀ tP tR (cfg N (some (.move u)) (u :: x :: r) 1 [])
  | halted (c : Cfg k Bool (State S₁ S₂) input) : c.state = none →
      (∀ i, c.workTapePos i ∈ window 1) → Good P R N input U w₀ tP tR c

variable {tP sP : ℕ}

private theorem workTapePos_cfg_mem {q : Option (State S₁ S₂)} {w : List Bool} {pos S : ℕ}
    {out : List Bool} (hpos : pos ≤ S) (i : Fin k) :
    (cfg (input := input) N q w pos out).workTapePos i ∈ window S := by
  by_cases hi : i = N <;> simp [cfg, hi, mem_window, hpos]

private theorem good_next_dcfg {w : List Bool} (hw : Reach U w₀ w) (b : Bool) :
    Good P R N input U w₀ tP tR ((wordGame P R N).next b (dcfg N w)) := by
  rcases w with _ | ⟨u, r⟩
  · rw [next_disp0_nil P R N]
    exact .halted _ rfl (workTapePos_cfg_mem (Nat.zero_le 1))
  · rw [next_disp0_cons P R N]
    exact .d1 u r hw

private theorem Good.next (hP : PrepSpec P N input w₀ tP sP)
    (hR : RoundSpec R N input U w₀ tR sR) {c : Cfg k Bool (State S₁ S₂) input}
    (hc : Good P R N input U w₀ tP tR c) (b : Bool) :
    Good P R N input U w₀ tP tR ((wordGame P R N).next b c) := by
  cases hc with
  | prep j hj =>
    by_cases hs : (P.runFrom (Cfg.init P.q₀ input) j).state = none
    · rw [← MultiTapeTM.runFrom_eq_of_halt P _ hj hs, hP.1]
      have : liftCfg (S₂ := S₂) .prep
          (wordsCfg input none (Function.update (fun _ => []) N w₀) []) =
          dcfg (S₁ := S₁) N w₀ :=
        (cfg_zero _ _ _).symm
      rw [this]
      exact good_next_dcfg .start b
    · rw [next_liftCfg_prep b hs]
      have hj' : j < tP := by
        rcases Nat.lt_or_eq_of_le hj with h | rfl
        · exact h
        · exact absurd (by rw [hP.1]; rfl) hs
      have := Good.prep (P := P) (R := R) (N := N) (input := input) (U := U) (w₀ := w₀)
        (tR := tR) (j + 1) (show j + 1 ≤ tP by omega)
      simpa only [MultiTapeTM.runFrom, Function.iterate_succ_apply'] using this
  | @round u x r b' j hreach hj =>
    obtain ⟨hrun, -⟩ := hR u x r hreach b'
    by_cases hs : (R.runFrom (wordsCfg input (some R.q₀)
        (Function.update (fun _ => []) N (u :: b' :: r)) []) j).state = none
    · rw [← MultiTapeTM.runFrom_eq_of_halt R _ hj hs, hrun]
      have : liftCfg (S₁ := S₁) .round
          (wordsCfg input none (Function.update (fun _ => []) N (U (u :: b' :: r))) []) =
          dcfg (S₂ := S₂) N (U (u :: b' :: r)) :=
        (cfg_zero _ _ _).symm
      rw [this]
      exact good_next_dcfg (Reach.move b' hreach) b
    · rw [next_liftCfg_round b hs]
      have hj' : j < tR := by
        rcases Nat.lt_or_eq_of_le hj with h | rfl
        · exact h
        · exact absurd (by rw [hrun]; rfl) hs
      have := Good.round (P := P) (R := R) (N := N) (input := input) (tP := tP) (tR := tR) b'
        (j + 1) hreach (show j + 1 ≤ tR by omega)
      simpa only [MultiTapeTM.runFrom, Function.iterate_succ_apply'] using this
  | d0 w hw => exact good_next_dcfg hw b
  | d1 u r hw =>
    rcases r with _ | ⟨x, r⟩
    · rw [next_disp1_halt P R N b u rfl]
      exact .halted _ rfl (workTapePos_cfg_mem le_rfl)
    · rw [next_disp1_move P R N b u x rfl]
      exact .dm hw
  | @dm u x r hw =>
    rw [next_move P R N b u (by simp), List.set_cons_succ, List.set_cons_zero]
    have := Good.round (P := P) (R := R) (N := N) (input := input) (tP := tP) (tR := tR) b 0 hw
      (Nat.zero_le _)
    rwa [MultiTapeTM.runFrom, Function.iterate_zero, id, liftCfg_round_wordsCfg,
      ← cfg_zero] at this
  | halted c hs hpos =>
    rw [next_of_halted _ hs]
    exact .halted c hs hpos

private theorem mem_window_of_le {S : ℕ} {z : ℤ} {s : ℕ} (h : z ∈ window s) (hs : s ≤ S) :
    z ∈ window S :=
  mem_window.mpr ((mem_window.mp h).trans hs)

private theorem Good.workTapePos_mem (hP : PrepSpec P N input w₀ tP sP)
    (hR : RoundSpec R N input U w₀ tR sR) {S : ℕ} (hSP : sP ≤ S) (hSR : sR ≤ S) (hS : 1 ≤ S)
    {c : Cfg k Bool (State S₁ S₂) input} (hc : Good P R N input U w₀ tP tR c) (i : Fin k) :
    c.workTapePos i ∈ window S := by
  cases hc with
  | prep j hj =>
    have hwin := MultiTapeNTM.RunPath.inWindow_of_space_le
      (p := MultiTapeNTM.RunPath.ofDeterministic P (Cfg.init P.q₀ input) tP)
      (fun i => rfl) hP.2
    exact mem_window_of_le (hwin _ ⟨⟨j, Nat.lt_succ_of_le hj⟩, rfl⟩ i) hSP
  | @round u x r b j hreach hj =>
    have hwin := MultiTapeNTM.RunPath.inWindow_of_space_le
      (p := MultiTapeNTM.RunPath.ofDeterministic R
        (wordsCfg input (some R.q₀) (Function.update (fun _ => []) N (u :: b :: r)) []) tR)
      (fun i => rfl) (hR u x r hreach b).2
    exact mem_window_of_le (hwin _ ⟨⟨j, Nat.lt_succ_of_le hj⟩, rfl⟩ i) hSR
  | d0 w hw => exact workTapePos_cfg_mem (Nat.zero_le S) i
  | d1 u r hw => exact workTapePos_cfg_mem hS i
  | dm hw => exact workTapePos_cfg_mem hS i
  | halted c hs hpos => exact mem_window_of_le (hpos i) hS

private theorem initCfg_wordGame :
    (wordGame P R N).toPTM.toNTM.initCfg input = liftCfg .prep (Cfg.init P.q₀ input) := rfl

private theorem good_of_mem (hP : PrepSpec P N input w₀ tP sP)
    (hR : RoundSpec R N input U w₀ tR sR) (p : (wordGame P R N).toPTM.toNTM.ComputationPath input) :
    ∀ c ∈ p.toRunPath, Good P R N input U w₀ tP tR c := by
  rintro _ ⟨i, rfl⟩
  induction i using Fin.induction with
  | zero =>
    have h0 : p.toRunPath 0 = (wordGame P R N).toPTM.toNTM.initCfg input := p.head_eq
    rw [h0, initCfg_wordGame]
    exact .prep 0 (Nat.zero_le _)
  | succ i ih =>
    obtain ⟨b, hb⟩ := (MultiTapePTM.step_toNTM_iff (wordGame P R N).toPTM).mp (p.step i)
    have : p.toRunPath i.succ = (wordGame P R N).next b (p.toRunPath i.castSucc) := hb.symm
    rw [this]
    exact ih.next hP hR b

private theorem exists_prep
    (hP : P.runFrom (Cfg.init P.q₀ input) tP =
      wordsCfg input none (Function.update (fun _ => []) N w₀) []) :
    ∃ τ ≤ tP, (∀ j < τ, ∀ b, (wordGame P R N).next b (((wordGame P R N).next false)^[j]
        ((wordGame P R N).toPTM.toNTM.initCfg input)) =
        ((wordGame P R N).next false)^[j + 1] ((wordGame P R N).toPTM.toNTM.initCfg input)) ∧
      (∀ j ≤ τ, (((wordGame P R N).next false)^[j]
        ((wordGame P R N).toPTM.toNTM.initCfg input)).state ≠ none) ∧
      ((wordGame P R N).next false)^[τ] ((wordGame P R N).toPTM.toNTM.initCfg input) =
        dcfg N w₀ := by
  have hstep : ∀ b (c : Cfg k Bool S₁ input), c.state ≠ none →
      (wordGame P R N).next b (liftCfg .prep c) = liftCfg .prep (P.step c) :=
    fun b c h => next_liftCfg_prep b h
  obtain ⟨τ, hτ, h1, h2, h3⟩ := exists_phase .prep hstep (hP ▸ rfl : (P.runFrom
    (Cfg.init P.q₀ input) tP).state = none)
  rw [hP] at h3
  exact ⟨τ, hτ, h1, h2, h3.trans (cfg_zero _ _ _).symm⟩

end WordGame

open WordGame in
/-- **A potential pays for the time of a word game.** Suppose `P` writes `w₀` in `tP` steps,
and, after each move from a reachable position, `R` writes the next position in some `t` steps.
If the potential drops by at least `t + 3`, every branch halts within
`tP + potential w₀ + 2` steps. The three steps dispatch and choose the move; the final two
inspect a terminal word. Round times may depend on the position and on the chosen move.

This is an actual machine-time bound. The potential is used only in the proof and need not be
computable. The hypothesis must account for both moves, including losing plays. -/
theorem runsInTime_wordGame_of_potential {k : ℕ} {S₁ S₂ : Type}
    {P : MultiTapeTM k Bool S₁} {R : MultiTapeTM k Bool S₂} {N : Fin k}
    {input : List Bool} {U : List Bool → List Bool} {w₀ : List Bool} {tP : ℕ}
    (potential : List Bool → ℕ)
    (hP : P.runFrom (Cfg.init P.q₀ input) tP =
      wordsCfg input none (Function.update (fun _ => []) N w₀) [])
    (hR : ∀ u x r, Reach U w₀ (u :: x :: r) → ∀ b, ∃ t,
      R.runFrom (wordsCfg input (some R.q₀)
          (Function.update (fun _ => []) N (u :: b :: r)) []) t =
        wordsCfg input none (Function.update (fun _ => []) N (U (u :: b :: r))) [] ∧
      t + 3 + potential (U (u :: b :: r)) ≤ potential (u :: x :: r)) :
    (wordGame P R N).toPTM.toNTM.RunsInTime input (tP + (potential w₀ + 2)) := by
  obtain ⟨τ, hτ, hnext, hrun, hd⟩ := exists_prep (R := R) (N := N) hP
  rw [runsInTime_iff_haltsWithin, haltsWithin_iff_of_phase hnext hrun hd]
  exact ⟨by omega, (haltsWithin_of_potential (P := P) potential hR w₀ .start).mono (by omega)⟩

open WordGame in
/-- The native machine accepts exactly the winning positions whenever preparation and every
reachable round halt with the specified words. Round times need not have a common bound. -/
theorem accepts_wordGame_iff_of_computes {k : ℕ} {S₁ S₂ : Type}
    {P : MultiTapeTM k Bool S₁} {R : MultiTapeTM k Bool S₂} {N : Fin k}
    {input w₀ : List Bool} {U : List Bool → List Bool} {tP : ℕ}
    (hP : P.runFrom (Cfg.init P.q₀ input) tP =
      wordsCfg input none (Function.update (fun _ => []) N w₀) [])
    (hR : RoundComputes R N input U w₀) :
    (wordGame P R N).Accepts input ↔ Wins U w₀ := by
  obtain ⟨τ, hτ, hnext, hrun, hd⟩ := exists_prep (R := R) hP
  constructor
  · rintro ⟨n, hn⟩
    rw [acceptsWithin_iff_of_phase hnext hrun hd] at hn
    exact wins_of_acceptsWithin hR _ w₀ .start hn.2
  · intro hw
    obtain ⟨n, hn⟩ := acceptsWithin_of_wins (P := P) hR hw .start
    exact ⟨n + τ, (acceptsWithin_iff_of_phase hnext hrun hd _).mpr (by simpa using hn)⟩

open WordGame in
/-- **The word game machine plays the word game.** If `P` writes the initial position `w₀` within
`tP` steps and `sP` cells, and `R` performs the update `U` after every move from a reachable
position within `tR` steps and `sR` cells, then every computation path of the machine stays within
`k * (2 * max (max sP sR) 1 + 1)` cells, the machine accepts exactly when the existential player
wins the game from `w₀`, and if every play ends within `n` moves, every branch halts within
`tP + (n * (tR + 3) + 2)` steps. -/
theorem wordGame_spec {k : ℕ} {S₁ S₂ : Type} {P : MultiTapeTM k Bool S₁}
    {R : MultiTapeTM k Bool S₂} {N : Fin k} {input : List Bool} {U : List Bool → List Bool}
    {w₀ : List Bool} {tP sP tR sR : ℕ} (hP : PrepSpec P N input w₀ tP sP)
    (hR : RoundSpec R N input U w₀ tR sR) :
    (wordGame P R N).toPTM.toNTM.RunsInSpace input (k * (2 * max (max sP sR) 1 + 1)) ∧
      ((wordGame P R N).Accepts input ↔ Wins U w₀) ∧
      ∀ n, Ends U n w₀ →
        (wordGame P R N).toPTM.toNTM.RunsInTime input (tP + (n * (tR + 3) + 2)) := by
  obtain ⟨τ, hτ, hnext, hrun, hd⟩ := exists_prep (R := R) hP.1
  refine ⟨fun p => ?_, accepts_wordGame_iff_of_computes hP.1 hR.computes, fun n hn => ?_⟩
  · refine MultiTapeNTM.RunPath.InWindow.space_le fun c hc i => ?_
    exact (good_of_mem hP hR p c hc).workTapePos_mem hP hR
      ((le_max_left _ _).trans (le_max_left _ _)) ((le_max_right _ _).trans (le_max_left _ _))
      (le_max_right _ _) i
  · rw [runsInTime_iff_haltsWithin, haltsWithin_iff_of_phase hnext hrun hd]
    exact ⟨by omega, (haltsWithin_of_ends (P := P) hR n w₀ .start hn).mono (by omega)⟩

open WordGame in
/-- The space part of `Turing.MultiTapeATM.wordGame_spec`: every computation path of the word game
machine stays within the space of the preparation and of one round. -/
theorem runsInSpace_wordGame {k : ℕ} {S₁ S₂ : Type} {P : MultiTapeTM k Bool S₁}
    {R : MultiTapeTM k Bool S₂} {N : Fin k} {input : List Bool} {U : List Bool → List Bool}
    {w₀ : List Bool} {tP sP tR sR : ℕ} (hP : PrepSpec P N input w₀ tP sP)
    (hR : RoundSpec R N input U w₀ tR sR) :
    (wordGame P R N).toPTM.toNTM.RunsInSpace input (k * (2 * max (max sP sR) 1 + 1)) :=
  (wordGame_spec hP hR).1

open WordGame in
/-- The acceptance part of `Turing.MultiTapeATM.wordGame_spec`: the word game machine accepts
exactly when the existential player wins the game from `w₀`. -/
theorem accepts_wordGame_iff {k : ℕ} {S₁ S₂ : Type} {P : MultiTapeTM k Bool S₁}
    {R : MultiTapeTM k Bool S₂} {N : Fin k} {input : List Bool} {U : List Bool → List Bool}
    {w₀ : List Bool} {tP sP tR sR : ℕ} (hP : PrepSpec P N input w₀ tP sP)
    (hR : RoundSpec R N input U w₀ tR sR) :
    (wordGame P R N).Accepts input ↔ Wins U w₀ :=
  (wordGame_spec hP hR).2.1

open WordGame in
/-- The time part of `Turing.MultiTapeATM.wordGame_spec`: if every play ends within `n` moves,
every branch of the word game machine halts within `tP + (n * (tR + 3) + 2)` steps. -/
theorem runsInTime_wordGame {k : ℕ} {S₁ S₂ : Type} {P : MultiTapeTM k Bool S₁}
    {R : MultiTapeTM k Bool S₂} {N : Fin k} {input : List Bool} {U : List Bool → List Bool}
    {w₀ : List Bool} {tP sP tR sR : ℕ} (hP : PrepSpec P N input w₀ tP sP)
    (hR : RoundSpec R N input U w₀ tR sR) {n : ℕ} (hn : Ends U n w₀) :
    (wordGame P R N).toPTM.toNTM.RunsInTime input (tP + (n * (tR + 3) + 2)) :=
  (wordGame_spec hP hR).2.2 n hn

end Turing.MultiTapeATM
