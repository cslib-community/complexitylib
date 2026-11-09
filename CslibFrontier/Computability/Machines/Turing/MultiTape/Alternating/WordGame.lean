/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.GuessVerify

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
* `Turing.MultiTapeATM.WordGame.PrepSpec`, `Turing.MultiTapeATM.WordGame.RoundSpec`: the
  specifications of the preparing machine and of the round machine.

## Main results

* `Turing.MultiTapeATM.WordGame.wins_false_cons_cons_iff`,
  `Turing.MultiTapeATM.WordGame.wins_true_cons_cons_iff`: won positions of each player.
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
private def liftCfg {S : Type} (f : S → State S₁ S₂) (c : Cfg k Bool S input) :
    Cfg k Bool (State S₁ S₂) input :=
  c.mapState fun st => some (st.elim .disp0 f)

private theorem next_liftCfg_round (b : Bool) {c : Cfg k Bool S₂ input} (h : c.state ≠ none) :
    (wordGame P R N).next b (liftCfg .round c) = liftCfg .round (R.step c) := by
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp h
  have hstate : (liftCfg (S₁ := S₁) .round c).state = some (State.round q) := by
    simp [liftCfg, Cfg.mapState, hq]
  rw [wordGame, next_ofTMs, MultiTapeTM.step_of_state hstate, MultiTapeTM.step_of_state hq]
  simp only [tm, MultiTapeTM.tr_ofTr, tr]
  rfl

private theorem next_liftCfg_prep (b : Bool) {c : Cfg k Bool S₁ input} (h : c.state ≠ none) :
    (wordGame P R N).next b (liftCfg .prep c) = liftCfg .prep (P.step c) := by
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp h
  have hstate : (liftCfg (S₂ := S₂) .prep c).state = some (State.prep q) := by
    simp [liftCfg, Cfg.mapState, hq]
  rw [wordGame, next_ofTMs, MultiTapeTM.step_of_state hstate, MultiTapeTM.step_of_state hq]
  simp only [tm, MultiTapeTM.tr_ofTr, tr]
  rfl

/-- The configuration with the word `w` on tape `N` and its head at `pos`, every other work tape
blank with its head at `0`, the input head at the start, and output `out`. -/
private def cfg (N : Fin k) (q : Option (State S₁ S₂)) (w : List Bool) (pos : ℕ)
    (out : List Bool) : Cfg k Bool (State S₁ S₂) input :=
  ⟨q, 1, Function.update (fun _ _ => none) N (tapeOfList w),
    Function.update (fun _ => 0) N (pos : ℤ), out⟩

private theorem cfg_zero (q : Option (State S₁ S₂)) (w : List Bool) (out : List Bool) :
    cfg (input := input) N q w 0 out =
      wordsCfg input q (Function.update (fun _ => []) N w) out := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> by_cases hi : i = N <;>
    simp [cfg, wordsCfg, hi]

variable (P R N) in
private theorem next_disp0_nil (b : Bool) :
    (wordGame P R N).next b (cfg (input := input) N (some .disp0) [] 0 []) =
      cfg N none [] 0 [] := by
  rw [wordGame, next_ofTMs, MultiTapeTM.step_of_state rfl]
  have hread : (cfg (input := input) N (some (State.disp0 (S₁ := S₁) (S₂ := S₂))) [] 0
      []).workTapeSymbols N = none := by
    simp [Cfg.workTapeSymbols, cfg]
  simp only [tm, MultiTapeTM.tr_ofTr, tr, hread, act]
  refine Cfg.ext rfl (by simp [cfg, moveInputPos_zero]) ?_ ?_ (by simp [cfg]) <;>
    funext i <;> by_cases hi : i = N <;> simp [cfg, hi]

variable (P R N) in
private theorem next_disp0_cons (b u : Bool) (r : List Bool) :
    (wordGame P R N).next b (cfg (input := input) N (some .disp0) (u :: r) 0 []) =
      cfg N (some (.disp1 u)) (u :: r) 1 [] := by
  rw [wordGame, next_ofTMs, MultiTapeTM.step_of_state rfl]
  have hread : (cfg (input := input) N (some (State.disp0 (S₁ := S₁) (S₂ := S₂))) (u :: r) 0
      []).workTapeSymbols N = some u := by
    simp [Cfg.workTapeSymbols, cfg, tapeOfList_zero]
  simp only [tm, MultiTapeTM.tr_ofTr, tr, hread, act]
  refine Cfg.ext rfl (by simp [cfg, moveInputPos_zero]) ?_ ?_ (by simp [cfg]) <;>
    funext i <;> by_cases hi : i = N <;> simp [cfg, hi]

variable (P R N) in
private theorem next_disp1_halt (b u : Bool) {w : List Bool} (hw : w[1]? = none) :
    (wordGame P R N).next b (cfg (input := input) N (some (.disp1 u)) w 1 []) =
      cfg N none w 1 (if u then [true] else []) := by
  rw [wordGame, next_ofTMs, MultiTapeTM.step_of_state rfl]
  have hread : (cfg (input := input) N (some (State.disp1 (S₁ := S₁) (S₂ := S₂) u)) w 1
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
private theorem next_disp1_move (b u x : Bool) {w : List Bool} (hw : w[1]? = some x) :
    (wordGame P R N).next b (cfg (input := input) N (some (.disp1 u)) w 1 []) =
      cfg N (some (.move u)) w 1 [] := by
  rw [wordGame, next_ofTMs, MultiTapeTM.step_of_state rfl]
  have hread : (cfg (input := input) N (some (State.disp1 (S₁ := S₁) (S₂ := S₂) u)) w 1
      []).workTapeSymbols N = some x := by
    have h1 : tapeOfList w 1 = w[1]? := by simpa using tapeOfList_ofNat w 1
    simp [Cfg.workTapeSymbols, cfg, h1, hw]
  simp only [tm, MultiTapeTM.tr_ofTr, tr, hread, act]
  refine Cfg.ext rfl (by simp [cfg, moveInputPos_zero]) ?_ ?_ (by simp [cfg]) <;>
    funext i <;> by_cases hi : i = N <;> simp [cfg, hi]

variable (P R N) in
private theorem next_move (b u : Bool) {w : List Bool} (hw : 1 < w.length) :
    (wordGame P R N).next b (cfg (input := input) N (some (.move u)) w 1 []) =
      cfg N (some (.round R.q₀)) (w.set 1 b) 0 [] := by
  rw [wordGame, next_ofTMs, MultiTapeTM.step_of_state rfl]
  simp only [tm, MultiTapeTM.tr_ofTr, tr, act]
  refine Cfg.ext rfl (by simp [cfg, moveInputPos_zero]) ?_ ?_ (by simp [cfg]) <;>
    funext i <;> by_cases hi : i = N <;> simp [cfg, hi, tapeOfList_set w hw]

/-! ### Phases -/

private theorem iterate_next_liftCfg {S : Type} {M : MultiTapeTM k Bool S}
    (f : S → State S₁ S₂)
    (hstep : ∀ b (c : Cfg k Bool S input), c.state ≠ none →
      (wordGame P R N).next b (liftCfg f c) = liftCfg f (M.step c))
    (c : Cfg k Bool S input) : ∀ j, (∀ i < j, (M.runFrom c i).state ≠ none) →
      ((wordGame P R N).next false)^[j] (liftCfg f c) = liftCfg f (M.runFrom c j)
  | 0, _ => rfl
  | j + 1, h => by
    rw [Function.iterate_succ_apply',
      iterate_next_liftCfg f hstep c j (fun i hi => h i (by omega)),
      hstep false _ (h j (by omega))]
    simp only [MultiTapeTM.runFrom, Function.iterate_succ_apply']

private theorem exists_phase {S : Type} {M : MultiTapeTM k Bool S} (f : S → State S₁ S₂)
    (hstep : ∀ b (c : Cfg k Bool S input), c.state ≠ none →
      (wordGame P R N).next b (liftCfg f c) = liftCfg f (M.step c))
    {c : Cfg k Bool S input} {t : ℕ} (ht : (M.runFrom c t).state = none) :
    ∃ τ ≤ t, (∀ j < τ, ∀ b, (wordGame P R N).next b
        (((wordGame P R N).next false)^[j] (liftCfg f c)) =
        ((wordGame P R N).next false)^[j + 1] (liftCfg f c)) ∧
      (∀ j ≤ τ, (((wordGame P R N).next false)^[j] (liftCfg f c)).state ≠ none) ∧
      ((wordGame P R N).next false)^[τ] (liftCfg f c) = liftCfg f (M.runFrom c t) := by
  classical
  have hex : ∃ τ, (M.runFrom c τ).state = none := ⟨t, ht⟩
  refine ⟨Nat.find hex, Nat.find_min' hex ht, fun j hj b => ?_, fun j hj => ?_, ?_⟩
  · have hrun : ∀ i < j, (M.runFrom c i).state ≠ none := fun i hi => Nat.find_min hex (by omega)
    rw [Function.iterate_succ_apply', iterate_next_liftCfg f hstep c j hrun,
      hstep b _ (Nat.find_min hex hj), hstep false _ (Nat.find_min hex hj)]
  · rw [iterate_next_liftCfg f hstep c j fun i hi => Nat.find_min hex (by omega)]
    simp [liftCfg]
  · rw [iterate_next_liftCfg f hstep c _ fun i hi => Nat.find_min hex hi,
      MultiTapeTM.runFrom_eq_of_halt M c (Nat.find_min' hex ht) (Nat.find_spec hex)]

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

variable {U : List Bool → List Bool} {w₀ : List Bool} {tR sR : ℕ}

private theorem liftCfg_round_wordsCfg (q : Option S₂) (ws : Fin k → List Bool) :
    liftCfg (S₁ := S₁) .round (wordsCfg input q ws []) =
      wordsCfg input (some (q.elim .disp0 .round)) ws [] := rfl

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
  have hstep : ∀ b (c : Cfg k Bool S₂ input), c.state ≠ none →
      (wordGame P R N).next b (liftCfg .round c) = liftCfg .round (R.step c) :=
    fun b c h => next_liftCfg_round b h
  obtain ⟨τ, hτ, h1, h2, h3⟩ := exists_phase .round hstep (hrun ▸ rfl : (R.runFrom
    (wordsCfg input (some R.q₀) (Function.update (fun _ => []) N v) []) tR).state = none)
  have hc : liftCfg (S₁ := S₁) .round
      (wordsCfg input (some R.q₀) (Function.update (fun _ => []) N v) []) =
      cfg N (some (.round R.q₀)) v 0 [] := by
    rw [liftCfg_round_wordsCfg, cfg_zero]
    rfl
  rw [hc, hrun] at h3
  rw [hc] at h1 h2
  exact ⟨τ, hτ, h1, h2, h3.trans (by rw [liftCfg_round_wordsCfg, cfg_zero]; rfl)⟩

/-- The dispatch configuration on the position `w`. -/
private abbrev dcfg (N : Fin k) (w : List Bool) : Cfg k Bool (State S₁ S₂) input :=
  cfg N (some .disp0) w 0 []

private theorem acceptsWithin_of_wins (hR : RoundSpec R N input U w₀ tR sR) {w : List Bool}
    (hw : Wins U w) (hreach : Reach U w₀ w) :
    ∃ n, (wordGame P R N).AcceptsWithin n (dcfg (input := input) N w) := by
  induction hw with
  | accept =>
    refine ⟨2, ?_⟩
    rw [acceptsWithin_succ_of_next_eq (next_disp0_cons P R N · true []),
      acceptsWithin_succ_of_next_eq (next_disp1_halt P R N · true rfl),
      acceptsWithin_of_halted _ rfl]
    rfl
  | @existsMove x r b hwin ih =>
    obtain ⟨n, hn⟩ := ih (Reach.move b hreach)
    obtain ⟨τ, -, hnext, hrun, hd⟩ := exists_round (P := P) (hR false x r hreach b).1
    refine ⟨n + τ + 3, ?_⟩
    rw [acceptsWithin_succ_of_next_eq (next_disp0_cons P R N · false (x :: r)),
      acceptsWithin_succ_of_next_eq (next_disp1_move P R N · false x rfl),
      acceptsWithin_succ_of_existential _ rfl rfl]
    refine ⟨b, ?_⟩
    rw [next_move P R N b false (by simp), List.set_cons_succ, List.set_cons_zero,
      acceptsWithin_iff_of_phase hnext hrun hd]
    simpa using hn
  | @forallMove x r hwin ih =>
    have h (b : Bool) := ih b (Reach.move b hreach)
    choose n hn using h
    have hr (b : Bool) := exists_round (P := P) (hR true x r hreach b).1
    choose τ hτ hnext hrun hd using hr
    refine ⟨max (n false + τ false) (n true + τ true) + 3, ?_⟩
    rw [acceptsWithin_succ_of_next_eq (next_disp0_cons P R N · true (x :: r)),
      acceptsWithin_succ_of_next_eq (next_disp1_move P R N · true x rfl),
      acceptsWithin_succ_of_universal _ rfl rfl]
    intro b
    rw [next_move P R N b true (by simp), List.set_cons_succ, List.set_cons_zero,
      acceptsWithin_iff_of_phase (hnext b) (hrun b) (hd b)]
    have hle : n b + τ b ≤ max (n false + τ false) (n true + τ true) := by
      cases b
      · exact le_max_left _ _
      · exact le_max_right _ _
    exact ⟨by omega, (hn b).mono (by omega)⟩

private theorem wins_of_acceptsWithin (hR : RoundSpec R N input U w₀ tR sR) (n : ℕ) :
    ∀ w, Reach U w₀ w → (wordGame P R N).AcceptsWithin n (dcfg (input := input) N w) →
      Wins U w := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w hreach hacc
  rcases w with _ | ⟨u, _ | ⟨x, r⟩⟩
  · rcases n with _ | m
    · exact absurd hacc (not_acceptsWithin_zero _ rfl)
    · rw [acceptsWithin_succ_of_next_eq (next_disp0_nil P R N), acceptsWithin_of_halted _ rfl]
        at hacc
      simp [cfg] at hacc
  · rcases n with _ | _ | m
    · exact absurd hacc (not_acceptsWithin_zero _ rfl)
    · rw [acceptsWithin_succ_of_next_eq (next_disp0_cons P R N · u [])] at hacc
      exact absurd hacc (not_acceptsWithin_zero _ rfl)
    · rw [acceptsWithin_succ_of_next_eq (next_disp0_cons P R N · u []),
        acceptsWithin_succ_of_next_eq (next_disp1_halt P R N · u rfl),
        acceptsWithin_of_halted _ rfl] at hacc
      cases u
      · simp [cfg] at hacc
      · exact Wins.accept
  · rcases n with _ | _ | _ | m
    · exact absurd hacc (not_acceptsWithin_zero _ rfl)
    · rw [acceptsWithin_succ_of_next_eq (next_disp0_cons P R N · u (x :: r))] at hacc
      exact absurd hacc (not_acceptsWithin_zero _ rfl)
    · rw [acceptsWithin_succ_of_next_eq (next_disp0_cons P R N · u (x :: r)),
        acceptsWithin_succ_of_next_eq (next_disp1_move P R N · u x rfl)] at hacc
      exact absurd hacc (not_acceptsWithin_zero _ rfl)
    · rw [acceptsWithin_succ_of_next_eq (next_disp0_cons P R N · u (x :: r)),
        acceptsWithin_succ_of_next_eq (next_disp1_move P R N · u x rfl)] at hacc
      cases u
      · rw [acceptsWithin_succ_of_existential _ rfl rfl] at hacc
        obtain ⟨b, hb⟩ := hacc
        obtain ⟨τ, -, hnext, hrun, hd⟩ := exists_round (P := P) (hR false x r hreach b).1
        rw [next_move P R N b false (by simp), List.set_cons_succ, List.set_cons_zero,
          acceptsWithin_iff_of_phase hnext hrun hd] at hb
        exact Wins.existsMove b (ih (m - τ) (by omega) _ (Reach.move b hreach) hb.2)
      · rw [acceptsWithin_succ_of_universal _ rfl rfl] at hacc
        refine Wins.forallMove fun b => ?_
        have hb := hacc b
        obtain ⟨τ, -, hnext, hrun, hd⟩ := exists_round (P := P) (hR true x r hreach b).1
        rw [next_move P R N b true (by simp), List.set_cons_succ, List.set_cons_zero,
          acceptsWithin_iff_of_phase hnext hrun hd] at hb
        exact ih (m - τ) (by omega) _ (Reach.move b hreach) hb.2

private theorem haltsWithin_of_ends (hR : RoundSpec R N input U w₀ tR sR) (n : ℕ) :
    ∀ w, Reach U w₀ w → Ends U n w →
      (wordGame P R N).HaltsWithin (n * (tR + 3) + 2) (dcfg (input := input) N w) := by
  induction n with
  | zero =>
    intro w hreach hend
    rcases w with _ | ⟨u, _ | ⟨x, r⟩⟩
    · exact haltsWithin_succ.mpr fun b => by
        rw [next_disp0_nil P R N]
        exact haltsWithin_of_halted rfl
    · exact haltsWithin_succ.mpr fun b => by
        rw [next_disp0_cons P R N b u []]
        exact haltsWithin_succ.mpr fun b' => by
          rw [next_disp1_halt P R N b' u rfl]
          exact haltsWithin_of_halted rfl
    · exact absurd hend (by simp [Ends])
  | succ m ih =>
    intro w hreach hend
    rcases w with _ | ⟨u, _ | ⟨x, r⟩⟩
    · exact haltsWithin_succ.mpr fun b => by
        rw [next_disp0_nil P R N]
        exact haltsWithin_of_halted rfl
    · exact haltsWithin_succ.mpr fun b => by
        rw [next_disp0_cons P R N b u []]
        exact haltsWithin_succ.mpr fun b' => by
          rw [next_disp1_halt P R N b' u rfl]
          exact haltsWithin_of_halted rfl
    · rw [show (m + 1) * (tR + 3) + 2 = m * (tR + 3) + 2 + tR + 1 + 1 + 1 by ring]
      refine haltsWithin_succ.mpr fun b₀ => ?_
      rw [next_disp0_cons P R N b₀ u (x :: r)]
      refine haltsWithin_succ.mpr fun b₁ => ?_
      rw [next_disp1_move P R N b₁ u x rfl]
      refine haltsWithin_succ.mpr fun b => ?_
      obtain ⟨τ, hτ, hnext, hrun, hd⟩ := exists_round (P := P) (hR u x r hreach b).1
      rw [next_move P R N b u (by simp), List.set_cons_succ, List.set_cons_zero,
        haltsWithin_iff_of_phase hnext hrun hd]
      exact ⟨by omega, (ih _ (Reach.move b hreach) (hend b)).mono (by omega)⟩

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

private theorem exists_prep (hP : PrepSpec P N input w₀ tP sP) :
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
  obtain ⟨τ, hτ, h1, h2, h3⟩ := exists_phase .prep hstep (hP.1 ▸ rfl : (P.runFrom
    (Cfg.init P.q₀ input) tP).state = none)
  rw [hP.1] at h3
  exact ⟨τ, hτ, h1, h2, h3.trans (cfg_zero _ _ _).symm⟩

end WordGame

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
  obtain ⟨τ, hτ, hnext, hrun, hd⟩ := exists_prep (R := R) hP
  refine ⟨fun p => ?_, ⟨fun ⟨n, hn⟩ => ?_, fun hw => ?_⟩, fun n hn => ?_⟩
  · refine MultiTapeNTM.RunPath.InWindow.space_le fun c hc i => ?_
    exact (good_of_mem hP hR p c hc).workTapePos_mem hP hR
      ((le_max_left _ _).trans (le_max_left _ _)) ((le_max_right _ _).trans (le_max_left _ _))
      (le_max_right _ _) i
  · rw [acceptsWithin_iff_of_phase hnext hrun hd] at hn
    exact wins_of_acceptsWithin hR _ w₀ .start hn.2
  · obtain ⟨n, hn⟩ := acceptsWithin_of_wins (P := P) hR hw .start
    exact ⟨n + τ, (acceptsWithin_iff_of_phase hnext hrun hd _).mpr (by simpa using hn)⟩
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
