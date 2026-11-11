/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.TwoProverGame
import Complexity.Probability.PMF.Event

/-!
# The CHSH game

The *CHSH game* [Clauser, Horne, Shimony, Holt][ClauserHorneShimonyHolt1969] in the form of
[Cleve, Høyer, Toner, Watrous, §3.1][CleveHoyerTonerWatrous2004]: the referee sends uniformly
random bits `x` to Alice and `y` to Bob, and accepts their answer bits `a` and `b` when
`a ⊕ b = x ∧ y` (`Cslib.PCP.TwoProverGame.chsh`). Every deterministic strategy loses on at least
one of the four questions (`Cslib.PCP.TwoProverGame.winProb_chsh_le`), and answering `0` always
wins on three of them, so the classical value is `3/4` (`Cslib.PCP.TwoProverGame.value_chsh`). By
`Cslib.PCP.TwoProverGame.winProb_shared_le_value` this also bounds strategies with shared
randomness. Its entangled value `cos²(π/8)` is in
`Complexity/Computability/PCP/TwoProverGame/Tsirelson.lean`.

## Main definitions

* `Cslib.PCP.TwoProverGame.chsh`: the CHSH game.

## Main results

* `Cslib.PCP.TwoProverGame.winProb_chsh_le`: every deterministic strategy wins with probability at
  most `3/4`.
* `Cslib.PCP.TwoProverGame.value_chsh`: the classical value of CHSH is `3/4`.

## References

* [J. F. Clauser, M. A. Horne, A. Shimony, R. A. Holt, *Proposed experiment to test local
  hidden-variable theories*][ClauserHorneShimonyHolt1969]
* [R. Cleve, P. Høyer, B. Toner, J. Watrous, *Consequences and limits of nonlocal
  strategies*][CleveHoyerTonerWatrous2004]
-/

@[expose] public section

namespace Cslib.PCP.TwoProverGame

/-- The **CHSH game** [Cleve, Høyer, Toner, Watrous, §3.1][CleveHoyerTonerWatrous2004]: uniform
questions `x, y`, accepted when `a xor b = x && y`. -/
noncomputable def chsh : TwoProverGame Bool Bool Bool Bool where
  questions := Cslib.Probability.PMF.uniformOfFintype (Bool × Bool)
  accepts x y a b := (a ^^ b) = (x && y)

instance (x y a b : Bool) : Decidable (chsh.accepts x y a b) :=
  inferInstanceAs (Decidable ((a ^^ b) = (x && y)))

theorem chsh_questions_apply (x y : Bool) : (chsh.questions (x, y)).toReal = 1 / 4 := by
  simp [chsh, Cslib.Probability.PMF.uniformOfFintype_apply]

/-- Answering `0` to every question wins CHSH with probability `3/4`. -/
theorem winProb_chsh_const : chsh.winProb (fun _ => false) (fun _ => false) = 3 / 4 := by
  rw [TwoProverGame.winProb, Cslib.Probability.PMF.toOuterMeasure_apply_toReal]
  simp [chsh, Cslib.Probability.PMF.uniformOfFintype_apply, Fintype.sum_prod_type]
  norm_num

/-- Every deterministic strategy for CHSH loses on at least one of the four questions. -/
theorem winProb_chsh_le (ha hb : Bool → Bool) : chsh.winProb ha hb ≤ 3 / 4 := by
  rw [TwoProverGame.winProb, Cslib.Probability.PMF.toOuterMeasure_apply_toReal]
  simp only [chsh, Cslib.Probability.PMF.uniformOfFintype_apply, Fintype.sum_prod_type,
    Fintype.sum_bool, Set.mem_ofPred_eq, Fintype.card_prod, Fintype.card_bool]
  rcases Bool.eq_false_or_eq_true (ha true) with h1 | h1 <;>
  rcases Bool.eq_false_or_eq_true (ha false) with h2 | h2 <;>
  rcases Bool.eq_false_or_eq_true (hb true) with h3 | h3 <;>
  rcases Bool.eq_false_or_eq_true (hb false) with h4 | h4 <;>
  simp [h1, h2, h3, h4] <;> norm_num

/-- The classical value of CHSH is `3/4`
[Cleve, Høyer, Toner, Watrous, §3.1][CleveHoyerTonerWatrous2004]. -/
theorem value_chsh : chsh.value = 3 / 4 :=
  le_antisymm (ciSup_le fun ha => ciSup_le fun hb => winProb_chsh_le ha hb)
    (winProb_chsh_const ▸ chsh.winProb_le_value _ _)

end Cslib.PCP.TwoProverGame
