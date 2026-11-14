/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.WordGame
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm
import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.StreamFold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.KernelOnWords

/-!
# Compiling locally computed word games to alternating time

A tidy preparation and a tidy update give one finite multitape alternating machine. The update
may be specified only on typed reachable positions. Its time is charged at each actual position,
including copying the current word, writing the successor and clearing temporary tapes.

The exact round charge is `t + 3 * input.length + 7 * output.length + 26`: the update's own
clock, tape plumbing, and the three alternating dispatch steps. A natural-valued potential
paying this charge bounds the total time along every branch. The potential is a proof device;
the machine does not compute it. There is no random-access or free-decoder assumption.

This is a compiler for a local bit-evaluation game, not a contraction construction. In particular,
a polynomial-time certificate for generating an entire arithmetic circuit cannot be substituted
for a small local-decoding cost.

## Main results

* `Turing.MultiTapeATM.exists_wordGame_of_tidy`: one native machine accepts the winning positions
  and obeys the potential bound, with explicit preparation and round costs.
-/

public section

namespace Turing.MultiTapeATM

open MultiTapeTM WordGame

/-- Compile a typed update into one finite native alternating machine. All time spent on the
encoded positions is charged. `hpos` also requires the update for both possible move bits,
including the move not chosen by an existential winning strategy. -/
theorem exists_wordGame_of_tidy {α π : Type} {enc : α ↪ List Bool}
    {encPos : π ↪ List Bool} {I : α → List Bool} {U : List Bool → List Bool}
    {F : π → List Bool} {tI sI : α → ℕ} {tF sF : π → ℕ}
    (hI : ComputableTidilyInTimeAndSpace I enc encBits tI sI)
    (hF : ComputableTidilyInTimeAndSpace F encPos encBits tF sF)
    (potential : α → List Bool → ℕ)
    (hpos : ∀ a u x r b, Reach U (I a) (u :: x :: r) →
      ∃ p, encPos p = u :: b :: r ∧ F p = U (u :: b :: r) ∧
        tF p + 3 * (encPos p).length + 7 * (F p).length + 26 +
          potential a (F p) ≤ potential a (u :: x :: r)) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (atm : MultiTapeATM k Bool State),
      ∀ a, (atm.Accepts (enc a) ↔ Wins U (I a)) ∧
        atm.toPTM.toNTM.RunsInTime (enc a) (tI a + (I a).length + potential a (I a) + 4) := by
  classical
  obtain ⟨kI, SI, _, TI, hTI⟩ := hI
  obtain ⟨kF, SF, _, TF, hTF⟩ := hF
  let K := kI + kF + 3
  let N : Fin K := ⟨0, by omega⟩
  let O : Fin K := ⟨1, by omega⟩
  let M : Fin K := ⟨2, by omega⟩
  have hNO : N ≠ O := by simp [N, O]
  have hNM : N ≠ M := by simp [N, M]
  have hOM : O ≠ M := by simp [O, M]
  obtain ⟨eI, heI⟩ := exists_embedding_eq (show kI + 1 ≤ K by omega) (Fin.last kI) N
  obtain ⟨eF, heFi, heFo⟩ := exists_embedding_eq₂ (show kF + 1 + 2 ≤ K by omega)
    (i := Fin.natAdd (kF + 1) 0) (o := (Fin.last kF).castAdd 2) (by simp [Fin.ext_iff]) hNO
  let P := TI.outputToWord.extendTapes eI
  let R := frozenRound (nop K Bool) ((TF.onWords true).extendTapes eF) N O M hNO hNM hOM
  have hprep (a : α) : P.runFrom (Cfg.init P.q₀ (enc a)) (tI a + (I a).length + 2) =
      wordsCfg (enc a) none (Function.update (fun _ => []) N (I a)) [] := by
    have h := (hTI a).outputToWord_onTape heI
    simp only [encBits_apply] at h
    obtain ⟨ws, em, hrun, ⟨rfl, rfl⟩, _⟩ := transformsTapes_iff_runFrom.mp h
      (enc a) (fun _ => []) [] ⟨rfl, rfl⟩
    rw [Cfg.init_eq_wordsCfg]
    exact hrun
  have hround (p : π) (input : List Bool) :
      R.runFrom (wordsCfg input (some R.q₀) (Function.update (fun _ => []) N (encPos p)) [])
          (tF p + 3 * (encPos p).length + 7 * (F p).length + 23) =
        wordsCfg input none (Function.update (fun _ => []) N (F p)) [] := by
    have hE := (transformsTapes_nop K Bool).imp
      (P' := fun _ ws => ws = Function.update (fun _ => []) N (encPos p))
      (Q' := fun _ ws ws' em => ws' = ws ∧ em = []) (fun _ _ _ => trivial)
      (fun _ _ _ _ _ h => h) le_rfl le_rfl
    have hN := (hTF p).onWords_extendTapes true heFi heFo
    simp only [encBits_apply] at hN
    have h := transformsTapes_frozenRound hNO hNM hOM hE hN
    obtain ⟨ws, em, hrun, ⟨rfl, rfl⟩, _⟩ := transformsTapes_iff_runFrom.mp h input _ [] rfl
    have ht : 1 + (tF p + (F p).length + 6 +
        (3 * ((encPos p).length + 1) +
          ((3 * (F p).length + 10) + 3 * ((F p).length + 1)))) =
        tF p + 3 * (encPos p).length + 7 * (F p).length + 23 := by omega
    rw [ht] at hrun
    exact hrun
  refine ⟨K, _, inferInstance, wordGame P R N, fun a => ⟨?_, ?_⟩⟩
  · apply accepts_wordGame_iff_of_computes (hprep a)
    intro u x r hr b
    obtain ⟨p, hp, hF, _⟩ := hpos a u x r b hr
    refine ⟨tF p + 3 * (encPos p).length + 7 * (F p).length + 23, ?_⟩
    rw [← hF, ← hp]
    exact hround p (enc a)
  · have h := runsInTime_wordGame_of_potential (R := R) (potential a) (hprep a) (by
      intro u x r hr b
      obtain ⟨p, hp, hF, hcost⟩ := hpos a u x r b hr
      refine ⟨tF p + 3 * (encPos p).length + 7 * (F p).length + 23, ?_, ?_⟩
      · rw [← hF, ← hp]
        exact hround p (enc a)
      · rw [← hF]
        omega)
    convert h using 1; omega

end Turing.MultiTapeATM
