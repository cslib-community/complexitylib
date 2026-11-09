/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.StreamFold
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.RepeatUntilBlank

/-!
# Multi-pass streaming folds

A multi-pass fold reads its input several times, from left to right, keeping a state on a work tape
between the passes. A pass is a streaming loop over the tokens of the input, followed by an end
round that computes the state for the next pass, and a flag on a separate tape that says whether
another pass follows. Like a streaming fold, it never copies the input.

## Main definitions

* `Turing.MultiTapeTM.passTM`: one pass.
* `Turing.MultiTapeTM.multiPassTM`: the passes, between the initial state and the final emission.

## Main results

* `Turing.MultiTapeTM.transformsTapes_passTM`: the specification of a pass.
* `Turing.MultiTapeTM.computesTidily_multiPassTM`: the passes compute tidily.
-/

namespace Turing.MultiTapeTM

variable {K : ℕ} {Q SI SE SN SEe SNe SC SF SP : Type*} {r : InputReader Bool Q}
  {I : MultiTapeTM K Bool SI} {E : MultiTapeTM K Bool SE} {Nm : MultiTapeTM K Bool SN}
  {Ee : MultiTapeTM K Bool SEe} {Ne : MultiTapeTM K Bool SNe} {Cm : MultiTapeTM K Bool SC}
  {Fm : MultiTapeTM K Bool SF} {V N F C : Fin K}

/-- One pass: clear the flag tape `C`, run the streaming loop with the rounds `E`, `Nm`, run the
end round `Ee`, `Ne` with the input head frozen, write the flag with `Cm` and rewind the input. -/
public noncomputable def passTM (r : InputReader Bool Q) (E : MultiTapeTM K Bool SE)
    (Nm : MultiTapeTM K Bool SN) (Ee : MultiTapeTM K Bool SEe) (Ne : MultiTapeTM K Bool SNe)
    (Cm : MultiTapeTM K Bool SC) (V N F C : Fin K) (hVN : V ≠ N) (hVF : V ≠ F) (hNF : N ≠ F) :=
  ((clearWork Bool).extendTapes (tapeEmb C)).seq
    ((whileInput (streamRound r E Nm V N F hVN hVF hNF)).seq
      ((frozenRound Ee Ne V N F hVN hVF hNF).freezeInput.seq
        (Cm.freezeInput.seq (rewindInputOn K Bool))))

/-- The multi-pass fold: write the initial state to tape `V` with `I`, run passes until the flag
tape `C` is blank, emit from the final state with `Fm` and clear tape `V`. -/
public noncomputable def multiPassTM (I : MultiTapeTM K Bool SI) (pass : MultiTapeTM K Bool SP)
    (Fm : MultiTapeTM K Bool SF) (V C : Fin K) :=
  I.seq ((repeatUntilBlank C pass).seq (Fm.seq ((clearWork Bool).extendTapes (tapeEmb V))))

/-- The tapes between two passes: the state `v` on tape `V` and the flag `c` on tape `C`. -/
@[expose] public def passTapes (V C : Fin K) (v c : List Bool) : Fin K → List Bool :=
  Function.update (Function.update (fun _ => []) V v) C c

lemma passTapes_nil (hVC : V ≠ C) (v : List Bool) :
    passTapes V C v [] = Function.update (fun _ => []) V v := by
  funext l
  by_cases hl : l = C
  · subst hl; simp [passTapes, hVC.symm]
  · simp [passTapes, hl]

-- upstream: candidate
/-- Clear the continuation flag, run a streaming phase, then compute the end-of-pass state
and flag and rewind the input. The phase owns the token and round specifications. -/
public theorem transformsTapes_passTM (hVN : V ≠ N) (hVF : V ≠ F) (hNF : N ≠ F) (hVC : V ≠ C)
    (x v₀ v₁ em ee v' c c' : List Bool) {tLoop sLoop tEe sEe tNe sNe tC sC : ℕ}
    (hloop : TransformsTapesAt (whileInput (streamRound r E Nm V N F hVN hVF hNF))
      (fun input p ws => input = x ∧ p.val = 1 ∧ ws = Function.update (fun _ => []) V v₀)
      (fun input _ _ p' ws' e => input = x ∧ p'.val = 1 + x.length ∧
        ws' = Function.update (fun _ => []) V v₁ ∧ e = em) tLoop sLoop)
    (hEe : TransformsTapes Ee (fun _ ws => ws = Function.update (fun _ => []) V v₁)
      (fun _ ws ws' e => ws' = ws ∧ e = ee) tEe sEe)
    (hNe : TransformsTapes Ne (fun _ ws => ws = Function.update (fun _ => []) V v₁)
      (fun _ ws ws' e => ws' = Function.update ws N v' ∧ e = []) tNe sNe)
    (hC : TransformsTapes Cm (fun _ ws => ws = Function.update (fun _ => []) V v')
      (fun _ ws ws' e => ws' = Function.update ws C c' ∧ e = []) tC sC) :
    TransformsTapes (passTM r E Nm Ee Ne Cm V N F C hVN hVF hNF)
      (fun inp ws => inp = x ∧ ws = passTapes V C v₀ c)
      (fun _ _ ws' e => ws' = passTapes V C v' c' ∧ e = em ++ ee)
      (3 * (c.length + 1) + (tLoop +
        ((tEe + (tNe + (3 * (v₁.length + 1) + ((3 * v'.length + 10) +
          3 * (v'.length + 1))))) + (tC + (x.length + 2)))))
      (c.length + 1 + K + (sLoop +
        ((sEe + (sNe + ((v₁.length + 1 + K) + ((4 * v'.length + K + 15) +
          (v'.length + 1 + K))))) + (sC + K)))) := by
  have hclear := ((transformsTapes_clearWork_tapeEmb C c).imp
    (P' := fun inp ws => inp = x ∧ ws = passTapes V C v₀ c)
    (Q' := fun _ _ ws' e => ws' = Function.update (fun _ => []) V v₀ ∧ e = [])
    (fun _ _ ⟨_, h⟩ => by simp [h, passTapes])
    (fun _ _ _ _ ⟨_, h⟩ ⟨h', he⟩ => ⟨by rw [h', h, passTapes, Function.update_idem,
      ← passTapes, passTapes_nil hVC], he⟩) le_rfl le_rfl).transformsTapesAt_eq
  have hend := (transformsTapes_frozenRound hVN hVF hNF hEe hNe).freezeInput_eq x (1 + x.length)
  have hflag := (hC.imp (Q' := fun _ _ ws' e => ws' = passTapes V C v' c' ∧ e = [])
    (fun _ _ h => h)
    (fun _ _ _ _ hws ⟨h, he⟩ => ⟨by rw [h, hws]; rfl, he⟩) le_rfl le_rfl).freezeInput_eq x
      (1 + x.length)
  have hrw := (transformsTapesAt_rewindInput (k := K) x).imp
    (P' := fun input p ws => input = x ∧ p.val = 1 + x.length ∧ ws = passTapes V C v' c')
    (Q' := fun input _ _ p' ws' e => input = x ∧ p'.val = 1 ∧ ws' = passTapes V C v' c' ∧ e = [])
    (fun _ _ _ h => h.1)
    (by rintro _ _ _ _ _ _ ⟨hin, _, rfl⟩ ⟨rfl, hws, he⟩
        exact ⟨hin, rfl, hws, he⟩) le_rfl le_rfl
  have hall := hclear.seq_eq (hloop.seq_eq (hend.seq_eq (hflag.seq_eq hrw)))
  refine (hall.transformsTapes (fun _ _ _ _ _ _ h => Fin.ext h.2.1)).imp
    (fun _ _ ⟨hin, hws⟩ => ⟨hin, rfl, hws⟩)
    (fun _ _ _ _ _ ⟨_, _, hws, he⟩ => ⟨hws, by simpa using he⟩) le_rfl le_rfl

-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)
/-- **The multi-pass fold.** If `I` writes the initial state `vs 0` to tape `V`, each pass `i`
takes the state `vs i` and the flag `cs i` to the state `vs (i + 1)` and the flag `cs (i + 1)`,
emitting `es i`, where the flag is blank at the start and exactly after the last pass `passes`, and
`Fm` emits `ef` from the final state, then `multiPassTM` emits the words `es i` followed by `ef`,
tidily. -/
public theorem computesTidily_multiPassTM {pass : MultiTapeTM K Bool SP} (hVC : V ≠ C)
    (x : List Bool) (passes : ℕ) (vs cs es : ℕ → List Bool) (ef : List Bool)
    {tI sI tP sP tF sF : ℕ}
    (hI : TransformsTapes I (fun inp ws => inp = x ∧ ws = fun _ => [])
      (fun _ _ ws' em => ws' = Function.update (fun _ => []) V (vs 0) ∧ em = []) tI sI)
    (hpass : ∀ i ≤ passes, TransformsTapes pass
      (fun inp ws => inp = x ∧ ws = passTapes V C (vs i) (cs i))
      (fun _ _ ws' em => ws' = passTapes V C (vs (i + 1)) (cs (i + 1)) ∧ em = es i) tP sP)
    (hfirst : cs 0 = []) (hcs : ∀ i < passes, cs (i + 1) ≠ []) (hlast : cs (passes + 1) = [])
    (hF : TransformsTapes Fm
      (fun _ ws => ws = Function.update (fun _ => []) V (vs (passes + 1)))
      (fun _ ws ws' em => ws' = ws ∧ em = ef) tF sF) :
    (multiPassTM I pass Fm V C).ComputesTidilyInTimeAndSpace x
      (((List.range (passes + 1)).map es).flatten ++ ef)
      (tI + ((passes + 1) * (tP + 1) + (tF + 3 * ((vs (passes + 1)).length + 1))))
      (sI + ((2 * K * sP + K) + (sF + ((vs (passes + 1)).length + 1 + K)))) := by
  let P (n : ℕ) (inp : List Bool) (ws : Fin K → List Bool) (em : List Bool) : Prop :=
    inp = x ∧ ws = passTapes V C (vs n) (cs n) ∧ em = ((List.range n).map es).flatten
  have hround : ∀ n < passes, ∀ acc, TransformsTapes pass (fun inp ws => P n inp ws acc)
      (fun inp _ ws' e => P (n + 1) inp ws' (acc ++ e) ∧ ws' C ≠ []) tP sP := by
    -- vendored: `TransformsTapes` is stated with run paths since cslib #1117
    refine fun n hn acc => transformsTapes_iff_runFrom.mpr ?_
    rintro inp ws out ⟨hin, hws, rfl⟩
    obtain ⟨ws', e, hrun, ⟨h, rfl⟩, hsp⟩ :=
      transformsTapes_iff_runFrom.mp (hpass n hn.le) inp ws out ⟨hin, hws⟩
    refine ⟨ws', _, hrun, ⟨⟨hin, h, by simp [List.range_succ]⟩, ?_⟩, hsp⟩
    simpa [h, passTapes] using hcs n hn
  let R (inp : List Bool) (ws : Fin K → List Bool) (em : List Bool) : Prop :=
    inp = x ∧ ws = Function.update (fun _ => []) V (vs (passes + 1)) ∧
      em = ((List.range (passes + 1)).map es).flatten
  have hstop : ∀ acc, TransformsTapes pass (fun inp ws => P passes inp ws acc)
      (fun inp _ ws' e => R inp ws' (acc ++ e) ∧ ws' C = []) tP sP := by
    -- vendored: `TransformsTapes` is stated with run paths since cslib #1117
    refine fun acc => transformsTapes_iff_runFrom.mpr ?_
    rintro inp ws out ⟨hin, hws, rfl⟩
    obtain ⟨ws', e, hrun, ⟨h, rfl⟩, hsp⟩ :=
      transformsTapes_iff_runFrom.mp (hpass passes le_rfl) inp ws out ⟨hin, hws⟩
    refine ⟨ws', _, hrun, ⟨⟨hin, by rw [h, hlast, passTapes_nil hVC], by simp [List.range_succ]⟩,
      ?_⟩, hsp⟩
    simp [h, passTapes, hlast]
  have hloop := transformsTapes_repeatUntilBlank C hround hstop
  have hclear : TransformsTapes ((clearWork Bool).extendTapes (tapeEmb V))
      (fun _ ws => ws = Function.update (fun _ => []) V (vs (passes + 1)))
      (fun _ _ ws' em => ws' = (fun _ => []) ∧ em = [])
      (3 * ((vs (passes + 1)).length + 1)) ((vs (passes + 1)).length + 1 + K) :=
    (transformsTapes_clearWork_tapeEmb V (vs (passes + 1))).imp (fun _ _ h => by simp [h])
      (fun _ _ _ _ hws ⟨h, he⟩ => ⟨by rw [h, hws]; simp, he⟩) le_rfl le_rfl
  have hfin := (hF.imp (fun _ _ h => h) (fun _ _ _ _ hws ⟨h, he⟩ => ⟨h.trans hws, he⟩) le_rfl
    le_rfl).seq_eq hclear
  have hmain := transformsTapes_seq hloop hfin fun _ _ _ _ _ h => h.2.1
  refine (transformsTapes_seq hI hmain fun _ _ _ _ ⟨hin, _⟩ ⟨h, _⟩ =>
    ⟨hin, by rw [h, hfirst, passTapes_nil hVC], rfl⟩).imp (fun _ _ h => h) ?_ le_rfl le_rfl
  rintro _ _ _ _ _ ⟨_, _, _, ⟨-, rfl⟩, ⟨_, _, _, ⟨-, -, rfl⟩, ⟨rfl, rfl⟩, rfl⟩, rfl⟩
  simp

end Turing.MultiTapeTM
