/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @9cce4cc7 (unsubmitted)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.StreamFold
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.InputHead
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.MarkWork
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.WhileCond

/-!
# Step machines, on words

A machine that carries the state of a step machine on tape `V`, behind two cells that record the
symbol under the input head. Each round records that symbol with `peekInput`, emits with `E` and
computes the next state with `Nm` (`frozenRound`), writes the move of the input head to tape `M`
with `Mm` and moves the input head there, and writes to tape `C` with `Cm` whether another round
follows. The input head stays where the step machine has it between the rounds.

## Main definitions

* `Turing.MultiTapeTM.stepRound`: one round.
* `Turing.MultiTapeTM.stepTM`: the rounds, between the initial state and the final clean-up.

## Main results

* `Turing.MultiTapeTM.transformsTapesAt_stepRound`: the specification of a round.
* `Turing.MultiTapeTM.computesTidily_stepTM`: the rounds compute tidily.
-/

namespace Turing.MultiTapeTM

variable {K : ℕ} {SI SE SN SM SC : Type*} {I : MultiTapeTM K Bool SI}
  {E : MultiTapeTM K Bool SE} {Nm : MultiTapeTM K Bool SN} {Mm : MultiTapeTM K Bool SM}
  {Cm : MultiTapeTM K Bool SC} {V N F C M : Fin K}

/-- The two cells in front of the state on tape `V`, before the symbol under the input head is
recorded in them. -/
@[expose] public def slot : List Bool := [false, false]

/-- One round: clear the flag tape `C`, record the symbol under the input head on tape `V`, emit
with `E` and compute the next state with `Nm`, write the move to tape `M` with `Mm`, move the input
head, clear tape `M` and write the flag with `Cm`. -/
public noncomputable def stepRound (E : MultiTapeTM K Bool SE) (Nm : MultiTapeTM K Bool SN)
    (Mm : MultiTapeTM K Bool SM) (Cm : MultiTapeTM K Bool SC) (V N F C M : Fin K)
    (hVN : V ≠ N) (hVF : V ≠ F) (hNF : N ≠ F) :=
  ((clearWork Bool).extendTapes (tapeEmb C)).freezeInput.seq
    ((peekInput.extendTapes (tapeEmb V)).seq
      ((frozenRound E Nm V N F hVN hVF hNF).freezeInput.seq
        (Mm.freezeInput.seq
          ((moveInput.extendTapes (tapeEmb M)).seq
            (((clearWork Bool).extendTapes (tapeEmb M)).freezeInput.seq Cm.freezeInput)))))

/-- The tapes between two rounds: the state `w` on tape `V` behind the two cells of `slot`, and
the flag `c` on tape `C`. -/
@[expose] public def stepTapes (V C : Fin K) (w c : List Bool) : Fin K → List Bool :=
  Function.update (Function.update (fun _ => []) V (slot ++ w)) C c

/-- The time of a round, in the lengths of the old flag `lc`, of the word `lu` that the parts
read, of the new state `lv` and of the move `lm`, and the times of the parts. -/
@[expose] public def stepRoundTime (lc lu lv lm tE tN tM tC : ℕ) : ℕ :=
  3 * (lc + 1) + (2 + ((tE + (tN + (3 * (lu + 1) + ((3 * lv + 10) + 3 * (lv + 1))))) +
    (tM + (1 + (3 * (lm + 1) + tC)))))

/-- The space of a round, as `stepRoundTime`, on `K` tapes. -/
@[expose] public def stepRoundSpace (K lc lu lv lm sE sN sM sC : ℕ) : ℕ :=
  lc + 1 + K + ((2 + (K - 1)) + ((sE + (sN + ((lu + 1 + K) + ((4 * lv + K + 15) +
    (lv + 1 + K))))) + (sM + ((1 + (K - 1)) + ((lm + 1 + K) + sC)))))

lemma update_blank_nil {l V : Fin K} (hl : l ≠ V) (v : List Bool) :
    Function.update (Function.update (fun _ : Fin K => ([] : List Bool)) V v) l [] =
      Function.update (fun _ => []) V v := by
  funext j
  by_cases hj : j = l
  · subst hj
    simp [hl]
  · simp [hj]

/-- **A round.** If, from the state `w` behind the symbol `a` under the input head, `E` emits `e`
and `Nm` computes the next state `w'`, and from `w'` `Mm` writes the move `m` and `Cm` the flag
`c'`, then a round takes the state `w` and any flag to `w'` and the flag `c'`, emitting `e`, and
moves the input head by `m`. -/
public theorem transformsTapesAt_stepRound (hVN : V ≠ N) (hVF : V ≠ F) (hNF : N ≠ F)
    (hVC : V ≠ C) (hVM : V ≠ M) (x : List Bool) (p : Fin (x.length + 2))
    {w w' c c' e m : List Bool} {tE sE tN sN tM sM tC sC : ℕ}
    (hE : TransformsTapes E (fun _ ws => ws = Function.update (fun _ => []) V
        (peekWord (inputSymbolAt x p) ++ w))
      (fun _ ws ws' em => ws' = ws ∧ em = e) tE sE)
    (hN : TransformsTapes Nm (fun _ ws => ws = Function.update (fun _ => []) V
        (peekWord (inputSymbolAt x p) ++ w))
      (fun _ ws ws' em => ws' = Function.update ws N (slot ++ w') ∧ em = []) tN sN)
    (hM : TransformsTapes Mm (fun _ ws => ws = Function.update (fun _ => []) V (slot ++ w'))
      (fun _ ws ws' em => ws' = Function.update ws M m ∧ em = []) tM sM)
    (hC : TransformsTapes Cm (fun _ ws => ws = Function.update (fun _ => []) V (slot ++ w'))
      (fun _ ws ws' em => ws' = Function.update ws C c' ∧ em = []) tC sC) :
    TransformsTapesAt (stepRound E Nm Mm Cm V N F C M hVN hVF hNF)
      (fun input p₀ ws => input = x ∧ p₀.val = p.val ∧ ws = stepTapes V C w c)
      (fun input _ _ p' ws' em => input = x ∧ p'.val = (moveInputPos p (moveOfCell m.head?)).val ∧
        ws' = stepTapes V C w' c' ∧ em = e)
      (stepRoundTime c.length (peekWord (inputSymbolAt x p) ++ w).length (slot ++ w').length
        m.length tE tN tM tC)
      (stepRoundSpace K c.length (peekWord (inputSymbolAt x p) ++ w).length (slot ++ w').length
        m.length sE sN sM sC) := by
  set a := inputSymbolAt x p
  -- clear the flag
  have h₁ := TransformsWords.freezeInput ((transformsTapes_clearWork_tapeEmb C c).words
    (ws := stepTapes V C w c) (ws' := Function.update (fun _ => []) V (slot ++ w)) (e := [])
    (fun _ => by simp [stepTapes])
    fun _ _ _ ⟨h, he⟩ => ⟨by rw [h, stepTapes, Function.update_idem, update_blank_nil hVC.symm],
      he⟩) x p.val
  -- record the symbol under the input head
  have h₂ := (transformsTapesAt_peekInput.tapeEmb V).wordsAt (x := x) (p := p.val) (p' := p.val)
    (ws := Function.update (fun _ => []) V (slot ++ w))
    (ws' := Function.update (fun _ => []) V (peekWord a ++ w)) (e := [])
    (fun _ _ => by simp [slot]) fun q q' v e' hq ⟨v', ⟨hq', hv, he⟩, h⟩ => by
      obtain rfl : q = p := Fin.ext hq
      exact ⟨by rw [hq'], by rw [h, hv]; simp [slot, a], he⟩
  -- emit and compute the next state
  have h₃ := TransformsWords.freezeInput (transformsTapes_frozenRound hVN hVF hNF hE hN) x p.val
  -- write the move, move the input head and clear the move
  have h₄ := TransformsWords.freezeInput (hM.words
    (ws' := Function.update (Function.update (fun _ => []) V (slot ++ w')) M m) (e := [])
    (fun _ => rfl) fun _ _ _ h => h) x p.val
  have h₅ := (transformsTapesAt_moveInput.tapeEmb M).wordsAt (x := x) (p := p.val)
    (p' := (moveInputPos p (moveOfCell m.head?)).val)
    (ws := Function.update (Function.update (fun _ => []) V (slot ++ w')) M m)
    (ws' := Function.update (Function.update (fun _ => []) V (slot ++ w')) M m) (e := [])
    (fun _ _ => trivial) fun q q' v e' hq ⟨v', ⟨hq', hv, he⟩, h⟩ => by
      obtain rfl : q = p := Fin.ext hq
      exact ⟨by rw [hq']; simp, by rw [h, hv]; simp, he⟩
  have h₆ := TransformsWords.freezeInput ((transformsTapes_clearWork_tapeEmb M m).words
    (ws := Function.update (Function.update (fun _ => []) V (slot ++ w')) M m)
    (ws' := Function.update (fun _ => []) V (slot ++ w')) (e := []) (fun _ => by simp)
    fun _ _ _ ⟨h, he⟩ => ⟨by rw [h, Function.update_idem, update_blank_nil hVM.symm], he⟩)
    x (moveInputPos p (moveOfCell m.head?)).val
  -- write the flag
  have h₇ := TransformsWords.freezeInput (hC.words (ws' := stepTapes V C w' c') (e := [])
    (fun _ => rfl) fun _ _ _ h => h) x (moveInputPos p (moveOfCell m.head?)).val
  exact (h₁.seq (h₂.seq (h₃.seq (h₄.seq (h₅.seq (h₆.seq h₇)))))).congr rfl rfl rfl rfl (by simp)

/-- The step machine on words: write the initial state with `I` and the flag with `Cm`, run rounds
while the flag is not blank, then clear tape `V` and rewind the input. -/
public noncomputable def stepTM (I : MultiTapeTM K Bool SI) (E : MultiTapeTM K Bool SE)
    (Nm : MultiTapeTM K Bool SN) (Mm : MultiTapeTM K Bool SM) (Cm : MultiTapeTM K Bool SC)
    (V N F C M : Fin K) (hVN : V ≠ N) (hVF : V ≠ F) (hNF : N ≠ F) :=
  (I.seq Cm).seq ((whileCond (fun _ w => (w C).isSome) (stepRound E Nm Mm Cm V N F C M hVN hVF
    hNF)).seq (((clearWork Bool).extendTapes (tapeEmb V)).freezeInput.seq (rewindInputOn K Bool)))

/-- **The step machine on words.** If `I` writes the initial state `ws 0` and, for every round
`n`, from the state `ws n` behind the symbol under the input head at `ps n`, `E` emits `es n` and
`Nm` computes the next state, from which `Mm` writes the move `ms n` that takes the input head to
`ps (n + 1)`, and `Cm` writes from every state `ws n` a flag `cs n` that is blank exactly after the
last round `rounds`, then `stepTM` emits the words `es n`, tidily. -/
public theorem computesTidily_stepTM (hVN : V ≠ N) (hVF : V ≠ F) (hNF : N ≠ F) (hVC : V ≠ C)
    (hVM : V ≠ M) (x : List Bool) (rounds : ℕ) (ws es ms cs : ℕ → List Bool)
    (ps : ℕ → Fin (x.length + 2)) (hp₀ : ps 0 = 1)
    (hps : ∀ n < rounds, ps (n + 1) = moveInputPos (ps n) (moveOfCell (ms n).head?))
    (hcs : ∀ n < rounds, cs n ≠ []) (hlast : cs rounds = [])
    {tI sI sR : ℕ} {tE sE tN sN tM sM tC sC : ℕ → ℕ}
    (hI : TransformsTapes I (fun inp ws => inp = x ∧ ws = fun _ => [])
      (fun _ _ ws' em => ws' = Function.update (fun _ => []) V (slot ++ ws 0) ∧ em = []) tI sI)
    (hE : ∀ n < rounds, TransformsTapes E (fun _ v => v = Function.update (fun _ => []) V
        (peekWord (inputSymbolAt x (ps n)) ++ ws n))
      (fun _ v v' em => v' = v ∧ em = es n) (tE n) (sE n))
    (hN : ∀ n < rounds, TransformsTapes Nm (fun _ v => v = Function.update (fun _ => []) V
        (peekWord (inputSymbolAt x (ps n)) ++ ws n))
      (fun _ v v' em => v' = Function.update v N (slot ++ ws (n + 1)) ∧ em = []) (tN n) (sN n))
    (hM : ∀ n < rounds, TransformsTapes Mm
      (fun _ v => v = Function.update (fun _ => []) V (slot ++ ws (n + 1)))
      (fun _ v v' em => v' = Function.update v M (ms n) ∧ em = []) (tM n) (sM n))
    (hC : ∀ n ≤ rounds, TransformsTapes Cm
      (fun _ v => v = Function.update (fun _ => []) V (slot ++ ws n))
      (fun _ v v' em => v' = Function.update v C (cs n) ∧ em = []) (tC n) (sC n))
    (hsR : ∀ n < rounds, stepRoundSpace K (cs n).length
      (peekWord (inputSymbolAt x (ps n)) ++ ws n).length (slot ++ ws (n + 1)).length
        (ms n).length (sE n) (sN n) (sM n) (sC (n + 1)) ≤ sR) :
    (stepTM I E Nm Mm Cm V N F C M hVN hVF hNF).ComputesTidilyInTimeAndSpace x
      ((List.range rounds).map es).flatten
      ((tI + tC 0) + ((∑ n ∈ Finset.range rounds, (stepRoundTime (cs n).length
        (peekWord (inputSymbolAt x (ps n)) ++ ws n).length (slot ++ ws (n + 1)).length
          (ms n).length (tE n) (tN n) (tM n) (tC (n + 1)) + 1) + 1) +
        (3 * ((slot ++ ws rounds).length + 1) + (x.length + 2))))
      ((sI + sC 0) + ((2 * K * sR + K) + ((slot ++ ws rounds).length + 1 + K + K))) := by
  -- the rounds
  let P (n : ℕ) (inp : List Bool) (p : Fin (inp.length + 2)) (v : Fin K → List Bool)
      (em : List Bool) : Prop :=
    inp = x ∧ p.val = (ps n).val ∧ v = stepTapes V C (ws n) (cs n) ∧
      em = ((List.range n).map es).flatten
  have hround : ∀ n < rounds, ∀ acc, TransformsTapesAt (stepRound E Nm Mm Cm V N F C M hVN hVF hNF)
      (fun inp p v => P n inp p v acc) (fun inp _ _ p' v' e => P (n + 1) inp p' v' (acc ++ e))
      (stepRoundTime (cs n).length (peekWord (inputSymbolAt x (ps n)) ++ ws n).length
        (slot ++ ws (n + 1)).length (ms n).length (tE n) (tN n) (tM n) (tC (n + 1))) sR := by
    intro n hn acc
    refine (transformsTapesAt_stepRound hVN hVF hNF hVC hVM x (ps n) (c := cs n) (hE n hn)
      (hN n hn) (hM n hn) (hC (n + 1) hn)).imp (fun _ _ _ ⟨hin, hp, hv, _⟩ => ⟨hin, hp, hv⟩) ?_
      le_rfl (hsR n hn)
    rintro _ _ _ _ _ _ ⟨-, -, -, rfl⟩ ⟨hin, hp, hv, rfl⟩
    exact ⟨hin, by rw [hp, hps n hn], hv, by simp [List.range_succ]⟩
  have hmore : ∀ n < rounds, ∀ inp p v em, P n inp p v em →
      condAt (fun _ w => (w C).isSome) inp p v := by
    rintro n hn inp p v em ⟨-, -, rfl, -⟩
    obtain ⟨b, l, hbl⟩ := List.exists_cons_of_ne_nil (hcs n hn)
    simp [condAt, stepTapes, hbl]
  have hloop := transformsTapesAt_whileCond hround hmore
    (R := fun inp _ v em => inp = x ∧ v = Function.update (fun _ => []) V (slot ++ ws rounds) ∧
      em = ((List.range rounds).map es).flatten)
    (fun _ _ _ _ ⟨hin, _, hv, he⟩ => ⟨by simp [condAt, hv, stepTapes, hlast], hin,
      by rw [hv, stepTapes, hlast, update_blank_nil hVC.symm], he⟩)
  -- clear the state and rewind the input
  have hclear := ((transformsTapes_clearWork_tapeEmb V (slot ++ ws rounds)).imp
    (P' := fun _ v => v = Function.update (fun _ => []) V (slot ++ ws rounds))
    (Q' := fun _ _ v' em => v' = (fun _ => []) ∧ em = []) (fun _ _ h => by simp [h])
    (fun _ _ _ _ hv ⟨h, he⟩ => ⟨by rw [h, hv]; simp, he⟩) le_rfl le_rfl).freezeInput.imp
    (P' := fun inp _ v => inp = x ∧ v = Function.update (fun _ => []) V (slot ++ ws rounds))
    (fun _ _ _ h => h.2) (fun _ _ _ _ _ _ _ h => h) le_rfl le_rfl
  have hend := transformsTapesAt_seq hclear (transformsTapesAt_rewindInput (k := K) x)
    fun _ _ _ _ _ _ h _ => h.1
  have hmain := transformsTapesAt_seq hloop hend fun _ _ _ _ _ _ _ ⟨hin, hv, _⟩ => ⟨hin, hv⟩
  -- the initial state and flag
  have hstart := transformsTapes_seq hI (hC 0 (Nat.zero_le _)) fun _ _ _ _ _ ⟨h, _⟩ => h
  have hall := transformsTapesAt_seq hstart.transformsTapesAt hmain
    fun _ _ _ p' _ _ ⟨_, hin, _⟩ ⟨hp', _, _, _, ⟨hv₁, _⟩, ⟨hv₂, _⟩, _⟩ =>
      ⟨hin, by simp [hp', hp₀], by rw [hv₂, hv₁]; rfl, by simp⟩
  refine (hall.transformsTapes ?_).imp (fun _ _ ⟨hin, hv⟩ => ⟨rfl, hin, hv⟩) ?_ ?_ ?_
  · rintro _ _ _ _ _ _ ⟨_, _, _, _, -, ⟨_, _, _, _, -, ⟨_, _, _, _, -, ⟨hp, -⟩, -⟩, -⟩, -⟩
    exact hp
  · rintro _ _ _ _ _ ⟨_, _, _, _, ⟨-, -, _, _, ⟨-, rfl⟩, ⟨-, rfl⟩, rfl⟩, ⟨_, _, _, _, ⟨-, -, rfl⟩,
      ⟨_, _, _, _, ⟨-, hv, rfl⟩, ⟨-, rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    exact ⟨hv, by simp⟩
  · omega
  · omega

end Turing.MultiTapeTM
