/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Replay
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.PreparePair
import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapesView
import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.InputFromTape
import Complexity.Foundations.Data.Fin.Tuple
import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Tactic.Linarith

/-!
# Efficient replay from an encoded input and saved coins

Replay receives an ordinary encoded pair of coins and input. A pair preparer writes both words,
a marker enables virtual input, and the saved-coin controller executes the supplied transitions.
The final tidy normalization clears the working storage and restores all heads.

## Main results

* `Turing.MultiTapePTM.computableTidilyInLinearTimeAndSpace_runClosedCoins`: deterministic replay
  has a uniform linear time and space bound in the encoded pair length.
* `Turing.MultiTapePTM.computableInPolyTime_runClosedCoins`: deterministic replay is
  polynomial-time, for plain certificates.

## References

Adapted from the cslib `crypto` branch's MultiTape/Oracle/ReplayInput.lean at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the common machine and the tidy pair calculus.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open MultiTapeTM

variable {k r : ℕ} {State PrepareState : Type}

namespace Replay

private def tapes (k r : ℕ) : Fin (k + 1) ↪ Fin (k + r + 1) :=
  Fin.Embedding.snoc ((Fin.castAddEmb r).trans Fin.castSuccEmb)
    (a := Fin.last (k + r)) (by
    rintro ⟨i, h⟩
    have : (i : ℕ) = k + r := congrArg Fin.val h
    lia)

private def prepareTapes (k r : ℕ) : Fin (r + 2) ↪ Fin (k + r + 3) :=
  (Fin.natAddEmb k).trans Fin.castSuccEmb

private def words (k r : ℕ) (coins input : List Bool) : Fin (k + r + 3) → List Bool :=
  Fin.snoc (Fin.append (n := r + 2) (fun _ : Fin k => [])
    (Fin.append (fun _ : Fin r => []) ![coins, input])) []

private def initial {Q : Type} (k r : ℕ) (coins input : List Bool) (q : Option Q) :
    Cfg (k + r + 1) Bool Q input :=
  wordsCfg input q (Fin.snoc (fun _ => []) coins) []

private theorem words_eq (k r : ℕ) (coins input : List Bool) :
    words k r coins input = Fin.append (Fin.snoc (fun _ : Fin (k + r) => []) coins)
      ![input, []] := by
  simp only [words, ← Fin.append_snoc, Fin.append_left_snoc]
  simpa [Fin.append_const, Function.comp_def] using
    (Fin.append_assoc (fun _ : Fin k => ([] : List Bool)) (fun _ : Fin r => [])
      (![coins, input, []] : Fin 3 → List Bool)).symm

private theorem runFrom_mark (coins input outer : List Bool) :
    (markFlag (k + r + 1) (some true)).runFrom
        (wordsCfg outer (some (markWork Bool (some true)).q₀) (words k r coins input) []) 2 =
      inCfg true (initial k r coins input (Q := MarkWorkState) none) outer := by
  rw [words_eq, markFlag, runFrom_tapeEmb]
  have hv : oneTapeCfg (Fin.natAdd (k + r + 1) 1)
      (wordsCfg outer (some (markWork Bool (some true)).q₀)
        (Fin.append (Fin.snoc (fun _ : Fin (k + r) => []) coins) ![input, []]) []) =
      ⟨some (markWork Bool (some true)).q₀, 1, fun _ => (fun _ => none), fun _ => 0, []⟩ := by
    simp [oneTapeCfg, wordsCfg]
  rw [hv, runFrom_markWork, embed_tapeEmb]
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;>
    cases i using Fin.addCases with
    | left j => simp [initial, wordsCfg,
        Fin.castAdd_ne_natAdd]
    | right j => match j with
      | 0 | 1 => simp [initial, wordsCfg]

private theorem embed_initial (machine : MultiTapePTM k Bool State) (coins input : List Bool) :
    embed (tapes k r) (config (machine.initialConfig input) (tapeOfList coins) 0)
      (fun _ _ => none) (fun _ => 0) = initial k r coins input (some (some machine.initial)) := by
  have hc : config (machine.initialConfig input) (tapeOfList coins) 0 =
      wordsCfg input (some (some machine.initial)) (Fin.snoc (fun _ => []) coins) [] := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;>
      induction i using Fin.lastCases <;> simp [config, MultiTapeMachine.initialConfig, wordsCfg]
  rw [hc]
  simp only [initial]
  have he := embed_wordsCfg (input := input) (tapes k r) (ws := fun _ => [])
    (q := some (some machine.initial)) (out := [])
    (v := Fin.snoc (fun _ => []) coins) (ws' := Fin.snoc (fun _ => []) coins)
    (by
      intro j
      induction j using Fin.lastCases <;>
        simp [tapes, Fin.Embedding.snoc_last, Fin.Embedding.snoc_castSucc,
          Function.Embedding.trans_apply, Fin.castAddEmb_apply])
    (by
      intro i hi
      induction i using Fin.lastCases with
      | last => exact (hi ⟨Fin.last k, by simp [tapes, Fin.Embedding.snoc_last]⟩).elim
      | cast i => simp)
  simpa only [tapeOfList_nil] using he

private theorem runFrom_initial (machine : MultiTapePTM k Bool State) (coins input : List Bool) :
    (machine.replay.extendTapes (tapes k r)).runFrom
        (initial k r coins input (some (some machine.initial))) (coins.length + 1) =
      embed (tapes k r)
        (stopped (machine.runClosedConfigFromCoins coins (machine.initialConfig input))
          (tapeOfList coins) coins.length) (fun _ _ => none) (fun _ => 0) := by
  rw [← embed_initial machine coins input, ← embedHom_apply machine.replay, runFrom_map,
    runFrom_replay, embedHom_apply]

private theorem runFrom_prepare (prepare : MultiTapeTM (r + 2) Bool PrepareState)
    (coins input outer : List Bool) (t s : ℕ)
    (h : TransformsTapes prepare (fun inp ws => inp = outer ∧ ws = fun _ => [])
      (fun _ _ ws' emitted =>
        ws' = Fin.append (fun _ : Fin r => []) ![coins, input] ∧ emitted = []) t s) :
    (prepare.extendTapes (prepareTapes k r)).runFrom
        ((prepare.extendTapes (prepareTapes k r)).initCfg outer) t =
      wordsCfg outer none (words k r coins input) [] := by
  obtain ⟨ws', _, hrun, ⟨⟨hv, rfl⟩, hx⟩, _⟩ :=
    transformsTapes_iff_runFrom.mp (h.extendTapes (prepareTapes k r))
      outer (fun _ => []) [] ⟨rfl, rfl⟩
  have hw : ws' = words k r coins input := by
    funext i
    induction i using Fin.lastCases with
    | last =>
      rw [hx]
      · simp [words]
      · rintro ⟨j, hj⟩
        have : k + (j : ℕ) = k + r + 2 := congrArg Fin.val hj
        lia
    | cast i =>
      cases i using (Fin.addCases (m := k) (n := r + 2)) with
      | left i =>
        rw [hx]
        · simp [words]
        · rintro ⟨j, hj⟩
          have : (Fin.natAdd k j).castSucc = (i.castAdd (r + 2)).castSucc := hj
          exact Fin.castAdd_ne_natAdd i j (Fin.castSucc_injective _ this).symm
      | right j =>
        have hj : ws' (Fin.natAdd k j).castSucc = Fin.append (fun _ => []) ![coins, input] j :=
          congrFun hv j
        simpa only [words, Fin.snoc_castSucc, Fin.append_right] using hj
  simpa only [initCfg_eq_wordsCfg, hw, List.nil_append] using hrun

private noncomputable def compile (machine : MultiTapePTM k Bool State)
    (prepare : MultiTapeTM (r + 2) Bool PrepareState) :
    MultiTapeTM (k + r + 3) Bool (PrepareState ⊕ MarkWorkState ⊕ Option State) :=
  (prepare.extendTapes (prepareTapes k r)).seq
    ((markFlag (k + r + 1) (some true)).seq
      (machine.replay.extendTapes (tapes k r)).inputFromTape)

private def finish (machine : MultiTapePTM k Bool State) (coins input outer : List Bool) :
    Cfg (k + r + 3) Bool (PrepareState ⊕ MarkWorkState ⊕ Option State) outer :=
  Sequential.rightCfg (Sequential.rightCfg (inCfg true
    (embed (tapes k r)
      (stopped (machine.runClosedConfigFromCoins coins (machine.initialConfig input))
        (tapeOfList coins) coins.length) (fun _ _ => none) (fun _ => 0)) outer))

private theorem runFrom_compile (machine : MultiTapePTM k Bool State)
    (prepare : MultiTapeTM (r + 2) Bool PrepareState) (coins input outer : List Bool) (t s : ℕ)
    (h : TransformsTapes prepare (fun inp ws => inp = outer ∧ ws = fun _ => [])
      (fun _ _ ws' emitted =>
        ws' = Fin.append (fun _ : Fin r => []) ![coins, input] ∧ emitted = []) t s) :
    (compile machine prepare).runFrom ((compile machine prepare).initCfg outer)
        (t + (2 + (coins.length + 1))) = finish machine coins input outer := by
  have hr := runFrom_map ((machine.replay.extendTapes (tapes k r)).inCfgHom true outer)
    (initial k r coins input (some (some machine.initial))) (coins.length + 1)
  simp only [inCfgHom_apply, runFrom_initial] at hr
  have hq : (machine.replay.extendTapes (tapes k r)).inputFromTape.q₀ = some machine.initial := by
    simp [inputFromTape, q₀_ofTr, replay]
  have hm := runFrom_mark (k := k) (r := r) coins input outer
  have hs := runFrom_seq (tm₁ := (machine.replay.extendTapes (tapes k r)).inputFromTape) hm rfl
    (by simpa only [hq, Cfg.withState, initial, wordsCfg, inCfg] using hr) rfl
  have hp := runFrom_prepare (k := k) prepare coins input outer t s h
  have hqseq : ((markFlag (k + r + 1) (some true)).seq
      (machine.replay.extendTapes (tapes k r)).inputFromTape).q₀ =
        Sum.inl (markWork Bool (some true)).q₀ := by
    simp [MultiTapeTM.seq, q₀_ofTr, markFlag]
  have hc := runFrom_seq (tm₁ := (markFlag (k + r + 1) (some true)).seq
      (machine.replay.extendTapes (tapes k r)).inputFromTape) hp rfl
    (by simpa [hqseq, Cfg.withState, Sequential.leftCfg, wordsCfg, Cfg.mapState] using hs) rfl
  simpa [compile, initCfg_eq_wordsCfg, Sequential.leftCfg, wordsCfg, Cfg.mapState,
    MultiTapeTM.seq, q₀_ofTr, finish, inCfg] using hc

end Replay

/-- Running a fixed machine on a supplied pair of coins and input is tidily computable in linear
time and space. The bound charges input preparation, every supplied coin, and final cleanup;
it does not assume that the source machine halts. -/
theorem computableTidilyInLinearTimeAndSpace_runClosedCoins [Finite State]
    (machine : MultiTapePTM k Bool State) :
    ComputableTidilyInLinearTimeAndSpace
      (fun p : List Bool × List Bool => machine.runClosedCoins p.1 p.2)
      (encPair encBits encBits) encBits := by
  obtain ⟨r, PrepareState, _, prepare, c, hp⟩ :=
    PairEncoding.exists_prepare encBits encBits (encPair encBits encBits)
  let size (p : List Bool × List Bool) := (encPair encBits encBits p).length + 1
  let time (p : List Bool × List Bool) := c * size p + (2 + (p.1.length + 1))
  let n := k + r + 3
  let b := (n + 1) * (c + 5)
  have hraw : ComputableInTimeAndSpace
      (fun p : List Bool × List Bool => machine.runClosedCoins p.1 p.2)
      (encPair encBits encBits) encBits (fun p => b * size p) (fun p => b * size p) := by
    refine ⟨n, PrepareState ⊕ MarkWorkState ⊕ Option State, inferInstance,
      Replay.compile machine prepare, fun p => ?_⟩
    have hr := Replay.runFrom_compile machine prepare p.1 p.2 (encPair encBits encBits p)
      (c * size p) (c * size p) (hp p)
    have hh : ((Replay.compile machine prepare).runFrom
        ((Replay.compile machine prepare).initCfg (encPair encBits encBits p))
        (time p)).Halted := by
      rw [show time p = c * size p + (2 + (p.1.length + 1)) from rfl, hr]
      rfl
    have hlen := length_le_encPair_left encBits encBits p
    have ht₀ : time p + 1 ≤ (c + 5) * size p := by
      dsimp only [time, size]
      simp only [encBits_apply] at hlen
      nlinarith
    have ht : time p ≤ b * size p :=
      (Nat.le_succ _).trans (ht₀.trans
        (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left (c + 5) (Nat.succ_pos n))))
    have hs : n * (time p + 1) ≤ b * size p := by
      calc
        _ ≤ n * ((c + 5) * size p) := Nat.mul_le_mul_left n ht₀
        _ ≤ (n + 1) * ((c + 5) * size p) := Nat.mul_le_mul_right _ (Nat.le_succ n)
        _ = _ := (Nat.mul_assoc _ _ _).symm
    refine ⟨⟨time p, hh, ?_⟩, (runsInTime_of_halted hh).mono ht,
      runsInSpace_of_halted hh ?_⟩
    · change ((Replay.compile machine prepare).runFrom _
        (c * size p + (2 + (p.1.length + 1)))).output = _
      rw [hr]
      rfl
    · exact (MultiTapeNTM.RunPath.ofDeterministic (Replay.compile machine prepare)
        ((Replay.compile machine prepare).initCfg (encPair encBits encBits p))
        (time p)).space_le_mul_time_add_one.trans hs
  obtain ⟨d, htidy⟩ := hraw.exists_computableTidilyInTimeAndSpace
  refine ⟨(d + 5) * (b + 1), htidy.mono (fun p => ?_) (fun p => ?_)⟩ <;>
    dsimp only [size] <;>
    nlinarith [Nat.zero_le (d * b * (encPair encBits encBits p).length)]

/-- The ordinary functional polynomial-time API can invoke saved-coin replay directly. -/
@[fun_prop] theorem computableTidilyInPolyTime_runClosedCoins [Finite State]
    (machine : MultiTapePTM k Bool State) :
    ComputableTidilyInPolyTime
      (fun p : List Bool × List Bool => machine.runClosedCoins p.1 p.2)
      (encPair encBits encBits) encBits :=
  .of_linear (computableTidilyInLinearTimeAndSpace_runClosedCoins machine)

/-- `computableTidilyInPolyTime_runClosedCoins` for plain certificates. -/
@[fun_prop] theorem computableInPolyTime_runClosedCoins [Finite State]
    (machine : MultiTapePTM k Bool State) :
    ComputableInPolyTime
      (fun p : List Bool × List Bool => machine.runClosedCoins p.1 p.2)
      (encPair encBits encBits) encBits :=
  (computableTidilyInPolyTime_runClosedCoins machine).computableInPolyTime

end Turing.MultiTapePTM
