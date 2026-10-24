/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Alternation.Game
public import Complexity.Computability.Machines.Turing.MultiTape.Alternating.GuessVerify
public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.InputFromTape
public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.OutputToTape
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Games of polynomially many moves are in `AP`

A polynomial-time game verifier (`Cslib.Complexity.IsGameVerifier`) decides a problem through a
game of `2 * p n` alternate single-bit moves, the existential player first. Through the
guess-then-verify alternating machine (`Turing.MultiTapeATM.guessVerify`, in
`Complexity.Computability.Machines.Turing.MultiTape.Alternating.GuessVerify`)
[Chandra, Kozen and Stockmeyer][ChandraKozenStockmeyer1981]
[Arora and Barak, Section 5.3][AroraBarak09], acceptance in the guessing phase is the game of `L`
alternate moves (`Turing.MultiTapeATM.GuessVerify.acceptsWithin_lift_tag`), giving the overall time
and acceptance specification (`Turing.MultiTapeATM.guessVerify_spec`).

For a game verifier `V`, `prep` writes the frame of `2 * p (enc a).length` bits followed by
`enc a`, by a polynomial-time machine with its output redirected to tape `B`
(`Turing.MultiTapeTM.outputToWord`), and `verify` runs a polynomial-time machine computing
`V (a, z)` from the word on tape `B`, which is the encoded pair `encPair encBits enc (z, a)` of the
moves `z` and the instance (`Turing.MultiTapeTM.inputFromWord`). The machine therefore runs within
polynomial time, and it accepts `enc a` exactly when the existential player wins the game, proving
that every problem with a polynomial-time game verifier is in `AP`
(`Cslib.Complexity.IsGameVerifier.mem_AP`).

## Main results

* `Turing.MultiTapeATM.GuessVerify.acceptsWithin_lift_tag`: the guessing phase is a game.
* `Turing.MultiTapeATM.guessVerify_spec`: the guess-then-verify machine plays the game within the
  time of `prep`, plus `4 * L + 3`, plus the time of `verify`.
* `Cslib.Complexity.IsGameVerifier.mem_AP`: every problem with a polynomial-time game verifier is
  in `AP`.

## References

* [A. K. Chandra, D. C. Kozen, L. J. Stockmeyer, *Alternation*][ChandraKozenStockmeyer1981]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Turing.MultiTapeATM

namespace GuessVerify

open MultiTapeTM

variable {k : ℕ} {S₁ S₂ : Type} {B : Fin k} {prep : MultiTapeTM k Bool S₁}
  {verify : MultiTapeTM k Bool S₂} {input : List Bool}

/-- **The guessing phase.** From the tag of the first of `r` pairs `true, true` that follow the
pairs of the moves `zd`, with the player `u` to move (`true` for universal), acceptance within
`2 * r + 1 + n` moves is the game of `r` alternate moves, the first by the player `u`, after which
the configuration ending the guessing phase accepts within `n` moves. -/
theorem acceptsWithin_lift_tag (r : ℕ) : ∀ (zd : List Bool) (u : Bool) (n : ℕ),
    (guessVerify B prep verify).AcceptsWithin (2 * r + 1 + n)
      (lift S₁ B verify (cfg (input := input) B (some (.tag u))
        (frame (zd ++ List.replicate r true) ++ input) (2 * zd.length))) ↔
    Cslib.Complexity.Alternation (!u) (List.replicate r 1) fun zr =>
      (guessVerify B prep verify).AcceptsWithin n
        (lift S₁ B verify (cfg (input := input) B none (frame (zd ++ zr) ++ input)
          (2 * (zd.length + r)))) := by
  induction r with
  | zero =>
    intro zd u n
    rw [show 2 * 0 + 1 + n = n + 1 by omega, List.replicate_zero, List.replicate_zero,
      List.append_nil, acceptsWithin_succ_of_next_eq (next_lift_halt zd u),
      Cslib.Complexity.alternation_nil, List.append_nil, add_zero]
  | succ r ih =>
    intro zd u n
    simp only [List.replicate_succ]
    have hstate : (lift S₁ B verify (cfg (input := input) B (some (.move u))
        (frame (zd ++ true :: List.replicate r true) ++ input)
        (2 * zd.length + 1))).state = some (.inr (.inl (.move u))) := rfl
    have hgame (b : Bool) := ih (zd ++ [b]) (!u) n
    simp only [Bool.not_not, List.append_assoc, List.singleton_append, List.length_append,
      List.length_singleton, show zd.length + 1 + r = zd.length + (r + 1) by ring] at hgame
    rw [show 2 * (r + 1) + 1 + n = 2 * r + 1 + n + 1 + 1 by omega,
      acceptsWithin_succ_of_next_eq (next_lift_tag zd _ true u)]
    cases u
    · rw [(guessVerify B prep verify).acceptsWithin_succ_of_existential hstate rfl,
        Bool.not_false, Cslib.Complexity.alternation_true_one_cons]
      refine exists_congr fun b => ?_
      rw [next_lift_move]
      exact hgame b
    · rw [(guessVerify B prep verify).acceptsWithin_succ_of_universal hstate rfl,
        Bool.not_true, Cslib.Complexity.alternation_false_one_cons]
      refine forall_congr' fun b => ?_
      rw [next_lift_move]
      exact hgame b

end GuessVerify

section Spec

open MultiTapeTM

variable {k : ℕ} {S₁ S₂ : Type} {B : Fin k} {prep : MultiTapeTM k Bool S₁}
  {verify : MultiTapeTM k Bool S₂} {input : List Bool}

/-- **The guess-then-verify machine plays the game of `L` moves.** Suppose that `prep`, started on
the input with blank work tapes, has halted after `t₁` steps with the frame of `L` bits `true`
followed by the input on tape `B` and every other work tape blank, and that `verify`, started on
the frame of any `L` moves `z` followed by the input on tape `B` and every other work tape blank,
has halted after `t₂` steps with output `[V z]`. Then for some
`T ≤ t₁ + 4 * L + 3 + t₂`, every list of `T` moves reaches a halted configuration, and the
machine accepts within `T` moves exactly when the existential player wins the game of `L`
alternate moves, the existential first, with winning condition `V`. -/
theorem guessVerify_spec {L t₁ t₂ : ℕ} {V : List Bool → Bool}
    (hprep : prep.runFrom (Cfg.init prep.q₀ input) t₁ = wordsCfg input none
      (Function.update (fun _ => []) B (frame (List.replicate L true) ++ input)) [])
    (hverify : ∀ z : List Bool, z.length = L →
      (verify.runFrom (wordsCfg input (some verify.q₀)
        (Function.update (fun _ => []) B (frame z ++ input)) []) t₂).state = none ∧
      (verify.runFrom (wordsCfg input (some verify.q₀)
        (Function.update (fun _ => []) B (frame z ++ input)) []) t₂).output = [V z]) :
    ∃ T ≤ t₁ + (4 * L + 3 + t₂),
      (guessVerify B prep verify).HaltsWithin T
        ((guessVerify B prep verify).toPTM.toNTM.initCfg input) ∧
      ((guessVerify B prep verify).AcceptsWithin T
        ((guessVerify B prep verify).toPTM.toNTM.initCfg input) ↔
        Cslib.Complexity.Alternation true (List.replicate L 1) fun z => V z = true) := by
  obtain ⟨u, hut, hu⟩ := exists_haltsAt (tm := prep) (cfg := Cfg.init prep.q₀ input)
    (t := t₁) (by rw [hprep]; rfl)
  obtain ⟨hdet, hstart⟩ := GuessVerify.prepare_spec (S₁ := S₁) (verify := verify) hu
    ((hu.runFrom_eq hut).symm.trans hprep)
  have hguess (zd : List Bool) (hzd : zd = []) (pos : ℕ) (hpos : pos = 2 * zd.length) :
      GuessVerify.cfg (input := input) (State := GuessState) B (some (.tag false))
        (frame (List.replicate L true) ++ input) 0 =
      GuessVerify.cfg B (some (.tag false)) (frame (zd ++ List.replicate L true) ++ input) pos := by
    subst hzd hpos
    rfl
  have hpos (z : List Bool) : 2 * ([] ++ z).length ≤ (frame z ++ input).length := by
    simpa using two_mul_length_le_length_frame_append z input
  refine ⟨u + (2 * L + 1 + (2 * L + 2 + t₂)), by omega, ?_, ?_⟩
  · rw [haltsWithin_add_iff_of_next_eq hdet, hstart, hguess [] rfl _ rfl,
      GuessVerify.haltsWithin_lift_tag]
    intro z hz
    have := GuessVerify.haltsWithin_lift_none (S₁ := S₁) (prep := prep) (hpos z)
      (hverify z hz).1
    simp only [List.nil_append, List.length_nil, zero_add] at this ⊢
    rwa [hz] at this
  · rw [acceptsWithin_add_iff_of_next_eq hdet, hstart, hguess [] rfl _ rfl,
      GuessVerify.acceptsWithin_lift_tag, Bool.not_false]
    refine Cslib.Complexity.alternation_congr_of_length fun z hz => ?_
    rw [Cslib.Complexity.sum_replicate_one] at hz
    have := GuessVerify.acceptsWithin_lift_none (S₁ := S₁) (prep := prep) (hpos z)
      (hverify z hz).1
    simp only [List.nil_append, List.length_nil, zero_add, hz] at this ⊢
    rw [this, (hverify z hz).2]
    simp

end Spec

end Turing.MultiTapeATM

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM

/-- The embedding of `Fin m` into `Fin K` that places `j` at `B`. -/
private def placeAt {m K : ℕ} (h : m ≤ K) (j : Fin m) (B : Fin K) : Fin m ↪ Fin K :=
  (Fin.castLEEmb h).trans (Equiv.swap (Fin.castLE h j) B).toEmbedding

private theorem placeAt_self {m K : ℕ} (h : m ≤ K) (j : Fin m) (B : Fin K) :
    placeAt h j B j = B := by
  simp [placeAt]

variable {α : Type} {enc : α ↪ List Bool} {p : Polynomial ℕ} {V : α × List Bool → Bool}
  {A : Set α}

/-- **Games of polynomially many moves are in `AP`** [Chandra, Kozen and
Stockmeyer][ChandraKozenStockmeyer1981]: a problem with a polynomial-time game verifier is decided
in polynomial time by the guess-then-verify machine, which writes the moves of the two players,
alternately, and then runs the verifier. -/
theorem IsGameVerifier.mem_AP
    (hV : Turing.MultiTapeTM.ComputableInPolyTime V (encPair enc encBits) encBool)
    (h : IsGameVerifier enc p V A) : A ∈ AP enc := by
  have hV := hV.tidy
  -- the number of moves, and the word prepared on tape `B`
  set L : α → ℕ := fun a => 2 * p.eval (enc a).length
  have hL : ComputableTidilyInPolyTime L enc encUnary :=
    ComputableTidilyInPolyTime.unary_mul.comp ((ComputableTidilyInPolyTime.const 2).prod
      ((ComputableTidilyInPolyTime.unary_eval p).comp
        (ComputableTidilyInPolyTime.encoding_length enc)))
  set g : α → List Bool := fun a => frame (List.replicate (L a) true) ++ enc a with hg_def
  have hg : ComputableTidilyInPolyTime g enc encBits :=
    (((ComputableTidilyInPolyTime.bitsReplicate true).comp hL).prod
      (ComputableTidilyInPolyTime.of_eq (encMid := enc) fun _ => rfl)).encoded
  have hLb : PolyBounded (fun a => (enc a).length) L := hL.polyBounded
  have hgl : PolyBounded (fun a => (enc a).length) fun a => (g a).length :=
    hg.polyBounded_length
  have hV' : ComputableTidilyInPolyTime (fun x : List Bool × α => V (x.2, x.1))
      (encPair encBits enc) encBool :=
    hV.comp ((ComputableTidilyInPolyTime.snd encBits enc).prod
      (ComputableTidilyInPolyTime.fst encBits enc))
  obtain ⟨tg, sg, htg, -, k₁, S₁, _, Tg, hTg⟩ := hg
  obtain ⟨tv, sv, htv, -, k₂, S₂, _, Tv, hTv⟩ := hV'
  obtain ⟨cv, dv, htv⟩ := htv.exists_le
  -- the machine
  have hk₁ : k₁ + 1 ≤ k₁ + 1 + (k₂ + 2) := by omega
  have hk₂ : k₂ + 2 ≤ k₁ + 1 + (k₂ + 2) := by omega
  let B : Fin (k₁ + 1 + (k₂ + 2)) := ⟨0, by omega⟩
  let prep := Tg.outputToWord.extendTapes (placeAt hk₁ (Fin.last k₁) B)
  let verify := (Tv.inputFromWord true).extendTapes (placeAt hk₂ (Fin.natAdd k₂ 0) B)
  -- the time bound
  let t₂ : α → ℕ := fun a => cv * ((g a).length + 1) ^ dv + 4
  let t : α → ℕ := fun a => tg a + (g a).length + 2 + (4 * L a + 3 + t₂ a)
  have hprep (a : α) : prep.runFrom (Cfg.init prep.q₀ (enc a)) (tg a + (g a).length + 2) =
      wordsCfg (enc a) none (Function.update (fun _ => []) B
        (frame (List.replicate (L a) true) ++ enc a)) [] := by
    obtain ⟨ws, em, hrun, ⟨rfl, rfl⟩, -⟩ := transformsTapes_iff_runFrom.mp
      ((hTg a).outputToWord_onTape (placeAt_self hk₁ (Fin.last k₁) B)) (enc a) (fun _ => [])
      [] ⟨rfl, rfl⟩
    rw [Cfg.init_eq_wordsCfg]
    exact hrun
  have hverify (a : α) (z : List Bool) (hz : z.length = L a) :
      (verify.runFrom (wordsCfg (enc a) (some verify.q₀)
        (Function.update (fun _ => []) B (frame z ++ enc a)) []) (t₂ a)).state = none ∧
      (verify.runFrom (wordsCfg (enc a) (some verify.q₀)
        (Function.update (fun _ => []) B (frame z ++ enc a)) []) (t₂ a)).output = [V (a, z)] := by
    have hlen : (encPair encBits enc (z, a)).length = (g a).length := by
      simp [hg_def, hz]
    obtain ⟨ws, em, hrun, ⟨rfl, rfl⟩, -⟩ := transformsTapes_iff_runFrom.mp
      (((hTv (z, a)).inputFromWord_extendTapes true
        (placeAt_self hk₂ (Fin.natAdd k₂ 0) B)).mono
        (Nat.add_le_add_right ((htv (z, a)).trans_eq (by rw [hlen])) 4) le_rfl)
      (enc a) _ [] rfl
    have hrun' : verify.runFrom (wordsCfg (enc a) (some verify.q₀)
        (Function.update (fun _ => []) B (frame z ++ enc a)) []) (t₂ a) = _ := hrun
    rw [hrun']
    exact ⟨rfl, rfl⟩
  have hspec (a : α) := MultiTapeATM.guessVerify_spec (hprep a) (hverify a)
  refine ⟨t, ?_, k₁ + 1 + (k₂ + 2), _, inferInstance, MultiTapeATM.guessVerify B prep verify,
    fun a => ?_⟩
  · have hpow : PolyBounded (fun a => (enc a).length) fun a => cv * ((g a).length + 1) ^ dv :=
      (PolyBounded.of_forall_le (size := id) cv dv fun _ => le_rfl).comp hgl
    exact ((htg.add hgl).add (.const 2)).add ((((PolyBounded.const 4).mul hLb).add
      (.const 3)).add (hpow.add (.const 4)))
  · obtain ⟨T, hT, hhalt, hacc⟩ := hspec a
    have hrun : (MultiTapeATM.guessVerify B prep verify).toPTM.toNTM.RunsInTime (enc a) T :=
      MultiTapeATM.runsInTime_iff_haltsWithin.mpr hhalt
    refine ⟨hrun.mono hT, ?_⟩
    rw [h a, MultiTapeATM.accepts_iff_acceptsWithin hrun, hacc]

end Cslib.Complexity
