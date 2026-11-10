/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Classes.IP.Games
public import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.Games.Repetition

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Foundations.Data.BitString.Block
import CslibFrontier.Foundations.Data.BitString.List

/-!
# Parallel repetition of private-coin games

The `t`-fold parallel repetition `Cslib.Complexity.IPGame.repeatShape t g` of a private-coin game
shape `g` plays `t` copies of `g` at once: every move sends the `t` copies' messages concatenated,
and copy `i` of a transcript is read with `Cslib.Complexity.AMGame.copyTranscript`, as for
public-coin games. The repeated verifier (`Cslib.Complexity.IPGame.repeatMsg`,
`Cslib.Complexity.IPGame.repeatDec`) gives copy `i` row `i` of its coins, sends at every move the
messages of all copies on their own parts of the transcript, and accepts when all copies accept.

The prover may coordinate the copies, but this does not help it: against an optimal prover the
repeated verifier accepts exactly `bestCount ^ t` of its `t * ρ` coin strings
(`Cslib.Complexity.IPGame.bestCount_repeat`). The coins agreeing with a transcript of the
repetition and accepting it are counted by the product over the copies
(`Cslib.Complexity.IPGame.acceptedCoins_repeat`), and the count of a product payoff factors
(`Cslib.Complexity.IPGame.count_repeatShape_prod`). So with `T(n)` copies a verifier of
`IPGameClass enc π` with yes/no thresholds `2 / 3` and `1 / 3` becomes a polynomial-time verifier
of the same pattern with thresholds `(2 / 3) ^ T(n)` and `(1 / 3) ^ T(n)`, a gap of `2 ^ T(n)`
(`Cslib.Complexity.IPGameClass.exists_repeat`). This is the gap amplification that precedes the
emulation of private coins by public coins [Goldwasser and Sipser][GoldwasserSipser1986],
[Arora and Barak, Section 8.2][AroraBarak09]. Completeness decreases too: the repetition reduces
the soundness error relative to the completeness, not both errors.

## Main definitions

* `Cslib.Complexity.IPGame.repeatShape`, `Cslib.Complexity.IPGame.repeatMsg`,
  `Cslib.Complexity.IPGame.repeatDec`: the repeated game and verifier.
* `Cslib.Complexity.IPGame.repeatVerifierMsg`, `Cslib.Complexity.IPGame.repeatVerifierDec`,
  `Cslib.Complexity.IPGame.repeatShapePoly`: `T(n)` copies of a polynomial-time verifier.

## Main results

* `Cslib.Complexity.IPGame.count_repeatShape_prod`: the count of a product payoff factors.
* `Cslib.Complexity.IPGame.agrees_repeatMsg`: the repeated verifier agrees with a transcript
  exactly when every copy agrees with its part.
* `Cslib.Complexity.IPGame.bestCount_repeat`, `Cslib.Complexity.IPGame.countAt_repeat`: **parallel
  repetition of private-coin games is multiplicative**.
* `Cslib.Complexity.IPGame.computableInPolyTime_repeatVerifierMsg`,
  `Cslib.Complexity.IPGame.computableInPolyTime_repeatVerifierDec`: the repetition runs in
  polynomial time.
* `Cslib.Complexity.IPGameClass.exists_repeat`: gap amplification.

## References

* [S. Goldwasser, M. Sipser, *Private coins versus public coins in interactive proof
  systems*][GoldwasserSipser1986]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Finset Turing.MultiTapeTM

variable {α : Type}

namespace IPGame

/-- The `t`-fold parallel repetition of a private-coin game shape: every move sends the `t`
copies' messages concatenated. -/
def repeatShape (t : ℕ) (g : List (IPMove × ℕ)) : List (IPMove × ℕ) :=
  g.map fun x => (x.1, t * x.2)

@[simp] theorem repeatShape_nil (t : ℕ) : repeatShape t [] = [] := rfl

theorem repeatShape_cons (t : ℕ) (x : IPMove × ℕ) (g : List (IPMove × ℕ)) :
    repeatShape t (x :: g) = (x.1, t * x.2) :: repeatShape t g := rfl

theorem toAM_repeatShape (t : ℕ) (g : List (IPMove × ℕ)) :
    toAM (repeatShape t g) = AMGame.repeatShape t (toAM g) := by
  simp [toAM, repeatShape, AMGame.repeatShape]

theorem verifierBits_repeatShape (t : ℕ) (g : List (IPMove × ℕ)) :
    verifierBits (repeatShape t g) = t * verifierBits g := by
  induction g with
  | nil => rfl
  | cons x g ih =>
    obtain ⟨_ | _, n⟩ := x
    · rw [repeatShape_cons, verifierBits_verifier, verifierBits_verifier, ih, Nat.mul_add]
    · rw [repeatShape_cons, verifierBits_prover, verifierBits_prover, ih]

/-- **The count of a parallel repetition on a product payoff is the product of the counts.** The
prover may coordinate the copies, but this does not help it. -/
theorem count_repeatShape_prod (t : ℕ) (g : List (IPMove × ℕ)) (f : Fin t → List Bool → ℕ) :
    count (repeatShape t g) (fun w => ∏ i, f i (AMGame.copyTranscript t i (toAM g) w)) =
      ∏ i, count g (f i) := by
  have h := count_eq_value (repeatShape t g)
    (fun w => ∏ i, f i (AMGame.copyTranscript t i (toAM g) w))
  rw [toAM_repeatShape, verifierBits_repeatShape] at h
  push_cast at h
  rw [AMGame.value_repeatShape_prod true t (toAM g) (fun i t => (f i t : ℚ))
    (fun _ _ => by positivity)] at h
  have h' : ((∏ i, count g (f i) : ℕ) : ℚ) =
      2 ^ (t * verifierBits g) * ∏ i, AMGame.value true (toAM g) fun t => (f i t : ℚ) := by
    push_cast
    simp only [count_eq_value g, prod_mul_distrib, prod_const, card_univ, Fintype.card_fin,
      ← pow_mul, mul_comm (verifierBits g) t]
  exact_mod_cast h.trans h'.symm

/-! ### The repeated verifier -/

/-- The length of move `j` of a game shape, `0` past its end. -/
def moveLength (g : List (IPMove × ℕ)) (j : ℕ) : ℕ := (g.map Prod.snd).getD j 0

theorem moveLength_append_cons (pre g : List (IPMove × ℕ)) (x : IPMove × ℕ) :
    moveLength (pre ++ x :: g) pre.length = x.2 := by
  simp [moveLength, List.getD_eq_getElem?_getD]

/-- The messages of `t` parallel copies of a verifier of shape `g` at move `j` after the transcript
`p`: copy `i` sends `msg i j` on its own part of `p`, read as a string of the length of move `j`,
and the messages of the copies are concatenated. -/
def repeatMsg (t : ℕ) (g : List (IPMove × ℕ)) (msg : ℕ → ℕ → List Bool → List Bool) (j : ℕ)
    (p : List Bool) : List Bool :=
  (List.range t).flatMap fun i => List.ofFn (BitString.ofList (moveLength g j)
    (msg i j (AMGame.copyTranscript t i (toAM (g.take j)) p)))

/-- The decision of `t` parallel copies: every copy accepts its own part of the transcript. -/
def repeatDec (t : ℕ) (g : List (IPMove × ℕ)) (dec : ℕ → List Bool → Bool) (w : List Bool) :
    Bool :=
  (List.range t).all fun i => dec i (AMGame.copyTranscript t i (toAM g) w)

theorem repeatDec_eq_true_iff (t : ℕ) (g : List (IPMove × ℕ)) (dec : ℕ → List Bool → Bool)
    (w : List Bool) :
    repeatDec t g dec w = true ↔
      ∀ i : Fin t, dec i (AMGame.copyTranscript t i (toAM g) w) = true := by
  simp only [repeatDec, List.all_eq_true, List.mem_range]
  exact ⟨fun h i => h i i.2, fun h i hi => h ⟨i, hi⟩⟩

theorem repeatShape_cons' (t : ℕ) (v : IPMove) (n : ℕ) (g : List (IPMove × ℕ)) :
    repeatShape t ((v, n) :: g) = (v, t * n) :: repeatShape t g := rfl

theorem repeatShape_append (t : ℕ) (g h : List (IPMove × ℕ)) :
    repeatShape t (g ++ h) = repeatShape t g ++ repeatShape t h := by
  simp [repeatShape]

/-- A bit string is the concatenation of `t` strings of `n` bits exactly when its blocks are
those strings. -/
theorem eq_ofList_flatMap_iff {t n : ℕ} (r : BitString (t * n)) (F : ℕ → BitString n) :
    r = BitString.ofList (t * n) ((List.range t).flatMap fun i => List.ofFn (F i)) ↔
      ∀ i : Fin t, BitString.block r i = F i := by
  have h : ((List.range t).flatMap fun i => List.ofFn (F i)) =
      List.ofFn (BitString.blocksEquiv.symm fun i : Fin t => F i) := by
    rw [BitString.ofFn_blocksEquiv_symm, List.flatMap_def, List.ofFn_eq_map,
      ← List.map_coe_finRange_eq_range, List.map_map]
    rfl
  rw [h, BitString.ofList_ofFn, Equiv.eq_symm_apply, funext_iff]
  rfl

/-- A word whose length is `k + L` is a string of `k` bits followed by a word of length `L`. -/
theorem exists_eq_ofFn_append {k L : ℕ} {u : List Bool} (hu : u.length = k + L) :
    ∃ (r : BitString k) (v : List Bool), u = List.ofFn r ++ v ∧ v.length = L :=
  ⟨BitString.ofList k u, u.drop k, by
    rw [BitString.ofFn_ofList_eq_take, List.take_append_of_le_length (by omega),
      List.take_append_drop], by simp [hu]⟩

/-- Copy `i` of a transcript of `repeatShape t (pre ++ [(v, n)])` is copy `i` of its part for
`pre` followed by block `i` of its last move. -/
theorem copyTranscript_append_ofFn (t : ℕ) {pre : List (AMMove × ℕ)} {u : List Bool}
    (hu : u.length = AMGame.transcriptLength (AMGame.repeatShape t pre)) (b : AMMove) (n : ℕ)
    (i : Fin t) (r : BitString (t * n)) :
    AMGame.copyTranscript t i (pre ++ [(b, n)]) (u ++ List.ofFn r) =
      AMGame.copyTranscript t i pre u ++ List.ofFn (BitString.block r i) := by
  induction pre generalizing u with
  | nil =>
    rw [List.length_eq_zero_iff.1 hu, List.nil_append, List.nil_append]
    have h := AMGame.copyTranscript_ofFn_append i b [] r []
    rw [List.append_nil] at h
    rw [h]
    simp [AMGame.copyTranscript]
  | cons x pre ih =>
    obtain ⟨b', n'⟩ := x
    have hu' : u.length = t * n' + AMGame.transcriptLength (AMGame.repeatShape t pre) := hu
    obtain ⟨r', v, rfl, hv⟩ := exists_eq_ofFn_append hu'
    rw [List.cons_append, List.append_assoc, AMGame.copyTranscript_ofFn_append,
      AMGame.copyTranscript_ofFn_append, ih hv, List.append_assoc]

theorem repeatMsg_append_cons (t : ℕ) (pre g : List (IPMove × ℕ)) (v : IPMove) (n : ℕ)
    (msg : ℕ → ℕ → List Bool → List Bool) (p : List Bool) :
    repeatMsg t (pre ++ (v, n) :: g) msg pre.length p = (List.range t).flatMap fun i =>
      List.ofFn (BitString.ofList n
        (msg i pre.length (AMGame.copyTranscript t i (toAM pre) p))) := by
  unfold repeatMsg
  rw [moveLength_append_cons]
  simp only [List.take_left']

/-- **The repeated verifier agrees with a transcript exactly when every copy agrees with its
part.** Here `pre` are the moves already made, with transcript `p`. -/
theorem agrees_repeatMsg (t : ℕ) (msg : ℕ → ℕ → List Bool → List Bool)
    (g pre : List (IPMove × ℕ)) (p w : List Bool)
    (hp : p.length = transcriptLength (repeatShape t pre))
    (hw : w.length = transcriptLength (repeatShape t g)) :
    agrees (repeatMsg t (pre ++ g) msg) (repeatShape t g) pre.length p w = true ↔
      ∀ i : Fin t, agrees (msg i) g pre.length (AMGame.copyTranscript t i (toAM pre) p)
        (AMGame.copyTranscript t i (toAM g) w) = true := by
  induction g generalizing pre p w with
  | nil => simp [agrees]
  | cons x g ih =>
    obtain ⟨v, n⟩ := x
    have hw' : w.length = t * n + transcriptLength (repeatShape t g) := hw
    obtain ⟨r, w', rfl, hw''⟩ := exists_eq_ofFn_append hw'
    have hp' : (p ++ List.ofFn r).length = transcriptLength (repeatShape t (pre ++ [(v, n)])) := by
      simp [hp, transcriptLength, repeatShape]
    have ih' := ih (pre ++ [(v, n)]) (p ++ List.ofFn r) w' hp' hw''
    rw [List.append_assoc, List.singleton_append, List.length_append, List.length_singleton]
      at ih'
    have hcopy : (p.length = AMGame.transcriptLength (AMGame.repeatShape t (toAM pre))) := by
      rw [← toAM_repeatShape, transcriptLength_toAM, hp]
    cases v
    · rw [repeatShape_cons', agrees_verifier_ofFn, repeatMsg_append_cons, Bool.and_eq_true,
        decide_eq_true_eq, eq_ofList_flatMap_iff, ih']
      simp only [toAM_append, toAM_cons, toAM_nil, IPMove.toAM, copyTranscript_append_ofFn t hcopy,
        AMGame.copyTranscript_ofFn_append, agrees_verifier_ofFn, Bool.and_eq_true,
        decide_eq_true_eq, ← forall_and]
    · rw [repeatShape_cons', agrees_prover_ofFn, ih']
      simp only [toAM_append, toAM_cons, toAM_nil, IPMove.toAM, copyTranscript_append_ofFn t hcopy,
        AMGame.copyTranscript_ofFn_append, agrees_prover_ofFn]

/-- **Coins of the repeated verifier.** Copy `i` reads block `i` of the coins. On a transcript of
the repetition, the coins accepted by the repeated verifier are counted by the product over the
copies of the coins accepted on each copy's part. -/
theorem acceptedCoins_repeat (t ρ : ℕ) (msg : List Bool → ℕ → List Bool → List Bool)
    (dec : List Bool → List Bool → Bool) (g : List (IPMove × ℕ)) (w : List Bool)
    (hw : w.length = transcriptLength (repeatShape t g)) :
    acceptedCoins (ρ := t * ρ)
        (fun c => repeatMsg t g fun i => msg (BitString.listRow ρ i (List.ofFn c)))
        (fun c => repeatDec t g fun i => dec (BitString.listRow ρ i (List.ofFn c)))
        (repeatShape t g) w =
      ∏ i : Fin t, acceptedCoins (ρ := ρ) (fun c => msg (List.ofFn c)) (fun c => dec (List.ofFn c))
        g (AMGame.copyTranscript t i (toAM g) w) := by
  unfold acceptedCoins
  have key (c : BitString (t * ρ)) :
      ((agrees (repeatMsg t g fun i => msg (BitString.listRow ρ i (List.ofFn c)))
          (repeatShape t g) 0 [] w &&
        repeatDec t g (fun i => dec (BitString.listRow ρ i (List.ofFn c))) w) = true) ↔
      ∀ i : Fin t, (agrees (msg (List.ofFn (BitString.block c i))) g 0 []
          (AMGame.copyTranscript t i (toAM g) w) &&
        dec (List.ofFn (BitString.block c i)) (AMGame.copyTranscript t i (toAM g) w)) = true := by
    have h := agrees_repeatMsg t (fun i => msg (BitString.listRow ρ i (List.ofFn c))) g [] []
      w rfl hw
    simp only [List.nil_append, List.length_nil, toAM_nil] at h
    simp only [Bool.and_eq_true, h, repeatDec_eq_true_iff, BitString.listRow_eq_ofFn,
      BitString.ofList_ofFn, ← forall_and]
    rfl
  simp only [key]
  rw [← Fintype.card_piFinset]
  refine card_equiv BitString.blocksEquiv fun c => ?_
  simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, BitString.blocksEquiv_apply]

/-- **Parallel repetition of private-coin games is multiplicative.** Against an optimal prover,
the `t`-fold parallel repetition of a verifier with `ρ` coins, which accepts when all copies
accept, accepts `bestCount ^ t` of its `t * ρ` coin strings. -/
theorem bestCount_repeat (t ρ : ℕ) (msg : List Bool → ℕ → List Bool → List Bool)
    (dec : List Bool → List Bool → Bool) (g : List (IPMove × ℕ)) :
    bestCount (ρ := t * ρ)
        (fun c => repeatMsg t g fun i => msg (BitString.listRow ρ i (List.ofFn c)))
        (fun c => repeatDec t g fun i => dec (BitString.listRow ρ i (List.ofFn c)))
        (repeatShape t g) =
      bestCount (ρ := ρ) (fun c => msg (List.ofFn c)) (fun c => dec (List.ofFn c)) g ^ t := by
  unfold bestCount
  rw [count_congr_of_length _ fun w hw => acceptedCoins_repeat t ρ msg dec g w hw,
    count_repeatShape_prod, prod_const, card_univ, Fintype.card_fin]

/-- The count of a verifier that reads its coins as a list does not depend on how the number of
coins is written. -/
theorem bestCount_ofFn_congr {K K' : ℕ} (hK : K = K') (msg : List Bool → ℕ → List Bool → List Bool)
    (dec : List Bool → List Bool → Bool) (g : List (IPMove × ℕ)) :
    bestCount (ρ := K) (fun c => msg (List.ofFn c)) (fun c => dec (List.ofFn c)) g =
      bestCount (ρ := K') (fun c => msg (List.ofFn c)) (fun c => dec (List.ofFn c)) g := by
  subst hK
  rfl

/-! ### Polynomial time -/

theorem toAM_evalShape (G : List (IPMove × Polynomial ℕ)) (n : ℕ) :
    toAM (evalShape G n) = AMGame.evalShape (G.map fun x => (x.1.toAM, x.2)) n := by
  simp [toAM, evalShape, AMGame.evalShape]

theorem computableInPolyTime_moveLength {γ : Type} {encIn : γ ↪ List Bool}
    (G : List (IPMove × Polynomial ℕ)) {len j : γ → ℕ}
    (hlen : ComputableInPolyTime len encIn encUnary) (hj : ComputableInPolyTime j encIn encUnary) :
    ComputableInPolyTime (fun x => moveLength (evalShape G (len x)) (j x)) encIn encUnary := by
  induction G generalizing j with
  | nil =>
    exact (ComputableInPolyTime.const (encOut := encUnary) 0).of_enc_eq fun x => by
      simp [moveLength, evalShape]
  | cons y G ih =>
    have h := ComputableInPolyTime.ite' (ComputableInPolyTime.unary_beq' hj
      (ComputableInPolyTime.const 0)) ((ComputableInPolyTime.unary_eval y.2).comp hlen)
      (ih (ComputableInPolyTime.unary_sub' hj (ComputableInPolyTime.const 1)))
    refine h.of_enc_eq fun x => congrArg _ ?_
    rcases j x with _ | k <;> simp [moveLength, evalShape]

theorem computableInPolyTime_copyTranscript_take {γ : Type} {encIn : γ ↪ List Bool}
    (G : List (IPMove × Polynomial ℕ)) {len m i j : γ → ℕ} {w : γ → List Bool}
    (hlen : ComputableInPolyTime len encIn encUnary) (hm : ComputableInPolyTime m encIn encUnary)
    (hi : ComputableInPolyTime i encIn encUnary) (hj : ComputableInPolyTime j encIn encUnary)
    (hw : ComputableInPolyTime w encIn encBits) :
    ComputableInPolyTime (fun x => AMGame.copyTranscript (m x) (i x)
      (toAM ((evalShape G (len x)).take (j x))) (w x)) encIn encBits := by
  induction G generalizing j w with
  | nil =>
    exact (ComputableInPolyTime.const (encOut := encBits) []).of_enc_eq fun x => by
      simp [evalShape, AMGame.copyTranscript]
  | cons y G ih =>
    have hn : ComputableInPolyTime (fun x => y.2.eval (len x)) encIn encUnary :=
      (ComputableInPolyTime.unary_eval y.2).comp hlen
    have h := ComputableInPolyTime.ite' (ComputableInPolyTime.unary_beq' hj
      (ComputableInPolyTime.const 0)) (ComputableInPolyTime.const [])
      (ComputableInPolyTime.bitsAppend (.bitsRowWithInput hn hi hw)
        (ih (ComputableInPolyTime.unary_sub' hj (ComputableInPolyTime.const 1))
          (.bitsDropWithInput hw (ComputableInPolyTime.unary_mul.comp (hm.prod hn)))))
    refine h.of_enc_eq fun x => congrArg _ ?_
    rcases j x with _ | k <;> simp [evalShape, toAM, AMGame.copyTranscript]

end IPGame

open IPGame

/-- The messages of `T(n)` parallel copies of a private-coin game verifier `msg` with shape `G`
and `ρ(n)` coins: copy `i` uses row `i` of the coins. -/
def IPGame.repeatVerifierMsg (enc : α ↪ List Bool) (G : List (IPMove × Polynomial ℕ))
    (T ρ : Polynomial ℕ) (msg : α × List Bool × ℕ × List Bool → List Bool)
    (x : α × List Bool × ℕ × List Bool) : List Bool :=
  repeatMsg (T.eval (enc x.1).length) (evalShape G (enc x.1).length)
    (fun i j p => msg (x.1, BitString.listRow (ρ.eval (enc x.1).length) i x.2.1, j, p)) x.2.2.1
    x.2.2.2

/-- The decision of `T(n)` parallel copies of a private-coin game verifier `dec` with shape `G`
and `ρ(n)` coins: all copies accept. -/
def IPGame.repeatVerifierDec (enc : α ↪ List Bool) (G : List (IPMove × Polynomial ℕ))
    (T ρ : Polynomial ℕ) (dec : α × List Bool × List Bool → Bool)
    (x : α × List Bool × List Bool) : Bool :=
  repeatDec (T.eval (enc x.1).length) (evalShape G (enc x.1).length)
    (fun i t => dec (x.1, BitString.listRow (ρ.eval (enc x.1).length) i x.2.1, t)) x.2.2

theorem IPGame.computableInPolyTime_repeatVerifierMsg {enc : α ↪ List Bool}
    (G : List (IPMove × Polynomial ℕ)) (T ρ : Polynomial ℕ)
    {msg : α × List Bool × ℕ × List Bool → List Bool}
    (hmsg : ComputableInPolyTime msg (encMsgInput enc) encBits) :
    ComputableInPolyTime (repeatVerifierMsg enc G T ρ msg) (encMsgInput enc) encBits := by
  set E := encMsgInput enc
  have hn : ComputableInPolyTime (fun x : α × List Bool × ℕ × List Bool => (enc x.1).length) E
      encUnary := (ComputableInPolyTime.encoding_length enc).comp (.fst _ _)
  have ht := (ComputableInPolyTime.unary_eval T).comp hn
  have hρ := (ComputableInPolyTime.unary_eval ρ).comp hn
  have hc : ComputableInPolyTime (fun x : α × List Bool × ℕ × List Bool => x.2.1) E encBits :=
    (ComputableInPolyTime.fst _ _).comp (.snd _ _)
  have hj : ComputableInPolyTime (fun x : α × List Bool × ℕ × List Bool => x.2.2.1) E encUnary :=
    ((ComputableInPolyTime.fst _ _).comp (.snd _ _)).comp (.snd _ _)
  have hp : ComputableInPolyTime (fun x : α × List Bool × ℕ × List Bool => x.2.2.2) E encBits :=
    ((ComputableInPolyTime.snd _ _).comp (.snd _ _)).comp (.snd _ _)
  have hx1 : ComputableInPolyTime (fun y : (α × List Bool × ℕ × List Bool) × ℕ => y.1) (encPair E
      encUnary) E := .fst _ _
  have hi : ComputableInPolyTime (fun y : (α × List Bool × ℕ × List Bool) × ℕ => y.2) (encPair E
      encUnary) encUnary := .snd _ _
  have hlen := computableInPolyTime_moveLength G (hn.comp hx1) (hj.comp hx1)
  have hcopy := computableInPolyTime_copyTranscript_take G (hn.comp hx1) (ht.comp hx1) hi
    (hj.comp hx1) (hp.comp hx1)
  have hrow := ComputableInPolyTime.bitsRowWithInput (hρ.comp hx1) hi (hc.comp hx1)
  have hm := hmsg.comp (((ComputableInPolyTime.fst _ _).comp hx1).prod
    (hrow.prod ((hj.comp hx1).prod hcopy)))
  have hblock := ComputableInPolyTime.bitsRowWithInput hlen (ComputableInPolyTime.const 0) hm
  refine (ComputableInPolyTime.flatMapToBitsWithInput (f := fun (x : α × List Bool × ℕ × List Bool)
      (i : ℕ) =>
    BitString.listRow (moveLength (evalShape G (enc x.1).length) x.2.2.1) 0
      (msg (x.1, BitString.listRow (ρ.eval (enc x.1).length) i x.2.1, x.2.2.1,
        AMGame.copyTranscript (T.eval (enc x.1).length) i
          (toAM ((evalShape G (enc x.1).length).take x.2.2.1)) x.2.2.2)))
    (ComputableInPolyTime.range.comp ht) hblock).of_enc_eq fun x => congrArg _ ?_
  simp only [repeatVerifierMsg, repeatMsg, BitString.listRow_zero]
  rfl

theorem IPGame.computableInPolyTime_repeatVerifierDec {enc : α ↪ List Bool}
    (G : List (IPMove × Polynomial ℕ)) (T ρ : Polynomial ℕ)
    {dec : α × List Bool × List Bool → Bool}
    (hdec : ComputableInPolyTime dec (encDecInput enc) encBool) :
    ComputableInPolyTime (repeatVerifierDec enc G T ρ dec) (encDecInput enc) encBool := by
  set E := encDecInput enc
  have hn : ComputableInPolyTime (fun x : α × List Bool × List Bool => (enc x.1).length) E
      encUnary := (ComputableInPolyTime.encoding_length enc).comp (.fst _ _)
  have ht := (ComputableInPolyTime.unary_eval T).comp hn
  have hρ := (ComputableInPolyTime.unary_eval ρ).comp hn
  have hc : ComputableInPolyTime (fun x : α × List Bool × List Bool => x.2.1) E encBits :=
    (ComputableInPolyTime.fst _ _).comp (.snd _ _)
  have hw : ComputableInPolyTime (fun x : α × List Bool × List Bool => x.2.2) E encBits :=
    (ComputableInPolyTime.snd _ _).comp (.snd _ _)
  have hx1 : ComputableInPolyTime (fun y : (α × List Bool × List Bool) × ℕ => y.1) (encPair E
      encUnary) E := .fst _ _
  have hi : ComputableInPolyTime (fun y : (α × List Bool × List Bool) × ℕ => y.2) (encPair E
      encUnary) encUnary := .snd _ _
  have hcopy := AMGame.computableInPolyTime_copyTranscript (G.map fun x => (x.1.toAM, x.2))
    (hn.comp hx1) (ht.comp hx1) hi (hw.comp hx1)
  have hrow := ComputableInPolyTime.bitsRowWithInput (hρ.comp hx1) hi (hc.comp hx1)
  have hd := hdec.comp (((ComputableInPolyTime.fst _ _).comp hx1).prod (hrow.prod hcopy))
  refine (ComputableInPolyTime.allWithInput
    (test := fun (x : α × List Bool × List Bool) (i : ℕ) =>
    dec (x.1, BitString.listRow (ρ.eval (enc x.1).length) i x.2.1,
      AMGame.copyTranscript (T.eval (enc x.1).length) i
        (AMGame.evalShape (G.map fun x => (x.1.toAM, x.2)) (enc x.1).length) x.2.2))
    (ComputableInPolyTime.range.comp ht) hd).of_enc_eq fun x => congrArg _ ?_
  simp only [repeatVerifierDec, repeatDec, toAM_evalShape]
  rfl

/-- The shape of `T(n)` parallel copies: every move is `T(n)` times longer. -/
noncomputable def IPGame.repeatShapePoly (T : Polynomial ℕ) (G : List (IPMove × Polynomial ℕ)) :
    List (IPMove × Polynomial ℕ) :=
  G.map fun x => (x.1, T * x.2)

theorem IPGame.evalShape_repeatShapePoly (T : Polynomial ℕ) (G : List (IPMove × Polynomial ℕ))
    (n : ℕ) : evalShape (repeatShapePoly T G) n = repeatShape (T.eval n) (evalShape G n) := by
  simp [evalShape, repeatShapePoly, repeatShape]

/-- **Parallel repetition of a private-coin game verifier.** Against an optimal prover, `T(n)`
parallel copies that accept when all copies accept are accepted on `countAt ^ T(n)` of their coin
strings. -/
theorem IPGame.countAt_repeat (enc : α ↪ List Bool) (G : List (IPMove × Polynomial ℕ))
    (T ρ : Polynomial ℕ) (msg : α × List Bool × ℕ × List Bool → List Bool)
    (dec : α × List Bool × List Bool → Bool) (a : α) :
    countAt enc (repeatShapePoly T G) (T * ρ) (repeatVerifierMsg enc G T ρ msg)
        (repeatVerifierDec enc G T ρ dec) a =
      countAt enc G ρ msg dec a ^ T.eval (enc a).length := by
  unfold countAt
  rw [evalShape_repeatShapePoly]
  refine (bestCount_ofFn_congr (Polynomial.eval_mul ..)
    (fun l j p => repeatVerifierMsg enc G T ρ msg (a, l, j, p))
    (fun l t => repeatVerifierDec enc G T ρ dec (a, l, t)) _).trans ?_
  exact bestCount_repeat (T.eval (enc a).length) (ρ.eval (enc a).length)
    (fun c j p => msg (a, c, j, p)) (fun c t => dec (a, c, t)) (evalShape G (enc a).length)

/-- **Gap amplification for private-coin games.** A problem with a private-coin game verifier of
pattern `π` has, for every polynomial `T`, a polynomial-time verifier of the same pattern whose
yes/no gap is `2 ^ T(n)`: on a member an optimal prover is accepted on at least a `(2 / 3) ^ T(n)`
fraction of the coin strings, and on a non-member every prover on at most a `(1 / 3) ^ T(n)`
fraction. The verifier runs `T(n)` parallel copies and accepts when all copies accept. -/
theorem IPGameClass.exists_repeat {enc : α ↪ List Bool} {π : List IPMove} {A : Set α}
    (hA : A ∈ IPGameClass enc π) (T : Polynomial ℕ) :
    ∃ (G : List (IPMove × Polynomial ℕ)) (ρ : Polynomial ℕ)
      (msg : α × List Bool × ℕ × List Bool → List Bool) (dec : α × List Bool × List Bool → Bool),
      G.map Prod.fst = π ∧
        ComputableInPolyTime msg (encMsgInput enc) encBits ∧
        ComputableInPolyTime dec (encDecInput enc) encBool ∧
        ∀ a, (a ∈ A → 2 ^ T.eval (enc a).length * 2 ^ ρ.eval (enc a).length ≤
            3 ^ T.eval (enc a).length * countAt enc G ρ msg dec a) ∧
          (a ∉ A → 3 ^ T.eval (enc a).length * countAt enc G ρ msg dec a ≤
            2 ^ ρ.eval (enc a).length) := by
  obtain ⟨G, ρ, msg, dec, hG, hmsg, hdec, hV⟩ := hA
  refine ⟨repeatShapePoly T G, T * ρ, repeatVerifierMsg enc G T ρ msg,
    repeatVerifierDec enc G T ρ dec, by simp [repeatShapePoly, ← hG],
    computableInPolyTime_repeatVerifierMsg G T ρ hmsg,
    computableInPolyTime_repeatVerifierDec G T ρ hdec, fun a => ?_⟩
  rw [countAt_repeat, Polynomial.eval_mul, pow_mul']
  obtain ⟨h1, h2⟩ := hV a
  refine ⟨fun ha => ?_, fun ha => ?_⟩
  · calc 2 ^ T.eval (enc a).length * (2 ^ ρ.eval (enc a).length) ^ T.eval (enc a).length
        = (2 * 2 ^ ρ.eval (enc a).length) ^ T.eval (enc a).length := by rw [mul_pow]
      _ ≤ (3 * countAt enc G ρ msg dec a) ^ T.eval (enc a).length := Nat.pow_le_pow_left (h1 ha) _
      _ = _ := by rw [mul_pow]
  · calc 3 ^ T.eval (enc a).length * countAt enc G ρ msg dec a ^ T.eval (enc a).length
        = (3 * countAt enc G ρ msg dec a) ^ T.eval (enc a).length := by rw [mul_pow]
      _ ≤ _ := Nat.pow_le_pow_left (h2 ha) _

end Cslib.Complexity
