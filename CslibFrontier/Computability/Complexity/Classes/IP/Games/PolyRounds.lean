/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.Games.PolyRounds
public import CslibFrontier.Computability.Complexity.Classes.IP.Games.GoldwasserSipser

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Probabilistic.AffineHash
import CslibFrontier.Foundations.Data.BitString.List
import CslibFrontier.Tactic.EncLen

/-!
# Private-coin games with polynomially many rounds and `IP[k(n)] ⊆ AM[k(n) + 2]`

Private-coin interactive games (`Cslib.Complexity.IPPolyGameClass`, `Cslib.Complexity.IPPolyRounds`)
whose move patterns, move lengths, and coin counts vary polynomially with the input length
`n = (enc a).length`, computed in polynomial time from `n` in unary. Every fixed-pattern class
`IPGameClass enc π` embeds into `IPPolyGameClass enc (fun _ => π)` and `IP[k]` embeds into
`IPPolyRounds enc (fun _ => k)`.

The main theorem is Goldwasser–Sipser [GoldwasserSipser1986] for polynomially many rounds
(`Cslib.Complexity.IPPolyRounds_subset_AMPolyRounds`): `IP[k(n)] ⊆ AM[k(n) + 2]`, without relying
on round collapse (`AMk_eq_AM`, which is unavailable when `k(n)` grows with `n`).

**Source mapping to [GoldwasserSipser1986] (paraphrase):**
* In §3, printed p. 63, a round is a pair of messages, one from each participant. The full proof
  in §4.2, printed p. 65, uses `g(n) = Q(n) / 2` such pairs. We follow that proof's total-message
  convention: its `Q(n)` is Lean's `k(n)` individual moves, and `q(n)` oracle query/reply exchanges
  give `Q(n) = k(n) = 2 * q(n)`. The last paragraph of §3 instead bounds messages sent by the
  verifier; that convention is not used to identify `Q` here. The theorem/proof is in §4.2,
  printed pp. 64–67.
* On members, some prover achieves acceptance at least `2/3`; on nonmembers, every prover's
  acceptance is at most `1/3`. Uniformity means polynomial-time shape and coin-count maps from
  unary input length
  (`encUnary` to `encIPShape` and `encUnary`, respectively), together with polynomial-time
  message and decision maps in their displayed encodings.
* The parallel repetition count `R(n) = 72 * c(n) * W(n)` and its arithmetic are original to this
  implementation. They beat the `μ ^ c(n)` soundness factor of `Emulation.three_mul_value_le_one`
  uniformly in `n` (`Cslib.Complexity.Emulation.six_mul_pow_mul_two_pow_le_three_pow`).

Proof sketch:
1. When `k(n)` is odd, the prover never sees the trailing verifier move, so folding that move into
   the verifier's final decision preserves `IPGame.bestCount`
   (`Cslib.Complexity.IPGame.bestCount_append_verifier`) and reduces the pattern to even length.
2. Emulating the even-length game appended with a final coin-revealing verifier move and merging
   adjacent Merlin moves (`Cslib.Complexity.AMGame.mergeMerlin`), plus a dummy zero-bit Arthur
   move in the odd case, gives `alternatingMoves .arthur (k(n) + 2)` directly.
3. Dynamic `agrees`, `repeatMsg`, `repeatDec`, `Emulation.check`, and `revealPayoff` run in
   polynomial time via `foldlWith_spec`.

## Main definitions

* `Cslib.Complexity.encIPMove`, `Cslib.Complexity.encIPShape`: encodings of `IPMove` and
  private-coin game shapes.
* `Cslib.Complexity.IsIPPolyGameVerifier`, `Cslib.Complexity.IPPolyGameClass`,
  `Cslib.Complexity.IPPolyRounds`: private-coin game verifiers with input-length-dependent shapes.

## Main results

* `Cslib.Complexity.IPGame.bestCount_append_verifier`,
  `Cslib.Complexity.IPk_two_mul_add_one_eq`: dropping a trailing verifier move preserves counts.
* `Cslib.Complexity.IPPolyRounds_subset_AMPolyRounds`: `IP[k(n)] ⊆ AM[k(n) + 2]`.
* `Cslib.Complexity.AMPolyGameClass_subset_IPPolyGameClass`,
  `Cslib.Complexity.AMPolyRounds_subset_IPPolyRounds`: public coins embed into private coins.

## References

* [S. Goldwasser, M. Sipser, *Private coins versus public coins in interactive proof
  systems*][GoldwasserSipser1986]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, web draft of January
  2007][AroraBarak07] (locators unverified)
-/

public section

namespace Cslib.Complexity

open Finset Turing.MultiTapeTM BitString.LinearHash

variable {α : Type}

/-- Boolean tag of a private-coin move: `false` for verifier, `true` for prover. -/
@[expose] def IPMove.toBool : IPMove → Bool
  | .verifier => false
  | .prover => true

/-- `IPMove.toBool` is injective. -/
theorem IPMove.toBool_injective : Function.Injective IPMove.toBool := by
  intro x y h
  cases x <;> cases y <;> simp_all [IPMove.toBool]

/-- Binary encoding of a private-coin move (`[false]` for verifier, `[true]` for prover). -/
@[expose] def encIPMove : IPMove ↪ List Bool :=
  ⟨fun m => encBool m.toBool, fun _ _ h => IPMove.toBool_injective (encBool.injective h)⟩

/-- Binary encoding of a private-coin game shape as a framed list of `(move, unary length)`
pairs. -/
abbrev encIPShape : List (IPMove × ℕ) ↪ List Bool :=
  encList (encPair encIPMove encUnary)

private theorem computableInPolyTime_ipMoveCases {γ β : Type} {encIn : γ ↪ List Bool}
    {encOut : β ↪ List Bool} {m : γ → IPMove} {f : γ → IPMove → β}
    (hm : ComputableInPolyTime m encIn encIPMove)
    (hv : ComputableInPolyTime (fun x => f x .verifier) encIn encOut)
    (hp : ComputableInPolyTime (fun x => f x .prover) encIn encOut) :
    ComputableInPolyTime (fun x => f x (m x)) encIn encOut := by
  have hbool : ComputableInPolyTime (fun x => (m x).toBool) encIn encBool :=
    hm.of_enc_eq fun _ => rfl
  exact (hbool.ite hp hv).of_enc_eq fun x => by cases m x <;> rfl

private theorem computableInPolyTime_amMoveCases {γ β : Type} {encIn : γ ↪ List Bool}
    {encOut : β ↪ List Bool} {m : γ → AMMove} {f : γ → AMMove → β}
    (hm : ComputableInPolyTime m encIn encAMMove)
    (ha : ComputableInPolyTime (fun x => f x .arthur) encIn encOut)
    (hmer : ComputableInPolyTime (fun x => f x .merlin) encIn encOut) :
    ComputableInPolyTime (fun x => f x (m x)) encIn encOut := by
  have hbool : ComputableInPolyTime (fun x => (m x).toBool) encIn encBool :=
    hm.of_enc_eq fun _ => rfl
  exact (hbool.ite hmer ha).of_enc_eq fun x => by cases m x <;> rfl

private theorem computableInPolyTime_unaryOdd :
    ComputableInPolyTime (fun n : ℕ => decide (n % 2 = 1)) encUnary encBool := by
  have hstep : ComputableTidilyInPolyTime (fun p : Bool × Bool => !p.1)
      (encPair encBool encBool) encBool := by fun_prop
  have hf := ComputableTidilyInPolyTime.foldl_of_bounded_growth (encA := encBool)
    (encL := encBits) (encB := encBool)
    (list := encUnary) (init := fun _ => false) (step := fun acc _ => !acc)
    (ComputableTidilyInPolyTime.encoded (ComputableTidilyInPolyTime.id' (encIn := encUnary)))
    (ComputableTidilyInPolyTime.const false) hstep (growth := 1) (fun _ _ => by simp)
  refine (ComputableInPolyTime.of_tidy hf).of_enc_eq fun n => congrArg encBool ?_
  have hacc : ∀ k (b : Bool), (List.replicate k true).foldl (fun acc _ => !acc) b =
      (if k % 2 = 1 then !b else b) := by
    intro k
    induction k with
    | zero => intro b; simp
    | succ k ih =>
      intro b
      rw [List.replicate_succ, List.foldl_cons, ih]
      cases b <;> split_ifs <;> simp <;> omega
  simpa [encUnary_apply] using (hacc n false).symm

private theorem computableInPolyTime_listAppend {α γ : Type}
    {encA : α ↪ List Bool} {encIn : γ ↪ List Bool} {left right : γ → List α}
    (hleft : ComputableInPolyTime left encIn (encList encA))
    (hright : ComputableInPolyTime right encIn (encList encA)) :
    ComputableInPolyTime (fun x => left x ++ right x) encIn (encList encA) :=
  .of_tidy (ComputableTidilyInPolyTime.listAppend' hleft.tidy hright.tidy)

private theorem computableInPolyTime_listReverseWithInput {α γ : Type}
    {encA : α ↪ List Bool} {encIn : γ ↪ List Bool} {list : γ → List α}
    (hlist : ComputableInPolyTime list encIn (encList encA)) :
    ComputableInPolyTime (fun x => (list x).reverse) encIn (encList encA) :=
  .of_tidy (ComputableTidilyInPolyTime.listReverseWithInput hlist.tidy)

private theorem list_getLastD_eq_getD {α : Type} (l : List α) (d : α) :
    l.getLastD d = l.getD (l.length - 1) d := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?]
  rfl

namespace IPGame

/-- Total transcript length is at most the encoded length of a private-coin game shape. -/
theorem transcriptLength_le_length_encIPShape (g : List (IPMove × ℕ)) :
    transcriptLength g ≤ (encIPShape g).length := by
  induction g with
  | nil => simp [transcriptLength]
  | cons x g ih =>
    obtain ⟨m, n⟩ := x
    enc_len [transcriptLength, List.map_cons, List.sum_cons, encIPShape] at ih ⊢

/-- Evaluating a fixed polynomial private-coin shape `G` at unary `n` is polynomial-time. -/
theorem computableInPolyTime_evalShape (G : List (IPMove × Polynomial ℕ)) :
    ComputableInPolyTime (evalShape G) encUnary encIPShape := by
  induction G with
  | nil => exact ComputableInPolyTime.const []
  | cons x G ih =>
    obtain ⟨m, p⟩ := x
    have hlen : ComputableInPolyTime (fun n => p.eval n) encUnary encUnary :=
      ComputableInPolyTime.unary_eval p
    have hpair : ComputableInPolyTime (fun n => (m, p.eval n)) encUnary
        (encPair encIPMove encUnary) :=
      (ComputableInPolyTime.const m).prod hlen
    exact (hpair.cons' ih).of_enc_eq fun n => by simp [evalShape]

/-- `toAM` on a polynomial-time shape is polynomial-time. -/
theorem computableInPolyTime_toAM_dyn {γ : Type} {encIn : γ ↪ List Bool}
    {g : γ → List (IPMove × ℕ)} (hg : ComputableInPolyTime g encIn encIPShape) :
    ComputableInPolyTime (fun x => toAM (g x)) encIn encAMShape := by
  let encStep : (γ × (IPMove × ℕ)) ↪ List Bool :=
    encPair encIn (encPair encIPMove encUnary)
  have hmap : ComputableInPolyTime (fun x : γ × (IPMove × ℕ) => (x.2.1.toAM, x.2.2))
      encStep (encPair encAMMove encUnary) := by
    have h1 : ComputableInPolyTime (fun x : γ × (IPMove × ℕ) => x.2.1.toAM)
        encStep encAMMove :=
      ((ComputableInPolyTime.fst encIPMove encUnary).comp
        (.snd encIn (encPair encIPMove encUnary))).of_enc_eq fun x => by
        dsimp only [Function.comp_apply]
        cases x.2.1 <;> rfl
    exact h1.prod ((ComputableInPolyTime.snd encIPMove encUnary).comp
      (.snd encIn (encPair encIPMove encUnary)))
  exact (ComputableInPolyTime.mapWithInput hg hmap).of_enc_eq fun _ => rfl

/-- `transcriptLength` on a polynomial-time private-coin shape is polynomial-time. -/
theorem computableInPolyTime_transcriptLength_dyn {γ : Type} {encIn : γ ↪ List Bool}
    {g : γ → List (IPMove × ℕ)} (hg : ComputableInPolyTime g encIn encIPShape) :
    ComputableInPolyTime (fun x => transcriptLength (g x)) encIn encUnary := by
  obtain ⟨c, d, hlen⟩ := hg.polyBounded_length.exists_le
  have hstep : ComputableInPolyTime (fun p : (Bool × ℕ) × (IPMove × ℕ) => p.1.2 + p.2.2)
      (encFoldStep encBool encUnary (encPair encIPMove encUnary)) encUnary := by
    fun_prop
  have hspec := ComputableInPolyTime.foldlWith_spec
    (encP := encBool) (encB := encUnary) (encA := encPair encIPMove encUnary) (encL := encIPShape)
    (par := fun _ => false) (list := g) (init := fun _ => 0)
    (step := fun _ s x => s + x.2)
    (ComputableInPolyTime.const false) hg (ComputableInPolyTime.const 0) hstep
    (fun _ pre s => s = transcriptLength pre) (fun _ => rfl)
    (fun _ pre s val _ hs => by
      simp only [hs, transcriptLength, List.map_append, List.map_cons, List.map_nil,
        List.sum_append, List.sum_cons, List.sum_nil, add_zero])
    (size := fun x => c * ((encIn x).length + 1) ^ d)
    (PolyBounded.of_forall_le _ _ fun _ => le_rfl)
    (fun x pre s hpre hs => by
      obtain ⟨sfx, hsfx⟩ := hpre
      have hsub : transcriptLength pre ≤ transcriptLength (g x) := by
        rw [← hsfx]
        simp only [transcriptLength, List.map_append, List.sum_append]
        exact Nat.le_add_right _ _
      simpa only [hs, encUnary_apply, List.length_replicate] using
        (hsub.trans (transcriptLength_le_length_encIPShape (g x))).trans (hlen x))
  refine hspec.1.of_enc_eq fun x => congrArg encUnary ?_
  have hfold : ∀ (l : List (IPMove × ℕ)) (s : ℕ),
      l.foldl (fun s x => s + x.2) s = s + transcriptLength l := by
    intro l
    induction l with
    | nil => intro s; simp [transcriptLength]
    | cons a l ih =>
      intro s
      simp only [List.foldl_cons, ih, transcriptLength, List.map_cons, List.sum_cons]
      omega
  simpa using (hfold (g x) 0).symm

/-- `verifierMoves` on a polynomial-time private-coin shape is polynomial-time. -/
theorem computableInPolyTime_verifierMoves_dyn {γ : Type} {encIn : γ ↪ List Bool}
    {g : γ → List (IPMove × ℕ)} (hg : ComputableInPolyTime g encIn encIPShape) :
    ComputableInPolyTime (fun x => verifierMoves (g x)) encIn encUnary := by
  obtain ⟨c, d, hlen⟩ := hg.polyBounded_length.exists_le
  have hstep : ComputableInPolyTime
      (fun p : (Bool × ℕ) × (IPMove × ℕ) => p.1.2 + if p.2.1 = .verifier then 1 else 0)
      (encFoldStep encBool encUnary (encPair encIPMove encUnary)) encUnary := by
    refine ComputableInPolyTime.unary_add' ((ComputableInPolyTime.snd _ _).comp (.fst _ _)) ?_
    have hmbool : ComputableInPolyTime (fun p : (Bool × ℕ) × (IPMove × ℕ) => p.2.1.toBool)
        (encFoldStep encBool encUnary (encPair encIPMove encUnary)) encBool :=
      ((ComputableInPolyTime.fst encIPMove encUnary).comp (.snd _ _)).of_enc_eq fun _ => rfl
    exact (hmbool.ite (ComputableInPolyTime.const 0) (ComputableInPolyTime.const 1)).of_enc_eq
      fun p => by cases p.2.1 <;> rfl
  have hspec := ComputableInPolyTime.foldlWith_spec
    (encP := encBool) (encB := encUnary) (encA := encPair encIPMove encUnary) (encL := encIPShape)
    (par := fun _ => false) (list := g) (init := fun _ => 0)
    (step := fun _ s x => s + if x.1 = .verifier then 1 else 0)
    (ComputableInPolyTime.const false) hg (ComputableInPolyTime.const 0) hstep
    (fun _ pre s => s ≤ pre.length) (fun _ => le_rfl)
    (fun _ pre s val _ hs => by
      simp only [List.length_append, List.length_singleton]
      split_ifs <;> omega)
    (size := fun x => c * ((encIn x).length + 1) ^ d)
    (PolyBounded.of_forall_le _ _ fun _ => le_rfl)
    (fun x pre s hpre hs => by
      have hsub : pre.length ≤ (g x).length := hpre.length_le
      have hl : (g x).length ≤ (encIPShape (g x)).length :=
        SizedListEncoding.length_le (encA := encPair encIPMove encUnary) (encL := encIPShape) _
      simpa only [encUnary_apply, List.length_replicate] using
        (hs.trans (hsub.trans hl)).trans (hlen x))
  refine hspec.1.of_enc_eq fun x => congrArg encUnary ?_
  have hfold : ∀ (l : List (IPMove × ℕ)) (s : ℕ),
      l.foldl (fun s x => s + if x.1 = .verifier then 1 else 0) s = s + verifierMoves l := by
    intro l
    induction l with
    | nil => intro s; simp [verifierMoves]
    | cons a l ih =>
      intro s
      obtain ⟨_ | _, _⟩ := a
      · simp [List.foldl_cons, ih, verifierMoves]; omega
      · simp [List.foldl_cons, ih, verifierMoves]
  simpa using (hfold (g x) 0).symm

/-- `moveLength` on a polynomial-time private-coin shape is polynomial-time. -/
theorem computableInPolyTime_moveLength_dyn {γ : Type} {encIn : γ ↪ List Bool}
    {g : γ → List (IPMove × ℕ)} {j : γ → ℕ}
    (hg : ComputableInPolyTime g encIn encIPShape)
    (hj : ComputableInPolyTime j encIn encUnary) :
    ComputableInPolyTime (fun x => moveLength (g x) (j x)) encIn encUnary := by
  have hget := ComputableInPolyTime.listGetDWithInput hg hj (IPMove.prover, 0)
  have hsnd : ComputableInPolyTime (fun p : IPMove × ℕ => p.2)
      (encPair encIPMove encUnary) encUnary := ComputableInPolyTime.snd _ _
  refine (hsnd.comp hget).of_enc_eq fun x => congrArg encUnary ?_
  simp only [Function.comp_apply, moveLength, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases (g x)[j x]? <;> simp

/-! ### Dropping a trailing verifier move -/

/-- `agrees` splits cleanly across concatenated shapes when the prefix transcript matches the
prefix shape length. -/
theorem agrees_append (msg : ℕ → List Bool → List Bool) (g h : List (IPMove × ℕ))
    (j : ℕ) (p t u : List Bool) (ht : t.length = transcriptLength g) :
    agrees msg (g ++ h) j p (t ++ u) =
      (agrees msg g j p t && agrees msg h (j + g.length) (p ++ t) u) := by
  induction g generalizing j p t with
  | nil =>
    obtain rfl : t = [] := List.eq_nil_of_length_eq_zero (by simpa [transcriptLength] using ht)
    simp [agrees]
  | cons x g ih =>
    obtain ⟨v, n⟩ := x
    simp only [transcriptLength, List.map_cons, List.sum_cons] at ht
    have htake : (t ++ u).take n = t.take n := List.take_append_of_le_length (by omega)
    have hdrop : (t ++ u).drop n = t.drop n ++ u := List.drop_append_of_le_length (by omega)
    have hsub : (t.drop n).length = transcriptLength g := by
      simp [List.length_drop, transcriptLength, ht]
    have htd : t.take n ++ t.drop n = t := List.take_append_drop n t
    have ih' := ih (j + 1) (p ++ t.take n) (t.drop n) hsub
    rw [show j + 1 + g.length = j + (g.length + 1) by omega,
      List.append_assoc, htd] at ih'
    cases v <;> simp only [List.cons_append, agrees, htake, hdrop, ih', List.length_cons,
      Bool.and_assoc]

/-- Dropping a trailing verifier move by folding its message directly into the verifier's final
decision preserves `bestCount`. -/
theorem bestCount_append_verifier {ρ : ℕ} (msg : BitString ρ → ℕ → List Bool → List Bool)
    (dec : BitString ρ → List Bool → Bool) (g : List (IPMove × ℕ)) (L : ℕ) :
    bestCount msg dec (g ++ [(.verifier, L)]) =
      bestCount msg
        (fun c t => dec c (t ++ List.ofFn (BitString.ofList L (msg c g.length t)))) g := by
  unfold bestCount
  rw [count_append]
  refine count_congr_of_length g fun t ht => ?_
  rw [count_verifier]
  simp only [count_nil, acceptedCoins]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun c : BitString ρ =>
      BitString.ofList L (msg c g.length t)) (t := univ) fun _ _ => mem_univ _]
  refine sum_congr rfl fun m _ => ?_
  rw [Finset.filter_filter]
  congr 1
  ext c
  have hag := agrees_append (msg c) g [(.verifier, L)] 0 [] t (List.ofFn m) ht
  have hm_len : (List.ofFn m).length ≤ L := by simp
  simp only [List.nil_append, zero_add, agrees, List.take_of_length_le hm_len,
    Bool.and_true, List.ofFn_inj, eq_comm (a := m)] at hag
  simp only [List.append_nil, mem_filter, mem_univ, true_and, Bool.and_eq_true,
    decide_eq_true_eq, hag]
  constructor
  · rintro ⟨⟨hg, hm⟩, hd⟩
    refine ⟨⟨hg, ?_⟩, hm⟩
    rwa [← hm] at hd
  · rintro ⟨⟨hg, hd⟩, hm⟩
    refine ⟨⟨hg, hm⟩, ?_⟩
    rwa [hm] at hd

/-! ### Dynamic polynomial-time `agrees`, `repeatMsg`, and `repeatDec` -/

/-- State for folding `agrees` across the transcript. -/
private structure AgreesState where
  /-- Current message index. -/
  j : ℕ
  /-- Accumulated transcript prefix. -/
  p : List Bool
  /-- Remaining transcript suffix. -/
  t : List Bool
  /-- Whether all messages agree so far. -/
  ok : Bool
  deriving Repr, DecidableEq

/-- Encoding for `AgreesState`. -/
private enc_structure encAgreesState : AgreesState where
  j : encUnary, p : encBits, t : encBits, ok : encBool

private def agreesStep (msg : α × List Bool × ℕ × List Bool → List Bool)
    (par : α × List Bool) (st : AgreesState) (x : IPMove × ℕ) : AgreesState :=
  let {j, p, t, ok} := st
  let ok' := ok && match x.1 with
    | .verifier => decide (t.take x.2 = BitString.listRow x.2 0 (msg (par.1, par.2, j, p)))
    | .prover => true
  { j := j + 1, p := p ++ t.take x.2, t := t.drop x.2, ok := ok' }

private theorem foldl_agreesStep (msg : α × List Bool × ℕ × List Bool → List Bool)
    (a : α) (c : List Bool) (g : List (IPMove × ℕ)) (j : ℕ) (p t : List Bool) (ok : Bool) :
    (g.foldl (agreesStep msg (a, c)) { j := j, p := p, t := t, ok := ok }).ok =
      (ok && agrees (fun j' p' => msg (a, c, j', p')) g j p t) := by
  induction g generalizing j p t ok with
  | nil => simp [agrees]
  | cons x g ih =>
    obtain ⟨_ | _, n⟩ := x
    · simp only [List.foldl_cons, agreesStep, ih, agrees, BitString.listRow_zero, Bool.and_assoc]
    · simp only [List.foldl_cons, agreesStep, ih, agrees, Bool.and_true]

/-- `agrees` on a dynamic polynomial-time shape `g` is polynomial-time. -/
theorem computableInPolyTime_agrees_dyn {γ : Type} {enc : α ↪ List Bool} {encIn : γ ↪ List Bool}
    {a : γ → α} {c : γ → List Bool} {g : γ → List (IPMove × ℕ)} {j₀ : γ → ℕ}
    {p₀ t₀ : γ → List Bool}
    {msg : α × List Bool × ℕ × List Bool → List Bool}
    (ha : ComputableInPolyTime a encIn enc)
    (hc : ComputableInPolyTime c encIn encBits)
    (hg : ComputableInPolyTime g encIn encIPShape)
    (hj₀ : ComputableInPolyTime j₀ encIn encUnary)
    (hp₀ : ComputableInPolyTime p₀ encIn encBits)
    (ht₀ : ComputableInPolyTime t₀ encIn encBits)
    (hmsg : ComputableInPolyTime msg (encMsgInput enc) encBits) :
    ComputableInPolyTime
      (fun x => agrees (fun j p => msg (a x, c x, j, p)) (g x) (j₀ x) (p₀ x) (t₀ x))
      encIn encBool := by
  let encAg : (((α × List Bool) × AgreesState) × (IPMove × ℕ)) ↪ List Bool :=
    encFoldStep (encPair enc encBits)
      encAgreesState
      (encPair encIPMove encUnary)
  have hstep : ComputableInPolyTime
      (fun q : ((α × List Bool) × AgreesState) × (IPMove × ℕ) =>
        agreesStep msg q.1.1 q.1.2 q.2)
      encAg
      encAgreesState := by
    unfold agreesStep
    have ha' : ComputableInPolyTime
        (fun q : ((α × List Bool) × AgreesState) × (IPMove × ℕ) => q.1.1.1) encAg enc := by
      fun_prop
    have hc' : ComputableInPolyTime
        (fun q : ((α × List Bool) × AgreesState) × (IPMove × ℕ) => q.1.1.2) encAg encBits := by
      fun_prop
    have hj' : ComputableInPolyTime
        (fun q : ((α × List Bool) × AgreesState) × (IPMove × ℕ) => q.1.2.j) encAg encUnary := by
      fun_prop
    have hp' : ComputableInPolyTime
        (fun q : ((α × List Bool) × AgreesState) × (IPMove × ℕ) => q.1.2.p) encAg encBits := by
      fun_prop
    have ht' : ComputableInPolyTime
        (fun q : ((α × List Bool) × AgreesState) × (IPMove × ℕ) => q.1.2.t)
        encAg encBits := by
      fun_prop
    have hok' : ComputableInPolyTime
        (fun q : ((α × List Bool) × AgreesState) × (IPMove × ℕ) => q.1.2.ok)
        encAg encBool := by
      fun_prop
    have hm' : ComputableInPolyTime
        (fun q : ((α × List Bool) × AgreesState) × (IPMove × ℕ) => q.2.1) encAg encIPMove := by
      fun_prop
    have hn' : ComputableInPolyTime
        (fun q : ((α × List Bool) × AgreesState) × (IPMove × ℕ) => q.2.2) encAg encUnary := by
      fun_prop
    have hmsg' : ComputableInPolyTime
        (fun q : ((α × List Bool) × AgreesState) × (IPMove × ℕ) =>
          msg (q.1.1.1, q.1.1.2, q.1.2.j, q.1.2.p)) encAg encBits :=
      hmsg.comp (ha'.prod (hc'.prod (hj'.prod hp')))
    have htake : ComputableInPolyTime
        (fun q : ((α × List Bool) × AgreesState) × (IPMove × ℕ) => q.1.2.t.take q.2.2)
        encAg encBits :=
      ComputableInPolyTime.bitsTakeWithInput ht' hn'
    have hrow : ComputableInPolyTime
        (fun q : ((α × List Bool) × AgreesState) × (IPMove × ℕ) =>
          BitString.listRow q.2.2 0 (msg (q.1.1.1, q.1.1.2, q.1.2.j, q.1.2.p)))
        encAg encBits :=
      ComputableInPolyTime.bitsRowWithInput hn' (ComputableInPolyTime.const 0) hmsg'
    have hcheck : ComputableInPolyTime
        (fun q : ((α × List Bool) × AgreesState) × (IPMove × ℕ) =>
          match q.2.1 with
          | .verifier =>
            decide (q.1.2.t.take q.2.2 =
              BitString.listRow q.2.2 0 (msg (q.1.1.1, q.1.1.2, q.1.2.j, q.1.2.p)))
          | .prover => true)
        encAg encBool :=
      computableInPolyTime_ipMoveCases
        (f := fun q m => match m with
          | .verifier =>
            decide (q.1.2.t.take q.2.2 =
              BitString.listRow q.2.2 0 (msg (q.1.1.1, q.1.1.2, q.1.2.j, q.1.2.p)))
          | .prover => true)
        hm' (ComputableInPolyTime.decide_eq' htake hrow) (ComputableInPolyTime.const true)
    have hokNext := ComputableInPolyTime.bool_and' hok' hcheck
    have hdrop := ComputableInPolyTime.bitsDropWithInput ht' hn'
    have hpNext := ComputableInPolyTime.bitsAppend hp' htake
    have hjNext := ComputableInPolyTime.unary_add' hj' (ComputableInPolyTime.const 1)
    exact (encAgreesState_mk_polyTime hjNext hpNext hdrop hokNext).of_enc_eq fun q => rfl
  obtain ⟨c₁, d₁, hjlen⟩ := hj₀.polyBounded_length.exists_le
  obtain ⟨c₂, d₂, hglen⟩ := hg.polyBounded_length.exists_le
  obtain ⟨c₃, d₃, hplen⟩ := (show PolyBounded (fun x => (encIn x).length) (fun x => (p₀ x).length)
    from by simpa only [encBits_apply] using hp₀.polyBounded_length).exists_le
  obtain ⟨c₄, d₄, htlen⟩ := (show PolyBounded (fun x => (encIn x).length) (fun x => (t₀ x).length)
    from by simpa only [encBits_apply] using ht₀.polyBounded_length).exists_le
  set D := max (max d₁ d₂) (max d₃ d₄)
  have hspec := ComputableInPolyTime.foldlWith_spec
    (encP := encPair enc encBits)
    (encB := encAgreesState)
    (encA := encPair encIPMove encUnary) (encL := encIPShape)
    (par := fun x => (a x, c x)) (list := g)
    (init := fun x => { j := j₀ x, p := p₀ x, t := t₀ x, ok := true }) (step := agreesStep msg)
    (ha.prod hc) hg (hj₀.prod (hp₀.prod (ht₀.prod (ComputableInPolyTime.const true)))) hstep
    (fun x pre st => st.j = j₀ x + pre.length ∧
      st.p.length + st.t.length ≤ (p₀ x).length + (t₀ x).length)
    (fun x => ⟨rfl, le_rfl⟩)
    (fun x pre st val _ hst => by
      rcases st with ⟨j, p, t, ok⟩
      obtain ⟨hj', hlen'⟩ := hst
      simp only [agreesStep, List.length_append, List.length_singleton, List.length_take,
        List.length_drop] at hj' hlen' ⊢
      exact ⟨by omega, by omega⟩)
    (size := fun x => (2 * (c₁ + c₂) + 4 * (c₃ + c₄) + 6) * ((encIn x).length + 1) ^ D)
    (PolyBounded.of_forall_le _ _ fun _ => le_rfl)
    (fun x pre st hpre hst => by
      have hpfx : pre.length ≤ (g x).length := hpre.length_le
      have hgl : (g x).length ≤ (encIPShape (g x)).length :=
        SizedListEncoding.length_le (encA := encPair encIPMove encUnary) (encL := encIPShape) _
      have hm1 : ((encIn x).length + 1) ^ d₁ ≤ ((encIn x).length + 1) ^ D :=
        Nat.pow_le_pow_right (Nat.succ_pos _) ((le_max_left _ _).trans (le_max_left _ _))
      have hm2 : ((encIn x).length + 1) ^ d₂ ≤ ((encIn x).length + 1) ^ D :=
        Nat.pow_le_pow_right (Nat.succ_pos _) ((le_max_right _ _).trans (le_max_left _ _))
      have hm3 : ((encIn x).length + 1) ^ d₃ ≤ ((encIn x).length + 1) ^ D :=
        Nat.pow_le_pow_right (Nat.succ_pos _) ((le_max_left _ _).trans (le_max_right _ _))
      have hm4 : ((encIn x).length + 1) ^ d₄ ≤ ((encIn x).length + 1) ^ D :=
        Nat.pow_le_pow_right (Nat.succ_pos _) ((le_max_right _ _).trans (le_max_right _ _))
      have hpow : 1 ≤ ((encIn x).length + 1) ^ D := Nat.one_le_pow _ _ (Nat.succ_pos _)
      have h1 : j₀ x ≤ c₁ * ((encIn x).length + 1) ^ D := by
        have := (show j₀ x ≤ c₁ * ((encIn x).length + 1) ^ d₁ from by
          simpa only [encUnary_apply, List.length_replicate] using hjlen x)
        exact this.trans (Nat.mul_le_mul_left _ hm1)
      have h2 : (g x).length ≤ c₂ * ((encIn x).length + 1) ^ D :=
        (hgl.trans (hglen x)).trans (Nat.mul_le_mul_left _ hm2)
      have h3 : (p₀ x).length ≤ c₃ * ((encIn x).length + 1) ^ D :=
        (hplen x).trans (Nat.mul_le_mul_left _ hm3)
      have h4 : (t₀ x).length ≤ c₄ * ((encIn x).length + 1) ^ D :=
        (htlen x).trans (Nat.mul_le_mul_left _ hm4)
      simp only [encAgreesState_apply, length_encPair, encUnary_apply,
        List.length_replicate, encBits_apply, encBool_apply, List.length_singleton]
      nlinarith [hst.1, hst.2])
  have hout : ComputableInPolyTime
      (fun x => ((g x).foldl (agreesStep msg (a x, c x))
        { j := j₀ x, p := p₀ x, t := t₀ x, ok := true }).ok)
      encIn encBool :=
    (by fun_prop : ComputableInPolyTime (fun st : AgreesState => st.ok)
        encAgreesState encBool).comp hspec.1
  exact hout.of_enc_eq fun x => by
    simp only [foldl_agreesStep, Bool.true_and]

/-- `repeatShape` for a dynamic shape and repetition count is polynomial-time. -/
theorem computableInPolyTime_repeatShape_dyn {γ : Type} {encIn : γ ↪ List Bool}
    {t : γ → ℕ} {g : γ → List (IPMove × ℕ)}
    (ht : ComputableInPolyTime t encIn encUnary)
    (hg : ComputableInPolyTime g encIn encIPShape) :
    ComputableInPolyTime (fun x => repeatShape (t x) (g x)) encIn encIPShape := by
  let encStep : (γ × (IPMove × ℕ)) ↪ List Bool :=
    encPair encIn (encPair encIPMove encUnary)
  have hf : ComputableInPolyTime (fun p : γ × (IPMove × ℕ) => (p.2.1, t p.1 * p.2.2))
      encStep (encPair encIPMove encUnary) := by
    have ht' : ComputableInPolyTime (fun p : γ × (IPMove × ℕ) => t p.1) encStep encUnary :=
      ht.comp (.fst encIn (encPair encIPMove encUnary))
    have hm' : ComputableInPolyTime (fun p : γ × (IPMove × ℕ) => p.2.1) encStep encIPMove :=
      (ComputableInPolyTime.fst encIPMove encUnary).comp (.snd encIn (encPair encIPMove encUnary))
    have hn' : ComputableInPolyTime (fun p : γ × (IPMove × ℕ) => p.2.2) encStep encUnary :=
      (ComputableInPolyTime.snd encIPMove encUnary).comp (.snd encIn (encPair encIPMove encUnary))
    exact hm'.prod (ComputableInPolyTime.unary_mul' ht' hn')
  exact (ComputableInPolyTime.mapWithInput hg hf).of_enc_eq fun _ => rfl

/-- `repeatMsg` on dynamic `T`, `ρ`, and shape `g` is polynomial-time. -/
theorem computableInPolyTime_repeatMsg_dyn {γ : Type} {enc : α ↪ List Bool} {encIn : γ ↪ List Bool}
    {a : γ → α} {c : γ → List Bool} {g : γ → List (IPMove × ℕ)} {T ρ j : γ → ℕ}
    {p : γ → List Bool} {msg : α × List Bool × ℕ × List Bool → List Bool}
    (ha : ComputableInPolyTime a encIn enc)
    (hc : ComputableInPolyTime c encIn encBits)
    (hg : ComputableInPolyTime g encIn encIPShape)
    (hT : ComputableInPolyTime T encIn encUnary)
    (hρ : ComputableInPolyTime ρ encIn encUnary)
    (hj : ComputableInPolyTime j encIn encUnary)
    (hp : ComputableInPolyTime p encIn encBits)
    (hmsg : ComputableInPolyTime msg (encMsgInput enc) encBits) :
    ComputableInPolyTime
      (fun x => repeatMsg (T x) (g x)
        (fun i => fun j' p' => msg (a x, BitString.listRow (ρ x) i (c x), j', p'))
        (j x) (p x))
      encIn encBits := by
  have hx1 : ComputableInPolyTime (fun y : γ × ℕ => y.1) (encPair encIn encUnary) encIn :=
    .fst _ _
  have hi : ComputableInPolyTime (fun y : γ × ℕ => y.2) (encPair encIn encUnary) encUnary :=
    .snd _ _
  have hlen := computableInPolyTime_moveLength_dyn (hg.comp hx1) (hj.comp hx1)
  have htake : ComputableInPolyTime (fun y : γ × ℕ => toAM ((g y.1).take (j y.1)))
      (encPair encIn encUnary) encAMShape :=
    computableInPolyTime_toAM_dyn
      (.of_tidy (ComputableTidilyInPolyTime.listTakeWithInput (hg.comp hx1).tidy
        (hj.comp hx1).tidy))
  have hcopy := AMGame.computableInPolyTime_copyTranscript_dyn
    (hT.comp hx1) hi htake (hp.comp hx1)
  have hrow := ComputableInPolyTime.bitsRowWithInput (hρ.comp hx1) hi (hc.comp hx1)
  have hm := hmsg.comp ((ha.comp hx1).prod (hrow.prod ((hj.comp hx1).prod hcopy)))
  have hblock := ComputableInPolyTime.bitsRowWithInput hlen (ComputableInPolyTime.const 0) hm
  refine (ComputableInPolyTime.flatMapToBitsWithInput
    (f := fun x i => BitString.listRow (moveLength (g x) (j x)) 0
      (msg (a x, BitString.listRow (ρ x) i (c x), j x,
        AMGame.copyTranscript (T x) i (toAM ((g x).take (j x))) (p x))))
    (ComputableInPolyTime.range.comp hT) hblock).of_enc_eq fun x => congrArg _ ?_
  simp only [repeatMsg, BitString.listRow_zero]
  rfl

/-- `repeatDec` on dynamic `T`, `ρ`, and shape `g` is polynomial-time. -/
theorem computableInPolyTime_repeatDec_dyn {γ : Type} {enc : α ↪ List Bool} {encIn : γ ↪ List Bool}
    {a : γ → α} {c : γ → List Bool} {g : γ → List (IPMove × ℕ)} {T ρ : γ → ℕ}
    {w : γ → List Bool} {dec : α × List Bool × List Bool → Bool}
    (ha : ComputableInPolyTime a encIn enc)
    (hc : ComputableInPolyTime c encIn encBits)
    (hg : ComputableInPolyTime g encIn encIPShape)
    (hT : ComputableInPolyTime T encIn encUnary)
    (hρ : ComputableInPolyTime ρ encIn encUnary)
    (hw : ComputableInPolyTime w encIn encBits)
    (hdec : ComputableInPolyTime dec (encDecInput enc) encBool) :
    ComputableInPolyTime
      (fun x => repeatDec (T x) (g x)
        (fun i t => dec (a x, BitString.listRow (ρ x) i (c x), t)) (w x))
      encIn encBool := by
  have hx1 : ComputableInPolyTime (fun y : γ × ℕ => y.1) (encPair encIn encUnary) encIn :=
    .fst _ _
  have hi : ComputableInPolyTime (fun y : γ × ℕ => y.2) (encPair encIn encUnary) encUnary :=
    .snd _ _
  have hcopy := AMGame.computableInPolyTime_copyTranscript_dyn
    (hT.comp hx1) hi (computableInPolyTime_toAM_dyn (hg.comp hx1)) (hw.comp hx1)
  have hrow := ComputableInPolyTime.bitsRowWithInput (hρ.comp hx1) hi (hc.comp hx1)
  have hd := hdec.comp ((ha.comp hx1).prod (hrow.prod hcopy))
  refine (ComputableInPolyTime.allWithInput
    (test := fun x i =>
      dec (a x, BitString.listRow (ρ x) i (c x),
        AMGame.copyTranscript (T x) i (toAM (g x)) (w x)))
    (ComputableInPolyTime.range.comp hT) hd).of_enc_eq fun x => congrArg _ ?_
  rfl

end IPGame

namespace Emulation

open IPGame

/-- `Emulation.shape B Z` for dynamic `B`, `Z`, and `g` is polynomial-time. -/
theorem computableInPolyTime_shape_dyn {γ : Type} {encIn : γ ↪ List Bool}
    {B Z : γ → ℕ} {g : γ → List (IPMove × ℕ)}
    (hB : ComputableInPolyTime B encIn encUnary)
    (hZ : ComputableInPolyTime Z encIn encUnary)
    (hg : ComputableInPolyTime g encIn encIPShape) :
    ComputableInPolyTime (fun x => shape (B x) (Z x) (g x)) encIn encAMShape := by
  let encStep : (γ × (IPMove × ℕ)) ↪ List Bool :=
    encPair encIn (encPair encIPMove encUnary)
  have hf : ComputableInPolyTime
      (fun p : γ × (IPMove × ℕ) => match p.2.1 with
        | .verifier => [(.arthur, B p.1 * (p.2.2 + Z p.1) + B p.1),
            (.merlin, B p.1 + (p.2.2 + Z p.1))]
        | .prover => [(.merlin, p.2.2)])
      encStep encAMShape := by
    have hm : ComputableInPolyTime (fun p : γ × (IPMove × ℕ) => p.2.1) encStep encIPMove :=
      (ComputableInPolyTime.fst encIPMove encUnary).comp
        (.snd encIn (encPair encIPMove encUnary))
    have hBx : ComputableInPolyTime (fun p : γ × (IPMove × ℕ) => B p.1) encStep encUnary :=
      hB.comp (.fst encIn (encPair encIPMove encUnary))
    have hZx : ComputableInPolyTime (fun p : γ × (IPMove × ℕ) => Z p.1) encStep encUnary :=
      hZ.comp (.fst encIn (encPair encIPMove encUnary))
    have hnx : ComputableInPolyTime (fun p : γ × (IPMove × ℕ) => p.2.2) encStep encUnary :=
      (ComputableInPolyTime.snd encIPMove encUnary).comp
        (.snd encIn (encPair encIPMove encUnary))
    have hvBranch : ComputableInPolyTime
        (fun p : γ × (IPMove × ℕ) =>
          [(.arthur, B p.1 * (p.2.2 + Z p.1) + B p.1), (.merlin, B p.1 + (p.2.2 + Z p.1))])
        encStep encAMShape := by
      have hnZ := ComputableInPolyTime.unary_add' hnx hZx
      have hA := ComputableInPolyTime.unary_add'
        (ComputableInPolyTime.unary_mul' hBx hnZ) hBx
      have hM := ComputableInPolyTime.unary_add' hBx hnZ
      have eA : ComputableInPolyTime
          (fun p : γ × (IPMove × ℕ) => (AMMove.arthur, B p.1 * (p.2.2 + Z p.1) + B p.1))
          encStep (encPair encAMMove encUnary) :=
        (ComputableInPolyTime.const (encOut := encAMMove) AMMove.arthur).prod hA
      have eM : ComputableInPolyTime
          (fun p : γ × (IPMove × ℕ) => (AMMove.merlin, B p.1 + (p.2.2 + Z p.1)))
          encStep (encPair encAMMove encUnary) :=
        (ComputableInPolyTime.const (encOut := encAMMove) AMMove.merlin).prod hM
      exact (eA.cons' (eM.cons' (ComputableInPolyTime.const []))).of_enc_eq fun _ => rfl
    have hpBranch : ComputableInPolyTime
        (fun p : γ × (IPMove × ℕ) => [(AMMove.merlin, p.2.2)]) encStep encAMShape := by
      have eM : ComputableInPolyTime (fun p : γ × (IPMove × ℕ) => (AMMove.merlin, p.2.2))
          encStep (encPair encAMMove encUnary) :=
        (ComputableInPolyTime.const (encOut := encAMMove) AMMove.merlin).prod hnx
      exact (eM.cons' (ComputableInPolyTime.const [])).of_enc_eq fun _ => rfl
    exact computableInPolyTime_ipMoveCases (encOut := encAMShape)
      (f := fun (p : γ × (IPMove × ℕ)) (m : IPMove) => match m with
        | .verifier => [(AMMove.arthur, B p.1 * (p.2.2 + Z p.1) + B p.1),
            (AMMove.merlin, B p.1 + (p.2.2 + Z p.1))]
        | .prover => [(AMMove.merlin, p.2.2)])
      hm hvBranch hpBranch
  let stepFn : γ → (IPMove × ℕ) → List (AMMove × ℕ) := fun x y => match y.1 with
    | .verifier => [(.arthur, B x * (y.2 + Z x) + B x), (.merlin, B x + (y.2 + Z x))]
    | .prover => [(.merlin, y.2)]
  refine (ComputableInPolyTime.flatMapWithInput (f := stepFn) hg hf).of_enc_eq
    fun x => congrArg encAMShape ?_
  induction g x with
  | nil => rfl
  | cons y ys ih =>
    obtain ⟨_ | _, n⟩ := y <;> simp [shape, stepFn, ih]

/-- State for folding `check` across the transcript. -/
private structure CheckState where
  /-- Current logarithmic size claim. -/
  κ : ℕ
  /-- Decoded private-game transcript prefix. -/
  p : List Bool
  /-- Remaining emulation transcript. -/
  w : List Bool
  /-- Whether all checks pass so far. -/
  ok : Bool
  deriving Repr, DecidableEq

/-- Encoding for `CheckState`. -/
private enc_structure encCheckState : CheckState where
  κ : encUnary, p : encBits, w : encBits, ok : encBool

private def checkStep (B Z K : ℕ) (st : CheckState) (move : IPMove × ℕ) : CheckState :=
  let {κ, p, w, ok} := st
  match move with
  | (.verifier, n) =>
    let r := w.take (B * (n + Z) + B)
    let y := w.drop (B * (n + Z) + B)
    let b := (y.take B).count true
    let x := (y.drop B).take (n + Z)
    let ok' := ok && hashZero B (n + Z) r x &&
      (!((x.drop n).take (Z + κ - (b + K))).any fun b => b)
    { κ := b, p := p ++ x.take n, w := (y.drop B).drop (n + Z), ok := ok' }
  | (.prover, n) =>
    { κ := κ, p := p ++ w.take n, w := w.drop n, ok := ok }

private theorem foldl_checkStep (B Z K : ℕ) (V : List Bool → Bool)
    (g : List (IPMove × ℕ)) (κ : ℕ) (p w : List Bool) (ok : Bool) :
    (let st := g.foldl (checkStep B Z K) { κ := κ, p := p, w := w, ok := ok };
      st.ok && decide (st.κ = 0) && V st.p) =
      (ok && check B Z K V g κ p w) := by
  induction g generalizing κ p w ok with
  | nil =>
    dsimp only [List.foldl_nil, check]
    exact Bool.and_assoc _ _ _
  | cons a g ih =>
    obtain ⟨_ | _, n⟩ := a
    · dsimp only
      rw [List.foldl_cons, checkStep, ih, check]
      simp only [Bool.and_assoc]
    · dsimp only
      rw [List.foldl_cons, checkStep, ih, check]

/-- **`Emulation.check` on a dynamic shape `g` is polynomial-time.** -/
theorem computableInPolyTime_check_dyn {γ : Type} {encIn : γ ↪ List Bool}
    {B Z K : γ → ℕ} {g : γ → List (IPMove × ℕ)} {V : γ → List Bool → Bool}
    {κ : γ → ℕ} {p w : γ → List Bool}
    (hB : ComputableInPolyTime B encIn encUnary)
    (hZ : ComputableInPolyTime Z encIn encUnary)
    (hK : ComputableInPolyTime K encIn encUnary)
    (hg : ComputableInPolyTime g encIn encIPShape)
    (hV : ∀ {q : γ → List Bool}, ComputableInPolyTime q encIn encBits →
      ComputableInPolyTime (fun x => V x (q x)) encIn encBool)
    (hκ : ComputableInPolyTime κ encIn encUnary)
    (hp : ComputableInPolyTime p encIn encBits)
    (hw : ComputableInPolyTime w encIn encBits) :
    ComputableInPolyTime
      (fun x => check (B x) (Z x) (K x) (V x) (g x) (κ x) (p x) (w x)) encIn encBool := by
  let encCh : (((ℕ × ℕ × ℕ) × CheckState) × (IPMove × ℕ)) ↪ List Bool :=
    encFoldStep (encPair encUnary (encPair encUnary encUnary))
      (encCheckState)
      (encPair encIPMove encUnary)
  let encSt : CheckState ↪ List Bool :=
    encCheckState
  have hstep : ComputableInPolyTime
      (fun q : ((ℕ × ℕ × ℕ) × CheckState) × (IPMove × ℕ) =>
        checkStep q.1.1.1 q.1.1.2.1 q.1.1.2.2 q.1.2 q.2)
      encCh encSt := by
    have hBq : ComputableInPolyTime
        (fun q : ((ℕ × ℕ × ℕ) × CheckState) × (IPMove × ℕ) => q.1.1.1) encCh encUnary := by
      fun_prop
    have hZq : ComputableInPolyTime
        (fun q : ((ℕ × ℕ × ℕ) × CheckState) × (IPMove × ℕ) => q.1.1.2.1) encCh encUnary := by
      fun_prop
    have hKq : ComputableInPolyTime
        (fun q : ((ℕ × ℕ × ℕ) × CheckState) × (IPMove × ℕ) => q.1.1.2.2) encCh encUnary := by
      fun_prop
    have hκq : ComputableInPolyTime
        (fun q : ((ℕ × ℕ × ℕ) × CheckState) × (IPMove × ℕ) => q.1.2.κ) encCh encUnary := by
      fun_prop
    have hpq : ComputableInPolyTime
        (fun q : ((ℕ × ℕ × ℕ) × CheckState) × (IPMove × ℕ) => q.1.2.p) encCh encBits := by
      fun_prop
    have hwq : ComputableInPolyTime
        (fun q : ((ℕ × ℕ × ℕ) × CheckState) × (IPMove × ℕ) => q.1.2.w) encCh encBits := by
      fun_prop
    have hokq : ComputableInPolyTime
        (fun q : ((ℕ × ℕ × ℕ) × CheckState) × (IPMove × ℕ) => q.1.2.ok) encCh encBool := by
      fun_prop
    have hmq : ComputableInPolyTime
        (fun q : ((ℕ × ℕ × ℕ) × CheckState) × (IPMove × ℕ) => q.2.1) encCh encIPMove := by
      fun_prop
    have hnq : ComputableInPolyTime
        (fun q : ((ℕ × ℕ × ℕ) × CheckState) × (IPMove × ℕ) => q.2.2) encCh encUnary := by
      fun_prop
    have hvBranch : ComputableInPolyTime
        (fun q : ((ℕ × ℕ × ℕ) × CheckState) × (IPMove × ℕ) =>
          checkStep q.1.1.1 q.1.1.2.1 q.1.1.2.2 q.1.2 (.verifier, q.2.2))
        encCh encSt := by
      have hnZ := ComputableInPolyTime.unary_add' hnq hZq
      have hP := ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_mul' hBq hnZ) hBq
      have hr := ComputableInPolyTime.bitsTakeWithInput hwq hP
      have hy := ComputableInPolyTime.bitsDropWithInput hwq hP
      have hb := ComputableInPolyTime.bitsCountWithInput
        (ComputableInPolyTime.bitsTakeWithInput hy hBq) (ComputableInPolyTime.const true)
      have hyB := ComputableInPolyTime.bitsDropWithInput hy hBq
      have hx := ComputableInPolyTime.bitsTakeWithInput hyB hnZ
      have hhash := computableInPolyTime_hashZero hBq hnZ hr hx
      have hpad := ComputableInPolyTime.bool_not.comp (ComputableInPolyTime.bitsAnyWithInput
        (test := fun _ b => b)
        (ComputableInPolyTime.bitsTakeWithInput (ComputableInPolyTime.bitsDropWithInput hx hnq)
          (ComputableInPolyTime.unary_sub' (ComputableInPolyTime.unary_add' hZq hκq)
            (ComputableInPolyTime.unary_add' hb hKq)))
        (ComputableInPolyTime.snd _ _))
      have hokNext := ComputableInPolyTime.bool_and'
        (ComputableInPolyTime.bool_and' hokq hhash) hpad
      have hpNext := ComputableInPolyTime.bitsAppend hpq
        (ComputableInPolyTime.bitsTakeWithInput hx hnq)
      have hwNext := ComputableInPolyTime.bitsDropWithInput hyB hnZ
      exact (encCheckState_mk_polyTime hb hpNext hwNext hokNext).of_enc_eq fun q => rfl
    have hpBranch : ComputableInPolyTime
        (fun q : ((ℕ × ℕ × ℕ) × CheckState) × (IPMove × ℕ) =>
          checkStep q.1.1.1 q.1.1.2.1 q.1.1.2.2 q.1.2 (.prover, q.2.2))
        encCh encSt := by
      have hpNext := ComputableInPolyTime.bitsAppend hpq
        (ComputableInPolyTime.bitsTakeWithInput hwq hnq)
      have hwNext := ComputableInPolyTime.bitsDropWithInput hwq hnq
      exact (encCheckState_mk_polyTime hκq hpNext hwNext hokq).of_enc_eq fun q => rfl
    exact computableInPolyTime_ipMoveCases
      (f := fun q m => checkStep q.1.1.1 q.1.1.2.1 q.1.1.2.2 q.1.2 (m, q.2.2))
      hmq hvBranch hpBranch
  obtain ⟨c₁, d₁, hBlen⟩ := hB.polyBounded_length.exists_le
  obtain ⟨c₂, d₂, hκlen⟩ := hκ.polyBounded_length.exists_le
  obtain ⟨c₃, d₃, hplen⟩ := (show PolyBounded (fun x => (encIn x).length) (fun x => (p x).length)
    from by simpa only [encBits_apply] using hp.polyBounded_length).exists_le
  obtain ⟨c₄, d₄, hglen⟩ := hg.polyBounded_length.exists_le
  obtain ⟨c₅, d₅, hwlen⟩ := (show PolyBounded (fun x => (encIn x).length) (fun x => (w x).length)
    from by simpa only [encBits_apply] using hw.polyBounded_length).exists_le
  set D := max (max (max d₁ d₂) (max d₃ d₄)) d₅
  have hspec := ComputableInPolyTime.foldlWith_spec
    (encP := encPair encUnary (encPair encUnary encUnary))
    (encB := encCheckState) (encA := encPair encIPMove encUnary) (encL := encIPShape)
    (par := fun x => (B x, Z x, K x)) (list := g)
    (init := fun x => { κ := κ x, p := p x, w := w x, ok := true })
    (step := fun par => checkStep par.1 par.2.1 par.2.2)
    (hB.prod (hZ.prod hK)) hg
    (by fun_prop) hstep
    (fun (x : γ) (pre : List (IPMove × ℕ)) (st : CheckState) => st.κ ≤ max (κ x) (B x) ∧
      st.p.length ≤ (p x).length + transcriptLength pre ∧ st.w.length ≤ (w x).length)
    (fun x => ⟨le_max_left _ _, by simp, le_rfl⟩)
    (fun x pre st val _ hst => by
      rcases st with ⟨κ', p', w', ok'⟩
      obtain ⟨hκ', hp', hw'⟩ := hst
      obtain ⟨_ | _, n⟩ := val
      · simp only [checkStep]
        refine ⟨?_, ?_, ?_⟩
        · exact ((List.count_le_length).trans (by simp)).trans (le_max_right _ _)
        · have htake : ((((w'.drop (B x * (n + Z x) + B x)).drop (B x)).take
              (n + Z x)).take n).length ≤ n := by
            simp only [List.length_take]
            omega
          simp only [List.length_append, transcriptLength, List.map_append,
            List.sum_append] at hp' ⊢
          simp only [List.map_cons, List.sum_cons] at hp' ⊢
          omega
        · simp only [List.length_drop] at hw' ⊢
          omega
      · simp only [checkStep]
        refine ⟨hκ', ?_, ?_⟩
        · simp only [List.length_append, List.length_take, transcriptLength,
            List.map_append, List.sum_append] at hp' ⊢
          simp only [List.map_cons, List.sum_cons] at hp' ⊢
          omega
        · simp only [List.length_drop] at hw' ⊢
          omega)
    (size := fun x =>
      (2 * (c₁ + c₂) + 2 * (c₃ + c₄ + c₅) + 8) * ((encIn x).length + 1) ^ D)
    (PolyBounded.of_forall_le _ _ fun _ => le_rfl)
    (fun x pre st hpre hst => by
      obtain ⟨sfx, hsfx⟩ := hpre
      have htr : transcriptLength pre ≤ transcriptLength (g x) := by
        rw [← hsfx]
        simp only [transcriptLength, List.map_append, List.sum_append]
        exact Nat.le_add_right _ _
      have hB1 : B x ≤ c₁ * ((encIn x).length + 1) ^ D :=
        (show B x ≤ c₁ * ((encIn x).length + 1) ^ d₁ from by
          simpa only [encUnary_apply, List.length_replicate] using hBlen x).trans
          (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos _)
            ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))))
      have hκ1 : κ x ≤ c₂ * ((encIn x).length + 1) ^ D :=
        (show κ x ≤ c₂ * ((encIn x).length + 1) ^ d₂ from by
          simpa only [encUnary_apply, List.length_replicate] using hκlen x).trans
          (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos _)
            ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))))
      have hp1 : (p x).length ≤ c₃ * ((encIn x).length + 1) ^ D :=
        (hplen x).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos _)
          ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _)))))
      have hg1 : transcriptLength (g x) ≤ c₄ * ((encIn x).length + 1) ^ D :=
        ((transcriptLength_le_length_encIPShape (g x)).trans (hglen x)).trans
          (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos _)
            ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _)))))
      have hw1 : (w x).length ≤ c₅ * ((encIn x).length + 1) ^ D :=
        (hwlen x).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos _)
          (le_max_right _ _)))
      have hpow : 1 ≤ ((encIn x).length + 1) ^ D := Nat.one_le_pow _ _ (Nat.succ_pos _)
      have hmax : st.κ ≤ (c₁ + c₂) * ((encIn x).length + 1) ^ D := by
        have := hst.1
        rcases max_choice (κ x) (B x) with h | h <;> nlinarith
      simp only [encCheckState_apply, length_encPair, encUnary_apply, List.length_replicate,
        encBits_apply, encBool_apply, List.length_singleton]
      nlinarith [hst.1, hst.2.1, hst.2.2])
  have hst := hspec.1
  have hok : ComputableInPolyTime
      (fun x => ((g x).foldl (checkStep (B x) (Z x) (K x))
        { κ := κ x, p := p x, w := w x, ok := true }).ok)
      encIn encBool :=
    (by fun_prop : ComputableInPolyTime (fun st : CheckState => st.ok)
        encCheckState encBool).comp hst
  have hfinκ : ComputableInPolyTime
      (fun x => ((g x).foldl (checkStep (B x) (Z x) (K x))
        { κ := κ x, p := p x, w := w x, ok := true }).κ)
      encIn encUnary :=
    (by fun_prop : ComputableInPolyTime (fun st : CheckState => st.κ)
        encCheckState encUnary).comp hst
  have hfinp : ComputableInPolyTime
      (fun x => ((g x).foldl (checkStep (B x) (Z x) (K x))
        { κ := κ x, p := p x, w := w x, ok := true }).p)
      encIn encBits :=
    (by fun_prop : ComputableInPolyTime (fun st : CheckState => st.p)
        encCheckState encBits).comp hst
  have hzero := ComputableInPolyTime.decide_eq' hfinκ (ComputableInPolyTime.const 0)
  have hv := hV hfinp
  exact (ComputableInPolyTime.bool_and' (ComputableInPolyTime.bool_and' hok hzero) hv).of_enc_eq
    fun x => by
      simpa only [Bool.true_and] using
        congrArg encBool (foldl_checkStep (B x) (Z x) (K x) (V x) (g x) (κ x) (p x) (w x) true).symm

/-- `revealPayoff` on a dynamic shape `g` is polynomial-time. -/
theorem computableInPolyTime_revealPayoff_dyn {γ : Type} {enc : α ↪ List Bool}
    {encIn : γ ↪ List Bool}
    {a : γ → α} {g : γ → List (IPMove × ℕ)} {L : γ → ℕ}
    {msg : α × List Bool × ℕ × List Bool → List Bool} {dec : α × List Bool × List Bool → Bool}
    {w : γ → List Bool}
    (ha : ComputableInPolyTime a encIn enc)
    (hg : ComputableInPolyTime g encIn encIPShape)
    (hL : ComputableInPolyTime L encIn encUnary)
    (hmsg : ComputableInPolyTime msg (encMsgInput enc) encBits)
    (hdec : ComputableInPolyTime dec (encDecInput enc) encBool)
    (hw : ComputableInPolyTime w encIn encBits) :
    ComputableInPolyTime
      (fun x => revealPayoff (fun c j p => msg (a x, c, j, p)) (fun c t => dec (a x, c, t))
        (g x) (L x) (w x))
      encIn encBool := by
  have hc := ComputableInPolyTime.bitsDropWithInput hw hL
  have ht := ComputableInPolyTime.bitsTakeWithInput hw hL
  have hag := IPGame.computableInPolyTime_agrees_dyn ha hc hg
    (ComputableInPolyTime.const 0) (ComputableInPolyTime.const []) ht hmsg
  have hd := hdec.comp (ha.prod (hc.prod ht))
  exact (ComputableInPolyTime.bool_and' hag hd).of_enc_eq fun _ => rfl

/-- State for folding adjacent Merlin moves in AM games. -/
private structure MergeState where
  /-- Pending accumulated Merlin length. -/
  pending : Option ℕ
  /-- Reversed compacted shape so far. -/
  history : List (AMMove × ℕ)
  deriving Repr, DecidableEq

/-- Encoding for `MergeState`. -/
private enc_structure encMergeState : MergeState where
  pending : (encOption encUnary), history : encAMShape

private def mergeStep (st : MergeState) (x : AMMove × ℕ) : MergeState :=
  match x.1 with
  | .merlin => MergeState.mk (some (st.pending.getD 0 + x.2)) st.history
  | .arthur =>
    match st.pending with
    | none => (MergeState.mk none ((.arthur, x.2) :: st.history))
    | some m => (MergeState.mk none ((.arthur, x.2) :: (.merlin, m) :: st.history))

private def mergeFlush (st : MergeState) : List (AMMove × ℕ) :=
  (match st.pending with
    | none => st.history
    | some m => (.merlin, m) :: st.history).reverse

private theorem mergeMerlin_append_arthur_cons (pref : List (AMMove × ℕ)) (n : ℕ)
    (g : List (AMMove × ℕ)) :
    AMGame.mergeMerlin (pref ++ (.arthur, n) :: g) =
      AMGame.mergeMerlin pref ++ (.arthur, n) :: AMGame.mergeMerlin g := by
  induction pref with
  | nil => rfl
  | cons x pref ih =>
    obtain ⟨_ | _, m⟩ := x
    · simp [AMGame.mergeMerlin, ih]
    · simp only [List.cons_append, AMGame.mergeMerlin, ih]
      cases h : AMGame.mergeMerlin pref with
      | nil => rfl
      | cons y tail =>
        obtain ⟨_ | _, m'⟩ := y <;> rfl

private theorem mergeMerlin_append_of_head_ne (acc : List (AMMove × ℕ))
    (hhead : acc.head?.map Prod.fst ≠ some .merlin) (u : List (AMMove × ℕ)) :
    AMGame.mergeMerlin (acc.reverse ++ u) =
      AMGame.mergeMerlin acc.reverse ++ AMGame.mergeMerlin u := by
  cases acc with
  | nil => rfl
  | cons y tail =>
    obtain ⟨_ | _, k⟩ := y
    · rw [List.reverse_cons, List.append_assoc, List.singleton_append,
        mergeMerlin_append_arthur_cons tail.reverse k u,
        mergeMerlin_append_arthur_cons tail.reverse k []]
      simp only [AMGame.mergeMerlin, List.append_assoc, List.singleton_append]
    · simp at hhead

private theorem mergeMerlin_merlin_merlin (m n : ℕ) (g : List (AMMove × ℕ)) :
    AMGame.mergeMerlin ((.merlin, m) :: (.merlin, n) :: g) =
      AMGame.mergeMerlin ((.merlin, m + n) :: g) := by
  simp only [AMGame.mergeMerlin]
  cases h : AMGame.mergeMerlin g with
  | nil => rfl
  | cons y tail =>
    obtain ⟨_ | _, k⟩ := y
    · rfl
    · simp [Nat.add_assoc]

private theorem mergeMerlin_eq_mergeFlush_aux (g acc : List (AMMove × ℕ))
    (hacc : AMGame.mergeMerlin acc.reverse = acc.reverse)
    (hhead : acc.head?.map Prod.fst ≠ some .merlin) :
    ∀ p : Option ℕ,
      AMGame.mergeMerlin (acc.reverse ++
        match p with | none => g | some m => (.merlin, m) :: g) =
      mergeFlush (g.foldl mergeStep (MergeState.mk p acc)) := by
  induction g generalizing acc with
  | nil =>
    intro p
    rcases p with _ | m
    · simp only [List.append_nil, List.foldl_nil, mergeFlush]
      exact hacc
    · simp only [List.foldl_nil, mergeFlush, List.reverse_cons]
      rw [mergeMerlin_append_of_head_ne acc hhead [(.merlin, m)], hacc]
      rfl
  | cons x g ih =>
    intro p
    obtain ⟨_ | _, n⟩ := x
    · rcases p with _ | m
      · simp only [List.foldl_cons, mergeStep]
        have hacc' : AMGame.mergeMerlin ((.arthur, n) :: acc).reverse =
            ((.arthur, n) :: acc).reverse := by
          rw [List.reverse_cons, mergeMerlin_append_of_head_ne acc hhead [(.arthur, n)], hacc]
          rfl
        simpa [List.reverse_cons, List.append_assoc] using
          ih ((.arthur, n) :: acc) hacc' (by simp) none
      · simp only [List.foldl_cons, mergeStep]
        have haccM : AMGame.mergeMerlin ((.merlin, m) :: acc).reverse =
            ((.merlin, m) :: acc).reverse := by
          rw [List.reverse_cons, mergeMerlin_append_of_head_ne acc hhead [(.merlin, m)], hacc]
          rfl
        have hacc' : AMGame.mergeMerlin ((.arthur, n) :: (.merlin, m) :: acc).reverse =
            ((.arthur, n) :: (.merlin, m) :: acc).reverse := by
          rw [List.reverse_cons, mergeMerlin_append_arthur_cons _ n [], haccM]
          rfl
        have h1 := ih ((.arthur, n) :: (.merlin, m) :: acc) hacc' (by simp) none
        have hleft : AMGame.mergeMerlin (acc.reverse ++ (.merlin, m) :: (.arthur, n) :: g) =
            AMGame.mergeMerlin (((.arthur, n) :: (.merlin, m) :: acc).reverse ++ g) :=
          calc AMGame.mergeMerlin (acc.reverse ++ (.merlin, m) :: (.arthur, n) :: g)
              = acc.reverse ++ AMGame.mergeMerlin ((.merlin, m) :: (.arthur, n) :: g) := by
                  rw [mergeMerlin_append_of_head_ne acc hhead, hacc]
            _ = acc.reverse ++ (.merlin, m) :: (.arthur, n) :: AMGame.mergeMerlin g := by
                  simp [AMGame.mergeMerlin]
            _ = (acc.reverse ++ [(.merlin, m)]) ++ (.arthur, n) :: AMGame.mergeMerlin g := by
                  simp [List.append_assoc]
            _ = AMGame.mergeMerlin (acc.reverse ++ [(.merlin, m)]) ++
                  (.arthur, n) :: AMGame.mergeMerlin g := by
                  rw [mergeMerlin_append_of_head_ne acc hhead, hacc]
                  simp [AMGame.mergeMerlin]
            _ = AMGame.mergeMerlin ((acc.reverse ++ [(.merlin, m)]) ++ (.arthur, n) :: g) :=
                  (mergeMerlin_append_arthur_cons _ n g).symm
            _ = AMGame.mergeMerlin (((.arthur, n) :: (.merlin, m) :: acc).reverse ++ g) := by
                  simp [List.reverse_cons, List.append_assoc]
        exact hleft.trans h1
    · rcases p with _ | m
      · simpa [List.foldl_cons, mergeStep, Nat.zero_add] using
          ih acc hacc hhead (some n)
      · have ih' := ih acc hacc hhead (some (m + n))
        have hmer : AMGame.mergeMerlin (acc.reverse ++ (.merlin, m) :: (.merlin, n) :: g) =
            AMGame.mergeMerlin (acc.reverse ++ (.merlin, m + n) :: g) := by
          rw [mergeMerlin_append_of_head_ne acc hhead ((.merlin, m) :: (.merlin, n) :: g),
            mergeMerlin_append_of_head_ne acc hhead ((.merlin, m + n) :: g),
            mergeMerlin_merlin_merlin]
        exact hmer.trans (by simpa [List.foldl_cons, mergeStep] using ih')

private theorem mergeMerlin_eq_mergeFlush (g : List (AMMove × ℕ)) :
    AMGame.mergeMerlin g = mergeFlush (g.foldl mergeStep (MergeState.mk none [])) :=
  mergeMerlin_eq_mergeFlush_aux g [] rfl (by simp) none

/-- `AMGame.mergeMerlin` on a polynomial-time shape is polynomial-time. -/
theorem computableInPolyTime_mergeMerlin {γ : Type} {encIn : γ ↪ List Bool}
    {g : γ → List (AMMove × ℕ)} (hg : ComputableInPolyTime g encIn encAMShape) :
    ComputableInPolyTime (fun x => AMGame.mergeMerlin (g x)) encIn encAMShape := by
  let encSt : MergeState ↪ List Bool := encMergeState
  let encMe : ((Bool × MergeState) × (AMMove × ℕ)) ↪ List Bool :=
    encFoldStep encBool encSt (encPair encAMMove encUnary)
  have hstep : ComputableInPolyTime
      (fun q : (Bool × MergeState) × (AMMove × ℕ) => mergeStep q.1.2 q.2)
      encMe encSt := by
    have hopt : ComputableInPolyTime
        (fun q : (Bool × MergeState) × (AMMove × ℕ) => q.1.2.pending)
          encMe (encOption encUnary) :=
      by
      fun_prop
    have hacc : ComputableInPolyTime
        (fun q : (Bool × MergeState) × (AMMove × ℕ) => q.1.2.history) encMe encAMShape := by
      fun_prop
    have hm : ComputableInPolyTime
        (fun q : (Bool × MergeState) × (AMMove × ℕ) => q.2.1) encMe encAMMove := by
      fun_prop
    have hn : ComputableInPolyTime
        (fun q : (Bool × MergeState) × (AMMove × ℕ) => q.2.2) encMe encUnary := by
      fun_prop
    have haBranch : ComputableInPolyTime
        (fun q : (Bool × MergeState) × (AMMove × ℕ) =>
          mergeStep q.1.2 (.arthur, q.2.2)) encMe encSt := by
      have hnone : ComputableInPolyTime
          (fun q : (Bool × MergeState) × (AMMove × ℕ) => ⟨none, (.arthur, q.2.2) :: q.1.2.history⟩)
          encMe encSt := by
        have he : ComputableInPolyTime (fun q : (Bool × MergeState) × (AMMove × ℕ) =>
            (AMMove.arthur, q.2.2)) encMe (encPair encAMMove encUnary) :=
          (ComputableInPolyTime.const (encOut := encAMMove) AMMove.arthur).prod hn
        exact (
        encMergeState_mk_polyTime (ComputableInPolyTime.const (none : Option ℕ))
            (he.cons' hacc)).of_enc_eq
          fun _ => rfl
      have hsome : ComputableInPolyTime
          (fun p : ((Bool × MergeState) × (AMMove × ℕ)) × ℕ =>
            ⟨none, (.arthur, p.1.2.2) :: (.merlin, p.2) :: p.1.1.2.history⟩)
          (encPair encMe encUnary) encSt := by
        have hq : ComputableInPolyTime
            (fun p : ((Bool × MergeState) × (AMMove × ℕ)) × ℕ => p.1.2.2)
            (encPair encMe encUnary) encUnary := by
          fun_prop
        have hm2 : ComputableInPolyTime
            (fun p : ((Bool × MergeState) × (AMMove × ℕ)) × ℕ => p.2)
            (encPair encMe encUnary) encUnary := by
          fun_prop
        have hacc2 : ComputableInPolyTime
            (fun p : ((Bool × MergeState) × (AMMove × ℕ)) × ℕ => p.1.1.2.history)
            (encPair encMe encUnary) encAMShape := by
          fun_prop
        have eA : ComputableInPolyTime
            (fun p : ((Bool × MergeState) × (AMMove × ℕ)) × ℕ => (AMMove.arthur, p.1.2.2))
            (encPair encMe encUnary) (encPair encAMMove encUnary) :=
          (ComputableInPolyTime.const (encOut := encAMMove) AMMove.arthur).prod hq
        have eM : ComputableInPolyTime
            (fun p : ((Bool × MergeState) × (AMMove × ℕ)) × ℕ => (AMMove.merlin, p.2))
            (encPair encMe encUnary) (encPair encAMMove encUnary) :=
          (ComputableInPolyTime.const (encOut := encAMMove) AMMove.merlin).prod hm2
        exact (encMergeState_mk_polyTime (ComputableInPolyTime.const (none : Option ℕ))
          (eA.cons' (eM.cons' hacc2))).of_enc_eq fun _ => rfl
      exact (ComputableInPolyTime.optionElimWithInput hopt hnone hsome).of_enc_eq fun q => by
        dsimp only [mergeStep]
        cases q.1.2.pending <;> rfl
    have hmBranch : ComputableInPolyTime
        (fun q : (Bool × MergeState) × (AMMove × ℕ) =>
          mergeStep q.1.2 (.merlin, q.2.2)) encMe encSt := by
      have hcur := ComputableInPolyTime.optionGetDWithInput hopt (ComputableInPolyTime.const 0)
      have hsum := ComputableInPolyTime.unary_add' hcur hn
      exact (encMergeState_mk_polyTime ((
        ComputableInPolyTime.optionSome encUnary).comp hsum) hacc).of_enc_eq
        fun _ => rfl
    exact (computableInPolyTime_amMoveCases
      (f := fun q m => mergeStep q.1.2 (m, q.2.2)) hm haBranch hmBranch).of_enc_eq fun q => by
      rcases q with ⟨_, ⟨_ | _, _⟩⟩ <;> rfl
  obtain ⟨c, d, hglen⟩ := hg.polyBounded_length.exists_le
  have hspec := ComputableInPolyTime.foldlWith_spec
    (encP := encBool) (encB := encSt) (encA := encPair encAMMove encUnary) (encL := encAMShape)
    (par := fun _ => false) (list := g) (init := fun _ => MergeState.mk none [])
    (step := fun _ => mergeStep) (ComputableInPolyTime.const false) hg
    (ComputableInPolyTime.const (MergeState.mk none [])) hstep
    (fun _ pre st => st.pending.getD 0 + AMGame.transcriptLength st.history ≤
        AMGame.transcriptLength pre ∧
      (st.history.length ≤ 2 * pre.length))
    (fun _ => ⟨le_rfl, le_rfl⟩)
    (fun _ pre st val _ hst => by
      rcases st with ⟨opt, acc⟩
      obtain ⟨_ | _, n⟩ := val
      · rcases opt with _ | m
        · simp only [mergeStep, Option.getD_none, zero_add, List.length_cons, List.length_append,
            AMGame.transcriptLength, List.map_cons, List.map_append,
            List.map_nil, List.sum_cons, List.sum_append, List.sum_nil, add_zero] at hst ⊢
          omega
        · simp only [mergeStep, Option.getD_none, zero_add, Option.getD_some, List.length_cons,
            List.length_append, AMGame.transcriptLength, List.map_cons,
            List.map_append, List.map_nil, List.sum_cons, List.sum_append, List.sum_nil,
            add_zero] at hst ⊢
          omega
      · rcases opt with _ | m <;>
        · simp only [mergeStep, Option.getD_none, zero_add, Option.getD_some, List.length_append,
            AMGame.transcriptLength, List.map_append, List.map_cons,
            List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at hst ⊢
          omega)
    (size := fun x => (24 * c + 12) * ((encIn x).length + 1) ^ d)
    (PolyBounded.of_forall_le _ _ fun _ => le_rfl)
    (fun x pre st hpre hst => by
      have hsubL : pre.length ≤ (g x).length := hpre.length_le
      have hsubT : AMGame.transcriptLength pre ≤ AMGame.transcriptLength (g x) := by
        obtain ⟨sfx, hsfx⟩ := hpre
        rw [← hsfx]
        simp only [AMGame.transcriptLength, List.map_append, List.sum_append]
        exact Nat.le_add_right _ _
      have hgL : (g x).length ≤ (encAMShape (g x)).length :=
        SizedListEncoding.length_le (encA := encPair encAMMove encUnary) (encL := encAMShape) _
      have hgT : AMGame.transcriptLength (g x) ≤ (encAMShape (g x)).length :=
        AMGame.transcriptLength_le_length_encAMShape (g x)
      have hSum : st.pending.getD 0 + AMGame.transcriptLength st.history ≤
        c * ((encIn x).length + 1) ^ d :=
        hst.1.trans (hsubT.trans (hgT.trans (hglen x)))
      have hLen : st.history.length ≤ 2 * (c * ((encIn x).length + 1) ^ d) :=
        hst.2.trans (Nat.mul_le_mul_left 2 ((hsubL.trans hgL).trans (hglen x)))
      have hAccLen : (encAMShape st.history).length ≤
          8 * st.history.length + 2 * AMGame.transcriptLength st.history := by
        clear hst hpre hsubL hsubT hgL hgT hSum hLen
        induction st.history with
        | nil => simp [AMGame.transcriptLength]
        | cons y ys ih =>
          obtain ⟨m, n⟩ := y
          have hm1 : (encAMMove m).length = 1 := by cases m <;> rfl
          enc_len [encAMShape, hm1, AMGame.transcriptLength, List.map_cons, List.sum_cons] at ih ⊢
      have hOptLen : (encOption encUnary st.pending).length ≤ 1 + st.pending.getD 0 := by
        cases st.pending with
        | none => simp
        | some m => simp
      have hpow : 1 ≤ ((encIn x).length + 1) ^ d := Nat.one_le_pow _ _ (Nat.succ_pos _)
      simp only [encSt, encMergeState_apply, length_encPair]
      nlinarith)
  have hst := hspec.1
  have hoptOut : ComputableInPolyTime
      (fun x => ((g x).foldl mergeStep (MergeState.mk none [])).pending)
        encIn (encOption encUnary) :=
    encMergeState_pending_polyTime hst
  have haccOut : ComputableInPolyTime
      (fun x => ((g x).foldl mergeStep (MergeState.mk none [])).history) encIn encAMShape :=
    encMergeState_history_polyTime hst
  have hpreRev : ComputableInPolyTime
      (fun x => match ((g x).foldl mergeStep (MergeState.mk none [])).pending with
        | none => ((g x).foldl mergeStep (MergeState.mk none [])).history
        | some m => (.merlin, m) :: ((g x).foldl mergeStep (MergeState.mk none [])).history)
      encIn encAMShape := by
    have eM : ComputableInPolyTime (fun p : γ × ℕ => (AMMove.merlin, p.2))
        (encPair encIn encUnary) (encPair encAMMove encUnary) :=
      (ComputableInPolyTime.const AMMove.merlin).prod (.snd _ _)
    have hcons : ComputableInPolyTime
        (fun p : γ × ℕ => (AMMove.merlin, p.2) :: ((g p.1).foldl mergeStep ⟨none, []⟩).history)
        (encPair encIn encUnary) encAMShape :=
      (eM.cons' (haccOut.comp (.fst _ _))).of_enc_eq fun _ => rfl
    exact (ComputableInPolyTime.optionElimWithInput hoptOut haccOut hcons).of_enc_eq fun x => by
      cases ((g x).foldl mergeStep (MergeState.mk none [])).pending <;> rfl
  refine (computableInPolyTime_listReverseWithInput hpreRev).of_enc_eq fun x =>
    congrArg encAMShape ?_
  simp only [mergeFlush, mergeMerlin_eq_mergeFlush (g x)]

/-- **Uniform soundness arithmetic for polynomial round counts:** for `1 ≤ c ≤ W` and
`R = 72 * c * W`, `B = R * W`, the soundness factor of `Emulation.three_mul_value_le_one` is
strictly dominated by `(3 / 2) ^ R` for all `n`. -/
theorem six_mul_pow_mul_two_pow_le_three_pow {c W : ℕ} (hc : 1 ≤ c) (hcW : c ≤ W) :
    6 * (72 * c ^ 2 * (72 * c * W * W + 1) ^ 2) ^ c * 2 ^ (72 * c * W) ≤
      3 ^ (72 * c * W) := by
  have hW1 : 1 ≤ W := hc.trans hcW
  have hWW : 1 ≤ W * W := Nat.mul_le_mul hW1 hW1
  have hpos : 1 ≤ 72 * c * W * W := by nlinarith
  have hB : 72 * c * W * W + 1 ≤ 2 * (72 * c * W * W) := by omega
  have hbase : 72 * c ^ 2 * (72 * c * W * W + 1) ^ 2 ≤ 288 * 72 ^ 2 * W ^ 8 := by
    calc 72 * c ^ 2 * (72 * c * W * W + 1) ^ 2
        ≤ 72 * W ^ 2 * (2 * (72 * W * W * W)) ^ 2 := by
          gcongr
          calc 72 * c * W * W + 1 ≤ 2 * (72 * c * W * W) := hB
            _ ≤ 2 * (72 * W * W * W) := by gcongr
      _ = 288 * 72 ^ 2 * W ^ 8 := by ring
  have hcne : c ≠ 0 := by omega
  have h6 : 6 ≤ 6 ^ c := Nat.le_self_pow hcne 6
  have hpowW : W ^ 8 ≤ 2 ^ (8 * W) := by
    have hlt : W ≤ 2 ^ W := Nat.lt_two_pow_self.le
    calc W ^ 8 ≤ (2 ^ W) ^ 8 := Nat.pow_le_pow_left hlt 8
      _ = 2 ^ (W * 8) := (pow_mul 2 W 8).symm
      _ = 2 ^ (8 * W) := by rw [Nat.mul_comm]
  have hconst : 6 * (288 * 72 ^ 2) ≤ 2 ^ 24 := by norm_num
  have hstep1 : 6 * (72 * c ^ 2 * (72 * c * W * W + 1) ^ 2) ≤ 2 ^ (40 * W) := by
    calc 6 * (72 * c ^ 2 * (72 * c * W * W + 1) ^ 2)
        ≤ 6 * (288 * 72 ^ 2 * W ^ 8) := Nat.mul_le_mul_left 6 hbase
      _ = (6 * (288 * 72 ^ 2)) * W ^ 8 := by ring
      _ ≤ 2 ^ 24 * 2 ^ (8 * W) := Nat.mul_le_mul hconst hpowW
      _ = 2 ^ (24 + 8 * W) := by rw [← pow_add]
      _ ≤ 2 ^ (40 * W) := Nat.pow_le_pow_right two_pos (by omega)
  have h3_18 : 2 ^ 28 ≤ 3 ^ 18 := by norm_num
  have hsingle : 6 * (72 * c ^ 2 * (72 * c * W * W + 1) ^ 2) * 2 ^ (72 * W) ≤ 3 ^ (72 * W) := by
    calc 6 * (72 * c ^ 2 * (72 * c * W * W + 1) ^ 2) * 2 ^ (72 * W)
        ≤ 2 ^ (40 * W) * 2 ^ (72 * W) := Nat.mul_le_mul_right _ hstep1
      _ = (2 ^ 28) ^ (4 * W) := by rw [← pow_add, ← pow_mul]; congr 1; omega
      _ ≤ (3 ^ 18) ^ (4 * W) := Nat.pow_le_pow_left h3_18 (4 * W)
      _ = 3 ^ (72 * W) := by rw [← pow_mul]; congr 1; omega
  calc 6 * (72 * c ^ 2 * (72 * c * W * W + 1) ^ 2) ^ c * 2 ^ (72 * c * W)
      ≤ 6 ^ c * (72 * c ^ 2 * (72 * c * W * W + 1) ^ 2) ^ c * 2 ^ (72 * c * W) := by gcongr
    _ = 6 ^ c * (72 * c ^ 2 * (72 * c * W * W + 1) ^ 2) ^ c * (2 ^ (72 * W)) ^ c := by
        rw [← pow_mul]; congr 2; ring
    _ = (6 * (72 * c ^ 2 * (72 * c * W * W + 1) ^ 2) * 2 ^ (72 * W)) ^ c := by
        simp only [← mul_pow]
    _ ≤ (3 ^ (72 * W)) ^ c := Nat.pow_le_pow_left hsingle c
    _ = 3 ^ (72 * c * W) := by rw [← pow_mul]; congr 1; ring

end Emulation

/-! ### Dynamic private-coin game classes and `IP[k(n)] ⊆ AM[k(n) + 2]` -/

open IPGame Emulation

/-- `(msg, dec)` is a dynamic private-coin game verifier for `A` with polynomial-time shape `g`
and `ρ(n)` coins evaluated at `n = (enc a).length`. -/
@[expose] def IsIPPolyGameVerifier (enc : α ↪ List Bool) (g : ℕ → List (IPMove × ℕ))
    (ρ : ℕ → ℕ) (msg : α × List Bool × ℕ × List Bool → List Bool)
    (dec : α × List Bool × List Bool → Bool) (A : Set α) : Prop :=
  ∀ a, (a ∈ A → 2 * 2 ^ ρ (enc a).length ≤
      3 * bestCount (fun (c : BitString (ρ (enc a).length)) j p => msg (a, List.ofFn c, j, p))
        (fun (c : BitString (ρ (enc a).length)) t => dec (a, List.ofFn c, t))
        (g (enc a).length)) ∧
    (a ∉ A → 3 * bestCount (fun (c : BitString (ρ (enc a).length)) j p =>
        msg (a, List.ofFn c, j, p))
        (fun (c : BitString (ρ (enc a).length)) t => dec (a, List.ofFn c, t))
        (g (enc a).length) ≤
      2 ^ ρ (enc a).length)

/-- Problems decided by polynomial-time private-coin game verifiers whose move pattern at input
length `n` is `π n`. -/
@[expose] def IPPolyGameClass (enc : α ↪ List Bool) (π : ℕ → List IPMove) : Set (Set α) :=
  {A | ∃ (g : ℕ → List (IPMove × ℕ)) (ρ : ℕ → ℕ)
    (msg : α × List Bool × ℕ × List Bool → List Bool) (dec : α × List Bool × List Bool → Bool),
    (∀ n, (g n).map Prod.fst = π n) ∧
      ComputableInPolyTime g encUnary encIPShape ∧
      ComputableInPolyTime ρ encUnary encUnary ∧
      ComputableInPolyTime msg (encMsgInput enc) encBits ∧
      ComputableInPolyTime dec (encDecInput enc) encBool ∧
      IsIPPolyGameVerifier enc g ρ msg dec A}

/-- `IP[k(n)]` for input-length-dependent alternating move count `k : ℕ → ℕ`, verifier first. -/
@[expose] def IPPolyRounds (enc : α ↪ List Bool) (k : ℕ → ℕ) : Set (Set α) :=
  IPPolyGameClass enc (fun n => (alternatingMoves .arthur (k n)).map AMMove.toIP)

/-- Every fixed-pattern private-coin game class embeds into `IPPolyGameClass`. -/
theorem IPGameClass_subset_IPPolyGameClass {enc : α ↪ List Bool} (π : List IPMove) :
    IPGameClass enc π ⊆ IPPolyGameClass enc (fun _ => π) := by
  rintro A ⟨G, ρ, msg, dec, hG, hmsg, hdec, hA⟩
  refine ⟨evalShape G, fun n => ρ.eval n, msg, dec, fun _ => ?_,
    computableInPolyTime_evalShape G, ComputableInPolyTime.unary_eval ρ, hmsg, hdec, fun a => ?_⟩
  · simp [evalShape, ← hG]
  · simpa [IsIPGameVerifier, countAt] using hA a

/-- Every constant-round `IP[k]` embeds into `IPPolyRounds`. -/
theorem IPk_subset_IPPolyRounds {enc : α ↪ List Bool} (k : ℕ) :
    IPk enc k ⊆ IPPolyRounds enc (fun _ => k) :=
  IPGameClass_subset_IPPolyGameClass _

/-- Public-coin dynamic games embed into private-coin dynamic games with the same move patterns. -/
theorem AMPolyGameClass_subset_IPPolyGameClass {enc : α ↪ List Bool} (π : ℕ → List AMMove) :
    AMPolyGameClass enc π ⊆ IPPolyGameClass enc (fun n => (π n).map AMMove.toIP) := by
  rintro A ⟨g, V, hg, hgp, hV, hA⟩
  have hofAM : ComputableInPolyTime (fun n => ofAM (g n)) encUnary encIPShape := by
    let encStep : (ℕ × (AMMove × ℕ)) ↪ List Bool :=
      encPair encUnary (encPair encAMMove encUnary)
    have hf : ComputableInPolyTime (fun x : ℕ × (AMMove × ℕ) => (x.2.1.toIP, x.2.2))
        encStep (encPair encIPMove encUnary) := by
      have hm : ComputableInPolyTime (fun x : ℕ × (AMMove × ℕ) => x.2.1.toIP)
          encStep encIPMove :=
        ((ComputableInPolyTime.fst encAMMove encUnary).comp
          (.snd encUnary (encPair encAMMove encUnary))).of_enc_eq fun x => by
          dsimp only [Function.comp_apply]
          cases x.2.1 <;> rfl
      exact hm.prod ((ComputableInPolyTime.snd encAMMove encUnary).comp
        (.snd encUnary (encPair encAMMove encUnary)))
    exact (ComputableInPolyTime.mapWithInput hgp hf).of_enc_eq fun _ => rfl
  have htr : ComputableInPolyTime (fun n => AMGame.transcriptLength (g n)) encUnary encUnary :=
    (computableInPolyTime_transcriptLength_dyn hofAM).of_enc_eq fun n => congrArg encUnary (by
      have hm : ∀ l : List (AMMove × ℕ),
          (ofAM l).map Prod.snd = l.map Prod.snd := fun l => by
        induction l <;> simp [ofAM, *]
      simp [AMGame.transcriptLength, IPGame.transcriptLength, hm])
  have hmsg : ComputableInPolyTime
      (fun x : α × List Bool × ℕ × List Bool => x.2.1.drop x.2.2.2.length)
      (encMsgInput enc) encBits := by
    have hc : ComputableInPolyTime (fun x : α × List Bool × ℕ × List Bool => x.2.1)
        (encMsgInput enc) encBits := (ComputableInPolyTime.fst _ _).comp (.snd _ _)
    have hp : ComputableInPolyTime (fun x : α × List Bool × ℕ × List Bool => x.2.2.2)
        (encMsgInput enc) encBits :=
      (ComputableInPolyTime.snd _ _).comp ((ComputableInPolyTime.snd _ _).comp (.snd _ _))
    exact ComputableInPolyTime.bitsDropWithInput hc (ComputableInPolyTime.length_bits.comp hp)
  have hdec : ComputableInPolyTime (fun x : α × List Bool × List Bool => V (x.1, x.2.2))
      (encDecInput enc) encBool := by
    have ha : ComputableInPolyTime (fun x : α × List Bool × List Bool => x.1)
        (encDecInput enc) enc := .fst _ _
    have ht : ComputableInPolyTime (fun x : α × List Bool × List Bool => x.2.2)
        (encDecInput enc) encBits := (ComputableInPolyTime.snd _ _).comp (.snd _ _)
    exact hV.comp (ha.prod ht)
  refine ⟨fun n => ofAM (g n), fun n => AMGame.transcriptLength (g n),
    fun x => x.2.1.drop x.2.2.2.length, fun x => V (x.1, x.2.2), fun n => ?_,
    hofAM, htr, hmsg, hdec, fun a => ?_⟩
  · have hmf : ∀ l : List (AMMove × ℕ), (ofAM l).map Prod.fst = (l.map Prod.fst).map AMMove.toIP :=
      fun l => by induction l <;> simp [ofAM, *]
    rw [hmf, hg n]
  · set n := (enc a).length
    have hcount := bestCount_reveal (g n) (fun t => V (a, t)) rfl
    dsimp only
    rw [hcount, transcriptLength_eq_arthurBits_add_merlinBits, pow_add]
    obtain ⟨h1, h2⟩ := hA a
    refine ⟨fun ha => ?_, fun ha => ?_⟩
    · have := Nat.mul_le_mul_right (2 ^ merlinBits (g n)) (h1 ha)
      linarith
    · have := Nat.mul_le_mul_right (2 ^ merlinBits (g n)) (h2 ha)
      linarith

/-- `AM[k(n)] ⊆ IP[k(n)]`. -/
theorem AMPolyRounds_subset_IPPolyRounds {enc : α ↪ List Bool} (k : ℕ → ℕ) :
    AMPolyRounds enc k ⊆ IPPolyRounds enc k :=
  AMPolyGameClass_subset_IPPolyGameClass _

private theorem alternatingMoves_add_two (x : AMMove) (k : ℕ) :
    alternatingMoves x (k + 2) = x :: x.other :: alternatingMoves x k := by
  cases x <;> rfl

private theorem alternatingMoves_two_mul_add_one (x : AMMove) (m : ℕ) :
    alternatingMoves x (2 * m + 1) = alternatingMoves x (2 * m) ++ [x] := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by omega,
      show 2 * (m + 1) = 2 * m + 2 by omega,
      alternatingMoves_add_two, alternatingMoves_add_two, ih]
    rfl

private theorem length_alternatingMoves (x : AMMove) (k : ℕ) :
    (alternatingMoves x k).length = k := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => simp [alternatingMoves, ih]

private theorem list_take_append_getLastD {β : Type} (l : List β) (d : β) (hl : l ≠ []) :
    l.take (l.length - 1) ++ [l.getLastD d] = l := by
  induction l with
  | nil => contradiction
  | cons x xs ih =>
    cases xs with
    | nil => simp
    | cons y ys => simpa [List.take_succ_cons, List.getLastD_cons] using ih (by simp)

private theorem list_getLastD_map_fst (l : List (IPMove × ℕ)) (d : IPMove × ℕ) (hl : l ≠ []) :
    (l.getLastD d).1 = (l.map Prod.fst).getLastD d.1 := by
  induction l with
  | nil => contradiction
  | cons x xs ih =>
    cases xs with
    | nil => simp
    | cons y ys => simpa using ih (by simp)

/-- For constant `q`, dropping the trailing verifier move gives `IP[2 * q + 1] = IP[2 * q]`. -/
theorem IPk_two_mul_add_one_eq {enc : α ↪ List Bool} (q : ℕ) :
    IPk enc (2 * q + 1) = IPk enc (2 * q) := by
  refine le_antisymm ?_ ?_
  · rintro A ⟨G, ρ, msg, dec, hG, hmsg, hdec, hA⟩
    have hpat : G.map Prod.fst =
        (alternatingMoves .arthur (2 * q)).map AMMove.toIP ++ [.verifier] := by
      rw [hG, alternatingMoves_two_mul_add_one, List.map_append]
      rfl
    obtain ⟨G', Gtail, rfl, hG', htail⟩ := List.map_eq_append_iff.1 hpat
    obtain ⟨⟨v, L⟩, Gnil, rfl, hv, hnil⟩ := List.map_eq_cons_iff.1 htail
    dsimp only at hv
    subst hv
    have hnil' : Gnil = [] := List.map_eq_nil_iff.1 hnil
    subst hnil'
    have hlenG : ∀ a, G'.length = (evalShape G' (enc a).length).length := fun a => by
      simp [evalShape]
    refine ⟨G', ρ, msg,
      fun x => dec (x.1, x.2.1, x.2.2 ++ BitString.listRow (L.eval (enc x.1).length) 0
        (msg (x.1, x.2.1, G'.length, x.2.2))), hG', hmsg, ?_, fun a => ?_⟩
    · have hn : ComputableInPolyTime (fun x : α × List Bool × List Bool => (enc x.1).length)
          (encDecInput enc) encUnary :=
        (ComputableInPolyTime.encoding_length enc).comp (.fst _ _)
      have hL : ComputableInPolyTime (fun x : α × List Bool × List Bool =>
          L.eval (enc x.1).length) (encDecInput enc) encUnary :=
        (ComputableInPolyTime.unary_eval L).comp hn
      have ha : ComputableInPolyTime (fun x : α × List Bool × List Bool => x.1)
          (encDecInput enc) enc := .fst _ _
      have hc : ComputableInPolyTime (fun x : α × List Bool × List Bool => x.2.1)
          (encDecInput enc) encBits :=
        (ComputableInPolyTime.fst _ _).comp (.snd enc (encPair encBits encBits))
      have ht : ComputableInPolyTime (fun x : α × List Bool × List Bool => x.2.2)
          (encDecInput enc) encBits :=
        (ComputableInPolyTime.snd _ _).comp (.snd enc (encPair encBits encBits))
      have hm := hmsg.comp (ha.prod (hc.prod ((ComputableInPolyTime.const G'.length).prod ht)))
      have hrow := ComputableInPolyTime.bitsRowWithInput hL (ComputableInPolyTime.const 0) hm
      exact hdec.comp (ha.prod (hc.prod (ComputableInPolyTime.bitsAppend ht hrow)))
    · have hbest := @bestCount_append_verifier (ρ.eval (enc a).length)
        (fun c j p => msg (a, List.ofFn c, j, p))
        (fun c t => dec (a, List.ofFn c, t)) (evalShape G' (enc a).length)
        (L.eval (enc a).length)
      have ha := hA a
      change _ ∧ _ at ha ⊢
      have hcongr : countAt enc G' ρ msg
          (fun x => dec (x.1, x.2.1, x.2.2 ++ BitString.listRow (L.eval (enc x.1).length) 0
            (msg (x.1, x.2.1, G'.length, x.2.2)))) a =
          countAt enc (G' ++ [(.verifier, L)]) ρ msg dec a := by
        unfold countAt
        rw [evalShape_append, evalShape_cons, evalShape_nil, hbest]
        simp only [BitString.listRow_zero, hlenG a]
      rw [hcongr]
      exact ha
  · rintro A ⟨G, ρ, msg, dec, hG, hmsg, hdec, hA⟩
    refine ⟨G ++ [(.verifier, 0)], ρ, msg, dec, ?_, hmsg, hdec, fun a => ?_⟩
    · rw [List.map_append, hG, alternatingMoves_two_mul_add_one, List.map_append]
      rfl
    · have hbest := @bestCount_append_verifier (ρ.eval (enc a).length)
        (fun c j p => msg (a, List.ofFn c, j, p))
        (fun c t => dec (a, List.ofFn c, t)) (evalShape G (enc a).length) 0
      have ha := hA a
      unfold countAt at ha ⊢
      rw [evalShape_append, evalShape_cons, evalShape_nil, Polynomial.eval_zero, hbest]
      simpa [List.ofFn_zero, List.append_nil] using ha

private theorem map_fst_mergeMerlin_emulation (B Z ρ : ℕ) :
    ∀ (m : ℕ) (g : List (IPMove × ℕ)),
      g.map Prod.fst = (alternatingMoves .arthur (2 * m)).map AMMove.toIP →
      (AMGame.mergeMerlin (shape B Z (g ++ [(.verifier, ρ)]))).map Prod.fst =
        alternatingMoves .arthur (2 * m + 2) := by
  intro m
  induction m with
  | zero =>
    intro g hg
    have hgEmpty : g.map Prod.fst = [] := by simpa [alternatingMoves] using hg
    have hgnil : g = [] := List.map_eq_nil_iff.1 hgEmpty
    subst hgnil
    simp [shape, AMGame.mergeMerlin, alternatingMoves, AMMove.other]
  | succ m ih =>
    intro g hg
    rw [show 2 * (m + 1) = 2 * m + 2 by omega] at hg ⊢
    change g.map Prod.fst = [.verifier, .prover] ++
        (alternatingMoves .arthur (2 * m)).map AMMove.toIP at hg
    obtain ⟨⟨v, nV⟩, g₁, rfl, hv, hg₁⟩ := List.map_eq_cons_iff.1 hg
    obtain ⟨⟨p, nP⟩, g', rfl, hp, hg'⟩ := List.map_eq_cons_iff.1 hg₁
    dsimp only at hv hp
    subst hv hp
    have ih' := ih g' hg'
    have hne : AMGame.mergeMerlin (shape B Z (g' ++ [(.verifier, ρ)])) ≠ [] := by
      intro h
      rw [h] at ih'
      simp [alternatingMoves] at ih'
    have hhead : ∃ nA tail, AMGame.mergeMerlin (shape B Z (g' ++ [(.verifier, ρ)])) =
        (.arthur, nA) :: tail := by
      cases h : AMGame.mergeMerlin (shape B Z (g' ++ [(.verifier, ρ)])) with
      | nil => exact absurd h hne
      | cons y tail =>
        obtain ⟨_ | _, nA⟩ := y
        · exact ⟨nA, tail, rfl⟩
        · rw [h] at ih'
          simp [alternatingMoves] at ih'
    obtain ⟨nA, tail, htail⟩ := hhead
    simp only [List.cons_append, shape, AMGame.mergeMerlin, htail, List.map_cons]
    have halt : alternatingMoves AMMove.arthur (2 * m + 2 + 2) =
        AMMove.arthur :: AMMove.merlin :: alternatingMoves AMMove.arthur (2 * m + 2) := rfl
    rw [halt, ← ih', htail]
    rfl

private def truncShape (g₀ : ℕ → List (IPMove × ℕ)) (n : ℕ) : List (IPMove × ℕ) :=
  if (g₀ n).length % 2 = 1 then (g₀ n).take ((g₀ n).length - 1) else g₀ n

private theorem computableInPolyTime_truncShape {g₀ : ℕ → List (IPMove × ℕ)}
    (hgp₀ : ComputableInPolyTime g₀ encUnary encIPShape) :
    ComputableInPolyTime (truncShape g₀) encUnary encIPShape := by
  have hlen : ComputableInPolyTime (fun n => (g₀ n).length) encUnary encUnary :=
    (ComputableInPolyTime.length_list (encPair encIPMove encUnary)).comp hgp₀
  have hodd : ComputableInPolyTime (fun n => decide ((g₀ n).length % 2 = 1)) encUnary encBool :=
    computableInPolyTime_unaryOdd.comp hlen
  have htake : ComputableInPolyTime (fun n => (g₀ n).take ((g₀ n).length - 1))
      encUnary encIPShape :=
    .of_tidy (ComputableTidilyInPolyTime.listTakeWithInput hgp₀.tidy
      (ComputableInPolyTime.unary_sub' hlen (ComputableInPolyTime.const 1)).tidy)
  exact (hodd.ite htake hgp₀).of_enc_eq fun n => by
    simp only [truncShape, decide_eq_true_eq]

private def truncDec (enc : α ↪ List Bool) (g₀ : ℕ → List (IPMove × ℕ))
    (msg₀ : α × List Bool × ℕ × List Bool → List Bool)
    (dec₀ : α × List Bool × List Bool → Bool) (x : α × List Bool × List Bool) : Bool :=
  let n := (enc x.1).length
  if (g₀ n).length % 2 = 1 then
    dec₀ (x.1, x.2.1, x.2.2 ++ BitString.listRow ((g₀ n).getLastD (.verifier, 0)).2 0
      (msg₀ (x.1, x.2.1, (g₀ n).length - 1, x.2.2)))
  else dec₀ x

private theorem computableInPolyTime_truncDec {enc : α ↪ List Bool} {g₀ : ℕ → List (IPMove × ℕ)}
    {msg₀ : α × List Bool × ℕ × List Bool → List Bool} {dec₀ : α × List Bool × List Bool → Bool}
    (hgp₀ : ComputableInPolyTime g₀ encUnary encIPShape)
    (hmsg₀ : ComputableInPolyTime msg₀ (encMsgInput enc) encBits)
    (hdec₀ : ComputableInPolyTime dec₀ (encDecInput enc) encBool) :
    ComputableInPolyTime (truncDec enc g₀ msg₀ dec₀) (encDecInput enc) encBool := by
  have hn : ComputableInPolyTime (fun x : α × List Bool × List Bool => (enc x.1).length)
      (encDecInput enc) encUnary :=
    (ComputableInPolyTime.encoding_length enc).comp (.fst _ _)
  have hg₀n : ComputableInPolyTime (fun x : α × List Bool × List Bool => g₀ (enc x.1).length)
      (encDecInput enc) encIPShape := hgp₀.comp hn
  have hlen : ComputableInPolyTime (fun x : α × List Bool × List Bool =>
      (g₀ (enc x.1).length).length) (encDecInput enc) encUnary :=
    (ComputableInPolyTime.length_list (encPair encIPMove encUnary)).comp hg₀n
  have hodd : ComputableInPolyTime (fun x : α × List Bool × List Bool =>
      decide ((g₀ (enc x.1).length).length % 2 = 1)) (encDecInput enc) encBool :=
    computableInPolyTime_unaryOdd.comp hlen
  have hsub : ComputableInPolyTime (fun x : α × List Bool × List Bool =>
      (g₀ (enc x.1).length).length - 1) (encDecInput enc) encUnary :=
    ComputableInPolyTime.unary_sub' hlen (ComputableInPolyTime.const 1)
  have hlast : ComputableInPolyTime (fun x : α × List Bool × List Bool =>
      ((g₀ (enc x.1).length).getLastD (.verifier, 0)).2) (encDecInput enc) encUnary := by
    have hget := ComputableInPolyTime.listGetDWithInput hg₀n hsub (.verifier, 0)
    have hsnd : ComputableInPolyTime (fun p : IPMove × ℕ => p.2)
        (encPair encIPMove encUnary) encUnary := ComputableInPolyTime.snd _ _
    exact (hsnd.comp hget).of_enc_eq fun x => congrArg encUnary (by
      dsimp only [Function.comp_apply]
      rw [list_getLastD_eq_getD])
  have ha : ComputableInPolyTime (fun x : α × List Bool × List Bool => x.1)
      (encDecInput enc) enc := .fst _ _
  have hc : ComputableInPolyTime (fun x : α × List Bool × List Bool => x.2.1)
      (encDecInput enc) encBits :=
    (ComputableInPolyTime.fst _ _).comp (.snd enc (encPair encBits encBits))
  have ht : ComputableInPolyTime (fun x : α × List Bool × List Bool => x.2.2)
      (encDecInput enc) encBits :=
    (ComputableInPolyTime.snd _ _).comp (.snd enc (encPair encBits encBits))
  have hm := hmsg₀.comp (ha.prod (hc.prod (hsub.prod ht)))
  have hrow := ComputableInPolyTime.bitsRowWithInput hlast (ComputableInPolyTime.const 0) hm
  have hbr := hdec₀.comp (ha.prod (hc.prod (ComputableInPolyTime.bitsAppend ht hrow)))
  exact (hodd.ite hbr hdec₀).of_enc_eq fun x => by
    simp only [truncDec, decide_eq_true_eq, Function.comp_apply]

private def gsC (g₁ : ℕ → List (IPMove × ℕ)) (n : ℕ) : ℕ := verifierMoves (g₁ n) + 1

private def gsW (g₁ : ℕ → List (IPMove × ℕ)) (ρ₀ : ℕ → ℕ) (n : ℕ) : ℕ :=
  transcriptLength (g₁ n) + (g₁ n).length + ρ₀ n + 1

private def gsR (g₁ : ℕ → List (IPMove × ℕ)) (ρ₀ : ℕ → ℕ) (n : ℕ) : ℕ :=
  72 * gsC g₁ n * gsW g₁ ρ₀ n

private def gsB (g₁ : ℕ → List (IPMove × ℕ)) (ρ₀ : ℕ → ℕ) (n : ℕ) : ℕ :=
  gsR g₁ ρ₀ n * gsW g₁ ρ₀ n

private def gsZ (g₁ : ℕ → List (IPMove × ℕ)) (ρ₀ : ℕ → ℕ) (n : ℕ) : ℕ :=
  2 * (gsB g₁ ρ₀ n + 6 * gsC g₁ n * (gsB g₁ ρ₀ n + 1))

private def gsK (g₁ : ℕ → List (IPMove × ℕ)) (ρ₀ : ℕ → ℕ) (n : ℕ) : ℕ :=
  Emulation.threshold (gsC g₁ n) (gsB g₁ ρ₀ n)

private def gsRep (g₁ : ℕ → List (IPMove × ℕ)) (ρ₀ : ℕ → ℕ) (n : ℕ) : List (IPMove × ℕ) :=
  repeatShape (gsR g₁ ρ₀ n) (g₁ n) ++ [(.verifier, gsR g₁ ρ₀ n * ρ₀ n)]

private def gsAM (g₀ : ℕ → List (IPMove × ℕ)) (ρ₀ : ℕ → ℕ) (n : ℕ) : List (AMMove × ℕ) :=
  let g₁ := truncShape g₀
  let base := AMGame.mergeMerlin (shape (gsB g₁ ρ₀ n) (gsZ g₁ ρ₀ n) (gsRep g₁ ρ₀ n))
  if (g₀ n).length % 2 = 1 then base ++ [(.arthur, 0)] else base

private def gsMsgRep (enc : α ↪ List Bool) (g₁ : ℕ → List (IPMove × ℕ)) (ρ₀ : ℕ → ℕ)
    (msg₀ : α × List Bool × ℕ × List Bool → List Bool) (R : ℕ → ℕ)
    (a : α) (c' : List Bool) (j : ℕ) (p : List Bool) : List Bool :=
  repeatMsg (R (enc a).length) (g₁ (enc a).length)
    (fun i j' p' => msg₀ (a, BitString.listRow (ρ₀ (enc a).length) i c', j', p')) j p

private def gsDecRep (enc : α ↪ List Bool) (g₁ : ℕ → List (IPMove × ℕ)) (ρ₀ : ℕ → ℕ)
    (dec₁ : α × List Bool × List Bool → Bool) (R : ℕ → ℕ)
    (a : α) (c' : List Bool) (t : List Bool) : Bool :=
  repeatDec (R (enc a).length) (g₁ (enc a).length)
    (fun i t' => dec₁ (a, BitString.listRow (ρ₀ (enc a).length) i c', t')) t

private def gsReveal (enc : α ↪ List Bool) (g₁ : ℕ → List (IPMove × ℕ)) (ρ₀ : ℕ → ℕ)
    (msg₀ : α × List Bool × ℕ × List Bool → List Bool)
    (dec₁ : α × List Bool × List Bool → Bool) (R : ℕ → ℕ) (a : α) (w : List Bool) : Bool :=
  revealPayoff (gsMsgRep enc g₁ ρ₀ msg₀ R a) (gsDecRep enc g₁ ρ₀ dec₁ R a)
    (repeatShape (R (enc a).length) (g₁ (enc a).length))
    (transcriptLength (repeatShape (R (enc a).length) (g₁ (enc a).length))) w

private def gsVAM (enc : α ↪ List Bool) (g₀ : ℕ → List (IPMove × ℕ)) (ρ₀ : ℕ → ℕ)
    (msg₀ : α × List Bool × ℕ × List Bool → List Bool)
    (dec₀ : α × List Bool × List Bool → Bool) (x : α × List Bool) : Bool :=
  check
    (gsB (truncShape g₀) ρ₀ (enc x.1).length)
    (gsZ (truncShape g₀) ρ₀ (enc x.1).length)
    (gsK (truncShape g₀) ρ₀ (enc x.1).length)
    (gsReveal enc (truncShape g₀) ρ₀ msg₀ (truncDec enc g₀ msg₀ dec₀)
      (gsR (truncShape g₀) ρ₀) x.1)
    (gsRep (truncShape g₀) ρ₀ (enc x.1).length)
    (gsR (truncShape g₀) ρ₀ (enc x.1).length * ρ₀ (enc x.1).length -
      gsR (truncShape g₀) ρ₀ (enc x.1).length)
    [] x.2

private theorem computableInPolyTime_gsC {g₁ : ℕ → List (IPMove × ℕ)}
    (hg₁ : ComputableInPolyTime g₁ encUnary encIPShape) :
    ComputableInPolyTime (gsC g₁) encUnary encUnary :=
  (ComputableInPolyTime.unary_add' (computableInPolyTime_verifierMoves_dyn hg₁)
    (ComputableInPolyTime.const 1)).of_enc_eq fun _ => rfl

private theorem computableInPolyTime_gsW {g₁ : ℕ → List (IPMove × ℕ)} {ρ₀ : ℕ → ℕ}
    (hg₁ : ComputableInPolyTime g₁ encUnary encIPShape)
    (hρ : ComputableInPolyTime ρ₀ encUnary encUnary) :
    ComputableInPolyTime (gsW g₁ ρ₀) encUnary encUnary :=
  (ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_add'
    (ComputableInPolyTime.unary_add' (computableInPolyTime_transcriptLength_dyn hg₁)
      ((ComputableInPolyTime.length_list (encPair encIPMove encUnary)).comp hg₁))
    hρ) (ComputableInPolyTime.const 1)).of_enc_eq fun _ => rfl

private theorem computableInPolyTime_gsR {g₁ : ℕ → List (IPMove × ℕ)} {ρ₀ : ℕ → ℕ}
    (hg₁ : ComputableInPolyTime g₁ encUnary encIPShape)
    (hρ : ComputableInPolyTime ρ₀ encUnary encUnary) :
    ComputableInPolyTime (gsR g₁ ρ₀) encUnary encUnary :=
  (ComputableInPolyTime.unary_mul'
    (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 72)
      (computableInPolyTime_gsC hg₁))
    (computableInPolyTime_gsW hg₁ hρ)).of_enc_eq fun _ => rfl

private theorem computableInPolyTime_gsB {g₁ : ℕ → List (IPMove × ℕ)} {ρ₀ : ℕ → ℕ}
    (hg₁ : ComputableInPolyTime g₁ encUnary encIPShape)
    (hρ : ComputableInPolyTime ρ₀ encUnary encUnary) :
    ComputableInPolyTime (gsB g₁ ρ₀) encUnary encUnary :=
  (ComputableInPolyTime.unary_mul' (computableInPolyTime_gsR hg₁ hρ)
    (computableInPolyTime_gsW hg₁ hρ)).of_enc_eq fun _ => rfl

private theorem computableInPolyTime_gsZ {g₁ : ℕ → List (IPMove × ℕ)} {ρ₀ : ℕ → ℕ}
    (hg₁ : ComputableInPolyTime g₁ encUnary encIPShape)
    (hρ : ComputableInPolyTime ρ₀ encUnary encUnary) :
    ComputableInPolyTime (gsZ g₁ ρ₀) encUnary encUnary :=
  (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2)
    (ComputableInPolyTime.unary_add' (computableInPolyTime_gsB hg₁ hρ)
      (ComputableInPolyTime.unary_mul'
        (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 6)
          (computableInPolyTime_gsC hg₁))
        (ComputableInPolyTime.unary_add' (computableInPolyTime_gsB hg₁ hρ)
          (ComputableInPolyTime.const 1))))).of_enc_eq fun _ => rfl

private theorem computableInPolyTime_gsK {g₁ : ℕ → List (IPMove × ℕ)} {ρ₀ : ℕ → ℕ}
    (hg₁ : ComputableInPolyTime g₁ encUnary encIPShape)
    (hρ : ComputableInPolyTime ρ₀ encUnary encUnary) :
    ComputableInPolyTime (gsK g₁ ρ₀) encUnary encUnary :=
  (ComputableInPolyTime.unary_add' (computableInPolyTime_gsB hg₁ hρ)
    ((ComputableInPolyTime.unary_clog_const 2).comp
      (ComputableInPolyTime.unary_mul'
        (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 6)
          (computableInPolyTime_gsC hg₁))
        (ComputableInPolyTime.unary_add' (computableInPolyTime_gsB hg₁ hρ)
          (ComputableInPolyTime.const 1))))).of_enc_eq fun _ => rfl

private theorem computableInPolyTime_gsRep {g₁ : ℕ → List (IPMove × ℕ)} {ρ₀ : ℕ → ℕ}
    (hg₁ : ComputableInPolyTime g₁ encUnary encIPShape)
    (hρ : ComputableInPolyTime ρ₀ encUnary encUnary) :
    ComputableInPolyTime (gsRep g₁ ρ₀) encUnary encIPShape := by
  have hrep := computableInPolyTime_repeatShape_dyn (computableInPolyTime_gsR hg₁ hρ) hg₁
  have hlast : ComputableInPolyTime (fun n => [(IPMove.verifier, gsR g₁ ρ₀ n * ρ₀ n)])
      encUnary encIPShape :=
    ((ComputableInPolyTime.const IPMove.verifier).prod
      (ComputableInPolyTime.unary_mul' (computableInPolyTime_gsR hg₁ hρ) hρ)).cons'
      (ComputableInPolyTime.const [])
  exact (computableInPolyTime_listAppend hrep hlast).of_enc_eq fun _ => rfl

private theorem computableInPolyTime_gsAM {g₀ : ℕ → List (IPMove × ℕ)} {ρ₀ : ℕ → ℕ}
    (hgp₀ : ComputableInPolyTime g₀ encUnary encIPShape)
    (hρ : ComputableInPolyTime ρ₀ encUnary encUnary) :
    ComputableInPolyTime (gsAM g₀ ρ₀) encUnary encAMShape := by
  have hg₁ := computableInPolyTime_truncShape hgp₀
  have hbase := computableInPolyTime_mergeMerlin
    (computableInPolyTime_shape_dyn (computableInPolyTime_gsB hg₁ hρ)
      (computableInPolyTime_gsZ hg₁ hρ) (computableInPolyTime_gsRep hg₁ hρ))
  have hlen : ComputableInPolyTime (fun n => (g₀ n).length) encUnary encUnary :=
    (ComputableInPolyTime.length_list (encPair encIPMove encUnary)).comp hgp₀
  have hodd : ComputableInPolyTime (fun n => decide ((g₀ n).length % 2 = 1)) encUnary encBool :=
    computableInPolyTime_unaryOdd.comp hlen
  have happ := computableInPolyTime_listAppend hbase (ComputableInPolyTime.const [(.arthur, 0)])
  exact (hodd.ite happ hbase).of_enc_eq fun n => by simp [gsAM]

private theorem computableInPolyTime_gsMsgRep {enc : α ↪ List Bool}
    {g₁ : ℕ → List (IPMove × ℕ)} {ρ₀ R : ℕ → ℕ}
    {msg₀ : α × List Bool × ℕ × List Bool → List Bool}
    (hg₁ : ComputableInPolyTime g₁ encUnary encIPShape)
    (hρ : ComputableInPolyTime ρ₀ encUnary encUnary)
    (hR : ComputableInPolyTime R encUnary encUnary)
    (hmsg₀ : ComputableInPolyTime msg₀ (encMsgInput enc) encBits) :
    ComputableInPolyTime
      (fun y : α × List Bool × ℕ × List Bool =>
        gsMsgRep enc g₁ ρ₀ msg₀ R y.1 y.2.1 y.2.2.1 y.2.2.2)
      (encMsgInput enc) encBits := by
  have hn : ComputableInPolyTime
      (fun y : α × List Bool × ℕ × List Bool => (enc y.1).length)
      (encMsgInput enc) encUnary :=
    (ComputableInPolyTime.encoding_length enc).comp (.fst _ _)
  have haM : ComputableInPolyTime (fun y : α × List Bool × ℕ × List Bool => y.1)
      (encMsgInput enc) enc := .fst _ _
  have hcM : ComputableInPolyTime (fun y : α × List Bool × ℕ × List Bool => y.2.1)
      (encMsgInput enc) encBits :=
    (ComputableInPolyTime.fst _ _).comp (.snd enc (encPair encBits (encPair encUnary encBits)))
  have hjM : ComputableInPolyTime (fun y : α × List Bool × ℕ × List Bool => y.2.2.1)
      (encMsgInput enc) encUnary :=
    (ComputableInPolyTime.fst _ _).comp
      ((ComputableInPolyTime.snd _ _).comp (.snd enc (encPair encBits (encPair encUnary encBits))))
  have hpM : ComputableInPolyTime (fun y : α × List Bool × ℕ × List Bool => y.2.2.2)
      (encMsgInput enc) encBits :=
    (ComputableInPolyTime.snd _ _).comp
      ((ComputableInPolyTime.snd _ _).comp (.snd enc (encPair encBits (encPair encUnary encBits))))
  exact (computableInPolyTime_repeatMsg_dyn haM hcM (hg₁.comp hn) (hR.comp hn)
    (hρ.comp hn) hjM hpM hmsg₀).of_enc_eq fun _ => rfl

private theorem computableInPolyTime_gsDecRep {enc : α ↪ List Bool}
    {g₁ : ℕ → List (IPMove × ℕ)} {ρ₀ R : ℕ → ℕ}
    {dec₁ : α × List Bool × List Bool → Bool}
    (hg₁ : ComputableInPolyTime g₁ encUnary encIPShape)
    (hρ : ComputableInPolyTime ρ₀ encUnary encUnary)
    (hR : ComputableInPolyTime R encUnary encUnary)
    (hdec₁ : ComputableInPolyTime dec₁ (encDecInput enc) encBool) :
    ComputableInPolyTime
      (fun y : α × List Bool × List Bool =>
        gsDecRep enc g₁ ρ₀ dec₁ R y.1 y.2.1 y.2.2)
      (encDecInput enc) encBool := by
  have hn : ComputableInPolyTime
      (fun y : α × List Bool × List Bool => (enc y.1).length)
      (encDecInput enc) encUnary :=
    (ComputableInPolyTime.encoding_length enc).comp (.fst _ _)
  have haD : ComputableInPolyTime (fun y : α × List Bool × List Bool => y.1)
      (encDecInput enc) enc := .fst _ _
  have hcD : ComputableInPolyTime (fun y : α × List Bool × List Bool => y.2.1)
      (encDecInput enc) encBits :=
    (ComputableInPolyTime.fst _ _).comp (.snd enc (encPair encBits encBits))
  have hwD : ComputableInPolyTime (fun y : α × List Bool × List Bool => y.2.2)
      (encDecInput enc) encBits :=
    (ComputableInPolyTime.snd _ _).comp (.snd enc (encPair encBits encBits))
  exact (computableInPolyTime_repeatDec_dyn haD hcD (hg₁.comp hn) (hR.comp hn)
    (hρ.comp hn) hwD hdec₁).of_enc_eq fun _ => rfl

private theorem computableInPolyTime_gsReveal {enc : α ↪ List Bool}
    {g₁ : ℕ → List (IPMove × ℕ)} {ρ₀ R : ℕ → ℕ}
    {msg₀ : α × List Bool × ℕ × List Bool → List Bool}
    {dec₁ : α × List Bool × List Bool → Bool}
    {q : α × List Bool → List Bool}
    (hg₁ : ComputableInPolyTime g₁ encUnary encIPShape)
    (hρ : ComputableInPolyTime ρ₀ encUnary encUnary)
    (hR : ComputableInPolyTime R encUnary encUnary)
    (hmsg₀ : ComputableInPolyTime msg₀ (encMsgInput enc) encBits)
    (hdec₁ : ComputableInPolyTime dec₁ (encDecInput enc) encBool)
    (hq : ComputableInPolyTime q (encPair enc encBits) encBits) :
    ComputableInPolyTime
      (fun x : α × List Bool => gsReveal enc g₁ ρ₀ msg₀ dec₁ R x.1 (q x))
      (encPair enc encBits) encBool := by
  have hn : ComputableInPolyTime (fun x : α × List Bool => (enc x.1).length)
      (encPair enc encBits) encUnary := (ComputableInPolyTime.encoding_length enc).comp (.fst _ _)
  have hx1 : ComputableInPolyTime (fun x : α × List Bool => x.1) (encPair enc encBits) enc :=
    .fst _ _
  have hgrepx := computableInPolyTime_repeatShape_dyn (hR.comp hn) (hg₁.comp hn)
  have hLx := computableInPolyTime_transcriptLength_dyn hgrepx
  have hmsgRep := computableInPolyTime_gsMsgRep (enc := enc) hg₁ hρ hR hmsg₀
  have hdecRep := computableInPolyTime_gsDecRep (enc := enc) hg₁ hρ hR hdec₁
  exact computableInPolyTime_revealPayoff_dyn hx1 hgrepx hLx hmsgRep hdecRep hq

private theorem computableInPolyTime_gsVAM {enc : α ↪ List Bool} {g₀ : ℕ → List (IPMove × ℕ)}
    {ρ₀ : ℕ → ℕ} {msg₀ : α × List Bool × ℕ × List Bool → List Bool}
    {dec₀ : α × List Bool × List Bool → Bool}
    (hgp₀ : ComputableInPolyTime g₀ encUnary encIPShape)
    (hρ : ComputableInPolyTime ρ₀ encUnary encUnary)
    (hmsg₀ : ComputableInPolyTime msg₀ (encMsgInput enc) encBits)
    (hdec₀ : ComputableInPolyTime dec₀ (encDecInput enc) encBool) :
    ComputableInPolyTime (gsVAM enc g₀ ρ₀ msg₀ dec₀) (encPair enc encBits) encBool := by
  have hg₁ := computableInPolyTime_truncShape hgp₀
  have hdec₁ := computableInPolyTime_truncDec hgp₀ hmsg₀ hdec₀
  have hn : ComputableInPolyTime (fun x : α × List Bool => (enc x.1).length)
      (encPair enc encBits) encUnary := (ComputableInPolyTime.encoding_length enc).comp (.fst _ _)
  have hR := computableInPolyTime_gsR hg₁ hρ
  have hBx := (computableInPolyTime_gsB hg₁ hρ).comp hn
  have hZx := (computableInPolyTime_gsZ hg₁ hρ).comp hn
  have hKx := (computableInPolyTime_gsK hg₁ hρ).comp hn
  have hgRepx := (computableInPolyTime_gsRep hg₁ hρ).comp hn
  have hRx := hR.comp hn
  have hρx := hρ.comp hn
  have hκx := ComputableInPolyTime.unary_sub'
    (ComputableInPolyTime.unary_mul' hRx hρx) hRx
  exact computableInPolyTime_check_dyn hBx hZx hKx hgRepx
    (fun {q} hq => computableInPolyTime_gsReveal hg₁ hρ hR hmsg₀ hdec₁ hq)
    hκx (ComputableInPolyTime.const []) (ComputableInPolyTime.snd _ _)

/-- **Goldwasser–Sipser for polynomially many rounds (`IP[k(n)] ⊆ AM[k(n) + 2]`)** without
round collapse: odd-length patterns drop their trailing verifier move into `dec`, while parallel
repetition of `R(n) = 72 * c(n) * W(n)` copies beats `μ ^ c(n)` uniformly for all `n`. -/
theorem IPPolyRounds_subset_AMPolyRounds {enc : α ↪ List Bool} (k : ℕ → ℕ) :
    IPPolyRounds enc k ⊆ AMPolyRounds enc (fun n => k n + 2) := by
  rintro A ⟨g₀, ρ₀, msg₀, dec₀, hg₀, hgp₀, hρp₀, hmsg₀, hdec₀, hA⟩
  let g₁ := truncShape g₀
  let dec₁ := truncDec enc g₀ msg₀ dec₀
  have hg₁_pat : ∀ n, (g₁ n).map Prod.fst =
      (alternatingMoves .arthur (2 * (k n / 2))).map AMMove.toIP := by
    intro n
    have hlen : (g₀ n).length = k n := by
      have hL := congrArg List.length (hg₀ n)
      simpa only [List.length_map, length_alternatingMoves] using hL
    by_cases hodd : k n % 2 = 1
    · have hodd' : (g₀ n).length % 2 = 1 := by omega
      have hlen1 : (g₀ n).length - 1 = 2 * (k n / 2) := by omega
      have hsub : k n = 2 * (k n / 2) + 1 := by omega
      dsimp only [g₁, truncShape]
      rw [ite_eq_left hodd', hlen1, List.map_take, hg₀ n]
      dsimp only
      have halt : alternatingMoves AMMove.arthur (k n) =
          alternatingMoves AMMove.arthur (2 * (k n / 2)) ++ [AMMove.arthur] := by
        conv_lhs => rw [hsub]
        exact alternatingMoves_two_mul_add_one .arthur (k n / 2)
      rw [halt, List.map_append, List.take_left' (by simp [length_alternatingMoves])]
    · have heven : (g₀ n).length % 2 ≠ 1 := by omega
      have hsub : k n = 2 * (k n / 2) := by omega
      dsimp only [g₁, truncShape]
      rw [ite_eq_right heven, hg₀ n]
      dsimp only
      conv_lhs => rw [hsub]
  have hcount₁ : ∀ a, bestCount (fun (c : BitString (ρ₀ (enc a).length)) j p =>
        msg₀ (a, List.ofFn c, j, p))
      (fun (c : BitString (ρ₀ (enc a).length)) t => dec₁ (a, List.ofFn c, t))
      (g₁ (enc a).length) =
      bestCount (fun (c : BitString (ρ₀ (enc a).length)) j p => msg₀ (a, List.ofFn c, j, p))
        (fun (c : BitString (ρ₀ (enc a).length)) t => dec₀ (a, List.ofFn c, t))
        (g₀ (enc a).length) := by
    intro a
    set n := (enc a).length
    have hlen : (g₀ n).length = k n := by
      have hL := congrArg List.length (hg₀ n)
      simpa only [List.length_map, length_alternatingMoves] using hL
    by_cases hodd : (g₀ n).length % 2 = 1
    · have hsub : k n = 2 * (k n / 2) + 1 := by omega
      have hne : g₀ n ≠ [] := by intro h; simp [h] at hodd
      have hsplit : g₁ n ++ [(g₀ n).getLastD (.verifier, 0)] = g₀ n := by
        dsimp only [g₁, truncShape]
        rw [ite_eq_left hodd]
        exact list_take_append_getLastD (g₀ n) (.verifier, 0) hne
      have hlastMove : ((g₀ n).getLastD (.verifier, 0)).1 = .verifier := by
        rw [list_getLastD_map_fst _ _ hne, hg₀ n]
        dsimp only
        have halt : alternatingMoves AMMove.arthur (k n) =
            alternatingMoves AMMove.arthur (2 * (k n / 2)) ++ [AMMove.arthur] := by
          conv_lhs => rw [hsub]
          exact alternatingMoves_two_mul_add_one .arthur (k n / 2)
        rw [halt, List.map_append]
        simp [AMMove.toIP]
      have hlen1 : (g₁ n).length = (g₀ n).length - 1 := by
        dsimp only [g₁, truncShape]
        rw [ite_eq_left hodd, List.length_take]
        omega
      have heq : g₀ n = g₁ n ++ [(.verifier, ((g₀ n).getLastD (.verifier, 0)).2)] := by
        have hpair : (g₀ n).getLastD (.verifier, 0) =
            (.verifier, ((g₀ n).getLastD (.verifier, 0)).2) := Prod.ext hlastMove rfl
        rw [← hpair]
        exact hsplit.symm
      rw [heq, @bestCount_append_verifier (ρ₀ n)]
      refine congrArg (fun f => bestCount _ f _) (funext₂ fun c t => ?_)
      dsimp only [dec₁, truncDec]
      rw [ite_eq_left hodd, BitString.listRow_zero, hlen1]
    · dsimp only [g₁, truncShape]
      rw [ite_eq_right hodd]
      refine congrArg (fun f => bestCount _ f _) (funext₂ fun c t => ?_)
      dsimp only [dec₁, truncDec]
      rw [ite_eq_right hodd]
  refine ⟨gsAM g₀ ρ₀, gsVAM enc g₀ ρ₀ msg₀ dec₀, fun n => ?_,
    computableInPolyTime_gsAM hgp₀ hρp₀,
    computableInPolyTime_gsVAM hgp₀ hρp₀ hmsg₀ hdec₀, ?_⟩
  · have hlen : (g₀ n).length = k n := by
      have hL := congrArg List.length (hg₀ n)
      simpa only [List.length_map, length_alternatingMoves] using hL
    have hrep_pat : (repeatShape (gsR g₁ ρ₀ n) (g₁ n)).map Prod.fst =
        (alternatingMoves .arthur (2 * (k n / 2))).map AMMove.toIP := by
      simp [repeatShape, List.map_map, Function.comp_def, hg₁_pat n]
    have hbase := map_fst_mergeMerlin_emulation (gsB g₁ ρ₀ n) (gsZ g₁ ρ₀ n) (gsR g₁ ρ₀ n * ρ₀ n)
      (k n / 2) (repeatShape (gsR g₁ ρ₀ n) (g₁ n)) hrep_pat
    have hbase' : (AMGame.mergeMerlin (shape (gsB g₁ ρ₀ n) (gsZ g₁ ρ₀ n)
        (gsRep g₁ ρ₀ n))).map Prod.fst = alternatingMoves .arthur (2 * (k n / 2) + 2) := hbase
    by_cases hodd : (g₀ n).length % 2 = 1
    · have hsub : k n = 2 * (k n / 2) + 1 := by omega
      dsimp only [gsAM]
      rw [ite_eq_left hodd, List.map_append]
      change (AMGame.mergeMerlin (shape (gsB g₁ ρ₀ n) (gsZ g₁ ρ₀ n)
        (gsRep g₁ ρ₀ n))).map Prod.fst ++ [AMMove.arthur] = alternatingMoves .arthur (k n + 2)
      rw [hbase']
      conv_rhs =>
        rw [hsub, show 2 * (k n / 2) + 1 + 2 = 2 * (k n / 2 + 1) + 1 by omega,
          alternatingMoves_two_mul_add_one]
      have htwo : 2 * (k n / 2 + 1) = 2 * (k n / 2) + 2 := by omega
      rw [htwo]
    · have hsub : k n = 2 * (k n / 2) := by omega
      dsimp only [gsAM]
      rw [ite_eq_right hodd]
      change (AMGame.mergeMerlin (shape (gsB g₁ ρ₀ n) (gsZ g₁ ρ₀ n)
        (gsRep g₁ ρ₀ n))).map Prod.fst = alternatingMoves .arthur (k n + 2)
      rw [hbase']
      conv_rhs => rw [hsub]
  · rw [isAMPolyGameVerifier_iff_value]
    intro a
    set n := (enc a).length
    have hvalAM : ∀ f : List Bool → ℚ, AMGame.value true (gsAM g₀ ρ₀ n) f =
        AMGame.value true (shape (gsB g₁ ρ₀ n) (gsZ g₁ ρ₀ n) (gsRep g₁ ρ₀ n)) f := by
      intro f
      dsimp only [gsAM]
      split_ifs
      · rw [AMGame.value_append_arthur_zero, AMGame.value_mergeMerlin]
      · exact AMGame.value_mergeMerlin _ _
    dsimp only [gsVAM]
    simp only [hvalAM]
    have hc_eq : verifierMoves (gsRep g₁ ρ₀ n) = gsC g₁ n := by
      simp [gsRep, gsC, verifierMoves, repeatShape, List.map_append, List.map_map,
        Function.comp_def]
    have hcpos : 0 < verifierMoves (gsRep g₁ ρ₀ n) := by rw [hc_eq]; dsimp [gsC]; omega
    have hW_ge : gsC g₁ n ≤ gsW g₁ ρ₀ n := by
      have hvm : verifierMoves (g₁ n) ≤ (g₁ n).length := by
        simpa [verifierMoves, List.length_map] using
          (List.count_le_length :
            List.count IPMove.verifier ((g₁ n).map Prod.fst) ≤ ((g₁ n).map Prod.fst).length)
      dsimp [gsC, gsW]; omega
    have hg_bits : verifierBits (gsRep g₁ ρ₀ n) ≤ gsB g₁ ρ₀ n := by
      dsimp only [gsRep]
      rw [verifierBits_append, verifierBits_repeatShape, verifierBits_verifier]
      have hnil : verifierBits [] = 0 := rfl
      rw [hnil, Nat.add_zero]
      dsimp only [gsB]
      rw [← Nat.mul_add]
      have := verifierBits_le_transcriptLength (g₁ n)
      exact Nat.mul_le_mul_left _ (by dsimp [gsW]; omega)
    have hκ_le : gsR g₁ ρ₀ n * ρ₀ n - gsR g₁ ρ₀ n ≤ gsB g₁ ρ₀ n :=
      (Nat.sub_le _ _).trans (Nat.mul_le_mul_left _ (by dsimp [gsW]; omega))
    have hN_eq : countFrom (gsRep g₁ ρ₀ n)
        (gsReveal enc g₁ ρ₀ msg₀ dec₁ (gsR g₁ ρ₀) a) [] =
        (bestCount (fun (c' : BitString (ρ₀ n)) j p => msg₀ (a, List.ofFn c', j, p))
          (fun (c' : BitString (ρ₀ n)) t => dec₁ (a, List.ofFn c', t))
          (g₁ n)) ^ gsR g₁ ρ₀ n := by
      change countFrom (repeatShape (gsR g₁ ρ₀ n) (g₁ n) ++ [(.verifier, gsR g₁ ρ₀ n * ρ₀ n)])
        (revealPayoff (gsMsgRep enc g₁ ρ₀ msg₀ (gsR g₁ ρ₀) a)
          (gsDecRep enc g₁ ρ₀ dec₁ (gsR g₁ ρ₀) a)
          (repeatShape (gsR g₁ ρ₀ n) (g₁ n))
          (transcriptLength (repeatShape (gsR g₁ ρ₀ n) (g₁ n)))) [] = _
      rw [countFrom_revealPayoff _ _ _ rfl _]
      exact bestCount_repeat (gsR g₁ ρ₀ n) (ρ₀ n)
        (fun c' j p => msg₀ (a, c', j, p)) (fun c' t => dec₁ (a, c', t)) (g₁ n)
    have hgap : 6 * (72 * verifierMoves (gsRep g₁ ρ₀ n) ^ 2 * (gsB g₁ ρ₀ n + 1) ^ 2) ^
          verifierMoves (gsRep g₁ ρ₀ n) *
        2 ^ gsR g₁ ρ₀ n ≤ 3 ^ gsR g₁ ρ₀ n := by
      rw [hc_eq]
      exact six_mul_pow_mul_two_pow_le_three_pow (by dsimp [gsC]; omega) hW_ge
    have hK_eq : gsK g₁ ρ₀ n =
        Emulation.threshold (verifierMoves (gsRep g₁ ρ₀ n)) (gsB g₁ ρ₀ n) := by
      simp [gsK, hc_eq]
    rw [hK_eq]
    obtain ⟨h1, h2⟩ := hA a
    rw [← hcount₁ a] at h1 h2
    set N₀ := bestCount (fun (c' : BitString (ρ₀ n)) j p => msg₀ (a, List.ofFn c', j, p))
      (fun (c' : BitString (ρ₀ n)) t => dec₁ (a, List.ofFn c', t)) (g₁ n)
    refine ⟨fun ha => ?_, fun ha => ?_⟩
    · refine two_le_three_mul_value (gsB g₁ ρ₀ n) (gsZ g₁ ρ₀ n)
        (gsReveal enc g₁ ρ₀ msg₀ dec₁ (gsR g₁ ρ₀) a) (gsRep g₁ ρ₀ n) hcpos
        (by simp [gsZ, hc_eq]) hg_bits (gsR g₁ ρ₀ n * ρ₀ n - gsR g₁ ρ₀ n) hκ_le ?_
      rw [hN_eq]
      refine two_pow_sub_le ?_
      calc 2 ^ gsR g₁ ρ₀ n * 2 ^ (gsR g₁ ρ₀ n * ρ₀ n)
          = (2 * 2 ^ ρ₀ n) ^ gsR g₁ ρ₀ n := by rw [mul_pow, pow_mul']
        _ ≤ (3 * N₀) ^ gsR g₁ ρ₀ n := Nat.pow_le_pow_left (h1 ha) _
        _ = 3 ^ gsR g₁ ρ₀ n * N₀ ^ gsR g₁ ρ₀ n := mul_pow _ _ _
    · refine three_mul_value_le_one (gsB g₁ ρ₀ n) (gsZ g₁ ρ₀ n)
        (gsReveal enc g₁ ρ₀ msg₀ dec₁ (gsR g₁ ρ₀) a) (gsRep g₁ ρ₀ n) hcpos
        (gsR g₁ ρ₀ n * ρ₀ n - gsR g₁ ρ₀ n) hκ_le ?_
      rw [hN_eq]
      refine le_two_pow_sub ?_
      calc 6 * (72 * verifierMoves (gsRep g₁ ρ₀ n) ^ 2 * (gsB g₁ ρ₀ n + 1) ^ 2) ^
            verifierMoves (gsRep g₁ ρ₀ n) * N₀ ^ gsR g₁ ρ₀ n * 2 ^ gsR g₁ ρ₀ n
          = 6 * (72 * verifierMoves (gsRep g₁ ρ₀ n) ^ 2 * (gsB g₁ ρ₀ n + 1) ^ 2) ^
              verifierMoves (gsRep g₁ ρ₀ n) * 2 ^ gsR g₁ ρ₀ n * N₀ ^ gsR g₁ ρ₀ n := by ring
        _ ≤ 3 ^ gsR g₁ ρ₀ n * N₀ ^ gsR g₁ ρ₀ n := Nat.mul_le_mul_right _ hgap
        _ = (3 * N₀) ^ gsR g₁ ρ₀ n := (mul_pow _ _ _).symm
        _ ≤ (2 ^ ρ₀ n) ^ gsR g₁ ρ₀ n := Nat.pow_le_pow_left (h2 ha) _
        _ = 2 ^ (gsR g₁ ρ₀ n * ρ₀ n) := by rw [← pow_mul, mul_comm]

end Cslib.Complexity
