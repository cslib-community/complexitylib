/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.BPP
public import CslibFrontier.Computability.Complexity.Classes.IP
public import CslibFrontier.Computability.Complexity.Classes.IP.Games.PolyRounds

import CslibFrontier.Computability.Complexity.Classes.IP.OptimalProver
import CslibFrontier.Computability.Complexity.Classes.IP.PSPACE
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Configuration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.QueryBounds
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Foundations.Analysis.ENNRealNatDiv
import CslibFrontier.Foundations.Data.List.Append
import CslibFrontier.Languages.Probabilistic.Oracle.Transcript
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Tactic.EncLen

/-!
# Oracle-model `IP[k]` and polynomial-round equivalence

See `CslibFrontier.Computability.Complexity.Classes.IP.Games.PolyRounds` for the mapped
source citations to [GoldwasserSipser1986] (GS1986).

Every oracle-PPT interactive proof verifier making at most `q(n)` queries can be simulated by a
game-tree private-coin verifier with `2 * q(n)` alternating moves, and conversely every dynamic
`IP[2 * q(n)]` game verifier is realized by a strict oracle-PPT verifier making at most `q(n)`
queries:

* `Cslib.Complexity.IPQueryBounded` and `Cslib.Complexity.IPPolyQueryBounded`: oracle-PPT `IP`
  with constant or input-length-dependent query budgets.
* `Cslib.Complexity.IPQueryBounded_eq_IPk` and `Cslib.Complexity.IPQueryBounded_eq_IPk_odd`:
  `IPQueryBounded enc q = IPk enc (2 * q) = IPk enc (2 * q + 1)`.
* `Cslib.Complexity.IPQueryBounded_zero` and `Cslib.Complexity.IPk_zero_eq_BPP`: zero-query
  interactive proofs and zero-round private-coin games coincide with `BPP`.
* `Cslib.Complexity.IPQueryBounded_eq_AM`: for every `1 ≤ q`, `IPQueryBounded enc q = AM enc`
  [Goldwasser and Sipser][GoldwasserSipser1986], [Babai and Moran][BabaiMoran1988].
* `Cslib.Complexity.IPPolyQueryBounded_eq_IPPolyRounds`,
  `Cslib.Complexity.IPPolyQueryBounded_subset_AMPolyRounds`, and
  `Cslib.Complexity.IP_subset_AMPolyRounds`: `IPPolyQueryBounded enc q = IPPolyRounds enc (2 * q ·)`
  and `IP ⊆ AM[poly]`, carrying Goldwasser–Sipser without round collapse to the full oracle model
  [Arora and Barak][AroraBarak09], [Arora and Barak (2007 draft)][AroraBarak07].

## Main definitions

* `Cslib.Complexity.IPQueryBounded`: oracle-PPT `IP` verifiers with a constant query budget `q`.
* `Cslib.Complexity.IPPolyQueryBounded`: oracle-PPT `IP` verifiers with input-length query budget
  `q : ℕ → ℕ`.

## Main results

* `Cslib.Complexity.IPk_zero_eq_BPP`, `Cslib.Complexity.IPQueryBounded_zero`: `IP[0] = BPP` and
  `IPQueryBounded enc 0 = BPP`.
* `Cslib.Complexity.IPQueryBounded_eq_IPk`, `Cslib.Complexity.IPQueryBounded_eq_IPk_odd`:
  equivalence between `q`-query oracle-PPT verifiers and `2 * q` (or `2 * q + 1`) alternating
  moves.
* `Cslib.Complexity.IPQueryBounded_eq_AM`: for `1 ≤ q`, `IPQueryBounded enc q = AM enc`.
* `Cslib.Complexity.IPPolyQueryBounded_eq_IPPolyRounds`: `IPPolyQueryBounded enc q` equals
  `IPPolyRounds enc (fun n => 2 * q n)` whenever `q` is computable in polynomial time.
* `Cslib.Complexity.IPPolyQueryBounded_subset_AMPolyRounds` and
  `Cslib.Complexity.IP_subset_AMPolyRounds`: `IPPolyQueryBounded enc q ⊆ AMPolyRounds enc`
  `(fun n => 2 * q n + 2)` and every `A ∈ IP enc` lies in `AMPolyRounds enc k`.

## References

* [S. Goldwasser, S. Micali, C. Rackoff, *The knowledge complexity of interactive proof
  systems*][GoldwasserMicaliRackoff1989]
* [S. Goldwasser, M. Sipser, *Private coins versus public coins in interactive proof
  systems*][GoldwasserSipser1986]
* [L. Babai, S. Moran, *Arthur-Merlin games: a randomized proof system, and a hierarchy of
  complexity classes*][BabaiMoran1988]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, web draft of January
  2007][AroraBarak07] (locators unverified)
-/

public section

namespace Cslib.Complexity

open Finset Cslib.Probability Turing.MultiTapeTM

variable {α : Type}

/-- Problems decided by strict oracle-PPT interactive proof verifiers making at most `q` queries to
the prover on every instance. -/
@[expose] def IPQueryBounded (enc : α ↪ List Bool) (q : ℕ) : Set (Set α) :=
  {A | ∃ verifier : α → WordOracleComp Unit Bool,
    IsOraclePPTOn enc encBool verifier ∧
      (∀ a, (verifier a).IsQueryBounded q) ∧
      IsInteractiveProof verifier A (2 / 3) (1 / 3)}

/-- Problems decided by strict oracle-PPT interactive proof verifiers making at most
`q (enc a).length` queries to the prover on each instance `a`. -/
@[expose] def IPPolyQueryBounded (enc : α ↪ List Bool) (q : ℕ → ℕ) : Set (Set α) :=
  {A | ∃ verifier : α → WordOracleComp Unit Bool,
    IsOraclePPTOn enc encBool verifier ∧
      (∀ a, (verifier a).IsQueryBounded (q (enc a).length)) ∧
      IsInteractiveProof verifier A (2 / 3) (1 / 3)}

/-- Constant-query `IP` is `IPPolyQueryBounded` for the constant function. -/
theorem IPQueryBounded_eq_IPPolyQueryBounded (enc : α ↪ List Bool) (q : ℕ) :
    IPQueryBounded enc q = IPPolyQueryBounded enc (fun _ => q) := rfl

/-- Constant-query oracle-PPT interactive proofs are in `IP`. -/
theorem IPQueryBounded_subset_IP (enc : α ↪ List Bool) (q : ℕ) :
    IPQueryBounded enc q ⊆ IP enc :=
  fun _ ⟨verifier, hV, _, hproof⟩ => ⟨verifier, hV, hproof⟩

/-- Polynomial-query oracle-PPT interactive proofs are in `IP`. -/
theorem IPPolyQueryBounded_subset_IP (enc : α ↪ List Bool) (q : ℕ → ℕ) :
    IPPolyQueryBounded enc q ⊆ IP enc :=
  fun _ ⟨verifier, hV, _, hproof⟩ => ⟨verifier, hV, hproof⟩

/-- Every problem in `IP` admits a polynomial query budget. -/
theorem IP_subset_exists_IPPolyQueryBounded {enc : α ↪ List Bool} {A : Set α} (hA : A ∈ IP enc) :
    ∃ c d : ℕ, A ∈ IPPolyQueryBounded enc (fun n => c * (n + 1) ^ d) := by
  obtain ⟨verifier, hV, hproof, c, d, hbounds⟩ := exists_queryBounds_of_mem_IP hA
  exact ⟨c, d, verifier, hV, fun a => (hbounds a).1, hproof⟩

/-! ### `IP[0] = BPP` -/

/-- Zero-round private-coin games coincide with `BPP`. -/
theorem IPk_zero_eq_BPP (enc : α ↪ List Bool) : IPk enc 0 = BPP enc := by
  ext A
  constructor
  · rintro ⟨G, ρ, msg, dec, hG, _, hdec, hA⟩
    have hgnil : G = [] :=
      (List.map_eq_nil_iff (f := Prod.fst)).1 (by simpa [alternatingMoves] using hG)
    subst hgnil
    refine ⟨ρ, fun x => dec (x.1, x.2, []), ?_, fun a => ?_⟩
    · have ha : ComputableInPolyTime (fun x : α × List Bool => x.1)
          (encPair enc encBits) enc := .fst _ _
      have hc : ComputableInPolyTime (fun x : α × List Bool => x.2)
          (encPair enc encBits) encBits := .snd _ _
      exact hdec.comp (ha.prod (hc.prod (ComputableInPolyTime.const [])))
    · have hbest : IPGame.countAt enc [] ρ msg dec a =
          #(univ.filter fun c : BitString (ρ.eval (enc a).length) =>
            dec (a, List.ofFn c, []) = true) := by
        simp [IPGame.countAt, IPGame.evalShape, IPGame.bestCount, IPGame.count,
          IPGame.acceptedCoins, IPGame.agrees]
      have ha := hA a
      rw [hbest] at ha
      have hsum := Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (fun r : BitString (ρ.eval (enc a).length) => dec (a, List.ofFn r, []) = true)
      simp only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin] at hsum
      refine ⟨fun h => ha.1 h, fun h => ?_⟩
      have h2 := ha.2 h
      change 2 * 2 ^ ρ.eval (enc a).length ≤
        3 * #(univ.filter fun r : BitString (ρ.eval (enc a).length) =>
          dec (a, List.ofFn r, []) = false)
      omega
  · rintro ⟨p, V, hV, hA⟩
    refine ⟨[], p, fun _ => [], fun x => V (x.1, x.2.1), rfl,
      ComputableInPolyTime.const [], ?_, fun a => ?_⟩
    · have ha : ComputableInPolyTime (fun x : α × List Bool × List Bool => x.1)
          (IPGame.encDecInput enc) enc := .fst _ _
      have hc : ComputableInPolyTime (fun x : α × List Bool × List Bool => x.2.1)
          (IPGame.encDecInput enc) encBits := (ComputableInPolyTime.fst _ _).comp (.snd _ _)
      exact hV.comp (ha.prod hc)
    · have hbest : IPGame.countAt enc [] p (fun _ => []) (fun x => V (x.1, x.2.1)) a =
          #(univ.filter fun c : BitString (p.eval (enc a).length) =>
            V (a, List.ofFn c) = true) := by
        simp [IPGame.countAt, IPGame.evalShape, IPGame.bestCount, IPGame.count,
          IPGame.acceptedCoins, IPGame.agrees]
      rw [hbest]
      have hsum := Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (fun r : BitString (p.eval (enc a).length) => V (a, List.ofFn r) = true)
      simp only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin] at hsum
      refine ⟨fun h => (hA a).1 h, fun h => ?_⟩
      have h2 : BoundedErrorAt enc p V a false := (hA a).2 h
      change 2 * 2 ^ p.eval (enc a).length ≤
        3 * #(univ.filter fun r : BitString (p.eval (enc a).length) =>
          V (a, List.ofFn r) = false) at h2
      omega

/-! ### Bounded history extraction and polynomial-time helpers -/

private theorem computableInPolyTime_encodeWord :
    ComputableInPolyTime (fun p : ℕ × List Bool => Interaction.encodeWord p.1 p.2)
      (encPair encUnary encBits) encBits := by
  have hL : ComputableInPolyTime (fun p : ℕ × List Bool => p.1)
      (encPair encUnary encBits) encUnary := .fst _ _
  have hw : ComputableInPolyTime (fun p : ℕ × List Bool => p.2)
      (encPair encUnary encBits) encBits := .snd _ _
  have hlen : ComputableInPolyTime (fun p : ℕ × List Bool => p.2.length)
      (encPair encUnary encBits) encUnary :=
    ComputableInPolyTime.length_bits.comp hw
  have hrep : ComputableInPolyTime
      (fun p : ℕ × List Bool => List.replicate (p.1 - p.2.length) false)
      (encPair encUnary encBits) encBits :=
    (ComputableInPolyTime.bitsReplicate false).comp (ComputableInPolyTime.unary_sub' hL hlen)
  have hcons : ComputableInPolyTime (fun p : ℕ × List Bool => [true] ++ p.2)
      (encPair encUnary encBits) encBits :=
    ComputableInPolyTime.bitsAppend (ComputableInPolyTime.const [true]) hw
  exact (ComputableInPolyTime.bitsAppend hrep hcons).of_enc_eq fun p => by
    simp [Interaction.encodeWord]


/-- State for extracting interaction history from a transcript. -/
private structure ExtractState where
  /-- Remaining transcript to parse. -/
  rem : List Bool
  /-- Accumulated interaction history so far. -/
  hist : Interaction.History
  /-- Whether parsing is still successful. -/
  ok : Bool
  deriving Repr, DecidableEq

/-- Encoding for `ExtractState`. -/
private enc_structure encExtractState : ExtractState where
  rem : encBits, hist : Interaction.encHistory, ok : encBool

/-- State for simulating the interactive protocol. -/
private structure SimState where
  /-- The current round number. -/
  round : ℕ
  /-- The interaction transcript so far. -/
  transcript : List Bool
  deriving Repr, DecidableEq

/-- Encoding for `SimState`. -/
private enc_structure encSimState : SimState where
  round : encUnary, transcript : encBits


/-- One step of decoding a transcript prefix into a `History`. Stops (`ok := false`) once a
chunk starts with `false` or fewer than `2 * t + 3` bits remain. -/
private def extractStep (t : ℕ) (st : ExtractState) : ExtractState :=
  let ⟨rem, hist, ok⟩ := st
  if ok && decide (2 * t + 3 ≤ rem.length) && rem.getD 0 false then
    let m := Interaction.decodeWord ((rem.take (t + 2)).drop 1)
    let y := Interaction.decodeWord ((rem.drop (t + 2)).take (t + 1))
    ⟨rem.drop (2 * t + 3), hist ++ [(m, y)], true⟩
  else
    ⟨rem, hist, false⟩

/-- Decode a transcript prefix into a query-reply `History`, halting at the first padded round
whose verifier tag bit is `false`. -/
private def extractHistory (t : ℕ) (p : List Bool) : Interaction.History :=
  ((List.replicate p.length false).foldl (fun st _ => extractStep t st)
    (ExtractState.mk p [] true)).hist

private theorem length_decodeWord_le_length (u : List Bool) :
    (Interaction.decodeWord u).length ≤ u.length := by
  simp only [Interaction.decodeWord, List.length_drop]
  exact Nat.sub_le _ _

private theorem computableInPolyTime_extractHistory {γ : Type} {encIn : γ ↪ List Bool}
    {t : γ → ℕ} {p : γ → List Bool}
    (ht : ComputableInPolyTime t encIn encUnary)
    (hp : ComputableInPolyTime p encIn encBits) :
    ComputableInPolyTime (fun x => extractHistory (t x) (p x))
      encIn Interaction.encHistory := by
  let encSt : ExtractState ↪ List Bool := encExtractState
  let encStep : ((ℕ × ExtractState) × Bool) ↪ List Bool :=
    encFoldStep encUnary encSt encBool
  have hstep : ComputableInPolyTime
      (fun q : (ℕ × ExtractState) × Bool => extractStep q.1.1 q.1.2)
      encStep encSt := by
    have htq : ComputableInPolyTime
        (fun q : (ℕ × ExtractState) × Bool => q.1.1)
        encStep encUnary :=
      (ComputableInPolyTime.fst _ _).comp (.fst _ _)
    have hrem : ComputableInPolyTime
        (fun q : (ℕ × ExtractState) × Bool => q.1.2.rem)
        encStep encBits :=
      encExtractState_rem_polyTime ((ComputableInPolyTime.snd _ _).comp (.fst _ _))
    have hhist : ComputableInPolyTime
        (fun q : (ℕ × ExtractState) × Bool => q.1.2.hist)
        encStep Interaction.encHistory :=
      encExtractState_hist_polyTime ((ComputableInPolyTime.snd _ _).comp (.fst _ _))
    have hok : ComputableInPolyTime
        (fun q : (ℕ × ExtractState) × Bool => q.1.2.ok)
        encStep encBool :=
      encExtractState_ok_polyTime ((ComputableInPolyTime.snd _ _).comp (.fst _ _))
    have h2t3 : ComputableInPolyTime
        (fun q : (ℕ × ExtractState) × Bool => 2 * q.1.1 + 3)
        encStep encUnary :=
      ComputableInPolyTime.unary_add'
        (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2) htq)
        (ComputableInPolyTime.const 3)
    have ht2 : ComputableInPolyTime
        (fun q : (ℕ × ExtractState) × Bool => q.1.1 + 2)
        encStep encUnary :=
      ComputableInPolyTime.unary_add' htq (ComputableInPolyTime.const 2)
    have ht1 : ComputableInPolyTime
        (fun q : (ℕ × ExtractState) × Bool => q.1.1 + 1)
        encStep encUnary :=
      ComputableInPolyTime.unary_add' htq (ComputableInPolyTime.const 1)
    have hlen : ComputableInPolyTime
        (fun q : (ℕ × ExtractState) × Bool => q.1.2.rem.length)
        encStep encUnary :=
      ComputableInPolyTime.length_bits.comp hrem
    have hle : ComputableInPolyTime
        (fun q : (ℕ × ExtractState) × Bool =>
          decide (2 * q.1.1 + 3 ≤ q.1.2.rem.length)) encStep encBool :=
      .of_tidy (ComputableTidilyInPolyTime.unary_le' h2t3.tidy hlen.tidy)
    have hhead : ComputableInPolyTime
        (fun q : (ℕ × ExtractState) × Bool => q.1.2.rem.getD 0 false)
        encStep encBool :=
      ComputableInPolyTime.bitsGetDWithInput hrem (ComputableInPolyTime.const 0) false
    have hcond : ComputableInPolyTime
        (fun q : (ℕ × ExtractState) × Bool =>
          q.1.2.ok && decide (2 * q.1.1 + 3 ≤ q.1.2.rem.length) && q.1.2.rem.getD 0 false)
        encStep encBool :=
      ComputableInPolyTime.bool_and' (ComputableInPolyTime.bool_and' hok hle) hhead
    have hm : ComputableInPolyTime
        (fun q : (ℕ × ExtractState) × Bool =>
          Interaction.decodeWord ((q.1.2.rem.take (q.1.1 + 2)).drop 1))
        encStep encBits :=
      Interaction.computableInPolyTime_decodeWord.comp
        (ComputableInPolyTime.bitsDropWithInput
          (ComputableInPolyTime.bitsTakeWithInput hrem ht2) (ComputableInPolyTime.const 1))
    have hy : ComputableInPolyTime
        (fun q : (ℕ × ExtractState) × Bool =>
          Interaction.decodeWord ((q.1.2.rem.drop (q.1.1 + 2)).take (q.1.1 + 1)))
        encStep encBits :=
      Interaction.computableInPolyTime_decodeWord.comp
        (ComputableInPolyTime.bitsTakeWithInput
          (ComputableInPolyTime.bitsDropWithInput hrem ht2) ht1)
    have hrem' : ComputableInPolyTime
        (fun q : (ℕ × ExtractState) × Bool =>
          q.1.2.rem.drop (2 * q.1.1 + 3))
        encStep encBits :=
      ComputableInPolyTime.bitsDropWithInput hrem h2t3
    have hhist' : ComputableInPolyTime
        (fun q : (ℕ × ExtractState) × Bool =>
          q.1.2.hist ++ [(Interaction.decodeWord ((q.1.2.rem.take (q.1.1 + 2)).drop 1),
            Interaction.decodeWord ((q.1.2.rem.drop (q.1.1 + 2)).take (q.1.1 + 1)))])
        encStep Interaction.encHistory :=
      ComputableInPolyTime.listAppend' hhist ((hm.prod hy).cons' (ComputableInPolyTime.const []))
    exact (hcond.ite (encExtractState_mk_polyTime hrem' hhist' (ComputableInPolyTime.const true))
      (encExtractState_mk_polyTime hrem hhist
        (ComputableInPolyTime.const false))).of_enc_eq fun q => rfl
  obtain ⟨c, d, hplen⟩ := hp.polyBounded_length.exists_le
  have hlist : ComputableInPolyTime (fun x => List.replicate (p x).length false) encIn encBits :=
    (ComputableInPolyTime.bitsReplicate false).comp (ComputableInPolyTime.length_bits.comp hp)
  have hinit : ComputableInPolyTime (fun x => ExtractState.mk (p x) ([] : Interaction.History) true)
      encIn encSt :=
    encExtractState_mk_polyTime hp (ComputableInPolyTime.const ([] : Interaction.History))
      (ComputableInPolyTime.const true)
  have hspec := ComputableInPolyTime.foldlWith_spec
    (encP := encUnary) (encB := encSt) (encA := encBool) (encL := encBits)
    (par := t) (list := fun x => List.replicate (p x).length false)
    (init := fun x => ExtractState.mk (p x) ([] : Interaction.History) true)
    (step := fun t' st _ => extractStep t' st)
    ht hlist hinit hstep
    (fun x _ st => 6 * st.rem.length + (Interaction.encHistory st.hist).length ≤
      6 * (p x).length + 1)
    (fun x => by simp [Interaction.encHistory, encList_nil])
    (fun x _ st _ _ hs => by
      rcases st with ⟨rem, hist, ok⟩
      dsimp only at hs
      dsimp only [extractStep]
      split_ifs with hif
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at hif
        obtain ⟨⟨_, hlen⟩, _⟩ := hif
        have hmLen : (Interaction.decodeWord ((rem.take (t x + 2)).drop 1)).length ≤ t x + 1 :=
          (length_decodeWord_le_length _).trans (by
            simp only [List.length_drop, List.length_take]
            omega)
        have hyLen : (Interaction.decodeWord ((rem.drop (t x + 2)).take (t x + 1))).length ≤
            t x + 1 :=
          (length_decodeWord_le_length _).trans (by
            simp only [List.length_take]
            exact Nat.min_le_left _ _)
        have hencAppend : ∀ (h : Interaction.History) (e : List Bool × List Bool),
            (Interaction.encHistory (h ++ [e])).length + 1 ≤
              (Interaction.encHistory h).length +
                (frame (encPair encBits encBits e)).length + 1 := by
          intro h e
          simp only [Interaction.encHistory, encList_append, encList_cons, encList_nil,
            List.append_nil, List.length_append]
          omega
        have hframe : (frame (encPair encBits encBits
            (Interaction.decodeWord ((rem.take (t x + 2)).drop 1),
             Interaction.decodeWord ((rem.drop (t x + 2)).take (t x + 1))))).length ≤
            8 * t x + 15 := by
          rw [length_frame, length_encPair]
          simp only [encBits_apply]
          omega
        have happ := hencAppend hist
          (Interaction.decodeWord ((rem.take (t x + 2)).drop 1),
           Interaction.decodeWord ((rem.drop (t x + 2)).take (t x + 1)))
        have hdrop : (rem.drop (2 * t x + 3)).length = rem.length - (2 * t x + 3) :=
          List.length_drop
        dsimp only
        rw [hdrop]
        omega
      · exact hs)
    (size := fun x => 12 * (c * ((encIn x).length + 1) ^ d) + 6)
    (PolyBounded.of_forall_le (12 * c + 6) d fun x => by
      have h1 : 1 ≤ ((encIn x).length + 1) ^ d := Nat.one_le_pow _ _ (Nat.succ_pos _)
      nlinarith)
    (fun x _ st _ hs => by
      have hp' := hplen x
      simp only [encBits_apply] at hp'
      have hstLen : (encSt st).length =
          2 * st.rem.length + 1 + 2 * (Interaction.encHistory st.hist).length + 1 + 1 := by
        change (encExtractState st).length = _
        simp only [encExtractState_apply, encExtractStateFields, length_encPair,
          encBits_apply, encBool_apply, List.length_singleton, Nat.add_assoc]
      omega)
  exact encExtractState_hist_polyTime hspec.1

private theorem foldl_extractStep_false (t k : ℕ) (rem : List Bool) (hist : Interaction.History) :
    ((List.replicate k false).foldl (fun st _ => extractStep t st) ⟨rem, hist, false⟩).hist =
      hist := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [List.replicate_succ, extractStep] using ih

private theorem foldl_extractStep_append (t k : ℕ) (v w rest : List Bool)
    (hist : Interaction.History)
    (hv : v.length = t + 2) (hw : w.length = t + 1) (hk : 1 ≤ k) :
    ((List.replicate k false).foldl (fun st _ => extractStep t st)
      ⟨v ++ w ++ rest, hist, true⟩).hist =
      if v.headD false then
        ((List.replicate (k - 1) false).foldl (fun st _ => extractStep t st)
          ⟨rest, hist ++ [(Interaction.decodeWord (v.drop 1), Interaction.decodeWord w)],
            true⟩).hist
      else hist := by
  cases k with
  | zero => omega
  | succ k' =>
    simp only [List.replicate_succ, List.foldl_cons]
    have hlen : 2 * t + 3 ≤ (v ++ w ++ rest).length := by
      simp only [List.length_append, hv, hw]
      omega
    have hhead : (v ++ w ++ rest).getD 0 false = v.headD false := by
      cases v with
      | nil => simp at hv
      | cons b vs => rfl
    dsimp only [extractStep]
    simp only [hlen, decide_true, Bool.true_and, hhead]
    split_ifs with h
    · have hm : ((v ++ w ++ rest).take (t + 2)).drop 1 = v.drop 1 := by
        rw [List.append_assoc, List.take_left' hv]
      have hy : ((v ++ w ++ rest).drop (t + 2)).take (t + 1) = w := by
        rw [List.append_assoc, List.drop_left' hv, List.take_left' hw]
      have hdrop : (v ++ w ++ rest).drop (2 * t + 3) = rest :=
        List.drop_left' (show (v ++ w).length = 2 * t + 3 by
          simp only [List.length_append, hv, hw]; omega)
      rw [hm, hy, hdrop]
      rfl
    · exact foldl_extractStep_false t k' (v ++ w ++ rest) hist

private theorem foldl_extractStep_length_ge (t k₁ k₂ : ℕ) (rem : List Bool)
    (hist : Interaction.History)
    (hk₁ : rem.length ≤ k₁) (hk₂ : rem.length ≤ k₂) :
    ((List.replicate k₁ false).foldl (fun st _ => extractStep t st) ⟨rem, hist, true⟩).hist =
      ((List.replicate k₂ false).foldl (fun st _ => extractStep t st) ⟨rem, hist, true⟩).hist := by
  induction k₁ generalizing k₂ rem hist with
  | zero =>
    have hr : rem = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hr
    induction k₂ with
    | zero => rfl
    | succ k₂ _ =>
      simp only [List.replicate_succ, List.foldl_cons, extractStep, List.length_nil]
      simp only [show ¬(2 * t + 3 ≤ 0) by omega, decide_false, Bool.and_false, Bool.false_and]
      exact (foldl_extractStep_false t k₂ [] hist).symm
  | succ k₁ ih =>
    cases k₂ with
    | zero =>
      have hr : rem = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hr
      simp only [List.replicate_succ, List.foldl_cons, extractStep, List.length_nil,
        show ¬(2 * t + 3 ≤ 0) by omega, decide_false, Bool.and_false, Bool.false_and,
        List.replicate_zero, List.foldl_nil]
      exact foldl_extractStep_false t k₁ [] hist
    | succ k₂ =>
      simp only [List.replicate_succ, List.foldl_cons]
      by_cases hif : (true && decide (2 * t + 3 ≤ rem.length) && rem.getD 0 false) = true
      · simp only [extractStep, hif, ite_true]
        simp only [Bool.true_and, Bool.and_eq_true, decide_eq_true_eq] at hif
        refine ih k₂ (rem.drop (2 * t + 3)) _ ?_ ?_ <;> (rw [List.length_drop]; omega)
      · have hstep : extractStep t ⟨rem, hist, true⟩ = ⟨rem, hist, false⟩ :=
          ite_eq_right fun h => absurd h hif
        rw [hstep, foldl_extractStep_false, foldl_extractStep_false]

private theorem foldl_extractStep_step_true {t : ℕ} {v w rest : List Bool}
    (hist : Interaction.History) (hv : v.length = t + 2) (hw : w.length = t + 1)
    (htr : v.headD false = true) :
    ((List.replicate (v ++ w ++ rest).length false).foldl (fun st _ => extractStep t st)
      ⟨v ++ w ++ rest, hist, true⟩).hist =
      ((List.replicate rest.length false).foldl (fun st _ => extractStep t st)
        ⟨rest, hist ++ [(Interaction.decodeWord (v.drop 1), Interaction.decodeWord w)],
          true⟩).hist := by
  have h1 := foldl_extractStep_append t (v ++ w ++ rest).length v w rest hist hv hw (by
    simp only [List.length_append, hv, hw]; omega)
  rw [htr] at h1
  simp only [reduceIte] at h1
  rw [h1]
  exact foldl_extractStep_length_ge t _ rest.length rest _ (by
    simp only [List.length_append, hv, hw]; omega) le_rfl

private theorem foldl_extractStep_step_false {t : ℕ} {v w rest : List Bool}
    (hist : Interaction.History) (hv : v.length = t + 2) (hw : w.length = t + 1)
    (hf : v.headD false = false) :
    ((List.replicate (v ++ w ++ rest).length false).foldl (fun st _ => extractStep t st)
      ⟨v ++ w ++ rest, hist, true⟩).hist = hist := by
  have h1 := foldl_extractStep_append t (v ++ w ++ rest).length v w rest hist hv hw (by
    simp only [List.length_append, hv, hw]; omega)
  rw [hf] at h1
  exact h1

private theorem foldl_extractStep_nil (t k : ℕ) (hist : Interaction.History) :
    ((List.replicate k false).foldl (fun st _ => extractStep t st) ⟨[], hist, true⟩).hist =
      hist := by
  cases k with
  | zero => rfl
  | succ k =>
    simp only [List.replicate_succ, List.foldl_cons, extractStep, List.length_nil,
      show ¬(2 * t + 3 ≤ 0) by omega, decide_false, Bool.and_false, Bool.false_and]
    exact foldl_extractStep_false t k [] hist

/-! ### Query budget bounds coin-family rounds -/

private theorem after_map {γ δ : Type} (f : γ → δ) (p : WordQueryComp Unit γ)
    (h : Interaction.History) :
    Interaction.after (f <$> p) h = (Interaction.after p h).map (f <$> ·) := by
  induction p generalizing h with
  | pure a =>
    cases h with
    | nil => rfl
    | cons _ _ => rfl
  | liftBind q next ih =>
    cases h with
    | nil => rfl
    | cons x h =>
      obtain ⟨m, y⟩ := x
      change (if m = q.2 then Interaction.after (f <$> next y) h else none) =
        Option.map (f <$> ·) (if m = q.2 then Interaction.after (next y) h else none)
      split_ifs
      · exact ih y h
      · rfl

private theorem exists_transcript_ge_of_after {γ : Type} (p : WordQueryComp Unit γ)
    (h : Interaction.History) (tr : OracleComp.Transcript (fun _ : Unit × List Bool => List Bool))
    (m : List Bool) (next : List Bool → WordQueryComp Unit γ)
    (hafter : Interaction.after p h = some (.liftBind ((), m) next)) :
    let oracle : Unit × List Bool → StateT Interaction.History PMF (List Bool) :=
      fun _ rem => match rem with | [] => PMF.pure ([], []) | (_, y) :: rem' => PMF.pure (y, rem')
    ∃ out s' tr', (out, s', tr') ∈
      ((OracleComp.interpret (OracleComp.withTranscript oracle) p).run (h, tr)).support ∧
      tr.length + h.length + 1 ≤ tr'.length := by
  intro oracle
  induction h generalizing p tr with
  | nil =>
    rw [Interaction.after_nil, Option.some.injEq] at hafter
    have hq : (PFunctor.FreeM.liftBind ((), m) next : WordQueryComp Unit γ) =
        OracleComp.query ((), m) >>= next := rfl
    rw [hafter, hq, OracleComp.interpret_bind, OracleComp.interpret_query, StateT.run_bind]
    have hq : (OracleComp.withTranscript oracle ((), m)).run ([], tr) =
        PMF.pure ([], [], ⟨((), m), []⟩ :: tr) := by
      simp [OracleComp.withTranscript, oracle, StateT.run]
    rw [hq, Probability.PMF.monad_bind_eq_bind, PMF.pure_bind]
    obtain ⟨⟨out, s', tr'⟩, hmem⟩ := PMF.support_nonempty
      ((OracleComp.interpret (OracleComp.withTranscript oracle) (next [])).run
        ([], ⟨((), m), []⟩ :: tr))
    have hlen : (⟨((), m), []⟩ :: tr).length ≤ tr'.length := by
      have happ := OracleComp.run_interpret_withTranscript_append oracle (next [])
        ([] : Interaction.History) (⟨((), m), []⟩ :: tr)
      have hmem' := hmem
      rw [happ, PMF.mem_support_map_iff] at hmem'
      obtain ⟨⟨_, _, fresh⟩, _, hrec⟩ := hmem'
      have htr : fresh ++ (⟨((), m), []⟩ :: tr) = tr' := congrArg (·.2.2) hrec
      rw [← htr, List.length_append]
      omega
    exact ⟨out, s', tr', hmem, by
      simp only [List.length_nil, add_zero]
      simp only [List.length_cons] at hlen
      omega⟩
  | cons e h ih =>
    obtain ⟨m', y'⟩ := e
    cases p with
    | pure a => simp at hafter
    | liftBind q cont =>
      obtain ⟨⟨⟩, m0⟩ := q
      change (if m' = m0 then Interaction.after (cont y') h else none) = _ at hafter
      split_ifs at hafter with hm
      · subst hm
        obtain ⟨out, s', tr', hmem, hlen⟩ := ih (cont y') (⟨((), m'), y'⟩ :: tr) hafter
        refine ⟨out, s', tr', ?_, by simp only [List.length_cons] at hlen ⊢; omega⟩
        have hq' : (PFunctor.FreeM.liftBind ((), m') cont : WordQueryComp Unit γ) =
            OracleComp.query ((), m') >>= cont := rfl
        rw [hq', OracleComp.interpret_bind, OracleComp.interpret_query, StateT.run_bind]
        have hq : (OracleComp.withTranscript oracle ((), m')).run ((m', y') :: h, tr) =
            PMF.pure (y', h, ⟨((), m'), y'⟩ :: tr) := by
          simp [OracleComp.withTranscript, oracle, StateT.run]
        rw [hq, Probability.PMF.monad_bind_eq_bind, PMF.pure_bind]
        exact hmem

/-- If a machine-realized oracle verifier has query budget `D`, its fixed-coin family has
`rounds` bounded by `D`. -/
private theorem isBounded_coinFamily_of_isQueryBounded {k : ℕ} {Control : Type}
    (MUnit : Turing.MultiTapePTM k Bool Control Unit) {V : WordOracleComp Unit Bool} {t : ℕ}
    {x : List Bool} {D : ℕ}
    (hbound : V.IsQueryBounded D)
    (hreal : ∀ (State : Type) (oracle : Unit × List Bool → StateT State PMF (List Bool))
      (s : State),
      (OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        (encBool <$> V)).run s =
      (OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        (MUnit.runOracle t x)).run s) :
    Interaction.IsBounded (Interaction.coinFamily MUnit t x) D t where
  rounds r₀ h m hm := by
    by_contra hge
    have hD : D ≤ h.length := Nat.le_of_not_lt hge
    let F := Interaction.coinFamily MUnit t x
    dsimp only [Interaction.outcome] at hm
    change (match Interaction.after (F r₀) h with
      | none => Interaction.Outcome.invalid
      | some (.pure b) => .done b
      | some (.liftBind q _) => .ask q.2) = .ask m at hm
    cases hah : Interaction.after (F r₀) h with
    | none => simp [hah] at hm
    | some p0 =>
      cases p0 with
      | pure b => simp [hah] at hm
      | liftBind q cont =>
        obtain ⟨⟨⟩, m0⟩ := q
        rw [hah] at hm
        simp only [Interaction.Outcome.ask.injEq] at hm
        subst hm
        have hah' : Interaction.after ((fun cfg => decide (cfg.tapes.output = [true])) <$>
            (List.ofFn r₀).foldlM (Interaction.coinStep MUnit t)
              (Turing.MultiTapeMachine.FiniteConfig.init MUnit.initial x)) h =
            some (.liftBind ((), m0) cont) := hah
        rw [after_map] at hah'
        cases hcore : Interaction.after
            ((List.ofFn r₀).foldlM (Interaction.coinStep MUnit t)
              (Turing.MultiTapeMachine.FiniteConfig.init MUnit.initial x)) h with
        | none => simp [hcore] at hah'
        | some pc =>
          simp only [hcore, Option.map_some, Option.some.injEq] at hah'
          cases pc with
          | pure cfg =>
            change PFunctor.FreeM.pure _ = PFunctor.FreeM.liftBind _ _ at hah'
            cases hah'
          | liftBind q' cont' =>
            obtain ⟨⟨⟩, m'⟩ := q'
            dsimp only [Functor.map, PFunctor.FreeM.map] at hah'
            have hm' : m' = m0 := by cases hah'; rfl
            subst hm'
            have hmap : Interaction.after
                ((fun cfg => cfg.tapes.output) <$>
                  (List.ofFn r₀).foldlM (Interaction.coinStep MUnit t)
                    (Turing.MultiTapeMachine.FiniteConfig.init MUnit.initial x)) h =
                some (.liftBind ((), m') fun y => (fun cfg => cfg.tapes.output) <$> cont' y) := by
              rw [after_map, hcore]; rfl
            let oracle : Unit × List Bool → StateT Interaction.History PMF (List Bool) :=
              fun _ rem => match rem with
                | [] => PMF.pure ([], [])
                | (_, y) :: rem' => PMF.pure (y, rem')
            obtain ⟨out, s', tr, hmem, htr⟩ :=
              exists_transcript_ge_of_after _ h [] m' _ hmap
            have hmemM : (out, s', tr) ∈
                ((OracleComp.interpret
                  (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n))
                    (OracleComp.withTranscript oracle))
                  (MUnit.runOracle t x)).run (h, [])).support := by
              rw [Interaction.run_interpret_runOracle_eq_coins, PMF.mem_support_bind_iff]
              refine ⟨List.ofFn r₀, ?_, hmem⟩
              rw [BitString.uniformList, PMF.mem_support_map_iff]
              exact ⟨r₀, by simp, rfl⟩
            rw [← hreal _ (OracleComp.withTranscript oracle) (h, [])] at hmemM
            rw [OracleComp.interpret_map, StateT.run_map, _root_.PMF.monad_map_eq_map,
              PMF.mem_support_map_iff] at hmemM
            obtain ⟨⟨res, sV, trV⟩, hmemV, hres⟩ := hmemM
            have htrV : trV = tr := congrArg (·.2.2) hres
            have hsV : sV = s' := congrArg (·.2.1) hres
            subst htrV hsV
            have hlen := hbound.length_transcript_le oracle hmemV
            omega
  message := (Interaction.isBounded_coinFamily MUnit t x).message
  reply := (Interaction.isBounded_coinFamily MUnit t x).reply

/-! ### Simulation of `IPPolyQueryBounded` in `IPPolyRounds (2 * q ·)` -/

section SimGame

private noncomputable def simMsg (enc : α ↪ List Bool) {k : ℕ} {Control : Type}
    (MUnit : Turing.MultiTapePTM k Bool Control Unit) (t : ℕ → ℕ)
    (x : α × List Bool × ℕ × List Bool) : List Bool :=
  let n := (enc x.1).length
  let h := extractHistory (t n) x.2.2.2
  let s := Interaction.aliveRun (fun _ _ => true) id MUnit (enc x.1) x.2.1 h
  if s.2.2 then List.replicate (t n + 2) false
  else [true] ++ Interaction.encodeWord (t n) (s.1.channels ()).1

private noncomputable def simDec (enc : α ↪ List Bool) {k : ℕ} {Control : Type}
    (MUnit : Turing.MultiTapePTM k Bool Control Unit) (t : ℕ → ℕ)
    (x : α × List Bool × List Bool) : Bool :=
  let n := (enc x.1).length
  Interaction.accepts (fun _ _ => true) id MUnit (enc x.1) x.2.1
    (extractHistory (t n) x.2.2)

private theorem computableInPolyTime_simMsg {enc : α ↪ List Bool} {k : ℕ} {Control : Type}
    [Finite Control] (MUnit : Turing.MultiTapePTM k Bool Control Unit) {t : ℕ → ℕ}
    (ht : ComputableInPolyTime t encUnary encUnary) :
    ComputableInPolyTime (simMsg enc MUnit t) (IPGame.encMsgInput enc) encBits := by
  have ha : ComputableInPolyTime (fun x : α × List Bool × ℕ × List Bool => x.1)
      (IPGame.encMsgInput enc) enc := .fst _ _
  have hxa : ComputableInPolyTime (fun x : α × List Bool × ℕ × List Bool => enc x.1)
      (IPGame.encMsgInput enc) encBits :=
    (ComputableInPolyTime.of_eq fun _ => rfl).comp ha
  have hn : ComputableInPolyTime (fun x : α × List Bool × ℕ × List Bool => (enc x.1).length)
      (IPGame.encMsgInput enc) encUnary :=
    (ComputableInPolyTime.encoding_length enc).comp ha
  have htn : ComputableInPolyTime (fun x : α × List Bool × ℕ × List Bool => t (enc x.1).length)
      (IPGame.encMsgInput enc) encUnary := ht.comp hn
  have hc : ComputableInPolyTime (fun x : α × List Bool × ℕ × List Bool => x.2.1)
      (IPGame.encMsgInput enc) encBits :=
    (ComputableInPolyTime.fst _ _).comp (.snd _ _)
  have hp : ComputableInPolyTime (fun x : α × List Bool × ℕ × List Bool => x.2.2.2)
      (IPGame.encMsgInput enc) encBits :=
    (ComputableInPolyTime.snd _ _).comp ((ComputableInPolyTime.snd _ _).comp (.snd _ _))
  have hh : ComputableInPolyTime
      (fun x : α × List Bool × ℕ × List Bool =>
        extractHistory (t (enc x.1).length) x.2.2.2)
      (IPGame.encMsgInput enc) Interaction.encHistory :=
    computableInPolyTime_extractHistory htn hp
  have halive : ComputableInPolyTime
      (fun x : α × List Bool × ℕ × List Bool =>
        Interaction.aliveRun (fun _ _ => true) id MUnit (enc x.1) x.2.1
          (extractHistory (t (enc x.1).length) x.2.2.2))
      (IPGame.encMsgInput enc) (Interaction.encAliveState (encPair encBits encBits)) := by
    have hr := Interaction.computableInPolyTime_aliveRun (fun _ _ => true) id MUnit
      (encEntry := encPair encBits encBits) (fun _ => ComputableInPolyTime.const true)
      ComputableInPolyTime.id'
    exact ComputableInPolyTime.comp
      (f := fun p : List Bool × List Bool × Interaction.History =>
        Interaction.aliveRun (fun _ _ => true) id MUnit p.1 p.2.1 p.2.2)
      (g := fun x : α × List Bool × ℕ × List Bool =>
        (enc x.1, x.2.1, extractHistory (t (enc x.1).length) x.2.2.2))
      hr (hxa.prod (hc.prod hh))
  have hlive : ComputableInPolyTime
      (fun x : α × List Bool × ℕ × List Bool =>
        (Interaction.aliveRun (fun _ _ => true) id MUnit (enc x.1) x.2.1
          (extractHistory (t (enc x.1).length) x.2.2.2)).2.2)
      (IPGame.encMsgInput enc) encBool :=
    (ComputableInPolyTime.snd _ _).comp ((ComputableInPolyTime.snd _ _).comp halive)
  have hchan : ComputableInPolyTime
      (fun x : α × List Bool × ℕ × List Bool =>
        ((Interaction.aliveRun (fun _ _ => true) id MUnit (enc x.1) x.2.1
          (extractHistory (t (enc x.1).length) x.2.2.2)).1.channels ()).1)
      (IPGame.encMsgInput enc) encBits := by
    have hcfg : ComputableInPolyTime
        (fun x : α × List Bool × ℕ × List Bool =>
          (Interaction.aliveRun (fun _ _ => true) id MUnit (enc x.1) x.2.1
            (extractHistory (t (enc x.1).length) x.2.2.2)).1)
        (IPGame.encMsgInput enc) encFiniteConfig :=
      (ComputableInPolyTime.fst _ _).comp halive
    have hchs : ComputableInPolyTime
        (fun cfg : Turing.MultiTapeMachine.FiniteConfig k Bool Control Unit =>
          (cfg.channels ()).1)
        encFiniteConfig encBits :=
      (ComputableInPolyTime.fst _ _).comp
        ((ComputableInPolyTime.pi_apply (encPair encBits (encBiTape encBool)) ()).comp
          (ComputableInPolyTime.finiteConfig_channels (k := k) (State := Control)
            (Oracle := Unit)))
    exact hchs.comp hcfg
  have hpad : ComputableInPolyTime
      (fun x : α × List Bool × ℕ × List Bool => List.replicate (t (enc x.1).length + 2) false)
      (IPGame.encMsgInput enc) encBits :=
    (ComputableInPolyTime.bitsReplicate false).comp
      (ComputableInPolyTime.unary_add' htn (ComputableInPolyTime.const 2))
  have hmsg : ComputableInPolyTime
      (fun x : α × List Bool × ℕ × List Bool =>
        [true] ++ Interaction.encodeWord (t (enc x.1).length)
          ((Interaction.aliveRun (fun _ _ => true) id MUnit (enc x.1) x.2.1
            (extractHistory (t (enc x.1).length) x.2.2.2)).1.channels ()).1)
      (IPGame.encMsgInput enc) encBits :=
    ComputableInPolyTime.bitsAppend (ComputableInPolyTime.const [true])
      (computableInPolyTime_encodeWord.comp (htn.prod hchan))
  exact (hlive.ite hpad hmsg).of_enc_eq fun x => rfl

private theorem computableInPolyTime_simDec {enc : α ↪ List Bool} {k : ℕ} {Control : Type}
    [Finite Control] (MUnit : Turing.MultiTapePTM k Bool Control Unit) {t : ℕ → ℕ}
    (ht : ComputableInPolyTime t encUnary encUnary) :
    ComputableInPolyTime (simDec enc MUnit t) (IPGame.encDecInput enc) encBool := by
  have ha : ComputableInPolyTime (fun x : α × List Bool × List Bool => x.1)
      (IPGame.encDecInput enc) enc := .fst _ _
  have hxa : ComputableInPolyTime (fun x : α × List Bool × List Bool => enc x.1)
      (IPGame.encDecInput enc) encBits :=
    (ComputableInPolyTime.of_eq fun _ => rfl).comp ha
  have hn : ComputableInPolyTime (fun x : α × List Bool × List Bool => (enc x.1).length)
      (IPGame.encDecInput enc) encUnary :=
    (ComputableInPolyTime.encoding_length enc).comp ha
  have hc : ComputableInPolyTime (fun x : α × List Bool × List Bool => x.2.1)
      (IPGame.encDecInput enc) encBits :=
    (ComputableInPolyTime.fst _ _).comp (.snd _ _)
  have hp : ComputableInPolyTime (fun x : α × List Bool × List Bool => x.2.2)
      (IPGame.encDecInput enc) encBits :=
    (ComputableInPolyTime.snd _ _).comp (.snd _ _)
  have hh := computableInPolyTime_extractHistory (ht.comp hn) hp
  have hacc := Interaction.computableInPolyTime_accepts (fun _ _ => true) id MUnit
    (encEntry := encPair encBits encBits) (fun _ => ComputableInPolyTime.const true)
    ComputableInPolyTime.id'
  exact (hacc.comp (hxa.prod (hc.prod hh))).of_enc_eq fun _ => rfl

private noncomputable def simGameShape (t q : ℕ) : List (IPMove × ℕ) :=
  (List.replicate q [(.verifier, t + 2), (.prover, t + 1)]).flatten

private theorem simGameShape_map_fst (t q : ℕ) :
    (simGameShape t q).map Prod.fst = (alternatingMoves .arthur (2 * q)).map AMMove.toIP := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [show 2 * (q + 1) = 2 * q + 2 by omega]
    change ([(IPMove.verifier, t + 2), (IPMove.prover, t + 1)] ++ simGameShape t q).map Prod.fst =
      (AMMove.arthur :: AMMove.merlin :: alternatingMoves AMMove.arthur (2 * q)).map AMMove.toIP
    rw [List.map_append, List.map_cons, List.map_cons, ih]
    rfl

private def HistLive (t : ℕ) (p : List Bool) (h : Interaction.History) : Prop :=
  ∀ rem, extractHistory t (p ++ rem) =
    ((List.replicate rem.length false).foldl (fun st _ => extractStep t st) ⟨rem, h, true⟩).hist

private def HistStopped (t : ℕ) (p : List Bool) (h : Interaction.History) : Prop :=
  ∀ rem, extractHistory t (p ++ rem) = h

private theorem histLive_nil (t : ℕ) : HistLive t [] [] := fun rem => by rfl

private theorem histLive_extract {t : ℕ} {p : List Bool} {h : Interaction.History}
    (hp : HistLive t p h) :
    extractHistory t p = h := by
  simpa only [List.append_nil, foldl_extractStep_nil] using hp []

private theorem histStopped_extract {t : ℕ} {p : List Bool} {h : Interaction.History}
    (hp : HistStopped t p h) :
    extractHistory t p = h := by
  simpa only [List.append_nil] using hp []

private theorem histLive_append_true {t : ℕ} {p v w : List Bool} {h : Interaction.History}
    (hp : HistLive t p h) (hv : v.length = t + 2) (hw : w.length = t + 1)
    (htr : v.headD false = true) :
    HistLive t (p ++ v ++ w)
      (h ++ [(Interaction.decodeWord (v.drop 1), Interaction.decodeWord w)]) := by
  intro rem
  have hhp := hp (v ++ w ++ rem)
  rw [← List.append_assoc p (v ++ w) rem, ← List.append_assoc p v w] at hhp
  rw [hhp]
  exact foldl_extractStep_step_true h hv hw htr

private theorem histLive_append_false {t : ℕ} {p v w : List Bool} {h : Interaction.History}
    (hp : HistLive t p h) (hv : v.length = t + 2) (hw : w.length = t + 1)
    (hf : v.headD false = false) :
    HistStopped t (p ++ v ++ w) h := by
  intro rem
  have hhp := hp (v ++ w ++ rem)
  rw [← List.append_assoc p (v ++ w) rem, ← List.append_assoc p v w] at hhp
  rw [hhp]
  exact foldl_extractStep_step_false h hv hw hf

private theorem histStopped_append {t : ℕ} {p ext : List Bool} {h : Interaction.History}
    (hp : HistStopped t p h) :
    HistStopped t (p ++ ext) h := fun rem => by
  rw [List.append_assoc, hp]

private theorem simMsg_of_outcome_ask {enc : α ↪ List Bool} {k : ℕ} {Control : Type}
    (MUnit : Turing.MultiTapePTM k Bool Control Unit) (t : ℕ → ℕ) (a : α)
    (c : BitString (t (enc a).length)) (j : ℕ) {p : List Bool} {h : Interaction.History}
    {m : List Bool} (hp : extractHistory (t (enc a).length) p = h)
    (hout : Interaction.outcome (Interaction.coinFamily MUnit (t (enc a).length) (enc a) c) h =
      .ask m) :
    simMsg enc MUnit t (a, List.ofFn c, j, p) =
      [true] ++ Interaction.encodeWord (t (enc a).length) m := by
  have hsim : Interaction.simulate MUnit (List.ofFn c).length (enc a) (List.ofFn c) h =
      .error (some m) := by
    rw [List.length_ofFn]
    have hc := Interaction.outcome_coinProgram MUnit (t (enc a).length) (enc a) (List.ofFn c) h
    change Interaction.outcome
      (Interaction.coinFamily MUnit (t (enc a).length) (enc a) c) h = _ at hc
    rw [hout] at hc
    rcases hs : Interaction.simulate MUnit (t (enc a).length) (enc a) (List.ofFn c) h with
      (_ | m') | ⟨cfg, _ | ⟨e, rest⟩⟩ <;>
      simp only [hs, Except.map, Interaction.replayOutcome] at hc
    · cases hc
    · simp only [Interaction.Outcome.ask.injEq] at hc
      subst hc
      rfl
    · cases hc
    · cases hc
  obtain ⟨cfg, rem, hcfg, hm⟩ := Interaction.aliveRun_of_simulate_error_some MUnit hsim
  dsimp only [simMsg]
  rw [hp, hcfg, hm]
  rfl

private theorem simMsg_of_outcome_done {enc : α ↪ List Bool} {k : ℕ} {Control : Type}
    (MUnit : Turing.MultiTapePTM k Bool Control Unit) (t : ℕ → ℕ) (a : α)
    (c : BitString (t (enc a).length)) (j : ℕ) {p : List Bool} {h : Interaction.History}
    {b : Bool} (hp : extractHistory (t (enc a).length) p = h)
    (hout : Interaction.outcome (Interaction.coinFamily MUnit (t (enc a).length) (enc a) c) h =
      .done b) :
    simMsg enc MUnit t (a, List.ofFn c, j, p) =
      List.replicate (t (enc a).length + 2) false := by
  have hsim : ∃ cfg,
      Interaction.simulate MUnit (List.ofFn c).length (enc a) (List.ofFn c) h =
        .ok (cfg, []) := by
    rw [List.length_ofFn]
    have hc := Interaction.outcome_coinProgram MUnit (t (enc a).length) (enc a) (List.ofFn c) h
    change Interaction.outcome
      (Interaction.coinFamily MUnit (t (enc a).length) (enc a) c) h = _ at hc
    rw [hout] at hc
    rcases hs : Interaction.simulate MUnit (t (enc a).length) (enc a) (List.ofFn c) h with
      (_ | m') | ⟨cfg, _ | ⟨e, rest⟩⟩ <;>
      simp only [hs, Except.map, Interaction.replayOutcome] at hc
    · cases hc
    · cases hc
    · exact ⟨cfg, rfl⟩
    · cases hc
  obtain ⟨cfg, hcfg⟩ := hsim
  have hal := Interaction.aliveRun_of_simulate_ok MUnit hcfg
  dsimp only [simMsg]
  rw [hp, hal]
  rfl

private theorem after_eq_pure_of_outcome_done {p : WordQueryComp Unit Bool}
    {h : Interaction.History} {b : Bool} (hb : Interaction.outcome p h = .done b) :
    Interaction.after p h = some (.pure b) := by
  unfold Interaction.outcome at hb
  cases ha : Interaction.after p h with
  | none => rw [ha] at hb; cases hb
  | some p0 =>
    cases p0 with
    | pure b' =>
      simp only [ha, Interaction.Outcome.done.injEq] at hb
      subst hb
      rfl
    | liftBind _ _ => rw [ha] at hb; cases hb

private theorem acceptFrom_pure_bool (P : Prover Unit) (s : P.State) (b : Bool) :
    Interaction.acceptFrom P s (some (.pure b)) = if b = true then 1 else 0 := by
  cases b <;> simp [Interaction.acceptFrom]

private theorem simDec_eq_of_outcome_done {enc : α ↪ List Bool} {k : ℕ} {Control : Type}
    (MUnit : Turing.MultiTapePTM k Bool Control Unit) (t : ℕ → ℕ) (a : α)
    (c : BitString (t (enc a).length)) {p : List Bool} {h : Interaction.History} {b : Bool}
    (hp : extractHistory (t (enc a).length) p = h)
    (hout : Interaction.outcome (Interaction.coinFamily MUnit (t (enc a).length) (enc a) c) h =
      .done b) :
    simDec enc MUnit t (a, List.ofFn c, p) = b := by
  dsimp only [simDec]
  rw [hp]
  have hiff := Interaction.accepts_eq_true_iff MUnit (enc a) (List.ofFn c) h
  rw [List.length_ofFn] at hiff
  change Interaction.accepts (fun _ _ => true) id MUnit (enc a) (List.ofFn c) h = true ↔
      Interaction.outcome (Interaction.coinFamily MUnit (t (enc a).length) (enc a) c) h =
        .done true at hiff
  exact Bool.eq_iff_iff.2 (hiff.trans (by simp only [hout, Interaction.Outcome.done.injEq]))

private theorem trace_sim_eq {enc : α ↪ List Bool} {k : ℕ} {Control : Type}
    (MUnit : Turing.MultiTapePTM k Bool Control Unit) (t : ℕ → ℕ) (a : α)
    {D : ℕ} (hF : Interaction.IsBounded (Interaction.coinFamily MUnit (t (enc a).length) (enc a))
      D (t (enc a).length))
    (c : BitString (t (enc a).length)) (PGame : ℕ → List Bool → List Bool)
    (PUnit : Prover Unit)
    (Match : ℕ → List Bool → Interaction.History → PUnit.State → Prop)
    (hstep : ∀ j p h s m, Match j p h s → HistLive (t (enc a).length) p h →
      Interaction.outcome (Interaction.coinFamily MUnit (t (enc a).length) (enc a) c) h =
        .ask m →
      let v := [true] ++ Interaction.encodeWord (t (enc a).length) m
      let w := List.ofFn (BitString.ofList (t (enc a).length + 1) (PGame (j + 1) (p ++ v)))
      ∃ s', PUnit.respond ((), m) s = PMF.pure (Interaction.decodeWord w, s') ∧
        Match (j + 2) (p ++ v ++ w) (h ++ [(m, Interaction.decodeWord w)]) s') :
    ∀ (rem : ℕ) (j : ℕ) (p : List Bool) (h : Interaction.History) (s : PUnit.State),
      ((Match j p h s ∧ HistLive (t (enc a).length) p h ∧ h.length + rem = D ∧
          Interaction.outcome (Interaction.coinFamily MUnit (t (enc a).length) (enc a) c) h ≠
            .invalid) ∨
        (HistStopped (t (enc a).length) p h ∧
          ∃ b, Interaction.outcome (Interaction.coinFamily MUnit (t (enc a).length) (enc a) c) h =
            .done b)) →
      Interaction.acceptFrom PUnit s
        (Interaction.after (Interaction.coinFamily MUnit (t (enc a).length) (enc a) c) h) =
        if simDec enc MUnit t (a, List.ofFn c,
            p ++ IPGame.run (fun j' p' => simMsg enc MUnit t (a, List.ofFn c, j', p'))
              PGame (simGameShape (t (enc a).length) rem) j p) = true then 1 else 0 := by
  let t_n := t (enc a).length
  let F := Interaction.coinFamily MUnit t_n (enc a)
  intro rem
  induction rem with
  | zero =>
    intro j p h s hinv
    have hdone : ∃ b, Interaction.outcome (F c) h = .done b := by
      rcases hinv with ⟨_, _, hlen, hvalid⟩ | ⟨_, hb⟩
      · cases ho : Interaction.outcome (F c) h with
        | invalid => exact absurd ho hvalid
        | done b => exact ⟨b, rfl⟩
        | ask m =>
          have hlt := hF.rounds c h m ho
          omega
      · exact hb
    obtain ⟨b, hb⟩ := hdone
    have hex : extractHistory t_n p = h := by
      rcases hinv with ⟨_, hl, _, _⟩ | ⟨hs, _⟩
      · exact histLive_extract hl
      · exact histStopped_extract hs
    have hrunNil : IPGame.run (fun j' p' => simMsg enc MUnit t (a, List.ofFn c, j', p')) PGame
        (simGameShape t_n 0) j p = [] := rfl
    rw [hrunNil, List.append_nil, after_eq_pure_of_outcome_done hb, acceptFrom_pure_bool,
      simDec_eq_of_outcome_done MUnit t a c hex hb]
  | succ rem ih =>
    intro j p h s hinv
    have hrunCons : ∀ v w,
        v = List.ofFn (BitString.ofList (t_n + 2) (simMsg enc MUnit t (a, List.ofFn c, j, p))) →
        w = List.ofFn (BitString.ofList (t_n + 1) (PGame (j + 1) (p ++ v))) →
        p ++ IPGame.run (fun j' p' => simMsg enc MUnit t (a, List.ofFn c, j', p')) PGame
            (simGameShape t_n (rem + 1)) j p =
          (p ++ v ++ w) ++
            IPGame.run (fun j' p' => simMsg enc MUnit t (a, List.ofFn c, j', p')) PGame
              (simGameShape t_n rem) (j + 2) (p ++ v ++ w) := by
      intro v w hv hw
      have hsh : simGameShape t_n (rem + 1) =
          (.verifier, t_n + 2) :: (.prover, t_n + 1) :: simGameShape t_n rem := rfl
      rw [hsh]
      simp only [IPGame.run, List.append_assoc, ← hv, ← hw]
    rcases hinv with ⟨hm, hl, hlen, hvalid⟩ | ⟨hs, b, hb⟩
    · have hex := histLive_extract hl
      cases ho : Interaction.outcome (F c) h with
      | invalid => exact absurd ho hvalid
      | done b =>
        have hmsg := simMsg_of_outcome_done MUnit t a c j hex ho
        have hvlen : (List.replicate (t_n + 2) false).length = t_n + 2 := List.length_replicate
        set w := List.ofFn (BitString.ofList (t_n + 1)
          (PGame (j + 1) (p ++ List.replicate (t_n + 2) false)))
        have hwlen : w.length = t_n + 1 := List.length_ofFn
        have hv : List.replicate (t_n + 2) false = List.ofFn (BitString.ofList (t_n + 2)
            (simMsg enc MUnit t (a, List.ofFn c, j, p))) := by
          rw [hmsg, BitString.ofFn_ofList hvlen]
        have hs' : HistStopped t_n (p ++ List.replicate (t_n + 2) false ++ w) h :=
          histLive_append_false hl hvlen hwlen rfl
        rw [hrunCons _ w hv rfl]
        exact ih (j + 2) (p ++ List.replicate (t_n + 2) false ++ w) h s
          (Or.inr ⟨hs', b, ho⟩)
      | ask m =>
        have hmLen : m.length ≤ t_n := hF.message c h m ho
        have hmsg := simMsg_of_outcome_ask MUnit t a c j hex ho
        set v := [true] ++ Interaction.encodeWord t_n m
        have hvlen : v.length = t_n + 2 := by
          simp only [v, List.length_append, List.length_singleton,
            Interaction.length_encodeWord hmLen]
          omega
        set w := List.ofFn (BitString.ofList (t_n + 1) (PGame (j + 1) (p ++ v)))
        have hwlen : w.length = t_n + 1 := List.length_ofFn
        have hv : v = List.ofFn (BitString.ofList (t_n + 2)
            (simMsg enc MUnit t (a, List.ofFn c, j, p))) := by
          rw [hmsg, BitString.ofFn_ofList hvlen]
        obtain ⟨s', hresp, hm'⟩ := hstep j p h s m hm hl ho
        have hvhead : v.headD false = true := rfl
        have hdecv : Interaction.decodeWord (v.drop 1) = m := by
          simp only [v, List.singleton_append, List.drop_succ_cons, List.drop_zero,
            Interaction.decodeWord_encodeWord]
        have hl' : HistLive t_n (p ++ v ++ w) (h ++ [(m, Interaction.decodeWord w)]) := by
          simpa only [hdecv] using histLive_append_true hl hvlen hwlen hvhead
        unfold Interaction.outcome at ho
        cases hah : Interaction.after (F c) h with
        | none => simp [hah] at ho
        | some p0 =>
          cases p0 with
          | pure b => simp [hah] at ho
          | liftBind q cont =>
            obtain ⟨⟨⟩, m0⟩ := q
            simp only [hah, Interaction.Outcome.ask.injEq] at ho
            subst ho
            have hafter : Interaction.after (F c) (h ++ [(m0, Interaction.decodeWord w)]) =
                some (cont (Interaction.decodeWord w)) := by
              rw [Interaction.after_append, hah]
              change Interaction.after (.liftBind ((), m0) cont)
                  [(m0, Interaction.decodeWord w)] = _
              simp [Interaction.after]
            have haccept : Interaction.acceptFrom PUnit s (some (.liftBind ((), m0) cont)) =
                Interaction.acceptFrom PUnit s'
                  (Interaction.after (F c) (h ++ [(m0, Interaction.decodeWord w)])) := by
              have hq : (PFunctor.FreeM.liftBind ((), m0) cont : WordQueryComp Unit Bool) =
                  OracleComp.query ((), m0) >>= cont := rfl
              rw [hq, Interaction.acceptFrom, OracleComp.interpret_bind, OracleComp.interpret_query,
                StateT.run_bind, StateT.run, hresp, Probability.PMF.monad_bind_eq_bind,
                PMF.map_bind, PMF.pure_bind, hafter]
              rfl
            have hvalid' : Interaction.outcome (F c) (h ++ [(m0, Interaction.decodeWord w)]) ≠
                .invalid := by
              unfold Interaction.outcome
              rw [hafter]
              cases cont (Interaction.decodeWord w) <;> simp
            rw [haccept, hrunCons v w hv rfl]
            exact ih (j + 2) (p ++ v ++ w) (h ++ [(m0, Interaction.decodeWord w)]) s'
              (Or.inl ⟨hm', hl',
                by simp only [List.length_append, List.length_cons, List.length_nil]; omega,
                hvalid'⟩)
    · have hex := histStopped_extract hs
      have hmsg := simMsg_of_outcome_done MUnit t a c j hex hb
      have hvlen : (List.replicate (t_n + 2) false).length = t_n + 2 := List.length_replicate
      set w := List.ofFn (BitString.ofList (t_n + 1)
        (PGame (j + 1) (p ++ List.replicate (t_n + 2) false)))
      have hv : List.replicate (t_n + 2) false = List.ofFn (BitString.ofList (t_n + 2)
          (simMsg enc MUnit t (a, List.ofFn c, j, p))) := by
        rw [hmsg, BitString.ofFn_ofList hvlen]
      have hs' : HistStopped t_n (p ++ List.replicate (t_n + 2) false ++ w) h := by
        rw [List.append_assoc]
        exact histStopped_append hs
      rw [hrunCons _ w hv rfl]
      exact ih (j + 2) (p ++ List.replicate (t_n + 2) false ++ w) h s (Or.inr ⟨hs', b, hb⟩)

private noncomputable def proverOfGame (t_n : ℕ) (PGame : ℕ → List Bool → List Bool) :
    Prover Unit where
  State := SimState
  init := SimState.mk 0 []
  respond q st :=
    let v := [true] ++ Interaction.encodeWord t_n q.2
    let w := List.ofFn (BitString.ofList (t_n + 1) (PGame (st.round + 1) (st.transcript ++ v)))
    PMF.pure (Interaction.decodeWord w, SimState.mk (st.round + 2) (st.transcript ++ v ++ w))

private noncomputable def gameProverOfOptimal {R : Type} [Fintype R]
    (F : R → WordQueryComp Unit Bool) (t_n D : ℕ) (_j : ℕ) (q_str : List Bool) : List Bool :=
  let p_pre := q_str.take (q_str.length - (t_n + 2))
  let v := q_str.drop (q_str.length - (t_n + 2))
  let h_pre := extractHistory t_n p_pre
  if v.headD false then
    Interaction.encodeWord t_n
      (Interaction.bestReply F t_n (D - h_pre.length - 1) h_pre
        (Interaction.decodeWord (v.drop 1)))
  else List.replicate (t_n + 1) false

private theorem sim_bestCount_eq_value {enc : α ↪ List Bool} {k : ℕ} {Control : Type}
    (MUnit : Turing.MultiTapePTM k Bool Control Unit) (t : ℕ → ℕ) (a : α) {D : ℕ}
    (hF : Interaction.IsBounded (Interaction.coinFamily MUnit (t (enc a).length) (enc a))
      D (t (enc a).length)) :
    IPGame.bestCount (fun (c : BitString (t (enc a).length)) j p =>
        simMsg enc MUnit t (a, List.ofFn c, j, p))
      (fun (c : BitString (t (enc a).length)) tr => simDec enc MUnit t (a, List.ofFn c, tr))
      (simGameShape (t (enc a).length) D) =
      Interaction.value (Interaction.coinFamily MUnit (t (enc a).length) (enc a))
        (t (enc a).length) D [] := by
  let t_n := t (enc a).length
  let F := Interaction.coinFamily MUnit t_n (enc a)
  have hvalid0 : ∀ c, Interaction.outcome (F c) [] ≠ .invalid := fun c => by
    unfold Interaction.outcome
    rw [Interaction.after_nil]
    cases F c <;> simp
  apply le_antisymm
  · obtain ⟨PGame, hP⟩ := IPGame.exists_card_filter_run_eq_bestCount
      (fun (c : BitString t_n) j p => simMsg enc MUnit t (a, List.ofFn c, j, p))
      (fun (c : BitString t_n) tr => simDec enc MUnit t (a, List.ofFn c, tr))
      (simGameShape t_n D)
    rw [← hP]
    let PUnit := proverOfGame t_n PGame
    have hsum : (∑ c : BitString t_n,
        Interaction.acceptFrom PUnit PUnit.init (some (F c))) =
        (#(univ.filter fun c : BitString t_n =>
          simDec enc MUnit t (a, List.ofFn c,
            IPGame.run (fun j p => simMsg enc MUnit t (a, List.ofFn c, j, p)) PGame
              (simGameShape t_n D) 0 []) = true) : ENNReal) := by
      rw [Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      have htr := trace_sim_eq MUnit t a hF c PGame PUnit (fun j p _ st => st = SimState.mk j p)
        (fun j p _ s m hm _ _ => ⟨SimState.mk (j + 2) (p ++ ([true] ++ Interaction.encodeWord t_n m)
          ++
          List.ofFn (BitString.ofList (t_n + 1)
            (PGame (j + 1) (p ++ ([true] ++ Interaction.encodeWord t_n m))))),
          by rw [hm]; rfl, rfl⟩)
        D 0 [] [] PUnit.init (Or.inl ⟨rfl, histLive_nil t_n, by simp, hvalid0 c⟩)
      simpa only [Interaction.after_nil, List.nil_append, F, t_n, Nat.cast_ite, Nat.cast_one,
        Nat.cast_zero] using htr
    have hle := Interaction.sum_acceptFrom_le_value hF PUnit
    dsimp only [F, t_n] at hsum
    rw [hsum] at hle
    exact_mod_cast hle
  · let PGame := gameProverOfOptimal F t_n D
    let PUnit := Interaction.optimalProver F t_n D
    have hsum : (∑ c : BitString t_n,
        Interaction.acceptFrom PUnit PUnit.init (some (F c))) =
        (#(univ.filter fun c : BitString t_n =>
          simDec enc MUnit t (a, List.ofFn c,
            IPGame.run (fun j p => simMsg enc MUnit t (a, List.ofFn c, j, p)) PGame
              (simGameShape t_n D) 0 []) = true) : ENNReal) := by
      rw [Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      have htr := trace_sim_eq MUnit t a hF c PGame PUnit (fun _ _ h st => st = h)
        (fun j p h s m hm hl ho => by
          have hmLen : m.length ≤ t_n := hF.message c h m ho
          set v := [true] ++ Interaction.encodeWord t_n m
          have hvlen : v.length = t_n + 2 := by
            simp only [v, List.length_append, List.length_singleton,
              Interaction.length_encodeWord hmLen]
            omega
          set y := Interaction.bestReply F t_n (D - h.length - 1) h m
          have hy_mem : y ∈ BitString.shortWords t_n := by
            have hne : (BitString.shortWords t_n).Nonempty :=
              ⟨[], BitString.mem_shortWords.2 (Nat.zero_le _)⟩
            change ((BitString.shortWords t_n).exists_max_image _ hne).choose ∈ _
            exact ((BitString.shortWords t_n).exists_max_image _ hne).choose_spec.1
          have hyLen : y.length ≤ t_n := BitString.mem_shortWords.1 hy_mem
          have hex : extractHistory t_n p = h := histLive_extract hl
          have hP : PGame (j + 1) (p ++ v) = Interaction.encodeWord t_n y := by
            dsimp only [PGame, gameProverOfOptimal]
            have hsub : (p ++ v).length - (t_n + 2) = p.length := by
              rw [List.length_append, hvlen]; omega
            rw [hsub, List.take_left, List.drop_left]
            have hvhead : v.headD false = true := rfl
            have hvdrop : Interaction.decodeWord (v.drop 1) = m := by
              simp only [v, List.singleton_append, List.drop_succ_cons, List.drop_zero,
                Interaction.decodeWord_encodeWord]
            rw [hvhead, hex, hvdrop]
            simp only [reduceIte]
            rfl
          have hw : List.ofFn (BitString.ofList (t_n + 1) (PGame (j + 1) (p ++ v))) =
              Interaction.encodeWord t_n y := by
            rw [hP, BitString.ofFn_ofList (Interaction.length_encodeWord hyLen)]
          have hdecy : Interaction.decodeWord
              (List.ofFn (BitString.ofList (t_n + 1) (PGame (j + 1) (p ++ v)))) = y := by
            rw [hw, Interaction.decodeWord_encodeWord]
          refine ⟨h ++ [(m, y)], ?_, by rw [hdecy]⟩
          rw [hdecy, hm]
          rfl)
        D 0 [] [] PUnit.init (Or.inl ⟨rfl, histLive_nil t_n, by simp, hvalid0 c⟩)
      simpa only [Interaction.after_nil, List.nil_append, F, t_n, Nat.cast_ite, Nat.cast_one,
        Nat.cast_zero] using htr
    have hopt := Interaction.sum_acceptFrom_optimalProver hF
    have hcard := IPGame.card_filter_run_le_bestCount
      (fun (c : BitString t_n) j p => simMsg enc MUnit t (a, List.ofFn c, j, p))
      (fun (c : BitString t_n) tr => simDec enc MUnit t (a, List.ofFn c, tr))
      (simGameShape t_n D) PGame
    dsimp only [PUnit, F, t_n] at hsum
    rw [Nat.cast_injective (hsum.symm.trans hopt)] at hcard
    exact hcard

private theorem evalShape_simShape (tPoly : Polynomial ℕ) (q n : ℕ) :
    IPGame.evalShape
        ((List.replicate q [(.verifier, tPoly + 2), (.prover, tPoly + 1)]).flatten) n =
      simGameShape (tPoly.eval n) q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simp only [List.replicate_succ, List.flatten_cons, IPGame.evalShape_append,
      IPGame.evalShape_cons, IPGame.evalShape_nil, Polynomial.eval_add,
      Polynomial.eval_ofNat, Polynomial.eval_one, ih, simGameShape]

private theorem map_fst_simPolyShape (tPoly : Polynomial ℕ) (q : ℕ) :
    ((List.replicate q [(.verifier, tPoly + 2), (.prover, tPoly + 1)]).flatten).map Prod.fst =
      (alternatingMoves .arthur (2 * q)).map AMMove.toIP := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [show 2 * (q + 1) = 2 * q + 2 by omega]
    change ([IPMove.verifier, IPMove.prover] ++
        ((List.replicate q [(.verifier, tPoly + 2), (.prover, tPoly + 1)]).flatten).map
          Prod.fst) =
      (AMMove.arthur :: AMMove.merlin :: alternatingMoves AMMove.arthur (2 * q)).map AMMove.toIP
    rw [ih]
    rfl

private theorem sim_verifier_bounds {enc : α ↪ List Bool} {A : Set α}
    {verifier : α → WordOracleComp Unit Bool} {q : ℕ → ℕ}
    (hV : IsOraclePPTOn enc encBool verifier)
    (hq : ∀ a, (verifier a).IsQueryBounded (q (enc a).length))
    (hproof : IsInteractiveProof verifier A (2 / 3) (1 / 3)) :
    ∃ (k : ℕ) (Control : Type) (_ : Finite Control)
      (MUnit : Turing.MultiTapePTM k Bool Control Unit) (tPoly : Polynomial ℕ),
      (ComputableInPolyTime (simMsg enc MUnit tPoly.eval) (IPGame.encMsgInput enc) encBits ∧
       ComputableInPolyTime (simDec enc MUnit tPoly.eval) (IPGame.encDecInput enc) encBool) ∧
      ∀ a,
        (a ∈ A → 2 * 2 ^ tPoly.eval (enc a).length ≤
          3 * IPGame.bestCount
            (fun (c : BitString (tPoly.eval (enc a).length)) j p =>
              simMsg enc MUnit tPoly.eval (a, List.ofFn c, j, p))
            (fun (c : BitString (tPoly.eval (enc a).length)) tr =>
              simDec enc MUnit tPoly.eval (a, List.ofFn c, tr))
            (simGameShape (tPoly.eval (enc a).length) (q (enc a).length))) ∧
        (a ∉ A →
          3 * IPGame.bestCount
            (fun (c : BitString (tPoly.eval (enc a).length)) j p =>
              simMsg enc MUnit tPoly.eval (a, List.ofFn c, j, p))
            (fun (c : BitString (tPoly.eval (enc a).length)) tr =>
              simDec enc MUnit tPoly.eval (a, List.ofFn c, tr))
            (simGameShape (tPoly.eval (enc a).length) (q (enc a).length)) ≤
            2 ^ tPoly.eval (enc a).length) := by
  obtain ⟨_, k, Control, hfin, MUnit, cM, dM, hreal⟩ := hV
  let tPoly : Polynomial ℕ := Polynomial.C cM * (Polynomial.X + 1) ^ dM
  have htEval : ∀ n, tPoly.eval n = cM * (n + 1) ^ dM := fun n => by
    simp [tPoly]
  have htPoly : ComputableInPolyTime tPoly.eval encUnary encUnary :=
    ComputableInPolyTime.unary_eval tPoly
  refine ⟨k, Control, hfin, MUnit, tPoly,
    ⟨computableInPolyTime_simMsg MUnit htPoly, computableInPolyTime_simDec MUnit htPoly⟩,
    fun a => ?_⟩
  set t_n := tPoly.eval (enc a).length
  set F := Interaction.coinFamily MUnit t_n (enc a)
  have hreal_a : ∀ (S : Type) (oracle : Unit × List Bool → StateT S PMF (List Bool)) (s : S),
      (OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        (encBool <$> verifier a)).run s =
      (OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        (MUnit.runOracle t_n (enc a))).run s := fun S oracle s => by
    simpa [t_n, htEval, ProbOracleComp.runWith, OracleComp.runWith, Prod.map, encBool_apply] using
      hreal a S oracle s
  have hF : Interaction.IsBounded F (q (enc a).length) t_n :=
    isBounded_coinFamily_of_isQueryBounded MUnit (hq a) hreal_a
  have hbest := sim_bestCount_eq_value MUnit tPoly.eval a hF
  rw [hbest]
  have hne : 2 ^ t_n ≠ 0 := (pow_pos two_pos _).ne'
  refine ⟨fun ha => ?_, fun ha => ?_⟩
  · obtain ⟨P, hP⟩ := hproof.complete a ha
    have hacc := Interaction.acceptProb_eq_sum MUnit hreal_a P
    rw [hacc] at hP
    have hle := Interaction.sum_acceptFrom_le_value hF P
    have hpow : (2 : ENNReal) / 3 ≤
        (Interaction.value F t_n (q (enc a).length) [] : ENNReal) / (2 ^ t_n : ℕ) := by
      refine hP.trans ((mul_le_mul_right hle _).trans ?_)
      rw [div_eq_mul_inv, mul_comm, Nat.cast_pow, Nat.cast_ofNat]
    have hle' := (ENNReal.natCast_div_le_natCast_div_iff three_ne_zero hne).mp hpow
    simpa [Nat.mul_comm] using hle'
  · have hP := hproof.sound a ha (Interaction.optimalProver F t_n (q (enc a).length))
    have hacc := Interaction.acceptProb_eq_sum MUnit hreal_a
      (Interaction.optimalProver F t_n (q (enc a).length))
    rw [hacc] at hP
    change (2 ^ t_n : ENNReal)⁻¹ * ∑ r, Interaction.acceptFrom
        (Interaction.optimalProver F t_n (q (enc a).length))
        (Interaction.optimalProver F t_n (q (enc a).length)).init (some (F r)) ≤ 1 / 3 at hP
    rw [Interaction.sum_acceptFrom_optimalProver hF] at hP
    have hpow : (Interaction.value F t_n (q (enc a).length) [] : ENNReal) / (2 ^ t_n : ℕ) ≤
        1 / 3 := by
      refine le_trans ?_ hP
      rw [div_eq_mul_inv, mul_comm, Nat.cast_pow, Nat.cast_ofNat]
    have hle' := (ENNReal.natCast_div_le_natCast_div_iff hne three_ne_zero
      (a := Interaction.value F t_n (q (enc a).length) []) (c := 1)).mp (by simpa using hpow)
    simpa [Nat.mul_comm, one_mul] using hle'

/-- Every constant-query oracle-PPT interactive proof embeds into `IP[2 * q]`. -/
theorem IPQueryBounded_subset_IPk (enc : α ↪ List Bool) (q : ℕ) :
    IPQueryBounded enc q ⊆ IPk enc (2 * q) := by
  rintro A ⟨verifier, hV, hq, hproof⟩
  obtain ⟨k, Control, _, MUnit, tPoly, ⟨hmsg, hdec⟩, hbounds⟩ :=
    sim_verifier_bounds (q := fun _ => q) hV hq hproof
  refine ⟨(List.replicate q [(.verifier, tPoly + 2), (.prover, tPoly + 1)]).flatten, tPoly,
    simMsg enc MUnit tPoly.eval, simDec enc MUnit tPoly.eval,
    map_fst_simPolyShape tPoly q, hmsg, hdec, fun a => ?_⟩
  simpa only [IPGame.countAt, evalShape_simShape] using hbounds a

/-- Every polynomial-query oracle-PPT interactive proof embeds into `IP[2 * q(n)]` when `q` is
computable in polynomial time. -/
theorem IPPolyQueryBounded_subset_IPPolyRounds {enc : α ↪ List Bool} {q : ℕ → ℕ}
    (hqPoly : ComputableInPolyTime q encUnary encUnary) :
    IPPolyQueryBounded enc q ⊆ IPPolyRounds enc (fun n => 2 * q n) := by
  rintro A ⟨verifier, hV, hq, hproof⟩
  obtain ⟨k, Control, _, MUnit, tPoly, ⟨hmsg, hdec⟩, hbounds⟩ :=
    sim_verifier_bounds hV hq hproof
  have hflat : ComputableInPolyTime (fun n => simGameShape (tPoly.eval n) (q n))
      encUnary encIPShape := by
    have hrep : ComputableInPolyTime (fun n => List.replicate (q n) false)
        encUnary (encList encBool) :=
      ComputableInPolyTime.replicate hqPoly (ComputableInPolyTime.const false)
    have ht : ComputableInPolyTime tPoly.eval encUnary encUnary :=
      ComputableInPolyTime.unary_eval tPoly
    have hstep : ComputableInPolyTime
        (fun x : ℕ × Bool => [(.verifier, tPoly.eval x.1 + 2), (.prover, tPoly.eval x.1 + 1)])
        (encPair encUnary encBool) (encList (encPair encIPMove encUnary)) := by
      have hn : ComputableInPolyTime (fun x : ℕ × Bool => x.1)
          (encPair encUnary encBool) encUnary := .fst _ _
      have ht2 : ComputableInPolyTime (fun x : ℕ × Bool => (IPMove.verifier, tPoly.eval x.1 + 2))
          (encPair encUnary encBool) (encPair encIPMove encUnary) :=
        (ComputableInPolyTime.const IPMove.verifier).prod
          (ComputableInPolyTime.unary_add' (ht.comp hn) (ComputableInPolyTime.const 2))
      have ht1 : ComputableInPolyTime (fun x : ℕ × Bool => (IPMove.prover, tPoly.eval x.1 + 1))
          (encPair encUnary encBool) (encPair encIPMove encUnary) :=
        (ComputableInPolyTime.const IPMove.prover).prod
          (ComputableInPolyTime.unary_add' (ht.comp hn) (ComputableInPolyTime.const 1))
      exact ht2.cons' (ht1.cons' (ComputableInPolyTime.const []))
    refine (ComputableInPolyTime.flatMapWithInput
        (f := fun n (_ : Bool) => [(.verifier, tPoly.eval n + 2), (.prover, tPoly.eval n + 1)])
        hrep hstep).of_enc_eq fun n => congrArg encIPShape ?_
    induction q n with
    | zero => rfl
    | succ m ih =>
      simp only [List.replicate_succ, List.flatMap_cons, List.flatten_cons, simGameShape] at ih ⊢
      exact congrArg (_ ++ ·) ih
  refine ⟨fun n => simGameShape (tPoly.eval n) (q n), tPoly.eval,
    simMsg enc MUnit tPoly.eval, simDec enc MUnit tPoly.eval,
    fun n => simGameShape_map_fst (tPoly.eval n) (q n), hflat,
    ComputableInPolyTime.unary_eval tPoly, hmsg, hdec, hbounds⟩

end SimGame

/-! ### Simulation of `IPPolyRounds (2 * q ·)` in `IPPolyQueryBounded` -/

section SimOracle

private noncomputable def oracleStep (enc : α ↪ List Bool) (g : ℕ → List (IPMove × ℕ))
    (msg : α × List Bool × ℕ × List Bool → List Bool)
    (ac : α × List Bool) (st : SimState) : WordOracleComp Unit SimState :=
  let n := (enc ac.1).length
  let nv := ((g n).getD st.round (.verifier, 0)).2
  let np := ((g n).getD (st.round + 1) (.prover, 0)).2
  let m := BitString.listRow nv 0 (msg (ac.1, ac.2, st.round, st.transcript))
  (fun y => SimState.mk (st.round + 2) (st.transcript ++ m ++ BitString.listRow np 0 y)) <$>
    (List.take np <$> ProbOracleComp.query ((), m))

private noncomputable def oracleVerifier (enc : α ↪ List Bool) (g : ℕ → List (IPMove × ℕ))
    (ρ q : ℕ → ℕ) (msg : α × List Bool × ℕ × List Bool → List Bool)
    (dec : α × List Bool × List Bool → Bool) (a : α) : WordOracleComp Unit Bool := do
  let c ← ProbOracleComp.sample (BitString.sampleList (ρ (enc a).length))
  let st ← OracleComp.iterate (q (enc a).length) (oracleStep enc g msg (a, c)) (SimState.mk 0 [])
  pure (dec (a, c, st.transcript))

private theorem isQueryBounded_oracleStep (enc : α ↪ List Bool) (g : ℕ → List (IPMove × ℕ))
    (msg : α × List Bool × ℕ × List Bool → List Bool) (ac : α × List Bool) (st : SimState) :
    (oracleStep enc g msg ac st).IsQueryBounded 1 := by
  unfold oracleStep ProbOracleComp.IsQueryBounded
  rw [OracleComp.isCostBounded_map_iff, OracleComp.isCostBounded_map_iff]
  exact ProbOracleComp.IsQueryBounded.query _

private theorem isQueryBounded_iterate_unit {σ : Type} {step : σ → WordOracleComp Unit σ}
    (hstep : ∀ s, (step s).IsQueryBounded 1) (m : ℕ) (init : σ) :
    ProbOracleComp.IsQueryBounded (OracleComp.iterate m step init) m := by
  induction m generalizing init with
  | zero => exact .pure init 0
  | succ m ih =>
    rw [OracleComp.iterate_succ_bind]
    have h1 : OracleComp.IsCostBounded (Sum.elim (fun _ => 0) fun _ => 1) (step init) 1 :=
      hstep init
    have h2 : ∀ s, OracleComp.IsCostBounded (Sum.elim (fun _ => 0) fun _ => 1)
        (OracleComp.iterate m step s) m := fun s => ih s
    exact (OracleComp.IsCostBounded.bind h1 h2).mono (by omega)

private theorem isQueryBounded_oracleVerifier (enc : α ↪ List Bool) (g : ℕ → List (IPMove × ℕ))
    (ρ q : ℕ → ℕ) (msg : α × List Bool × ℕ × List Bool → List Bool)
    (dec : α × List Bool × List Bool → Bool) (a : α) :
    (oracleVerifier enc g ρ q msg dec a).IsQueryBounded (q (enc a).length) := by
  unfold oracleVerifier
  dsimp only [ProbOracleComp.IsQueryBounded]
  have hiter : ∀ c, OracleComp.IsCostBounded (Sum.elim (fun _ => 0) fun _ => 1)
      (OracleComp.iterate (q (enc a).length) (oracleStep enc g msg (a, c)) (SimState.mk 0 []) >>=
        fun st => pure (dec (a, c, st.transcript))) (q (enc a).length + 0) := fun c => by
    have hunit : OracleComp.IsCostBounded (Sum.elim (fun _ => 0) fun _ => 1)
        (OracleComp.iterate (q (enc a).length) (oracleStep enc g msg (a, c)) (SimState.mk 0 []))
        (q (enc a).length) :=
      isQueryBounded_iterate_unit (isQueryBounded_oracleStep enc g msg (a, c))
        (q (enc a).length) (SimState.mk 0 [])
    exact OracleComp.IsCostBounded.bind hunit (fun st => .pure _ 0)
  have hwhole : OracleComp.IsCostBounded (Sum.elim (fun _ => 0) fun _ => 1)
      (ProbOracleComp.sample (BitString.sampleList (ρ (enc a).length)) >>= fun c =>
        OracleComp.iterate (q (enc a).length) (oracleStep enc g msg (a, c)) (SimState.mk 0 []) >>=
          fun st => pure (dec (a, c, st.transcript))) (0 + (q (enc a).length + 0)) :=
    OracleComp.IsCostBounded.bind (ProbOracleComp.IsQueryBounded.sample _) hiter
  exact hwhole.mono (by omega)

private theorem isOraclePPTOn_oracleVerifier {enc : α ↪ List Bool}
    {g : ℕ → List (IPMove × ℕ)} {ρ q : ℕ → ℕ}
    {msg : α × List Bool × ℕ × List Bool → List Bool} {dec : α × List Bool × List Bool → Bool}
    (hgmap : ∀ n, (g n).map Prod.fst = (alternatingMoves .arthur (2 * q n)).map AMMove.toIP)
    (hg : ComputableInPolyTime g encUnary encIPShape)
    (hρ : ComputableInPolyTime ρ encUnary encUnary)
    (hq : ComputableInPolyTime q encUnary encUnary)
    (hmsg : ComputableInPolyTime msg (IPGame.encMsgInput enc) encBits)
    (hdec : ComputableInPolyTime dec (IPGame.encDecInput enc) encBool) :
    IsOraclePPTOn enc encBool (oracleVerifier enc g ρ q msg dec) := by
  let encAC : (α × List Bool) ↪ List Bool := encPair enc encBits
  let encSt : SimState ↪ List Bool := encSimState
  let encArg : ((α × List Bool) × SimState) ↪ List Bool := encPair encAC encSt
  have hsample : IsOraclePPTOn (Operation := Unit) enc encBits
      (fun a => ProbOracleComp.sample (BitString.sampleList (ρ (enc a).length))) :=
    (ComputableInPolyTime.sampleList
      (hρ.comp (ComputableInPolyTime.encoding_length enc))).isOraclePPTOn (Operation := Unit)
  have hstepPPT : IsOraclePPTOn encArg encSt (fun arg => oracleStep enc g msg arg.1 arg.2) := by
    have hac : ComputableInPolyTime (fun arg : (α × List Bool) × SimState => arg.1)
        encArg encAC := .fst _ _
    have ha : ComputableInPolyTime (fun arg : (α × List Bool) × SimState => arg.1.1)
        encArg enc := (ComputableInPolyTime.fst _ _).comp hac
    have hc : ComputableInPolyTime (fun arg : (α × List Bool) × SimState => arg.1.2)
        encArg encBits := (ComputableInPolyTime.snd _ _).comp hac
    have hst : ComputableInPolyTime (fun arg : (α × List Bool) × SimState => arg.2)
        encArg encSt := .snd _ _
    have hj : ComputableInPolyTime (fun arg : (α × List Bool) × SimState => arg.2.round)
        encArg encUnary := encSimState_round_polyTime hst
    have hp : ComputableInPolyTime (fun arg : (α × List Bool) × SimState => arg.2.transcript)
        encArg encBits := encSimState_transcript_polyTime hst
    have hn : ComputableInPolyTime
        (fun arg : (α × List Bool) × SimState => (enc arg.1.1).length) encArg encUnary :=
      (ComputableInPolyTime.encoding_length enc).comp ha
    have hgn : ComputableInPolyTime
        (fun arg : (α × List Bool) × SimState => g (enc arg.1.1).length)
        encArg encIPShape := hg.comp hn
    have hnv : ComputableInPolyTime
        (fun arg : (α × List Bool) × SimState =>
          ((g (enc arg.1.1).length).getD arg.2.round (.verifier, 0)).2) encArg encUnary :=
      (ComputableInPolyTime.snd encIPMove encUnary).comp
        (ComputableInPolyTime.listGetDWithInput hgn hj (.verifier, 0))
    have hnp : ComputableInPolyTime
        (fun arg : (α × List Bool) × SimState =>
          ((g (enc arg.1.1).length).getD (arg.2.round + 1) (.prover, 0)).2) encArg encUnary :=
      (ComputableInPolyTime.snd encIPMove encUnary).comp
        (ComputableInPolyTime.listGetDWithInput hgn
          (ComputableInPolyTime.unary_add' hj (ComputableInPolyTime.const 1)) (.prover, 0))
    have hm : ComputableInPolyTime
        (fun arg : (α × List Bool) × SimState =>
          BitString.listRow ((g (enc arg.1.1).length).getD arg.2.round (.verifier, 0)).2 0
            (msg (arg.1.1, arg.1.2, arg.2.round, arg.2.transcript))) encArg encBits :=
      ComputableInPolyTime.bitsRowWithInput hnv (ComputableInPolyTime.const 0)
        (hmsg.comp (ha.prod (hc.prod (hj.prod hp))))
    have hqry := IsOraclePPTOn.query_take' () hm hnp
    have hy : ComputableInPolyTime
        (fun p : ((α × List Bool) × SimState) × List Bool =>
          SimState.mk (p.1.2.round + 2) (p.1.2.transcript ++
            BitString.listRow ((g (enc p.1.1.1).length).getD p.1.2.round (.verifier, 0)).2 0
              (msg (p.1.1.1, p.1.1.2, p.1.2.round, p.1.2.transcript)) ++
            BitString.listRow ((g (enc p.1.1.1).length).getD (p.1.2.round + 1)
              (.prover, 0)).2 0 p.2))
        (encPair encArg encBits) encSt := by
      have ha1 : ComputableInPolyTime
          (fun p : ((α × List Bool) × SimState) × List Bool => p.1)
          (encPair encArg encBits) encArg := .fst _ _
      have hy2 : ComputableInPolyTime
          (fun p : ((α × List Bool) × SimState) × List Bool => p.2)
          (encPair encArg encBits) encBits := .snd _ _
      have hj' := ComputableInPolyTime.unary_add' (hj.comp ha1) (ComputableInPolyTime.const 2)
      have hp' := ComputableInPolyTime.bitsAppend
        (ComputableInPolyTime.bitsAppend (hp.comp ha1) (hm.comp ha1))
        (ComputableInPolyTime.bitsRowWithInput (hnp.comp ha1) (ComputableInPolyTime.const 0) hy2)
      exact encSimState_mk_polyTime hj' hp'
    simpa only [oracleStep] using hqry.map_with' hy
  obtain ⟨c₁, d₁, hqlen⟩ := hq.polyBounded_length.exists_le
  obtain ⟨c₂, d₂, hglen⟩ := hg.polyBounded_length.exists_le
  let D := max d₁ d₂
  have hcount : ComputableInPolyTime (fun ac : α × List Bool => q (enc ac.1).length)
      encAC encUnary :=
    hq.comp ((ComputableInPolyTime.encoding_length enc).comp (.fst _ _))
  have hiter := IsOraclePPTOn.iterateWith_spec' (input := encAC) (stateEncoding := encSt)
    hcount (ComputableInPolyTime.const (SimState.mk 0 [])) hstepPPT
    (fun ac i st => st.round = 2 * i ∧
      st.transcript.length = IPGame.transcriptLength ((g (enc ac.1).length).take (2 * i)))
    (fun _ => by dsimp [SimState.round, SimState.transcript]; exact ⟨rfl, rfl⟩)
    (fun ac i st hi hinv next hnext => by
      obtain ⟨hst1, hplen⟩ := hinv
      dsimp only [oracleStep, OracleComp.support] at hnext
      simp only [OracleComp.mem_supportWith_map_iff, ProbOracleComp.supportWith_query,
        Set.mem_univ, true_and] at hnext
      obtain ⟨y, _, rfl⟩ := hnext
      refine ⟨by dsimp only [SimState.round]; omega, ?_⟩
      have hlenG : (g (enc ac.1).length).length = 2 * q (enc ac.1).length := by
        have hm := congrArg List.length (hgmap (enc ac.1).length)
        simp only [List.length_map] at hm
        have haltLen : ∀ m0 k, (alternatingMoves m0 k).length = k := fun m0 k => by
          induction k generalizing m0 with
          | zero => rfl
          | succ k ih => simp [alternatingMoves, ih m0.other]
        rw [hm, haltLen]
      have htake : (g (enc ac.1).length).take (2 * (i + 1)) =
          (g (enc ac.1).length).take (2 * i) ++
            [(g (enc ac.1).length).getD (2 * i) (.verifier, 0),
             (g (enc ac.1).length).getD (2 * i + 1) (.prover, 0)] := by
        have hlt1 : 2 * i < (g (enc ac.1).length).length := by omega
        have hlt2 : 2 * i + 1 < (g (enc ac.1).length).length := by omega
        rw [show 2 * (i + 1) = (2 * i + 1) + 1 by omega, List.take_add_one, List.take_add_one]
        simp only [List.getElem?_eq_getElem hlt1, List.getElem?_eq_getElem hlt2,
          Option.toList_some, List.getD_eq_getElem?_getD, Option.getD_some, List.append_assoc,
          List.singleton_append]
      rw [htake, IPGame.transcriptLength, List.map_append, List.sum_append]
      simp only [hst1, List.length_append, hplen, BitString.listRow_zero, List.length_ofFn,
        IPGame.transcriptLength, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, Nat.add_assoc])
    (size := fun ac => (4 * c₁ + 2 * c₂ + 3) * ((encAC ac).length + 1) ^ D)
    (PolyBounded.of_forall_le _ D fun _ => le_rfl)
    (fun ac i st hi hinv => by
      obtain ⟨hj, hp⟩ := hinv
      set n := (enc ac.1).length
      have hnAC : n ≤ (encAC ac).length := by
        simp only [encAC, length_encPair, n]
        omega
      have h1 : 1 ≤ ((encAC ac).length + 1) ^ D := Nat.one_le_pow _ _ (Nat.succ_pos _)
      have hpow1 : (n + 1) ^ d₁ ≤ ((encAC ac).length + 1) ^ D :=
        (Nat.pow_le_pow_left (by omega) _).trans
          (Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_left _ _))
      have hpow2 : (n + 1) ^ d₂ ≤ ((encAC ac).length + 1) ^ D :=
        (Nat.pow_le_pow_left (by omega) _).trans
          (Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_right _ _))
      have hqB := hqlen n
      simp only [encUnary_apply, List.length_replicate] at hqB
      have hqB' : q n ≤ c₁ * ((encAC ac).length + 1) ^ D := hqB.trans (Nat.mul_le_mul_left _ hpow1)
      have hgB := hglen n
      simp only [encUnary_apply, List.length_replicate] at hgB
      have htrB : st.transcript.length ≤ (encIPShape (g n)).length := by
        rw [hp]
        refine le_trans ?_ (IPGame.transcriptLength_le_length_encIPShape (g n))
        conv_rhs => rw [← List.take_append_drop (2 * i) (g n)]
        simp only [IPGame.transcriptLength, List.map_append, List.sum_append]
        exact Nat.le_add_right _ _
      have hgB' : st.transcript.length ≤ c₂ * ((encAC ac).length + 1) ^ D :=
        htrB.trans (hgB.trans (Nat.mul_le_mul_left _ hpow2))
      simp only [encSt, encSimState_apply, encSimStateFields, length_encPair, encUnary_apply,
        List.length_replicate, encBits_apply]
      nlinarith)
  have hdecPPT : IsOraclePPTOn (Operation := Unit) (encPair encAC encSt) encBool
      (fun x : (α × List Bool) × SimState => pure (dec (x.1.1, x.1.2, x.2.transcript))) := by
    have ha : ComputableInPolyTime
        (fun x : (α × List Bool) × SimState => x.1.1) (encPair encAC encSt) enc :=
      (ComputableInPolyTime.fst _ _).comp (.fst _ _)
    have hc : ComputableInPolyTime
        (fun x : (α × List Bool) × SimState => x.1.2) (encPair encAC encSt) encBits :=
      (ComputableInPolyTime.snd _ _).comp (.fst _ _)
    have hp : ComputableInPolyTime
        (fun x : (α × List Bool) × SimState => x.2.transcript) (encPair encAC encSt) encBits :=
      encSimState_transcript_polyTime (.snd _ _)
    exact (hdec.comp (ha.prod (hc.prod hp))).isOraclePPTOn (Operation := Unit)
  have hcont : IsOraclePPTOn encAC encBool
      (fun ac => do
        let st ← OracleComp.iterate (q (enc ac.1).length) (oracleStep enc g msg ac)
          (SimState.mk 0 [])
        pure (dec (ac.1, ac.2, st.transcript))) :=
    hiter.1.bind_with hdecPPT
  unfold oracleVerifier
  exact hsample.bind_with hcont

private theorem acceptProb_sample_uniformList {k : ℕ} (next : List Bool → WordOracleComp Unit Bool)
    (P : Prover Unit) :
    acceptProb (ProbOracleComp.sample (BitString.sampleList k) >>= next) P =
      (2 ^ k : ENNReal)⁻¹ * ∑ c : BitString k, acceptProb (next (List.ofFn c)) P := by
  rw [acceptProb_sample_bind]
  simp only [BitString.eval_sampleList, BitString.uniformList, PMF.map_apply,
    PMF.uniformOfFintype_apply, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Nat.cast_pow, Nat.cast_ofNat, tsum_fintype]
  rw [tsum_eq_sum (s := Finset.univ.image List.ofFn) fun b hb => by
    rw [Finset.sum_eq_zero]
    · simp
    · intro c _
      simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists] at hb
      exact ite_eq_right fun h => absurd h.symm (hb c)]
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_image (f := fun b => ∑ a : BitString k,
      if b = List.ofFn a then (2 ^ k : ENNReal)⁻¹ * acceptProb (next b) P else 0)
    fun _ _ _ _ h => List.ofFn_injective h]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_eq_single c
    (fun c' _ hne => ite_eq_right fun h => absurd (List.ofFn_injective h).symm hne)
    fun hc => absurd (Finset.mem_univ c) hc]
  simp only [reduceIte]

private theorem execProg_acceptProb_le {enc : α ↪ List Bool} (g : ℕ → List (IPMove × ℕ))
    (msg : α × List Bool × ℕ × List Bool → List Bool) (dec : α × List Bool × List Bool → Bool)
    {ρn : ℕ} (a : α) (P : Prover Unit) :
    ∀ (m : ℕ) (g' : List (IPMove × ℕ)) (j : ℕ) (p : List Bool) (S : Finset (BitString ρn))
      (s : P.State),
      g'.map Prod.fst = (alternatingMoves .arthur (2 * m)).map AMMove.toIP →
      (∀ k, g'.getD k (.verifier, 0) = (g (enc a).length).getD (j + k) (.verifier, 0)) →
      (∀ k, g'.getD k (.prover, 0) = (g (enc a).length).getD (j + k) (.prover, 0)) →
      (∑ c ∈ S, (P.run ((fun st => dec (a, List.ofFn c, st.transcript)) <$>
          OracleComp.iterate m (oracleStep enc g msg (a, List.ofFn c)) (SimState.mk j p)) s).map
            Prod.fst true : ENNReal) ≤
        IPGame.count g' (fun t => #(S.filter fun c =>
          (IPGame.agrees (fun j' p' => msg (a, List.ofFn c, j', p')) g' j p t &&
            dec (a, List.ofFn c, p ++ t)) = true)) := by
  intro m
  induction m with
  | zero =>
    intro g' j p S s hgmap _ _
    have hnil : g' = [] :=
      (List.map_eq_nil_iff (f := Prod.fst)).1 (by simpa [alternatingMoves] using hgmap)
    subst hnil
    simp only [OracleComp.iterate_zero, Functor.map, IPGame.count_nil, IPGame.agrees, Bool.true_and,
      Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_le_sum fun c _ => ?_
    cases dec (a, List.ofFn c, p) <;> simp [Prover.run_pure]
  | succ m ih =>
    intro g' j p S s hgmap hgetV hgetP
    rw [show 2 * (m + 1) = 2 * m + 2 by omega] at hgmap
    change g'.map Prod.fst = [.verifier, .prover] ++
        (alternatingMoves .arthur (2 * m)).map AMMove.toIP at hgmap
    obtain ⟨⟨v, nv⟩, g₁, rfl, hv, hg₁⟩ := List.map_eq_cons_iff.1 hgmap
    obtain ⟨⟨pr, np⟩, g'', rfl, hpr, hg''⟩ := List.map_eq_cons_iff.1 hg₁
    dsimp only at hv hpr
    subst hv hpr
    have hnv : ((g (enc a).length).getD j (.verifier, 0)).2 = nv := by
      simpa using (congrArg Prod.snd (hgetV 0)).symm
    have hnp : ((g (enc a).length).getD (j + 1) (.prover, 0)).2 = np := by
      simpa using (congrArg Prod.snd (hgetP 1)).symm
    have hgetV'' : ∀ k, g''.getD k (.verifier, 0) =
        (g (enc a).length).getD (j + 2 + k) (.verifier, 0) := fun k => by
      rw [show j + 2 + k = j + (k + 2) by omega]
      exact hgetV (k + 2)
    have hgetP'' : ∀ k, g''.getD k (.prover, 0) =
        (g (enc a).length).getD (j + 2 + k) (.prover, 0) := fun k => by
      rw [show j + 2 + k = j + (k + 2) by omega]
      exact hgetP (k + 2)
    have hstepEq : ∀ c : BitString ρn,
        (P.run ((fun st => dec (a, List.ofFn c, st.transcript)) <$>
            OracleComp.iterate (m + 1) (oracleStep enc g msg (a, List.ofFn c))
              (SimState.mk j p)) s).map
            Prod.fst true =
          ∑' ys : List Bool × P.State,
            (P.respond
              ((), List.ofFn (BitString.ofList nv (msg (a, List.ofFn c, j, p))))).run s ys *
            (P.run ((fun st => dec (a, List.ofFn c, st.transcript)) <$>
              OracleComp.iterate m (oracleStep enc g msg (a, List.ofFn c))
                (SimState.mk (j + 2) (p ++ List.ofFn (BitString.ofList nv
                  (msg (a, List.ofFn c, j, p))) ++
                  List.ofFn (BitString.ofList np ys.1)))) ys.2).map Prod.fst true := by
      intro c
      rw [OracleComp.iterate_succ_bind, map_eq_bind_pure_comp]
      change (P.run ((oracleStep enc g msg (a, List.ofFn c) (SimState.mk j p) >>= fun st' =>
          OracleComp.iterate m (oracleStep enc g msg (a, List.ofFn c)) st' >>=
            fun st => pure (dec (a, List.ofFn c, st.transcript)))) s).map Prod.fst true = _
      unfold oracleStep
      simp only [hnv, hnp, BitString.listRow_zero]
      conv_lhs => rw [Prover.run_bind, Prover.run_map, Prover.run_map, Prover.run_query]
      rw [PMF.bind_map, PMF.bind_map, PMF.map_bind, PMF.bind_apply]
      refine tsum_congr fun ys => ?_
      have htake : List.ofFn (BitString.ofList np (ys.1.take np)) =
          List.ofFn (BitString.ofList np ys.1) := by
        simp [BitString.ofList_take]
      dsimp only [Function.comp_apply, Prod.map, id_eq]
      rw [htake, bind_pure_comp]
    simp_rw [hstepEq]
    rw [← Finset.sum_fiberwise_of_maps_to (s := S) (t := univ)
      (g := fun c => BitString.ofList nv (msg (a, List.ofFn c, j, p)))
      fun _ _ => mem_univ _]
    rw [IPGame.count_verifier, Nat.cast_sum]
    refine Finset.sum_le_sum fun m0 _ => ?_
    have hswap : ∑ c ∈ S.filter (fun c => BitString.ofList nv (msg (a, List.ofFn c, j, p)) = m0),
        ∑' ys : List Bool × P.State,
          (P.respond ((), List.ofFn (BitString.ofList nv (msg (a, List.ofFn c, j, p))))).run s ys *
            (P.run ((fun st => dec (a, List.ofFn c, st.transcript)) <$>
              OracleComp.iterate m (oracleStep enc g msg (a, List.ofFn c))
                (SimState.mk (j + 2) (p ++ List.ofFn (BitString.ofList nv
                  (msg (a, List.ofFn c, j, p))) ++
                  List.ofFn (BitString.ofList np ys.1)))) ys.2).map Prod.fst true =
        ∑' ys : List Bool × P.State, (P.respond ((), List.ofFn m0)).run s ys *
          ∑ c ∈ S.filter (fun c => BitString.ofList nv (msg (a, List.ofFn c, j, p)) = m0),
            (P.run ((fun st => dec (a, List.ofFn c, st.transcript)) <$>
              OracleComp.iterate m (oracleStep enc g msg (a, List.ofFn c))
                (SimState.mk (j + 2) (p ++ List.ofFn m0 ++
                  List.ofFn (BitString.ofList np ys.1)))) ys.2).map
              Prod.fst true := by
      rw [← Summable.tsum_finsetSum fun _ _ => CompleteLattice.summable]
      refine tsum_congr fun ys => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c hc => ?_
      rw [(Finset.mem_filter.1 hc).2]
    rw [hswap]
    calc ∑' ys : List Bool × P.State, (P.respond ((), List.ofFn m0)).run s ys * _
        ≤ ∑' ys : List Bool × P.State, (P.respond ((), List.ofFn m0)).run s ys *
            (IPGame.count ((.prover, np) :: g'') (fun t => #(S.filter fun c =>
              (IPGame.agrees (fun j' p' => msg (a, List.ofFn c, j', p'))
                ((.verifier, nv) :: (.prover, np) :: g'') j p (List.ofFn m0 ++ t) &&
                dec (a, List.ofFn c, p ++ (List.ofFn m0 ++ t))) = true)) : ENNReal) := by
          refine tsum_le_tsum fun ys => mul_le_mul_right ?_ _
          refine (ih g'' (j + 2) (p ++ List.ofFn m0 ++ List.ofFn (BitString.ofList np ys.1))
            _ ys.2 hg'' hgetV'' hgetP'').trans ?_
          rw [IPGame.count_prover]
          exact_mod_cast le_trans (le_of_eq (IPGame.count_congr_of_length g'' fun t _ => by
            rw [Finset.filter_filter]
            congr 1
            refine Finset.filter_congr fun c _ => ?_
            rw [IPGame.agrees_verifier_ofFn, IPGame.agrees_prover_ofFn]
            simp only [Bool.and_eq_true, decide_eq_true_eq, List.append_assoc]
            exact ⟨fun ⟨hm0, ha', hd⟩ => ⟨⟨hm0.symm, ha'⟩, hd⟩,
              fun ⟨⟨hm0, ha'⟩, hd⟩ => ⟨hm0.symm, ha', hd⟩⟩))
            (Finset.le_sup (f := fun y0 : BitString np => IPGame.count g'' fun t =>
              #(S.filter fun c =>
                (IPGame.agrees (fun j' p' => msg (a, List.ofFn c, j', p'))
                  ((.verifier, nv) :: (.prover, np) :: g'') j p
                  (List.ofFn m0 ++ (List.ofFn y0 ++ t)) &&
                  dec (a, List.ofFn c, p ++ (List.ofFn m0 ++ (List.ofFn y0 ++ t)))) = true))
              (mem_univ (BitString.ofList np ys.1)))
      _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

@[reducible] private noncomputable def proverOfIPGame (enc : α ↪ List Bool)
    (g : ℕ → List (IPMove × ℕ)) (a : α) (PGame : ℕ → List Bool → List Bool) : Prover Unit where
  State := SimState
  init := SimState.mk 0 []
  respond q st :=
    let np := ((g (enc a).length).getD (2 * st.round + 1) (.prover, 0)).2
    let y := List.ofFn (BitString.ofList np (PGame (2 * st.round + 1) (st.transcript ++ q.2)))
    PMF.pure (y, SimState.mk (st.round + 1) (st.transcript ++ q.2 ++ y))

private theorem execProg_acceptProb_proverOfIPGame {enc : α ↪ List Bool}
    (g : ℕ → List (IPMove × ℕ)) (msg : α × List Bool × ℕ × List Bool → List Bool)
    (dec : α × List Bool × List Bool → Bool) {ρn : ℕ} (a : α)
    (PGame : ℕ → List Bool → List Bool) (c : BitString ρn) :
    ∀ (m : ℕ) (g' : List (IPMove × ℕ)) (i : ℕ) (p : List Bool),
      g'.map Prod.fst = (alternatingMoves .arthur (2 * m)).map AMMove.toIP →
      (∀ k, g'.getD k (.verifier, 0) = (g (enc a).length).getD (2 * i + k) (.verifier, 0)) →
      (∀ k, g'.getD k (.prover, 0) = (g (enc a).length).getD (2 * i + k) (.prover, 0)) →
      ((proverOfIPGame enc g a PGame).run ((fun st => dec (a, List.ofFn c, st.transcript)) <$>
          OracleComp.iterate m (oracleStep enc g msg (a, List.ofFn c)) (SimState.mk (2 * i) p))
          (SimState.mk i p)).map Prod.fst true =
        if dec (a, List.ofFn c,
            p ++ IPGame.run (fun j' p' => msg (a, List.ofFn c, j', p')) PGame g' (2 * i) p) =
            true then 1 else 0 := by
  intro m
  induction m with
  | zero =>
    intro g' i p hgmap _ _
    have hnil : g' = [] :=
      (List.map_eq_nil_iff (f := Prod.fst)).1 (by simpa [alternatingMoves] using hgmap)
    subst hnil
    simp only [OracleComp.iterate_zero, Functor.map, IPGame.run, List.append_nil]
    cases hdec : dec (a, List.ofFn c, p) <;> simp [hdec, Prover.run_pure]
  | succ m ih =>
    intro g' i p hgmap hgetV hgetP
    rw [show 2 * (m + 1) = 2 * m + 2 by omega] at hgmap
    change g'.map Prod.fst = [.verifier, .prover] ++
        (alternatingMoves .arthur (2 * m)).map AMMove.toIP at hgmap
    obtain ⟨⟨v, nv⟩, g₁, rfl, hv, hg₁⟩ := List.map_eq_cons_iff.1 hgmap
    obtain ⟨⟨pr, np⟩, g'', rfl, hpr, hg''⟩ := List.map_eq_cons_iff.1 hg₁
    dsimp only at hv hpr
    subst hv hpr
    have hnv : ((g (enc a).length).getD (2 * i) (.verifier, 0)).2 = nv := by
      simpa using (congrArg Prod.snd (hgetV 0)).symm
    have hnp : ((g (enc a).length).getD (2 * i + 1) (.prover, 0)).2 = np := by
      simpa using (congrArg Prod.snd (hgetP 1)).symm
    have hgetV'' : ∀ k, g''.getD k (.verifier, 0) =
        (g (enc a).length).getD (2 * (i + 1) + k) (.verifier, 0) := fun k => by
      rw [show 2 * (i + 1) + k = 2 * i + (k + 2) by omega]
      exact hgetV (k + 2)
    have hgetP'' : ∀ k, g''.getD k (.prover, 0) =
        (g (enc a).length).getD (2 * (i + 1) + k) (.prover, 0) := fun k => by
      rw [show 2 * (i + 1) + k = 2 * i + (k + 2) by omega]
      exact hgetP (k + 2)
    let p1 := p ++ List.ofFn (BitString.ofList nv (msg (a, List.ofFn c, 2 * i, p))) ++
      List.ofFn (BitString.ofList np (PGame (2 * i + 1)
        (p ++ List.ofFn (BitString.ofList nv (msg (a, List.ofFn c, 2 * i, p))))))
    have hstep :
        (PMF.map Prod.fst ((proverOfIPGame enc g a PGame).run
          ((fun st => dec (a, List.ofFn c, st.transcript)) <$>
            OracleComp.iterate (m + 1) (oracleStep enc g msg (a, List.ofFn c))
              (SimState.mk (2 * i) p)) (SimState.mk i p))) true =
        (PMF.map Prod.fst ((proverOfIPGame enc g a PGame).run
          ((fun st => dec (a, List.ofFn c, st.transcript)) <$>
            OracleComp.iterate m (oracleStep enc g msg (a, List.ofFn c))
              (SimState.mk (2 * (i + 1)) p1)) (SimState.mk (i + 1) p1))) true := by
      rw [OracleComp.iterate_succ_bind, map_eq_bind_pure_comp]
      change ((proverOfIPGame enc g a PGame).run
          (oracleStep enc g msg (a, List.ofFn c) (SimState.mk (2 * i) p) >>= fun st' =>
            OracleComp.iterate m (oracleStep enc g msg (a, List.ofFn c)) st' >>=
              fun st => pure (dec (a, List.ofFn c, st.transcript)))
            (SimState.mk i p)).map Prod.fst true = _
      conv_lhs =>
        dsimp only [oracleStep]
        simp only [hnv, hnp, BitString.listRow_zero]
        rw [Prover.run_bind, Prover.run_map, Prover.run_map, Prover.run_query]
        rw [PMF.bind_map, PMF.bind_map, PMF.map_bind]
        simp only [proverOfIPGame, StateT.run, PMF.pure_bind, Function.comp_apply, Prod.map,
          id_eq]
        rw [hnp, List.take_of_length_le (Nat.le_of_eq List.length_ofFn), BitString.ofList_ofFn,
          bind_pure_comp, show 2 * i + 2 = 2 * (i + 1) by omega]
    have hrun : p ++ IPGame.run (fun j' p' => msg (a, List.ofFn c, j', p')) PGame
          ((.verifier, nv) :: (.prover, np) :: g'') (2 * i) p =
        p1 ++ IPGame.run (fun j' p' => msg (a, List.ofFn c, j', p')) PGame g''
          (2 * (i + 1)) p1 := by
      simp only [p1, IPGame.run, List.append_assoc]
      rfl
    rw [hstep, hrun]
    exact ih g'' (i + 1) p1 hg'' hgetV'' hgetP''

/-- Every dynamic `IP[2 * q(n)]` game class is simulated by an oracle-PPT verifier making at most
`q(n)` queries when `q` is computable in polynomial time. -/
theorem IPPolyRounds_subset_IPPolyQueryBounded {enc : α ↪ List Bool} {q : ℕ → ℕ}
    (hqPoly : ComputableInPolyTime q encUnary encUnary) :
    IPPolyRounds enc (fun n => 2 * q n) ⊆ IPPolyQueryBounded enc q := by
  rintro A ⟨g, ρ, msg, dec, hgmap, hg, hρ, hmsg, hdec, hA⟩
  refine ⟨oracleVerifier enc g ρ q msg dec,
    isOraclePPTOn_oracleVerifier hgmap hg hρ hqPoly hmsg hdec,
    isQueryBounded_oracleVerifier enc g ρ q msg dec, fun a ha => ?_, fun a ha P => ?_⟩
  · obtain ⟨PGame, hP⟩ := IPGame.exists_card_filter_run_eq_bestCount
      (fun (c : BitString (ρ (enc a).length)) j p => msg (a, List.ofFn c, j, p))
      (fun (c : BitString (ρ (enc a).length)) tr => dec (a, List.ofFn c, tr))
      (g (enc a).length)
    refine ⟨proverOfIPGame enc g a PGame, ?_⟩
    rw [oracleVerifier, acceptProb_sample_uniformList]
    have hsum : ∑ c : BitString (ρ (enc a).length),
        acceptProb (do
          let st ← OracleComp.iterate (q (enc a).length)
            (oracleStep enc g msg (a, List.ofFn c)) (SimState.mk 0 [])
          pure (dec (a, List.ofFn c, st.transcript))) (proverOfIPGame enc g a PGame) =
        (#(univ.filter fun c : BitString (ρ (enc a).length) =>
          dec (a, List.ofFn c,
            IPGame.run (fun j p => msg (a, List.ofFn c, j, p)) PGame
              (g (enc a).length) 0 []) = true) : ENNReal) := by
      rw [Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      have hpr := execProg_acceptProb_proverOfIPGame (enc := enc) g msg dec a PGame c
        (q (enc a).length) (g (enc a).length) 0 [] (hgmap (enc a).length)
        (fun _ => by simp) (fun _ => by simp)
      simpa [acceptProb] using hpr
    rw [hsum, hP]
    have hne : 2 ^ ρ (enc a).length ≠ 0 := (pow_pos two_pos _).ne'
    have h2 : (2 : ENNReal) / 3 ≤
        (IPGame.bestCount _ _ (g (enc a).length) : ENNReal) / (2 ^ ρ (enc a).length : ℕ) :=
      (ENNReal.natCast_div_le_natCast_div_iff three_ne_zero hne).mpr
        (by simpa [Nat.mul_comm] using (hA a).1 ha)
    simpa [div_eq_mul_inv, mul_comm] using h2
  · rw [oracleVerifier, acceptProb_sample_uniformList]
    have hle := execProg_acceptProb_le (enc := enc) g msg dec (ρn := ρ (enc a).length) a P
      (q (enc a).length) (g (enc a).length) 0 [] univ P.init (hgmap (enc a).length)
      (fun _ => by simp) (fun _ => by simp)
    have hle' : ∑ c : BitString (ρ (enc a).length),
        acceptProb (do
          let st ← OracleComp.iterate (q (enc a).length)
            (oracleStep enc g msg (a, List.ofFn c)) (SimState.mk 0 [])
          pure (dec (a, List.ofFn c, st.transcript))) P ≤
        (IPGame.bestCount (fun (c : BitString (ρ (enc a).length)) j p =>
            msg (a, List.ofFn c, j, p))
          (fun (c : BitString (ρ (enc a).length)) tr => dec (a, List.ofFn c, tr))
          (g (enc a).length) : ENNReal) := by
      dsimp only [acceptProb, IPGame.bestCount]
      unfold IPGame.acceptedCoins
      simpa only [bind_pure_comp, List.nil_append] using hle
    have hne : 2 ^ ρ (enc a).length ≠ 0 := (pow_pos two_pos _).ne'
    have hdiv : (IPGame.bestCount (fun (c : BitString (ρ (enc a).length)) j p =>
            msg (a, List.ofFn c, j, p))
          (fun (c : BitString (ρ (enc a).length)) tr => dec (a, List.ofFn c, tr))
          (g (enc a).length) : ENNReal) / (2 ^ ρ (enc a).length : ℕ) ≤ 1 / 3 := by
      have hdiv' := (ENNReal.natCast_div_le_natCast_div_iff hne three_ne_zero
        (a := IPGame.bestCount (fun (c : BitString (ρ (enc a).length)) j p =>
            msg (a, List.ofFn c, j, p))
          (fun (c : BitString (ρ (enc a).length)) tr => dec (a, List.ofFn c, tr))
          (g (enc a).length))
        (c := 1)).mpr (by simpa [Nat.mul_comm, one_mul] using (hA a).2 ha)
      simpa using hdiv'
    refine le_trans (mul_le_mul_right hle' _) ?_
    simpa [div_eq_mul_inv, mul_comm] using hdiv

end SimOracle

/-! ### Main equivalences and `IP ⊆ AM[poly]` -/

/-- **Oracle-model `IP[k]` equals `IP[2 * q]`**: oracle-PPT verifiers making at most `q` queries
decide exactly `IPk enc (2 * q)`. -/
theorem IPQueryBounded_eq_IPk (enc : α ↪ List Bool) (q : ℕ) :
    IPQueryBounded enc q = IPk enc (2 * q) :=
  le_antisymm (IPQueryBounded_subset_IPk enc q)
    ((IPk_subset_IPPolyRounds (2 * q)).trans
      (IPPolyRounds_subset_IPPolyQueryBounded (ComputableInPolyTime.const q)))

/-- **Oracle-model `IP[k]` equals `IP[2 * q + 1]`**: appending one final verifier move does not
change the class. -/
theorem IPQueryBounded_eq_IPk_odd (enc : α ↪ List Bool) (q : ℕ) :
    IPQueryBounded enc q = IPk enc (2 * q + 1) :=
  (IPQueryBounded_eq_IPk enc q).trans (IPk_two_mul_add_one_eq q).symm

/-- Zero-query oracle-PPT interactive proofs coincide with `BPP`. -/
theorem IPQueryBounded_zero (enc : α ↪ List Bool) :
    IPQueryBounded enc 0 = BPP enc :=
  (IPQueryBounded_eq_IPk enc 0).trans (IPk_zero_eq_BPP enc)

/-- **Babai–Moran–Goldwasser–Sipser for oracle verifiers**: every constant non-zero query budget
`1 ≤ q` collapses `IPQueryBounded enc q` to `AM enc`. -/
theorem IPQueryBounded_eq_AM (enc : α ↪ List Bool) {q : ℕ} (hq : 1 ≤ q) :
    IPQueryBounded enc q = AM enc :=
  (IPQueryBounded_eq_IPk enc q).trans (IPk_eq_AM (by omega))

/-- **Dynamic oracle-model equivalence**: for every polynomial-time query budget `q : ℕ → ℕ`,
`IPPolyQueryBounded enc q` coincides with `IPPolyRounds enc (fun n => 2 * q n)`. -/
theorem IPPolyQueryBounded_eq_IPPolyRounds {enc : α ↪ List Bool} {q : ℕ → ℕ}
    (hq : ComputableInPolyTime q encUnary encUnary) :
    IPPolyQueryBounded enc q = IPPolyRounds enc (fun n => 2 * q n) :=
  le_antisymm (IPPolyQueryBounded_subset_IPPolyRounds hq)
    (IPPolyRounds_subset_IPPolyQueryBounded hq)

/-- **Goldwasser–Sipser without round collapse for oracle verifiers**: every `q(n)`-query
oracle-PPT interactive proof sits in `AM[2 * q(n) + 2]`. -/
theorem IPPolyQueryBounded_subset_AMPolyRounds {enc : α ↪ List Bool} {q : ℕ → ℕ}
    (hq : ComputableInPolyTime q encUnary encUnary) :
    IPPolyQueryBounded enc q ⊆ AMPolyRounds enc (fun n => 2 * q n + 2) :=
  (IPPolyQueryBounded_subset_IPPolyRounds hq).trans
    (IPPolyRounds_subset_AMPolyRounds (fun n => 2 * q n))

/-- **Every problem in `IP` admits a dynamic public-coin `AM[k(n)]` protocol** with a
polynomial-time round count `k`. -/
theorem IP_subset_AMPolyRounds {enc : α ↪ List Bool} {A : Set α} (hA : A ∈ IP enc) :
    ∃ k : ℕ → ℕ, ComputableInPolyTime k encUnary encUnary ∧ A ∈ AMPolyRounds enc k := by
  obtain ⟨c, d, hq⟩ := IP_subset_exists_IPPolyQueryBounded hA
  let qPoly : Polynomial ℕ := Polynomial.C c * (Polynomial.X + 1) ^ d
  have hqEval : (fun n => qPoly.eval n) = (fun n => c * (n + 1) ^ d) := funext fun n => by
    simp [qPoly]
  have hqPoly : ComputableInPolyTime (fun n => c * (n + 1) ^ d) encUnary encUnary := by
    rw [← hqEval]
    exact ComputableInPolyTime.unary_eval qPoly
  exact ⟨fun n => 2 * (c * (n + 1) ^ d) + 2,
    ComputableInPolyTime.unary_add'
      (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2) hqPoly)
      (ComputableInPolyTime.const 2),
    IPPolyQueryBounded_subset_AMPolyRounds hqPoly hq⟩

end Cslib.Complexity
