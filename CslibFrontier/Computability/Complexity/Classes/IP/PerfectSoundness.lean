/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.IP.Simulation
import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length

/-!
# Interactive proofs with perfect soundness are in `NP`

A problem with an interactive proof without soundness error is in `NP`
(`Cslib.Complexity.IsInteractiveProof.mem_NP`) [Goldreich, Proposition 9.2][Goldreich2007DraftR5].
The model is that of `Cslib.Complexity.IP`: the verifier is strict oracle PPT, realized against
every stateful prover by one finite fair-coin oracle machine `M` under the clock
`t = c * (n + 1) ^ d` for instances encoded with `n` bits, and provers are arbitrary randomized
stateful strategies that see the messages but not the coins.

The certificate is a transcript with the coins that produced it. Fixing the `t` coins of the
machine leaves the program `Cslib.Complexity.Interaction.coinProgram`, and acceptance averages the
programs over the coins (`Cslib.Complexity.Interaction.acceptProb_eq_sum`). So some prover is
accepted with positive probability exactly when some coins `r` of length `t` and some history `e`
of at most `t` messages and replies, each of at most `t` bits, make the program of `r` accept
(`Cslib.Complexity.Interaction.exists_pos_acceptProb_iff`):

* a prover with positive acceptance probability gives a positive value of the empty history
  (`Cslib.Complexity.Interaction.sum_acceptFrom_le_value`), and a positive value is witnessed by an
  accepting history of short words
  (`Cslib.Complexity.Interaction.exists_outcome_eq_done_of_pos_value`);
* conversely, the deterministic prover replaying the replies of an accepting history
  (`Cslib.Complexity.Interaction.historyProver`) makes the program of `r` accept, so it is accepted
  with probability at least `2⁻ᵗ` (`Cslib.Complexity.Interaction.acceptFrom_historyProver`).

Whether given coins and history make the program accept is decided in polynomial time by a replay
(`Cslib.Complexity.Interaction.computableInPolyTime_accepts`), and the certificate has length at
most `2t + 1 + t(6t + 3)`. With soundness error `0`, no prover is accepted on a non-member, so
the transcripts are `NP` certificates as soon as every member has a prover accepted with positive
probability (`Cslib.Complexity.mem_NP_of_exists_pos_acceptProb`).

**Completeness.** Goldreich's draft Definition 9.1 assumes perfect completeness, and the proof
of Proposition 9.2 fixes the verifier's coins to the all-zero string (PDF pp. 8–9 / printed
pp. 390–391). This formalization strengthens that result: the coins are part of the certificate,
so any completeness `c > 0` suffices and perfect completeness is not assumed.

## Main definitions

* `Cslib.Complexity.Interaction.historyProver`: the prover replaying the replies of a history.

## Main results

* `Cslib.Complexity.Interaction.exists_outcome_eq_done_of_pos_value`: a positive value has an
  accepting history.
* `Cslib.Complexity.Interaction.acceptFrom_historyProver`,
  `Cslib.Complexity.Interaction.pos_acceptProb_historyProver`: replaying an accepting history
  accepts.
* `Cslib.Complexity.Interaction.exists_pos_acceptProb_iff`: positive acceptance is a bounded
  accepting transcript with its coins.
* `Cslib.Complexity.mem_NP_of_exists_pos_acceptProb`, `Cslib.Complexity.IsInteractiveProof.mem_NP`:
  perfect soundness gives `NP`.

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, draft
  r5][Goldreich2007DraftR5]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Probability Turing.MultiTapeTM

namespace Interaction

/-! ### Accepting histories of a positive value -/

section Value

variable {R : Type} [Fintype R] {F : R → WordQueryComp Unit Bool} {L : ℕ}

/-- A history after which some program has accepted extends, by the empty history, to an accepting
one. -/
private theorem exists_outcome_eq_done_of_pos_accepted {h : History} (hpos : 0 < accepted F h) :
    ∃ r, outcome (F r) (h ++ []) = .done true := by
  classical
  rw [accepted, Finset.card_pos] at hpos
  obtain ⟨r, hr⟩ := hpos
  exact ⟨r, by simpa using hr⟩

/-- **A positive value has an accepting history**: when the value of `h` with `n` rounds to go is
positive, some program accepts after `h` followed by at most `n` messages and replies, each of
length at most `L`. -/
theorem exists_outcome_eq_done_of_pos_value : ∀ {n : ℕ} {h : History}, 0 < value F L n h →
    ∃ r e, e.length ≤ n ∧ (∀ x ∈ e, x.1.length ≤ L ∧ x.2.length ≤ L) ∧
      outcome (F r) (h ++ e) = .done true
  | 0, h, hpos => by
    obtain ⟨r, hr⟩ := exists_outcome_eq_done_of_pos_accepted hpos
    exact ⟨r, [], le_rfl, by simp, hr⟩
  | n + 1, h, hpos => by
    rw [value] at hpos
    rcases Nat.eq_zero_or_pos (accepted F h) with h0 | hacc
    · rw [h0, zero_add, Finset.sum_pos_iff] at hpos
      obtain ⟨m, hm, hsup⟩ := hpos
      obtain ⟨y, hy, hval⟩ := Finset.lt_sup_iff.1 hsup
      obtain ⟨r, e, he, hshort, hout⟩ := exists_outcome_eq_done_of_pos_value hval
      refine ⟨r, (m, y) :: e, by simpa using he, ?_, by simpa using hout⟩
      simp only [List.mem_cons, forall_eq_or_imp]
      exact ⟨⟨BitString.mem_shortWords.1 hm, BitString.mem_shortWords.1 hy⟩, hshort⟩
    · obtain ⟨r, hr⟩ := exists_outcome_eq_done_of_pos_accepted hacc
      exact ⟨r, [], by simp, by simp, hr⟩

end Value

/-! ### Replaying a history -/

/-- The deterministic prover that answers the messages of an interaction with the replies of the
history `h`, in order and whatever the messages are; once `h` is exhausted it replies with the
empty word. Its state is the part of `h` still to be replayed. -/
noncomputable def historyProver (h : History) : Prover Unit where
  State := History
  init := h
  respond _ s := PMF.pure ((s.headD ([], [])).2, s.tail)

/-- **Replaying an accepting history accepts**: from the state `e`, the prover replaying `e` makes
a program accept with probability `1` when the program accepts after the history `e`. -/
theorem acceptFrom_historyProver (h : History) {p : WordQueryComp Unit Bool} {e : History}
    (hp : outcome p e = .done true) : acceptFrom (historyProver h) e (some p) = 1 := by
  induction e generalizing p with
  | nil =>
    cases p with
    | pure b =>
      have hb : b = true := Outcome.done.inj hp
      subst hb
      exact (acceptFrom_pure _ _ true).trans (by simp)
    | liftBind q next => exact absurd hp nofun
  | cons x e ih =>
    obtain ⟨m, y⟩ := x
    cases p with
    | pure b => exact absurd hp nofun
    | liftBind q next =>
      obtain ⟨⟨⟩, m'⟩ := q
      have key : after (.liftBind ((), m') next : WordQueryComp Unit Bool) ((m, y) :: e) =
          if m = m' then after (next y) e else none := rfl
      unfold outcome at hp
      rw [key] at hp
      split_ifs at hp with hm
      · subst hm
        have hp' : outcome (next y) e = .done true := hp
        refine (acceptFrom_query_bind (historyProver h) ((m, y) :: e) m next).trans ?_
        have hrun : ((historyProver h).respond ((), m)).run ((m, y) :: e) = PMF.pure (y, e) := rfl
        rw [hrun]
        change ∑' ys : List Bool × History,
          (PMF.pure (y, e)) ys * acceptFrom (historyProver h) ys.2 (some (next ys.1)) = 1
        rw [tsum_eq_single (y, e) fun ys hys => by simp [PMF.pure_apply, hys]]
        simpa [PMF.pure_apply] using ih hp'

/-! ### Positive acceptance is an accepting transcript -/

section Transcript

variable {k : ℕ} {Control : Type} (M : _root_.Turing.MultiTapePTM k Bool Control Unit)

/-- **An accepting transcript is accepted with positive probability.** Let the verifier `V` be
realized by the fair-coin oracle machine `M` under the clock `t` on the input `x`. If the `t` coins
`r` and the history `e` make the program of `r` accept, then the prover replaying `e` is accepted
with positive probability (at least `2⁻ᵗ`). -/
theorem pos_acceptProb_historyProver {V : WordOracleComp Unit Bool} {t : ℕ} {x : List Bool}
    (hV : ∀ (S : Type) (oracle : Unit × List Bool → StateT S PMF (List Bool)) s,
      ProbOracleComp.runWith oracle (encBool <$> V) s =
        ProbOracleComp.runWith oracle (M.runOracle t x) s)
    {r : List Bool} {e : History} (hr : r.length = t)
    (hout : outcome (coinProgram M t x r) e = .done true) :
    0 < acceptProb V (historyProver e) := by
  subst hr
  rw [acceptProb_eq_sum M hV]
  refine ENNReal.mul_pos (ENNReal.inv_ne_zero.2 (ENNReal.pow_ne_top ENNReal.ofNat_ne_top))
    (ne_of_gt ?_)
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun _ _ => bot_le)
    (Finset.mem_univ r.get))
  rw [List.ofFn_get]
  exact (acceptFrom_historyProver e hout).symm ▸ zero_lt_one

/-- **Positive acceptance is a bounded accepting transcript.** Let the verifier `V` be realized by
the fair-coin oracle machine `M` under the clock `t` on the input `x`. Some prover is accepted
with positive probability exactly when some `t` coins and some history of at most `t` messages and
replies, each of at most `t` bits, make the program of the coins accept. -/
theorem exists_pos_acceptProb_iff {V : WordOracleComp Unit Bool} {t : ℕ} {x : List Bool}
    (hV : ∀ (S : Type) (oracle : Unit × List Bool → StateT S PMF (List Bool)) s,
      ProbOracleComp.runWith oracle (encBool <$> V) s =
        ProbOracleComp.runWith oracle (M.runOracle t x) s) :
    (∃ P : Prover Unit, 0 < acceptProb V P) ↔
      ∃ r e, r.length = t ∧ e.length ≤ t ∧ (∀ y ∈ e, y.1.length ≤ t ∧ y.2.length ≤ t) ∧
        outcome (coinProgram M t x r) e = .done true := by
  constructor
  · rintro ⟨P, hP⟩
    rw [acceptProb_eq_sum M hV P, ENNReal.mul_pos_iff] at hP
    have hval : (0 : ENNReal) < value (coinFamily M t x) t t [] :=
      hP.2.trans_le (sum_acceptFrom_le_value (isBounded_coinFamily M t x) P)
    obtain ⟨r, e, he, hshort, hout⟩ :=
      exists_outcome_eq_done_of_pos_value (Nat.cast_pos.1 hval)
    exact ⟨List.ofFn r, e, List.length_ofFn, he, hshort, by simpa [coinFamily] using hout⟩
  · rintro ⟨r, e, hr, -, -, hout⟩
    exact ⟨_, pos_acceptProb_historyProver M hV hr hout⟩

end Transcript

end Interaction

/-! ### Perfect soundness gives `NP` -/

section NP

open Interaction

variable {α : Type} {enc : α ↪ List Bool}

/-- The length of a certificate of `t` coins and a history of at most `t` messages and replies,
each of at most `t` bits. -/
private theorem length_encTranscript_le {t : ℕ} {r : List Bool} {e : History}
    (hr : r.length = t) (he : e.length ≤ t) (hshort : ∀ y ∈ e, y.1.length ≤ t ∧ y.2.length ≤ t) :
    (encPair encBits encHistory (r, e)).length ≤ 2 * t + 1 + t * (6 * t + 3) := by
  rw [length_encPair, encBits_apply, hr, length_encList]
  have hsum := List.sum_le_length_nsmul
    (e.map fun y => 2 * (encPair encBits encBits y).length + 1) (6 * t + 3) fun z hz => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
      obtain ⟨h1, h2⟩ := hshort y hy
      rw [length_encPair, encBits_apply, encBits_apply]
      lia
  rw [List.length_map, smul_eq_mul] at hsum
  have := Nat.mul_le_mul_right (6 * t + 3) he
  lia

/-- **Positive acceptance on members and none on non-members gives `NP`.** Let `V` be strict
oracle PPT. If every member of `A` has a prover accepted with positive probability, and no prover
is accepted with positive probability on a non-member, then `A ∈ NP`. The certificate is a
transcript of at most `t` messages and replies of at most `t` bits each, together with the `t`
coins that produced it, where `t = c * (n + 1) ^ d` is the clock of `V`. -/
theorem mem_NP_of_exists_pos_acceptProb {V : α → WordOracleComp Unit Bool} {A : Set α}
    (hV : IsOraclePPTOn enc encBool V)
    (complete : ∀ a ∈ A, ∃ P : Prover Unit, 0 < acceptProb (V a) P)
    (sound : ∀ a ∉ A, ∀ P : Prover Unit, acceptProb (V a) P = 0) : A ∈ NP enc := by
  obtain ⟨_, k, Control, _, M, c, d, hreal⟩ := hV
  set fuel : α → ℕ := fun a => c * ((enc a).length + 1) ^ d
  have hfuel : ComputableInPolyTime fuel enc encUnary := by
    have hlen : ComputableInPolyTime (fun a => (enc a).length) enc encUnary := by fun_prop
    exact ((ComputableInPolyTime.unary_eval (Polynomial.C c * (Polynomial.X + 1) ^ d)).comp
      hlen).of_enc_eq fun a => by simp [fuel]
  have hacc := computableInPolyTime_accepts (fun _ _ => true) id M
    (encEntry := encPair encBits encBits) (fun _ => ComputableInPolyTime.const true)
    ComputableInPolyTime.id'
  let check : α × (List Bool × History) → Bool := fun q =>
    decide (q.2.1.length = fuel q.1) && accepts (fun _ _ => true) id M (enc q.1) q.2.1 q.2.2
  have hcheck : ComputableInPolyTime check (encPair enc (encPair encBits encHistory)) encBool := by
    have hacc' : ComputableInPolyTime
        (fun q : α × (List Bool × History) => accepts (fun _ _ => true) id M (enc q.1) q.2.1 q.2.2)
        (encPair enc (encPair encBits encHistory)) encBool := by fun_prop
    have hlen : ComputableInPolyTime (fun q : α × (List Bool × History) => q.2.1.length)
        (encPair enc (encPair encBits encHistory)) encUnary := by fun_prop
    have hfuel' : ComputableInPolyTime (fun q : α × (List Bool × History) => fuel q.1)
        (encPair enc (encPair encBits encHistory)) encUnary :=
      hfuel.comp (ComputableInPolyTime.fst _ _)
    exact ComputableInPolyTime.bool_and' (hlen.decide_eq' hfuel') hacc'
  have hiff (a : α) (r : List Bool) (e : History) : check (a, (r, e)) = true ↔
      r.length = fuel a ∧ outcome (coinProgram M (fuel a) (enc a) r) e = .done true := by
    simp only [check, Bool.and_eq_true, decide_eq_true_eq]
    refine and_congr_right fun hr => ?_
    rw [accepts_eq_true_iff, hr]
  set T : Polynomial ℕ := Polynomial.C c * (Polynomial.X + 1) ^ d
  refine mem_NP_of_check (p := 2 * T + 1 + T * (6 * T + 3))
    (Decoder.bits.pair (Decoder.bits.pair Decoder.bits).list) hcheck
    (fun a ⟨r, e⟩ hre => ?_) fun a ha => ?_
  · by_contra ha
    obtain ⟨hr, hout⟩ := (hiff a r e).1 hre
    exact (pos_acceptProb_historyProver M (hreal a) hr hout).ne' (sound a ha _)
  · obtain ⟨r, e, hr, he, hshort, hout⟩ := (exists_pos_acceptProb_iff M (hreal a)).1 (complete a ha)
    refine ⟨(r, e), (hiff a r e).2 ⟨hr, hout⟩, ?_⟩
    simpa [fuel, T] using length_encTranscript_le hr he hshort

/-- **Perfect soundness gives `NP`** [Goldreich, Proposition 9.2][Goldreich2007DraftR5]. A problem
with an interactive proof whose verifier is strict oracle PPT, with any positive completeness `c`
and soundness error `0` against all randomized stateful provers, is in `NP`. Perfect completeness
is not needed. -/
theorem IsInteractiveProof.mem_NP {V : α → WordOracleComp Unit Bool} {A : Set α} {c : ENNReal}
    (hV : IsOraclePPTOn enc encBool V) (h : IsInteractiveProof V A c 0) (hc : 0 < c) :
    A ∈ NP enc :=
  mem_NP_of_exists_pos_acceptProb hV (fun a ha => (h.complete a ha).imp fun _ hP => hc.trans_le hP)
    fun a ha P => le_zero_iff.1 (h.sound a ha P)

end NP

end Cslib.Complexity
