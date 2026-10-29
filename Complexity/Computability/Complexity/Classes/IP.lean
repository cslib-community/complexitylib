/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.BPP
public import Complexity.Computability.Complexity.Classes.NP
public import Complexity.Computability.Probabilistic.Oracle
public import Complexity.Languages.Probabilistic.BitString
public import Complexity.Languages.Probabilistic.Oracle.QueryCount
public import Complexity.Languages.Probabilistic.Oracle.Interaction
import Complexity.Computability.Probabilistic.Oracle.Composition
import Complexity.Computability.Probabilistic.PPT.Capture
import Complexity.Computability.Probabilistic.QueryBounds
import Complexity.Computability.Probabilistic.Sampling

/-!
# Interactive proofs and the class IP

An interactive proof system for a problem `A` is an efficient probabilistic verifier exchanging
messages with an all-powerful prover. On members of `A` some prover convinces the verifier with
high probability (completeness); on non-members no prover does, except with small probability
(soundness) [Goldwasser, Micali and Rackoff][GoldwasserMicaliRackoff1989],
[Arora and Barak, Definition 8.6][AroraBarak09].

A verifier is a program `α → WordOracleComp Unit Bool`: it draws private fair coins with
`ProbOracleComp.sample` and sends the prover a word with `ProbOracleComp.query ((), message)`,
receiving the reply word. Every call is one round, and later messages may depend on earlier
replies and coins. Its efficiency is `Cslib.Probability.IsOraclePPTOn`: one finite fair-coin machine
with one polynomial clock realizes the verifier against every stateful oracle. The clock charges
writing messages and reading reply bits but not the prover's computation, so the verifier exchanges
polynomially many messages of polynomial length (`Cslib.Complexity.exists_queryBounds_of_mem_IP`)
and reads only a polynomial part of each reply.

A `Cslib.Complexity.Prover` is any stateful strategy answering messages: a type of private states,
an initial state, and a probabilistic response function, with no efficiency requirement. It sees
the messages but not the verifier's coins, so the proofs are private-coin. As in
[GoldwasserMicaliRackoff1989] provers may be randomized; Arora and Barak use deterministic
provers. The provers built here are deterministic, and soundness holds against the larger class.

`IP` uses the thresholds `2 / 3` and `1 / 3` of Arora and Barak. `NP ⊆ IP` with a single message:
the prover sends a certificate and the verifier checks a prefix of the reply of the certificate
length, with completeness `1` and soundness `0`. `BPP ⊆ IP` without messages.
Conversely, `IP ⊆ PSPACE` (`Complexity.Computability.Complexity.Classes.IP.PSPACE`).

## Main definitions

* `Cslib.Complexity.Prover`: an unbounded stateful prover, with `Prover.run` the joint law of a
  verifier's result and the prover's final state.
* `Cslib.Complexity.acceptProb`: the probability that a verifier accepts against a prover.
* `Cslib.Complexity.IsInteractiveProof`: completeness and soundness thresholds.
* `Cslib.Complexity.IP`.

## Main results

* `Cslib.Complexity.exists_queryBounds_of_mem_IP`: polynomially many rounds of polynomial length.
* `Cslib.Complexity.NP_subset_IP`, `Cslib.Complexity.BPP_subset_IP`.

## References

* [S. Goldwasser, S. Micali, C. Rackoff, *The knowledge complexity of interactive proof
  systems*][GoldwasserMicaliRackoff1989]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Probability Turing.MultiTapeTM

/-- A prover for interactive proofs: a computationally unbounded strategy answering every message
`(op, word)` of the verifier with a reply word, possibly at random, updating a private state. -/
structure Prover (Operation : Type) where
  /-- The private states of the prover. -/
  State : Type
  /-- The state at the start of the interaction. -/
  init : State
  /-- The reply to one message, which may read and update the state. -/
  respond : Operation × List Bool → StateT State PMF (List Bool)

namespace Prover

variable {Operation α β : Type} (P : Prover Operation)

/-- The joint law of the result of `program` and of the prover's final state, when `program`
interacts with `P` starting from the prover state `s`. Private coins are fresh fair samples. -/
noncomputable def run (program : WordOracleComp Operation α) (s : P.State) :
    PMF (α × P.State) :=
  (OracleComp.interpret
    (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) P.respond)
      program).run s

/-- `Prover.run` is the run against the prover as a stateful oracle with word queries and
replies. -/
theorem run_eq_runWith (program : WordOracleComp Operation α) (s : P.State) :
    P.run program s = ProbOracleComp.runWith P.respond program s := rfl

@[simp] theorem run_pure (a : α) (s : P.State) :
    P.run (pure a : WordOracleComp Operation α) s = PMF.pure (a, s) := rfl

theorem run_bind (program : WordOracleComp Operation α) (next : α → WordOracleComp Operation β)
    (s : P.State) :
    P.run (program >>= next) s = (P.run program s).bind fun x => P.run (next x.1) x.2 := by
  simp only [run, OracleComp.interpret_bind, StateT.run_bind]
  rfl

theorem run_map (f : α → β) (program : WordOracleComp Operation α) (s : P.State) :
    P.run (f <$> program) s = (P.run program s).map (Prod.map f id) := by
  simp only [run, OracleComp.interpret_map, StateT.run_map]
  rfl

/-- Private coins do not involve the prover, whose state is unchanged. -/
@[simp] theorem run_sample (program : ProbComp α) (s : P.State) :
    P.run (ProbOracleComp.sample program) s = (ProbComp.eval program).map (·, s) :=
  ProbOracleComp.run_interpret_sample _ _ _

/-- A message is answered by the prover's response function. -/
@[simp] theorem run_query (q : Operation × List Bool) (s : P.State) :
    P.run (ProbOracleComp.query q) s = (P.respond q).run s := by
  simp only [run, ProbOracleComp.interpret_query]

/-- The deterministic prover answering every message with `reply`. -/
noncomputable def const (reply : List Bool) : Prover Operation where
  State := Unit
  init := ()
  respond _ s := PMF.pure (reply, s)

end Prover

variable {Operation α : Type}

/-- The probability that `verifier` accepts when interacting with the prover `P`. -/
noncomputable def acceptProb (verifier : WordOracleComp Operation Bool) (P : Prover Operation) :
    ENNReal :=
  (P.run verifier P.init).map Prod.fst true

/-- The acceptance probability is that of the verifier against the prover as a stateful oracle,
from its initial state. -/
theorem acceptProb_eq_acceptProbWith (verifier : WordOracleComp Operation Bool)
    (P : Prover Operation) :
    acceptProb verifier P = ProbOracleComp.acceptProbWith P.respond verifier P.init := rfl

/-- The acceptance probability sums the masses of the accepting outcomes over final states. -/
theorem acceptProb_eq_tsum (verifier : WordOracleComp Operation Bool) (P : Prover Operation) :
    acceptProb verifier P = ∑' s, P.run verifier P.init (true, s) := by
  rw [acceptProb, PMF.map_apply, ENNReal.tsum_prod', tsum_bool]
  simp

/-- Private coins drawn before any message average the acceptance probabilities of the
continuations. -/
theorem acceptProb_sample_bind {β : Type} (program : ProbComp β)
    (next : β → WordOracleComp Operation Bool) (P : Prover Operation) :
    acceptProb (ProbOracleComp.sample program >>= next) P =
      ∑' b, ProbComp.eval program b * acceptProb (next b) P := by
  rw [acceptProb, Prover.run_bind, Prover.run_sample, PMF.bind_map, PMF.map_bind, PMF.bind_apply]
  rfl

/-- A verifier none of whose possible results accepts has acceptance probability zero. -/
theorem acceptProb_eq_zero {verifier : WordOracleComp Operation Bool} (P : Prover Operation)
    (h : ∀ x ∈ (P.run verifier P.init).support, x.1 = false) : acceptProb verifier P = 0 := by
  rw [acceptProb, PMF.apply_eq_zero_iff, PMF.support_map]
  rintro ⟨x, hx, hx'⟩
  simp [h x hx] at hx'

/-- `verifier` is an interactive proof for `A` with completeness `completeness` and soundness
error `soundness`: on every member of `A` some prover is accepted with probability at least
`completeness`, and on every non-member every prover is accepted with probability at most
`soundness`. -/
structure IsInteractiveProof (verifier : α → WordOracleComp Operation Bool) (A : Set α)
    (completeness soundness : ENNReal) : Prop where
  complete : ∀ a ∈ A, ∃ P : Prover Operation, completeness ≤ acceptProb (verifier a) P
  sound : ∀ a ∉ A, ∀ P : Prover Operation, acceptProb (verifier a) P ≤ soundness

/-- Weakening the thresholds preserves an interactive proof. -/
theorem IsInteractiveProof.mono {verifier : α → WordOracleComp Operation Bool} {A : Set α}
    {c c' s s' : ENNReal} (h : IsInteractiveProof verifier A c s) (hc : c' ≤ c) (hs : s ≤ s') :
    IsInteractiveProof verifier A c' s' where
  complete a ha := (h.complete a ha).imp fun _ hP => hc.trans hP
  sound a ha P := (h.sound a ha P).trans hs

/-- The problems with interactive proofs whose verifiers are strict oracle PPT, with completeness
`2 / 3` and soundness error `1 / 3`, with respect to the encoding `enc` of instances. -/
def IP (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ verifier : α → WordOracleComp Unit Bool,
    IsOraclePPTOn enc encBool verifier ∧ IsInteractiveProof verifier A (2 / 3) (1 / 3)}

variable {enc : α ↪ List Bool}

theorem mem_IP {A : Set α} : A ∈ IP enc ↔ ∃ verifier : α → WordOracleComp Unit Bool,
    IsOraclePPTOn enc encBool verifier ∧ IsInteractiveProof verifier A (2 / 3) (1 / 3) :=
  Iff.rfl

/-- An efficient interactive proof with at least the class thresholds puts a problem in `IP`. -/
theorem mem_IP_of {A : Set α} {verifier : α → WordOracleComp Unit Bool} {c s : ENNReal}
    (hV : IsOraclePPTOn enc encBool verifier) (h : IsInteractiveProof verifier A c s)
    (hc : 2 / 3 ≤ c) (hs : s ≤ 1 / 3) : A ∈ IP enc :=
  ⟨verifier, hV, h.mono hc hs⟩

/-- An `IP` verifier exchanges polynomially many messages of polynomial length: one polynomial in
the instance length bounds the number of messages and the length of each, against every prover. -/
theorem exists_queryBounds_of_mem_IP {A : Set α} (h : A ∈ IP enc) :
    ∃ verifier : α → WordOracleComp Unit Bool, IsOraclePPTOn enc encBool verifier ∧
      IsInteractiveProof verifier A (2 / 3) (1 / 3) ∧ ∃ c d : ℕ, ∀ a,
        (verifier a).IsQueryBounded (c * ((enc a).length + 1) ^ d) ∧
          (verifier a).QueriesSatisfy fun message =>
            message.2.length ≤ c * ((enc a).length + 1) ^ d := by
  obtain ⟨verifier, hV, hproof⟩ := h
  exact ⟨verifier, hV, hproof, hV.query_bounds⟩

/-! ### `NP ⊆ IP` -/

/-- The one-message interactive proof of a problem with verifier `V` and certificate length
`p`: ask the prover for a certificate, read the first `p (enc a).length` bits of its reply, and
run `V` on them when there are that many. -/
def npVerifier (enc : α ↪ List Bool) (p : Polynomial ℕ) (V : α × List Bool → Bool)
    (a : α) : WordOracleComp Unit Bool :=
  (fun w => decide (w.length = p.eval (enc a).length) && V (a, w)) <$>
    (List.take (p.eval (enc a).length) <$> ProbOracleComp.query ((), []))

/-- The one-message verifier of a polynomial-time `NP` verifier is strict oracle PPT: it reads only
a polynomially long prefix of the prover's reply. -/
private theorem isOraclePPTOn_npVerifier {p : Polynomial ℕ} {V : α × List Bool → Bool}
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool) :
    IsOraclePPTOn enc encBool (npVerifier enc p V) := by
  unfold npVerifier
  refine IsOraclePPTOn.map_with' (IsOraclePPTOn.query_take' () (by fun_prop) ?_) ?_
  · exact (ComputableInPolyTime.unary_eval p).comp (ComputableInPolyTime.encoding_length enc)
  · refine ComputableInPolyTime.bool_and' ?_ (by simpa only [Prod.mk.eta] using hV)
    exact (ComputableInPolyTime.length_bits.comp (.snd enc encBits)).decide_eq'
      (((ComputableInPolyTime.unary_eval p).comp
        (ComputableInPolyTime.encoding_length enc)).comp (.fst enc encBits))

/-- Sending a certificate of the right length makes the verifier accept exactly when `V` accepts
the certificate. -/
theorem acceptProb_npVerifier_const {p : Polynomial ℕ} {V : α × List Bool → Bool} {a : α}
    {w : List Bool} (hw : w.length = p.eval (enc a).length) :
    acceptProb (npVerifier enc p V a) (Prover.const w) = if V (a, w) then 1 else 0 := by
  simp only [acceptProb, npVerifier, Prover.run_map, Prover.run_query, Prover.const, StateT.run,
    PMF.pure_map, PMF.pure_apply, Prod.map_fst, List.take_of_length_le hw.le, hw, decide_true,
    Bool.true_and, eq_comm (a := true)]

/-- **`NP ⊆ IP`**, with one message, completeness `1` and soundness error `0`. -/
theorem NP_subset_IP (enc : α ↪ List Bool) : NP enc ⊆ IP enc := by
  rintro A ⟨p, V, hV, hA⟩
  refine mem_IP_of (isOraclePPTOn_npVerifier (p := p) hV) (c := 1) (s := 0)
    ⟨fun a ha => ?_, fun a ha P => ?_⟩ (ENNReal.div_le_of_le_mul (by norm_num)) bot_le
  · obtain ⟨w, hw, hVw⟩ := (hA a).1 ha
    refine ⟨Prover.const w, ?_⟩
    rw [acceptProb_npVerifier_const hw, hVw]
    rfl
  · refine (acceptProb_eq_zero P fun x hx => ?_).le
    simp only [npVerifier, Prover.run_map, Prover.run_query, PMF.support_map] at hx
    obtain ⟨y, ⟨z, _, rfl⟩, rfl⟩ := hx
    by_contra hacc
    simp only [Prod.map_fst, Bool.not_eq_false, Bool.and_eq_true, decide_eq_true_eq] at hacc
    exact ha ((hA a).2 ⟨_, hacc.1, hacc.2⟩)

/-! ### `BPP ⊆ IP` -/

/-- The interactive proof without messages for a bounded-error decider `V` with random strings of
length `p`: sample a random string and run `V`. -/
private noncomputable def bppVerifier (enc : α ↪ List Bool) (p : Polynomial ℕ)
    (V : α × List Bool → Bool) (a : α) : WordOracleComp Unit Bool :=
  ProbOracleComp.sample ((fun r => V (a, r)) <$> BitString.sampleList (p.eval (enc a).length))

/-- The verifier without messages of a polynomial-time decider is strict oracle PPT. -/
private theorem isOraclePPTOn_bppVerifier {p : Polynomial ℕ} {V : α × List Bool → Bool}
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool) :
    IsOraclePPTOn enc encBool (bppVerifier enc p V) := by
  have hcount : ComputableInPolyTime (fun a => p.eval (enc a).length) enc encUnary := by
    fun_prop
  exact (IsPPTOn.map_with (f := fun a r => V (a, r)) hcount.sampleList hV).isOraclePPTOn

/-- The verifier without messages accepts every prover with the fraction of accepted random
strings. -/
private theorem acceptProb_bppVerifier {p : Polynomial ℕ} {V : α × List Bool → Bool} (a : α)
    (P : Prover Unit) :
    acceptProb (bppVerifier enc p V a) P =
      (Finset.univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
        V (a, List.ofFn r) = true).card / 2 ^ p.eval (enc a).length := by
  simp only [acceptProb, bppVerifier, Prover.run_sample, PMF.map_comp, ProbComp.eval_map,
    BitString.eval_sampleList]
  exact BitString.uniformList_map_apply _ _ true

private theorem natCast_div_le_natCast_div {a b c d : ℕ} (hb : b ≠ 0) (hd : d ≠ 0)
    (h : a * d ≤ b * c) : (a : ENNReal) / b ≤ (c : ENNReal) / d := by
  rw [ENNReal.div_le_iff_le_mul (Or.inl (by exact_mod_cast hb)) (Or.inl (ENNReal.natCast_ne_top _)),
    ← ENNReal.mul_div_right_comm, ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast hd))
      (Or.inl (ENNReal.natCast_ne_top _))]
  exact_mod_cast h.trans_eq (mul_comm b c)

/-- **`BPP ⊆ IP`**, without messages. -/
theorem BPP_subset_IP (enc : α ↪ List Bool) : BPP enc ⊆ IP enc := by
  rintro A ⟨p, V, hV, hA⟩
  refine ⟨_, isOraclePPTOn_bppVerifier (p := p) hV, fun a ha => ⟨Prover.const [], ?_⟩,
    fun a ha P => ?_⟩ <;> rw [acceptProb_bppVerifier]
  · have h := (hA a).1 ha
    unfold BoundedErrorAt at h
    exact_mod_cast natCast_div_le_natCast_div (a := 2) (b := 3)
      (d := 2 ^ p.eval (enc a).length) three_ne_zero (pow_pos two_pos _).ne' (by omega)
  · have h := (hA a).2 ha
    unfold BoundedErrorAt at h
    have hsum := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun r : Fin (p.eval (enc a).length) → Bool => V (a, List.ofFn r) = true)
    simp only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin] at hsum
    exact_mod_cast natCast_div_le_natCast_div (c := 1) (d := 3)
      (b := 2 ^ p.eval (enc a).length) (pow_pos two_pos _).ne' three_ne_zero (by omega)

end Cslib.Complexity
