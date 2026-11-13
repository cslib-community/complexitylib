/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.IP.PerfectSoundness
import CslibFrontier.Computability.Probabilistic.QueryBounds

/-!
# Deterministic interactive proofs: `dIP = NP`

`dIP` is the class of problems with deterministic interactive proofs
[Arora and Barak, Definition 8.2][AroraBarak07], and it equals `NP`
(`Cslib.Complexity.dIP_eq_NP`) [Arora and Barak, Theorem 8.3][AroraBarak07].

`dIP` is the deterministic special case of `Cslib.Complexity.IP`, in the same interaction model.
The verifier is a word-query program without private coins (`Cslib.Complexity.WordQueryComp`), the
programs of `Cslib.Complexity.ComputableInPolyTimeWithOracle`; it is run as an `IP` verifier by
sending each of its requests to the prover (`OracleComp.interpret ProbOracleComp.query`). Its
efficiency is the strict oracle PPT certificate of `IP`, `Cslib.Probability.IsOraclePPTOn`: one
finite machine and one polynomial clock `c * (n + 1) ^ d` realize the verifier against every
stateful prover, charging the writing of messages and the reading of replies. So the verifier runs
in polynomial time, and it exchanges polynomially many messages of polynomial length and reads only
a polynomial prefix of every reply (`Cslib.Complexity.exists_queryBounds_of_mem_dIP`). The number of
rounds is therefore polynomial, as Arora and Barak require of `dIP`. Completeness is `1` and the
soundness error is `0`, against the randomized stateful provers of `IP`. Without coins, a verifier
accepts against a deterministic prover with probability `0` or `1`, so these thresholds are the
"accepts" and "rejects" of the definition.

**Source correction.** The soundness condition of the January 2007 draft of Definition 8.2 reads
`x ∉ L ⇒ ∀ P, out_V⟨V, P⟩(x) = 1`, an evident typo for `= 0`; the corrected condition is used.

The two inclusions:

* `NP ⊆ dIP`: the one-message verifier `Cslib.Complexity.npVerifier` of `NP ⊆ IP` asks for a
  certificate and checks it; it uses no coins (`Cslib.Complexity.NP_subset_dIP`).
* `dIP ⊆ NP`: a deterministic interactive proof has perfect soundness, so its accepting transcripts
  are `NP` certificates (`Cslib.Complexity.IsInteractiveProof.mem_NP`). The certificate is a
  transcript of at most `t` messages and replies of at most `t` bits each, where `t` is the clock,
  together with `t` coins of the realizing machine, which a coin-free verifier ignores; the replay
  that checks it runs in polynomial time (`Cslib.Complexity.dIP_subset_NP`).

## Main definitions

* `Cslib.Complexity.dIP`: deterministic interactive proofs.

## Main results

* `Cslib.Complexity.exists_queryBounds_of_mem_dIP`: polynomially many messages of polynomial
  length.
* `Cslib.Complexity.dIP_subset_IP`: deterministic interactive proofs are interactive proofs.
* `Cslib.Complexity.NP_subset_dIP`, `Cslib.Complexity.dIP_subset_NP`,
  `Cslib.Complexity.dIP_eq_NP`: `dIP = NP`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, web draft
  2007-01-08][AroraBarak07]
* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, draft
  r5][Goldreich2007DraftR5]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Probability Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-- The problems with deterministic interactive proofs
[Arora and Barak, Definition 8.2][AroraBarak07], with respect to the encoding `enc` of instances:
interactive proofs (`IsInteractiveProof`) with completeness `1` and soundness error `0` whose
verifier is a word-query program without private coins, run against the prover, and strict oracle
PPT as an `IP` verifier. -/
def dIP (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ verifier : α → WordQueryComp Unit Bool,
    IsOraclePPTOn enc encBool (fun a => OracleComp.interpret ProbOracleComp.query (verifier a)) ∧
      IsInteractiveProof (fun a => OracleComp.interpret ProbOracleComp.query (verifier a)) A 1 0}

theorem mem_dIP {A : Set α} : A ∈ dIP enc ↔ ∃ verifier : α → WordQueryComp Unit Bool,
    IsOraclePPTOn enc encBool (fun a => OracleComp.interpret ProbOracleComp.query (verifier a)) ∧
      IsInteractiveProof (fun a => OracleComp.interpret ProbOracleComp.query (verifier a)) A 1 0 :=
  Iff.rfl

/-- A `dIP` verifier exchanges polynomially many messages of polynomial length: one polynomial in
the instance length bounds the number of messages and the length of each, against every prover.
It also reads only a polynomial prefix of every reply, since its clock charges every bit read. -/
theorem exists_queryBounds_of_mem_dIP {A : Set α} (h : A ∈ dIP enc) :
    ∃ verifier : α → WordQueryComp Unit Bool,
      IsOraclePPTOn enc encBool (fun a => OracleComp.interpret ProbOracleComp.query (verifier a)) ∧
      IsInteractiveProof (fun a => OracleComp.interpret ProbOracleComp.query (verifier a)) A 1 0 ∧
      ∃ c d : ℕ, ∀ a,
        (OracleComp.interpret ProbOracleComp.query (verifier a) :
          WordOracleComp Unit Bool).IsQueryBounded (c * ((enc a).length + 1) ^ d) ∧
        (OracleComp.interpret ProbOracleComp.query (verifier a) :
          WordOracleComp Unit Bool).QueriesSatisfy fun message =>
            message.2.length ≤ c * ((enc a).length + 1) ^ d := by
  obtain ⟨verifier, hV, hproof⟩ := h
  exact ⟨verifier, hV, hproof, hV.query_bounds⟩

/-- **Deterministic interactive proofs are interactive proofs**: `dIP ⊆ IP`. -/
theorem dIP_subset_IP (enc : α ↪ List Bool) : dIP enc ⊆ IP enc := fun _ ⟨_, hV, h⟩ =>
  mem_IP_of hV h (ENNReal.div_le_of_le_mul (by norm_num)) bot_le

/-- The coin-free one-message verifier of an `NP` verifier: it asks the prover for a certificate
and checks the prefix of the reply of the certificate length. Run against the prover, it is
`Cslib.Complexity.npVerifier`. -/
def npQueryVerifier (enc : α ↪ List Bool) (p : Polynomial ℕ) (V : α × List Bool → Bool) (a : α) :
    WordQueryComp Unit Bool :=
  (fun w => decide (w.length = p.eval (enc a).length) && V (a, w)) <$>
    (List.take (p.eval (enc a).length) <$> OracleComp.query ((), []))

theorem interpret_npQueryVerifier (p : Polynomial ℕ) (V : α × List Bool → Bool) (a : α) :
    OracleComp.interpret ProbOracleComp.query (npQueryVerifier enc p V a) = npVerifier enc p V a :=
  by simp [npQueryVerifier, npVerifier, OracleComp.interpret_map, OracleComp.interpret_query]

/-- **`NP ⊆ dIP`** [Arora and Barak, Theorem 8.3][AroraBarak07]: with one message, the prover
sending a certificate. -/
theorem NP_subset_dIP (enc : α ↪ List Bool) : NP enc ⊆ dIP enc := by
  rintro A ⟨p, V, hV, hA⟩
  refine ⟨npQueryVerifier enc p V, ?_, ?_⟩ <;> simp only [interpret_npQueryVerifier]
  · exact isOraclePPTOn_npVerifier hV
  · exact isInteractiveProof_npVerifier hA

/-- **`dIP ⊆ NP`** [Arora and Barak, Theorem 8.3][AroraBarak07]: an accepting transcript is a
certificate. This is the case of perfect soundness and perfect completeness of
`Cslib.Complexity.IsInteractiveProof.mem_NP`. -/
theorem dIP_subset_NP (enc : α ↪ List Bool) : dIP enc ⊆ NP enc := fun _ ⟨_, hV, h⟩ =>
  h.mem_NP hV one_pos

/-- **`dIP = NP`** [Arora and Barak, Theorem 8.3][AroraBarak07]: deterministic interactive proofs
with polynomially many rounds decide exactly the problems in `NP`. -/
theorem dIP_eq_NP (enc : α ↪ List Bool) : dIP enc = NP enc :=
  (dIP_subset_NP enc).antisymm (NP_subset_dIP enc)

end Cslib.Complexity
