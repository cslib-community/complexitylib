/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import Complexity.Computability.Probabilistic.Oracle.Parameter
public import Complexity.Computability.Probabilistic.Parameter
public import Complexity.Crypto.Game
import Complexity.Probability.PMF.Bind
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Complexity.Computability.Probabilistic.Oracle.Composition
import Complexity.Computability.Probabilistic.Oracle.Tidy
import Complexity.Languages.Probabilistic.Oracle.Simulation
import Complexity.Crypto.Negligible.Basic
import Complexity.Probability.PMF
import Complexity.Tactic.PolyTime
import Complexity.Tactic.PPT

/-!
# Uniform digital signature schemes and existential unforgeability

A uniform digital signature scheme (`SignatureScheme`) consists of a strict probabilistic
polynomial-time key generator `keyGen`, a strict probabilistic polynomial-time signing algorithm
`sign`, and a deterministic polynomial-time verification algorithm `verify` that accepts every
signature produced by `sign` on an `n`-bit message under a key pair sampled at security parameter
`n`. The message space at parameter `n` is exactly the `n`-bit words; this module does not
claim security for arbitrary polynomial-length message families.

We formalize two adaptive chosen-message security notions against uniform strict oracle-PPT forgers
(`IsOraclePPT`):

* **Existential unforgeability under adaptive chosen-message attack (`eufCmaGame`, `EUFCMA`)**:
  the forger receives the unary security parameter `n` and public verification key `pk`, has
  adaptive oracle access to `signingOracle sk` on arbitrary messages, and wins by outputting a valid
  `(msg, sig)` pair with `msg.length = n` such that `msg` was never queried to the signing oracle.
* **Existential unforgeability under one-time adaptive chosen-message attack (`eufOneTimeGame`,
  `OneTimeEUFCMA`)**: the signing oracle `oneTimeSigningOracle sk` answers at most the first
  signing query and returns the empty word on any subsequent query. Every `EUFCMA`-secure scheme is
  a fortiori `OneTimeEUFCMA`-secure (`SignatureScheme.EUFCMA.oneTimeEUFCMA`).

## Main definitions

* `Cslib.Crypto.Forger`: adaptive oracle adversary outputting a `(message, signature)` pair.
* `Cslib.Crypto.SignatureScheme`: uniform digital signature scheme on `n`-bit messages.
* `Cslib.Crypto.SignatureScheme.signingOracle`, `eufCmaGame`, `EUFCMA`: full adaptive EUF-CMA
  experiment and security predicate.
* `Cslib.Crypto.SignatureScheme.oneTimeSigningOracle`, `eufOneTimeGame`, `OneTimeEUFCMA`: one-time
  adaptive EUF-CMA experiment and security predicate.

## Main results

* `Cslib.Crypto.SignatureScheme.isPPTOn_eufCmaGame`, `isPPT_eufCmaGame`: strict PPT certificates
  for the full EUF-CMA experiment.
* `Cslib.Crypto.SignatureScheme.isPPTOn_eufOneTimeGame`, `isPPT_eufOneTimeGame`: strict PPT
  certificates for the one-time EUF-CMA experiment.
* `Cslib.Crypto.SignatureScheme.EUFCMA.oneTimeEUFCMA`: full EUF-CMA security implies one-time
  EUF-CMA security.

## References

* [S. Goldwasser, S. Micali, R. L. Rivest, *A Digital Signature Scheme Secure Against Adaptive
  Chosen-Message Attacks*][GoldwasserMicaliRivest1988]
* [L. Lamport, *Constructing Digital Signatures from a One-Way Function*][Lamport1979]
* [J. Rompel, *One-Way Functions are Necessary and Sufficient for Secure Signatures*][Rompel1990]
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal

/-- An adaptive forger receives a unary security parameter and a public verification key, queries a
signing oracle on chosen messages, and outputs a candidate `(message, signature)` pair. -/
abbrev Forger := ℕ → List Bool → WordOracleComp Unit (List Bool × List Bool)

/-- A uniform digital signature scheme on `n`-bit messages at security parameter `n`, with strict
polynomial-time key generation and signing, deterministic polynomial-time verification, and perfect
completeness on supported key pairs, `n`-bit messages, and signatures. -/
structure SignatureScheme where
  /-- Sample a public verification key and secret signing key `(pk, sk)` at unary parameter `n`. -/
  keyGen : ℕ → ProbComp (List Bool × List Bool)
  /-- Sign a message `msg` using the secret signing key `sk`. -/
  sign : List Bool → List Bool → ProbComp (List Bool)
  /-- Deterministically verify a candidate signature `sig` on `msg` under public key `pk`. -/
  verify : List Bool → List Bool → List Bool → Bool
  /-- Key generation is uniformly strict PPT in the unary security parameter. -/
  keyGen_ppt : IsPPTOn encUnary (encPair encBits encBits) keyGen
  /-- Signing is uniformly strict PPT in the encoded secret key and message. -/
  sign_ppt : IsPPTOn (encPair encBits encBits) encBits (fun p => sign p.1 p.2)
  /-- Verification is computable in plain polynomial time on `(pk, msg, sig)`. -/
  verify_polyTime : ComputableInPolyTime
    (fun p : List Bool × List Bool × List Bool => verify p.1 p.2.1 p.2.2)
    (encPair encBits (encPair encBits encBits)) encBool
  /-- Every signature produced by `sign` on an `n`-bit message under a supported key pair at
  security parameter `n` is accepted by `verify`. -/
  verify_sign : ∀ n keys, keys ∈ (ProbComp.eval (keyGen n)).support →
    ∀ msg, msg.length = n →
    ∀ sig, sig ∈ (ProbComp.eval (sign keys.2 msg)).support →
    verify keys.1 msg sig = true

/-- The equivalent tidy contract used internally by compositional proofs. -/
theorem SignatureScheme.verify_polyTime_tidy (h : SignatureScheme) :
    ComputableTidilyInPolyTime
    (fun p : List Bool × List Bool × List Bool => h.verify p.1 p.2.1 p.2.2)
    (encPair encBits (encPair encBits encBits)) encBool := by
  simpa only [← computableInPolyTime_iff_computableTidilyInPolyTime] using h.verify_polyTime

namespace SignatureScheme

attribute [program_certificate] keyGen_ppt sign_ppt verify_polyTime

@[program_certificate, fun_prop]
theorem isPPTOn_keyGen_comp (S : SignatureScheme) {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} (hn : ComputableTidilyInPolyTime n encIn encUnary) :
    IsPPTOn encIn (encPair encBits encBits) (fun a => S.keyGen (n a)) :=
  S.keyGen_ppt.preprocess (ComputableInPolyTime.of_tidy hn)

@[program_certificate, fun_prop]
theorem isPPTOn_sign_comp (S : SignatureScheme) {γ : Type} {encIn : γ ↪ List Bool}
    {sk msg : γ → List Bool}
    (hsk : ComputableTidilyInPolyTime sk encIn encBits)
    (hmsg : ComputableTidilyInPolyTime msg encIn encBits) :
    IsPPTOn encIn encBits (fun a => S.sign (sk a) (msg a)) :=
  S.sign_ppt.preprocess (ComputableInPolyTime.of_tidy (hsk.prod hmsg))

@[program_certificate, fun_prop]
theorem computableTidilyInPolyTime_verify_comp (S : SignatureScheme)
    {γ : Type} {encIn : γ ↪ List Bool} {pk msg sig : γ → List Bool}
    (hpk : ComputableTidilyInPolyTime pk encIn encBits)
    (hmsg : ComputableTidilyInPolyTime msg encIn encBits)
    (hsig : ComputableTidilyInPolyTime sig encIn encBits) :
    ComputableTidilyInPolyTime (fun a => S.verify (pk a) (msg a) (sig a)) encIn encBool :=
  S.verify_polyTime.tidy.comp (hpk.prod (hmsg.prod hsig))

@[fun_prop]
private theorem computableTidilyInPolyTime_contains {γ : Type} {encIn : γ ↪ List Bool}
    {list : γ → List (List Bool)} {elem : γ → List Bool}
    (hlist : ComputableTidilyInPolyTime list encIn (encList encBits))
    (helem : ComputableTidilyInPolyTime elem encIn encBits) :
    ComputableTidilyInPolyTime (fun a => (list a).contains (elem a)) encIn encBool := by
  have heq : (fun a => (list a).contains (elem a)) =
      (fun a => (list a).any (fun x => elem a == x)) := by
    funext a
    rw [Bool.eq_iff_iff, List.contains_iff_mem, List.any_eq_true]
    simp only [beq_iff_eq]
    exact ⟨fun h => ⟨elem a, h, rfl⟩, fun ⟨_, h, heq⟩ => heq ▸ h⟩
  rw [heq]
  exact ComputableTidilyInPolyTime.anyWithInput (test := fun a x => elem a == x) hlist (by polytime)

/-! ### Full adaptive chosen-message security (`EUFCMA`) -/

/-- Stateful signing oracle that signs the requested message under `sk` and prepends the message to
the list of queried messages. -/
def signingOracle (S : SignatureScheme) (sk : List Bool)
    (request : Unit × List Bool) : StateT (List (List Bool)) ProbComp (List Bool) :=
  fun queried => do
    let sig ← S.sign sk request.2
    return (sig, request.2 :: queried)

/-- The EUF-CMA experiment: sample `(pk, sk) ← S.keyGen n`, run the adaptive forger on `(n, pk)`
with oracle access to `S.signingOracle sk`, and accept when the forger outputs a valid signature on
an `n`-bit message that was never queried to the signing oracle. -/
def eufCmaGame (S : SignatureScheme) (adversary : Forger) (n : ℕ) :
    ProbComp Bool := do
  let keys ← S.keyGen n
  let out ← (OracleComp.interpret
    (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifFin k))
      (S.signingOracle keys.2)) (adversary n keys.1)).run []
  return (out.1.1.length == n) && !out.2.contains out.1.1 &&
    S.verify keys.1 out.1.1 out.1.2

/-- Run the complete EUF-CMA experiment on its unary security parameter for any oracle-PPT
forger. -/
@[program_certificate]
theorem isPPTOn_eufCmaGame (S : SignatureScheme) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPTOn encUnary encBool (S.eufCmaGame adversary) := by
  obtain ⟨c, d, hlen⟩ := S.sign_ppt.length_le
  have hhandler : IsPPTOn
      (encPair (encPair encUnary (encPair encBits encBits))
        (encPair (encPair (encFinite Unit) encBits) (encList encBits)))
      (encPair encBits (encList encBits))
      (fun pair : (ℕ × (List Bool × List Bool)) × ((Unit × List Bool) × List (List Bool)) =>
        S.signingOracle pair.1.2.2 pair.2.1 pair.2.2) := by
    unfold signingOracle
    ppt
  have hrun : IsPPTOn (encPair encUnary (encPair encBits encBits))
      (encPair (encPair encBits encBits) (encList encBits))
      (fun caller : ℕ × (List Bool × List Bool) =>
        (OracleComp.interpret
          (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifFin k))
            (S.signingOracle caller.2.2)) (adversary caller.1 caller.2.1)).run []) := by
    apply hadversary.run_interpret_preprocess
      (prepare := fun caller : ℕ × (List Bool × List Bool) => (caller.1, caller.2.1))
      (initial := fun _ => ([] : List (List Bool)))
      (resources := fun caller query =>
        c * (2 * caller.2.2.length + query.length + 2) ^ d + 2 * query.length + 2)
      (by fun_prop) hhandler (by fun_prop)
      (fun _ _ => True) (fun _ => trivial) (by fun_prop)
    intro caller request queried _ result hresult
    simp only [signingOracle, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hresult
    obtain ⟨sig, hsig, rfl⟩ := hresult
    have hsigLen := hlen (caller.2.2, request.2) sig hsig
    simp only [encBits_apply, length_encPair] at hsigLen
    refine ⟨trivial, by lia, ?_⟩
    simp only [encList_cons, List.length_append, length_frame, encBits_apply]
    lia
  have hpost : ComputableTidilyInPolyTime
      (fun pair : (ℕ × (List Bool × List Bool)) × ((List Bool × List Bool) × List (List Bool)) =>
        (pair.2.1.1.length == pair.1.1) && !pair.2.2.contains pair.2.1.1 &&
          S.verify pair.1.2.1 pair.2.1.1 pair.2.1.2)
      (encPair (encPair encUnary (encPair encBits encBits))
        (encPair (encPair encBits encBits) (encList encBits))) encBool := by
    polytime
  exact S.keyGen_ppt.bind_with (hrun.bind_with hpost.isPPTOn)

/-- The EUF-CMA experiment is uniformly strict PPT, independently of unused auxiliary input. -/
@[program_certificate]
theorem isPPT_eufCmaGame (S : SignatureScheme) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPT encBool (fun n _ => S.eufCmaGame adversary n) :=
  ((S.isPPTOn_eufCmaGame hadversary).preprocess (ComputableInPolyTime.fst _ _)).isPPT

/-- Existential unforgeability under adaptive chosen-message attack (EUF-CMA) against uniform
strict oracle-PPT adversaries. -/
def EUFCMA (S : SignatureScheme) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (S.eufCmaGame adversary n))
    (fun _ _ => PMF.pure false)
    (IsOraclePPT (encPair encBits encBits))

/-- Full EUF-CMA security gives negligible forgery probability for every oracle-PPT forger. -/
theorem EUFCMA.negligible {S : SignatureScheme} (h : S.EUFCMA)
    (adversary : Forger) (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    Negligible (fun n => Game.succProbability (ProbComp.eval (S.eufCmaGame adversary n))) := by
  simpa only [Game.advantage_pure_false] using h adversary hadversary

/-- Establish EUF-CMA security by bounding every oracle-PPT forger's success probability. -/
theorem EUFCMA.of_negligible {S : SignatureScheme}
    (h : ∀ adversary, IsOraclePPT (encPair encBits encBits) adversary →
      Negligible (fun n => Game.succProbability (ProbComp.eval (S.eufCmaGame adversary n)))) :
    S.EUFCMA := by
  intro adversary hadversary
  simpa only [Game.advantage_pure_false] using h adversary hadversary

/-! ### One-time adaptive chosen-message security (`OneTimeEUFCMA`) -/

/-- One-time signing oracle that answers at most the first signing query using `S.sign sk` and
returns the empty word without signing on any subsequent query. -/
def oneTimeSigningOracle (S : SignatureScheme) (sk : List Bool)
    (request : Unit × List Bool) : StateT (List (List Bool)) ProbComp (List Bool) :=
  fun queried =>
    if queried.isEmpty then do
      let sig ← S.sign sk request.2
      return (sig, [request.2])
    else
      return ([], queried)

/-- The one-time EUF-CMA experiment: sample `(pk, sk) ← S.keyGen n`, run the adaptive forger on
`(n, pk)` with oracle access to `S.oneTimeSigningOracle sk` (which answers at most one signing
query), and accept when the forger outputs a valid signature on an `n`-bit message distinct from
the queried message (if any). -/
def eufOneTimeGame (S : SignatureScheme) (adversary : Forger) (n : ℕ) :
    ProbComp Bool := do
  let keys ← S.keyGen n
  let out ← (OracleComp.interpret
    (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifFin k))
      (S.oneTimeSigningOracle keys.2)) (adversary n keys.1)).run []
  return (out.1.1.length == n) && !out.2.contains out.1.1 &&
    S.verify keys.1 out.1.1 out.1.2

/-- Running an oracle-PPT forger against `oneTimeSigningOracle` is uniformly strict PPT in the
unary security parameter, public key, and secret key. -/
@[program_certificate]
theorem isPPTOn_run_oneTimeSigningOracle (S : SignatureScheme) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPTOn (encPair encUnary (encPair encBits encBits))
      (encPair (encPair encBits encBits) (encList encBits))
      (fun caller : ℕ × (List Bool × List Bool) =>
        (OracleComp.interpret
          (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifFin k))
            (S.oneTimeSigningOracle caller.2.2)) (adversary caller.1 caller.2.1)).run []) := by
  obtain ⟨c, d, hlen⟩ := S.sign_ppt.length_le
  have hhandler : IsPPTOn
      (encPair (encPair encUnary (encPair encBits encBits))
        (encPair (encPair (encFinite Unit) encBits) (encList encBits)))
      (encPair encBits (encList encBits))
      (fun pair : (ℕ × (List Bool × List Bool)) × ((Unit × List Bool) × List (List Bool)) =>
        S.oneTimeSigningOracle pair.1.2.2 pair.2.1 pair.2.2) := by
    unfold oneTimeSigningOracle
    ppt
  apply hadversary.run_interpret_preprocess
    (prepare := fun caller : ℕ × (List Bool × List Bool) => (caller.1, caller.2.1))
    (initial := fun _ => ([] : List (List Bool)))
    (resources := fun caller query =>
      c * (2 * caller.2.2.length + query.length + 2) ^ d + 2 * query.length + 2)
    (by fun_prop) hhandler (by fun_prop)
    (fun _ _ => True) (fun _ => trivial) (by fun_prop)
  intro caller request queried _ result hresult
  unfold oneTimeSigningOracle at hresult
  split_ifs at hresult with hempty
  · simp only [ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hresult
    obtain ⟨sig, hsig, rfl⟩ := hresult
    have hsigLen := hlen (caller.2.2, request.2) sig hsig
    simp only [encBits_apply, length_encPair] at hsigLen
    refine ⟨trivial, by lia, ?_⟩
    rw [List.isEmpty_iff.mp hempty]
    simp only [encList_cons, encList_nil, List.length_append, List.length_nil, length_frame,
      encBits_apply]
    lia
  · simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hresult
    subst result
    exact ⟨trivial, by simp, by lia⟩

/-- Run the complete one-time EUF-CMA experiment on its unary security parameter for any oracle-PPT
forger. -/
@[program_certificate]
theorem isPPTOn_eufOneTimeGame (S : SignatureScheme) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPTOn encUnary encBool (S.eufOneTimeGame adversary) := by
  have hrun := S.isPPTOn_run_oneTimeSigningOracle hadversary
  have hpost : ComputableTidilyInPolyTime
      (fun pair : (ℕ × (List Bool × List Bool)) × ((List Bool × List Bool) × List (List Bool)) =>
        (pair.2.1.1.length == pair.1.1) && !pair.2.2.contains pair.2.1.1 &&
          S.verify pair.1.2.1 pair.2.1.1 pair.2.1.2)
      (encPair (encPair encUnary (encPair encBits encBits))
        (encPair (encPair encBits encBits) (encList encBits))) encBool := by
    polytime
  exact S.keyGen_ppt.bind_with (hrun.bind_with hpost.isPPTOn)

/-- The one-time EUF-CMA experiment is uniformly strict PPT, independently of unused auxiliary
input. -/
@[program_certificate]
theorem isPPT_eufOneTimeGame (S : SignatureScheme) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPT encBool (fun n _ => S.eufOneTimeGame adversary n) :=
  ((S.isPPTOn_eufOneTimeGame hadversary).preprocess (ComputableInPolyTime.fst _ _)).isPPT

/-- Existential unforgeability under one-time adaptive chosen-message attack against uniform strict
oracle-PPT adversaries. -/
def OneTimeEUFCMA (S : SignatureScheme) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (S.eufOneTimeGame adversary n))
    (fun _ _ => PMF.pure false)
    (IsOraclePPT (encPair encBits encBits))

/-- One-time EUF-CMA security gives negligible forgery probability for every oracle-PPT forger. -/
theorem OneTimeEUFCMA.negligible {S : SignatureScheme} (h : S.OneTimeEUFCMA)
    (adversary : Forger) (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    Negligible (fun n => Game.succProbability (ProbComp.eval (S.eufOneTimeGame adversary n))) := by
  simpa only [Game.advantage_pure_false] using h adversary hadversary

/-- Establish one-time EUF-CMA security by bounding every oracle-PPT forger's success
probability. -/
theorem OneTimeEUFCMA.of_negligible {S : SignatureScheme}
    (h : ∀ adversary, IsOraclePPT (encPair encBits encBits) adversary →
      Negligible (fun n => Game.succProbability (ProbComp.eval (S.eufOneTimeGame adversary n)))) :
    S.OneTimeEUFCMA := by
  intro adversary hadversary
  simpa only [Game.advantage_pure_false] using h adversary hadversary

/-- Starting from the empty query log, `oneTimeSigningOracle` records at most one queried
message. -/
theorem length_le_one_of_mem_support_run_oneTimeSigningOracle (S : SignatureScheme) {α : Type}
    (sk : List Bool) (prog : WordOracleComp Unit α) {result : α} {queried : List (List Bool)}
    (h : (result, queried) ∈ ((OracleComp.interpret
      (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifOracle k))
        (fun q s => ProbComp.eval (S.oneTimeSigningOracle sk q s))) prog).run []).support) :
    queried.length ≤ 1 := by
  refine ProbOracleComp.run_interpret_invariant
    (fun q s => ProbComp.eval (S.oneTimeSigningOracle sk q s))
    (fun s => s.length ≤ 1) ?_ prog [] (by simp) result queried h
  intro ⟨⟨⟩, req⟩ s hs a s' hmem
  unfold oneTimeSigningOracle at hmem
  split_ifs at hmem with hempty
  · simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
      PMF.mem_support_pure_iff] at hmem
    obtain ⟨_, _, heq⟩ := hmem
    cases heq
    simp
  · simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hmem
    cases hmem
    exact hs

private theorem run_oneTimeSigningOracle_apply_eq_zero_of_not_agree (S : SignatureScheme)
    {α : Type} (sk : List Bool) {agree : List Bool → Prop} (prog : WordOracleComp Unit α)
    {s queried' : List (List Bool)} (hs : ¬ ∀ r ∈ s, agree r) (hq' : ∀ r ∈ queried', agree r)
    (a : α) :
    ((OracleComp.interpret
      (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifOracle k))
        (fun q s => ProbComp.eval (S.oneTimeSigningOracle sk q s))) prog).run s) (a, queried') =
      0 := by
  rw [PMF.apply_eq_zero_iff]
  intro hmem
  have hbad : ¬ ∀ r ∈ queried', agree r := by
    refine ProbOracleComp.run_interpret_invariant
      (fun q s => ProbComp.eval (S.oneTimeSigningOracle sk q s))
      (fun state => ¬ ∀ r ∈ state, agree r) ?_ prog s hs a queried' hmem
    intro ⟨⟨⟩, req⟩ state hstate val next hnext
    unfold oneTimeSigningOracle at hnext
    split_ifs at hnext with hempty
    · rw [List.isEmpty_iff] at hempty
      subst hempty
      exact absurd (fun _ h => nomatch h) hstate
    · simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hnext
      cases hnext
      exact hstate
  exact hbad hq'

/-- If `S.sign sk₁` and `S.sign sk₂` agree on all requests satisfying `agree`, then running any
adaptive program against `oneTimeSigningOracle` under `sk₁` and `sk₂` assigns the same probability
to every outcome `(a, queried')` whose recorded query log satisfies `agree`. -/
theorem run_oneTimeSigningOracle_apply_eq_of_agree (S : SignatureScheme) {α : Type}
    (sk₁ sk₂ : List Bool) {agree : List Bool → Prop}
    (hagree : ∀ req, agree req → S.sign sk₁ req = S.sign sk₂ req)
    (prog : WordOracleComp Unit α) (s : List (List Bool)) (a : α)
    (queried' : List (List Bool)) (hq' : ∀ r ∈ queried', agree r) :
    ((OracleComp.interpret
      (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifOracle k))
        (fun q s => ProbComp.eval (S.oneTimeSigningOracle sk₁ q s))) prog).run s) (a, queried') =
    ((OracleComp.interpret
      (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifOracle k))
        (fun q s => ProbComp.eval (S.oneTimeSigningOracle sk₂ q s))) prog).run s)
      (a, queried') := by
  induction prog using PFunctor.FreeM.induction generalizing s with
  | pure x => rfl
  | lift_bind q cont ih =>
    change (((OracleComp.interpret (m := StateT (List (List Bool)) PMF) _
        (OracleComp.query q >>= cont)).run s) (a, queried')) =
      (((OracleComp.interpret (m := StateT (List (List Bool)) PMF) _
        (OracleComp.query q >>= cont)).run s) (a, queried'))
    simp only [OracleComp.interpret_bind, OracleComp.interpret_query, StateT.run_bind,
      PMF.monad_bind_eq_bind]
    cases q with
    | inl k =>
      change (((ProbComp.unifOracle k).map (·, s)).bind _) (a, queried') =
        (((ProbComp.unifOracle k).map (·, s)).bind _) (a, queried')
      simp only [PMF.bind_map, Function.comp_def, PMF.bind_apply]
      exact tsum_congr fun r => congrArg _ (ih r s)
    | inr req =>
      rcases req with ⟨⟨⟩, msg⟩
      change ((ProbComp.eval (S.oneTimeSigningOracle sk₁ ((), msg) s)).bind _) (a, queried') =
        ((ProbComp.eval (S.oneTimeSigningOracle sk₂ ((), msg) s)).bind _) (a, queried')
      rw [oneTimeSigningOracle, oneTimeSigningOracle]
      split_ifs with hempty
      · by_cases hmsg : agree msg
        · rw [hagree msg hmsg]
          simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind,
            PMF.bind_apply]
          exact tsum_congr fun sig => congrArg _ (ih sig [msg])
        · have hnot : ¬ ∀ r ∈ [msg], agree r := fun h => hmsg (h msg (List.mem_singleton_self _))
          simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind,
            PMF.bind_apply]
          have h1 (sig : List Bool) :
              ((OracleComp.interpret
                (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifOracle k))
                  (fun q s => ProbComp.eval (S.oneTimeSigningOracle sk₁ q s)))
                (cont sig)).run [msg]) (a, queried') = 0 :=
            run_oneTimeSigningOracle_apply_eq_zero_of_not_agree S sk₁ (cont sig) hnot hq' a
          have h2 (sig : List Bool) :
              ((OracleComp.interpret
                (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifOracle k))
                  (fun q s => ProbComp.eval (S.oneTimeSigningOracle sk₂ q s)))
                (cont sig)).run [msg]) (a, queried') = 0 :=
            run_oneTimeSigningOracle_apply_eq_zero_of_not_agree S sk₂ (cont sig) hnot hq' a
          simp [h1, h2]
      · simp only [ProbComp.eval_pure, PMF.pure_bind]
        exact ih [] s

/-! ### Reduction from one-time EUF-CMA to full EUF-CMA -/

/-- Open stateful handler that forwards at most the first signing request to the external signing
oracle (truncating the reply to `bound n msg.length`) and answers subsequent requests with `[]`. -/
def oneTimeFilterHandler (bound : ℕ → ℕ → ℕ) (caller : ℕ × List Bool)
    (request : Unit × List Bool) : StateT Bool (WordOracleComp Unit) (List Bool) :=
  fun alreadyQueried =>
    if alreadyQueried then
      pure ([], true)
    else
      (fun sig => (sig, true)) <$> (List.take (bound caller.1 request.2.length) <$>
        ProbOracleComp.query ((), request.2))

/-- Wrap an adaptive forger so that it issues at most one external signing query. -/
def limitToOneQuery (bound : ℕ → ℕ → ℕ) (adversary : Forger) : Forger :=
  fun n pk =>
    Prod.fst <$> (OracleComp.interpret
      (ProbOracleComp.handler
        (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
        (oneTimeFilterHandler bound (n, pk)))
      (adversary n pk)).run false

theorem isOraclePPT_limitToOneQuery {bound : ℕ → ℕ → ℕ}
    (hbound : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => bound p.1 p.2)
      (encPair encUnary encUnary) encUnary)
    {adversary : Forger} (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsOraclePPT (encPair encBits encBits) (limitToOneQuery bound adversary) := by
  have hhandler : IsOraclePPTOn
      (encPair (encPair encUnary encBits)
        (encPair (encPair (encFinite Unit) encBits) encBool))
      (encPair encBits encBool)
      (fun pair : (ℕ × List Bool) × ((Unit × List Bool) × Bool) =>
        oneTimeFilterHandler bound pair.1 pair.2.1 pair.2.2) := by
    unfold oneTimeFilterHandler
    have hprep1 : ComputableTidilyInPolyTime
        (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Bool) => (p.1.1, p.2.1.2.length))
        (encPair (encPair encUnary encBits)
          (encPair (encPair (encFinite Unit) encBits) encBool))
        (encPair encUnary encUnary) := by
      polytime
    have hbound' := hbound.comp hprep1
    have hq : IsOraclePPTOn
        (encPair (encPair encUnary encBits)
          (encPair (encPair (encFinite Unit) encBits) encBool))
        encBits
        (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Bool) =>
          List.take (bound p.1.1 p.2.1.2.length) <$> ProbOracleComp.query ((), p.2.1.2)) :=
      IsOraclePPTOn.query_take () (by polytime) hbound'
    have hpair : ComputableTidilyInPolyTime (fun sig : List Bool => (sig, true))
        encBits (encPair encBits encBool) := by
      polytime
    have hyes : IsOraclePPTOn
        (encPair (encPair encUnary encBits)
          (encPair (encPair (encFinite Unit) encBits) encBool))
        (encPair encBits encBool)
        (fun _ => pure ([], true)) :=
      (ComputableTidilyInPolyTime.const ([], true)).isOraclePPTOn (Operation := Unit)
    have hcond : ComputableTidilyInPolyTime
        (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Bool) => p.2.2)
        (encPair (encPair encUnary encBits)
          (encPair (encPair (encFinite Unit) encBits) encBool))
        encBool := by
      polytime
    exact IsOraclePPTOn.cond hcond hyes (hq.map hpair)
  have hrun : IsOraclePPTOn (encPair encUnary encBits)
      (encPair (encPair encBits encBits) encBool)
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (ProbOracleComp.handler
            (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
            (oneTimeFilterHandler bound caller))
          (adversary caller.1 caller.2)).run false) := by
    apply hadversary.run_interpret_preprocess_open
      (prepare := id)
      (initial := fun _ => false)
      (resources := fun caller query => bound caller.1 query.length + 1)
      (by fun_prop) hhandler (by fun_prop)
      (fun _ _ => True) (fun _ => trivial)
      (by
        have hprep2 : ComputableTidilyInPolyTime
            (fun pair : (ℕ × List Bool) × List Bool => (pair.1.1, pair.2.length))
            (encPair (encPair encUnary encBits) encBits)
            (encPair encUnary encUnary) := by
          polytime
        have hb := hbound.comp hprep2
        polytime)
    intro caller request state _ result hresult
    unfold oneTimeFilterHandler at hresult
    split_ifs at hresult with hstate
    · have heq := ProbOracleComp.eq_of_mem_support_pure hresult
      subst heq
      simp [encBool_apply]
    · obtain ⟨sig, hsig, rfl⟩ := ProbOracleComp.mem_support_map hresult
      obtain ⟨rawSig, _, rfl⟩ := ProbOracleComp.mem_support_map hsig
      refine ⟨trivial, ?_, ?_⟩
      · exact (List.length_take_le _ _).trans (by lia)
      · simp [encBool_apply]
  unfold limitToOneQuery
  exact (hrun.map (ComputableTidilyInPolyTime.fst _ _)).isOraclePPT

private theorem run_limitToOneQuery_eq_oneTimeSigningOracle (S : SignatureScheme)
    (bound : ℕ → ℕ → ℕ) (n : ℕ) (pk sk : List Bool)
    (hbound : ∀ msg sig, sig ∈ (ProbComp.eval (S.sign sk msg)).support →
      sig.length ≤ bound n msg.length)
    (prog : WordOracleComp Unit (List Bool × List Bool)) :
    ProbComp.eval (Prod.map Prod.fst id <$> ((OracleComp.interpret
      (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifFin k))
        (S.signingOracle sk))
      ((OracleComp.interpret
        (ProbOracleComp.handler
          (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
          (oneTimeFilterHandler bound (n, pk)))
        prog).run false)).run [])) =
    ProbComp.eval ((OracleComp.interpret
      (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifFin k))
        (S.oneTimeSigningOracle sk)) prog).run []) := by
  rw [ProbComp.eval_map, ProbOracleComp.eval_run_interpret, ProbOracleComp.eval_run_interpret,
    ProbOracleComp.run_interpret_run_interpret, PMF.map_comp]
  have hsim := ProbOracleComp.run_interpret_map_state_of_invariant
    (oracle := fun q (state : Bool × List (List Bool)) =>
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifOracle k))
          (fun q s => ProbComp.eval (S.signingOracle sk q s)))
        ((oneTimeFilterHandler bound (n, pk) q).run state.1)).run state.2).map
          (fun result => (result.1.1, result.1.2, result.2)))
    (oracle' := fun q s => ProbComp.eval (S.oneTimeSigningOracle sk q s))
    (represent := Prod.snd)
    (invariant := fun state : Bool × List (List Bool) => state.1 = !state.2.isEmpty)
    (preserve := by
      intro ⟨⟨⟩, msg⟩ ⟨alreadyQueried, queried⟩ hinv value ⟨nextQueried, nextList⟩ hmem
      simp only [PMF.mem_support_map_iff] at hmem
      obtain ⟨⟨⟨v, nq⟩, nl⟩, hmem, heq⟩ := hmem
      cases heq
      cases alreadyQueried
      · change ((v, nq), nl) ∈ ((OracleComp.interpret
            (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifOracle k))
              (fun q s => ProbComp.eval (S.signingOracle sk q s)))
            (oneTimeFilterHandler bound (n, pk) ((), msg) false)).run queried).support at hmem
        simp only [oneTimeFilterHandler, Bool.false_eq_true, ↓reduceIte, Functor.map_map,
          OracleComp.interpret_map, StateT.run_map, ProbOracleComp.interpret_query,
          PMF.monad_map_eq_map, PMF.mem_support_map_iff] at hmem
        obtain ⟨⟨rawSig, nl'⟩, hsig, hpair⟩ := hmem
        change (rawSig, nl') ∈
          (ProbComp.eval (S.signingOracle sk ((), msg) queried)).support at hsig
        simp only [signingOracle, ProbComp.eval_bind, ProbComp.eval_pure,
          PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hsig
        obtain ⟨sig, _, hsigEq⟩ := hsig
        cases hsigEq
        cases hpair
        rfl
      · change ((v, nq), nl) ∈ ((OracleComp.interpret
            (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifOracle k))
              (fun q s => ProbComp.eval (S.signingOracle sk q s)))
            (oneTimeFilterHandler bound (n, pk) ((), msg) true)).run queried).support at hmem
        simp only [oneTimeFilterHandler, ↓reduceIte, OracleComp.interpret_pure,
          StateT.run_pure, PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hmem
        cases hmem
        simpa using hinv)
    (step := by
      intro ⟨⟨⟩, msg⟩ ⟨alreadyQueried, queried⟩ hinv
      dsimp at hinv
      cases hq : queried.isEmpty
      · have halready : alreadyQueried = true := by simp [hinv, hq]
        subst halready
        change PMF.map (fun (a, s') => (a, s'.2))
            (((OracleComp.interpret
              (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifOracle k))
                (fun q s => ProbComp.eval (S.signingOracle sk q s)))
              (oneTimeFilterHandler bound (n, pk) ((), msg) true)).run queried).map
                (fun result => (result.1.1, result.1.2, result.2))) =
          ProbComp.eval (S.oneTimeSigningOracle sk ((), msg) queried)
        simp [oneTimeFilterHandler, oneTimeSigningOracle, hq, OracleComp.interpret_pure,
          StateT.run_pure, ProbComp.eval_pure]
      · have halready : alreadyQueried = false := by simp [hinv, hq]
        subst halready
        change PMF.map (fun (a, s') => (a, s'.2))
            (((OracleComp.interpret
              (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifOracle k))
                (fun q s => ProbComp.eval (S.signingOracle sk q s)))
              (oneTimeFilterHandler bound (n, pk) ((), msg) false)).run queried).map
                (fun result => (result.1.1, result.1.2, result.2))) =
          ProbComp.eval (S.oneTimeSigningOracle sk ((), msg) queried)
        simp only [oneTimeFilterHandler, Bool.false_eq_true, ↓reduceIte, Functor.map_map,
          OracleComp.interpret_map, StateT.run_map, ProbOracleComp.interpret_query,
          PMF.monad_map_eq_map, PMF.map_comp, Function.comp_def]
        change PMF.map (fun x : List Bool × List (List Bool) =>
            (x.1.take (bound n msg.length), x.2))
            (ProbComp.eval (S.signingOracle sk ((), msg) queried)) =
          ProbComp.eval (S.oneTimeSigningOracle sk ((), msg) queried)
        simp only [signingOracle, oneTimeSigningOracle, hq, ↓reduceIte,
          ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_bind]
        refine PMF.bind_congr_on_support _ _ _ fun sig hsig => ?_
        rw [List.isEmpty_iff.mp hq]
        simp [List.take_of_length_le (hbound msg sig hsig)])
    prog (false, []) rfl
  exact hsim

/-- Full EUF-CMA security implies one-time EUF-CMA security. -/
theorem EUFCMA.oneTimeEUFCMA {S : SignatureScheme} (h : S.EUFCMA) : S.OneTimeEUFCMA := by
  obtain ⟨ck, dk, hlenk⟩ := S.keyGen_ppt.length_le
  obtain ⟨cs, ds, hlens⟩ := S.sign_ppt.length_le
  let skBound (n : ℕ) : ℕ := ck * (n + 1) ^ dk
  let bound (n msgLen : ℕ) : ℕ := cs * (2 * skBound n + msgLen + 2) ^ ds
  have hbound_poly : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => bound p.1 p.2)
      (encPair encUnary encUnary) encUnary := by
    dsimp [bound, skBound]
    polytime
  apply OneTimeEUFCMA.of_negligible
  intro adversary hadversary
  have hred := h.negligible (limitToOneQuery bound adversary)
    (isOraclePPT_limitToOneQuery hbound_poly hadversary)
  refine hred.congr fun n => ?_
  congr 1
  simp only [eufOneTimeGame, eufCmaGame, ProbComp.eval_bind, ProbComp.eval_pure]
  refine PMF.bind_congr_on_support _ _ _ fun keys hkeys => ?_
  have hkeysLen := hlenk n keys hkeys
  simp only [encUnary_apply, List.length_replicate, length_encPair, encBits_apply] at hkeysLen
  have hskLen : keys.2.length ≤ skBound n := by
    dsimp [skBound]
    lia
  have hsigBound : ∀ msg sig, sig ∈ (ProbComp.eval (S.sign keys.2 msg)).support →
      sig.length ≤ bound n msg.length := by
    intro msg sig hsig
    have h1 := hlens (keys.2, msg) sig hsig
    simp only [length_encPair, encBits_apply] at h1
    have h2 : 2 * keys.2.length + 1 + msg.length + 1 ≤ 2 * skBound n + msg.length + 2 := by lia
    exact h1.trans (Nat.mul_le_mul_left cs (Nat.pow_le_pow_left h2 ds))
  have hrun := run_limitToOneQuery_eq_oneTimeSigningOracle S bound n keys.1 keys.2 hsigBound
    (adversary n keys.1)
  have hmap : ((OracleComp.interpret
      (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifFin k))
        (S.signingOracle keys.2))
      (limitToOneQuery bound adversary n keys.1)).run []) =
    Prod.map Prod.fst id <$> ((OracleComp.interpret
      (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifFin k))
        (S.signingOracle keys.2))
      ((OracleComp.interpret
        (ProbOracleComp.handler
          (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
          (oneTimeFilterHandler bound (n, keys.1)))
        (adversary n keys.1)).run false)).run []) := by
    unfold limitToOneQuery
    rw [OracleComp.interpret_map, StateT.run_map]
    rfl
  rw [hmap]
  exact congrArg (fun p : PMF ((List Bool × List Bool) × List (List Bool)) =>
    p.bind fun x => PMF.pure
      ((x.1.1.length == n) && !x.2.contains x.1.1 && S.verify keys.1 x.1.1 x.1.2)) hrun

end SignatureScheme

end Cslib.Crypto
