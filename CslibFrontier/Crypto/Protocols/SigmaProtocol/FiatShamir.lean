/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.SigmaProtocol.ForkingReduction
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Identification
public import CslibFrontier.Crypto.Protocols.Signature.RandomOracle
public import CslibFrontier.Languages.Probabilistic.Forking
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.BindFailure
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Union
import CslibFrontier.Languages.Probabilistic.Presample
import CslibFrontier.Languages.Probabilistic.UntilBad
import CslibFrontier.Languages.Probabilistic.RandomOracle
import CslibFrontier.Languages.Probabilistic.RandomOracle.Programming
import CslibFrontier.Probability.PMF

/-!
# Fiat–Shamir signatures

The Fiat–Shamir transform ([BonehShoup2023], Section 19.6.1) turns a Sigma protocol into a
signature scheme in the random-oracle model: to sign `m`, the prover commits to `t`, takes the
challenge `c := H(m, t)` and responds with `z`; the signature `(t, z)` verifies when
`(t, H(m, t), z)` is an accepting conversation.

The implementation permits an injective representation `hashPoint : (M × T) ↪ Query` and hashes
`hashPoint (m, t)`. Every `Query`, including points outside this image, is retained in the same
oracle table and charged to the hash-call budget. There is no image-membership test or decoder.
This representation generalization is original; the identity embedding recovers the typed model.

Honest signatures verify (`fiatShamir_correct`). With special soundness, special HVZK and
`δ`-unpredictable commitments ([BonehShoup2023], Definition 19.7), a forger making at most `Qs`
signing calls and `Qro` hash calls wins the random-oracle EUF-CMA experiment with probability `ε`
bounded by

`ε ≤ Qs · (Qs + Qro) · δ + (Qro + 1) / N + √((Qro + 1) · ε')`,

where `N` is the number of challenges and `ε'` the success probability of an explicit adversary
in the one-way game for the key generator (`succProbability_eufCmaGame_le`). This is
[BonehShoup2023], Equation 19.21, with `Qs · (Qs + Qro) · δ` in place of the slightly larger
`Qs · (Qs + Qro + 1) · δ`.

The proof follows [BonehShoup2023], Theorems 19.7 and 19.16, with the general forking lemma of
[BellareNeven2006] in place of the reduction through impersonation:

1. The signer is replaced by one that programs the oracle at `hashPoint (m, t)` with a fresh
   challenge.
   The two agree until the signer's commitment hits a point already in the oracle's table, which
   has probability at most `Qs · (Qs + Qro) · δ` (the difference lemma,
   `OracleComp.IdenticalUntilBad.bind_apply_le`, and `OracleComp.toOuterMeasure_bad_le`).
2. Special HVZK replaces the programming signer by the simulator, which needs no witness.
3. The simulated transcripts are drawn in advance, one per call
   (`OracleComp.IsQueryBounded.run_interpret_presample`).
4. The result is a program over the hash oracle alone, with explicit coins
   (`FiatShamir.forkingProgram`), that names the hash query of the forgery whenever the forger
   wins. It is the shared forking reduction `ForkingReduction.program` for the signer
   `FiatShamir.signer` and the final check `FiatShamir.check`. The forking lemma
   (`ForkingReduction.toReal_le_add_sqrt_fork_of_le`) and special soundness turn it into the
   one-way adversary `FiatShamir.reduction`.

These are exact probability laws for one Sigma protocol, key generator and forger; there is no
efficiency claim. The forger has explicit coins, so the reduction can rerun it.

## Main definitions

* `Cslib.Crypto.Protocols.SigmaProtocol.fiatShamir`: the Fiat–Shamir signature scheme.
* `Cslib.Crypto.Protocols.SigmaProtocol.FiatShamir.signer`,
  `Cslib.Crypto.Protocols.SigmaProtocol.FiatShamir.check`: signing from simulated transcripts and
  the final verification, as inputs to the shared forking reduction.
* `Cslib.Crypto.Protocols.SigmaProtocol.FiatShamir.forkingProgram`: the forger with simulated
  signing, as a program over the hash oracle.
* `Cslib.Crypto.Protocols.SigmaProtocol.FiatShamir.reduction`: the one-way adversary.

## Main results

* `Cslib.Crypto.Protocols.SigmaProtocol.fiatShamir_correct`: honest signatures verify.
* `Cslib.Crypto.Protocols.SigmaProtocol.succProbability_eufCmaGame_le`: the security bound.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Sections 19.2 and 19.6.1.
* [M. Bellare, G. Neven, *Multi-Signatures in the Plain Public-Key Model and a General Forking
  Lemma*][BellareNeven2006], Lemma 1.
* [A. Fiat, A. Shamir, *How to Prove Yourself: Practical Solutions to Identification and Signature
  Problems*][FiatShamir1986].
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.SigmaProtocol

open Probability OracleComp ROMSignature

variable {X Y T C Z M Query : Type}
variable (hashPoint : (M × T) ↪ Query)

/-- The Fiat–Shamir signature scheme ([BonehShoup2023], Section 19.6.1): the public key is the
statement and the secret key the witness-statement pair. To sign `m`, commit to `t`, query the
oracle at `hashPoint (m, t)` for the challenge and respond; a signature `(t, z)` verifies when
`(t, H(hashPoint (m, t)), z)` is accepting. Arbitrary other `Query` points remain available to the
forger in the same random oracle. -/
noncomputable def fiatShamir (P : SigmaProtocol X Y T C Z) (keyGen : PMF (X × Y)) :
    Scheme Y (X × Y) M (T × Z) Query C where
  keyGen := keyGen.map fun key => (key.2, key)
  SignCoins := T × P.State
  signCoins sk _ := P.commit sk.1 sk.2
  sign sk m coins := (fun c => (coins.1, P.respond sk.1 sk.2 coins.2 c)) <$>
    OracleComp.query (spec := fun _ : Query => C) (hashPoint (m, coins.1))
  verify y m σ := (fun c => P.verify y σ.1 c σ.2) <$>
    OracleComp.query (spec := fun _ : Query => C) (hashPoint (m, σ.1))

variable [DecidableEq M] [DecidableEq Query] [Fintype C] [Nonempty C]

omit [DecidableEq M] in
/-- **Correctness** of Fiat–Shamir signatures: with a complete Sigma protocol and keys in the
relation, every honest signature verifies. -/
theorem fiatShamir_correct {P : SigmaProtocol X Y T C Z} {keyGen : PMF (X × Y)}
    {R : X → Y → Prop} (hP : P.Complete R) (hkey : ∀ key ∈ keyGen.support, R key.1 key.2) :
    (fiatShamir hashPoint P keyGen).Correct := by
  intro keys hkeys m coins hcoins cache signed hsigned verified hverified
  obtain ⟨key, hmem, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hkeys
  simp only [fiatShamir, interpret_map, interpret_query, StateT.run_map,
    PMF.monad_map_eq_map, PMF.mem_support_map_iff] at hsigned hverified
  obtain ⟨r, hr, rfl⟩ := hsigned
  obtain ⟨r', hr', rfl⟩ := hverified
  have hlookup := lookup_of_mem_support_oracle hr
  change r' ∈ (oracle C (hashPoint (m, coins.1)) r.2).support at hr'
  rw [oracle] at hr'
  rw [memoize_of_some _ _ _ _ hlookup, PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hr'
  subst hr'
  exact hP.accepts_of_mem_support_commit (hkey key hmem) hcoins r.1

/-! ### The reduction -/

namespace FiatShamir

/-- The final check on a forgery `(m, (t, z))` against the statement `y`: its point is
`hashPoint (m, t)`, and it wins when `(t, c, z)` is accepting and `m` was never signed. -/
def check (P : SigmaProtocol X Y T C Z) (y : Y) : ForkingReduction.Check M T C Z Query M where
  point m t := hashPoint (m, t)
  accepts _ t c z := P.verify y t c z
  fresh m _ signed := !signed.contains m

variable [Nonempty T] [Nonempty Z]

/-- Signing without the witness, from one simulated transcript `(t, c, z)` per call: a signing
call on `m` returns `(t, z)`, programs the oracle at `hashPoint (m, t)` with `c` and logs `m`. -/
noncomputable def signer :
    ForkingReduction.Signer M (T × Z) Query C M (T × C × Z) where
  fallback := Classical.arbitrary _
  step := fun (t, c, z) m => ((t, z), some (hashPoint (m, t), c, m))

/-- The forger, with simulated signing, as a program over the hash oracle with explicit coins: the
statement, the forger's coins and the simulated transcripts. It names the query of the forgery's
point when the forger wins. -/
noncomputable def forkingProgram (P : SigmaProtocol X Y T C Z)
    (A : Forger Y M (T × Z) Query C) (s : Y × A.Coins × List (T × C × Z)) :
    OracleComp (fun _ : Query => C) (Option ℕ × ForkingReduction.Outcome M T C Z) :=
  let (y, coins, transcripts) := s
  ForkingReduction.program (signer hashPoint) (check hashPoint P y) (A.forge y coins) transcripts

/-- The coins of the forking program for the statement `y`: the forger's coins and `Q` simulated
transcripts. -/
noncomputable def coins (simulate : Y → C → PMF (T × Z)) (A : Forger Y M (T × Z) Query C)
    (Q : ℕ) (y : Y) : PMF (Y × A.Coins × List (T × C × Z)) := do
  let s ← A.coins
  let transcripts ← (PMF.iid (simulateConversation simulate y) Q).map List.ofFn
  return (y, s, transcripts)

variable [DecidableEq C]

/-- **The one-way adversary** built from a forger making at most `Qs` signing and `Qro` hash
calls: draw one simulated transcript per call, fork the forking program with the `Qro + 1`
answers of its hash oracle, and extract a witness from the two forgeries. A failed fork returns
the supplied `fallback`; this value need not satisfy the witness relation. -/
noncomputable def reduction (P : SigmaProtocol X Y T C Z)
    (simulate : Y → C → PMF (T × Z)) (extract : Y → T → C → Z → C → Z → X)
    (fallback : X) (A : Forger Y M (T × Z) Query C) (Qs Qro : ℕ) (y : Y) : PMF X :=
  (Forking.fork (coins simulate A (Qs + Qro) y)
    (forkingAlgorithm (Classical.arbitrary C) (Qro + 1) (forkingProgram hashPoint P A))).map fun
      result =>
      match result with
      | none => fallback
      | some (_, ((_, outcome), _), ((_, outcome'), _)) =>
        extract y outcome.commitment outcome.challenge outcome.response outcome'.challenge
          outcome'.response

end FiatShamir

/-! ### Game hops -/

/-- The oracle table and the signed messages. -/
private abbrev GameState (M Query C : Type) := List (Query × C) × List M

/-- The EUF-CMA experiment for Fiat–Shamir signatures, with the final verification unfolded. -/
private theorem eufCmaGame_fiatShamir (P : SigmaProtocol X Y T C Z) (keyGen : PMF (X × Y))
    (A : Forger Y M (T × Z) Query C) :
    eufCmaGame (fiatShamir hashPoint P keyGen) A = keyGen.bind fun key => A.coins.bind fun s =>
      ((interpret (handler (fiatShamir hashPoint P keyGen) key) (A.forge key.2 s)).run ([],
        [])).bind
        (ForkingReduction.finishGame (FiatShamir.check hashPoint P key.2)) := by
  simp only [eufCmaGame, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  rw [show (fiatShamir hashPoint P keyGen).keyGen = keyGen.map fun key => (key.2, key) from rfl,
    PMF.bind_map]
  refine congrArg keyGen.bind (funext fun key => congrArg A.coins.bind (funext fun s => ?_))
  refine congrArg (PMF.bind _) (funext fun forged => ?_)
  simp only [fiatShamir, ForkingReduction.finishGame, FiatShamir.check, interpret_map,
    interpret_query, StateT.run_map, PMF.monad_map_eq_map, PMF.bind_map]
  rfl

/-- The real signer, with a flag raised when its commitment hits a point of the table. -/
private noncomputable def realHandler (P : SigmaProtocol X Y T C Z) (key : X × Y) :
    (q : M ⊕ Query) → StateT (GameState M Query C × Bool) PMF (ForgerSpec M Query (T × Z) C q)
  | .inl m => fun st => (P.commit key.1 key.2).bind fun ts =>
    (oracle C (hashPoint (m, ts.1)) st.1.1).map fun r => ((ts.1, P.respond key.1 key.2 ts.2 r.1),
      ((r.2, m :: st.1.2), st.2 || (st.1.1.lookup (hashPoint (m, ts.1))).isSome))
  | .inr x => fun st => (oracle C x st.1.1).map fun r => (r.1, ((r.2, st.1.2), st.2))

/-- The programming signer: it sets the oracle at `hashPoint (m, t)` to a fresh challenge,
with the same flag as the real signer. -/
private noncomputable def programHandler (P : SigmaProtocol X Y T C Z) (key : X × Y) :
    (q : M ⊕ Query) → StateT (GameState M Query C × Bool) PMF (ForgerSpec M Query (T × Z) C q) :=
  RandomOracle.flaggedOverwriteProgramHandler (Reply := fun _ : M => T × Z)
    (PMF.uniformOfFintype C) (fun _ : M => true) (fun _ h _ => Bool.noConfusion h)
    (fun _ => P.commit key.1 key.2) (fun m ts => hashPoint (m, ts.1))
    (fun m ts c signed => ((ts.1, P.respond key.1 key.2 ts.2 c), m :: signed))

omit [DecidableEq M] in
private theorem realHandler_eq_flaggedLazyProgramHandler (P : SigmaProtocol X Y T C Z)
    (key : X × Y) :
    realHandler hashPoint P key =
      RandomOracle.flaggedLazyProgramHandler (Reply := fun _ : M => T × Z)
        (PMF.uniformOfFintype C) (fun _ : M => true) (fun _ h _ => Bool.noConfusion h)
        (fun _ => P.commit key.1 key.2) (fun m ts => hashPoint (m, ts.1))
        (fun m ts c signed => ((ts.1, P.respond key.1 key.2 ts.2 c), m :: signed)) := by
  funext q ⟨⟨cache, signed⟩, b⟩
  cases q with
  | inl m =>
    rw [RandomOracle.flaggedLazyProgramHandler_apply_inl]
    rfl
  | inr x =>
    rw [RandomOracle.flaggedLazyProgramHandler_apply_inr]
    rfl

omit [DecidableEq M] in
private theorem handler_fiatShamir_eq_lazyProgramHandler (P : SigmaProtocol X Y T C Z)
    (keyGen : PMF (X × Y)) (key : X × Y) :
    handler (fiatShamir hashPoint P keyGen) key =
      RandomOracle.lazyProgramHandler (Reply := fun _ : M => T × Z)
        (PMF.uniformOfFintype C) (fun _ : M => true) (fun _ h _ => Bool.noConfusion h)
        (fun _ => P.commit key.1 key.2) (fun m ts => hashPoint (m, ts.1))
        (fun m ts c signed => ((ts.1, P.respond key.1 key.2 ts.2 c), m :: signed)) := by
  funext q ⟨cache, signed⟩
  cases q with
  | inl m =>
    simp only [pmf_norm, handler, fiatShamir, RandomOracle.lazyProgramHandler, ↓reduceDIte,
      interpret_map, interpret_query, StateT.run_map, oracle]
    rfl
  | inr x =>
    simp only [pmf_norm, handler, RandomOracle.lazyProgramHandler, oracle]
    exact (PMF.bind_pure_comp _ _).symm

omit [DecidableEq M] in
/-- The real and the programming signer agree until the flag is raised. -/
private theorem identicalUntilBad (P : SigmaProtocol X Y T C Z) (key : X × Y) :
    IdenticalUntilBad (realHandler hashPoint P key) (programHandler hashPoint P key)
      fun st => st.2 = true := by
  rw [realHandler_eq_flaggedLazyProgramHandler, programHandler]
  exact RandomOracle.identicalUntilBad_flaggedProgramHandlers _ _ _ _ _ _

omit [Fintype C] [Nonempty C] in
open scoped ENNReal in
omit [DecidableEq M] in
/-- With `δ`-unpredictable commitments, a commitment hits one of the points of a table, for a
fixed message, with probability at most `δ` times the table's length. -/
private theorem toOuterMeasure_lookup_le (P : SigmaProtocol X Y T C Z) (key : X × Y)
    {δ : ℝ≥0∞} (hcommit : ∀ t, (P.commit key.1 key.2).map Prod.fst t ≤ δ) (m : M)
    (cache : List (Query × C)) :
    (P.commit key.1 key.2).toOuterMeasure {ts | (cache.lookup (hashPoint (m, ts.1))).isSome} ≤
      cache.length * δ := by
  have hpoint (x : Query) :
      (P.commit key.1 key.2).toOuterMeasure {ts | hashPoint (m, ts.1) = x} ≤ δ := by
    by_cases hx : ∃ t, hashPoint (m, t) = x
    · obtain ⟨t, rfl⟩ := hx
      simp only [hashPoint.injective.eq_iff, Prod.mk.injEq, true_and]
      rw [show {ts : T × P.State | ts.1 = t} = Prod.fst ⁻¹' {t} from rfl,
        ← PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_singleton]
      exact hcommit t
    · have hempty : {ts : T × P.State | hashPoint (m, ts.1) = x} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        exact fun ts hts => hx ⟨ts.1, hts⟩
      simp [hempty]
  exact Probability.PMF.toOuterMeasure_lookup_isSome_le _ _ hpoint cache

open scoped ENNReal in
omit [DecidableEq M] in
/-- With `δ`-unpredictable commitments, the flag of a forger making at most `Qs` signing calls
and `Q` calls in all is raised with probability at most `Qs · Q · δ`: each signing call hits one of
the at most `Q` points of the table with probability at most `Q · δ`. -/
private theorem toOuterMeasure_flag_le (P : SigmaProtocol X Y T C Z) (key : X × Y)
    {δ : ℝ≥0∞} (hcommit : ∀ t, (P.commit key.1 key.2).map Prod.fst t ≤ δ) {α : Type}
    {program : OracleComp (ForgerSpec M Query (T × Z) C) α} {Qs Q : ℕ}
    (hQs : IsCostBounded signingCost program Qs) (hQ : IsQueryBounded program Q) :
    ((interpret (realHandler hashPoint P key) program).run (([], []), false)).toOuterMeasure
      {x | x.2.2 = true} ≤ Qs * (Q * δ) := by
  have h := toOuterMeasure_bad_le (handler := realHandler hashPoint P key) (bad := fun st => st.2
    = true)
    signingCost (fun st => st.1.1.length * δ) δ ?_ ?_ hQ hQs (s := (([], []), false)) (by simp)
  · simpa using h
  · intro q st hst
    cases q with
    | inl m =>
      rw [signingCost, Nat.cast_one, one_mul, realHandler]
      refine (Probability.PMF.toOuterMeasure_bind_le_add _ _
        {ts : T × P.State | (st.1.1.lookup (hashPoint (m, ts.1))).isSome} _ 0
        fun ts _ hts => le_of_eq ((PMF.toOuterMeasure_apply_eq_zero_iff _ _).mpr
          (Set.disjoint_left.mpr fun x hx hbad => ?_))).trans ?_
      · obtain ⟨r, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
        simp_all
      · rw [add_zero]
        exact toOuterMeasure_lookup_le hashPoint P key hcommit m st.1.1
    | inr x =>
      refine le_of_eq_of_le ((PMF.toOuterMeasure_apply_eq_zero_iff _ _).mpr ?_) zero_le
      refine Set.disjoint_left.mpr fun y hy hbad => hst ?_
      obtain ⟨r, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
      exact hbad
  · intro q st _ x hx _
    have hlen : x.2.1.1.length ≤ st.1.1.length + 1 := by
      cases q with
      | inl m =>
        obtain ⟨ts, -, hx⟩ := (PMF.mem_support_bind_iff _ _ _).mp hx
        obtain ⟨r, hr, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
        exact length_le_of_mem_support_oracle hr
      | inr x' =>
        obtain ⟨r, hr, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
        exact length_le_of_mem_support_oracle hr
    calc (x.2.1.1.length : ℝ≥0∞) * δ ≤ ((st.1.1.length + 1 : ℕ) : ℝ≥0∞) * δ := by
          gcongr
      _ = st.1.1.length * δ + δ := by
          rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]

omit [DecidableEq M] in
/-- Under special HVZK, the unflagged overwrite signer equals the game signer of
`FiatShamir.signer` on a simulated transcript. -/
private theorem overwriteProgramHandler_eq_gameHandler [Nonempty T] [Nonempty Z]
    {P : SigmaProtocol X Y T C Z} {R : X → Y → Prop} {simulate : Y → C → PMF (T × Z)}
    (hzk : P.SpecialHVZK R simulate) {key : X × Y} (hkey : R key.1 key.2) :
    RandomOracle.overwriteProgramHandler (Reply := fun _ : M => T × Z)
        (PMF.uniformOfFintype C) (fun _ : M => true) (fun _ h _ => Bool.noConfusion h)
        (fun _ => P.commit key.1 key.2) (fun m ts => hashPoint (m, ts.1))
        (fun m ts c signed => ((ts.1, P.respond key.1 key.2 ts.2 c), m :: signed)) =
      fun q st => (simulateConversation simulate key.2).bind fun v =>
        ForkingReduction.gameHandler (FiatShamir.signer hashPoint) v q st := by
  funext q ⟨cache, signed⟩
  cases q with
  | inl m =>
    simp only [pmf_norm, RandomOracle.overwriteProgramHandler, ↓reduceDIte,
      ForkingReduction.gameHandler, FiatShamir.signer, ForkingReduction.recordGame,
      simulateConversation, hzk.transcript_eq key.1 key.2 hkey, SigmaProtocol.transcript]
    rw [PMF.bind_comm]
  | inr x =>
    simp only [RandomOracle.overwriteProgramHandler, ForkingReduction.gameHandler, PMF.bind_const,
      oracle]

/-! ### The reduction simulates the game -/

namespace FiatShamir

omit [DecidableEq Query] [Fintype C] in
/-- A forgery at a point programmed by a signing call on `m` is a forgery on `m`, which is then
signed, so it does not win. -/
theorem rejectsProgrammed [Nonempty T] [Nonempty Z] (P : SigmaProtocol X Y T C Z) (y : Y) :
    ForkingReduction.RejectsProgrammed (signer (Z := Z) hashPoint) (check hashPoint P y) := by
  intro s q x c l hr m t log hpt hl
  simp only [signer, Option.some.injEq, Prod.mk.injEq] at hr
  obtain ⟨rfl, -, rfl⟩ := hr
  simp only [check, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq] at hpt ⊢
  obtain ⟨rfl, -⟩ := hpt
  simp [hl]

variable [Nonempty T] [Nonempty Z]

/-- **The game hops** for one key and one choice of the forger's coins: the experiment wins at
most as often as the forking program, with presampled transcripts, plus `Qs · (Qs + Qro) · δ`. -/
private theorem run_bind_finishGame_le {P : SigmaProtocol X Y T C Z} {keyGen : PMF (X × Y)}
    {R : X → Y → Prop} {simulate : Y → C → PMF (T × Z)} (hzk : P.SpecialHVZK R simulate)
    {key : X × Y} (hkey : R key.1 key.2) {δ : ENNReal}
    (hcommit : ∀ t, (P.commit key.1 key.2).map Prod.fst t ≤ δ)
    (A : Forger Y M (T × Z) Query C) {Qs Qro : ℕ} (hA : A.CallBounded Qs Qro)
    (c : A.Coins) :
    ((interpret (handler (fiatShamir hashPoint P keyGen) key) (A.forge key.2 c)).run ([], [])).bind
        (ForkingReduction.finishGame (check hashPoint P key.2)) true ≤
      ((PMF.iid (simulateConversation simulate key.2) (Qs + Qro)).map List.ofFn).bind (fun trs =>
        ((interpret countingUniform (forkingProgram hashPoint P A (key.2, c, trs))).run 0).map
          fun ((_, outcome), _) => outcome.won) true + (Qs * (Qs + Qro) : ℕ) * δ := by
  have h0 : ((interpret (realHandler hashPoint P key) (A.forge key.2 c)).run (([], []), false)).map
      (Prod.map id Prod.fst) =
      (interpret (handler (fiatShamir hashPoint P keyGen) key) (A.forge key.2 c)).run ([], []) := by
    rw [realHandler_eq_flaggedLazyProgramHandler, handler_fiatShamir_eq_lazyProgramHandler]
    exact RandomOracle.run_flaggedLazyProgramHandler_map_fst _ _ _ _ _ _ _ _ false
  have h1 : ((interpret (programHandler hashPoint P key) (A.forge key.2 c)).run
      (([], []), false)).map (Prod.map id Prod.fst) =
      (interpret (m := StateT (GameState M Query C) PMF)
        (fun q st => (simulateConversation simulate key.2).bind fun v =>
          ForkingReduction.gameHandler (signer hashPoint) v q st) (A.forge key.2 c)).run
        ([], []) := by
    rw [programHandler, ← overwriteProgramHandler_eq_gameHandler hashPoint hzk hkey]
    exact RandomOracle.run_flaggedOverwriteProgramHandler_map_fst _ _ _ _ _ _ _ _ false
  have h2 := (hA.isQueryBounded key.2 c).run_interpret_presample
    (simulateConversation simulate key.2) (signer hashPoint).fallback
      (ForkingReduction.gameHandler (signer hashPoint)) ([], [])
  have hflag := toOuterMeasure_flag_le hashPoint P key hcommit (hA key.2 c).1 (hA.isQueryBounded
    key.2 c)
  rw [show (Qs : ENNReal) * ((Qs + Qro : ℕ) * δ) = (Qs * (Qs + Qro) : ℕ) * δ by
    push_cast; ring] at hflag
  rw [← h0, PMF.bind_map]
  refine ((identicalUntilBad hashPoint P key).bind_apply_le _ _ _ _).trans
    (add_le_add (le_of_eq ?_) hflag)
  rw [← PMF.bind_map, h1, ← h2, PMF.bind_bind]
  refine congrArg (fun p : PMF Bool => p true) (congrArg (PMF.bind _) (funext fun trs => ?_))
  rw [PMF.bind_map, forkingProgram, ForkingReduction.map_run_program]
  rfl

variable [DecidableEq C]

/-- **Extraction from a successful fork.** Both runs of a successful fork name the same query,
for the same point, answered with two different challenges, and both forgeries are accepting;
special soundness turns them into a witness. -/
private theorem fork_le_oneWayGame {P : SigmaProtocol X Y T C Z}
    {keyGen : PMF (X × Y)} {R : X → Y → Prop} [∀ x y, Decidable (R x y)]
    {extract : Y → T → C → Z → C → Z → X} (hsound : P.SpecialSoundOn keyGen R extract)
    (simulate : Y → C → PMF (T × Z)) (fallback : X)
    (A : Forger Y M (T × Z) Query C) (Qs Qro : ℕ) :
    (Forking.fork (keyGen.bind fun key => coins simulate A (Qs + Qro) key.2)
        (forkingAlgorithm (Classical.arbitrary C) (Qro + 1) (forkingProgram hashPoint P A))).map
          Option.isSome true ≤
      oneWayGame keyGen R (reduction hashPoint P simulate extract fallback A Qs Qro) true := by
  have hfork : Forking.fork (keyGen.bind fun key => coins simulate A (Qs + Qro) key.2)
      (forkingAlgorithm (Classical.arbitrary C) (Qro + 1) (forkingProgram hashPoint P A)) =
      keyGen.bind fun key => Forking.fork (coins simulate A (Qs + Qro) key.2)
        (forkingAlgorithm (Classical.arbitrary C) (Qro + 1) (forkingProgram hashPoint P A)) := by
    simp only [Forking.fork, PMF.monad_bind_eq_bind, PMF.bind_bind]
  rw [hfork, PMF.map_bind]
  simp only [pmf_norm, oneWayGame, reduction]
  refine Probability.PMF.bind_apply_mono_on_support _ _ fun key hkey => ?_
  rw [← PMF.bind_pure_comp]
  refine Probability.PMF.bind_apply_mono_on_support _ _ fun result hresult => ?_
  rcases result with _ | ⟨j, ⟨⟨_, outcome⟩, _⟩, ⟨⟨_, outcome'⟩, _⟩⟩
  · simp
  · obtain ⟨s, hs, hpt, hne, hv, hv'⟩ := ForkingReduction.exists_of_mem_support_fork
      (first := coins simulate A (Qs + Qro) key.2) (signer hashPoint)
      (fun s => check hashPoint P s.1) (fun _ => rejectsProgrammed hashPoint P _)
      (fun s => A.forge s.1 s.2.1) (fun s => s.2.2) hresult
    simp only [coins, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff,
      PMF.mem_support_pure_iff] at hs
    obtain ⟨c, -, trs, -, rfl⟩ := hs
    have ht : outcome.commitment = outcome'.commitment :=
      congrArg Prod.snd (hashPoint.injective hpt)
    have hR := hsound key hkey outcome.commitment outcome.challenge outcome.response
      outcome'.challenge outcome'.response hne hv (by rw [ht]; exact hv')
    simp [hR]

end FiatShamir

open FiatShamir in
open scoped NNReal in
/-- **Security of Fiat–Shamir signatures** ([BonehShoup2023], Theorem 19.16 with Equation 19.21,
via [BellareNeven2006], Lemma 1). Let the Sigma protocol be special sound on the generated keys
with extractor `extract`, special HVZK with simulator `simulate`, and have `δ`-unpredictable
commitments, and let the key generator produce pairs in the relation. A forger making at most `Qs`
signing calls and `Qro` hash calls wins the random-oracle EUF-CMA experiment with probability at
most `Qs · (Qs + Qro) · δ + (Qro + 1) / N + √((Qro + 1) · ε')`, where `N` is the number of
challenges and `ε'` is the probability that the reduction outputs a witness for a generated
statement. The signer and final verifier use `hashPoint (m, t)`, while `Qro` counts all adversary
hash calls, including queries outside the embedding's image. The bound holds for every supplied
failure output `fallback`; no correctness assumption is made about that output. -/
theorem succProbability_eufCmaGame_le [Nonempty T] [Nonempty Z] [DecidableEq C]
    {P : SigmaProtocol X Y T C Z} {keyGen : PMF (X × Y)} {R : X → Y → Prop}
    [∀ x y, Decidable (R x y)] {extract : Y → T → C → Z → C → Z → X}
    {simulate : Y → C → PMF (T × Z)} {δ : ℝ≥0}
    (hkey : ∀ key ∈ keyGen.support, R key.1 key.2) (hsound : P.SpecialSoundOn keyGen R extract)
    (hzk : P.SpecialHVZK R simulate)
    (hcommit : ∀ key ∈ keyGen.support, ∀ t, (P.commit key.1 key.2).map Prod.fst t ≤ δ)
    (fallback : X) (A : Forger Y M (T × Z) Query C)
    {Qs Qro : ℕ} (hA : A.CallBounded Qs Qro) :
    (Game.succProbability (eufCmaGame (fiatShamir hashPoint P keyGen) A) : ℝ) ≤
      Qs * (Qs + Qro) * δ + (Qro + 1) / Fintype.card C +
        √((Qro + 1) * Game.succProbability
          (oneWayGame keyGen R (reduction hashPoint P simulate extract fallback A Qs Qro))) := by
  classical
  set first := keyGen.bind fun key => coins simulate A (Qs + Qro) key.2 with hfirst
  have hA' : eufCmaGame (fiatShamir hashPoint P keyGen) A true ≤
      first.bind (fun s => ((interpret countingUniform (forkingProgram hashPoint P A s)).run 0).map
        fun ((_, outcome), _) => outcome.won) true + (Qs * (Qs + Qro) : ℕ) * (δ : ENNReal) := by
    rw [(eufCmaGame_fiatShamir hashPoint), hfirst]
    simp only [coins, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind,
      PMF.pure_bind]
    refine Probability.PMF.bind_apply_le_add_const_on_support _ _ fun key hkey' =>
      Probability.PMF.bind_apply_le_add_const_on_support _ _ fun c _ => ?_
    exact (run_bind_finishGame_le hashPoint) hzk (hkey key hkey') (hcommit key hkey') A hA c
  have h := ForkingReduction.toReal_le_add_sqrt_fork_of_le first (signer hashPoint)
    (fun s => check hashPoint P s.1) (fun _ => rejectsProgrammed hashPoint P _)
    (fun s => A.forge s.1 s.2.1) (fun s => s.2.2) (fun s => (hA s.1 s.2.1).2)
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.coe_ne_top) hA'
    ((fork_le_oneWayGame (P := P) hashPoint) hsound simulate fallback A Qs Qro)
    (PMF.apply_ne_top _ _)
  simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal]
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.coe_toReal] at h
  push_cast at h ⊢
  linarith

end Cslib.Crypto.Protocols.SigmaProtocol
