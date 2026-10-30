/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Protocols.SigmaProtocol.Identification
public import Complexity.Crypto.Protocols.Signature.RandomOracle
public import Complexity.Languages.Probabilistic.Forking
import Complexity.Foundations.Data.List.Lookup
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF.Event
import Complexity.Languages.Probabilistic.Presample
import Complexity.Languages.Probabilistic.Simulation
import Complexity.Languages.Probabilistic.UntilBad
import Complexity.Languages.Probabilistic.RandomOracle
import Complexity.Probability.PMF

/-!
# Fiat–Shamir signatures

The Fiat–Shamir transform ([BonehShoup2023], Section 19.6.1) turns a Sigma protocol into a
signature scheme in the random-oracle model: to sign `m`, the prover commits to `t`, takes the
challenge `c := H(m, t)` and responds with `z`; the signature `(t, z)` verifies when
`(t, H(m, t), z)` is an accepting conversation.

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

1. The signer is replaced by one that programs the oracle at `(m, t)` with a fresh challenge.
   The two agree until the signer's commitment hits a point already in the oracle's table, which
   has probability at most `Qs · (Qs + Qro) · δ` (the difference lemma,
   `OracleComp.IdenticalUntilBad.bind_apply_le`, and `OracleComp.toOuterMeasure_bad_le`).
2. Special HVZK replaces the programming signer by the simulator, which needs no witness.
3. The simulated transcripts are drawn in advance, one per call
   (`OracleComp.IsQueryBounded.run_interpret_presample`).
4. The result is a program over the hash oracle alone, with explicit coins
   (`FiatShamir.forkingProgram`), that names the hash query of the forgery whenever the forger
   wins. The forking lemma (`OracleComp.le_add_sqrt_fork`) and special soundness turn it into
   the one-way adversary `FiatShamir.reduction`.

These are exact probability laws for one Sigma protocol, key generator and forger; there is no
efficiency claim. The forger has explicit coins, so the reduction can rerun it.

## Main definitions

* `Cslib.Crypto.Protocols.SigmaProtocol.fiatShamir`: the Fiat–Shamir signature scheme.
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

variable {X Y T C Z M : Type}

/-- The Fiat–Shamir signature scheme ([BonehShoup2023], Section 19.6.1): the public key is the
statement and the secret key the witness-statement pair. To sign `m`, commit to `t`, query the
oracle at `(m, t)` for the challenge and respond; a signature `(t, z)` verifies when
`(t, H(m, t), z)` is accepting. -/
noncomputable def fiatShamir (P : SigmaProtocol X Y T C Z) (keyGen : PMF (X × Y)) :
    Scheme Y (X × Y) M (T × Z) (M × T) C where
  keyGen := keyGen.map fun key => (key.2, key)
  SignCoins := T × P.State
  signCoins sk _ := P.commit sk.1 sk.2
  sign sk m coins := (fun c => (coins.1, P.respond sk.1 sk.2 coins.2 c)) <$>
    OracleComp.query (spec := fun _ : M × T => C) (m, coins.1)
  verify y m σ := (fun c => P.verify y σ.1 c σ.2) <$>
    OracleComp.query (spec := fun _ : M × T => C) (m, σ.1)

variable [DecidableEq M] [DecidableEq T] [Fintype C] [Nonempty C]

/-- A table entry produced by a call of the oracle is found at its point. -/
private theorem lookup_of_mem_support_oracle {x : M × T} {cache : List ((M × T) × C)}
    {result : C × List ((M × T) × C)} (h : result ∈ (oracle C x cache).support) :
    result.2.lookup x = some result.1 := by
  rcases (RandomOracle.mem_support_memoize_iff _ _ _ _).mp h with ⟨hlookup, hnext⟩ | ⟨_, _, hnext⟩
  · rw [hnext, hlookup]
  · rw [hnext, List.lookup_cons_self]

/-- **Correctness** of Fiat–Shamir signatures: with a complete Sigma protocol and keys in the
relation, every honest signature verifies. -/
theorem fiatShamir_correct {P : SigmaProtocol X Y T C Z} {keyGen : PMF (X × Y)}
    {R : X → Y → Prop} (hP : P.Complete R) (hkey : ∀ key ∈ keyGen.support, R key.1 key.2) :
    (fiatShamir (M := M) P keyGen).Correct := by
  intro keys hkeys m coins hcoins cache signed hsigned verified hverified
  obtain ⟨key, hmem, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hkeys
  simp only [fiatShamir, interpret_map, interpret_query, StateT.run_map,
    PMF.monad_map_eq_map, PMF.mem_support_map_iff] at hsigned hverified
  obtain ⟨r, hr, rfl⟩ := hsigned
  obtain ⟨r', hr', rfl⟩ := hverified
  have hlookup := lookup_of_mem_support_oracle hr
  change r' ∈ (oracle C (m, coins.1) r.2).support at hr'
  rw [oracle] at hr'
  rw [memoize_of_some _ _ _ _ hlookup, PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hr'
  subst hr'
  exact hP.accepts_of_mem_support_commit (hkey key hmem) hcoins r.1

/-! ### The reduction -/

namespace FiatShamir

/-- The state of the reduction while it runs the forger: the oracle table, each point with its
challenge and, when the reduction asked its own oracle for the point, the position of that query;
the messages signed so far; the number of queries asked so far; and the simulated transcripts not
used yet. -/
structure ReductionState (M T C Z : Type) where
  /-- The oracle table. -/
  table : List ((M × T) × C × Option ℕ)
  /-- The messages signed so far. -/
  signed : List M
  /-- The number of queries asked so far. -/
  count : ℕ
  /-- The simulated transcripts not used yet. -/
  transcripts : List (T × C × Z)

variable [Nonempty T] [Nonempty Z]

/-- Answer the forger's calls without the witness, consuming one simulated transcript `(t, c, z)`
per call. A signing call on `m` returns `(t, z)` and programs the table at `(m, t)` with `c`. A
hash call returns the table's challenge, or asks the reduction's own oracle and records the
answer with the position of the query. -/
noncomputable def reductionHandler :
    (q : M ⊕ (M × T)) → StateT (ReductionState M T C Z) (OracleComp (fun _ : M × T => C))
      (ForgerSpec M (M × T) (T × Z) C q)
  | .inl m => fun st =>
    let v := st.transcripts.headD (Classical.arbitrary _)
    pure ((v.1, v.2.2),
      ⟨((m, v.1), v.2.1, none) :: st.table, m :: st.signed, st.count, st.transcripts.tail⟩)
  | .inr x => fun st =>
    match st.table.lookup x with
    | some entry => pure (entry.1, ⟨st.table, st.signed, st.count, st.transcripts.tail⟩)
    | none => (fun c => (c, ⟨(x, c, some st.count) :: st.table, st.signed, st.count + 1,
        st.transcripts.tail⟩)) <$> OracleComp.query x

/-- The verdict on a forgery `(m, (t, z))` whose point `(m, t)` has challenge `c`: the forgery wins
when `(t, c, z)` is accepting and `m` was never signed, and then the reduction names `position`,
the position of the query for `(m, t)`. The verdict records the point, the challenge and the
response. -/
def verdict (P : SigmaProtocol X Y T C Z) (y : Y) (forged : (M × (T × Z)) × ReductionState M T C Z)
    (c : C) (position : Option ℕ) : Option ℕ × Bool × (M × T) × C × Z :=
  (if P.verify y forged.1.2.1 c forged.1.2.2 && !forged.2.signed.contains forged.1.1 then position
    else none, P.verify y forged.1.2.1 c forged.1.2.2 && !forged.2.signed.contains forged.1.1,
    (forged.1.1, forged.1.2.1), c, forged.1.2.2)

/-- Check a forgery, querying its point when the table lacks it. -/
noncomputable def finish (P : SigmaProtocol X Y T C Z) (y : Y)
    (forged : (M × (T × Z)) × ReductionState M T C Z) :
    OracleComp (fun _ : M × T => C) (Option ℕ × Bool × (M × T) × C × Z) :=
  match forged.2.table.lookup (forged.1.1, forged.1.2.1) with
  | some entry => pure (verdict P y forged entry.1 entry.2)
  | none => (fun c => verdict P y forged c (some forged.2.count)) <$>
      OracleComp.query (forged.1.1, forged.1.2.1)

/-- The forger, with simulated signing, as a program over the hash oracle with explicit coins: the
statement, the forger's coins and the simulated transcripts. It names the query of the forgery's
point when the forger wins. -/
noncomputable def forkingProgram (P : SigmaProtocol X Y T C Z)
    (A : Forger Y M (T × Z) (M × T) C) (s : Y × A.Coins × List (T × C × Z)) :
    OracleComp (fun _ : M × T => C) (Option ℕ × Bool × (M × T) × C × Z) :=
  (interpret reductionHandler (A.forge s.1 s.2.1)).run ⟨[], [], 0, s.2.2⟩ >>= finish P s.1

/-- The coins of the forking program for the statement `y`: the forger's coins and `Q` simulated
transcripts. -/
noncomputable def coins (simulate : Y → C → PMF (T × Z)) (A : Forger Y M (T × Z) (M × T) C)
    (Q : ℕ) (y : Y) : PMF (Y × A.Coins × List (T × C × Z)) := do
  let s ← A.coins
  let transcripts ← (PMF.iid (simulateConversation simulate y) Q).map List.ofFn
  return (y, s, transcripts)

variable [DecidableEq C]

/-- **The one-way adversary** built from a forger making at most `Qs` signing and `Qro` hash
calls: draw one simulated transcript per call, fork the forking program with the `Qro + 1`
answers of its hash oracle, and extract a witness from the two forgeries. -/
noncomputable def reduction [Nonempty X] (P : SigmaProtocol X Y T C Z)
    (simulate : Y → C → PMF (T × Z)) (extract : Y → T → C → Z → C → Z → X)
    (A : Forger Y M (T × Z) (M × T) C) (Qs Qro : ℕ) (y : Y) : PMF X :=
  (Forking.fork (coins simulate A (Qs + Qro) y)
    (forkingAlgorithm (Classical.arbitrary C) (Qro + 1) (forkingProgram P A))).map fun result =>
      match result with
      | none => Classical.arbitrary X
      | some (_, out, out') =>
        extract y out.1.2.2.1.2 out.1.2.2.2.1 out.1.2.2.2.2 out'.1.2.2.2.1 out'.1.2.2.2.2

end FiatShamir

/-! ### Game hops -/

/-- The oracle table and the signed messages. -/
private abbrev GameState (M T C : Type) := List ((M × T) × C) × List M

/-- The experiment's final step: check the forgery against the oracle. -/
private noncomputable def finishGame (P : SigmaProtocol X Y T C Z) (y : Y)
    (forged : (M × (T × Z)) × GameState M T C) : PMF Bool :=
  (oracle C (forged.1.1, forged.1.2.1) forged.2.1).map fun r =>
    P.verify y forged.1.2.1 r.1 forged.1.2.2 && !forged.2.2.contains forged.1.1

/-- The EUF-CMA experiment for Fiat–Shamir signatures, with the final verification unfolded. -/
private theorem eufCmaGame_fiatShamir (P : SigmaProtocol X Y T C Z) (keyGen : PMF (X × Y))
    (A : Forger Y M (T × Z) (M × T) C) :
    eufCmaGame (fiatShamir P keyGen) A = keyGen.bind fun key => A.coins.bind fun s =>
      ((interpret (handler (fiatShamir P keyGen) key) (A.forge key.2 s)).run ([], [])).bind
        (finishGame P key.2) := by
  simp only [eufCmaGame, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  rw [show (fiatShamir (M := M) P keyGen).keyGen = keyGen.map fun key => (key.2, key) from rfl,
    PMF.bind_map]
  refine congrArg keyGen.bind (funext fun key => congrArg A.coins.bind (funext fun s => ?_))
  refine congrArg (PMF.bind _) (funext fun forged => ?_)
  simp only [fiatShamir, finishGame, interpret_map, interpret_query, StateT.run_map,
    PMF.monad_map_eq_map, PMF.bind_map]
  rfl

/-- The real signer, with a flag raised when its commitment hits a point of the table. -/
private noncomputable def realHandler (P : SigmaProtocol X Y T C Z) (key : X × Y) :
    (q : M ⊕ (M × T)) → StateT (GameState M T C × Bool) PMF (ForgerSpec M (M × T) (T × Z) C q)
  | .inl m => fun st => (P.commit key.1 key.2).bind fun ts =>
    (oracle C (m, ts.1) st.1.1).map fun r => ((ts.1, P.respond key.1 key.2 ts.2 r.1),
      ((r.2, m :: st.1.2), st.2 || (st.1.1.lookup (m, ts.1)).isSome))
  | .inr x => fun st => (oracle C x st.1.1).map fun r => (r.1, ((r.2, st.1.2), st.2))

/-- The programming signer: it sets the oracle at `(m, t)` to a fresh challenge, with the same
flag as the real signer. -/
private noncomputable def programHandler (P : SigmaProtocol X Y T C Z) (key : X × Y) :
    (q : M ⊕ (M × T)) → StateT (GameState M T C × Bool) PMF (ForgerSpec M (M × T) (T × Z) C q)
  | .inl m => fun st => (P.commit key.1 key.2).bind fun ts =>
    (PMF.uniformOfFintype C).map fun c => ((ts.1, P.respond key.1 key.2 ts.2 c),
      ((((m, ts.1), c) :: st.1.1, m :: st.1.2), st.2 || (st.1.1.lookup (m, ts.1)).isSome))
  | .inr x => fun st => (oracle C x st.1.1).map fun r => (r.1, ((r.2, st.1.2), st.2))

/-- The signer from a simulated transcript `(t, c, z)`: it returns `(t, z)` and sets the oracle at
`(m, t)` to `c`. -/
private noncomputable def simulatedHandler (v : T × C × Z) :
    (q : M ⊕ (M × T)) → StateT (GameState M T C) PMF (ForgerSpec M (M × T) (T × Z) C q)
  | .inl m => fun st => PMF.pure ((v.1, v.2.2), ((((m, v.1), v.2.1) :: st.1), m :: st.2))
  | .inr x => fun st => (oracle C x st.1).map fun r => (r.1, (r.2, st.2))

/-- Forgetting the flag, the flagged real signer is the real signer. -/
private theorem realHandler_map (P : SigmaProtocol X Y T C Z) (keyGen : PMF (X × Y))
    (key : X × Y) (q : M ⊕ (M × T)) (st : GameState M T C × Bool) :
    (realHandler P key q st).map (fun x => (x.1, x.2.1)) =
      handler (fiatShamir P keyGen) key q st.1 := by
  cases q with
  | inl m =>
    simp only [realHandler, handler, fiatShamir, interpret_map, interpret_query, StateT.run_map,
      PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.monad_map_eq_map, PMF.map_bind,
      PMF.map_comp, PMF.bind_map, Function.comp_def]
    exact congrArg (PMF.bind _) (funext fun ts => (PMF.bind_pure_comp _ _).symm)
  | inr x =>
    simp only [realHandler, handler, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      PMF.map_comp, Function.comp_def]
    rfl

/-- An oracle call adds at most one entry to the table. -/
private theorem length_le_of_mem_support_oracle {x : M × T} {cache : List ((M × T) × C)}
    {result : C × List ((M × T) × C)} (h : result ∈ (oracle C x cache).support) :
    result.2.length ≤ cache.length + 1 := by
  rcases (RandomOracle.mem_support_memoize_iff _ _ _ _).mp h with ⟨_, hnext⟩ | ⟨_, _, hnext⟩
  · rw [hnext]
    exact Nat.le_succ _
  · rw [hnext, List.length_cons]

/-- The real and the programming signer agree until the flag is raised. -/
private theorem identicalUntilBad (P : SigmaProtocol X Y T C Z) (key : X × Y) :
    IdenticalUntilBad (realHandler (M := M) P key) (programHandler P key)
      fun st => st.2 = true where
  agree q st _ a st' hst' := by
    cases q with
    | inr x => rfl
    | inl m =>
      simp only [realHandler, programHandler, PMF.bind_apply]
      refine tsum_congr fun ts => congrArg (_ * ·) ?_
      cases hlookup : st.1.1.lookup (m, ts.1) with
      | some c =>
        refine ((PMF.apply_eq_zero_iff _ _).mpr fun hx => ?_).trans
          ((PMF.apply_eq_zero_iff _ _).mpr fun hx => ?_).symm <;>
        · obtain ⟨r, -, hr⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
          exact hst' (by rw [← (Prod.mk.inj hr).2]; simp)
      | none =>
        rw [oracle, memoize_of_none _ _ _ hlookup]
        simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.map_bind, PMF.pure_map]
        exact DFunLike.congr_fun (PMF.bind_pure_comp _ _) _
  absorb_first q st hst x hx := by
    cases q with
    | inl m =>
      obtain ⟨ts, -, hx⟩ := (PMF.mem_support_bind_iff _ _ _).mp hx
      obtain ⟨r, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
      simp [hst]
    | inr x' =>
      obtain ⟨r, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
      exact hst
  absorb_second q st hst x hx := by
    cases q with
    | inl m =>
      obtain ⟨ts, -, hx⟩ := (PMF.mem_support_bind_iff _ _ _).mp hx
      obtain ⟨c, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
      simp [hst]
    | inr x' =>
      obtain ⟨r, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
      exact hst

omit [Fintype C] [Nonempty C] in
open scoped ENNReal in
/-- With `δ`-unpredictable commitments, a commitment hits one of the points of a table, for a
fixed message, with probability at most `δ` times the table's length. -/
private theorem toOuterMeasure_lookup_le (P : SigmaProtocol X Y T C Z) (key : X × Y)
    {δ : ℝ≥0∞} (hcommit : ∀ t, (P.commit key.1 key.2).map Prod.fst t ≤ δ) (m : M)
    (cache : List ((M × T) × C)) :
    (P.commit key.1 key.2).toOuterMeasure {ts | (cache.lookup (m, ts.1)).isSome} ≤
      cache.length * δ := by
  induction cache with
  | nil => simp
  | cons e rest ih =>
    obtain ⟨⟨m', t'⟩, c⟩ := e
    calc (P.commit key.1 key.2).toOuterMeasure
          {ts | ((((m', t'), c) :: rest).lookup (m, ts.1)).isSome}
        ≤ (P.commit key.1 key.2).toOuterMeasure
          ({ts | ts.1 = t'} ∪ {ts | (rest.lookup (m, ts.1)).isSome}) := by
          refine (P.commit key.1 key.2).toOuterMeasure.mono fun ts hts => ?_
          have hts : ((((m', t'), c) :: rest).lookup (m, ts.1)).isSome = true := hts
          rw [List.lookup_cons] at hts
          by_cases h : (m, ts.1) = (m', t')
          · exact Or.inl (Prod.ext_iff.mp h).2
          · rw [beq_false_of_ne h] at hts
            exact Or.inr hts
      _ ≤ (P.commit key.1 key.2).toOuterMeasure {ts | ts.1 = t'} +
          (P.commit key.1 key.2).toOuterMeasure {ts | (rest.lookup (m, ts.1)).isSome} :=
          MeasureTheory.measure_union_le _ _
      _ ≤ δ + rest.length * δ := by
          refine add_le_add ?_ ih
          rw [show {ts : T × P.State | ts.1 = t'} = Prod.fst ⁻¹' {t'} from rfl,
            ← PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_singleton]
          exact hcommit t'
      _ = (((m', t'), c) :: rest).length * δ := by
          rw [List.length_cons, Nat.cast_add, Nat.cast_one]
          ring

open scoped ENNReal in
/-- With `δ`-unpredictable commitments, the flag of a forger making at most `Qs` signing calls
and `Q` calls in all is raised with probability at most `Qs · Q · δ`: each signing call hits one of
the at most `Q` points of the table with probability at most `Q · δ`. -/
private theorem toOuterMeasure_flag_le (P : SigmaProtocol X Y T C Z) (key : X × Y)
    {δ : ℝ≥0∞} (hcommit : ∀ t, (P.commit key.1 key.2).map Prod.fst t ≤ δ) {α : Type}
    {program : OracleComp (ForgerSpec M (M × T) (T × Z) C) α} {Qs Q : ℕ}
    (hQs : IsCostBounded signingCost program Qs) (hQ : IsQueryBounded program Q) :
    ((interpret (realHandler P key) program).run (([], []), false)).toOuterMeasure
      {x | x.2.2 = true} ≤ Qs * (Q * δ) := by
  have h := toOuterMeasure_bad_le (handler := realHandler P key) (bad := fun st => st.2 = true)
    signingCost (fun st => st.1.1.length * δ) δ ?_ ?_ hQ hQs (s := (([], []), false)) (by simp)
  · simpa using h
  · intro q st hst
    cases q with
    | inl m =>
      rw [signingCost, Nat.cast_one, one_mul, realHandler, PMF.toOuterMeasure_bind_apply]
      calc ∑' ts, (P.commit key.1 key.2) ts *
            ((oracle C (m, ts.1) st.1.1).map fun r => ((ts.1, P.respond key.1 key.2 ts.2 r.1),
              ((r.2, m :: st.1.2), st.2 || (st.1.1.lookup (m, ts.1)).isSome))).toOuterMeasure
              {x | x.2.2 = true}
          ≤ ∑' ts, (P.commit key.1 key.2) ts *
              {ts : T × P.State | (st.1.1.lookup (m, ts.1)).isSome}.indicator 1 ts := by
            refine tsum_le_tsum fun ts => mul_le_mul_of_nonneg_left ?_ zero_le
            by_cases hts : (st.1.1.lookup (m, ts.1)).isSome
            · rw [Set.indicator_of_mem (show ts ∈ {ts : T × P.State |
                (st.1.1.lookup (m, ts.1)).isSome} from hts), Pi.one_apply]
              exact Probability.PMF.toOuterMeasure_le_one _ _
            · rw [Set.indicator_of_notMem (show ts ∉ {ts : T × P.State |
                (st.1.1.lookup (m, ts.1)).isSome} from hts)]
              refine le_of_eq ((PMF.toOuterMeasure_apply_eq_zero_iff _ _).mpr ?_)
              refine Set.disjoint_left.mpr fun x hx hbad => ?_
              obtain ⟨r, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
              simp_all
        _ = (P.commit key.1 key.2).toOuterMeasure
              {ts | (st.1.1.lookup (m, ts.1)).isSome} := by
            rw [PMF.toOuterMeasure_apply]
            refine tsum_congr fun ts => ?_
            by_cases hts : (st.1.1.lookup (m, ts.1)).isSome
            · rw [Set.indicator_of_mem (show ts ∈ {ts : T × P.State |
                (st.1.1.lookup (m, ts.1)).isSome} from hts),
                Set.indicator_of_mem (show ts ∈ {ts : T × P.State |
                (st.1.1.lookup (m, ts.1)).isSome} from hts), Pi.one_apply, mul_one]
            · rw [Set.indicator_of_notMem (show ts ∉ {ts : T × P.State |
                (st.1.1.lookup (m, ts.1)).isSome} from hts),
                Set.indicator_of_notMem (show ts ∉ {ts : T × P.State |
                (st.1.1.lookup (m, ts.1)).isSome} from hts), mul_zero]
        _ ≤ st.1.1.length * δ := toOuterMeasure_lookup_le P key hcommit m st.1.1
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

/-- Forgetting the flag, the programming signer is the simulator's signer, by special HVZK. -/
private theorem programHandler_map {P : SigmaProtocol X Y T C Z} {R : X → Y → Prop}
    {simulate : Y → C → PMF (T × Z)} (hzk : P.SpecialHVZK R simulate) {key : X × Y}
    (hkey : R key.1 key.2) (q : M ⊕ (M × T)) (st : GameState M T C × Bool) :
    (programHandler P key q st).map (fun x => (x.1, x.2.1)) =
      (simulateConversation simulate key.2).bind fun v => simulatedHandler v q st.1 := by
  cases q with
  | inl m =>
    simp only [programHandler, simulatedHandler, simulateConversation, PMF.monad_bind_eq_bind,
      PMF.monad_pure_eq_pure, PMF.map_bind, PMF.map_comp, PMF.bind_bind, PMF.pure_bind,
      hzk.transcript_eq key.1 key.2 hkey, SigmaProtocol.transcript, PMF.bind_map,
      Function.comp_def]
    rw [PMF.bind_comm]
    rfl
  | inr x =>
    simp only [programHandler, simulatedHandler, PMF.bind_const, PMF.map_comp]
    rfl

/-! ### The reduction simulates the game -/

namespace FiatShamir

/-- The game's view of the reduction's state: the table without positions, the signed messages,
and the unused transcripts. -/
private def represent (st : ReductionState M T C Z) : GameState M T C × List (T × C × Z) :=
  ((st.table.map fun e => (e.1, e.2.1), st.signed), st.transcripts)

omit [Fintype C] [Nonempty C] in
/-- Forgetting positions commutes with looking up a point. -/
private theorem lookup_map_table (table : List ((M × T) × C × Option ℕ)) (x : M × T) :
    (table.map fun e => (e.1, e.2.1)).lookup x = (table.lookup x).map Prod.fst := by
  induction table with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨k, b⟩ := e
    cases hxk : x == k <;> simp [List.lookup_cons, hxk, ih]

variable [Nonempty T] [Nonempty Z]

omit [Fintype C] in
/-- A signing call of the reduction's handler. -/
private theorem run_reductionHandler_inl (m : M) (st : ReductionState M T C Z) :
    (reductionHandler (.inl m)).run st =
      pure (((st.transcripts.headD (Classical.arbitrary _)).1,
          (st.transcripts.headD (Classical.arbitrary _)).2.2),
        ⟨((m, (st.transcripts.headD (Classical.arbitrary _)).1),
          (st.transcripts.headD (Classical.arbitrary _)).2.1, none) :: st.table, m :: st.signed,
          st.count, st.transcripts.tail⟩) := rfl

omit [Fintype C] in
/-- A hash call of the reduction's handler on a point of the table. -/
private theorem run_reductionHandler_inr_some {x : M × T} {st : ReductionState M T C Z}
    {e : C × Option ℕ} (h : st.table.lookup x = some e) :
    (reductionHandler (.inr x)).run st =
      pure (e.1, ⟨st.table, st.signed, st.count, st.transcripts.tail⟩) := by
  simp only [reductionHandler, StateT.run, h]

omit [Fintype C] in
/-- A hash call of the reduction's handler on a new point. -/
private theorem run_reductionHandler_inr_none {x : M × T} {st : ReductionState M T C Z}
    (h : st.table.lookup x = none) :
    (reductionHandler (.inr x)).run st =
      (fun c => (c, ⟨(x, c, some st.count) :: st.table, st.signed, st.count + 1,
        st.transcripts.tail⟩)) <$> OracleComp.query x := by
  simp only [reductionHandler, StateT.run, h]

omit [DecidableEq M] [DecidableEq T] [Nonempty T] in
/-- A returned value, with the oracle answered uniformly and counted, makes no call. -/
private theorem run_interpret_countingUniform_pure {β : Type} (b : β) (n : ℕ) :
    (interpret countingUniform (pure b : OracleComp (fun _ : M × T => C) β)).run n =
      PMF.pure (b, n) := rfl

omit [DecidableEq M] [DecidableEq T] [Nonempty T] in
/-- A counted uniform answer. -/
private theorem run_countingUniform (x : M × T) (n : ℕ) :
    (countingUniform (H := C) x).run n = (PMF.uniformOfFintype C).map (·, n + 1) := rfl

/-- One call of the reduction's handler, with its oracle answered uniformly and counted, is a call
of the simulator's signer in the game's view. -/
private theorem combined_step (q : M ⊕ (M × T)) (s : ReductionState M T C Z × ℕ) :
    ((fun result => (result.1.1, result.1.2, result.2)) <$>
      (interpret countingUniform ((reductionHandler q).run s.1)).run s.2).map
        (fun x => (x.1, represent x.2.1)) =
      withSampleList (Classical.arbitrary _) simulatedHandler q (represent s.1) := by
  cases q with
  | inl m =>
    rw [run_reductionHandler_inl, run_interpret_countingUniform_pure]
    simp only [PMF.monad_map_eq_map, PMF.pure_map, withSampleList, simulatedHandler, represent]
    rfl
  | inr x =>
    cases h : s.1.table.lookup x with
    | some e =>
      have hcache : (represent s.1).1.1.lookup x = some e.1 := by
        rw [represent, lookup_map_table, h]
        rfl
      rw [run_reductionHandler_inr_some h]
      simp only [run_interpret_countingUniform_pure, PMF.monad_map_eq_map, PMF.pure_map,
        withSampleList, simulatedHandler]
      rw [oracle, memoize_of_some _ _ _ _ hcache]
      simp only [PMF.monad_pure_eq_pure, PMF.pure_map]
      rfl
    | none =>
      have hcache : (represent s.1).1.1.lookup x = none := by
        rw [represent, lookup_map_table, h]
        rfl
      rw [run_reductionHandler_inr_none h]
      simp only [interpret_map, interpret_query, StateT.run_map, PMF.monad_map_eq_map,
        withSampleList, simulatedHandler]
      rw [oracle, memoize_of_none _ _ _ hcache]
      simp only [run_countingUniform, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
        ← PMF.bind_pure_comp, PMF.bind_bind, PMF.pure_bind, Function.comp_apply]
      rfl

omit [Nonempty T] [Nonempty Z] in
/-- The reduction's final check, with its oracle answered uniformly, wins exactly when the game's
final check does. -/
private theorem map_run_finish (P : SigmaProtocol X Y T C Z) (y : Y) (a : M × (T × Z))
    (st : ReductionState M T C Z) (n : ℕ) :
    ((interpret countingUniform (finish P y (a, st))).run n).map (fun run => run.1.2.1) =
      finishGame P y (a, (represent st).1) := by
  cases h : st.table.lookup (a.1, a.2.1) with
  | some e =>
    have hcache : (represent st).1.1.lookup (a.1, a.2.1) = some e.1 := by
      rw [represent, lookup_map_table, h]
      rfl
    simp only [finish, h, run_interpret_countingUniform_pure, PMF.pure_map, finishGame]
    rw [oracle, memoize_of_some _ _ _ _ hcache]
    simp only [PMF.monad_pure_eq_pure, PMF.pure_map]
    rfl
  | none =>
    have hcache : (represent st).1.1.lookup (a.1, a.2.1) = none := by
      rw [represent, lookup_map_table, h]
      rfl
    simp only [finish, h, interpret_map, interpret_query, StateT.run_map, PMF.monad_map_eq_map,
      finishGame]
    rw [oracle, memoize_of_none _ _ _ hcache]
    simp only [run_countingUniform, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      ← PMF.bind_pure_comp, PMF.bind_bind, PMF.pure_bind, Function.comp_apply]
    rfl

/-- **The reduction simulates the game.** With its oracle answered uniformly, the forking program
wins exactly when the forger wins against the simulator's signer with the same transcripts. -/
private theorem map_run_forkingProgram (P : SigmaProtocol X Y T C Z)
    (A : Forger Y M (T × Z) (M × T) C) (s : Y × A.Coins × List (T × C × Z)) :
    ((interpret countingUniform (forkingProgram P A s)).run 0).map (fun run => run.1.2.1) =
      ((interpret (withSampleList (Classical.arbitrary _) simulatedHandler)
        (A.forge s.1 s.2.1)).run (([], []), s.2.2)).bind fun x =>
          finishGame P s.1 (x.1, x.2.1) := by
  have hsim := run_interpret_map_state _
    (withSampleList (Classical.arbitrary _) simulatedHandler) (fun s => represent s.1)
    combined_step (A.forge s.1 s.2.1) (⟨[], [], 0, s.2.2⟩, 0)
  rw [show represent (⟨[], [], 0, s.2.2⟩ : ReductionState M T C Z) = (([], []), s.2.2) from rfl]
    at hsim
  rw [forkingProgram, interpret_bind, StateT.run_bind, run_interpret_run_interpret, ← hsim]
  simp only [PMF.monad_bind_eq_bind, PMF.monad_map_eq_map, PMF.map_bind, PMF.bind_map,
    Function.comp_def]
  exact congrArg (PMF.bind _) (funext fun r => map_run_finish P s.1 r.1 r.2.1 r.2.2)

/-! ### The reduction's runs on fixed answers -/

omit [Fintype C] [Nonempty C] [Nonempty T] [Nonempty Z] in
/-- The final check on a forgery whose point is in the table. -/
private theorem finish_of_some {P : SigmaProtocol X Y T C Z} {y : Y}
    {forged : (M × (T × Z)) × ReductionState M T C Z} {e : C × Option ℕ}
    (h : forged.2.table.lookup (forged.1.1, forged.1.2.1) = some e) :
    finish P y forged = pure (verdict P y forged e.1 e.2) := by
  simp only [finish, h]

omit [Fintype C] [Nonempty C] [Nonempty T] [Nonempty Z] in
/-- The final check on a forgery whose point is not in the table. -/
private theorem finish_of_none {P : SigmaProtocol X Y T C Z} {y : Y}
    {forged : (M × (T × Z)) × ReductionState M T C Z}
    (h : forged.2.table.lookup (forged.1.1, forged.1.2.1) = none) :
    finish P y forged = (fun c => verdict P y forged c (some forged.2.count)) <$>
      OracleComp.query (forged.1.1, forged.1.2.1) := by
  simp only [finish, h]

/-- The invariant of the reduction's run on a list of answers, given the queries asked so far: the
count is their number; an entry with a position records the query at that position and its
answer; an entry without one is for a signed message. -/
private def Consistent (answers : List C) (st : ReductionState M T C Z)
    (queries : List (M × T)) : Prop :=
  st.count = queries.length ∧
    (∀ x c i, (x, c, some i) ∈ st.table →
      queries[i]? = some x ∧ answers.getD i (Classical.arbitrary C) = c) ∧
    ∀ x c, (x, c, none) ∈ st.table → x.1 ∈ st.signed

omit [Fintype C] in
/-- Every call of the reduction's handler preserves the invariant. -/
private theorem consistent_step (answers : List C) (q : M ⊕ (M × T))
    (st : ReductionState M T C Z) (queries : List (M × T))
    (h : Consistent answers st queries) :
    Consistent answers (runWithAnswers (Classical.arbitrary C) ((reductionHandler q).run st)
        (answers.drop queries.length)).1.2
      (queries ++ (runWithAnswers (Classical.arbitrary C) ((reductionHandler q).run st)
        (answers.drop queries.length)).2) := by
  obtain ⟨hcount, hpos, hsigned⟩ := h
  cases q with
  | inl m =>
    rw [run_reductionHandler_inl, runWithAnswers_pure, List.append_nil]
    refine ⟨hcount, fun x c i hx => ?_, fun x c hx => ?_⟩
    · simp only [List.mem_cons, Prod.mk.injEq, reduceCtorEq, and_false, false_or] at hx
      exact hpos x c i hx
    · simp only [List.mem_cons, Prod.mk.injEq] at hx
      rcases hx with ⟨rfl, -, -⟩ | hx
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hsigned x c hx)
  | inr x =>
    cases hl : st.table.lookup x with
    | some e =>
      rw [run_reductionHandler_inr_some hl, runWithAnswers_pure, List.append_nil]
      exact ⟨hcount, hpos, hsigned⟩
    | none =>
      rw [run_reductionHandler_inr_none hl, runWithAnswers_map_query]
      refine ⟨by simp [hcount], fun x' c i hx => ?_, fun x' c hx => ?_⟩
      · simp only [List.mem_cons, Prod.mk.injEq, Option.some.injEq] at hx
        rcases hx with ⟨rfl, rfl, rfl⟩ | hx
        · rw [hcount, List.getElem?_concat_length, List.getD_eq_getElem?_getD,
            List.headD_eq_head?_getD, List.head?_drop]
          exact ⟨rfl, rfl⟩
        · obtain ⟨hq, hc⟩ := hpos x' c i hx
          have hi : i < queries.length := (List.getElem?_eq_some_iff.mp hq).1
          exact ⟨by rw [List.getElem?_append_left hi, hq], hc⟩
      · simp only [List.mem_cons, Prod.mk.injEq, reduceCtorEq, and_false, false_or] at hx
        exact hsigned x' c hx

omit [Fintype C] in
/-- **The reduction's run on fixed answers.** On any list of answers, a winning forgery names a
position, and a named position is that of the query for the forgery's point, answered there with
the forgery's challenge, and the forgery is accepting. -/
private theorem runWithAnswers_forkingProgram (P : SigmaProtocol X Y T C Z)
    (A : Forger Y M (T × Z) (M × T) C) (s : Y × A.Coins × List (T × C × Z)) (answers : List C)
    {out : (Option ℕ × Bool × (M × T) × C × Z) × List (M × T)}
    (hout : runWithAnswers (Classical.arbitrary C) (forkingProgram P A s) answers = out) :
    (out.1.2.1 = true → out.1.1.isSome) ∧
      ∀ j, out.1.1 = some j → out.2[j]? = some out.1.2.2.1 ∧
        answers.getD j (Classical.arbitrary C) = out.1.2.2.2.1 ∧
        P.verify s.1 out.1.2.2.1.2 out.1.2.2.2.1 out.1.2.2.2.2 = true := by
  have hinv := runWithAnswers_run_interpret_invariant (Classical.arbitrary C) reductionHandler
    answers (Consistent answers) (consistent_step answers) (A.forge s.1 s.2.1)
    ⟨[], [], 0, s.2.2⟩ [] ⟨rfl, by simp, by simp⟩
  simp only [List.length_nil, List.drop_zero, List.nil_append] at hinv
  rw [forkingProgram, runWithAnswers_bind] at hout
  subst hout
  generalize runWithAnswers (Classical.arbitrary C)
    ((interpret reductionHandler (A.forge s.1 s.2.1)).run ⟨[], [], 0, s.2.2⟩) answers = r at hinv ⊢
  obtain ⟨⟨forged, st⟩, queries⟩ := r
  obtain ⟨hcount, hpos, hsigned⟩ := hinv
  cases hl : st.table.lookup (forged.1, forged.2.1) with
  | some e =>
    rw [finish_of_some hl, runWithAnswers_pure, List.append_nil]
    obtain ⟨l₁, l₂, htable, -⟩ := List.lookup_eq_some_iff.mp hl
    have hmem : ((forged.1, forged.2.1), e.1, e.2) ∈ st.table := by
      rw [htable]
      exact List.mem_append_right _ List.mem_cons_self
    obtain ⟨c, position⟩ := e
    cases position with
    | none =>
      have hm := hsigned _ _ hmem
      simp [verdict, hm]
    | some i =>
      obtain ⟨hq, hc⟩ := hpos _ _ _ hmem
      refine ⟨fun hwin => ?_, fun j hj => ?_⟩
      · simp only [verdict] at hwin ⊢
        simpa using hwin
      · simp only [verdict] at hj ⊢
        split_ifs at hj with hwin
        · cases hj
          exact ⟨hq, hc, (Bool.and_eq_true _ _).mp hwin |>.1⟩
  | none =>
    rw [finish_of_none hl, runWithAnswers_map_query]
    refine ⟨fun hwin => ?_, fun j hj => ?_⟩
    · simp only [verdict] at hwin ⊢
      simpa using hwin
    · simp only [verdict] at hj ⊢
      split_ifs at hj with hwin
      · cases hj
        refine ⟨by rw [hcount, List.getElem?_concat_length], ?_,
          (Bool.and_eq_true _ _).mp hwin |>.1⟩
        rw [hcount, List.getD_eq_getElem?_getD, List.headD_eq_head?_getD, List.head?_drop]

omit [Fintype C] in
/-- The forking program asks at most one query per hash call of the forger, and one more to check
the forgery. -/
private theorem isQueryBounded_forkingProgram (P : SigmaProtocol X Y T C Z)
    (A : Forger Y M (T × Z) (M × T) C) {Qro : ℕ}
    (hQro : ∀ y s, IsCostBounded hashCost (A.forge y s) Qro)
    (s : Y × A.Coins × List (T × C × Z)) : IsQueryBounded (forkingProgram P A s) (Qro + 1) := by
  have hhandler (q : M ⊕ (M × T)) (st : ReductionState M T C Z) :
      IsQueryBounded ((reductionHandler q).run st) (hashCost q) := by
    cases q with
    | inl m =>
      rw [run_reductionHandler_inl]
      exact .pure _ _
    | inr x =>
      cases hl : st.table.lookup x with
      | some e =>
        rw [run_reductionHandler_inr_some hl]
        exact .pure _ _
      | none =>
        rw [run_reductionHandler_inr_none hl]
        exact .liftBind _ _ 0 fun _ => .pure _ 0
  refine ((hQro s.1 s.2.1).run_interpret hhandler ⟨[], [], 0, s.2.2⟩).bind fun forged => ?_
  cases hl : forged.2.table.lookup (forged.1.1, forged.1.2.1) with
  | some e =>
    rw [finish_of_some hl]
    exact .pure _ _
  | none =>
    rw [finish_of_none hl]
    exact .liftBind _ _ 0 fun _ => .pure _ 0

/-- With its oracle answered uniformly, the forking program wins at most as often as it validly
names a query. -/
private theorem map_run_le_accept (P : SigmaProtocol X Y T C Z)
    (A : Forger Y M (T × Z) (M × T) C) {Qro : ℕ}
    (hQro : ∀ y s, IsCostBounded hashCost (A.forge y s) Qro)
    (s : Y × A.Coins × List (T × C × Z)) :
    ((interpret countingUniform (forkingProgram P A s)).run 0).map (fun run => run.1.2.1) true ≤
      ((interpret countingUniform (forkingProgram P A s)).run 0).bind
        (fun run => PMF.pure (validIndex (Qro + 1) run.2 run.1.1).isSome) true := by
  have hbound := isQueryBounded_forkingProgram P A hQro s
  rw [run_interpret_countingUniform_eq (Classical.arbitrary C) _ hbound]
  simp only [← PMF.bind_pure_comp, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
  refine Probability.PMF.bind_apply_mono_on_support _ _ fun h _ => ?_
  obtain ⟨hwin, hnamed⟩ := runWithAnswers_forkingProgram P A s (List.ofFn h) rfl
  by_cases hw : (runWithAnswers (Classical.arbitrary C) (forkingProgram P A s)
      (List.ofFn h)).1.2.1 = true
  · obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp (hwin hw)
    have hlt : j < (runWithAnswers (Classical.arbitrary C) (forkingProgram P A s)
        (List.ofFn h)).2.length := (List.getElem?_eq_some_iff.mp (hnamed j hj).1).1
    have hle := hbound.length_runWithAnswers_le (Classical.arbitrary C) (List.ofFn h)
    have hvalid : (validIndex (Qro + 1) (0 + (runWithAnswers (Classical.arbitrary C)
        (forkingProgram P A s) (List.ofFn h)).2.length) (runWithAnswers (Classical.arbitrary C)
          (forkingProgram P A s) (List.ofFn h)).1.1).isSome = true := by
      rw [hj, zero_add]
      simp only [validIndex, Option.bind_some]
      split_ifs with hc
      · rfl
      · exact absurd ⟨by omega, hlt⟩ hc
    rw [hw, hvalid]
  · rw [Bool.eq_false_iff.mpr hw]
    simp

variable [DecidableEq C]

/-- **Extraction from a successful fork.** Both runs of a successful fork name the same query,
for the same point, answered with two different challenges, and both forgeries are accepting;
special soundness turns them into a witness. -/
private theorem fork_le_oneWayGame [Nonempty X] {P : SigmaProtocol X Y T C Z}
    {keyGen : PMF (X × Y)} {R : X → Y → Prop} [∀ x y, Decidable (R x y)]
    {extract : Y → T → C → Z → C → Z → X} (hsound : P.SpecialSoundOn keyGen R extract)
    (simulate : Y → C → PMF (T × Z)) (A : Forger Y M (T × Z) (M × T) C) (Qs Qro : ℕ) :
    (Forking.fork (keyGen.bind fun key => coins simulate A (Qs + Qro) key.2)
        (forkingAlgorithm (Classical.arbitrary C) (Qro + 1) (forkingProgram P A))).map
          Option.isSome true ≤
      oneWayGame keyGen R (reduction P simulate extract A Qs Qro) true := by
  have hfork : Forking.fork (keyGen.bind fun key => coins simulate A (Qs + Qro) key.2)
      (forkingAlgorithm (Classical.arbitrary C) (Qro + 1) (forkingProgram P A)) =
      keyGen.bind fun key => Forking.fork (coins simulate A (Qs + Qro) key.2)
        (forkingAlgorithm (Classical.arbitrary C) (Qro + 1) (forkingProgram P A)) := by
    simp only [Forking.fork, PMF.monad_bind_eq_bind, PMF.bind_bind]
  rw [hfork, PMF.map_bind]
  simp only [oneWayGame, reduction, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_map]
  refine Probability.PMF.bind_apply_mono_on_support _ _ fun key hkey => ?_
  rw [← PMF.bind_pure_comp]
  refine Probability.PMF.bind_apply_mono_on_support _ _ fun result hresult => ?_
  rcases result with _ | ⟨j, out, out'⟩
  · simp
  · obtain ⟨s, hs, h, h', -, hne, hout, hout', hj, hj', -, query, hq, hq'⟩ :=
      mem_support_fork hresult
    simp only [coins, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff,
      PMF.mem_support_pure_iff] at hs
    obtain ⟨c, -, trs, -, rfl⟩ := hs
    obtain ⟨-, hnamed⟩ := runWithAnswers_forkingProgram P A _ (List.ofFn h) hout.symm
    obtain ⟨-, hnamed'⟩ := runWithAnswers_forkingProgram P A _ (List.ofFn h') hout'.symm
    obtain ⟨hp, hc, hv⟩ := hnamed j hj
    obtain ⟨hp', hc', hv'⟩ := hnamed' j hj'
    rw [List.getD_ofFn] at hc hc'
    have hpoint : out.1.2.2.1 = out'.1.2.2.1 :=
      Option.some.inj (hp.symm.trans (hq.trans (hq'.symm.trans hp')))
    have hR := hsound key hkey out.1.2.2.1.2 out.1.2.2.2.1 out.1.2.2.2.2 out'.1.2.2.2.1
      out'.1.2.2.2.2 (by rw [← hc, ← hc']; exact hne) hv (by rw [hpoint]; exact hv')
    simp [hR]

omit [DecidableEq C] in
/-- If every continuation accepts at most `K` more often than another, then so does the whole
experiment. -/
private theorem bind_apply_le_add {α β : Type} {μ : PMF α} {f g : α → PMF β} {b : β}
    {K : ENNReal} (h : ∀ a ∈ μ.support, f a b ≤ g a b + K) :
    (μ.bind f) b ≤ (μ.bind g) b + K := by
  simp only [PMF.bind_apply]
  calc ∑' a, μ a * f a b ≤ ∑' a, μ a * (g a b + K) := by
        refine tsum_le_tsum fun a => ?_
        by_cases ha : a ∈ μ.support
        · exact mul_le_mul_of_nonneg_left (h a ha) zero_le
        · rw [(PMF.apply_eq_zero_iff _ _).mpr ha, zero_mul, zero_mul]
    _ = ∑' a, μ a * g a b + K := by
        simp only [mul_add, tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

omit [DecidableEq C] in
/-- **The game hops** for one key and one choice of the forger's coins: the experiment wins at
most as often as the forking program, with presampled transcripts, plus `Qs · (Qs + Qro) · δ`. -/
private theorem run_bind_finishGame_le {P : SigmaProtocol X Y T C Z} {keyGen : PMF (X × Y)}
    {R : X → Y → Prop} {simulate : Y → C → PMF (T × Z)} (hzk : P.SpecialHVZK R simulate)
    {key : X × Y} (hkey : R key.1 key.2) {δ : ENNReal}
    (hcommit : ∀ t, (P.commit key.1 key.2).map Prod.fst t ≤ δ)
    (A : Forger Y M (T × Z) (M × T) C) {Qs Qro : ℕ} (hA : A.CallBounded Qs Qro)
    (c : A.Coins) :
    ((interpret (handler (fiatShamir P keyGen) key) (A.forge key.2 c)).run ([], [])).bind
        (finishGame P key.2) true ≤
      ((PMF.iid (simulateConversation simulate key.2) (Qs + Qro)).map List.ofFn).bind (fun trs =>
        ((interpret countingUniform (forkingProgram P A (key.2, c, trs))).run 0).map
          fun run => run.1.2.1) true + (Qs * (Qs + Qro) : ℕ) * δ := by
  have h0 := run_interpret_map_state (realHandler P key) (handler (fiatShamir P keyGen) key)
    Prod.fst (realHandler_map P keyGen key) (A.forge key.2 c) (([], []), false)
  have h1 := run_interpret_map_state (programHandler P key)
    (fun q st => (simulateConversation simulate key.2).bind fun v => simulatedHandler v q st)
    Prod.fst (programHandler_map hzk hkey) (A.forge key.2 c) (([], []), false)
  have h2 := (hA.isQueryBounded key.2 c).run_interpret_presample
    (simulateConversation simulate key.2) (Classical.arbitrary _) simulatedHandler ([], [])
  have hflag := toOuterMeasure_flag_le P key hcommit (hA key.2 c).1 (hA.isQueryBounded key.2 c)
  rw [show (Qs : ENNReal) * ((Qs + Qro : ℕ) * δ) = (Qs * (Qs + Qro) : ℕ) * δ by
    push_cast; ring] at hflag
  rw [← h0, PMF.bind_map]
  refine ((identicalUntilBad P key).bind_apply_le _ _ _ _).trans (add_le_add (le_of_eq ?_) hflag)
  rw [← PMF.bind_map, h1, ← h2, PMF.bind_bind]
  refine congrArg (fun p : PMF Bool => p true) (congrArg (PMF.bind _) (funext fun trs => ?_))
  rw [PMF.bind_map, map_run_forkingProgram]
  rfl

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
statement. -/
theorem succProbability_eufCmaGame_le [Nonempty X] [Nonempty T] [Nonempty Z] [DecidableEq C]
    {P : SigmaProtocol X Y T C Z} {keyGen : PMF (X × Y)} {R : X → Y → Prop}
    [∀ x y, Decidable (R x y)] {extract : Y → T → C → Z → C → Z → X}
    {simulate : Y → C → PMF (T × Z)} {δ : ℝ≥0}
    (hkey : ∀ key ∈ keyGen.support, R key.1 key.2) (hsound : P.SpecialSoundOn keyGen R extract)
    (hzk : P.SpecialHVZK R simulate)
    (hcommit : ∀ key ∈ keyGen.support, ∀ t, (P.commit key.1 key.2).map Prod.fst t ≤ δ)
    (A : Forger Y M (T × Z) (M × T) C) {Qs Qro : ℕ} (hA : A.CallBounded Qs Qro) :
    (Game.succProbability (eufCmaGame (fiatShamir P keyGen) A) : ℝ) ≤
      Qs * (Qs + Qro) * δ + (Qro + 1) / Fintype.card C +
        √((Qro + 1) * Game.succProbability
          (oneWayGame keyGen R (reduction P simulate extract A Qs Qro))) := by
  classical
  set first := keyGen.bind fun key => coins simulate A (Qs + Qro) key.2 with hfirst
  have hA' : eufCmaGame (fiatShamir P keyGen) A true ≤
      first.bind (fun s => ((interpret countingUniform (forkingProgram P A s)).run 0).map
        fun run => run.1.2.1) true + (Qs * (Qs + Qro) : ℕ) * (δ : ENNReal) := by
    rw [eufCmaGame_fiatShamir, hfirst]
    simp only [coins, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind,
      PMF.pure_bind]
    refine bind_apply_le_add fun key hkey' => bind_apply_le_add fun c _ => ?_
    exact run_bind_finishGame_le hzk (hkey key hkey') (hcommit key hkey') A hA c
  have hQro (y : Y) (s : A.Coins) : IsCostBounded hashCost (A.forge y s) Qro := (hA y s).2
  have hB : first.bind (fun s => ((interpret countingUniform (forkingProgram P A s)).run 0).map
        fun run => run.1.2.1) true ≤
      first.bind (fun s => ((interpret countingUniform (forkingProgram P A s)).run 0).bind
        fun run => PMF.pure (validIndex (Qro + 1) run.2 run.1.1).isSome) true :=
    Probability.PMF.bind_apply_mono_on_support _ _ fun s _ => map_run_le_accept P A hQro s
  have hC := le_add_sqrt_fork first (forkingProgram P A) (Classical.arbitrary C)
    (fun s => isQueryBounded_forkingProgram P A hQro s)
  have hD := fork_le_oneWayGame (P := P) hsound simulate A Qs Qro
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure] at hC
  simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal]
  have hK : (((Qs * (Qs + Qro) : ℕ) : ENNReal) * δ).toReal = Qs * (Qs + Qro) * δ := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.coe_toReal]
    push_cast
    ring
  calc (eufCmaGame (fiatShamir P keyGen) A true).toReal
      ≤ (first.bind (fun s => ((interpret countingUniform (forkingProgram P A s)).run 0).bind
          fun run => PMF.pure (validIndex (Qro + 1) run.2 run.1.1).isSome) true).toReal +
          Qs * (Qs + Qro) * δ := by
        rw [← hK, ← ENNReal.toReal_add (PMF.apply_ne_top _ _)
          (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.coe_ne_top)]
        exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _,
          ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.coe_ne_top⟩)
          (hA'.trans (add_le_add hB le_rfl))
    _ ≤ ((Qro + 1 : ℕ) / Fintype.card C + √((Qro + 1 : ℕ) * ((Forking.fork first
          (forkingAlgorithm (Classical.arbitrary C) (Qro + 1) (forkingProgram P A))).map
            Option.isSome true).toReal)) + Qs * (Qs + Qro) * δ := add_le_add hC le_rfl
    _ ≤ _ := by
        push_cast
        have hsqrt := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
          (ENNReal.toReal_mono (PMF.apply_ne_top _ _) hD) (by positivity : (0 : ℝ) ≤ Qro + 1))
        linarith

end Cslib.Crypto.Protocols.SigmaProtocol
