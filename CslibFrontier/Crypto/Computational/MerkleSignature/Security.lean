/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.IndexedSignature.Counter
public import CslibFrontier.Crypto.Computational.MerkleSignature
public import CslibFrontier.Foundations.Data.BitString.List.Binary
public import CslibFrontier.Crypto.Computational.OneWay
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Frame
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Oracle.Tidy
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.Repeat
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Crypto.Computational.OneWayToSignature
import CslibFrontier.Crypto.Game.Hybrid
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.UniformNat

/-!
# Security of Merkle signatures

A forgery against `MerkleSignature.scheme S H depth` either contains a collision of `H k`, or it
is a one-time forgery against `S` at the leaf it names. Two reductions turn this into a bound with
an explicit loss, for every forger `A` and every security parameter `n`:

  `Pr[A forges] ≤ 2 ^ depth n * Pr[oneTimeForger A forges against S] + Pr[collisionFinder A
  finds a collision of H]`.

* `MerkleSignature.collisionFinder` generates all keys itself, answers `A`'s signing queries
  honestly, and extracts a collision from the forgery. If the forged verification key differs from
  the one at the named leaf, both open the same position of the tree, and
  `extractMerkleCollision` finds a collision in the tree. Otherwise, if the leaf already signed
  another message with the same digest, those two messages collide.
* `MerkleSignature.oneTimeForger` plants its challenge key at a uniform leaf `i`, generates the
  other keys itself, and answers the query at leaf `i` with its one-time signing oracle. Because
  the indexed game never signs twice at one leaf, it makes at most one query, and its simulation of
  the signing oracle is exact. A forgery at leaf `i` that is not a collision is a one-time forgery
  on a new digest. The factor `2 ^ depth n` is exact: the leaf is drawn from exactly
  `2 ^ depth n` values.

Merkle ([Merkle1989], Section 6) gives the construction with an informal argument. The bound is
the composition, original to this library, of the plug-and-pray argument for indexed signatures
from one-time signatures ([BonehShoup2023], Section 14.6.1, referring to Exercise 13.2), the
collision extraction behind [BonehShoup2023], Theorem 8.8, for the shrunken public key, and the
hash-and-sign bound of [BonehShoup2023], Theorem 13.1, for the digest.

## Main definitions

* `Cslib.Crypto.MerkleSignature.collisionOf`, `Cslib.Crypto.MerkleSignature.collisionFinder`: the
  reduction to collision finding.
* `Cslib.Crypto.MerkleSignature.leafIndex`, `Cslib.Crypto.MerkleSignature.plantKeys`,
  `Cslib.Crypto.MerkleSignature.plantedHandler`, `Cslib.Crypto.MerkleSignature.oneTimeForgerAt`,
  `Cslib.Crypto.MerkleSignature.oneTimeForger`: the reduction to one-time forgery.

## Main results

* `Cslib.Crypto.MerkleSignature.succProbability_indexedEufCmaGame_le`: the explicit bound.
* `Cslib.Crypto.MerkleSignature.isPPT_collisionFinder`,
  `Cslib.Crypto.MerkleSignature.isOraclePPT_oneTimeForger`: the reductions are efficient.
* `Cslib.Crypto.MerkleSignature.eval_leafIndex`, `Cslib.Crypto.MerkleSignature.isPPTOn_leafIndex`:
  the leaf is exactly uniform and sampled efficiently.
* `Cslib.Crypto.SignatureScheme.OneTimeEUFCMA.indexedEUFCMA_merkle`: one-time security of `S` and
  collision resistance of `H` give indexed EUF-CMA security.
* `Cslib.Crypto.OneWay.exists_indexedEUFCMA`: a one-way function and a collision-resistant hash
  family give indexed EUF-CMA secure signatures of every polynomial capacity `2 ^ depth n`.
* `Cslib.Crypto.OneWay.exists_counterEUFCMA`: used with a counter, they give counter-stateful
  many-time signatures of every polynomial capacity.

## References

* [R. C. Merkle, *A Certified Digital Signature*][Merkle1989], Section 6.
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Sections 8.9, 13.2 and 14.6.1.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

namespace MerkleSignature

variable (S : SignatureScheme) (H : List Bool → List Bool → List Bool) (depth : ℕ → ℕ)

/-! ### The reduction to collision finding -/

/-- The candidate collision of `H k` in a forgery `out = ((u, msg, sig), signed)` against the
keys `keys`: a collision in the tree if the forged verification key is not the one at leaf `u`,
and otherwise the forged message with a message signed at leaf `u` with the same digest. -/
def collisionOf (k : List Bool) (keys : List (List Bool × List Bool))
    (out : (ℕ × List Bool × List Bool) × List (ℕ × List Bool)) : List Bool × List Bool :=
  let ((u, msg, sig), signed) := out
  let (vk, _, path) := signatureDecoder.decode sig
  let vks := keys.map Prod.fst
  if vk == vks.getD u [] then
    (msg, (signed.find? fun e => e.1 == u && H k e.2 == H k msg).elim [] Prod.snd)
  else
    extractMerkleCollision H k vk (vks.getD u []) u path (merklePath H k vks u)

/-- The collision finder: given the hash key `k`, generate the one-time keys, answer the forger's
signing queries honestly, and return `collisionOf` its forgery. -/
noncomputable def collisionFinder
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k m, (H k m).length = k.length)
    (hcap : ComputableInPolyTime (fun n => 2 ^ depth n) encUnary encUnary)
    (adversary : IndexedForger) : CollisionFinder := fun n k => do
  let keys ← OracleComp.replicate (2 ^ depth n) (S.keyGen n)
  let out ← (OracleComp.interpret
    (OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifFin j))
      ((scheme S H depth hH hlen hcap).indexedSigningOracle n (secretKey k keys)))
    (adversary n (publicKey H k keys))).run []
  return collisionOf H k keys out

/-! ### The reduction to one-time forgery -/

/-- A uniform leaf below `2 ^ depth n`, from `depth n` fair bits. -/
noncomputable def leafIndex (n : ℕ) : ProbComp ℕ :=
  BitString.boundedBinaryValue (2 ^ depth n) <$> BitString.sampleList (depth n)

/-- Sample a hash key and the one-time keys of every leaf except leaf `i`, where the
verification key `vk` is planted with an empty secret key. -/
noncomputable def plantKeys (n i : ℕ) (vk : List Bool) :
    ProbComp (List Bool × List (List Bool × List Bool)) := do
  let k ← BitString.sampleList n
  let front ← OracleComp.replicate i (S.keyGen n)
  let back ← OracleComp.replicate (2 ^ depth n - i - 1) (S.keyGen n)
  return (k, front ++ (vk, []) :: back)

/-- The one-time forger's answer to a signing request: as the indexed signing oracle, except that
leaf `i` is signed by an external query to the one-time signing oracle, whose reply is truncated
to `bound` bits. -/
def plantedHandler (n : ℕ) (k : List Bool) (keys : List (List Bool × List Bool)) (i bound : ℕ)
    (request : Unit × List Bool) :
    StateT (List (ℕ × List Bool)) (WordOracleComp Unit) (List Bool) := fun signed =>
  let r := IndexedSignatureScheme.requestDecoder.decode request.2
  if r.1 < 2 ^ depth n ∧ r.1 ∉ signed.map Prod.fst then
    if r.1 = i then
      (fun ots => (encodeSignature (keys.getD i ([], [])).1 ots
        (merklePath H k (keys.map Prod.fst) i), r :: signed)) <$>
          (List.take bound <$> ProbOracleComp.query ((), H k r.2))
    else
      (fun sig => (sig, r :: signed)) <$> ProbOracleComp.sample (signWith S H k keys r.1 r.2)
  else
    pure ([], signed)

/-- The one-time forger with its challenge planted at leaf `i`. -/
noncomputable def oneTimeForgerAt (bound : ℕ → ℕ) (adversary : IndexedForger) (i : ℕ) :
    Forger := fun n vk => do
  let setup ← ProbOracleComp.sample (plantKeys S depth n i vk)
  let out ← (OracleComp.interpret
    (OracleComp.sumHandler (fun j => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin j)))
      (plantedHandler S H depth n setup.1 setup.2 i (bound n)))
    (adversary n (publicKey H setup.1 setup.2))).run []
  let ((_, msg, sig), _) := out
  let (_, ots, _) := signatureDecoder.decode sig
  return (H setup.1 msg, ots)

/-- The one-time forger: plant the challenge at a uniform leaf. -/
noncomputable def oneTimeForger (bound : ℕ → ℕ) (adversary : IndexedForger) : Forger :=
  fun n vk => do
    let i ← ProbOracleComp.sample (leafIndex depth n)
    oneTimeForgerAt S H depth bound adversary i n vk

/-! ### Exact simulation by the one-time forger -/

/-- The log of the one-time signing oracle implied by an indexed log: the digest of the message
signed at leaf `i`, if any. -/
private def otsLogOf (i : ℕ) (k : List Bool) (signed : List (ℕ × List Bool)) : List (List Bool) :=
  (signed.filter fun e => e.1 == i).map fun e => H k e.2

variable {S H depth} in
/-- The one-time forger's handler, followed by the one-time signing oracle on the planted key,
is the indexed signing oracle on the real keys: the joint run is the real run, with the one-time
oracle's log determined by the indexed log. -/
private theorem eval_run_plantedHandler
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k m, (H k m).length = k.length)
    (hcap : ComputableInPolyTime (fun n => 2 ^ depth n) encUnary encUnary)
    {n b : ℕ} {k : List Bool} {front back : List (List Bool × List Bool)}
    {x : List Bool × List Bool} (hk : k.length = n)
    (hbound : ∀ msg, msg.length = n → ∀ σ ∈ (ProbComp.eval (S.sign x.2 msg)).support,
      σ.length ≤ b)
    {α : Type} (program : WordOracleComp Unit α) :
    ProbOracleComp.runWith (fun q s => ProbComp.eval (S.oneTimeSigningOracle x.2 q s))
      ((OracleComp.interpret
        (OracleComp.sumHandler
          (fun j => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin j)))
          (plantedHandler S H depth n k (front ++ (x.1, []) :: back) front.length b))
        program).run []) [] =
    (ProbOracleComp.runWith (fun q s => ProbComp.eval
      ((scheme S H depth hH hlen hcap).indexedSigningOracle n (secretKey k (front ++ x :: back))
        q s)) program []).map
      (fun r => (r, otsLogOf H front.length k r.2)) := by
  rw [ProbOracleComp.runWith_run_interpret]
  have hsim := ProbOracleComp.runWith_map_state_of_invariant
    (oracle := fun (q : Unit × List Bool) (signed : List (ℕ × List Bool)) => ProbComp.eval
      ((scheme S H depth hH hlen hcap).indexedSigningOracle n
        (secretKey k (front ++ x :: back)) q signed))
    (oracle' := fun (q : Unit × List Bool) (state : List (ℕ × List Bool) × List (List Bool)) =>
      (ProbOracleComp.runWith (fun q s => ProbComp.eval (S.oneTimeSigningOracle x.2 q s))
        ((plantedHandler S H depth n k (front ++ (x.1, []) :: back) front.length b q).run
          state.1) state.2).map (fun result => (result.1.1, result.1.2, result.2)))
    (represent := fun signed => (signed, otsLogOf H front.length k signed))
    (invariant := fun _ => True) (by simp)
    (step := by
      have hmapApply : ∀ {σ β γ : Type} (f : β → γ) (p : StateT σ PMF β) (state : σ),
          (f <$> p) state = (p state).map (fun r => (f r.1, r.2)) := fun _ _ _ => rfl
      have hpureApply : ∀ {σ β : Type} (a : β) (state : σ),
          (pure a : StateT σ PMF β) state = PMF.pure (a, state) := fun _ _ => rfl
      have hsampleApply : ∀ {β : Type} (p : ProbComp β) (state : List (List Bool)),
          (OracleComp.interpret
            (OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifOracle j))
              (fun q s => ProbComp.eval (S.oneTimeSigningOracle x.2 q s)))
            (ProbOracleComp.sample p)) state = (ProbComp.eval p).map (·, state) :=
        fun p state => ProbOracleComp.runWith_sample _ p state
      rintro ⟨⟨⟩, w⟩ signed -
      unfold IndexedSignatureScheme.indexedSigningOracle plantedHandler
      simp only [scheme, StateT.run, ProbOracleComp.runWith, OracleComp.runWith]
      generalize IndexedSignatureScheme.requestDecoder.decode w = r
      obtain ⟨u, m⟩ := r
      dsimp only
      by_cases hguard : u < 2 ^ depth n ∧ u ∉ signed.map Prod.fst
      · simp only [hguard, not_false_eq_true, and_self, ↓reduceIte]
        have hkeys : (front ++ (x.1, []) :: back).map Prod.fst =
            (front ++ x :: back).map Prod.fst := by
          simp
        by_cases hi : u = front.length
        · subst hi
          have hempty : otsLogOf H front.length k signed = [] := by
            simp only [otsLogOf, List.map_eq_nil_iff, List.filter_eq_nil_iff, beq_iff_eq]
            intro e he heq
            exact hguard.2 (List.mem_map.mpr ⟨e, he, heq⟩)
          simp only [↓reduceIte, hempty, sign, secretKey, secretKeyDecoder.decode_enc, signWith,
            List.getD_append_cons_length, hkeys, OracleComp.interpret_map,
            ProbOracleComp.interpret_query, SignatureScheme.oneTimeSigningOracle, List.isEmpty_nil,
            ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_bind, PMF.bind_bind, PMF.pure_bind,
            PMF.pure_map, hmapApply]
          refine PMF.bind_congr_on_support _ _ _ fun σ hσ => ?_
          have hots : otsLogOf H front.length k ((front.length, m) :: signed) = [H k m] := by
            rw [← List.singleton_append, ← hempty]
            simp [otsLogOf]
          rw [hots, List.take_of_length_le (hbound _ (by rw [hlen, hk]) σ hσ)]
        · have hots : otsLogOf H front.length k ((u, m) :: signed) =
              otsLogOf H front.length k signed := by
            simp [otsLogOf, hi]
          simp only [hi, ↓reduceIte, sign, secretKey, secretKeyDecoder.decode_enc, signWith, hkeys,
            List.getD_append_cons_of_ne front back x (x.1, []) ([], []) hi,
            OracleComp.interpret_map,
            ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_bind, hmapApply, hsampleApply,
            PMF.bind_bind, PMF.pure_bind, PMF.pure_map, hots]
      · simp only [hguard, ↓reduceIte, ProbComp.eval_pure, PMF.pure_map, OracleComp.interpret_pure,
          hpureApply])
    program [] trivial
  rw [show otsLogOf H front.length k [] = [] from rfl] at hsim
  erw [← hsim, PMF.map_comp]
  rfl

/-- The run of the forger against the honest indexed signing oracle on the keys `keys`. -/
private noncomputable def realRun
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k m, (H k m).length = k.length)
    (hcap : ComputableInPolyTime (fun n => 2 ^ depth n) encUnary encUnary)
    (adversary : IndexedForger) (n : ℕ) (k : List Bool) (keys : List (List Bool × List Bool)) :
    PMF ((ℕ × List Bool × List Bool) × List (ℕ × List Bool)) :=
  ProbComp.eval ((OracleComp.interpret
    (OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifFin j))
      ((scheme S H depth hH hlen hcap).indexedSigningOracle n (secretKey k keys)))
    (adversary n (publicKey H k keys))).run [])

/-- The one-time forger at leaf `i` wins, read off the real run. -/
private def otsWin (n i : ℕ) (k : List Bool) (keys : List (List Bool × List Bool))
    (r : (ℕ × List Bool × List Bool) × List (ℕ × List Bool)) : Bool :=
  ((H k r.1.2.1).length == n) && !(otsLogOf H i k r.2).contains (H k r.1.2.1) &&
    S.verify (keys.getD i ([], [])).1 (H k r.1.2.1) (signatureDecoder.decode r.1.2.2).2.1

variable {S H depth} in
private theorem eval_eufOneTimeGame_oneTimeForgerAt
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k m, (H k m).length = k.length)
    (hcap : ComputableInPolyTime (fun n => 2 ^ depth n) encUnary encUnary)
    {bound : ℕ → ℕ} {n : ℕ}
    (hbound : ∀ x ∈ (ProbComp.eval (S.keyGen n)).support, ∀ msg, msg.length = n →
      ∀ σ ∈ (ProbComp.eval (S.sign x.2 msg)).support, σ.length ≤ bound n)
    (adversary : IndexedForger) (i : ℕ) :
    ProbComp.eval (S.eufOneTimeGame (oneTimeForgerAt S H depth bound adversary i) n) =
      (ProbComp.eval (S.keyGen n)).bind fun x =>
        (BitString.uniformList n).bind fun k =>
          (ProbComp.eval (OracleComp.replicate i (S.keyGen n))).bind fun front =>
            (ProbComp.eval (OracleComp.replicate (2 ^ depth n - i - 1) (S.keyGen n))).bind
              fun back => (realRun S H depth hH hlen hcap adversary n k (front ++ x :: back)).map
                (otsWin S H n i k (front ++ x :: back)) := by
  simp only [SignatureScheme.eufOneTimeGame, oneTimeForgerAt, ProbComp.eval_bind,
    ProbComp.eval_pure, ProbOracleComp.eval_run_interpret_eq_runWith,
    ProbOracleComp.runWith_bind, ProbOracleComp.runWith_sample, ProbOracleComp.runWith_pure,
    plantKeys, BitString.eval_sampleList, PMF.map_bind,
    PMF.bind_bind, PMF.pure_bind, PMF.pure_map]
  refine PMF.bind_congr_on_support _ _ _ fun x hx => ?_
  refine PMF.bind_congr_on_support _ _ _ fun k hk => ?_
  refine PMF.bind_congr_on_support _ _ _ fun front hfront => ?_
  refine PMF.bind_congr_on_support _ _ _ fun back _ => ?_
  have hklen : k.length = n := BitString.length_of_mem_support_uniformList hk
  have hfrontLen : front.length = i :=
    ((ProbComp.mem_support_replicate_iff _ _ _).mp hfront).1
  subst hfrontLen
  rw [eval_run_plantedHandler hH hlen hcap hklen (hbound x hx) (adversary n _)]
  have hpk : publicKey H k (front ++ (x.1, []) :: back) = publicKey H k (front ++ x :: back) := by
    simp [publicKey]
  rw [hpk, PMF.bind_map, realRun, ProbOracleComp.eval_run_interpret_eq_runWith,
    ← PMF.bind_pure_comp]
  congr 1 with r : 1
  simp only [Function.comp_apply, otsWin, List.getD_append_cons_length]

/-- The real experiment: the hash key, the one-time keys and the forger's run. -/
private noncomputable def realExp
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k m, (H k m).length = k.length)
    (hcap : ComputableInPolyTime (fun n => 2 ^ depth n) encUnary encUnary)
    (adversary : IndexedForger) (n : ℕ) :
    PMF (List Bool × List (List Bool × List Bool) ×
      ((ℕ × List Bool × List Bool) × List (ℕ × List Bool))) := do
  let k ← BitString.uniformList n
  let keys ← ProbComp.eval (OracleComp.replicate (2 ^ depth n) (S.keyGen n))
  (realRun S H depth hH hlen hcap adversary n k keys).map fun r => (k, keys, r)

variable {S H depth} in
private theorem map_otsWin_realExp
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k m, (H k m).length = k.length)
    (hcap : ComputableInPolyTime (fun n => 2 ^ depth n) encUnary encUnary)
    {bound : ℕ → ℕ} {n : ℕ}
    (hbound : ∀ x ∈ (ProbComp.eval (S.keyGen n)).support, ∀ msg, msg.length = n →
      ∀ σ ∈ (ProbComp.eval (S.sign x.2 msg)).support, σ.length ≤ bound n)
    (adversary : IndexedForger) {i : ℕ} (hi : i < 2 ^ depth n) :
    (realExp S H depth hH hlen hcap adversary n).map
        (fun t => otsWin S H n i t.1 t.2.1 t.2.2) =
      ProbComp.eval (S.eufOneTimeGame (oneTimeForgerAt S H depth bound adversary i) n) := by
  rw [eval_eufOneTimeGame_oneTimeForgerAt hH hlen hcap hbound adversary i, realExp]
  have hsplit : 2 ^ depth n = i + ((2 ^ depth n - i - 1) + 1) := by omega
  rw [hsplit, ← ProbComp.eval_replicate_splice, ← hsplit]
  simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.monad_bind_eq_bind, PMF.map_bind,
    PMF.bind_bind, PMF.pure_bind, PMF.map_comp, Function.comp_def]
  rw [PMF.bind_comm]

variable {S H depth} in
private theorem eval_indexedEufCmaGame_eq
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k m, (H k m).length = k.length)
    (hcap : ComputableInPolyTime (fun n => 2 ^ depth n) encUnary encUnary)
    (adversary : IndexedForger) (n : ℕ) :
    ProbComp.eval ((scheme S H depth hH hlen hcap).indexedEufCmaGame adversary n) =
      (realExp S H depth hH hlen hcap adversary n).map fun t =>
        !t.2.2.2.contains (t.2.2.1.1, t.2.2.1.2.1) &&
          verify S H depth (publicKey H t.1 t.2.1) t.2.2.1.1 t.2.2.1.2.1 t.2.2.1.2.2 := by
  simp only [IndexedSignatureScheme.indexedEufCmaGame, scheme, keyGen, realExp, realRun,
    ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList, PMF.monad_bind_eq_bind,
    PMF.map_bind, PMF.bind_bind, PMF.pure_bind, PMF.map_comp, Function.comp_def]
  rfl

variable {S H depth} in
private theorem eval_collisionGame_eq
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k m, (H k m).length = k.length)
    (hcap : ComputableInPolyTime (fun n => 2 ^ depth n) encUnary encUnary)
    (adversary : IndexedForger) (n : ℕ) :
    ProbComp.eval (collisionGame H (fun _ _ => true)
        (collisionFinder S H depth hH hlen hcap adversary) n) =
      (realExp S H depth hH hlen hcap adversary n).map fun t =>
        isCollision H (fun _ _ => true) n t.1 (collisionOf H t.1 t.2.1 t.2.2).1
          (collisionOf H t.1 t.2.1 t.2.2).2 := by
  simp only [collisionGame, collisionFinder, realExp, realRun, ProbComp.eval_bind,
    ProbComp.eval_pure, BitString.eval_sampleList, PMF.monad_bind_eq_bind, PMF.map_bind,
    PMF.bind_bind, PMF.pure_bind, PMF.map_comp, Function.comp_def]
  rfl

variable {S H depth} in
/-- **The case split of a forgery**: a valid forgery on a fresh pair either contains a collision
of `H k`, found by `collisionOf`, or is a one-time forgery at the leaf it names. -/
private theorem win_cases (hlen : ∀ k m, (H k m).length = k.length) {n : ℕ} {k : List Bool}
    {keys : List (List Bool × List Bool)} (hk : k.length = n)
    (hkeys : keys.length = 2 ^ depth n)
    (r : (ℕ × List Bool × List Bool) × List (ℕ × List Bool))
    (hwin : (!r.2.contains (r.1.1, r.1.2.1) &&
      verify S H depth (publicKey H k keys) r.1.1 r.1.2.1 r.1.2.2) = true) :
    isCollision H (fun _ _ => true) n k (collisionOf H k keys r).1
        (collisionOf H k keys r).2 = true ∨
      (List.range (2 ^ depth n)).any (fun i => otsWin S H n i k keys r) = true := by
  obtain ⟨⟨u, m, sig⟩, signed⟩ := r
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hwin
  obtain ⟨hfresh, hver⟩ := hwin
  have hnot : (u, m) ∉ signed := fun hmem => by
    rw [List.contains_iff_mem.mpr hmem] at hfresh
    exact Bool.noConfusion hfresh
  simp only [verify, publicKey, encPair_apply, unframe_frame_append, dropFrame_frame_append,
    encBits_apply, hk, Bool.and_eq_true] at hver
  obtain ⟨hopen, hots⟩ := hver
  have hu : u < 2 ^ depth n := by
    simp only [merkleVerify, Bool.and_eq_true, decide_eq_true_eq] at hopen
    exact hopen.1.2
  have hdepth : Nat.clog 2 (keys.map Prod.fst).length = depth n := by
    rw [List.length_map, hkeys, Nat.clog_pow _ _ (by norm_num)]
  have hu' : u < keys.length := hkeys ▸ hu
  have hvks : (keys.map Prod.fst).getD u [] = (keys.getD u ([], [])).1 := by
    rw [List.getD_eq_getElem _ _ (by simpa using hu'), List.getD_eq_getElem _ _ hu',
      List.getElem_map]
  by_cases hvk : (signatureDecoder.decode sig).1 = (keys.map Prod.fst).getD u []
  · by_cases hfound : ∃ e ∈ signed, e.1 = u ∧ H k e.2 = H k m
    · left
      obtain ⟨e, he, heu, hem⟩ := hfound
      have hsome : (signed.find? fun e => e.1 == u && H k e.2 == H k m).isSome :=
        List.find?_isSome.mpr ⟨e, he, by simp [heu, hem]⟩
      obtain ⟨e', he'⟩ := Option.isSome_iff_exists.mp hsome
      have hmem := List.mem_of_find?_eq_some he'
      have hprop := List.find?_some he'
      simp only [Bool.and_eq_true, beq_iff_eq] at hprop
      have hne : m ≠ e'.2 := fun h => hnot (by rw [h, ← hprop.1]; exact hmem)
      simp only [collisionOf, hvk, beq_self_eq_true, ↓reduceIte, he', Option.elim_some,
        isCollision_eq_true_iff]
      exact ⟨trivial, trivial, hne, hprop.2.symm⟩
    · right
      simp only [List.any_eq_true, List.mem_range]
      refine ⟨u, hu, ?_⟩
      have hnotin : ¬ (otsLogOf H u k signed).contains (H k m) = true := by
        rw [List.contains_iff_mem]
        simp only [otsLogOf, List.mem_map, List.mem_filter, beq_iff_eq]
        rintro ⟨e, ⟨he, heu⟩, hem⟩
        exact hfound ⟨e, he, heu, hem⟩
      simp only [otsWin, Bool.and_eq_true, beq_iff_eq, hlen, hk, true_and]
      refine ⟨by simpa using hnotin, ?_⟩
      rw [← hvks, ← hvk]
      exact hots
  · left
    have hcol := isCollision_of_merkleVerify hopen
      (merkleVerify_merklePath_of_clog_eq (H := H) (k := k) hdepth hu) hvk n
    simpa only [collisionOf, beq_iff_eq, hvk, ↓reduceIte] using hcol

/-- **The leaf is exactly uniform** below `2 ^ depth n`, the law of
`ProbComp.sampleBinaryNat (depth n)` (`ProbComp.eval_sampleBinaryNat`). `leafIndex` reads its bits
with `BitString.boundedBinaryValue`, whose cap `2 ^ depth n` never binds, because the reduction
needs the leaf in unary (`isPPTOn_leafIndex`), and `Probability.isPPTOn_sampleBinaryNat` outputs
it in binary. -/
theorem eval_leafIndex (n : ℕ) :
    ProbComp.eval (leafIndex depth n) =
      (PMF.uniformOfFintype (Fin (2 ^ depth n))).map Fin.val := by
  simp only [leafIndex, ProbComp.eval_map, BitString.eval_sampleList,
    BitString.uniformList_boundedBinaryValue]
  congr 1 with i : 1
  exact Nat.min_eq_right i.isLt.le

variable {S H depth} in
private theorem eval_eufOneTimeGame_oneTimeForger (bound : ℕ → ℕ) (adversary : IndexedForger)
    (n : ℕ) :
    ProbComp.eval (S.eufOneTimeGame (oneTimeForger S H depth bound adversary) n) =
      (PMF.uniformOfFintype (Fin (2 ^ depth n))).bind fun i =>
        ProbComp.eval (S.eufOneTimeGame (oneTimeForgerAt S H depth bound adversary i.val) n) := by
  simp only [SignatureScheme.eufOneTimeGame, oneTimeForger, ProbComp.eval_bind,
    ProbComp.eval_pure, ProbOracleComp.eval_run_interpret_eq_runWith,
    ProbOracleComp.runWith_bind, ProbOracleComp.runWith_sample, eval_leafIndex, PMF.bind_map,
    PMF.bind_bind, Function.comp_def]
  rw [PMF.bind_comm]

/-! ### The explicit bound -/

variable {S H depth} in
/-- **Security of Merkle signatures, with an explicit loss.** For every forger and every security
parameter `n`, the forging probability against `MerkleSignature.scheme S H depth` is at most
`2 ^ depth n` times the success of `oneTimeForger` against `S` in the one-time game, plus the
success of `collisionFinder` in the collision game of `H`. The bound `bound n` must cover the
length of every one-time signature on an `n`-bit message under a supported key; the one-time
forger truncates replies to it. -/
theorem succProbability_indexedEufCmaGame_le
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k m, (H k m).length = k.length)
    (hcap : ComputableInPolyTime (fun n => 2 ^ depth n) encUnary encUnary)
    {bound : ℕ → ℕ} {n : ℕ}
    (hbound : ∀ x ∈ (ProbComp.eval (S.keyGen n)).support, ∀ msg, msg.length = n →
      ∀ σ ∈ (ProbComp.eval (S.sign x.2 msg)).support, σ.length ≤ bound n)
    (adversary : IndexedForger) :
    Game.succProbability
        (ProbComp.eval ((scheme S H depth hH hlen hcap).indexedEufCmaGame adversary n)) ≤
      2 ^ depth n * Game.succProbability
          (ProbComp.eval (S.eufOneTimeGame (oneTimeForger S H depth bound adversary) n)) +
        Game.succProbability (ProbComp.eval (collisionGame H (fun _ _ => true)
          (collisionFinder S H depth hH hlen hcap adversary) n)) := by
  set X := realExp S H depth hH hlen hcap adversary n with hX
  have hsupp : ∀ t ∈ X.support, t.1.length = n ∧ t.2.1.length = 2 ^ depth n := by
    intro t ht
    simp only [X, realExp, PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff,
      PMF.mem_support_map_iff] at ht
    obtain ⟨k, hk, keys, hkeys, r, _, rfl⟩ := ht
    exact ⟨BitString.length_of_mem_support_uniformList hk,
      ((ProbComp.mem_support_replicate_iff _ _ _).mp hkeys).1⟩
  have hsplit : ProbComp.eval ((scheme S H depth hH hlen hcap).indexedEufCmaGame adversary n) true ≤
      ProbComp.eval (collisionGame H (fun _ _ => true)
          (collisionFinder S H depth hH hlen hcap adversary) n) true +
        ∑ i ∈ Finset.range (2 ^ depth n),
          ProbComp.eval (S.eufOneTimeGame (oneTimeForgerAt S H depth bound adversary i) n)
            true := by
    rw [eval_indexedEufCmaGame_eq hH hlen hcap adversary n,
      eval_collisionGame_eq hH hlen hcap adversary n]
    refine (PMF.map_true_le_add X ?_).trans
      (add_le_add le_rfl ((PMF.map_any_range_true_le_sum X (2 ^ depth n)
        (fun i t => otsWin S H n i t.1 t.2.1 t.2.2)).trans ?_))
    · intro t ht hwin
      obtain ⟨hk, hkeys⟩ := hsupp t ht
      exact win_cases hlen hk hkeys t.2.2 hwin
    · refine Finset.sum_le_sum fun i hi => ?_
      rw [map_otsWin_realExp hH hlen hcap hbound adversary (Finset.mem_range.mp hi)]
  have havg : ((2 ^ depth n : ℕ) : ℝ≥0∞) *
        ProbComp.eval (S.eufOneTimeGame (oneTimeForger S H depth bound adversary) n) true =
      ∑ i ∈ Finset.range (2 ^ depth n),
        ProbComp.eval (S.eufOneTimeGame (oneTimeForgerAt S H depth bound adversary i) n) true := by
    rw [eval_eufOneTimeGame_oneTimeForger, PMF.bind_apply, tsum_fintype]
    simp only [PMF.uniformOfFintype_apply, Fintype.card_fin]
    rw [← Finset.mul_sum, ← mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp), one_mul,
      ← Fin.sum_univ_eq_sum_range (fun i => ProbComp.eval
        (S.eufOneTimeGame (oneTimeForgerAt S H depth bound adversary i) n) true)]
  rw [← havg] at hsplit
  have hfin : ProbComp.eval (collisionGame H (fun _ _ => true)
        (collisionFinder S H depth hH hlen hcap adversary) n) true +
      ((2 ^ depth n : ℕ) : ℝ≥0∞) *
        ProbComp.eval (S.eufOneTimeGame (oneTimeForger S H depth bound adversary) n) true ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _,
      ENNReal.mul_ne_top (by simp) (PMF.apply_ne_top _ _)⟩
  have h := ENNReal.toNNReal_mono hfin hsplit
  rw [ENNReal.toNNReal_add (PMF.apply_ne_top _ _)
    (ENNReal.mul_ne_top (by simp) (PMF.apply_ne_top _ _)), ENNReal.toNNReal_mul,
    ENNReal.toNNReal_natCast] at h
  simpa only [Game.succProbability, Nat.cast_pow, Nat.cast_ofNat, add_comm] using h

/-! ### Efficiency of the reductions -/

section Efficiency

variable {S H depth}
variable (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
  (encPair encBits encBits) encBits)
  (hlen : ∀ k m, (H k m).length = k.length)
  (hcap : ComputableInPolyTime (fun n => 2 ^ depth n) encUnary encUnary)

include hH hlen in
private theorem computableTidilyInPolyTime_collisionOf :
    ComputableTidilyInPolyTime
      (fun q : ((ℕ × List Bool) × List (List Bool × List Bool)) ×
          ((ℕ × List Bool × List Bool) × List (ℕ × List Bool)) =>
        collisionOf H q.1.1.2 q.1.2 q.2)
      (encPair (encPair (encPair encUnary encBits) (encList (encPair encBits encBits)))
        (encPair (encPair encUnary (encPair encBits encBits)) (encList (encPair encUnary encBits))))
      (encPair encBits encBits) := by
  let E := encPair (encPair (encPair encUnary encBits) (encList (encPair encBits encBits)))
    (encPair (encPair encUnary (encPair encBits encBits)) (encList (encPair encUnary encBits)))
  have hfst₁ := ComputableTidilyInPolyTime.fst
    (encPair (encPair encUnary encBits) (encList (encPair encBits encBits)))
    (encPair (encPair encUnary (encPair encBits encBits)) (encList (encPair encUnary encBits)))
  have hsnd₁ := ComputableTidilyInPolyTime.snd
    (encPair (encPair encUnary encBits) (encList (encPair encBits encBits)))
    (encPair (encPair encUnary (encPair encBits encBits)) (encList (encPair encUnary encBits)))
  have hk := hfst₁.fst'.snd'
  have hkeys := hfst₁.snd'
  have hforgery := hsnd₁.fst'
  have hlog := hsnd₁.snd'
  have hu := hforgery.fst'
  have hm := hforgery.snd'.fst'
  have hsig := hforgery.snd'.snd'
  have hvks := (ComputableTidilyInPolyTime.map
    (ComputableTidilyInPolyTime.fst encBits encBits)).comp hkeys
  have hvku := (ComputableTidilyInPolyTime.listGetD (encA := encBits) []).comp (hvks.prod hu)
  have hdec := signatureDecoder.computableInPolyTime.tidy.comp hsig
  have hvk := hdec.fst'
  have hpath' := hdec.snd'.snd'
  have hcond := ComputableTidilyInPolyTime.beq hvk hvku
  have htest : ComputableTidilyInPolyTime
      (fun p : (((ℕ × List Bool) × List (List Bool × List Bool)) ×
          ((ℕ × List Bool × List Bool) × List (ℕ × List Bool))) × (ℕ × List Bool) =>
        p.2.1 == p.1.2.1.1 && H p.1.1.1.2 p.2.2 == H p.1.1.1.2 p.1.2.1.2.1)
      (encPair E (encPair encUnary encBits)) encBool := by
    have hq := ComputableTidilyInPolyTime.fst E (encPair encUnary encBits)
    have he := ComputableTidilyInPolyTime.snd E (encPair encUnary encBits)
    exact ComputableTidilyInPolyTime.bool_and'
      (ComputableTidilyInPolyTime.beq he.fst' (hu.comp hq))
      (ComputableTidilyInPolyTime.beq
        (hH.tidy.comp ((hk.comp hq).prod he.snd'))
        (hH.tidy.comp ((hk.comp hq).prod (hm.comp hq))))
  have hfind := ComputableTidilyInPolyTime.findWithInput
    (test := fun q e => e.1 == q.2.1.1 && H q.1.1.2 e.2 == H q.1.1.2 q.2.1.2.1) hlog htest
  have hprev := ComputableTidilyInPolyTime.optionElimWithInput (body := fun _ e => e.2) hfind
    (ComputableTidilyInPolyTime.const []) (ComputableTidilyInPolyTime.snd _ _).snd'
  have hpath := (computableInPolyTime_merklePath hH hlen).tidy.comp (hk.prod (hvks.prod hu))
  have hextract := (computableInPolyTime_extractMerkleCollision hH hlen).tidy.comp
    (hk.prod ((hvk.prod hvku).prod (hu.prod (hpath'.prod hpath))))
  unfold collisionOf
  exact ComputableTidilyInPolyTime.cond hcond (hm.prod hprev) hextract

include hH hlen hcap in
/-- The collision finder is uniformly strict PPT for every oracle-PPT forger. -/
theorem isPPT_collisionFinder {adversary : IndexedForger}
    (hadversary : IsOraclePPT (encPair encUnary (encPair encBits encBits)) adversary) :
    IsPPT (encPair encBits encBits) (collisionFinder S H depth hH hlen hcap adversary) := by
  change IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
    (fun p => collisionFinder S H depth hH hlen hcap adversary p.1 p.2)
  have hkeys : IsPPTOn (encPair encUnary encBits) (encList (encPair encBits encBits))
      (fun p : ℕ × List Bool => OracleComp.replicate (2 ^ depth p.1) (S.keyGen p.1)) :=
    (S.isPPTOn_keyGen_comp (ComputableInPolyTime.fst encUnary encBits)).replicate
      (.of_tidy (hcap.tidy.comp (ComputableTidilyInPolyTime.fst encUnary encBits)))
  have hfst := ComputableTidilyInPolyTime.fst (encPair encUnary encBits)
    (encList (encPair encBits encBits))
  have hkk : ComputableTidilyInPolyTime
      (fun q : (ℕ × List Bool) × List (List Bool × List Bool) => (q.1.2, q.2))
      (encPair (encPair encUnary encBits) (encList (encPair encBits encBits)))
      (encPair encBits (encList (encPair encBits encBits))) :=
    hfst.snd'.prod (ComputableTidilyInPolyTime.snd _ _)
  have hprep : ComputableTidilyInPolyTime
      (fun q : (ℕ × List Bool) × List (List Bool × List Bool) =>
        (q.1.1, publicKey H q.1.2 q.2, secretKey q.1.2 q.2))
      (encPair (encPair encUnary encBits) (encList (encPair encBits encBits)))
      (encPair encUnary (encPair encBits encBits)) :=
    hfst.fst'.prod
      (((computableInPolyTime_publicKey hH hlen).tidy.comp hkk).prod
        ((ComputableTidilyInPolyTime.encode
          (encPair encBits (encList (encPair encBits encBits)))).comp hkk))
  have hrun₀ := (scheme S H depth hH hlen hcap).isPPTOn_run_indexedSigningOracle hadversary
  have hrun := hrun₀.preprocess
    (prepare := fun q : (ℕ × List Bool) × List (List Bool × List Bool) =>
      (q.1.1, publicKey H q.1.2 q.2, secretKey q.1.2 q.2)) (.of_tidy hprep)
  exact hkeys.bind_with (hrun.bind_with (computableTidilyInPolyTime_collisionOf hH hlen).isPPTOn)

include hcap in
/-- Sampling a uniform leaf is uniformly strict PPT. -/
theorem isPPTOn_leafIndex : IsPPTOn encUnary encUnary (leafIndex depth) := by
  have hdepth := (computableInPolyTime_depth hcap).tidy
  unfold leafIndex
  exact (ComputableInPolyTime.sampleList (.of_tidy hdepth)).map_with
    (.of_tidy (ComputableTidilyInPolyTime.bitsBoundedBinaryValueWithInput
      (hcap.tidy.comp (ComputableTidilyInPolyTime.fst _ _)) (ComputableTidilyInPolyTime.snd _ _)))

include hcap in
private theorem isPPTOn_plantKeys :
    IsPPTOn (encPair (encPair encUnary encBits) encUnary)
      (encPair encBits (encList (encPair encBits encBits)))
      (fun c : (ℕ × List Bool) × ℕ => plantKeys S depth c.1.1 c.2 c.1.2) := by
  let E1 := encPair (encPair encUnary encBits) encUnary
  let EK := encList (encPair encBits encBits)
  have hn : ComputableTidilyInPolyTime (fun c : (ℕ × List Bool) × ℕ => c.1.1) E1 encUnary :=
    (ComputableTidilyInPolyTime.fst _ _).fst'
  have hk : IsPPTOn E1 encBits (fun c : (ℕ × List Bool) × ℕ => BitString.sampleList c.1.1) :=
    ComputableInPolyTime.sampleList (.of_tidy hn)
  have hn2 := hn.comp (ComputableTidilyInPolyTime.fst E1 encBits)
  have hfront : IsPPTOn (encPair E1 encBits) EK
      (fun q : ((ℕ × List Bool) × ℕ) × List Bool =>
        OracleComp.replicate q.1.2 (S.keyGen q.1.1.1)) :=
    (S.isPPTOn_keyGen_comp (.of_tidy hn2)).replicate
      (.of_tidy (ComputableTidilyInPolyTime.fst E1 encBits).snd')
  have hn3 := hn2.comp (ComputableTidilyInPolyTime.fst (encPair E1 encBits) EK)
  have hback : IsPPTOn (encPair (encPair E1 encBits) EK) EK
      (fun q : (((ℕ × List Bool) × ℕ) × List Bool) × List (List Bool × List Bool) =>
        OracleComp.replicate (2 ^ depth q.1.1.1.1 - q.1.1.2 - 1) (S.keyGen q.1.1.1.1)) := by
    have hi : ComputableTidilyInPolyTime
        (fun q : (((ℕ × List Bool) × ℕ) × List Bool) × List (List Bool × List Bool) => q.1.1.2)
        (encPair (encPair E1 encBits) EK) encUnary :=
      (ComputableTidilyInPolyTime.fst _ _).fst'.snd'
    have hcount := ComputableTidilyInPolyTime.unary_sub.comp
      ((ComputableTidilyInPolyTime.unary_sub.comp ((hcap.tidy.comp hn3).prod hi)).prod
        (ComputableTidilyInPolyTime.const 1))
    exact (S.isPPTOn_keyGen_comp (.of_tidy hn3)).replicate (.of_tidy hcount)
  have hret : ComputableTidilyInPolyTime
      (fun r : ((((ℕ × List Bool) × ℕ) × List Bool) × List (List Bool × List Bool)) ×
          List (List Bool × List Bool) =>
        (r.1.1.2, r.1.2 ++ (r.1.1.1.1.2, []) :: r.2))
      (encPair (encPair (encPair E1 encBits) EK) EK) (encPair encBits EK) := by
    have hfst := ComputableTidilyInPolyTime.fst (encPair (encPair E1 encBits) EK) EK
    have hkr := hfst.fst'.snd'
    have hvk := hfst.fst'.fst'.fst'.snd'
    have hplanted :=
      hvk.prod (ComputableTidilyInPolyTime.const (encMid := encBits) ([] : List Bool))
    exact hkr.prod (ComputableTidilyInPolyTime.listAppend' hfst.snd'
      (ComputableTidilyInPolyTime.cons' hplanted (ComputableTidilyInPolyTime.snd _ _)))
  unfold plantKeys
  exact hk.bind_with (hfront.bind_with (hback.bind_with hret.isPPTOn))

/-- The encoding of the one-time forger's caller: the parameter, the challenge key, the leaf,
the hash key and the planted key list. -/
private abbrev encCaller :
    (((ℕ × List Bool) × ℕ) × (List Bool × List (List Bool × List Bool))) ↪ List Bool :=
  encPair (encPair (encPair encUnary encBits) encUnary)
    (encPair encBits (encList (encPair encBits encBits)))

/-- The encoding of the planted handler's input: the caller, the request and the indexed log. -/
private noncomputable abbrev encHandlerInput :
    ((((ℕ × List Bool) × ℕ) × (List Bool × List (List Bool × List Bool))) ×
      ((Unit × List Bool) × List (ℕ × List Bool))) ↪ List Bool :=
  encPair encCaller
    (encPair (encPair (encFinEnum Unit) encBits) (encList (encPair encUnary encBits)))

include hH hlen hcap in
private theorem isOraclePPTOn_plantedHandler {bound : ℕ → ℕ}
    (hboundPoly : ComputableInPolyTime bound encUnary encUnary) :
    IsOraclePPTOn encHandlerInput (encPair encBits (encList (encPair encUnary encBits)))
      (fun p : (((ℕ × List Bool) × ℕ) × (List Bool × List (List Bool × List Bool))) ×
          ((Unit × List Bool) × List (ℕ × List Bool)) =>
        plantedHandler S H depth p.1.1.1.1 p.1.2.1 p.1.2.2 p.1.1.2 (bound p.1.1.1.1) p.2.1
          p.2.2) := by
  have hc := ComputableTidilyInPolyTime.fst encCaller
    (encPair (encPair (encFinEnum Unit) encBits) (encList (encPair encUnary encBits)))
  have hrest := ComputableTidilyInPolyTime.snd encCaller
    (encPair (encPair (encFinEnum Unit) encBits) (encList (encPair encUnary encBits)))
  have hn := hc.fst'.fst'.fst'
  have hi := hc.fst'.snd'
  have hk := hc.snd'.fst'
  have hkeys := hc.snd'.snd'
  have hw := hrest.fst'.snd'
  have hsigned := hrest.snd'
  have hr := IndexedSignatureScheme.requestDecoder.computableInPolyTime.tidy.comp hw
  have hu := hr.fst'
  have hm := hr.snd'
  have hcapn := hcap.tidy.comp hn
  have hbn := hboundPoly.tidy.comp hn
  have hlog := ComputableTidilyInPolyTime.cons' hr hsigned
  have hvks := (ComputableTidilyInPolyTime.map
    (ComputableTidilyInPolyTime.fst encBits encBits)).comp hkeys
  have hdigest := hH.tidy.comp (hk.prod hm)
  -- the condition
  have hcond := ComputableTidilyInPolyTime.decide_and
    (ComputableTidilyInPolyTime.unary_lt' hu hcapn)
    (ComputableTidilyInPolyTime.decide_not (ComputableTidilyInPolyTime.decide_mem
      ((ComputableTidilyInPolyTime.map (ComputableTidilyInPolyTime.fst encUnary encBits)).comp
        hsigned) hu))
  have hcondi := ComputableTidilyInPolyTime.decide_eq' hu hi
  have hq := IsOraclePPTOn.query_take (input := encHandlerInput) () hdigest hbn
  have hvki :=
    ((ComputableTidilyInPolyTime.listGetD (encA := encPair encBits encBits) ([], [])).comp
      (hkeys.prod hi)).fst'
  have hpathi := (computableInPolyTime_merklePath hH hlen).tidy.comp (hk.prod (hvks.prod hi))
  have hfst := ComputableTidilyInPolyTime.fst encHandlerInput encBits
  have hqpost := ((ComputableTidilyInPolyTime.encode
    (encPair encBits (encPair encBits (encList encBits)))).comp
      ((hvki.comp hfst).prod ((ComputableTidilyInPolyTime.snd encHandlerInput encBits).prod
        (hpathi.comp hfst)))).prod (hlog.comp hfst)
  have hquery := hq.map_with
    (f := fun (p : (((ℕ × List Bool) × ℕ) × (List Bool × List (List Bool × List Bool))) ×
        ((Unit × List Bool) × List (ℕ × List Bool))) ots =>
      (encodeSignature (p.1.2.2.getD p.1.1.2 ([], [])).1 ots
        (merklePath H p.1.2.1 (p.1.2.2.map Prod.fst) p.1.1.2),
        IndexedSignatureScheme.requestDecoder.decode p.2.1.2 :: p.2.2)) hqpost
  have hkeyu :=
    (ComputableTidilyInPolyTime.listGetD (encA := encPair encBits encBits) ([], [])).comp
      (hkeys.prod hu)
  have hots := S.isPPTOn_sign_comp (.of_tidy hkeyu.snd') (.of_tidy hdigest)
  have hpathu := (computableInPolyTime_merklePath hH hlen).tidy.comp (hk.prod (hvks.prod hu))
  have hsignPost := (ComputableTidilyInPolyTime.encode
    (encPair encBits (encPair encBits (encList encBits)))).comp
      ((hkeyu.fst'.comp hfst).prod
        ((ComputableTidilyInPolyTime.snd encHandlerInput encBits).prod (hpathu.comp hfst)))
  have hsign := hots.bind_with
    (second := fun (p : (((ℕ × List Bool) × ℕ) × (List Bool × List (List Bool × List Bool))) ×
        ((Unit × List Bool) × List (ℕ × List Bool))) ots =>
      pure (encodeSignature
        (p.1.2.2.getD (IndexedSignatureScheme.requestDecoder.decode p.2.1.2).1 ([], [])).1 ots
        (merklePath H p.1.2.1 (p.1.2.2.map Prod.fst)
          (IndexedSignatureScheme.requestDecoder.decode p.2.1.2).1))) hsignPost.isPPTOn
  have hsample := (hsign.isOraclePPTOn (Operation := Unit)).map_with
    (f := fun (p : (((ℕ × List Bool) × ℕ) × (List Bool × List (List Bool × List Bool))) ×
        ((Unit × List Bool) × List (ℕ × List Bool))) sig =>
      (sig, IndexedSignatureScheme.requestDecoder.decode p.2.1.2 :: p.2.2))
    ((ComputableTidilyInPolyTime.snd encHandlerInput encBits).prod (hlog.comp hfst))
  have hpure := ((ComputableTidilyInPolyTime.const (encMid := encBits) ([] : List Bool)).prod
    hsigned).isOraclePPTOn (Operation := Unit)
  unfold plantedHandler signWith
  exact IsOraclePPTOn.ite hcond (IsOraclePPTOn.ite hcondi hquery hsample) hpure

/-- A per-request size bound for the planted handler's reply and added log entry. -/
private def handlerBound (cs ds : ℕ) (bound : ℕ → ℕ)
    (c : ((ℕ × List Bool) × ℕ) × (List Bool × List (List Bool × List Bool)))
    (w : List Bool) : ℕ :=
  2 * bound c.1.1.1 + 2 * (cs * (3 * (encCaller c).length + 2) ^ ds) +
    2 * ((2 * (encCaller c).length + 1) * (2 * (encCaller c).length + 1)) +
      4 * (encCaller c).length + 6 * w.length + 8

private theorem computableTidilyInPolyTime_handlerBound
    {α β γ : Type} {enc : ((ℕ × α) × β) × γ ↪ List Bool}
    (cs ds : ℕ) {bound : ℕ → ℕ}
    (hbound : ComputableTidilyInPolyTime (fun c : ((ℕ × α) × β) × γ => bound c.1.1.1)
      enc encUnary) :
    ComputableTidilyInPolyTime
      (fun pair : (((ℕ × α) × β) × γ) × List Bool =>
        2 * bound pair.1.1.1.1 + 2 * (cs * (3 * (enc pair.1).length + 2) ^ ds) +
          2 * ((2 * (enc pair.1).length + 1) * (2 * (enc pair.1).length + 1)) +
            4 * (enc pair.1).length + 6 * pair.2.length + 8)
      (encPair enc encBits) encUnary := by
  have hfst := ComputableTidilyInPolyTime.fst enc encBits
  have hL := hfst.encoded.trans (ComputableTidilyInPolyTime.length encBool)
  have hW := (ComputableTidilyInPolyTime.snd enc encBits).trans
    (ComputableTidilyInPolyTime.length encBool)
  have hb := hfst.trans hbound
  have add {f g} (hf : ComputableTidilyInPolyTime f (encPair enc encBits) encUnary)
      (hg : ComputableTidilyInPolyTime g (encPair enc encBits) encUnary) :
      ComputableTidilyInPolyTime (fun x => f x + g x) (encPair enc encBits) encUnary :=
    ComputableTidilyInPolyTime.unary_add.comp (hf.prod hg)
  have mul {f g} (hf : ComputableTidilyInPolyTime f (encPair enc encBits) encUnary)
      (hg : ComputableTidilyInPolyTime g (encPair enc encBits) encUnary) :
      ComputableTidilyInPolyTime (fun x => f x * g x) (encPair enc encBits) encUnary :=
    ComputableTidilyInPolyTime.unary_mul.comp (hf.prod hg)
  have pow (d : ℕ) {f} (hf : ComputableTidilyInPolyTime f (encPair enc encBits) encUnary) :
      ComputableTidilyInPolyTime (fun x => f x ^ d) (encPair enc encBits) encUnary :=
    (ComputableTidilyInPolyTime.unary_pow d).comp hf
  have cst (k : ℕ) : ComputableTidilyInPolyTime (fun _ => k) (encPair enc encBits) encUnary :=
    ComputableTidilyInPolyTime.const k
  have h2L1 := add (mul (cst 2) hL) (cst 1)
  exact add (add (add (add (add (mul (cst 2) hb)
    (mul (cst 2) (mul (cst cs) (pow ds (add (mul (cst 3) hL) (cst 2))))))
    (mul (cst 2) (mul h2L1 h2L1))) (mul (cst 4) hL)) (mul (cst 6) hW)) (cst 8)

private theorem length_encList_merklePath_le (hlen : ∀ k m, (H k m).length = k.length)
    {k : List Bool} {vks : List (List Bool)} {u L : ℕ} (hk : k.length ≤ L)
    (hvks : vks.length ≤ L) :
    (encList encBits (merklePath H k vks u)).length ≤ (2 * L + 1) * (2 * L + 1) := by
  refine (length_encList_le encBits _ (b := L) fun x hx =>
    (length_le_of_mem_merklePath hlen hx).trans hk).trans ?_
  rw [length_merklePath]
  have hclog : Nat.clog 2 vks.length ≤ vks.length :=
    Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  exact Nat.mul_le_mul_right _ (by omega)

private theorem plantedHandler_bound (hlen : ∀ k m, (H k m).length = k.length)
    {bound : ℕ → ℕ} {cs ds : ℕ}
    (hsignLen : ∀ a : List Bool × List Bool, ∀ result ∈ (ProbComp.eval (S.sign a.1 a.2)).support,
      (encBits result).length ≤ cs * ((encPair encBits encBits a).length + 1) ^ ds)
    (c : ((ℕ × List Bool) × ℕ) × (List Bool × List (List Bool × List Bool)))
    (request : Unit × List Bool) (signed : List (ℕ × List Bool))
    (result : List Bool × List (ℕ × List Bool))
    (hres : result ∈ OracleComp.support
      (plantedHandler S H depth c.1.1.1 c.2.1 c.2.2 c.1.2 (bound c.1.1.1) request signed)) :
    result.1.length ≤ handlerBound cs ds bound c request.2 ∧
      (encList (encPair encUnary encBits) result.2).length ≤
        (encList (encPair encUnary encBits) signed).length +
          handlerBound cs ds bound c request.2 := by
  obtain ⟨⟨⟨n, vk⟩, i⟩, k, keys⟩ := c
  obtain ⟨⟨⟩, w⟩ := request
  unfold handlerBound
  have hkL : k.length ≤ (encCaller (((n, vk), i), k, keys)).length := by
    simp only [encCaller, encPair_apply, encBits_apply, List.length_append, length_frame]
    omega
  have hkeysL : (encList (encPair encBits encBits) keys).length ≤
      (encCaller (((n, vk), i), k, keys)).length := by
    simp only [encCaller, encPair_apply, encBits_apply, List.length_append, length_frame]
    omega
  generalize (encCaller (((n, vk), i), k, keys)).length = L at hkL hkeysL ⊢
  have hkeyLen : ∀ u, (keys.getD u ([], [])).1.length ≤ L ∧
      (keys.getD u ([], [])).2.length ≤ L := by
    intro u
    rw [List.getD_eq_getElem?_getD]
    cases hget : keys[u]? with
    | none => simp
    | some e =>
      have hmem := length_le_encList_of_mem (encPair encBits encBits) (List.mem_of_getElem? hget)
      simp only [encPair_apply, encBits_apply, List.length_append, length_frame] at hmem
      simp only [Option.getD_some]
      constructor <;> omega
  have hvks : (keys.map Prod.fst).length ≤ L := by
    rw [List.length_map]
    exact (length_le_length_encList _ keys).trans hkeysL
  have hpath (u : ℕ) := length_encList_merklePath_le (u := u) hlen hkL hvks
  have hu := length_unframe_le w
  have hm := length_dropFrame_le w
  have hdecode :
      IndexedSignatureScheme.requestDecoder.decode w = ((unframe w).length, dropFrame w) := rfl
  have hpair (u : ℕ) (ots : List Bool) (hots : ots.length ≤ bound n + cs * (3 * L + 2) ^ ds) :
      (encodeSignature (keys.getD u ([], [])).1 ots
        (merklePath H k (keys.map Prod.fst) u)).length ≤
          2 * bound n + 2 * (cs * (3 * L + 2) ^ ds) + 2 * ((2 * L + 1) * (2 * L + 1)) +
            4 * L + 6 * w.length + 8 ∧
        (encList (encPair encUnary encBits)
          (IndexedSignatureScheme.requestDecoder.decode w :: signed)).length ≤
          (encList (encPair encUnary encBits) signed).length +
            (2 * bound n + 2 * (cs * (3 * L + 2) ^ ds) + 2 * ((2 * L + 1) * (2 * L + 1)) +
              4 * L + 6 * w.length + 8) := by
    have hvk := (hkeyLen u).1
    have hp := hpath u
    refine ⟨?_, ?_⟩
    · simp only [encodeSignature, encPair_apply, encBits_apply, List.length_append, length_frame]
      omega
    · simp only [hdecode, encList_cons, encPair_apply, encUnary_apply,
        encBits_apply, List.length_append, length_frame, List.length_replicate]
      omega
  unfold plantedHandler at hres
  dsimp only at hres
  split_ifs at hres with hguard hi
  · obtain ⟨ots, hots, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hres
    obtain ⟨raw, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hots
    exact hpair i _ ((List.length_take_le (bound n) raw).trans (Nat.le_add_right _ _))
  · obtain ⟨sig, hsig, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hres
    simp only [ProbOracleComp.support_sample, signWith, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hsig
    obtain ⟨ots, hots, rfl⟩ := hsig
    have hotsLen := hsignLen (_, _) ots hots
    simp only [encBits_apply, encPair_apply, List.length_append, length_frame, hlen] at hotsLen
    set u := (IndexedSignatureScheme.requestDecoder.decode w).1
    have hvk := (hkeyLen u).2
    have hpow : cs * (2 * (keys.getD u ([], [])).2.length + 1 + k.length + 1) ^ ds ≤
        cs * (3 * L + 2) ^ ds := Nat.mul_le_mul_left cs (Nat.pow_le_pow_left (by omega) ds)
    exact hpair u ots ((hotsLen.trans hpow).trans (Nat.le_add_left _ _))
  · have h := OracleComp.eq_of_mem_supportWith_pure hres
    subst h
    exact ⟨by simp, Nat.le_add_right _ _⟩

include hH hlen hcap in
/-- The one-time forger is uniformly strict oracle PPT for every oracle-PPT indexed forger and
every polynomial-time truncation bound. -/
theorem isOraclePPT_oneTimeForger {bound : ℕ → ℕ}
    (hboundPoly : ComputableInPolyTime bound encUnary encUnary) {adversary : IndexedForger}
    (hadversary : IsOraclePPT (encPair encUnary (encPair encBits encBits)) adversary) :
    IsOraclePPT (encPair encBits encBits) (oneTimeForger S H depth bound adversary) := by
  obtain ⟨cs, ds, hsignLen⟩ := S.sign_ppt.length_le
  have hleaf : IsOraclePPTOn (Operation := Unit) (encPair encUnary encBits) encUnary
      (fun p : ℕ × List Bool => ProbOracleComp.sample (leafIndex depth p.1)) :=
    ((isPPTOn_leafIndex hcap).preprocess (ComputableInPolyTime.fst _ _)).isOraclePPTOn
  have hsetup : IsOraclePPTOn (Operation := Unit) (encPair (encPair encUnary encBits) encUnary)
      (encPair encBits (encList (encPair encBits encBits)))
      (fun c : (ℕ × List Bool) × ℕ => ProbOracleComp.sample (plantKeys S depth c.1.1 c.2 c.1.2)) :=
    (isPPTOn_plantKeys hcap).isOraclePPTOn
  have hfst := ComputableTidilyInPolyTime.fst
    (encPair (encPair encUnary encBits) encUnary)
    (encPair encBits (encList (encPair encBits encBits)))
  have hprep : ComputableTidilyInPolyTime
      (fun c : ((ℕ × List Bool) × ℕ) × (List Bool × List (List Bool × List Bool)) =>
        (c.1.1.1, publicKey H c.2.1 c.2.2)) encCaller (encPair encUnary encBits) :=
    hfst.fst'.fst'.prod ((ComputableTidilyInPolyTime.snd
      (encPair (encPair encUnary encBits) encUnary)
      (encPair encBits (encList (encPair encBits encBits)))).trans
        (computableInPolyTime_publicKey hH hlen).tidy)
  have hres := computableTidilyInPolyTime_handlerBound cs ds (hfst.fst'.fst'.trans hboundPoly.tidy)
  have hrun :=
    hadversary.run_interpret_preprocess_open
      (prepare := fun c => (c.1.1.1, publicKey H c.2.1 c.2.2))
      (initial := fun _ => ([] : List (ℕ × List Bool)))
      (resources := fun c w => handlerBound cs ds bound c w)
      hprep (isOraclePPTOn_plantedHandler hH hlen hcap hboundPoly) (.const [])
      (fun _ _ => True) (fun _ => trivial) hres
      (fun c request state _ result hresult =>
        ⟨trivial, plantedHandler_bound hlen hsignLen c request state result hresult⟩)
  let EO := encPair (encPair encUnary (encPair encBits encBits))
    (encList (encPair encUnary encBits))
  have hk := (ComputableTidilyInPolyTime.fst encCaller EO).snd'.fst'
  have hms := (ComputableTidilyInPolyTime.snd encCaller EO).fst'.snd'
  have hfinal := ((hk.prod hms.fst').trans hH.tidy).prod
    (hms.snd'.trans signatureDecoder.computableInPolyTime.tidy).snd'.fst'
  unfold oneTimeForger oneTimeForgerAt
  exact hleaf.bind_with
    (hsetup.bind_with (hrun.bind_with (hfinal.isOraclePPTOn (Operation := Unit))))

end Efficiency

/-! ### Security -/

/-- **Merkle signatures are secure** ([Merkle1989], Section 6; [BonehShoup2023],
Section 14.6.1): if `S` is one-time EUF-CMA secure and `H` is collision resistant, then
`MerkleSignature.scheme S H depth` is an indexed EUF-CMA secure signature scheme of capacity
`2 ^ depth n`. The reductions are `oneTimeForger`, with loss `2 ^ depth n`, and `collisionFinder`,
with loss `1` (`succProbability_indexedEufCmaGame_le`). -/
theorem _root_.Cslib.Crypto.SignatureScheme.OneTimeEUFCMA.indexedEUFCMA_merkle
    {S : SignatureScheme} (hS : S.OneTimeEUFCMA) {H : List Bool → List Bool → List Bool}
    (hcr : CollisionResistant H)
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k m, (H k m).length = k.length) {depth : ℕ → ℕ}
    (hcap : ComputableInPolyTime (fun n => 2 ^ depth n) encUnary encUnary) :
    (scheme S H depth hH hlen hcap).IndexedEUFCMA := by
  obtain ⟨ck, dk, hlenk⟩ := S.keyGen_ppt.length_le
  obtain ⟨cs, ds, hlens⟩ := S.sign_ppt.length_le
  let bound (n : ℕ) : ℕ := cs * (2 * (ck * (n + 1) ^ dk) + n + 2) ^ ds
  have hboundPoly : ComputableInPolyTime bound encUnary encUnary := by
    let hn := ComputableInPolyTime.id' (encIn := encUnary)
    let cst (k : ℕ) := ComputableInPolyTime.const (encIn := encUnary) (encOut := encUnary) k
    exact ComputableInPolyTime.unary_mul' (cst cs)
      ((ComputableInPolyTime.unary_pow ds).comp
        (ComputableInPolyTime.unary_add'
          (ComputableInPolyTime.unary_add'
            (ComputableInPolyTime.unary_mul' (cst 2)
              (ComputableInPolyTime.unary_mul' (cst ck)
                ((ComputableInPolyTime.unary_pow dk).comp
                  (ComputableInPolyTime.unary_add' hn (cst 1)))))
            hn)
          (cst 2)))
  have hbound (n : ℕ) : ∀ x ∈ (ProbComp.eval (S.keyGen n)).support, ∀ msg, msg.length = n →
      ∀ σ ∈ (ProbComp.eval (S.sign x.2 msg)).support, σ.length ≤ bound n := by
    intro x hx msg hmsg σ hσ
    have hkeyLen := hlenk n x hx
    simp only [encUnary_apply, List.length_replicate, length_encPair, encBits_apply] at hkeyLen
    have hσLen := hlens (x.2, msg) σ hσ
    simp only [length_encPair, encBits_apply] at hσLen
    refine hσLen.trans (Nat.mul_le_mul_left cs (Nat.pow_le_pow_left ?_ ds))
    omega
  apply IndexedSignatureScheme.IndexedEUFCMA.of_negligible
  intro adversary hadversary
  have hB := hS.negligible (oneTimeForger S H depth bound adversary)
    (isOraclePPT_oneTimeForger hH hlen hcap hboundPoly hadversary)
  have hC := hcr.negligible (collisionFinder S H depth hH hlen hcap adversary)
    (isPPT_collisionFinder hH hlen hcap hadversary)
  have hN : PolynomiallyBounded (fun n => 2 ^ depth n) := hcap.tidy.polynomiallyBounded
  refine negligible_of_le ((hB.polynomiallyBounded_mul hN).add hC) fun n => ?_
  have h := succProbability_indexedEufCmaGame_le hH hlen hcap (hbound n) adversary
  simpa only [Nat.cast_pow, Nat.cast_ofNat, Pi.add_apply] using h

/-- **Indexed signatures from one-way functions and collision-resistant hashing**: Lamport's
one-time scheme on any one-way function, under Merkle's tree with any collision-resistant hash
family, gives an indexed EUF-CMA secure signature scheme of every polynomial capacity
`2 ^ depth n`. -/
theorem _root_.Cslib.Crypto.OneWay.exists_indexedEUFCMA {f : List Bool → List Bool}
    (hf : OneWay f) {H : List Bool → List Bool → List Bool} (hH : HashFamily H)
    {depth : ℕ → ℕ} (hcap : ComputableInPolyTime (fun n => 2 ^ depth n) encUnary encUnary) :
    ∃ S : IndexedSignatureScheme, (∀ n, S.capacity n = 2 ^ depth n) ∧ S.IndexedEUFCMA := by
  obtain ⟨S, hS⟩ := hf.exists_oneTimeSignature
  exact ⟨scheme S H depth hH.polyTime hH.length_eq hcap, fun _ => rfl,
    hS.indexedEUFCMA_merkle hH.collisionResistant hH.polyTime hH.length_eq hcap⟩

/-- **Counter-stateful many-time signatures from one-way functions and collision-resistant
hashing** ([Merkle1989], Sections 6–7): a one-way function and a hash family give a counter
EUF-CMA secure indexed scheme of every polynomial capacity `2 ^ depth n`; the witness is Merkle's
tree signature over Lamport's one-time scheme, with the signer choosing the leaves by a counter. -/
theorem _root_.Cslib.Crypto.OneWay.exists_counterEUFCMA {f : List Bool → List Bool}
    (hf : OneWay f) {H : List Bool → List Bool → List Bool} (hH : HashFamily H)
    {depth : ℕ → ℕ} (hcap : ComputableInPolyTime (fun n => 2 ^ depth n) encUnary encUnary) :
    ∃ S : IndexedSignatureScheme, (∀ n, S.capacity n = 2 ^ depth n) ∧ S.CounterEUFCMA :=
  let ⟨S, hcapS, hS⟩ := hf.exists_indexedEUFCMA hH hcap
  ⟨S, hcapS, hS.counterEUFCMA⟩

end MerkleSignature

end Cslib.Crypto
