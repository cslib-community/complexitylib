/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.PCP.NP
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Crypto.Computational.MerkleTree.Binding
public import CslibFrontier.Languages.Probabilistic.Repeat
public import CslibFrontier.Computability.Probabilistic.Repeat
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.PolyTime

/-!
# Kilian's protocol: committing to a PCP proof with a Merkle tree

Kilian's argument system ([Kilian1992]; [BarakGoldreich2001], Construction 3.4) lets a prover
convince a verifier that `x ∈ L` while sending only a hash-tree root and a few openings of a PCP
proof. For a PCP verifier `V` with logarithmic randomness and a keyed hash `H`, at security
parameter `n`:

1. the verifier sends a uniform `n`-bit hash key `k`;
2. the prover sends the statement `x` and the Merkle root `root` of its proof table;
3. the verifier sends `n` independent PCP random strings `ρs`, each of `V.coins x` bits;
4. for each random string `ρ` the prover sends one opening per query of `V` on `(x, ρ)`: the bit at
   that position of the table and its authentication path;
5. the verifier accepts when every opening is accepted by `merkleVerify` and `V` accepts every
   repetition on the opened bits (`kilianVerify`).

**Positions.** PCP addresses are binary numbers that may be exponentially large, so the committed
object is not the PCP proof itself but its *compact table*: the bits at the addresses of
`V.queryTable x`, the list of all addresses queried on all random strings, as in
`PCPVerifier.tableVerifier`. Address `a` is stored at position `(V.queryTable x).idxOf a`, its first
occurrence, and the tree has depth `Nat.clog 2 (V.queryTable x).length` (`kilianDepth`). The
verifier computes positions itself, so a prover cannot choose them. With logarithmic randomness the
table has polynomially many entries.

**The honest prover** (`kilianTable`, `kilianCommit`, `kilianRespond`) takes a table accepted by
`V.tableVerifier` as its witness, normalizes it to the length of `V.queryTable x`, commits to its
bits as one-bit leaves `[b]`, and opens the queried positions with `merklePath`. Every repetition
then passes (`kilianVerify_kilianRespond`), so the honest execution (`kilianHonestGame`) accepts
with probability one (`eval_kilianHonestGame`): perfect completeness. The tables accepted by
`V.tableVerifier` are exactly the witnesses of `PCP_log_subset_NP`, so for a PCP verifier for `L`
this is the NP relation of `L` on which the prover is efficient.

**Efficiency.** The verifier's decision (`computableInPolyTime_kilianVerify`) and the honest
prover's two messages (`computableInPolyTime_kilianCommit`, `computableInPolyTime_kilianRespond`)
have plain polynomial-time certificates, and sampling the verifier's challenges is strict PPT
(`isPPTOn_kilianChallenges`), for a polynomial-time `V` with `O(log n)` random bits and a
polynomial-time `H` with `n`-bit digests.

Computational soundness, against cheating provers that choose `x` after seeing the key, is in
`CslibFrontier.Crypto.Computational.Kilian.Soundness`, and the arguments for NP in
`CslibFrontier.Crypto.Computational.Kilian.NP`.

**Differences from [BarakGoldreich2001], Construction 3.4.** The tree is the one of
`CslibFrontier.Crypto.Computational.MerkleTree` (hashed leaves, `encPair` pairing, sibling-only
openings), not Barak and Goldreich's tree over raw proof bits (see the module documentation of
`CslibFrontier.Crypto.Computational.MerkleTree.Binding`). The prover commits to a compact table of
polynomial length, which suffices for NP, rather than to an oracle of superpolynomial length.
Repetition is explicit (`n` parallel PCP runs). The hash key is uniform and hashing resists uniform
adversaries, as in `CollisionResistant`.

## Main definitions

* `Cslib.Crypto.KilianResponse`: the prover's answers, one `MerkleOpening Bool` per query.
* `Cslib.Crypto.kilianDepth`, `Cslib.Crypto.kilianPosition`: depth of the committed tree and the
  position of a PCP address.
* `Cslib.Crypto.kilianCheck`, `Cslib.Crypto.kilianVerify`: the verifier's decision on one
  repetition and on all of them.
* `Cslib.Crypto.kilianChallenges`: the verifier's challenge sampler.
* `Cslib.Crypto.kilianLeaves`, `Cslib.Crypto.kilianTable`, `Cslib.Crypto.kilianCommit`,
  `Cslib.Crypto.kilianOpen`, `Cslib.Crypto.kilianRespond`: the honest prover.
* `Cslib.Crypto.kilianHonestGame`: the honest execution.

## Main results

* `Cslib.Crypto.kilianVerify_kilianRespond`, `Cslib.Crypto.eval_kilianHonestGame`: perfect
  completeness for tables accepted by `PCPVerifier.tableVerifier`.
* `Cslib.Crypto.computableInPolyTime_kilianVerify`, `Cslib.Crypto.isPPTOn_kilianChallenges`: the
  verifier is efficient.
* `Cslib.Crypto.computableInPolyTime_kilianCommit`,
  `Cslib.Crypto.computableInPolyTime_kilianRespond`: the honest prover is efficient.

## References

* [J. Kilian, *A note on efficient zero-knowledge proofs and arguments*][Kilian1992]
* [B. Barak, O. Goldreich, *Universal Arguments and their Applications*][BarakGoldreich2001],
  Construction 3.4.
-/

@[expose] public section

namespace Cslib.Crypto

open Complexity Probability Turing.MultiTapeTM

variable {α : Type} (H : List Bool → List Bool → List Bool) (V : PCPVerifier α)

/-! ### The verifier -/

/-- The prover's last message: for each repetition, one opening per query of the PCP verifier, each
the claimed bit of the table and its authentication path. -/
abbrev KilianResponse := List (List (MerkleOpening Bool))

/-- The depth of the tree committing to the compact table of `x`. -/
def kilianDepth (x : α) : ℕ := Nat.clog 2 (V.queryTable x).length

/-- The position of the PCP address `a` in the compact table of `x`: its first occurrence in
`V.queryTable x`. -/
def kilianPosition (x : α) (a : ℕ) : ℕ := (V.queryTable x).idxOf a

/-- The verifier's decision on one repetition with random string `ρ`: one opening per query of `V`
on `(x, ρ)`, each accepted (`MerkleOpening.verify`, one-bit leaves) at the position of its address,
and `V` accepts the opened bits. -/
def kilianCheck (k : List Bool) (x : α) (root ρ : List Bool)
    (answers : List (MerkleOpening Bool)) : Bool :=
  answers.length == (V.queries (x, ρ)).length &&
    ((V.queries (x, ρ)).zip answers).all (fun (a, o) =>
      o.verify H k (fun b => [b]) (kilianDepth V x) root (kilianPosition V x a)) &&
    V.verdict ((x, ρ), answers.map MerkleOpening.leaf)

/-- The verifier's decision: one answer list per random string, each accepted by `kilianCheck`. -/
def kilianVerify (k : List Bool) (x : α) (root : List Bool) (ρs : List (List Bool))
    (response : KilianResponse) : Bool :=
  response.length == ρs.length &&
    (ρs.zip response).all fun (ρ, answers) => kilianCheck H V k x root ρ answers

/-- The verifier's challenge at security parameter `n` on statement `x`: `n` independent uniform
random strings of `V.coins x` bits. -/
noncomputable def kilianChallenges (n : ℕ) (x : α) : ProbComp (List (List Bool)) :=
  OracleComp.replicate n (BitString.sampleList (V.coins x))

/-! ### The honest prover -/

/-- The leaves committing to a table of bits: each bit as a one-bit leaf. -/
def kilianLeaves (table : List Bool) : List (List Bool) := table.map fun b => [b]

/-- The honest prover's table: a candidate table normalized to the length of `V.queryTable x`,
missing entries read as `false`, as `PCPVerifier.tableVerifier` reads them. -/
def kilianTable (x : α) (table : List Bool) : List Bool :=
  (List.range (V.queryTable x).length).map fun i => table.getD i false

/-- The honest prover's commitment: the Merkle root of its normalized table. -/
def kilianCommit (k : List Bool) (x : α) (table : List Bool) : List Bool :=
  merkleRoot H k (kilianLeaves (kilianTable V x table))

/-- The honest prover's openings for the random string `ρ`: for each query of `V`, the bit of the
normalized table at its position and the authentication path. -/
def kilianOpen (k : List Bool) (x : α) (table ρ : List Bool) : List (MerkleOpening Bool) :=
  (V.queries (x, ρ)).map fun a =>
    ⟨(kilianTable V x table).getD (kilianPosition V x a) false,
      merklePath H k (kilianLeaves (kilianTable V x table)) (kilianPosition V x a)⟩

/-- The honest prover's last message: its openings for each random string. -/
def kilianRespond (k : List Bool) (x : α) (table : List Bool) (ρs : List (List Bool)) :
    KilianResponse :=
  ρs.map (kilianOpen H V k x table)

/-- The honest execution at security parameter `n` on statement `x` with witness table `table`:
the verifier samples a key, the prover commits, the verifier samples challenges, the prover
answers, and the verifier decides. -/
noncomputable def kilianHonestGame (x : α) (table : List Bool) (n : ℕ) : ProbComp Bool := do
  let k ← BitString.sampleList n
  let ρs ← kilianChallenges V n x
  return kilianVerify H V k x (kilianCommit H V k x table) ρs (kilianRespond H V k x table ρs)

/-! ### Completeness -/

variable {H V}

/-- Every address queried on a random string of the right length has a position inside the
compact table. -/
theorem kilianPosition_lt {x : α} {ρ : List Bool} {a : ℕ} (hρ : ρ.length = V.coins x)
    (ha : a ∈ V.queries (x, ρ)) : kilianPosition V x a < (V.queryTable x).length :=
  List.idxOf_lt_length_of_mem (V.mem_queryTable hρ ha)

/-- The normalized table has one entry per address of the address table. -/
@[simp]
theorem length_kilianTable (x : α) (table : List Bool) :
    (kilianTable V x table).length = (V.queryTable x).length := by
  simp [kilianTable]

/-- Below the length of the address table, the normalized table agrees with the candidate. -/
theorem getD_kilianTable {x : α} {table : List Bool} {i : ℕ}
    (hi : i < (V.queryTable x).length) :
    (kilianTable V x table).getD i false = table.getD i false := by
  simp [kilianTable, hi]

/-- **Honest openings pass**: for a table accepted by `V.tableVerifier`, the honest openings for
a random string of the right length pass `kilianCheck`. -/
theorem kilianCheck_kilianOpen {x : α} {table : List Bool}
    (htable : V.tableVerifier (x, table) = true) (k : List Bool) {ρ : List Bool}
    (hρ : ρ.length = V.coins x) :
    kilianCheck H V k x (kilianCommit H V k x table) ρ (kilianOpen H V k x table ρ) = true := by
  have hverdict := List.all_eq_true.mp htable ρ (BitString.mem_enumList.mpr hρ)
  have hzip (g : ℕ → MerkleOpening Bool) : (V.queries (x, ρ)).zip ((V.queries (x, ρ)).map g) =
      (V.queries (x, ρ)).map fun a => (a, g a) := by
    simpa only [List.map_id, id] using List.zip_map' (f := id) (g := g) (l := V.queries (x, ρ))
  simp only [kilianCheck, MerkleOpening.verify, kilianOpen, hzip, Bool.and_eq_true, beq_iff_eq,
    List.length_map, List.all_map, List.all_eq_true, Function.comp_def, List.map_map, true_and]
  refine ⟨fun a ha => ?_, ?_⟩
  · have hpos := kilianPosition_lt hρ ha
    have hleaf : (kilianLeaves (kilianTable V x table)).getD (kilianPosition V x a) [] =
        [(kilianTable V x table).getD (kilianPosition V x a) false] := by
      simp [kilianLeaves, hpos]
    rw [kilianCommit, ← hleaf]
    exact merkleVerify_merklePath_of_clog_eq (by simp [kilianLeaves, kilianDepth])
      (hpos.trans_le (Nat.le_pow_clog (by norm_num) _))
  · convert hverdict using 3
    refine List.map_congr_left fun a ha => ?_
    exact getD_kilianTable (kilianPosition_lt hρ ha)

/-- **Honest responses are accepted**: for a table accepted by `V.tableVerifier`, the honest
prover's commitment and openings are accepted on every list of random strings of the right length.
-/
theorem kilianVerify_kilianRespond {x : α} {table : List Bool}
    (htable : V.tableVerifier (x, table) = true) (k : List Bool) {ρs : List (List Bool)}
    (hρs : ∀ ρ ∈ ρs, ρ.length = V.coins x) :
    kilianVerify H V k x (kilianCommit H V k x table) ρs (kilianRespond H V k x table ρs) =
      true := by
  have hzip : ρs.zip (ρs.map (kilianOpen H V k x table)) =
      ρs.map fun ρ => (ρ, kilianOpen H V k x table ρ) := by
    simpa only [List.map_id, id] using
      List.zip_map' (f := id) (g := kilianOpen H V k x table) (l := ρs)
  simp only [kilianVerify, kilianRespond, hzip, List.length_map, beq_self_eq_true,
    Bool.true_and, List.all_map, List.all_eq_true, Function.comp_def]
  exact fun ρ hρ => kilianCheck_kilianOpen htable k (hρs ρ hρ)

variable (H V) in
/-- **Perfect completeness of Kilian's protocol**: on a statement `x` with a table accepted by
`V.tableVerifier`, the honest execution accepts with probability one, at every security
parameter. -/
theorem eval_kilianHonestGame {x : α} {table : List Bool}
    (htable : V.tableVerifier (x, table) = true) (n : ℕ) :
    ProbComp.eval (kilianHonestGame H V x table n) = PMF.pure true := by
  simp only [kilianHonestGame, ProbComp.eval_bind, ProbComp.eval_pure]
  conv_rhs => rw [← PMF.bind_const (ProbComp.eval (BitString.sampleList n)) (PMF.pure true),
    ← PMF.bind_const (ProbComp.eval (kilianChallenges V n x)) (PMF.pure true)]
  refine congrArg _ (funext fun k => Probability.PMF.bind_congr_on_support _ _ _ fun ρs hρs => ?_)
  rw [kilianVerify_kilianRespond htable k fun ρ hρ => ?_]
  rw [kilianChallenges, ProbComp.mem_support_replicate_iff] at hρs
  exact BitString.length_of_mem_support_uniformList (by simpa using hρs.2 ρ hρ)

/-! ### Efficiency -/

/-- The encoding of an opening of a bit: the bit, then the authentication path. -/
enc_structure encKilianOpening : MerkleOpening Bool where
  leaf : encBool, path : (encList encBits)

attribute [fun_prop] encKilianOpening_leaf_polyTime encKilianOpening_path_polyTime
  encKilianOpening_mk_polyTime

/-- The encoding of the prover's last message. -/
abbrev encKilianResponse : KilianResponse ↪ List Bool := encList (encList encKilianOpening)

/-- The encoding of the triple `(k, x, w)` that Kilian's verifier and honest prover start from:
the hash key `k` as a bit word, the statement `x` encoded by `enc`, and a bit word `w`, which is
the committed root for the verifier and the witness table for the honest prover. The key and the
statement are framed; `w` is not. -/
abbrev encKilianInput (enc : α ↪ List Bool) : List Bool × α × List Bool ↪ List Bool :=
  encPair encBits (encPair enc encBits)

section Efficiency

variable {enc : α ↪ List Bool} {c : ℕ} {γ : Type} {encIn : γ ↪ List Bool}

private theorem computableInPolyTime_kilianCheck
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k x, (H k x).length = k.length) (hV : V.PolyTime enc)
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1))
    {k : γ → List Bool} {x : γ → α} {root ρ : γ → List Bool}
    {answers : γ → List (MerkleOpening Bool)}
    (hk : ComputableInPolyTime k encIn encBits)
    (hx : ComputableInPolyTime x encIn enc)
    (hroot : ComputableInPolyTime root encIn encBits)
    (hρ : ComputableInPolyTime ρ encIn encBits)
    (hanswers : ComputableInPolyTime answers encIn (encList encKilianOpening)) :
    ComputableInPolyTime (fun g => kilianCheck H V (k g) (x g) (root g) (ρ g) (answers g))
      encIn encBool := by
  have htable := (PCPVerifier.isPolyTime_queryTable hV hcoins).comp hx
  have hqueries := hV.2.1.comp (hx.prod hρ)
  have hdepth : ComputableInPolyTime (fun g => kilianDepth V (x g)) encIn encUnary :=
    (ComputableInPolyTime.unary_clog_const 2).comp
      ((ComputableInPolyTime.length_list encNat).comp htable)
  have hfst := ComputableInPolyTime.fst encIn (encPair encNat encKilianOpening)
  have hsnd := ComputableInPolyTime.snd encIn (encPair encNat encKilianOpening)
  have ha := (ComputableInPolyTime.fst encNat encKilianOpening).comp hsnd
  have hopening := (ComputableInPolyTime.snd encNat encKilianOpening).comp hsnd
  have hb := encKilianOpening_leaf_polyTime hopening
  have hpath := encKilianOpening_path_polyTime hopening
  have hpos : ComputableInPolyTime
      (fun p : γ × ℕ × MerkleOpening Bool => kilianPosition V (x p.1) p.2.1)
      (encPair encIn (encPair encNat encKilianOpening)) encUnary :=
    ComputableInPolyTime.idxOfWithInput (htable.comp hfst) ha
  have hleaf : ComputableInPolyTime (fun p : γ × ℕ × MerkleOpening Bool => [p.2.2.leaf])
      (encPair encIn (encPair encNat encKilianOpening)) encBits :=
    ComputableInPolyTime.bitsCons hb (ComputableInPolyTime.const [])
  have hverify := (computableInPolyTime_merkleVerify hH hlen).comp
    (((hk.comp hfst).prod (hdepth.comp hfst)).prod (((hroot.comp hfst).prod hpos).prod
      (hleaf.prod hpath)))
  have hall : ComputableInPolyTime
      (fun g => ((V.queries (x g, ρ g)).zip (answers g)).all (fun (a, o) =>
        o.verify H (k g) (fun b => [b]) (kilianDepth V (x g)) (root g)
          (kilianPosition V (x g) a)))
      encIn encBool :=
    ComputableInPolyTime.allWithInput
      ((ComputableInPolyTime.zip encNat encKilianOpening).comp (hqueries.prod hanswers))
      hverify
  have hlength : ComputableInPolyTime
      (fun g => (answers g).length == (V.queries (x g, ρ g)).length) encIn encBool :=
    ComputableInPolyTime.beq
      ((ComputableInPolyTime.length_list encKilianOpening).comp hanswers)
      ((ComputableInPolyTime.length_list encNat).comp hqueries)
  have hbits : ComputableInPolyTime (fun g => (answers g).map MerkleOpening.leaf) encIn encBits :=
    ComputableInPolyTime.listToBits.comp
      (ComputableInPolyTime.mapWithInput hanswers
        (encKilianOpening_leaf_polyTime (ComputableInPolyTime.snd encIn encKilianOpening)))
  have hverdict := hV.2.2.comp ((hx.prod hρ).prod hbits)
  unfold kilianCheck
  exact ComputableInPolyTime.bool_and' (ComputableInPolyTime.bool_and' hlength hall)
    hverdict

/-- **The verifier's decision is efficient**: `kilianVerify` on the key, the statement, the root,
the random strings and the response takes polynomial time, for a polynomial-time PCP verifier with
`O(log n)` random bits and a polynomial-time hash with `n`-bit digests. Malformed responses are
charged for their length. -/
@[program_certificate]
theorem computableInPolyTime_kilianVerify
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k x, (H k x).length = k.length) (hV : V.PolyTime enc)
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1)) :
    ComputableInPolyTime
      (fun p : (List Bool × α × List Bool) × List (List Bool) × KilianResponse =>
        kilianVerify H V p.1.1 p.1.2.1 p.1.2.2 p.2.1 p.2.2)
      (encPair (encKilianInput enc) (encPair (encList encBits) encKilianResponse)) encBool := by
  have hfst := ComputableInPolyTime.fst (encPair encBits (encPair enc encBits))
    (encPair (encList encBits) encKilianResponse)
  have hsnd := ComputableInPolyTime.snd (encPair encBits (encPair enc encBits))
    (encPair (encList encBits) encKilianResponse)
  have hρs := (ComputableInPolyTime.fst (encList encBits) encKilianResponse).comp hsnd
  have hresponse := (ComputableInPolyTime.snd (encList encBits) encKilianResponse).comp hsnd
  have hlength := ComputableInPolyTime.beq
    ((ComputableInPolyTime.length_list (encList encKilianOpening)).comp hresponse)
    ((ComputableInPolyTime.length_list encBits).comp hρs)
  have hpf := ComputableInPolyTime.fst
    (encPair (encPair encBits (encPair enc encBits)) (encPair (encList encBits) encKilianResponse))
    (encPair encBits (encList encKilianOpening))
  have hps := ComputableInPolyTime.snd
    (encPair (encPair encBits (encPair enc encBits)) (encPair (encList encBits) encKilianResponse))
    (encPair encBits (encList encKilianOpening))
  have hcommon := (ComputableInPolyTime.fst (encPair encBits (encPair enc encBits))
    (encPair (encList encBits) encKilianResponse)).comp hpf
  have hk := (ComputableInPolyTime.fst encBits (encPair enc encBits)).comp hcommon
  have hxroot := (ComputableInPolyTime.snd encBits (encPair enc encBits)).comp hcommon
  have hx := (ComputableInPolyTime.fst enc encBits).comp hxroot
  have hroot := (ComputableInPolyTime.snd enc encBits).comp hxroot
  have hρ := (ComputableInPolyTime.fst encBits (encList encKilianOpening)).comp hps
  have hanswers := (ComputableInPolyTime.snd encBits (encList encKilianOpening)).comp hps
  have hcheck := computableInPolyTime_kilianCheck hH hlen hV hcoins hk hx hroot hρ hanswers
  have hall := ComputableInPolyTime.allWithInput
    (test := fun g q => kilianCheck H V g.1.1 g.1.2.1 g.1.2.2 q.1 q.2)
    ((ComputableInPolyTime.zip encBits (encList encKilianOpening)).comp (hρs.prod hresponse))
    hcheck
  unfold kilianVerify
  exact ComputableInPolyTime.bool_and' hlength hall

private theorem computableInPolyTime_kilianTable (hV : V.PolyTime enc)
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1))
    {x : γ → α} {table : γ → List Bool}
    (hx : ComputableInPolyTime x encIn enc)
    (htable : ComputableInPolyTime table encIn encBits) :
    ComputableInPolyTime (fun g => kilianTable V (x g) (table g)) encIn encBits := by
  have hcount := (ComputableInPolyTime.length_list encNat).comp
    ((PCPVerifier.isPolyTime_queryTable hV hcoins).comp hx)
  exact ComputableInPolyTime.listToBits.comp
    (ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp hcount)
      (ComputableInPolyTime.bitsGetDWithInput
        (htable.comp (ComputableInPolyTime.fst encIn encUnary))
        (ComputableInPolyTime.snd encIn encUnary) false))

private theorem computableInPolyTime_kilianLeaves {table : γ → List Bool}
    (htable : ComputableInPolyTime table encIn encBits) :
    ComputableInPolyTime (fun g => kilianLeaves (table g)) encIn (encList encBits) :=
  ComputableInPolyTime.mapWithInput (ComputableInPolyTime.bitsToList.comp htable)
    (ComputableInPolyTime.bitsCons (ComputableInPolyTime.snd encIn encBool)
      (ComputableInPolyTime.const []))

/-- **The honest commitment is efficient**: the root of the honest prover's tree takes polynomial
time in the key, the statement and the witness table. -/
@[program_certificate]
theorem computableInPolyTime_kilianCommit
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k x, (H k x).length = k.length) (hV : V.PolyTime enc)
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1)) :
    ComputableInPolyTime (fun p : List Bool × α × List Bool => kilianCommit H V p.1 p.2.1 p.2.2)
      (encKilianInput enc) encBits := by
  have hk := ComputableInPolyTime.fst encBits (encPair enc encBits)
  have hrest := ComputableInPolyTime.snd encBits (encPair enc encBits)
  have hx := (ComputableInPolyTime.fst enc encBits).comp hrest
  have htable := (ComputableInPolyTime.snd enc encBits).comp hrest
  exact (computableInPolyTime_merkleRoot hH hlen).comp
    (hk.prod (computableInPolyTime_kilianLeaves
      (computableInPolyTime_kilianTable hV hcoins hx htable)))

private theorem computableInPolyTime_kilianOpen
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k x, (H k x).length = k.length) (hV : V.PolyTime enc)
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1))
    {k : γ → List Bool} {x : γ → α} {table ρ : γ → List Bool}
    (hk : ComputableInPolyTime k encIn encBits)
    (hx : ComputableInPolyTime x encIn enc)
    (htable : ComputableInPolyTime table encIn encBits)
    (hρ : ComputableInPolyTime ρ encIn encBits) :
    ComputableInPolyTime (fun g => kilianOpen H V (k g) (x g) (table g) (ρ g)) encIn
      (encList encKilianOpening) := by
  have hqueries := hV.2.1.comp (hx.prod hρ)
  have hfst := ComputableInPolyTime.fst encIn encNat
  have ha := ComputableInPolyTime.snd encIn encNat
  have hnormal := computableInPolyTime_kilianTable hV hcoins (hx.comp hfst)
    (htable.comp hfst)
  have hpos : ComputableInPolyTime (fun p : γ × ℕ => kilianPosition V (x p.1) p.2)
      (encPair encIn encNat) encUnary :=
    ComputableInPolyTime.idxOfWithInput
      ((PCPVerifier.isPolyTime_queryTable hV hcoins).comp (hx.comp hfst)) ha
  have hbit := ComputableInPolyTime.bitsGetDWithInput hnormal hpos false
  have hpath := (computableInPolyTime_merklePath hH hlen).comp
    ((hk.comp hfst).prod ((computableInPolyTime_kilianLeaves hnormal).prod hpos))
  exact ComputableInPolyTime.mapWithInput hqueries (encKilianOpening_mk_polyTime hbit hpath)

/-- **The honest response is efficient**: the honest prover's openings take polynomial time in
the key, the statement, the witness table and the random strings. -/
@[program_certificate]
theorem computableInPolyTime_kilianRespond
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k x, (H k x).length = k.length) (hV : V.PolyTime enc)
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1)) :
    ComputableInPolyTime
      (fun p : (List Bool × α × List Bool) × List (List Bool) =>
        kilianRespond H V p.1.1 p.1.2.1 p.1.2.2 p.2)
      (encPair (encKilianInput enc) (encList encBits)) encKilianResponse := by
  have hfst := ComputableInPolyTime.fst (encPair encBits (encPair enc encBits))
    (encList encBits)
  have hρs := ComputableInPolyTime.snd (encPair encBits (encPair enc encBits))
    (encList encBits)
  have hpf := ComputableInPolyTime.fst
    (encPair (encPair encBits (encPair enc encBits)) (encList encBits)) encBits
  have hρ := ComputableInPolyTime.snd
    (encPair (encPair encBits (encPair enc encBits)) (encList encBits)) encBits
  have hcommon := hfst.comp hpf
  have hk := (ComputableInPolyTime.fst encBits (encPair enc encBits)).comp hcommon
  have hrest := (ComputableInPolyTime.snd encBits (encPair enc encBits)).comp hcommon
  have hx := (ComputableInPolyTime.fst enc encBits).comp hrest
  have htable := (ComputableInPolyTime.snd enc encBits).comp hrest
  exact ComputableInPolyTime.mapWithInput hρs
    (computableInPolyTime_kilianOpen hH hlen hV hcoins hk hx htable hρ)

/-- **Sampling the challenges is efficient**: drawing `n` random strings of `V.coins x` bits is
strict PPT in the unary security parameter and the statement, for a polynomial-time PCP verifier
with `O(log n)` random bits. -/
theorem isPPTOn_kilianChallenges (hV : V.PolyTime enc)
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1)) :
    IsPPTOn (encPair encUnary enc) (encList encBits)
      (fun p : ℕ × α => kilianChallenges V p.1 p.2) :=
  IsPPTOn.replicate
    (((ComputableInPolyTime.binary_to_unary_bounded hV.1 (by fun_prop) hcoins).comp
      (ComputableInPolyTime.snd encUnary enc)).sampleList)
    (ComputableInPolyTime.fst encUnary enc)

end Efficiency

end Cslib.Crypto
