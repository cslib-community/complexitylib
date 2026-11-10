/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Computational.MerkleTree.Binding
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn

/-!
# The BCS transform: public-coin interactive oracle proofs to non-interactive arguments

The Ben-Sasson–Chiesa–Spooner (BCS) transformation ([BenSassonChiesaSpooner2016]; compare
[ChiesaYogev2024], Construction 25.1.1 and Remark 25.1.3, printed pp. 274–275) compiles a
multi-round public-coin Interactive Oracle Proof (`PublicCoinIOP`) into a non-interactive argument
(`BCSProof`, `bcsProve`, `bcsVerify`) by combining two primitives:

1. **Merkle-tree oracle commitments** (`merkleRoot`, `merklePath`, `merkleVerify` from
   `CslibFrontier.Crypto.Computational.MerkleTree` and
   `CslibFrontier.Crypto.Computational.MerkleTree.Binding`): in each round `j : Fin r`, the prover
   commits to its oracle table `π_j : Fin (2 ^ d) → Sym` as the root of a depth-`d` Merkle tree
   over the encoded symbols `oracleLeaves encSym d π_j`.
2. **Fiat–Shamir challenge derivation** (`bcsChallenge`): the verifier's `j`-th public-coin
   challenge `c_j` is derived deterministically by hashing the statement `x` and the prefix of
   Merkle roots `[rt_0, ..., rt_j]` through round `j` with a Fiat–Shamir oracle
   `hFS : Stmt → List (List Bool) → Chal`.
3. **Query openings**: after all `r` rounds, the prover evaluates the IOP verifier's query list
   `iop.queries x chals` on the derived challenges `chals` and opens every queried entry `(j, idx)`
   together with its Merkle authentication path against `rt_j`.

## Main definitions

* `Cslib.Crypto.Protocols.BCS.OracleTable`, `Cslib.Crypto.Protocols.BCS.oracleLeaves`,
  `Cslib.Crypto.Protocols.BCS.prefixChallenges`: depth-`d` oracle tables, their encoded Merkle leaf
  lists, and challenge-prefix restriction.
* `Cslib.Crypto.Protocols.BCS.PublicCoinIOP`, `Cslib.Crypto.Protocols.BCS.iopProverOracles`,
  `Cslib.Crypto.Protocols.BCS.iopAnswers`, `Cslib.Crypto.Protocols.BCS.iopVerify`: syntax and
  evaluation of an `r`-round public-coin Interactive Oracle Proof.
* `Cslib.Crypto.Protocols.BCS.IOPCompleteness`, `Cslib.Crypto.Protocols.BCS.IOPSoundness`,
  `Cslib.Crypto.Protocols.BCS.IOPRoundByRoundSoundness`,
  `Cslib.Crypto.Protocols.BCS.IOPKnowledgeSoundnessAt`,
  `Cslib.Crypto.Protocols.BCS.IOPKnowledgeSoundness`: completeness, soundness, round-by-round
  soundness, and straight-line knowledge soundness of a `PublicCoinIOP`.
* `Cslib.Crypto.Protocols.BCS.BCSOpening`, `Cslib.Crypto.Protocols.BCS.BCSProof`,
  `Cslib.Crypto.Protocols.BCS.rootPrefix`, `Cslib.Crypto.Protocols.BCS.bcsChallenge`: BCS proof
  structure and Fiat–Shamir challenge derivation from Merkle root prefixes.
* `Cslib.Crypto.Protocols.BCS.bcsHonestTables`, `Cslib.Crypto.Protocols.BCS.bcsHonestRoots`,
  `Cslib.Crypto.Protocols.BCS.bcsHonestChallenges`, `Cslib.Crypto.Protocols.BCS.bcsHonestOpenings`,
  `Cslib.Crypto.Protocols.BCS.bcsProve`, `Cslib.Crypto.Protocols.BCS.bcsVerify`: the BCS prover and
  verifier.
* `Cslib.Crypto.Protocols.BCS.bcsFindConflict`,
  `Cslib.Crypto.Protocols.BCS.bcsExtractTableCollision`: deterministic Merkle collision extraction
  when an accepted BCS proof opens a queried entry inconsistently with the committed oracle tables.

## Main results

* `Cslib.Crypto.Protocols.BCS.merkleVerify_oracleLeaves`: honest Merkle paths for `oracleLeaves`
  pass `merkleVerify` at depth `d`.
* `Cslib.Crypto.Protocols.BCS.bcsHonestTables_eq_iopProverOracles`: the causal round-by-round tables
  computed by `bcsHonestTables` agree with the IOP prover run on the full Fiat–Shamir challenge
  vector.
* `Cslib.Crypto.Protocols.BCS.bcsVerify_bcsProve_of_iopVerify`,
  `Cslib.Crypto.Protocols.BCS.bcsVerify_bcsProve_eq_true`: perfect completeness of the BCS transform
  for any hash function `H k` and any Fiat–Shamir function `hFS`.
* `Cslib.Crypto.Protocols.BCS.bcs_sound_or_merkleCollision`,
  `Cslib.Crypto.Protocols.BCS.isCollision_of_bcsVerify_of_iopVerify_eq_false`,
  `Cslib.Crypto.Protocols.BCS.isCollision_of_bcsVerify_conflict`: committed-table and two-opening
  binding extraction reducing BCS soundness to IOP soundness and Merkle collision resistance.
* `Cslib.Crypto.Protocols.BCS.bcs_knowledge_or_soundness_violation_or_collision`,
  `Cslib.Crypto.Protocols.BCS.bcs_knowledge_or_merkleCollision`,
  `Cslib.Crypto.Protocols.BCS.rel_iopExtract_of_bcsVerify_of_openings_eq`: straight-line knowledge
  extraction reduction from accepting BCS proofs to IOP knowledge soundness or an explicit hash
  collision.

## References

* [E. Ben-Sasson, A. Chiesa, N. Spooner, *Interactive Oracle Proofs*][BenSassonChiesaSpooner2016]
* [A. Chiesa, E. Yogev, *Building Cryptographic Proofs from Hash Functions*][ChiesaYogev2024],
  Chapter 25 (Construction 25.1.1, Remark 25.1.3, and Theorem 25.2.1, printed pp. 274–278) and
  Chapter 26 (Theorem 26.1.1, printed pp. 288–289).
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.BCS

open Cslib.Crypto

/-! ### Oracle tables and Merkle leaf encodings -/

/-- An oracle table of depth `d` over alphabet `Sym`, with `2 ^ d` entries indexed by
`Fin (2 ^ d)`. -/
abbrev OracleTable (d : ℕ) (Sym : Type) : Type :=
  Fin (2 ^ d) → Sym

/-- Encode an oracle table `π : OracleTable d Sym` as a list of `2 ^ d` bit-string leaves for a
Merkle tree. -/
def oracleLeaves {Sym : Type} (encSym : Sym → List Bool) (d : ℕ) (π : OracleTable d Sym) :
    List (List Bool) :=
  List.ofFn fun i : Fin (2 ^ d) => encSym (π i)

@[simp]
theorem length_oracleLeaves {Sym : Type} (encSym : Sym → List Bool) (d : ℕ)
    (π : OracleTable d Sym) :
    (oracleLeaves encSym d π).length = 2 ^ d := by
  simp [oracleLeaves]

theorem clog_length_oracleLeaves {Sym : Type} (encSym : Sym → List Bool) (d : ℕ)
    (π : OracleTable d Sym) :
    Nat.clog 2 (oracleLeaves encSym d π).length = d := by
  rw [length_oracleLeaves, Nat.clog_pow _ _ Nat.one_lt_two]

theorem getD_oracleLeaves {Sym : Type} (encSym : Sym → List Bool) (d : ℕ)
    (π : OracleTable d Sym) (idx : Fin (2 ^ d)) :
    (oracleLeaves encSym d π).getD idx.val [] = encSym (π idx) := by
  have hlt : idx.val < (oracleLeaves encSym d π).length := by
    simpa only [length_oracleLeaves] using idx.isLt
  rw [List.getD_eq_getElem _ _ hlt]
  simp [oracleLeaves]

/-- **Honest openings of an oracle table pass `merkleVerify`**: for every index `idx : Fin (2 ^ d)`,
opening `oracleLeaves encSym d π` at `idx.val` with `merklePath` is accepted by `merkleVerify` at
depth `d`. -/
theorem merkleVerify_oracleLeaves (H : List Bool → List Bool → List Bool) (k : List Bool)
    {Sym : Type} (encSym : Sym → List Bool) (d : ℕ) (π : OracleTable d Sym)
    (idx : Fin (2 ^ d)) :
    merkleVerify H k d (merkleRoot H k (oracleLeaves encSym d π)) idx.val (encSym (π idx))
      (merklePath H k (oracleLeaves encSym d π) idx.val) = true := by
  rw [← getD_oracleLeaves encSym d π idx]
  exact merkleVerify_merklePath_of_clog_eq (clog_length_oracleLeaves encSym d π) idx.isLt

/-! ### Public-coin Interactive Oracle Proofs (`PublicCoinIOP`) -/

/-- Restrict a full `r`-round challenge vector `chals : Fin r → Chal` to the first `j` challenges
`(c_0, ..., c_{j-1})` visible before round `j`. -/
def prefixChallenges {r : ℕ} {Chal : Type} (chals : Fin r → Chal) (j : Fin r) :
    Fin j.val → Chal :=
  fun i => chals ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩

/-- An `r`-round public-coin Interactive Oracle Proof (`PublicCoinIOP`) with oracle table depth `d`,
statement type `Stmt`, witness type `Wit`, oracle alphabet `Sym`, and verifier challenge type `Chal`
([BenSassonChiesaSpooner2016]). -/
structure PublicCoinIOP (r d : ℕ) (Stmt Wit Sym Chal : Type) where
  /-- In round `j : Fin r`, given the statement `x`, witness `w`, and previous challenges
  `Fin j.val → Chal`, the honest IOP prover produces an oracle table `Fin (2 ^ d) → Sym`. -/
  proveRound : (j : Fin r) → Stmt → Wit → (Fin j.val → Chal) → OracleTable d Sym
  /-- After all `r` rounds of challenges, the IOP verifier deterministically selects a list of
  `(round, position)` oracle queries. -/
  queries : Stmt → (Fin r → Chal) → List (Fin r × Fin (2 ^ d))
  /-- Given the statement, challenges, and the list of symbols read at `queries x chals`, the IOP
  verifier decides whether to accept. -/
  decide : Stmt → (Fin r → Chal) → List Sym → Bool

section IOP

variable {r d : ℕ} {Stmt Wit Sym Chal : Type}

/-- The `r` oracle tables produced by the honest IOP prover on statement `x`, witness `w`, and
challenges `chals : Fin r → Chal`. -/
def iopProverOracles (iop : PublicCoinIOP r d Stmt Wit Sym Chal) (x : Stmt) (w : Wit)
    (chals : Fin r → Chal) : Fin r → OracleTable d Sym :=
  fun j => iop.proveRound j x w (prefixChallenges chals j)

/-- The list of oracle answers read by `iop.queries x chals` from the oracle tables `oracles`. -/
def iopAnswers (iop : PublicCoinIOP r d Stmt Wit Sym Chal) (x : Stmt) (chals : Fin r → Chal)
    (oracles : Fin r → OracleTable d Sym) : List Sym :=
  (iop.queries x chals).map fun (j, idx) => oracles j idx

@[simp]
theorem length_iopAnswers (iop : PublicCoinIOP r d Stmt Wit Sym Chal) (x : Stmt)
    (chals : Fin r → Chal) (oracles : Fin r → OracleTable d Sym) :
    (iopAnswers iop x chals oracles).length = (iop.queries x chals).length := by
  simp [iopAnswers]

/-- Evaluate the IOP verifier on statement `x`, challenge vector `chals`, and oracle tables
`oracles`. -/
def iopVerify (iop : PublicCoinIOP r d Stmt Wit Sym Chal) (x : Stmt) (chals : Fin r → Chal)
    (oracles : Fin r → OracleTable d Sym) : Bool :=
  iop.decide x chals (iopAnswers iop x chals oracles)

/-- **Perfect completeness** of a `PublicCoinIOP` for relation `rel`: for every `(x, w)` satisfying
`rel x w` and every challenge vector `chals`, the IOP verifier accepts the honest prover's oracle
tables. -/
def IOPCompleteness (iop : PublicCoinIOP r d Stmt Wit Sym Chal) (rel : Stmt → Wit → Prop) : Prop :=
  ∀ x w, rel x w → ∀ chals : Fin r → Chal,
    iopVerify iop x chals (iopProverOracles iop x w chals) = true

/-- **Soundness** of a `PublicCoinIOP` on a set of non-bad challenge vectors `goodChallenges`: for
every statement `x ∉ lang`, every family of oracle tables `oracles`, and every challenge vector
`chals ∈ goodChallenges x oracles`, the IOP verifier rejects. -/
def IOPSoundness (iop : PublicCoinIOP r d Stmt Wit Sym Chal) (lang : Set Stmt)
    (goodChallenges : Stmt → (Fin r → OracleTable d Sym) → Set (Fin r → Chal)) : Prop :=
  ∀ x ∉ lang, ∀ (oracles : Fin r → OracleTable d Sym) (chals : Fin r → Chal),
    chals ∈ goodChallenges x oracles → iopVerify iop x chals oracles = false

/-- **Round-by-round soundness** of a `PublicCoinIOP` with respect to a doomed-prefix predicate
`doomed : Stmt → List (OracleTable d Sym × Chal) → Prop` and non-escaping round transitions
`goodStep : Stmt → List (OracleTable d Sym × Chal) → OracleTable d Sym → Chal → Prop`:
1. The empty prefix is doomed for every `x ∉ lang`.
2. Whenever a prefix `pref` is doomed and the round challenge `c` satisfies `goodStep x pref π c`,
   the extended prefix `pref ++ [(π, c)]` remains doomed.
3. On any full transcript `List.ofFn (fun j => (oracles j, chals j))` that is doomed, the IOP
   verifier rejects. -/
structure IOPRoundByRoundSoundness (iop : PublicCoinIOP r d Stmt Wit Sym Chal) (lang : Set Stmt)
    (doomed : Stmt → List (OracleTable d Sym × Chal) → Prop)
    (goodStep : Stmt → List (OracleTable d Sym × Chal) → OracleTable d Sym → Chal → Prop) :
    Prop where
  /-- Every false statement starts in a doomed state on the empty transcript prefix. -/
  init_doomed : ∀ x ∉ lang, doomed x []
  /-- Every non-escaping challenge preserves the doomed state. -/
  step_doomed : ∀ x pref π c, doomed x pref → goodStep x pref π c → doomed x (pref ++ [(π, c)])
  /-- A doomed complete transcript is rejected by the IOP verifier. -/
  reject_of_doomed : ∀ x (oracles : Fin r → OracleTable d Sym) (chals : Fin r → Chal),
    doomed x (List.ofFn fun j : Fin r => (oracles j, chals j)) →
      iopVerify iop x chals oracles = false

/-- A prefix predicate `doomed x` that holds on the empty prefix and survives every round
satisfying `goodStep` holds on the complete transcript when every round satisfies `goodStep`. -/
theorem doomed_ofFn_of_goodSteps {doomed : Stmt → List (OracleTable d Sym × Chal) → Prop}
    {goodStep : Stmt → List (OracleTable d Sym × Chal) → OracleTable d Sym → Chal → Prop}
    {x : Stmt} (hinit : doomed x [])
    (hstep : ∀ pref π c, doomed x pref → goodStep x pref π c → doomed x (pref ++ [(π, c)]))
    (oracles : Fin r → OracleTable d Sym) (chals : Fin r → Chal)
    (hsteps : ∀ j : Fin r,
      goodStep x ((List.ofFn fun i : Fin r => (oracles i, chals i)).take j.val)
        (oracles j) (chals j)) :
    doomed x (List.ofFn fun j : Fin r => (oracles j, chals j)) := by
  set tr := List.ofFn fun j : Fin r => (oracles j, chals j)
  have hlen : tr.length = r := List.length_ofFn
  suffices ∀ m ≤ r, doomed x (tr.take m) by
    simpa only [← hlen, List.take_length] using this r le_rfl
  intro m hm
  induction m with
  | zero =>
    simpa only [List.take_zero] using hinit
  | succ m ih =>
    have hmr : m < r := hm
    have hmlen : m < tr.length := by simpa only [hlen] using hmr
    rw [List.take_succ_eq_append_getElem hmlen]
    have hget : tr[m] = (oracles ⟨m, hmr⟩, chals ⟨m, hmr⟩) := by
      simp [tr]
    rw [hget]
    exact hstep (tr.take m) (oracles ⟨m, hmr⟩) (chals ⟨m, hmr⟩) (ih hmr.le) (hsteps ⟨m, hmr⟩)

/-- If every round's challenge satisfies `goodStep` under `IOPRoundByRoundSoundness`, then the IOP
verifier rejects `x ∉ lang`. -/
theorem IOPRoundByRoundSoundness.iopVerify_eq_false
    {iop : PublicCoinIOP r d Stmt Wit Sym Chal} {lang : Set Stmt}
    {doomed : Stmt → List (OracleTable d Sym × Chal) → Prop}
    {goodStep : Stmt → List (OracleTable d Sym × Chal) → OracleTable d Sym → Chal → Prop}
    (hrbr : IOPRoundByRoundSoundness iop lang doomed goodStep) {x : Stmt} (hx : x ∉ lang)
    (oracles : Fin r → OracleTable d Sym) (chals : Fin r → Chal)
    (hsteps : ∀ j : Fin r,
      goodStep x ((List.ofFn fun i : Fin r => (oracles i, chals i)).take j.val)
        (oracles j) (chals j)) :
    iopVerify iop x chals oracles = false :=
  hrbr.reject_of_doomed x oracles chals
    (doomed_ofFn_of_goodSteps (hrbr.init_doomed x hx) (hrbr.step_doomed x) oracles chals hsteps)

/-- **Knowledge soundness at a challenge vector** `(x, chals, oracles)`: if the IOP verifier accepts
`oracles` at challenge `chals`, the straight-line IOP knowledge extractor `iopExtract` recovers a
valid witness for `x`. -/
def IOPKnowledgeSoundnessAt (iop : PublicCoinIOP r d Stmt Wit Sym Chal) (rel : Stmt → Wit → Prop)
    (iopExtract : Stmt → (Fin r → OracleTable d Sym) → Wit) (x : Stmt) (chals : Fin r → Chal)
    (oracles : Fin r → OracleTable d Sym) : Prop :=
  iopVerify iop x chals oracles = true → rel x (iopExtract x oracles)

/-- **Straight-line knowledge soundness** of a `PublicCoinIOP`: whenever `iopVerify` accepts
`oracles` on `(x, chals)`, `iopExtract x oracles` satisfies `rel x`. -/
def IOPKnowledgeSoundness (iop : PublicCoinIOP r d Stmt Wit Sym Chal) (rel : Stmt → Wit → Prop)
    (iopExtract : Stmt → (Fin r → OracleTable d Sym) → Wit) : Prop :=
  ∀ x chals oracles, IOPKnowledgeSoundnessAt iop rel iopExtract x chals oracles

end IOP

/-! ### The BCS Transform (`BCSProof`, `bcsProve`, `bcsVerify`) -/

/-- A single query opening in a BCS proof: the claimed symbol `Sym` and its Merkle authentication
path `List (List Bool)`. -/
abbrev BCSOpening (Sym : Type) : Type :=
  Sym × List (List Bool)

/-- A non-interactive BCS proof for an `r`-round `PublicCoinIOP`: one Merkle root per round and one
`BCSOpening` per verifier query ([BenSassonChiesaSpooner2016]; compare [ChiesaYogev2024],
Construction 25.1.1). -/
structure BCSProof (r : ℕ) (Sym : Type) where
  /-- The Merkle root committed in each round `j : Fin r`. -/
  roots : Fin r → List Bool
  /-- The opened symbol and authentication path for each query in `iop.queries x chals`. -/
  openings : List (BCSOpening Sym)

/-- The prefix of Merkle roots `[rt_0, ..., rt_j]` through round `j : Fin r`. -/
def rootPrefix {r : ℕ} (roots : Fin r → List Bool) (j : Fin r) : List (List Bool) :=
  List.ofFn fun t : Fin (j.val + 1) => roots ⟨t.val, Nat.lt_of_lt_of_le t.isLt j.isLt⟩

@[simp]
theorem length_rootPrefix {r : ℕ} (roots : Fin r → List Bool) (j : Fin r) :
    (rootPrefix roots j).length = j.val + 1 := by
  simp [rootPrefix]

/-- `rootPrefix roots j` is the length-`(j + 1)` prefix of the full root list `List.ofFn roots`. -/
theorem rootPrefix_eq_take_ofFn {r : ℕ} (roots : Fin r → List Bool) (j : Fin r) :
    rootPrefix roots j = (List.ofFn roots).take (j.val + 1) := by
  refine List.ext_getElem ?_ fun m h₁ h₂ => ?_
  · have hj : j.val + 1 ≤ r := j.isLt
    simp [rootPrefix, hj]
  · simp only [rootPrefix, List.getElem_ofFn, List.getElem_take]

/-- The Fiat–Shamir challenge for round `j : Fin r`, obtained by applying the Fiat–Shamir oracle
`hFS` to the statement `x` and the prefix of Merkle roots `[rt_0, ..., rt_j]`. -/
def bcsChallenge {r : ℕ} {Stmt Chal : Type} (hFS : Stmt → List (List Bool) → Chal)
    (x : Stmt) (roots : Fin r → List Bool) (j : Fin r) : Chal :=
  hFS x (rootPrefix roots j)

section Transform

variable {r d : ℕ} {Stmt Wit Sym Chal : Type}

/-- Structural helper for `bcsHonestTables`: given `fuel ≥ j.val`, computes the round-`j` oracle
table by structural recursion on `fuel` so that concrete instances reduce in the kernel. -/
def bcsHonestTablesAux (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (H : List Bool → List Bool → List Bool) (k : List Bool) (encSym : Sym → List Bool)
    (hFS : Stmt → List (List Bool) → Chal) (x : Stmt) (w : Wit) :
    (fuel : ℕ) → (j : Fin r) → j.val ≤ fuel → OracleTable d Sym
  | 0, j, hj =>
    iop.proveRound j x w fun i => absurd (Nat.lt_of_lt_of_le i.isLt hj) (Nat.not_lt_zero _)
  | fuel + 1, j, hj =>
    iop.proveRound j x w fun i =>
      hFS x (List.ofFn fun t : Fin (i.val + 1) =>
        have ht : t.val < j.val := Nat.lt_of_lt_of_le t.isLt i.isLt
        merkleRoot H k (oracleLeaves encSym d
          (bcsHonestTablesAux iop H k encSym hFS x w fuel
            ⟨t.val, Nat.lt_trans ht j.isLt⟩
            (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le ht hj)))))

private theorem bcsHonestTablesAux_eq (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (H : List Bool → List Bool → List Bool) (k : List Bool) (encSym : Sym → List Bool)
    (hFS : Stmt → List (List Bool) → Chal) (x : Stmt) (w : Wit) :
    ∀ (fuel₁ fuel₂ : ℕ) (j : Fin r) (hj₁ : j.val ≤ fuel₁) (hj₂ : j.val ≤ fuel₂),
      bcsHonestTablesAux iop H k encSym hFS x w fuel₁ j hj₁ =
        bcsHonestTablesAux iop H k encSym hFS x w fuel₂ j hj₂
  | 0, 0, j, _, _ => rfl
  | 0, _ + 1, j, hj₁, _ => by
    simp only [bcsHonestTablesAux]
    exact congrArg (iop.proveRound j x w) (funext fun i =>
      False.elim (Nat.not_lt_zero _ (Nat.lt_of_lt_of_le i.isLt hj₁)))
  | _ + 1, 0, j, _, hj₂ => by
    simp only [bcsHonestTablesAux]
    exact congrArg (iop.proveRound j x w) (funext fun i =>
      False.elim (Nat.not_lt_zero _ (Nat.lt_of_lt_of_le i.isLt hj₂)))
  | fuel₁ + 1, fuel₂ + 1, j, hj₁, hj₂ => by
    simp only [bcsHonestTablesAux]
    refine congrArg (iop.proveRound j x w) (funext fun i => congrArg (hFS x) ?_)
    refine congrArg List.ofFn (funext fun t => ?_)
    have ht : t.val < j.val := Nat.lt_of_lt_of_le t.isLt i.isLt
    rw [bcsHonestTablesAux_eq iop H k encSym hFS x w fuel₁ fuel₂ ⟨t.val, Nat.lt_trans ht j.isLt⟩
      (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le ht hj₁))
      (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le ht hj₂))]

/-- The honest IOP oracle tables computed sequentially during the BCS transform: in round `j`, each
earlier challenge `c_i` (`i < j`) is derived via `hFS` from the Merkle roots of rounds `0, ..., i`,
and the IOP prover computes the round-`j` oracle table from `(c_0, ..., c_{j-1})`. -/
def bcsHonestTables (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (H : List Bool → List Bool → List Bool) (k : List Bool) (encSym : Sym → List Bool)
    (hFS : Stmt → List (List Bool) → Chal) (x : Stmt) (w : Wit) (j : Fin r) :
    OracleTable d Sym :=
  bcsHonestTablesAux iop H k encSym hFS x w j.val j le_rfl

/-- The Merkle roots committed by the honest BCS prover in each round `j : Fin r`. -/
def bcsHonestRoots (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (H : List Bool → List Bool → List Bool) (k : List Bool) (encSym : Sym → List Bool)
    (hFS : Stmt → List (List Bool) → Chal) (x : Stmt) (w : Wit) : Fin r → List Bool :=
  fun j => merkleRoot H k (oracleLeaves encSym d (bcsHonestTables iop H k encSym hFS x w j))

/-- The Fiat–Shamir challenges derived from the honest BCS prover's Merkle roots. -/
def bcsHonestChallenges (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (H : List Bool → List Bool → List Bool) (k : List Bool) (encSym : Sym → List Bool)
    (hFS : Stmt → List (List Bool) → Chal) (x : Stmt) (w : Wit) : Fin r → Chal :=
  bcsChallenge hFS x (bcsHonestRoots iop H k encSym hFS x w)

/-- The Merkle openings produced by the honest BCS prover for all queries in `iop.queries`. -/
def bcsHonestOpenings (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (H : List Bool → List Bool → List Bool) (k : List Bool) (encSym : Sym → List Bool)
    (hFS : Stmt → List (List Bool) → Chal) (x : Stmt) (w : Wit) : List (BCSOpening Sym) :=
  let tables := bcsHonestTables iop H k encSym hFS x w
  let chals := bcsHonestChallenges iop H k encSym hFS x w
  (iop.queries x chals).map fun (j, idx) =>
    (tables j idx, merklePath H k (oracleLeaves encSym d (tables j)) idx.val)

/-- **The BCS prover** (`bcsProve`): sequentially computes each round's IOP oracle table, commits to
it with `merkleRoot`, derives the Fiat–Shamir challenges via `hFS`, and opens every queried entry
with `merklePath` ([BenSassonChiesaSpooner2016]; compare [ChiesaYogev2024], Construction 25.1.1 and
Remark 25.1.3). -/
def bcsProve (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (H : List Bool → List Bool → List Bool) (k : List Bool) (encSym : Sym → List Bool)
    (hFS : Stmt → List (List Bool) → Chal) (x : Stmt) (w : Wit) : BCSProof r Sym where
  roots := bcsHonestRoots iop H k encSym hFS x w
  openings := bcsHonestOpenings iop H k encSym hFS x w

/-- **The BCS verifier** (`bcsVerify`): recomputes the Fiat–Shamir challenges `c_j` from the Merkle
roots in `prf`, checks that every queried entry `(j, idx)` has a valid depth-`d` Merkle opening
against `prf.roots j`, and runs `iop.decide` on the opened symbols ([BenSassonChiesaSpooner2016];
compare [ChiesaYogev2024], Construction 25.1.1 and Remark 25.1.3). -/
def bcsVerify (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (H : List Bool → List Bool → List Bool) (k : List Bool) (encSym : Sym → List Bool)
    (hFS : Stmt → List (List Bool) → Chal) (x : Stmt) (prf : BCSProof r Sym) : Bool :=
  let chals := bcsChallenge hFS x prf.roots
  let qs := iop.queries x chals
  prf.openings.length == qs.length &&
    (qs.zip prf.openings).all (fun ((j, idx), (val, path)) =>
      merkleVerify H k d (prf.roots j) idx.val (encSym val) path) &&
    iop.decide x chals (prf.openings.map Prod.fst)

/-! ### Perfect completeness -/

/-- **Causal consistency of `bcsHonestTables`**: the oracle tables produced sequentially in the BCS
transform equal the IOP prover's oracle tables evaluated on the full Fiat–Shamir challenge vector
`bcsHonestChallenges`. -/
theorem bcsHonestTables_eq_iopProverOracles (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (H : List Bool → List Bool → List Bool) (k : List Bool) (encSym : Sym → List Bool)
    (hFS : Stmt → List (List Bool) → Chal) (x : Stmt) (w : Wit) :
    bcsHonestTables iop H k encSym hFS x w =
      iopProverOracles iop x w (bcsHonestChallenges iop H k encSym hFS x w) := by
  funext j
  rw [bcsHonestTables, bcsHonestTablesAux_eq iop H k encSym hFS x w j.val (j.val + 1) j
    le_rfl (Nat.le_succ _)]
  simp only [bcsHonestTablesAux, iopProverOracles]
  refine congrArg (iop.proveRound j x w) (funext fun i => congrArg (hFS x) ?_)
  refine congrArg List.ofFn (funext fun t => ?_)
  have ht : t.val < j.val := Nat.lt_of_lt_of_le t.isLt i.isLt
  rw [bcsHonestRoots, bcsHonestTables, bcsHonestTablesAux_eq iop H k encSym hFS x w j.val t.val
    ⟨t.val, Nat.lt_trans ht j.isLt⟩ (Nat.le_of_lt ht) le_rfl]

/-- If the IOP verifier accepts the honest prover's tables at the Fiat–Shamir challenge vector
`bcsHonestChallenges`, then `bcsVerify` accepts `bcsProve`. -/
theorem bcsVerify_bcsProve_of_iopVerify (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (H : List Bool → List Bool → List Bool) (k : List Bool) (encSym : Sym → List Bool)
    (hFS : Stmt → List (List Bool) → Chal) (x : Stmt) (w : Wit)
    (hiop : iopVerify iop x (bcsHonestChallenges iop H k encSym hFS x w)
      (iopProverOracles iop x w (bcsHonestChallenges iop H k encSym hFS x w)) = true) :
    bcsVerify iop H k encSym hFS x (bcsProve iop H k encSym hFS x w) = true := by
  set tables := bcsHonestTables iop H k encSym hFS x w
  set chals := bcsHonestChallenges iop H k encSym hFS x w
  set qs := iop.queries x chals
  have hzip (g : Fin r × Fin (2 ^ d) → BCSOpening Sym) :
      qs.zip (qs.map g) = qs.map fun q => (q, g q) := by
    simpa only [List.map_id, id] using List.zip_map' (f := id) (g := g) (l := qs)
  change ((qs.map _).length == qs.length &&
    (qs.zip (qs.map _)).all (fun ((j, idx), (val, path)) =>
      merkleVerify H k d (bcsHonestRoots iop H k encSym hFS x w j) idx.val (encSym val) path) &&
    iop.decide x chals ((qs.map _).map Prod.fst)) = true
  simp only [hzip, Bool.and_eq_true, beq_iff_eq, List.length_map, List.all_map, List.all_eq_true,
    Function.comp_def, List.map_map, true_and]
  refine ⟨fun ⟨j, idx⟩ _ => ?_, ?_⟩
  · exact merkleVerify_oracleLeaves H k encSym d (tables j) idx
  · rw [bcsHonestTables_eq_iopProverOracles]
    exact hiop

/-- **Perfect completeness of the BCS transform**: if `iop` satisfies `IOPCompleteness iop rel` and
`rel x w` holds, then for *every* Merkle hash `H`, key `k`, symbol encoding `encSym`, and
Fiat–Shamir function `hFS`, `bcsVerify` accepts `bcsProve` ([BenSassonChiesaSpooner2016]; compare
[ChiesaYogev2024], Construction 25.1.1). -/
theorem bcsVerify_bcsProve_eq_true {iop : PublicCoinIOP r d Stmt Wit Sym Chal}
    {rel : Stmt → Wit → Prop} (hcomp : IOPCompleteness iop rel)
    (H : List Bool → List Bool → List Bool) (k : List Bool) (encSym : Sym → List Bool)
    (hFS : Stmt → List (List Bool) → Chal) {x : Stmt} {w : Wit} (hrel : rel x w) :
    bcsVerify iop H k encSym hFS x (bcsProve iop H k encSym hFS x w) = true :=
  bcsVerify_bcsProve_of_iopVerify iop H k encSym hFS x w
    (hcomp x w hrel (bcsHonestChallenges iop H k encSym hFS x w))

/-! ### Binding extraction and soundness / knowledge reductions -/

/-- Find the first query-opening pair `((j, idx), (val, path))` in a BCS proof whose encoded symbol
`encSym val` disagrees with the committed oracle table entry `encSym (oracles j idx)`. -/
def bcsFindConflict (iop : PublicCoinIOP r d Stmt Wit Sym Chal) (encSym : Sym → List Bool)
    (hFS : Stmt → List (List Bool) → Chal) (x : Stmt) (oracles : Fin r → OracleTable d Sym)
    (prf : BCSProof r Sym) : Option ((Fin r × Fin (2 ^ d)) × BCSOpening Sym) :=
  let chals := bcsChallenge hFS x prf.roots
  ((iop.queries x chals).zip prf.openings).find? fun ((j, idx), (val, _)) =>
    encSym val != encSym (oracles j idx)

/-- **Deterministic Merkle collision extractor for the BCS transform**: given committed oracle
tables `oracles` and a BCS proof `prf`, find the first query position where `prf` opens a symbol
whose encoding differs from `oracles` and run `extractMerkleCollision` against the honest Merkle
path of `oracles`. -/
def bcsExtractTableCollision (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (H : List Bool → List Bool → List Bool) (k : List Bool) (encSym : Sym → List Bool)
    (hFS : Stmt → List (List Bool) → Chal) (x : Stmt) (oracles : Fin r → OracleTable d Sym)
    (prf : BCSProof r Sym) : List Bool × List Bool :=
  match bcsFindConflict iop encSym hFS x oracles prf with
  | none => ([], [])
  | some ((j, idx), (val, path)) =>
    extractMerkleCollision H k (encSym val) (encSym (oracles j idx)) idx.val path
      (merklePath H k (oracleLeaves encSym d (oracles j)) idx.val)

/-- If `bcsVerify` accepts `prf` and every opened symbol in `prf` agrees with the oracle tables
`oracles`, then the IOP verifier accepts `oracles` at the Fiat–Shamir challenge vector
`bcsChallenge hFS x prf.roots`. -/
theorem iopVerify_eq_true_of_bcsVerify_of_openings_eq
    {iop : PublicCoinIOP r d Stmt Wit Sym Chal}
    {H : List Bool → List Bool → List Bool} {k : List Bool} {encSym : Sym → List Bool}
    {hFS : Stmt → List (List Bool) → Chal} {x : Stmt} {oracles : Fin r → OracleTable d Sym}
    {prf : BCSProof r Sym} (hver : bcsVerify iop H k encSym hFS x prf = true)
    (hagree : ∀ j idx val path,
      ((j, idx), (val, path)) ∈ (iop.queries x (bcsChallenge hFS x prf.roots)).zip prf.openings →
      val = oracles j idx) :
    iopVerify iop x (bcsChallenge hFS x prf.roots) oracles = true := by
  simp only [bcsVerify, Bool.and_eq_true, beq_iff_eq] at hver
  obtain ⟨⟨hlen, -⟩, hdecide⟩ := hver
  rw [iopVerify, ← hdecide]
  congr 1
  symm
  refine List.ext_getElem (by simp [iopAnswers, hlen]) fun m h₁ h₂ => ?_
  set chals := bcsChallenge hFS x prf.roots
  set qs := iop.queries x chals
  have hmq : m < qs.length := by simpa only [length_iopAnswers] using h₂
  have hmo : m < prf.openings.length := by simpa only [List.length_map] using h₁
  have hmem : (qs[m], prf.openings[m]) ∈ qs.zip prf.openings :=
    List.mem_iff_getElem.mpr ⟨m, by simp [hmq, hmo], by simp⟩
  have heq := hagree qs[m].1 qs[m].2 prf.openings[m].1 prf.openings[m].2 hmem
  simpa only [iopAnswers, List.getElem_map] using heq

/-- **Committed-table binding extraction (`bcs_sound_or_merkleCollision`)**: if `bcsVerify` accepts
`prf` against the Merkle roots of `oracles : Fin r → OracleTable d Sym` and `encSym` is injective,
then either the IOP verifier accepts `oracles` on the Fiat–Shamir challenges
`bcsChallenge hFS x prf.roots`, or `bcsExtractTableCollision` deterministically extracts a hash
collision for `H k` ([BenSassonChiesaSpooner2016]; compare [ChiesaYogev2024], Theorem 25.2.1). -/
theorem bcs_sound_or_merkleCollision
    {iop : PublicCoinIOP r d Stmt Wit Sym Chal}
    {H : List Bool → List Bool → List Bool} {k : List Bool} {encSym : Sym → List Bool}
    (hinj : Function.Injective encSym) {hFS : Stmt → List (List Bool) → Chal}
    {x : Stmt} {oracles : Fin r → OracleTable d Sym} {prf : BCSProof r Sym}
    (hroots : ∀ j : Fin r, prf.roots j = merkleRoot H k (oracleLeaves encSym d (oracles j)))
    (hver : bcsVerify iop H k encSym hFS x prf = true) (n : ℕ) :
    iopVerify iop x (bcsChallenge hFS x prf.roots) oracles = true ∨
      let col := bcsExtractTableCollision iop H k encSym hFS x oracles prf
      isCollision H (fun _ _ => true) n k col.1 col.2 = true := by
  by_cases hfind : (bcsFindConflict iop encSym hFS x oracles prf).isSome = true
  · right
    obtain ⟨⟨⟨j, idx⟩, ⟨val, path⟩⟩, hsome⟩ := Option.isSome_iff_exists.mp hfind
    have hmem := List.mem_of_find?_eq_some hsome
    have hne_bool := List.find?_some hsome
    simp only [bne_iff_ne, ne_eq] at hne_bool
    simp only [bcsVerify, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hver
    have hmv₁ : merkleVerify H k d (prf.roots j) idx.val (encSym val) path = true :=
      hver.1.2 ((j, idx), (val, path)) hmem
    have hmv₂ : merkleVerify H k d (prf.roots j) idx.val (encSym (oracles j idx))
        (merklePath H k (oracleLeaves encSym d (oracles j)) idx.val) = true := by
      rw [hroots j]
      exact merkleVerify_oracleLeaves H k encSym d (oracles j) idx
    simp only [bcsExtractTableCollision, hsome]
    exact isCollision_of_merkleVerify hmv₁ hmv₂ hne_bool n
  · left
    rw [Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hfind
    refine iopVerify_eq_true_of_bcsVerify_of_openings_eq hver fun j idx val path hmem => ?_
    have hnone := List.find?_eq_none.mp hfind ((j, idx), (val, path)) hmem
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hnone
    exact hinj hnone

/-- If the IOP verifier rejects `oracles` at the Fiat–Shamir challenge vector
`bcsChallenge hFS x prf.roots` while `bcsVerify` accepts `prf`, then `bcsExtractTableCollision`
deterministically extracts a hash collision for `H k`. -/
theorem isCollision_of_bcsVerify_of_iopVerify_eq_false
    {iop : PublicCoinIOP r d Stmt Wit Sym Chal}
    {H : List Bool → List Bool → List Bool} {k : List Bool} {encSym : Sym → List Bool}
    (hinj : Function.Injective encSym) {hFS : Stmt → List (List Bool) → Chal}
    {x : Stmt} {oracles : Fin r → OracleTable d Sym} {prf : BCSProof r Sym}
    (hroots : ∀ j : Fin r, prf.roots j = merkleRoot H k (oracleLeaves encSym d (oracles j)))
    (hver : bcsVerify iop H k encSym hFS x prf = true)
    (hrej : iopVerify iop x (bcsChallenge hFS x prf.roots) oracles = false) (n : ℕ) :
    let col := bcsExtractTableCollision iop H k encSym hFS x oracles prf
    isCollision H (fun _ _ => true) n k col.1 col.2 = true := by
  rcases bcs_sound_or_merkleCollision hinj hroots hver n with hacc | hcol
  · rw [hrej] at hacc
    cases hacc
  · exact hcol

/-- **Two-opening binding extraction (`isCollision_of_bcsVerify_conflict`)**: if two accepted BCS
proofs `prf₁` and `prf₂` share the same round-`j` Merkle root and open the same position `(j, idx)`
to symbols `val₁, val₂` with distinct encodings `encSym val₁ ≠ encSym val₂`, then
`extractMerkleCollision` finds a hash collision for `H k`. -/
theorem isCollision_of_bcsVerify_conflict
    {iop : PublicCoinIOP r d Stmt Wit Sym Chal}
    {H : List Bool → List Bool → List Bool} {k : List Bool} {encSym : Sym → List Bool}
    {hFS : Stmt → List (List Bool) → Chal} {x₁ x₂ : Stmt} {prf₁ prf₂ : BCSProof r Sym}
    (hver₁ : bcsVerify iop H k encSym hFS x₁ prf₁ = true)
    (hver₂ : bcsVerify iop H k encSym hFS x₂ prf₂ = true)
    {j : Fin r} (hroot : prf₁.roots j = prf₂.roots j) {idx : Fin (2 ^ d)}
    {val₁ val₂ : Sym} {path₁ path₂ : List (List Bool)}
    (ho₁ : ((j, idx), (val₁, path₁)) ∈
      (iop.queries x₁ (bcsChallenge hFS x₁ prf₁.roots)).zip prf₁.openings)
    (ho₂ : ((j, idx), (val₂, path₂)) ∈
      (iop.queries x₂ (bcsChallenge hFS x₂ prf₂.roots)).zip prf₂.openings)
    (hne : encSym val₁ ≠ encSym val₂) (n : ℕ) :
    let col := extractMerkleCollision H k (encSym val₁) (encSym val₂) idx.val path₁ path₂
    isCollision H (fun _ _ => true) n k col.1 col.2 = true := by
  simp only [bcsVerify, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hver₁ hver₂
  have hmv₁ : merkleVerify H k d (prf₁.roots j) idx.val (encSym val₁) path₁ = true :=
    hver₁.1.2 ((j, idx), (val₁, path₁)) ho₁
  have hmv₂ : merkleVerify H k d (prf₁.roots j) idx.val (encSym val₂) path₂ = true := by
    rw [hroot]
    exact hver₂.1.2 ((j, idx), (val₂, path₂)) ho₂
  exact isCollision_of_merkleVerify hmv₁ hmv₂ hne n

/-- **Knowledge extraction when openings match the committed tables**: if `bcsVerify` accepts `prf`
and every opened symbol in `prf` agrees with `oracles`, then under `IOPKnowledgeSoundnessAt` at the
Fiat–Shamir challenge vector `bcsChallenge hFS x prf.roots`, the straight-line IOP extractor
`iopExtract x oracles` produces a valid witness for `x`. -/
theorem rel_iopExtract_of_bcsVerify_of_openings_eq
    {iop : PublicCoinIOP r d Stmt Wit Sym Chal} {rel : Stmt → Wit → Prop}
    {iopExtract : Stmt → (Fin r → OracleTable d Sym) → Wit}
    {H : List Bool → List Bool → List Bool} {k : List Bool} {encSym : Sym → List Bool}
    {hFS : Stmt → List (List Bool) → Chal} {x : Stmt} {oracles : Fin r → OracleTable d Sym}
    {prf : BCSProof r Sym} (hver : bcsVerify iop H k encSym hFS x prf = true)
    (hagree : ∀ j idx val path,
      ((j, idx), (val, path)) ∈ (iop.queries x (bcsChallenge hFS x prf.roots)).zip prf.openings →
      val = oracles j idx)
    (hks : IOPKnowledgeSoundnessAt iop rel iopExtract x (bcsChallenge hFS x prf.roots) oracles) :
    rel x (iopExtract x oracles) :=
  hks (iopVerify_eq_true_of_bcsVerify_of_openings_eq hver hagree)

/-- **Three-way BCS knowledge extraction reduction**: for any straight-line IOP extractor
`iopExtract : Stmt → (Fin r → OracleTable d Sym) → Wit`, any accepting BCS proof `prf` against
committed oracle tables `oracles` (with `encSym` injective) satisfies at least one of:
1. `rel x (iopExtract x oracles)` (the IOP extractor recovers a valid witness for `x`),
2. `iopVerify iop x (bcsChallenge hFS x prf.roots) oracles = true ∧ ¬ rel x (iopExtract x oracles)`
   (`oracles` violates IOP knowledge soundness at the Fiat–Shamir challenge), or
3. `bcsExtractTableCollision` extracts an explicit hash collision for `H k`
   ([BenSassonChiesaSpooner2016]; compare [ChiesaYogev2024], Theorem 26.1.1). -/
theorem bcs_knowledge_or_soundness_violation_or_collision
    {iop : PublicCoinIOP r d Stmt Wit Sym Chal} (rel : Stmt → Wit → Prop)
    (iopExtract : Stmt → (Fin r → OracleTable d Sym) → Wit)
    {H : List Bool → List Bool → List Bool} {k : List Bool} {encSym : Sym → List Bool}
    (hinj : Function.Injective encSym) {hFS : Stmt → List (List Bool) → Chal}
    {x : Stmt} {oracles : Fin r → OracleTable d Sym} {prf : BCSProof r Sym}
    (hroots : ∀ j : Fin r, prf.roots j = merkleRoot H k (oracleLeaves encSym d (oracles j)))
    (hver : bcsVerify iop H k encSym hFS x prf = true) (n : ℕ) :
    rel x (iopExtract x oracles) ∨
      (iopVerify iop x (bcsChallenge hFS x prf.roots) oracles = true ∧
        ¬ rel x (iopExtract x oracles)) ∨
      (let col := bcsExtractTableCollision iop H k encSym hFS x oracles prf
      isCollision H (fun _ _ => true) n k col.1 col.2 = true) := by
  rcases bcs_sound_or_merkleCollision hinj hroots hver n with hiop | hcol
  · by_cases hrel : rel x (iopExtract x oracles)
    · exact Or.inl hrel
    · exact Or.inr (Or.inl ⟨hiop, hrel⟩)
  · exact Or.inr (Or.inr hcol)

/-- **BCS knowledge extraction under IOP knowledge soundness (`bcs_knowledge_or_merkleCollision`)**:
if `IOPKnowledgeSoundnessAt` holds at the Fiat–Shamir challenge `bcsChallenge hFS x prf.roots`, then
any accepting BCS proof against `oracles` either yields a valid witness
`rel x (iopExtract x oracles)` or yields an explicit hash collision via
`bcsExtractTableCollision`. -/
theorem bcs_knowledge_or_merkleCollision
    {iop : PublicCoinIOP r d Stmt Wit Sym Chal} {rel : Stmt → Wit → Prop}
    {iopExtract : Stmt → (Fin r → OracleTable d Sym) → Wit}
    {H : List Bool → List Bool → List Bool} {k : List Bool} {encSym : Sym → List Bool}
    (hinj : Function.Injective encSym) {hFS : Stmt → List (List Bool) → Chal}
    {x : Stmt} {oracles : Fin r → OracleTable d Sym} {prf : BCSProof r Sym}
    (hroots : ∀ j : Fin r, prf.roots j = merkleRoot H k (oracleLeaves encSym d (oracles j)))
    (hver : bcsVerify iop H k encSym hFS x prf = true)
    (hks : IOPKnowledgeSoundnessAt iop rel iopExtract x (bcsChallenge hFS x prf.roots) oracles)
    (n : ℕ) :
    rel x (iopExtract x oracles) ∨
      let col := bcsExtractTableCollision iop H k encSym hFS x oracles prf
      isCollision H (fun _ _ => true) n k col.1 col.2 = true := by
  rcases bcs_sound_or_merkleCollision hinj hroots hver n with hiop | hcol
  · exact Or.inl (hks hiop)
  · exact Or.inr hcol

end Transform

end Cslib.Crypto.Protocols.BCS
