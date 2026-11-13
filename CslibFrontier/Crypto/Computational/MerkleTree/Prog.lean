/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MerkleTree.ROMExtract
public import CslibFrontier.Languages.Probabilistic.RandomOracle.Invariant
import CslibFrontier.Tactic.SuppCases

/-!
# Merkle trees as oracle programs

`merkleRootProg`, `merklePathProg` and `merkleVerifyProg` lift the binary Merkle tree operations
`merkleRoot`, `merklePath` and `merkleVerify` (`CslibFrontier.Crypto.Computational.MerkleTree`,
`CslibFrontier.Crypto.Computational.MerkleTree.Binding`) to oracle programs over the unkeyed hash
interface `MerkleHashSpec` (`List Bool → List Bool`). Random-oracle constructions such as Micali's
computationally sound proofs (`CslibFrontier.Crypto.Computational.Kilian.Micali`) and the BCS
transformation (`CslibFrontier.Crypto.Protocols.BCS.ROM`) build their provers and verifiers from
these programs.

Evaluating the programs against a deterministic hash `h` with `OracleComp.evalPure h` reproduces
the pure operations at `fun _ => h` with the empty key (`evalPure_merkleRootProg`,
`evalPure_merklePathProg`, `evalPure_merkleVerifyProg`). Under a shared lazy random oracle, every
honest opening verifies with probability one (`merkleVerifyProg_merklePathProg`). Under the
memoized random oracle `memoize dist`, a verification makes at most `path.length + 1` queries and
records every hash step of the checked path in the final trace, as straight-line extraction
(`CslibFrontier.Crypto.Computational.MerkleTree.ROMExtract`) requires.

## Main definitions

* `Cslib.Crypto.MerkleHashSpec`: the oracle interface of an unkeyed hash `List Bool → List Bool`.
* `Cslib.Crypto.merkleRootProg`, `Cslib.Crypto.merklePathProg`, `Cslib.Crypto.merkleVerifyProg`:
  oracle-program Merkle commitment, opening and verification.

## Main results

* `Cslib.Crypto.evalPure_merkleRootProg`, `Cslib.Crypto.evalPure_merklePathProg`,
  `Cslib.Crypto.evalPure_merkleVerifyProg`: simulation by `merkleRoot`, `merklePath` and
  `merkleVerify`.
* `Cslib.Crypto.evalPure_merkleVerifyProg_merklePathProg`,
  `Cslib.Crypto.merkleVerifyProg_merklePathProg`: opening completeness under deterministic and
  lazy random oracles.
* `Cslib.Crypto.isQueryBounded_merkleVerifyProg`: the query bound of a verification.
* `Cslib.Crypto.mem_support_run_memoize_invariant`: the trace invariant of memoized runs.
* `Cslib.Crypto.pathQueriedInTrace_of_mem_support_merkleVerifyProg`,
  `Cslib.Crypto.pathQueriedInTrace_of_mem_support_mapM_merkleVerifyProg`: memoized verifications
  record the hash steps of every checked path.
-/

@[expose] public section

namespace Cslib

namespace Crypto

open Probability Turing.MultiTapeTM

/-! ### Oracle-program Merkle tree -/

/-- Oracle specification for an unkeyed Merkle hash function `List Bool → List Bool`. -/
abbrev MerkleHashSpec : OracleSpec (List Bool) := fun _ => List Bool

/-- Oracle-program computation of leaf-level labels in a Merkle tree, hashing each leaf and
padding to `2 ^ Nat.clog 2 leaves.length` leaves with the empty word `[]`. -/
def merkleLeafLevelProg (leaves : List (List Bool)) :
    OracleComp MerkleHashSpec (List (List Bool)) :=
  (List.range (2 ^ Nat.clog 2 leaves.length)).mapM fun i =>
    OracleComp.query (leaves.getD i [])

/-- Oracle-program computation of one parent layer in a Merkle tree. -/
def merkleParentsProg (level : List (List Bool)) :
    OracleComp MerkleHashSpec (List (List Bool)) :=
  (List.range (level.length / 2)).mapM fun i =>
    OracleComp.query (encPair encBits encBits (level.getD (2 * i) [], level.getD (2 * i + 1) []))

/-- Oracle-program computation of level `j` of the Merkle tree over `leaves`. -/
def merkleLevelProg (leaves : List (List Bool)) :
    ℕ → OracleComp MerkleHashSpec (List (List Bool))
  | 0 => merkleLeafLevelProg leaves
  | j + 1 => do
    let prev ← merkleLevelProg leaves j
    merkleParentsProg prev

/-- Oracle-program computation of the Merkle root of `leaves`. -/
def merkleRootProg (leaves : List (List Bool)) : OracleComp MerkleHashSpec (List Bool) := do
  let top ← merkleLevelProg leaves (Nat.clog 2 leaves.length)
  return top.headD []

/-- One step of `merklePathProg`: record the sibling of the current node, then compute the parent
level and move to the parent position. -/
def merklePathStepProg (state : List (List Bool) × ℕ × List (List Bool)) :
    OracleComp MerkleHashSpec (List (List Bool) × ℕ × List (List Bool)) := do
  let (level, pos, path) := state
  let parents ← merkleParentsProg level
  return (parents, pos / 2, path ++ [level.getD (merkleSibling pos) []])

/-- Iterate `merklePathStepProg` `d` times from `state`. -/
def merklePathLoopProg :
    ℕ → List (List Bool) × ℕ × List (List Bool) →
      OracleComp MerkleHashSpec (List (List Bool) × ℕ × List (List Bool))
  | 0, state => return state
  | d + 1, state => do
    let state' ← merklePathStepProg state
    merklePathLoopProg d state'

/-- Oracle-program computation of the sibling authentication path for position `i`. -/
def merklePathProg (leaves : List (List Bool)) (i : ℕ) :
    OracleComp MerkleHashSpec (List (List Bool)) := do
  let level0 ← merkleLeafLevelProg leaves
  let (_, _, path) ← merklePathLoopProg (Nat.clog 2 leaves.length) (level0, i, [])
  return path

/-- One step of `merkleInputsProg`: hash the current head input and pair it with `sibling`. -/
def merkleInputsStepProg (state : List (List Bool) × ℕ) (sibling : List Bool) :
    OracleComp MerkleHashSpec (List (List Bool) × ℕ) := do
  let node ← OracleComp.query (state.1.headD [])
  return ((if state.2 % 2 = 0 then encPair encBits encBits (node, sibling)
    else encPair encBits encBits (sibling, node)) :: state.1, state.2 / 2)

/-- Oracle-program computation of the hash inputs met while recomputing a root from `leaf` at
position `i` along `path`. -/
def merkleInputsProg (leaf : List Bool) (i : ℕ) (path : List (List Bool)) :
    OracleComp MerkleHashSpec (List (List Bool)) := do
  let (inputs, _) ← path.foldlM merkleInputsStepProg ([leaf], i)
  return inputs

/-- Oracle-program reconstruction of the candidate root from `leaf`, `i` and `path`. -/
def merkleRootOfPathProg (leaf : List Bool) (i : ℕ) (path : List (List Bool)) :
    OracleComp MerkleHashSpec (List Bool) := do
  let inputs ← merkleInputsProg leaf i path
  OracleComp.query (inputs.headD [])

/-- Oracle-program Merkle path verification at depth `d`: checks `path.length == d`,
`i < 2 ^ d`, and that the recomputed root equals `root`. -/
def merkleVerifyProg (d : ℕ) (root : List Bool) (i : ℕ) (leaf : List Bool)
    (path : List (List Bool)) : OracleComp MerkleHashSpec Bool := do
  let cand ← merkleRootOfPathProg leaf i path
  return path.length == d && decide (i < 2 ^ d) && cand == root

/-! ### Simulation by a pure hash -/

@[simp]
theorem evalPure_merkleLeafLevelProg (h : List Bool → List Bool) (leaves : List (List Bool)) :
    OracleComp.evalPure h (merkleLeafLevelProg leaves) =
      merkleLeafLevel (fun _ => h) [] leaves := by
  simp [merkleLeafLevelProg, merkleLeafLevel]

@[simp]
theorem evalPure_merkleParentsProg (h : List Bool → List Bool) (level : List (List Bool)) :
    OracleComp.evalPure h (merkleParentsProg level) =
      merkleParents (fun _ => h) [] level := by
  simp [merkleParentsProg, merkleParents]

@[simp]
theorem evalPure_merkleLevelProg (h : List Bool → List Bool) (leaves : List (List Bool))
    (j : ℕ) :
    OracleComp.evalPure h (merkleLevelProg leaves j) =
      merkleLevel (fun _ => h) [] leaves j := by
  induction j with
  | zero => simp [merkleLevelProg, merkleLevel]
  | succ j ih =>
    simp only [merkleLevelProg, OracleComp.evalPure_bind, ih, evalPure_merkleParentsProg,
      merkleLevel, Function.iterate_succ_apply']

@[simp]
theorem evalPure_merkleRootProg (h : List Bool → List Bool) (leaves : List (List Bool)) :
    OracleComp.evalPure h (merkleRootProg leaves) =
      merkleRoot (fun _ => h) [] leaves := by
  simp [merkleRootProg, merkleRoot]

@[simp]
theorem evalPure_merklePathStepProg (h : List Bool → List Bool)
    (state : List (List Bool) × ℕ × List (List Bool)) :
    OracleComp.evalPure h (merklePathStepProg state) =
      merklePathStep (fun _ => h) [] state := by
  rcases state with ⟨level, pos, path⟩
  simp [merklePathStepProg, merklePathStep]

@[simp]
theorem evalPure_merklePathLoopProg (h : List Bool → List Bool) (d : ℕ)
    (state : List (List Bool) × ℕ × List (List Bool)) :
    OracleComp.evalPure h (merklePathLoopProg d state) =
      (merklePathStep (fun _ => h) [])^[d] state := by
  induction d generalizing state with
  | zero => rfl
  | succ d ih =>
    simp only [merklePathLoopProg, OracleComp.evalPure_bind, evalPure_merklePathStepProg, ih,
      Function.iterate_succ_apply]

@[simp]
theorem evalPure_merklePathProg (h : List Bool → List Bool) (leaves : List (List Bool))
    (i : ℕ) :
    OracleComp.evalPure h (merklePathProg leaves i) =
      merklePath (fun _ => h) [] leaves i := by
  simp [merklePathProg, merklePath]

@[simp]
theorem evalPure_merkleInputsStepProg (h : List Bool → List Bool)
    (state : List (List Bool) × ℕ) (sibling : List Bool) :
    OracleComp.evalPure h (merkleInputsStepProg state sibling) =
      merkleInputsStep (fun _ => h) [] state sibling := by
  simp [merkleInputsStepProg, merkleInputsStep]

@[simp]
theorem evalPure_merkleInputsProg (h : List Bool → List Bool) (leaf : List Bool) (i : ℕ)
    (path : List (List Bool)) :
    OracleComp.evalPure h (merkleInputsProg leaf i path) =
      merkleInputs (fun _ => h) [] leaf i path := by
  simp [merkleInputsProg, merkleInputs, evalPure_merkleInputsStepProg]

@[simp]
theorem evalPure_merkleRootOfPathProg (h : List Bool → List Bool) (leaf : List Bool) (i : ℕ)
    (path : List (List Bool)) :
    OracleComp.evalPure h (merkleRootOfPathProg leaf i path) =
      merkleRootOfPath (fun _ => h) [] leaf i path := by
  simp [merkleRootOfPathProg, merkleRootOfPath]

@[simp]
theorem evalPure_merkleVerifyProg (h : List Bool → List Bool) (d : ℕ) (root : List Bool)
    (i : ℕ) (leaf : List Bool) (path : List (List Bool)) :
    OracleComp.evalPure h (merkleVerifyProg d root i leaf path) =
      merkleVerify (fun _ => h) [] d root i leaf path := by
  simp [merkleVerifyProg, merkleVerify]

/-- **Completeness of `merkleVerifyProg` against `merklePathProg` (pure simulation form)**: for any
deterministic hash `h` and `i < 2 ^ Nat.clog 2 leaves.length`, `merkleVerifyProg` accepts
`merkleRootProg leaves` and `merklePathProg leaves i`. -/
theorem evalPure_merkleVerifyProg_merklePathProg (h : List Bool → List Bool)
    (leaves : List (List Bool)) {i : ℕ} (hi : i < 2 ^ Nat.clog 2 leaves.length) :
    OracleComp.evalPure h (do
      let root ← merkleRootProg leaves
      let path ← merklePathProg leaves i
      merkleVerifyProg (Nat.clog 2 leaves.length) root i (leaves.getD i []) path) = true := by
  simpa using merkleVerify_merklePath (H := fun _ => h) (k := []) leaves hi

/-- **Completeness of `merkleVerifyProg` against `merklePathProg` (lazy random-oracle form)**:
under a shared lazy random oracle `RandomOracle.answer dist`, computing the root with
`merkleRootProg`, opening position `i < 2 ^ Nat.clog 2 leaves.length` with `merklePathProg`, and
verifying with `merkleVerifyProg` returns `true` with probability `1`. -/
theorem merkleVerifyProg_merklePathProg (dist : (q : List Bool) → PMF (MerkleHashSpec q))
    (leaves : List (List Bool)) {i : ℕ} (hi : i < 2 ^ Nat.clog 2 leaves.length) :
    (OracleComp.runWith (RandomOracle.answer dist) (do
      let root ← merkleRootProg leaves
      let path ← merklePathProg leaves i
      merkleVerifyProg (Nat.clog 2 leaves.length) root i (leaves.getD i []) path)
        (fun _ => none)).map Prod.fst = PMF.pure true :=
  OracleComp.map_fst_runWith_answer_eq_pure dist _ true fun h _ =>
    evalPure_merkleVerifyProg_merklePathProg h leaves hi

/-! ### Query bounds and memoized traces -/

private theorem isQueryBounded_foldlM_merkleInputsStepProg (path : List (List Bool))
    (init : List (List Bool) × ℕ) :
    OracleComp.IsQueryBounded (path.foldlM merkleInputsStepProg init) path.length := by
  induction path generalizing init with
  | nil => exact .pure init 0
  | cons sibling rest ih =>
    simp only [List.foldlM_cons, List.length_cons, merkleInputsStepProg]
    exact .liftBind (init.1.headD []) _ rest.length fun node => ih _

/-- `merkleVerifyProg d root i leaf path` makes at most `path.length + 1` Merkle hash queries
(one leaf query plus one query per sibling along `path`). -/
theorem isQueryBounded_merkleVerifyProg (d : ℕ) (root : List Bool) (i : ℕ) (leaf : List Bool)
    (path : List (List Bool)) :
    OracleComp.IsQueryBounded (merkleVerifyProg d root i leaf path) (path.length + 1) := by
  unfold merkleVerifyProg merkleRootOfPathProg merkleInputsProg
  have hinputs : OracleComp.IsQueryBounded
      (path.foldlM merkleInputsStepProg ([leaf], i) >>= fun x => pure x.1)
      path.length := by
    simpa only [Nat.add_zero] using
      (isQueryBounded_foldlM_merkleInputsStepProg path ([leaf], i)).bind fun x =>
        OracleComp.IsCostBounded.pure x.1 0
  have hroot : OracleComp.IsQueryBounded
      ((path.foldlM merkleInputsStepProg ([leaf], i) >>= fun x => pure x.1) >>= fun inputs =>
        OracleComp.query (spec := MerkleHashSpec) (inputs.headD []))
      (path.length + 1) :=
    hinputs.bind fun inputs =>
      OracleComp.IsCostBounded.query (cost := fun _ => 1) (inputs.headD [])
  simpa only [Nat.add_zero] using hroot.bind fun cand =>
    OracleComp.IsCostBounded.pure _ 0

/-- Multi-step invariant of `memoize`: running `prog` from `tr` produces `tr'` extending `tr` with
`Nodup` keys and supported values, and `res = evalPure h prog` for every `h` consistent with
`tr'`. -/
theorem mem_support_run_memoize_invariant {Query : Type} [BEq Query] [LawfulBEq Query]
    {Value β : Type} (dist : Query → PMF Value) (prog : OracleComp (fun _ : Query => Value) β)
    {tr tr' : List (Query × Value)} {res : β}
    (hnodup : (tr.map Prod.fst).Nodup)
    (hsupp : ∀ e ∈ tr, e.2 ∈ (dist e.1).support)
    (hmem : (res, tr') ∈ ((OracleComp.interpret (memoize dist) prog).run tr).support) :
    (∀ e ∈ tr, e ∈ tr') ∧
      (tr'.map Prod.fst).Nodup ∧
      (∀ e ∈ tr', e.2 ∈ (dist e.1).support) ∧
      (∀ h : Query → Value, TraceConsistentWith h tr' → res = OracleComp.evalPure h prog) := by
  induction prog using OracleComp.induction generalizing tr with
  | pure a =>
    supp_cases hmem [OracleComp.run_interpret_pure] with ⟨rfl, rfl⟩
    exact ⟨fun _ h => h, hnodup, hsupp, fun _ _ => rfl⟩
  | query_bind q cont ih =>
    supp_cases hmem [OracleComp.run_interpret_bind, OracleComp.run_interpret_query]
      with ⟨⟨ans, tr₁⟩, hans, hcont⟩
    obtain ⟨hq_mem, hsub₁, hnodup₁, hsupp₁⟩ :=
      mem_support_memoize_nodup dist q hnodup hsupp hans
    obtain ⟨hsub₂, hnodup', hsupp', heval⟩ := ih ans hnodup₁ hsupp₁ hcont
    refine ⟨fun e he => hsub₂ e (hsub₁ e he), hnodup', hsupp', fun h hcons => ?_⟩
    have hq_eq : h q = ans := hcons (q, ans) (hsub₂ (q, ans) hq_mem)
    simp only [OracleComp.evalPure_bind, OracleComp.evalPure_query, hq_eq]
    exact heval h hcons

private theorem mem_support_foldlM_merkleInputsStepProg (dist : List Bool → PMF (List Bool))
    (path : List (List Bool)) (init : List (List Bool) × ℕ) (hinit : init.1 ≠ [])
    {tr tr' : List (List Bool × List Bool)} {out : List (List Bool) × ℕ}
    (hnodup : (tr.map Prod.fst).Nodup)
    (hsupp : ∀ e ∈ tr, e.2 ∈ (dist e.1).support)
    (htail_init : ∀ q ∈ init.1.tail, ∃ ans, (q, ans) ∈ tr)
    (hmem : (out, tr') ∈
      ((OracleComp.interpret (memoize dist)
        (path.foldlM merkleInputsStepProg init)).run tr).support) :
    out.1 ≠ [] ∧ ∀ q ∈ out.1.tail, ∃ ans, (q, ans) ∈ tr' := by
  induction path generalizing init tr with
  | nil =>
    supp_cases hmem [List.foldlM_nil, OracleComp.run_interpret_pure] with ⟨rfl, rfl⟩
    exact ⟨hinit, htail_init⟩
  | cons sibling rest ih =>
    supp_cases hmem [List.foldlM_cons, merkleInputsStepProg, OracleComp.run_interpret_bind,
      OracleComp.run_interpret_query, OracleComp.run_interpret_pure]
      with ⟨_, ⟨⟨node, tr₁⟩, hnode, rfl⟩, hrest⟩
    obtain ⟨hq_mem, hsub₁, hnodup₁, hsupp₁⟩ :=
      mem_support_memoize_nodup dist (init.1.headD []) hnodup hsupp hnode
    refine ih _ (List.cons_ne_nil _ _) hnodup₁ hsupp₁ ?_ hrest
    intro q hq
    simp only [List.tail_cons] at hq
    cases hlist : init.1 with
    | nil => exact False.elim (hinit hlist)
    | cons hd tl =>
      rw [hlist, List.headD_cons] at hq_mem
      rw [hlist] at hq htail_init
      rcases List.mem_cons.mp hq with rfl | htl
      · exact ⟨node, hq_mem⟩
      · obtain ⟨ans, hans⟩ := htail_init q htl
        exact ⟨ans, hsub₁ _ hans⟩

/-- Running `merkleVerifyProg d root i leaf path` under `memoize dist` records every hash step of
`merkleInputs` in the final trace `tr'`. -/
theorem pathQueriedInTrace_of_mem_support_merkleVerifyProg (dist : List Bool → PMF (List Bool))
    (d : ℕ) (root : List Bool) (i : ℕ) (leaf : List Bool) (path : List (List Bool))
    {tr tr' : List (List Bool × List Bool)} {ok : Bool}
    (hnodup : (tr.map Prod.fst).Nodup)
    (hsupp : ∀ e ∈ tr, e.2 ∈ (dist e.1).support)
    (hmem : (ok, tr') ∈
      ((OracleComp.interpret (memoize dist)
        (merkleVerifyProg d root i leaf path)).run tr).support)
    {h : List Bool → List Bool} (hcons : TraceConsistentWith h tr') :
    PathQueriedInTrace (fun _ => h) [] tr' i leaf path := by
  supp_cases hmem [merkleVerifyProg, merkleRootOfPathProg, merkleInputsProg,
    OracleComp.run_interpret_bind, OracleComp.run_interpret_query, OracleComp.run_interpret_pure]
    with ⟨⟨cand, tr₂⟩, ⟨_, ⟨⟨⟨inputs, pos⟩, tr₁⟩, hfold, rfl⟩, hcand⟩, rfl, rfl⟩
  obtain ⟨hsub₁, hnodup₁, hsupp₁, heval₁⟩ :=
    mem_support_run_memoize_invariant dist (path.foldlM merkleInputsStepProg ([leaf], i))
      hnodup hsupp hfold
  obtain ⟨hhead_mem, hsub₂, -, -⟩ :=
    mem_support_memoize_nodup dist (inputs.headD []) hnodup₁ hsupp₁ hcand
  have hcons₁ : TraceConsistentWith h tr₁ := fun p hp => hcons p (hsub₂ p hp)
  have hinputs_eq : inputs = merkleInputs (fun _ => h) [] leaf i path := by
    have heq := congrArg Prod.fst (heval₁ h hcons₁)
    simpa [merkleInputs, evalPure_merkleInputsStepProg] using heq
  obtain ⟨hne, htail⟩ := mem_support_foldlM_merkleInputsStepProg dist path ([leaf], i)
    (List.cons_ne_nil _ _) hnodup hsupp (by simp) hfold
  intro q hq
  rw [← hinputs_eq] at hq
  cases hlist : inputs with
  | nil => exact False.elim (hne hlist)
  | cons hd tl =>
    rw [hlist, List.headD_cons] at hhead_mem
    rw [hlist] at hq htail
    rcases List.mem_cons.mp hq with rfl | htl
    · have hc : h q = cand := hcons (q, cand) hhead_mem
      dsimp only
      rwa [hc]
    · obtain ⟨ans, hans⟩ := htail q htl
      have hans' := hsub₂ (q, ans) hans
      have hc : h q = ans := hcons (q, ans) hans'
      dsimp only
      rwa [hc]

/-- Running a list of Merkle verifications under `memoize dist` records every hash step of each
checked opening in the final trace `tr'`. Item `b` is checked by `check b`, which verifies the
opening `(leaf b, path b)` at position `pos b` against `root b` (`hcheck`). -/
theorem pathQueriedInTrace_of_mem_support_mapM_merkleVerifyProg {β : Type}
    {dist : List Bool → PMF (List Bool)} {check : β → OracleComp MerkleHashSpec Bool}
    {items : List β} {tr tr' : List (List Bool × List Bool)} {checks : List Bool}
    (hnodup : (tr.map Prod.fst).Nodup)
    (hsupp : ∀ e ∈ tr, e.2 ∈ (dist e.1).support)
    (hmem : (checks, tr') ∈
      ((OracleComp.interpret (memoize dist) (items.mapM check)).run tr).support)
    (d : ℕ) (root : β → List Bool) (pos : β → ℕ) (leaf : β → List Bool)
    (path : β → List (List Bool))
    (hcheck : ∀ b, check b = merkleVerifyProg d (root b) (pos b) (leaf b) (path b))
    {h : List Bool → List Bool} (hcons : TraceConsistentWith h tr') :
    ∀ b ∈ items, PathQueriedInTrace (fun _ => h) [] tr' (pos b) (leaf b) (path b) := by
  induction items generalizing tr checks with
  | nil =>
    intro _ hb
    cases hb
  | cons b items ih =>
    supp_cases hmem [List.mapM_cons, OracleComp.run_interpret_bind, OracleComp.run_interpret_pure]
      with ⟨⟨c, tr₁⟩, hc, ⟨cs, tr₂⟩, hcs, rfl, rfl⟩
    rw [hcheck b] at hc
    obtain ⟨hsub₁, hnodup₁, hsupp₁, -⟩ :=
      mem_support_run_memoize_invariant dist _ hnodup hsupp hc
    obtain ⟨hsub₂, -, -, -⟩ := mem_support_run_memoize_invariant dist _ hnodup₁ hsupp₁ hcs
    have hhd := pathQueriedInTrace_of_mem_support_merkleVerifyProg dist d (root b) (pos b)
      (leaf b) (path b) hnodup hsupp hc fun p hp => hcons p (hsub₂ p hp)
    intro b' hb'
    rcases List.mem_cons.mp hb' with rfl | htl
    · intro q hq
      exact hsub₂ _ (hhd q hq)
    · exact ih hnodup₁ hsupp₁ hcs b' htl

end Crypto

end Cslib
