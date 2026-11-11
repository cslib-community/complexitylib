/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.MCSP.Magnification
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure

/-!
# The oracle of the McKay–Murray–Williams merge tree

McKay, Murray and Williams decide `MCSP[s]` on `N = 2 ^ n`-bit truth tables with a merge tree over
the subcubes of `{0, 1} ^ n` [McKayMurrayWilliams2019, Lemma 3.1]. The \[MMW19\] bullet of
[ChenHiraharaOliveiraPichRajgopalSanthanam2020, Appendix A.2, Proposition 63] states the resulting
oracle circuits: `MCSP[s] ∈ [O(N/poly(s)), poly(s), O(n/log s)]–Circuit[N/poly(s)]`, from a tree
whose nodes merge many children at once and whose leaves read `poly(s)` table bits. This module
fixes one oracle for such trees and proves what its queries answer. The circuits are built on top.

The state of a subcube `p` (`Cslib.MCSP.subcubeState`) is its validity bit and least size-`s`
certificate. If `L` encodes `CircuitMinMergeLanguage`, then `Cslib.MCSP.mergeVec L` merges the
states of `p ++ [false]` and `p ++ [true]` into that of `p` (`Cslib.MCSP.mergeVec_eq_subcubeState`).
Iterating it `k` times (`Cslib.MCSP.iterMergeVec`) merges the `2 ^ k` states of the subcubes
`p ++ e`, `e ∈ {0, 1} ^ k`, into the state of `p` (`Cslib.MCSP.iterMergeVec_eq_subcubeState`), by
induction on `k` from the binary step. At a point, the state depends only on the value of the
function there (`Cslib.MCSP.subcubeState_eq_pointState`).

A query (`Cslib.MCSP.MergeTree.Query`) carries `n`, `s`, the prefix `p`, the number `k` of merge
levels, a leaf flag, the requested bit `j` as a unary field, and a payload: the `2 ^ k` child states
for an inner node, or the `2 ^ k` table bits at the points `p ++ e` for a leaf. Its answer is
bit `j` of the `k`-fold merge of its children. The oracle `Cslib.MCSP.MergeTree.oracle` is the set
of encodings of the queries answering yes. It is one language for every `n` and `s`, which the
header carries. A node query built from correct child states
(`Cslib.MCSP.MergeTree.encQuery_ofNode_mem_oracle_iff_merge`) or from table bits
(`Cslib.MCSP.MergeTree.encQuery_ofNode_mem_oracle_iff_leaf`) answers bit `j` of the state of `p`.
At the root, bit `0` is the answer of `MCSP[s]` (`Cslib.GapMCSP.yesSet s`, the yes set alone, with
no gap). For a node query with `j < stateWidth n s`, the header length does not depend on `j` or on
the payload (`Cslib.MCSP.MergeTree.length_encQuery_ofNode`).

**Relation to the source.** CHOPRS Definition 62 allows any oracle language, and CHOPRS do not bound
its uniform complexity ("for our discussion, this is not going to be relevant"); neither does this
module. The oracle is derived from `CircuitMinMergeLanguage`, the binary `Circuit-Min-Merge`
language of `Cslib.MCSP.circuitMinMergeLanguage_mem_PPolyOn`: `k` levels of its merge step, plus
leaf queries on `2 ^ k` table bits. Querying `CircuitMinMergeLanguage` itself gives only the
binary-tree parameters: each oracle gate answers one bit, so each of the `N - 1` binary merges takes
`stateWidth n s` oracle gates, for `≈ N · poly(n, s)` oracle gates of fan-in `poly(n, s)` and
adaptivity `n`.

## Main definitions

* `Cslib.MCSP.mergeLanguage`: the encodings of `CircuitMinMergeLanguage`.
* `Cslib.MCSP.iterMergeVec`: `k` levels of `mergeVec`, merging `2 ^ k` states.
* `Cslib.MCSP.pointState`: the state of a point with a given value.
* `Cslib.MCSP.MergeTree.Query`, `Cslib.MCSP.MergeTree.encQuery`,
  `Cslib.MCSP.MergeTree.Query.ofNode`: queries, their encoding, and the query of a tree node.
* `Cslib.MCSP.MergeTree.childState`, `Cslib.MCSP.MergeTree.Query.answer`: the children read from a
  payload, and the answer to a query.
* `Cslib.MCSP.MergeTree.oracle`: the merge-tree oracle.

## Main results

* `Cslib.MCSP.iterMergeVec_eq_subcubeState`: `k` merge levels map the states of the `2 ^ k`
  subcubes below `p` to the state of `p`.
* `Cslib.MCSP.MergeTree.encQuery_ofNode_mem_oracle_iff_merge`,
  `Cslib.MCSP.MergeTree.encQuery_ofNode_mem_oracle_iff_leaf`: inner and leaf node queries answer a
  bit of the state of their subcube.
* `Cslib.MCSP.MergeTree.encQuery_ofNode_nil_mem_oracle_iff_leaf`: a single root leaf query
  answers `MCSP[s]`.
* `Cslib.MCSP.MergeTree.length_encQuery`, `Cslib.MCSP.MergeTree.encQuery_ofNode`,
  `Cslib.MCSP.MergeTree.length_encQuery_ofNode`: a node query is a fixed header followed by its
  payload.

## References

* [D. McKay, C. D. Murray, R. R. Williams, *Weak Lower Bounds on Resource-Bounded Compression
  Imply Strong Separations of Complexity Classes*][McKayMurrayWilliams2019]
* [L. Chen, S. Hirahara, I. C. Oliveira, J. Pich, N. Rajgopal, R. Santhanam, *Beyond natural
  proofs: hardness magnification and locality*][ChenHiraharaOliveiraPichRajgopalSanthanam2020]
-/

public section

namespace Cslib.MCSP

open Circuits Circuits.Boolean Turing.MultiTapeTM

/-! ### Iterated merges -/

/-- The encodings of `CircuitMinMergeLanguage` under `encMerge`. -/
def mergeLanguage : Language Bool :=
  {w | ∃ a ∈ CircuitMinMergeLanguage, encMerge a = w}

/-- `mergeLanguage` encodes `CircuitMinMergeLanguage`; `mergeVec_eq_subcubeState` takes the
reverse direction. -/
theorem encMerge_mem_mergeLanguage_iff (a : MergeInput) :
    encMerge a ∈ mergeLanguage ↔ a ∈ CircuitMinMergeLanguage :=
  ⟨fun ⟨_, ha', h⟩ => encMerge.injective h ▸ ha', fun ha => ⟨a, ha, rfl⟩⟩

/-- `k` levels of the merge step `mergeVec L`: merges the `2 ^ k` states `y e` of the subcubes
`p ++ e`, `e ∈ {0, 1} ^ k`, into one state, splitting on the first bit of `e`. -/
noncomputable def iterMergeVec (L : Language Bool) (n s : ℕ) :
    (p : List Bool) → (k : ℕ) → (BitString k → BitString (stateWidth n s)) →
      BitString (stateWidth n s)
  | _, 0, y => y Fin.elim0
  | p, k + 1, y => mergeVec L n s p
      (Fin.append (iterMergeVec L n s (p ++ [false]) k fun e => y (Fin.cons false e))
        (iterMergeVec L n s (p ++ [true]) k fun e => y (Fin.cons true e)))

/-- **`k` merge levels.** If `L` encodes `CircuitMinMergeLanguage` and `y e` is the state of the
subcube `p ++ e` for every `e ∈ {0, 1} ^ k`, where `p ++ e` has at most `n` bits, then
`iterMergeVec L n s p k y` is the state of `p`. -/
theorem iterMergeVec_eq_subcubeState {L : Language Bool}
    (hL : ∀ a : MergeInput, a ∈ CircuitMinMergeLanguage ↔ encMerge a ∈ L)
    {n s : ℕ} (f : BooleanFunction n) {p : List Bool} {k : ℕ} (hpk : p.length + k ≤ n)
    {y : BitString k → BitString (stateWidth n s)}
    (hy : ∀ e, y e = subcubeState n s f (p ++ List.ofFn e)) :
    iterMergeVec L n s p k y = subcubeState n s f p := by
  induction k generalizing p with
  | zero => simpa [iterMergeVec] using hy Fin.elim0
  | succ k ih =>
    have hb (b : Bool) : iterMergeVec L n s (p ++ [b]) k (fun e => y (Fin.cons b e)) =
        subcubeState n s f (p ++ [b]) :=
      ih (by simp only [List.length_append, List.length_singleton]; omega) fun e => by
        rw [hy, List.ofFn_succ, Fin.cons_zero]
        simp only [Fin.cons_succ, List.append_assoc, List.singleton_append]
    rw [iterMergeVec, hb, hb]
    exact mergeVec_eq_subcubeState hL f (by omega)

/-- The state of the subcube `p` for the constant function `b`. At a point `p`, it is the state
of every function with value `b` there (`Cslib.MCSP.subcubeState_eq_pointState`). -/
noncomputable def pointState (n s : ℕ) (p : List Bool) (b : Bool) : BitString (stateWidth n s) :=
  subcubeState n s (fun _ => b) p

/-- The state of a point `p` is the point state of the value of `f` at `p`. -/
theorem subcubeState_eq_pointState {n s : ℕ} (f : BooleanFunction n) {p : List Bool}
    (hp : p.length = n) :
    subcubeState n s f p = pointState n s p (f (BitString.ofList n p)) :=
  subcubeState_congr_of_length_eq hp rfl

namespace MergeTree

/-! ### Queries and the oracle -/

/-- A query to the merge-tree oracle: bit `j` of the `levels`-fold merge
(`Cslib.MCSP.iterMergeVec`) of the `2 ^ levels` children of the subcube `subcube`, for arity `arity`
and size bound `size`. -/
structure Query where
  /-- The arity `n` of the truth table. -/
  arity : ℕ
  /-- The size bound `s`. -/
  size : ℕ
  /-- The prefix `p` of the node's subcube. -/
  subcube : List Bool
  /-- The number `k` of merge levels; the node has `2 ^ k` children. -/
  levels : ℕ
  /-- Whether the children are points read from table bits (`true`) or subcubes whose states the
  payload holds (`false`). -/
  leaf : Bool
  /-- The requested bit `j`, as the number of `true` bits of a unary field. -/
  bitField : List Bool
  /-- The children, in the order of `BitString.equivFin`: one table bit each for a leaf, and
  otherwise a block of `stateWidth arity size` bits each. -/
  payload : List Bool

/-- **Unary parameters, raw prefix, leaf flag, raw bit field, then the payload**: `arity`, `size`
and `levels` in unary, `subcube`, `bitField` and `payload` as raw bits, and every field but the
payload framed. -/
enc_structure encQuery : Query where
  arity : encUnary, size : encUnary, subcube : encBits, levels : encUnary, leaf : encBool,
  bitField : encBits, payload : encBits

/-- **The length of a query**: twice its unary parameters, prefix and bit field, plus `8` for
the six frame terminators and the framed leaf flag, plus the payload. -/
theorem length_encQuery (q : Query) :
    (encQuery q).length =
      2 * (q.arity + q.size + q.subcube.length + q.levels + q.bitField.length) + 8 +
        q.payload.length := by
  simp only [encQuery_apply, encQueryFields, length_encPair, encUnary_apply,
    List.length_replicate, encBits_apply, encBool_apply, List.length_singleton]
  ring

/-- The query for bit `j` of the node `p` with `k` merge levels, arity `n`, size bound `s`, leaf
flag `leaf` and payload `v`. Its bit field is the unary field of width `stateWidth n s` for `j`. -/
@[expose] def Query.ofNode (n s : ℕ) (p : List Bool) (k : ℕ) (leaf : Bool) (j : ℕ)
    (v : List Bool) : Query :=
  ⟨n, s, p, k, leaf, unaryField (stateWidth n s) j, v⟩

/-- **A node query is its header followed by its payload**: the encoding of the query with payload
`v` is the encoding of the query with empty payload, followed by `v`. -/
theorem encQuery_ofNode (n s : ℕ) (p : List Bool) (k : ℕ) (leaf : Bool) (j : ℕ) (v : List Bool) :
    encQuery (Query.ofNode n s p k leaf j v) = encQuery (Query.ofNode n s p k leaf j []) ++ v := by
  simp [encQuery_apply, encQueryFields, Query.ofNode]

/-- **The header length of a node query** for a bit `j ≤ stateWidth n s` does not depend on `j`. -/
theorem length_encQuery_ofNode (n s : ℕ) (p : List Bool) (k : ℕ) (leaf : Bool) {j : ℕ}
    (hj : j ≤ stateWidth n s) :
    (encQuery (Query.ofNode n s p k leaf j [])).length =
      2 * (n + s + p.length + k + stateWidth n s) + 8 := by
  rw [length_encQuery]
  simp [Query.ofNode, hj]

/-- The state of child `e` of a node with prefix `p`, `k` merge levels and payload `v`: for a leaf,
the point state of `p ++ e` for table bit `equivFin k e`; otherwise the block of `stateWidth n s`
payload bits starting at `equivFin k e · stateWidth n s`. Missing bits read as `false`. -/
noncomputable def childState (n s : ℕ) (p : List Bool) (k : ℕ) (leaf : Bool) (v : List Bool)
    (e : BitString k) : BitString (stateWidth n s) :=
  if leaf then pointState n s (p ++ List.ofFn e) (v.getD (BitString.equivFin k e) false)
  else fun i => v.getD (BitString.equivFin k e * stateWidth n s + i) false

/-- The answer to a query: bit `j` of the `levels`-fold merge of its children under
`mergeLanguage`, where `j` is the number of `true` bits of the bit field, or `false` when
`j ≥ stateWidth arity size`. -/
noncomputable def Query.answer (q : Query) : Bool :=
  if hj : q.bitField.count true < stateWidth q.arity q.size then
    iterMergeVec mergeLanguage q.arity q.size q.subcube q.levels
      (childState q.arity q.size q.subcube q.levels q.leaf q.payload) ⟨_, hj⟩
  else false

/-- **The merge-tree oracle**: the encodings of the queries whose answer is `true`. It is one
language for every arity `n` and size bound `s`, since every query carries them, so it can be
fixed before `n`.

It is derived from `CircuitMinMergeLanguage`: a query asks for a bit of `k` levels of its merge
step (`Cslib.MCSP.iterMergeVec` of `Cslib.MCSP.mergeVec` under `Cslib.MCSP.mergeLanguage`), on
`2 ^ k` child states, or, at a leaf, on the point states of `2 ^ k` table bits. Querying
`CircuitMinMergeLanguage` itself, one binary merge per oracle gate, gives only the binary-tree
parameters. No bound on the complexity of this language is claimed.

A single root leaf query with `k = n` already decides `MCSP[s]`
(`Cslib.MCSP.MergeTree.encQuery_ofNode_nil_mem_oracle_iff_leaf`), so the content of the
\[MMW19\] bullet lies in the oracle-gate, fan-in and adaptivity bounds of the circuit built from
these queries, not in the oracle. -/
def oracle : Language Bool :=
  {w | ∃ q : Query, q.answer = true ∧ encQuery q = w}

/-- The oracle decides the queries answering yes. -/
theorem encQuery_mem_oracle_iff (q : Query) : encQuery q ∈ oracle ↔ q.answer = true :=
  ⟨fun ⟨_, hq, h⟩ => encQuery.injective h ▸ hq, fun hq => ⟨q, hq, rfl⟩⟩

/-- A node query for bit `j < stateWidth n s` answers bit `j` of the merge of its children. -/
theorem answer_ofNode {n s : ℕ} (p : List Bool) (k : ℕ) (leaf : Bool) (j : Fin (stateWidth n s))
    (v : List Bool) :
    (Query.ofNode n s p k leaf j v).answer =
      iterMergeVec mergeLanguage n s p k (childState n s p k leaf v) j := by
  have hj : (unaryField (stateWidth n s) j).count true < stateWidth n s := by
    rw [count_unaryField]
    exact j.isLt
  unfold Query.answer Query.ofNode
  simp only [hj, ↓reduceDIte]
  congr 1
  exact Fin.ext (count_unaryField _ _)

/-! ### Correctness of node queries -/

/-- **An inner node.** If block `equivFin k e` of the payload `v` holds the state of the subcube
`p ++ e` for every `e ∈ {0, 1} ^ k`, where `p ++ e` has at most `n` bits, then the node query for
bit `j` is in the oracle exactly when bit `j` of the state of `p` is `true`. -/
theorem encQuery_ofNode_mem_oracle_iff_merge {n s : ℕ} (f : BooleanFunction n) {p : List Bool}
    {k : ℕ} (hpk : p.length + k ≤ n) (j : Fin (stateWidth n s)) {v : List Bool}
    (hv : ∀ (e : BitString k) (i : Fin (stateWidth n s)),
      v.getD (BitString.equivFin k e * stateWidth n s + i) false =
        subcubeState n s f (p ++ List.ofFn e) i) :
    encQuery (Query.ofNode n s p k false j v) ∈ oracle ↔ subcubeState n s f p j = true := by
  rw [encQuery_mem_oracle_iff, answer_ofNode,
    iterMergeVec_eq_subcubeState (fun a => (encMerge_mem_mergeLanguage_iff a).symm) f
      hpk fun e => ?_]
  funext i
  simp only [childState, Bool.false_eq_true, ↓reduceIte]
  exact hv e i

/-- **A leaf.** If bit `equivFin k e` of the payload `v` is the value of `f` at the point `p ++ e`
for every `e ∈ {0, 1} ^ k`, where `p ++ e` has `n` bits, then the node query for bit `j` is in the
oracle exactly when bit `j` of the state of `p` is `true`. -/
theorem encQuery_ofNode_mem_oracle_iff_leaf {n s : ℕ} (f : BooleanFunction n) {p : List Bool}
    {k : ℕ} (hpk : p.length + k = n) (j : Fin (stateWidth n s)) {v : List Bool}
    (hv : ∀ e : BitString k,
      v.getD (BitString.equivFin k e) false = f (BitString.ofList n (p ++ List.ofFn e))) :
    encQuery (Query.ofNode n s p k true j v) ∈ oracle ↔ subcubeState n s f p j = true := by
  rw [encQuery_mem_oracle_iff, answer_ofNode,
    iterMergeVec_eq_subcubeState (fun a => (encMerge_mem_mergeLanguage_iff a).symm) f
      hpk.le fun e => ?_]
  simp only [childState, ↓reduceIte]
  rw [hv, subcubeState_eq_pointState f (by simp only [List.length_append, List.length_ofFn]; omega)]

/-- **The root, as a leaf, answers `MCSP[s]`.** If bit `equivFin n e` of the payload `v` is bit
`equivFin n e` of the truth table `T`, then bit `0` of the root leaf query with `n` levels is the
answer of `MCSP[s]` (`GapMCSP.yesSet s`) on `T`. -/
theorem encQuery_ofNode_nil_mem_oracle_iff_leaf (s : ℕ → ℕ) {n : ℕ} (T : BitString (2 ^ n))
    {v : List Bool} (hv : ∀ e : BitString n, v.getD (BitString.equivFin n e) false =
      T (BitString.equivFin n e)) :
    encQuery (Query.ofNode n (s n) [] n true 0 v) ∈ oracle ↔
      (GapMCSP.yesSet s).slice (2 ^ n) T = true := by
  rw [← subcubeState_nil_zero_eq_slice_yesSet]
  refine encQuery_ofNode_mem_oracle_iff_leaf ((truthTable n).symm T) (p := []) (by simp)
    ⟨0, Nat.succ_pos _⟩ fun e => ?_
  rw [hv, List.nil_append, BitString.ofList_ofFn]
  simp [truthTable]

end MergeTree

end Cslib.MCSP
