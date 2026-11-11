/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.MCSP.Magnification.MergeTree
public import CslibFrontier.Computability.Circuit.Boolean.Oracle.Selection
import CslibFrontier.Computability.Circuit.CompositionDepth
import CslibFrontier.Computability.Circuit.FanIn
import CslibFrontier.Computability.Circuit.Simulation
import CslibFrontier.Foundations.Data.List.Lookup

/-!
# The McKay–Murray–Williams merge tree as an oracle circuit

This module builds the merge tree of [McKayMurrayWilliams2019, Lemma 3.1] as an explicit circuit
over the oracle basis (`Cslib.Circuits.Boolean.oracleSignature`), with the merge-tree oracle
`Cslib.MCSP.MergeTree.oracle` at its oracle gates.

The nodes at level `ℓ` are the subcubes `p`, `|p| = ℓ`, numbered by `BitString.equivFin ℓ`
(`Cslib.MCSP.MergeTree.nodePrefix`). A tree with `j` merge levels of `k` bits
(`Cslib.MCSP.MergeTree.tree`) has its leaves at level `ℓ + j k`, each one oracle gate per
state bit reading `2 ^ (n - ℓ - j k)` table bits; every merge level above asks, for each node
and state bit, one oracle gate reading the `2 ^ k` child states. A layer is
`Cslib.Circuits.Boolean.queryLayer` on `Cslib.Circuits.Boolean.constLayer`, and layers are joined
by `Circuit.comp`. Every oracle gate asks a node query (`Cslib.MCSP.MergeTree.Query.ofNode`): a
constant header, then payload wires.

The output gates are chosen by a map `out : Fin N → Fin (2 ^ ℓ) × Fin (stateWidth n s)`, so the
root circuit (`Cslib.MCSP.MergeTree.circuit`) computes only bit `0` of the root state, which is
the answer of `MCSP[s]` (`Cslib.MCSP.MergeTree.eval_circuit`). Its counts are exact:
`1 + W · ∑_{i < j} 2 ^ ((i + 1) k)` oracle gates, where `W = stateWidth n s`, two constant gates
per layer, at most `j + 1` oracle gates on any path, and fan-in at most the header length plus
`max (2 ^ (n - j k)) (2 ^ k · W)`.

The McKay–Murray–Williams parameters (`Cslib.MCSP.MergeTree.mmwCircuit`) take `k = ⌊log₂ s⌋`
and as many levels as leave every leaf at least `2 ^ (3 k) > s ³ / 8` points (when `3 k ≤ n`;
otherwise the circuit is a single leaf). For `2 ≤ s` and `n ≤ s`, with `N = 2 ^ n`, the circuit
has at most `1 + 128 N / s` oracle gates, at most `3 + 129 N / s` gates, fan-in at most `12 s ⁴`
and adaptivity at most `n / ⌊log₂ s⌋ + 1`. The gate counts are `O(N / s)` once `s ≤ N`, which
holds in the bullet's regime `s ≤ N / poly(n)`. So it is an
`[O(N / s), O(s ⁴), O(n / log s)]–Circuit[O(N / s)]` circuit for `MCSP[s]`. The \[MMW19\] bullet
of [ChenHiraharaOliveiraPichRajgopalSanthanam2020, Proposition 63] asks for
`[O(N / poly(s)), poly(s), O(n / log s)]–Circuit[N / poly(s)]`; this is `poly(s) = s` in the
counts and `s ⁴` in the fan-in. The oracle is the derived merge-tree oracle; as Definition 62
allows, no bound on its complexity is claimed.

## Main definitions

* `Cslib.MCSP.MergeTree.nodePrefix`: the prefix of node `a` at level `ℓ`.
* `Cslib.MCSP.MergeTree.layer`: one oracle gate per output, each asking a node query.
* `Cslib.MCSP.MergeTree.tree`: the merge tree with `j` merge levels below level `ℓ`.
* `Cslib.MCSP.MergeTree.circuit`: the root tree, computing bit `0` of the root state.
* `Cslib.MCSP.MergeTree.mmwCircuit`: the circuit with the McKay–Murray–Williams parameters.

## Main results

* `Cslib.MCSP.MergeTree.eval_tree`: every output of the tree is its bit of the state of its node.
* `Cslib.MCSP.MergeTree.eval_circuit`: the root circuit decides `MCSP[s]`.
* `Cslib.MCSP.MergeTree.cost_program_circuit`, `Cslib.MCSP.MergeTree.size_circuit`,
  `Cslib.MCSP.MergeTree.depthWith_circuit_le`, `Cslib.MCSP.MergeTree.fanInAtMost_circuit`: exact
  oracle-gate and gate counts, adaptivity and fan-in.
* `Cslib.MCSP.MergeTree.eval_mmwCircuit`, `Cslib.MCSP.MergeTree.mul_cost_program_mmwCircuit_le`,
  `Cslib.MCSP.MergeTree.mul_size_mmwCircuit_le`, `Cslib.MCSP.MergeTree.depthWith_mmwCircuit_le`,
  `Cslib.MCSP.MergeTree.fanInAtMost_mmwCircuit`: the \[MMW19\] bullet of
  [ChenHiraharaOliveiraPichRajgopalSanthanam2020, Proposition 63], with explicit constants.

## References

* [D. McKay, C. D. Murray, R. R. Williams, *Weak Lower Bounds on Resource-Bounded Compression
  Imply Strong Separations of Complexity Classes*][McKayMurrayWilliams2019]
* [L. Chen, S. Hirahara, I. C. Oliveira, J. Pich, N. Rajgopal, R. Santhanam, *Beyond natural
  proofs: hardness magnification and locality*][ChenHiraharaOliveiraPichRajgopalSanthanam2020]
-/

public section

namespace Cslib.MCSP.MergeTree

open Circuits Circuits.Boolean Turing.MultiTapeTM

/-! ### Nodes -/

/-- The prefix of node `a` at level `ℓ`: the `ℓ` bits numbered `a` by `BitString.equivFin ℓ`. -/
def nodePrefix (ℓ : ℕ) (a : Fin (2 ^ ℓ)) : List Bool :=
  List.ofFn ((BitString.equivFin ℓ).symm a)

@[simp] theorem length_nodePrefix (ℓ : ℕ) (a : Fin (2 ^ ℓ)) : (nodePrefix ℓ a).length = ℓ := by
  simp [nodePrefix]

/-- Child `e ∈ {0, 1} ^ k` of node `a` at level `ℓ`: the node at level `ℓ + k` whose prefix is that
of `a` followed by `e`. -/
def childNode (ℓ k : ℕ) (a : Fin (2 ^ ℓ)) (e : BitString k) : Fin (2 ^ (ℓ + k)) :=
  BitString.equivFin (ℓ + k) (Fin.append ((BitString.equivFin ℓ).symm a) e)

theorem nodePrefix_childNode (ℓ k : ℕ) (a : Fin (2 ^ ℓ)) (e : BitString k) :
    nodePrefix (ℓ + k) (childNode ℓ k a e) = nodePrefix ℓ a ++ List.ofFn e := by
  simp [nodePrefix, childNode, List.ofFn_fin_append]

/-! ### Layers of node queries -/

/-- The header length `2 (n + s + ℓ + k + stateWidth n s) + 8` of a node query at level `ℓ` with
`k` merge levels (`Cslib.MCSP.MergeTree.length_encQuery_ofNode`). -/
abbrev headerLength (n s ℓ k : ℕ) : ℕ := 2 * (n + s + ℓ + k + stateWidth n s) + 8

/-- The sources of a node query: the constant header of the query for bit `j` of node `p` at level
`ℓ`, then the payload wires `w`. -/
noncomputable def querySources {K P : ℕ} (n s ℓ : ℕ) (p : List Bool) (k : ℕ) (leaf : Bool)
    (j : ℕ) (w : Fin P → Fin K) : Fin (headerLength n s ℓ k + P) → Source K :=
  Fin.append (Sum.inr ∘ BitString.ofList _ (encQuery (Query.ofNode n s p k leaf j [])))
    (Sum.inl ∘ w)

/-- The sources of a node query read the node query with payload `x ∘ w`. -/
theorem ofFn_substitute_querySources {K P : ℕ} (n s ℓ : ℕ) {p : List Bool} (hp : p.length = ℓ)
    (k : ℕ) (leaf : Bool) (j : Fin (stateWidth n s)) (w : Fin P → Fin K) (x : BitString K) :
    List.ofFn (substitute (querySources n s ℓ p k leaf j w) x) =
      encQuery (Query.ofNode n s p k leaf j (List.ofFn (x ∘ w))) := by
  have hsub : substitute (querySources n s ℓ p k leaf j w) x =
      Fin.append (BitString.ofList _ (encQuery (Query.ofNode n s p k leaf j []))) (x ∘ w) := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      simp [substitute, querySources]
  rw [hsub, List.ofFn_fin_append, BitString.ofFn_ofList, ← encQuery_ofNode]
  rw [length_encQuery_ofNode _ _ _ _ _ j.isLt.le, hp]

/-- One oracle gate for each output `o`, asking the node query for bit `(out o).2` of node
`(out o).1` at level `ℓ`, with payload wires `w (out o).1`. -/
noncomputable def layer {K P N : ℕ} (n s ℓ k : ℕ) (leaf : Bool)
    (out : Fin N → Fin (2 ^ ℓ) × Fin (stateWidth n s)) (w : Fin (2 ^ ℓ) → Fin P → Fin K) :
    Circuit oracleSignature K N :=
  (queryLayer fun o => querySources n s ℓ (nodePrefix ℓ (out o).1) k leaf (out o).2
    (w (out o).1)).comp (constLayer K)

theorem eval_layer {K P N : ℕ} (n s ℓ k : ℕ) (leaf : Bool)
    (out : Fin N → Fin (2 ^ ℓ) × Fin (stateWidth n s)) (w : Fin (2 ^ ℓ) → Fin P → Fin K)
    (x : BitString K) (o : Fin N) :
    (layer n s ℓ k leaf out w).eval (oracleInterpretation oracle) x o = true ↔
      encQuery (Query.ofNode n s (nodePrefix ℓ (out o).1) k leaf (out o).2
        (List.ofFn (x ∘ w (out o).1))) ∈ oracle := by
  rw [layer, Circuit.eval_comp, eval_queryLayer, Language.slice_eq_true_iff,
    ofFn_substitute_querySources _ _ _ (length_nodePrefix ℓ _)]

@[simp] theorem cost_program_layer {K P N : ℕ} (n s ℓ k : ℕ) (leaf : Bool)
    (out : Fin N → Fin (2 ^ ℓ) × Fin (stateWidth n s)) (w : Fin (2 ^ ℓ) → Fin P → Fin K) :
    (layer n s ℓ k leaf out w).program.cost OracleOp.queryWeight = N := by
  rw [layer, Circuit.cost_program_comp, cost_program_constLayer, cost_program_queryLayer,
    Nat.zero_add]

@[simp] theorem size_layer {K P N : ℕ} (n s ℓ k : ℕ) (leaf : Bool)
    (out : Fin N → Fin (2 ^ ℓ) × Fin (stateWidth n s)) (w : Fin (2 ^ ℓ) → Fin P → Fin K) :
    (layer n s ℓ k leaf out w).size = N + 2 := by
  simp [layer, Nat.add_comm]

theorem depthWith_layer_le {K P N : ℕ} (n s ℓ k : ℕ) (leaf : Bool)
    (out : Fin N → Fin (2 ^ ℓ) × Fin (stateWidth n s)) (w : Fin (2 ^ ℓ) → Fin P → Fin K) :
    (layer n s ℓ k leaf out w).depthWith OracleOp.queryWeight ≤ 1 :=
  (Circuit.depthWith_comp_le _ _ _).trans (by simpa using depthWith_queryLayer_le _)

theorem fanInAtMost_layer {K P N : ℕ} (n s ℓ k : ℕ) (leaf : Bool)
    (out : Fin N → Fin (2 ^ ℓ) × Fin (stateWidth n s)) (w : Fin (2 ^ ℓ) → Fin P → Fin K) :
    (layer n s ℓ k leaf out w).FanInAtMost (headerLength n s ℓ k + P) :=
  (fanInAtMost_queryLayer _).comp (fanInAtMost_constLayer _ _)

/-! ### Leaves and merges -/

/-- Point `e ∈ {0, 1} ^ (n - ℓ)` of the leaf `a` at level `ℓ ≤ n`: the table bit of the input whose
first `ℓ` bits are the prefix of `a` and whose other bits are `e`. -/
def leafWire (n ℓ : ℕ) (a : Fin (2 ^ ℓ)) (i : Fin (2 ^ (n - ℓ))) : Fin (2 ^ n) :=
  BitString.equivFin n (BitString.ofList n (nodePrefix ℓ a ++
    List.ofFn ((BitString.equivFin (n - ℓ)).symm i)))

/-- Bit `b` of child `c` of node `a`, at payload position `b + W c` (`finProdFinEquiv`), is bit `b`
of the state of node `childNode ℓ k a c` at level `ℓ + k`. -/
def mergeWire (W ℓ k : ℕ) (a : Fin (2 ^ ℓ)) (i : Fin (2 ^ k * W)) : Fin (2 ^ (ℓ + k) * W) :=
  let cb := finProdFinEquiv.symm i
  finProdFinEquiv (childNode ℓ k a ((BitString.equivFin k).symm cb.1), cb.2)

/-- **The merge tree** with `j` merge levels of `k` bits below level `ℓ`, on the `2 ^ n`-bit truth
table, computing bit `(out o).2` of the state of node `(out o).1` at level `ℓ` at output `o`. The
leaves are at level `ℓ + j k` and read `2 ^ (n - ℓ - j k)` table bits each. -/
noncomputable def tree (n s k : ℕ) :
    (j ℓ N : ℕ) → (Fin N → Fin (2 ^ ℓ) × Fin (stateWidth n s)) →
      Circuit oracleSignature (2 ^ n) N
  | 0, ℓ, _, out => layer n s ℓ (n - ℓ) true out (leafWire n ℓ)
  | j + 1, ℓ, _, out =>
    (layer n s ℓ k false out (mergeWire (stateWidth n s) ℓ k)).comp
      (tree n s k j (ℓ + k) _ finProdFinEquiv.symm)

/-- **The merge tree computes the states of its nodes.** If the leaves of `tree n s k j ℓ N out`
are at level `ℓ + j k ≤ n`, then on the truth table `T` its output `o` is bit `(out o).2` of the
state of node `(out o).1` for the function with truth table `T`. -/
theorem eval_tree (s : ℕ → ℕ) {n k : ℕ} (T : BitString (2 ^ n)) :
    ∀ (j ℓ N : ℕ) (out : Fin N → Fin (2 ^ ℓ) × Fin (stateWidth n (s n))),
      ℓ + j * k ≤ n → ∀ o,
        (tree n (s n) k j ℓ N out).eval (oracleInterpretation oracle) T o =
          subcubeState n (s n) ((truthTable n).symm T) (nodePrefix ℓ (out o).1) (out o).2
  | 0, ℓ, N, out, hℓ, o => by
    rw [Bool.eq_iff_iff, tree, eval_layer]
    refine encQuery_ofNode_mem_oracle_iff_leaf _ (by simp; omega) _ fun e => ?_
    rw [List.getD_ofFn, Function.comp_apply, truthTable_symm_apply, leafWire,
      Equiv.symm_apply_apply]
  | j + 1, ℓ, N, out, hℓ, o => by
    have hℓ' : ℓ + k + j * k ≤ n := by rw [Nat.add_mul, Nat.one_mul] at hℓ; omega
    have ih := eval_tree s T j (ℓ + k) _ finProdFinEquiv.symm hℓ'
    rw [Bool.eq_iff_iff, tree, Circuit.eval_comp, eval_layer]
    refine encQuery_ofNode_mem_oracle_iff_merge _
      (by rw [length_nodePrefix]; omega) _ fun e b => ?_
    have hi : (BitString.equivFin k e : ℕ) * stateWidth n (s n) + b < 2 ^ k * stateWidth n (s n) :=
      calc (BitString.equivFin k e : ℕ) * stateWidth n (s n) + b
          < (BitString.equivFin k e + 1) * stateWidth n (s n) := by rw [Nat.add_mul]; omega
        _ ≤ 2 ^ k * stateWidth n (s n) :=
          Nat.mul_le_mul_right _ (BitString.equivFin k e).isLt
    rw [List.getD_ofFn_of_lt _ hi, Function.comp_apply, ih, mergeWire]
    have hcb : finProdFinEquiv.symm (⟨_, hi⟩ : Fin (2 ^ k * stateWidth n (s n))) =
        (BitString.equivFin k e, b) :=
      finProdFinEquiv.symm_apply_eq.2 (Fin.ext (by simp only [finProdFinEquiv_apply_val]; ring))
    simp only [hcb, Equiv.symm_apply_apply, nodePrefix_childNode]

/-- **The merge-tree circuit for `MCSP[s]`**: the tree with `j` merge levels of `k` bits below the
root, computing bit `0` of the root state. -/
noncomputable def circuit (n s k j : ℕ) : Circuit oracleSignature (2 ^ n) 1 :=
  tree n s k j 0 1 fun _ => (0, ⟨0, Nat.succ_pos _⟩)

/-- **The merge-tree circuit decides `MCSP[s]`**: if `j k ≤ n`, then under the merge-tree oracle it
computes the `2 ^ n`-bit slice of `GapMCSP.yesSet s`. -/
theorem eval_circuit (s : ℕ → ℕ) {n k j : ℕ} (hjk : j * k ≤ n) (T : BitString (2 ^ n)) :
    (circuit n (s n) k j).eval (oracleInterpretation oracle) T 0 =
      (GapMCSP.yesSet s).slice (2 ^ n) T := by
  rw [circuit, eval_tree s T j 0 1 _ (by omega)]
  exact subcubeState_nil_zero_eq_slice_yesSet s n T

/-! ### Counts -/

theorem cost_program_tree (n s k : ℕ) :
    ∀ (j ℓ N : ℕ) (out : Fin N → Fin (2 ^ ℓ) × Fin (stateWidth n s)),
      (tree n s k j ℓ N out).program.cost OracleOp.queryWeight =
        N + stateWidth n s * ∑ i ∈ Finset.range j, 2 ^ (ℓ + (i + 1) * k)
  | 0, ℓ, N, out => by simp [tree]
  | j + 1, ℓ, N, out => by
    rw [tree, Circuit.cost_program_comp, cost_program_tree n s k j, cost_program_layer,
      Finset.sum_range_succ']
    have h (i : ℕ) : ℓ + k + (i + 1) * k = ℓ + (i + 1 + 1) * k := by ring
    simp only [h, zero_add, one_mul]
    ring

theorem size_tree (n s k : ℕ) :
    ∀ (j ℓ N : ℕ) (out : Fin N → Fin (2 ^ ℓ) × Fin (stateWidth n s)),
      (tree n s k j ℓ N out).size =
        N + stateWidth n s * ∑ i ∈ Finset.range j, 2 ^ (ℓ + (i + 1) * k) + 2 * (j + 1)
  | 0, ℓ, N, out => by simp [tree]
  | j + 1, ℓ, N, out => by
    rw [tree, Circuit.size_comp, size_tree n s k j, size_layer, Finset.sum_range_succ']
    have h (i : ℕ) : ℓ + k + (i + 1) * k = ℓ + (i + 1 + 1) * k := by ring
    simp only [h, zero_add, one_mul]
    ring

theorem depthWith_tree_le (n s k : ℕ) :
    ∀ (j ℓ N : ℕ) (out : Fin N → Fin (2 ^ ℓ) × Fin (stateWidth n s)),
      (tree n s k j ℓ N out).depthWith OracleOp.queryWeight ≤ j + 1
  | 0, ℓ, N, out => depthWith_layer_le _ _ _ _ _ _ _
  | j + 1, ℓ, N, out =>
    (Circuit.depthWith_comp_le _ _ _).trans
      (Nat.add_le_add (depthWith_layer_le _ _ _ _ _ _ _) (depthWith_tree_le n s k j _ _ _)) |>.trans
      (by omega)

theorem fanInAtMost_tree (n s k : ℕ) :
    ∀ (j ℓ N : ℕ) (out : Fin N → Fin (2 ^ ℓ) × Fin (stateWidth n s)),
      ℓ + j * k ≤ n →
        (tree n s k j ℓ N out).FanInAtMost
          (headerLength n s n n + max (2 ^ (n - ℓ - j * k)) (2 ^ k * stateWidth n s))
  | 0, ℓ, N, out, hℓ => by
    refine (fanInAtMost_layer _ _ _ _ _ _ _).mono ?_
    simp only [Nat.zero_mul, Nat.sub_zero]
    exact Nat.add_le_add (by unfold headerLength; omega) (le_max_left _ _)
  | j + 1, ℓ, N, out, hℓ => by
    have hk : ℓ + k ≤ n := by rw [Nat.add_mul, Nat.one_mul] at hℓ; omega
    refine Circuit.FanInAtMost.comp ((fanInAtMost_layer _ _ _ _ _ _ _).mono ?_) ?_
    · exact Nat.add_le_add (by unfold headerLength; omega) (le_max_right _ _)
    · have h := fanInAtMost_tree n s k j (ℓ + k) _ finProdFinEquiv.symm
        (by rw [Nat.add_mul, Nat.one_mul] at hℓ; omega)
      have he : n - (ℓ + k) - j * k = n - ℓ - (j + 1) * k := by
        rw [Nat.add_mul, Nat.one_mul]; omega
      rwa [he] at h

/-- **Oracle gates of the merge-tree circuit**: `1 + W · ∑_{i < j} 2 ^ ((i + 1) k)`, where
`W = stateWidth n s`. -/
theorem cost_program_circuit (n s k j : ℕ) :
    (circuit n s k j).program.cost OracleOp.queryWeight =
      1 + stateWidth n s * ∑ i ∈ Finset.range j, 2 ^ ((i + 1) * k) := by
  simp [circuit, cost_program_tree]

/-- **Gates of the merge-tree circuit**: its oracle gates and two constant gates per layer. -/
theorem size_circuit (n s k j : ℕ) :
    (circuit n s k j).size =
      1 + stateWidth n s * ∑ i ∈ Finset.range j, 2 ^ ((i + 1) * k) + 2 * (j + 1) := by
  simp [circuit, size_tree]

/-- **Adaptivity of the merge-tree circuit**: at most `j + 1` oracle gates on any path. -/
theorem depthWith_circuit_le (n s k j : ℕ) :
    (circuit n s k j).depthWith OracleOp.queryWeight ≤ j + 1 :=
  depthWith_tree_le _ _ _ _ _ _ _

/-- **Fan-in of the merge-tree circuit**: at most the header length plus the larger of the
`2 ^ (n - j k)` table bits of a leaf and the `2 ^ k` child states of a merge. -/
theorem fanInAtMost_circuit {n s k j : ℕ} (hjk : j * k ≤ n) :
    (circuit n s k j).FanInAtMost
      (headerLength n s n n + max (2 ^ (n - j * k)) (2 ^ k * stateWidth n s)) := by
  have h := fanInAtMost_tree n s k j 0 1 (fun _ => (0, ⟨0, Nat.succ_pos _⟩)) (by omega)
  rwa [Nat.sub_zero] at h

/-! ### The McKay–Murray–Williams parameters -/

/-- The number of merge levels of the McKay–Murray–Williams tree for `MCSP[s]`: with
`k = ⌊log₂ s⌋` bits per level, the largest `m` with `m k ≤ n - 3 k`. When `3 k ≤ n`, each leaf
then reads `2 ^ (n - m k) ≥ 2 ^ (3 k) > s ^ 3 / 8` table bits; otherwise `m = 0` and the single
leaf reads all `2 ^ n`. It is `0` when `s ≤ 1`. -/
def mmwLevels (n s : ℕ) : ℕ := (n - 3 * Nat.log 2 s) / Nat.log 2 s

/-- **The McKay–Murray–Williams circuit for `MCSP[s]`**: `mmwLevels n s` merge levels of
`⌊log₂ s⌋` bits each. -/
noncomputable def mmwCircuit (n s : ℕ) : Circuit oracleSignature (2 ^ n) 1 :=
  circuit n s (Nat.log 2 s) (mmwLevels n s)

private theorem mmwLevels_spec (n s : ℕ) :
    mmwLevels n s * Nat.log 2 s ≤ n - 3 * Nat.log 2 s ∧
      (0 < Nat.log 2 s → n - 3 * Nat.log 2 s < mmwLevels n s * Nat.log 2 s + Nat.log 2 s) :=
  ⟨Nat.div_mul_le_self _ _, fun hk => Nat.lt_div_mul_add hk⟩

private theorem mmwLevels_mul_le (n s : ℕ) : mmwLevels n s * Nat.log 2 s ≤ n := by
  have := (mmwLevels_spec n s).1
  omega

private theorem two_le_of_log_pos {s : ℕ} (hk : 0 < Nat.log 2 s) : 2 ≤ s :=
  (Nat.log_pos_iff.1 hk).1

private theorem mmwLevels_eq_zero_of_log_eq_zero {n s : ℕ} (hk : Nat.log 2 s = 0) :
    mmwLevels n s = 0 := by
  simp [mmwLevels, hk]

/-- `∑_{i < j} 2 ^ ((i + 1) k) ≤ 2 · 2 ^ (j k)` for `k ≥ 1`. -/
private theorem sum_pow_le {k : ℕ} (hk : 1 ≤ k) :
    ∀ j : ℕ, ∑ i ∈ Finset.range j, 2 ^ ((i + 1) * k) ≤ 2 * 2 ^ (j * k)
  | 0 => by simp
  | j + 1 => by
    rw [Finset.sum_range_succ]
    have ih := sum_pow_le hk j
    have h : 2 * 2 ^ (j * k) ≤ 2 ^ ((j + 1) * k) := by
      rw [← Nat.pow_succ']
      exact Nat.pow_le_pow_right (by omega) (by rw [Nat.add_mul, Nat.one_mul]; omega)
    omega

/-- The state width is at most `8 s²` when `n ≤ s` and `2 ≤ s`. -/
private theorem stateWidth_le {n s : ℕ} (hns : n ≤ s) (hs : 2 ≤ s) :
    stateWidth n s ≤ 8 * s ^ 2 := by
  unfold stateWidth certLength
  have h1 : s * (3 + 2 * (n + s)) ≤ s * (3 + 4 * s) := Nat.mul_le_mul_left _ (by omega)
  nlinarith

/-- **Oracle gates of the McKay–Murray–Williams circuit**: `O(N / s)`, namely
`s · q ≤ s + 128 · 2 ^ n` for `q` oracle gates, when `n ≤ s`. -/
theorem mul_cost_program_mmwCircuit_le {n s : ℕ} (hns : n ≤ s) :
    s * (mmwCircuit n s).program.cost OracleOp.queryWeight ≤ s + 128 * 2 ^ n := by
  rw [mmwCircuit, cost_program_circuit, Nat.mul_add, Nat.mul_one]
  refine Nat.add_le_add_left ?_ _
  rcases Nat.eq_zero_or_pos (mmwLevels n s) with hm | hm
  · simp [hm]
  have hk : 0 < Nat.log 2 s := Nat.pos_of_ne_zero fun hk => by
    simp [mmwLevels_eq_zero_of_log_eq_zero hk] at hm
  have hs := two_le_of_log_pos hk
  have hW := stateWidth_le hns hs
  have hspec := (mmwLevels_spec n s).1
  have hsk : s ≤ 2 ^ (Nat.log 2 s + 1) := (Nat.lt_pow_succ_log_self (by norm_num) s).le
  generalize Nat.log 2 s = k at *
  generalize mmwLevels n s = m at *
  have hmk : k ≤ m * k := Nat.le_mul_of_pos_left _ hm
  have hs3 : s ^ 3 ≤ 8 * 2 ^ (3 * k) :=
    calc s ^ 3 ≤ (2 ^ (k + 1)) ^ 3 := Nat.pow_le_pow_left hsk 3
      _ = 8 * 2 ^ (3 * k) := by ring
  have hpow : 2 ^ (m * k) * 2 ^ (3 * k) ≤ 2 ^ n := by
    rw [← Nat.pow_add]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  calc s * (stateWidth n s * ∑ i ∈ Finset.range m, 2 ^ ((i + 1) * k))
      ≤ s * (8 * s ^ 2 * (2 * 2 ^ (m * k))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul hW (sum_pow_le hk m))
    _ = 16 * s ^ 3 * 2 ^ (m * k) := by ring
    _ ≤ 16 * (8 * 2 ^ (3 * k)) * 2 ^ (m * k) := by gcongr
    _ = 128 * (2 ^ (m * k) * 2 ^ (3 * k)) := by ring
    _ ≤ 128 * 2 ^ n := Nat.mul_le_mul_left _ hpow

/-- The constant gates of the McKay–Murray–Williams circuit beyond the root are few:
`2 s m ≤ 2 ^ n` for `m = mmwLevels n s`, since `s < 2 ^ (k + 1)`, `m < 2 ^ (m k)` and
`m k + k + 2 ≤ n` when `m ≥ 1`. -/
private theorem two_mul_mul_mmwLevels_le (n s : ℕ) : 2 * (s * mmwLevels n s) ≤ 2 ^ n := by
  rcases Nat.eq_zero_or_pos (mmwLevels n s) with hm | hm
  · simp [hm]
  have hk : 0 < Nat.log 2 s := Nat.pos_of_ne_zero fun hk => by
    simp [mmwLevels_eq_zero_of_log_eq_zero hk] at hm
  have hspec := (mmwLevels_spec n s).1
  have hsk : s ≤ 2 ^ (Nat.log 2 s + 1) := (Nat.lt_pow_succ_log_self (by norm_num) s).le
  generalize Nat.log 2 s = k at *
  generalize mmwLevels n s = m at *
  have hmk : k ≤ m * k := Nat.le_mul_of_pos_left _ hm
  have hm2 : m ≤ 2 ^ (m * k) :=
    Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right _ hk))
  calc 2 * (s * m) ≤ 2 * (2 ^ (k + 1) * 2 ^ (m * k)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul hsk hm2)
    _ = 2 ^ (m * k + k + 2) := by ring
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **Gates of the McKay–Murray–Williams circuit**: `O(N / s)`, namely
`s · size ≤ 129 · 2 ^ n + 3 s`, when `n ≤ s`: the oracle gates, and two constant gates per layer.
-/
theorem mul_size_mmwCircuit_le {n s : ℕ} (hns : n ≤ s) :
    s * (mmwCircuit n s).size ≤ 129 * 2 ^ n + 3 * s := by
  have hc := mul_cost_program_mmwCircuit_le hns
  have hm := two_mul_mul_mmwLevels_le n s
  have hsize : (mmwCircuit n s).size =
      (mmwCircuit n s).program.cost OracleOp.queryWeight + 2 * (mmwLevels n s + 1) := by
    rw [mmwCircuit, cost_program_circuit, size_circuit]
  rw [hsize]
  generalize (mmwCircuit n s).program.cost OracleOp.queryWeight = q at *
  have h2 : s * (q + 2 * (mmwLevels n s + 1)) = s * q + 2 * (s * mmwLevels n s) + 2 * s := by
    ring
  omega

/-- **Adaptivity of the McKay–Murray–Williams circuit**: at most `n / ⌊log₂ s⌋ + 1` oracle gates
on any path. -/
theorem depthWith_mmwCircuit_le (n s : ℕ) :
    (mmwCircuit n s).depthWith OracleOp.queryWeight ≤ n / Nat.log 2 s + 1 :=
  (depthWith_circuit_le _ _ _ _).trans
    (Nat.add_le_add_right (Nat.div_le_div_right (Nat.sub_le _ _)) _)

/-- **Fan-in of the McKay–Murray–Williams circuit**: at most `12 s ⁴` when `n ≤ s` and `2 ≤ s`:
a leaf reads fewer than `2 ^ (4 ⌊log₂ s⌋) ≤ s ⁴` table bits and a merge `2 ^ ⌊log₂ s⌋` states of
`O(s ²)` bits, after an `O(s ²)`-bit header. -/
theorem fanInAtMost_mmwCircuit {n s : ℕ} (hns : n ≤ s) (hs : 2 ≤ s) :
    (mmwCircuit n s).FanInAtMost (12 * s ^ 4) := by
  refine (fanInAtMost_circuit (mmwLevels_mul_le n s)).mono ?_
  have hk : 0 < Nat.log 2 s := Nat.log_pos (by norm_num) hs
  have hspec := (mmwLevels_spec n s).2 hk
  have hks : 2 ^ Nat.log 2 s ≤ s := Nat.pow_log_le_self 2 (by omega)
  have hW := stateWidth_le hns hs
  generalize Nat.log 2 s = k at *
  generalize mmwLevels n s = m at *
  have hleaf : 2 ^ (n - m * k) ≤ s ^ 4 :=
    calc 2 ^ (n - m * k) ≤ 2 ^ (4 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = (2 ^ k) ^ 4 := by ring
      _ ≤ s ^ 4 := Nat.pow_le_pow_left hks 4
  have h2 : s ≤ s ^ 2 := by nlinarith
  have h4' : 4 ≤ s ^ 2 := by nlinarith
  have h4 : 4 * s ^ 2 ≤ s ^ 4 :=
    calc 4 * s ^ 2 ≤ s ^ 2 * s ^ 2 := Nat.mul_le_mul_right _ h4'
      _ = s ^ 4 := by ring
  have hmerge : 2 ^ k * stateWidth n s ≤ 4 * s ^ 4 :=
    calc 2 ^ k * stateWidth n s ≤ s * (8 * s ^ 2) := Nat.mul_le_mul hks hW
      _ = 8 * s ^ 3 := by ring
      _ ≤ 4 * s ^ 4 := by nlinarith
  have hmax : max (2 ^ (n - m * k)) (2 ^ k * stateWidth n s) ≤ 4 * s ^ 4 :=
    max_le (hleaf.trans (by omega)) hmerge
  have hhead : headerLength n s n n ≤ 8 * s ^ 4 := by
    unfold headerLength
    omega
  omega

/-- **The McKay–Murray–Williams circuit decides `MCSP[s]`** under the merge-tree oracle. -/
theorem eval_mmwCircuit (s : ℕ → ℕ) (n : ℕ) (T : BitString (2 ^ n)) :
    (mmwCircuit n (s n)).eval (oracleInterpretation oracle) T 0 =
      (GapMCSP.yesSet s).slice (2 ^ n) T :=
  eval_circuit s (mmwLevels_mul_le n (s n)) T

end Cslib.MCSP.MergeTree
