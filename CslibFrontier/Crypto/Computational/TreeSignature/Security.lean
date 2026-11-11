/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.TreeSignature.CoinHybrid
public import CslibFrontier.Crypto.Computational.CollisionResistant
public import CslibFrontier.Crypto.Computational.OneWay
public import CslibFrontier.Crypto.Negligible.Dyadic
public import CslibFrontier.Languages.Probabilistic.Repeat
public import CslibFrontier.Languages.Probabilistic.UniformNat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Frame
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Oracle.Memoize
import CslibFrontier.Computability.Probabilistic.Oracle.Substitution
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.QueryBounds
import CslibFrontier.Computability.Probabilistic.Repeat
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Probabilistic.UniformNat
import CslibFrontier.Crypto.Computational.MerkleSignature.Security
import CslibFrontier.Crypto.Computational.OneWayToPRF
import CslibFrontier.Foundations.Data.List.GetD
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Languages.Probabilistic.Oracle.Support
import CslibFrontier.Languages.Probabilistic.RandomOracle.Probabilistic
import CslibFrontier.Languages.Probabilistic.UntilBad
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.BindFailure
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Tactic.Negligible

/-!
# Security of stateless tree signatures

Stateless EUF-CMA security ([BonehShoup2023], Section 14.6.3, Theorem 14.6) for
`TreeSignature.scheme`: combining an indexed EUF-CMA secure signature scheme `S` of capacity at
least `2` with a pseudorandom function `F` yields a stateless many-time signature scheme.

Starting from `treeGame` (`TreeSignature.scheme`'s `eufCmaGame`), the reduction proceeds in two
steps after replacing `prfCoins F` with a uniform random function (`treeIdealGame`, proved in
`CslibFrontier.Crypto.Computational.TreeSignature.CoinHybrid`):

1. **Lazy node keys and edge signatures without leaf collisions** (`lazyTreeGame`): when `N n`
   exceeds all coin-request lengths (`2 * depth n + 4 ≤ N n`) and all seeded key/signature coin
   budgets on supported keys and messages, distinct tree nodes and `(node, bit)` edges pad to
   distinct random-function inputs. Guarding against repeated leaves across `Q` signing queries adds
   at most `(Q ^ 2 : ℝ≥0) / 2 ^ (depth n + 1)` by `OracleComp.IdenticalUntilBad`, and on good runs
   every node key is distributed as `S.keyGen n` and every edge signature as `S.sign`.
2. **Reduction to indexed forgery** (`indexedForger`): pre-sampling `dyadicSize (slotBound n)` node
   keys and planting the indexed challenge verification key at a uniform dyadic slot `target`
   simulates `lazyTreeGame` exactly whenever `Q * depth n ≤ slotBound n`. Any valid tree forgery on
   a fresh `n`-bit message diverges from the visited tree or forges at a leaf parent, yielding a
   valid indexed forgery at the deepest matching visited node along the forged path.

Combining this upgrade with `OneWay.exists_pseudorandomFunction` and `OneWay.exists_indexedEUFCMA`
constructs a stateless EUF-CMA secure signature scheme from a one-way function and a
collision-resistant hash family (`OneWay.exists_eufCMA_of_hashFamily`); removing the
collision-resistant hash family assumption requires universal one-way hash functions
([Rompel1990]).

## Main definitions

* `Cslib.Crypto.TreeSignature.lazyTreeGame`: intermediate tree forging game with lazy node keys,
  lazy edge signatures, and leaf-collision abort.
* `Cslib.Crypto.TreeSignature.plantNodeKeys`, `Cslib.Crypto.TreeSignature.plantedTreeHandler`,
  `Cslib.Crypto.TreeSignature.extractForgery`, `Cslib.Crypto.TreeSignature.indexedForgerAt`,
  `Cslib.Crypto.TreeSignature.indexedForger`: the reduction from stateless tree forgery to indexed
  forgery.

## Main results

* `Cslib.Crypto.TreeSignature.exists_treeCoinBudget`: polynomial-time unary coin budget covering
  all tree request widths and seeded key/signature budgets.
* `Cslib.Crypto.TreeSignature.isOraclePPT_indexedForger`: `indexedForger` is uniformly strict
  oracle PPT for every oracle-PPT tree forger.
* `Cslib.Crypto.TreeSignature.succProbability_treeIdealGame_le_lazy`,
  `Cslib.Crypto.TreeSignature.succProbability_lazyTreeGame_le`,
  `Cslib.Crypto.TreeSignature.succProbability_treeIdealGame_le`,
  `Cslib.Crypto.TreeSignature.succProbability_eufCmaGame_scheme_le`: concrete Theorem 14.6
  security bounds for `treeIdealGame`, `lazyTreeGame`, and `TreeSignature.scheme`.
* `Cslib.Crypto.TreeSignature.eufCMA_scheme_of_inv`,
  `Cslib.Crypto.TreeSignature.eufCMA_scheme`: stateless EUF-CMA security of `TreeSignature.scheme`
  from `IndexedEUFCMA` and `PseudorandomFunction`.
* `Cslib.Crypto.IndexedSignatureScheme.IndexedEUFCMA.exists_eufCMA_of_prf`,
  `Cslib.Crypto.IndexedSignatureScheme.IndexedEUFCMA.exists_eufCMA_of_oneWay`,
  `Cslib.Crypto.OneWay.exists_eufCMA_of_hashFamily`: existential upgrades from indexed signatures
  and from a one-way function plus a collision-resistant hash family.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 14.6.3, Theorem 14.6.
* [J. Rompel, *One-Way Functions are Necessary and Sufficient for Secure Signatures*][Rompel1990].
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

namespace TreeSignature

attribute [local fun_prop]
  ComputableInPolyTime.bool_and'
  ComputableInPolyTime.unary_dyadicSize
  IsPPTOn.replicate

@[local fun_prop]
private theorem headD_list_fp {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {l : α → List β} (hl : ComputableInPolyTime l encA (encList encB)) (d : β) :
    ComputableInPolyTime (fun a => (l a).headD d) encA encB :=
  (ComputableInPolyTime.headD (encA := encB) (encL := encList encB) d).comp hl

@[local fun_prop]
private theorem getLastD_fp {α : Type} {encA : α ↪ List Bool} {l : α → List Bool} (d : Bool)
    (hl : ComputableInPolyTime l encA encBits) :
    ComputableInPolyTime (fun a => (l a).getLastD d) encA encBool := by
  have heq : (fun a => (l a).getLastD d) = fun a => (l a).getD ((l a).length - 1) d := by
    funext a
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD]
  rw [heq]; fun_prop

@[local fun_prop]
private theorem contains_fp {α β : Type} [BEq β] [LawfulBEq β] {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {l : α → List β} {x : α → β}
    (hl : ComputableInPolyTime l encA (encList encB))
    (hx : ComputableInPolyTime x encA encB) :
    ComputableInPolyTime (fun a => (l a).contains (x a)) encA encBool := by
  have heq : (fun a => (l a).contains (x a)) = fun a => (l a).any (fun b => b == x a) := by
    funext a
    rw [Bool.eq_iff_iff, List.contains_iff_mem, List.any_eq_true]
    simp only [beq_iff_eq, exists_eq_right]
  rw [heq]
  exact ComputableInPolyTime.anyWithInput hl
    ((ComputableInPolyTime.snd encA encB).beq (hx.comp (ComputableInPolyTime.fst encA encB)))

@[local fun_prop]
private theorem encodeSignature_funProp {α : Type} {encA : α ↪ List Bool}
    {leaf : α → List Bool} {certs : α → List (List Bool × List Bool)} {last : α → List Bool}
    (hl : ComputableInPolyTime leaf encA encBits)
    (hc : ComputableInPolyTime certs encA (encList (encPair encBits encBits)))
    (hs : ComputableInPolyTime last encA encBits) :
    ComputableInPolyTime (fun a => encodeSignature (leaf a) (certs a) (last a)) encA encBits := by
  unfold encodeSignature; fun_prop

@[local fun_prop]
private theorem signatureDecoder_funProp {α : Type} {encA : α ↪ List Bool} {s : α → List Bool}
    (hs : ComputableInPolyTime s encA encBits) :
    ComputableInPolyTime (fun a => signatureDecoder.decode (s a)) encA
      (encPair encBits (encPair (encList (encPair encBits encBits)) encBits)) :=
  signatureDecoder.computableInPolyTime.comp hs

private theorem exists_signInput_length_bound (S : IndexedSignatureScheme) :
    ∃ pkB : ℕ → ℕ,
      ComputableInPolyTime pkB encUnary encUnary ∧
      ∀ n, ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
        (msg.length = n ∨ ∃ keys' ∈ (ProbComp.eval (S.keyGen n)).support, msg = keys'.1) →
        (encPair encBits (encPair encUnary encBits) (keys.2, u, msg)).length + 1 ≤
          3 * pkB n + n + 5 := by
  obtain ⟨ck, dk, hkgLen⟩ := S.keyGen_ppt.length_le
  simp only [encUnary_apply, List.length_replicate] at hkgLen
  refine ⟨fun n => ck * (n + 1) ^ dk, by fun_prop, fun n keys hkeys u hu msg hmsg => ?_⟩
  have hskLen : keys.2.length ≤ ck * (n + 1) ^ dk :=
    (length_le_encPair_right encBits encBits keys).trans (hkgLen n keys hkeys)
  have hmsgLen : msg.length ≤ ck * (n + 1) ^ dk + n := by
    rcases hmsg with rfl | ⟨keys', hkeys', rfl⟩
    · omega
    · have hk' := (length_le_encPair_left encBits encBits keys').trans (hkgLen n keys' hkeys')
      simp only [encBits_apply] at hk'
      omega
  simp only [length_encPair, encBits_apply, encUnary_apply, List.length_replicate]
  omega

/-! ### Request lengths, injectivity, and coin budgets -/

section Requests

theorem length_keyInput (path : List Bool) : (keyInput path).length = path.length + 3 := by
  simp only [keyInput, length_encPair, encBool_apply, List.length_singleton, encBits_apply]
  omega

theorem length_signInput (path : List Bool) (u : ℕ) :
    (signInput path u).length = 2 * path.length + u + 4 := by
  simp only [signInput, length_encPair, encBool_apply, List.length_singleton, encBits_apply,
    encUnary_apply, List.length_replicate]
  omega

theorem keyInput_injective : Function.Injective keyInput := by
  intro p q h
  exact (Prod.mk.inj ((encPair encBool encBits).injective h)).2

theorem signInput_injective {p q : List Bool} {u v : ℕ} (h : signInput p u = signInput q v) :
    p = q ∧ u = v :=
  Prod.mk.inj (Prod.mk.inj ((encPair encBool (encPair encBits encUnary)).injective h)).2

theorem keyInput_ne_signInput (p q : List Bool) (u : ℕ) : keyInput p ≠ signInput q u := by
  intro h
  have hu := congrArg unframe h
  simp only [keyInput, signInput, encPair_apply, unframe_frame_append] at hu
  exact Bool.false_ne_true (encBool.injective hu)

theorem padRequest_keyInput_injective {M d : ℕ} (hM : 2 * d + 4 ≤ M) {p q : List Bool}
    (hp : p.length < d) (hq : q.length < d)
    (h : padRequest M (keyInput p) = padRequest M (keyInput q)) : p = q := by
  apply keyInput_injective
  apply padRequest_injective _ _ h
  · rw [length_keyInput]; omega
  · rw [length_keyInput]; omega

theorem padRequest_signInput_injective {M d : ℕ} (hM : 2 * d + 4 ≤ M) {p q : List Bool}
    {u v : ℕ} (hp : p.length < d) (hq : q.length < d) (hu : u ≤ 1) (hv : v ≤ 1)
    (h : padRequest M (signInput p u) = padRequest M (signInput q v)) : p = q ∧ u = v := by
  apply signInput_injective
  apply padRequest_injective _ _ h
  · rw [length_signInput]; omega
  · rw [length_signInput]; omega

theorem padRequest_keyInput_ne_signInput {M d : ℕ} (hM : 2 * d + 4 ≤ M) {p q : List Bool}
    {u : ℕ} (hp : p.length < d) (hq : q.length < d) (hu : u ≤ 1) :
    padRequest M (keyInput p) ≠ padRequest M (signInput q u) := by
  intro h
  apply keyInput_ne_signInput p q u
  apply padRequest_injective _ _ h
  · rw [length_keyInput]; omega
  · rw [length_signInput]; omega

/-- Every seeded indexed signature scheme admits a polynomial-time unary coin budget covering all
tree request widths (`2 * depth n + 4`), key-generation budgets, and signing budgets on supported
keys and messages (`n`-bit messages or supported public keys). -/
theorem exists_treeCoinBudget (S : IndexedSignatureScheme) (T : S.Seeded) {depth : ℕ → ℕ}
    (hdepth : ComputableInPolyTime depth encUnary encUnary) :
    ∃ budget : ℕ → ℕ,
      ComputableInPolyTime budget encUnary encUnary ∧
      (∀ n, 2 * depth n + 4 ≤ budget n) ∧
      (∀ n, T.keyGenBudget n ≤ budget n) ∧
      ∀ n, ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
        (msg.length = n ∨ ∃ keys' ∈ (ProbComp.eval (S.keyGen n)).support, msg = keys'.1) →
        T.signBudget keys.2 u msg ≤ budget n := by
  obtain ⟨pkB, hpkB, hlenB⟩ := exists_signInput_length_bound S
  obtain ⟨cb, db, hkb⟩ := T.keyGenBudget_polyTime.polyBounded_length.exists_le
  obtain ⟨cB, dB, hsb⟩ := T.signBudget_polyTime.polyBounded_length.exists_le
  simp only [encUnary_apply, List.length_replicate] at hkb hsb
  let budget (n : ℕ) : ℕ :=
    2 * depth n + 4 + cb * (n + 1) ^ db + cB * (3 * pkB n + n + 5) ^ dB
  refine ⟨budget, by dsimp only [budget]; fun_prop, fun n => by dsimp only [budget]; omega,
    fun n => by have := hkb n; dsimp only [budget]; omega,
    fun n keys hkeys u hu msg hmsg => ?_⟩
  have hle := (hsb (keys.2, u, msg)).trans
    (Nat.mul_le_mul_left cB (Nat.pow_le_pow_left (hlenB n keys hkeys u hu msg hmsg) dB))
  dsimp only [budget] at hle ⊢
  omega

end Requests

/-! ### Lazy tree game and reduction to indexed forgery -/

/-- Association-list cache assigning node paths to pre-sampled slot indices. -/
abbrev NodeSlotCache := List (List Bool × ℕ)

/-- Association-list cache memoizing node keys `(pk, sk)` by path. -/
abbrev NodeKeyCache := List (List Bool × (List Bool × List Bool))

/-- Association-list cache memoizing signatures by `(path, u)`. -/
abbrev EdgeSigCache := List ((List Bool × ℕ) × List Bool)

/-- State of the lazy tree signing handler: node keys, edge signatures, queried messages,
sampled leaves, and the leaf-collision abort flag. -/
abbrev LazyTreeState :=
  (NodeKeyCache × EdgeSigCache) × (List (List Bool) × List (List Bool) × Bool)

/-- Chain state during `certifyLazy`. -/
abbrev LazyCertState := CertState × (NodeKeyCache × EdgeSigCache)

/-- One step of lazy certification along `leaf`: memoize the child's key from `S.keyGen n` and
memoize the parent's signature on the child's public key from `S.sign`. -/
@[expose] noncomputable def certifyStepLazy (S : IndexedSignatureScheme) (n : ℕ)
    (leaf : List Bool) (state : LazyCertState) : ProbComp LazyCertState := do
  let ((node, (_, sk), certs), (nodes, edges)) := state
  let bit := leaf.getD node.length false
  let childPath := node ++ [bit]
  let (child, nodes') ← memoize (fun _ => S.keyGen n) childPath nodes
  let (σ, edges') ← memoize (fun _ => S.sign sk bit.toNat child.1) (node, bit.toNat) edges
  return ((childPath, child, certs ++ [(child.1, σ)]), (nodes', edges'))

/-- Lazily certify the path along `leaf` from `root` for `depth n - 1` steps. -/
@[expose] noncomputable def certifyLazy (S : IndexedSignatureScheme) (depth : ℕ → ℕ) (n : ℕ)
    (root : List Bool × List Bool) (leaf : List Bool) (caches : NodeKeyCache × EdgeSigCache) :
    ProbComp LazyCertState :=
  OracleComp.iterate (depth n - 1) (certifyStepLazy S n leaf) (([], root, []), caches)

/-- Signing handler of `lazyTreeGame`: check `msg.length = n`, sample a uniform leaf, abort with
`[]` if a leaf collision occurs (or has already occurred), and otherwise lazily certify the path
and sign `msg`. -/
@[expose] noncomputable def lazySignHandler (S : IndexedSignatureScheme) (depth : ℕ → ℕ) (n : ℕ)
    (root : List Bool × List Bool) (request : Unit × List Bool) :
    StateT LazyTreeState ProbComp (List Bool) := fun state =>
  let msg := request.2
  let ((nodes, edges), (queried, seenLeaves, bad)) := state
  if msg.length = n then
    if bad then
      pure ([], ((nodes, edges), (msg :: queried, seenLeaves, true)))
    else do
      let leaf ← BitString.sampleList (depth n)
      if seenLeaves.contains leaf then
        pure ([], ((nodes, edges), (msg :: queried, seenLeaves, true)))
      else do
        let ((node, (_, sk), certs), (nodes', edges')) ←
          certifyLazy S depth n root leaf (nodes, edges)
        let (σ, edges'') ←
          memoize (fun _ => S.sign sk (leaf.getLastD false).toNat msg)
            (node, (leaf.getLastD false).toNat) edges'
        return (encodeSignature leaf certs σ,
          ((nodes', edges''), (msg :: queried, leaf :: seenLeaves, false)))
  else
    pure ([], ((nodes, edges), (msg :: queried, seenLeaves, bad)))

/-- Intermediate tree forging game ([BonehShoup2023], proof of Theorem 14.6): node keys and
internal/leaf signatures are sampled lazily from `S.keyGen` and `S.sign`, and signing returns `[]`
once any leaf is sampled twice. -/
@[expose] noncomputable def lazyTreeGame (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    (adversary : Forger) (n : ℕ) : ProbComp Bool := do
  let root ← S.keyGen n
  let pk := encPair encUnary encBits (n, root.1)
  let init : LazyTreeState := (([([], root)], []), ([], [], false))
  let (msig, state) ← (OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
      (lazySignHandler S depth n root)) (adversary n pk)).run init
  let (_, (queried, _, _)) := state
  let (msg, sig) := msig
  return (msg.length == n) && !queried.contains msg && verify S depth pk msg sig

/-! ### The planted-node reduction (`indexedForger`) -/

/-- State of `plantedTreeHandler`: visited node-to-slot cache, edge-signature cache, queried
messages, sampled leaves, and the leaf-collision abort flag. -/
abbrev PlantedState :=
  (NodeSlotCache × EdgeSigCache) × (List (List Bool) × List (List Bool) × Bool)

/-- Initial state of `plantedTreeHandler`: the root `[]` occupies slot `0`. -/
@[expose] def initPlantedState : PlantedState :=
  (([([], 0)], []), ([], [], false))

/-- Pre-sample `dyadicSize (slotBound n)` node key pairs, planting `(vk, [])` at `min target
(dyadicSize (slotBound n) - 1)`. -/
@[expose] noncomputable def plantNodeKeys (S : IndexedSignatureScheme) (slotBound : ℕ → ℕ)
    (n target : ℕ) (vk : List Bool) : ProbComp (List (List Bool × List Bool)) := do
  let total := dyadicSize (slotBound n)
  let idx := min target (total - 1)
  let front ← OracleComp.replicate idx (S.keyGen n)
  let back ← OracleComp.replicate (total - idx - 1) (S.keyGen n)
  return front ++ (vk, []) :: back

/-- Assign `path` its cached slot or the next available slot `min visited.length cap`. -/
@[expose] def visitNodeM (cap : ℕ) (path : List Bool) (visited : NodeSlotCache) :
    WordOracleComp Unit (ℕ × NodeSlotCache) :=
  memoize (fun _ => pure (min visited.length cap)) path visited

/-- Produce an edge signature at slot `idx` and index `u` on `msg`, querying the external indexed
signing oracle when `idx = target` and running `S.sign` locally otherwise, capped at `sigCap`
bits. -/
@[expose] noncomputable def signEdgeRaw (S : IndexedSignatureScheme)
    (keys : List (List Bool × List Bool)) (target sigCap idx u : ℕ) (msg : List Bool) :
    WordOracleComp Unit (List Bool) :=
  if idx = target then
    List.take sigCap <$> ProbOracleComp.query ((), encPair encUnary encBits (u, msg))
  else
    List.take sigCap <$> ProbOracleComp.sample (S.sign (keys.getD idx ([], [])).2 u msg)

/-- Memoize `signEdgeRaw` on `(path, u)` in `edges`. -/
@[expose] noncomputable def signEdgeM (S : IndexedSignatureScheme)
    (keys : List (List Bool × List Bool)) (target sigCap : ℕ) (path : List Bool) (idx u : ℕ)
    (msg : List Bool) (edges : EdgeSigCache) :
    WordOracleComp Unit (List Bool × EdgeSigCache) :=
  memoize (fun _ => signEdgeRaw S keys target sigCap idx u msg) (path, u) edges

/-- Chain state during `certifyPlanted`: `(path, slotIdx, certs)` paired with `(visited, edges)`. -/
abbrev PlantedCertState :=
  (List Bool × ℕ × List (List Bool × List Bool)) × (NodeSlotCache × EdgeSigCache)

/-- One step of planted certification along `leaf`. -/
@[expose] noncomputable def certifyStepPlanted (S : IndexedSignatureScheme)
    (keys : List (List Bool × List Bool)) (target sigCap : ℕ) (leaf : List Bool)
    (state : PlantedCertState) : WordOracleComp Unit PlantedCertState := do
  let ((node, idx, certs), (visited, edges)) := state
  let bit := leaf.getD node.length false
  let childPath := node ++ [bit]
  let (childIdx, visited') ← visitNodeM keys.length childPath visited
  let childPk := (keys.getD childIdx ([], [])).1
  let (σ, edges') ← signEdgeM S keys target sigCap node idx bit.toNat childPk edges
  return ((childPath, childIdx, certs ++ [(childPk, σ)]), (visited', edges'))

/-- Certify `depth n - 1` steps from the root `[]` at slot `0` using planted keys. -/
@[expose] noncomputable def certifyPlanted (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    (keys : List (List Bool × List Bool)) (target sigCap n : ℕ) (leaf : List Bool)
    (caches : NodeSlotCache × EdgeSigCache) : WordOracleComp Unit PlantedCertState :=
  OracleComp.iterate (depth n - 1) (certifyStepPlanted S keys target sigCap leaf)
    (([], 0, []), caches)

/-- Signing handler of `indexedForgerAt`: answer `n`-bit signing queries along uniform leaves,
aborting with `[]` on leaf collisions, and delegating signatures at slot `target` to the external
indexed signing oracle. -/
@[expose] noncomputable def plantedTreeHandler (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    (keys : List (List Bool × List Bool)) (target sigCap n : ℕ) (request : Unit × List Bool) :
    StateT PlantedState (WordOracleComp Unit) (List Bool) := fun state =>
  let msg := request.2
  let ((visited, edges), (queried, seenLeaves, bad)) := state
  if msg.length = n then
    if bad then
      pure ([], ((visited, edges), (msg :: queried, seenLeaves, true)))
    else do
      let leaf ← ProbOracleComp.sample (BitString.sampleList (depth n))
      if seenLeaves.contains leaf then
        pure ([], ((visited, edges), (msg :: queried, seenLeaves, true)))
      else do
        let ((node, idx, certs), (visited', edges')) ←
          certifyPlanted S depth keys target sigCap n leaf (visited, edges)
        let (σ, edges'') ←
          signEdgeM S keys target sigCap node idx (leaf.getLastD false).toNat msg edges'
        return (encodeSignature leaf certs σ,
          ((visited', edges''), (msg :: queried, leaf :: seenLeaves, false)))
  else
    pure ([], ((visited, edges), (msg :: queried, seenLeaves, bad)))

/-- Extract a candidate indexed forgery `(u, m, σ)` for the key planted at `target` from a tree
forgery `(msg, sig)` and the visited-node cache `visited`: look up the unique path assigned to
`target`, and output either the child-key certificate at depth `path.length` (when internal) or the
final message signature `(u, msg, last)` (when at depth `d - 1`). -/
@[expose] def extractForgery (d target : ℕ) (visited : NodeSlotCache) (msg sig : List Bool) :
    ℕ × List Bool × List Bool :=
  let (leaf, certs, last) := signatureDecoder.decode sig
  let path := ((visited.filter fun e => e.2 == target).headD ([], 0)).1
  let j := path.length
  let u := (leaf.getD j false).toNat
  if j + 1 < d then
    let (childPk, childSig) := certs.getD j ([], [])
    (u, childPk, childSig)
  else
    (u, msg, last)

/-- The indexed forger with its challenge verification key planted at slot `target`. -/
@[expose] noncomputable def indexedForgerAt (S : IndexedSignatureScheme)
    (depth slotBound sigCap : ℕ → ℕ) (adversary : Forger) (target : ℕ) : IndexedForger :=
  fun n vk => do
    let keys ← ProbOracleComp.sample (plantNodeKeys S slotBound n target vk)
    let pk := encPair encUnary encBits (n, (keys.getD 0 ([], [])).1)
    let (msig, state) ← (OracleComp.interpret
      (OracleComp.sumHandler (fun j => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin j)))
        (plantedTreeHandler S depth keys target (sigCap n) n))
      (adversary n pk)).run initPlantedState
    let ((visited, _), _) := state
    let (msg, sig) := msig
    return extractForgery (depth n) target visited msg sig

/-- The indexed forger: sample a uniform dyadic slot `target < dyadicSize (slotBound n)` and run
`indexedForgerAt`. -/
@[expose] noncomputable def indexedForger (S : IndexedSignatureScheme)
    (depth slotBound sigCap : ℕ → ℕ) (adversary : Forger) : IndexedForger :=
  fun n vk => do
    let target ← ProbOracleComp.sample (ProbComp.sampleDyadicIndex (slotBound n))
    indexedForgerAt S depth slotBound sigCap adversary target n vk

/-! ### Strict oracle-PPT certificate for `indexedForger` -/

section ForgerEfficiency

/-- The visited node-to-slot cache, encoded as a list of entries; each entry is a node path in
binary followed by its slot in unary, the path framed. -/
private abbrev encNodeCache : NodeSlotCache ↪ List Bool :=
  encList (encPair encBits encUnary)

/-- The edge-signature cache, encoded as a list of entries; each entry is an edge (a node path in
binary followed by the edge bit in unary, the path framed), framed, followed by its signature in
binary. -/
private abbrev encEdgeCache : EdgeSigCache ↪ List Bool :=
  encList (encPair (encPair encBits encUnary) encBits)

/-- A list of pairs of words, such as the pre-sampled node key pairs or a certificate chain;
each pair is its first word in binary, framed, followed by its second word in binary. -/
private abbrev encKeys : List (List Bool × List Bool) ↪ List Bool :=
  encList (encPair encBits encBits)

/-- The state of `plantedTreeHandler`, encoded as a nested pair: the visited node cache (framed)
and the edge-signature cache, framed together, followed by the queried messages (framed), the
sampled leaves (framed) and the abort flag. Each list holds its words in binary. -/
private abbrev encPlantedState : PlantedState ↪ List Bool :=
  encPair (encPair encNodeCache encEdgeCache)
    (encPair (encList encBits) (encPair (encList encBits) encBool))

/-- The chain state of `certifyPlanted`, encoded as a nested pair: the node path in binary
(framed), the slot in unary (framed) and the certificates (key/signature word pairs, `encKeys`),
framed together, followed by the visited node cache (framed) and the edge-signature cache. -/
private abbrev encPlantedCert : PlantedCertState ↪ List Bool :=
  encPair (encPair encBits (encPair encUnary encKeys)) (encPair encNodeCache encEdgeCache)

private theorem length_fst_getD_keys_le (keys : List (List Bool × List Bool)) (idx : ℕ) :
    (keys.getD idx ([], [])).1.length ≤ (encKeys keys).length := by
  by_cases h : idx < keys.length
  · exact (length_le_encPair_left encBits encBits _).trans
      (length_le_encList_of_mem (encPair encBits encBits) (List.getD_mem _ h))
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt h)]
    exact Nat.zero_le _

private theorem isPPTOn_plantNodeKeys (S : IndexedSignatureScheme) {slotBound : ℕ → ℕ}
    (hslot : ComputableInPolyTime slotBound encUnary encUnary) :
    IsPPTOn (encPair (encPair encUnary encBits) encUnary) encKeys
      (fun c : (ℕ × List Bool) × ℕ => plantNodeKeys S slotBound c.1.1 c.2 c.1.2) := by
  have _ := S.keyGen_ppt
  dsimp only [plantNodeKeys]
  fun_prop

private theorem isOraclePPTOn_visitNodeM {γ : Type} {enc : γ ↪ List Bool}
    {cap : γ → ℕ} {path : γ → List Bool} {visited : γ → NodeSlotCache}
    (hcap : ComputableInPolyTime cap enc encUnary)
    (hpath : ComputableInPolyTime path enc encBits)
    (hvisited : ComputableInPolyTime visited enc encNodeCache) :
    IsOraclePPTOn enc (encPair encUnary encNodeCache)
      (fun a => visitNodeM (cap a) (path a) (visited a)) :=
  IsOraclePPTOn.memoize (compute := fun a _ => pure (min (visited a).length (cap a)))
    (ComputableInPolyTime.isOraclePPTOn (by fun_prop)) hpath hvisited

private theorem isOraclePPTOn_signEdgeM (S : IndexedSignatureScheme) {γ : Type}
    {enc : γ ↪ List Bool} {keys : γ → List (List Bool × List Bool)}
    {target sigCap idx u : γ → ℕ} {path msg : γ → List Bool} {edges : γ → EdgeSigCache}
    (hkeys : ComputableInPolyTime keys enc encKeys)
    (htarget : ComputableInPolyTime target enc encUnary)
    (hsigCap : ComputableInPolyTime sigCap enc encUnary)
    (hpath : ComputableInPolyTime path enc encBits)
    (hidx : ComputableInPolyTime idx enc encUnary)
    (hu : ComputableInPolyTime u enc encUnary)
    (hmsg : ComputableInPolyTime msg enc encBits)
    (hedges : ComputableInPolyTime edges enc encEdgeCache) :
    IsOraclePPTOn enc (encPair encBits encEdgeCache)
      (fun a => signEdgeM S (keys a) (target a) (sigCap a) (path a) (idx a) (u a) (msg a)
        (edges a)) := by
  have hraw : IsOraclePPTOn enc encBits
      (fun a => signEdgeRaw S (keys a) (target a) (sigCap a) (idx a) (u a) (msg a)) := by
    unfold signEdgeRaw
    exact IsOraclePPTOn.ite' (condition := fun a => idx a = target a) (by fun_prop)
      (IsOraclePPTOn.query_take' () (by fun_prop) hsigCap)
      (((S.sign_ppt.preprocess
        (prepare := fun a => (((keys a).getD (idx a) ([], [])).2, u a, msg a))
        (by fun_prop)).isOraclePPTOn (Operation := Unit)).map_with'
        (f := fun a σ => σ.take (sigCap a)) (by fun_prop))
  exact IsOraclePPTOn.memoize
    (compute := fun a _ => signEdgeRaw S (keys a) (target a) (sigCap a) (idx a) (u a) (msg a))
    hraw (hpath.prod hu) hedges

private theorem length_le_of_mem_support_signEdgeRaw (S : IndexedSignatureScheme)
    (keys : List (List Bool × List Bool)) (target sigCap idx u : ℕ) (msg : List Bool)
    {σ : List Bool} (hσ : σ ∈ OracleComp.support (signEdgeRaw S keys target sigCap idx u msg)) :
    σ.length ≤ sigCap := by
  unfold signEdgeRaw at hσ
  split_ifs at hσ with h
  · obtain ⟨raw, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hσ
    exact List.length_take_le _ _
  · obtain ⟨raw, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hσ
    exact List.length_take_le _ _

/-- Input to `certifyPlanted`: `((keys, (target, sigCap), (n, leaf)), (visited₀, edges₀))`. -/
private abbrev CertLoopIn :=
  (List (List Bool × List Bool) × (ℕ × ℕ) × (ℕ × List Bool)) × (NodeSlotCache × EdgeSigCache)

private abbrev CertLoopIn.keys (a : CertLoopIn) := a.1.1
private abbrev CertLoopIn.target (a : CertLoopIn) := a.1.2.1.1
private abbrev CertLoopIn.sigCap (a : CertLoopIn) := a.1.2.1.2
private abbrev CertLoopIn.parameter (a : CertLoopIn) := a.1.2.2.1
private abbrev CertLoopIn.leaf (a : CertLoopIn) := a.1.2.2.2
private abbrev CertLoopIn.visited (a : CertLoopIn) := a.2.1
private abbrev CertLoopIn.edges (a : CertLoopIn) := a.2.2

/-- Fixed step parameters paired with the current certification state. -/
private abbrev CertStepIn :=
  (List (List Bool × List Bool) × (ℕ × ℕ) × List Bool) × PlantedCertState
/-- A step input together with the newly visited child slot and cache. -/
private abbrev CertVisitIn := CertStepIn × (ℕ × NodeSlotCache)
/-- A visited step input together with the edge signature and cache. -/
private abbrev CertSignIn := CertVisitIn × (List Bool × EdgeSigCache)

private theorem isOraclePPTOn_certifyStepPlanted (S : IndexedSignatureScheme) :
    IsOraclePPTOn
      (encPair (encPair encKeys (encPair (encPair encUnary encUnary) encBits)) encPlantedCert)
      encPlantedCert
      (fun q : CertStepIn =>
        certifyStepPlanted S q.1.1 q.1.2.1.1 q.1.2.1.2 q.1.2.2 q.2) := by
  let encIn := encPair (encPair encKeys (encPair (encPair encUnary encUnary) encBits))
    encPlantedCert
  let encMid := encPair encIn (encPair encUnary encNodeCache)
  let encEnd := encPair encMid (encPair encBits encEdgeCache)
  have hvisit := isOraclePPTOn_visitNodeM (enc := encIn)
    (cap := fun (((keys, _, _), _) : CertStepIn) => keys.length)
    (path := fun ((_, _, leaf), ((node, _, _), _)) => node ++ [leaf.getD node.length false])
    (visited := fun (_, (_, (visited, _))) => visited) (by fun_prop) (by fun_prop) (by fun_prop)
  have hsign := isOraclePPTOn_signEdgeM S (enc := encMid)
    (keys := fun ((((keys, _, _), _), _) : CertVisitIn) => keys)
    (target := fun (((_, (target, _), _), _), _) => target)
    (sigCap := fun (((_, (_, sigCap), _), _), _) => sigCap)
    (path := fun ((_, ((node, _, _), _)), _) => node)
    (idx := fun ((_, ((_, idx, _), _)), _) => idx)
    (u := fun (((_, _, leaf), ((node, _, _), _)), _) => (leaf.getD node.length false).toNat)
    (msg := fun (((keys, _, _), _), (childIdx, _)) => (keys.getD childIdx ([], [])).1)
    (edges := fun ((_, (_, (_, edges))), _) => edges)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  have hpost : ComputableInPolyTime
      (fun (((((keys, _, leaf), ((node, _, certs), _)), (childIdx, visited)), (σ, edges)) :
          CertSignIn) =>
        ((node ++ [leaf.getD node.length false], childIdx,
          certs ++ [((keys.getD childIdx ([], [])).1, σ)]), (visited, edges)))
      encEnd encPlantedCert := by fun_prop
  exact hvisit.bind_with
    (second := fun ((keys, (target, sigCap), leaf), ((node, idx, certs), (_, edges)))
        (childIdx, visited) => do
      let childPk := (keys.getD childIdx ([], [])).1
      let bit := leaf.getD node.length false
      let (σ, edges') ← signEdgeM S keys target sigCap node idx bit.toNat childPk edges
      return ((node ++ [bit], childIdx, certs ++ [(childPk, σ)]), (visited, edges')))
    (hsign.bind_with
      (second := fun (((keys, _, leaf), ((node, _, certs), _)), (childIdx, visited)) (σ, edges) =>
        (pure ((node ++ [leaf.getD node.length false], childIdx,
          certs ++ [((keys.getD childIdx ([], [])).1, σ)]), (visited, edges)) :
          WordOracleComp Unit PlantedCertState))
      hpost.isOraclePPTOn)

private def plantedLoopInv (Mv Me : ℕ) (a : CertLoopIn) (i : ℕ)
    (state : PlantedCertState) : Prop :=
  let ((keys, _, _), (visited₀, edges₀)) := a
  let ((node, idx, certs), (visited, edges)) := state
  node.length = i ∧ idx ≤ Mv ∧ certs.length = i ∧
  (∀ c ∈ certs, c.1.length ≤ (encKeys keys).length ∧ c.2.length ≤ Me) ∧
  (∀ e ∈ visited, e.2 ≤ Mv) ∧ (∀ e ∈ edges, e.2.length ≤ Me) ∧
  (encNodeCache visited).length ≤
    (encNodeCache visited₀).length + i * (4 * (i + 1) + 2 * Mv + 3) ∧
  (encEdgeCache edges).length ≤
    (encEdgeCache edges₀).length + i * (8 * i + 2 * Me + 11)

private theorem plantedLoopInv_step (S : IndexedSignatureScheme) {Mv Me : ℕ} (a : CertLoopIn)
    (hMv : a.keys.length ≤ Mv) (hMe : a.sigCap ≤ Me) (i : ℕ) (state : PlantedCertState)
    (hinv : plantedLoopInv Mv Me a i state) (next : PlantedCertState)
    (hnext : next ∈ OracleComp.support
      (certifyStepPlanted S a.keys a.target a.sigCap a.leaf state)) :
    plantedLoopInv Mv Me a (i + 1) next := by
  rcases a with ⟨⟨keys, ⟨target, sigCap⟩, ⟨n, leaf⟩⟩, ⟨visited₀, edges₀⟩⟩
  rcases state with ⟨⟨node, idx, certs⟩, ⟨visited, edges⟩⟩
  -- the memoization bounds below are stated for the spelled-out cache encodings
  dsimp only [plantedLoopInv, encNodeCache, encEdgeCache] at hinv
  obtain ⟨hnode, hidx, hcertsLen, hcerts, hvis, hedg, hvisLen, hedgLen⟩ := hinv
  simp only [certifyStepPlanted, OracleComp.support, OracleComp.mem_supportWith_bind_iff] at hnext
  obtain ⟨⟨childIdx, visited'⟩, hvisStep, ⟨σ, edges'⟩, hedgStep, hnext⟩ := hnext
  have hnext := OracleComp.eq_of_mem_supportWith_pure hnext
  subst hnext
  dsimp only [plantedLoopInv, encNodeCache, encEdgeCache]
  have hvBound := ProbOracleComp.memoize_call_size_le encBits encUnary
    (fun _ => pure (min visited.length keys.length))
    (node ++ [leaf.getD node.length false]) visited Mv
    (fun e he => by simpa only [encUnary_apply, List.length_replicate] using hvis e he)
    (fun val hval => by
      have hval' := OracleComp.eq_of_mem_supportWith_pure hval
      subst hval'
      simp only [encUnary_apply, List.length_replicate]
      exact (Nat.min_le_right _ _).trans hMv)
    hvisStep
  simp only [encBits_apply, encUnary_apply, List.length_replicate, List.length_append,
    List.length_singleton, hnode] at hvBound
  have heBound := ProbOracleComp.memoize_call_size_le (encPair encBits encUnary) encBits
    (fun _ => signEdgeRaw S keys target sigCap idx
      (leaf.getD node.length false).toNat (keys.getD childIdx ([], [])).1)
    (node, (leaf.getD node.length false).toNat) edges Me
    (fun e he => by simpa only [encBits_apply] using hedg e he)
    (fun val hval => by
      simp only [encBits_apply]
      exact (length_le_of_mem_support_signEdgeRaw S keys target sigCap idx _ _ hval).trans hMe)
    hedgStep
  simp only [length_encPair, encBits_apply, encUnary_apply, List.length_replicate, hnode]
    at heBound
  have hu : (leaf.getD i false).toNat ≤ 1 := Bool.toNat_le _
  refine ⟨by simp [hnode], hvBound.1, by simp [hcertsLen], ?_, hvBound.2.1, heBound.2.1, ?_, ?_⟩
  · intro c hc
    simp only [List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · exact hcerts c hc
    · exact ⟨length_fst_getD_keys_le keys childIdx, heBound.1⟩
  · have hstepV : i * (4 * (i + 1) + 2 * Mv + 3) ≤ i * (4 * (i + 1 + 1) + 2 * Mv + 3) :=
      Nat.mul_le_mul_left i (by omega)
    have hsuccV : (i + 1) * (4 * (i + 1 + 1) + 2 * Mv + 3) =
        i * (4 * (i + 1 + 1) + 2 * Mv + 3) + (4 * (i + 1 + 1) + 2 * Mv + 3) := Nat.succ_mul _ _
    exact hvBound.2.2.trans (by omega)
  · have hstepE : i * (8 * i + 2 * Me + 11) ≤ i * (8 * (i + 1) + 2 * Me + 11) :=
      Nat.mul_le_mul_left i (by omega)
    have hsuccE : (i + 1) * (8 * (i + 1) + 2 * Me + 11) =
        i * (8 * (i + 1) + 2 * Me + 11) + (8 * (i + 1) + 2 * Me + 11) := Nat.succ_mul _ _
    exact heBound.2.2.trans (by omega)

private theorem certifyPlanted_support_inv (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    {Mv Me : ℕ} (a : CertLoopIn)
    (hMv : a.keys.length ≤ Mv) (hMe : a.sigCap ≤ Me)
    (hv₀ : ∀ e ∈ a.visited, e.2 ≤ Mv) (he₀ : ∀ e ∈ a.edges, e.2.length ≤ Me) :
    ∀ state ∈ OracleComp.support
      (certifyPlanted S depth a.keys a.target a.sigCap a.parameter a.leaf a.2),
      plantedLoopInv Mv Me a (depth a.parameter - 1) state := by
  have hiter : ∀ k, ∀ state ∈ OracleComp.support
      (OracleComp.iterate k (certifyStepPlanted S a.keys a.target a.sigCap a.leaf)
        (([], 0, []), a.2)),
      plantedLoopInv Mv Me a k state := by
    intro k
    induction k with
    | zero =>
      intro state hstate
      have hstate' := OracleComp.eq_of_mem_supportWith_pure hstate
      subst hstate'
      exact ⟨rfl, Nat.zero_le _, rfl, by simp, hv₀, he₀, by simp, by simp⟩
    | succ k ih =>
      intro state hstate
      rw [OracleComp.iterate_succ] at hstate
      obtain ⟨prev, hprev, hstep⟩ := OracleComp.mem_supportWith_bind_iff.mp hstate
      exact plantedLoopInv_step S a hMv hMe k prev (ih prev hprev) state hstep
  exact hiter (depth a.parameter - 1)

private theorem plantedLoopInv_enc_bounds {Mv Me d i : ℕ} {a : CertLoopIn}
    {state : PlantedCertState} (hi : i ≤ d)
    (hinv : plantedLoopInv Mv Me a i state) :
    (encKeys state.1.2.2).length ≤ d * (2 * (2 * (encKeys a.keys).length + 1 + Me) + 1) ∧
    (encNodeCache state.2.1).length ≤
      (encNodeCache a.visited).length + d * (4 * (d + 1) + 2 * Mv + 3) ∧
    (encEdgeCache state.2.2).length ≤
      (encEdgeCache a.edges).length + d * (8 * d + 2 * Me + 11) := by
  rcases a with ⟨⟨keys, ⟨target, sigCap⟩, ⟨n, leaf⟩⟩, ⟨visited₀, edges₀⟩⟩
  rcases state with ⟨⟨node, idx, certs⟩, ⟨visited, edges⟩⟩
  dsimp only [plantedLoopInv, CertLoopIn.keys, CertLoopIn.sigCap,
    CertLoopIn.visited, CertLoopIn.edges] at hinv ⊢
  obtain ⟨-, -, hcertsLen, hcerts, -, -, hvisLen, hedgLen⟩ := hinv
  have hcertsList : (encKeys certs).length ≤
      certs.length * (2 * (2 * (encKeys keys).length + 1 + Me) + 1) :=
    length_encList_le (encPair encBits encBits) certs fun c hc => by
      obtain ⟨h1, h2⟩ := hcerts c hc
      simp only [length_encPair, encBits_apply]
      omega
  rw [hcertsLen] at hcertsList
  have hcmul := Nat.mul_le_mul_right (2 * (2 * (encKeys keys).length + 1 + Me) + 1) hi
  have hvmul := Nat.mul_le_mul hi
    (show 4 * (i + 1) + 2 * Mv + 3 ≤ 4 * (d + 1) + 2 * Mv + 3 by omega)
  have hemul := Nat.mul_le_mul hi
    (show 8 * i + 2 * Me + 11 ≤ 8 * d + 2 * Me + 11 by omega)
  exact ⟨hcertsList.trans hcmul, hvisLen.trans (by omega), hedgLen.trans (by omega)⟩

private theorem isOraclePPTOn_certifyPlanted (S : IndexedSignatureScheme) {depth : ℕ → ℕ}
    (hdepth : ComputableInPolyTime depth encUnary encUnary) :
    IsOraclePPTOn
      (encPair (encPair encKeys (encPair (encPair encUnary encUnary) (encPair encUnary encBits)))
        (encPair encNodeCache encEdgeCache))
      encPlantedCert
      (fun a : CertLoopIn =>
        certifyPlanted S depth a.keys a.target a.sigCap a.parameter a.leaf a.2) := by
  let encLoopIn :=
    encPair (encPair encKeys (encPair (encPair encUnary encUnary) (encPair encUnary encBits)))
      (encPair encNodeCache encEdgeCache)
  obtain ⟨cd, dd, hdd⟩ := hdepth.polyBounded_length.exists_le
  simp only [encUnary_apply, List.length_replicate] at hdd
  have hleIn (a : CertLoopIn) :
      a.keys.length ≤ (encLoopIn a).length ∧
      (encKeys a.keys).length ≤ (encLoopIn a).length ∧
      a.sigCap ≤ (encLoopIn a).length ∧
      a.parameter ≤ (encLoopIn a).length ∧
      (encNodeCache a.visited).length ≤ (encLoopIn a).length ∧
      (encEdgeCache a.edges).length ≤ (encLoopIn a).length := by
    rcases a with ⟨⟨keys, targetCap, ⟨n, leaf⟩⟩, ⟨visited, edges⟩⟩
    have hk := length_le_length_encList (encPair encBits encBits) keys
    simp only [CertLoopIn.keys, CertLoopIn.sigCap, CertLoopIn.parameter, CertLoopIn.visited,
      CertLoopIn.edges, encLoopIn, encKeys, length_encPair, encUnary_apply, List.length_replicate,
      encBits_apply]
    omega
  have hd : PolyBounded (fun a : CertLoopIn => (encLoopIn a).length)
      (fun a => depth a.parameter) :=
    PolyBounded.of_forall_le cd dd fun a => (hdd a.parameter).trans
      (Nat.mul_le_mul_left cd (Nat.pow_le_pow_left (Nat.add_le_add_right (hleIn a).2.2.2.1 1) dd))
  let Mv (a : CertLoopIn) : ℕ := a.keys.length + (encNodeCache a.visited).length
  let Me (a : CertLoopIn) : ℕ := a.sigCap + (encEdgeCache a.edges).length
  have hMvPoly : PolyBounded (fun a : CertLoopIn => (encLoopIn a).length) Mv :=
    (PolyBounded.self.mono fun a => (hleIn a).1).add
      (PolyBounded.self.mono fun a => (hleIn a).2.2.2.2.1)
  have hMePoly : PolyBounded (fun a : CertLoopIn => (encLoopIn a).length) Me :=
    (PolyBounded.self.mono fun a => (hleIn a).2.2.1).add
      (PolyBounded.self.mono fun a => (hleIn a).2.2.2.2.2)
  have hKPoly : PolyBounded (fun a : CertLoopIn => (encLoopIn a).length)
      (fun a => (encKeys a.keys).length) :=
    PolyBounded.self.mono fun a => (hleIn a).2.1
  have hN0Poly : PolyBounded (fun a : CertLoopIn => (encLoopIn a).length)
      (fun a => (encNodeCache a.visited).length) :=
    PolyBounded.self.mono fun a => (hleIn a).2.2.2.2.1
  have hE0Poly : PolyBounded (fun a : CertLoopIn => (encLoopIn a).length)
      (fun a => (encEdgeCache a.edges).length) :=
    PolyBounded.self.mono fun a => (hleIn a).2.2.2.2.2
  have hloopId := ComputableInPolyTime.id' (encIn := encLoopIn)
  have hpair1 := ComputableInPolyTime.fst encLoopIn encPlantedCert
  have hpair2 := ComputableInPolyTime.snd encLoopIn encPlantedCert
  refine (IsOraclePPTOn.iterateWith_spec' (input := encLoopIn) (stateEncoding := encPlantedCert)
    (count := fun a : CertLoopIn => depth a.parameter - 1)
    (initial := fun a => ((([], 0, []), a.2) : PlantedCertState))
    (step := fun (a : CertLoopIn) state =>
      certifyStepPlanted S a.keys a.target a.sigCap a.leaf state)
    ((hdepth.comp hloopId.fst'.snd'.snd'.fst').unary_sub' (.const 1))
    (((ComputableInPolyTime.const []).prod ((ComputableInPolyTime.const 0).prod (.const []))).prod
      hloopId.snd')
    ((isOraclePPTOn_certifyStepPlanted S).preprocess'
      (prepare := fun pair : CertLoopIn × PlantedCertState =>
        ((pair.1.keys, (pair.1.target, pair.1.sigCap), pair.1.leaf), pair.2))
      (((hpair1.fst'.fst'.prod (hpair1.fst'.snd'.fst'.prod hpair1.fst'.snd'.snd'.snd')).prod
        hpair2)))
    (fun a i state => plantedLoopInv (Mv a) (Me a) a i state)
    (fun a => by
      refine ⟨rfl, Nat.zero_le _, rfl, by simp, ?_, ?_, by simp, by simp⟩
      · intro e he
        have hmem := length_le_encList_of_mem (encPair encBits encUnary) he
        have hle : e.2 ≤ (encPair encBits encUnary e).length := by
          simp only [length_encPair, encUnary_apply, List.length_replicate]; omega
        exact (hle.trans hmem).trans (Nat.le_add_left _ _)
      · intro e he
        have hmem := length_le_encList_of_mem (encPair (encPair encBits encUnary) encBits) he
        have hle : e.2.length ≤ (encPair (encPair encBits encUnary) encBits e).length := by
          simp only [length_encPair, encBits_apply]; omega
        exact (hle.trans hmem).trans (Nat.le_add_left _ _))
    (fun a i state _ hinv next hnext =>
      plantedLoopInv_step S a (Nat.le_add_right _ _) (Nat.le_add_right _ _) i state hinv next
        hnext)
    (size := fun a : CertLoopIn =>
      let d := depth a.parameter
      let certB := d * (2 * (2 * (encKeys a.keys).length + 1 + Me a) + 1)
      let vB := (encNodeCache a.visited).length + d * (4 * (d + 1) + 2 * Mv a + 3)
      let eB := (encEdgeCache a.edges).length + d * (8 * d + 2 * Me a + 11)
      2 * (2 * d + 1 + (2 * Mv a + 1 + certB)) + 1 + (2 * vB + 1 + eB))
    ?_ ?_).1
  · have hcertB : PolyBounded (fun a : CertLoopIn => (encLoopIn a).length)
        (fun a => depth a.parameter * (2 * (2 * (encKeys a.keys).length + 1 + Me a) + 1)) :=
      hd.mul (((PolyBounded.const 2).mul
        ((((PolyBounded.const 2).mul hKPoly).add (.const 1)).add hMePoly)).add (.const 1))
    have hvB : PolyBounded (fun a : CertLoopIn => (encLoopIn a).length)
        (fun a => (encNodeCache a.visited).length +
          depth a.parameter * (4 * (depth a.parameter + 1) + 2 * Mv a + 3)) :=
      hN0Poly.add (hd.mul (((((PolyBounded.const 4).mul (hd.add (.const 1))).add
        ((PolyBounded.const 2).mul hMvPoly))).add (.const 3)))
    have heB : PolyBounded (fun a : CertLoopIn => (encLoopIn a).length)
        (fun a => (encEdgeCache a.edges).length +
          depth a.parameter * (8 * depth a.parameter + 2 * Me a + 11)) :=
      hE0Poly.add (hd.mul (((((PolyBounded.const 8).mul hd).add
        ((PolyBounded.const 2).mul hMePoly))).add (.const 11)))
    have hleft : PolyBounded (fun a : CertLoopIn => (encLoopIn a).length)
        (fun a => 2 * depth a.parameter + 1 + (2 * Mv a + 1 +
          depth a.parameter * (2 * (2 * (encKeys a.keys).length + 1 + Me a) + 1))) :=
      (((PolyBounded.const 2).mul hd).add (.const 1)).add
        ((((PolyBounded.const 2).mul hMvPoly).add (.const 1)).add hcertB)
    have hright : PolyBounded (fun a : CertLoopIn => (encLoopIn a).length)
        (fun a => 2 * ((encNodeCache a.visited).length +
            depth a.parameter * (4 * (depth a.parameter + 1) + 2 * Mv a + 3)) + 1 +
          ((encEdgeCache a.edges).length +
            depth a.parameter * (8 * depth a.parameter + 2 * Me a + 11))) :=
      (((PolyBounded.const 2).mul hvB).add (.const 1)).add heB
    exact (((PolyBounded.const 2).mul hleft).add (.const 1)).add hright
  · intro a i ⟨⟨node, idx, certs⟩, ⟨visited, edges⟩⟩ hi hinv
    have hle := plantedLoopInv_enc_bounds (hi.trans (Nat.sub_le _ _)) hinv
    dsimp only [plantedLoopInv] at hinv
    dsimp only at hle
    obtain ⟨hnode, hidx, -⟩ := hinv
    obtain ⟨hcB, hvB, heB⟩ := hle
    simp only [length_encPair, encBits_apply, encUnary_apply, List.length_replicate, hnode]
    omega

/-- Caller tuple for `plantedTreeHandler`: `(((n, vk), target), keys)`. -/
private abbrev ForgerCaller := ((ℕ × List Bool) × ℕ) × List (List Bool × List Bool)

private theorem isOraclePPTOn_plantedTreeHandler (S : IndexedSignatureScheme)
    {depth sigCap : ℕ → ℕ}
    (hdepth : ComputableInPolyTime depth encUnary encUnary)
    (hsigCap : ComputableInPolyTime sigCap encUnary encUnary) :
    let encCaller := encPair (encPair (encPair encUnary encBits) encUnary) encKeys
    IsOraclePPTOn
      (encPair encCaller (encPair (encPair (encFinEnum Unit) encBits) encPlantedState))
      (encPair encBits encPlantedState)
      (fun pair : ForgerCaller × ((Unit × List Bool) × PlantedState) =>
        plantedTreeHandler S depth pair.1.2 pair.1.1.2 (sigCap pair.1.1.1.1) pair.1.1.1.1
          pair.2.1 pair.2.2) := by
  intro encCaller
  let encH := encPair encCaller (encPair (encPair (encFinEnum Unit) encBits) encPlantedState)
  let encHL := encPair encH encBits
  let encHLC := encPair encHL encPlantedCert
  let encHLCS := encPair encHLC (encPair encBits encEdgeCache)
  let badOut (p : ForgerCaller × ((Unit × List Bool) × PlantedState)) : List Bool × PlantedState :=
    ([], ((p.2.2.1.1, p.2.2.1.2), (p.2.1.2 :: p.2.2.2.1, p.2.2.2.2.1, true)))
  let goodLeaf (q : (ForgerCaller × ((Unit × List Bool) × PlantedState)) × List Bool) :
      WordOracleComp Unit (List Bool × PlantedState) :=
    certifyPlanted S depth q.1.1.2 q.1.1.1.2 (sigCap q.1.1.1.1.1) q.1.1.1.1.1 q.2
      (q.1.2.2.1.1, q.1.2.2.1.2) >>= fun c =>
        signEdgeM S q.1.1.2 q.1.1.1.2 (sigCap q.1.1.1.1.1) c.1.1 c.1.2.1
          (q.2.getLastD false).toNat q.1.2.1.2 c.2.2 >>= fun e =>
            pure (encodeSignature q.2 c.1.2.2 e.1,
              ((c.2.1, e.2), (q.1.2.1.2 :: q.1.2.2.2.1, q.2 :: q.1.2.2.2.2.1, false)))
  let afterLeaf (p : ForgerCaller × ((Unit × List Bool) × PlantedState)) (leaf : List Bool) :
      WordOracleComp Unit (List Bool × PlantedState) :=
    if p.2.2.2.2.1.contains leaf then pure (badOut p) else goodLeaf (p, leaf)
  have hbadBr : ComputableInPolyTime badOut encH (encPair encBits encPlantedState) := by fun_prop
  have hnoMsgBr : ComputableInPolyTime
      (fun p : ForgerCaller × ((Unit × List Bool) × PlantedState) =>
        (([] : List Bool),
          ((p.2.2.1.1, p.2.2.1.2), (p.2.1.2 :: p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2))))
      encH (encPair encBits encPlantedState) := by fun_prop
  have hleaf : IsOraclePPTOn (Operation := Unit) encH encBits
      (fun p : ForgerCaller × ((Unit × List Bool) × PlantedState) =>
        ProbOracleComp.sample (BitString.sampleList (depth p.1.1.1.1))) :=
    ((by fun_prop : ComputableInPolyTime
      (fun p : ForgerCaller × ((Unit × List Bool) × PlantedState) => depth p.1.1.1.1)
      encH encUnary).sampleList).isOraclePPTOn
  have hcollBr : ComputableInPolyTime
      (fun q : (ForgerCaller × ((Unit × List Bool) × PlantedState)) × List Bool => badOut q.1)
      encHL (encPair encBits encPlantedState) :=
    hbadBr.comp (ComputableInPolyTime.fst encH encBits)
  have hcertPrep := (isOraclePPTOn_certifyPlanted S hdepth).preprocess' (input := encHL)
    (prepare := fun q : (ForgerCaller × ((Unit × List Bool) × PlantedState)) × List Bool =>
      (((q.1.1.2, (q.1.1.1.2, sigCap q.1.1.1.1.1), (q.1.1.1.1.1, q.2)),
        (q.1.2.2.1.1, q.1.2.2.1.2)) : CertLoopIn)) (by fun_prop)
  have hsignLast := isOraclePPTOn_signEdgeM S (enc := encHLC)
    (keys := fun r => r.1.1.1.2) (target := fun r => r.1.1.1.1.2)
    (sigCap := fun r => sigCap r.1.1.1.1.1.1) (path := fun r => r.2.1.1)
    (idx := fun r => r.2.1.2.1) (u := fun r => (r.1.2.getLastD false).toNat)
    (msg := fun r => r.1.1.2.1.2) (edges := fun r => r.2.2.2)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  have hpostGood : ComputableInPolyTime
      (fun s : (((ForgerCaller × ((Unit × List Bool) × PlantedState)) × List Bool) ×
          PlantedCertState) × (List Bool × EdgeSigCache) =>
        (encodeSignature s.1.1.2 s.1.2.1.2.2 s.2.1,
          ((s.1.2.2.1, s.2.2),
            (s.1.1.1.2.1.2 :: s.1.1.1.2.2.2.1, s.1.1.2 :: s.1.1.1.2.2.2.2.1, false))))
      encHLCS (encPair encBits encPlantedState) := by fun_prop
  have hgoodLeaf : IsOraclePPTOn encHL (encPair encBits encPlantedState) goodLeaf :=
    hcertPrep.bind_with
      (second := fun (q : (ForgerCaller × ((Unit × List Bool) × PlantedState)) × List Bool)
          (c : PlantedCertState) =>
        signEdgeM S q.1.1.2 q.1.1.1.2 (sigCap q.1.1.1.1.1) c.1.1 c.1.2.1
          (q.2.getLastD false).toNat q.1.2.1.2 c.2.2 >>= fun e =>
            pure (encodeSignature q.2 c.1.2.2 e.1,
              ((c.2.1, e.2), (q.1.2.1.2 :: q.1.2.2.2.1, q.2 :: q.1.2.2.2.2.1, false))))
      (hsignLast.bind_with
        (second := fun (r : ((ForgerCaller × ((Unit × List Bool) × PlantedState)) × List Bool) ×
            PlantedCertState) (e : List Bool × EdgeSigCache) =>
          (pure (encodeSignature r.1.2 r.2.1.2.2 e.1,
            ((r.2.2.1, e.2), (r.1.1.2.1.2 :: r.1.1.2.2.2.1, r.1.2 :: r.1.1.2.2.2.2.1, false))) :
            WordOracleComp Unit (List Bool × PlantedState)))
        hpostGood.isOraclePPTOn)
  have hafterLeaf : IsOraclePPTOn encHL (encPair encBits encPlantedState)
      (fun q => afterLeaf q.1 q.2) :=
    IsOraclePPTOn.cond' (condition := fun q => q.1.2.2.2.2.1.contains q.2) (by fun_prop)
      hcollBr.isOraclePPTOn hgoodLeaf
  have hnotBad := hleaf.bind_with (second := afterLeaf) hafterLeaf
  have hlenEq := IsOraclePPTOn.cond' (condition := fun p => p.2.2.2.2.2) (by fun_prop)
    hbadBr.isOraclePPTOn hnotBad
  simpa only [plantedTreeHandler, StateT.run, badOut, afterLeaf, goodLeaf] using
    IsOraclePPTOn.ite' (condition := fun p => p.2.1.2.length = p.1.1.1.1) (by fun_prop)
      hlenEq hnoMsgBr.isOraclePPTOn

private def plantedResourceAllowance (depth sigCap : ℕ → ℕ) (c : ForgerCaller)
    (w : List Bool) : ℕ :=
  let n := c.1.1.1
  let d := depth n
  let sc := sigCap n
  let kLen := c.2.length
  let kEncLen := (encKeys c.2).length
  let replyB := 2 * d + 1 + (2 * (d * (2 * (2 * kEncLen + 1 + sc) + 1)) + 1 + sc)
  let vGrow := d * (4 * (d + 1) + 2 * kLen + 3)
  let eGrow := (d + 1) * (8 * d + 2 * sc + 11)
  let qGrow := 2 * w.length + 2
  let slGrow := 2 * d + 2
  replyB + 4 * vGrow + 2 * eGrow + 2 * qGrow + 2 * slGrow

private theorem plantedState_length_eq (state : PlantedState) :
    (encPlantedState state).length =
      4 * (encNodeCache state.1.1).length +
      2 * (encEdgeCache state.1.2).length +
      2 * (encList encBits state.2.1).length +
      2 * (encList encBits state.2.2.1).length + 6 := by
  rcases state with ⟨⟨v, e⟩, ⟨q, sl, b⟩⟩
  simp only [length_encPair, encBool_apply, List.length_singleton]
  omega

private theorem plantedTreeHandler_preserve (S : IndexedSignatureScheme) (depth sigCap : ℕ → ℕ)
    (c : ForgerCaller) (request : Unit × List Bool) (state : PlantedState)
    (hinv : (∀ e ∈ state.1.1, e.2 ≤ c.2.length) ∧
      (∀ e ∈ state.1.2, e.2.length ≤ sigCap c.1.1.1))
    (result : List Bool × PlantedState)
    (hresult : result ∈ OracleComp.support
      (plantedTreeHandler S depth c.2 c.1.2 (sigCap c.1.1.1) c.1.1.1 request state)) :
    ((∀ e ∈ result.2.1.1, e.2 ≤ c.2.length) ∧
      (∀ e ∈ result.2.1.2, e.2.length ≤ sigCap c.1.1.1)) ∧
    result.1.length ≤ plantedResourceAllowance depth sigCap c request.2 ∧
    (encPlantedState result.2).length ≤
      (encPlantedState state).length + plantedResourceAllowance depth sigCap c request.2 := by
  rcases state with ⟨⟨visited, edges⟩, ⟨queried, seenLeaves, bad⟩⟩
  obtain ⟨hvis, hedg⟩ := hinv
  have hqCons : (encList encBits (request.2 :: queried)).length ≤
      (encList encBits queried).length + (2 * request.2.length + 2) := by
    simp only [encList_cons, List.length_append, length_frame, encBits_apply]
    omega
  unfold plantedTreeHandler at hresult
  dsimp only at hresult
  split_ifs at hresult with hmsg hbad
  · have hres := OracleComp.eq_of_mem_supportWith_pure hresult
    subst hres
    refine ⟨⟨hvis, hedg⟩, Nat.zero_le _, ?_⟩
    rw [plantedState_length_eq, plantedState_length_eq]
    dsimp only [plantedResourceAllowance]
    omega
  · simp only [OracleComp.support, OracleComp.mem_supportWith_bind_iff] at hresult
    obtain ⟨leaf, hleaf, hrest⟩ := hresult
    have hleaf' : leaf ∈ OracleComp.support
        (ProbOracleComp.sample (BitString.sampleList (depth c.1.1.1))) := hleaf
    rw [ProbOracleComp.support_sample, BitString.eval_sampleList] at hleaf'
    have hleafLen := BitString.length_of_mem_support_uniformList hleaf'
    split_ifs at hrest with hcoll
    · have hres := OracleComp.eq_of_mem_supportWith_pure hrest
      subst hres
      refine ⟨⟨hvis, hedg⟩, Nat.zero_le _, ?_⟩
      rw [plantedState_length_eq, plantedState_length_eq]
      dsimp only [plantedResourceAllowance]
      omega
    · simp only [OracleComp.mem_supportWith_bind_iff] at hrest
      obtain ⟨⟨⟨node, idx, certs⟩, ⟨visited', edges'⟩⟩, hcert, ⟨σ, edges''⟩, hsig, hres⟩ := hrest
      have hres' := OracleComp.eq_of_mem_supportWith_pure hres
      subst hres'
      have hloop := certifyPlanted_support_inv S depth
        ((c.2, (c.1.2, sigCap c.1.1.1), (c.1.1.1, leaf)), (visited, edges))
        le_rfl le_rfl hvis hedg _ hcert
      have hloopB := plantedLoopInv_enc_bounds (Nat.sub_le (depth c.1.1.1) 1) hloop
      dsimp only [plantedLoopInv, CertLoopIn.keys, CertLoopIn.sigCap,
        CertLoopIn.parameter] at hloop
      -- `encodeSignature` and the memoization bound spell out the encodings
      dsimp only [CertLoopIn.keys, CertLoopIn.sigCap, CertLoopIn.visited,
        CertLoopIn.edges, encKeys, encNodeCache, encEdgeCache] at hloopB
      obtain ⟨hnode, hidx, -, -, hvis', hedg', -, -⟩ := hloop
      obtain ⟨hcB, hvB, heB⟩ := hloopB
      have hsub := Nat.sub_le (depth c.1.1.1) 1
      have heLast := ProbOracleComp.memoize_call_size_le (encPair encBits encUnary) encBits
        (fun _ => signEdgeRaw S c.2 c.1.2 (sigCap c.1.1.1) idx
          (leaf.getLastD false).toNat request.2)
        (node, (leaf.getLastD false).toNat) edges' (sigCap c.1.1.1)
        (fun e he => by simpa only [encBits_apply] using hedg' e he)
        (fun val hval => by
          simpa only [encBits_apply] using
            length_le_of_mem_support_signEdgeRaw S c.2 c.1.2 (sigCap c.1.1.1) idx _ _ hval)
        hsig
      simp only [length_encPair, encBits_apply, encUnary_apply, List.length_replicate, hnode]
        at heLast
      have hu : (leaf.getLastD false).toNat ≤ 1 := Bool.toNat_le _
      refine ⟨⟨hvis', heLast.2.1⟩, ?_, ?_⟩
      · have hσLen : σ.length ≤ sigCap c.1.1.1 := heLast.1
        simp only [encodeSignature, length_encPair, encBits_apply, hleafLen]
        dsimp only [plantedResourceAllowance, encKeys]
        omega
      · have hslCons : (encList encBits (leaf :: seenLeaves)).length ≤
            (encList encBits seenLeaves).length + (2 * depth c.1.1.1 + 2) := by
          simp only [encList_cons, List.length_append, length_frame, encBits_apply, hleafLen]
          omega
        have hsucc : (depth c.1.1.1 + 1) * (8 * depth c.1.1.1 + 2 * sigCap c.1.1.1 + 11) =
            depth c.1.1.1 * (8 * depth c.1.1.1 + 2 * sigCap c.1.1.1 + 11) +
              (8 * depth c.1.1.1 + 2 * sigCap c.1.1.1 + 11) := Nat.succ_mul _ _
        rw [plantedState_length_eq, plantedState_length_eq]
        dsimp only [plantedResourceAllowance, encKeys, encNodeCache, encEdgeCache]
        omega
  · have hres := OracleComp.eq_of_mem_supportWith_pure hresult
    subst hres
    refine ⟨⟨hvis, hedg⟩, Nat.zero_le _, ?_⟩
    rw [plantedState_length_eq, plantedState_length_eq]
    dsimp only [plantedResourceAllowance]
    omega

/-- The planted-node reduction `indexedForger` is uniformly strict oracle PPT whenever `depth`,
`slotBound`, and `sigCap` are polynomial-time in unary and `adversary` is strict oracle PPT. -/
theorem isOraclePPT_indexedForger (S : IndexedSignatureScheme) {depth slotBound sigCap : ℕ → ℕ}
    (hdepth : ComputableInPolyTime depth encUnary encUnary)
    (hslot : ComputableInPolyTime slotBound encUnary encUnary)
    (hsigCap : ComputableInPolyTime sigCap encUnary encUnary)
    {adversary : Forger} (hA : IsOraclePPT (encPair encBits encBits) adversary) :
    IsOraclePPT (encPair encUnary (encPair encBits encBits))
      (indexedForger S depth slotBound sigCap adversary) := by
  let encStage := encPair (encPair encUnary encBits) encUnary
  let encCaller := encPair encStage encKeys
  let encRunOut := encPair (encPair encBits encBits) encPlantedState
  have htarget : IsOraclePPTOn (Operation := Unit) (encPair encUnary encBits) encUnary
      (fun p : ℕ × List Bool =>
        ProbOracleComp.sample (ProbComp.sampleDyadicIndex (slotBound p.1))) :=
    (isPPTOn_sampleDyadicIndex (by fun_prop)).isOraclePPTOn
  have hkeys : IsOraclePPTOn (Operation := Unit) encStage encKeys
      (fun c : (ℕ × List Bool) × ℕ =>
        ProbOracleComp.sample (plantNodeKeys S slotBound c.1.1 c.2 c.1.2)) :=
    (isPPTOn_plantNodeKeys S hslot).isOraclePPTOn
  have hres : ComputableInPolyTime
      (fun pair : ForgerCaller × List Bool =>
        plantedResourceAllowance depth sigCap pair.1 pair.2)
      (encPair encCaller encBits) encUnary := by
    let encFive := encPair (encPair encUnary encUnary)
      (encPair encUnary (encPair encUnary encUnary))
    have hp1 := ComputableInPolyTime.fst encCaller encBits
    have hn := (ComputableInPolyTime.id' (encIn := encCaller)).fst'.fst'.fst'.comp hp1
    have hkeysL := (ComputableInPolyTime.id' (encIn := encCaller)).snd'.comp hp1
    have hinputs : ComputableInPolyTime
        (fun pair : ForgerCaller × List Bool =>
          ((depth pair.1.1.1.1, sigCap pair.1.1.1.1),
            (pair.1.2.length, (encKeys pair.1.2).length, pair.2.length)))
        (encPair encCaller encBits) encFive :=
      ((hdepth.comp hn).prod (hsigCap.comp hn)).prod
        (((ComputableInPolyTime.length_list (encPair encBits encBits)).comp hkeysL).prod
          (((ComputableInPolyTime.encoding_length encKeys).comp hkeysL).prod
            (ComputableInPolyTime.snd encCaller encBits).length_bits_comp))
    have hformula : ComputableInPolyTime
        (fun q : (ℕ × ℕ) × (ℕ × ℕ × ℕ) =>
          let d := q.1.1; let sc := q.1.2; let kLen := q.2.1
          let kEncLen := q.2.2.1; let wLen := q.2.2.2
          2 * d + 1 + (2 * (d * (2 * (2 * kEncLen + 1 + sc) + 1)) + 1 + sc) +
            4 * (d * (4 * (d + 1) + 2 * kLen + 3)) +
            2 * ((d + 1) * (8 * d + 2 * sc + 11)) +
            2 * (2 * wLen + 2) + 2 * (2 * d + 2))
        encFive encUnary := by fun_prop
    exact Eq.mp (congrArg (ComputableInPolyTime · (encPair encCaller encBits) encUnary)
      (funext fun pair => by simp only [Function.comp_apply, plantedResourceAllowance]))
      (hformula.comp hinputs)
  have hprepCaller : ComputableInPolyTime
      (fun c : ForgerCaller =>
        (c.1.1.1, encPair encUnary encBits (c.1.1.1, (c.2.getD 0 ([], [])).1)))
      encCaller (encPair encUnary encBits) := by fun_prop
  have hrun := hA.run_interpret_preprocess_open' (External := Unit)
    (handler := fun c : ForgerCaller =>
      plantedTreeHandler S depth c.2 c.1.2 (sigCap c.1.1.1) c.1.1.1)
    (prepare := fun c : ForgerCaller =>
      (c.1.1.1, encPair encUnary encBits (c.1.1.1, (c.2.getD 0 ([], [])).1)))
    (initial := fun _ => initPlantedState)
    (resources := plantedResourceAllowance depth sigCap)
    hprepCaller
    (isOraclePPTOn_plantedTreeHandler S hdepth hsigCap)
    (ComputableInPolyTime.const initPlantedState)
    (fun c state => (∀ e ∈ state.1.1, e.2 ≤ c.2.length) ∧
      (∀ e ∈ state.1.2, e.2.length ≤ sigCap c.1.1.1))
    (fun c => by
      simp only [initPlantedState, List.mem_singleton, List.not_mem_nil, IsEmpty.forall_iff,
        implies_true, and_true]
      rintro _ rfl
      exact Nat.zero_le _)
    hres
    (plantedTreeHandler_preserve S depth sigCap)
  have hextract : ComputableInPolyTime
      (fun pair : ForgerCaller × ((List Bool × List Bool) × PlantedState) =>
        extractForgery (depth pair.1.1.1.1) pair.1.1.2 pair.2.2.1.1 pair.2.1.1 pair.2.1.2)
      (encPair encCaller encRunOut)
      (encPair encUnary (encPair encBits encBits)) := by
    let encEx := encPair encCaller encRunOut
    let encMid := encPair encEx
      (encPair (encPair encBits (encPair encKeys encBits)) encUnary)
    have hmid : ComputableInPolyTime
        (fun pair : ForgerCaller × ((List Bool × List Bool) × PlantedState) =>
          (pair, signatureDecoder.decode pair.2.1.2,
            ((pair.2.2.1.1.filter fun e => e.2 == pair.1.1.2).headD ([], 0)).1.length))
        encEx encMid := by fun_prop
    have hstep : ComputableInPolyTime
        (fun t : (ForgerCaller × ((List Bool × List Bool) × PlantedState)) ×
            (List Bool × List (List Bool × List Bool) × List Bool) × ℕ =>
          if t.2.2 + 1 < depth t.1.1.1.1.1 then
            ((t.2.1.1.getD t.2.2 false).toNat, (t.2.1.2.1.getD t.2.2 ([], [])).1,
              (t.2.1.2.1.getD t.2.2 ([], [])).2)
          else
            ((t.2.1.1.getD t.2.2 false).toNat, t.1.2.1.1, t.2.1.2.2))
        encMid (encPair encUnary (encPair encBits encBits)) := by fun_prop
    exact Eq.mp
      (congrArg (ComputableInPolyTime · encEx (encPair encUnary (encPair encBits encBits)))
        (funext fun pair => by dsimp only [Function.comp_apply, extractForgery]))
      (hstep.comp hmid)
  have hforgerAt : IsOraclePPTOn encStage (encPair encUnary (encPair encBits encBits))
      (fun c : (ℕ × List Bool) × ℕ =>
        indexedForgerAt S depth slotBound sigCap adversary c.2 c.1.1 c.1.2) :=
    hkeys.bind_with
      (second := fun (c : (ℕ × List Bool) × ℕ) (keys : List (List Bool × List Bool)) =>
        (OracleComp.interpret
          (OracleComp.sumHandler
            (fun j => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin j)))
            (plantedTreeHandler S depth keys c.2 (sigCap c.1.1) c.1.1))
          (adversary c.1.1 (encPair encUnary encBits (c.1.1, (keys.getD 0 ([], [])).1)))).run
            initPlantedState >>= fun out =>
              pure (extractForgery (depth c.1.1) c.2 out.2.1.1 out.1.1 out.1.2))
      (hrun.bind_with
        (second := fun (c : ForgerCaller) (out : (List Bool × List Bool) × PlantedState) =>
          (pure (extractForgery (depth c.1.1.1) c.1.2 out.2.1.1 out.1.1 out.1.2) :
            WordOracleComp Unit (ℕ × List Bool × List Bool)))
        hextract.isOraclePPTOn)
  exact IsOraclePPTOn.isOraclePPT (htarget.bind_with
    (second := fun (p : ℕ × List Bool) (target : ℕ) =>
      indexedForgerAt S depth slotBound sigCap adversary target p.1 p.2)
    hforgerAt)

end ForgerEfficiency

/-! ### From ideal coins to the lazy tree game -/

section IdealToLazy

private abbrev CoinCache := List (List Bool × List Bool)

private noncomputable def lazyCoinRequest (M : ℕ) (x : List Bool) (L : ℕ) :
    StateT CoinCache PMF (List Bool) := fun cc =>
  (memoize (fun _ => BitString.uniformList M) (padRequest M x) cc).map
    fun out => (out.1.take L, out.2)

private noncomputable def lazyCoinHandler (M : ℕ) (r : Unit × List Bool) :
    StateT CoinCache PMF (List Bool) :=
  let req := coinRequestDecoder.decode r.2
  lazyCoinRequest M req.1 req.2

private theorem eval_treeIdealGame_eq_lazyCoin (S : IndexedSignatureScheme) (T : S.Seeded)
    (depth N : ℕ → ℕ) (adversary : Forger) (n : ℕ) :
    ProbComp.eval (treeIdealGame S T depth N adversary n) =
      ((OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
          (lazyCoinHandler (N n)))
        (simulateTreeGame S T depth adversary n)).run []).map Prod.fst := by
  set M := N n
  set prog := simulateTreeGame S T depth adversary n
  have hideal : ProbComp.eval (treeIdealGame S T depth N adversary n) =
      (PMF.uniformOfFintype (BitString M → BitString M)).bind fun table =>
        OracleComp.interpret
          (OracleComp.sumHandler ProbComp.unifOracle
            (fun r : Unit × List Bool => PMF.pure (randomCoinOracle M table r.2)))
          prog := by
    simp only [treeIdealGame, ProbComp.eval_bind, ProbComp.eval_uniform]
    refine PMF.bind_congr_on_support _ _ _ fun table _ => ?_
    have hc : ∀ x L, (randomCoinOracle M table (encPair encBits encUnary (x, L))).length ≤ L := by
      intro x L
      simp only [randomCoinOracle, coinRequestDecoder.decode_enc]
      exact List.length_take_le _ _
    have hcoins : coinsOf (randomCoinOracle M table) = tableCoins M table := by
      funext _ x L
      simp only [coinsOf, randomCoinOracle, coinRequestDecoder.decode_enc, tableCoins]
    rw [← hcoins, ← evalDet_simulateTreeGame hc adversary n [], ← eval_interpret_eq_evalDet,
      ProbOracleComp.eval_interpret]
    simp only [ProbComp.eval_pure]
    rfl
  let adapt (r : Unit × List Bool) :
      ProbOracleComp (fun _ : BitString M => List Bool) (List Bool) :=
    let req := coinRequestDecoder.decode r.2
    List.take req.2 <$> ProbOracleComp.query (BitString.ofList M (padRequest M req.1))
  let adapted := OracleComp.interpret
    (OracleComp.sumHandler (fun k => ProbOracleComp.sample (ProbComp.unifFin k)) adapt) prog
  have hmem := RandomOracle.interpret_prob_eq_memoize_map
    (Query := BitString M) (Value := BitString M) (Key' := List Bool) (Value' := List Bool)
    ⟨List.ofFn, List.ofFn_injective⟩ List.ofFn
    (fun _ => PMF.uniformOfFintype (BitString M))
    (fun _ => BitString.uniformList M)
    (fun _ => rfl)
    adapted
  rw [PMF.pi_uniformOfFintype, Probability.PMF.monad_bind_eq_bind] at hmem
  simp only [Function.Embedding.coeFn_mk] at hmem
  have hlhs : (PMF.uniformOfFintype (BitString M → BitString M)).bind (fun table =>
        OracleComp.interpret
          (OracleComp.sumHandler ProbComp.unifOracle (fun key => PMF.pure (List.ofFn (table key))))
          adapted) =
      (PMF.uniformOfFintype (BitString M → BitString M)).bind (fun table =>
        OracleComp.interpret
          (OracleComp.sumHandler ProbComp.unifOracle
            (fun r : Unit × List Bool => PMF.pure (randomCoinOracle M table r.2)))
          prog) := by
    refine PMF.bind_congr_on_support _ _ _ fun table _ => ?_
    simp only [adapted, OracleComp.interpret_interpret, OracleComp.interpret_sumHandler,
      ProbOracleComp.interpret_sample, ProbComp.unifFin, OracleComp.interpret_query]
    congr 1
    funext q
    cases q with
    | inl k => rfl
    | inr r =>
      simp only [adapt, OracleComp.interpret_map,
        ProbOracleComp.interpret_query, PMF.monad_map_eq_map, PMF.pure_map, randomCoinOracle,
        randomFunctionOracle, length_padRequest, ↓reduceIte]
  have hrhs : ((OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
          (fun key => memoize (fun _ => BitString.uniformList M) (List.ofFn key)))
        adapted).run []) =
      (OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
          (lazyCoinHandler M)) prog).run [] := by
    simp only [adapted, OracleComp.interpret_interpret, OracleComp.interpret_sumHandler,
      ProbOracleComp.interpret_sample, ProbComp.unifFin, OracleComp.interpret_query]
    refine congrArg (fun h => (OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k)) h) prog).run [])
      (funext fun r => funext fun cc => ?_)
    change ((OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
        (fun key => memoize (fun _ => BitString.uniformList M) (List.ofFn key)))
      (adapt r)).run cc) = lazyCoinHandler M r cc
    simp only [adapt, OracleComp.interpret_map, ProbOracleComp.interpret_query,
      StateT.run_map, PMF.monad_map_eq_map,
      BitString.ofFn_ofList (length_padRequest M _), lazyCoinHandler, lazyCoinRequest]
    rfl
  rw [hideal, ← hlhs, hmem, hrhs]

private noncomputable def coinSignBody (S : IndexedSignatureScheme) (T : S.Seeded)
    (depth : ℕ → ℕ) (M n : ℕ) (leaf msg : List Bool) (cc : CoinCache) :
    PMF (List Bool × CoinCache) :=
  (OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k)) (lazyCoinHandler M))
    (do
      let (node, (_, sk), certs) ← certifyO S T depth n leaf
      let σ ← signAtO S T node sk (leaf.getLastD false).toNat msg
      return encodeSignature leaf certs σ)).run cc

private abbrev GuardedCoinState :=
  CoinCache × (List (List Bool) × List (List Bool) × Bool)

private noncomputable def unguardedCoinHandler (S : IndexedSignatureScheme) (T : S.Seeded)
    (depth : ℕ → ℕ) (M n : ℕ) (request : Unit × List Bool) :
    StateT GuardedCoinState PMF (List Bool) := fun state =>
  let msg := request.2
  let (cc, (queried, seenLeaves, bad)) := state
  if msg.length = n then do
    let leaf ← BitString.uniformList (depth n)
    let bad' := bad || seenLeaves.contains leaf
    let seen' := if bad' then seenLeaves else leaf :: seenLeaves
    (coinSignBody S T depth M n leaf msg cc).map fun out =>
      (out.1, (out.2, (msg :: queried, seen', bad')))
  else
    PMF.pure ([], (cc, (msg :: queried, seenLeaves, bad)))

private noncomputable def guardedCoinHandler (S : IndexedSignatureScheme) (T : S.Seeded)
    (depth : ℕ → ℕ) (M n : ℕ) (request : Unit × List Bool) :
    StateT GuardedCoinState PMF (List Bool) := fun state =>
  let msg := request.2
  let (cc, (queried, seenLeaves, bad)) := state
  if msg.length = n then
    if bad then
      PMF.pure ([], (cc, (msg :: queried, seenLeaves, true)))
    else do
      let leaf ← BitString.uniformList (depth n)
      if seenLeaves.contains leaf then
        pure ([], (cc, (msg :: queried, seenLeaves, true)))
      else
        (coinSignBody S T depth M n leaf msg cc).map fun out =>
          (out.1, (out.2, (msg :: queried, leaf :: seenLeaves, false)))
  else
    PMF.pure ([], (cc, (msg :: queried, seenLeaves, bad)))

private theorem identicalUntilBad_coinHandlers (S : IndexedSignatureScheme) (T : S.Seeded)
    (depth : ℕ → ℕ) (M n : ℕ) :
    OracleComp.IdenticalUntilBad
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
        (unguardedCoinHandler S T depth M n))
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
        (guardedCoinHandler S T depth M n))
      (fun s => s.2.2.2 = true) where
  agree q s hs a s' hs' := by
    cases q with
    | inl k => rfl
    | inr req =>
      obtain ⟨cc, queried, seenLeaves, bad⟩ := s
      have hbad : bad = false := Bool.eq_false_iff.mpr hs
      subst hbad
      change unguardedCoinHandler S T depth M n req (cc, queried, seenLeaves, false) (a, s') =
        guardedCoinHandler S T depth M n req (cc, queried, seenLeaves, false) (a, s')
      simp only [unguardedCoinHandler, guardedCoinHandler, PMF.monad_bind_eq_bind,
        PMF.monad_pure_eq_pure, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
      split_ifs with hmsg
      · simp only [PMF.bind_apply]
        refine tsum_congr fun leaf => ?_
        cases hmem : seenLeaves.contains leaf
        · rfl
        · simp only [↓reduceIte]
          have h1 : ((coinSignBody S T depth M n leaf req.2 cc).map fun out =>
              (out.1, (out.2, (req.2 :: queried, seenLeaves, true)))) (a, s') = 0 := by
            rw [PMF.apply_eq_zero_iff]
            intro hsupp
            obtain ⟨out, -, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hsupp
            exact hs' (congrArg (fun x => x.2.2.2.2) heq.symm)
          have h2 : (PMF.pure ([], (cc, (req.2 :: queried, seenLeaves, true))) :
              PMF (List Bool × GuardedCoinState)) (a, s') = 0 := by
            rw [PMF.apply_eq_zero_iff]
            intro hsupp
            have heq := (PMF.mem_support_pure_iff _ _).mp hsupp
            exact hs' (congrArg (fun x => x.2.2.2.2) heq)
          rw [h1, h2]
      · rfl
  absorb_first q s hs x hx := by
    cases q with
    | inl k =>
      change x ∈ ((ProbComp.unifOracle k).map (·, s)).support at hx
      obtain ⟨_, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
      exact hs
    | inr req =>
      obtain ⟨cc, queried, seenLeaves, bad⟩ := s
      dsimp only at hs
      subst hs
      change x ∈ (unguardedCoinHandler S T depth M n req (cc, queried, seenLeaves, true)).support
        at hx
      simp only [unguardedCoinHandler, PMF.monad_bind_eq_bind, Bool.true_or, ↓reduceIte] at hx
      split_ifs at hx with hmsg
      · obtain ⟨leaf, -, hx⟩ := (PMF.mem_support_bind_iff _ _ _).mp hx
        obtain ⟨out, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
        rfl
      · obtain rfl := (PMF.mem_support_pure_iff _ _).mp hx
        rfl
  absorb_second q s hs x hx := by
    cases q with
    | inl k =>
      change x ∈ ((ProbComp.unifOracle k).map (·, s)).support at hx
      obtain ⟨_, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
      exact hs
    | inr req =>
      obtain ⟨cc, queried, seenLeaves, bad⟩ := s
      dsimp only at hs
      subst hs
      change x ∈ (guardedCoinHandler S T depth M n req (cc, queried, seenLeaves, true)).support
        at hx
      simp only [guardedCoinHandler, ↓reduceIte] at hx
      split_ifs at hx with hmsg <;>
        · obtain rfl := (PMF.mem_support_pure_iff _ _).mp hx
          rfl

private theorem toOuterMeasure_bad_queryBounded_le {α σ : Type}
    (extHandler : Unit × List Bool → StateT σ PMF (List Bool))
    (bad : σ → Prop) (seen : σ → ℕ) (d : ℕ)
    (hstep : ∀ q s, ¬ bad s →
      (extHandler q s).toOuterMeasure {x | bad x.2} ≤
        (seen s : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ d))
    (hgrow : ∀ q s, ¬ bad s → ∀ x ∈ (extHandler q s).support, ¬ bad x.2 →
      seen x.2 ≤ seen s + 1)
    {prog : WordOracleComp Unit α} {Q : ℕ} (hq : prog.IsQueryBounded Q)
    {s : σ} (hs : ¬ bad s) :
    ((OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k)) extHandler)
      prog).run s).toOuterMeasure {x | bad x.2} ≤
      ((2 * Q * seen s + Q ^ 2 : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ (d + 1)) := by
  classical
  set ε : ℝ≥0∞ := (1 : ℝ≥0∞) / 2 ^ (d + 1)
  have htwo : (1 : ℝ≥0∞) / 2 ^ d = 2 * ε := by
    simp only [ε, one_div, pow_succ']
    rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)), ← mul_assoc,
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  induction hq generalizing s with
  | pure a Q =>
    simp only [OracleComp.run_interpret_pure, Probability.PMF.monad_pure_eq_pure,
      PMF.toOuterMeasure_pure_apply]
    have hnot : (a, s) ∉ {x : α × σ | bad x.2} := hs
    simp only [hnot, ↓reduceIte]
    exact zero_le
  | liftBind q cont rem hcont ih =>
    cases q with
    | inl k =>
      simp only [Sum.elim_inl, Nat.add_zero]
      simp only [OracleComp.run_interpret_bind, OracleComp.run_interpret_query,
        Probability.PMF.monad_bind_eq_bind]
      change (((ProbComp.unifOracle k).map (·, s)).bind fun x =>
        (OracleComp.interpret
          (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k)) extHandler)
          (cont x.1)).run x.2).toOuterMeasure {x | bad x.2} ≤ _
      rw [PMF.bind_map, Function.comp_def, PMF.toOuterMeasure_bind_apply]
      calc ∑' i, ProbComp.unifOracle k i *
            ((OracleComp.interpret
              (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k)) extHandler)
              (cont i)).run s).toOuterMeasure {x | bad x.2}
          ≤ ∑' i, ProbComp.unifOracle k i *
              (((2 * rem * seen s + rem ^ 2 : ℕ) : ℝ≥0∞) * ε) :=
            tsum_le_tsum fun i => mul_le_mul_of_nonneg_left (ih i hs) zero_le
        _ = ((2 * rem * seen s + rem ^ 2 : ℕ) : ℝ≥0∞) * ε := by
            rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    | inr req =>
      simp only [Sum.elim_inr]
      simp only [OracleComp.run_interpret_bind, OracleComp.run_interpret_query,
        Probability.PMF.monad_bind_eq_bind]
      change ((extHandler req s).bind fun y =>
        (OracleComp.interpret
          (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k)) extHandler)
          (cont y.1)).run y.2).toOuterMeasure {x | bad x.2} ≤ _
      set K : ℝ≥0∞ := ((2 * rem * (seen s + 1) + rem ^ 2 : ℕ) : ℝ≥0∞) * ε
      calc _ ≤ (extHandler req s).toOuterMeasure {x | bad x.2} + K := by
            refine Probability.PMF.toOuterMeasure_bind_le_add _ _ _ _ K fun y hmem hy => ?_
            have hnat : 2 * rem * seen y.2 + rem ^ 2 ≤ 2 * rem * (seen s + 1) + rem ^ 2 := by
              have := hgrow req s hs y hmem hy
              nlinarith
            exact (ih y.1 hy).trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hnat) zero_le)
        _ ≤ (seen s : ℝ≥0∞) * (2 * ε) + K := by
            rw [← htwo]
            exact add_le_add_left (hstep req s hs) K
        _ = ((2 * seen s + (2 * rem * (seen s + 1) + rem ^ 2) : ℕ) : ℝ≥0∞) * ε := by
            simp only [K, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
            ring
        _ ≤ ((2 * (rem + 1) * seen s + (rem + 1) ^ 2 : ℕ) : ℝ≥0∞) * ε := by
            have hnat : 2 * seen s + (2 * rem * (seen s + 1) + rem ^ 2) ≤
                2 * (rem + 1) * seen s + (rem + 1) ^ 2 := by nlinarith
            exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hnat) zero_le

private theorem step_bad_guardedCoinHandler (S : IndexedSignatureScheme) (T : S.Seeded)
    (depth : ℕ → ℕ) (M n : ℕ) (req : Unit × List Bool) (s : GuardedCoinState)
    (hs : ¬ s.2.2.2 = true) :
    (guardedCoinHandler S T depth M n req s).toOuterMeasure {x | x.2.2.2.2 = true} ≤
      (s.2.2.1.length : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ depth n) := by
  obtain ⟨cc, queried, seenLeaves, bad⟩ := s
  have hbad : bad = false := Bool.eq_false_iff.mpr hs
  subst hbad
  simp only [guardedCoinHandler, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    Bool.false_eq_true, ↓reduceIte]
  split_ifs with hmsg
  · classical
    rw [PMF.toOuterMeasure_bind_apply]
    have hpt (leaf : List Bool) :
        ((if seenLeaves.contains leaf = true then
          PMF.pure ([], (cc, req.2 :: queried, seenLeaves, true))
        else
          (coinSignBody S T depth M n leaf req.2 cc).map fun out =>
            (out.1, (out.2, req.2 :: queried, leaf :: seenLeaves, false))).toOuterMeasure
          {x | x.2.2.2.2 = true}) ≤
        ((seenLeaves.toFinset : Set (List Bool)).indicator 1 leaf : ℝ≥0∞) := by
      cases hmem : seenLeaves.contains leaf
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hzero : ((coinSignBody S T depth M n leaf req.2 cc).map fun out =>
            (out.1, (out.2, req.2 :: queried, leaf :: seenLeaves, false))).toOuterMeasure
            {x | x.2.2.2.2 = true} = 0 := by
          rw [PMF.toOuterMeasure_apply, tsum_eq_zero_iff]
          intro x
          by_cases hx : x ∈ {x : List Bool × GuardedCoinState | x.2.2.2.2 = true}
          · rw [Set.indicator_of_mem hx, (PMF.apply_eq_zero_iff _ _).mpr]
            intro hsupp
            obtain ⟨out, -, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hsupp
            have hfalse : x.2.2.2.2 = false := congrArg (fun z => z.2.2.2.2) heq.symm
            exact Bool.false_ne_true (hfalse.symm.trans hx)
          · rw [Set.indicator_of_notMem hx]
        rw [hzero]
        exact zero_le
      · simp only [↓reduceIte]
        have hin : leaf ∈ (seenLeaves.toFinset : Set (List Bool)) := by
          rw [Finset.mem_coe, List.mem_toFinset]
          exact List.contains_iff_mem.mp hmem
        rw [Set.indicator_of_mem hin, Pi.one_apply]
        exact Probability.PMF.toOuterMeasure_le_one _ _
    calc ∑' leaf, BitString.uniformList (depth n) leaf * _
        ≤ ∑' leaf, BitString.uniformList (depth n) leaf *
            ((seenLeaves.toFinset : Set (List Bool)).indicator 1 leaf : ℝ≥0∞) :=
          tsum_le_tsum fun leaf => mul_le_mul_of_nonneg_left (hpt leaf) zero_le
      _ = (BitString.uniformList (depth n)).toOuterMeasure
            (seenLeaves.toFinset : Set (List Bool)) := by
          rw [PMF.toOuterMeasure_apply]
          refine tsum_congr fun leaf => ?_
          by_cases hl : leaf ∈ (seenLeaves.toFinset : Set (List Bool))
          · rw [Set.indicator_of_mem hl, Set.indicator_of_mem hl, Pi.one_apply, mul_one]
          · rw [Set.indicator_of_notMem hl, Set.indicator_of_notMem hl, mul_zero]
      _ ≤ (seenLeaves.toFinset.card : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ depth n) :=
          BitString.toOuterMeasure_uniformList_finset_le (depth n) seenLeaves.toFinset
      _ ≤ (seenLeaves.length : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ depth n) := by
          gcongr
          exact_mod_cast List.toFinset_card_le seenLeaves
  · simp only [PMF.toOuterMeasure_pure_apply]
    have hnot : (([], (cc, req.2 :: queried, seenLeaves, false)) : List Bool × GuardedCoinState) ∉
        {x : List Bool × GuardedCoinState | x.2.2.2.2 = true} := Bool.false_ne_true
    simp only [hnot, ↓reduceIte]
    exact zero_le

private theorem grow_seen_guardedCoinHandler (S : IndexedSignatureScheme) (T : S.Seeded)
    (depth : ℕ → ℕ) (M n : ℕ) (req : Unit × List Bool) (s : GuardedCoinState)
    (hs : ¬ s.2.2.2 = true) (x : List Bool × GuardedCoinState)
    (hx : x ∈ (guardedCoinHandler S T depth M n req s).support) (hxbad : ¬ x.2.2.2.2 = true) :
    x.2.2.2.1.length ≤ s.2.2.1.length + 1 := by
  obtain ⟨cc, queried, seenLeaves, bad⟩ := s
  have hbad : bad = false := Bool.eq_false_iff.mpr hs
  subst hbad
  simp only [guardedCoinHandler, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    Bool.false_eq_true, ↓reduceIte] at hx
  split_ifs at hx with hmsg
  · obtain ⟨leaf, -, hx⟩ := (PMF.mem_support_bind_iff _ _ _).mp hx
    split_ifs at hx with hmem
    · obtain rfl := (PMF.mem_support_pure_iff _ _).mp hx
      exact False.elim (hxbad rfl)
    · obtain ⟨out, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
      exact le_rfl
  · obtain rfl := (PMF.mem_support_pure_iff _ _).mp hx
    exact Nat.le_succ _

private abbrev JointLazyState := CoinCache × LazyTreeState

private noncomputable def jointNodeKey (S : IndexedSignatureScheme) (T : S.Seeded) (M n : ℕ)
    (path : List Bool) (st : CoinCache × NodeKeyCache) :
    PMF ((List Bool × List Bool) × (CoinCache × NodeKeyCache)) :=
  (lazyCoinRequest M (keyInput path) (T.keyGenBudget n) st.1).map fun out =>
    let key := T.keyGenWith n out.1
    let nodes' := match st.2.lookup path with
      | some _ => st.2
      | none => (path, key) :: st.2
    (key, (out.2, nodes'))

private noncomputable def jointSignAt (S : IndexedSignatureScheme) (T : S.Seeded) (M : ℕ)
    (path sk : List Bool) (u : ℕ) (msg : List Bool) (st : CoinCache × EdgeSigCache) :
    PMF (List Bool × (CoinCache × EdgeSigCache)) :=
  (lazyCoinRequest M (signInput path u) (T.signBudget sk u msg) st.1).map fun out =>
    let σ := T.signWith sk u msg out.1
    let edges' := match st.2.lookup (path, u) with
      | some _ => st.2
      | none => ((path, u), σ) :: st.2
    (σ, (out.2, edges'))

private noncomputable def jointCertifyStep (S : IndexedSignatureScheme) (T : S.Seeded) (M n : ℕ)
    (leaf : List Bool) (st : CoinCache × LazyCertState) : PMF (CoinCache × LazyCertState) := do
  let (cc, ((node, (_, sk), certs), (nodes, edges))) := st
  let bit := leaf.getD node.length false
  let childPath := node ++ [bit]
  let (child, (cc', nodes')) ← jointNodeKey S T M n childPath (cc, nodes)
  (jointSignAt S T M node sk bit.toNat child.1 (cc', edges)).map fun (σ, (cc'', edges')) =>
    (cc'', ((childPath, child, certs ++ [(child.1, σ)]), (nodes', edges')))

private noncomputable def jointCertify (S : IndexedSignatureScheme) (T : S.Seeded)
    (depth : ℕ → ℕ) (M n : ℕ) (leaf : List Bool)
    (st : CoinCache × (NodeKeyCache × EdgeSigCache)) : PMF (CoinCache × LazyCertState) := do
  let (root, (cc₀, nodes₀)) ← jointNodeKey S T M n [] (st.1, st.2.1)
  Nat.iterate (fun m => m.bind (jointCertifyStep S T M n leaf)) (depth n - 1)
    (PMF.pure (cc₀, (([], root, []), (nodes₀, st.2.2))))

private noncomputable def jointCoinHandler (S : IndexedSignatureScheme) (T : S.Seeded)
    (depth : ℕ → ℕ) (M n : ℕ) (request : Unit × List Bool) :
    StateT JointLazyState PMF (List Bool) := fun state =>
  let msg := request.2
  let (cc, ((nodes, edges), (queried, seenLeaves, bad))) := state
  if msg.length = n then
    if bad then
      PMF.pure ([], (cc, ((nodes, edges), (msg :: queried, seenLeaves, true))))
    else do
      let leaf ← BitString.uniformList (depth n)
      if seenLeaves.contains leaf then
        pure ([], (cc, ((nodes, edges), (msg :: queried, seenLeaves, true))))
      else
        let (cc', ((node, (_, sk), certs), (nodes', edges'))) ←
          jointCertify S T depth M n leaf (cc, (nodes, edges))
        (jointSignAt S T M node sk (leaf.getLastD false).toNat msg (cc', edges')).map
          fun (σ, (cc'', edges'')) =>
            (encodeSignature leaf certs σ,
              (cc'', ((nodes', edges''), (msg :: queried, leaf :: seenLeaves, false))))
  else
    PMF.pure ([], (cc, ((nodes, edges), (msg :: queried, seenLeaves, bad))))

private theorem interpret_iterate_pmf {σ ext : Type}
    (h : Unit × List Bool → StateT ext PMF (List Bool))
    (m : ℕ) (step : σ → WordOracleComp Unit σ) (init : σ) (cc : ext) :
    (OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k)) h)
      (OracleComp.iterate m step init)).run cc =
      Nat.iterate
        (fun dist => dist.bind fun (s, c) =>
          (OracleComp.interpret
            (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k)) h)
            (step s)).run c)
        m (PMF.pure (init, cc)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [OracleComp.iterate_succ, OracleComp.run_interpret_bind,
      Probability.PMF.monad_bind_eq_bind, ih, Function.iterate_succ_apply']

private theorem eval_iterate_probComp {σ : Type}
    (m : ℕ) (step : σ → ProbComp σ) (init : σ) :
    ProbComp.eval (OracleComp.iterate m step init) =
      Nat.iterate (fun dist => dist.bind fun s => ProbComp.eval (step s)) m (PMF.pure init) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [OracleComp.iterate_succ, ProbComp.eval_bind, ih, Function.iterate_succ_apply']

private theorem bind_bind_comm_of_invariant {α₁ β₁ α β γ : Type}
    (d₁ : PMF α₁) (exp₁ : α₁ → PMF γ) (rep₁ : α₁ → β₁) (d₂ : γ → PMF β₁) (inv₁ : α₁ → Prop)
    (exp₀ : PMF γ)
    (f₁ : α₁ → PMF α) (exp : α → PMF γ) (rep : α → β) (f₂ : γ → β₁ → PMF β) (inv : α → Prop)
    (hd : (d₁.bind fun a => (exp₁ a).map (·, rep₁ a)) =
        (exp₀.bind fun k => (d₂ k).map (k, ·)) ∧ ∀ a ∈ d₁.support, inv₁ a)
    (hf : ∀ a ∈ d₁.support, inv₁ a →
      ((f₁ a).bind fun b => (exp b).map (·, rep b)) =
        ((exp₁ a).bind fun k => (f₂ k (rep₁ a)).map (k, ·)) ∧
      ∀ b ∈ (f₁ a).support, inv b) :
    ((d₁.bind f₁).bind fun b => (exp b).map (·, rep b)) =
      (exp₀.bind fun k => ((d₂ k).bind (f₂ k)).map (k, ·)) ∧
    ∀ b ∈ (d₁.bind f₁).support, inv b := by
  refine ⟨?_, ?_⟩
  · rw [PMF.bind_bind]
    have hcongr : (d₁.bind fun a => (f₁ a).bind fun b => (exp b).map (·, rep b)) =
        (d₁.bind fun a => (exp₁ a).bind fun k => (f₂ k (rep₁ a)).map (k, ·)) :=
      PMF.bind_congr_on_support _ _ _ fun a ha => (hf a ha (hd.2 a ha)).1
    rw [hcongr]
    have h2 := congrArg (fun d => d.bind fun (k, b₁) => (f₂ k b₁).map (k, ·)) hd.1
    simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def] at h2 ⊢
    rw [h2]
    refine PMF.bind_congr_on_support _ _ _ fun k _ => ?_
    simp only [PMF.map_bind]
  · intro b hb
    obtain ⟨a, ha, hmem⟩ := (PMF.mem_support_bind_iff _ _ _).mp hb
    exact (hf a ha (hd.2 a ha)).2 b hmem

private theorem bind_map_of_invariant {α₁ β₁ α β : Type}
    (d₁ : PMF α₁) (d₂ : PMF β₁) (rep₁ : α₁ → β₁) (inv₁ : α₁ → Prop)
    (f₁ : α₁ → PMF α) (f₂ : β₁ → PMF β) (rep : α → β) (inv : α → Prop)
    (hd : d₁.map rep₁ = d₂ ∧ ∀ a ∈ d₁.support, inv₁ a)
    (hf : ∀ a ∈ d₁.support, inv₁ a →
      (f₁ a).map rep = f₂ (rep₁ a) ∧ ∀ b ∈ (f₁ a).support, inv b) :
    (d₁.bind f₁).map rep = d₂.bind f₂ ∧ ∀ b ∈ (d₁.bind f₁).support, inv b := by
  have hmain := bind_bind_comm_of_invariant d₁ (fun _ => PMF.pure ()) rep₁ (fun _ => d₂) inv₁
    (PMF.pure ()) f₁ (fun _ => PMF.pure ()) rep (fun _ => f₂) inv
    ⟨by rw [PMF.pure_bind, ← hd.1]; simp only [PMF.map, PMF.bind_bind,
      PMF.pure_bind, Function.comp_def], hd.2⟩
    fun a ha hia => by
      obtain ⟨heq, hinv⟩ := hf a ha hia
      refine ⟨?_, hinv⟩
      rw [PMF.pure_bind, ← heq]
      simp only [PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
  exact ⟨by simpa only [PMF.map, PMF.pure_bind, PMF.bind_pure, PMF.bind_bind,
    Function.comp_def] using congrArg (PMF.map Prod.snd) hmain.1, hmain.2⟩

private theorem eval_ite {α : Type} (P : Prop) [Decidable P] (a b : ProbComp α) :
    ProbComp.eval (if P then a else b) = if P then ProbComp.eval a else ProbComp.eval b := by
  split_ifs <;> rfl

private theorem run_interpret_ite {ι ext α : Type} {spec : ι → Type}
    (h : (q : ι) → StateT ext PMF (spec q)) (P : Prop) [Decidable P]
    (a b : OracleComp spec α) (s : ext) :
    (OracleComp.interpret h (if P then a else b)).run s =
      if P then (OracleComp.interpret h a).run s else (OracleComp.interpret h b).run s := by
  split_ifs <;> rfl

private theorem pmf_map_ite {α β : Type} (P : Prop) [Decidable P] (a b : PMF α) (f : α → β) :
    (if P then a else b).map f = if P then a.map f else b.map f := by
  split_ifs <;> rfl

private theorem iterate_pmf_bind_comm_of_invariant {α β γ : Type}
    (step₁ : α → PMF α) (step₂ : γ → β → PMF β)
    (exp : α → PMF γ) (rep : α → β) (inv : ℕ → α → Prop)
    (m : ℕ) (init : α) (hinit : inv 0 init)
    (hstep : ∀ i < m, ∀ a, inv i a →
      ((step₁ a).bind fun a' => (exp a').map (·, rep a')) =
        ((exp a).bind fun k => (step₂ k (rep a)).map (k, ·)) ∧
      ∀ a' ∈ (step₁ a).support, inv (i + 1) a') :
    let jDist := Nat.iterate (fun d => d.bind step₁) m (PMF.pure init)
    (jDist.bind fun a => (exp a).map (·, rep a)) =
      ((exp init).bind fun k =>
        (Nat.iterate (fun d => d.bind (step₂ k)) m (PMF.pure (rep init))).map (k, ·)) ∧
      ∀ a ∈ jDist.support, inv m a := by
  induction m with
  | zero =>
    refine ⟨?_, fun a ha => ?_⟩
    · simp only [Function.iterate_zero, id_eq, PMF.pure_bind, PMF.map, Function.comp_def]
    · obtain rfl := (PMF.mem_support_pure_iff _ _).mp ha
      exact hinit
  | succ m ih =>
    obtain ⟨heq, hsupp⟩ := ih fun i hi => hstep i (Nat.lt_succ_of_lt hi)
    set jDist_m := Nat.iterate (fun d => d.bind step₁) m (PMF.pure init)
    refine ⟨?_, ?_⟩
    · rw [Function.iterate_succ_apply', PMF.bind_bind]
      have hbind : (jDist_m.bind fun a => (step₁ a).bind fun a' => (exp a').map (·, rep a')) =
          (jDist_m.bind fun a => (exp a).bind fun k => (step₂ k (rep a)).map (k, ·)) :=
        PMF.bind_congr_on_support _ _ _ fun a ha =>
          (hstep m (Nat.lt_succ_self m) a (hsupp a ha)).1
      rw [hbind]
      have h2 := congrArg (fun d => d.bind fun (k, b) => (step₂ k b).map (k, ·)) heq
      simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def] at h2 ⊢
      rw [h2]
      refine PMF.bind_congr_on_support _ _ _ fun k _ => ?_
      rw [Function.iterate_succ_apply']
      simp only [PMF.map_bind]
    · intro a' ha'
      rw [Function.iterate_succ_apply'] at ha'
      obtain ⟨a, ha, hm⟩ := (PMF.mem_support_bind_iff _ _ _).mp ha'
      exact (hstep m (Nat.lt_succ_self m) a (hsupp a ha)).2 a' hm

private theorem iterate_pmf_map_of_invariant {α β : Type}
    (step₁ : α → PMF α) (step₂ : β → PMF β) (rep : α → β) (inv : ℕ → α → Prop)
    (m : ℕ) (init : α) (hinit : inv 0 init)
    (hstep : ∀ i < m, ∀ a, inv i a →
      (step₁ a).map rep = step₂ (rep a) ∧ ∀ a' ∈ (step₁ a).support, inv (i + 1) a') :
    let dist := Nat.iterate (fun d => d.bind step₁) m (PMF.pure init)
    dist.map rep = Nat.iterate (fun d => d.bind step₂) m (PMF.pure (rep init)) ∧
      ∀ a ∈ dist.support, inv m a := by
  have hmain := iterate_pmf_bind_comm_of_invariant step₁ (fun _ => step₂)
    (fun _ => PMF.pure ()) rep inv m init hinit fun i hi a ha => by
      obtain ⟨heq, hinv⟩ := hstep i hi a ha
      refine ⟨?_, hinv⟩
      rw [PMF.pure_bind, ← heq]
      simp only [PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
  exact ⟨by simpa only [PMF.map, PMF.pure_bind, PMF.bind_pure, PMF.bind_bind,
    Function.comp_def] using congrArg (PMF.map Prod.snd) hmain.1, hmain.2⟩

private theorem iterate_pmf_invariant {α : Type}
    (step : α → PMF α) (inv : ℕ → α → Prop) (m : ℕ) (init : α) (hinit : inv 0 init)
    (hstep : ∀ i < m, ∀ a, inv i a → ∀ a' ∈ (step a).support, inv (i + 1) a') :
    ∀ a ∈ (Nat.iterate (fun d => d.bind step) m (PMF.pure init)).support, inv m a :=
  (iterate_pmf_map_of_invariant step (fun _ => PMF.pure ()) (fun _ => ()) inv m init hinit
    fun i hi a ha => ⟨by rw [PMF.map_const], hstep i hi a ha⟩).2

private theorem treeHandler_bind_comm_of_invariant {α β γ : Type}
    (P Q : Prop) [Decidable P] [Decidable Q]
    (leafDist : PMF (List Bool)) (seen : List Bool → Bool)
    (rn₁ rb₁ rc₁ : α) (g₁ : List Bool → PMF α)
    (exp₀ : PMF γ) (exp : α → PMF γ) (rep : α → β)
    (rn₂ rb₂ rc₂ : γ → β) (g₂ : γ → List Bool → PMF β) (inv : α → Prop)
    (hrn : (exp rn₁).map (·, rep rn₁) = exp₀.map (fun k => (k, rn₂ k)) ∧ inv rn₁)
    (hrb : (exp rb₁).map (·, rep rb₁) = exp₀.map (fun k => (k, rb₂ k)) ∧ inv rb₁)
    (hrc : (exp rc₁).map (·, rep rc₁) = exp₀.map (fun k => (k, rc₂ k)) ∧ inv rc₁)
    (hgood : P → ¬ Q → ∀ leaf ∈ leafDist.support, seen leaf = false →
      ((g₁ leaf).bind fun x => (exp x).map (·, rep x)) =
        (exp₀.bind fun k => (g₂ k leaf).map (k, ·)) ∧
      ∀ x ∈ (g₁ leaf).support, inv x) :
    let lhs : PMF α :=
      if P then
        if Q then PMF.pure rb₁
        else leafDist.bind fun leaf => if seen leaf then PMF.pure rc₁ else g₁ leaf
      else PMF.pure rn₁
    (lhs.bind fun x => (exp x).map (·, rep x)) =
      (exp₀.bind fun k =>
        (if P then
          if Q then PMF.pure (rb₂ k)
          else leafDist.bind fun leaf => if seen leaf then PMF.pure (rc₂ k) else g₂ k leaf
        else PMF.pure (rn₂ k)).map (k, ·)) ∧
    ∀ x ∈ lhs.support, inv x := by
  dsimp only
  split_ifs with hP hQ
  · refine ⟨(by
      rw [PMF.pure_bind]; simp only [PMF.pure_map]
      simpa only [PMF.map, Function.comp_def] using hrb.1), fun x hx => ?_⟩
    obtain rfl := (PMF.mem_support_pure_iff _ _).mp hx
    exact hrb.2
  · refine ⟨?_, ?_⟩
    · rw [PMF.bind_bind]
      simp_rw [PMF.map_bind]
      rw [PMF.bind_comm exp₀ leafDist]
      refine PMF.bind_congr_on_support _ _ _ fun leaf hl => ?_
      cases hs : seen leaf
      · simp only [Bool.false_eq_true, ↓reduceIte]
        simpa only [PMF.map_bind] using (hgood hP hQ leaf hl hs).1
      · simp only [↓reduceIte, PMF.pure_bind, PMF.pure_map]
        exact hrc.1
    · intro x hx
      obtain ⟨leaf, hl, hmem⟩ := (PMF.mem_support_bind_iff _ _ _).mp hx
      cases hs : seen leaf
      · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hmem
        exact (hgood hP hQ leaf hl hs).2 x hmem
      · simp only [hs, ↓reduceIte] at hmem
        obtain rfl := (PMF.mem_support_pure_iff _ _).mp hmem
        exact hrc.2
  · refine ⟨(by
      rw [PMF.pure_bind]; simp only [PMF.pure_map]
      simpa only [PMF.map, Function.comp_def] using hrn.1), fun x hx => ?_⟩
    obtain rfl := (PMF.mem_support_pure_iff _ _).mp hx
    exact hrn.2

private theorem treeHandler_map_of_invariant {α β : Type}
    (P Q : Prop) [Decidable P] [Decidable Q]
    (leafDist : PMF (List Bool)) (seen : List Bool → Bool)
    (rn₁ rb₁ rc₁ : α) (g₁ : List Bool → PMF α) (rep : α → β)
    (rn₂ rb₂ rc₂ : β) (g₂ : List Bool → PMF β) (inv : α → Prop)
    (hrn : rep rn₁ = rn₂ ∧ inv rn₁) (hrb : rep rb₁ = rb₂ ∧ inv rb₁)
    (hrc : rep rc₁ = rc₂ ∧ inv rc₁)
    (hgood : P → ¬ Q → ∀ leaf ∈ leafDist.support, seen leaf = false →
      (g₁ leaf).map rep = g₂ leaf ∧ ∀ x ∈ (g₁ leaf).support, inv x) :
    let lhs : PMF α :=
      if P then
        if Q then PMF.pure rb₁
        else leafDist.bind fun leaf => if seen leaf then PMF.pure rc₁ else g₁ leaf
      else PMF.pure rn₁
    lhs.map rep =
      (if P then
        if Q then PMF.pure rb₂
        else leafDist.bind fun leaf => if seen leaf then PMF.pure rc₂ else g₂ leaf
      else PMF.pure rn₂) ∧
    ∀ x ∈ lhs.support, inv x := by
  have hmain := treeHandler_bind_comm_of_invariant P Q leafDist seen rn₁ rb₁ rc₁ g₁
    (PMF.pure ()) (fun _ => PMF.pure ()) rep (fun _ => rn₂) (fun _ => rb₂) (fun _ => rc₂)
    (fun _ => g₂) inv
    ⟨by rw [hrn.1], hrn.2⟩
    ⟨by rw [hrb.1], hrb.2⟩
    ⟨by rw [hrc.1], hrc.2⟩
    fun hP hQ leaf hl hs => by
      obtain ⟨heq, hinv⟩ := hgood hP hQ leaf hl hs
      refine ⟨?_, hinv⟩
      rw [PMF.pure_bind, ← heq]
      simp only [PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
  exact ⟨by simpa only [PMF.map, PMF.pure_bind, PMF.bind_pure, PMF.bind_bind,
    Function.comp_def] using congrArg (PMF.map Prod.snd) hmain.1, hmain.2⟩

private theorem treeHandler_support_invariant {α : Type}
    (P Q : Prop) [Decidable P] [Decidable Q]
    (leafDist : PMF (List Bool)) (seen : List Bool → Bool)
    (rn rb rc : α) (g : List Bool → PMF α) (inv : α → Prop)
    (hrn : inv rn) (hrb : inv rb) (hrc : inv rc)
    (hgood : P → ¬ Q → ∀ leaf ∈ leafDist.support, seen leaf = false →
      ∀ x ∈ (g leaf).support, inv x) :
    ∀ x ∈ (if P then
        if Q then PMF.pure rb
        else leafDist.bind fun leaf => if seen leaf then PMF.pure rc else g leaf
      else PMF.pure rn).support, inv x :=
  (treeHandler_map_of_invariant P Q leafDist seen rn rb rc g (fun _ => ()) () () ()
    (fun _ => PMF.pure ()) inv ⟨rfl, hrn⟩ ⟨rfl, hrb⟩ ⟨rfl, hrc⟩
    fun hP hQ leaf hl hs => ⟨by rw [PMF.map_const], hgood hP hQ leaf hl hs⟩).2

private theorem run_interpret_queryBounded_bind_comm {α σ₁ σ₂ γ : Type}
    (h₁ : Unit × List Bool → StateT σ₁ PMF (List Bool))
    (h₂ : γ → Unit × List Bool → StateT σ₂ PMF (List Bool))
    (exp : σ₁ → PMF γ) (rep : σ₁ → σ₂) (inv : ℕ → σ₁ → Prop)
    (hweaken : ∀ r s, inv (r + 1) s → inv r s)
    (hstep : ∀ rem req s, inv (rem + 1) s →
      ((h₁ req s).bind fun x => (exp x.2).map fun k => (k, x.1, rep x.2)) =
        ((exp s).bind fun k => (h₂ k req (rep s)).map fun y => (k, y.1, y.2)) ∧
      ∀ ans s', (ans, s') ∈ (h₁ req s).support → inv rem s')
    {prog : WordOracleComp Unit α} {rem : ℕ} (hq : prog.IsQueryBounded rem)
    {st : σ₁} (hinv : inv rem st) :
    (((OracleComp.interpret
      (OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifOracle j)) h₁)
      prog).run st).bind fun x => (exp x.2).map fun k => (k, x.1, rep x.2)) =
      ((exp st).bind fun k =>
        ((OracleComp.interpret
          (OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifOracle j)) (h₂ k))
          prog).run (rep st)).map fun y => (k, y.1, y.2)) ∧
    ∀ res st', (res, st') ∈ ((OracleComp.interpret
      (OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifOracle j)) h₁)
      prog).run st).support → inv 0 st' := by
  have hzero : ∀ r s, inv r s → inv 0 s := by
    intro r
    induction r with
    | zero => exact fun _ h => h
    | succ r ih => exact fun s h => ih s (hweaken r s h)
  induction hq generalizing st with
  | pure a rem =>
    refine ⟨?_, fun res st' hm => ?_⟩
    · simp only [OracleComp.run_interpret_pure, Probability.PMF.monad_pure_eq_pure,
        PMF.pure_bind, PMF.map, Function.comp_def]
    · simp only [OracleComp.run_interpret_pure, Probability.PMF.monad_pure_eq_pure] at hm
      obtain ⟨_, rfl⟩ := Prod.mk.inj ((PMF.mem_support_pure_iff _ _).mp hm)
      exact hzero rem _ hinv
  | liftBind q cont rem _ ih =>
    cases q with
    | inl j =>
      simp only [Sum.elim_inl, Nat.add_zero] at hinv
      refine ⟨?_, ?_⟩
      · simp only [OracleComp.run_interpret_bind, OracleComp.run_interpret_query,
          Probability.PMF.monad_bind_eq_bind]
        change (((ProbComp.unifOracle j).map (·, st)).bind fun x =>
          (OracleComp.interpret
            (OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifOracle j)) h₁)
            (cont x.1)).run x.2).bind
            (fun x => (exp x.2).map fun k => (k, x.1, rep x.2)) = _
        rw [PMF.bind_map, Function.comp_def, PMF.bind_bind]
        simp_rw [(ih _ hinv).1]
        rw [PMF.bind_comm]
        refine PMF.bind_congr_on_support _ _ _ fun k _ => ?_
        change _ = (((ProbComp.unifOracle j).map (·, rep st)).bind fun x =>
          (OracleComp.interpret
            (OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifOracle j)) (h₂ k))
            (cont x.1)).run x.2).map fun y => (k, y.1, y.2)
        rw [PMF.bind_map, PMF.map_bind]
        rfl
      · intro res st' hm
        simp only [OracleComp.run_interpret_bind, OracleComp.run_interpret_query,
          Probability.PMF.monad_bind_eq_bind] at hm
        change (res, st') ∈ (((ProbComp.unifOracle j).map (·, st)).bind fun x =>
          (OracleComp.interpret
            (OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifOracle j)) h₁)
            (cont x.1)).run x.2).support at hm
        obtain ⟨⟨i, st₁⟩, hmi, hmc⟩ := (PMF.mem_support_bind_iff _ _ _).mp hm
        obtain ⟨_, -, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hmi
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        exact (ih _ hinv).2 res st' hmc
    | inr req =>
      simp only [Sum.elim_inr] at hinv
      obtain ⟨hstep_eq, hstep_supp⟩ := hstep rem req st hinv
      refine ⟨?_, ?_⟩
      · simp only [OracleComp.run_interpret_bind, OracleComp.run_interpret_query,
          Probability.PMF.monad_bind_eq_bind]
        change ((h₁ req st).bind fun x =>
          (OracleComp.interpret
            (OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifOracle j)) h₁)
            (cont x.1)).run x.2).bind
            (fun x => (exp x.2).map fun k => (k, x.1, rep x.2)) = _
        rw [PMF.bind_bind]
        have hcont : ((h₁ req st).bind fun x =>
              (((OracleComp.interpret
                (OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifOracle j)) h₁)
                (cont x.1)).run x.2).bind fun x =>
                  (exp x.2).map fun k => (k, x.1, rep x.2))) =
            ((h₁ req st).bind fun x =>
              (exp x.2).bind fun k =>
                ((OracleComp.interpret
                  (OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifOracle j)) (h₂ k))
                  (cont x.1)).run (rep x.2)).map fun y => (k, y.1, y.2)) :=
          PMF.bind_congr_on_support _ _ _ fun ⟨ans, s'⟩ hm =>
            (ih ans (hstep_supp ans s' hm)).1
        rw [hcont]
        have h2 := congrArg (fun d => d.bind fun x =>
          ((OracleComp.interpret
            (OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifOracle j)) (h₂ x.1))
            (cont x.2.1)).run x.2.2).map fun y => (x.1, y.1, y.2)) hstep_eq
        simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def] at h2
        rw [h2]
        refine PMF.bind_congr_on_support _ _ _ fun k _ => ?_
        change _ = ((h₂ k req (rep st)).bind fun x =>
          (OracleComp.interpret
            (OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifOracle j)) (h₂ k))
            (cont x.1)).run x.2).map fun y => (k, y.1, y.2)
        rw [PMF.map_bind]
      · intro res st' hm
        simp only [OracleComp.run_interpret_bind, OracleComp.run_interpret_query,
          Probability.PMF.monad_bind_eq_bind] at hm
        change (res, st') ∈ ((h₁ req st).bind fun x =>
          (OracleComp.interpret
            (OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifOracle j)) h₁)
            (cont x.1)).run x.2).support at hm
        obtain ⟨⟨ans, s'⟩, hms, hmc⟩ := (PMF.mem_support_bind_iff _ _ _).mp hm
        exact (ih ans (hstep_supp ans s' hms)).2 res st' hmc

private theorem run_interpret_queryBounded_invariant {α σ : Type}
    (h : Unit × List Bool → StateT σ PMF (List Bool)) (inv : ℕ → σ → Prop)
    (hweaken : ∀ r s, inv (r + 1) s → inv r s)
    (hstep : ∀ rem req s, inv (rem + 1) s → ∀ ans s', (ans, s') ∈ (h req s).support → inv rem s')
    {prog : WordOracleComp Unit α} {rem : ℕ} (hq : prog.IsQueryBounded rem)
    {st : σ} (hinv : inv rem st) :
    ∀ res st', (res, st') ∈ ((OracleComp.interpret
      (OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifOracle j)) h)
      prog).run st).support → inv 0 st' :=
  (run_interpret_queryBounded_bind_comm h (fun _ => h) (fun _ => PMF.pure ()) id inv hweaken
    (fun rem req s hs => ⟨by simp only [PMF.pure_bind, PMF.pure_map]; rfl, hstep rem req s hs⟩)
    hq hinv).2

private theorem map_dropCaches_jointSignAt (S : IndexedSignatureScheme) (T : S.Seeded)
    (M : ℕ) (path sk : List Bool) (u : ℕ) (msg : List Bool) (c : CoinCache)
    (es : EdgeSigCache) :
    (jointSignAt S T M path sk u msg (c, es)).map (fun out => (out.1, out.2.1)) =
      (OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
          (lazyCoinHandler M))
        (signAtO S T path sk u msg)).run c := by
  simp only [jointSignAt, signAtO, coinRequest, OracleComp.interpret_map,
    ProbOracleComp.interpret_query, StateT.run_map, PMF.monad_map_eq_map, PMF.map_comp,
    Function.comp_def]
  change (lazyCoinRequest M (signInput path u) (T.signBudget sk u msg) c).map _ =
    (lazyCoinHandler M ((), encPair encBits encUnary (signInput path u, T.signBudget sk u msg))
      c).map _
  simp only [lazyCoinHandler, coinRequestDecoder.decode_enc, lazyCoinRequest, PMF.map_comp,
    Function.comp_def, List.take_take, Nat.min_self]

private theorem map_dropCaches_jointCertify (S : IndexedSignatureScheme) (T : S.Seeded)
    (depth : ℕ → ℕ) (M n : ℕ) (leaf : List Bool) (cc : CoinCache)
    (caches : NodeKeyCache × EdgeSigCache) :
    (jointCertify S T depth M n leaf (cc, caches)).map (fun out => (out.2.1, out.1)) =
      (OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
          (lazyCoinHandler M))
        (certifyO S T depth n leaf)).run cc := by
  have hnk (path : List Bool) (c : CoinCache) (ns : NodeKeyCache) :
      (jointNodeKey S T M n path (c, ns)).map (fun out => (out.1, out.2.1)) =
        (OracleComp.interpret
          (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
            (lazyCoinHandler M))
          (nodeKeyO S T n path)).run c := by
    simp only [jointNodeKey, nodeKeyO, coinRequest, OracleComp.interpret_map,
      ProbOracleComp.interpret_query, StateT.run_map, PMF.monad_map_eq_map, PMF.map_comp,
      Function.comp_def]
    change (lazyCoinRequest M (keyInput path) (T.keyGenBudget n) c).map _ =
      (lazyCoinHandler M ((), encPair encBits encUnary (keyInput path, T.keyGenBudget n)) c).map _
    simp only [lazyCoinHandler, coinRequestDecoder.decode_enc, lazyCoinRequest, PMF.map_comp,
      Function.comp_def, List.take_take, Nat.min_self]
  simp only [jointCertify, certifyO, OracleComp.run_interpret_bind,
    Probability.PMF.monad_bind_eq_bind, PMF.map_bind, ← hnk [] cc caches.1, PMF.bind_map,
    Function.comp_def]
  refine PMF.bind_congr_on_support _ _ _ fun ⟨root, cc₀, nodes₀⟩ _ => ?_
  rw [interpret_iterate_pmf]
  refine (iterate_pmf_map_of_invariant (jointCertifyStep S T M n leaf) _
    (fun out => (out.2.1, out.1)) (fun _ _ => True) (depth n - 1)
    (cc₀, (([], root, []), (nodes₀, caches.2))) trivial fun _ _ out _ => ?_).1
  obtain ⟨c, ⟨node, ⟨pk, sk⟩, certs⟩, ns, es⟩ := out
  refine ⟨?_, fun _ _ => trivial⟩
  simp only [jointCertifyStep, certifyStepO, OracleComp.run_interpret_bind,
    OracleComp.run_interpret_pure, Probability.PMF.monad_bind_eq_bind,
    Probability.PMF.monad_pure_eq_pure, PMF.map_bind, PMF.map_comp, Function.comp_def,
    ← hnk (node ++ [leaf.getD node.length false]) c ns, PMF.bind_map]
  refine PMF.bind_congr_on_support _ _ _ fun ⟨child, c', ns'⟩ _ => ?_
  rw [← map_dropCaches_jointSignAt S T M node sk (leaf.getD node.length false).toNat child.1 c'
    es, PMF.bind_map]
  simp only [PMF.map, Function.comp_def]

private theorem map_dropCaches_jointCoinHandler (S : IndexedSignatureScheme) (T : S.Seeded)
    (depth : ℕ → ℕ) (M n : ℕ) (req : Unit × List Bool) (s : JointLazyState) :
    (jointCoinHandler S T depth M n req s).map (fun (a, s') => (a, (s'.1, s'.2.2))) =
      guardedCoinHandler S T depth M n req (s.1, s.2.2) := by
  obtain ⟨cc, ⟨nodes, edges⟩, queried, seenLeaves, bad⟩ := s
  simp only [jointCoinHandler, guardedCoinHandler, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  split_ifs with hmsg hbad
  · simp only [PMF.pure_map]
  · simp only [PMF.map_bind]
    refine PMF.bind_congr_on_support _ _ _ fun leaf _ => ?_
    split_ifs with hseen
    · simp only [PMF.pure_map]
    · simp only [coinSignBody, OracleComp.run_interpret_bind, OracleComp.run_interpret_pure,
        Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure,
        ← map_dropCaches_jointCertify S T depth M n leaf cc (nodes, edges),
        PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def]
      refine PMF.bind_congr_on_support _ _ _
        fun ⟨cc', ⟨node, ⟨pk, sk⟩, certs⟩, nodes', edges'⟩ _ => ?_
      dsimp only [Function.comp_def]
      rw [← map_dropCaches_jointSignAt S T M node sk (leaf.getLastD false).toNat req.2 cc' edges',
        PMF.bind_map]
      simp only [PMF.map, PMF.pure_bind, Function.comp_def]
  · simp only [PMF.pure_map]

private theorem take_sub_one_append_getLastD {l : List Bool} {d : ℕ} (hd : 1 ≤ d)
    (hl : l.length = d) : l.take (d - 1) ++ [l.getLastD false] = l := by
  have hlt : d - 1 < l.length := by omega
  have hlast : l.getLastD false = l[d - 1] := by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?]
    simp only [hl, Option.getD_eq_iff, List.getElem?_eq_getElem hlt, true_or]
  rw [hlast, ← List.take_succ_eq_append_getElem hlt, show d - 1 + 1 = l.length by omega,
    List.take_length]

private def jointLazyInv (S : IndexedSignatureScheme) (T : S.Seeded) (M d n : ℕ)
    (root : List Bool × List Bool) (s : JointLazyState) : Prop :=
  let (cc, ((nodes, edges), (_, seenLeaves, _))) := s
  nodes.lookup [] = some root ∧
  (∀ p k, (p, k) ∈ nodes → p.length < d ∧ k ∈ (ProbComp.eval (S.keyGen n)).support) ∧
  (∀ p, p.length < d →
    nodes.lookup p =
      (cc.lookup (padRequest M (keyInput p))).map
        (fun w => T.keyGenWith n (w.take (T.keyGenBudget n)))) ∧
  (∀ q v σ, ((q, v), σ) ∈ edges →
    q.length < d ∧ v ≤ 1 ∧
      (q.length = d - 1 → ∃ l ∈ seenLeaves, l.length = d ∧ q = l.take (d - 1) ∧
        v = (l.getLastD false).toNat)) ∧
  (∀ p u, p.length < d → u ≤ 1 → edges.lookup (p, u) = none →
    cc.lookup (padRequest M (signInput p u)) = none) ∧
  ∀ p (b : Bool) σ, p.length + 1 < d → edges.lookup (p, b.toNat) = some σ →
    ∃ kp kc w, nodes.lookup p = some kp ∧ nodes.lookup (p ++ [b]) = some kc ∧
      cc.lookup (padRequest M (signInput p b.toNat)) = some w ∧
      σ = T.signWith kp.2 b.toNat kc.1 (w.take (T.signBudget kp.2 b.toNat kc.1))

private theorem lookup_mem {K V : Type} [BEq K] [LawfulBEq K] {l : List (K × V)} {k : K} {v : V}
    (h : l.lookup k = some v) : (k, v) ∈ l := by
  obtain ⟨before, after, rfl, -⟩ := List.lookup_eq_some_iff.mp h
  exact List.mem_append_right _ (List.mem_cons_self)

private theorem jointNodeKey_spec (S : IndexedSignatureScheme) (T : S.Seeded) {M d n : ℕ}
    (hwidth : 2 * d + 4 ≤ M) (hkgBudget : T.keyGenBudget n ≤ M)
    {root : List Bool × List Bool} {s : JointLazyState}
    (hinv : jointLazyInv S T M d n root s) {path : List Bool} (hpath : path.length < d) :
    let (cc, ((nodes, edges), rest)) := s
    ((jointNodeKey S T M n path (cc, nodes)).map fun (k, (_, ns')) => (k, ns')) =
      ProbComp.eval (memoize (fun _ => S.keyGen n) path nodes) ∧
    ∀ k cc' ns', (k, (cc', ns')) ∈ (jointNodeKey S T M n path (cc, nodes)).support →
      jointLazyInv S T M d n root (cc', ((ns', edges), rest)) ∧
      ns'.lookup path = some k ∧ k ∈ (ProbComp.eval (S.keyGen n)).support ∧
      ∀ q v, nodes.lookup q = some v → q ≠ path → ns'.lookup q = some v := by
  obtain ⟨cc, ⟨nodes, edges⟩, queried, seenLeaves, bad⟩ := s
  obtain ⟨hroot, hnodesMem, hnodesLk, hedgesMem, hedgesNone, hedgesSome⟩ := hinv
  have hrel := hnodesLk path hpath
  simp only [jointNodeKey, lazyCoinRequest, memoize]
  cases hcc : cc.lookup (padRequest M (keyInput path)) with
  | some w =>
    rw [hcc, Option.map_some] at hrel
    constructor
    · simp only [hrel, Probability.PMF.monad_pure_eq_pure, PMF.pure_map, ProbComp.eval_pure]
    · intro k cc' ns' hmem
      simp only [hrel, Probability.PMF.monad_pure_eq_pure, PMF.pure_map] at hmem
      have heq := (PMF.mem_support_pure_iff _ _).mp hmem
      cases heq
      exact ⟨⟨hroot, hnodesMem, hnodesLk, hedgesMem, hedgesNone, hedgesSome⟩, hrel,
        T.keyGenWith_mem_support n _, fun _ _ h _ => h⟩
  | none =>
    rw [hcc, Option.map_none] at hrel
    simp only [hrel, bind_pure_comp, PMF.monad_map_eq_map, ProbComp.eval_map,
      PMF.map_comp, Function.comp_def]
    refine ⟨?_, ?_⟩
    · rw [T.eval_keyGen n (T.keyGenBudget n) le_rfl, ← BitString.uniformList_take hkgBudget,
        PMF.map_comp, PMF.map_comp]
      rfl
    · intro k cc' ns' hmem
      obtain ⟨w, -, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hmem
      obtain ⟨rfl, h2⟩ := Prod.mk.inj heq.symm
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
      have hstay {q : List Bool} {v : List Bool × List Bool} (hq : nodes.lookup q = some v) :
          ((path, T.keyGenWith n (w.take (T.keyGenBudget n))) :: nodes).lookup q = some v := by
        have hne : q ≠ path := fun h => by subst h; rw [hq] at hrel; cases hrel
        rw [List.lookup_cons, beq_false_of_ne hne]
        exact hq
      refine ⟨⟨hstay hroot, ?_, ?_, hedgesMem, ?_, ?_⟩, by simp,
        T.keyGenWith_mem_support n _, ?_⟩
      · intro p kp hp
        rcases List.mem_cons.mp hp with hhead | htail
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hhead
          exact ⟨hpath, T.keyGenWith_mem_support n _⟩
        · exact hnodesMem p kp htail
      · intro p hp
        by_cases hpeq : p = path
        · subst hpeq
          simp only [List.lookup_cons, beq_self_eq_true, Option.map_some]
        · have hpadNe : padRequest M (keyInput p) ≠ padRequest M (keyInput path) :=
            fun h => hpeq (padRequest_keyInput_injective hwidth hp hpath h)
          rw [List.lookup_cons, beq_false_of_ne hpeq, List.lookup_cons, beq_false_of_ne hpadNe]
          exact hnodesLk p hp
      · intro p u hp hu he
        have hpadNe : padRequest M (signInput p u) ≠ padRequest M (keyInput path) :=
          (padRequest_keyInput_ne_signInput hwidth hpath hp hu).symm
        rw [List.lookup_cons, beq_false_of_ne hpadNe]
        exact hedgesNone p u hp hu he
      · intro p b σ hp he
        obtain ⟨kp, kc, w', hkp, hkc, hw', hσ⟩ := hedgesSome p b σ hp he
        have hbu : b.toNat ≤ 1 := by cases b <;> simp
        have hp_lt : p.length < d := Nat.lt_of_succ_lt hp
        have hpadNe : padRequest M (signInput p b.toNat) ≠ padRequest M (keyInput path) :=
          (padRequest_keyInput_ne_signInput hwidth hpath hp_lt hbu).symm
        refine ⟨kp, kc, w', hstay hkp, hstay hkc, ?_, hσ⟩
        rw [List.lookup_cons, beq_false_of_ne hpadNe]
        exact hw'
      · intro q v hqv hne
        rw [List.lookup_cons, beq_false_of_ne hne]
        exact hqv

private theorem jointLazyInv_insert_sign (S : IndexedSignatureScheme) (T : S.Seeded)
    {M d n : ℕ} (hwidth : 2 * d + 4 ≤ M) {root : List Bool × List Bool}
    {c' : CoinCache} {ns' : NodeKeyCache} {es' : EdgeSigCache}
    {queried₀ seenLeaves₀ : List (List Bool)} {bad₀ : Bool}
    (queried₁ : List (List Bool)) {seenLeaves₁ : List (List Bool)} (bad₁ : Bool)
    (hinv : jointLazyInv S T M d n root (c', ((ns', es'), (queried₀, seenLeaves₀, bad₀))))
    (hsub : ∀ l ∈ seenLeaves₀, l ∈ seenLeaves₁)
    {node : List Bool} {u : ℕ} (hnode_lt : node.length < d) (hu : u ≤ 1)
    (w σ : List Bool)
    (hleaf_head : node.length = d - 1 →
      ∃ l ∈ seenLeaves₁, l.length = d ∧ node = l.take (d - 1) ∧ u = (l.getLastD false).toNat)
    (hinternal : ∀ b : Bool, b.toNat = u → node.length + 1 < d →
      ∃ kp kc, ns'.lookup node = some kp ∧ ns'.lookup (node ++ [b]) = some kc ∧
        σ = T.signWith kp.2 b.toNat kc.1 (w.take (T.signBudget kp.2 b.toNat kc.1))) :
    jointLazyInv S T M d n root
      ((padRequest M (signInput node u), w) :: c',
        ((ns', ((node, u), σ) :: es'), (queried₁, seenLeaves₁, bad₁))) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hinv
  refine ⟨h1, h2, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [List.lookup_cons,
      beq_false_of_ne (padRequest_keyInput_ne_signInput hwidth hp hnode_lt hu)]
    exact h3 p hp
  · intro q v σ' hmem_e
    rcases List.mem_cons.mp hmem_e with hhead | htail
    · obtain ⟨hqv, _⟩ := Prod.mk.inj hhead
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hqv
      exact ⟨hnode_lt, hu, hleaf_head⟩
    · obtain ⟨hq_lt, hv_le, hleaf_ex⟩ := h4 q v σ' htail
      exact ⟨hq_lt, hv_le, fun hq_len =>
        let ⟨l, hl, h1', h2', h3'⟩ := hleaf_ex hq_len
        ⟨l, hsub l hl, h1', h2', h3'⟩⟩
  · intro p u' hp hu' he_none
    have hne_pu : (p, u') ≠ (node, u) := fun h => by
      rw [h, List.lookup_cons, beq_self_eq_true] at he_none; cases he_none
    have hpadNe : padRequest M (signInput p u') ≠ padRequest M (signInput node u) :=
      fun h => hne_pu (Prod.ext_iff.mpr
        (padRequest_signInput_injective hwidth hp hnode_lt hu' hu h))
    rw [List.lookup_cons, beq_false_of_ne hne_pu] at he_none
    rw [List.lookup_cons, beq_false_of_ne hpadNe]
    exact h5 p u' hp hu' he_none
  · intro p b σ' hp he_some
    by_cases hpb : (p, b.toNat) = (node, u)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpb
      rw [List.lookup_cons, beq_self_eq_true] at he_some
      obtain rfl := Option.some.inj he_some.symm
      obtain ⟨kp, kc, hkp, hkc, hσ⟩ := hinternal b rfl hp
      exact ⟨kp, kc, w, hkp, hkc, by simp only [List.lookup_cons, beq_self_eq_true], hσ⟩
    · have hbu' : b.toNat ≤ 1 := by cases b <;> simp
      have hp_lt : p.length < d := Nat.lt_of_succ_lt hp
      have hpadNe : padRequest M (signInput p b.toNat) ≠ padRequest M (signInput node u) :=
        fun h => hpb (Prod.ext_iff.mpr
          (padRequest_signInput_injective hwidth hp_lt hnode_lt hbu' hu h))
      rw [List.lookup_cons, beq_false_of_ne hpb] at he_some
      obtain ⟨kp, kc, w', hkp, hkc, hw', hσ'⟩ := h6 p b σ' hp he_some
      refine ⟨kp, kc, w', hkp, hkc, ?_, hσ'⟩
      rw [List.lookup_cons, beq_false_of_ne hpadNe]
      exact hw'

private theorem jointCertify_spec (S : IndexedSignatureScheme) (T : S.Seeded) (depth : ℕ → ℕ)
    {M n : ℕ} (hdepth_pos : 1 ≤ depth n) (hwidth : 2 * depth n + 4 ≤ M)
    (hkgBudget : T.keyGenBudget n ≤ M)
    (hsgBudget : ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
      (msg.length = n ∨ ∃ keys' ∈ (ProbComp.eval (S.keyGen n)).support, msg = keys'.1) →
      T.signBudget keys.2 u msg ≤ M)
    {root : List Bool × List Bool} {s : JointLazyState}
    (hinv : jointLazyInv S T M (depth n) n root s) {leaf : List Bool}
    (hleaf : leaf.length = depth n) :
    let (cc, ((nodes, edges), rest)) := s
    ((jointCertify S T depth M n leaf (cc, (nodes, edges))).map Prod.snd) =
      ProbComp.eval (certifyLazy S depth n root leaf (nodes, edges)) ∧
    ∀ cc' cert ns' es',
      (cc', (cert, (ns', es'))) ∈ (jointCertify S T depth M n leaf (cc, (nodes, edges))).support →
      jointLazyInv S T M (depth n) n root (cc', ((ns', es'), rest)) ∧
      cert.1 = leaf.take (depth n - 1) ∧
      ns'.lookup cert.1 = some cert.2.1 ∧
      cert.2.1 ∈ (ProbComp.eval (S.keyGen n)).support := by
  obtain ⟨cc, ⟨nodes, edges⟩, queried, seenLeaves, bad⟩ := s
  have hrootLen : ([] : List Bool).length < depth n := by simp; omega
  have hrootSome : nodes.lookup [] = some root := hinv.1
  have hnk0_pure : jointNodeKey S T M n [] (cc, nodes) = PMF.pure (root, (cc, nodes)) := by
    have hrel := hinv.2.2.1 [] hrootLen
    rw [hrootSome] at hrel
    cases hcc : cc.lookup (padRequest M (keyInput [])) with
    | none => rw [hcc] at hrel; cases hrel
    | some w =>
      rw [hcc, Option.map_some] at hrel
      have hw : T.keyGenWith n (w.take (T.keyGenBudget n)) = root := Option.some.inj hrel.symm
      simp only [jointNodeKey, lazyCoinRequest, memoize, hcc, hrootSome,
        Probability.PMF.monad_pure_eq_pure, PMF.pure_map, hw]
  simp only [jointCertify, PMF.monad_bind_eq_bind, hnk0_pure, PMF.pure_bind, certifyLazy,
    eval_iterate_probComp]
  let stepInv (m : ℕ) (out : CoinCache × LazyCertState) : Prop :=
    jointLazyInv S T M (depth n) n root (out.1, (out.2.2, (queried, seenLeaves, bad))) ∧
    out.2.1.1 = leaf.take m ∧
    out.2.2.1.lookup out.2.1.1 = some out.2.1.2.1 ∧
    out.2.1.2.1 ∈ (ProbComp.eval (S.keyGen n)).support
  have hmain := iterate_pmf_map_of_invariant (jointCertifyStep S T M n leaf)
    (fun s => ProbComp.eval (certifyStepLazy S n leaf s)) Prod.snd stepInv (depth n - 1)
    (cc, (([], root, []), (nodes, edges)))
    ⟨hinv, rfl, hrootSome, (hinv.2.1 [] root (lookup_mem hrootSome)).2⟩
    fun m hm ⟨c, ⟨node, ⟨pk, sk⟩, certs⟩, ns, es⟩ ⟨hinv_c, hnode_eq, hns_node, hkey_supp⟩ => by
      dsimp only at hinv_c hnode_eq hns_node hkey_supp
      have hnode_len : node.length = m := by
        rw [hnode_eq, List.length_take, hleaf, Nat.min_eq_left (by omega)]
      have hnode_lt_d1 : node.length + 1 < depth n := by omega
      have hnode_lt : node.length < depth n := Nat.lt_of_succ_lt hnode_lt_d1
      set bit := leaf.getD node.length false
      set childPath := node ++ [bit]
      have hchild_len : childPath.length < depth n := by
        simpa only [childPath, List.length_append, List.length_singleton] using hnode_lt_d1
      obtain ⟨hnk_eq, hnk_inv⟩ := jointNodeKey_spec S T hwidth hkgBudget hinv_c hchild_len
      have hbu : bit.toNat ≤ 1 := by
        dsimp only [bit]
        cases leaf.getD node.length false <;> simp
      have hne_nc : node ≠ childPath := by
        intro h
        have := congrArg List.length h
        simp only [childPath, List.length_append, List.length_singleton] at this
        omega
      simp only [jointCertifyStep, certifyStepLazy, ProbComp.eval_bind, ProbComp.eval_pure,
        PMF.monad_bind_eq_bind]
      refine bind_map_of_invariant (jointNodeKey S T M n childPath (c, ns))
        (ProbComp.eval (memoize (fun _ => S.keyGen n) childPath ns))
        (fun x => (x.1, x.2.2))
        (fun x =>
          jointLazyInv S T M (depth n) n root (x.2.1, ((x.2.2, es), (queried, seenLeaves, bad))) ∧
          x.2.2.lookup childPath = some x.1 ∧
          x.1 ∈ (ProbComp.eval (S.keyGen n)).support ∧
          x.2.2.lookup node = some (pk, sk))
        (fun (child, c', ns') => (jointSignAt S T M node sk bit.toNat child.1 (c', es)).map
          fun (σ, c'', es') => (c'', ((childPath, child, certs ++ [(child.1, σ)]), (ns', es'))))
        (fun (child, ns') => (ProbComp.eval (memoize (fun _ => S.sign sk bit.toNat child.1)
          (node, bit.toNat) es)).bind fun (σ, es') =>
            PMF.pure ((childPath, child, certs ++ [(child.1, σ)]), (ns', es')))
        Prod.snd (stepInv (m + 1))
        ⟨hnk_eq, fun ⟨child, c', ns'⟩ hmem_nk => by
          obtain ⟨hinv_c', hns'_child, hchild_supp, hns'_keep⟩ := hnk_inv child c' ns' hmem_nk
          exact ⟨hinv_c', hns'_child, hchild_supp, hns'_keep node (pk, sk) hns_node hne_nc⟩⟩
        fun ⟨child, c', ns'⟩ _ ⟨hinv_c', hns'_child, hchild_supp, hns'_node⟩ => by
          have hsign_step :
              ((jointSignAt S T M node sk bit.toNat child.1 (c', es)).map fun (σ, (_, es')) =>
                (σ, es')) =
                ProbComp.eval (memoize (fun _ => S.sign sk bit.toNat child.1)
                  (node, bit.toNat) es) ∧
              ∀ σ c'' es',
                (σ, (c'', es')) ∈ (jointSignAt S T M node sk bit.toNat child.1 (c', es)).support →
                jointLazyInv S T M (depth n) n root
                  (c'', ((ns', es'), (queried, seenLeaves, bad))) := by
            simp only [jointSignAt, lazyCoinRequest, memoize]
            cases hes : es.lookup (node, bit.toNat) with
            | some σ₀ =>
              obtain ⟨kp, kc, w, hkp, hkc, hw, hσ₀⟩ :=
                hinv_c'.2.2.2.2.2 node bit σ₀ hnode_lt_d1 hes
              rw [hns'_node] at hkp; cases Option.some.inj hkp
              rw [hns'_child] at hkc; cases Option.some.inj hkc
              constructor
              · simp only [hw, Probability.PMF.monad_pure_eq_pure, PMF.pure_map, ProbComp.eval_pure,
                  ← hσ₀]
              · intro σ c'' es' hm_sa
                simp only [hw, Probability.PMF.monad_pure_eq_pure, PMF.pure_map] at hm_sa
                cases (PMF.mem_support_pure_iff _ _).mp hm_sa
                exact hinv_c'
            | none =>
              have hcc_none := hinv_c'.2.2.2.2.1 node bit.toNat hnode_lt hbu hes
              have hbud : T.signBudget sk bit.toNat child.1 ≤ M :=
                hsgBudget (pk, sk) hkey_supp bit.toNat hbu child.1
                  (Or.inr ⟨child, hchild_supp, rfl⟩)
              simp only [hcc_none, bind_pure_comp, PMF.monad_map_eq_map,
                ProbComp.eval_map, PMF.map_comp, Function.comp_def]
              refine ⟨?_, ?_⟩
              · rw [T.eval_sign sk bit.toNat child.1 (T.signBudget sk bit.toNat child.1) le_rfl,
                  ← BitString.uniformList_take hbud, PMF.map_comp, PMF.map_comp]
                rfl
              · intro σ c'' es' hm_sa
                obtain ⟨w, -, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hm_sa
                obtain ⟨rfl, h2⟩ := Prod.mk.inj heq.symm
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
                refine jointLazyInv_insert_sign S T hwidth queried bad hinv_c' (fun _ h => h)
                  hnode_lt hbu w _ (fun _ => by omega) fun b hb_eq _ => ?_
                have hb' : b = bit :=
                  Bool.eq_iff_iff.mpr (by rw [← b.toNat_eq_one, ← bit.toNat_eq_one, hb_eq])
                subst hb'
                exact ⟨(pk, sk), child, hns'_node, hns'_child, rfl⟩
          refine ⟨?_, ?_⟩
          · have heq := congrArg (PMF.map fun (σ, es') =>
              ((childPath, child, certs ++ [(child.1, σ)]), (ns', es'))) hsign_step.1
            simpa only [PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def] using heq
          · intro out' hout'
            obtain ⟨⟨σ, c'', es'⟩, hmem_sa, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout'
            refine ⟨hsign_step.2 σ c'' es' hmem_sa, ?_, hns'_child, hchild_supp⟩
            have hlt_leaf : m < leaf.length := by omega
            dsimp only [stepInv, childPath, bit]
            rw [hnode_len, hnode_eq, List.getD_eq_getElem _ _ hlt_leaf,
              List.take_succ_eq_append_getElem hlt_leaf]
  exact ⟨hmain.1, fun cc' cert ns' es' hm => hmain.2 (cc', (cert, (ns', es'))) hm⟩

private theorem jointCoinHandler_step_lazy (S : IndexedSignatureScheme) (T : S.Seeded)
    (depth : ℕ → ℕ) {M n : ℕ} (hdepth_pos : 1 ≤ depth n) (hwidth : 2 * depth n + 4 ≤ M)
    (hkgBudget : T.keyGenBudget n ≤ M)
    (hsgBudget : ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
      (msg.length = n ∨ ∃ keys' ∈ (ProbComp.eval (S.keyGen n)).support, msg = keys'.1) →
      T.signBudget keys.2 u msg ≤ M)
    (root : List Bool × List Bool) (req : Unit × List Bool) (s : JointLazyState)
    (hinv : jointLazyInv S T M (depth n) n root s) :
    (jointCoinHandler S T depth M n req s).map (fun (a, s') => (a, s'.2)) =
      ProbComp.eval (lazySignHandler S depth n root req s.2) ∧
    ∀ a s', (a, s') ∈ (jointCoinHandler S T depth M n req s).support →
      jointLazyInv S T M (depth n) n root s' := by
  obtain ⟨cc, ⟨nodes, edges⟩, queried, seenLeaves, bad⟩ := s
  simp only [jointCoinHandler, lazySignHandler, eval_ite, ProbComp.eval_bind,
    BitString.eval_sampleList, ProbComp.eval_pure, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  refine (fun h => ⟨h.1, fun a s' hm => h.2 (a, s') hm⟩)
    (treeHandler_map_of_invariant (req.2.length = n) (bad = true)
      (BitString.uniformList (depth n)) (fun leaf => seenLeaves.contains leaf)
      _ _ _ _ (fun x : List Bool × JointLazyState => (x.1, x.2.2)) _ _ _ _
      (fun x : List Bool × JointLazyState => jointLazyInv S T M (depth n) n root x.2)
      ⟨rfl, hinv⟩ ⟨rfl, hinv⟩ ⟨rfl, hinv⟩ fun hmsg _ leaf hleaf_supp hseen => ?_)
  have hleaf_len := BitString.length_of_mem_support_uniformList hleaf_supp
  have hnotMem : leaf ∉ seenLeaves := fun h => by simp [h] at hseen
  obtain ⟨hcert_eq, hcert_inv⟩ :=
    jointCertify_spec S T depth hdepth_pos hwidth hkgBudget hsgBudget hinv hleaf_len
  refine bind_map_of_invariant (jointCertify S T depth M n leaf (cc, (nodes, edges)))
    (ProbComp.eval (certifyLazy S depth n root leaf (nodes, edges))) Prod.snd
    (fun (cc', (cert, (ns', es'))) =>
      jointLazyInv S T M (depth n) n root (cc', ((ns', es'), (queried, seenLeaves, bad))) ∧
      cert.1 = leaf.take (depth n - 1) ∧
      ns'.lookup cert.1 = some cert.2.1 ∧
      cert.2.1 ∈ (ProbComp.eval (S.keyGen n)).support)
    _ _ (fun x : List Bool × JointLazyState => (x.1, x.2.2))
    (fun x : List Bool × JointLazyState => jointLazyInv S T M (depth n) n root x.2)
    ⟨hcert_eq, fun ⟨cc', cert, ns', es'⟩ hm_cert => hcert_inv cc' cert ns' es' hm_cert⟩
    fun ⟨cc', ⟨node, ⟨pk, sk⟩, certs⟩, ns', es'⟩ _
      ⟨hinv_c', hnode_eq, hns'_node, hkey_supp⟩ => ?_
  dsimp only at hnode_eq hns'_node hkey_supp ⊢
  have hnode_len : node.length = depth n - 1 := by
    rw [hnode_eq, List.length_take, hleaf_len, Nat.min_eq_left (by omega)]
  have hnode_lt : node.length < depth n := by
    rw [hnode_len]
    exact Nat.sub_lt hdepth_pos Nat.one_pos
  set uLast := (leaf.getLastD false).toNat
  have huLast : uLast ≤ 1 := Bool.toNat_le _
  have hes'_none : es'.lookup (node, uLast) = none := by
    cases hlk : es'.lookup (node, uLast) with
    | none => rfl
    | some σ₀ =>
      exfalso
      obtain ⟨-, -, hleaf_ex⟩ := hinv_c'.2.2.2.1 node uLast σ₀ (lookup_mem hlk)
      obtain ⟨l, hl_mem, hl_len, hq_eq, hv_eq⟩ := hleaf_ex hnode_len
      have hbit_eq : leaf.getLastD false = l.getLastD false :=
        Bool.eq_iff_iff.mpr (by
          rw [← (leaf.getLastD false).toNat_eq_one, ← (l.getLastD false).toNat_eq_one]
          exact congrArg (· = 1) hv_eq |>.to_iff)
      have hleaf_eq : leaf = l := by
        rw [← take_sub_one_append_getLastD hdepth_pos hleaf_len,
          ← take_sub_one_append_getLastD hdepth_pos hl_len, ← hnode_eq, hq_eq, hbit_eq]
      exact hnotMem (hleaf_eq ▸ hl_mem)
  have hcc'_none := hinv_c'.2.2.2.2.1 node uLast hnode_lt huLast hes'_none
  have hbud : T.signBudget sk uLast req.2 ≤ M :=
    hsgBudget (pk, sk) hkey_supp uLast huLast req.2 (Or.inl hmsg)
  simp only [jointSignAt, lazyCoinRequest, memoize, hes'_none, hcc'_none,
    bind_pure_comp, PMF.monad_map_eq_map, ProbComp.eval_map, PMF.map_comp, Function.comp_def]
  refine ⟨?_, fun x hm_last => ?_⟩
  · rw [T.eval_sign sk uLast req.2 (T.signBudget sk uLast req.2) le_rfl,
      ← BitString.uniformList_take hbud]
    simp only [PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
  · obtain ⟨w, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hm_last
    exact jointLazyInv_insert_sign S T hwidth (req.2 :: queried) false hinv_c'
      (fun _ h => List.mem_cons_of_mem _ h) hnode_lt huLast w _
      (fun _ => ⟨leaf, List.mem_cons_self, hleaf_len, hnode_eq, rfl⟩)
      (fun _ _ hp => by omega)

private theorem run_interpret_signHandler (S : IndexedSignatureScheme) (T : S.Seeded)
    (depth : ℕ → ℕ) (M n : ℕ) (req : Unit × List Bool) (queried : List (List Bool))
    (cc : CoinCache) :
    (((OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k)) (lazyCoinHandler M))
      (signHandler S T depth n req queried)).run cc)).map (fun ⟨⟨a, b⟩, c⟩ => (a, b, c)) =
      (unguardedCoinHandler S T depth M n req (cc, (queried, [], false))).map
        (fun (a, s') => (a, (s'.2.1, s'.1))) := by
  simp only [signHandler, unguardedCoinHandler, signO, PMF.monad_bind_eq_bind]
  split_ifs with hmsg
  · rw [bind_assoc, OracleComp.run_interpret_bind, ProbOracleComp.run_interpret_sample,
      BitString.eval_sampleList, Probability.PMF.monad_bind_eq_bind, PMF.bind_map, PMF.map_bind,
      PMF.map_bind]
    dsimp only [Function.comp_def]
    refine PMF.bind_congr_on_support _ _ _ fun leaf _ => ?_
    simp only [coinSignBody, OracleComp.run_interpret_bind, OracleComp.run_interpret_pure,
      Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure,
      PMF.map_bind, PMF.pure_map, PMF.bind_bind, PMF.pure_bind]
  · simp only [pure_bind, OracleComp.run_interpret_pure, Probability.PMF.monad_pure_eq_pure,
      PMF.pure_map]

/-- **From ideal coins to lazy tree signing**: when `N n` covers all padded tree request widths and
seeded key/signature coin budgets, replacing the uniform random function in `treeIdealGame` with
lazy node keys, lazy edge signatures, and leaf-collision aborts (`lazyTreeGame`) loses at most
`(Q ^ 2 : ℝ≥0) / 2 ^ (depth n + 1)` across any `Q`-query adversary. -/
theorem succProbability_treeIdealGame_le_lazy (S : IndexedSignatureScheme) (T : S.Seeded)
    (depth N : ℕ → ℕ) {n Q : ℕ} (hdepth_pos : 1 ≤ depth n) (hwidth : 2 * depth n + 4 ≤ N n)
    (hkgBudget : T.keyGenBudget n ≤ N n)
    (hsgBudget : ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
      (msg.length = n ∨ ∃ keys' ∈ (ProbComp.eval (S.keyGen n)).support, msg = keys'.1) →
      T.signBudget keys.2 u msg ≤ N n)
    (adversary : Forger)
    (hq : ∀ root ∈ (ProbComp.eval (S.keyGen n)).support,
      (adversary n (encPair encUnary encBits (n, root.1))).IsQueryBounded Q) :
    Game.succProbability (ProbComp.eval (treeIdealGame S T depth N adversary n)) ≤
      Game.succProbability (ProbComp.eval (lazyTreeGame S depth adversary n)) +
        (Q ^ 2 : ℝ≥0) / 2 ^ (depth n + 1) := by
  set M := N n
  let gameWith (h : Unit × List Bool → StateT GuardedCoinState PMF (List Bool))
      (w₀ : List Bool) : PMF Bool :=
    let root := T.keyGenWith n (w₀.take (T.keyGenBudget n))
    let pk := encPair encUnary encBits (n, root.1)
    let init : GuardedCoinState := ([(padRequest M (keyInput []), w₀)], ([], [], false))
    ((OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k)) h)
      (adversary n pk)).run init).bind fun (msig, (_, (queried, _, _))) =>
        PMF.pure ((msig.1.length == n) && !queried.contains msig.1 &&
          verify S depth pk msig.1 msig.2)
  -- Step 1: rewrite treeIdealGame as w₀ ← uniformList M followed by unguardedCoinHandler
  have hstep1 : ProbComp.eval (treeIdealGame S T depth N adversary n) =
      (BitString.uniformList M).bind (gameWith (unguardedCoinHandler S T depth M n)) := by
    rw [eval_treeIdealGame_eq_lazyCoin]
    simp only [simulateTreeGame, OracleComp.run_interpret_bind, OracleComp.run_interpret_pure,
      Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure,
      PMF.map_bind]
    have hroot : (OracleComp.interpret
          (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
            (lazyCoinHandler M))
          (nodeKeyO S T n [])).run [] =
        (BitString.uniformList M).map fun w₀ =>
          (T.keyGenWith n (w₀.take (T.keyGenBudget n)),
            [(padRequest M (keyInput []), w₀)]) := by
      simp only [nodeKeyO, coinRequest, OracleComp.interpret_map, ProbOracleComp.interpret_query,
        StateT.run_map, PMF.monad_map_eq_map, PMF.map_comp, Function.comp_def]
      change (lazyCoinHandler M ((), encPair encBits encUnary (keyInput [], T.keyGenBudget n))
        []).map _ = _
      simp only [lazyCoinHandler, coinRequestDecoder.decode_enc, lazyCoinRequest, memoize,
        List.lookup_nil, bind_pure_comp, PMF.monad_map_eq_map, PMF.map_comp, Function.comp_def,
        List.take_take, Nat.min_self]
    rw [hroot, PMF.bind_map]
    refine PMF.bind_congr_on_support _ _ _ fun w₀ _ => ?_
    dsimp only [Function.comp_def, gameWith]
    set root := T.keyGenWith n (w₀.take (T.keyGenBudget n))
    set pk := encPair encUnary encBits (n, root.1)
    set cc₀ : CoinCache := [(padRequest M (keyInput []), w₀)]
    have hflat := ProbOracleComp.run_interpret_run_interpret (signHandler S T depth n)
      (lazyCoinHandler M) (adversary n pk) [] cc₀
    have hunguard := ProbOracleComp.run_interpret_map_state
      (unguardedCoinHandler S T depth M n)
      (fun q (st : List (List Bool) × CoinCache) =>
        (((OracleComp.interpret
          (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
            (lazyCoinHandler M))
          (signHandler S T depth n q st.1)).run st.2)).map (fun ⟨⟨a, b⟩, c⟩ => (a, b, c)))
      (fun (s : GuardedCoinState) => (s.2.1, s.1))
      (fun req s => by
        obtain ⟨cc, queried, seenLeaves, bad⟩ := s
        rw [run_interpret_signHandler S T depth M n req queried cc]
        simp only [unguardedCoinHandler, PMF.monad_bind_eq_bind]
        split_ifs with hmsg
        · simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
        · simp only [PMF.pure_map])
      (adversary n pk) (cc₀, ([], [], false))
    have hcomb := hflat.trans (congrArg (PMF.map fun ⟨a, b, c⟩ => ((a, b), c)) hunguard.symm)
    have hwin := congrArg (fun d => d.bind fun out : ((List Bool × List Bool) × List (List Bool)) ×
        CoinCache =>
      PMF.pure (((out.1.1.1.length == n) && !out.1.2.contains out.1.1.1 &&
        verify S depth pk out.1.1.1 out.1.1.2, out.2))) hcomb
    have hfst := congrArg (PMF.map Prod.fst) hwin
    simp only [PMF.map_bind, PMF.bind_map, PMF.pure_map, Function.comp_def] at hfst
    simpa only [PMF.pure_map] using hfst
  -- Step 2: rewrite lazyTreeGame via jointCoinHandler -> guardedCoinHandler
  have hstep2 : ProbComp.eval (lazyTreeGame S depth adversary n) =
      (BitString.uniformList M).bind (gameWith (guardedCoinHandler S T depth M n)) := by
    have hrootLaw : ProbComp.eval (S.keyGen n) =
        (BitString.uniformList M).map (fun w₀ => T.keyGenWith n (w₀.take (T.keyGenBudget n))) := by
      rw [T.eval_keyGen n (T.keyGenBudget n) le_rfl, ← BitString.uniformList_take hkgBudget,
        PMF.map_comp]
      rfl
    have hrootLen : ([] : List Bool).length < depth n := by simp; omega
    simp only [lazyTreeGame, ProbComp.eval_bind, ProbComp.eval_pure, hrootLaw, PMF.bind_map,
      Function.comp_def, ProbOracleComp.eval_run_interpret]
    refine PMF.bind_congr_on_support _ _ _ fun w₀ _ => ?_
    dsimp only [gameWith]
    set root := T.keyGenWith n (w₀.take (T.keyGenBudget n))
    set pk := encPair encUnary encBits (n, root.1)
    set jInit : JointLazyState :=
      ([(padRequest M (keyInput []), w₀)], (([([], root)], []), ([], [], false)))
    have hjInv : jointLazyInv S T M (depth n) n root jInit := by
      refine ⟨by simp only [List.lookup_cons, beq_self_eq_true], ?_, ?_, ?_, ?_, ?_⟩
      · intro p k hp
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp hp)
        exact ⟨hrootLen, T.keyGenWith_mem_support n _⟩
      · intro p hp
        by_cases hp0 : p = []
        · subst hp0
          simp only [List.lookup_cons, beq_self_eq_true, Option.map_some, root]
        · have hpadNe : padRequest M (keyInput p) ≠ padRequest M (keyInput []) :=
            fun h => hp0 (padRequest_keyInput_injective hwidth hp hrootLen h)
          simp only [List.lookup_cons, beq_false_of_ne hp0, beq_false_of_ne hpadNe,
            List.lookup_nil, Option.map_none]
      · intro _ _ _ h; cases h
      · intro p u hp hu _
        have hpadNe : padRequest M (signInput p u) ≠ padRequest M (keyInput []) :=
          (padRequest_keyInput_ne_signInput hwidth hrootLen hp hu).symm
        simp only [List.lookup_cons, beq_false_of_ne hpadNe, List.lookup_nil]
      · intro _ _ _ _ h; cases h
    have hprojLazy := ProbOracleComp.run_interpret_map_state_of_invariant
      (jointCoinHandler S T depth M n)
      (fun q s => ProbComp.eval (lazySignHandler S depth n root q s))
      Prod.snd
      (jointLazyInv S T M (depth n) n root)
      (fun q s hs a s' hm =>
        (jointCoinHandler_step_lazy S T depth hdepth_pos hwidth hkgBudget hsgBudget root q s hs).2
          a s' hm)
      (fun q s hs =>
        (jointCoinHandler_step_lazy S T depth hdepth_pos hwidth hkgBudget hsgBudget root q s hs).1)
      (adversary n pk) jInit hjInv
    have hprojGuard := ProbOracleComp.run_interpret_map_state
      (jointCoinHandler S T depth M n)
      (guardedCoinHandler S T depth M n)
      (fun s => (s.1, s.2.2))
      (map_dropCaches_jointCoinHandler S T depth M n)
      (adversary n pk) jInit
    have hwinLazy := congrArg (fun d => d.bind fun (msig, (_, (queried, _, _))) =>
      PMF.pure ((msig.1.length == n) && !queried.contains msig.1 &&
        verify S depth pk msig.1 msig.2)) hprojLazy.symm
    have hwinGuard := congrArg (fun d => d.bind fun (msig, (_, (queried, _, _))) =>
      PMF.pure ((msig.1.length == n) && !queried.contains msig.1 &&
        verify S depth pk msig.1 msig.2)) hprojGuard
    simp only [PMF.bind_map, Function.comp_def] at hwinLazy hwinGuard
    exact hwinLazy.trans hwinGuard
  -- Step 3: apply IdenticalUntilBad + bad probability bound pointwise at w₀
  set err : ℝ≥0 := (Q ^ 2 : ℝ≥0) / 2 ^ (depth n + 1)
  have herr : (err : ℝ≥0∞) = ((Q ^ 2 : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ (depth n + 1)) := by
    dsimp only [err]
    rw [ENNReal.coe_div (by positivity), div_eq_mul_inv, one_div]
    push_cast
    ring
  have hle_enn : ProbComp.eval (treeIdealGame S T depth N adversary n) true ≤
      ProbComp.eval (lazyTreeGame S depth adversary n) true + (err : ℝ≥0∞) := by
    rw [hstep1, hstep2, PMF.bind_apply, PMF.bind_apply]
    have hpt (w₀ : List Bool) :
        BitString.uniformList M w₀ *
          gameWith (unguardedCoinHandler S T depth M n) w₀ true ≤
        BitString.uniformList M w₀ *
          (gameWith (guardedCoinHandler S T depth M n) w₀ true + (err : ℝ≥0∞)) := by
      refine mul_le_mul_of_nonneg_left ?_ zero_le
      dsimp only [gameWith]
      set root := T.keyGenWith n (w₀.take (T.keyGenBudget n))
      set pk := encPair encUnary encBits (n, root.1)
      set init : GuardedCoinState := ([(padRequest M (keyInput []), w₀)], ([], [], false))
      have hiub := identicalUntilBad_coinHandlers S T depth M n
      have hdiff := hiub.bind_apply_le (adversary n pk) init
        (fun (msig, (_, (queried, _, _))) =>
          PMF.pure ((msig.1.length == n) && !queried.contains msig.1 &&
            verify S depth pk msig.1 msig.2)) true
      rw [hiub.bad_eq] at hdiff
      have hq_root : (adversary n pk).IsQueryBounded Q :=
        hq root (T.keyGenWith_mem_support n _)
      have hbad_le := toOuterMeasure_bad_queryBounded_le
        (guardedCoinHandler S T depth M n)
        (fun s => s.2.2.2 = true) (fun s => s.2.2.1.length) (depth n)
        (step_bad_guardedCoinHandler S T depth M n)
        (grow_seen_guardedCoinHandler S T depth M n)
        hq_root (s := init) Bool.false_ne_true
      simp only [init, List.length_nil, mul_zero, zero_add] at hbad_le
      exact hdiff.trans (add_le_add le_rfl (hbad_le.trans_eq herr.symm))
    calc ∑' w₀, _
        ≤ ∑' w₀, BitString.uniformList M w₀ * _ := tsum_le_tsum hpt
      _ = _ := by
          simp_rw [mul_add]
          rw [tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  have hfin : ProbComp.eval (lazyTreeGame S depth adversary n) true + (err : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, ENNReal.coe_ne_top⟩
  have h := ENNReal.toNNReal_mono hfin hle_enn
  rw [ENNReal.toNNReal_add (PMF.apply_ne_top _ _) ENNReal.coe_ne_top, ENNReal.toNNReal_coe] at h
  exact h

end IdealToLazy

/-! ### From lazy tree signing to indexed forgery -/

section LazyToIndexed

/-- Full log entry `(path, slotIdx, u, msg)` recorded on every fresh edge signature in the
pre-sampled tree experiment. -/
private abbrev AllSignedLog := List (List Bool × ℕ × ℕ × List Bool)

/-- State of the pre-sampled tree signing handler: `PlantedState` paired with `AllSignedLog`. -/
private abbrev PresampledState := PlantedState × AllSignedLog

/-- Initial state of the pre-sampled tree signing handler. -/
private def initPresampledState : PresampledState := (initPlantedState, [])

/-- Extract the indexed signing oracle log `(u, msg)` at slot `target` from `allSigned`. -/
private def signedLogOf (target : ℕ) (allSigned : AllSignedLog) : List (ℕ × List Bool) :=
  (allSigned.filter fun e => e.2.1 == target).map fun e => (e.2.2.1, e.2.2.2)

/-- Pure counterpart of `visitNodeM`. -/
private def visitNodePure (cap : ℕ) (path : List Bool) (visited : NodeSlotCache) :
    ℕ × NodeSlotCache :=
  match visited.lookup path with
  | some idx => (idx, visited)
  | none =>
    let idx := min visited.length cap
    (idx, (path, idx) :: visited)

private theorem run_interpret_visitNodeM {External : Type}
    (oracle : Unit × List Bool → StateT External PMF (List Bool))
    (cap : ℕ) (path : List Bool) (visited : NodeSlotCache) (ext : External) :
    (OracleComp.interpret
      (OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifOracle j)) oracle)
      (visitNodeM cap path visited)).run ext =
      PMF.pure (visitNodePure cap path visited, ext) := by
  simp only [visitNodeM, visitNodePure, memoize]
  cases visited.lookup path <;>
    simp only [pure_bind, OracleComp.run_interpret_pure, Probability.PMF.monad_pure_eq_pure]

private theorem filter_headD_of_mem_unique (visited : NodeSlotCache) {p : List Bool}
    {idx : ℕ} (hmem : (p, idx) ∈ visited)
    (huniq : ∀ e₁ ∈ visited, ∀ e₂ ∈ visited, e₁.2 = e₂.2 → e₁ = e₂) :
    ((visited.filter fun e => e.2 == idx).headD ([], 0)).1 = p := by
  have hin : (p, idx) ∈ visited.filter fun e => e.2 == idx :=
    List.mem_filter.mpr ⟨hmem, beq_self_eq_true idx⟩
  cases hflt : visited.filter fun e => e.2 == idx with
  | nil => rw [hflt] at hin; cases hin
  | cons hd tl =>
    have hhd : hd ∈ visited.filter fun e => e.2 == idx := by
      rw [hflt]; exact List.mem_cons_self
    obtain ⟨hhd_vis, hhd_eq⟩ := List.mem_filter.mp hhd
    have heq : hd = (p, idx) := huniq hd hhd_vis (p, idx) hmem (beq_iff_eq.mp hhd_eq)
    simp only [List.headD_cons, heq]

private theorem slot_bound_lt_dyadicSize {Q d B : ℕ} (hd : 1 ≤ d) (hB : Q * d ≤ B) :
    1 + Q * (d - 1) < dyadicSize B := by
  rcases Nat.eq_zero_or_pos Q with rfl | hQ
  · have h2 := two_le_dyadicSize B
    omega
  · have hmul : Q * (d - 1) + Q = Q * d := by
      have := Nat.mul_sub_left_distrib Q d 1
      have : Q ≤ Q * d := Nat.le_mul_of_pos_right Q hd
      omega
    have hlt := lt_dyadicSize B
    omega

private theorem fst_getD_splice (front back : List (List Bool × List Bool))
    (x : List Bool × List Bool) (idx : ℕ) :
    ((front ++ (x.1, []) :: back).getD idx ([], [])).1 =
      ((front ++ x :: back).getD idx ([], [])).1 := by
  by_cases h : idx = front.length
  · subst h
    simp only [List.getD_append_cons_length]
  · rw [List.getD_append_cons_of_ne front back (x.1, []) x ([], []) h]

/-- Local edge-signing step on pre-sampled `keys`, truncating fresh signatures to `sigCap` bits and
recording `(path, idx, u, msg)` in `allSigned`. -/
private noncomputable def localSignEdge (S : IndexedSignatureScheme)
    (keys : List (List Bool × List Bool)) (sigCap : ℕ) (path : List Bool) (idx u : ℕ)
    (msg : List Bool) (ea : EdgeSigCache × AllSignedLog) :
    PMF (List Bool × (EdgeSigCache × AllSignedLog)) :=
  match ea.1.lookup (path, u) with
  | some σ => PMF.pure (σ, ea)
  | none =>
    (ProbComp.eval (S.sign (keys.getD idx ([], [])).2 u msg)).map fun raw =>
      let σ := raw.take sigCap
      (σ, (((path, u), σ) :: ea.1, (path, idx, u, msg) :: ea.2))

private abbrev LocalCertState :=
  (List Bool × ℕ × List (List Bool × List Bool)) × (NodeSlotCache × EdgeSigCache × AllSignedLog)

private noncomputable def localCertifyStep (S : IndexedSignatureScheme)
    (keys : List (List Bool × List Bool)) (sigCap : ℕ) (leaf : List Bool)
    (state : LocalCertState) : PMF LocalCertState :=
  let ((node, idx, certs), (visited, edges, allSigned)) := state
  let bit := leaf.getD node.length false
  let childPath := node ++ [bit]
  let (childIdx, visited') := visitNodePure keys.length childPath visited
  let childPk := (keys.getD childIdx ([], [])).1
  (localSignEdge S keys sigCap node idx bit.toNat childPk (edges, allSigned)).map
    fun (σ, (edges', allSigned')) =>
      ((childPath, childIdx, certs ++ [(childPk, σ)]), (visited', edges', allSigned'))

private noncomputable def localCertify (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    (keys : List (List Bool × List Bool)) (sigCap n : ℕ) (leaf : List Bool)
    (caches : NodeSlotCache × EdgeSigCache × AllSignedLog) : PMF LocalCertState :=
  Nat.iterate (fun d => d.bind (localCertifyStep S keys sigCap leaf)) (depth n - 1)
    (PMF.pure (([], 0, []), caches))

private noncomputable def localTreeHandler (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    (keys : List (List Bool × List Bool)) (sigCap n : ℕ) (request : Unit × List Bool) :
    StateT PresampledState PMF (List Bool) := fun state =>
  let msg := request.2
  let (((visited, edges), (queried, seenLeaves, bad)), allSigned) := state
  if msg.length = n then
    if bad then
      PMF.pure ([], (((visited, edges), (msg :: queried, seenLeaves, true)), allSigned))
    else do
      let leaf ← BitString.uniformList (depth n)
      if seenLeaves.contains leaf then
        pure ([], (((visited, edges), (msg :: queried, seenLeaves, true)), allSigned))
      else
        let ((node, idx, certs), (visited', edges', allSigned')) ←
          localCertify S depth keys sigCap n leaf (visited, edges, allSigned)
        (localSignEdge S keys sigCap node idx (leaf.getLastD false).toNat msg
          (edges', allSigned')).map fun (σ, (edges'', allSigned'')) =>
            (encodeSignature leaf certs σ,
              (((visited', edges''), (msg :: queried, leaf :: seenLeaves, false)), allSigned''))
  else
    PMF.pure ([], (((visited, edges), (msg :: queried, seenLeaves, bad)), allSigned))

/-- Pre-sampled tree experiment: sample `dyadicSize (slotBound n)` key pairs of `S`, then run
`adversary` against `localTreeHandler`. -/
private noncomputable def presampledExp (S : IndexedSignatureScheme)
    (depth slotBound sigCap : ℕ → ℕ) (adversary : Forger) (n : ℕ) :
    PMF (List (List Bool × List Bool) × (List Bool × List Bool) × PresampledState) := do
  let keys ← ProbComp.eval (OracleComp.replicate (dyadicSize (slotBound n)) (S.keyGen n))
  let pk := encPair encUnary encBits (n, (keys.getD 0 ([], [])).1)
  ((OracleComp.interpret
    (OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifOracle j))
      (localTreeHandler S depth keys (sigCap n) n))
    (adversary n pk)).run initPresampledState).map fun (msig, st) => (keys, msig, st)

/-- Whether `indexedForgerAt` at `target` wins on a pre-sampled outcome. -/
private def plantedWin (S : IndexedSignatureScheme) (depth : ℕ → ℕ) (n target : ℕ)
    (out : List (List Bool × List Bool) × (List Bool × List Bool) × PresampledState) : Bool :=
  let (keys, msig, (ps, allSigned)) := out
  let cand := extractForgery (depth n) target ps.1.1 msig.1 msig.2
  !(signedLogOf target allSigned).contains (cand.1, cand.2.1) &&
    S.verify (keys.getD target ([], [])).1 cand.1 cand.2.1 cand.2.2

/-- Whether `adversary` wins `lazyTreeGame` on a pre-sampled outcome. -/
private def treeWinOfPresampled (S : IndexedSignatureScheme) (depth : ℕ → ℕ) (n : ℕ)
    (out : List (List Bool × List Bool) × (List Bool × List Bool) × PresampledState) : Bool :=
  let (keys, msig, (ps, _)) := out
  let pk := encPair encUnary encBits (n, (keys.getD 0 ([], [])).1)
  (msig.1.length == n) && !ps.2.1.contains msig.1 && verify S depth pk msig.1 msig.2

/-! #### Simulation of `plantedTreeHandler` + `indexedSigningOracle` by `localTreeHandler` -/

private def slotEdgeInv (K : ℕ) (st : PresampledState) : Prop :=
  let (((visited, edges), _), allSigned) := st
  ([], 0) ∈ visited ∧
  (∀ e ∈ visited, e.2 < K → e.2 < visited.length) ∧
  (∀ e₁ ∈ visited, ∀ e₂ ∈ visited, e₁.2 < K → e₁.2 = e₂.2 → e₁ = e₂) ∧
  ∀ p idx u m, (p, idx, u, m) ∈ allSigned → (p, idx) ∈ visited ∧ edges.lookup (p, u) ≠ none

private theorem visitNodePure_inv {P : List Bool → Prop} {K : ℕ} {visited : NodeSlotCache}
    (path : List Bool) (hp : P path)
    (hlt : ∀ e ∈ visited, P e.1 ∧ (e.2 < K → e.2 < visited.length))
    (huniq : ∀ e₁ ∈ visited, ∀ e₂ ∈ visited, e₁.2 < K → e₁.2 = e₂.2 → e₁ = e₂) :
    let (idx, visited') := visitNodePure K path visited
    (path, idx) ∈ visited' ∧
    (∀ e ∈ visited, e ∈ visited') ∧
    visited'.length ≤ visited.length + 1 ∧
    (∀ e ∈ visited', P e.1 ∧ (e.2 < K → e.2 < visited'.length)) ∧
    (∀ e₁ ∈ visited', ∀ e₂ ∈ visited', e₁.2 < K → e₁.2 = e₂.2 → e₁ = e₂) ∧
    (∀ e ∈ visited', e ∈ visited ∨ e = (path, min visited.length K)) := by
  simp only [visitNodePure]
  cases hlk : visited.lookup path with
  | some idx =>
    exact ⟨lookup_mem hlk, fun _ h => h, Nat.le_succ _, hlt, huniq, fun _ h => Or.inl h⟩
  | none =>
    refine ⟨List.mem_cons_self, fun _ h => List.mem_cons_of_mem _ h,
      by simp only [List.length_cons, le_refl], ?_, ?_, fun _ h => List.mem_cons.mp h |>.symm⟩
    · intro e he
      simp only [List.length_cons]
      rcases List.mem_cons.mp he with rfl | htail
      · exact ⟨hp, fun _ => Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
      · exact ⟨(hlt e htail).1, fun hK => Nat.lt_succ_of_lt ((hlt e htail).2 hK)⟩
    · intro e₁ he₁ e₂ he₂ he₁K heq
      rcases List.mem_cons.mp he₁ with rfl | ht₁ <;> rcases List.mem_cons.mp he₂ with rfl | ht₂
      · rfl
      · dsimp only at he₁K heq
        have hlt₂ := (hlt e₂ ht₂).2 (heq ▸ he₁K)
        omega
      · have hlt₁ := (hlt e₁ ht₁).2 he₁K
        dsimp only at heq
        omega
      · exact huniq e₁ ht₁ e₂ ht₂ he₁K heq

private theorem visitNodePure_slotInv {K : ℕ} {visited : NodeSlotCache} (path : List Bool)
    (hlt : ∀ e ∈ visited, e.2 < K → e.2 < visited.length)
    (huniq : ∀ e₁ ∈ visited, ∀ e₂ ∈ visited, e₁.2 < K → e₁.2 = e₂.2 → e₁ = e₂) :
    let (idx, visited') := visitNodePure K path visited
    (path, idx) ∈ visited' ∧
    (∀ e ∈ visited, e ∈ visited') ∧
    (∀ e ∈ visited', e.2 < K → e.2 < visited'.length) ∧
    (∀ e₁ ∈ visited', ∀ e₂ ∈ visited', e₁.2 < K → e₁.2 = e₂.2 → e₁ = e₂) := by
  have h := visitNodePure_inv (P := fun _ => True) path trivial
    (fun e he => ⟨trivial, hlt e he⟩) huniq
  exact ⟨h.1, h.2.1, fun e he => (h.2.2.2.1 e he).2, h.2.2.2.2.1⟩

private theorem localSignEdge_planted_spec (S : IndexedSignatureScheme)
    {n sigCap : ℕ} (hcap : 2 ≤ S.capacity n)
    {front back : List (List Bool × List Bool)} {x : List Bool × List Bool}
    {visited : NodeSlotCache} {edges : EdgeSigCache} {allSigned : AllSignedLog}
    (hslotLt : front.length < (front ++ x :: back).length)
    (huniq : ∀ e₁ ∈ visited, ∀ e₂ ∈ visited,
      e₁.2 < (front ++ x :: back).length → e₁.2 = e₂.2 → e₁ = e₂)
    (hall : ∀ p₀ idx₀ u₀ m₀, (p₀, idx₀, u₀, m₀) ∈ allSigned →
      (p₀, idx₀) ∈ visited ∧ edges.lookup (p₀, u₀) ≠ none)
    {path : List Bool} {idx u : ℕ} (hvis : (path, idx) ∈ visited) (hu : u ≤ 1)
    (msg : List Bool) :
    let keys := front ++ x :: back
    let keys' := front ++ (x.1, []) :: back
    let target := front.length
    ((localSignEdge S keys sigCap path idx u msg (edges, allSigned)).map
      fun (σ, (edges', allSigned')) => (σ, (edges', signedLogOf target allSigned'))) =
      ((OracleComp.interpret
        (OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifOracle j))
          (fun q s => ProbComp.eval (S.indexedSigningOracle n x.2 q s)))
        (signEdgeM S keys' target sigCap path idx u msg edges)).run
        (signedLogOf target allSigned)).map (fun ⟨⟨σ, edges'⟩, signed'⟩ => (σ, (edges', signed'))) ∧
    ∀ σ edges' allSigned',
      (σ, (edges', allSigned')) ∈
        (localSignEdge S (front ++ x :: back) sigCap path idx u msg (edges, allSigned)).support →
      ∀ p₀ idx₀ u₀ m₀, (p₀, idx₀, u₀, m₀) ∈ allSigned' →
        (p₀, idx₀) ∈ visited ∧ edges'.lookup (p₀, u₀) ≠ none := by
  dsimp only
  simp only [localSignEdge, signEdgeM, memoize]
  cases hes : edges.lookup (path, u) with
  | some σ₀ =>
    refine ⟨?_, ?_⟩
    · simp only [OracleComp.run_interpret_pure, Probability.PMF.monad_pure_eq_pure, PMF.pure_map]
    · intro σ edges' allSigned' hm
      obtain ⟨_, h2⟩ := Prod.mk.inj ((PMF.mem_support_pure_iff _ _).mp hm)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
      exact hall
  | none =>
    refine ⟨?_, ?_⟩
    · simp only [signEdgeRaw]
      by_cases hidx : idx = front.length
      · subst hidx
        have hnotMem : u ∉ (signedLogOf front.length allSigned).map Prod.fst := by
          simp only [signedLogOf, List.mem_map, List.mem_filter, beq_iff_eq]
          rintro ⟨_, ⟨⟨p₀, idx₀, u₀, m₀⟩, ⟨hm_all, hidx₀⟩, rfl⟩, hfst⟩
          dsimp only at hidx₀ hfst
          obtain ⟨hp₀_vis, hp₀_lk⟩ := hall p₀ idx₀ u₀ m₀ hm_all
          rw [hidx₀] at hp₀_vis
          rw [hfst] at hp₀_lk
          have hpeq : (p₀, front.length) = (path, front.length) :=
            huniq _ hp₀_vis _ hvis hslotLt rfl
          obtain ⟨rfl, -⟩ := Prod.mk.inj hpeq
          exact hp₀_lk hes
        have huLt : u < S.capacity n := by omega
        have hlogCons : signedLogOf front.length ((path, front.length, u, msg) :: allSigned) =
            (u, msg) :: signedLogOf front.length allSigned := by
          simp only [signedLogOf, List.filter_cons, beq_self_eq_true, ↓reduceIte, List.map_cons]
        simp only [↓reduceIte, List.getD_append_cons_length,
          OracleComp.run_interpret_bind, OracleComp.interpret_map,
          ProbOracleComp.interpret_query, OracleComp.run_interpret_pure,
          Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure,
          StateT.run_map, PMF.monad_map_eq_map, IndexedSignatureScheme.indexedSigningOracle,
          IndexedSignatureScheme.requestDecoder.decode_enc, PMF.map_bind, PMF.bind_map,
          PMF.pure_map, PMF.map_comp, Function.comp_def, hlogCons]
        dsimp only [StateT.run]
        simp only [huLt, hnotMem, not_false_eq_true, and_self, ↓reduceIte, ProbComp.eval_bind,
          ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind, PMF.map, Function.comp_def]
      · have hlogStay : signedLogOf front.length ((path, idx, u, msg) :: allSigned) =
            signedLogOf front.length allSigned := by
          simp only [signedLogOf, List.filter_cons, beq_false_of_ne hidx, Bool.false_eq_true,
            ↓reduceIte]
        have hgetNe : (front ++ (x.1, []) :: back).getD idx ([], []) =
            (front ++ x :: back).getD idx ([], []) :=
          List.getD_append_cons_of_ne front back (x.1, []) x ([], []) hidx
        simp only [hidx, ↓reduceIte, hgetNe, OracleComp.run_interpret_bind,
          OracleComp.interpret_map, ProbOracleComp.run_interpret_sample,
          OracleComp.run_interpret_pure, Probability.PMF.monad_bind_eq_bind,
          Probability.PMF.monad_pure_eq_pure, StateT.run_map, PMF.monad_map_eq_map,
          PMF.map_bind, PMF.bind_map, PMF.pure_map, PMF.map_comp,
          Function.comp_def, hlogStay]
        simp only [PMF.map, Function.comp_def]
    · intro σ edges' allSigned' hm
      obtain ⟨raw, -, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hm
      obtain ⟨rfl, h2⟩ := Prod.mk.inj heq.symm
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
      intro p₀ idx₀ u₀ m₀ hm_all
      rcases List.mem_cons.mp hm_all with hhead | htail
      · obtain ⟨rfl, h2'⟩ := Prod.mk.inj hhead
        obtain ⟨rfl, h3'⟩ := Prod.mk.inj h2'
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h3'
        refine ⟨hvis, ?_⟩
        rw [List.lookup_cons, beq_self_eq_true]
        rintro ⟨⟩
      · obtain ⟨hp₀_vis, hp₀_lk⟩ := hall p₀ idx₀ u₀ m₀ htail
        refine ⟨hp₀_vis, ?_⟩
        rw [List.lookup_cons]
        cases (p₀, u₀) == (path, u)
        · exact hp₀_lk
        · rintro ⟨⟩

private theorem localCertify_planted_spec (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    {n sigCap : ℕ} (hcap : 2 ≤ S.capacity n)
    {front back : List (List Bool × List Bool)} {x : List Bool × List Bool}
    (leaf : List Bool) {ps : PlantedState} {allSigned : AllSignedLog}
    (hinv : slotEdgeInv (front ++ x :: back).length (ps, allSigned)) :
    let keys := front ++ x :: back
    let keys' := front ++ (x.1, []) :: back
    let target := front.length
    let ((visited, edges), rest) := ps
    ((localCertify S depth keys sigCap n leaf (visited, edges, allSigned)).map
      fun (c, (v, e, a)) => (((c, (v, e)), signedLogOf target a))) =
      (OracleComp.interpret
        (OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifOracle j))
          (fun q s => ProbComp.eval (S.indexedSigningOracle n x.2 q s)))
        (certifyPlanted S depth keys' target sigCap n leaf (visited, edges))).run
        (signedLogOf target allSigned) ∧
    ∀ c v e a,
      (c, (v, e, a)) ∈
        (localCertify S depth keys sigCap n leaf (visited, edges, allSigned)).support →
      (c.1, c.2.1) ∈ v ∧ slotEdgeInv keys.length (((v, e), rest), a) := by
  obtain ⟨⟨visited, edges⟩, rest⟩ := ps
  obtain ⟨hrootVis, hltVis, huniqVis, hallVis⟩ := hinv
  set keys := front ++ x :: back
  set keys' := front ++ (x.1, []) :: back
  set target := front.length
  have hslotLt : target < keys.length := by
    simp only [keys, target, List.length_append, List.length_cons]
    omega
  have hlenEq : keys'.length = keys.length := by
    simp only [keys, keys', List.length_append, List.length_cons]
  dsimp only [localCertify, certifyPlanted]
  rw [interpret_iterate_pmf]
  let loopInv (st : LocalCertState) : Prop :=
    let ((node, idx, _), (v, e, a)) := st
    (node, idx) ∈ v ∧ slotEdgeInv keys.length (((v, e), rest), a)
  have hmain := iterate_pmf_map_of_invariant
    (localCertifyStep S keys sigCap leaf)
    (fun (cs, sg) =>
      (OracleComp.interpret
        (OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifOracle j))
          (fun q s => ProbComp.eval (S.indexedSigningOracle n x.2 q s)))
        (certifyStepPlanted S keys' target sigCap leaf cs)).run sg)
    (fun (c, (v, e, a)) => ((c, (v, e)), signedLogOf target a))
    (fun _ st => loopInv st) (depth n - 1) (([], 0, []), (visited, edges, allSigned))
    ⟨hrootVis, hrootVis, hltVis, huniqVis, hallVis⟩
    fun _ _ ⟨⟨node, idx, certs⟩, v, e, a⟩ ⟨hnode_v, hroot_v, hlt_v, huniq_v, hall_v⟩ => by
      set bit := leaf.getD node.length false
      set childPath := node ++ [bit]
      obtain ⟨hchild_vp, hmono_vp, hlt_vp, huniq_vp⟩ :=
        visitNodePure_slotInv childPath hlt_v huniq_v
      set vp := visitNodePure keys.length childPath v
      have hnode_vp : (node, idx) ∈ vp.2 := hmono_vp _ hnode_v
      have hall_vp : ∀ p₀ idx₀ u₀ m₀, (p₀, idx₀, u₀, m₀) ∈ a →
          (p₀, idx₀) ∈ vp.2 ∧ e.lookup (p₀, u₀) ≠ none :=
        fun p₀ idx₀ u₀ m₀ hm => ⟨hmono_vp _ (hall_v p₀ idx₀ u₀ m₀ hm).1,
          (hall_v p₀ idx₀ u₀ m₀ hm).2⟩
      have hbu : bit.toNat ≤ 1 := Bool.toNat_le bit
      have hpkEq : (keys'.getD vp.1 ([], [])).1 = (keys.getD vp.1 ([], [])).1 :=
        fst_getD_splice front back x vp.1
      obtain ⟨hedg_eq, hedg_inv⟩ :=
        localSignEdge_planted_spec S (sigCap := sigCap) hcap hslotLt huniq_vp hall_vp hnode_vp hbu
          (keys.getD vp.1 ([], [])).1
      refine ⟨?_, fun st' hst' => ?_⟩
      · simp only [localCertifyStep, certifyStepPlanted, hlenEq, OracleComp.run_interpret_bind,
          OracleComp.run_interpret_pure, run_interpret_visitNodeM,
          Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure,
          PMF.pure_bind, PMF.map_comp, Function.comp_def]
        have h1 := congrArg (PMF.map fun (σ, (e', s')) =>
          (((childPath, vp.1, certs ++ [((keys.getD vp.1 ([], [])).1, σ)]), (vp.2, e')), s'))
          hedg_eq
        dsimp only [keys, keys', target, bit, childPath, vp] at hpkEq h1 ⊢
        rw [hpkEq]
        simp only [PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def] at h1 ⊢
        exact h1
      · simp only [localCertifyStep, PMF.mem_support_map_iff] at hst'
        obtain ⟨⟨σ, e', a'⟩, hm_edg, rfl⟩ := hst'
        exact ⟨hchild_vp, hmono_vp _ hroot_v, hlt_vp, huniq_vp, hedg_inv σ e' a' hm_edg⟩
  exact ⟨hmain.1, fun c v e a hm => hmain.2 (c, (v, e, a)) hm⟩

private theorem localTreeHandler_planted_step (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    {n sigCap : ℕ} (hcap : 2 ≤ S.capacity n)
    {front back : List (List Bool × List Bool)} {x : List Bool × List Bool}
    (req : Unit × List Bool) (st : PresampledState)
    (hinv : slotEdgeInv (front ++ x :: back).length st) :
    let keys := front ++ x :: back
    let keys' := front ++ (x.1, []) :: back
    let target := front.length
    ((localTreeHandler S depth keys sigCap n req st).map
      fun (ans, (ps', allSigned')) => (ans, ps', signedLogOf target allSigned')) =
      (((OracleComp.interpret
        (OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifOracle j))
          (fun q s => ProbComp.eval (S.indexedSigningOracle n x.2 q s)))
        ((plantedTreeHandler S depth keys' target sigCap n req).run st.1)).run
        (signedLogOf target st.2)).map fun ⟨⟨ans, ps'⟩, signed'⟩ => (ans, ps', signed')) ∧
    ∀ ans st',
      (ans, st') ∈ (localTreeHandler S depth (front ++ x :: back) sigCap n req st).support →
      slotEdgeInv (front ++ x :: back).length st' := by
  obtain ⟨⟨⟨visited, edges⟩, queried, seenLeaves, bad⟩, allSigned⟩ := st
  set keys := front ++ x :: back
  set keys' := front ++ (x.1, []) :: back
  set target := front.length
  have hslotLt : target < keys.length := by
    simp only [keys, target, List.length_append, List.length_cons]
    omega
  dsimp only
  rw [show (plantedTreeHandler S depth keys' target sigCap n req).run
      ((visited, edges), (queried, seenLeaves, bad)) =
      plantedTreeHandler S depth keys' target sigCap n req
        ((visited, edges), (queried, seenLeaves, bad)) from rfl]
  simp only [localTreeHandler, plantedTreeHandler, Probability.PMF.monad_bind_eq_bind,
    Probability.PMF.monad_pure_eq_pure]
  conv =>
    arg 1
    rhs
    simp only [run_interpret_ite, pmf_map_ite, OracleComp.run_interpret_bind,
      OracleComp.run_interpret_pure, ProbOracleComp.run_interpret_sample, BitString.eval_sampleList,
      Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure, PMF.bind_map,
      PMF.map_bind, PMF.pure_map, Function.comp_def]
  refine (fun h => ⟨h.1, fun ans st' hm => h.2 (ans, st') hm⟩)
    (treeHandler_map_of_invariant (req.2.length = n) (bad = true)
      (BitString.uniformList (depth n)) (fun leaf => seenLeaves.contains leaf)
      _ _ _ _ (fun x : List Bool × PresampledState => (x.1, x.2.1, signedLogOf target x.2.2))
      _ _ _ _ (fun x : List Bool × PresampledState => slotEdgeInv keys.length x.2)
      ⟨rfl, hinv⟩ ⟨rfl, hinv⟩ ⟨rfl, hinv⟩ fun _ _ leaf _ _ => ?_)
  obtain ⟨hcert_eq, hcert_inv⟩ := localCertify_planted_spec S depth hcap leaf hinv
  dsimp only [keys, keys', target] at hcert_eq ⊢
  refine bind_map_of_invariant
    (localCertify S depth keys sigCap n leaf (visited, edges, allSigned))
    ((OracleComp.interpret
      (OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifOracle j))
        (fun q s => ProbComp.eval (S.indexedSigningOracle n x.2 q s)))
      (certifyPlanted S depth keys' target sigCap n leaf (visited, edges))).run
      (signedLogOf target allSigned))
    (fun (c, (v, e, a)) => ((c, (v, e)), signedLogOf target a))
    (fun ((node, idx, _), (v', e', a')) =>
      (node, idx) ∈ v' ∧ slotEdgeInv keys.length (((v', e'), (queried, seenLeaves, bad)), a'))
    _ _ (fun x : List Bool × PresampledState => (x.1, x.2.1, signedLogOf target x.2.2))
    (fun x : List Bool × PresampledState => slotEdgeInv keys.length x.2)
    ⟨hcert_eq, fun ⟨c, v', e', a'⟩ hm => hcert_inv c v' e' a' hm⟩
    fun ⟨⟨node, idx, certs⟩, v', e', a'⟩ _ ⟨hnode_v', hroot_v', hlt_v', huniq_v', hall_v'⟩ => ?_
  have huLast : (leaf.getLastD false).toNat ≤ 1 := Bool.toNat_le _
  obtain ⟨hedg_eq, hedg_inv⟩ :=
    localSignEdge_planted_spec S (sigCap := sigCap) hcap hslotLt huniq_v' hall_v'
      hnode_v' huLast req.2
  refine ⟨?_, fun x hm_edg => ?_⟩
  · have h1 := congrArg (PMF.map fun (σ, (e'', s'')) =>
      (encodeSignature leaf certs σ,
        ((v', e''), (req.2 :: queried, leaf :: seenLeaves, false)), s'')) hedg_eq
    dsimp only [keys, keys', target] at h1 ⊢
    simp only [PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def] at h1 ⊢
    exact h1
  · obtain ⟨⟨σ, e'', a''⟩, hm_se, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hm_edg
    exact ⟨hroot_v', hlt_v', huniq_v', hedg_inv σ e'' a'' hm_se⟩

private theorem map_plantedWin_presampledExp (S : IndexedSignatureScheme)
    (depth slotBound sigCap : ℕ → ℕ) {n : ℕ} (hcap : 2 ≤ S.capacity n)
    (adversary : Forger) {target : ℕ} (htarget : target < dyadicSize (slotBound n)) :
    (presampledExp S depth slotBound sigCap adversary n).map (plantedWin S depth n target) =
      ProbComp.eval
        (S.indexedEufCmaGame (indexedForgerAt S depth slotBound sigCap adversary target) n) := by
  set K := dyadicSize (slotBound n) with hK_def
  have hmin : min target (K - 1) = target := Nat.min_eq_left (by omega)
  have hsplit : K = target + ((K - target - 1) + 1) := by omega
  simp only [presampledExp, PMF.monad_bind_eq_bind, IndexedSignatureScheme.indexedEufCmaGame,
    indexedForgerAt, plantNodeKeys, ← hK_def, hmin]
  conv_lhs => rw [hsplit, ← ProbComp.eval_replicate_splice]
  simp only [ProbComp.eval_bind, ProbComp.eval_pure, ProbOracleComp.eval_run_interpret,
    OracleComp.interpret_bind, StateT.run_bind, ProbOracleComp.run_interpret_sample,
    OracleComp.interpret_pure, StateT.run_pure, PMF.map_bind, PMF.bind_bind, PMF.pure_bind,
    PMF.pure_map, PMF.map_comp, Function.comp_def]
  refine PMF.bind_congr_on_support _ _ _ fun x _ => ?_
  refine PMF.bind_congr_on_support _ _ _ fun front hfront => ?_
  refine PMF.bind_congr_on_support _ _ _ fun back _ => ?_
  have hfrontLen : front.length = target :=
    ((ProbComp.mem_support_replicate_iff _ _ _).mp hfront).1
  subst hfrontLen
  set keys := front ++ x :: back
  set keys' := front ++ (x.1, []) :: back
  have hpk0 : (keys'.getD 0 ([], [])).1 = (keys.getD 0 ([], [])).1 :=
    fst_getD_splice front back x 0
  set pk := encPair encUnary encBits (n, (keys.getD 0 ([], [])).1)
  have hinitInv : slotEdgeInv keys.length initPresampledState := by
    refine ⟨List.mem_singleton.mpr rfl, ?_, ?_, fun _ _ _ _ h => by cases h⟩
    · intro e he _
      obtain rfl := List.mem_singleton.mp he
      simp
    · intro e₁ he₁ e₂ he₂ _ _
      rw [List.mem_singleton.mp he₁, List.mem_singleton.mp he₂]
  have hflat := ProbOracleComp.run_interpret_run_interpret
    (plantedTreeHandler S depth keys' front.length (sigCap n) n)
    (fun q s => ProbComp.eval (S.indexedSigningOracle n x.2 q s))
    (adversary n pk) initPlantedState []
  have hsim := ProbOracleComp.run_interpret_map_state_of_invariant
    (localTreeHandler S depth keys (sigCap n) n)
    (fun q (st : PlantedState × List (ℕ × List Bool)) =>
      (((OracleComp.interpret
        (OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifOracle j))
          (fun q s => ProbComp.eval (S.indexedSigningOracle n x.2 q s)))
        ((plantedTreeHandler S depth keys' front.length (sigCap n) n q).run st.1)).run st.2).map
        fun ⟨⟨a, b⟩, c⟩ => (a, b, c)))
    (fun (st : PresampledState) => (st.1, signedLogOf front.length st.2))
    (slotEdgeInv keys.length)
    (fun q st hst ans st' hm =>
      (localTreeHandler_planted_step S depth hcap q st hst).2 ans st' hm)
    (fun q st hst => (localTreeHandler_planted_step S depth hcap q st hst).1)
    (adversary n pk) initPresampledState hinitInv
  have hlogNil : signedLogOf front.length ([] : AllSignedLog) = [] := rfl
  rw [show (initPresampledState.1, signedLogOf front.length initPresampledState.2) =
    (initPlantedState, []) from rfl] at hsim
  have hcomb := (congrArg (PMF.map fun ⟨a, b, c⟩ => ((a, b), c)) hsim).trans hflat.symm
  rw [hpk0]
  have hwin := congrArg (PMF.map fun out : ((List Bool × List Bool) × PlantedState) ×
      List (ℕ × List Bool) =>
    let cand := extractForgery (depth n) front.length out.1.2.1.1 out.1.1.1 out.1.1.2
    !out.2.contains (cand.1, cand.2.1) && S.verify x.1 cand.1 cand.2.1 cand.2.2) hcomb
  simp only [PMF.map_comp, Function.comp_def, plantedWin, keys,
    List.getD_append_cons_length] at hwin ⊢
  exact hwin

/-! #### Equivalence between `lazyTreeGame` and `presampledExp` -/

private abbrev JointKeysState :=
  List (List Bool × List Bool) × PresampledState

private def nodesOf (usedKeys : List (List Bool × List Bool)) (visited : NodeSlotCache) :
    NodeKeyCache :=
  visited.map fun e => (e.1, usedKeys.getD e.2 ([], []))

private noncomputable def jointVisitKey (S : IndexedSignatureScheme) (n : ℕ) (path : List Bool)
    (uv : List (List Bool × List Bool) × NodeSlotCache) :
    PMF (ℕ × (List (List Bool × List Bool) × NodeSlotCache)) :=
  match uv.2.lookup path with
  | some idx => PMF.pure (idx, uv)
  | none =>
    (ProbComp.eval (S.keyGen n)).map fun child =>
      (uv.2.length, (uv.1 ++ [child], (path, uv.2.length) :: uv.2))

private abbrev JointKeysCertState :=
  List (List Bool × List Bool) × LocalCertState

private noncomputable def jointKeysCertifyStep (S : IndexedSignatureScheme) (sigCap n : ℕ)
    (leaf : List Bool) (st : JointKeysCertState) : PMF JointKeysCertState := do
  let (usedKeys, ((node, idx, certs), (visited, edges, allSigned))) := st
  let bit := leaf.getD node.length false
  let childPath := node ++ [bit]
  let (childIdx, (usedKeys', visited')) ← jointVisitKey S n childPath (usedKeys, visited)
  let childPk := (usedKeys'.getD childIdx ([], [])).1
  (localSignEdge S usedKeys' sigCap node idx bit.toNat childPk (edges, allSigned)).map
    fun (σ, (edges', allSigned')) =>
      (usedKeys', ((childPath, childIdx, certs ++ [(childPk, σ)]),
        (visited', edges', allSigned')))

private noncomputable def jointKeysCertify (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    (sigCap n : ℕ) (leaf : List Bool)
    (init : List (List Bool × List Bool) × (NodeSlotCache × EdgeSigCache × AllSignedLog)) :
    PMF JointKeysCertState :=
  Nat.iterate (fun d => d.bind (jointKeysCertifyStep S sigCap n leaf)) (depth n - 1)
    (PMF.pure (init.1, (([], 0, []), init.2)))

private noncomputable def jointKeysHandler (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    (sigCap n : ℕ) (request : Unit × List Bool) :
    StateT JointKeysState PMF (List Bool) := fun state =>
  let msg := request.2
  let (usedKeys, (((visited, edges), (queried, seenLeaves, bad)), allSigned)) := state
  if msg.length = n then
    if bad then
      PMF.pure ([], (usedKeys, (((visited, edges), (msg :: queried, seenLeaves, true)), allSigned)))
    else do
      let leaf ← BitString.uniformList (depth n)
      if seenLeaves.contains leaf then
        pure ([], (usedKeys, (((visited, edges), (msg :: queried, seenLeaves, true)), allSigned)))
      else
        let (usedKeys', ((node, idx, certs), (visited', edges', allSigned'))) ←
          jointKeysCertify S depth sigCap n leaf (usedKeys, (visited, edges, allSigned))
        (localSignEdge S usedKeys' sigCap node idx (leaf.getLastD false).toNat msg
          (edges', allSigned')).map fun (σ, (edges'', allSigned'')) =>
            (encodeSignature leaf certs σ,
              (usedKeys', (((visited', edges''),
                (msg :: queried, leaf :: seenLeaves, false)), allSigned'')))
  else
    PMF.pure ([], (usedKeys, (((visited, edges), (msg :: queried, seenLeaves, bad)), allSigned)))

private def jointKeysInv (S : IndexedSignatureScheme) (n : ℕ) (root : List Bool × List Bool)
    (st : JointKeysState) : Prop :=
  let (usedKeys, (((visited, _), _), _)) := st
  usedKeys.length = visited.length ∧
  visited.lookup [] = some 0 ∧
  usedKeys.getD 0 ([], []) = root ∧
  (∀ k ∈ usedKeys, k ∈ (ProbComp.eval (S.keyGen n)).support) ∧
  ∀ e ∈ visited, e.2 < visited.length

private theorem nodesOf_append_singleton (usedKeys : List (List Bool × List Bool))
    (visited : NodeSlotCache) (hvis : ∀ e ∈ visited, e.2 < usedKeys.length)
    (path : List Bool) (child : List Bool × List Bool) :
    nodesOf (usedKeys ++ [child]) ((path, usedKeys.length) :: visited) =
      (path, child) :: nodesOf usedKeys visited := by
  simp only [nodesOf, List.map_cons]
  have hhead : (usedKeys ++ [child]).getD usedKeys.length ([], []) = child :=
    List.getD_append_cons_length usedKeys [] child ([], [])
  rw [hhead]
  congr 1
  refine List.map_congr_left fun e he => ?_
  rw [List.getD_append _ _ _ _ (hvis e he)]

private theorem jointVisitKey_support_inv (S : IndexedSignatureScheme) (n : ℕ)
    {uk : List (List Bool × List Bool)} {vis : NodeSlotCache}
    (hlen : uk.length = vis.length) (hpos : 0 < uk.length)
    (hvis : ∀ e ∈ vis, e.2 < vis.length) (path : List Bool)
    {idx : ℕ} {uk' : List (List Bool × List Bool)} {vis' : NodeSlotCache}
    (hm : (idx, (uk', vis')) ∈ (jointVisitKey S n path (uk, vis)).support) :
    uk'.length = vis'.length ∧
    0 < uk'.length ∧
    (∀ e ∈ vis', e.2 < vis'.length) ∧
    idx < uk'.length ∧
    uk.length ≤ uk'.length ∧
    vis'.length ≤ vis.length + 1 ∧
    uk'.getD 0 ([], []) = uk.getD 0 ([], []) ∧
    (∀ k ∈ uk', k ∈ uk ∨ k ∈ (ProbComp.eval (S.keyGen n)).support) ∧
    (∀ j < uk.length, uk'.getD j ([], []) = uk.getD j ([], [])) ∧
    (∀ p₀ i₀, vis.lookup p₀ = some i₀ → vis'.lookup p₀ = some i₀) := by
  simp only [jointVisitKey] at hm
  cases hlk : vis.lookup path with
  | some i₀ =>
    rw [hlk] at hm
    obtain ⟨rfl, h2⟩ := Prod.mk.inj ((PMF.mem_support_pure_iff _ _).mp hm)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
    exact ⟨hlen, hpos, hvis, hlen ▸ hvis _ (lookup_mem hlk), le_rfl, Nat.le_succ _,
      rfl, fun _ h => Or.inl h, fun _ _ => rfl, fun _ _ h => h⟩
  | none =>
    rw [hlk] at hm
    obtain ⟨child, hchild, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hm
    obtain ⟨rfl, h2⟩ := Prod.mk.inj heq.symm
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
    refine ⟨by simp [hlen], by simp, ?_, by simp [hlen], by simp, by simp,
      List.getD_append _ _ _ _ hpos, ?_, fun j hj => List.getD_append _ _ _ _ hj, ?_⟩
    · intro e he
      simp only [List.length_cons]
      rcases List.mem_cons.mp he with rfl | htail
      · simp
      · have := hvis e htail
        omega
    · intro k hk
      rcases List.mem_append.mp hk with hk | hk
      · exact Or.inl hk
      · obtain rfl := List.mem_singleton.mp hk
        exact Or.inr hchild
    · intro p₀ i₀ hp₀
      have hne : p₀ ≠ path := fun h => by subst h; rw [hp₀] at hlk; cases hlk
      rw [List.lookup_cons, beq_false_of_ne hne]
      exact hp₀

private theorem jointVisitKey_lazy_spec (S : IndexedSignatureScheme) (n : ℕ)
    {root : List Bool × List Bool} {usedKeys : List (List Bool × List Bool)}
    {visited : NodeSlotCache}
    (hlen : usedKeys.length = visited.length)
    (hrootVis : visited.lookup [] = some 0)
    (hrootKey : usedKeys.getD 0 ([], []) = root)
    (hsupp : ∀ k ∈ usedKeys, k ∈ (ProbComp.eval (S.keyGen n)).support)
    (hvis : ∀ e ∈ visited, e.2 < visited.length) (path : List Bool) :
    ((jointVisitKey S n path (usedKeys, visited)).map
      fun (idx, (uk', vis')) => (uk'.getD idx ([], []), nodesOf uk' vis')) =
      ProbComp.eval (memoize (fun _ => S.keyGen n) path (nodesOf usedKeys visited)) ∧
    ∀ idx uk' vis',
      (idx, (uk', vis')) ∈ (jointVisitKey S n path (usedKeys, visited)).support →
      uk'.length = vis'.length ∧
      vis'.lookup [] = some 0 ∧
      uk'.getD 0 ([], []) = root ∧
      (∀ k ∈ uk', k ∈ (ProbComp.eval (S.keyGen n)).support) ∧
      (∀ e ∈ vis', e.2 < vis'.length) ∧
      idx < uk'.length ∧
      usedKeys.length ≤ uk'.length ∧
      vis'.length ≤ visited.length + 1 ∧
      ∀ j < usedKeys.length, uk'.getD j ([], []) = usedKeys.getD j ([], []) := by
  have hpos : 0 < usedKeys.length := by
    have := hvis ([], 0) (lookup_mem hrootVis)
    omega
  refine ⟨?_, ?_⟩
  · simp only [jointVisitKey, memoize]
    have hlkMap : (nodesOf usedKeys visited).lookup path =
        (visited.lookup path).map (fun i => usedKeys.getD i ([], [])) :=
      List.lookup_map_snd visited (fun i => usedKeys.getD i ([], [])) path
    cases hlk : visited.lookup path with
    | some idx =>
      rw [hlk, Option.map_some] at hlkMap
      simp only [hlkMap, PMF.pure_map, ProbComp.eval_pure]
    | none =>
      rw [hlk, Option.map_none] at hlkMap
      have hvisU : ∀ e ∈ visited, e.2 < usedKeys.length := fun e he => hlen ▸ hvis e he
      simp only [hlkMap, bind_pure_comp, ProbComp.eval_map, PMF.map_comp, Function.comp_def]
      refine PMF.map_congr_on_support _ _ _ fun child _ => ?_
      simp only [← hlen, List.getD_append_cons_length usedKeys [] child ([], []),
        nodesOf_append_singleton usedKeys visited hvisU path child]
  · intro i uk' vis' hm
    obtain ⟨h1, _, h5, h6, h7, h8, h0, h4, h9, hlk0⟩ :=
      jointVisitKey_support_inv S n hlen hpos hvis path hm
    exact ⟨h1, hlk0 [] 0 hrootVis, h0.trans hrootKey,
      fun k hk => (h4 k hk).elim (hsupp k) id, h5, h6, h7, h8, h9⟩

private theorem localSignEdge_notrunc (S : IndexedSignatureScheme) {sigCap n : ℕ}
    (hsigCap : ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
      (msg.length = n ∨ ∃ keys' ∈ (ProbComp.eval (S.keyGen n)).support, msg = keys'.1) →
      ∀ σ ∈ (ProbComp.eval (S.sign keys.2 u msg)).support, σ.length ≤ sigCap)
    {usedKeys : List (List Bool × List Bool)}
    (hsupp : ∀ k ∈ usedKeys, k ∈ (ProbComp.eval (S.keyGen n)).support)
    {idx u : ℕ} (hidx : idx < usedKeys.length) (hu : u ≤ 1)
    {path msg : List Bool}
    (hmsg : msg.length = n ∨ ∃ keys' ∈ (ProbComp.eval (S.keyGen n)).support, msg = keys'.1)
    (edges : EdgeSigCache) (allSigned : AllSignedLog) :
    ((localSignEdge S usedKeys sigCap path idx u msg (edges, allSigned)).map
      fun (σ, (edges', _)) => (σ, edges')) =
      ProbComp.eval
        (memoize (fun _ => S.sign (usedKeys.getD idx ([], [])).2 u msg) (path, u) edges) := by
  simp only [localSignEdge, memoize]
  cases edges.lookup (path, u) with
  | some σ₀ =>
    simp only [PMF.pure_map, ProbComp.eval_pure]
  | none =>
    simp only [bind_pure_comp, ProbComp.eval_map, PMF.map_comp, Function.comp_def]
    have hk_mem := hsupp _ (List.getD_mem ([], []) hidx)
    refine PMF.map_congr_on_support _ _ _ fun raw hraw => ?_
    have hle := hsigCap _ hk_mem u hu msg hmsg raw hraw
    simp only [List.take_of_length_le hle]

private theorem jointKeysCertify_lazy_spec (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    {sigCap n : ℕ}
    (hsigCap : ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
      (msg.length = n ∨ ∃ keys' ∈ (ProbComp.eval (S.keyGen n)).support, msg = keys'.1) →
      ∀ σ ∈ (ProbComp.eval (S.sign keys.2 u msg)).support, σ.length ≤ sigCap)
    {root : List Bool × List Bool} {st : JointKeysState}
    (hinv : jointKeysInv S n root st) (leaf : List Bool) :
    let (usedKeys, (((visited, edges), rest), allSigned)) := st
    ((jointKeysCertify S depth sigCap n leaf (usedKeys, (visited, edges, allSigned))).map
      fun (uk', ((node, idx, certs), (vis', edg', _))) =>
        ((node, uk'.getD idx ([], []), certs), (nodesOf uk' vis', edg'))) =
      ProbComp.eval (certifyLazy S depth n root leaf (nodesOf usedKeys visited, edges)) ∧
    ∀ uk' node idx certs vis' edg' all',
      (uk', ((node, idx, certs), (vis', edg', all'))) ∈
        (jointKeysCertify S depth sigCap n leaf
          (usedKeys, (visited, edges, allSigned))).support →
      jointKeysInv S n root (uk', (((vis', edg'), rest), all')) ∧
      idx < uk'.length := by
  obtain ⟨usedKeys, ⟨⟨visited, edges⟩, rest⟩, allSigned⟩ := st
  obtain ⟨hlen0, hrootVis0, hrootKey0, hsupp0, hvis0⟩ := hinv
  have hpos0 : 0 < usedKeys.length := by
    have := hvis0 ([], 0) (lookup_mem hrootVis0)
    omega
  dsimp only [jointKeysCertify, certifyLazy]
  rw [eval_iterate_probComp]
  let rep : JointKeysCertState → LazyCertState :=
    fun (uk', ((node, idx, certs), (vis', edg', _))) =>
      ((node, uk'.getD idx ([], []), certs), (nodesOf uk' vis', edg'))
  let stepInv (out : JointKeysCertState) : Prop :=
    let (uk, ((_, idx, _), (vis, edg, all))) := out
    jointKeysInv S n root (uk, (((vis, edg), rest), all)) ∧ idx < uk.length
  have hmain := iterate_pmf_map_of_invariant
    (jointKeysCertifyStep S sigCap n leaf)
    (fun s => ProbComp.eval (certifyStepLazy S n leaf s)) rep
    (fun _ out => stepInv out) (depth n - 1)
    (usedKeys, (([], 0, []), (visited, edges, allSigned)))
    ⟨⟨hlen0, hrootVis0, hrootKey0, hsupp0, hvis0⟩, hpos0⟩
    fun _ _ ⟨uk, ⟨node, idx, certs⟩, vis, edg, all⟩
        ⟨⟨hlen, hrootVis, hrootKey, hsupp_u, hvis⟩, hidx⟩ => by
      set bit := leaf.getD node.length false
      set childPath := node ++ [bit]
      obtain ⟨hvis_eq, hvis_inv⟩ :=
        jointVisitKey_lazy_spec S n hlen hrootVis hrootKey hsupp_u hvis childPath
      have hbu : bit.toNat ≤ 1 := Bool.toNat_le bit
      simp only [jointKeysCertifyStep, certifyStepLazy, ProbComp.eval_bind, ProbComp.eval_pure,
        PMF.monad_bind_eq_bind]
      refine bind_map_of_invariant (jointVisitKey S n childPath (uk, vis))
        (ProbComp.eval (memoize (fun _ => S.keyGen n) childPath (nodesOf uk vis)))
        (fun (idx, (uk', vis')) => (uk'.getD idx ([], []), nodesOf uk' vis'))
        (fun (childIdx, (uk', vis')) =>
          jointKeysInv S n root (uk', (((vis', edg), rest), all)) ∧ childIdx < uk'.length ∧
          uk'.getD idx ([], []) = uk.getD idx ([], []) ∧ idx < uk'.length)
        _ _ rep stepInv ⟨hvis_eq, fun ⟨childIdx, uk', vis'⟩ hm_v => by
          obtain ⟨hlen', hrv', hrk', hsp', hv', hcLt, hlenLe, _, hkeep⟩ :=
            hvis_inv childIdx uk' vis' hm_v
          exact ⟨⟨hlen', hrv', hrk', hsp', hv'⟩, hcLt, hkeep idx hidx, hidx.trans_le hlenLe⟩⟩
        fun ⟨childIdx, uk', vis'⟩ _ ⟨⟨hlen', hrv', hrk', hsp', hv'⟩, hcLt, hidx_eq, hidx'⟩ => by
          have hchildMem := hsp' _ (List.getD_mem ([], []) hcLt)
          have hse := localSignEdge_notrunc S hsigCap hsp' hidx' hbu (path := node)
            (Or.inr ⟨_, hchildMem, rfl⟩) edg all
          rw [hidx_eq] at hse
          refine ⟨?_, fun out' hm_out => ?_⟩
          · dsimp only [Function.comp_def, bit, rep]
            have heq := congrArg (PMF.map fun (σ, edg') =>
              ((childPath, uk'.getD childIdx ([], []),
                  certs ++ [((uk'.getD childIdx ([], [])).1, σ)]),
                nodesOf uk' vis', edg')) hse
            simp only [PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def] at heq ⊢
            exact heq
          · obtain ⟨⟨σ, edg', all'⟩, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hm_out
            exact ⟨⟨hlen', hrv', hrk', hsp', hv'⟩, hcLt⟩
  refine ⟨by simpa only [rep, hrootKey0] using hmain.1, fun uk' node idx certs vis' edg' all' hm =>
    hmain.2 (uk', ((node, idx, certs), (vis', edg', all'))) hm⟩

private def lazyStateOfJoint (st : JointKeysState) : LazyTreeState :=
  ((nodesOf st.1 st.2.1.1.1, st.2.1.1.2), st.2.1.2)

private theorem jointKeysHandler_lazy_step (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    {sigCap n : ℕ}
    (hsigCap : ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
      (msg.length = n ∨ ∃ keys' ∈ (ProbComp.eval (S.keyGen n)).support, msg = keys'.1) →
      ∀ σ ∈ (ProbComp.eval (S.sign keys.2 u msg)).support, σ.length ≤ sigCap)
    {root : List Bool × List Bool} (req : Unit × List Bool) (st : JointKeysState)
    (hinv : jointKeysInv S n root st) :
    ((jointKeysHandler S depth sigCap n req st).map fun (ans, st') =>
      (ans, lazyStateOfJoint st')) =
      ProbComp.eval (lazySignHandler S depth n root req (lazyStateOfJoint st)) ∧
    ∀ ans st', (ans, st') ∈ (jointKeysHandler S depth sigCap n req st).support →
      jointKeysInv S n root st' := by
  obtain ⟨uk, ⟨⟨vis, edg⟩, queried, seenLeaves, bad⟩, allSigned⟩ := st
  simp only [lazyStateOfJoint]
  simp only [jointKeysHandler, lazySignHandler, eval_ite, ProbComp.eval_bind,
    BitString.eval_sampleList, ProbComp.eval_pure, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  refine (fun h => ⟨h.1, fun ans st' hm => h.2 (ans, st') hm⟩)
    (treeHandler_map_of_invariant (req.2.length = n) (bad = true)
      (BitString.uniformList (depth n)) (fun leaf => seenLeaves.contains leaf)
      _ _ _ _ (fun x : List Bool × JointKeysState => (x.1, lazyStateOfJoint x.2)) _ _ _ _
      (fun x : List Bool × JointKeysState => jointKeysInv S n root x.2)
      ⟨rfl, hinv⟩ ⟨rfl, hinv⟩ ⟨rfl, hinv⟩ fun hmsg _ leaf _ _ => ?_)
  obtain ⟨hcert_eq, hcert_inv⟩ := jointKeysCertify_lazy_spec S depth hsigCap hinv leaf
  refine bind_map_of_invariant
    (jointKeysCertify S depth sigCap n leaf (uk, (vis, edg, allSigned)))
    (ProbComp.eval (certifyLazy S depth n root leaf (nodesOf uk vis, edg)))
    (fun (uk', ((node, idx, certs), (vis', edg', _))) =>
      ((node, uk'.getD idx ([], []), certs), (nodesOf uk' vis', edg')))
    (fun (uk', (_, idx, _), (vis', edg', all')) =>
      jointKeysInv S n root (uk', (((vis', edg'), (queried, seenLeaves, bad)), all')) ∧
      idx < uk'.length)
    _ _ (fun x : List Bool × JointKeysState => (x.1, lazyStateOfJoint x.2))
    (fun x : List Bool × JointKeysState => jointKeysInv S n root x.2)
    ⟨hcert_eq, fun ⟨uk', ⟨node, idx, certs⟩, vis', edg', all'⟩ hm =>
      hcert_inv uk' node idx certs vis' edg' all' hm⟩
    fun ⟨uk', ⟨node, idx, certs⟩, vis', edg', all'⟩ _
      ⟨⟨hlen', hrv', hrk', hsp', hv'⟩, hidx'⟩ => ?_
  have huLast : (leaf.getLastD false).toNat ≤ 1 := Bool.toNat_le _
  have hse := localSignEdge_notrunc S hsigCap hsp' hidx' huLast (path := node)
    (Or.inl hmsg) edg' all'
  refine ⟨?_, fun x hm_se => ?_⟩
  · dsimp only [Function.comp_def, lazyStateOfJoint]
    have heq := congrArg (PMF.map fun (σ, edg'') =>
      (encodeSignature leaf certs σ, (nodesOf uk' vis', edg''),
        req.2 :: queried, leaf :: seenLeaves, false)) hse
    simp only [PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def] at heq ⊢
    exact heq
  · obtain ⟨⟨σ, edg'', all''⟩, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hm_se
    exact ⟨hlen', hrv', hrk', hsp', hv'⟩

private noncomputable def expandKeys (S : IndexedSignatureScheme) (n K : ℕ)
    (uk : List (List Bool × List Bool)) : PMF (List (List Bool × List Bool)) :=
  (ProbComp.eval (OracleComp.replicate (K - uk.length) (S.keyGen n))).map (uk ++ ·)

private theorem jointVisitKey_expandKeys (S : IndexedSignatureScheme) (n K : ℕ)
    {uk : List (List Bool × List Bool)} {vis : NodeSlotCache}
    (hlen : uk.length = vis.length) (hlt : vis.length < K) (path : List Bool) :
    ((jointVisitKey S n path (uk, vis)).bind fun (idx, (uk', vis')) =>
      (expandKeys S n K uk').map fun keys => (keys, idx, vis')) =
      (expandKeys S n K uk).map fun keys =>
        let (idx, vis') := visitNodePure keys.length path vis
        (keys, idx, vis') := by
  simp only [jointVisitKey, visitNodePure]
  cases vis.lookup path with
  | some idx =>
    simp only [PMF.pure_bind]
  | none =>
    set m := K - uk.length - 1
    have hsub : K - uk.length = m + 1 := by omega
    simp only [expandKeys, hsub, OracleComp.replicate_succ, ProbComp.eval_bind,
      ProbComp.eval_map, PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def]
    refine PMF.bind_congr_on_support _ _ _ fun child _ => ?_
    have hsub' : K - (uk ++ [child]).length = m := by
      simp only [List.length_append, List.length_singleton]
      omega
    rw [hsub']
    refine PMF.map_congr_on_support _ _ _ fun rem hrem => ?_
    have hremLen : rem.length = m := ((ProbComp.mem_support_replicate_iff _ _ _).mp hrem).1
    have htotLen : (uk ++ child :: rem).length = K := by
      simp only [List.length_append, List.length_cons, hremLen]
      omega
    have hmin : min vis.length (uk ++ child :: rem).length = vis.length := by
      rw [htotLen]
      exact Nat.min_eq_left hlt.le
    simp only [List.append_assoc, List.singleton_append, hmin]

private theorem localSignEdge_expandKeys (S : IndexedSignatureScheme) (n K sigCap : ℕ)
    {uk : List (List Bool × List Bool)} {idx : ℕ} (hidx : idx < uk.length)
    (path : List Bool) (u : ℕ) (msg : List Bool) (ea : EdgeSigCache × AllSignedLog) :
    ((localSignEdge S uk sigCap path idx u msg ea).bind fun out =>
      (expandKeys S n K uk).map fun keys => (keys, out)) =
      (expandKeys S n K uk).bind fun keys =>
        (localSignEdge S keys sigCap path idx u msg ea).map fun out => (keys, out) := by
  have hcomm : ((localSignEdge S uk sigCap path idx u msg ea).bind fun out =>
      (expandKeys S n K uk).map fun keys => (keys, out)) =
      (expandKeys S n K uk).bind fun keys =>
        (localSignEdge S uk sigCap path idx u msg ea).map fun out => (keys, out) := by
    simp only [PMF.map]
    exact PMF.bind_comm _ _ _
  rw [hcomm]
  refine PMF.bind_congr_on_support _ _ _ fun keys hkeys => ?_
  obtain ⟨rem, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hkeys
  simp only [localSignEdge, List.getD_append _ _ _ _ hidx]

private theorem jointKeysCertify_expandKeys (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    (sigCap n K : ℕ) {uk : List (List Bool × List Bool)} {vis : NodeSlotCache}
    (hlen0 : uk.length = vis.length) (hpos0 : 0 < uk.length)
    (hvis0 : ∀ e ∈ vis, e.2 < vis.length) (hbound : vis.length + (depth n - 1) ≤ K)
    (leaf : List Bool) (edg : EdgeSigCache) (all : AllSignedLog) :
    ((jointKeysCertify S depth sigCap n leaf (uk, (vis, edg, all))).bind
      fun (uk', cs) => (expandKeys S n K uk').map fun keys => (keys, cs)) =
      (expandKeys S n K uk).bind (fun keys =>
        (localCertify S depth keys sigCap n leaf (vis, edg, all)).map fun cs => (keys, cs)) ∧
    ∀ uk' cs, (uk', cs) ∈ (jointKeysCertify S depth sigCap n leaf (uk, (vis, edg, all))).support →
      uk'.length = cs.2.1.length ∧ 0 < uk'.length ∧
      (∀ e ∈ cs.2.1, e.2 < cs.2.1.length) ∧
      cs.1.2.1 < uk'.length ∧ cs.2.1.length ≤ vis.length + (depth n - 1) := by
  dsimp only [jointKeysCertify, localCertify]
  let inv (m : ℕ) (st : List (List Bool × List Bool) × LocalCertState) : Prop :=
    st.1.length = st.2.2.1.length ∧ 0 < st.1.length ∧
    (∀ e ∈ st.2.2.1, e.2 < st.2.2.1.length) ∧
    st.2.1.2.1 < st.1.length ∧ st.2.2.1.length ≤ vis.length + m
  have hmain := iterate_pmf_bind_comm_of_invariant (jointKeysCertifyStep S sigCap n leaf)
    (fun keys => localCertifyStep S keys sigCap leaf) (fun st => expandKeys S n K st.1) Prod.snd
    inv (depth n - 1) (uk, (([], 0, []), (vis, edg, all)))
    ⟨hlen0, hpos0, hvis0, hpos0, Nat.le_add_right _ _⟩
    fun m hm ⟨uk_m, ⟨⟨node, idx, certs⟩, vis_m, edg_m, all_m⟩⟩
        ⟨hlen_m, hpos_m, hvis_m, hidx_m, hgrow_m⟩ => by
      dsimp only at hlen_m hpos_m hvis_m hidx_m hgrow_m
      have hltK : vis_m.length < K := by omega
      set bit := leaf.getD node.length false
      set childPath := node ++ [bit]
      simp only [jointKeysCertifyStep, localCertifyStep, PMF.monad_bind_eq_bind]
      have hstep := bind_bind_comm_of_invariant (jointVisitKey S n childPath (uk_m, vis_m))
        (fun x => expandKeys S n K x.2.1) (fun x => (x.1, x.2.2))
        (fun keys => PMF.pure (visitNodePure keys.length childPath vis_m))
        (fun x => x.2.1.length = x.2.2.length ∧ 0 < x.2.1.length ∧
          (∀ e ∈ x.2.2, e.2 < x.2.2.length) ∧
          x.1 < x.2.1.length ∧ uk_m.length ≤ x.2.1.length ∧ x.2.2.length ≤ vis_m.length + 1)
        (expandKeys S n K uk_m)
        (fun (childIdx, uk', vis') =>
          let childPk := (uk'.getD childIdx ([], [])).1
          (localSignEdge S uk' sigCap node idx bit.toNat childPk (edg_m, all_m)).map
            fun (σ, (edg', all')) =>
              (uk', ((childPath, childIdx, certs ++ [(childPk, σ)]), (vis', edg', all'))))
        (fun x => expandKeys S n K x.1) Prod.snd
        (fun keys (childIdx, vis') =>
          let childPk := (keys.getD childIdx ([], [])).1
          (localSignEdge S keys sigCap node idx bit.toNat childPk (edg_m, all_m)).map
            fun (σ, (edg', all')) =>
              ((childPath, childIdx, certs ++ [(childPk, σ)]), (vis', edg', all')))
        (inv (m + 1))
        ⟨by simpa only [PMF.map, PMF.pure_bind, Function.comp_def] using
            jointVisitKey_expandKeys S n K hlen_m hltK childPath,
          fun ⟨childIdx, uk', vis'⟩ hm_vk => by
            obtain ⟨hl, hp, hv, hc, hle, hg, -⟩ :=
              jointVisitKey_support_inv S n hlen_m hpos_m hvis_m childPath hm_vk
            exact ⟨hl, hp, hv, hc, hle, hg⟩⟩
        fun ⟨childIdx, uk', vis'⟩ _ ⟨hl1, hp1, hv1, hcLt, hleU, hg1⟩ => by
          have hidx' : idx < uk'.length := hidx_m.trans_le hleU
          refine ⟨?_, ?_⟩
          · simp only [PMF.bind_map, Function.comp_def]
            have hse := localSignEdge_expandKeys S n K sigCap hidx' node bit.toNat
              (uk'.getD childIdx ([], [])).1 (edg_m, all_m)
            have hse' := congrArg (PMF.map fun (keys, (σ, (edg', all'))) =>
              (keys, ((childPath, childIdx, certs ++ [((uk'.getD childIdx ([], [])).1, σ)]),
                (vis', edg', all')))) hse
            simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at hse'
            rw [hse']
            refine PMF.bind_congr_on_support _ _ _ fun keys hkeys => ?_
            obtain ⟨rem, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hkeys
            rw [List.getD_append _ _ _ _ hcLt]
            simp only [PMF.map_comp, Function.comp_def]
          · intro ⟨uk'', cs'⟩ hm_se
            obtain ⟨⟨σ, edg', all'⟩, -, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hm_se
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq.symm
            exact ⟨hl1, hp1, hv1, hcLt, hg1.trans (Nat.add_le_add_right hgrow_m 1)⟩
      exact ⟨by simpa only [PMF.pure_bind] using hstep.1, hstep.2⟩
  exact ⟨hmain.1, fun uk' cs hm => hmain.2 (uk', cs) hm⟩

private def jointExpandInv (K : ℕ) (budget : ℕ) (st : JointKeysState) : Prop :=
  st.1.length = st.2.1.1.1.length ∧
  0 < st.1.length ∧
  (∀ e ∈ st.2.1.1.1, e.2 < st.2.1.1.1.length) ∧
  st.2.1.1.1.length + budget ≤ K

private theorem jointKeysHandler_expandKeys (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    (sigCap n K : ℕ) (req : Unit × List Bool) (st : JointKeysState)
    (hinv : jointExpandInv K (depth n - 1) st) :
    ((jointKeysHandler S depth sigCap n req st).bind fun (ans, (uk', ps')) =>
      (expandKeys S n K uk').map fun keys => (keys, ans, ps')) =
      (expandKeys S n K st.1).bind (fun keys =>
        (localTreeHandler S depth keys sigCap n req st.2).map fun (ans, ps') =>
          (keys, ans, ps')) ∧
    ∀ ans uk' ps', (ans, (uk', ps')) ∈ (jointKeysHandler S depth sigCap n req st).support →
      uk'.length = ps'.1.1.1.length ∧
      0 < uk'.length ∧
      (∀ e ∈ ps'.1.1.1, e.2 < ps'.1.1.1.length) ∧
      ps'.1.1.1.length ≤ st.2.1.1.1.length + (depth n - 1) := by
  obtain ⟨uk, ⟨⟨vis, edg⟩, queried, seenLeaves, bad⟩, allSigned⟩ := st
  obtain ⟨hlen, hpos, hvis, hbound⟩ := hinv
  dsimp only at hlen hpos hvis hbound ⊢
  simp only [jointKeysHandler, localTreeHandler, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  let invOut : List Bool × JointKeysState → Prop := fun x =>
    x.2.1.length = x.2.2.1.1.1.length ∧ 0 < x.2.1.length ∧
    (∀ e ∈ x.2.2.1.1.1, e.2 < x.2.2.1.1.1.length) ∧
    x.2.2.1.1.1.length ≤ vis.length + (depth n - 1)
  have hpureInv : uk.length = vis.length ∧ 0 < uk.length ∧
      (∀ e ∈ vis, e.2 < vis.length) ∧ vis.length ≤ vis.length + (depth n - 1) :=
    ⟨hlen, hpos, hvis, Nat.le_add_right _ _⟩
  have hmain := treeHandler_bind_comm_of_invariant (req.2.length = n) (bad = true)
    (BitString.uniformList (depth n)) (fun leaf => seenLeaves.contains leaf)
    ([], (uk, (((vis, edg), (req.2 :: queried, seenLeaves, bad)), allSigned)))
    ([], (uk, (((vis, edg), (req.2 :: queried, seenLeaves, true)), allSigned)))
    ([], (uk, (((vis, edg), (req.2 :: queried, seenLeaves, true)), allSigned)))
    (fun leaf => (jointKeysCertify S depth sigCap n leaf (uk, (vis, edg, allSigned))).bind
      fun (uk', ((node, idx, certs), (vis', edg', allSigned'))) =>
        (localSignEdge S uk' sigCap node idx (leaf.getLastD false).toNat req.2
          (edg', allSigned')).map fun (σ, (edg'', allSigned'')) =>
            (encodeSignature leaf certs σ,
              (uk', (((vis', edg''),
                (req.2 :: queried, leaf :: seenLeaves, false)), allSigned''))))
    (expandKeys S n K uk) (fun x : List Bool × JointKeysState => expandKeys S n K x.2.1)
    (fun x : List Bool × JointKeysState => (x.1, x.2.2))
    (fun _ => ([], (((vis, edg), (req.2 :: queried, seenLeaves, bad)), allSigned)))
    (fun _ => ([], (((vis, edg), (req.2 :: queried, seenLeaves, true)), allSigned)))
    (fun _ => ([], (((vis, edg), (req.2 :: queried, seenLeaves, true)), allSigned)))
    (fun keys leaf => (localCertify S depth keys sigCap n leaf (vis, edg, allSigned)).bind
      fun ((node, idx, certs), (vis', edg', allSigned')) =>
        (localSignEdge S keys sigCap node idx (leaf.getLastD false).toNat req.2
          (edg', allSigned')).map fun (σ, (edg'', allSigned'')) =>
            (encodeSignature leaf certs σ,
              (((vis', edg''), (req.2 :: queried, leaf :: seenLeaves, false)), allSigned'')))
    invOut ⟨rfl, hpureInv⟩ ⟨rfl, hpureInv⟩ ⟨rfl, hpureInv⟩ fun _ _ leaf _ _ => by
      have hcert :=
        jointKeysCertify_expandKeys S depth sigCap n K hlen hpos hvis hbound leaf edg allSigned
      let certInv : List (List Bool × List Bool) × LocalCertState → Prop := fun (uk', cs') =>
        uk'.length = cs'.2.1.length ∧ 0 < uk'.length ∧
        (∀ e ∈ cs'.2.1, e.2 < cs'.2.1.length) ∧
        cs'.1.2.1 < uk'.length ∧ cs'.2.1.length ≤ vis.length + (depth n - 1)
      exact bind_bind_comm_of_invariant
        (jointKeysCertify S depth sigCap n leaf (uk, (vis, edg, allSigned)))
        (fun x => expandKeys S n K x.1) Prod.snd
        (fun keys => localCertify S depth keys sigCap n leaf (vis, edg, allSigned))
        certInv (expandKeys S n K uk)
        (fun (uk', ((node, idx, certs), (vis', edg', allSigned'))) =>
          (localSignEdge S uk' sigCap node idx (leaf.getLastD false).toNat req.2
            (edg', allSigned')).map fun (σ, (edg'', allSigned'')) =>
              (encodeSignature leaf certs σ,
                (uk', (((vis', edg''),
                  (req.2 :: queried, leaf :: seenLeaves, false)), allSigned''))))
        (fun x : List Bool × JointKeysState => expandKeys S n K x.2.1)
        (fun x : List Bool × JointKeysState => (x.1, x.2.2))
        (fun keys ((node, idx, certs), (vis', edg', allSigned')) =>
          (localSignEdge S keys sigCap node idx (leaf.getLastD false).toNat req.2
            (edg', allSigned')).map fun (σ, (edg'', allSigned'')) =>
              (encodeSignature leaf certs σ,
                (((vis', edg''), (req.2 :: queried, leaf :: seenLeaves, false)), allSigned'')))
        invOut ⟨hcert.1, fun ⟨uk', cs'⟩ hm => hcert.2 uk' cs' hm⟩
        fun ⟨uk', ⟨node, idx, certs⟩, vis', edg', all'⟩ _ ⟨hl1, hp1, hv1, hidx', hg1⟩ => by
          refine ⟨?_, ?_⟩
          · simp only [PMF.bind_map, Function.comp_def]
            have hse := localSignEdge_expandKeys S n K sigCap hidx' node
              (leaf.getLastD false).toNat req.2 (edg', all')
            have hse' := congrArg (PMF.map fun (keys, (σ, (edg'', all''))) =>
              (keys, encodeSignature leaf certs σ,
                (((vis', edg''), (req.2 :: queried, leaf :: seenLeaves, false)), all''))) hse
            simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def] using hse'
          · intro ⟨ans, uk'', ps'⟩ hm_se
            obtain ⟨⟨σ, edg'', all''⟩, -, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hm_se
            obtain ⟨_, h2⟩ := Prod.mk.inj heq.symm
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
            exact ⟨hl1, hp1, hv1, hg1⟩
  exact ⟨hmain.1, fun ans uk' ps' hm => hmain.2 (ans, (uk', ps')) hm⟩

private theorem expand_jointKeys_run_interpret {α : Type} (S : IndexedSignatureScheme)
    (depth : ℕ → ℕ) (sigCap n K : ℕ) {prog : WordOracleComp Unit α} {rem : ℕ}
    (hq : prog.IsQueryBounded rem) {st : JointKeysState}
    (hinv : jointExpandInv K (rem * (depth n - 1)) st) :
    (((OracleComp.interpret
      (OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifOracle j))
        (jointKeysHandler S depth sigCap n))
      prog).run st).bind fun (res, (uk', ps')) =>
        (expandKeys S n K uk').map fun keys => (keys, res, ps')) =
      (expandKeys S n K st.1).bind fun keys =>
        ((OracleComp.interpret
          (OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifOracle j))
            (localTreeHandler S depth keys sigCap n))
          prog).run st.2).map fun (res, ps') => (keys, res, ps') := by
  exact (run_interpret_queryBounded_bind_comm (jointKeysHandler S depth sigCap n)
    (fun keys => localTreeHandler S depth keys sigCap n)
    (fun st => expandKeys S n K st.1) Prod.snd
    (fun rem st => jointExpandInv K (rem * (depth n - 1)) st)
    (fun r s ⟨h1, h2, h3, h4⟩ =>
      ⟨h1, h2, h3, le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ r)) _) h4⟩)
    (fun r req s ⟨h1, h2, h3, h4⟩ => by
      have hmul : (r + 1) * (depth n - 1) = r * (depth n - 1) + (depth n - 1) :=
        Nat.succ_mul r (depth n - 1)
      obtain ⟨heq, hsupp⟩ :=
        jointKeysHandler_expandKeys S depth sigCap n K req s ⟨h1, h2, h3, by omega⟩
      exact ⟨heq, fun ans ⟨uk', ps'⟩ hm => by
        obtain ⟨hl, hp, hv, hg⟩ := hsupp ans uk' ps' hm
        exact ⟨hl, hp, hv, by dsimp only at hg ⊢; omega⟩⟩)
    hq hinv).1

private theorem eval_lazyTreeGame_eq_presampled (S : IndexedSignatureScheme)
    (depth slotBound sigCap : ℕ → ℕ) {n Q : ℕ} (hdepth_pos : 1 ≤ depth n)
    (hslot : Q * depth n ≤ slotBound n)
    (hsigCap : ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
      (msg.length = n ∨ ∃ keys' ∈ (ProbComp.eval (S.keyGen n)).support, msg = keys'.1) →
      ∀ σ ∈ (ProbComp.eval (S.sign keys.2 u msg)).support, σ.length ≤ sigCap n)
    (adversary : Forger)
    (hq : ∀ root ∈ (ProbComp.eval (S.keyGen n)).support,
      (adversary n (encPair encUnary encBits (n, root.1))).IsQueryBounded Q) :
    ProbComp.eval (lazyTreeGame S depth adversary n) =
      (presampledExp S depth slotBound sigCap adversary n).map
        (treeWinOfPresampled S depth n) := by
  set K := dyadicSize (slotBound n) with hK_def
  have hK2 : 2 ≤ K := two_le_dyadicSize (slotBound n)
  have hslotLt : 1 + Q * (depth n - 1) < K := slot_bound_lt_dyadicSize hdepth_pos hslot
  -- Step 1: rewrite lazyTreeGame using jointKeysHandler
  have hstep1 : ProbComp.eval (lazyTreeGame S depth adversary n) =
      (ProbComp.eval (S.keyGen n)).bind fun root =>
        let pk := encPair encUnary encBits (n, root.1)
        let initJ : JointKeysState := ([root], initPresampledState)
        (((OracleComp.interpret
          (OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifOracle j))
            (jointKeysHandler S depth (sigCap n) n))
          (adversary n pk)).run initJ).bind fun (res, (uk', ps')) =>
            (expandKeys S n K uk').map fun keys => (keys, res, ps')).map
          (treeWinOfPresampled S depth n) := by
    simp only [lazyTreeGame, ProbComp.eval_bind, ProbComp.eval_pure,
      ProbOracleComp.eval_run_interpret]
    refine PMF.bind_congr_on_support _ _ _ fun root hroot => ?_
    set pk := encPair encUnary encBits (n, root.1)
    set initJ : JointKeysState := ([root], initPresampledState)
    have hjInv : jointKeysInv S n root initJ := by
      refine ⟨rfl, rfl, rfl, ?_, ?_⟩
      · intro k hk
        obtain rfl := List.mem_singleton.mp hk
        exact hroot
      · intro e he
        obtain rfl := List.mem_singleton.mp he
        simp
    have hproj := ProbOracleComp.run_interpret_map_state_of_invariant
      (jointKeysHandler S depth (sigCap n) n)
      (fun q s => ProbComp.eval (lazySignHandler S depth n root q s))
      lazyStateOfJoint
      (jointKeysInv S n root)
      (fun q s hs a s' hm => (jointKeysHandler_lazy_step S depth hsigCap q s hs).2 a s' hm)
      (fun q s hs => (jointKeysHandler_lazy_step S depth hsigCap q s hs).1)
      (adversary n pk) initJ hjInv
    have hinitEq : lazyStateOfJoint initJ = (([([], root)], []), ([], [], false)) := rfl
    rw [hinitEq] at hproj
    rw [← hproj]
    simp only [PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def]
    refine PMF.bind_congr_on_support _ _ _ fun ⟨msig, st'⟩ hm_run => ?_
    have hjInv' : jointKeysInv S n root st' :=
      ProbOracleComp.run_interpret_invariant (jointKeysHandler S depth (sigCap n) n)
        (jointKeysInv S n root)
        (fun q s hs a s' hm => (jointKeysHandler_lazy_step S depth hsigCap q s hs).2 a s' hm)
        (adversary n pk) initJ hjInv msig st' hm_run
    obtain ⟨uk', ps'⟩ := st'
    obtain ⟨hlen', hrv', hrk', -, hvis'⟩ := hjInv'
    have hpos' : 0 < uk'.length := by
      have := hvis' ([], 0) (lookup_mem hrv')
      omega
    have hexp : ((expandKeys S n K uk').map fun keys =>
        treeWinOfPresampled S depth n (keys, msig, ps')) =
        PMF.pure ((msig.1.length == n) && !ps'.1.2.1.contains msig.1 &&
          verify S depth pk msig.1 msig.2) := by
      have hconst : ∀ keys ∈ (expandKeys S n K uk').support,
          treeWinOfPresampled S depth n (keys, msig, ps') =
            ((msig.1.length == n) && !ps'.1.2.1.contains msig.1 &&
              verify S depth pk msig.1 msig.2) := by
        intro keys hkeys
        obtain ⟨rem, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hkeys
        have h0 : (uk' ++ rem).getD 0 ([], []) = root := by
          rw [List.getD_append _ _ _ _ hpos']
          exact hrk'
        simp only [treeWinOfPresampled, h0, pk]
      rw [← PMF.map_const (expandKeys S n K uk')]
      exact PMF.map_congr_on_support _ _ _ hconst
    exact hexp.symm
  -- Step 2: apply expand_jointKeys_run_interpret and combine root :: remKeys = replicate K
  rw [hstep1]
  have hrep : ProbComp.eval (OracleComp.replicate K (S.keyGen n)) =
      (ProbComp.eval (S.keyGen n)).bind fun root => expandKeys S n K [root] := by
    have hKeq : K = (K - 1) + 1 := by omega
    conv_lhs => rw [hKeq, OracleComp.replicate_succ]
    simp only [expandKeys, ProbComp.eval_bind, ProbComp.eval_map, List.length_singleton,
      List.singleton_append]
  simp only [presampledExp, PMF.monad_bind_eq_bind, ← hK_def, PMF.map_bind]
  rw [hrep, PMF.bind_bind]
  refine PMF.bind_congr_on_support _ _ _ fun root hroot => ?_
  set pk := encPair encUnary encBits (n, root.1)
  set initJ : JointKeysState := ([root], initPresampledState)
  have hexpInv : jointExpandInv K (Q * (depth n - 1)) initJ := by
    refine ⟨rfl, by simp [initJ], ?_, ?_⟩
    · intro e he
      obtain rfl := List.mem_singleton.mp he
      exact Nat.zero_lt_one
    · dsimp only [initJ, initPresampledState, initPlantedState]
      simp only [List.length_singleton]
      exact hslotLt.le
  have hexpRun := expand_jointKeys_run_interpret S depth (sigCap n) n K (hq root hroot) hexpInv
  have hexpWin := congrArg (PMF.map (treeWinOfPresampled S depth n)) hexpRun
  simp only [initJ, PMF.map_bind, PMF.map_comp, Function.comp_def] at hexpWin ⊢
  rw [hexpWin]
  refine PMF.bind_congr_on_support _ _ _ fun keys hkeys => ?_
  obtain ⟨rem, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hkeys
  rfl

/-! #### Query-bounded invariant on `presampledExp` and forgery extraction -/

private def presampledBoundedInv (d : ℕ) (keys : List (List Bool × List Bool)) (rem : ℕ)
    (st : PresampledState) : Prop :=
  let (((visited, _), (queried, _, _)), allSigned) := st
  ([], 0) ∈ visited ∧
  visited.length + rem * (d - 1) ≤ keys.length ∧
  (∀ e ∈ visited, e.1.length < d ∧ e.2 < visited.length) ∧
  (∀ e₁ ∈ visited, ∀ e₂ ∈ visited, e₁.2 = e₂.2 → e₁ = e₂) ∧
  ∀ p idx u m, (p, idx, u, m) ∈ allSigned →
    (p, idx) ∈ visited ∧
    ((p.length + 1 < d ∧ ∃ (b : Bool) (childIdx : ℕ),
        b.toNat = u ∧ (p ++ [b], childIdx) ∈ visited ∧ m = (keys.getD childIdx ([], [])).1) ∨
      (p.length + 1 = d ∧ m ∈ queried))

private theorem localCertify_bounded_inv (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    (keys : List (List Bool × List Bool)) (sigCap n : ℕ) (hd : 1 ≤ depth n)
    (leaf : List Bool) {visited : NodeSlotCache} {edges : EdgeSigCache}
    {queried : List (List Bool)} {allSigned : AllSignedLog}
    (hroot : ([], 0) ∈ visited)
    (hbound : visited.length + (depth n - 1) ≤ keys.length)
    (hvis : ∀ e ∈ visited, e.1.length < depth n ∧ e.2 < visited.length)
    (huniq : ∀ e₁ ∈ visited, ∀ e₂ ∈ visited, e₁.2 = e₂.2 → e₁ = e₂)
    (hall : ∀ p idx u m, (p, idx, u, m) ∈ allSigned →
      (p, idx) ∈ visited ∧
      ((p.length + 1 < depth n ∧ ∃ (b : Bool) (childIdx : ℕ),
          b.toNat = u ∧ (p ++ [b], childIdx) ∈ visited ∧ m = (keys.getD childIdx ([], [])).1) ∨
        (p.length + 1 = depth n ∧ m ∈ queried))) :
    ∀ node idx certs v' e' a',
      ((node, idx, certs), (v', e', a')) ∈
        (localCertify S depth keys sigCap n leaf (visited, edges, allSigned)).support →
      node.length + 1 = depth n ∧
      (node, idx) ∈ v' ∧
      ([], 0) ∈ v' ∧
      v'.length ≤ visited.length + (depth n - 1) ∧
      (∀ e ∈ v', e.1.length < depth n ∧ e.2 < v'.length) ∧
      (∀ e₁ ∈ v', ∀ e₂ ∈ v', e₁.2 = e₂.2 → e₁ = e₂) ∧
      ∀ p idx₀ u m, (p, idx₀, u, m) ∈ a' →
        (p, idx₀) ∈ v' ∧
        ((p.length + 1 < depth n ∧ ∃ (b : Bool) (childIdx : ℕ),
            b.toNat = u ∧ (p ++ [b], childIdx) ∈ v' ∧ m = (keys.getD childIdx ([], [])).1) ∨
          (p.length + 1 = depth n ∧ m ∈ queried)) := by
  dsimp only [localCertify]
  let inv (k : ℕ) (cs : LocalCertState) : Prop :=
    cs.1.1.length = k ∧
    (cs.1.1, cs.1.2.1) ∈ cs.2.1 ∧
    ([], 0) ∈ cs.2.1 ∧
    cs.2.1.length ≤ visited.length + k ∧
    (∀ e ∈ cs.2.1, e.1.length < depth n ∧ e.2 < cs.2.1.length) ∧
    (∀ e₁ ∈ cs.2.1, ∀ e₂ ∈ cs.2.1, e₁.2 = e₂.2 → e₁ = e₂) ∧
    ∀ p idx₀ u m, (p, idx₀, u, m) ∈ cs.2.2.2 →
      (p, idx₀) ∈ cs.2.1 ∧
      ((p.length + 1 < depth n ∧ ∃ (b : Bool) (childIdx : ℕ),
          b.toNat = u ∧ (p ++ [b], childIdx) ∈ cs.2.1 ∧
            m = (keys.getD childIdx ([], [])).1) ∨
        (p.length + 1 = depth n ∧ m ∈ queried))
  have hmain := iterate_pmf_invariant (localCertifyStep S keys sigCap leaf) inv (depth n - 1)
    (([], 0, []), (visited, edges, allSigned))
    ⟨rfl, hroot, hroot, Nat.le_add_right _ _, hvis, huniq, hall⟩
    fun k hk ⟨⟨node, idx, certs⟩, v, e, a⟩
        ⟨hnLen, hnode_v, hroot_v, hgrow_v, hvis_v, huniq_v, hall_v⟩ cs' hm_step => by
      dsimp only at hnLen hnode_v hroot_v hgrow_v hvis_v huniq_v hall_v
      have hvLt : v.length < keys.length := by omega
      have hkLt : k + 1 < depth n := by omega
      set bit := leaf.getD node.length false
      set childPath := node ++ [bit]
      have hcLen : childPath.length = k + 1 := by
        simp only [childPath, List.length_append, List.length_singleton, hnLen]
      simp only [localCertifyStep, PMF.mem_support_map_iff] at hm_step
      obtain ⟨⟨σ, e', a'⟩, hm_se, rfl⟩ := hm_step
      set vp := visitNodePure keys.length childPath v
      have hvp := visitNodePure_inv (P := fun p => p.length < depth n) (K := keys.length)
        childPath (hcLen ▸ hkLt) (fun ent he => ⟨(hvis_v ent he).1, fun _ => (hvis_v ent he).2⟩)
        (fun e₁ he₁ e₂ he₂ _ heq => huniq_v e₁ he₁ e₂ he₂ heq)
      have hltK : ∀ ent ∈ vp.2, ent.2 < keys.length := fun ent he => by
        rcases hvp.2.2.2.2.2 ent he with h | rfl
        · exact (hvis_v ent h).2.trans hvLt
        · exact (Nat.min_le_left _ _).trans_lt hvLt
      refine ⟨hcLen, hvp.1, hvp.2.1 _ hroot_v, hvp.2.2.1.trans (Nat.add_le_add_right hgrow_v 1),
        fun ent he => ⟨(hvp.2.2.2.1 ent he).1, (hvp.2.2.2.1 ent he).2 (hltK ent he)⟩,
        fun e₁ he₁ e₂ he₂ heq => hvp.2.2.2.2.1 e₁ he₁ e₂ he₂ (hltK e₁ he₁) heq, ?_⟩
      intro p idx₀ u m hm_a'
      simp only [localSignEdge] at hm_se
      have liftOld : ∀ (p₀ : List Bool) (idx₁ u₁ : ℕ) (m₁ : List Bool),
          (p₀, idx₁, u₁, m₁) ∈ a →
          (p₀, idx₁) ∈ vp.2 ∧
          ((p₀.length + 1 < depth n ∧ ∃ (b : Bool) (childIdx : ℕ),
              b.toNat = u₁ ∧ (p₀ ++ [b], childIdx) ∈ vp.2 ∧
                m₁ = (keys.getD childIdx ([], [])).1) ∨
            (p₀.length + 1 = depth n ∧ m₁ ∈ queried)) := by
        intro p₀ idx₁ u₁ m₁ hma
        obtain ⟨hpv, hdisj⟩ := hall_v p₀ idx₁ u₁ m₁ hma
        refine ⟨hvp.2.1 _ hpv, ?_⟩
        rcases hdisj with ⟨hpLt, b, cIdx, hbu, hcv, hmeq⟩ | hleafCase
        · exact Or.inl ⟨hpLt, b, cIdx, hbu, hvp.2.1 _ hcv, hmeq⟩
        · exact Or.inr hleafCase
      cases hes : e.lookup (node, bit.toNat) with
      | some σ₀ =>
        rw [hes] at hm_se
        obtain ⟨_, h2⟩ := Prod.mk.inj ((PMF.mem_support_pure_iff _ _).mp hm_se)
        obtain ⟨_, rfl⟩ := Prod.mk.inj h2
        exact liftOld p idx₀ u m hm_a'
      | none =>
        rw [hes] at hm_se
        obtain ⟨raw, -, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hm_se
        obtain ⟨_, h2⟩ := Prod.mk.inj heq.symm
        obtain ⟨_, rfl⟩ := Prod.mk.inj h2
        rcases List.mem_cons.mp hm_a' with hhead | htail
        · obtain ⟨rfl, h2'⟩ := Prod.mk.inj hhead
          obtain ⟨rfl, h3'⟩ := Prod.mk.inj h2'
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj h3'
          exact ⟨hvp.2.1 _ hnode_v,
            Or.inl ⟨hnLen ▸ hkLt, bit, vp.1, rfl, hvp.1, rfl⟩⟩
        · exact liftOld p idx₀ u m htail
  intro node idx certs v' e' a' hm
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hmain _ hm
  exact ⟨by dsimp only at h1; omega, h2, h3, h4, h5, h6, h7⟩

private theorem localTreeHandler_bounded_inv (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    (keys : List (List Bool × List Bool)) (sigCap n : ℕ) (hd : 1 ≤ depth n)
    (req : Unit × List Bool) {rem : ℕ} {st : PresampledState}
    (hinv : presampledBoundedInv (depth n) keys (rem + 1) st) :
    ∀ ans st', (ans, st') ∈ (localTreeHandler S depth keys sigCap n req st).support →
      presampledBoundedInv (depth n) keys rem st' := by
  obtain ⟨⟨⟨visited, edges⟩, queried, seenLeaves, bad⟩, allSigned⟩ := st
  obtain ⟨hroot, hbound, hvis, huniq, hall⟩ := hinv
  have hmul : (rem + 1) * (depth n - 1) = rem * (depth n - 1) + (depth n - 1) :=
    Nat.succ_mul rem (depth n - 1)
  have liftQ {v : NodeSlotCache} {a : List (List Bool × ℕ × ℕ × List Bool)}
      (ha : ∀ p idx u m, (p, idx, u, m) ∈ a →
        (p, idx) ∈ v ∧
        ((p.length + 1 < depth n ∧ ∃ (b : Bool) (childIdx : ℕ),
            b.toNat = u ∧ (p ++ [b], childIdx) ∈ v ∧ m = (keys.getD childIdx ([], [])).1) ∨
          (p.length + 1 = depth n ∧ m ∈ queried)))
      (m' : List Bool) (p : List Bool) (idx u : ℕ) (m : List Bool) (hma : (p, idx, u, m) ∈ a) :
      (p, idx) ∈ v ∧
      ((p.length + 1 < depth n ∧ ∃ (b : Bool) (childIdx : ℕ),
          b.toNat = u ∧ (p ++ [b], childIdx) ∈ v ∧ m = (keys.getD childIdx ([], [])).1) ∨
        (p.length + 1 = depth n ∧ m ∈ m' :: queried)) :=
    let ⟨hpv, hdisj⟩ := ha p idx u m hma
    ⟨hpv, hdisj.imp id fun ⟨hl, hmq⟩ => ⟨hl, List.mem_cons_of_mem _ hmq⟩⟩
  have hpureInv : ∀ b, presampledBoundedInv (depth n) keys rem
      (((visited, edges), (req.2 :: queried, seenLeaves, b)), allSigned) := fun b =>
    ⟨hroot, by omega, hvis, huniq, liftQ hall req.2⟩
  intro ans st' hm
  simp only [localTreeHandler, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure] at hm
  refine treeHandler_support_invariant (req.2.length = n) (bad = true)
    (BitString.uniformList (depth n)) (fun leaf => seenLeaves.contains leaf)
    ([], (((visited, edges), (req.2 :: queried, seenLeaves, bad)), allSigned))
    ([], (((visited, edges), (req.2 :: queried, seenLeaves, true)), allSigned))
    ([], (((visited, edges), (req.2 :: queried, seenLeaves, true)), allSigned))
    (fun leaf => (localCertify S depth keys sigCap n leaf (visited, edges, allSigned)).bind
      fun ((node, idx, certs), (visited', edges', allSigned')) =>
        (localSignEdge S keys sigCap node idx (leaf.getLastD false).toNat req.2
          (edges', allSigned')).map fun (σ, (edges'', allSigned'')) =>
            (encodeSignature leaf certs σ,
              (((visited', edges''), (req.2 :: queried, leaf :: seenLeaves, false)), allSigned'')))
    (fun x => presampledBoundedInv (depth n) keys rem x.2)
    (hpureInv bad) (hpureInv true) (hpureInv true)
    (fun _ _ leaf _ _ x hm_in => by
      obtain ⟨⟨⟨node, idx, certs⟩, v', e', a'⟩, hm_cert, hm_se⟩ :=
        (PMF.mem_support_bind_iff _ _ _).mp hm_in
      obtain ⟨⟨σ, e'', a''⟩, hm_edge, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hm_se
      obtain ⟨hnLen, hnode_v', hroot_v', hgrow_v', hvis_v', huniq_v', hall_v'⟩ :=
        localCertify_bounded_inv S depth keys sigCap n hd leaf hroot (by omega) hvis huniq hall
          node idx certs v' e' a' hm_cert
      refine ⟨hroot_v', by omega, hvis_v', huniq_v', ?_⟩
      intro p idx₀ u m hm_a''
      simp only [localSignEdge] at hm_edge
      cases hes : e'.lookup (node, (leaf.getLastD false).toNat) with
      | some σ₀ =>
        rw [hes] at hm_edge
        obtain ⟨_, h2⟩ := Prod.mk.inj ((PMF.mem_support_pure_iff _ _).mp hm_edge)
        obtain ⟨_, rfl⟩ := Prod.mk.inj h2
        exact liftQ hall_v' req.2 p idx₀ u m hm_a''
      | none =>
        rw [hes] at hm_edge
        obtain ⟨raw, -, heq'⟩ := (PMF.mem_support_map_iff _ _ _).mp hm_edge
        obtain ⟨_, h2⟩ := Prod.mk.inj heq'.symm
        obtain ⟨_, rfl⟩ := Prod.mk.inj h2
        rcases List.mem_cons.mp hm_a'' with hhead | htail
        · obtain ⟨rfl, h2'⟩ := Prod.mk.inj hhead
          obtain ⟨rfl, h3'⟩ := Prod.mk.inj h2'
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj h3'
          exact ⟨hnode_v', Or.inr ⟨hnLen, List.mem_cons_self⟩⟩
        · exact liftQ hall_v' req.2 p idx₀ u m htail)
    (ans, st') hm

private theorem run_interpret_localTreeHandler_bounded_inv {α : Type}
    (S : IndexedSignatureScheme) (depth : ℕ → ℕ) (keys : List (List Bool × List Bool))
    (sigCap n : ℕ) (hd : 1 ≤ depth n) {prog : WordOracleComp Unit α} {rem : ℕ}
    (hq : prog.IsQueryBounded rem) {st : PresampledState}
    (hinv : presampledBoundedInv (depth n) keys rem st) :
    ∀ res st', (res, st') ∈
      ((OracleComp.interpret
        (OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifOracle j))
          (localTreeHandler S depth keys sigCap n))
        prog).run st).support →
      presampledBoundedInv (depth n) keys 0 st' :=
  run_interpret_queryBounded_invariant (localTreeHandler S depth keys sigCap n)
    (presampledBoundedInv (depth n) keys)
    (fun r _ ⟨h1, h2, h3, h4, h5⟩ =>
      ⟨h1, le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ r)) _) h2,
        h3, h4, h5⟩)
    (fun _ req _ hs ans st' hm => localTreeHandler_bounded_inv S depth keys sigCap n hd req hs
      ans st' hm)
    hq hinv

private def chainPk (pk₀ : List Bool) (certs : List (List Bool × List Bool)) (j : ℕ) :
    List Bool :=
  if j = 0 then pk₀ else (certs.getD (j - 1) ([], [])).1

private theorem foldl_verifyStep_spec (S : IndexedSignatureScheme) (pk₀ : List Bool)
    (bits : List Bool) (certs : List (List Bool × List Bool)) (hlen : bits.length = certs.length) :
    ((bits.zip certs).foldl (verifyStep S) (true, pk₀)).2 = chainPk pk₀ certs bits.length ∧
    (((bits.zip certs).foldl (verifyStep S) (true, pk₀)).1 = true ↔
      ∀ j < bits.length,
        S.verify (chainPk pk₀ certs j) (bits.getD j false).toNat
          (certs.getD j ([], [])).1 (certs.getD j ([], [])).2 = true) := by
  suffices ∀ m ≤ bits.length,
      (((bits.take m).zip (certs.take m)).foldl (verifyStep S) (true, pk₀)).2 =
        chainPk pk₀ certs m ∧
      ((((bits.take m).zip (certs.take m)).foldl (verifyStep S) (true, pk₀)).1 = true ↔
        ∀ j < m,
          S.verify (chainPk pk₀ certs j) (bits.getD j false).toNat
            (certs.getD j ([], [])).1 (certs.getD j ([], [])).2 = true) by
    have h := this bits.length le_rfl
    rwa [List.take_length, hlen, List.take_length, ← hlen] at h
  intro m
  induction m with
  | zero =>
    intro _
    simp [chainPk]
  | succ m ih =>
    intro hm
    have hm_b : m < bits.length := hm
    have hm_c : m < certs.length := hlen ▸ hm
    obtain ⟨ih_pk, ih_ok⟩ := ih (by omega)
    have hlen_t : (bits.take m).length = (certs.take m).length := by
      simp only [List.length_take, hlen]
    rw [List.take_succ_eq_append_getElem hm_b, List.take_succ_eq_append_getElem hm_c,
      List.zip_append hlen_t, List.zip_cons_cons, List.zip_nil_right, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    simp only [verifyStep, ih_pk, Bool.and_eq_true, ih_ok]
    have hbg : bits[m] = bits.getD m false := (List.getD_eq_getElem bits false hm_b).symm
    have hcg : certs[m] = certs.getD m ([], []) :=
      (List.getD_eq_getElem certs ([], []) hm_c).symm
    rw [hbg, hcg]
    refine ⟨by simp only [chainPk, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
        Nat.add_sub_cancel], ?_⟩
    constructor
    · rintro ⟨hall, hlast⟩ j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
      · exact hall j hj'
      · exact hlast
    · intro hall
      exact ⟨fun j hj => hall j (Nat.lt_succ_of_lt hj), hall m (Nat.lt_succ_self m)⟩

private theorem win_implies_any_plantedWin (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    {n K : ℕ} (hd : 1 ≤ depth n)
    {out : List (List Bool × List Bool) × (List Bool × List Bool) × PresampledState}
    (hkeysLen : out.1.length = K)
    (hinv : presampledBoundedInv (depth n) out.1 0 out.2.2)
    (hwin : treeWinOfPresampled S depth n out = true) :
    ((List.range K).any fun j => plantedWin S depth n j out) = true := by
  classical
  obtain ⟨keys, ⟨msgStar, sigStar⟩, ⟨⟨visited, edges⟩, queried, seenLeaves, bad⟩, allSigned⟩ := out
  dsimp only at hkeysLen
  obtain ⟨hroot, hbound, hvis, huniq, hall⟩ := hinv
  simp only [Nat.zero_mul, Nat.add_zero] at hbound
  simp only [treeWinOfPresampled, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff,
    ne_eq, List.contains_iff_mem, beq_iff_eq] at hwin
  obtain ⟨⟨_, hfresh⟩, hver⟩ := hwin
  set pk₀ := (keys.getD 0 ([], [])).1
  simp only [verify, keyDecoder.decode_enc] at hver
  set dec := signatureDecoder.decode sigStar
  set leaf := dec.1
  set certs := dec.2.1
  set last := dec.2.2
  change ((leaf.length == depth n) && (certs.length + 1 == depth n) &&
    ((leaf.dropLast.zip certs).foldl (verifyStep S) (true, pk₀)).1 &&
    S.verify ((leaf.dropLast.zip certs).foldl (verifyStep S) (true, pk₀)).2
      (leaf.getLastD false).toNat msgStar last) = true at hver
  simp only [Bool.and_eq_true, beq_iff_eq] at hver
  obtain ⟨⟨⟨hleafLen, hcertsLen⟩, hchainOk⟩, hlastOk⟩ := hver
  have hdropLen : leaf.dropLast.length = certs.length := by
    rw [List.length_dropLast, hleafLen]
    omega
  obtain ⟨hchainPk, hchainAll⟩ := foldl_verifyStep_spec S pk₀ leaf.dropLast certs hdropLen
  have hcertsVer : ∀ j < depth n - 1,
      S.verify (chainPk pk₀ certs j) (leaf.getD j false).toNat
        (certs.getD j ([], [])).1 (certs.getD j ([], [])).2 = true := by
    intro j hj
    have hjDrop : j < leaf.dropLast.length := by
      rw [List.length_dropLast, hleafLen]
      exact hj
    have hvj := hchainAll.mp hchainOk j hjDrop
    have hbitEq : leaf.dropLast.getD j false = leaf.getD j false := by
      rw [List.dropLast_eq_take, hleafLen,
        List.getD_eq_getElem _ _ (by simp only [List.length_take]; omega),
        List.getElem_take, List.getD_eq_getElem _ _ (by omega)]
    rwa [hbitEq] at hvj
  have hlastPkEq : ((leaf.dropLast.zip certs).foldl (verifyStep S) (true, pk₀)).2 =
      chainPk pk₀ certs (depth n - 1) := by
    rw [hchainPk, List.length_dropLast, hleafLen]
  have hlastBitEq : leaf.getLastD false = leaf.getD (depth n - 1) false := by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, hleafLen,
      List.getD_eq_getElem?_getD]
  rw [hlastPkEq, hlastBitEq] at hlastOk
  let P (j : ℕ) : Prop :=
    ∃ idx, (leaf.take j, idx) ∈ visited ∧ (keys.getD idx ([], [])).1 = chainPk pk₀ certs j
  have hP0 : P 0 := ⟨0, hroot, rfl⟩
  set jStar := Nat.findGreatest P (depth n - 1)
  have hjLe : jStar ≤ depth n - 1 := Nat.findGreatest_le (depth n - 1)
  obtain ⟨target, hmemT, hpkT⟩ : P jStar := Nat.findGreatest_spec (Nat.zero_le _) hP0
  have htargetVis : target < visited.length := (hvis _ hmemT).2
  have htargetK : target < K := by omega
  have hpathEq : ((visited.filter fun e => e.2 == target).headD ([], 0)).1 = leaf.take jStar :=
    filter_headD_of_mem_unique visited hmemT huniq
  have hpathLen : (leaf.take jStar).length = jStar := by
    rw [List.length_take, hleafLen]
    exact Nat.min_eq_left (by omega)
  rw [List.any_eq_true]
  refine ⟨target, List.mem_range.mpr htargetK, ?_⟩
  simp only [plantedWin, extractForgery, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff,
    ne_eq, List.contains_iff_mem, hpathEq, hpathLen]
  change (let cand : ℕ × List Bool × List Bool :=
      if jStar + 1 < depth n then
        ((leaf.getD jStar false).toNat,
          (certs.getD jStar ([], [])).1, (certs.getD jStar ([], [])).2)
      else
        ((leaf.getD jStar false).toNat, msgStar, last)
    (cand.1, cand.2.1) ∉ signedLogOf target allSigned ∧
      S.verify (keys.getD target ([], [])).1 cand.1 cand.2.1 cand.2.2 = true)
  have hlogMem : ∀ {u₀ m₀}, (u₀, m₀) ∈ signedLogOf target allSigned →
      ((leaf.take jStar).length + 1 < depth n ∧
        ∃ (b : Bool) (childIdx : ℕ), b.toNat = u₀ ∧
          (leaf.take jStar ++ [b], childIdx) ∈ visited ∧
          m₀ = (keys.getD childIdx ([], [])).1) ∨
      ((leaf.take jStar).length + 1 = depth n ∧ m₀ ∈ queried) := by
    intro u₀ m₀ hmemLog
    simp only [signedLogOf, List.mem_map, List.mem_filter, beq_iff_eq] at hmemLog
    obtain ⟨⟨p, idx, u', m'⟩, ⟨hm_all, hidxEq⟩, heqPair⟩ := hmemLog
    obtain ⟨huEq, hmEq⟩ := Prod.mk.inj heqPair
    dsimp only at hidxEq huEq hmEq
    rw [hidxEq, huEq, hmEq] at hm_all
    obtain ⟨hp_vis, hdisj⟩ := hall p target u₀ m₀ hm_all
    obtain ⟨rfl, -⟩ := Prod.mk.inj (huniq _ hp_vis _ hmemT rfl)
    exact hdisj
  by_cases hjLt : jStar + 1 < depth n
  · simp only [hjLt, ↓reduceIte]
    refine ⟨?_, ?_⟩
    · intro hmemLog
      rcases hlogMem hmemLog with ⟨_, b, childIdx, hbu, hcVis, hcmEq⟩ | ⟨hbadLen, _⟩
      · have hbeq : b = leaf.getD jStar false :=
          Bool.eq_iff_iff.mpr (by
            rw [← b.toNat_eq_one, ← (leaf.getD jStar false).toNat_eq_one, hbu])
        subst hbeq
        have hjLeaf : jStar < leaf.length := by omega
        have htakeSucc : leaf.take jStar ++ [leaf.getD jStar false] = leaf.take (jStar + 1) := by
          rw [List.getD_eq_getElem _ _ hjLeaf, ← List.take_succ_eq_append_getElem hjLeaf]
        rw [htakeSucc] at hcVis
        have hPsucc : P (jStar + 1) := by
          refine ⟨childIdx, hcVis, ?_⟩
          simp only [chainPk, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
            Nat.add_sub_cancel]
          exact hcmEq.symm
        exact Nat.findGreatest_is_greatest (lt_add_one jStar) (by omega) hPsucc
      · rw [hpathLen] at hbadLen
        omega
    · rw [hpkT]
      exact hcertsVer jStar (by omega)
  · simp only [hjLt, ↓reduceIte]
    have hjEq : jStar = depth n - 1 := by omega
    refine ⟨?_, ?_⟩
    · intro hmemLog
      rcases hlogMem hmemLog with ⟨hbadLt, _⟩ | ⟨_, hmq⟩
      · rw [hpathLen, hjEq] at hbadLt
        omega
      · exact hfresh hmq
    · rw [hpkT, hjEq]
      exact hlastOk

private theorem eval_indexedEufCmaGame_indexedForger (S : IndexedSignatureScheme)
    (depth slotBound sigCap : ℕ → ℕ) (adversary : Forger) (n : ℕ) :
    ProbComp.eval (S.indexedEufCmaGame (indexedForger S depth slotBound sigCap adversary) n) =
      (PMF.uniformOfFintype (Fin (dyadicSize (slotBound n)))).bind fun target =>
        ProbComp.eval
          (S.indexedEufCmaGame (indexedForgerAt S depth slotBound sigCap adversary target.val)
            n) := by
  simp only [IndexedSignatureScheme.indexedEufCmaGame, indexedForger, ProbComp.eval_bind,
    ProbComp.eval_pure, ProbOracleComp.eval_run_interpret, OracleComp.interpret_bind,
    StateT.run_bind, ProbOracleComp.run_interpret_sample, ProbComp.eval_sampleDyadicIndex,
    PMF.bind_map, PMF.bind_bind, Function.comp_def]
  rw [PMF.bind_comm]

/-- **From lazy tree signing to indexed forgery**: when `Q * depth n ≤ slotBound n` and `sigCap n`
bounds all supported edge signature lengths, the forging probability in `lazyTreeGame` is at most
`dyadicSize (slotBound n)` times `indexedForger`'s forging probability against `S`. -/
theorem succProbability_lazyTreeGame_le (S : IndexedSignatureScheme)
    (depth slotBound sigCap : ℕ → ℕ) {n Q : ℕ}
    (hcap : 2 ≤ S.capacity n) (hdepth_pos : 1 ≤ depth n)
    (hslot : Q * depth n ≤ slotBound n)
    (hsigCap : ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
      (msg.length = n ∨ ∃ keys' ∈ (ProbComp.eval (S.keyGen n)).support, msg = keys'.1) →
      ∀ σ ∈ (ProbComp.eval (S.sign keys.2 u msg)).support, σ.length ≤ sigCap n)
    (adversary : Forger)
    (hq : ∀ root ∈ (ProbComp.eval (S.keyGen n)).support,
      (adversary n (encPair encUnary encBits (n, root.1))).IsQueryBounded Q) :
    Game.succProbability (ProbComp.eval (lazyTreeGame S depth adversary n)) ≤
      dyadicSize (slotBound n) * Game.succProbability
        (ProbComp.eval
          (S.indexedEufCmaGame (indexedForger S depth slotBound sigCap adversary) n)) := by
  set K := dyadicSize (slotBound n)
  set X := presampledExp S depth slotBound sigCap adversary n
  have hslotLt : 1 + Q * (depth n - 1) < K := slot_bound_lt_dyadicSize hdepth_pos hslot
  have hsupp : ∀ out ∈ X.support,
      out.1.length = K ∧ presampledBoundedInv (depth n) out.1 0 out.2.2 := by
    intro out hout
    simp only [X, presampledExp, PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff,
      PMF.mem_support_map_iff] at hout
    obtain ⟨keys, hkeys, ⟨msig, st⟩, hrun, rfl⟩ := hout
    obtain ⟨hkLen, hkSupp⟩ := (ProbComp.mem_support_replicate_iff _ _ _).mp hkeys
    have hpos : 0 < keys.length := by
      have := two_le_dyadicSize (slotBound n)
      omega
    have hk0Mem := hkSupp _ (List.getD_mem ([], []) hpos)
    have hinit : presampledBoundedInv (depth n) keys Q initPresampledState := by
      refine ⟨List.mem_singleton.mpr rfl, ?_, ?_, ?_, fun _ _ _ _ h => by cases h⟩
      · simp only [List.length_singleton, hkLen]
        exact hslotLt.le
      · intro e he
        obtain rfl := List.mem_singleton.mp he
        exact ⟨by simp; omega, by simp⟩
      · intro e₁ he₁ e₂ he₂ _
        rw [List.mem_singleton.mp he₁, List.mem_singleton.mp he₂]
    exact ⟨hkLen, run_interpret_localTreeHandler_bounded_inv S depth keys (sigCap n) n
      hdepth_pos (hq _ hk0Mem) hinit msig st hrun⟩
  have hsum : ProbComp.eval (lazyTreeGame S depth adversary n) true ≤
      ∑ i ∈ Finset.range K,
        ProbComp.eval
          (S.indexedEufCmaGame (indexedForgerAt S depth slotBound sigCap adversary i) n) true := by
    rw [eval_lazyTreeGame_eq_presampled S depth slotBound sigCap hdepth_pos hslot hsigCap
      adversary hq]
    refine (PMF.map_true_mono X
      (F := fun out => (List.range K).any fun j => plantedWin S depth n j out) ?_).trans
      ((PMF.map_any_range_true_le_sum X K (plantedWin S depth n)).trans ?_)
    · intro out hout hwin
      obtain ⟨hkLen, hinv⟩ := hsupp out hout
      exact win_implies_any_plantedWin S depth hdepth_pos hkLen hinv hwin
    · refine Finset.sum_le_sum fun i hi => ?_
      rw [map_plantedWin_presampledExp S depth slotBound sigCap hcap adversary
        (Finset.mem_range.mp hi)]
  have havg : ((K : ℕ) : ℝ≥0∞) *
        ProbComp.eval
          (S.indexedEufCmaGame (indexedForger S depth slotBound sigCap adversary) n) true =
      ∑ i ∈ Finset.range K,
        ProbComp.eval
          (S.indexedEufCmaGame (indexedForgerAt S depth slotBound sigCap adversary i) n) true := by
    rw [eval_indexedEufCmaGame_indexedForger, PMF.bind_apply, tsum_fintype]
    simp only [PMF.uniformOfFintype_apply, Fintype.card_fin]
    rw [← Finset.mul_sum, ← mul_assoc,
      ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr (dyadicSize_pos (slotBound n)).ne') (by simp),
      one_mul,
      ← Fin.sum_univ_eq_sum_range (fun i => ProbComp.eval
        (S.indexedEufCmaGame (indexedForgerAt S depth slotBound sigCap adversary i) n) true)]
  rw [← havg] at hsum
  have hfin : ((K : ℕ) : ℝ≥0∞) *
      ProbComp.eval
        (S.indexedEufCmaGame (indexedForger S depth slotBound sigCap adversary) n) true ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (PMF.apply_ne_top _ _)
  have h := ENNReal.toNNReal_mono hfin hsum
  rw [ENNReal.toNNReal_mul, ENNReal.toNNReal_natCast] at h
  simpa only [Game.succProbability, K] using h

end LazyToIndexed

/-! ### Concrete and asymptotic EUF-CMA security of `TreeSignature.scheme` -/

section AsymptoticSecurity

/-- **Concrete security of `treeIdealGame`** ([BonehShoup2023], Section 14.6.3, Theorem 14.6):
combining the lazy-coin leaf-collision hybrid and the planted-node indexed-forgery reduction. -/
theorem succProbability_treeIdealGame_le (S : IndexedSignatureScheme) (T : S.Seeded)
    (depth N slotBound sigCap : ℕ → ℕ) {n Q : ℕ}
    (hcap : 2 ≤ S.capacity n) (hdepth_pos : 1 ≤ depth n)
    (hwidth : 2 * depth n + 4 ≤ N n) (hkgBudget : T.keyGenBudget n ≤ N n)
    (hsgBudget : ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
      (msg.length = n ∨ ∃ keys' ∈ (ProbComp.eval (S.keyGen n)).support, msg = keys'.1) →
      T.signBudget keys.2 u msg ≤ N n)
    (hslot : Q * depth n ≤ slotBound n)
    (hsigCap : ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
      (msg.length = n ∨ ∃ keys' ∈ (ProbComp.eval (S.keyGen n)).support, msg = keys'.1) →
      ∀ σ ∈ (ProbComp.eval (S.sign keys.2 u msg)).support, σ.length ≤ sigCap n)
    (adversary : Forger)
    (hq : ∀ root ∈ (ProbComp.eval (S.keyGen n)).support,
      (adversary n (encPair encUnary encBits (n, root.1))).IsQueryBounded Q) :
    Game.succProbability (ProbComp.eval (treeIdealGame S T depth N adversary n)) ≤
      dyadicSize (slotBound n) * Game.succProbability
        (ProbComp.eval
          (S.indexedEufCmaGame (indexedForger S depth slotBound sigCap adversary) n)) +
        (Q ^ 2 : ℝ≥0) / 2 ^ (depth n + 1) :=
  (succProbability_treeIdealGame_le_lazy S T depth N hdepth_pos hwidth hkgBudget hsgBudget
    adversary hq).trans
    (add_le_add
      (succProbability_lazyTreeGame_le S depth slotBound sigCap hcap hdepth_pos hslot hsigCap
        adversary hq) le_rfl)

/-- **Theorem 14.6 concrete security bound for `TreeSignature.scheme`**
([BonehShoup2023], Section 14.6.3, Theorem 14.6): the forging probability of any `Q`-query forger
against `TreeSignature.scheme` with `prfCoins family` is bounded by the PRF distinguishing
advantage of `coinDistinguisher (treeCoinAdversary …)` at `N n`, plus `dyadicSize (slotBound n)`
times `indexedForger`'s indexed forging probability against `S`, plus
`(Q ^ 2 : ℝ≥0) / 2 ^ (depth n + 1)`. -/
theorem succProbability_eufCmaGame_scheme_le (S : IndexedSignatureScheme) (T : S.Seeded)
    (family : List Bool → List Bool → List Bool)
    (depth N inv slotBound sigCap : ℕ → ℕ)
    (hcoins : ComputableInPolyTime
      (fun ((k, input, length) : List Bool × List Bool × ℕ) => prfCoins family k input length)
      (encPair encBits (encPair encBits encUnary)) encBits)
    (hN : ComputableInPolyTime N encUnary encUnary)
    (hdepth : ComputableInPolyTime depth encUnary encUnary)
    (hcap : ∀ n, 2 ≤ S.capacity n) (hdepth_pos : ∀ n, 1 ≤ depth n)
    (hinv : ∀ n, inv (N n) = n)
    {n Q : ℕ} (hwidth : 2 * depth n + 4 ≤ N n) (hkgBudget : T.keyGenBudget n ≤ N n)
    (hsgBudget : ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
      (msg.length = n ∨ ∃ keys' ∈ (ProbComp.eval (S.keyGen n)).support, msg = keys'.1) →
      T.signBudget keys.2 u msg ≤ N n)
    (hslot : Q * depth n ≤ slotBound n)
    (hsigCap : ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
      (msg.length = n ∨ ∃ keys' ∈ (ProbComp.eval (S.keyGen n)).support, msg = keys'.1) →
      ∀ σ ∈ (ProbComp.eval (S.sign keys.2 u msg)).support, σ.length ≤ sigCap n)
    (adversary : Forger)
    (hq : ∀ root ∈ (ProbComp.eval (S.keyGen n)).support,
      (adversary n (encPair encUnary encBits (n, root.1))).IsQueryBounded Q) :
    Game.succProbability (ProbComp.eval
        ((scheme S T (prfCoins family) N depth hcoins hN hdepth hcap hdepth_pos).eufCmaGame
          adversary n)) ≤
      Game.advantage
        (ProbComp.eval (prfRealGame family
          (coinDistinguisher (treeCoinAdversary S T depth N inv adversary)) (N n)))
        (ProbComp.eval (prfIdealGame
          (coinDistinguisher (treeCoinAdversary S T depth N inv adversary)) (N n))) +
      dyadicSize (slotBound n) * Game.succProbability
        (ProbComp.eval
          (S.indexedEufCmaGame (indexedForger S depth slotBound sigCap adversary) n)) +
      (Q ^ 2 : ℝ≥0) / 2 ^ (depth n + 1) := by
  rw [eufCmaGame_scheme]
  have hprf := succProbability_treeGame_le_prf (S := S) (T := T) (depth := depth) (N := N)
    family hinv adversary n
  have hideal := succProbability_treeIdealGame_le S T depth N slotBound sigCap (hcap n)
    (hdepth_pos n) hwidth hkgBudget hsgBudget hslot hsigCap adversary hq
  calc Game.succProbability (ProbComp.eval (treeGame S T depth N (prfCoins family) adversary n))
      ≤ Game.succProbability (ProbComp.eval (treeIdealGame S T depth N adversary n)) + _ := hprf
    _ ≤ (_ + _) + _ := add_le_add hideal le_rfl
    _ = _ := by ring

private theorem exists_sigCap_polyTime (S : IndexedSignatureScheme) :
    ∃ sigCap : ℕ → ℕ,
      ComputableInPolyTime sigCap encUnary encUnary ∧
      ∀ n, ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
        (msg.length = n ∨ ∃ keys' ∈ (ProbComp.eval (S.keyGen n)).support, msg = keys'.1) →
        ∀ σ ∈ (ProbComp.eval (S.sign keys.2 u msg)).support, σ.length ≤ sigCap n := by
  obtain ⟨pkB, hpkB, hlenB⟩ := exists_signInput_length_bound S
  obtain ⟨cs, ds, hsgLen⟩ := S.sign_ppt.length_le
  exact ⟨fun n => cs * (3 * pkB n + n + 5) ^ ds, by fun_prop,
    fun n keys hkeys u hu msg hmsg σ hσ =>
      (hsgLen (keys.2, u, msg) σ hσ).trans
        (Nat.mul_le_mul_left cs (Nat.pow_le_pow_left (hlenB n keys hkeys u hu msg hmsg) ds))⟩

/-- **Stateless EUF-CMA security of `TreeSignature.scheme` with an explicit left inverse**
([BonehShoup2023], Section 14.6.3, Theorem 14.6): if `S` is indexed EUF-CMA secure with capacity
at least `2`, `family` is a pseudorandom function, `N` covers all tree coin requests and has a
polynomial-time left inverse `inv`, and `(1 : ℝ≥0) / 2 ^ depth n` is negligible, then
`TreeSignature.scheme` is stateless EUF-CMA secure. -/
theorem eufCMA_scheme_of_inv (S : IndexedSignatureScheme) (hS : S.IndexedEUFCMA) (T : S.Seeded)
    {family : List Bool → List Bool → List Bool} (hF : PseudorandomFunction family)
    {depth N inv : ℕ → ℕ}
    (hdepth : ComputableInPolyTime depth encUnary encUnary)
    (hN : ComputableInPolyTime N encUnary encUnary)
    (hinvPoly : ComputableInPolyTime inv encUnary encUnary)
    (hcap : ∀ n, 2 ≤ S.capacity n) (hdepth_pos : ∀ n, 1 ≤ depth n)
    (hNge : ∀ n, n ≤ N n) (hinv : ∀ n, inv (N n) = n)
    (hwidth : ∀ n, 2 * depth n + 4 ≤ N n) (hkgBudget : ∀ n, T.keyGenBudget n ≤ N n)
    (hsgBudget : ∀ n, ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
      (msg.length = n ∨ ∃ keys' ∈ (ProbComp.eval (S.keyGen n)).support, msg = keys'.1) →
      T.signBudget keys.2 u msg ≤ N n)
    (hdepthNeg : Negligible (fun n => (1 : ℝ≥0) / 2 ^ depth n)) :
    (scheme S T (prfCoins family) N depth
      (computableInPolyTime_prfCoins hF.polyTime) hN hdepth hcap hdepth_pos).EUFCMA := by
  obtain ⟨sigCap, hsigCapPoly, hsigCap⟩ := exists_sigCap_polyTime S
  obtain ⟨ck, dk, hkgLen⟩ := S.keyGen_ppt.length_le
  simp only [encUnary_apply, List.length_replicate] at hkgLen
  apply SignatureScheme.EUFCMA.of_negligible
  intro adversary hA
  obtain ⟨εPrf, hεPrfNeg, hprfLe⟩ :=
    exists_negligible_treeGame_le S T depth N hF hdepth hN hNge hinvPoly hinv hA
  obtain ⟨cq, dq, hqb⟩ := hA.query_bounds
  let Q (n : ℕ) : ℕ := cq * (3 * n + ck * (n + 1) ^ dk + 3) ^ dq
  have hQPoly : ComputableInPolyTime Q encUnary encUnary := by
    dsimp only [Q]
    fun_prop
  let slotBound (n : ℕ) : ℕ := Q n * depth n
  have hslotPoly : ComputableInPolyTime slotBound encUnary encUnary :=
    hQPoly.unary_mul' hdepth
  have hForgerPPT := isOraclePPT_indexedForger S hdepth hslotPoly hsigCapPoly hA
  have hIdxNeg := hS.negligible (indexedForger S depth slotBound sigCap adversary) hForgerPPT
  have hbound : ∀ n,
      Game.succProbability
        (ProbComp.eval
          ((scheme S T (prfCoins family) N depth (computableInPolyTime_prfCoins hF.polyTime)
            hN hdepth hcap hdepth_pos).eufCmaGame adversary n)) ≤
      (dyadicSize (slotBound n) : ℝ≥0) * Game.succProbability
        (ProbComp.eval
          (S.indexedEufCmaGame (indexedForger S depth slotBound sigCap adversary) n)) +
      (Q n ^ 2 : ℝ≥0) / 2 ^ (depth n + 1) + εPrf n := fun n => by
    rw [eufCmaGame_scheme]
    have hqBound : ∀ root ∈ (ProbComp.eval (S.keyGen n)).support,
        (adversary n (encPair encUnary encBits (n, root.1))).IsQueryBounded (Q n) := by
      intro root hroot
      have hrk : root.1.length ≤ ck * (n + 1) ^ dk := by
        have := (length_le_encPair_left encBits encBits root).trans (hkgLen n root hroot)
        simpa only [encBits_apply] using this
      have hpkLen : (encPair encUnary encBits (n, root.1)).length = 2 * n + 1 + root.1.length := by
        simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply]
      have hleQ : cq * (n + (encPair encUnary encBits (n, root.1)).length + 2) ^ dq ≤ Q n :=
        Nat.mul_le_mul_left cq (Nat.pow_le_pow_left (by omega) dq)
      exact (hqb n _).1.mono hleQ
    have hideal := succProbability_treeIdealGame_le S T depth N slotBound sigCap (hcap n)
      (hdepth_pos n) (hwidth n) (hkgBudget n) (hsgBudget n) le_rfl (hsigCap n) adversary hqBound
    exact (hprfLe n).trans (add_le_add hideal le_rfl)
  negligible using hbound

/-- **Stateless EUF-CMA security of `TreeSignature.scheme` at `coinParam budget`**
([BonehShoup2023], Section 14.6.3, Theorem 14.6): instantiating the PRF parameter at
`coinParam budget` eliminates the separate left-inverse hypothesis. -/
theorem eufCMA_scheme (S : IndexedSignatureScheme) (hS : S.IndexedEUFCMA) (T : S.Seeded)
    {family : List Bool → List Bool → List Bool} (hF : PseudorandomFunction family)
    {depth budget : ℕ → ℕ}
    (hdepth : ComputableInPolyTime depth encUnary encUnary)
    (hbudget : ComputableInPolyTime budget encUnary encUnary)
    (hcap : ∀ n, 2 ≤ S.capacity n) (hdepth_pos : ∀ n, 1 ≤ depth n)
    (hwidth : ∀ n, 2 * depth n + 4 ≤ budget n) (hkgBudget : ∀ n, T.keyGenBudget n ≤ budget n)
    (hsgBudget : ∀ n, ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
      (msg.length = n ∨ ∃ keys' ∈ (ProbComp.eval (S.keyGen n)).support, msg = keys'.1) →
      T.signBudget keys.2 u msg ≤ budget n)
    (hdepthNeg : Negligible (fun n => (1 : ℝ≥0) / 2 ^ depth n)) :
    (scheme S T (prfCoins family) (coinParam budget) depth
      (computableInPolyTime_prfCoins hF.polyTime)
      (computableInPolyTime_coinParam hbudget) hdepth hcap hdepth_pos).EUFCMA :=
  eufCMA_scheme_of_inv S hS T hF hdepth
    (computableInPolyTime_coinParam hbudget)
    (computableInPolyTime_coinParamInv hbudget)
    hcap hdepth_pos (le_coinParam budget) (coinParamInv_coinParam budget)
    (fun n => (hwidth n).trans (lt_coinParam budget n).le)
    (fun n => (hkgBudget n).trans (lt_coinParam budget n).le)
    (fun n keys hk u hu msg hm =>
      (hsgBudget n keys hk u hu msg hm).trans (lt_coinParam budget n).le)
    hdepthNeg

/-- **Stateless many-time signatures from indexed signatures and PRFs**
([BonehShoup2023], Section 14.6.3, Theorem 14.6): any indexed EUF-CMA secure signature scheme of
capacity at least `2` and any pseudorandom function yield a stateless EUF-CMA secure signature
scheme. -/
theorem _root_.Cslib.Crypto.IndexedSignatureScheme.IndexedEUFCMA.exists_eufCMA_of_prf
    {S : IndexedSignatureScheme} (hS : S.IndexedEUFCMA) (hcap : ∀ n, 2 ≤ S.capacity n)
    {family : List Bool → List Bool → List Bool} (hF : PseudorandomFunction family) :
    ∃ M : SignatureScheme, M.EUFCMA := by
  let T := S.seeded
  let depth : ℕ → ℕ := fun n => n + 1
  have hdepth : ComputableInPolyTime depth encUnary encUnary :=
    (ComputableInPolyTime.id' (encIn := encUnary)).unary_add' (.const 1)
  have hdepth_pos : ∀ n, 1 ≤ depth n := fun _ => Nat.le_add_left 1 _
  have hdepthNeg : Negligible (fun n => (1 : ℝ≥0) / 2 ^ depth n) :=
    negligible_inv_two_pow_of_le fun n => Nat.le_succ n
  obtain ⟨budget, hbudget, hwidth, hkgB, hsgB⟩ := exists_treeCoinBudget S T hdepth
  exact ⟨scheme S T (prfCoins family) (coinParam budget) depth
      (computableInPolyTime_prfCoins hF.polyTime)
      (computableInPolyTime_coinParam hbudget) hdepth hcap hdepth_pos,
    eufCMA_scheme S hS T hF hdepth hbudget hcap hdepth_pos hwidth hkgB hsgB hdepthNeg⟩

/-- **Stateless many-time signatures from indexed signatures and one-way functions**: any indexed
EUF-CMA secure signature scheme of capacity at least `2` and any one-way function yield a stateless
EUF-CMA secure signature scheme. -/
theorem _root_.Cslib.Crypto.IndexedSignatureScheme.IndexedEUFCMA.exists_eufCMA_of_oneWay
    {S : IndexedSignatureScheme} (hS : S.IndexedEUFCMA) (hcap : ∀ n, 2 ≤ S.capacity n)
    {f : List Bool → List Bool} (hf : OneWay f) :
    ∃ M : SignatureScheme, M.EUFCMA := by
  obtain ⟨family, hF⟩ := hf.exists_pseudorandomFunction
  exact hS.exists_eufCMA_of_prf hcap hF

/-- **Stateless many-time signatures from one-way functions and collision-resistant hash families**:
combining Lamport one-time signatures, depth-`1` Merkle trees (capacity `2`), PRFs from one-way
functions, and stateless tree signatures yields a stateless EUF-CMA secure signature scheme. -/
theorem _root_.Cslib.Crypto.OneWay.exists_eufCMA_of_hashFamily
    {f : List Bool → List Bool} (hf : OneWay f)
    {H : List Bool → List Bool → List Bool} (hH : HashFamily H) :
    ∃ M : SignatureScheme, M.EUFCMA := by
  obtain ⟨S, hcapS, hS⟩ :=
    hf.exists_indexedEUFCMA hH (depth := fun _ => 1) (ComputableInPolyTime.const 2)
  exact hS.exists_eufCMA_of_oneWay (fun n => by rw [hcapS n]; decide) hf

end AsymptoticSecurity

end TreeSignature

end Cslib.Crypto
