/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.Explicit
public import Complexity.Computability.GenericRAM.Native.StackRecursion
public import Complexity.Foundations.Data.BitString.List.Binary
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Words
public import Complexity.Computability.GenericRAM.Native.BooleanFold
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListLookup
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeOptionPrimitives
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
import Complexity.Foundations.Data.BitString.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryDivision
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListBinaryLookup
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListMap
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListToBits
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.List.GetD

/-!
# Contracting a network with described tensors by direct summation

The leaves of the recursion in the proof of Theorem D.1 of [OpenAI2026ETH] are summed directly
over all Boolean edge assignments (Appendix D.4.7, p. 64), but their tensors are not tables: a
packet vertex has up to `2 L` ports, so its table would be superpolynomial, and its entries are
computed from a description instead (Appendix D.4.6, p. 63). A *described network*
(`DescribedNetwork T`) has, for each vertex, its ports and a descriptor `t : T` of its tensor,
whose entry at the bits `bs` on the ports is `eval t bs` for an evaluator `eval`. Explicit
networks are the case of tables (`DescribedNetwork.ofExplicit`).

**Direct summation as a stack recursion** (`DescribedNetwork.sumScheme`). The sum over the
`2 ^ m` assignments is a call whose children are the assignments, in binary order; an assignment
is a call whose children are the entries of the vertices at its bits, multiplied modulo `2 ^ P`;
an entry is a leaf, evaluated by the evaluator. The derivation has `2 ^ m (k + 1) + 1` nodes for
`k` vertices and two open calls (`DescribedNetwork.eval_sumRoot`). So a native certificate of the
evaluator, with any bounds, gives one native machine for the contraction modulo `2 ^ P` on every
input (`DescribedNetwork.contractionCertificate`), through
`Cslib.GenericRAM.StackRecursion.Scheme.certificate`. If the evaluator takes time `E`, space `ES`
and outputs at most `Ev` bits on every vertex, the machine takes time `2 ^ m (k + 1) + 1` times
`K (n + Ev + 1) ^ K + 2 E` and space `K (n + Ev + 1) ^ K + ES` on inputs of length `n`
(`DescribedNetwork.contractionCertificate_le`). This is the leaf step of the contraction
algorithm, with implicit packet tensors as descriptors.

## Main definitions

* `Cslib.Circuits.Frontier.DescribedNetwork`: a network with described tensors.
* `Cslib.Circuits.Frontier.DescribedNetwork.contraction`: its contraction.
* `Cslib.Circuits.Frontier.DescribedNetwork.sumScheme`: direct summation as a recursion scheme.
* `Cslib.Circuits.Frontier.DescribedNetwork.encDescribed`: the encoding of a described network.
* `Cslib.Circuits.Frontier.DescribedNetwork.contractionCertificate`: one native machine for the
  contraction modulo `2 ^ P`.

## Main results

* `Cslib.GenericRAM.StackRecursion.Scheme.Loop.counted`: a call whose children are indexed by
  a counter.
* `Cslib.Circuits.Frontier.DescribedNetwork.eval_sumRoot`: direct summation evaluates to the
  contraction modulo `2 ^ P`, with `2 ^ m (k + 1) + 1` nodes and two open calls.
* `Cslib.Circuits.Frontier.DescribedNetwork.contraction_ofExplicit`: explicit networks.
* `Cslib.Circuits.Frontier.DescribedNetwork.run_sumScheme`: the machine computes the contraction
  modulo `2 ^ P`.
* `Cslib.Circuits.Frontier.DescribedNetwork.contractionCertificate_le`: its time and space.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Appendix D.4.6–D.4.7
  (pp. 63–64).
-/

@[expose] public section

namespace Cslib.GenericRAM.StackRecursion.Scheme

open Finset

variable {X A Y : Type} {R : Scheme X A Y} {I : Invariant X A Y}

/-- **A call with counted children.** If, from the accumulators `acc c`, the call `x` asks for the
children `child c` for `c < bound` and then stops, and the children evaluate to `val c`, then its
loop from `acc 0` ends at `acc bound`, with the children's nodes and at most `H` levels. -/
theorem Loop.counted {x : X} {acc : ℕ → A} {child : ℕ → X} {val : ℕ → Y} {nodes height : ℕ → ℕ}
    (bound H : ℕ) (hnext : ∀ c < bound, R.next x (acc c) = some (child c))
    (hdone : R.next x (acc bound) = none)
    (habsorb : ∀ c < bound, R.absorb x (acc c) (val c) = acc (c + 1))
    (heval : ∀ c < bound, R.Eval I (child c) (val c) (nodes c) (height c))
    (hframe : ∀ c < bound, I.frame x (acc c)) (hH : ∀ c < bound, height c ≤ H) :
    ∃ h ≤ H, R.Loop I x (acc 0) (acc bound) (∑ c ∈ range bound, nodes c) h := by
  -- From any start `s ≤ bound`.
  have key : ∀ k s, s + k = bound →
      ∃ h ≤ H, R.Loop I x (acc s) (acc bound) (∑ c ∈ Ico s bound, nodes c) h := by
    intro k
    induction k with
    | zero =>
      intro s hs
      subst hs
      exact ⟨0, Nat.zero_le _, by simpa using Loop.done hdone⟩
    | succ k ih =>
      intro s hs
      obtain ⟨h, hh, hl⟩ := ih (s + 1) (by omega)
      have hs' : s < bound := by omega
      have hl' := Loop.child (hframe s hs') (hnext s hs') (heval s hs')
        (by rw [habsorb s hs']; exact hl)
      refine ⟨max (height s) h, max_le (hH s hs') hh, ?_⟩
      rwa [sum_eq_sum_Ico_succ_bot hs']
  simpa using key bound 0 (by omega)

end Cslib.GenericRAM.StackRecursion.Scheme

namespace Cslib.Circuits.Frontier

open Finset Cslib.BitString Cslib.GenericRAM Cslib.GenericRAM.StackRecursion

/-- A Boolean tensor network with *described* tensors: the number of edges, numbered from zero,
and for each vertex its ordered list of ports and a descriptor of its tensor. -/
structure DescribedNetwork (T : Type) where
  /-- The number of edges; the edges are numbered `0, …, numEdges - 1`. -/
  numEdges : ℕ
  /-- The vertices, each given by its ports and the descriptor of its tensor. -/
  vertices : List (List ℕ × T)

namespace DescribedNetwork

variable {T : Type} (eval : T → List Bool → ℕ)

/-- The bits that a word, read as an assignment of bits to the edges, puts on a list of ports;
a port past the end of the word reads `false`. -/
def wordBits (word : List Bool) (ports : List ℕ) : List Bool :=
  ports.map fun i => word.getD i false

/-- The *contraction*: the sum over all assignments of bits to the edges of the product of the
entries of the vertices at the bits on their ports. -/
def contraction (d : DescribedNetwork T) : ℕ :=
  ∑ x : Fin d.numEdges → Bool,
    (d.vertices.map fun v => eval v.2 (wordBits (List.ofFn x) v.1)).prod

/-- An explicit network, with its tables as descriptors. -/
def ofExplicit (d : ExplicitTensorNetwork ℕ) : DescribedNetwork (List ℕ) :=
  ⟨d.numEdges, d.vertices⟩

private theorem getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  by_cases h : i < n
  · rw [dite_eq_left h, List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]
  · rw [dite_eq_right h, List.getD_eq_default _ _ (by simp only [List.length_ofFn]; omega)]

/-- **Explicit networks**: with table lookup as the evaluator, the contraction is that of the
explicit network. -/
theorem contraction_ofExplicit (d : ExplicitTensorNetwork ℕ) :
    (ofExplicit d).contraction ExplicitTensorNetwork.entry = d.contraction := by
  refine sum_congr rfl fun x _ => ?_
  simp only [wordBits, ExplicitTensorNetwork.portBits]
  congr 1
  refine List.map_congr_left fun v _ => ?_
  congr 2
  funext i
  exact getD_ofFn x i

/-! ### Direct summation as a recursion scheme -/

/-- A node of direct summation: its kind (`0` the sum, `1` an assignment, `2` an entry), the
precision and the network, and the current word and vertex index. -/
abbrev Node (T : Type) := ℕ × ((ℕ × DescribedNetwork T) × (List Bool × ℕ))

/-- The entry of a node: the evaluator at the descriptor of its vertex and the bits of its word
on the vertex's ports, or zero for an index past the vertices. -/
def entryOf (x : Node T) : ℕ :=
  (x.2.1.2.vertices[x.2.2.2]?).elim 0 fun v => eval v.2 (wordBits x.2.2.1 v.1)

/-- **Direct summation as a recursion scheme.** The sum (kind `0`) has the `2 ^ m` assignments as
children, adding their values modulo `2 ^ P`; an assignment (kind `1`) has the entries of the
vertices as children, multiplying them modulo `2 ^ P`; an entry (kind `2`) is a leaf. The
accumulator is a counter and a residue. -/
def sumScheme : Scheme (Node T) (ℕ × ℕ) ℕ where
  isLeaf x := x.1 == 2
  leaf := entryOf eval
  start x := (0, (if x.1 = 0 then 0 else 1) % 2 ^ x.2.1.1)
  next x a :=
    if x.1 = 0 then
      (if a.1 < 2 ^ x.2.1.2.numEdges then some (1, (x.2.1, (lowBits x.2.1.2.numEdges a.1, 0)))
        else none)
    else if x.1 = 1 then
      (if a.1 < x.2.1.2.vertices.length then
        some (2, (x.2.1, (x.2.2.1, min x.2.1.2.vertices.length a.1))) else none)
    else none
  absorb x a y := (a.1 + 1, if x.1 = 0 then (a.2 + y) % 2 ^ x.2.1.1 else a.2 * y % 2 ^ x.2.1.1)
  finish _ a := a.2

/-- The root of direct summation on `(P, d)`. -/
def sumRoot (q : ℕ × DescribedNetwork T) : Node T := (0, (q, ([], 0)))

/-- The weight of a word modulo `2 ^ P`: the product of the entries at its bits, reduced after
each factor. -/
def weightMod (P : ℕ) (d : DescribedNetwork T) (word : List Bool) : ℕ :=
  d.vertices.foldl (fun acc v => acc * eval v.2 (wordBits word v.1) % 2 ^ P) (1 % 2 ^ P)

/-- The shape of a node of direct summation on `q`: it keeps `q`, its kind is at most `2`, its
word has at most `m` bits and its index is at most the number of vertices. -/
def NodeShape (q : ℕ × DescribedNetwork T) (x : Node T) : Prop :=
  x.2.1 = q ∧ x.1 ≤ 2 ∧ x.2.2.1.length ≤ q.2.numEdges ∧ x.2.2.2 ≤ q.2.vertices.length

/-- The invariant of direct summation on `q = (P, d)`: nodes have the shape of `NodeShape`, frames
also have a counter at most `2 ^ m + k` and a residue below `2 ^ P`, and every value is a residue
below `2 ^ P` or an entry of a vertex at the bits of an `m`-bit word. -/
def sumInvariant (q : ℕ × DescribedNetwork T) : Invariant (Node T) (ℕ × ℕ) ℕ :=
  ⟨NodeShape q, fun x a => NodeShape q x ∧ a.1 ≤ 2 ^ q.2.numEdges + q.2.vertices.length ∧
      a.2 < 2 ^ q.1,
    fun y => y < 2 ^ q.1 ∨ ∃ v ∈ q.2.vertices, ∃ w : List Bool, w.length = q.2.numEdges ∧
      y = eval v.2 (wordBits w v.1)⟩

variable {eval}

/-- An entry is a leaf. -/
theorem eval_entry (q : ℕ × DescribedNetwork T) {word : List Bool} {v : ℕ}
    (hw : word.length = q.2.numEdges) (hv : v < q.2.vertices.length) :
    (sumScheme eval).Eval (sumInvariant eval q) (2, (q, (word, v)))
      (entryOf eval (2, (q, (word, v)))) 1 0 := by
  refine Scheme.Eval.leaf (R := sumScheme eval) ⟨rfl, by omega, hw.le, hv.le⟩ rfl
    (.inr ⟨q.2.vertices[v], List.getElem_mem hv, word, hw, ?_⟩)
  change (q.2.vertices[v]?).elim 0 _ = _
  rw [List.getElem?_eq_getElem hv]
  rfl

private theorem foldl_take_succ (d : DescribedNetwork T) (P : ℕ) (word : List Bool) (c : ℕ)
    (hc : c < d.vertices.length) :
    (d.vertices.take (c + 1)).foldl (fun acc v => acc * eval v.2 (wordBits word v.1) % 2 ^ P)
        (1 % 2 ^ P) =
      (d.vertices.take c).foldl (fun acc v => acc * eval v.2 (wordBits word v.1) % 2 ^ P)
        (1 % 2 ^ P) * entryOf eval (2, ((P, d), (word, c))) % 2 ^ P := by
  rw [List.take_add_one, List.getElem?_eq_getElem hc, Option.toList_some, List.foldl_append]
  simp [entryOf, List.getElem?_eq_getElem hc]

private theorem foldl_mod_lt {α : Type} (f : α → ℕ) (P : ℕ) (l : List α) :
    l.foldl (fun acc v => acc * f v % 2 ^ P) (1 % 2 ^ P) < 2 ^ P := by
  have h (a : ℕ) (ha : a < 2 ^ P) : l.foldl (fun acc v => acc * f v % 2 ^ P) a < 2 ^ P := by
    induction l generalizing a with
    | nil => exact ha
    | cons v l ih => exact ih _ (Nat.mod_lt _ (Nat.two_pow_pos P))
  exact h _ (Nat.mod_lt _ (Nat.two_pow_pos P))

/-- **An assignment evaluates to the weight of its word**, with one node per vertex plus one
and one open call. -/
theorem eval_assign (P : ℕ) (d : DescribedNetwork T) {word : List Bool}
    (hw : word.length = d.numEdges) :
    ∃ h ≤ 1, (sumScheme eval).Eval (sumInvariant eval (P, d)) (1, ((P, d), (word, 0)))
      (weightMod eval P d word) (d.vertices.length + 1) h := by
  set acc : ℕ → ℕ × ℕ := fun c => (c, (d.vertices.take c).foldl
    (fun acc v => acc * eval v.2 (wordBits word v.1) % 2 ^ P) (1 % 2 ^ P))
  have hshape : NodeShape (P, d) ((1, ((P, d), (word, 0))) : Node T) :=
    ⟨rfl, by omega, hw.le, Nat.zero_le _⟩
  obtain ⟨h, hh, hloop⟩ := Scheme.Loop.counted (R := sumScheme eval)
    (I := sumInvariant eval (P, d))
    (x := (1, ((P, d), (word, 0)))) (acc := acc)
    (child := fun c => (2, ((P, d), (word, c))))
    (val := fun c => entryOf eval (2, ((P, d), (word, c))))
    (nodes := fun _ => 1) (height := fun _ => 0) d.vertices.length 0
    (fun c hc => by simp [sumScheme, acc, hc, min_eq_right hc.le])
    (by simp [sumScheme, acc])
    (fun c hc => by
      simp only [sumScheme, acc, one_ne_zero, ite_false]
      rw [foldl_take_succ d P word c hc])
    (fun c hc => eval_entry (P, d) hw hc)
    (fun c hc => ⟨hshape, (Nat.le_of_lt hc).trans (Nat.le_add_left _ _), foldl_mod_lt _ _ _⟩)
    (fun _ _ => le_rfl)
  have hstart : (sumScheme eval).start (1, ((P, d), (word, 0))) = acc 0 := by
    simp [sumScheme, acc]
  rw [← hstart] at hloop
  refine ⟨h + 1, by omega, ?_⟩
  have := Scheme.Eval.call (R := sumScheme eval) (I := sumInvariant eval (P, d))
    (x := (1, ((P, d), (word, 0)))) hshape rfl hloop (.inl (foldl_mod_lt _ _ _))
  simpa [sumScheme, acc, weightMod, List.take_length, Finset.sum_const, Finset.card_range] using
    this

private theorem sum_lowBits (n : ℕ) (g : List Bool → ℕ) :
    ∑ j ∈ range (2 ^ n), g (lowBits n j) = ∑ x : Fin n → Bool, g (List.ofFn x) := by
  rw [← Fin.sum_univ_eq_sum_range]
  exact Fintype.sum_equiv (equivFin n).symm _ _ fun k => by
    rw [lowBits_eq_ofFn_equivFin_symm]

private theorem foldl_mul_mod {α : Type} (f : α → ℕ) (m : ℕ) (l : List α) (a : ℕ) :
    l.foldl (fun acc v => acc * f v % m) (a % m) = a * (l.map f).prod % m := by
  induction l generalizing a with
  | nil => simp
  | cons v l ih =>
    rw [List.foldl_cons, Nat.mod_mul_mod, ih, List.map_cons, List.prod_cons, Nat.mul_assoc]

private theorem weightMod_eq (P : ℕ) (d : DescribedNetwork T) (word : List Bool) :
    weightMod eval P d word =
      (d.vertices.map fun v => eval v.2 (wordBits word v.1)).prod % 2 ^ P := by
  rw [weightMod, foldl_mul_mod, Nat.one_mul]

/-- **Direct summation computes the contraction modulo `2 ^ P`**, with `2 ^ m (k + 1) + 1`
nodes for `m` edges and `k` vertices, and at most two open calls. -/
theorem eval_sumRoot (P : ℕ) (d : DescribedNetwork T) :
    ∃ h ≤ 2, (sumScheme eval).Eval (sumInvariant eval (P, d)) (sumRoot (P, d))
      (d.contraction eval % 2 ^ P) (2 ^ d.numEdges * (d.vertices.length + 1) + 1) h := by
  set acc : ℕ → ℕ × ℕ := fun c => (c, (∑ j ∈ range c, weightMod eval P d (lowBits d.numEdges j)) %
    2 ^ P)
  have hassign (c : ℕ) := eval_assign (eval := eval) P d (length_lowBits d.numEdges c)
  choose hgt hhgt heval using hassign
  have hshape : NodeShape (P, d) (sumRoot (P, d)) := ⟨rfl, by simp [sumRoot], by simp [sumRoot],
    by simp [sumRoot]⟩
  obtain ⟨h, hh, hloop⟩ := Scheme.Loop.counted (R := sumScheme eval)
    (I := sumInvariant eval (P, d))
    (x := sumRoot (P, d)) (acc := acc)
    (child := fun c => (1, ((P, d), (lowBits d.numEdges c, 0))))
    (val := fun c => weightMod eval P d (lowBits d.numEdges c))
    (nodes := fun _ => d.vertices.length + 1) (height := hgt) (2 ^ d.numEdges) 1
    (fun c hc => by simp [sumScheme, sumRoot, acc, hc])
    (by simp [sumScheme, sumRoot, acc])
    (fun c hc => by simp [sumScheme, sumRoot, acc, sum_range_succ, Nat.add_mod])
    (fun c _ => heval c)
    (fun c hc => ⟨hshape, by simp only [acc]; omega, Nat.mod_lt _ (Nat.two_pow_pos P)⟩)
    (fun c _ => hhgt c)
  have hstart : (sumScheme eval).start (sumRoot (P, d)) = acc 0 := by
    simp [sumScheme, sumRoot, acc]
  rw [← hstart] at hloop
  refine ⟨h + 1, by omega, ?_⟩
  have := Scheme.Eval.call (R := sumScheme eval) (I := sumInvariant eval (P, d))
    (x := sumRoot (P, d)) hshape rfl hloop (.inl (Nat.mod_lt _ (Nat.two_pow_pos P)))
  have hval : (sumScheme eval).finish (sumRoot (P, d)) (acc (2 ^ d.numEdges)) =
      d.contraction eval % 2 ^ P := by
    simp only [sumScheme, acc, contraction]
    rw [sum_lowBits d.numEdges (weightMod eval P d)]
    simp only [weightMod_eq]
    exact (Finset.sum_nat_mod _ _ _).symm
  rw [hval, sum_const, card_range, smul_eq_mul] at this
  exact this

/-! ### The native machine -/

section Native

open Turing.MultiTapeTM

variable (encT : T ↪ List Bool)

/-- A described network is its number of edges and its list of vertices. -/
def equivProd : DescribedNetwork T ≃ ℕ × List (List ℕ × T) where
  toFun d := (d.numEdges, d.vertices)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The encoding of a described network**: its number of edges in unary, then its vertices,
each the pair of its list of ports in binary and its descriptor. -/
def encDescribed : DescribedNetwork T ↪ List Bool :=
  encOfEquiv equivProd (encPair encUnary (encList (encPair (encList encNat) encT)))

/-- The encoding of an input `(P, d)`: the precision in unary and the network. -/
abbrev encInput : ℕ × DescribedNetwork T ↪ List Bool := encPair encUnary (encDescribed encT)

/-- The encoding of a node: its kind in unary, its input, its word and its vertex index in
unary. -/
abbrev encNode : Node T ↪ List Bool :=
  encPair encUnary (encPair (encInput encT) (encPair encBits encUnary))

/-- The encoding of an accumulator: the counter and the residue, in binary. -/
abbrev encAcc : ℕ × ℕ ↪ List Bool := encPair encNat encNat

variable {encT}

/-- The number of edges of a described network, in unary. -/
theorem numEdges_polyTime :
    ComputableInPolyTime (fun d : DescribedNetwork T => d.numEdges) (encDescribed encT)
      encUnary :=
  (ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.of_eq (f := equivProd) fun _ => rfl)

/-- The vertices of a described network. -/
theorem vertices_polyTime :
    ComputableInPolyTime (fun d : DescribedNetwork T => d.vertices) (encDescribed encT)
      (encList (encPair (encList encNat) encT)) :=
  (ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.of_eq (f := equivProd) fun _ => rfl)

/-- The kind of a node. -/
theorem kind_polyTime : ComputableInPolyTime (fun x : Node T => x.1) (encNode encT)
    encUnary := ComputableInPolyTime.fst _ _

/-- The input `(P, d)` of a node. -/
theorem input_polyTime : ComputableInPolyTime (fun x : Node T => x.2.1) (encNode encT)
    (encInput encT) := (ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.snd _ _)

/-- The precision of a node. -/
theorem precision_polyTime : ComputableInPolyTime (fun x : Node T => x.2.1.1)
    (encNode encT) encUnary := (ComputableInPolyTime.fst _ _).comp input_polyTime

/-- The network of a node. -/
theorem network_polyTime : ComputableInPolyTime (fun x : Node T => x.2.1.2)
    (encNode encT) (encDescribed encT) := (ComputableInPolyTime.snd _ _).comp input_polyTime

/-- The word of a node. -/
theorem word_polyTime : ComputableInPolyTime (fun x : Node T => x.2.2.1)
    (encNode encT) encBits :=
  (ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.snd _ _).snd'

/-- The vertex index of a node. -/
theorem index_polyTime : ComputableInPolyTime (fun x : Node T => x.2.2.2)
    (encNode encT) encUnary :=
  (ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.snd _ _).snd'

/-- `2 ^ P`, from `P` in unary. -/
private theorem twoPow {α : Type} {encIn : α ↪ List Bool} {P : α → ℕ}
    (hP : ComputableInPolyTime P encIn encUnary) :
    ComputableInPolyTime (fun a => 2 ^ P a) encIn encNat :=
  ComputableInPolyTime.binary_two_pow.comp hP

/-- `x % 2 ^ P`, from `P` in unary. -/
private theorem modTwoPow {α : Type} {encIn : α ↪ List Bool} {x P : α → ℕ}
    (hx : ComputableInPolyTime x encIn encNat) (hP : ComputableInPolyTime P encIn encUnary) :
    ComputableInPolyTime (fun a => x a % 2 ^ P a) encIn encNat :=
  ComputableInPolyTime.binary_mod.comp (hx.prod (twoPow hP))

/-- **The polynomial-time components of direct summation.** -/
theorem sumScheme_polyTime : (sumScheme eval).PolyTime (encNode encT) encAcc encNat where
  isLeaf := ComputableInPolyTime.beq kind_polyTime (ComputableInPolyTime.const 2)
  start := by
    refine (ComputableInPolyTime.const 0).prod (modTwoPow ?_ precision_polyTime)
    refine (ComputableInPolyTime.ite (encMid := encNat) (ComputableInPolyTime.beq kind_polyTime
      (ComputableInPolyTime.const 0)) (ComputableInPolyTime.const 0)
      (ComputableInPolyTime.const 1)).of_enc_eq fun x => ?_
    by_cases h : x.1 = 0 <;> simp [h]
  next := by
    have hx := ComputableInPolyTime.fst (encNode encT) encAcc
    have ha := ComputableInPolyTime.snd (encNode encT) encAcc
    have hk := kind_polyTime.comp hx
    have hc := (ComputableInPolyTime.fst encNat encNat).comp ha
    have hq := input_polyTime.comp hx
    have hd := network_polyTime.comp hx
    have hm := numEdges_polyTime.comp hd
    have hlen := (ComputableInPolyTime.length_list _).comp (vertices_polyTime.comp hd)
    have hassign : ComputableInPolyTime (fun p : Node T × (ℕ × ℕ) =>
        (if p.2.1 < 2 ^ p.1.2.1.2.numEdges then
          some ((1, (p.1.2.1, (lowBits p.1.2.1.2.numEdges p.2.1, 0))) : Node T) else none))
        (encPair (encNode encT) encAcc) (encOption (encNode encT)) :=
      (ComputableInPolyTime.ite (ComputableInPolyTime.binary_lt' hc (twoPow hm))
        ((ComputableInPolyTime.optionSome (encNode encT)).comp
          ((ComputableInPolyTime.const (encOut := encUnary) 1).prod
          (hq.prod ((BooleanFold.decoder_polyTime.comp (hm.prod hc)).prod
            (ComputableInPolyTime.const (encOut := encUnary) 0)))))
        (ComputableInPolyTime.const none)).of_enc_eq fun p => by
          by_cases h : p.2.1 < 2 ^ p.1.2.1.2.numEdges <;> simp [h]
    have hentry : ComputableInPolyTime (fun p : Node T × (ℕ × ℕ) =>
        (if p.2.1 < p.1.2.1.2.vertices.length then
          some ((2, (p.1.2.1, (p.1.2.2.1, min p.1.2.1.2.vertices.length p.2.1))) : Node T)
          else none))
        (encPair (encNode encT) encAcc) (encOption (encNode encT)) :=
      (ComputableInPolyTime.ite (ComputableInPolyTime.binary_lt' hc
          (ComputableInPolyTime.unary_to_binary.comp hlen))
        ((ComputableInPolyTime.optionSome (encNode encT)).comp
          ((ComputableInPolyTime.const (encOut := encUnary) 2).prod
          (hq.prod ((word_polyTime.comp hx).prod
            (ComputableInPolyTime.binary_min_unary' hlen hc)))))
        (ComputableInPolyTime.const none)).of_enc_eq fun p => by
          by_cases h : p.2.1 < p.1.2.1.2.vertices.length <;> simp [h]
    refine (ComputableInPolyTime.ite (ComputableInPolyTime.beq hk (ComputableInPolyTime.const 0))
      hassign (ComputableInPolyTime.ite (ComputableInPolyTime.beq hk
        (ComputableInPolyTime.const 1)) hentry (ComputableInPolyTime.const none))).of_enc_eq
      fun p => ?_
    by_cases h0 : p.1.1 = 0
    · simp [sumScheme, h0]
    · by_cases h1 : p.1.1 = 1 <;> simp [sumScheme, h0, h1]
  absorb := by
    have hx := (ComputableInPolyTime.fst (encNode encT) encAcc).comp
      (ComputableInPolyTime.fst (encPair (encNode encT) encAcc) encNat)
    have ha := (ComputableInPolyTime.snd (encNode encT) encAcc).comp
      (ComputableInPolyTime.fst (encPair (encNode encT) encAcc) encNat)
    have hy := ComputableInPolyTime.snd (encPair (encNode encT) encAcc) encNat
    have hc := (ComputableInPolyTime.fst encNat encNat).comp ha
    have hr := (ComputableInPolyTime.snd encNat encNat).comp ha
    have hP := precision_polyTime.comp hx
    refine (ComputableInPolyTime.binary_add.comp (hc.prod (ComputableInPolyTime.const 1))).prod
      ((ComputableInPolyTime.ite (ComputableInPolyTime.beq (kind_polyTime.comp hx)
        (ComputableInPolyTime.const 0))
        (modTwoPow (ComputableInPolyTime.binary_add.comp (hr.prod hy)) hP)
        (modTwoPow (ComputableInPolyTime.binary_mul' hr hy) hP)).of_enc_eq fun q => ?_)
    by_cases h : q.1.1.1 = 0 <;> simp [h]
  finish := (ComputableInPolyTime.snd encNat encNat).comp (ComputableInPolyTime.snd _ _)

/-- The descriptor of a vertex and the bits of the node's word on its ports. -/
theorem query_polyTime :
    ComputableInPolyTime (fun p : Node T × (List ℕ × T) => (p.2.2, wordBits p.1.2.2.1 p.2.1))
      (encPair (encNode encT) (encPair (encList encNat) encT)) (encPair encT encBits) := by
  have hv := ComputableInPolyTime.snd (encNode encT) (encPair (encList encNat) encT)
  have hports := (ComputableInPolyTime.fst (encList encNat) encT).comp hv
  have hword := word_polyTime.comp (ComputableInPolyTime.fst (encNode encT)
    (encPair (encList encNat) encT))
  let E := encPair (encNode encT) (encPair (encList encNat) encT)
  have hbit : ComputableInPolyTime (fun z : (Node T × (List ℕ × T)) × ℕ =>
      z.1.1.2.2.1.getD z.2 false) (encPair E encNat) encBool :=
    ComputableInPolyTime.listGetD_binary (encA := encBool) (encL := encBits) false
      (hword.comp (ComputableInPolyTime.fst E encNat)) (ComputableInPolyTime.snd E encNat)
  have hbits := ComputableInPolyTime.listToBits.comp
    (ComputableInPolyTime.mapWithInput (f := fun p i => p.1.2.2.1.getD i false) hports hbit)
  exact ((ComputableInPolyTime.snd (encList encNat) encT).comp hv).prod hbits

/-- The vertex of a node, if its index is in range. -/
noncomputable def vertexCertificate :
    NativeCertificate (fun x : Node T => x.2.1.2.vertices[x.2.2.2]?) (encNode encT)
      (encOption (encPair (encList encNat) encT)) :=
  NativeCertificate.ofPolyTime (ComputableInPolyTime.getElem?
    (vertices_polyTime.comp network_polyTime) index_polyTime)

/-- The query to the evaluator: the descriptor and the bits on the ports. -/
noncomputable def queryCertificate :
    NativeCertificate (fun p : Node T × (List ℕ × T) => (p.2.2, wordBits p.1.2.2.1 p.2.1))
      (encPair (encNode encT) (encPair (encList encNat) encT)) (encPair encT encBits) :=
  NativeCertificate.ofPolyTime query_polyTime

variable (eval) in
/-- **The leaf step**: the evaluator at the descriptor of the node's vertex and its bits, from a
native certificate of the evaluator with any bounds. -/
noncomputable def leafCertificate
    (ev : NativeCertificate (fun q : T × List Bool => eval q.1 q.2) (encPair encT encBits)
      encNat) :
    NativeCertificate (sumScheme eval).leaf (encNode encT) encNat :=
  NativeCertificate.option (value := fun x : Node T => x.2.1.2.vertices[x.2.2.2]?)
    (fallback := fun _ => 0) (body := fun p => eval p.2.2 (wordBits p.1.2.2.1 p.2.1))
    vertexCertificate (NativeCertificate.const 0) (ev.comp queryCertificate)

/-- The time of the leaf step: the vertex lookup, and the query and the evaluator at a vertex. -/
theorem leafCertificate_time
    (ev : NativeCertificate (fun q : T × List Bool => eval q.1 q.2) (encPair encT encBits)
      encNat) (x : Node T) :
    (leafCertificate eval ev).time x = 2 * (vertexCertificate (encT := encT)).time x +
      (encNode encT x).length +
      (x.2.1.2.vertices[x.2.2.2]?).elim (encNode encT x).length
        fun v => (queryCertificate (encT := encT)).time (x, v) +
          ev.time (v.2, wordBits x.2.2.1 v.1) := rfl

/-- The space of the leaf step. -/
theorem leafCertificate_space
    (ev : NativeCertificate (fun q : T × List Bool => eval q.1 q.2) (encPair encT encBits)
      encNat) (x : Node T) :
    (leafCertificate eval ev).space x = 2 * (vertexCertificate (encT := encT)).space x +
      (encNode encT x).length +
      (x.2.1.2.vertices[x.2.2.2]?).elim (encNode encT x).length
        fun v => (queryCertificate (encT := encT)).space (x, v) +
          ev.space (v.2, wordBits x.2.2.1 v.1) := rfl

/-- The number of steps of direct summation: `2 (2 ^ m (k + 1) + 1) - 1`. -/
def fuel (q : ℕ × DescribedNetwork T) : ℕ :=
  2 * (2 ^ q.2.numEdges * (q.2.vertices.length + 1)) + 1

/-- The fuel in polynomial time. -/
theorem fuel_polyTime : ComputableInPolyTime (fuel (T := T)) (encInput encT) encNat := by
  have hd := ComputableInPolyTime.snd encUnary (encDescribed encT)
  have hm := numEdges_polyTime.comp hd
  have hlen := (ComputableInPolyTime.length_list _).comp (vertices_polyTime.comp hd)
  exact ComputableInPolyTime.binary_add.comp ((ComputableInPolyTime.binary_mul'
    (ComputableInPolyTime.const 2) (ComputableInPolyTime.binary_mul' (twoPow hm)
      (ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.unary_add' hlen
        (ComputableInPolyTime.const 1))))).prod (ComputableInPolyTime.const 1))

/-- The root in polynomial time. -/
theorem sumRoot_polyTime : ComputableInPolyTime (sumRoot (T := T)) (encInput encT)
    (encNode encT) :=
  (ComputableInPolyTime.const 0).prod (ComputableInPolyTime.id'.prod
    (ComputableInPolyTime.const ([], 0)))

variable (eval) in
/-- **One native machine for direct summation over described networks**, from a native
certificate of the evaluator. It returns `some (d.contraction eval % 2 ^ P)`
(`run_sumScheme`). -/
noncomputable def sumCertificate
    (ev : NativeCertificate (fun q : T × List Bool => eval q.1 q.2) (encPair encT encBits)
      encNat) :
    NativeCertificate ((sumScheme eval).run fuel sumRoot) (encInput encT) (encOption encNat) :=
  Scheme.certificate sumScheme_polyTime (leafCertificate eval ev)
    (NativeCertificate.ofPolyTime fuel_polyTime) (NativeCertificate.ofPolyTime sumRoot_polyTime)

/-- **The machine computes the contraction modulo `2 ^ P`.** -/
theorem run_sumScheme (q : ℕ × DescribedNetwork T) :
    (sumScheme eval).run fuel sumRoot q = some (q.2.contraction eval % 2 ^ q.1) := by
  obtain ⟨h, -, he⟩ := eval_sumRoot (eval := eval) q.1 q.2
  exact Scheme.run_eq_some he (by simp [fuel]; omega)

variable (eval) in
/-- **Direct summation over described networks, as a native certificate** for the contraction
modulo `2 ^ P` on every input `(P, d)`, from a native certificate of the evaluator. -/
noncomputable def contractionCertificate
    (ev : NativeCertificate (fun q : T × List Bool => eval q.1 q.2) (encPair encT encBits)
      encNat) :
    NativeCertificate (fun q : ℕ × DescribedNetwork T => q.2.contraction eval % 2 ^ q.1)
      (encInput encT) encNat :=
  (NativeCertificate.post (sumCertificate eval ev)
    (ComputableInDegree.getD (enc₁ := encNat) (enc := encOption encNat) 0).inO_one).congr
    fun q => by simp [run_sumScheme]

/-- The time is that of the stack machine. -/
@[simp] theorem contractionCertificate_time
    (ev : NativeCertificate (fun q : T × List Bool => eval q.1 q.2) (encPair encT encBits)
      encNat) :
    (contractionCertificate eval ev).time = (sumCertificate eval ev).time := rfl

/-- The space is that of the stack machine. -/
@[simp] theorem contractionCertificate_space
    (ev : NativeCertificate (fun q : T × List Bool => eval q.1 q.2) (encPair encT encBits)
      encNat) :
    (contractionCertificate eval ev).space = (sumCertificate eval ev).space := rfl

/-! ### Resources -/

/-- The number of edges and the number of vertices are at most the encoded length. -/
theorem length_numEdges_vertices_le (d : DescribedNetwork T) :
    d.numEdges + d.vertices.length ≤ (encDescribed encT d).length := by
  have h := length_le_length_encList (encPair (encList encNat) encT) d.vertices
  change d.numEdges + d.vertices.length ≤
    (encPair encUnary (encList (encPair (encList encNat) encT)) (d.numEdges, d.vertices)).length
  simp only [length_encPair, encUnary_apply, List.length_replicate]
  omega

/-- A node of the right shape is at most `5 n + 7` long, for `n` the length of the input. -/
theorem length_encNode_le {q : ℕ × DescribedNetwork T} {x : Node T} (hx : NodeShape q x) :
    (encNode encT x).length ≤ 5 * (encInput encT q).length + 7 := by
  obtain ⟨hq, hk, hw, hv⟩ := hx
  obtain ⟨k, ⟨P, d⟩, w, v⟩ := x
  simp only at hq hk hw hv
  subst hq
  dsimp only at hw hv
  have hd := length_numEdges_vertices_le (encT := encT) d
  simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply]
  omega

private theorem term_le {c a b d D z : ℕ} (hd : d ≤ D) :
    c * (a * z + b) ^ d ≤ c * (a + b) ^ d * (z + 1) ^ D :=
  calc c * (a * z + b) ^ d ≤ c * ((a + b) * (z + 1)) ^ d :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by nlinarith) _)
    _ = c * (a + b) ^ d * (z + 1) ^ d := by rw [Nat.mul_pow]; ring
    _ ≤ c * (a + b) ^ d * (z + 1) ^ D :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos _) hd)

private theorem length_encNat_lt {y P : ℕ} (h : y < 2 ^ P) : (encNat y).length ≤ P := by
  have h' := Nat.size_le.mpr h
  rw [← Nat.size_eq_bits_len] at h'
  exact h'

/-- **The resources of direct summation over described networks.** There is `K` such that, for
an input `(P, d)` of length `n` with `m` edges and `k` vertices, if the evaluator takes time at
most `E` and space at most `ES` and outputs at most `Ev` bits on every vertex and every list of
bits on its ports, then the time is at most `2 ^ m (k + 1) + 1` times
`K (n + Ev + 1) ^ K + 2 E`, and the space at most `K (n + Ev + 1) ^ K + ES`. -/
theorem contractionCertificate_le
    (ev : NativeCertificate (fun q : T × List Bool => eval q.1 q.2) (encPair encT encBits)
      encNat) :
    ∃ K : ℕ, ∀ (q : ℕ × DescribedNetwork T) (E ES Ev : ℕ),
      (∀ v ∈ q.2.vertices, ∀ bs : List Bool, bs.length = v.1.length →
        ev.time (v.2, bs) ≤ E ∧ ev.space (v.2, bs) ≤ ES ∧ (encNat (eval v.2 bs)).length ≤ Ev) →
      (contractionCertificate eval ev).time q ≤
          (2 ^ q.2.numEdges * (q.2.vertices.length + 1) + 1) *
            (K * ((encInput encT q).length + Ev + 1) ^ K + 2 * E) ∧
        (contractionCertificate eval ev).space q ≤
          K * ((encInput encT q).length + Ev + 1) ^ K + ES := by
  obtain ⟨K₀, hK₀⟩ := Scheme.certificate_le (sumScheme_polyTime (eval := eval) (encT := encT))
    (leafCertificate eval ev)
  have hV : (vertexCertificate (encT := encT)).IsPolynomial :=
    NativeCertificate.ofPolyTime_isPolynomial _
  have hQ : (queryCertificate (encT := encT)).IsPolynomial :=
    NativeCertificate.ofPolyTime_isPolynomial _
  have hF := NativeCertificate.ofPolyTime_isPolynomial (fuel_polyTime (encT := encT))
  have hR := NativeCertificate.ofPolyTime_isPolynomial (sumRoot_polyTime (encT := encT))
  obtain ⟨cv, dv, hvt⟩ := hV.1.exists_le
  obtain ⟨cv', dv', hvs⟩ := hV.2.exists_le
  obtain ⟨cq, dq, hqt⟩ := hQ.1.exists_le
  obtain ⟨cq', dq', hqs⟩ := hQ.2.exists_le
  obtain ⟨cf, df, hft⟩ := hF.1.exists_le
  obtain ⟨cf', df', hfs⟩ := hF.2.exists_le
  obtain ⟨cr, dr, hrt⟩ := hR.1.exists_le
  obtain ⟨cr', dr', hrs⟩ := hR.2.exists_le
  obtain ⟨D, hD⟩ : ∃ D, D = K₀ + dv + dv' + dq + dq' + df + df' + dr + dr' + 2 := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = K₀ * 96 ^ K₀ + (2 * cv * 13 ^ dv + 24 + cq * 27 ^ dq) + 16 :=
    ⟨_, rfl⟩
  obtain ⟨G', hG'⟩ : ∃ G', G' = K₀ * 96 ^ K₀ + (2 * cv' * 13 ^ dv' + 24 + cq' * 27 ^ dq') :=
    ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = cf + cr + cf' + cr' + 2 * G + G' + 4 := ⟨_, rfl⟩
  refine ⟨C + D, fun q E ES Ev hE => ?_⟩
  obtain ⟨P, d⟩ := q
  obtain ⟨n, hn⟩ : ∃ n, n = (encInput encT (P, d)).length := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z, z = n + Ev := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, W = (z + 1) ^ D := ⟨_, rfl⟩
  rw [← hn]
  rw [show n + Ev + 1 = z + 1 by omega]
  have hnP : 2 * P + 1 + (encDescribed encT d).length = n := by
    rw [hn]; simp [encInput]
  have hmk := length_numEdges_vertices_le (encT := encT) d
  -- Every vertex is at most `n` long.
  have hvlen (v : List ℕ × T) (hv : v ∈ d.vertices) :
      (encPair (encList encNat) encT v).length ≤ n := by
    have h1 := List.le_sum_of_mem (List.mem_map_of_mem (f := fun a =>
      (encPair (encList encNat) encT a).length) hv)
    have h2 := sum_length_le_length_encList (encPair (encList encNat) encT) d.vertices
    have h3 : (encList (encPair (encList encNat) encT) d.vertices).length ≤
        (encDescribed encT d).length := by
      change _ ≤ (encPair encUnary (encList (encPair (encList encNat) encT))
        (d.numEdges, d.vertices)).length
      simp only [length_encPair]; omega
    omega
  have hnode (x : Node T) (hx : (sumInvariant eval (P, d)).node x) :
      (encNode encT x).length ≤ 5 * z + 7 := (length_encNode_le hx).trans (by omega)
  have hleafT (x : Node T) (hx : (sumInvariant eval (P, d)).node x) :
      (leafCertificate eval ev).time x ≤
        2 * cv * (5 * z + 8) ^ dv + 2 * (5 * z + 7) + cq * (11 * z + 16) ^ dq + E := by
    have h1 := hnode x hx
    rw [leafCertificate_time]
    have h2 : (vertexCertificate (encT := encT)).time x ≤ cv * (5 * z + 8) ^ dv :=
      (hvt x).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
    have h2' : 2 * (vertexCertificate (encT := encT)).time x ≤ 2 * cv * (5 * z + 8) ^ dv := by
      rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left 2 h2
    cases hvx : x.2.1.2.vertices[x.2.2.2]? with
    | none => simp only [Option.elim]; omega
    | some v =>
      simp only [Option.elim]
      have hmem : v ∈ x.2.1.2.vertices := List.mem_of_getElem? hvx
      obtain ⟨hq, -, -, -⟩ := hx
      rw [hq] at hmem
      have h3 := hvlen v hmem
      have h4 : (queryCertificate (encT := encT)).time (x, v) ≤ cq * (11 * z + 16) ^ dq := by
        refine (hqt (x, v)).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _))
        have := length_encPair (enc₁ := encNode encT) (enc₂ := encPair (encList encNat) encT)
          (x, v)
        dsimp only at this
        omega
      have h5 := (hE v hmem (wordBits x.2.2.1 v.1) (by simp [wordBits])).1
      omega
  have hleafS (x : Node T) (hx : (sumInvariant eval (P, d)).node x) :
      (leafCertificate eval ev).space x ≤
        2 * cv' * (5 * z + 8) ^ dv' + 2 * (5 * z + 7) + cq' * (11 * z + 16) ^ dq' + ES := by
    have h1 := hnode x hx
    rw [leafCertificate_space]
    have h2 : (vertexCertificate (encT := encT)).space x ≤ cv' * (5 * z + 8) ^ dv' :=
      (hvs x).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
    have h2' : 2 * (vertexCertificate (encT := encT)).space x ≤ 2 * cv' * (5 * z + 8) ^ dv' := by
      rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left 2 h2
    cases hvx : x.2.1.2.vertices[x.2.2.2]? with
    | none => simp only [Option.elim]; omega
    | some v =>
      simp only [Option.elim]
      have hmem : v ∈ x.2.1.2.vertices := List.mem_of_getElem? hvx
      obtain ⟨hq, -, -, -⟩ := hx
      rw [hq] at hmem
      have h3 := hvlen v hmem
      have h4 : (queryCertificate (encT := encT)).space (x, v) ≤ cq' * (11 * z + 16) ^ dq' := by
        refine (hqs (x, v)).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _))
        have := length_encPair (enc₁ := encNode encT) (enc₂ := encPair (encList encNat) encT)
          (x, v)
        dsimp only at this
        omega
      have h5 := (hE v hmem (wordBits x.2.2.1 v.1) (by simp [wordBits])).2.1
      omega
  obtain ⟨h, hh, he⟩ := eval_sumRoot (eval := eval) P d
  have hres := hK₀ (NativeCertificate.ofPolyTime fuel_polyTime)
    (NativeCertificate.ofPolyTime sumRoot_polyTime) (sumInvariant eval (P, d)) (13 * z + 18)
    (2 * cv * (5 * z + 8) ^ dv + 2 * (5 * z + 7) + cq * (11 * z + 16) ^ dq + E)
    (2 * cv' * (5 * z + 8) ^ dv' + 2 * (5 * z + 7) + cq' * (11 * z + 16) ^ dq' + ES)
    (fun x hx => ⟨(hnode x hx).trans (by omega), fun _ => ⟨hleafT x hx, hleafS x hx⟩⟩)
    (fun x a ha => by
      obtain ⟨hx, ha1, ha2⟩ := ha
      have h1 := hnode x hx
      have h2 : (encNat a.1).length ≤ d.numEdges + d.vertices.length + 1 := by
        refine length_encNat_lt (lt_of_le_of_lt ha1 ?_)
        calc 2 ^ d.numEdges + d.vertices.length
            < 2 ^ d.numEdges + 2 ^ d.vertices.length := by
              have := Nat.lt_two_pow_self (n := d.vertices.length); omega
          _ ≤ 2 ^ (d.numEdges + d.vertices.length + 1) := by
              rw [pow_succ, pow_add, Nat.mul_two]
              exact Nat.add_le_add (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
                (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))
      have h3 := length_encNat_lt ha2
      have h4 : (encPair (encNode encT) encAcc (x, a)).length =
          2 * (encNode encT x).length + 1 + (encAcc a).length := length_encPair (x, a)
      have h5 : (encAcc a).length = 2 * (encNat a.1).length + 1 + (encNat a.2).length :=
        length_encPair a
      omega)
    (fun y hy => by
      rcases hy with hy | ⟨v, hv, w, -, rfl⟩
      · have := length_encNat_lt hy; omega
      · have := (hE v hv (wordBits w v.1) (by simp [wordBits])).2.2; omega)
    (P, d) _ _ _ he
  rw [← hn] at hres
  -- The clock and the size of the fuel.
  have hfuel : fuel (P, d) < 2 ^ (d.numEdges + d.vertices.length + 2) := by
    have hk : d.vertices.length + 1 ≤ 2 ^ d.vertices.length := Nat.lt_two_pow_self
    have h1 : 2 ^ d.numEdges * (d.vertices.length + 1) ≤ 2 ^ (d.numEdges + d.vertices.length) :=
      by rw [pow_add]; exact Nat.mul_le_mul_left _ hk
    have h2 : 2 ^ (d.numEdges + d.vertices.length + 2) = 4 * 2 ^ (d.numEdges + d.vertices.length) :=
      by rw [pow_add]; ring
    have h3 := Nat.two_pow_pos (d.numEdges + d.vertices.length)
    simp only [fuel]
    omega
  have hfl := length_encNat_lt hfuel
  obtain ⟨B, hB⟩ : ∃ B, B = 2 ^ d.numEdges * (d.vertices.length + 1) + 1 := ⟨_, rfl⟩
  have hfuel1 : fuel (P, d) + 1 = 2 * B := by rw [hB]; simp only [fuel]; ring
  have hB1 : 1 ≤ B := by omega
  rw [← hB]
  -- The polynomial parts, each at most a constant times `W`.
  have hW1 : z + 1 ≤ W := by
    rw [hW]
    calc z + 1 = (z + 1) ^ 1 := (pow_one _).symm
      _ ≤ (z + 1) ^ D := Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
  have hpoly {c e : ℕ} (he : e ≤ D) : c * (n + 1) ^ e ≤ c * W := by
    rw [hW]
    exact Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (by omega) _).trans
      (Nat.pow_le_pow_right (Nat.succ_pos _) he))
  have hterm {c a b e : ℕ} (he : e ≤ D) : c * (a * z + b) ^ e ≤ c * (a + b) ^ e * W := by
    rw [hW]; exact term_le he
  have hT1 : K₀ * ((h + 1) * (13 * z + 18 + 1)) ^ K₀ ≤ K₀ * 96 ^ K₀ * W := by
    have h3 : (h + 1) * (13 * z + 18 + 1) ≤ 39 * z + 57 := by
      have := Nat.mul_le_mul_right (13 * z + 18 + 1) (show h + 1 ≤ 3 by omega); omega
    exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h3 _)).trans (hterm (by omega))
  have hTL : 2 * cv * (5 * z + 8) ^ dv + 2 * (5 * z + 7) + cq * (11 * z + 16) ^ dq ≤
      (2 * cv * 13 ^ dv + 24 + cq * 27 ^ dq) * W := by
    have a1 := hterm (c := 2 * cv) (a := 5) (b := 8) (show dv ≤ D by omega)
    have a2 := hterm (c := cq) (a := 11) (b := 16) (show dq ≤ D by omega)
    have e : (2 * cv * 13 ^ dv + 24 + cq * 27 ^ dq) * W =
        2 * cv * (5 + 8) ^ dv * W + 24 * W + cq * (11 + 16) ^ dq * W := by ring
    omega
  have hSL : 2 * cv' * (5 * z + 8) ^ dv' + 2 * (5 * z + 7) + cq' * (11 * z + 16) ^ dq' ≤
      (2 * cv' * 13 ^ dv' + 24 + cq' * 27 ^ dq') * W := by
    have a1 := hterm (c := 2 * cv') (a := 5) (b := 8) (show dv' ≤ D by omega)
    have a2 := hterm (c := cq') (a := 11) (b := 16) (show dq' ≤ D by omega)
    have e : (2 * cv' * 13 ^ dv' + 24 + cq' * 27 ^ dq') * W =
        2 * cv' * (5 + 8) ^ dv' * W + 24 * W + cq' * (11 + 16) ^ dq' * W := by ring
    omega
  have hclock : ((encNat (fuel (P, d))).length + 1) ^ 2 ≤ 16 * W := by
    have h3 : (encNat (fuel (P, d))).length + 1 ≤ 4 * (z + 1) := by omega
    calc ((encNat (fuel (P, d))).length + 1) ^ 2 ≤ (4 * (z + 1)) ^ 2 := Nat.pow_le_pow_left h3 2
      _ = 16 * (z + 1) ^ 2 := by ring
      _ ≤ 16 * W := by
          rw [hW]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos _) (by omega))
  have hCD : C * W ≤ (C + D) * (z + 1) ^ (C + D) := by
    rw [hW]; exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (Nat.succ_pos _) (by omega))
  obtain ⟨htime, hspace⟩ := hres
  have hft' := hft (P, d)
  have hrt' := hrt (P, d)
  have hfs' := hfs (P, d)
  have hrs' := hrs (P, d)
  rw [← hn] at hft' hrt' hfs' hrs'
  have hcf := hft'.trans (hpoly (c := cf) (show df ≤ D by omega))
  have hcr := hrt'.trans (hpoly (c := cr) (show dr ≤ D by omega))
  have hcf' := hfs'.trans (hpoly (c := cf') (show df' ≤ D by omega))
  have hcr' := hrs'.trans (hpoly (c := cr') (show dr' ≤ D by omega))
  constructor
  · rw [hfuel1] at htime
    obtain ⟨S, hS⟩ : ∃ S, S = K₀ * ((h + 1) * (13 * z + 18 + 1)) ^ K₀ +
        (2 * cv * (5 * z + 8) ^ dv + 2 * (5 * z + 7) + cq * (11 * z + 16) ^ dq + E) +
        ((encNat (fuel (P, d))).length + 1) ^ 2 := ⟨_, rfl⟩
    rw [← hS] at htime
    have hstep : S ≤ G * W + E := by
      have e : G * W = K₀ * 96 ^ K₀ * W + (2 * cv * 13 ^ dv + 24 + cq * 27 ^ dq) * W + 16 * W := by
        rw [hG]; ring
      omega
    have hm := Nat.mul_le_mul_left (2 * B) hstep
    calc (contractionCertificate eval ev).time (P, d)
        ≤ cf * W + cr * W + 2 * W + 2 * B * (G * W + E) := by
          rw [contractionCertificate_time]; unfold sumCertificate; omega
      _ ≤ B * ((cf + cr + 2) * W) + B * (2 * G * W) + 2 * B * E := by
          have e2 : 2 * B * (G * W + E) = B * (2 * G * W) + 2 * B * E := by ring
          have e3 : cf * W + cr * W + 2 * W = (cf + cr + 2) * W := by ring
          have e4 : (cf + cr + 2) * W ≤ B * ((cf + cr + 2) * W) := Nat.le_mul_of_pos_left _ hB1
          omega
      _ = B * ((cf + cr + 2 + 2 * G) * W) + 2 * B * E := by ring
      _ ≤ B * (C * W) + 2 * B * E :=
          Nat.add_le_add_right (Nat.mul_le_mul_left B (Nat.mul_le_mul_right W (by omega))) _
      _ = B * (C * W + 2 * E) := by ring
      _ ≤ B * ((C + D) * (z + 1) ^ (C + D) + 2 * E) :=
          Nat.mul_le_mul_left _ (Nat.add_le_add_right hCD _)
  · have h1 : (contractionCertificate eval ev).space (P, d) ≤ C * W + ES := by
      rw [contractionCertificate_space]
      unfold sumCertificate
      have e : C * W = cf * W + cr * W + cf' * W + cr' * W + 2 * G * W + G' * W + 4 * W := by
        rw [hC]; ring
      have e' : G' * W = K₀ * 96 ^ K₀ * W + (2 * cv' * 13 ^ dv' + 24 + cq' * 27 ^ dq') * W := by
        rw [hG']; ring
      have hfl' : (encNat (fuel (P, d))).length ≤ W := by omega
      omega
    exact h1.trans (Nat.add_le_add_right hCD _)

end Native

end DescribedNetwork

end Cslib.Circuits.Frontier
