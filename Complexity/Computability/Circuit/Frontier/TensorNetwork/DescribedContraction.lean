/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.Explicit
public import Complexity.Computability.GenericRAM.Native.StackRecursion
public import Complexity.Computability.PolyTime.GaloisRingArithmetic
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
networks are the case of tables (`ExplicitTensorNetwork`, `DescribedNetwork.contraction_entry`).

**Values and their operations** (`SumOps`). The entries are values `Y` combined by ring
operations that depend on a precision `q : Q`: a zero, a one, a sum and a product, whose results
are *reduced* (of bounded size). The two instances are natural numbers modulo `2 ^ P`
(`SumOps.mod`) and the coefficient lists of `A_p = (ℤ / 2 ^ p)[U] / (f)` at the precision
`(p, fl)` (`SumOps.galois`), the coefficient rings of the recursion (Appendix D.4.1, p. 57). A map
of the values into a commutative semiring that takes the operations at `q` to the semiring
operations (`SumOps.IsHom`) takes the computed sum to the contraction of the mapped entries.

**Direct summation as a stack recursion** (`DescribedNetwork.sumScheme`). The sum over the
`2 ^ m` assignments is a call whose children are the assignments, in binary order, added with the
operations; an assignment is a call whose children are the entries of the vertices at its bits,
multiplied with the operations; an entry is a leaf, evaluated by the evaluator. The derivation has
`2 ^ m (k + 1) + 1` nodes for `k` vertices and two open calls, and its value is the fold of the
operations (`DescribedNetwork.sumValue`, `DescribedNetwork.eval_sumRoot`). So a native certificate
of the evaluator, with any bounds, gives one native machine for the sum on every input
(`DescribedNetwork.contractionCertificate`), through
`Cslib.GenericRAM.StackRecursion.Scheme.certificate`. If the evaluator takes time `E`, space `ES`
and outputs at most `Ev` bits on every vertex, and reduced values are at most `Rv` bits, the
machine takes time `2 ^ m (k + 1) + 1` times `K (n + Ev + Rv + 1) ^ K + 2 E` and space
`K (n + Ev + Rv + 1) ^ K + ES` on inputs of length `n`
(`DescribedNetwork.contractionCertificate_le`). Under a homomorphism the value is the contraction
(`DescribedNetwork.SumOps.IsHom.map_sumValue`): modulo `2 ^ P` for natural numbers
(`DescribedNetwork.sumValue_mod`, `DescribedNetwork.modContractionCertificate`), and in `A_p` for
coefficient lists (`DescribedNetwork.val_sumValue_galois`). This is the leaf step of the
contraction algorithm, with implicit packet tensors as descriptors.

## Main definitions

* `Cslib.Circuits.Frontier.SumOps`: ring operations on values, with `SumOps.IsHom` and
  `SumOps.PolyTime`; the instances `SumOps.mod` and `SumOps.galois`.
* `Cslib.Circuits.Frontier.DescribedNetwork.sumScheme`: direct summation as a recursion scheme.
* `Cslib.Circuits.Frontier.DescribedNetwork.sumValue`: its value.
* `Cslib.Circuits.Frontier.DescribedNetwork.encDescribed`: the encoding of a described network.
* `Cslib.Circuits.Frontier.DescribedNetwork.contractionCertificate`: one native machine for the
  sum.

## Main results

* `Cslib.GenericRAM.StackRecursion.Scheme.Loop.counted`: a call whose children are indexed by
  a counter.
* `Cslib.Circuits.Frontier.DescribedNetwork.eval_sumRoot`: direct summation evaluates to
  `sumValue`, with `2 ^ m (k + 1) + 1` nodes and two open calls.
* `Cslib.Circuits.Frontier.SumOps.IsHom.map_sumValue`: under a homomorphism, the value is the
  contraction; `DescribedNetwork.sumValue_mod` and `DescribedNetwork.val_sumValue_galois`.
* `Cslib.Circuits.Frontier.DescribedNetwork.run_sumScheme`: the machine computes `sumValue`.
* `Cslib.Circuits.Frontier.DescribedNetwork.contractionCertificate_le`: its time and space.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Appendix D.4.1 (p. 57)
  and Appendix D.4.6–D.4.7 (pp. 63–64).
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

open Finset Cslib.BitString Cslib.GenericRAM Cslib.GenericRAM.StackRecursion Turing.MultiTapeTM

/-! ### Values and their operations -/

/-- **Ring operations on values** for direct summation: at each precision `q : Q`, a zero, a
one, a sum and a product on the values `Y`, and the *reduced* values at `q`, among which are the
zero, the one and every sum and product. -/
structure SumOps (Q Y : Type) where
  /-- The zero at a precision. -/
  zero : Q → Y
  /-- The one at a precision. -/
  one : Q → Y
  /-- The sum at a precision. -/
  add : Q → Y → Y → Y
  /-- The product at a precision. -/
  mul : Q → Y → Y → Y
  /-- The reduced values at a precision. -/
  Reduced : Q → Y → Prop
  reduced_zero (q : Q) : Reduced q (zero q)
  reduced_one (q : Q) : Reduced q (one q)
  reduced_add (q : Q) (a b : Y) : Reduced q (add q a b)
  reduced_mul (q : Q) (a b : Y) : Reduced q (mul q a b)

namespace SumOps

variable {Q Y : Type} (ops : SumOps Q Y)

/-- A *homomorphism* of the operations at `q`: a map of the values into a commutative semiring
taking the zero, the one, sums and products at `q` to those of the semiring. -/
structure IsHom (q : Q) {R : Type*} [CommSemiring R] (φ : Y → R) : Prop where
  map_zero : φ (ops.zero q) = 0
  map_one : φ (ops.one q) = 1
  map_add (a b : Y) : φ (ops.add q a b) = φ a + φ b
  map_mul (a b : Y) : φ (ops.mul q a b) = φ a * φ b

/-- **Polynomial-time operations**, for encodings of the precisions and the values. -/
structure PolyTime (encQ : Q ↪ List Bool) (encY : Y ↪ List Bool) : Prop where
  zero : ComputableInPolyTime ops.zero encQ encY
  one : ComputableInPolyTime ops.one encQ encY
  add : ComputableInPolyTime (fun z : Q × Y × Y => ops.add z.1 z.2.1 z.2.2)
    (encPair encQ (encPair encY encY)) encY
  mul : ComputableInPolyTime (fun z : Q × Y × Y => ops.mul z.1 z.2.1 z.2.2)
    (encPair encQ (encPair encY encY)) encY

/-- A left fold of the sum or the product from a reduced start is reduced. -/
theorem reduced_foldl {α : Type} (q : Q) (op : Y → Y → Y) (hop : ∀ a b, ops.Reduced q (op a b))
    (f : α → Y) (l : List α) {a : Y} (ha : ops.Reduced q a) :
    ops.Reduced q (l.foldl (fun acc v => op acc (f v)) a) := by
  induction l generalizing a with
  | nil => exact ha
  | cons v l ih => exact ih (hop _ _)

variable {ops}

/-- A homomorphism takes a fold of products to the product of the images. -/
theorem IsHom.map_foldl_mul {q : Q} {R : Type*} [CommSemiring R] {φ : Y → R} (h : ops.IsHom q φ)
    {α : Type} (f : α → Y) (l : List α) (a : Y) :
    φ (l.foldl (fun acc v => ops.mul q acc (f v)) a) = φ a * (l.map fun v => φ (f v)).prod := by
  induction l generalizing a with
  | nil => simp
  | cons v l ih => rw [List.foldl_cons, ih, h.map_mul, List.map_cons, List.prod_cons, mul_assoc]

/-- A homomorphism takes a fold of sums over a range to the sum of the images. -/
theorem IsHom.map_foldl_add {q : Q} {R : Type*} [CommSemiring R] {φ : Y → R} (h : ops.IsHom q φ)
    (g : ℕ → Y) (n : ℕ) (a : Y) :
    φ ((List.range n).foldl (fun acc j => ops.add q acc (g j)) a) =
      φ a + ∑ j ∈ range n, φ (g j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, h.map_add, ih,
      sum_range_succ, add_assoc]

end SumOps

namespace DescribedNetwork

variable {T : Type}

/-! ### Direct summation as a recursion scheme -/

/-- A node of direct summation: its kind (`0` the sum, `1` an assignment, `2` an entry), the
precision and the network, and the current word and vertex index. -/
abbrev Node (Q T : Type) := ℕ × ((Q × DescribedNetwork T) × (List Bool × ℕ))

variable {Q Y : Type} (ops : SumOps Q Y) (eval : T → List Bool → Y)

/-- The entry of a node: the evaluator at the descriptor of its vertex and the bits of its word
on the vertex's ports, or the zero for an index past the vertices. -/
def entryOf (x : Node Q T) : Y :=
  (x.2.1.2.vertices[x.2.2.2]?).elim (ops.zero x.2.1.1) fun v => eval v.2 (wordBits x.2.2.1 v.1)

/-- **Direct summation as a recursion scheme.** The sum (kind `0`) has the `2 ^ m` assignments as
children, adding their values; an assignment (kind `1`) has the entries of the vertices as
children, multiplying them; an entry (kind `2`) is a leaf. The operations are those at the
precision of the node, and the accumulator is a counter and a value. -/
def sumScheme : Scheme (Node Q T) (ℕ × Y) Y where
  isLeaf x := x.1 == 2
  leaf := entryOf ops eval
  start x := (0, if x.1 = 0 then ops.zero x.2.1.1 else ops.one x.2.1.1)
  next x a :=
    if x.1 = 0 then
      (if a.1 < 2 ^ x.2.1.2.numEdges then some (1, (x.2.1, (lowBits x.2.1.2.numEdges a.1, 0)))
        else none)
    else if x.1 = 1 then
      (if a.1 < x.2.1.2.vertices.length then
        some (2, (x.2.1, (x.2.2.1, min x.2.1.2.vertices.length a.1))) else none)
    else none
  absorb x a y :=
    (a.1 + 1, if x.1 = 0 then ops.add x.2.1.1 a.2 y else ops.mul x.2.1.1 a.2 y)
  finish _ a := a.2

/-- The root of direct summation on `(q, d)`. -/
def sumRoot (q : Q × DescribedNetwork T) : Node Q T := (0, (q, ([], 0)))

/-- The weight of a word: the product of the entries at its bits, folded with the operations at
`q`. -/
def weight (q : Q) (d : DescribedNetwork T) (word : List Bool) : Y :=
  d.vertices.foldl (fun acc v => ops.mul q acc (eval v.2 (wordBits word v.1))) (ops.one q)

/-- **The value of direct summation**: the weights of the `2 ^ m` words in binary order, folded
with the sum at `q`. -/
def sumValue (q : Q) (d : DescribedNetwork T) : Y :=
  (List.range (2 ^ d.numEdges)).foldl
    (fun acc j => ops.add q acc (weight ops eval q d (lowBits d.numEdges j))) (ops.zero q)

/-- The shape of a node of direct summation on `q`: it keeps `q`, its kind is at most `2`, its
word has at most `m` bits and its index is at most the number of vertices. -/
def NodeShape (q : Q × DescribedNetwork T) (x : Node Q T) : Prop :=
  x.2.1 = q ∧ x.1 ≤ 2 ∧ x.2.2.1.length ≤ q.2.numEdges ∧ x.2.2.2 ≤ q.2.vertices.length

/-- The invariant of direct summation on `q`: nodes have the shape of `NodeShape`, frames also
have a counter at most `2 ^ m + k` and a reduced value, and every value is reduced or an entry of
a vertex at the bits of an `m`-bit word. -/
def sumInvariant (q : Q × DescribedNetwork T) : Invariant (Node Q T) (ℕ × Y) Y :=
  ⟨NodeShape q, fun x a => NodeShape q x ∧ a.1 ≤ 2 ^ q.2.numEdges + q.2.vertices.length ∧
      ops.Reduced q.1 a.2,
    fun y => ops.Reduced q.1 y ∨ ∃ v ∈ q.2.vertices, ∃ w : List Bool, w.length = q.2.numEdges ∧
      y = eval v.2 (wordBits w v.1)⟩

variable {ops eval}

/-- An entry is a leaf. -/
theorem eval_entry (q : Q × DescribedNetwork T) {word : List Bool} {v : ℕ}
    (hw : word.length = q.2.numEdges) (hv : v < q.2.vertices.length) :
    (sumScheme ops eval).Eval (sumInvariant ops eval q) (2, (q, (word, v)))
      (entryOf ops eval (2, (q, (word, v)))) 1 0 := by
  refine Scheme.Eval.leaf (R := sumScheme ops eval) ⟨rfl, by omega, hw.le, hv.le⟩ rfl
    (.inr ⟨q.2.vertices[v], List.getElem_mem hv, word, hw, ?_⟩)
  change (q.2.vertices[v]?).elim _ _ = _
  rw [List.getElem?_eq_getElem hv]
  rfl

private theorem foldl_take_succ (q : Q) (d : DescribedNetwork T) (word : List Bool) (c : ℕ)
    (hc : c < d.vertices.length) :
    (d.vertices.take (c + 1)).foldl (fun acc v => ops.mul q acc (eval v.2 (wordBits word v.1)))
        (ops.one q) =
      ops.mul q ((d.vertices.take c).foldl
        (fun acc v => ops.mul q acc (eval v.2 (wordBits word v.1))) (ops.one q))
        (entryOf ops eval (2, ((q, d), (word, c)))) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hc, Option.toList_some, List.foldl_append]
  simp [entryOf, List.getElem?_eq_getElem hc]

/-- **An assignment evaluates to the weight of its word**, with one node per vertex plus one
and one open call. -/
theorem eval_assign (q : Q) (d : DescribedNetwork T) {word : List Bool}
    (hw : word.length = d.numEdges) :
    ∃ h ≤ 1, (sumScheme ops eval).Eval (sumInvariant ops eval (q, d)) (1, ((q, d), (word, 0)))
      (weight ops eval q d word) (d.vertices.length + 1) h := by
  set acc : ℕ → ℕ × Y := fun c => (c, (d.vertices.take c).foldl
    (fun acc v => ops.mul q acc (eval v.2 (wordBits word v.1))) (ops.one q))
  have hshape : NodeShape (q, d) ((1, ((q, d), (word, 0))) : Node Q T) :=
    ⟨rfl, by omega, hw.le, Nat.zero_le _⟩
  have hred (c : ℕ) : ops.Reduced q (acc c).2 :=
    ops.reduced_foldl q _ (ops.reduced_mul q) _ _ (ops.reduced_one q)
  obtain ⟨h, hh, hloop⟩ := Scheme.Loop.counted (R := sumScheme ops eval)
    (I := sumInvariant ops eval (q, d))
    (x := (1, ((q, d), (word, 0)))) (acc := acc)
    (child := fun c => (2, ((q, d), (word, c))))
    (val := fun c => entryOf ops eval (2, ((q, d), (word, c))))
    (nodes := fun _ => 1) (height := fun _ => 0) d.vertices.length 0
    (fun c hc => by simp [sumScheme, acc, hc, min_eq_right hc.le])
    (by simp [sumScheme, acc])
    (fun c hc => by
      simp only [sumScheme, acc, one_ne_zero, ite_false]
      rw [foldl_take_succ q d word c hc])
    (fun c hc => eval_entry (q, d) hw hc)
    (fun c hc => ⟨hshape, (Nat.le_of_lt hc).trans (Nat.le_add_left _ _), hred c⟩)
    (fun _ _ => le_rfl)
  have hstart : (sumScheme ops eval).start (1, ((q, d), (word, 0))) = acc 0 := by
    simp [sumScheme, acc]
  rw [← hstart] at hloop
  refine ⟨h + 1, by omega, ?_⟩
  have := Scheme.Eval.call (R := sumScheme ops eval) (I := sumInvariant ops eval (q, d))
    (x := (1, ((q, d), (word, 0)))) hshape rfl hloop (.inl (hred d.vertices.length))
  simpa [sumScheme, acc, weight, List.take_length, Finset.sum_const, Finset.card_range] using
    this

private theorem sum_lowBits {M : Type*} [AddCommMonoid M] (n : ℕ) (g : List Bool → M) :
    ∑ j ∈ range (2 ^ n), g (lowBits n j) = ∑ x : Fin n → Bool, g (List.ofFn x) := by
  rw [← Fin.sum_univ_eq_sum_range]
  exact Fintype.sum_equiv (equivFin n).symm _ _ fun k => by
    rw [lowBits_eq_ofFn_equivFin_symm]

/-- **Direct summation computes `sumValue`**, with `2 ^ m (k + 1) + 1` nodes for `m` edges and
`k` vertices, and at most two open calls. -/
theorem eval_sumRoot (q : Q) (d : DescribedNetwork T) :
    ∃ h ≤ 2, (sumScheme ops eval).Eval (sumInvariant ops eval (q, d)) (sumRoot (q, d))
      (sumValue ops eval q d) (2 ^ d.numEdges * (d.vertices.length + 1) + 1) h := by
  set acc : ℕ → ℕ × Y := fun c => (c, (List.range c).foldl
    (fun acc j => ops.add q acc (weight ops eval q d (lowBits d.numEdges j))) (ops.zero q))
  have hassign (c : ℕ) := eval_assign (ops := ops) (eval := eval) q d
    (length_lowBits d.numEdges c)
  choose hgt hhgt heval using hassign
  have hshape : NodeShape (q, d) (sumRoot (q, d)) := ⟨rfl, by simp [sumRoot], by simp [sumRoot],
    by simp [sumRoot]⟩
  have hred (c : ℕ) : ops.Reduced q (acc c).2 :=
    ops.reduced_foldl q _ (ops.reduced_add q) _ _ (ops.reduced_zero q)
  obtain ⟨h, hh, hloop⟩ := Scheme.Loop.counted (R := sumScheme ops eval)
    (I := sumInvariant ops eval (q, d))
    (x := sumRoot (q, d)) (acc := acc)
    (child := fun c => (1, ((q, d), (lowBits d.numEdges c, 0))))
    (val := fun c => weight ops eval q d (lowBits d.numEdges c))
    (nodes := fun _ => d.vertices.length + 1) (height := hgt) (2 ^ d.numEdges) 1
    (fun c hc => by simp [sumScheme, sumRoot, acc, hc])
    (by simp [sumScheme, sumRoot, acc])
    (fun c hc => by
      simp only [sumScheme, sumRoot, acc, ite_true, List.range_succ, List.foldl_append,
        List.foldl_cons, List.foldl_nil])
    (fun c _ => heval c)
    (fun c hc => ⟨hshape, by simp only [acc]; omega, hred c⟩)
    (fun c _ => hhgt c)
  have hstart : (sumScheme ops eval).start (sumRoot (q, d)) = acc 0 := by
    simp [sumScheme, sumRoot, acc]
  rw [← hstart] at hloop
  refine ⟨h + 1, by omega, ?_⟩
  have := Scheme.Eval.call (R := sumScheme ops eval) (I := sumInvariant ops eval (q, d))
    (x := sumRoot (q, d)) hshape rfl hloop (.inl (hred (2 ^ d.numEdges)))
  rw [sum_const, card_range, smul_eq_mul] at this
  exact this

/-- `sumValue` is reduced. -/
theorem reduced_sumValue (q : Q) (d : DescribedNetwork T) : ops.Reduced q (sumValue ops eval q d) :=
  ops.reduced_foldl q _ (ops.reduced_add q) _ _ (ops.reduced_zero q)

/-- **Under a homomorphism, the value is the contraction** of the mapped entries. -/
theorem _root_.Cslib.Circuits.Frontier.SumOps.IsHom.map_sumValue {q : Q} {R : Type*}
    [CommSemiring R] {φ : Y → R} (h : ops.IsHom q φ) (d : DescribedNetwork T) :
    φ (sumValue ops eval q d) = d.contraction fun t bs => φ (eval t bs) := by
  rw [sumValue, h.map_foldl_add, h.map_zero, zero_add, contraction,
    sum_lowBits d.numEdges (fun w => φ (weight ops eval q d w))]
  refine sum_congr rfl fun x _ => ?_
  rw [weight, h.map_foldl_mul, h.map_one, one_mul]

/-! ### Natural numbers modulo a power of two -/

/-- **Natural numbers modulo `2 ^ P`**, with the precision `P`; the reduced values are those
below `2 ^ P`. -/
def _root_.Cslib.Circuits.Frontier.SumOps.mod : SumOps ℕ ℕ where
  zero _ := 0
  one P := 1 % 2 ^ P
  add P a b := (a + b) % 2 ^ P
  mul P a b := a * b % 2 ^ P
  Reduced P y := y < 2 ^ P
  reduced_zero P := Nat.two_pow_pos P
  reduced_one P := Nat.mod_lt _ (Nat.two_pow_pos P)
  reduced_add P _ _ := Nat.mod_lt _ (Nat.two_pow_pos P)
  reduced_mul P _ _ := Nat.mod_lt _ (Nat.two_pow_pos P)

/-- The cast into `ZMod (2 ^ P)` is a homomorphism of the operations at `P`. -/
theorem _root_.Cslib.Circuits.Frontier.SumOps.mod_isHom (P : ℕ) :
    SumOps.mod.IsHom P (Nat.cast : ℕ → ZMod (2 ^ P)) where
  map_zero := Nat.cast_zero
  map_one := by simp only [SumOps.mod, ZMod.natCast_mod, Nat.cast_one]
  map_add a b := by simp only [SumOps.mod, ZMod.natCast_mod, Nat.cast_add]
  map_mul a b := by simp only [SumOps.mod, ZMod.natCast_mod, Nat.cast_mul]

/-- **Modulo `2 ^ P`, the value is the contraction modulo `2 ^ P`.** -/
theorem sumValue_mod (eval : T → List Bool → ℕ) (P : ℕ) (d : DescribedNetwork T) :
    sumValue SumOps.mod eval P d = d.contraction eval % 2 ^ P := by
  have h := (SumOps.mod_isHom P).map_sumValue (eval := eval) d
  have h2 : ((d.contraction eval : ℕ) : ZMod (2 ^ P)) =
      d.contraction fun t bs => ((eval t bs : ℕ) : ZMod (2 ^ P)) :=
    map_contraction (Nat.castRingHom (ZMod (2 ^ P))) eval d
  have h' := congrArg ZMod.val (h.trans h2.symm)
  rwa [ZMod.val_cast_of_lt (reduced_sumValue (ops := SumOps.mod) P d), ZMod.val_natCast] at h'

/-! ### Coefficient lists of `(ℤ / 2 ^ p)[U] / (f)` -/

/-- **Coefficient lists of `A_p = (ℤ / 2 ^ p)[U] / (f)`**, with the precision `(p, fl)` and the
operations of `GaloisRingArith`; the reduced values have `e = fl.length` coordinates, each at most
`2 ^ p`. -/
def _root_.Cslib.Circuits.Frontier.SumOps.galois : SumOps (ℕ × List ℕ) (List ℕ) where
  zero q := GaloisRingArith.zero q.2
  one q := GaloisRingArith.one q.2
  add q := GaloisRingArith.add q.1 q.2
  mul q := GaloisRingArith.mul q.1 q.2
  Reduced q c := c.length = q.2.length ∧ ∀ x ∈ c, x ≤ 2 ^ q.1
  reduced_zero q := ⟨GaloisRingArith.length_zero _, fun x hx => by
    simp only [GaloisRingArith.zero, List.mem_map] at hx
    obtain ⟨_, -, rfl⟩ := hx
    exact Nat.zero_le _⟩
  reduced_one q := ⟨by simp [GaloisRingArith.one], fun x hx => by
    simp only [GaloisRingArith.one, List.mem_map] at hx
    obtain ⟨i, -, rfl⟩ := hx
    split_ifs
    · exact Nat.one_le_two_pow
    · exact Nat.zero_le _⟩
  reduced_add q _ _ := ⟨GaloisRingArith.length_add _ _ _ _,
    fun _ hx => (GaloisRingArith.lt_of_mem_add hx).le⟩
  reduced_mul q _ _ := ⟨GaloisRingArith.length_mul _ _ _ _,
    fun _ hx => (GaloisRingArith.lt_of_mem_mul hx).le⟩

/-- The value in `A_p` is a homomorphism of the operations at `(p, fl)`. -/
theorem _root_.Cslib.Circuits.Frontier.SumOps.galois_isHom (q : ℕ × List ℕ) :
    SumOps.galois.IsHom q (GaloisRingArith.val q.1 q.2) where
  map_zero := GaloisRingArith.val_zero
  map_one := GaloisRingArith.val_one
  map_add := GaloisRingArith.val_add
  map_mul := GaloisRingArith.val_mul

/-- **In `A_p`, the value is the contraction** of the values of the entries. -/
theorem val_sumValue_galois (eval : T → List Bool → List ℕ) (q : ℕ × List ℕ)
    (d : DescribedNetwork T) :
    GaloisRingArith.val q.1 q.2 (sumValue SumOps.galois eval q d) =
      d.contraction fun t bs => GaloisRingArith.val q.1 q.2 (eval t bs) :=
  (SumOps.galois_isHom q).map_sumValue d

/-- A reduced coefficient list at `(p, fl)` is at most `e (2 p + 3)` long in binary, with
`e = fl.length`. -/
theorem _root_.Cslib.Circuits.Frontier.SumOps.length_encList_le_of_galois_reduced
    {q : ℕ × List ℕ} {c : List ℕ} (hc : SumOps.galois.Reduced q c) :
    (encList encNat c).length ≤ q.2.length * (2 * q.1 + 3) := by
  obtain ⟨hlen, hle⟩ := hc
  have := GaloisRingArith.length_encList_le (p := q.1 + 1) hlen fun x hx =>
    (hle x hx).trans_lt (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _))
  calc (encList encNat c).length ≤ q.2.length * (2 * (q.1 + 1) + 1) := this
    _ = q.2.length * (2 * q.1 + 3) := by ring

/-! ### The native machine -/

section Native

variable (encQ : Q ↪ List Bool) (encY : Y ↪ List Bool) (encT : T ↪ List Bool)

/-- **The encoding of a described network**: its number of edges in unary, then its vertices,
each the pair of its list of ports in binary and its descriptor. -/
def encDescribed : DescribedNetwork T ↪ List Bool :=
  encOfEquiv equivProd (encPair encUnary (encList (encPair (encList encNat) encT)))

/-- The encoding of an input `(q, d)`: the precision and the network. -/
abbrev encInput : Q × DescribedNetwork T ↪ List Bool := encPair encQ (encDescribed encT)

/-- The encoding of a node: its kind in unary, its input, its word and its vertex index in
unary. -/
abbrev encNode : Node Q T ↪ List Bool :=
  encPair encUnary (encPair (encInput encQ encT) (encPair encBits encUnary))

/-- The encoding of an accumulator: the counter in binary and the value. -/
abbrev encAcc : ℕ × Y ↪ List Bool := encPair encNat encY

variable {encQ encY encT}

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
theorem kind_polyTime : ComputableInPolyTime (fun x : Node Q T => x.1) (encNode encQ encT)
    encUnary := ComputableInPolyTime.fst _ _

/-- The input `(q, d)` of a node. -/
theorem input_polyTime : ComputableInPolyTime (fun x : Node Q T => x.2.1) (encNode encQ encT)
    (encInput encQ encT) := (ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.snd _ _)

/-- The precision of a node. -/
theorem precision_polyTime : ComputableInPolyTime (fun x : Node Q T => x.2.1.1)
    (encNode encQ encT) encQ := (ComputableInPolyTime.fst _ _).comp input_polyTime

/-- The network of a node. -/
theorem network_polyTime : ComputableInPolyTime (fun x : Node Q T => x.2.1.2)
    (encNode encQ encT) (encDescribed encT) := (ComputableInPolyTime.snd _ _).comp input_polyTime

/-- The word of a node. -/
theorem word_polyTime : ComputableInPolyTime (fun x : Node Q T => x.2.2.1)
    (encNode encQ encT) encBits :=
  (ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.snd _ _).snd'

/-- The vertex index of a node. -/
theorem index_polyTime : ComputableInPolyTime (fun x : Node Q T => x.2.2.2)
    (encNode encQ encT) encUnary :=
  (ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.snd _ _).snd'

/-- `2 ^ P`, from `P` in unary. -/
private theorem twoPow {α : Type} {encIn : α ↪ List Bool} {P : α → ℕ}
    (hP : ComputableInPolyTime P encIn encUnary) :
    ComputableInPolyTime (fun a => 2 ^ P a) encIn encNat :=
  ComputableInPolyTime.binary_two_pow.comp hP

/-- **The polynomial-time components of direct summation**, from polynomial-time operations. -/
theorem sumScheme_polyTime (hops : ops.PolyTime encQ encY) :
    (sumScheme ops eval).PolyTime (encNode encQ encT) (encAcc encY) encY where
  isLeaf := ComputableInPolyTime.beq kind_polyTime (ComputableInPolyTime.const 2)
  start := by
    refine (ComputableInPolyTime.const 0).prod ?_
    exact (ComputableInPolyTime.ite (ComputableInPolyTime.beq kind_polyTime
      (ComputableInPolyTime.const 0)) (hops.zero.comp precision_polyTime)
      (hops.one.comp precision_polyTime)).of_enc_eq fun x => by
        by_cases h : x.1 = 0 <;> simp [h]
  next := by
    have hx := ComputableInPolyTime.fst (encNode encQ encT) (encAcc encY)
    have ha := ComputableInPolyTime.snd (encNode encQ encT) (encAcc encY)
    have hk := kind_polyTime.comp hx
    have hc := (ComputableInPolyTime.fst encNat encY).comp ha
    have hq := input_polyTime.comp hx
    have hd := network_polyTime.comp hx
    have hm := numEdges_polyTime.comp hd
    have hlen := (ComputableInPolyTime.length_list _).comp (vertices_polyTime.comp hd)
    have hassign : ComputableInPolyTime (fun p : Node Q T × (ℕ × Y) =>
        (if p.2.1 < 2 ^ p.1.2.1.2.numEdges then
          some ((1, (p.1.2.1, (lowBits p.1.2.1.2.numEdges p.2.1, 0))) : Node Q T) else none))
        (encPair (encNode encQ encT) (encAcc encY)) (encOption (encNode encQ encT)) :=
      (ComputableInPolyTime.ite (ComputableInPolyTime.binary_lt' hc (twoPow hm))
        ((ComputableInPolyTime.optionSome (encNode encQ encT)).comp
          ((ComputableInPolyTime.const (encOut := encUnary) 1).prod
          (hq.prod ((BooleanFold.decoder_polyTime.comp (hm.prod hc)).prod
            (ComputableInPolyTime.const (encOut := encUnary) 0)))))
        (ComputableInPolyTime.const none)).of_enc_eq fun p => by
          by_cases h : p.2.1 < 2 ^ p.1.2.1.2.numEdges <;> simp [h]
    have hentry : ComputableInPolyTime (fun p : Node Q T × (ℕ × Y) =>
        (if p.2.1 < p.1.2.1.2.vertices.length then
          some ((2, (p.1.2.1, (p.1.2.2.1, min p.1.2.1.2.vertices.length p.2.1))) : Node Q T)
          else none))
        (encPair (encNode encQ encT) (encAcc encY)) (encOption (encNode encQ encT)) :=
      (ComputableInPolyTime.ite (ComputableInPolyTime.binary_lt' hc
          (ComputableInPolyTime.unary_to_binary.comp hlen))
        ((ComputableInPolyTime.optionSome (encNode encQ encT)).comp
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
    have hx := (ComputableInPolyTime.fst (encNode encQ encT) (encAcc encY)).comp
      (ComputableInPolyTime.fst (encPair (encNode encQ encT) (encAcc encY)) encY)
    have ha := (ComputableInPolyTime.snd (encNode encQ encT) (encAcc encY)).comp
      (ComputableInPolyTime.fst (encPair (encNode encQ encT) (encAcc encY)) encY)
    have hy := ComputableInPolyTime.snd (encPair (encNode encQ encT) (encAcc encY)) encY
    have hc := (ComputableInPolyTime.fst encNat encY).comp ha
    have hr := (ComputableInPolyTime.snd encNat encY).comp ha
    have hP := precision_polyTime.comp hx
    refine (ComputableInPolyTime.binary_add.comp (hc.prod (ComputableInPolyTime.const 1))).prod
      ((ComputableInPolyTime.ite (ComputableInPolyTime.beq (kind_polyTime.comp hx)
        (ComputableInPolyTime.const 0))
        (hops.add.comp (hP.prod (hr.prod hy)))
        (hops.mul.comp (hP.prod (hr.prod hy)))).of_enc_eq fun q => ?_)
    by_cases h : q.1.1.1 = 0 <;> simp [h]
  finish := (ComputableInPolyTime.snd encNat encY).comp (ComputableInPolyTime.snd _ _)

/-- The descriptor of a vertex and the bits of the node's word on its ports. -/
theorem query_polyTime :
    ComputableInPolyTime (fun p : Node Q T × (List ℕ × T) => (p.2.2, wordBits p.1.2.2.1 p.2.1))
      (encPair (encNode encQ encT) (encPair (encList encNat) encT)) (encPair encT encBits) := by
  have hv := ComputableInPolyTime.snd (encNode encQ encT) (encPair (encList encNat) encT)
  have hports := (ComputableInPolyTime.fst (encList encNat) encT).comp hv
  have hword := word_polyTime.comp (ComputableInPolyTime.fst (encNode encQ encT)
    (encPair (encList encNat) encT))
  let E := encPair (encNode encQ encT) (encPair (encList encNat) encT)
  have hbit : ComputableInPolyTime (fun z : (Node Q T × (List ℕ × T)) × ℕ =>
      z.1.1.2.2.1.getD z.2 false) (encPair E encNat) encBool :=
    ComputableInPolyTime.listGetD_binary (encA := encBool) (encL := encBits) false
      (hword.comp (ComputableInPolyTime.fst E encNat)) (ComputableInPolyTime.snd E encNat)
  have hbits := ComputableInPolyTime.listToBits.comp
    (ComputableInPolyTime.mapWithInput (f := fun p i => p.1.2.2.1.getD i false) hports hbit)
  exact ((ComputableInPolyTime.snd (encList encNat) encT).comp hv).prod hbits

/-- The vertex of a node, if its index is in range. -/
noncomputable def vertexCertificate :
    NativeCertificate (fun x : Node Q T => x.2.1.2.vertices[x.2.2.2]?) (encNode encQ encT)
      (encOption (encPair (encList encNat) encT)) :=
  NativeCertificate.ofPolyTime (ComputableInPolyTime.getElem?
    (vertices_polyTime.comp network_polyTime) index_polyTime)

/-- The query to the evaluator: the descriptor and the bits on the ports. -/
noncomputable def queryCertificate :
    NativeCertificate (fun p : Node Q T × (List ℕ × T) => (p.2.2, wordBits p.1.2.2.1 p.2.1))
      (encPair (encNode encQ encT) (encPair (encList encNat) encT)) (encPair encT encBits) :=
  NativeCertificate.ofPolyTime query_polyTime

/-- The zero at the precision of a node. -/
noncomputable def zeroCertificate (hops : ops.PolyTime encQ encY) :
    NativeCertificate (fun x : Node Q T => ops.zero x.2.1.1) (encNode encQ encT) encY :=
  NativeCertificate.ofPolyTime (hops.zero.comp precision_polyTime)

variable (eval) in
/-- **The leaf step**: the evaluator at the descriptor of the node's vertex and its bits, from a
native certificate of the evaluator with any bounds. -/
noncomputable def leafCertificate (hops : ops.PolyTime encQ encY)
    (ev : NativeCertificate (fun q : T × List Bool => eval q.1 q.2) (encPair encT encBits) encY) :
    NativeCertificate (sumScheme ops eval).leaf (encNode encQ encT) encY :=
  NativeCertificate.option (value := fun x : Node Q T => x.2.1.2.vertices[x.2.2.2]?)
    (fallback := fun x => ops.zero x.2.1.1) (body := fun p => eval p.2.2 (wordBits p.1.2.2.1 p.2.1))
    vertexCertificate (zeroCertificate hops) (ev.comp queryCertificate)

/-- The time of the leaf step: the vertex lookup, and the zero or the query and the evaluator at
a vertex. -/
theorem leafCertificate_time (hops : ops.PolyTime encQ encY)
    (ev : NativeCertificate (fun q : T × List Bool => eval q.1 q.2) (encPair encT encBits) encY)
    (x : Node Q T) :
    (leafCertificate eval hops ev).time x =
      2 * (vertexCertificate (encQ := encQ) (encT := encT)).time x + (encNode encQ encT x).length +
      (x.2.1.2.vertices[x.2.2.2]?).elim ((zeroCertificate (encT := encT) hops).time x)
        fun v => (queryCertificate (encQ := encQ) (encT := encT)).time (x, v) +
          ev.time (v.2, wordBits x.2.2.1 v.1) := rfl

/-- The space of the leaf step. -/
theorem leafCertificate_space (hops : ops.PolyTime encQ encY)
    (ev : NativeCertificate (fun q : T × List Bool => eval q.1 q.2) (encPair encT encBits) encY)
    (x : Node Q T) :
    (leafCertificate eval hops ev).space x =
      2 * (vertexCertificate (encQ := encQ) (encT := encT)).space x + (encNode encQ encT x).length +
      (x.2.1.2.vertices[x.2.2.2]?).elim ((zeroCertificate (encT := encT) hops).space x)
        fun v => (queryCertificate (encQ := encQ) (encT := encT)).space (x, v) +
          ev.space (v.2, wordBits x.2.2.1 v.1) := rfl

/-- The number of steps of direct summation: `2 (2 ^ m (k + 1) + 1) - 1`. -/
def fuel (q : Q × DescribedNetwork T) : ℕ :=
  2 * (2 ^ q.2.numEdges * (q.2.vertices.length + 1)) + 1

/-- The fuel in polynomial time. -/
theorem fuel_polyTime : ComputableInPolyTime (fuel (Q := Q) (T := T)) (encInput encQ encT)
    encNat := by
  have hd := ComputableInPolyTime.snd encQ (encDescribed encT)
  have hm := numEdges_polyTime.comp hd
  have hlen := (ComputableInPolyTime.length_list _).comp (vertices_polyTime.comp hd)
  exact ComputableInPolyTime.binary_add.comp ((ComputableInPolyTime.binary_mul'
    (ComputableInPolyTime.const 2) (ComputableInPolyTime.binary_mul' (twoPow hm)
      (ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.unary_add' hlen
        (ComputableInPolyTime.const 1))))).prod (ComputableInPolyTime.const 1))

/-- The root in polynomial time. -/
theorem sumRoot_polyTime : ComputableInPolyTime (sumRoot (Q := Q) (T := T)) (encInput encQ encT)
    (encNode encQ encT) :=
  (ComputableInPolyTime.const 0).prod (ComputableInPolyTime.id'.prod
    (ComputableInPolyTime.const ([], 0)))

variable (eval) in
/-- **One native machine for direct summation over described networks**, from polynomial-time
operations and a native certificate of the evaluator. It returns `some (sumValue ops eval q d)`
(`run_sumScheme`). -/
noncomputable def sumCertificate (hops : ops.PolyTime encQ encY)
    (ev : NativeCertificate (fun q : T × List Bool => eval q.1 q.2) (encPair encT encBits) encY) :
    NativeCertificate ((sumScheme ops eval).run fuel sumRoot) (encInput encQ encT)
      (encOption encY) :=
  Scheme.certificate (sumScheme_polyTime hops) (leafCertificate eval hops ev)
    (NativeCertificate.ofPolyTime fuel_polyTime) (NativeCertificate.ofPolyTime sumRoot_polyTime)

/-- **The machine computes `sumValue`.** -/
theorem run_sumScheme (q : Q × DescribedNetwork T) :
    (sumScheme ops eval).run fuel sumRoot q = some (sumValue ops eval q.1 q.2) := by
  obtain ⟨h, -, he⟩ := eval_sumRoot (ops := ops) (eval := eval) q.1 q.2
  exact Scheme.run_eq_some he (by simp [fuel]; omega)

variable (eval) in
/-- **Direct summation over described networks, as a native certificate** for `sumValue` on
every input `(q, d)`, from polynomial-time operations and a native certificate of the
evaluator. -/
noncomputable def contractionCertificate [Inhabited Y] (hops : ops.PolyTime encQ encY)
    (ev : NativeCertificate (fun q : T × List Bool => eval q.1 q.2) (encPair encT encBits) encY) :
    NativeCertificate (fun q : Q × DescribedNetwork T => sumValue ops eval q.1 q.2)
      (encInput encQ encT) encY :=
  (NativeCertificate.post (sumCertificate eval hops ev)
    (ComputableInDegree.getD (enc₁ := encY) (enc := encOption encY) default).inO_one).congr
    fun q => by simp [run_sumScheme]

/-- The time is that of the stack machine. -/
@[simp] theorem contractionCertificate_time [Inhabited Y] (hops : ops.PolyTime encQ encY)
    (ev : NativeCertificate (fun q : T × List Bool => eval q.1 q.2) (encPair encT encBits) encY) :
    (contractionCertificate eval hops ev).time = (sumCertificate eval hops ev).time := rfl

/-- The space is that of the stack machine. -/
@[simp] theorem contractionCertificate_space [Inhabited Y] (hops : ops.PolyTime encQ encY)
    (ev : NativeCertificate (fun q : T × List Bool => eval q.1 q.2) (encPair encT encBits) encY) :
    (contractionCertificate eval hops ev).space = (sumCertificate eval hops ev).space := rfl

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
theorem length_encNode_le {q : Q × DescribedNetwork T} {x : Node Q T} (hx : NodeShape q x) :
    (encNode encQ encT x).length ≤ 5 * (encInput encQ encT q).length + 7 := by
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
an input `(q, d)` of length `n` with `m` edges and `k` vertices, if the evaluator takes time at
most `E` and space at most `ES` and outputs at most `Ev` bits on every vertex and every list of
bits on its ports, and the reduced values at `q` are at most `Rv` bits, then the time is at most
`2 ^ m (k + 1) + 1` times `K (n + Ev + Rv + 1) ^ K + 2 E`, and the space at most
`K (n + Ev + Rv + 1) ^ K + ES`. -/
theorem contractionCertificate_le [Inhabited Y] (hops : ops.PolyTime encQ encY)
    (ev : NativeCertificate (fun q : T × List Bool => eval q.1 q.2) (encPair encT encBits) encY) :
    ∃ K : ℕ, ∀ (q : Q × DescribedNetwork T) (E ES Ev Rv : ℕ),
      (∀ v ∈ q.2.vertices, ∀ bs : List Bool, bs.length = v.1.length →
        ev.time (v.2, bs) ≤ E ∧ ev.space (v.2, bs) ≤ ES ∧ (encY (eval v.2 bs)).length ≤ Ev) →
      (∀ y, ops.Reduced q.1 y → (encY y).length ≤ Rv) →
      (contractionCertificate eval hops ev).time q ≤
          (2 ^ q.2.numEdges * (q.2.vertices.length + 1) + 1) *
            (K * ((encInput encQ encT q).length + Ev + Rv + 1) ^ K + 2 * E) ∧
        (contractionCertificate eval hops ev).space q ≤
          K * ((encInput encQ encT q).length + Ev + Rv + 1) ^ K + ES := by
  obtain ⟨K₀, hK₀⟩ := Scheme.certificate_le
    (sumScheme_polyTime (ops := ops) (eval := eval) (encT := encT) hops)
    (leafCertificate eval hops ev)
  have hV : (vertexCertificate (encQ := encQ) (encT := encT)).IsPolynomial :=
    NativeCertificate.ofPolyTime_isPolynomial _
  have hQ : (queryCertificate (encQ := encQ) (encT := encT)).IsPolynomial :=
    NativeCertificate.ofPolyTime_isPolynomial _
  have hZ : (zeroCertificate (encT := encT) hops).IsPolynomial :=
    NativeCertificate.ofPolyTime_isPolynomial _
  have hF := NativeCertificate.ofPolyTime_isPolynomial (fuel_polyTime (encQ := encQ) (encT := encT))
  have hR := NativeCertificate.ofPolyTime_isPolynomial
    (sumRoot_polyTime (encQ := encQ) (encT := encT))
  obtain ⟨cv, dv, hvt⟩ := hV.1.exists_le
  obtain ⟨cv', dv', hvs⟩ := hV.2.exists_le
  obtain ⟨cq, dq, hqt⟩ := hQ.1.exists_le
  obtain ⟨cq', dq', hqs⟩ := hQ.2.exists_le
  obtain ⟨cz, dz, hzt⟩ := hZ.1.exists_le
  obtain ⟨cz', dz', hzs⟩ := hZ.2.exists_le
  obtain ⟨cf, df, hft⟩ := hF.1.exists_le
  obtain ⟨cf', df', hfs⟩ := hF.2.exists_le
  obtain ⟨cr, dr, hrt⟩ := hR.1.exists_le
  obtain ⟨cr', dr', hrs⟩ := hR.2.exists_le
  obtain ⟨D, hD⟩ : ∃ D, D = K₀ + dv + dv' + dq + dq' + dz + dz' + df + df' + dr + dr' + 2 :=
    ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = K₀ * 96 ^ K₀ +
      (2 * cv * 13 ^ dv + 12 + cz * 13 ^ dz + cq * 27 ^ dq) + 16 := ⟨_, rfl⟩
  obtain ⟨G', hG'⟩ : ∃ G', G' = K₀ * 96 ^ K₀ +
      (2 * cv' * 13 ^ dv' + 12 + cz' * 13 ^ dz' + cq' * 27 ^ dq') := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = cf + cr + cf' + cr' + 2 * G + G' + 4 := ⟨_, rfl⟩
  refine ⟨C + D, fun q E ES Ev Rv hE hRv => ?_⟩
  obtain ⟨P, d⟩ := q
  obtain ⟨n, hn⟩ : ∃ n, n = (encInput encQ encT (P, d)).length := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z, z = n + Ev + Rv := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, W = (z + 1) ^ D := ⟨_, rfl⟩
  rw [← hn]
  rw [show n + Ev + Rv + 1 = z + 1 by omega]
  have hnP : 2 * (encQ P).length + 1 + (encDescribed encT d).length = n := by
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
  have hnode (x : Node Q T) (hx : (sumInvariant ops eval (P, d)).node x) :
      (encNode encQ encT x).length ≤ 5 * z + 7 := (length_encNode_le hx).trans (by omega)
  have hleafT (x : Node Q T) (hx : (sumInvariant ops eval (P, d)).node x) :
      (leafCertificate eval hops ev).time x ≤ 2 * cv * (5 * z + 8) ^ dv + (5 * z + 7) +
        cz * (5 * z + 8) ^ dz + cq * (11 * z + 16) ^ dq + E := by
    have h1 := hnode x hx
    rw [leafCertificate_time]
    have h2 : (vertexCertificate (encQ := encQ) (encT := encT)).time x ≤
        cv * (5 * z + 8) ^ dv :=
      (hvt x).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
    have h2' : 2 * (vertexCertificate (encQ := encQ) (encT := encT)).time x ≤
        2 * cv * (5 * z + 8) ^ dv := by
      rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left 2 h2
    cases hvx : x.2.1.2.vertices[x.2.2.2]? with
    | none =>
      simp only [Option.elim]
      have h3 : (zeroCertificate (encT := encT) hops).time x ≤ cz * (5 * z + 8) ^ dz :=
        (hzt x).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
      omega
    | some v =>
      simp only [Option.elim]
      have hmem : v ∈ x.2.1.2.vertices := List.mem_of_getElem? hvx
      obtain ⟨hq, -, -, -⟩ := hx
      rw [hq] at hmem
      have h3 := hvlen v hmem
      have h4 : (queryCertificate (encQ := encQ) (encT := encT)).time (x, v) ≤
          cq * (11 * z + 16) ^ dq := by
        refine (hqt (x, v)).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _))
        have := length_encPair (enc₁ := encNode encQ encT)
          (enc₂ := encPair (encList encNat) encT) (x, v)
        dsimp only at this
        omega
      have h5 := (hE v hmem (wordBits x.2.2.1 v.1) (by simp [wordBits])).1
      omega
  have hleafS (x : Node Q T) (hx : (sumInvariant ops eval (P, d)).node x) :
      (leafCertificate eval hops ev).space x ≤ 2 * cv' * (5 * z + 8) ^ dv' + (5 * z + 7) +
        cz' * (5 * z + 8) ^ dz' + cq' * (11 * z + 16) ^ dq' + ES := by
    have h1 := hnode x hx
    rw [leafCertificate_space]
    have h2 : (vertexCertificate (encQ := encQ) (encT := encT)).space x ≤
        cv' * (5 * z + 8) ^ dv' :=
      (hvs x).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
    have h2' : 2 * (vertexCertificate (encQ := encQ) (encT := encT)).space x ≤
        2 * cv' * (5 * z + 8) ^ dv' := by
      rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left 2 h2
    cases hvx : x.2.1.2.vertices[x.2.2.2]? with
    | none =>
      simp only [Option.elim]
      have h3 : (zeroCertificate (encT := encT) hops).space x ≤ cz' * (5 * z + 8) ^ dz' :=
        (hzs x).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
      omega
    | some v =>
      simp only [Option.elim]
      have hmem : v ∈ x.2.1.2.vertices := List.mem_of_getElem? hvx
      obtain ⟨hq, -, -, -⟩ := hx
      rw [hq] at hmem
      have h3 := hvlen v hmem
      have h4 : (queryCertificate (encQ := encQ) (encT := encT)).space (x, v) ≤
          cq' * (11 * z + 16) ^ dq' := by
        refine (hqs (x, v)).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _))
        have := length_encPair (enc₁ := encNode encQ encT)
          (enc₂ := encPair (encList encNat) encT) (x, v)
        dsimp only at this
        omega
      have h5 := (hE v hmem (wordBits x.2.2.1 v.1) (by simp [wordBits])).2.1
      omega
  obtain ⟨h, hh, he⟩ := eval_sumRoot (ops := ops) (eval := eval) P d
  have hres := hK₀ (NativeCertificate.ofPolyTime fuel_polyTime)
    (NativeCertificate.ofPolyTime sumRoot_polyTime) (sumInvariant ops eval (P, d)) (13 * z + 18)
    (2 * cv * (5 * z + 8) ^ dv + (5 * z + 7) + cz * (5 * z + 8) ^ dz +
      cq * (11 * z + 16) ^ dq + E)
    (2 * cv' * (5 * z + 8) ^ dv' + (5 * z + 7) + cz' * (5 * z + 8) ^ dz' +
      cq' * (11 * z + 16) ^ dq' + ES)
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
      have h3 := hRv a.2 ha2
      have h4 : (encPair (encNode encQ encT) (encAcc encY) (x, a)).length =
          2 * (encNode encQ encT x).length + 1 + (encAcc encY a).length := length_encPair (x, a)
      have h5 : (encAcc encY a).length = 2 * (encNat a.1).length + 1 + (encY a.2).length :=
        length_encPair a
      omega)
    (fun y hy => by
      rcases hy with hy | ⟨v, hv, w, -, rfl⟩
      · have := hRv y hy; omega
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
  have hTL : 2 * cv * (5 * z + 8) ^ dv + (5 * z + 7) + cz * (5 * z + 8) ^ dz +
      cq * (11 * z + 16) ^ dq ≤ (2 * cv * 13 ^ dv + 12 + cz * 13 ^ dz + cq * 27 ^ dq) * W := by
    have a1 := hterm (c := 2 * cv) (a := 5) (b := 8) (show dv ≤ D by omega)
    have a2 := hterm (c := cz) (a := 5) (b := 8) (show dz ≤ D by omega)
    have a3 := hterm (c := cq) (a := 11) (b := 16) (show dq ≤ D by omega)
    have e : (2 * cv * 13 ^ dv + 12 + cz * 13 ^ dz + cq * 27 ^ dq) * W =
        2 * cv * (5 + 8) ^ dv * W + 12 * W + cz * (5 + 8) ^ dz * W + cq * (11 + 16) ^ dq * W := by
      ring
    omega
  have hSL : 2 * cv' * (5 * z + 8) ^ dv' + (5 * z + 7) + cz' * (5 * z + 8) ^ dz' +
      cq' * (11 * z + 16) ^ dq' ≤
        (2 * cv' * 13 ^ dv' + 12 + cz' * 13 ^ dz' + cq' * 27 ^ dq') * W := by
    have a1 := hterm (c := 2 * cv') (a := 5) (b := 8) (show dv' ≤ D by omega)
    have a2 := hterm (c := cz') (a := 5) (b := 8) (show dz' ≤ D by omega)
    have a3 := hterm (c := cq') (a := 11) (b := 16) (show dq' ≤ D by omega)
    have e : (2 * cv' * 13 ^ dv' + 12 + cz' * 13 ^ dz' + cq' * 27 ^ dq') * W =
        2 * cv' * (5 + 8) ^ dv' * W + 12 * W + cz' * (5 + 8) ^ dz' * W +
          cq' * (11 + 16) ^ dq' * W := by
      ring
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
        (2 * cv * (5 * z + 8) ^ dv + (5 * z + 7) + cz * (5 * z + 8) ^ dz +
          cq * (11 * z + 16) ^ dq + E) +
        ((encNat (fuel (P, d))).length + 1) ^ 2 := ⟨_, rfl⟩
    rw [← hS] at htime
    have hstep : S ≤ G * W + E := by
      have e : G * W = K₀ * 96 ^ K₀ * W +
          (2 * cv * 13 ^ dv + 12 + cz * 13 ^ dz + cq * 27 ^ dq) * W + 16 * W := by
        rw [hG]; ring
      omega
    have hm := Nat.mul_le_mul_left (2 * B) hstep
    calc (contractionCertificate eval hops ev).time (P, d)
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
  · have h1 : (contractionCertificate eval hops ev).space (P, d) ≤ C * W + ES := by
      rw [contractionCertificate_space]
      unfold sumCertificate
      have e : C * W = cf * W + cr * W + cf' * W + cr' * W + 2 * G * W + G' * W + 4 * W := by
        rw [hC]; ring
      have e' : G' * W = K₀ * 96 ^ K₀ * W +
          (2 * cv' * 13 ^ dv' + 12 + cz' * 13 ^ dz' + cq' * 27 ^ dq') * W := by
        rw [hG']; ring
      have hfl' : (encNat (fuel (P, d))).length ≤ W := by omega
      omega
    exact h1.trans (Nat.add_le_add_right hCD _)

/-! ### The two instances -/

/-- Natural numbers modulo `2 ^ P` are polynomial-time, with `P` in unary. -/
theorem _root_.Cslib.Circuits.Frontier.SumOps.mod_polyTime :
    SumOps.mod.PolyTime encUnary encNat where
  zero := ComputableInPolyTime.const 0
  one := GaloisRingArith.computableInPolyTime_mod_two_pow (ComputableInPolyTime.const 1)
    ComputableInPolyTime.id'
  add := GaloisRingArith.computableInPolyTime_mod_two_pow
    (ComputableInPolyTime.binary_add.comp ((ComputableInPolyTime.fst encNat encNat).comp
      (ComputableInPolyTime.snd _ _) |>.prod ((ComputableInPolyTime.snd encNat encNat).comp
        (ComputableInPolyTime.snd _ _)))) (ComputableInPolyTime.fst _ _)
  mul := GaloisRingArith.computableInPolyTime_mod_two_pow
    (ComputableInPolyTime.binary_mul' ((ComputableInPolyTime.fst encNat encNat).comp
      (ComputableInPolyTime.snd _ _)) ((ComputableInPolyTime.snd encNat encNat).comp
        (ComputableInPolyTime.snd _ _))) (ComputableInPolyTime.fst _ _)

/-- Coefficient lists are polynomial-time, with `p` in unary and the coefficients of `f` in
binary. -/
theorem _root_.Cslib.Circuits.Frontier.SumOps.galois_polyTime :
    SumOps.galois.PolyTime (encPair encUnary (encList encNat)) (encList encNat) where
  zero := GaloisRingArith.computableInPolyTime_tabulate (g := fun _ _ => 0)
    ((ComputableInPolyTime.length_list encNat).comp (ComputableInPolyTime.snd _ _))
    (ComputableInPolyTime.const 0)
  one := GaloisRingArith.computableInPolyTime_one (ComputableInPolyTime.snd _ _)
  add := by
    have hq := ComputableInPolyTime.fst (encPair encUnary (encList encNat))
      (encPair (encList encNat) (encList encNat))
    have hcd := ComputableInPolyTime.snd (encPair encUnary (encList encNat))
      (encPair (encList encNat) (encList encNat))
    exact GaloisRingArith.computableInPolyTime_add ((ComputableInPolyTime.fst _ _).comp hq)
      ((ComputableInPolyTime.snd _ _).comp hq) ((ComputableInPolyTime.fst _ _).comp hcd)
      ((ComputableInPolyTime.snd _ _).comp hcd)
  mul := by
    have hq := ComputableInPolyTime.fst (encPair encUnary (encList encNat))
      (encPair (encList encNat) (encList encNat))
    have hcd := ComputableInPolyTime.snd (encPair encUnary (encList encNat))
      (encPair (encList encNat) (encList encNat))
    exact GaloisRingArith.computableInPolyTime_mul ((ComputableInPolyTime.fst _ _).comp hq)
      ((ComputableInPolyTime.snd _ _).comp hq) ((ComputableInPolyTime.fst _ _).comp hcd)
      ((ComputableInPolyTime.snd _ _).comp hcd)

/-- **Direct summation modulo `2 ^ P`**: one native machine for `d.contraction eval % 2 ^ P` on
every input `(P, d)`, with `P` in unary, from a native certificate of a natural-number
evaluator. -/
noncomputable def modContractionCertificate (eval : T → List Bool → ℕ)
    (ev : NativeCertificate (fun q : T × List Bool => eval q.1 q.2) (encPair encT encBits)
      encNat) :
    NativeCertificate (fun q : ℕ × DescribedNetwork T => q.2.contraction eval % 2 ^ q.1)
      (encInput encUnary encT) encNat :=
  (contractionCertificate eval SumOps.mod_polyTime ev).congr fun q => sumValue_mod eval q.1 q.2

end Native

end DescribedNetwork

end Cslib.Circuits.Frontier
