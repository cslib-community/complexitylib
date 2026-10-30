/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.Explicit
public import Complexity.Computability.GenericRAM.Native.BooleanFold
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Words
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryDivision
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListBinaryLookup
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListMap
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListToBits
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Size

/-!
# Contracting an explicit tensor network by direct summation

The leaf and small-size case of the contraction theorem, Theorem D.1 of [OpenAI2026ETH]
(Appendix D.4.7, p. 64), where a leaf sums directly over all Boolean edge assignments, and the
fallback for small sizes (Appendix D.4.2, p. 58). On input `(P, r, d)`, with `d` an explicit network
whose row vertices are the first `r` (the bipartition the fast algorithm uses), direct summation
computes the contraction of `d` modulo `2 ^ P`. It ignores `r`.

`directContraction` streams over the `2 ^ m` assignments of bits to the `m` edges with
`Cslib.GenericRAM.BooleanFold`, in their binary order, keeping only the current index, the input
and an accumulator below `2 ^ P`. For each assignment it multiplies the table entries at the bits
on the ports, reducing modulo `2 ^ P` after each factor (`weightMod`), and adds the product to the
accumulator modulo `2 ^ P` (`sumStep`). `directContraction_eq` proves that the result is
`d.contraction % 2 ^ P`.

**Input encoding** (`encContractionInput`). The triple `(P, r, d)` is encoded as a pair: `P` in
unary, then the pair of `r` in binary and `d`. The network `d` (`encExplicitNetwork`) is the pair
of its number of edges, in unary, and its list of vertices. Each vertex is the pair of its list
of ports and its table, both lists of binary numbers. The unary fields keep the arithmetic
modulo `2 ^ P` and the streamed assignments polynomial in the input length.

## Main definitions

* `Cslib.Circuits.Frontier.ExplicitTensorNetwork.weightMod`: the weight of an assignment modulo
  `2 ^ P`.
* `Cslib.Circuits.Frontier.ExplicitTensorNetwork.sumStep`: one step of direct summation.
* `Cslib.Circuits.Frontier.ExplicitTensorNetwork.directContraction`: direct summation on
  `(P, r, d)`.
* `Cslib.Circuits.Frontier.ExplicitTensorNetwork.encExplicitNetwork`,
  `Cslib.Circuits.Frontier.ExplicitTensorNetwork.encContractionInput`: the input encodings.
* `Cslib.Circuits.Frontier.ExplicitTensorNetwork.directContractionCertificate`: one native
  machine for direct summation, streaming with `BooleanFold`.

## Main results

* `Cslib.Circuits.Frontier.ExplicitTensorNetwork.weightMod_ofFn`: the weight of an assignment.
* `Cslib.Circuits.Frontier.ExplicitTensorNetwork.directContraction_eq`: direct summation computes
  the contraction modulo `2 ^ P`.
* `Cslib.Circuits.Frontier.ExplicitTensorNetwork.runPrefix_sumStep`: every prefix of the loop
  retains the input and keeps its accumulator below `2 ^ P`.
* `Cslib.Circuits.Frontier.ExplicitTensorNetwork.weightMod_polyTime`,
  `Cslib.Circuits.Frontier.ExplicitTensorNetwork.sumStep_polyTime`,
  `Cslib.Circuits.Frontier.ExplicitTensorNetwork.numEdges_polyTime`,
  `Cslib.Circuits.Frontier.ExplicitTensorNetwork.initial_polyTime`: the weight, one step, the
  width and the initial state in polynomial time.

**Status.** `directContractionCertificate` is a native certificate, but its explicit bounds,
`2 ^ m` times a polynomial in time and a polynomial in space on every input, are not yet extracted
(`IndexFold.computableInO`, with `runPrefix_sumStep` bounding the live state).

## References

* [OpenAI2026ETH], Theorem D.1 (Appendix D.1, p. 53) and its proof (Appendix D.4.7, p. 64).
-/

@[expose] public section

namespace Cslib.Circuits.Frontier.ExplicitTensorNetwork

open Cslib.BitString Cslib.GenericRAM Turing.MultiTapeTM

/-- The weight modulo `2 ^ P` of an assignment of bits to the edges, given as a word: port `i`
reads bit `i` of the word, and `false` past its end. It is the product of the table entries at
the bits on the ports, reduced modulo `2 ^ P` after each factor. -/
def weightMod (P : ℕ) (d : ExplicitTensorNetwork ℕ) (word : List Bool) : ℕ :=
  d.vertices.foldl (fun acc v => acc * entry v.2 (v.1.map fun i => word.getD i false) % 2 ^ P)
    (1 % 2 ^ P)

/-- One step of direct summation, as a `BooleanFold` body: add the weight of the current word to
the accumulator modulo `2 ^ P`, retaining the precision `P` and the network. -/
def sumStep (s : (ℕ × List Bool) × ((ℕ × ExplicitTensorNetwork ℕ) × ℕ)) :
    (ℕ × ExplicitTensorNetwork ℕ) × ℕ :=
  (s.2.1, (s.2.2 + weightMod s.2.1.1 s.2.1.2 s.1.2) % 2 ^ s.2.1.1)

/-- **Direct summation** on the input `(P, r, d)`: stream over the `2 ^ m` assignments to the `m`
edges of `d`, accumulating their weights modulo `2 ^ P`. The number `r` of row vertices is not
used. -/
def directContraction (x : ℕ × ℕ × ExplicitTensorNetwork ℕ) : ℕ :=
  (BooleanFold.run sumStep x.2.2.numEdges ((x.1, x.2.2), 0)).2.2.2

/-! ### Input encoding -/

/-- An explicit network over `ℕ` is its number of edges and its list of vertices. -/
def equivProd : ExplicitTensorNetwork ℕ ≃ ℕ × List (List ℕ × List ℕ) where
  toFun d := (d.numEdges, d.vertices)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The encoding of an explicit network**: its number of edges in unary, then its list of
vertices, each the pair of its list of ports and its table, as lists of binary numbers. -/
def encExplicitNetwork : ExplicitTensorNetwork ℕ ↪ List Bool :=
  encOfEquiv equivProd (encPair encUnary (encList (encPair (encList encNat) (encList encNat))))

/-- **The encoding of a contraction input `(P, r, d)`**: the precision `P` in unary, then the
number `r` of row vertices in binary and the network (`encExplicitNetwork`). -/
def encContractionInput : ℕ × ℕ × ExplicitTensorNetwork ℕ ↪ List Bool :=
  encPair encUnary (encPair encNat encExplicitNetwork)

/-! ### Correctness -/

private theorem foldl_mul_mod {α : Type*} (f : α → ℕ) (m : ℕ) (l : List α) (a : ℕ) :
    l.foldl (fun acc v => acc * f v % m) (a % m) = a * (l.map f).prod % m := by
  induction l generalizing a with
  | nil => simp
  | cons v l ih =>
    rw [List.foldl_cons, Nat.mod_mul_mod, ih, List.map_cons, List.prod_cons, Nat.mul_assoc]

private theorem getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  by_cases h : i < n
  · rw [dite_eq_left h, List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]
  · rw [dite_eq_right h, List.getD_eq_default _ _ (by simp only [List.length_ofFn]; omega)]

/-- **The weight of an assignment.** On the word of an assignment `x` to the edges, `weightMod` is
the product of the table entries at the bits on the ports, modulo `2 ^ P`. -/
theorem weightMod_ofFn (P : ℕ) (d : ExplicitTensorNetwork ℕ) (x : Fin d.numEdges → Bool) :
    weightMod P d (List.ofFn x) =
      (d.vertices.map fun v => entry v.2 (d.portBits x v.1)).prod % 2 ^ P := by
  rw [weightMod, foldl_mul_mod, Nat.one_mul]
  simp only [portBits, getD_ofFn]

private theorem foldl_sumStep (P n : ℕ) (d : ExplicitTensorNetwork ℕ) (words : List (List Bool))
    (a : ℕ) :
    words.foldl (fun acc word => sumStep ((n, word), acc)) ((P, d), a % 2 ^ P) =
      ((P, d), (a + (words.map (weightMod P d)).sum) % 2 ^ P) := by
  induction words generalizing a with
  | nil => simp
  | cons w ws ih =>
    rw [List.foldl_cons]
    change ws.foldl (fun acc word => sumStep ((n, word), acc))
      ((P, d), (a % 2 ^ P + weightMod P d w) % 2 ^ P) = _
    rw [Nat.mod_add_mod, ih, List.map_cons, List.sum_cons, Nat.add_assoc]

private theorem sum_enumList (n : ℕ) (g : List Bool → ℕ) :
    ((enumList n).map g).sum = ∑ σ : BitString n, g (List.ofFn σ) := by
  have hall : (enum n).toFinset = Finset.univ := by ext; simp
  rw [enumList, List.map_map, ← List.sum_toFinset _ (nodup_enum n), hall]
  rfl

/-- **Direct summation computes the contraction modulo `2 ^ P`**, on every input. -/
theorem directContraction_eq (P r : ℕ) (d : ExplicitTensorNetwork ℕ) :
    directContraction (P, r, d) = d.contraction % 2 ^ P := by
  have h := foldl_sumStep P d.numEdges d (enumList d.numEdges) 0
  rw [Nat.zero_mod] at h
  rw [directContraction, BooleanFold.run_accumulator, h, Nat.zero_add, sum_enumList,
    contraction]
  simp only [weightMod_ofFn]
  exact (Finset.sum_nat_mod _ _ _).symm

/-! ### One step in polynomial time -/

local notation "encVertices" => encList (encPair (encList encNat) (encList encNat))

/-- The encoding of the precision, the network and the current word. -/
local notation "encWeightInput" => encPair (encPair encUnary encExplicitNetwork) encBits

/-- The vertices of a network, read from its encoding. -/
private theorem vertices_polyTime :
    ComputableInPolyTime (fun d : ExplicitTensorNetwork ℕ => d.vertices) encExplicitNetwork
      encVertices :=
  (ComputableInPolyTime.snd encUnary encVertices).comp
    (ComputableInPolyTime.of_eq (f := equivProd) fun _ => rfl)

/-- `2 ^ P` in binary from `P` in unary. -/
private theorem twoPow_polyTime :
    ComputableInPolyTime (fun P : ℕ => 2 ^ P) encUnary encNat :=
  BooleanFold.clock.polyTime ⟨PolyBounded.self, PolyBounded.self⟩

/-- A number below `2 ^ P` has at most `P` binary digits. -/
private theorem length_encNat_le {x P : ℕ} (hx : x < 2 ^ P) : (encNat x).length ≤ P := by
  change x.bits.length ≤ P
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr hx

/-- The weight of the current word modulo `2 ^ P` is computable in polynomial time. -/
theorem weightMod_polyTime :
    ComputableInPolyTime (fun q : (ℕ × ExplicitTensorNetwork ℕ) × List Bool =>
      weightMod q.1.1 q.1.2 q.2) encWeightInput encNat := by
  -- The modulus `2 ^ P`, the vertices and the word.
  have hP := (ComputableInPolyTime.fst encUnary encExplicitNetwork).comp
    (ComputableInPolyTime.fst (encPair encUnary encExplicitNetwork) encBits)
  have hmod := twoPow_polyTime.comp hP
  have hverts := vertices_polyTime.comp ((ComputableInPolyTime.snd encUnary encExplicitNetwork).comp
    (ComputableInPolyTime.fst (encPair encUnary encExplicitNetwork) encBits))
  have hinit : ComputableInPolyTime (fun q : (ℕ × ExplicitTensorNetwork ℕ) × List Bool =>
      1 % 2 ^ q.1.1) encWeightInput encNat :=
    (ComputableInPolyTime.snd encNat encNat).comp
      (ComputableInPolyTime.binary_divMod.comp ((ComputableInPolyTime.const 1).prod hmod))
  -- One step of the product: multiply by the entry at the bits on the ports, modulo `2 ^ P`.
  let encStep := encPair (encPair encWeightInput encNat) (encPair (encList encNat) (encList encNat))
  have hq : ComputableInPolyTime
      (fun p : (((ℕ × ExplicitTensorNetwork ℕ) × List Bool) × ℕ) × (List ℕ × List ℕ) => p.1.1)
      encStep encWeightInput :=
    (ComputableInPolyTime.fst encWeightInput encNat).comp
      (ComputableInPolyTime.fst (encPair encWeightInput encNat) _)
  have hacc : ComputableInPolyTime
      (fun p : (((ℕ × ExplicitTensorNetwork ℕ) × List Bool) × ℕ) × (List ℕ × List ℕ) => p.1.2)
      encStep encNat :=
    (ComputableInPolyTime.snd encWeightInput encNat).comp
      (ComputableInPolyTime.fst (encPair encWeightInput encNat) _)
  have hv := ComputableInPolyTime.snd (encPair encWeightInput encNat)
    (encPair (encList encNat) (encList encNat))
  have hports := (ComputableInPolyTime.fst (encList encNat) (encList encNat)).comp hv
  have htable := (ComputableInPolyTime.snd (encList encNat) (encList encNat)).comp hv
  have hbit : ComputableInPolyTime
      (fun z : ((((ℕ × ExplicitTensorNetwork ℕ) × List Bool) × ℕ) × (List ℕ × List ℕ)) × ℕ =>
        z.1.1.1.2.getD z.2 false) (encPair encStep encNat) encBool :=
    ComputableInPolyTime.listGetD_binary (encA := encBool) (encL := encBits) false
      ((ComputableInPolyTime.snd (encPair encUnary encExplicitNetwork) encBits).comp
        (hq.comp (ComputableInPolyTime.fst encStep encNat)))
      (ComputableInPolyTime.snd encStep encNat)
  have hbits := ComputableInPolyTime.listToBits.comp
    (ComputableInPolyTime.mapWithInput (f := fun p i => p.1.1.2.getD i false) hports hbit)
  have hindex := ComputableInPolyTime.bitsBinaryValue.comp
    (ComputableInPolyTime.bitsReverse.comp hbits)
  have hentry := ComputableInPolyTime.listGetD_binary (encA := encNat) (encL := encList encNat) 0
    htable hindex
  have hstepMod := twoPow_polyTime.comp ((ComputableInPolyTime.fst encUnary encExplicitNetwork).comp
    ((ComputableInPolyTime.fst (encPair encUnary encExplicitNetwork) encBits).comp hq))
  have hstep : ComputableInPolyTime
      (fun p : (((ℕ × ExplicitTensorNetwork ℕ) × List Bool) × ℕ) × (List ℕ × List ℕ) =>
        p.1.2 * entry p.2.2 (p.2.1.map fun i => p.1.1.2.getD i false) % 2 ^ p.1.1.1.1)
      encStep encNat := by
    have h := (ComputableInPolyTime.snd encNat encNat).comp
      (ComputableInPolyTime.binary_divMod.comp
        ((ComputableInPolyTime.binary_mul' hacc hentry).prod hstepMod))
    refine ComputableInPolyTime.of_enc_eq h fun p => ?_
    simp only [Function.comp_def, entry, lsbValue_eq_binaryValue_reverse]
  have hfold := ComputableInPolyTime.foldlWithInput_of_bounded_growth
    (encA := encPair (encList encNat) (encList encNat)) (encL := encVertices)
    (step := fun q acc v => acc * entry v.2 (v.1.map fun i => q.2.getD i false) % 2 ^ q.1.1)
    hinit ⟨hverts, hstep, inferInstance, inferInstance⟩
    (growth := fun q => q.1.1)
    ⟨PolyBounded.of_forall_le 1 1 fun q => by
      simp only [length_encPair, encUnary_apply, List.length_replicate, pow_one, one_mul]; omega,
      fun q acc v _ => (length_encNat_le (Nat.mod_lt _ (Nat.two_pow_pos _))).trans
        (Nat.le_add_left _ _)⟩
  exact hfold

/-- The live state of direct summation: the precision, the network and the accumulator. -/
local notation "encSumState" => encPair (encPair encUnary encExplicitNetwork) encNat

/-- **One step of direct summation is computable in polynomial time**, in the encoding of the
`BooleanFold` callback input: the width and the current word, and the live state. -/
theorem sumStep_polyTime :
    ComputableInPolyTime sumStep (encPair (encPair encUnary encBits) encSumState) encSumState := by
  have hstate := ComputableInPolyTime.snd (encPair encUnary encBits) encSumState
  have hpd := (ComputableInPolyTime.fst (encPair encUnary encExplicitNetwork) encNat).comp hstate
  have hacc := (ComputableInPolyTime.snd (encPair encUnary encExplicitNetwork) encNat).comp hstate
  have hword := (ComputableInPolyTime.snd encUnary encBits).comp
    (ComputableInPolyTime.fst (encPair encUnary encBits) encSumState)
  have hweight := weightMod_polyTime.comp (hpd.prod hword)
  have hmod := twoPow_polyTime.comp
    ((ComputableInPolyTime.fst encUnary encExplicitNetwork).comp hpd)
  have hsum := (ComputableInPolyTime.snd encNat encNat).comp
    (ComputableInPolyTime.binary_divMod.comp
      ((ComputableInPolyTime.binary_add.comp (hacc.prod hweight)).prod hmod))
  exact hpd.prod hsum

/-! ### The streaming loop -/

/-- **The live state of every prefix** of the loop: the precision and the network are retained,
and the accumulator is the sum of the weights of the visited words modulo `2 ^ P`, so it stays
below `2 ^ P`. -/
theorem runPrefix_sumStep (P : ℕ) (d : ExplicitTensorNetwork ℕ) (j : ℕ) :
    (BooleanFold.runPrefix sumStep d.numEdges j ((P, d), 0)).2.2 =
      ((P, d), (((List.range j).map (lowBits d.numEdges)).map (weightMod P d)).sum % 2 ^ P) := by
  have h := foldl_sumStep P d.numEdges d ((List.range j).map (lowBits d.numEdges)) 0
  rw [Nat.zero_mod, Nat.zero_add] at h
  rw [BooleanFold.prefix_accumulator, ← h, List.foldl_map]

/-- The width of the loop: the number of edges, in unary. -/
theorem numEdges_polyTime :
    ComputableInPolyTime (fun x : ℕ × ℕ × ExplicitTensorNetwork ℕ => x.2.2.numEdges)
      encContractionInput encUnary :=
  (ComputableInPolyTime.fst encUnary encVertices).comp
    ((ComputableInPolyTime.of_eq (f := equivProd) fun _ => rfl).comp
      ((ComputableInPolyTime.snd encNat encExplicitNetwork).comp
        (ComputableInPolyTime.snd encUnary (encPair encNat encExplicitNetwork))))

/-- The initial live state: the precision, the network and a zero accumulator. -/
theorem initial_polyTime :
    ComputableInPolyTime (fun x : ℕ × ℕ × ExplicitTensorNetwork ℕ => ((x.1, x.2.2), (0 : ℕ)))
      encContractionInput encSumState :=
  ((ComputableInPolyTime.fst encUnary (encPair encNat encExplicitNetwork)).prod
    ((ComputableInPolyTime.snd encNat encExplicitNetwork).comp
      (ComputableInPolyTime.snd encUnary (encPair encNat encExplicitNetwork)))).prod
    (ComputableInPolyTime.const 0)

/-- **A native certificate for direct summation**: one finite machine streams the `2 ^ m`
assignments with `BooleanFold`, running the polynomial-time step `sumStep` on each. Its resource
bounds are those of `BooleanFold.certificate`; the explicit `2 ^ m · poly` time and polynomial
space bounds are not yet extracted here. -/
noncomputable def directContractionCertificate :
    NativeCertificate directContraction encContractionInput encNat :=
  NativeCertificate.snd (NativeCertificate.snd (NativeCertificate.snd
    (BooleanFold.certificate (NativeCertificate.ofPolyTime numEdges_polyTime)
      (NativeCertificate.ofPolyTime initial_polyTime)
      (NativeCertificate.ofPolyTime sumStep_polyTime))))

end Cslib.Circuits.Frontier.ExplicitTensorNetwork
