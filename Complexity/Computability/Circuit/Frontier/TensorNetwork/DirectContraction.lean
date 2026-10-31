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
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryDivision
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListBinaryLookup
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListMap
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListToBits
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
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

**Precision in binary** (`directContractionBinaryCertificate`). The same triple with `P` in binary
(`encPair encNat (encPair encNat encExplicitNetwork)`) is handled by capping first: the
contraction is below `2 ^ |d|` for `|d|` the encoded length of `d`, so `P` can be replaced by the
unary `min |d| P` (`capPrecision`) without changing the residue. The bounds carry over.

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
* `Cslib.Circuits.Frontier.ExplicitTensorNetwork.capPrecision`,
  `Cslib.Circuits.Frontier.ExplicitTensorNetwork.directContractionBinaryCertificate`: capping a
  binary precision, and direct summation with the precision in binary.

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
* `Cslib.Circuits.Frontier.ExplicitTensorNetwork.directContractionCertificate_bounds`: on every
  input, polynomial workspace and time `2 ^ m + 1` times a polynomial in the input length, where
  `m` is the number of edges.
* `Cslib.Circuits.Frontier.ExplicitTensorNetwork.exists_directContractionCertificate_le`: the same
  with one constant, time `K (n + 1) ^ K 2 ^ m` and workspace `K (n + 1) ^ K` for input length
  `n`.
* `Cslib.Circuits.Frontier.ExplicitTensorNetwork.exists_computableInO_contraction_mod`: the
  contraction modulo `2 ^ P` is computable within time `(n + 1) ^ K 2 ^ m` and space
  `(n + 1) ^ K`, up to constants, on every input.

* `Cslib.Circuits.Frontier.ExplicitTensorNetwork.contraction_lt_two_pow_length`,
  `Cslib.Circuits.Frontier.ExplicitTensorNetwork.contraction_mod_two_pow_min`,
  `Cslib.Circuits.Frontier.ExplicitTensorNetwork.capPrecision_polyTime`: the contraction is below
  `2 ^ |d|`, so capping the precision at `|d|` keeps the residue, in polynomial time.
* `Cslib.Circuits.Frontier.ExplicitTensorNetwork.directContractionBinaryCertificate_bounds`,
  `Cslib.Circuits.Frontier.ExplicitTensorNetwork.exists_directContractionBinaryCertificate_le`:
  the same bounds with the precision in binary.

These bounds hold on every input because the live state keeps only the binary index, the input
and an accumulator below `2 ^ P`, and `P` is unary (`runPrefix_sumStep`, with
`Cslib.GenericRAM.BooleanFold.certificate_bounds`) or capped at the input length.

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

/-- **The encoding of an explicit network**: its number of edges in unary, then its list of
vertices, each the pair of its list of ports and its table, as lists of binary numbers. -/
def encExplicitNetwork : ExplicitTensorNetwork ℕ ↪ List Bool :=
  encOfEquiv DescribedNetwork.equivProd
    (encPair encUnary (encList (encPair (encList encNat) (encList encNat))))

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
    (ComputableInPolyTime.of_eq (f := DescribedNetwork.equivProd) fun _ => rfl)

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
    ((ComputableInPolyTime.of_eq (f := DescribedNetwork.equivProd) fun _ => rfl).comp
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
assignments with `BooleanFold`, running the polynomial-time step `sumStep` on each. Its explicit
bounds are `directContractionCertificate_bounds` and `exists_directContractionCertificate_le`. -/
noncomputable def directContractionCertificate :
    NativeCertificate directContraction encContractionInput encNat :=
  NativeCertificate.snd (NativeCertificate.snd (NativeCertificate.snd
    (BooleanFold.certificate (NativeCertificate.ofPolyTime numEdges_polyTime)
      (NativeCertificate.ofPolyTime initial_polyTime)
      (NativeCertificate.ofPolyTime sumStep_polyTime))))

/-! ### Explicit bounds -/

/-- The live state of every prefix is at most three times as long as the input: it retains the
precision and the network, and its accumulator is below `2 ^ P`. -/
private theorem length_runPrefix_sumStep_le (x : ℕ × ℕ × ExplicitTensorNetwork ℕ) (j : ℕ) :
    (encSumState (BooleanFold.runPrefix sumStep x.2.2.numEdges j ((x.1, x.2.2), 0)).2.2).length ≤
      3 * (encContractionInput x).length := by
  obtain ⟨P, r, d⟩ := x
  rw [runPrefix_sumStep]
  have h := length_encNat_le
    (Nat.mod_lt (((List.range j).map (lowBits d.numEdges)).map (weightMod P d)).sum
      (Nat.two_pow_pos P))
  simp only [encContractionInput, length_encPair, encUnary_apply, List.length_replicate]
  omega

/-- **The bounds of direct summation**, on every input `(P, r, d)`: polynomial workspace in the
input length, and time `2 ^ m + 1` times a polynomial in the input length, where `m` is the number
of edges of `d`. -/
theorem directContractionCertificate_bounds :
    PolyBounded (fun x => (encContractionInput x).length) directContractionCertificate.space ∧
      ∃ T : ℕ × ℕ × ExplicitTensorNetwork ℕ → ℕ,
        PolyBounded (fun x => (encContractionInput x).length) T ∧
        ∀ x, directContractionCertificate.time x ≤ (2 ^ x.2.2.numEdges + 1) * T x :=
  BooleanFold.certificate_bounds (NativeCertificate.ofPolyTime_isPolynomial numEdges_polyTime)
    (NativeCertificate.ofPolyTime_isPolynomial initial_polyTime)
    (NativeCertificate.ofPolyTime_isPolynomial sumStep_polyTime)
    ((PolyBounded.const 3).mul .self) fun x j _ => length_runPrefix_sumStep_le x j

/-- One constant for bounds of the form `(2 ^ m + 1)` times a polynomial in time and a polynomial in
space. -/
private theorem exists_le_of_bounds {enc : ℕ × ℕ × ExplicitTensorNetwork ℕ ↪ List Bool}
    {time space T : ℕ × ℕ × ExplicitTensorNetwork ℕ → ℕ}
    (hspace : PolyBounded (fun x => (enc x).length) space)
    (hT : PolyBounded (fun x => (enc x).length) T)
    (htime : ∀ x, time x ≤ (2 ^ x.2.2.numEdges + 1) * T x) :
    ∃ K : ℕ, ∀ x, time x ≤ K * ((enc x).length + 1) ^ K * 2 ^ x.2.2.numEdges ∧
      space x ≤ K * ((enc x).length + 1) ^ K := by
  obtain ⟨ct, dt, hct⟩ := hT.exists_le
  obtain ⟨cs, ds, hcs⟩ := hspace.exists_le
  refine ⟨2 * ct + cs + dt + ds, fun x => ⟨?_, ?_⟩⟩
  · have h1 : 2 ^ x.2.2.numEdges + 1 ≤ 2 * 2 ^ x.2.2.numEdges := by
      have := Nat.one_le_two_pow (n := x.2.2.numEdges)
      omega
    have h2 : ((enc x).length + 1) ^ dt ≤ ((enc x).length + 1) ^ (2 * ct + cs + dt + ds) :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
    calc time x
        ≤ (2 * 2 ^ x.2.2.numEdges) * (ct * ((enc x).length + 1) ^ dt) :=
          (htime x).trans (Nat.mul_le_mul h1 (hct x))
      _ = 2 * ct * ((enc x).length + 1) ^ dt * 2 ^ x.2.2.numEdges := by ac_rfl
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul (by omega) h2)
  · exact (hcs x).trans (Nat.mul_le_mul (by omega)
      (Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)))

/-- **The bounds of direct summation in one constant**: there is `K` such that on every input
`x = (P, r, d)` the time is at most `K (n + 1) ^ K 2 ^ m` and the workspace at most
`K (n + 1) ^ K`, where `n` is the input length and `m` the number of edges of `d`. Since
`2 ^ m ≤ 2 ^ (K m)`, this gives the unconditional `K (n + 1) ^ K 2 ^ (K m)` form of the
contraction contract. -/
theorem exists_directContractionCertificate_le :
    ∃ K : ℕ, ∀ x : ℕ × ℕ × ExplicitTensorNetwork ℕ,
      directContractionCertificate.time x ≤
          K * ((encContractionInput x).length + 1) ^ K * 2 ^ x.2.2.numEdges ∧
        directContractionCertificate.space x ≤ K * ((encContractionInput x).length + 1) ^ K :=
  let ⟨hspace, _, hT, htime⟩ := directContractionCertificate_bounds
  exists_le_of_bounds hspace hT htime

/-- **Direct summation is computable within time `(n + 1) ^ K 2 ^ m` and space `(n + 1) ^ K`**,
up to constants, on every input `x = (P, r, d)`, where `n` is the input length and `m` the number
of edges of `d`. The output is the contraction of `d` modulo `2 ^ P`, in binary. -/
theorem exists_computableInO_contraction_mod :
    ∃ K : ℕ, ComputableInO
      (fun x : ℕ × ℕ × ExplicitTensorNetwork ℕ => x.2.2.contraction % 2 ^ x.1)
      encContractionInput encNat
      (fun x => ((encContractionInput x).length + 1) ^ K * 2 ^ x.2.2.numEdges)
      (fun x => ((encContractionInput x).length + 1) ^ K) := by
  obtain ⟨K, hK⟩ := exists_directContractionCertificate_le
  refine ⟨K, (directContractionCertificate.computes.mono K (fun x => ?_) (fun x => ?_)).of_enc_eq
    fun x => ?_⟩
  · refine (hK x).1.trans ?_
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left K (Nat.le_succ _)
  · exact (hK x).2.trans (Nat.mul_le_mul_left K (Nat.le_succ _))
  · obtain ⟨P, r, d⟩ := x
    rw [directContraction_eq]

/-! ### The precision in binary

A precision given in binary can be exponentially larger than the input. It can be capped: the
contraction is below `2 ^ |d|`, for `|d|` the encoded length of the network, so reducing modulo
`2 ^ min |d| P` gives the same residue. The capped precision is unary and at most `|d|`, so direct
summation keeps its bounds. -/

/-- The encoding of a contraction input with the precision in binary. -/
local notation "encBinaryInput" => encPair encNat (encPair encNat encExplicitNetwork)

private theorem sum_lt_two_pow_length (t : List ℕ) : t.sum < 2 ^ (encList encNat t).length := by
  induction t with
  | nil => simp
  | cons e t ih =>
    have he : e < 2 ^ (encNat e).length := by
      change e < 2 ^ e.bits.length
      rw [Nat.size_eq_bits_len]
      exact Nat.lt_size_self e
    have h1 : 2 ^ (encNat e).length ≤ 2 ^ (2 * (encNat e).length + (encList encNat t).length) :=
      Nat.pow_le_pow_right two_pos (by omega)
    have h2 : 2 ^ (encList encNat t).length ≤
        2 ^ (2 * (encNat e).length + (encList encNat t).length) :=
      Nat.pow_le_pow_right two_pos (by omega)
    have hlen : (encList encNat (e :: t)).length =
        2 * (encNat e).length + (encList encNat t).length + 1 := by
      rw [length_encList, List.map_cons, List.sum_cons, ← length_encList]
      omega
    rw [List.sum_cons, hlen, pow_succ]
    omega

private theorem entry_le_sum (t : List ℕ) (bs : List Bool) : entry t bs ≤ t.sum := by
  unfold entry
  rcases lt_or_ge (lsbValue bs) t.length with h | h
  · rw [List.getD_eq_getElem _ _ h]
    exact List.le_sum_of_mem (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ h]
    exact Nat.zero_le _

private theorem prod_le_two_pow_length (vs : List (List ℕ × List ℕ)) (f : List ℕ × List ℕ → ℕ)
    (hf : ∀ v ∈ vs, f v ≤ v.2.sum) :
    (vs.map f).prod ≤ 2 ^ (encVertices vs).length := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    have hv : f v ≤ 2 ^ (encList encNat v.2).length :=
      (hf v List.mem_cons_self).trans (sum_lt_two_pow_length v.2).le
    have hvs := ih fun w hw => hf w (List.mem_cons_of_mem _ hw)
    have hlen : (encVertices (v :: vs)).length =
        2 * (2 * (encList encNat v.1).length + 1 + (encList encNat v.2).length) + 1 +
          (encVertices vs).length := by
      rw [length_encList, List.map_cons, List.sum_cons, ← length_encList, length_encPair]
    rw [List.map_cons, List.prod_cons, hlen]
    calc f v * (vs.map f).prod
        ≤ 2 ^ (encList encNat v.2).length * 2 ^ (encVertices vs).length := Nat.mul_le_mul hv hvs
      _ = 2 ^ ((encList encNat v.2).length + (encVertices vs).length) := (pow_add _ _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right two_pos (by omega)

/-- **The contraction is below `2 ^ |d|`**, for `|d|` the encoded length of the network: each
table entry is at most the sum of its table, and there are `2 ^ m` assignments. -/
theorem contraction_lt_two_pow_length (d : ExplicitTensorNetwork ℕ) :
    d.contraction < 2 ^ (encExplicitNetwork d).length := by
  have hw (x : Fin d.numEdges → Bool) :
      (d.vertices.map fun v => entry v.2 (d.portBits x v.1)).prod ≤
        2 ^ (encVertices d.vertices).length :=
    prod_le_two_pow_length _ _ fun v _ => entry_le_sum _ _
  have hlen : (encExplicitNetwork d).length =
      2 * d.numEdges + 1 + (encVertices d.vertices).length := by
    change (encPair encUnary encVertices (d.numEdges, d.vertices)).length = _
    rw [length_encPair, encUnary_apply, List.length_replicate]
  calc d.contraction
      ≤ ∑ _x : Fin d.numEdges → Bool, 2 ^ (encVertices d.vertices).length :=
        Finset.sum_le_sum fun x _ => hw x
    _ = 2 ^ (d.numEdges + (encVertices d.vertices).length) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin, smul_eq_mul, pow_add]
    _ < 2 ^ (encExplicitNetwork d).length := Nat.pow_lt_pow_right one_lt_two (by omega)

/-- Capping the precision at the encoded length of the network does not change the residue. -/
theorem contraction_mod_two_pow_min (P : ℕ) (d : ExplicitTensorNetwork ℕ) :
    d.contraction % 2 ^ min (encExplicitNetwork d).length P = d.contraction % 2 ^ P := by
  rcases le_total (encExplicitNetwork d).length P with h | h
  · rw [min_eq_left h, Nat.mod_eq_of_lt (contraction_lt_two_pow_length d),
      Nat.mod_eq_of_lt ((contraction_lt_two_pow_length d).trans_le
        (Nat.pow_le_pow_right two_pos h))]
  · rw [min_eq_right h]

/-- Cap the precision at the encoded length of the network. -/
def capPrecision (x : ℕ × ℕ × ExplicitTensorNetwork ℕ) : ℕ × ℕ × ExplicitTensorNetwork ℕ :=
  (min (encExplicitNetwork x.2.2).length x.1, x.2)

/-- **Capping is computable in polynomial time**, from the precision in binary to the capped
precision in unary. -/
theorem capPrecision_polyTime :
    ComputableInPolyTime capPrecision encBinaryInput encContractionInput := by
  have hrd := ComputableInPolyTime.snd encNat (encPair encNat encExplicitNetwork)
  have hd := (ComputableInPolyTime.snd encNat encExplicitNetwork).comp hrd
  have hbits : ComputableInPolyTime (fun d : ExplicitTensorNetwork ℕ => encExplicitNetwork d)
      encExplicitNetwork encBits := ComputableInPolyTime.of_eq fun _ => rfl
  have hlen := ComputableInPolyTime.length_bits_comp (hbits.comp hd)
  exact (ComputableInPolyTime.binary_min_unary' hlen
    (ComputableInPolyTime.fst encNat (encPair encNat encExplicitNetwork))).prod hrd

/-- **Direct summation with the precision in binary**: cap the precision, then sum directly. The
input `(P, r, d)` is encoded as `P` in binary, then `r` in binary and the network, and the output is
`d.contraction % 2 ^ P` in binary. -/
noncomputable def directContractionBinaryCertificate :
    NativeCertificate (fun x : ℕ × ℕ × ExplicitTensorNetwork ℕ => x.2.2.contraction % 2 ^ x.1)
      encBinaryInput encNat :=
  (directContractionCertificate.comp (NativeCertificate.ofPolyTime capPrecision_polyTime)).congr
    fun x => (directContraction_eq _ x.2.1 x.2.2).trans (contraction_mod_two_pow_min x.1 x.2.2)

/-- **The bounds of direct summation with the precision in binary**, on every input `(P, r, d)`:
polynomial workspace in the input length, and time `2 ^ m + 1` times a polynomial in the input
length, where `m` is the number of edges of `d`. -/
theorem directContractionBinaryCertificate_bounds :
    PolyBounded (fun x => (encBinaryInput x).length) directContractionBinaryCertificate.space ∧
      ∃ T : ℕ × ℕ × ExplicitTensorNetwork ℕ → ℕ,
        PolyBounded (fun x => (encBinaryInput x).length) T ∧
        ∀ x, directContractionBinaryCertificate.time x ≤ (2 ^ x.2.2.numEdges + 1) * T x := by
  obtain ⟨hspace, T, hT, htime⟩ := directContractionCertificate_bounds
  have hcap := NativeCertificate.ofPolyTime_isPolynomial capPrecision_polyTime
  have hlen : PolyBounded (fun x => (encBinaryInput x).length)
      fun x => (encContractionInput (capPrecision x)).length :=
    PolyBounded.of_forall_le 3 1 fun x => by
      have := min_le_left (encExplicitNetwork x.2.2).length x.1
      simp only [capPrecision, encContractionInput, length_encPair, encUnary_apply,
        List.length_replicate, pow_one]
      omega
  refine ⟨hcap.2.add (hspace.comp hlen), fun x =>
    (NativeCertificate.ofPolyTime capPrecision_polyTime).time x + T (capPrecision x),
    hcap.1.add (hT.comp hlen), fun x => ?_⟩
  have h := htime (capPrecision x)
  change (NativeCertificate.ofPolyTime capPrecision_polyTime).time x +
    directContractionCertificate.time (capPrecision x) ≤ _
  rw [Nat.mul_add]
  exact Nat.add_le_add (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)) h

/-- **The bounds of direct summation with the precision in binary, in one constant**: there is `K`
such that on every input the time is at most `K (n + 1) ^ K 2 ^ m` and the workspace at most
`K (n + 1) ^ K`, where `n` is the input length and `m` the number of edges. -/
theorem exists_directContractionBinaryCertificate_le :
    ∃ K : ℕ, ∀ x : ℕ × ℕ × ExplicitTensorNetwork ℕ,
      directContractionBinaryCertificate.time x ≤
          K * ((encBinaryInput x).length + 1) ^ K * 2 ^ x.2.2.numEdges ∧
        directContractionBinaryCertificate.space x ≤ K * ((encBinaryInput x).length + 1) ^ K :=
  let ⟨hspace, _, hT, htime⟩ := directContractionBinaryCertificate_bounds
  exists_le_of_bounds hspace hT htime

end Cslib.Circuits.Frontier.ExplicitTensorNetwork
