/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORClasses
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Containers
public import CslibFrontier.Computability.GenericRAM.Native.Certificate
public import CslibFrontier.Cryptanalysis.AddXNORDecision
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.RadixSort
import all CslibFrontier.Cryptanalysis.AddXNORDecision
import all CslibFrontier.Cryptanalysis.AddXNORReachability
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.RadixSort
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.RadixPartition
import all CslibFrontier.Computability.GenericRAM.Native.Combinators
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.StreamingFlatMap
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import Mathlib.Data.List.FinRange

/-!
# Tape-realized permutations of reachable-state counters

For a counter table stored as binary state/counter records, move every record
through one original Add/XNOR step (or its inverse) and radix-sort the resulting
keys. This realizes the two pull permutations before the addition stage of
[WangLvShenZhang2027], Lemma 8 (PDF pp. 21–22), without a table lookup per state.
Zero counters are physical records, not omitted support entries.

`run_graph` proves exact occurrence preservation for a complete table. The
uniform execution charges mapping, sorting and simultaneous materialization.
Interleaving the two outputs, initialization, operand iteration and readback
remain separate obligations before claiming the faster all-count prepass.

## Main results

* `run_graph`, `run_table_eq`: the exact recursive pulls, in canonical state order.
* `run_computable`: one machine, with linear record volume and polynomial scalar-width cost.
* `source_certificate`: derived bit time and prefix workspace on actual original DP counters.
-/

public section
namespace Cslib.Cryptanalysis.AddXNOR.CounterPull
open Turing.MultiTapeTM Cslib.GenericRAM

/-- Width, original operand, inverse-direction flag and operator flag. -/
abbrev Parameters := (ℕ × ℕ) × (Bool × Bool)

/-- Unary width followed by binary operand; then inverse and operator bits.
Within each pair the first coordinate is framed; the second is unframed. -/
abbrev parameterEncoding : Parameters ↪ List Bool :=
  encPair (encPair encUnary encNat) (encPair encBool encBool)

/-- Scalar parameters and all state/counter records. -/
abbrev Input := Parameters × List (ℕ × ℕ)

/-- Frame the scalar header, then the list of framed binary state/counter pairs. -/
abbrev encoding : Input ↪ List Bool := encPair parameterEncoding encNatPairList

/-- The runtime word width in the scalar header, distinct from physical wire width. -/
def wordWidth (parameters : Parameters) : ℕ :=
  let ((width, _), _) := parameters
  width

/-- Complement conjugacy executes inverse addition as well as inverse XNOR. -/
def image (parameters : Parameters) (state : ℕ) : ℕ :=
  let ((width, operand), (inverse, operator)) := parameters
  let modulus := 2 ^ width
  if inverse then
    modulus - 1 - natStep width (modulus - 1 - state % modulus) (operator, operand % modulus)
  else natStep width (state % modulus) (operator, operand % modulus)

/-- The exact word permutation used to relocate a stored counter. -/
def wordImage {m : ℕ} (inverse operator : Bool) (a s : BitVec m) : BitVec m :=
  if inverse then unstep operator s a else step operator s a

private theorem wordImage_inverse {m : ℕ} (inverse operator : Bool) (a s : BitVec m) :
    wordImage (!inverse) operator a (wordImage inverse operator a s) = s := by
  cases inverse <;> simp [wordImage, unstep_step, step_unstep]

theorem image_toNat {m : ℕ} (inverse operator : Bool) (a s : BitVec m) :
    image ((m, a.toNat), (inverse, operator)) s.toNat =
      (wordImage inverse operator a s).toNat := by
  cases inverse
  · simp [image, wordImage, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt s.isLt, natStep_toNat]
  · have hi : unstep operator s a = ~~~(step operator (~~~s) a) := by
      simpa only [BitVec.not_not] using unstep_not operator (~~~s) a
    simp only [image, ↓reduceIte, Nat.mod_eq_of_lt a.isLt,
      Nat.mod_eq_of_lt s.isLt, wordImage, hi, BitVec.toNat_not]
    rw [← BitVec.toNat_not, natStep_toNat]

theorem image_lt (parameters : Parameters) (state : ℕ) :
    image parameters state < 2 ^ wordWidth parameters := by
  rcases parameters with ⟨⟨width, operand⟩, inverse, operator⟩
  cases inverse <;> simp only [image, wordWidth, Bool.false_eq_true, ↓reduceIte]
  · exact natStep_lt _ _ _
  · have := Nat.two_pow_pos width
    omega

/-- Complete state order, with a physical record for every zero counter too. -/
def graph {m : ℕ} (f : BitVec m → ℕ) : List (ℕ × ℕ) :=
  List.ofFn fun i : Fin (2 ^ m) => (i.val, f (BitVec.ofFin i))

theorem graph_length {m : ℕ} (f : BitVec m → ℕ) : (graph f).length = 2 ^ m := by
  simp only [graph, List.length_ofFn]

private theorem graph_sorted {m : ℕ} (f : BitVec m → ℕ) :
    (graph f).Pairwise (fun a b => a.1 ≤ b.1) := by
  apply List.pairwise_ofFn.mpr
  intro i j hij
  exact Nat.le_of_lt hij

/-- A complete serialized table has exactly one counter at each key. -/
theorem graph_key_injective {m : ℕ} (f : BitVec m → ℕ) (a b : ℕ × ℕ)
    (ha : a ∈ graph f) (hb : b ∈ graph f) (hk : a.1 = b.1) : a = b := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hb
  have he : i = j := Fin.ext hk
  subst j
  rfl

/-- Each input record is read once by the mapper; no current table is captured by its callback. -/
def mapped (input : Input) : List (ℕ × ℕ) :=
  let (parameters, rows) := input
  rows.map fun (state, counter) => (image parameters state, counter)

/-- Actual sorted pull implementation on binary encoded records. -/
def run (input : Input) : List (ℕ × ℕ) :=
  let (((width, _), _), _) := input
  RadixSort.sort (width, mapped input)

/-- The machine's only semantic input is its actual table. Both inverse and forward relocation
are derived bijections, so all zero entries and multiplicities survive. -/
theorem run_graph {m : ℕ} (inverse operator : Bool) (a : BitVec m) (f : BitVec m → ℕ) :
    (run (((m, a.toNat), (inverse, operator)), graph f)).Perm
      (graph fun s => f (wordImage (!inverse) operator a s)) ∧
    (run (((m, a.toNat), (inverse, operator)), graph f)).Pairwise (fun a b => a.1 ≤ b.1) := by
  let e : Equiv.Perm (BitVec m) :=
    ⟨wordImage inverse operator a, wordImage (!inverse) operator a,
      wordImage_inverse inverse operator a, by
        intro s
        simpa only [Bool.not_not] using wordImage_inverse (!inverse) operator a s⟩
  let σ : Equiv.Perm (Fin (2 ^ m)) :=
    BitVec.equivFin.symm.toEquiv.trans (e.trans BitVec.equivFin.toEquiv)
  let target := fun i : Fin (2 ^ m) => (i.val, f (wordImage (!inverse) operator a (BitVec.ofFin i)))
  have relocate : (mapped (((m, a.toNat), (inverse, operator)), graph f)).Perm
      (graph fun s => f (wordImage (!inverse) operator a s)) := by
    have he : mapped (((m, a.toNat), (inverse, operator)), graph f) =
        List.ofFn (target ∘ σ) := by
      rw [mapped, graph, List.map_ofFn]
      apply congrArg List.ofFn
      funext i
      change (image ((m, a.toNat), (inverse, operator)) (BitVec.ofFin i).toNat,
        f (BitVec.ofFin i)) =
        ((wordImage inverse operator a (BitVec.ofFin i)).toNat,
          f (wordImage (!inverse) operator a (wordImage inverse operator a (BitVec.ofFin i))))
      rw [image_toNat, wordImage_inverse]
    rw [he]
    exact σ.ofFn_comp_perm target
  have sort := RadixSort.correct
    (m, mapped (((m, a.toNat), (inverse, operator)), graph f)) (by
      intro row hr
      obtain ⟨⟨state, counter⟩, _, rfl⟩ := List.mem_map.mp hr
      exact image_lt ((m, a.toNat), (inverse, operator)) state)
  exact ⟨sort.1.trans relocate, sort.2⟩

/-- The existing recursive DP pull selected by direction and operator. -/
def pulled {m : ℕ} (table : WordTable ℕ m) (inverse operator : Bool) (a : BitVec m) :
    WordTable ℕ m :=
  if operator then (WordTable.xorPull (stateKey (~~~a)) table).ret
  else if inverse then (WordTable.addPull (stateKey a) false table).ret
  else (WordTable.addPull (stateKey (~~~a)) true table).ret

/-- Relocation is exactly the native table permutation; inverse and forward dictionaries
are never identified merely because their resource bounds have the same shape. -/
theorem pulled_read {m : ℕ} (table : WordTable ℕ m) (inverse operator : Bool)
    (a s : BitVec m) :
    (pulled table inverse operator a).read s = table.read (wordImage (!inverse) operator a s) := by
  cases inverse <;> cases operator <;>
    simp [pulled, wordImage, WordTable.xorPull_read, WordTable.addPull_read, step, unstep,
      BitVec.not_xor_right, BitVec.sub_eq_add_neg, BitVec.neg_eq_not_add, add_assoc]

/-- The actual encoded sorting route computes each actual recursive pull, including all zeros. -/
theorem run_table {m : ℕ} (table : WordTable ℕ m) (inverse operator : Bool) (a : BitVec m) :
    (run (((m, a.toNat), (inverse, operator)), graph table.read)).Perm
      (graph (pulled table inverse operator a).read) := by
  have h := (run_graph inverse operator a table.read).1
  have he : (pulled table inverse operator a).read =
      fun s => table.read (wordImage (!inverse) operator a s) :=
    funext (pulled_read table inverse operator a)
  rwa [he]

/-- Sorting restores the canonical complete state order, not merely an unspecified permutation. -/
theorem run_table_eq {m : ℕ} (table : WordTable ℕ m) (inverse operator : Bool) (a : BitVec m) :
    run (((m, a.toNat), (inverse, operator)), graph table.read) =
      graph (pulled table inverse operator a).read := by
  have hp := run_table table inverse operator a
  apply hp.eq_of_pairwise
    (fun x y hx hy hxy hyx => graph_key_injective _ x y (hp.subset hx) hy
      (Nat.le_antisymm hxy hyx))
    (run_graph inverse operator a table.read).2 (graph_sorted _)

/-- Physical scalar and maximum record width; no entire table enters the polynomial factor. -/
def width (input : Input) : ℕ :=
  let (parameters, rows) := input
  (parameterEncoding parameters).length +
    streamRecordLength (encPair encNat encNat) rows + 1

private theorem emit_polyTime : ComputableInPolyTime
    (fun q : Parameters × (ℕ × ℕ) => [(image q.1 q.2.1, q.2.2)])
    (encPair parameterEncoding (encPair encNat encNat)) encNatPairList := by
  let input := encPair parameterEncoding (encPair encNat encNat)
  have w : ComputableInPolyTime (fun q : Parameters × (ℕ × ℕ) => q.1.1.1) input encUnary := by
    fun_prop
  have modulus := ComputableInPolyTime.binary_pow' (.const 2) w
  have s : ComputableInPolyTime (fun q : Parameters × (ℕ × ℕ) => q.2.1) input encNat := by
    fun_prop
  have a : ComputableInPolyTime (fun q : Parameters × (ℕ × ℕ) => q.1.1.2) input encNat := by
    fun_prop
  have inverse : ComputableInPolyTime (fun q : Parameters × (ℕ × ℕ) => q.1.2.1)
      input encBool := by fun_prop
  have operator : ComputableInPolyTime (fun q : Parameters × (ℕ × ℕ) => q.1.2.2)
      input encBool := by fun_prop
  have state := ComputableInPolyTime.binary_mod.comp (s.prod modulus)
  have operand := ComputableInPolyTime.binary_mod.comp (a.prod modulus)
  have mask := ComputableInPolyTime.binary_sub' modulus (.const 1)
  have complement := ComputableInPolyTime.binary_sub' mask state
  have fw := natStep_polyTime.comp ((w.prod state).prod (operator.prod operand))
  have bw := ComputableInPolyTime.binary_sub' mask
    (natStep_polyTime.comp ((w.prod complement).prod (operator.prod operand)))
  have key := inverse.ite bw fw
  have row := key.prod (ComputableInPolyTime.snd parameterEncoding (encPair encNat encNat)).snd'
  have single : ComputableTidilyInPolyTime (fun r : ℕ × ℕ => [r])
      (encPair encNat encNat) encNatPairList := .of_linear (.of_frame (fun _ => by simp))
  exact (single.computableInPolyTime.comp row).of_enc_eq (fun _ => rfl)

private theorem mapped_computable : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ComputableInO mapped encoding encNatPairList
      (fun input => (encoding input).length + (input.2.length + 1) * P (width input))
      (fun input => (encoding input).length + (input.2.length + 1) * P (width input)) := by
  obtain ⟨P, hp, hm, h⟩ := ComputableInO.flatMap_stream emit_polyTime
  refine ⟨P, hp, hm, ?_⟩
  have hh := h.of_enc_eq (g := mapped) (encC := encNatPairList) (fun input => by
    rcases input with ⟨parameters, rows⟩
    simp only [mapped, List.map_eq_flatMap])
  simpa only [width, streamFilterWidth] using hh

/-- A real uniform pull execution, including the mapper, radix passes, input/output buffers
and every callback temporary. No traversal, lookup or resource conclusion is a premise. -/
theorem run_computable : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ComputableInO run encoding encNatPairList
      (fun input => (input.2.length + 1) * P (width input))
      (fun input => (input.2.length + 1) * P (width input)) := by
  obtain ⟨A, ha, ma, hmap⟩ := mapped_computable
  obtain ⟨R, hr, mr, hsort⟩ := RadixSort.computable
  let P := fun B => 10 * B + 10 + A B + (B + 1) * (10 * B + 10 + R (5 * B + 5))
  have hp : Cslib.PolynomiallyBounded P := by dsimp only [P]; fun_prop
  have mp : Monotone P := by
    intro a b hab
    have hA := ma hab
    have hR := mr (by omega : 5 * a + 5 ≤ 5 * b + 5)
    have hm := Nat.mul_le_mul (by omega : a + 1 ≤ b + 1)
      (by omega : 10*a+10+R (5*a+5) ≤ 10*b+10+R (5*b+5))
    dsimp only [P]
    omega
  let original : NativeCertificate (id : Input → Input) encoding encoding :=
    .linear (.of_eq (fun _ => rfl))
  have keyWidth := original.fst.fst.fst.computes
  have prepare := keyWidth.prod hmap
  have composed := (hsort.comp prepare).of_enc_eq (g := run) (encC := encNatPairList)
    (fun _ => rfl)
  have bounds (input : Input) :
      let (((m, _), _), rows) := input
      let I := (encoding input).length
      let B := width input
      let J := (RadixPartition.inputEncoding (m, mapped input)).length
      let C := streamFilterWidth encUnary RadixPartition.recordEncoding (m, mapped input)
      I + (I + (rows.length+1)*A B) + (m+1)*(J+(rows.length+1)*R C) ≤
          (rows.length+1)*P B ∧
      I + (I + (rows.length+1)*A B) + (J+R C) ≤ (rows.length+1)*P B := by
    rcases input with ⟨⟨⟨m, a⟩, inverse, operator⟩, rows⟩
    let input : Input := (((m, a), (inverse, operator)), rows)
    let B := width input
    let N := rows.length + 1
    let J := (RadixPartition.inputEncoding (m, mapped input)).length
    let C := streamFilterWidth encUnary RadixPartition.recordEncoding (m, mapped input)
    have mB : m ≤ B := by
      dsimp only [B, width, input, parameterEncoding]
      simp only [length_encPair, encUnary_apply, encBool_apply, List.length_replicate,
        List.length_singleton]
      omega
    have old (row : ℕ × ℕ) (h : row ∈ rows) : (encPair encNat encNat row).length ≤ B := by
      have := le_listMax (f := fun r => (encPair encNat encNat r).length) h
      change (encPair encNat encNat row).length ≤
        streamRecordLength (encPair encNat encNat) rows at this
      dsimp only [B, width, input]
      omega
    have rowBound (row : ℕ × ℕ) (h : row ∈ mapped input) :
        (RadixPartition.recordEncoding row).length ≤ 4*B+4 := by
      obtain ⟨⟨key, value⟩, hv, rfl⟩ := List.mem_map.mp h
      have hi := length_encNat_le_of_lt_two_pow (image_lt input.1 key)
      change (encNat (image input.1 key)).length ≤ m at hi
      have ho := old (key, value) hv
      simp only [length_encPair] at ho
      change (encPair encNat encNat (image input.1 key, value)).length ≤ 4*B+4
      rw [length_encPair]
      change 2 * (encNat (image input.1 key)).length + 1 + (encNat value).length ≤ 4*B+4
      omega
    have mappedLength : (mapped input).length = rows.length := by
      change (rows.map _).length = rows.length
      exact List.length_map _
    have iBound : (encoding input).length ≤ N * (3*B+3) := by
      have hl := length_encList_le (encPair encNat encNat) rows old
      have hparam : (parameterEncoding input.1).length ≤ B := by
        dsimp only [B, width]; omega
      change (encNatPairList rows).length ≤ rows.length * (2*B+1) at hl
      change (encPair parameterEncoding encNatPairList input).length ≤ _
      rw [length_encPair]
      dsimp only [N]
      change 2 * (parameterEncoding input.1).length + 1 + (encNatPairList rows).length ≤ _
      nlinarith
    have jBound : J ≤ N * (10*B+10) := by
      have hl := length_encList_le RadixPartition.recordEncoding (mapped input) rowBound
      rw [mappedLength] at hl
      dsimp only [J, RadixPartition.inputEncoding]
      simp only [length_encPair, encUnary_apply, List.length_replicate]
      dsimp only [N]
      nlinarith
    have cBound : C ≤ 5*B+5 := by
      have := listMax_le rowBound
      change streamRecordLength RadixPartition.recordEncoding (mapped input) ≤ 4*B+4 at this
      dsimp only [C, streamFilterWidth]
      simp only [encUnary_apply, List.length_replicate]
      omega
    have hR := mr cBound
    have sortTime : (m+1)*(J+N*R C) ≤ N*((B+1)*(10*B+10+R (5*B+5))) := by
      calc
        _ ≤ (B+1)*(N*(10*B+10)+N*R (5*B+5)) :=
          Nat.mul_le_mul (by omega) (Nat.add_le_add jBound (Nat.mul_le_mul_left N hR))
        _ = _ := by ring
    have sortSpace : J+R C ≤ (m+1)*(J+N*R C) := by
      have hn : 1 ≤ N := by dsimp only [N]; omega
      nlinarith only [hn, Nat.zero_le (m * (J+N*R C)), Nat.zero_le J]
    have setup : (encoding input).length + ((encoding input).length+N*A B) ≤
        N*(10*B+10+A B) := by nlinarith only [iBound, Nat.zero_le (N*B), Nat.zero_le N]
    have ht := Nat.add_le_add setup sortTime
    have hbound : (encoding input).length + ((encoding input).length+N*A B) +
        (m+1)*(J+N*R C) ≤ N*P B := by
      dsimp only [P]
      nlinarith only [ht]
    exact ⟨hbound, (Nat.add_le_add_left sortSpace _).trans hbound⟩
  refine ⟨P, hp, mp, composed.mono_le (fun input => ?_) (fun input => ?_)⟩
  · simpa only [NativeCertificate.fst_time, original, NativeCertificate.linear_time,
      mapped, List.length_map, id_eq] using (bounds input).1
  · simpa only [NativeCertificate.fst_space, original, NativeCertificate.linear_space,
      id_eq] using (bounds input).2

/-- Complete-table physical width follows from counter bits, not from a unit-cost record model. -/
theorem graph_width {m B : ℕ} (f : BitVec m → ℕ) (bound : ∀ s, Nat.size (f s) ≤ B)
    (a : BitVec m) (inverse operator : Bool) :
    width (((m, a.toNat), (inverse, operator)), graph f) ≤ 10 * (m+B+1) := by
  have ha := length_encNat_le_of_lt_two_pow a.isLt
  have header : (parameterEncoding ((m, a.toNat), (inverse, operator))).length ≤ 6*m+7 := by
    simp only [parameterEncoding, length_encPair, encUnary_apply, List.length_replicate,
      encBool_apply, List.length_singleton]
    omega
  have records : ∀ row ∈ graph f, (encPair encNat encNat row).length ≤ 2*m+1+B := by
    intro row hrow
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hrow
    have key := length_encNat_le_of_lt_two_pow i.isLt
    have value : (encNat (f (BitVec.ofFin i))).length ≤ B := by
      simpa only [encNat_apply, Nat.size_eq_bits_len] using bound (BitVec.ofFin i)
    simp only [length_encPair]
    change 2*(encNat i.val).length+1+(encNat (f (BitVec.ofFin i))).length ≤ _
    omega
  have maximum := listMax_le records
  change streamRecordLength (encPair encNat encNat) (graph f) ≤ 2*m+1+B at maximum
  dsimp only [width]
  omega

/-- One actual pull machine handles every original counter prefix/suffix and both operators.
The polynomial uses original word/count widths; the exponential factor is only the number
of projected states. Initialization, pairing and the enclosing DP loop are not included. -/
theorem source_certificate : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ∃ c : NativeCertificate run encoding encNatPairList,
      ∀ m q (as : Fin q → BitVec m) (s a : BitVec m) (inverse operator : Bool),
        c.time (((m, a.toNat), (inverse, operator)),
          graph (WordTable.classCounters (List.ofFn as) s).read) ≤ 2^m * P (m+q+1) ∧
        c.space (((m, a.toNat), (inverse, operator)),
          graph (WordTable.classCounters (List.ofFn as) s).read) ≤ 2^m * P (m+q+1) ∧
        c.time (((m, a.toNat), (inverse, operator)),
          graph (WordTable.backwardCounters (List.ofFn as) s).read) ≤ 2^m * P (m+q+1) ∧
        c.space (((m, a.toNat), (inverse, operator)),
          graph (WordTable.backwardCounters (List.ofFn as) s).read) ≤ 2^m * P (m+q+1) := by
  obtain ⟨P, hp, mp, hc⟩ := run_computable
  let resource := fun input : Input => (input.2.length+1) * P (width input)
  let c : NativeCertificate run encoding encNatPairList := ⟨resource, resource, hc⟩
  let Q := fun B => 2 * P (10*(B+1))
  have hQ : Cslib.PolynomiallyBounded Q := by dsimp only [Q]; fun_prop
  have mQ : Monotone Q := by
    intro a b hab
    exact Nat.mul_le_mul_left 2 (mp (by omega : 10*(a+1) ≤ 10*(b+1)))
  have cost {m q : ℕ} (f : BitVec m → ℕ) (bound : ∀ s, Nat.size (f s) ≤ q+1)
      (a : BitVec m) (inverse operator : Bool) :
      resource (((m, a.toNat), (inverse, operator)), graph f) ≤ 2^m * Q (m+q+1) := by
    have hw := graph_width f bound a inverse operator
    have hP := mp hw
    have positive := Nat.two_pow_pos m
    dsimp only [resource, Q]
    rw [graph_length]
    have hm := Nat.mul_le_mul_left (2^m+1) hP
    have he : m+(q+1)+1 = (m+q+1)+1 := by omega
    rw [he] at hm
    nlinarith only [hm, positive]
  refine ⟨Q, hQ, mQ, c, fun m q as s a inverse operator => ?_⟩
  have hf := cost _ (WordTable.classCounters_size_le as s) a inverse operator
  have hb := cost _ (WordTable.backwardCounters_size_le as s) a inverse operator
  exact ⟨hf, hf, hb, hb⟩

end Cslib.Cryptanalysis.AddXNOR.CounterPull
