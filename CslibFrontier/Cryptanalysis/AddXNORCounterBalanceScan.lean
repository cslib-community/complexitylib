/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORSourceCounterCounts
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.PairMaxMin
import all CslibFrontier.Cryptanalysis.AddXNORCounterPairing
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.PairMaxMin
import all CslibFrontier.Computability.GenericRAM.Native.Combinators

/-!
# Executable balance scan of both dense counter arrays

Attach a side bit to the numeric state key, radix-sort both arrays together,
pair adjacent payloads, and reduce their binary minima into one scalar maximum.
The retained state of the final scan is a single binary number. No repeated
indexed lookup or growing remaining-list callback is used.

## Main results

* `pairs_graphs`: actual sorting/pairing aligns the two counters of each numeric state.
* `run_graphs`: the computed result is the maximum of their minima.
* `runCertificate`: one native machine for the complete tagged-sort/pair/scalar route.
-/

public section
namespace Cslib.Cryptanalysis.AddXNOR.CounterBalanceScan
open Turing.MultiTapeTM Cslib.GenericRAM

/-- Unary class depth followed by the original forward/backward count arrays. -/
abbrev Input := ℕ × SourceCounterCounts.Counts

/-- Frame unary depth before the existing framed-forward/unframed-backward count encoding. -/
abbrev encoding : Input ↪ List Bool := encPair encUnary SourceCounterCounts.countEncoding

/-- Both arrays are tagged on the key, rather than on the counter payload. -/
def tagged (input : Input) : List (ℕ × ℕ) :=
  let (_, (left, right)) := input
  left.map (CounterPairing.tag false) ++ right.map (CounterPairing.tag true)

/-- Runtime-width sorting makes every state's two side-tagged counters consecutive. -/
def sorted (input : Input) : List (ℕ × ℕ) :=
  let (p, _) := input
  RadixSort.sort (p+1, tagged input)

/-- Pair actual sorted payloads; class alignment is derived below, not an input premise. -/
def pairs (input : Input) : List (ℕ × ℕ) := AdjacentPairs.run (sorted input)

/-- Compute the balance scalar from both actual count arrays. -/
def run (input : Input) : ℕ := PairMaxMin.run (pairs input)

/-- Two dense numeric-key graphs are aligned by actual tags, sorting and adjacent pairing. -/
theorem pairs_graphs {p : ℕ} (left right : BitVec p → ℕ) :
    pairs (p, (CounterPull.graph left, CounterPull.graph right)) =
      List.ofFn (fun i : Fin (2^p) => (left (BitVec.ofFin i), right (BitVec.ofFin i))) := by
  let input := (p, (CounterPull.graph left, CounterPull.graph right))
  have perm : (tagged input).Perm (CounterPairing.canonical left right) := by
    have join := List.map_append_flatMap_perm (List.finRange (2^p))
      (fun i => CounterPairing.tag false (i.val, left (BitVec.ofFin i)))
      (fun i => [CounterPairing.tag true (i.val, right (BitVec.ofFin i))])
    simpa only [tagged, input, CounterPull.graph, List.ofFn_eq_map, List.map_map,
      Function.comp_def, ← List.map_eq_flatMap, CounterPairing.canonical, CounterPairing.tag,
      Bool.toNat_false, Bool.toNat_true, Nat.add_zero] using join
  have fits : ∀ row ∈ tagged input, row.1 < 2^(p+1) := by
    intro row hr
    simp only [tagged, input, List.mem_append, List.mem_map] at hr
    rcases hr with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ <;>
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr <;>
      simp only [CounterPairing.tag, Bool.toNat_false, Bool.toNat_true, pow_succ] <;> omega
  have hs := RadixSort.correct (p+1, tagged input) fits
  have full := hs.1.trans perm
  have ordered := full.eq_of_pairwise
    (fun x y hx hy hxy hyx => CounterPairing.canonical_key _ _ x y (full.subset hx) hy
      (Nat.le_antisymm hxy hyx)) hs.2 (CounterPairing.canonical_sorted _ _)
  change AdjacentPairs.run (RadixSort.sort (p+1, tagged input)) = _
  rw [ordered, CounterPairing.canonical, AdjacentPairs.run_flatMap, List.ofFn_eq_map]

/-- The executable scan returns exactly the finite maximum of the two populations' minima. -/
theorem run_graphs {p : ℕ} (left right : BitVec p → ℕ) :
    run (p, (CounterPull.graph left, CounterPull.graph right)) =
      Finset.univ.sup (fun g : BitVec p => min (left g) (right g)) := by
  rw [run, pairs_graphs, PairMaxMin.run_eq_listMax]
  apply Nat.le_antisymm
  · apply listMax_le
    intro row hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
    exact Finset.le_sup (f := fun g => min (left g) (right g)) (Finset.mem_univ _)
  · apply Finset.sup_le
    intro g _
    have member : (left g, right g) ∈ List.ofFn (fun i : Fin (2^p) =>
        (left (BitVec.ofFin i), right (BitVec.ofFin i))) := List.mem_ofFn.mpr ⟨g.toFin, rfl⟩
    exact le_listMax (f := fun r : ℕ × ℕ => min r.1 r.2) member

private theorem tags_computable : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ComputableInO (fun input : Bool × List (ℕ × ℕ) => input.2.map (CounterPairing.tag input.1))
      (encPair encBool encNatPairList) encNatPairList
      (fun input => (encPair encBool encNatPairList input).length+
        (input.2.length+1)*P (streamFilterWidth encBool (encPair encNat encNat) input))
      (fun input => (encPair encBool encNatPairList input).length+
        (input.2.length+1)*P (streamFilterWidth encBool (encPair encNat encNat) input)) := by
  have row : ComputableInPolyTime (fun q : Bool × (ℕ × ℕ) => [CounterPairing.tag q.1 q.2])
      (encPair encBool (encPair encNat encNat)) encNatPairList := by
    let e := encPair encBool (encPair encNat encNat)
    have key : ComputableTidilyInPolyTime (fun q : Bool × (ℕ × ℕ) => q.2.1) e encNat := by
      fun_prop
    have bit : ComputableTidilyInPolyTime (fun q : Bool × (ℕ × ℕ) => q.1.toNat) e encNat :=
      (ComputableTidilyInPolyTime.of_finite Bool.toNat).comp
        (ComputableTidilyInPolyTime.fst encBool (encPair encNat encNat))
    have doubled := ComputableTidilyInPolyTime.binary_mul.comp
      ((ComputableTidilyInPolyTime.const (encMid := encNat) 2).prod key)
    have tagged := (ComputableTidilyInPolyTime.binary_add.comp (doubled.prod bit)).prod
      ((ComputableTidilyInPolyTime.snd encBool (encPair encNat encNat)).snd')
    have single : ComputableTidilyInPolyTime (fun r : ℕ × ℕ => [r])
        (encPair encNat encNat) encNatPairList := .of_linear (.of_frame (fun _ => by simp))
    exact (single.comp tagged).computableInPolyTime.of_enc_eq (fun _ => rfl)
  obtain ⟨P, hp, mp, hc⟩ := ComputableInO.flatMap_stream row
  exact ⟨P, hp, mp, hc.of_enc_eq (fun _ => by rw [List.map_eq_flatMap])⟩

private noncomputable def tagCertificate : NativeCertificate
    (fun input : Bool × List (ℕ × ℕ) => input.2.map (CounterPairing.tag input.1))
    (encPair encBool encNatPairList) encNatPairList :=
  ⟨_, _, (Classical.choose_spec tags_computable).2.2⟩

private noncomputable def sortCertificate : NativeCertificate RadixSort.sort
    (encPair encUnary encNatPairList) encNatPairList :=
  ⟨_, _, (Classical.choose_spec RadixSort.computable).2.2⟩

private noncomputable def pairCertificate : NativeCertificate AdjacentPairs.run
    encNatPairList encNatPairList :=
  ⟨_, _, (Classical.choose_spec AdjacentPairs.run_computable).2.2⟩

private noncomputable def scalarCertificate : NativeCertificate PairMaxMin.run
    encNatPairList encNat :=
  ⟨_, _, (Classical.choose_spec PairMaxMin.run_computable).2.2⟩

/-- The actual unary key-width/header/copy and mapper/sort/pair/scan stages are composed here. -/
noncomputable def runCertificate : NativeCertificate run encoding encNat := by
  let original : NativeCertificate (id : Input → _) encoding encoding :=
    .linear (.of_eq (fun _ => rfl))
  let left := tagCertificate.comp ((NativeCertificate.const (em := encBool) false).prod
    original.snd.fst)
  let right := tagCertificate.comp ((NativeCertificate.const (em := encBool) true).prod
    original.snd.snd)
  let rows := (left.prod right).post (ComputableInO.append' (enc := (encPair encNat encNat)))
  let width := original.fst.post ComputableInO.unarySucc'
  exact (scalarCertificate.comp (pairCertificate.comp
    (sortCertificate.comp (width.prod rows)))).congr (fun _ => rfl)

/-- The installed scan is near-linear in dense table length with a polynomial only in
numeric-key and counter bit widths. All buffers/callback prefixes are charged. These
physical table hypotheses are discharged by the original-input counting DP. -/
theorem runCertificate_bounds : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ∀ {p B : ℕ} (left right : BitVec p → ℕ)
      (_ : ∀ g, Nat.size (left g) ≤ B) (_ : ∀ g, Nat.size (right g) ≤ B),
      runCertificate.time (p, (CounterPull.graph left, CounterPull.graph right)) ≤
        2^p*P (p+B+1) ∧
      runCertificate.space (p, (CounterPull.graph left, CounterPull.graph right)) ≤
        2^p*P (p+B+1) := by
  let A := Classical.choose tags_computable
  let R := Classical.choose RadixSort.computable
  let D := Classical.choose AdjacentPairs.run_computable
  let U := Classical.choose PairMaxMin.run_computable
  have ha : Cslib.PolynomiallyBounded A := (Classical.choose_spec tags_computable).1
  have ma : Monotone A := (Classical.choose_spec tags_computable).2.1
  have hr : Cslib.PolynomiallyBounded R := (Classical.choose_spec RadixSort.computable).1
  have mr : Monotone R := (Classical.choose_spec RadixSort.computable).2.1
  have hd : Cslib.PolynomiallyBounded D := (Classical.choose_spec AdjacentPairs.run_computable).1
  have md : Monotone D := (Classical.choose_spec AdjacentPairs.run_computable).2.1
  have hu : Cslib.PolynomiallyBounded U := (Classical.choose_spec PairMaxMin.run_computable).1
  have mu : Monotone U := (Classical.choose_spec PairMaxMin.run_computable).2.1
  let P := fun b => 200*b+200+4*A (4*b+4)+
    (b+2)*(20*b+20+3*R (5*b+5))+3*D (5*b+5)+3*U (15*b+15)
  have hp : Cslib.PolynomiallyBounded P := by dsimp only [P]; fun_prop
  have mp : Monotone P := by
    intro a b h
    have := ma (by omega : 4*a+4 ≤ 4*b+4)
    have := mr (by omega : 5*a+5 ≤ 5*b+5)
    have := md (by omega : 5*a+5 ≤ 5*b+5)
    have := mu (by omega : 15*a+15 ≤ 15*b+15)
    have prod := Nat.mul_le_mul (by omega : a+2 ≤ b+2)
      (by omega : 20*a+20+3*R (5*a+5) ≤ 20*b+20+3*R (5*b+5))
    dsimp only [P]
    omega
  refine ⟨P, hp, mp, ?_⟩
  intro p B left right hl hr
  let input := (p, (CounterPull.graph left, CounterPull.graph right))
  let b := p+B+1
  let E := 2^p
  have positive : 1 ≤ E := Nat.one_le_two_pow
  have old (f : BitVec p → ℕ) (hf : ∀ g, Nat.size (f g) ≤ B) :=
    CounterPull.graph_record_width f hf
  have oldMax (f : BitVec p → ℕ) (hf : ∀ g, Nat.size (f g) ≤ B) :
      streamRecordLength (encPair encNat encNat) (CounterPull.graph f) ≤ 2*p+1+B :=
    listMax_le (old f hf)
  have oldWire (f : BitVec p → ℕ) (hf : ∀ g, Nat.size (f g) ≤ B) :
      (encNatPairList (CounterPull.graph f)).length ≤ E*(4*b+4) := by
    have wire := length_encList_le (encPair encNat encNat) _ (old f hf)
    rw [CounterPull.graph_length] at wire
    exact wire.trans (Nat.mul_le_mul_left _ (by dsimp only [b]; omega))
  have taggedRow : ∀ row ∈ tagged input, (encPair encNat encNat row).length ≤ 3*b+3 := by
    intro row hrow
    have bound (f : BitVec p → ℕ) (hf : ∀ g, Nat.size (f g) ≤ B) (side : Bool)
        (i : Fin (2^p)) :
        (encPair encNat encNat (CounterPairing.tag side (i.val, f (BitVec.ofFin i)))).length ≤
          3*b+3 := by
      have key : 2*i.val+side.toNat < 2^(p+1) := by
        rw [pow_succ]
        have := i.isLt
        have := Bool.toNat_le side
        omega
      have bits := length_encNat_le_of_lt_two_pow key
      have value : (encNat (f (BitVec.ofFin i))).length ≤ B := by
        simpa only [encNat_apply, Nat.size_eq_bits_len] using hf (BitVec.ofFin i)
      simp only [CounterPairing.tag, length_encPair]
      dsimp only [b]
      omega
    simp only [tagged, input, List.mem_append, List.mem_map] at hrow
    rcases hrow with ⟨row, hrow, rfl⟩ | ⟨row, hrow, rfl⟩
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hrow
      exact bound left hl false i
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hrow
      exact bound right hr true i
  have taggedLength : (tagged input).length = 2*E := by
    simp [tagged, input, CounterPull.graph_length, E, two_mul]
  have sortedLength : (sorted input).length = 2*E :=
    (RadixSort.prefix_invariants (tagged input) (p+1)).2.length_eq.trans taggedLength
  have sortedRow : ∀ r ∈ sorted input, (encPair encNat encNat r).length ≤ 3*b+3 := by
    intro r hr
    exact taggedRow r ((RadixSort.prefix_invariants (tagged input) (p+1)).2.mem_iff.mp hr)
  have pairsLength : (pairs input).length ≤ 2*E :=
    (AdjacentPairs.length_le _).trans_eq sortedLength
  have pairRows := AdjacentPairs.record_bound (sorted input) (3*b+3) sortedRow
  have tagWidth (f : BitVec p → ℕ) (hf : ∀ g, Nat.size (f g) ≤ B) (side : Bool) :
      streamFilterWidth encBool (encPair encNat encNat) (side, CounterPull.graph f) ≤ 4*b+4 := by
    have h := oldMax f hf
    simp only [streamFilterWidth, encBool_apply, List.length_singleton]
    dsimp only [b]
    omega
  have sortWidth : streamFilterWidth encUnary (encPair encNat encNat)
      (p+1, tagged input) ≤ 5*b+5 := by
    have h := listMax_le taggedRow
    change streamRecordLength (encPair encNat encNat) (tagged input) ≤ 3*b+3 at h
    simp only [streamFilterWidth, encUnary_apply, List.length_replicate]
    dsimp only [b] at *
    omega
  have pairWidth : streamRecordLength (encPair encNat encNat) (sorted input)+1 ≤ 5*b+5 := by
    have h := listMax_le sortedRow
    change streamRecordLength (encPair encNat encNat) (sorted input) ≤ 3*b+3 at h
    omega
  have scalarWidth : PairMaxMin.width (pairs input) ≤ 15*b+15 := by
    have h := listMax_le pairRows
    change streamRecordLength (encPair encNat encNat) (pairs input) ≤ 3*(3*b+3)+1 at h
    dsimp only [PairMaxMin.width]
    omega
  have iw : (encoding input).length ≤ E*(20*b+20) := by
    have hleft := oldWire left hl
    have hright := oldWire right hr
    have copies := Nat.mul_le_mul_left p positive
    simp only [encoding, SourceCounterCounts.countEncoding, input, length_encPair,
      encUnary_apply, List.length_replicate]
    dsimp only [b] at *
    nlinarith only [hleft, hright, copies, positive, Nat.zero_le (E*B)]
  have tw (f : BitVec p → ℕ) (hf : ∀ g, Nat.size (f g) ≤ B) (side : Bool) :
      (encPair encBool encNatPairList (side, CounterPull.graph f)).length ≤ E*(10*b+10) := by
    have h := oldWire f hf
    simp only [length_encPair, encBool_apply, List.length_singleton]
    nlinarith only [h, positive, Nat.zero_le (E*b)]
  have sw : (RadixPartition.inputEncoding (p+1, tagged input)).length ≤ E*(20*b+20) := by
    have wire := length_encList_le (encPair encNat encNat) _ taggedRow
    rw [taggedLength] at wire
    have copies := Nat.mul_le_mul_left p positive
    simp only [RadixPartition.inputEncoding, RadixPartition.recordEncoding, length_encPair,
      encUnary_apply, List.length_replicate]
    dsimp only [b] at *
    nlinarith only [wire, copies, positive, Nat.zero_le (E*B)]
  have maps₁ := Nat.mul_le_mul (by omega : E+1 ≤ 2*E) (ma (tagWidth left hl false))
  have maps₂ := Nat.mul_le_mul (by omega : E+1 ≤ 2*E) (ma (tagWidth right hr true))
  have sortCost : (p+2)*((RadixPartition.inputEncoding (p+1, tagged input)).length+
      (2*E+1)*R (streamFilterWidth encUnary (encPair encNat encNat) (p+1, tagged input))) ≤
        E*((b+2)*(20*b+20+3*R (5*b+5))) := by
    have h := Nat.mul_le_mul (by omega : 2*E+1 ≤ 3*E) (mr sortWidth)
    calc
      _ ≤ (b+2)*(E*(20*b+20)+3*E*R (5*b+5)) :=
        Nat.mul_le_mul (by dsimp only [b]; omega) (Nat.add_le_add sw h)
      _ = _ := by ring
  have pairCost := Nat.mul_le_mul (by omega : 2*E+1 ≤ 3*E) (md pairWidth)
  have scalarCost := Nat.mul_le_mul (by omega : (pairs input).length+1 ≤ 3*E) (mu scalarWidth)
  have sortingSpaceCost : (RadixPartition.inputEncoding (p+1, tagged input)).length+
      R (streamFilterWidth encUnary (encPair encNat encNat) (p+1, tagged input)) ≤
      E*((b+2)*(20*b+20+3*R (5*b+5))) := by
    have h := Nat.mul_le_mul positive (mr sortWidth)
    calc
      _ ≤ E*(20*b+20)+E*R (5*b+5) := Nat.add_le_add sw (by simpa only [Nat.one_mul] using h)
      _ = E*(20*b+20+R (5*b+5)) := by ring
      _ ≤ _ := Nat.mul_le_mul_left E (by nlinarith [Nat.zero_le (b*R (5*b+5))])
  let common := 5*(encoding input).length+
    (encPair encBool encNatPairList (false, CounterPull.graph left)).length+
    (encPair encBool encNatPairList (true, CounterPull.graph right)).length+
    (E+1)*A (streamFilterWidth encBool (encPair encNat encNat) (false, CounterPull.graph left))+
    (E+1)*A (streamFilterWidth encBool (encPair encNat encNat) (true, CounterPull.graph right))+
    (2*E+1)*D (streamRecordLength (encPair encNat encNat) (sorted input)+1)+
    ((pairs input).length+1)*U (PairMaxMin.width (pairs input))
  have estimateTime : common+
      (p+2)*((RadixPartition.inputEncoding (p+1, tagged input)).length+
        (2*E+1)*R (streamFilterWidth encUnary (encPair encNat encNat) (p+1, tagged input))) ≤
      E*P b := by
    have twl := tw left hl false
    have twr := tw right hr true
    dsimp only [common, P]
    nlinarith only [iw, twl, twr, maps₁, maps₂, sortCost, pairCost, scalarCost,
      Nat.zero_le (E*b), Nat.zero_le E]
  have estimateSpace : common+(RadixPartition.inputEncoding (p+1, tagged input)).length+
      R (streamFilterWidth encUnary (encPair encNat encNat) (p+1, tagged input)) ≤ E*P b := by
    have twl := tw left hl false
    have twr := tw right hr true
    dsimp only [common, P]
    nlinarith only [iw, twl, twr, maps₁, maps₂, sortingSpaceCost, pairCost, scalarCost,
      Nat.zero_le (E*b), Nat.zero_le E]
  dsimp only [sorted, input, tagged, E] at sortedLength
  constructor
  · convert estimateTime using 1;
      simp only [runCertificate, tagCertificate, sortCertificate, pairCertificate,
        scalarCertificate,
        NativeCertificate.congr, NativeCertificate.comp, NativeCertificate.prod,
        NativeCertificate.const,
        NativeCertificate.fst, NativeCertificate.snd, NativeCertificate.post,
        NativeCertificate.linear,
        Function.comp_def, id_eq, CounterPull.graph_length, common, input, sorted, pairs,
        tagged,
        A, R, D, U, E, List.length_append, List.length_map, RadixPartition.recordEncoding,
        sortedLength]; ring
  · convert estimateSpace using 1;
      simp only [runCertificate, tagCertificate, sortCertificate, pairCertificate,
        scalarCertificate,
        NativeCertificate.congr, NativeCertificate.comp, NativeCertificate.prod,
        NativeCertificate.const,
        NativeCertificate.fst, NativeCertificate.snd, NativeCertificate.post,
        NativeCertificate.linear,
        Function.comp_def, id_eq, CounterPull.graph_length, common, input, sorted, pairs,
        tagged,
        A, R, D, U, E, List.length_append, List.length_map, RadixPartition.recordEncoding,
        sortedLength]; ring

end Cslib.Cryptanalysis.AddXNOR.CounterBalanceScan
