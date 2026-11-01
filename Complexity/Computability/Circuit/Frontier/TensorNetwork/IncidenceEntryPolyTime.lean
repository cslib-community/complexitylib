/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceEntry
import Complexity.Computability.GenericRAM.Native.SubsetPairFold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.BinaryDiv
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Choose
import Complexity.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListLookup
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListMap
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPrimitives
import Complexity.Foundations.Data.BitString.Binary
import Mathlib.Data.List.GetD

/-!
# The polynomial-time steps of the entries of the incidence network

The entry procedure of the incidence network of Lemma D.2 of [OpenAI2026ETH] (p. 56,
`Cslib.Circuits.Frontier.IncidenceNetwork.incEntry`) is polynomial-time apart from the sum of a
row over the `2 ^ |sel|` words on its selected incidences. This file proves the polynomial-time
steps, with precisions, truncation orders and selected numbers in unary: reading the indices
(`blockIndices_polyTime`), unranking and selecting (`selected_polyTime`), the validity test
(`validIndices_polyTime`), the context of a row (`rowContext_polyTime`), one term of the sum of a
row (`rowBody_polyTime`), and the entries of columns (`colEntry_polyTime`). The source states these
costs: "Each term costs polynomially many bit operations" and "The variable-side entries and checks
for invalid wire indices take polynomial time" (p. 56).

## Main results

* `Cslib.Circuits.Frontier.IncidenceNetwork.blockIndices_polyTime`,
  `Cslib.Circuits.Frontier.IncidenceNetwork.selected_polyTime`,
  `Cslib.Circuits.Frontier.IncidenceNetwork.validIndices_polyTime`: decoding.
* `Cslib.Circuits.Frontier.IncidenceNetwork.rowContext_polyTime`,
  `Cslib.Circuits.Frontier.IncidenceNetwork.rowValid_polyTime`: the context and validity of a row.
* `Cslib.Circuits.Frontier.IncidenceNetwork.factorCoeffs_polyTime`,
  `Cslib.Circuits.Frontier.IncidenceNetwork.rowTerm_polyTime`,
  `Cslib.Circuits.Frontier.IncidenceNetwork.rowBody_polyTime`: one term of a row.
* `Cslib.Circuits.Frontier.IncidenceNetwork.colEntry_polyTime`: the entries of columns.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Lemma D.2 (pp. 55–56).
-/

public section

namespace Cslib.Circuits.Frontier.IncidenceNetwork

open Turing.MultiTapeTM Cslib.GenericRAM GaloisRingArith Cslib.BitString

section PolyTime

open ComputableInPolyTime

/-! ### Decoding -/

/-- A block has at most as many index wires as incidences: `C(N, d) ≤ 2 ^ N`. -/
theorem blockWires_le (b : Block) : blockWires b ≤ b.1.length :=
  Nat.clog_le_of_le_pow (Nat.choose_le_two_pow _ _)

/-- The number of index wires of a block is polynomial-time, in unary. -/
theorem blockWires_polyTime : ComputableInPolyTime blockWires encBlock encUnary :=
  binary_clog_two.comp (binary_choose'
    ((length_list (encPair encNat encNat)).comp (fst _ _)) (snd _ _))

/-- One step of reading the indices is polynomial-time. -/
theorem indexStep_polyTime :
    ComputableInPolyTime (fun p : (List Bool × List ℕ) × Block => indexStep p.1 p.2)
      (encPair (encPair encBits (encList encNat)) encBlock) (encPair encBits (encList encNat)) := by
  have hst := fst (encPair encBits (encList encNat)) encBlock
  have hb := snd (encPair encBits (encList encNat)) encBlock
  have hw := blockWires_polyTime.comp hb
  have hbits := (fst encBits (encList encNat)).comp hst
  have hacc := (snd encBits (encList encNat)).comp hst
  have hval := bitsBinaryValue.comp (bitsReverse.comp (bitsTakeWithInput hbits hw))
  exact ((bitsDropWithInput hbits hw).prod (listAppend' hacc (cons' hval (const [])))).of_enc_eq
    fun p => by simp only [indexStep, lsbValue_eq_binaryValue_reverse, Function.comp_apply]

/-- A step of reading the indices adds at most `2 N + 1` bits for a block of `N` incidences. -/
theorem length_indexStep_le (st : List Bool × List ℕ) (b : Block) :
    (encPair encBits (encList encNat) (indexStep st b)).length ≤
      (encPair encBits (encList encNat) st).length + 2 * b.1.length + 1 := by
  have hval : (encNat (lsbValue (st.1.take (blockWires b)))).length ≤ b.1.length := by
    change (lsbValue _).bits.length ≤ _
    rw [Nat.size_eq_bits_len]
    refine (Nat.size_le.mpr ((lsbValue_lt _).trans_le
      (Nat.pow_le_pow_right (by norm_num) ?_))).trans le_rfl
    exact (List.length_take_le _ _).trans (blockWires_le b)
  simp only [indexStep, length_encPair, encBits_apply, length_encList, List.map_append,
    List.sum_append, List.length_drop, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

/-- **Reading the indices of the blocks is polynomial-time.** -/
theorem blockIndices_polyTime :
    ComputableInPolyTime (fun q : List Block × List Bool => blockIndices q.1 q.2)
      (encPair (encList encBlock) encBits) (encList encNat) := by
  let encQ := encPair (encList encBlock) encBits
  let encS := encPair encBits (encList encNat)
  have hinit : ComputableInPolyTime (fun q : List Block × List Bool => (q.2, ([] : List ℕ)))
      encQ encS := (snd (encList encBlock) encBits).prod (const [])
  have hlist : ComputableInPolyTime (fun q : List Block × List Bool => q.1) encQ
      (encList encBlock) := fst (encList encBlock) encBits
  have hp1 : ComputableInPolyTime
      (fun p : ((List Block × List Bool) × (List Bool × List ℕ)) × Block => p.1.2)
      (encPair (encPair encQ encS) encBlock) encS :=
    (snd encQ encS).comp (fst (encPair encQ encS) encBlock)
  have hp2 : ComputableInPolyTime
      (fun p : ((List Block × List Bool) × (List Bool × List ℕ)) × Block => p.2)
      (encPair (encPair encQ encS) encBlock) encBlock :=
    snd (encPair encQ encS) encBlock
  have hstep := indexStep_polyTime.comp (hp1.prod hp2)
  have hgrowth : ∀ (q : List Block × List Bool) (st : List Bool × List ℕ) (b : Block),
      b ∈ q.1 → (encS (indexStep st b)).length ≤ (encS st).length + (2 * (encQ q).length + 1) := by
    intro q st b hb
    have h1 : (encS (indexStep st b)).length ≤ (encS st).length + 2 * b.1.length + 1 :=
      length_indexStep_le st b
    have h2 : b.1.length ≤ (encQ q).length := by
      have h4 := length_le_encList_of_mem encBlock hb
      have h3 : b.1.length ≤ (encBlock b).length := by
        have h5 := sum_length_le_length_encList (encPair encNat encNat) b.1
        have h6 : b.1.length ≤ (b.1.map fun a => (encPair encNat encNat a).length).sum := by
          refine (List.length_map (f := fun a => (encPair encNat encNat a).length)
            (as := b.1)).symm.le.trans ?_
          exact List.length_le_sum_of_one_le _ fun x hx => by
            obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx
            simp only [length_encPair]
            omega
        simp only [encBlock, length_encPair]
        omega
      simp only [encQ, length_encPair]
      omega
    omega
  have hfold := foldlWithInput_of_bounded_growth (encA := encBlock) (encL := encList encBlock)
    (encB := encS) (step := fun _ st b => indexStep st b) hinit
    ⟨hlist, hstep, inferInstance, inferInstance⟩
    (growth := fun q => 2 * (encQ q).length + 1)
    ⟨((PolyBounded.const 2).mul .self).add (.const 1), hgrowth⟩
  exact ((snd encBits (encList encNat)).comp hfold).of_enc_eq fun q =>
    congrArg (encList encNat) (show blockIndices q.1 q.2 = _ from rfl)

/-- **Selecting the incidences of a block at an index is polynomial-time.** -/
theorem selectBlock_polyTime :
    ComputableInPolyTime (fun q : Block × ℕ => selectBlock q.1 q.2)
      (encPair encBlock encNat) (encList (encPair encNat encNat)) := by
  have hb := fst encBlock encNat
  have hι := snd encBlock encNat
  have hinc := (fst (encList (encPair encNat encNat)) encUnary).comp hb
  have hN := (length_list (encPair encNat encNat)).comp hinc
  have hd := (snd (encList (encPair encNat encNat)) encUnary).comp hb
  have hmask := SubsetPairFold.unrankCombination_polyTime.comp ((hN.prod hd).prod hι)
  have hzip := (zip (encPair encNat encNat) encBool).comp (hinc.prod (bitsToList.comp hmask))
  have htest : ComputableInPolyTime
      (fun p : (Block × ℕ) × ((ℕ × ℕ) × Bool) => p.2.2)
      (encPair (encPair encBlock encNat) (encPair (encPair encNat encNat) encBool)) encBool :=
    (snd (encPair encNat encNat) encBool).comp (snd _ _)
  have hfilter := filterWithInput (test := fun (_ : Block × ℕ) (p : (ℕ × ℕ) × Bool) => p.2)
    hzip htest
  have hmap := (map (fst (encPair encNat encNat) encBool)).comp hfilter
  exact hmap.of_enc_eq fun q => rfl

/-- **The selected incidences are polynomial-time**, from the blocks and the indices. -/
theorem selected_polyTime :
    ComputableInPolyTime (fun q : List Block × List ℕ => selected q.1 q.2)
      (encPair (encList encBlock) (encList encNat)) (encList (encPair encNat encNat)) := by
  have hzip := zip encBlock encNat
  have hf := selectBlock_polyTime.comp
    (snd (encPair (encList encBlock) (encList encNat)) (encPair encBlock encNat))
  exact (flatMapWithInput hzip hf).of_enc_eq fun q => rfl

/-- **The validity test is polynomial-time.** -/
theorem validIndices_polyTime :
    ComputableInPolyTime (fun q : List Block × List ℕ => validIndices q.1 q.2)
      (encPair (encList encBlock) (encList encNat)) encBool := by
  have hzip := zip encBlock encNat
  have hp := snd (encPair (encList encBlock) (encList encNat)) (encPair encBlock encNat)
  have hb := (fst encBlock encNat).comp hp
  have hι := (snd encBlock encNat).comp hp
  have hN := (length_list (encPair encNat encNat)).comp
    ((fst (encList (encPair encNat encNat)) encUnary).comp hb)
  have hd := (snd (encList (encPair encNat encNat)) encUnary).comp hb
  have htest := binary_lt' hι (binary_choose' hN hd)
  exact (allWithInput hzip htest).of_enc_eq fun q => rfl

/-- The encoding of the context of a row: `P` and `ℓ` in unary, then the tests and the selected
incidences. -/
abbrev encRowCtx : RowCtx ↪ List Bool :=
  encPair encUnary (encPair encUnary (encPair (encList (encList (encList encNat)))
    (encList (encPair encNat encNat))))

/-- **The context of a row is polynomial-time.** -/
theorem rowContext_polyTime :
    ComputableInPolyTime (fun q : RowDesc × List Bool => rowContext q.1 q.2)
      (encPair encRowDesc encBits) encRowCtx := by
  have hrow := fst encRowDesc encBits
  have hbs := snd encRowDesc encBits
  have hP := (fst _ _).comp hrow
  have hr1 := (snd _ _).comp hrow
  have hℓ := (fst _ _).comp hr1
  have hr2 := (snd _ _).comp hr1
  have htests := (fst _ _).comp hr2
  have hblocks := (snd (encList (encList (encList encNat))) (encList encBlock)).comp hr2
  have hsel := selected_polyTime.comp (hblocks.prod (blockIndices_polyTime.comp (hblocks.prod hbs)))
  exact (hP.prod (hℓ.prod (htests.prod hsel))).of_enc_eq fun ((_, _, _, _), _) => rfl

/-- **The validity test of a row is polynomial-time.** -/
theorem rowValid_polyTime :
    ComputableInPolyTime
      (fun (((_, _, _, blocks), bs) : RowDesc × List Bool) =>
        validIndices blocks (blockIndices blocks bs))
      (encPair encRowDesc encBits) encBool := by
  have hblocks := (snd (encList (encList (encList encNat))) (encList encBlock)).comp
    ((snd _ _).comp ((snd _ _).comp (fst encRowDesc encBits)))
  exact (validIndices_polyTime.comp
    (hblocks.prod (blockIndices_polyTime.comp (hblocks.prod (snd encRowDesc encBits))))).of_enc_eq
      fun ((_, _, _, _), _) => rfl

/-! ### One term of a row -/

/-- **The parity factor in `B_{P,ℓ}` is polynomial-time**, with `P` and `ℓ` in unary and the
count in binary. -/
theorem factorCoeffs_polyTime :
    ComputableInPolyTime (fun (((P, ℓ), x) : (ℕ × ℕ) × ℕ) => factorCoeffs P ℓ x)
      (encPair (encPair encUnary encUnary) encNat) (encList encNat) := by
  let encQ := encPair (encPair encUnary encUnary) encNat
  have hq := fst encQ encUnary
  have hj := snd encQ encUnary
  have hP := (fst encUnary encUnary).comp ((fst (encPair encUnary encUnary) encNat).comp hq)
  have hℓ := (snd encUnary encUnary).comp ((fst (encPair encUnary encUnary) encNat).comp hq)
  have hx := (snd (encPair encUnary encUnary) encNat).comp hq
  have hab := (listGetD (encA := encPair encIntBin encIntBin) (encL := encList (encPair encIntBin
    encIntBin)) (0, 0)).comp ((parityLinearCoeffs_polytime.comp hℓ).prod hj)
  have hm := binary_two_pow.comp hP
  have ha := intBin_emodNat' ((fst encIntBin encIntBin).comp hab) hm
  have hb := intBin_emodNat' ((snd encIntBin encIntBin).comp hab) hm
  have hlin := binary_add.comp (ha.prod (binary_mul' hb hx))
  have hh := binary_mul' hx (binary_sub' hx (const 1))
  have hterm := binary_mul' hlin (binary_pow' hh hj)
  have hg := computableInPolyTime_mod_two_pow hterm hP
  have hℓ₀ := (snd encUnary encUnary).comp (fst (encPair encUnary encUnary) encNat)
  exact (computableInPolyTime_tabulate (g := fun (q : (ℕ × ℕ) × ℕ) (j : ℕ) =>
    ((((parityLinearCoeffs q.1.2).getD j (0, 0)).1 % ((2 ^ q.1.1 : ℕ) : ℤ)).toNat +
        (((parityLinearCoeffs q.1.2).getD j (0, 0)).2 % ((2 ^ q.1.1 : ℕ) : ℤ)).toNat * q.2) *
      (q.2 * (q.2 - 1)) ^ j % 2 ^ q.1.1) hℓ₀ hg).of_enc_eq fun ((_, _), _) => rfl

/-- The input of `monomialsIn`: the test, its position and the chosen incidences. -/
abbrev encMonomialsIn : (List (List ℕ) × ℕ) × List (ℕ × ℕ) ↪ List Bool :=
  encPair (encPair (encList (encList encNat)) encUnary) (encList (encPair encNat encNat))

/-- **Counting the monomials inside the chosen variables is polynomial-time**, in unary. -/
theorem monomialsIn_polyTime :
    ComputableInPolyTime (fun (((test, t), chosen) : (List (List ℕ) × ℕ) × List (ℕ × ℕ)) =>
        monomialsIn test t chosen) encMonomialsIn encUnary := by
  have htest := (fst (encList (encList encNat)) encUnary).comp
    (fst (encPair (encList (encList encNat)) encUnary) (encList (encPair encNat encNat)))
  -- The inner test: `(t, v) ∈ chosen`.
  let encM := encPair encMonomialsIn (encList encNat)
  have hq := fst encMonomialsIn (encList encNat)
  have hinner : ComputableInPolyTime
      (fun p : ((List (List ℕ) × ℕ) × List (ℕ × ℕ)) × List ℕ => p.2) encM
      (encList encNat) := snd encMonomialsIn (encList encNat)
  have hv := snd encM encNat
  have hq' := hq.comp (fst encM encNat)
  have ht := (unary_to_binary.comp ((snd (encList (encList encNat)) encUnary).comp
    ((fst (encPair (encList (encList encNat)) encUnary) (encList (encPair encNat encNat))).comp
      hq')))
  have hchosen := (snd (encPair (encList (encList encNat)) encUnary)
    (encList (encPair encNat encNat))).comp hq'
  have hmem := decide_mem (encA := encPair encNat encNat) hchosen (ht.prod hv)
  have hall := allWithInput (test := fun (p : ((List (List ℕ) × ℕ) × List (ℕ × ℕ)) × List ℕ)
    (v : ℕ) => decide ((p.1.1.2, v) ∈ p.1.2)) hinner hmem
  exact (countPWithInput (test := fun (q : (List (List ℕ) × ℕ) × List (ℕ × ℕ)) (M : List ℕ) =>
    M.all fun v => decide ((q.1.2, v) ∈ q.2)) htest hall).of_enc_eq fun ((_, _), _) => rfl

/-- The input of `rowTerm`: `P`, `ℓ` and the tests, then the chosen incidences. -/
abbrev encRowTerm : (ℕ × ℕ × List (List (List ℕ))) × List (ℕ × ℕ) ↪ List Bool :=
  encPair (encPair encUnary (encPair encUnary (encList (encList (encList encNat)))))
    (encList (encPair encNat encNat))

/-- `truncFl ℓ` is polynomial-time from `ℓ` in unary. -/
theorem truncFl_polyTime : ComputableInPolyTime truncFl encUnary (encList encNat) :=
  (replicate (hcount := id') (hvalue := const 0)).of_enc_eq fun _ => rfl

/-- **The product of the parity factors of the tests is polynomial-time.** -/
theorem rowTerm_polyTime :
    ComputableInPolyTime
      (fun (((P, ℓ, tests), chosen) : (ℕ × ℕ × List (List (List ℕ))) × List (ℕ × ℕ)) =>
        rowTerm P ℓ tests chosen) encRowTerm (encList encNat) := by
  have hctx := fst (encPair encUnary (encPair encUnary (encList (encList (encList encNat)))))
    (encList (encPair encNat encNat))
  have hP := (fst _ _).comp hctx
  have hℓ := (fst _ _).comp ((snd _ _).comp hctx)
  have htests := (snd encUnary (encList (encList (encList encNat)))).comp ((snd _ _).comp hctx)
  have hchosen := snd (encPair encUnary (encPair encUnary (encList (encList (encList encNat)))))
    (encList (encPair encNat encNat))
  have hfl := truncFl_polyTime.comp hℓ
  -- One step: multiply by the factor of test `t`.
  let encS := encPair (encPair encRowTerm (encList encNat)) encUnary
  have hx := (fst encRowTerm (encList encNat)).comp (fst (encPair encRowTerm (encList encNat))
    encUnary)
  have hacc := (snd encRowTerm (encList encNat)).comp (fst (encPair encRowTerm (encList encNat))
    encUnary)
  have ht := snd (encPair encRowTerm (encList encNat)) encUnary
  have htest := (listGetD (encA := encList (encList encNat))
    (encL := encList (encList (encList encNat))) []).comp ((htests.comp hx).prod ht)
  have hcount := monomialsIn_polyTime.comp ((htest.prod ht).prod (hchosen.comp hx))
  have hfac := factorCoeffs_polyTime.comp
    ((((hP.comp hx).prod (hℓ.comp hx))).prod (unary_to_binary.comp hcount))
  have hstep := computableInPolyTime_mul (hP.comp hx) (hfl.comp hx) hacc hfac
  have hone := computableInPolyTime_one hfl
  have hPb := hP.polyBounded_length
  have hℓb := hℓ.polyBounded_length
  have hfold := foldlWithInput_of_bounded_growth (encA := encUnary) (encL := encList encUnary)
    (step := fun (x : (ℕ × ℕ × List (List (List ℕ))) × List (ℕ × ℕ)) acc t =>
      mul x.1.1 (truncFl x.1.2.1) acc
        (factorCoeffs x.1.1 x.1.2.1 (monomialsIn (x.1.2.2.getD t []) t x.2))) hone
    ⟨range.comp ((length_list (encList (encList encNat))).comp htests), hstep, inferInstance,
      inferInstance⟩
    (growth := fun x => (encUnary x.1.2.1).length * (2 * (encUnary x.1.1).length + 1))
    ⟨hℓb.mul (((PolyBounded.const 2).mul hPb).add (.const 1)), fun x acc t _ => by
      have h := length_encList_le (length_mul x.1.1 (truncFl x.1.2.1) acc
        (factorCoeffs x.1.1 x.1.2.1 (monomialsIn (x.1.2.2.getD t []) t x.2)))
        fun _ h => lt_of_mem_mul h
      simp only [length_truncFl, encUnary_apply, List.length_replicate] at h ⊢
      nlinarith⟩
  exact hfold.of_enc_eq fun ((_, _, _), _) => rfl

/-- **The incidences chosen by a word are polynomial-time.** -/
theorem chosenBy_polyTime :
    ComputableInPolyTime (fun q : List (ℕ × ℕ) × List Bool => chosenBy q.1 q.2)
      (encPair (encList (encPair encNat encNat)) encBits) (encList (encPair encNat encNat)) := by
  have hzip := (zip (encPair encNat encNat) encBool).comp
    ((fst (encList (encPair encNat encNat)) encBits).prod
      (bitsToList.comp (snd (encList (encPair encNat encNat)) encBits)))
  have htest : ComputableInPolyTime
      (fun p : (List (ℕ × ℕ) × List Bool) × ((ℕ × ℕ) × Bool) => p.2.2)
      (encPair (encPair (encList (encPair encNat encNat)) encBits)
        (encPair (encPair encNat encNat) encBool)) encBool :=
    (snd (encPair encNat encNat) encBool).comp (snd _ _)
  have hfilter := filterWithInput
    (test := fun (_ : List (ℕ × ℕ) × List Bool) (p : (ℕ × ℕ) × Bool) => p.2) hzip htest
  exact ((map (fst (encPair encNat encNat) encBool)).comp hfilter).of_enc_eq fun q => rfl

/-- The encoding of the state of the sum of a row: the context and the accumulator. -/
abbrev encRowState : RowCtx × List ℕ ↪ List Bool := encPair encRowCtx (encList encNat)

/-- **One term of the sum of a row is polynomial-time.** -/
theorem rowBody_polyTime :
    ComputableInPolyTime rowBody (encPair (encPair encUnary encBits) encRowState)
      encRowState := by
  have hw := (snd encUnary encBits).comp (fst (encPair encUnary encBits) encRowState)
  have hst := snd (encPair encUnary encBits) encRowState
  have hctx := (fst encRowCtx (encList encNat)).comp hst
  have hacc := (snd encRowCtx (encList encNat)).comp hst
  have hP := (fst _ _).comp hctx
  have hr1 := (snd _ _).comp hctx
  have hℓ := (fst _ _).comp hr1
  have hr2 := (snd _ _).comp hr1
  have htests := (fst _ _).comp hr2
  have hsel := (snd (encList (encList (encList encNat))) (encList (encPair encNat encNat))).comp
    hr2
  have hchosen := chosenBy_polyTime.comp (hsel.prod hw)
  have hterm := rowTerm_polyTime.comp ((hP.prod (hℓ.prod htests)).prod hchosen)
  have hfl := truncFl_polyTime.comp hℓ
  have hadd := computableInPolyTime_add hP hfl hacc hterm
  have hsub := computableInPolyTime_sub hP hfl hacc hterm
  have hdiff := unary_to_binary.comp (unary_sub.comp
    (((length_list (encPair encNat encNat)).comp hsel).prod (bitsCountWithInput hw (const true))))
  have hcond := (binary_mod.comp (hdiff.prod (const 2))).beq (const 0)
  exact (hctx.prod (ite hcond hadd hsub)).of_enc_eq fun ((_, _), (_, _, _, _), _) => by
    simp only [rowBody, Function.comp_apply, beq_iff_eq]

/-- **The entries of columns are polynomial-time.** -/
theorem colEntry_polyTime :
    ComputableInPolyTime (fun q : ColDesc × List Bool => colEntry q.1 q.2)
      (encPair encColDesc encBits) (encList encNat) := by
  have hcol := fst encColDesc encBits
  have hbs := snd encColDesc encBits
  have hP := (fst _ _).comp hcol
  have hr := (snd _ _).comp hcol
  have hvars := (fst (encList encNat) (encList encBlock)).comp hr
  have hblocks := (snd (encList encNat) (encList encBlock)).comp hr
  have hsel := selected_polyTime.comp (hblocks.prod (blockIndices_polyTime.comp (hblocks.prod hbs)))
  have hsnd := (map (snd encNat encNat)).comp
    (hsel.comp (fst (encPair encColDesc encBits) encNat))
  have hmem := decide_not (decide_mem (encA := encNat) hsnd
    (snd (encPair encColDesc encBits) encNat))
  have hu := countPWithInput (test := fun (q : ColDesc × List Bool) (v : ℕ) =>
    decide (v ∉ (selected q.1.2.2 (blockIndices q.1.2.2 q.2)).map Prod.snd)) hvars hmem
  have hval := computableInPolyTime_mod_two_pow (binary_two_pow.comp hu) hP
  exact (cons' hval (const [])).of_enc_eq fun ((_, _, _), _) => rfl

end PolyTime

end Cslib.Circuits.Frontier.IncidenceNetwork
