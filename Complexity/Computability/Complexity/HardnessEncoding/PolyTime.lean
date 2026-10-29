/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.HardnessEncoding.Program
public import Complexity.Computability.Complexity.AffineDisperser.PolyTime
public import Complexity.Computability.Complexity.Classes.BPP.Derandomization.Generator
public import Complexity.Computability.Complexity.Classes.EXP
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain

/-!
# The worst-case-to-average-case encoding is computable in exponential time

The program `Cslib.HardnessEncoding.encodedProgram` is certified in the polynomial-time calculus of
multi-tape machines, on padded inputs: with the length parameter `min |y| ⌊log₂ p⌋` for a
unary padding `p`, every loop of the program runs over at most `p ^ O(1)` elements, and the
decider of `L`, computable in time `2 ^ O(n)`, is called on words of length at most `⌊log₂ p⌋`
(`Cslib.HardnessEncoding.computableInPolyTime_paddedProgram`). With the padding
`p = 2 ^ |y|` the program runs in time `2 ^ O(|y|)`, so the encoded language of a language in `E`
is in `E` (`Cslib.HardnessEncoding.encodedLanguage_mem_E`, by
`Cslib.Complexity.setOf_mem_E_of_computableInPolyTime_pad`).

## Main definitions

* `Cslib.HardnessEncoding.paddedProgram`: the program with the length parameter read from a
  padding.

## Main results

* `Cslib.HardnessEncoding.computableInPolyTime_paddedProgram`: the padded program is
  polynomial-time.
* `Cslib.HardnessEncoding.encodedLanguage_mem_E`: **the encoding of a language in `E` is in `E`**.

## References

* [M. Sudan, L. Trevisan, S. Vadhan, *Pseudorandom generators without the XOR lemma*]
  [SudanTrevisanVadhan2001]
* [R. Impagliazzo, A. Wigderson, *P = BPP if E requires exponential circuits: Derandomizing the
  XOR lemma*][ImpagliazzoWigderson1997]
-/

@[expose] public section

namespace Cslib.HardnessEncoding

open Turing.MultiTapeTM ComputableInPolyTime Cslib.AffineDisperser

/-! ### Field arithmetic -/

/-- The multiplication table of the power basis, from the coefficient list of the modulus. -/
private theorem computableInPolyTime_powerMulTable :
    ComputableInPolyTime powerMulTable encBits encTable := by
  unfold powerMulTable
  fun_prop

/-- Inverses in coordinates, as a composition rule. -/
@[fun_prop]
theorem computableInPolyTime_fieldInv' {α : Type} {input : α ↪ List Bool}
    {tab : α → List (List (List Bool))} {w : α → ℕ} {y : α → List Bool}
    (htab : ComputableInPolyTime tab input encTable)
    (hw : ComputableInPolyTime w input encUnary)
    (hy : ComputableInPolyTime y input encBits) :
    ComputableInPolyTime (fun x => fieldInv (tab x) (w x) (y x)) input encBits := by
  unfold fieldInv
  fun_prop

/-- The parameters of a Lagrange numerator: the table, the width, the node and the point. -/
private abbrev encLagrangePar : (List (List (List Bool)) × ℕ) × (List Bool × List Bool) ↪
    List Bool :=
  encPair (encPair encTable encUnary) (encPair encBits encBits)

/-- One step of the Lagrange numerator. -/
private def lagrangeStep (par : (List (List (List Bool)) × ℕ) × (List Bool × List Bool))
    (acc a' : List Bool) : List Bool :=
  if a' = par.2.1 then acc else fieldMul par.1.1 acc (Cslib.BitString.listXor par.1.2 [par.2.2, a'])

/-- **The Lagrange numerator is polynomial-time**, uniformly in the table, the width, the nodes,
the node and the point: a fold over the nodes whose states are field elements. -/
private theorem computableInPolyTime_lagrangeNum : ComputableInPolyTime
    (fun p : ((List (List (List Bool)) × ℕ) × List (List Bool)) × (List Bool × List Bool) =>
      lagrangeNum p.1.1.1 p.1.1.2 p.1.2 p.2.1 p.2.2)
    (encPair (encPair (encPair encTable encUnary) (encList encBits)) (encPair encBits encBits))
    encBits := by
  have helse : ComputableInPolyTime
      (fun q : (((List (List (List Bool)) × ℕ) × (List Bool × List Bool)) × List Bool) ×
          List Bool =>
        fieldMul q.1.1.1.1 q.1.2 (Cslib.BitString.listXor q.1.1.1.2 [q.1.1.2.2, q.2]))
      (encPair (encPair encLagrangePar encBits) encBits) encBits := by
    fun_prop
  have hstep : ComputableInPolyTime
      (fun q : (((List (List (List Bool)) × ℕ) × (List Bool × List Bool)) × List Bool) ×
          List Bool => lagrangeStep q.1.1 q.1.2 q.2)
      (encPair (encPair encLagrangePar encBits) encBits) encBits := by
    unfold lagrangeStep
    exact ite_decide
      (decide_eq' (snd _ _) ((fst _ _).comp ((snd _ _).comp ((fst _ _).comp (fst _ _)))))
      ((snd _ _).comp (fst _ _)) helse
  have hlen : ComputableInPolyTime
      (fun p : ((List (List (List Bool)) × ℕ) × List (List Bool)) × (List Bool × List Bool) =>
        p.1.1.1.length)
      (encPair (encPair (encPair encTable encUnary) (encList encBits)) (encPair encBits encBits))
      encUnary :=
    (length_list (encList encBits)).comp ((fst _ _).comp ((fst _ _).comp (fst _ _)))
  have h := foldlWith_of_bounded_growth (encA := encBits) (encL := encList encBits)
    (encIn := encPair (encPair (encPair encTable encUnary) (encList encBits))
      (encPair encBits encBits)) (encP := encLagrangePar)
    (par := fun p : ((List (List (List Bool)) × ℕ) × List (List Bool)) ×
      (List Bool × List Bool) => ((p.1.1.1, p.1.1.2), (p.2.1, p.2.2)))
    (list := fun p => p.1.2) (init := fun _ => [true]) (step := lagrangeStep)
    (by fun_prop) (by fun_prop) (by fun_prop) hstep (growth := fun p => p.1.1.1.length)
    hlen.polyBounded fun p state value _ => by
      simp only [lagrangeStep]
      split_ifs
      · simp
      · simp [length_fieldMul]
  unfold lagrangeNum
  exact h

/-- The Lagrange numerator, as a composition rule. -/
@[fun_prop]
theorem computableInPolyTime_lagrangeNum' {α : Type} {input : α ↪ List Bool}
    {tab : α → List (List (List Bool))} {w : α → ℕ} {E : α → List (List Bool)}
    {a t : α → List Bool}
    (htab : ComputableInPolyTime tab input encTable)
    (hw : ComputableInPolyTime w input encUnary)
    (hE : ComputableInPolyTime E input (encList encBits))
    (ha : ComputableInPolyTime a input encBits)
    (ht : ComputableInPolyTime t input encBits) :
    ComputableInPolyTime (fun x => lagrangeNum (tab x) (w x) (E x) (a x) (t x)) input
      encBits := by
  simpa only [Function.comp_def] using
    computableInPolyTime_lagrangeNum.comp (((htab.prod hw).prod hE).prod (ha.prod ht))

/-- A Lagrange basis polynomial at a point, as a composition rule. -/
@[fun_prop]
theorem computableInPolyTime_lagrangeVal' {α : Type} {input : α ↪ List Bool}
    {tab : α → List (List (List Bool))} {w : α → ℕ} {E : α → List (List Bool)}
    {a t : α → List Bool}
    (htab : ComputableInPolyTime tab input encTable)
    (hw : ComputableInPolyTime w input encUnary)
    (hE : ComputableInPolyTime E input (encList encBits))
    (ha : ComputableInPolyTime a input encBits)
    (ht : ComputableInPolyTime t input encBits) :
    ComputableInPolyTime (fun x => lagrangeVal (tab x) (w x) (E x) (a x) (t x)) input
      encBits := by
  unfold lagrangeVal
  fun_prop

/-- The input of a term: the table, the width, the block length and the number of blocks; the
nodes and the coordinates of the point; and the accepted input. -/
private abbrev encTermIn : ((((List (List (List Bool)) × ℕ) × ℕ) × ℕ) ×
    ((List (List Bool) × List (List Bool)) × List Bool)) ↪ List Bool :=
  encPair (encPair (encPair (encPair encTable encUnary) encUnary) encUnary)
    (encPair (encPair (encList encBits) (encList encBits)) encBits)

/-- **A term of the extension is polynomial-time**: a fold over the `M` blocks whose states are
field elements. -/
private theorem computableInPolyTime_termVal : ComputableInPolyTime
    (fun p : (((List (List (List Bool)) × ℕ) × ℕ) × ℕ) ×
        ((List (List Bool) × List (List Bool)) × List Bool) =>
      termVal p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2.1.1 p.2.1.2 p.2.2) encTermIn encBits := by
  let encQ := encPair (encPair encTermIn encBits) encUnary
  have htabP : ComputableInPolyTime (fun p => p.1.1.1.1) encTermIn encTable :=
    (fst _ _).comp ((fst _ _).comp ((fst _ _).comp (fst _ _)))
  have hlen : ComputableInPolyTime (fun p => p.1.1.1.1.length) encTermIn encUnary :=
    (length_list (encList encBits)).comp htabP
  have hqP : ComputableInPolyTime (fun q => q.1.1) encQ encTermIn :=
    (fst _ _).comp (fst _ _)
  have htabQ : ComputableInPolyTime (fun q => q.1.1.1.1.1.1) encQ encTable := htabP.comp hqP
  have hwQ : ComputableInPolyTime (fun q => q.1.1.1.1.1.2) encQ encUnary :=
    ((snd _ _).comp ((fst _ _).comp ((fst _ _).comp (fst _ _)))).comp hqP
  have hbQ : ComputableInPolyTime (fun q => q.1.1.1.1.2) encQ encUnary :=
    ((snd _ _).comp ((fst _ _).comp (fst _ _))).comp hqP
  have hEQ : ComputableInPolyTime (fun q => q.1.1.2.1.1) encQ (encList encBits) :=
    ((fst _ _).comp ((fst _ _).comp (snd _ _))).comp hqP
  have hxsQ : ComputableInPolyTime (fun q => q.1.1.2.1.2) encQ (encList encBits) :=
    ((snd _ _).comp ((fst _ _).comp (snd _ _))).comp hqP
  have hzQ : ComputableInPolyTime (fun q => q.1.1.2.2) encQ encBits :=
    ((snd _ _).comp (snd _ _)).comp hqP
  have haccQ : ComputableInPolyTime (fun q => q.1.2) encQ encBits :=
    (snd _ _).comp (fst _ _)
  have hiQ : ComputableInPolyTime (fun q => q.2) encQ encUnary := snd _ _
  have hstep : ComputableInPolyTime
      (fun q : ((((((List (List (List Bool)) × ℕ) × ℕ) × ℕ) ×
          ((List (List Bool) × List (List Bool)) × List Bool)) × List Bool) × ℕ) =>
        fieldMul q.1.1.1.1.1.1 q.1.2 (lagrangeVal q.1.1.1.1.1.1 q.1.1.1.1.1.2 q.1.1.2.1.1
          (BitString.listBlock q.1.1.1.1.2 q.1.1.2.2 q.2) (q.1.1.2.1.2.getD q.2 [])))
      encQ encBits := by
    unfold BitString.listBlock
    exact computableInPolyTime_fieldMul' htabQ haccQ (computableInPolyTime_lagrangeVal' htabQ hwQ
      hEQ (bitsTakeWithInput (bitsDropWithInput hzQ (unary_mul.comp (hiQ.prod hbQ))) hbQ)
      (listGetDWithInput hxsQ hiQ []))
  have hM : ComputableInPolyTime (fun p => p.1.2) encTermIn encUnary :=
    (snd _ _).comp (fst _ _)
  have h := foldlWithInput_of_bounded_growth (encIn := encTermIn) (encA := encUnary)
    (encL := encList encUnary) (encB := encBits)
    (list := fun p => List.range p.1.2) (init := fun _ => [true])
    (step := fun p acc i => fieldMul p.1.1.1.1 acc (lagrangeVal p.1.1.1.1 p.1.1.1.2 p.2.1.1
      (BitString.listBlock p.1.1.2 p.2.2 i) (p.2.1.2.getD i [])))
    (const [true]) ⟨unary_range' hM, hstep, inferInstance, inferInstance⟩
    (growth := fun p => p.1.1.1.1.length) ⟨hlen.polyBounded, fun p state value _ => by
      simp [length_fieldMul]⟩
  unfold termVal
  exact h

/-- A term of the extension, as a composition rule. -/
@[fun_prop]
theorem computableInPolyTime_termVal' {α : Type} {input : α ↪ List Bool}
    {tab : α → List (List (List Bool))} {w b M : α → ℕ} {E xs : α → List (List Bool)}
    {z : α → List Bool}
    (htab : ComputableInPolyTime tab input encTable)
    (hw : ComputableInPolyTime w input encUnary)
    (hb : ComputableInPolyTime b input encUnary)
    (hM : ComputableInPolyTime M input encUnary)
    (hE : ComputableInPolyTime E input (encList encBits))
    (hxs : ComputableInPolyTime xs input (encList encBits))
    (hz : ComputableInPolyTime z input encBits) :
    ComputableInPolyTime (fun x => termVal (tab x) (w x) (b x) (M x) (E x) (xs x) (z x))
      input encBits := by
  simpa only [Function.comp_def] using
    computableInPolyTime_termVal.comp
      ((((htab.prod hw).prod hb).prod hM).prod ((hE.prod hxs).prod hz))

/-- **The low-degree extension at a point is polynomial-time**, as a composition rule. -/
@[fun_prop]
theorem computableInPolyTime_ldeVal' {α : Type} {input : α ↪ List Bool}
    {tab : α → List (List (List Bool))} {w b M : α → ℕ} {E pts xs : α → List (List Bool)}
    (htab : ComputableInPolyTime tab input encTable)
    (hw : ComputableInPolyTime w input encUnary)
    (hb : ComputableInPolyTime b input encUnary)
    (hM : ComputableInPolyTime M input encUnary)
    (hE : ComputableInPolyTime E input (encList encBits))
    (hpts : ComputableInPolyTime pts input (encList encBits))
    (hxs : ComputableInPolyTime xs input (encList encBits)) :
    ComputableInPolyTime (fun x => ldeVal (tab x) (w x) (b x) (M x) (E x) (pts x) (xs x))
      input encBits := by
  unfold ldeVal
  fun_prop

/-! ### The padded program -/

/-- The length parameter read from a unary padding `p`: `min |y| ⌊log₂ p⌋`. -/
def padLength (x : List Bool × ℕ) : ℕ := min x.1.length (Nat.log 2 x.2)

/-- **The padded program**: the encoding program with the length parameter read from the
padding. -/
def paddedProgram (M : ℕ) (gL : List Bool → Bool) (x : List Bool × ℕ) : Bool :=
  encodedProgram M gL x.1 (padLength x)

/-- The padding bounds `2 ^ ℓ` for the length parameter `ℓ`. -/
private theorem two_pow_padLength_le (x : List Bool × ℕ) : 2 ^ padLength x ≤ x.2 + 1 := by
  rcases Nat.eq_zero_or_pos x.2 with h | h
  · simp [padLength, h]
  · calc 2 ^ padLength x ≤ 2 ^ Nat.log 2 x.2 :=
          Nat.pow_le_pow_right (by norm_num) (min_le_right _ _)
      _ ≤ x.2 := Nat.pow_log_le_self 2 h.ne'
      _ ≤ x.2 + 1 := Nat.le_succ _

/-- Exponentials of multiples of the length parameter are polynomial in the padded input. -/
private theorem polyBounded_two_pow_mul_padLength (c : ℕ) :
    PolyBounded (fun x : List Bool × ℕ => (encPair encBits encUnary x).length)
      fun x => 2 ^ (c * padLength x) := by
  refine PolyBounded.of_forall_le 1 c fun x => ?_
  rw [one_mul, mul_comm, pow_mul]
  refine Nat.pow_le_pow_left ((two_pow_padLength_le x).trans ?_) c
  have := length_le_encPair_right encBits encUnary x
  rw [encUnary_apply, List.length_replicate] at this
  omega

/-- The length parameter is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_padLength :
    ComputableInPolyTime padLength (encPair encBits encUnary) encUnary := by
  unfold padLength
  have h1 : ComputableInPolyTime (fun x : List Bool × ℕ => x.1.length)
      (encPair encBits encUnary) encUnary := length_bits.comp (fst _ _)
  have h2 : ComputableInPolyTime (fun x : List Bool × ℕ => Nat.log 2 x.2)
      (encPair encBits encUnary) encUnary :=
    binary_log_two.comp (unary_to_binary.comp (snd _ _))
  simpa only [Nat.min_def] using ite_decide (unary_le' h1 h2) h1 h2

/-- **The padded program is polynomial-time**, for any function `gL` on bit words computable in
time `2 ^ O(n)`: every loop runs over at most `p ^ O(1)` elements for the padding `p`, the modulus
is found among `2 ^ (w + 1) ≤ 2 p + 2` codes, and `gL` is called on words of length at most
`⌊log₂ p⌋`. -/
theorem computableInPolyTime_paddedProgram (M : ℕ) {gL : List Bool → Bool} {k : ℕ}
    (hgL : ComputableInO gL encBits encBool (fun y => 2 ^ (k * y.length))
      fun y => 2 ^ (k * y.length)) :
    ComputableInPolyTime (paddedProgram M gL) (encPair encBits encUnary) encBool := by
  have hb : ComputableInPolyTime (fun x => blockLength M (padLength x))
      (encPair encBits encUnary) encUnary := by
    unfold blockLength
    fun_prop
  have hbℓ : ∀ x, blockLength M (padLength x) ≤ padLength x := fun x => Nat.div_le_self _ _
  have hMbℓ : ∀ x, M * blockLength M (padLength x) ≤ padLength x := fun x => by
    have := Nat.div_mul_le_self (padLength x) (4 * (M + 1))
    unfold blockLength
    nlinarith
  have h4bℓ : ∀ x, 4 * blockLength M (padLength x) ≤ padLength x := fun x => by
    have := Nat.div_mul_le_self (padLength x) (4 * (M + 1))
    unfold blockLength
    nlinarith
  -- the enumerations
  have hE : ComputableInPolyTime (fun x => BitString.enumList (blockLength M (padLength x)))
      (encPair encBits encUnary) (encList encBits) :=
    bitsEnumList_of_polyBounded hb
      ((polyBounded_two_pow_mul_padLength 1).mono fun x => by
        rw [one_mul]
        exact Nat.pow_le_pow_right (by norm_num) (hbℓ x))
  have hMb : ComputableInPolyTime (fun x => M * blockLength M (padLength x))
      (encPair encBits encUnary) encUnary := by
    fun_prop
  have hEn : ComputableInPolyTime
      (fun x => BitString.enumList (M * blockLength M (padLength x)))
      (encPair encBits encUnary) (encList encBits) :=
    bitsEnumList_of_polyBounded hMb
      ((polyBounded_two_pow_mul_padLength 1).mono fun x => by
        rw [one_mul]
        exact Nat.pow_le_pow_right (by norm_num) (hMbℓ x))
  -- the queries to the decider
  have htest := ComputableInO.computableInPolyTime_take
    (fun _ _ h => Nat.pow_le_pow_right two_pos (Nat.mul_le_mul_left k h)) hgL
    hMb ((polyBounded_two_pow_mul_padLength k).mono fun x =>
      Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left k (hMbℓ x)))
  have hpts : ComputableInPolyTime
      (fun x => (BitString.enumList (M * blockLength M (padLength x))).filter
        fun z => gL (z.take (M * blockLength M (padLength x))))
      (encPair encBits encUnary) (encList encBits) :=
    filterWithInput hEn htest
  -- the modulus, among the codes below `2 ^ (w + 1) ≤ 2 p + 2`
  have hpow : ComputableInPolyTime (fun x => 2 ^ (4 * blockLength M (padLength x) + 1))
      (encPair encBits encUnary) encUnary := by
    refine binary_to_unary_bounded (binary_two_pow.comp (by fun_prop))
      (bound := fun x => 2 * x.2 + 2) (by fun_prop) fun x => ?_
    have h1 := two_pow_padLength_le x
    have h2 : 2 ^ (4 * blockLength M (padLength x)) ≤ 2 ^ padLength x :=
      Nat.pow_le_pow_right (by norm_num) (h4bℓ x)
    rw [pow_succ]
    omega
  have h4b : ComputableInPolyTime (fun x => 4 * blockLength M (padLength x))
      (encPair encBits encUnary) encUnary := by
    fun_prop
  have hmod : ComputableInPolyTime (fun x => modulusBits (4 * blockLength M (padLength x)))
      (encPair encBits encUnary) encBits := by
    simpa only [modulusBits, Function.comp_def] using
      computableInPolyTime_bits_unary.comp
        (computableInPolyTime_leastIrreducibleCode.comp (hpow.prod h4b))
  have htab : ComputableInPolyTime (fun x => fieldTable (4 * blockLength M (padLength x)))
      (encPair encBits encUnary) encTable := by
    unfold fieldTable
    exact computableInPolyTime_powerMulTable.comp hmod
  have h4bp : ComputableInPolyTime
      (fun p : (List Bool × ℕ) × ℕ => 4 * blockLength M (padLength p.1))
      (encPair (encPair encBits encUnary) encUnary) encUnary :=
    h4b.comp (fst _ _)
  have helse : ComputableInPolyTime (fun x : List Bool × ℕ =>
      traceBit (BitString.listBlock (4 * blockLength M (padLength x)) x.1 M)
        (ldeVal (fieldTable (4 * blockLength M (padLength x)))
          (4 * blockLength M (padLength x)) (blockLength M (padLength x)) M
          (BitString.enumList (blockLength M (padLength x)))
          ((BitString.enumList (M * blockLength M (padLength x))).filter
            fun z => gL (z.take (M * blockLength M (padLength x))))
          ((List.range M).map
            (BitString.listBlock (4 * blockLength M (padLength x)) x.1))))
      (encPair encBits encUnary) encBool := by
    unfold BitString.listBlock
    refine computableInPolyTime_traceBit'
      (bitsTakeWithInput (bitsDropWithInput (fst _ _) (unary_mul.comp ((const M).prod h4b))) h4b)
      (computableInPolyTime_ldeVal' htab h4b hb (const M) hE hpts ?_)
    exact mapWithInput (unary_range' (const M))
      (bitsTakeWithInput
        (bitsDropWithInput ((fst _ _).comp (fst _ _)) (unary_mul.comp ((snd _ _).prod h4bp)))
        h4bp)
  unfold paddedProgram encodedProgram encodedProgramAt
  exact ite_decide (decide_eq' hb (const 0)) (const false) helse

end Cslib.HardnessEncoding

namespace Cslib.HardnessEncoding

open Turing.MultiTapeTM Cslib.Complexity

/-- **The encoding of a language in `E` is in `E`**: the encoded language of `L`, whose slice at
length `N` encodes the slice of `L` at length `M ⌊N / (4 (M + 1))⌋` over the explicit binary field,
is decided in time `2 ^ O(N)` by running the padded program with the padding `2 ^ N`. -/
theorem encodedLanguage_mem_E {L : Language Bool} (hL : (L : Set (List Bool)) ∈ E encBits)
    (M : ℕ) : (encodedLanguage L M : Set (List Bool)) ∈ E encBits := by
  obtain ⟨k, hk⟩ := mem_E_iff.1 hL
  obtain ⟨gL, hgL, hgLO⟩ := exists_computableInO_of_mem_DTIME hk
  have h := setOf_mem_E_of_computableInPolyTime_pad
    (computableInPolyTime_paddedProgram M hgLO)
  have hset : (encodedLanguage L M : Set (List Bool)) =
      {y | paddedProgram M gL (y, 2 ^ y.length) = true} := by
    ext y
    change y ∈ encodedLanguage L M ↔ paddedProgram M gL (y, 2 ^ y.length) = true
    rw [paddedProgram, padLength]
    simp only [Nat.log_pow one_lt_two, min_self]
    rw [encodedProgram_eq (L := L) hgL]
    rfl
  rw [hset]
  exact h

end Cslib.HardnessEncoding
