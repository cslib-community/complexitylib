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
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Tactic.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain

/-!
# The worst-case-to-average-case encoding is computable in exponential time

The program `Cslib.HardnessEncoding.encodedProgram` is certified in the polynomial-time calculus of
tidy multi-tape machines, on padded inputs: with the length parameter `min |y| ⌊log₂ p⌋` for a
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

open Turing.MultiTapeTM ComputableTidilyInPolyTime Cslib.AffineDisperser

/-! Tidy views of the plain certificates of `AffineDisperser`, for tidy `fun_prop` below. -/

@[local fun_prop]
private theorem computableTidilyInPolyTime_getD_list
    {α γ : Type} {input : α ↪ List Bool}
    {enc : List γ ↪ List Bool} {L : α → List (List γ)} {i : α → ℕ}
    (hL : ComputableTidilyInPolyTime L input (encList enc))
    (hi : ComputableTidilyInPolyTime i input encUnary) (d : List γ) :
    ComputableTidilyInPolyTime (fun a => (L a).getD (i a) d) input enc :=
  (ComputableInPolyTime.tidy (AffineDisperser.computableInPolyTime_getD_list (.of_tidy hL)
      (.of_tidy hi) d))

@[local fun_prop]
private theorem computableTidilyInPolyTime_tableEntry
    {α : Type} {input : α ↪ List Bool}
    {tab : α → List (List (List Bool))} {u w : α → ℕ}
    (htab : ComputableTidilyInPolyTime tab input encTable)
    (hu : ComputableTidilyInPolyTime u input encUnary)
    (hw : ComputableTidilyInPolyTime w input encUnary) :
    ComputableTidilyInPolyTime (fun a => tableEntry (tab a) (u a) (w a)) input encBits :=
  (ComputableInPolyTime.tidy (AffineDisperser.computableInPolyTime_tableEntry (.of_tidy htab)
      (.of_tidy hu) (.of_tidy hw)))

@[local fun_prop]
private theorem computableTidilyInPolyTime_fieldMul'
    {α : Type} {input : α ↪ List Bool}
    {tab : α → List (List (List Bool))} {a b : α → List Bool}
    (htab : ComputableTidilyInPolyTime tab input encTable)
    (ha : ComputableTidilyInPolyTime a input encBits)
    (hb : ComputableTidilyInPolyTime b input encBits) :
    ComputableTidilyInPolyTime (fun x => fieldMul (tab x) (a x) (b x)) input encBits :=
  (ComputableInPolyTime.tidy (AffineDisperser.computableInPolyTime_fieldMul' (.of_tidy htab)
      (.of_tidy ha) (.of_tidy hb)))

@[local fun_prop]
private theorem computableTidilyInPolyTime_powerPred'
    {α : Type} {input : α ↪ List Bool}
    {tab : α → List (List (List Bool))} {y : α → List Bool} {k : α → ℕ}
    (htab : ComputableTidilyInPolyTime tab input encTable)
    (hy : ComputableTidilyInPolyTime y input encBits)
    (hk : ComputableTidilyInPolyTime k input encUnary) :
    ComputableTidilyInPolyTime (fun x => powerPred (tab x) (y x) (k x)) input encBits :=
  (ComputableInPolyTime.tidy (AffineDisperser.computableInPolyTime_powerPred' (.of_tidy htab)
      (.of_tidy hy) (.of_tidy hk)))

@[local fun_prop]
private theorem computableTidilyInPolyTime_esymmCoords'
    {α : Type} {input : α ↪ List Bool}
    {tab : α → List (List (List Bool))} {t : α → ℕ} {zs : α → List (List Bool)}
    (htab : ComputableTidilyInPolyTime tab input encTable)
    (ht : ComputableTidilyInPolyTime t input encUnary)
    (hzs : ComputableTidilyInPolyTime zs input (encList encBits)) :
    ComputableTidilyInPolyTime (fun x => esymmCoords (tab x) (t x) (zs x)) input encBits :=
  (ComputableInPolyTime.tidy (AffineDisperser.computableInPolyTime_esymmCoords' (.of_tidy htab)
      (.of_tidy ht) (.of_tidy hzs)))

@[local fun_prop]
private theorem computableTidilyInPolyTime_traceVector'
    {α : Type} {input : α ↪ List Bool}
    {tab : α → List (List (List Bool))} (htab : ComputableTidilyInPolyTime tab input encTable) :
    ComputableTidilyInPolyTime (fun x => traceVector (tab x)) input encBits :=
  (ComputableInPolyTime.tidy (AffineDisperser.computableInPolyTime_traceVector' (.of_tidy htab)))

@[local fun_prop]
private theorem computableTidilyInPolyTime_traceBit'
    {α : Type} {input : α ↪ List Bool}
    {τ a : α → List Bool} (hτ : ComputableTidilyInPolyTime τ input encBits)
    (ha : ComputableTidilyInPolyTime a input encBits) :
    ComputableTidilyInPolyTime (fun x => traceBit (τ x) (a x)) input encBool :=
  (ComputableInPolyTime.tidy (AffineDisperser.computableInPolyTime_traceBit' (.of_tidy hτ)
      (.of_tidy ha)))

/-! ### Field arithmetic -/

/-- The multiplication table of the power basis, from the coefficient list of the modulus. -/
private theorem computableTidilyInPolyTime_powerMulTable :
    ComputableTidilyInPolyTime powerMulTable encBits encTable := by
  unfold powerMulTable
  have := computableInPolyTime_powerTable.tidy
  fun_prop

private theorem computableTidilyInPolyTime_fieldInv' {α : Type} {input : α ↪ List Bool}
    {tab : α → List (List (List Bool))} {w : α → ℕ} {y : α → List Bool}
    (htab : ComputableTidilyInPolyTime tab input encTable)
    (hw : ComputableTidilyInPolyTime w input encUnary)
    (hy : ComputableTidilyInPolyTime y input encBits) :
    ComputableTidilyInPolyTime (fun x => fieldInv (tab x) (w x) (y x)) input encBits := by
  unfold fieldInv
  fun_prop

attribute [local fun_prop] computableTidilyInPolyTime_fieldInv'

/-- Inverses in coordinates, as a composition rule. -/
@[fun_prop]
theorem computableInPolyTime_fieldInv' {α : Type} {input : α ↪ List Bool}
    {tab : α → List (List (List Bool))} {w : α → ℕ} {y : α → List Bool}
    (htab : ComputableInPolyTime tab input encTable)
    (hw : ComputableInPolyTime w input encUnary)
    (hy : ComputableInPolyTime y input encBits) :
    ComputableInPolyTime (fun x => fieldInv (tab x) (w x) (y x)) input encBits :=
  .of_tidy (computableTidilyInPolyTime_fieldInv' htab.tidy hw.tidy hy.tidy)

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
private theorem computableTidilyInPolyTime_lagrangeNum : ComputableTidilyInPolyTime
    (fun p : ((List (List (List Bool)) × ℕ) × List (List Bool)) × (List Bool × List Bool) =>
      lagrangeNum p.1.1.1 p.1.1.2 p.1.2 p.2.1 p.2.2)
    (encPair (encPair (encPair encTable encUnary) (encList encBits)) (encPair encBits encBits))
    encBits := by
  have hstep : ComputableTidilyInPolyTime
      (fun q : (((List (List (List Bool)) × ℕ) × (List Bool × List Bool)) × List Bool) ×
          List Bool => lagrangeStep q.1.1 q.1.2 q.2)
      (encPair (encPair encLagrangePar encBits) encBits) encBits := by
    unfold lagrangeStep
    fun_prop
  have hlen : ComputableTidilyInPolyTime
      (fun p : ((List (List (List Bool)) × ℕ) × List (List Bool)) × (List Bool × List Bool) =>
        p.1.1.1.length)
      (encPair (encPair (encPair encTable encUnary) (encList encBits)) (encPair encBits encBits))
      encUnary := by
    fun_prop
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

private theorem computableTidilyInPolyTime_lagrangeNum' {α : Type} {input : α ↪ List Bool}
    {tab : α → List (List (List Bool))} {w : α → ℕ} {E : α → List (List Bool)}
    {a t : α → List Bool}
    (htab : ComputableTidilyInPolyTime tab input encTable)
    (hw : ComputableTidilyInPolyTime w input encUnary)
    (hE : ComputableTidilyInPolyTime E input (encList encBits))
    (ha : ComputableTidilyInPolyTime a input encBits)
    (ht : ComputableTidilyInPolyTime t input encBits) :
    ComputableTidilyInPolyTime (fun x => lagrangeNum (tab x) (w x) (E x) (a x) (t x)) input
      encBits := by
  simpa only [Function.comp_def] using
    computableTidilyInPolyTime_lagrangeNum.comp (((htab.prod hw).prod hE).prod (ha.prod ht))

attribute [local fun_prop] computableTidilyInPolyTime_lagrangeNum'

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
      encBits :=
  .of_tidy (computableTidilyInPolyTime_lagrangeNum' htab.tidy hw.tidy hE.tidy ha.tidy ht.tidy)

private theorem computableTidilyInPolyTime_lagrangeVal' {α : Type} {input : α ↪ List Bool}
    {tab : α → List (List (List Bool))} {w : α → ℕ} {E : α → List (List Bool)}
    {a t : α → List Bool}
    (htab : ComputableTidilyInPolyTime tab input encTable)
    (hw : ComputableTidilyInPolyTime w input encUnary)
    (hE : ComputableTidilyInPolyTime E input (encList encBits))
    (ha : ComputableTidilyInPolyTime a input encBits)
    (ht : ComputableTidilyInPolyTime t input encBits) :
    ComputableTidilyInPolyTime (fun x => lagrangeVal (tab x) (w x) (E x) (a x) (t x)) input
      encBits := by
  unfold lagrangeVal
  fun_prop

attribute [local fun_prop] computableTidilyInPolyTime_lagrangeVal'

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
      encBits :=
  .of_tidy (computableTidilyInPolyTime_lagrangeVal' htab.tidy hw.tidy hE.tidy ha.tidy ht.tidy)

/-- The input of a term: the table, the width, the block length and the number of blocks; the
nodes and the coordinates of the point; and the accepted input. -/
private abbrev encTermIn : ((((List (List (List Bool)) × ℕ) × ℕ) × ℕ) ×
    ((List (List Bool) × List (List Bool)) × List Bool)) ↪ List Bool :=
  encPair (encPair (encPair (encPair encTable encUnary) encUnary) encUnary)
    (encPair (encPair (encList encBits) (encList encBits)) encBits)

/-- **A term of the extension is polynomial-time**: a fold over the `M` blocks whose states are
field elements. -/
private theorem computableTidilyInPolyTime_termVal : ComputableTidilyInPolyTime
    (fun p : (((List (List (List Bool)) × ℕ) × ℕ) × ℕ) ×
        ((List (List Bool) × List (List Bool)) × List Bool) =>
      termVal p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2.1.1 p.2.1.2 p.2.2) encTermIn encBits := by
  have hlen : ComputableTidilyInPolyTime
      (fun p : (((List (List (List Bool)) × ℕ) × ℕ) × ℕ) ×
        ((List (List Bool) × List (List Bool)) × List Bool) => p.1.1.1.1.length)
      encTermIn encUnary := by
    fun_prop
  have hstep : ComputableTidilyInPolyTime
      (fun q : ((((((List (List (List Bool)) × ℕ) × ℕ) × ℕ) ×
          ((List (List Bool) × List (List Bool)) × List Bool)) × List Bool) × ℕ) =>
        fieldMul q.1.1.1.1.1.1 q.1.2 (lagrangeVal q.1.1.1.1.1.1 q.1.1.1.1.1.2 q.1.1.2.1.1
          (BitString.listBlock q.1.1.1.1.2 q.1.1.2.2 q.2) (q.1.1.2.1.2.getD q.2 [])))
      (encPair (encPair encTermIn encBits) encUnary) encBits := by
    unfold BitString.listBlock
    fun_prop
  have h := foldlWithInput_of_bounded_growth (encIn := encTermIn) (encA := encUnary)
    (encL := encList encUnary) (encB := encBits)
    (list := fun p => List.range p.1.2) (init := fun _ => [true])
    (step := fun p acc i => fieldMul p.1.1.1.1 acc (lagrangeVal p.1.1.1.1 p.1.1.1.2 p.2.1.1
      (BitString.listBlock p.1.1.2 p.2.2 i) (p.2.1.2.getD i [])))
    (by fun_prop) ⟨by fun_prop, hstep, inferInstance, inferInstance⟩
    (growth := fun p => p.1.1.1.1.length) ⟨hlen.polyBounded, fun p state value _ => by
      simp [length_fieldMul]⟩
  unfold termVal
  exact h

private theorem computableTidilyInPolyTime_termVal' {α : Type} {input : α ↪ List Bool}
    {tab : α → List (List (List Bool))} {w b M : α → ℕ} {E xs : α → List (List Bool)}
    {z : α → List Bool}
    (htab : ComputableTidilyInPolyTime tab input encTable)
    (hw : ComputableTidilyInPolyTime w input encUnary)
    (hb : ComputableTidilyInPolyTime b input encUnary)
    (hM : ComputableTidilyInPolyTime M input encUnary)
    (hE : ComputableTidilyInPolyTime E input (encList encBits))
    (hxs : ComputableTidilyInPolyTime xs input (encList encBits))
    (hz : ComputableTidilyInPolyTime z input encBits) :
    ComputableTidilyInPolyTime (fun x => termVal (tab x) (w x) (b x) (M x) (E x) (xs x) (z x))
      input encBits := by
  simpa only [Function.comp_def] using computableTidilyInPolyTime_termVal.comp
    ((((htab.prod hw).prod hb).prod hM).prod ((hE.prod hxs).prod hz))

attribute [local fun_prop] computableTidilyInPolyTime_termVal'

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
      input encBits :=
  .of_tidy (computableTidilyInPolyTime_termVal' htab.tidy hw.tidy hb.tidy hM.tidy hE.tidy hxs.tidy
    hz.tidy)

private theorem computableTidilyInPolyTime_ldeVal' {α : Type} {input : α ↪ List Bool}
    {tab : α → List (List (List Bool))} {w b M : α → ℕ} {E pts xs : α → List (List Bool)}
    (htab : ComputableTidilyInPolyTime tab input encTable)
    (hw : ComputableTidilyInPolyTime w input encUnary)
    (hb : ComputableTidilyInPolyTime b input encUnary)
    (hM : ComputableTidilyInPolyTime M input encUnary)
    (hE : ComputableTidilyInPolyTime E input (encList encBits))
    (hpts : ComputableTidilyInPolyTime pts input (encList encBits))
    (hxs : ComputableTidilyInPolyTime xs input (encList encBits)) :
    ComputableTidilyInPolyTime (fun x => ldeVal (tab x) (w x) (b x) (M x) (E x) (pts x) (xs x))
      input encBits := by
  unfold ldeVal
  fun_prop

attribute [local fun_prop] computableTidilyInPolyTime_ldeVal'

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
      input encBits :=
  .of_tidy (computableTidilyInPolyTime_ldeVal' htab.tidy hw.tidy hb.tidy hM.tidy hE.tidy hpts.tidy
    hxs.tidy)

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

private theorem computableTidilyInPolyTime_padLength :
    ComputableTidilyInPolyTime padLength (encPair encBits encUnary) encUnary := by
  unfold padLength
  have := unary_log_two
  fun_prop

attribute [local fun_prop] computableTidilyInPolyTime_padLength

/-- The length parameter is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_padLength :
    ComputableInPolyTime padLength (encPair encBits encUnary) encUnary :=
  .of_tidy (computableTidilyInPolyTime_padLength)

/-- **The padded program is polynomial-time**, for any function `gL` on bit words computable in
time `2 ^ O(n)`: every loop runs over at most `p ^ O(1)` elements for the padding `p`, the modulus
is found among `2 ^ (w + 1) ≤ 2 p + 2` codes, and `gL` is called on words of length at most
`⌊log₂ p⌋`. -/
theorem computableInPolyTime_paddedProgram (M : ℕ) {gL : List Bool → Bool} {k : ℕ}
    (hgL : ComputableInO gL encBits encBool (fun y => 2 ^ (k * y.length))
      fun y => 2 ^ (k * y.length)) :
    ComputableInPolyTime (paddedProgram M gL) (encPair encBits encUnary) encBool := by
  have hgL : ComputableTidilyInO gL encBits encBool (fun y => 2 ^ (k * y.length)) fun y => 2 ^
      (k * y.length) := by simpa only
    [computableInO_iff_computableTidilyInO, computableInPolyTime_iff_computableTidilyInPolyTime]
    using hgL
  refine .of_tidy ?_
  have hℓ := computableInPolyTime_padLength.tidy
  have hb : ComputableTidilyInPolyTime (fun x => blockLength M (padLength x))
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
  have hE : ComputableTidilyInPolyTime (fun x => BitString.enumList (blockLength M (padLength x)))
      (encPair encBits encUnary) (encList encBits) :=
    (ComputableInPolyTime.bitsEnumList_of_polyBounded (.of_tidy hb)
      ((polyBounded_two_pow_mul_padLength 1).mono fun x => by
        rw [one_mul]
        exact Nat.pow_le_pow_right (by norm_num) (hbℓ x))).tidy
  have hMb : ComputableTidilyInPolyTime (fun x => M * blockLength M (padLength x))
      (encPair encBits encUnary) encUnary := by
    fun_prop
  have hEn : ComputableTidilyInPolyTime
      (fun x => BitString.enumList (M * blockLength M (padLength x)))
      (encPair encBits encUnary) (encList encBits) :=
    (ComputableInPolyTime.bitsEnumList_of_polyBounded (.of_tidy hMb)
      ((polyBounded_two_pow_mul_padLength 1).mono fun x => by
        rw [one_mul]
        exact Nat.pow_le_pow_right (by norm_num) (hMbℓ x))).tidy
  -- the queries to the decider
  have htest := (ComputableInO.computableInPolyTime_take
    (fun _ _ h => Nat.pow_le_pow_right two_pos (Nat.mul_le_mul_left k h)) (.of_tidy hgL)
    (.of_tidy hMb) ((polyBounded_two_pow_mul_padLength k).mono fun x =>
      Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left k (hMbℓ x)))).tidy
  have hpts : ComputableTidilyInPolyTime
      (fun x => (BitString.enumList (M * blockLength M (padLength x))).filter
        fun z => gL (z.take (M * blockLength M (padLength x))))
      (encPair encBits encUnary) (encList encBits) :=
    filterWithInput hEn htest
  -- the modulus, among the codes below `2 ^ (w + 1) ≤ 2 p + 2`
  have hpow : ComputableTidilyInPolyTime (fun x => 2 ^ (4 * blockLength M (padLength x) + 1))
      (encPair encBits encUnary) encUnary := by
    refine binary_to_unary_bounded (binary_two_pow.comp (by fun_prop))
      (bound := fun x => 2 * x.2 + 2) (by fun_prop) fun x => ?_
    have h1 := two_pow_padLength_le x
    have h2 : 2 ^ (4 * blockLength M (padLength x)) ≤ 2 ^ padLength x :=
      Nat.pow_le_pow_right (by norm_num) (h4bℓ x)
    rw [pow_succ]
    omega
  have hmod : ComputableTidilyInPolyTime (fun x => modulusBits (4 * blockLength M (padLength x)))
      (encPair encBits encUnary) encBits := by
    unfold modulusBits
    have := computableInPolyTime_bits_unary.tidy
    have := computableInPolyTime_leastIrreducibleCode.tidy
    fun_prop
  have htab : ComputableTidilyInPolyTime (fun x => fieldTable (4 * blockLength M (padLength x)))
      (encPair encBits encUnary) encTable := by
    unfold fieldTable
    exact computableTidilyInPolyTime_powerMulTable.comp hmod
  unfold paddedProgram encodedProgram encodedProgramAt
  fun_prop

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
