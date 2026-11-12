/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.PolyTime.Int.DotProduct
public import CslibFrontier.Foundations.Data.ZMod.DotProduct
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Lyubashevsky
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Lyubashevsky.NativeExtract
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Efficient
public import CslibFrontier.Crypto.Game.CloseTo.UniformNat
public import CslibFrontier.Computability.Probabilistic.UniformNat
public import CslibFrontier.Computability.Probabilistic.Repeat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.BinaryDiv
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Foundations.Data.List.OfFnGetD
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT
import Mathlib.Data.List.GetD

/-!
# Strict-PPT integer-box samplers and efficiency certificates for Lyubashevsky identification

`SigmaProtocol.lyubashevsky` (`CslibFrontier/Crypto/Protocols/SigmaProtocol/Lyubashevsky.lean`)
defines
Lyubashevsky's lattice identification protocol ([Lyubashevsky2009], [Lyubashevsky2012]) with
Dilithium-style uniform-box rejection sampling ([DucasEtAl2018]) over `PMF`. In the strict
polynomial-time Turing machine model with fair coins, sampling the integer box `[-B, B]^m` of
odd cardinality `(2 B + 1)^m` is approximate rather than exact.

This module constructs strict-PPT samplers for integer intervals and boxes from
`ProbComp.sampleModNat` (`CslibFrontier/Languages/Probabilistic/UniformNat.lean`) and connects them,
together with the serialized extractor of
`CslibFrontier/Crypto/Protocols/SigmaProtocol/Lyubashevsky/NativeExtract.lean`, to uniform
machine-backed efficiency certificates for `SigmaProtocol.lyubashevsky`:

1. **Strict-PPT integer-box samplers** (`sampleIntBox`, `sampleIntBoxList`, `sampleIntBoxVec`,
   and their deterministic coin maps `sampleIntBoxCoins`, `sampleIntBoxListCoins`,
   `sampleIntBoxVecCoins`):
   - `sampleIntBox B width` maps `ProbComp.sampleModNat width (2 * B + 1)` by
     `boxShift B u = (u : ℤ) - B`.
   - Every sample stays inside `[-B, B]` (`abs_sampleIntBoxCoins_le`,
     `abs_le_of_mem_support_sampleIntBox`, `mem_intBox_of_mem_support_sampleIntBoxVec`).
   - Statistical distance (`Cslib.Probability.CloseTo`) from the exact uniform distribution
     `uniformBox1D B` on `[-B, B]` is at most `(2 * B + 1) / 2 ^ width`
     (`closeTo_uniformBox1D_sampleIntBox`), and for `m` independent coordinates at most
     `m * ((2 * B + 1) / 2 ^ width)` (`closeTo_uniform_intBox_sampleIntBoxVec`,
     `closeTo_uniform_intBox_sampleIntBoxList`).
   - For dyadic centered ranges `[-2 ^ (width - 1), 2 ^ width - 1 - 2 ^ (width - 1)]`,
     `sampleDyadicIntBox width` is exact (`0` statistical distance) and strict PPT.
2. **Efficient special soundness** (`efficientSpecialSoundness_lyubashevsky`): connects
   `lyubashevskyExtractWord` to `SigmaProtocol.EfficientSpecialSoundness` over the indexed protocol
   family `lyubashevskyFamily`.
3. **Efficient verification** (`VerifierRealizedBy`, `EfficientVerifier`,
   `efficientVerifier_lyubashevsky`): a uniform polynomial-time word verifier
   `lyubashevskyVerifyWord` checks inner-box membership `z ∈ [-(γ - β), γ - β]^m` and the linear
   relation `A z = w + T ĉ` modulo `q`.
4. **Strict-PPT non-abort special HVZK simulator** (`NonAbortSimulatorRealizedBy`,
   `EfficientNonAbortSpecialHVZK`, `lyubashevskySimulateCoins`, `lyubashevskySimulateWord`,
   `efficientNonAbortSpecialHVZK_lyubashevsky`): realizes `lyubashevskySimulate` on encoded words
   within statistical distance `m * ((2 * γ + 1) / 2 ^ width)`.

## Main definitions

* `Cslib.Probability.boxShift`, `Cslib.Probability.sampleIntBoxCoins`,
  `Cslib.Probability.sampleIntBox`: 1D integer-box shift, coin map and strict-PPT sampler.
* `Cslib.Probability.sampleIntBoxListCoins`, `Cslib.Probability.sampleIntBoxVecCoins`,
  `Cslib.Probability.sampleIntBoxList`, `Cslib.Probability.sampleIntBoxVec`: `m`-coordinate
  integer-box coin maps and strict-PPT samplers.
* `Cslib.Probability.sampleDyadicIntBoxCoins`, `Cslib.Probability.sampleDyadicIntBox`: exact
  dyadic centered integer-box sampler.
* `Cslib.Crypto.Protocols.SigmaProtocol.VerifierRealizedBy`,
  `Cslib.Crypto.Protocols.SigmaProtocol.EfficientVerifier`: polynomial-time verifier certificates
  for indexed Sigma protocol families.
* `Cslib.Crypto.Protocols.SigmaProtocol.NonAbortSimulatorRealizedBy`,
  `Cslib.Crypto.Protocols.SigmaProtocol.EfficientNonAbortSpecialHVZK`: strict-PPT simulator
  certificates for Sigma protocols with aborts.
* `Cslib.Crypto.Protocols.SigmaProtocol.encCommitResponseOrAbort`: the encoding of the optional
  commitment-response pair output by a program that may abort.
* `Cslib.Crypto.Protocols.SigmaProtocol.LyubashevskyParams`,
  `Cslib.Crypto.Protocols.SigmaProtocol.encLyubashevskyParams`: parameter record and encoding.
* `Cslib.Crypto.Protocols.SigmaProtocol.lyubashevskyFamily`,
  `Cslib.Crypto.Protocols.SigmaProtocol.lyubashevskyEncoding`,
  `Cslib.Crypto.Protocols.SigmaProtocol.lyubashevskyVerifyWord`,
  `Cslib.Crypto.Protocols.SigmaProtocol.lyubashevskySimulateCoins`,
  `Cslib.Crypto.Protocols.SigmaProtocol.lyubashevskySimulateWord`.

## Main results

* `Cslib.Probability.computableInPolyTime_sampleIntBoxCoins`,
  `Cslib.Probability.isPPTOn_sampleIntBox`,
  `Cslib.Probability.closeTo_uniformBox1D_sampleIntBox`.
* `Cslib.Probability.computableInPolyTime_sampleIntBoxListCoins`,
  `Cslib.Probability.isPPTOn_sampleIntBoxList`,
  `Cslib.Probability.closeTo_uniform_intBox_sampleIntBoxVec`.
* `Cslib.Crypto.Protocols.SigmaProtocol.efficientSpecialSoundness_lyubashevsky`.
* `Cslib.Crypto.Protocols.SigmaProtocol.efficientVerifier_lyubashevsky`.
* `Cslib.Crypto.Protocols.SigmaProtocol.computableInPolyTime_lyubashevskySimulateCoins`,
  `Cslib.Crypto.Protocols.SigmaProtocol.isPPTOn_lyubashevskySimulateWord`,
  `Cslib.Crypto.Protocols.SigmaProtocol.nonAbortSimulatorRealizedBy_lyubashevskySimulateWord`,
  `Cslib.Crypto.Protocols.SigmaProtocol.efficientNonAbortSpecialHVZK_lyubashevsky`.

## References

* [V. Lyubashevsky, *Fiat-Shamir with Aborts: Applications to Lattice and Factoring-Based
  Signatures*][Lyubashevsky2009]
* [V. Lyubashevsky, *Lattice Signatures without Trapdoors*][Lyubashevsky2012]
* [L. Ducas et al., *CRYSTALS-Dilithium: A Lattice-Based Digital Signature
  Scheme*][DucasEtAl2018]
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023]
-/

@[expose] public section

namespace Cslib.Probability

open Probability.PMF Interactive Crypto Turing.MultiTapeTM
open scoped ENNReal NNReal Cslib.Probability.PMF

/-! ### Strict-PPT integer-box samplers -/

/-- The cardinality `2 * B + 1` of the symmetric integer interval `[-B, B]` is always positive. -/
instance (B : ℕ) : NeZero (2 * B + 1) := ⟨by omega⟩

/-- Shift a nonnegative residue `u < 2 * B + 1` into the symmetric interval `[-B, B]`. -/
def boxShift (B u : ℕ) : ℤ := (u : ℤ) - B

/-- `boxShift` is computable in polynomial time on binary natural inputs. -/
@[fun_prop]
theorem computableInPolyTime_boxShift :
    ComputableInPolyTime (fun p : ℕ × ℕ => boxShift p.1 p.2)
      (encPair encNat encNat) encIntBin := by
  apply ComputableInPolyTime.of_tidy
  unfold boxShift
  fun_prop

/-- Deterministic coin-to-residue map underlying `ProbComp.sampleModNat`. -/
def sampleModNatCoins (modulus : ℕ) (coins : List Bool) : ℕ :=
  BitString.binaryValue coins % modulus

/-- `sampleModNatCoins` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_sampleModNatCoins :
    ComputableInPolyTime (fun p : ℕ × List Bool => sampleModNatCoins p.1 p.2)
      (encPair encNat encBits) encNat := by
  apply ComputableInPolyTime.of_tidy
  unfold sampleModNatCoins
  fun_prop

/-- Deterministic coin-to-box map for the symmetric integer interval `[-B, B]`. -/
def sampleIntBoxCoins (B : ℕ) (coins : List Bool) : ℤ :=
  boxShift B (sampleModNatCoins (2 * B + 1) coins)

@[local fun_prop]
private theorem computableTidilyInPolyTime_sampleIntBoxCoins :
    ComputableTidilyInPolyTime (fun p : ℕ × List Bool => sampleIntBoxCoins p.1 p.2)
      (encPair encNat encBits) encIntBin := by
  unfold sampleIntBoxCoins sampleModNatCoins boxShift
  fun_prop

/-- `sampleIntBoxCoins` is computable in polynomial time from a binary bound and raw coin bits. -/
@[fun_prop]
theorem computableInPolyTime_sampleIntBoxCoins :
    ComputableInPolyTime (fun p : ℕ × List Bool => sampleIntBoxCoins p.1 p.2)
      (encPair encNat encBits) encIntBin :=
  .of_tidy computableTidilyInPolyTime_sampleIntBoxCoins

/-- Shifting a residue modulo `2 * B + 1` by `-B` stays within `[-B, B]`. -/
theorem abs_boxShift_mod_le (B u : ℕ) : |boxShift B (u % (2 * B + 1))| ≤ B := by
  have hlt : u % (2 * B + 1) < 2 * B + 1 := Nat.mod_lt u (by omega)
  rw [boxShift, abs_le]
  omega

/-- Shifting a residue modulo `2 * B + 1` by `-B` has `natAbs` at most `B`. -/
theorem natAbs_boxShift_mod_le (B u : ℕ) : (boxShift B (u % (2 * B + 1))).natAbs ≤ B := by
  zify
  exact abs_boxShift_mod_le B u

/-- Every coin string maps into `[-B, B]` under `sampleIntBoxCoins B`. -/
theorem abs_sampleIntBoxCoins_le (B : ℕ) (coins : List Bool) :
    |sampleIntBoxCoins B coins| ≤ B :=
  abs_boxShift_mod_le B (BitString.binaryValue coins)

/-- Every coin string maps to an integer of `natAbs` at most `B` under `sampleIntBoxCoins B`. -/
theorem natAbs_sampleIntBoxCoins_le (B : ℕ) (coins : List Bool) :
    (sampleIntBoxCoins B coins).natAbs ≤ B :=
  natAbs_boxShift_mod_le B (BitString.binaryValue coins)

/-- Sample an integer in `[-B, B]` using `width` fair bits reduced modulo `2 * B + 1`. -/
noncomputable def sampleIntBox (B width : ℕ) : ProbComp ℤ :=
  boxShift B <$> ProbComp.sampleModNat width (2 * B + 1)

/-- `sampleIntBox` is uniformly strict PPT when the radius `B` is supplied in binary and the bit
width `width` is supplied in unary. -/
theorem isPPTOn_sampleIntBox {α : Type} {input : α ↪ List Bool} {B width : α → ℕ}
    (hB : ComputableInPolyTime B input encNat)
    (hwidth : ComputableInPolyTime width input encUnary) :
    IsPPTOn input encIntBin (fun a => sampleIntBox (B a) (width a)) := by
  have hmod : ComputableInPolyTime (fun a => 2 * B a + 1) input encNat := by
    apply ComputableInPolyTime.of_tidy
    have := hB.tidy
    fun_prop
  have hshift : ComputableInPolyTime (fun p : α × ℕ => boxShift (B p.1) p.2)
      (encPair input encNat) encIntBin := by
    apply ComputableInPolyTime.of_tidy
    have := hB.tidy
    unfold boxShift
    fun_prop
  exact (isPPTOn_sampleModNat hwidth hmod).map_with hshift

/-- The evaluation law of `sampleIntBox B width` is the pushforward of `width` uniform fair bits by
`sampleIntBoxCoins B`. -/
theorem eval_sampleIntBox_eq_coins (B width : ℕ) :
    ProbComp.eval (sampleIntBox B width) =
      (BitString.uniformList width).map (sampleIntBoxCoins B) := by
  simp only [sampleIntBox, ProbComp.sampleModNat, ProbComp.sampleBinaryNat,
    ProbComp.eval_map, BitString.eval_sampleList, PMF.map_comp]
  rfl

/-- Every integer in the support of `sampleIntBox B width` has absolute value at most `B`. -/
theorem abs_le_of_mem_support_sampleIntBox {B width : ℕ} {z : ℤ}
    (hz : z ∈ (ProbComp.eval (sampleIntBox B width)).support) : |z| ≤ B := by
  rw [eval_sampleIntBox_eq_coins, PMF.mem_support_map_iff] at hz
  obtain ⟨coins, -, rfl⟩ := hz
  exact abs_sampleIntBoxCoins_le B coins

/-- Every integer in the support of `sampleIntBox B width` has `natAbs` at most `B`. -/
theorem natAbs_le_of_mem_support_sampleIntBox {B width : ℕ} {z : ℤ}
    (hz : z ∈ (ProbComp.eval (sampleIntBox B width)).support) : z.natAbs ≤ B := by
  zify
  exact abs_le_of_mem_support_sampleIntBox hz

/-- The support of `sampleIntBox B width` is contained in `Finset.Icc (-B) B`. -/
theorem mem_Icc_of_mem_support_sampleIntBox {B width : ℕ} {z : ℤ}
    (hz : z ∈ (ProbComp.eval (sampleIntBox B width)).support) :
    z ∈ Finset.Icc (-(B : ℤ)) B :=
  Finset.mem_Icc.mpr (abs_le.mp (abs_le_of_mem_support_sampleIntBox hz))

/-- The exact uniform distribution on the 1D integer interval `[-B, B]`. -/
noncomputable def uniformBox1D (B : ℕ) : PMF ℤ :=
  PMF.uniformOfFinset (Finset.Icc (-(B : ℤ)) B) (Finset.nonempty_Icc.mpr (by omega))

/-- Shifting the uniform distribution on `ZMod (2 * B + 1)` by `-B` gives `uniformBox1D B`. -/
theorem uniformOfFintype_zmod_map_boxShift (B : ℕ) :
    (PMF.uniformOfFintype (ZMod (2 * B + 1))).map (fun r => boxShift B r.val) =
      uniformBox1D B := by
  ext z
  rw [PMF.map_apply, uniformBox1D, PMF.uniformOfFinset_apply]
  by_cases hz : z ∈ Finset.Icc (-(B : ℤ)) B
  · rw [ite_eq_left hz]
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hz
    let u : ℕ := (z + B).toNat
    have hu_lt : u < 2 * B + 1 := by omega
    have hu_eq : boxShift B u = z := by
      simp only [boxShift, u]
      omega
    rw [tsum_eq_single (u : ZMod (2 * B + 1))]
    · have hval : ((u : ZMod (2 * B + 1)).val) = u := by
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt hu_lt]
      rw [hval, hu_eq, ite_eq_left rfl, PMF.uniformOfFintype_apply, ZMod.card, Int.card_Icc]
      congr 2
      omega
    · intro r hr
      rw [ite_eq_right]
      intro hrz
      apply hr
      apply ZMod.val_injective
      have hval : ((u : ZMod (2 * B + 1)).val) = u := by
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt hu_lt]
      rw [hval]
      simp only [boxShift] at hrz hu_eq
      omega
  · rw [ite_eq_right hz]
    refine tsum_eq_zero_iff.mpr fun r => ?_
    rw [ite_eq_right]
    rintro rfl
    apply hz
    rw [Finset.mem_Icc]
    have hlt := ZMod.val_lt r
    simp only [boxShift]
    omega

/-- `sampleIntBox B width` factors through `ZMod (2 * B + 1)` via `boxShift B ∘ ZMod.val`. -/
theorem eval_sampleIntBox_eq_map_zmod (B width : ℕ) :
    ProbComp.eval (sampleIntBox B width) =
      ((ProbComp.eval (ProbComp.sampleModNat width (2 * B + 1))).map
        (Nat.cast : ℕ → ZMod (2 * B + 1))).map (fun r => boxShift B r.val) := by
  rw [sampleIntBox, ProbComp.eval_map, PMF.map_comp, ProbComp.eval_sampleModNat,
    PMF.map_comp, PMF.map_comp]
  congr 1 with i : 1
  simp only [Function.comp_apply, ZMod.val_natCast, Nat.mod_mod]

/-- **1D box sampler statistical distance.** `sampleIntBox B width` is within
`(2 * B + 1) / 2 ^ width` of the exact uniform distribution `uniformBox1D B` on `[-B, B]`. -/
theorem closeTo_uniformBox1D_sampleIntBox (B width : ℕ) :
    CloseTo (uniformBox1D B) (ProbComp.eval (sampleIntBox B width))
      ((2 * B + 1 : ℝ≥0∞) / 2 ^ width) := by
  rw [← uniformOfFintype_zmod_map_boxShift B, eval_sampleIntBox_eq_map_zmod B width]
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
    (closeTo_uniform_sampleModNat width (2 * B + 1)).map (fun r => boxShift B r.val)

/-! ### Multi-coordinate integer-box samplers -/

/-- `m` independent draws from `uniformBox1D B` form the uniform distribution on the integer box
`intBox (Fin m) B = [-B, B]^m`. -/
theorem iid_uniformBox1D (B m : ℕ) :
    iid (uniformBox1D B) m = PMF.uniformOfFinset (intBox (Fin m) B) (intBox_nonempty B) := by
  ext z
  rw [iid_apply, PMF.uniformOfFinset_apply]
  by_cases hz : z ∈ intBox (Fin m) B
  · rw [ite_eq_left hz, card_intBox, Fintype.card_fin]
    have hcoord (i : Fin m) : uniformBox1D B (z i) = ((2 * B + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
      rw [uniformBox1D, PMF.uniformOfFinset_apply, ite_eq_left]
      · congr 2
        rw [Int.card_Icc]
        omega
      · have hzi := mem_intBox.mp hz i
        exact Finset.mem_Icc.mpr (abs_le.mp hzi)
    simp only [hcoord, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← ENNReal.inv_pow, Nat.cast_pow]
  · rw [ite_eq_right hz]
    obtain ⟨i, hi⟩ : ∃ i, ¬ |z i| ≤ B := by
      simpa only [mem_intBox, not_forall] using hz
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [uniformBox1D, PMF.uniformOfFinset_apply, ite_eq_right]
    rwa [Finset.mem_Icc, ← abs_le]

/-- View a list of integers as a vector in `Fin m → ℤ`, padding missing entries with `0`. -/
def vecOfList (m : ℕ) (l : List ℤ) : Fin m → ℤ :=
  fun i => l.getD i.val 0

@[simp] theorem vecOfList_ofFn {m : ℕ} (v : Fin m → ℤ) :
    vecOfList m (List.ofFn v) = v :=
  funext fun i => List.getD_ofFn v i 0

theorem ofFn_vecOfList {m : ℕ} {l : List ℤ} (hl : l.length = m) :
    List.ofFn (vecOfList m l) = l :=
  List.ofFn_getD_eq_of_length 0 hl

/-- Deterministic coin-to-list sampler for `[-B, B]^m`, slicing `m * width` bits into `m` rows of
`width` bits and mapping each row by `sampleIntBoxCoins B`. -/
def sampleIntBoxListCoins (B m width : ℕ) (coins : List Bool) : List ℤ :=
  (BitString.listRows m width coins).map (sampleIntBoxCoins B)

@[simp] theorem length_sampleIntBoxListCoins (B m width : ℕ) (coins : List Bool) :
    (sampleIntBoxListCoins B m width coins).length = m := by
  simp [sampleIntBoxListCoins]

/-- `sampleIntBoxListCoins` is computable in polynomial time when `B` is in binary and `m, width`
are in unary. -/
@[fun_prop]
theorem computableInPolyTime_sampleIntBoxListCoins :
    ComputableInPolyTime
      (fun p : ℕ × ℕ × ℕ × List Bool => sampleIntBoxListCoins p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encNat (encPair encUnary (encPair encUnary encBits))) (encList encIntBin) := by
  apply ComputableInPolyTime.of_tidy
  unfold sampleIntBoxListCoins
  fun_prop

/-- Deterministic coin-to-vector sampler for `intBox (Fin m) B = [-B, B]^m`. -/
def sampleIntBoxVecCoins (B m width : ℕ) (coins : List Bool) : Fin m → ℤ :=
  vecOfList m (sampleIntBoxListCoins B m width coins)

/-- Every coin string maps into `intBox (Fin m) B` under `sampleIntBoxVecCoins B m width`. -/
theorem sampleIntBoxVecCoins_mem_intBox (B m width : ℕ) (coins : List Bool) :
    sampleIntBoxVecCoins B m width coins ∈ intBox (Fin m) B := by
  rw [mem_intBox]
  intro i
  have hi : i.val < (sampleIntBoxListCoins B m width coins).length := by
    simp [sampleIntBoxListCoins]
  have hget : (sampleIntBoxListCoins B m width coins).getD i.val 0 =
      sampleIntBoxCoins B (BitString.listRows m width coins)[i.val] := by
    rw [List.getD_eq_getElem _ _ hi]
    simp [sampleIntBoxListCoins]
  change |(sampleIntBoxListCoins B m width coins).getD i.val 0| ≤ B
  rw [hget]
  exact abs_sampleIntBoxCoins_le B _

/-- Sample a list of `m` independent integers in `[-B, B]`, each using `width` fair bits. -/
noncomputable def sampleIntBoxList (B m width : ℕ) : ProbComp (List ℤ) :=
  OracleComp.replicate m (sampleIntBox B width)

/-- `sampleIntBoxList` is uniformly strict PPT when `B` is in binary and `m, width` are in unary. -/
theorem isPPTOn_sampleIntBoxList {α : Type} {input : α ↪ List Bool} {B m width : α → ℕ}
    (hB : ComputableInPolyTime B input encNat)
    (hm : ComputableInPolyTime m input encUnary)
    (hwidth : ComputableInPolyTime width input encUnary) :
    IsPPTOn input (encList encIntBin) (fun a => sampleIntBoxList (B a) (m a) (width a)) :=
  (isPPTOn_sampleIntBox hB hwidth).replicate hm

/-- Sample a vector in `Fin m → ℤ` with `m` independent coordinates from `sampleIntBox B width`. -/
noncomputable def sampleIntBoxVec (B m width : ℕ) : ProbComp (Fin m → ℤ) :=
  vecOfList m <$> sampleIntBoxList B m width

/-- `sampleIntBoxList B m width` has the same distribution as applying `sampleIntBoxListCoins` to
`m * width` uniform fair bits. -/
theorem eval_sampleIntBoxList_eq_coins (B m width : ℕ) :
    ProbComp.eval (sampleIntBoxList B m width) =
      (BitString.uniformList (m * width)).map (sampleIntBoxListCoins B m width) :=
  ProbComp.eval_replicate_of_uniformList m width (sampleIntBox B width)
    (sampleIntBoxCoins B) (eval_sampleIntBox_eq_coins B width)

/-- `sampleIntBoxVec B m width` has the same distribution as applying `sampleIntBoxVecCoins` to
`m * width` uniform fair bits. -/
theorem eval_sampleIntBoxVec_eq_coins (B m width : ℕ) :
    ProbComp.eval (sampleIntBoxVec B m width) =
      (BitString.uniformList (m * width)).map (sampleIntBoxVecCoins B m width) := by
  rw [sampleIntBoxVec, ProbComp.eval_map, eval_sampleIntBoxList_eq_coins, PMF.map_comp]
  rfl

/-- `sampleIntBoxVec B m width` has the `m`-fold independent product law `iid`. -/
theorem eval_sampleIntBoxVec_eq_iid (B m width : ℕ) :
    ProbComp.eval (sampleIntBoxVec B m width) =
      iid (ProbComp.eval (sampleIntBox B width)) m := by
  rw [sampleIntBoxVec, ProbComp.eval_map, sampleIntBoxList, ProbComp.eval_replicate_iid,
    PMF.map_comp]
  have hid : (vecOfList m ∘ (List.ofFn : (Fin m → ℤ) → List ℤ)) = id :=
    funext vecOfList_ofFn
  rw [hid, PMF.map_id]

/-- Every vector in the support of `sampleIntBoxVec B m width` lies in `intBox (Fin m) B`. -/
theorem mem_intBox_of_mem_support_sampleIntBoxVec {B m width : ℕ} {z : Fin m → ℤ}
    (hz : z ∈ (ProbComp.eval (sampleIntBoxVec B m width)).support) :
    z ∈ intBox (Fin m) B := by
  rw [eval_sampleIntBoxVec_eq_coins, PMF.mem_support_map_iff] at hz
  obtain ⟨coins, -, rfl⟩ := hz
  exact sampleIntBoxVecCoins_mem_intBox B m width coins

/-- **Multi-coordinate box sampler statistical distance (vector form).** `sampleIntBoxVec B m width`
is within `m * ((2 * B + 1) / 2 ^ width)` of the exact uniform distribution on
`intBox (Fin m) B = [-B, B]^m`. -/
theorem closeTo_uniform_intBox_sampleIntBoxVec (B m width : ℕ) :
    CloseTo (PMF.uniformOfFinset (intBox (Fin m) B) (intBox_nonempty B))
      (ProbComp.eval (sampleIntBoxVec B m width))
      ((m : ℝ≥0∞) * ((2 * B + 1 : ℝ≥0∞) / 2 ^ width)) := by
  rw [← iid_uniformBox1D B m, eval_sampleIntBoxVec_eq_iid B m width]
  have h1 := closeTo_uniformBox1D_sampleIntBox B width
  induction m with
  | zero =>
    simp only [PMF.iid, Nat.cast_zero, zero_mul, CloseTo.refl]
  | succ m ih =>
    simp only [PMF.iid, PMF.monad_bind_eq_bind]
    refine (CloseTo.bind h1 (fun a _ => CloseTo.map ih (Fin.cons (α := fun _ => ℤ) a))).mono ?_
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]

/-- **Multi-coordinate box sampler statistical distance (list form).** `sampleIntBoxList B m width`
is within `m * ((2 * B + 1) / 2 ^ width)` of the encoded uniform distribution on
`intBox (Fin m) B`. -/
theorem closeTo_uniform_intBox_sampleIntBoxList (B m width : ℕ) :
    CloseTo ((PMF.uniformOfFinset (intBox (Fin m) B) (intBox_nonempty B)).map List.ofFn)
      (ProbComp.eval (sampleIntBoxList B m width))
      ((m : ℝ≥0∞) * ((2 * B + 1 : ℝ≥0∞) / 2 ^ width)) := by
  have heq : ProbComp.eval (sampleIntBoxList B m width) =
      (ProbComp.eval (sampleIntBoxVec B m width)).map List.ofFn := by
    rw [eval_sampleIntBoxVec_eq_iid, sampleIntBoxList, ProbComp.eval_replicate_iid]
  rw [heq]
  exact (closeTo_uniform_intBox_sampleIntBoxVec B m width).map List.ofFn

/-! ### Exact dyadic centered integer-box sampler -/

/-- Deterministic coin-to-integer map for the dyadic half-range
`[-2 ^ (width - 1), 2 ^ width - 1 - 2 ^ (width - 1)]`. -/
def sampleDyadicIntBoxCoins (width : ℕ) (coins : List Bool) : ℤ :=
  (BitString.binaryValue coins : ℤ) - (2 : ℤ) ^ (width - 1)

/-- `sampleDyadicIntBoxCoins` is computable in polynomial time for a unary bit width. -/
@[fun_prop]
theorem computableInPolyTime_sampleDyadicIntBoxCoins :
    ComputableInPolyTime (fun p : ℕ × List Bool => sampleDyadicIntBoxCoins p.1 p.2)
      (encPair encUnary encBits) encIntBin := by
  apply ComputableInPolyTime.of_tidy
  unfold sampleDyadicIntBoxCoins
  fun_prop

/-- Sample an integer uniformly from the dyadic range `[0, 2 ^ width - 1] - 2 ^ (width - 1)`. -/
noncomputable def sampleDyadicIntBox (width : ℕ) : ProbComp ℤ :=
  (fun u : ℕ => (u : ℤ) - (2 : ℤ) ^ (width - 1)) <$> ProbComp.sampleBinaryNat width

/-- `sampleDyadicIntBox` is uniformly strict PPT for a unary bit width. -/
theorem isPPTOn_sampleDyadicIntBox {α : Type} {input : α ↪ List Bool} {width : α → ℕ}
    (hwidth : ComputableInPolyTime width input encUnary) :
    IsPPTOn input encIntBin (fun a => sampleDyadicIntBox (width a)) := by
  have hshift : ComputableInPolyTime
      (fun p : α × ℕ => (p.2 : ℤ) - (2 : ℤ) ^ (width p.1 - 1))
      (encPair input encNat) encIntBin := by
    apply ComputableInPolyTime.of_tidy
    have := hwidth.tidy
    fun_prop
  exact (ComputableInPolyTime.sampleBinaryNat hwidth).map_with hshift

/-- The exact uniform distribution on the dyadic centered range
`[0, 2 ^ width - 1] - 2 ^ (width - 1)`. -/
noncomputable def uniformDyadicIntBox (width : ℕ) : PMF ℤ :=
  (PMF.uniformOfFintype (Fin (2 ^ width))).map fun u => (u.val : ℤ) - (2 : ℤ) ^ (width - 1)

/-- `sampleDyadicIntBox width` has the exact law `uniformDyadicIntBox width`. -/
theorem eval_sampleDyadicIntBox (width : ℕ) :
    ProbComp.eval (sampleDyadicIntBox width) = uniformDyadicIntBox width := by
  simp only [sampleDyadicIntBox, uniformDyadicIntBox, ProbComp.eval_map,
    ProbComp.eval_sampleBinaryNat, PMF.map_comp]
  rfl

/-- `sampleDyadicIntBox width` has `0` statistical distance from `uniformDyadicIntBox width`. -/
theorem closeTo_uniformDyadicIntBox_sampleDyadicIntBox (width : ℕ) :
    CloseTo (uniformDyadicIntBox width) (ProbComp.eval (sampleDyadicIntBox width)) 0 := by
  rw [eval_sampleDyadicIntBox]
  exact CloseTo.refl _

end Cslib.Probability

namespace Cslib.Crypto.Protocols.SigmaProtocol

open Mathlib.Tactic.Matrix

open Probability Probability.PMF Interactive Turing.MultiTapeTM
open scoped ENNReal _root_.Matrix

/-! ### Efficient verifier and non-abort simulator interfaces -/

variable {I : Type} {X Y T C Z : I → Type}

/-- The word function `f` computes the verifier of the protocol family `P` on encodings: from the
index and the encoded statement, commitment, challenge and response, it returns `(P i).verify`. -/
def VerifierRealizedBy (P : ∀ i, SigmaProtocol (X i) (Y i) (T i) (C i) (Z i))
    (enc : Encoding I Y T C Z)
    (f : I × List Bool × List Bool × List Bool × List Bool → Bool) : Prop :=
  ∀ i y t c z,
    f (i, enc.statement i y, enc.commitment i t, enc.challenge i c, enc.response i z) =
      (P i).verify y t c z

/-- **Efficient verification** for an indexed family of Sigma protocols: one deterministic
polynomial-time function of the index and words computes `(P i).verify` on encodings. -/
def EfficientVerifier (P : ∀ i, SigmaProtocol (X i) (Y i) (T i) (C i) (Z i))
    (enc : Encoding I Y T C Z) : Prop :=
  ∃ f, ComputableInPolyTime f
      (encPair enc.index (encPair encBits (encPair encBits (encPair encBits encBits)))) encBool ∧
    VerifierRealizedBy P enc f

/-- Output of a word program that may abort, such as a non-abort simulator or a signing attempt:
`some (t, z)`, a commitment and a response as bit words, or `none` on an abort. `encOption`
encodes `none` as the empty word and `some` by a `true` tag bit before the pair, whose commitment
is framed. -/
abbrev encCommitResponseOrAbort : Option (List Bool × List Bool) ↪ List Bool :=
  encOption (encPair encBits encBits)

/-- The program `program` realizes the non-abort simulator family `simulate` on encodings up to
statistical distance `δ`: on the index, the encoded statement and the encoded challenge, its output
in `Option (List Bool × List Bool)` is within `δ i` of the encoded commitment/response pair (or
`none` for an abort) sampled by `simulate i`. -/
def NonAbortSimulatorRealizedBy
    (enc : Encoding I Y T C (fun i => Option (Z i)))
    (simulate : ∀ i, Y i → C i → PMF (Option (T i × Z i)))
    (program : I × List Bool × List Bool → ProbComp (Option (List Bool × List Bool)))
    (δ : I → ℝ≥0∞) : Prop :=
  ∀ i y c, CloseTo
    ((simulate i y c).map
      (Option.map fun tz => (enc.commitment i tz.1, enc.response i (some tz.2))))
    (ProbComp.eval (program (i, enc.statement i y, enc.challenge i c))) (δ i)

/-- **Efficient special HVZK up to aborts**, with statistical error `δ`. At every index `simulate i`
is a perfect `NonAbortSpecialHVZK` simulator for `P i`, and one uniform strict PPT program realizes
the family on encodings up to `δ`. -/
structure EfficientNonAbortSpecialHVZK
    (P : ∀ i, SigmaProtocol (X i) (Y i) (T i) (C i) (Option (Z i)))
    (R : ∀ i, X i → Y i → Prop)
    (enc : Encoding I Y T C (fun i => Option (Z i)))
    (simulate : ∀ i, Y i → C i → PMF (Option (T i × Z i))) (δ : I → ℝ≥0∞) : Prop where
  /-- `simulate i` is a perfect non-abort special HVZK simulator at every index. -/
  nonAbortSpecialHVZK : ∀ i, (P i).NonAbortSpecialHVZK (R i) (simulate i)
  /-- One uniform strict PPT program realizes the simulator family up to `δ`. -/
  realized : ∃ program,
    IsPPTOn (encSimulatorInput enc.index) encCommitResponseOrAbort program ∧
    NonAbortSimulatorRealizedBy enc simulate program δ

/-- A program realizing a non-abort simulator is `δ i`-close to the honest prover's encoded
`acceptedTranscript` (published transcripts and aborts) at every challenge. -/
theorem NonAbortSimulatorRealizedBy.closeTo_acceptedTranscript
    {P : ∀ i, SigmaProtocol (X i) (Y i) (T i) (C i) (Option (Z i))}
    {R : ∀ i, X i → Y i → Prop}
    {enc : Encoding I Y T C (fun i => Option (Z i))}
    {simulate : ∀ i, Y i → C i → PMF (Option (T i × Z i))}
    {program : I × List Bool × List Bool → ProbComp (Option (List Bool × List Bool))}
    {δ : I → ℝ≥0∞}
    (hS : ∀ i, (P i).NonAbortSpecialHVZK (R i) (simulate i))
    (h : NonAbortSimulatorRealizedBy enc simulate program δ)
    {i : I} {x : X i} {y : Y i} (hxy : R i x y) (c : C i) :
    CloseTo
      (((P i).acceptedTranscript x y c).map
        (Option.map fun tz => (enc.commitment i tz.1, enc.response i (some tz.2))))
      (ProbComp.eval (program (i, enc.statement i y, enc.challenge i c))) (δ i) := by
  rw [← (hS i).acceptedTranscript_eq x y hxy c]
  exact h i y c

/-! ### Word encodings for Lyubashevsky's identification family -/

/-- Runtime parameters for an indexed family of Lyubashevsky identification protocols:
unary dimensions `(n, m, k)` and per-coordinate sampling bit width `width`, paired with binary
modulus and box radii `(q, γ, β)`. -/
@[ext]
structure LyubashevskyParams where
  /-- Number of rows `n` in the public matrix `A`. -/
  n : ℕ
  /-- Number of columns `m` in the public matrix `A` (and response dimension). -/
  m : ℕ
  /-- Challenge bit length `k` (and number of columns in `T`). -/
  k : ℕ
  /-- Per-coordinate sampling bit width `width`. -/
  width : ℕ
  /-- Modulus `q`. -/
  q : ℕ
  /-- Outer commitment box radius `γ`. -/
  γ : ℕ
  /-- Rejection margin `β` (inner response box radius is `γ - β`). -/
  β : ℕ
  deriving DecidableEq, Repr

/-- Word encoding of `LyubashevskyParams`: `(n, m, k, width)` in unary and `(q, γ, β)` in
binary. -/
enc_structure encLyubashevskyParams : LyubashevskyParams where
  n : encUnary,
  m : encUnary,
  k : encUnary,
  width : encUnary,
  q : encNat,
  γ : encNat,
  β : encNat

attribute [fun_prop] encLyubashevskyParams_n_polyTime encLyubashevskyParams_m_polyTime
  encLyubashevskyParams_k_polyTime encLyubashevskyParams_width_polyTime
  encLyubashevskyParams_q_polyTime encLyubashevskyParams_γ_polyTime
  encLyubashevskyParams_β_polyTime encLyubashevskyParams_mk_polyTime

/-- Encode an element of `ZMod q` via its canonical integer representative `ZMod.cast` in binary.
This is injective for every `q : ℕ`, including `q = 0`. -/
def encZMod (q : ℕ) : ZMod q ↪ List Bool :=
  ⟨fun a => encIntBin (ZMod.cast a),
    encIntBin.injective.comp (Function.LeftInverse.injective ZMod.intCast_zmod_cast)⟩

/-- Encode a vector in `Fin n → ZMod q` as a framed list of binary integers. -/
def encZModVec (n q : ℕ) : (Fin n → ZMod q) ↪ List Bool :=
  ⟨fun v => encList encIntBin (List.ofFn fun i : Fin n => ZMod.cast (v i)), by
    intro u v huv
    have hlist := (encList encIntBin).injective huv
    funext i
    have hi := congrArg (fun l : List ℤ => l.getD i.val 0) hlist
    simp only [List.getD_ofFn] at hi
    exact Function.LeftInverse.injective ZMod.intCast_zmod_cast hi⟩

/-- Encode a matrix in `Matrix (Fin n) (Fin m) (ZMod q)` as a framed list of row lists. -/
def encZModMatrix (n m q : ℕ) : Matrix (Fin n) (Fin m) (ZMod q) ↪ List Bool :=
  ⟨fun M => encList (encList encIntBin)
      (List.ofFn fun i : Fin n => List.ofFn fun j : Fin m => ZMod.cast (M i j)), by
    intro M N hMN
    have hrows := (encList (encList encIntBin)).injective hMN
    ext i j
    have hij := congrArg (fun rows : List (List ℤ) => (rows.getD i.val []).getD j.val 0) hrows
    simp only [List.getD_ofFn] at hij
    exact Function.LeftInverse.injective ZMod.intCast_zmod_cast hij⟩

/-- Encode a fixed-width bit-string challenge `BitString k` as a raw bit list. -/
def encBitString (k : ℕ) : BitString k ↪ List Bool :=
  ⟨List.ofFn, List.ofFn_injective⟩

/-- Encode an optional integer response `Option (Fin m → ℤ)` via `encOption (encList encIntBin)`. -/
def encIntVecOption (m : ℕ) : Option (Fin m → ℤ) ↪ List Bool :=
  ⟨fun oz => encOption (encList encIntBin) (oz.map List.ofFn),
    (encOption (encList encIntBin)).injective.comp
      (Option.map_injective List.ofFn_injective)⟩

/-- Encode an extracted SIS witness `Fin m ⊕ Fin k → ℤ` as a framed list of `m + k` binary
integers, matching `lyubashevskyExtractWord_eq_extract`. -/
def encExtractedWitness (m k : ℕ) : (Fin m ⊕ Fin k → ℤ) ↪ List Bool :=
  ⟨fun u => encList encIntBin
      (List.ofFn fun j : Fin (m + k) => u (finSumFinEquiv.symm j)), by
    intro u v huv
    have hlist := (encList encIntBin).injective huv
    have hfn := List.ofFn_injective hlist
    funext s
    have hs := congrFun hfn (finSumFinEquiv s)
    simpa only [Equiv.symm_apply_apply] using hs⟩

/-- Lyubashevsky's identification protocol indexed by `p : LyubashevskyParams`. -/
noncomputable def lyubashevskyFamily (p : LyubashevskyParams) :
    SigmaProtocol (Matrix (Fin p.m) (Fin p.k) ℤ)
      (Matrix (Fin p.n) (Fin p.m) (ZMod p.q) ×
        Matrix (Fin p.n) (Fin p.k) (ZMod p.q))
      (Fin p.n → ZMod p.q) (BitString p.k) (Option (Fin p.m → ℤ)) :=
  lyubashevsky p.n p.m p.k p.q p.γ p.β

/-- Word encodings for `lyubashevskyFamily`. -/
def lyubashevskyEncoding :
    Encoding LyubashevskyParams
      (fun p => Matrix (Fin p.n) (Fin p.m) (ZMod p.q) ×
        Matrix (Fin p.n) (Fin p.k) (ZMod p.q))
      (fun p => Fin p.n → ZMod p.q)
      (fun p => BitString p.k)
      (fun p => Option (Fin p.m → ℤ)) where
  index := encLyubashevskyParams
  statement p := encPair (encZModMatrix p.n p.m p.q) (encZModMatrix p.n p.k p.q)
  commitment p := encZModVec p.n p.q
  challenge p := encBitString p.k
  response p := encIntVecOption p.m

/-- Extracted-witness encoding family for `lyubashevskyFamily`. -/
def encLyubashevskyExtracted (p : LyubashevskyParams) :
    (Fin p.m ⊕ Fin p.k → ℤ) ↪ List Bool :=
  encExtractedWitness p.m p.k

/-! ### Part 1a: Efficient special soundness via `NativeExtract` -/

/-- Adapter feeding the `(m, k)` dimensions and encoded challenge/response pairs from an
`ExtractorRealizedBy` input tuple into `lyubashevskyExtractWord`. -/
def lyubashevskyExtractorAdapter
    (inp : LyubashevskyParams × List Bool × List Bool × List Bool × List Bool ×
      List Bool × List Bool) : List Bool :=
  let (p, _, _, c, z, c', z') := inp
  lyubashevskyExtractWord
    (encPair (encPair encUnary encUnary)
      (encPair (encPair encBits encBits) (encPair encBits encBits))
      ((p.m, p.k), ((c, z), (c', z'))))

/-- `lyubashevskyExtractorAdapter` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_lyubashevskyExtractorAdapter :
    ComputableInPolyTime lyubashevskyExtractorAdapter
      (encPair encLyubashevskyParams (encPair encBits (encPair encBits
        (encPair encBits (encPair encBits (encPair encBits encBits)))))) encBits := by
  let encPack := encPair (encPair encUnary encUnary)
    (encPair (encPair encBits encBits) (encPair encBits encBits))
  have hpack : ComputableInPolyTime
      (fun inp : LyubashevskyParams × List Bool × List Bool × List Bool × List Bool ×
          List Bool × List Bool =>
        let (p, _, _, c, z, c', z') := inp
        encPack ((p.m, p.k), ((c, z), (c', z'))))
      (encPair encLyubashevskyParams (encPair encBits (encPair encBits
        (encPair encBits (encPair encBits (encPair encBits encBits)))))) encBits :=
    (by fun_prop : ComputableInPolyTime
      (fun inp : LyubashevskyParams × List Bool × List Bool × List Bool × List Bool ×
          List Bool × List Bool =>
        let (p, _, _, c, z, c', z') := inp
        ((p.m, p.k), ((c, z), (c', z'))))
      (encPair encLyubashevskyParams (encPair encBits (encPair encBits
        (encPair encBits (encPair encBits (encPair encBits encBits))))))
      encPack).encoding_comp
  exact computableInPolyTime_lyubashevskyExtractWord.comp hpack

/-- `lyubashevskyExtractorAdapter` realizes the typed extractor `lyubashevskyExtract` across all
parameter records `p : LyubashevskyParams`. -/
theorem extractorRealizedBy_lyubashevskyExtractorAdapter :
    ExtractorRealizedBy lyubashevskyEncoding encLyubashevskyExtracted
      (fun p => lyubashevskyExtract p.n p.m p.k p.q)
      lyubashevskyExtractorAdapter := by
  intro p y t c z c' z'
  have hinput :
      encPair (encPair encUnary encUnary)
        (encPair (encPair encBits encBits) (encPair encBits encBits))
        ((p.m, p.k),
          ((lyubashevskyEncoding.challenge p c, lyubashevskyEncoding.response p z),
            (lyubashevskyEncoding.challenge p c', lyubashevskyEncoding.response p z'))) =
      encLyubashevskyExtractInput ((p.m, p.k),
        ((List.ofFn c, z.map List.ofFn), (List.ofFn c', z'.map List.ofFn))) := rfl
  dsimp only [lyubashevskyExtractorAdapter]
  rw [hinput, lyubashevskyExtractWord_eq_extract p.n p.m p.k p.q y t c z c' z']
  rfl

/-- **Lyubashevsky's identification protocol has efficient special soundness** for the relaxed SIS
relation with norm bound `max (2 * (γ - β)) 1`. -/
theorem efficientSpecialSoundness_lyubashevsky :
    EfficientSpecialSoundness lyubashevskyFamily
      (fun p u y => SIS.IsSolution (Matrix.fromCols y.1 y.2) (max (2 * (p.γ - p.β)) 1) u)
      lyubashevskyEncoding encLyubashevskyExtracted
      (fun p => lyubashevskyExtract p.n p.m p.k p.q) where
  specialSoundness _ := lyubashevsky_specialSoundness
  polyTime := ⟨lyubashevskyExtractorAdapter,
    computableInPolyTime_lyubashevskyExtractorAdapter,
    extractorRealizedBy_lyubashevskyExtractorAdapter⟩

/-! ### Part 1b: Uniform polynomial-time verifier (`EfficientVerifier`) -/

/-- Total polynomial-time decoder for framed lists of signed binary integers. -/
def intListDecoder : Decoder (encList encIntBin) :=
  Decoder.list Decoder.intBin

/-- Total polynomial-time decoder for framed matrices of signed binary integers. -/
def intMatrixDecoder : Decoder (encList (encList encIntBin)) :=
  Decoder.list intListDecoder

/-- Total polynomial-time decoder for optional framed integer lists. -/
def responseListDecoder : Decoder (encOption (encList encIntBin)) :=
  Decoder.option intListDecoder

@[local fun_prop]
private theorem computableInPolyTime_decodeIntList :
    ComputableInPolyTime intListDecoder.decode encBits (encList encIntBin) :=
  intListDecoder.computableInPolyTime

@[local fun_prop]
private theorem computableInPolyTime_decodeIntMatrix :
    ComputableInPolyTime intMatrixDecoder.decode encBits (encList (encList encIntBin)) :=
  intMatrixDecoder.computableInPolyTime

@[local fun_prop]
private theorem computableInPolyTime_decodeResponseList :
    ComputableInPolyTime responseListDecoder.decode encBits (encOption (encList encIntBin)) :=
  responseListDecoder.computableInPolyTime

/-- Reduce an integer `a` to its canonical `ZMod q` representative `ZMod.cast (a : ZMod q)`, for any
`q : ℕ` (including `q = 0`). -/
def zmodReduce (q : ℕ) (a : ℤ) : ℤ :=
  if q == 0 then a else ((a % (q : ℤ)).toNat : ℤ)

@[local fun_prop]
private theorem computableTidilyInPolyTime_zmodReduce :
    ComputableTidilyInPolyTime (fun p : ℕ × ℤ => zmodReduce p.1 p.2)
      (encPair encNat encIntBin) encIntBin := by
  have hmod : ComputableInPolyTime (fun p : ℕ × ℤ => ((p.2 % (p.1 : ℤ)).toNat : ℤ))
      (encPair encNat encIntBin) encIntBin :=
    ComputableInPolyTime.intBin_natCast.comp
      (ComputableInPolyTime.intBin_emodNat' (by fun_prop) (by fun_prop))
  have hmod_tidy := hmod.tidy
  unfold zmodReduce
  fun_prop

/-- `zmodReduce` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_zmodReduce :
    ComputableInPolyTime (fun p : ℕ × ℤ => zmodReduce p.1 p.2)
      (encPair encNat encIntBin) encIntBin :=
  .of_tidy computableTidilyInPolyTime_zmodReduce

/-- `zmodReduce q a` equals `ZMod.cast (a : ZMod q)` for every `q : ℕ` and `a : ℤ`. -/
theorem zmodReduce_eq_cast (q : ℕ) (a : ℤ) :
    zmodReduce q a = ZMod.cast (a : ZMod q) := by
  rw [zmodReduce, ZMod.coe_intCast]
  by_cases hq : q = 0
  · subst q
    simp
  · have hq' : (q == 0) = false := beq_false_of_ne hq
    simp only [hq', Bool.false_eq_true, ↓reduceIte]
    have hnonneg : 0 ≤ a % (q : ℤ) := Int.emod_nonneg a (by omega)
    omega

/-- Convert the first `k` bits of a raw challenge word `c` into a `0`-`1` integer list. -/
def challengeIntList (k : ℕ) (c : List Bool) : List ℤ :=
  (List.range k).map fun j => if c.getD j false then 1 else 0

/-- Check whether the first `m` coordinates of `z` lie in `[-B, B]`. -/
def inBoxList (m B : ℕ) (z : List ℤ) : Bool :=
  (List.range m).all fun j => decide ((z.getD j 0).natAbs ≤ B)

/-- Polynomial-time evaluation on the displayed binary/unary encodings. -/
@[fun_prop]
theorem computableInPolyTime_challengeIntList :
    ComputableInPolyTime (fun p : ℕ × List Bool => challengeIntList p.1 p.2)
      (encPair encUnary encBits) (encList encIntBin) := by
  unfold challengeIntList
  fun_prop

/-- Polynomial-time evaluation on the displayed binary/unary encodings. -/
@[fun_prop]
theorem computableInPolyTime_inBoxList :
    ComputableInPolyTime (fun p : ℕ × ℕ × List ℤ => inBoxList p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encNat (encList encIntBin))) encBool := by
  unfold inBoxList
  fun_prop

/-- Check whether `A z = w + T ĉ` modulo `q` across the first `n` rows. -/
def lyubashevskyVerifyEqList (n m k q : ℕ) (A T : List (List ℤ)) (w z : List ℤ)
    (c : List Bool) : Bool :=
  (List.range n).all fun i =>
    decide (zmodReduce q (ListMatrix.dotProduct m (A.getD i []) z) =
      zmodReduce q (w.getD i 0 + ListMatrix.dotProduct k (T.getD i []) (challengeIntList k c)))

/-- List-level verifier for Lyubashevsky's identification protocol. -/
def lyubashevskyVerifyList (n m k q γ β : ℕ) (A T : List (List ℤ)) (w : List ℤ)
    (c : List Bool) (oz : Option (List ℤ)) : Bool :=
  oz.isSome &&
    inBoxList m (γ - β) (oz.getD []) &&
    lyubashevskyVerifyEqList n m k q A T w (oz.getD []) c

/-- Complete serialized verifier program for `lyubashevskyFamily`. -/
def lyubashevskyVerifyWord
    (inp : LyubashevskyParams × List Bool × List Bool × List Bool × List Bool) : Bool :=
  let (p, yw, ww, cw, zw) := inp
  lyubashevskyVerifyList p.n p.m p.k p.q p.γ p.β
    (intMatrixDecoder.decode (unframe yw))
    (intMatrixDecoder.decode (dropFrame yw))
    (intListDecoder.decode ww)
    cw
    (responseListDecoder.decode zw)

/-- `lyubashevskyVerifyWord` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_lyubashevskyVerifyWord :
    ComputableInPolyTime lyubashevskyVerifyWord
      (encPair encLyubashevskyParams (encPair encBits (encPair encBits (encPair encBits encBits))))
      encBool := by
  unfold lyubashevskyVerifyWord lyubashevskyVerifyList inBoxList lyubashevskyVerifyEqList
  fun_prop

theorem challengeIntList_ofFn {k : ℕ} (c : BitString k) :
    challengeIntList k (List.ofFn c) = List.ofFn (lyubashevskyChallenge c) := by
  rw [challengeIntList, ← List.map_coe_finRange_eq_range, List.map_map]
  conv_rhs => rw [List.ofFn_eq_map]
  refine List.map_congr_left fun j _ => ?_
  simp [lyubashevskyChallenge]

theorem inBoxList_ofFn {m B : ℕ} (z : Fin m → ℤ) :
    inBoxList m B (List.ofFn z) = decide (z ∈ intBox (Fin m) B) := by
  rw [Bool.eq_iff_iff, inBoxList, List.all_eq_true, decide_eq_true_eq, mem_intBox]
  constructor
  · intro h i
    have hi := h i.val (List.mem_range.mpr i.isLt)
    simp only [List.getD_ofFn, decide_eq_true_eq] at hi
    zify at hi
    exact hi
  · intro h j hj
    have hj_lt : j < m := List.mem_range.mp hj
    have hi := h ⟨j, hj_lt⟩
    simp only [List.getD_ofFn_of_lt z hj_lt, decide_eq_true_eq]
    zify
    exact hi

theorem lyubashevskyVerifyEqList_ofFn (n m k q : ℕ)
    (A : Matrix (Fin n) (Fin m) (ZMod q)) (T : Matrix (Fin n) (Fin k) (ZMod q))
    (w : Fin n → ZMod q) (z : Fin m → ℤ) (c : BitString k) :
    lyubashevskyVerifyEqList n m k q
      (List.ofFn fun r : Fin n => List.ofFn fun col : Fin m => ZMod.cast (A r col))
      (List.ofFn fun r : Fin n => List.ofFn fun col : Fin k => ZMod.cast (T r col))
      (List.ofFn fun r : Fin n => ZMod.cast (w r))
      (List.ofFn z) (List.ofFn c) =
      decide (A *ᵥ (Int.cast ∘ z) = w + T *ᵥ (Int.cast ∘ lyubashevskyChallenge c)) := by
  rw [Bool.eq_iff_iff, lyubashevskyVerifyEqList, challengeIntList_ofFn,
    List.all_eq_true, decide_eq_true_eq, funext_iff]
  constructor
  · intro h i
    have hi := h i.val (List.mem_range.mpr i.isLt)
    rw [decide_eq_true_eq, zmodReduce_eq_cast, zmodReduce_eq_cast] at hi
    have hcast := Function.LeftInverse.injective ZMod.intCast_zmod_cast hi
    rw [ListMatrix.intCast_dotProduct_matrix_ofFn A z i] at hcast
    rw [Int.cast_add,
      ListMatrix.intCast_dotProduct_matrix_ofFn T (lyubashevskyChallenge c) i] at hcast
    simp only [List.getD_ofFn, ZMod.intCast_zmod_cast] at hcast
    exact hcast
  · intro h j hj
    have hj_lt : j < n := List.mem_range.mp hj
    let i : Fin n := ⟨j, hj_lt⟩
    rw [decide_eq_true_eq, zmodReduce_eq_cast, zmodReduce_eq_cast]
    congr 1
    rw [ListMatrix.intCast_dotProduct_matrix_ofFn A z i, Int.cast_add,
      ListMatrix.intCast_dotProduct_matrix_ofFn T (lyubashevskyChallenge c) i]
    rw [List.getD_ofFn_of_lt _ hj_lt, ZMod.intCast_zmod_cast]
    exact h i

private theorem unframe_encPair {α β : Type} (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (p : α × β) : unframe (encPair encA encB p) = encA p.1 :=
  unframe_frame_append (encA p.1) (encB p.2)

private theorem dropFrame_encPair {α β : Type} (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (p : α × β) : dropFrame (encPair encA encB p) = encB p.2 :=
  dropFrame_frame_append (encA p.1) (encB p.2)

@[simp]
theorem decode_encZModMatrix (n m q : ℕ) (M : Matrix (Fin n) (Fin m) (ZMod q)) :
    intMatrixDecoder.decode (encZModMatrix n m q M) =
      List.ofFn fun i : Fin n => List.ofFn fun j : Fin m => ZMod.cast (M i j) :=
  intMatrixDecoder.decode_enc _

@[simp]
theorem decode_encZModVec (n q : ℕ) (v : Fin n → ZMod q) :
    intListDecoder.decode (encZModVec n q v) =
      List.ofFn fun i : Fin n => ZMod.cast (v i) :=
  intListDecoder.decode_enc _

@[simp]
theorem decode_encIntVecOption (m : ℕ) (oz : Option (Fin m → ℤ)) :
    responseListDecoder.decode (encIntVecOption m oz) = oz.map List.ofFn :=
  responseListDecoder.decode_enc _

@[simp]
theorem encBitString_apply (k : ℕ) (c : BitString k) :
    encBitString k c = List.ofFn c := rfl

/-- `lyubashevskyVerifyWord` agrees with `(lyubashevskyFamily p).verify` on all encoded inputs. -/
theorem verifierRealizedBy_lyubashevskyVerifyWord :
    VerifierRealizedBy lyubashevskyFamily lyubashevskyEncoding lyubashevskyVerifyWord := by
  intro p y w c oz
  dsimp only [lyubashevskyVerifyWord, lyubashevskyEncoding]
  rw [unframe_encPair, dropFrame_encPair, decode_encZModMatrix, decode_encZModMatrix,
    decode_encZModVec, decode_encIntVecOption, encBitString_apply]
  cases oz with
  | none =>
    rfl
  | some z =>
    simp only [Option.map_some, lyubashevskyVerifyList, Option.isSome_some, Option.getD_some,
      Bool.true_and, inBoxList_ofFn, lyubashevskyVerifyEqList_ofFn, lyubashevskyFamily,
      lyubashevsky, Bool.decide_and]

/-- **Lyubashevsky's identification protocol has an efficient polynomial-time verifier.** -/
theorem efficientVerifier_lyubashevsky :
    EfficientVerifier lyubashevskyFamily lyubashevskyEncoding :=
  ⟨lyubashevskyVerifyWord, computableInPolyTime_lyubashevskyVerifyWord,
    verifierRealizedBy_lyubashevskyVerifyWord⟩

/-! ### Part 2: Strict-PPT simulator (`lyubashevskySimulateCoins`, `lyubashevskySimulateWord`) -/

/-- Compute the simulated commitment vector `w = (A z - T ĉ) mod q` as a list of `n` canonical
integer representatives. -/
def lyubashevskySimCommitList (n m k q : ℕ) (A T : List (List ℤ)) (z : List ℤ) (c : List Bool) :
    List ℤ :=
  (List.range n).map fun i =>
    zmodReduce q
      (ListMatrix.dotProduct m (A.getD i []) z -
        ListMatrix.dotProduct k (T.getD i []) (challengeIntList k c))

theorem lyubashevskySimCommitList_ofFn (n m k q : ℕ)
    (A : Matrix (Fin n) (Fin m) (ZMod q)) (T : Matrix (Fin n) (Fin k) (ZMod q))
    (z : Fin m → ℤ) (c : BitString k) :
    lyubashevskySimCommitList n m k q
      (List.ofFn fun r : Fin n => List.ofFn fun col : Fin m => ZMod.cast (A r col))
      (List.ofFn fun r : Fin n => List.ofFn fun col : Fin k => ZMod.cast (T r col))
      (List.ofFn z) (List.ofFn c) =
      List.ofFn fun i : Fin n =>
        ZMod.cast ((A *ᵥ (Int.cast ∘ z) - T *ᵥ (Int.cast ∘ lyubashevskyChallenge c)) i) := by
  rw [lyubashevskySimCommitList, challengeIntList_ofFn, ← List.map_coe_finRange_eq_range,
    List.map_map]
  conv_rhs => rw [List.ofFn_eq_map]
  refine List.map_congr_left fun i _ => ?_
  rw [Function.comp_apply, zmodReduce_eq_cast, Int.cast_sub,
    ListMatrix.intCast_dotProduct_matrix_ofFn A z i,
    ListMatrix.intCast_dotProduct_matrix_ofFn T (lyubashevskyChallenge c) i]
  rfl

/-- Deterministic postprocessing of a candidate response list `z : List ℤ` in Lyubashevsky's
simulator: check `z ∈ [-(γ - β), γ - β]^m` and, if so, return the encoded commitment
`w = A z - T ĉ` and encoded response `some z`. -/
def lyubashevskySimulatePostprocess
    (inp : (LyubashevskyParams × List Bool × List Bool) × List ℤ) :
    Option (List Bool × List Bool) :=
  let ((p, yw, cw), z) := inp
  if inBoxList p.m (p.γ - p.β) z then
    some (
      encList encIntBin
        (lyubashevskySimCommitList p.n p.m p.k p.q
          (intMatrixDecoder.decode (unframe yw))
          (intMatrixDecoder.decode (dropFrame yw))
          z cw),
      encOption (encList encIntBin) (some z))
  else
    none

/-- `lyubashevskySimulatePostprocess` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_lyubashevskySimulatePostprocess :
    ComputableInPolyTime lyubashevskySimulatePostprocess
      (encPair (encSimulatorInput encLyubashevskyParams) (encList encIntBin))
      encCommitResponseOrAbort := by
  let encIn := encPair (encPair encLyubashevskyParams (encPair encBits encBits)) (encList encIntBin)
  have hcond : ComputableInPolyTime
      (fun inp : (LyubashevskyParams × List Bool × List Bool) × List ℤ =>
        let ((p, _, _), z) := inp
        inBoxList p.m (p.γ - p.β) z)
      encIn encBool := by
    unfold inBoxList encIn
    fun_prop
  have hw_list : ComputableInPolyTime
      (fun inp : (LyubashevskyParams × List Bool × List Bool) × List ℤ =>
        let ((p, yw, cw), z) := inp
        lyubashevskySimCommitList p.n p.m p.k p.q
          (intMatrixDecoder.decode (unframe yw))
          (intMatrixDecoder.decode (dropFrame yw))
          z cw)
      encIn (encList encIntBin) := by
    unfold lyubashevskySimCommitList encIn
    fun_prop
  have hw : ComputableInPolyTime
      (fun inp : (LyubashevskyParams × List Bool × List Bool) × List ℤ =>
        let ((p, yw, cw), z) := inp
        encList encIntBin
          (lyubashevskySimCommitList p.n p.m p.k p.q
            (intMatrixDecoder.decode (unframe yw))
            (intMatrixDecoder.decode (dropFrame yw))
            z cw))
      encIn encBits :=
    hw_list.encoding_comp
  have hz : ComputableInPolyTime
      (fun inp : (LyubashevskyParams × List Bool × List Bool) × List ℤ =>
        encOption (encList encIntBin) (some inp.2))
      encIn encBits :=
    ((ComputableInPolyTime.optionSome (encList encIntBin)).comp
      (ComputableInPolyTime.snd _ _)).encoding_comp
  have hsome : ComputableInPolyTime
      (fun inp : (LyubashevskyParams × List Bool × List Bool) × List ℤ =>
        let ((p, yw, cw), z) := inp
        some (
          encList encIntBin
            (lyubashevskySimCommitList p.n p.m p.k p.q
              (intMatrixDecoder.decode (unframe yw))
              (intMatrixDecoder.decode (dropFrame yw))
              z cw),
          encOption (encList encIntBin) (some z)))
      encIn (encOption (encPair encBits encBits)) :=
    (ComputableInPolyTime.optionSome (encPair encBits encBits)).comp (hw.prod hz)
  exact hcond.ite' hsome (ComputableInPolyTime.const none)

/-- Coin-realized deterministic simulator for Lyubashevsky's identification protocol: map
`m * width` fair coin bits to `z ∈ [-γ, γ]^m` via `sampleIntBoxListCoins` and apply
`lyubashevskySimulatePostprocess`. -/
def lyubashevskySimulateCoins
    (inp : (LyubashevskyParams × List Bool × List Bool) × List Bool) :
    Option (List Bool × List Bool) :=
  let ((p, yw, cw), coins) := inp
  lyubashevskySimulatePostprocess
    ((p, yw, cw), sampleIntBoxListCoins p.γ p.m p.width coins)

/-- `lyubashevskySimulateCoins` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_lyubashevskySimulateCoins :
    ComputableInPolyTime lyubashevskySimulateCoins
      (encPair (encSimulatorInput encLyubashevskyParams) encBits)
      encCommitResponseOrAbort := by
  unfold lyubashevskySimulateCoins
  fun_prop

/-- Uniform strict-PPT simulator program for `lyubashevskyFamily` on encoded words. -/
noncomputable def lyubashevskySimulateWord
    (inp : LyubashevskyParams × List Bool × List Bool) :
    ProbComp (Option (List Bool × List Bool)) :=
  let (p, _, _) := inp
  (fun z => lyubashevskySimulatePostprocess (inp, z)) <$>
    sampleIntBoxList p.γ p.m p.width

/-- `lyubashevskySimulateWord` is uniformly strict PPT. -/
theorem isPPTOn_lyubashevskySimulateWord :
    IsPPTOn (encSimulatorInput encLyubashevskyParams)
      encCommitResponseOrAbort lyubashevskySimulateWord := by
  let encIn := encPair encLyubashevskyParams (encPair encBits encBits)
  have hγ : ComputableInPolyTime
      (fun inp : LyubashevskyParams × List Bool × List Bool => inp.1.γ) encIn encNat := by
    unfold encIn
    fun_prop
  have hm : ComputableInPolyTime
      (fun inp : LyubashevskyParams × List Bool × List Bool => inp.1.m) encIn encUnary := by
    unfold encIn
    fun_prop
  have hwidth : ComputableInPolyTime
      (fun inp : LyubashevskyParams × List Bool × List Bool => inp.1.width) encIn encUnary := by
    unfold encIn
    fun_prop
  exact (isPPTOn_sampleIntBoxList hγ hm hwidth).map_with
    computableInPolyTime_lyubashevskySimulatePostprocess

/-- `lyubashevskySimulateWord` has the same evaluation law as running `lyubashevskySimulateCoins`
on `m * width` uniform fair coin bits. -/
theorem eval_lyubashevskySimulateWord_eq_coins
    (inp : LyubashevskyParams × List Bool × List Bool) :
    ProbComp.eval (lyubashevskySimulateWord inp) =
      (BitString.uniformList (inp.1.m * inp.1.width)).map
        (fun coins => lyubashevskySimulateCoins (inp, coins)) := by
  rw [lyubashevskySimulateWord, ProbComp.eval_map, eval_sampleIntBoxList_eq_coins, PMF.map_comp]
  rfl

/-- On canonical encoded statements and challenges, `lyubashevskySimulatePostprocess` computes the
exact simulator's postprocessing of a candidate vector `z ∈ [-γ, γ]^m`. -/
theorem lyubashevskySimulatePostprocess_ofFn (p : LyubashevskyParams)
    (y : Matrix (Fin p.n) (Fin p.m) (ZMod p.q) ×
      Matrix (Fin p.n) (Fin p.k) (ZMod p.q))
    (c : BitString p.k) (z : Fin p.m → ℤ) :
    lyubashevskySimulatePostprocess
      ((p, lyubashevskyEncoding.statement p y, lyubashevskyEncoding.challenge p c),
        List.ofFn z) =
      if z ∈ intBox (Fin p.m) (p.γ - p.β) then
        some (lyubashevskyEncoding.commitment p
            (y.1 *ᵥ (Int.cast ∘ z) - y.2 *ᵥ (Int.cast ∘ lyubashevskyChallenge c)),
          lyubashevskyEncoding.response p (some z))
      else
        none := by
  dsimp only [lyubashevskySimulatePostprocess, lyubashevskyEncoding]
  rw [unframe_encPair, dropFrame_encPair, decode_encZModMatrix, decode_encZModMatrix,
    encBitString_apply, inBoxList_ofFn, lyubashevskySimCommitList_ofFn]
  simp only [decide_eq_true_eq]
  split_ifs <;> rfl

/-- **Simulator realization.** `lyubashevskySimulateWord` realizes `lyubashevskySimulate` on
encodings up to statistical distance `m * ((2 * γ + 1) / 2 ^ width)`. -/
theorem nonAbortSimulatorRealizedBy_lyubashevskySimulateWord :
    NonAbortSimulatorRealizedBy lyubashevskyEncoding
      (fun p => lyubashevskySimulate p.n p.m p.k p.q p.γ p.β)
      lyubashevskySimulateWord
      (fun p => (p.m : ℝ≥0∞) * ((2 * p.γ + 1 : ℝ≥0∞) / 2 ^ p.width)) := by
  intro p y c
  let post (z : Fin p.m → ℤ) : Option (List Bool × List Bool) :=
    lyubashevskySimulatePostprocess
      ((p, lyubashevskyEncoding.statement p y, lyubashevskyEncoding.challenge p c), List.ofFn z)
  have hideal :
      ((lyubashevskySimulate p.n p.m p.k p.q p.γ p.β y c).map
        (Option.map fun tz =>
          (lyubashevskyEncoding.commitment p tz.1,
            lyubashevskyEncoding.response p (some tz.2)))) =
        (PMF.uniformOfFinset (intBox (Fin p.m) p.γ)
          (intBox_nonempty p.γ)).map post := by
    simp only [lyubashevskySimulate, boxReject, shiftReject, PMF.map_comp]
    congr 1 with z : 1
    simp only [Function.comp_apply, add_zero, post, lyubashevskySimulatePostprocess_ofFn]
    split_ifs <;> rfl
  have hreal :
      ProbComp.eval (lyubashevskySimulateWord
        (p, lyubashevskyEncoding.statement p y, lyubashevskyEncoding.challenge p c)) =
        (ProbComp.eval (sampleIntBoxVec p.γ p.m p.width)).map post := by
    have hlist : ProbComp.eval (sampleIntBoxList p.γ p.m p.width) =
        (ProbComp.eval (sampleIntBoxVec p.γ p.m p.width)).map List.ofFn := by
      rw [eval_sampleIntBoxVec_eq_iid, sampleIntBoxList, ProbComp.eval_replicate_iid]
    rw [lyubashevskySimulateWord, ProbComp.eval_map, hlist, PMF.map_comp]
    rfl
  rw [hideal, hreal]
  exact (closeTo_uniform_intBox_sampleIntBoxVec p.γ p.m p.width).map post

/-- Witness-statement relation for `lyubashevskyFamily` at norm bound `η p`, bundling the
rejection-sampling parameter conditions `p.β ≤ p.γ` and `p.k * η p ≤ p.β` required for perfect
non-abort HVZK. -/
def lyubashevskyFamilyRelation (η : LyubashevskyParams → ℕ) (p : LyubashevskyParams)
    (S : Matrix (Fin p.m) (Fin p.k) ℤ)
    (y : Matrix (Fin p.n) (Fin p.m) (ZMod p.q) × Matrix (Fin p.n) (Fin p.k) (ZMod p.q)) : Prop :=
  p.β ≤ p.γ ∧ p.k * η p ≤ p.β ∧ lyubashevskyRelation (η p) S y

instance (η : LyubashevskyParams → ℕ) (p : LyubashevskyParams)
    (S : Matrix (Fin p.m) (Fin p.k) ℤ)
    (y : Matrix (Fin p.n) (Fin p.m) (ZMod p.q) × Matrix (Fin p.n) (Fin p.k) (ZMod p.q)) :
    Decidable (lyubashevskyFamilyRelation η p S y) := by
  unfold lyubashevskyFamilyRelation lyubashevskyRelation
  infer_instance

/-- At every parameter record `p : LyubashevskyParams`, `lyubashevskySimulate` is a perfect
`NonAbortSpecialHVZK` simulator for `lyubashevskyFamilyRelation η p`. -/
theorem lyubashevskyFamily_nonAbortSpecialHVZK (η : LyubashevskyParams → ℕ)
    (p : LyubashevskyParams) :
    (lyubashevskyFamily p).NonAbortSpecialHVZK (lyubashevskyFamilyRelation η p)
      (lyubashevskySimulate p.n p.m p.k p.q p.γ p.β) where
  accepts y c t z h := by
    obtain ⟨oz, hoz, hsome⟩ := (PMF.mem_support_map_iff _ _ _).mp h
    cases oz with
    | none => cases hsome
    | some z' =>
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hsome
      obtain ⟨rfl, rfl⟩ := hsome
      rw [lyubashevskyFamily, lyubashevsky_accepts_some_iff]
      exact ⟨mem_intBox_of_some_mem_support_boxReject hoz, (sub_add_cancel _ _).symm⟩
  acceptedTranscript_eq S y hSy c :=
    (lyubashevsky_nonAbortSpecialHVZK hSy.1 hSy.2.1).acceptedTranscript_eq S y hSy.2.2 c

/-- **Efficient non-abort special HVZK for Lyubashevsky's identification protocol.** For any witness
norm schedule `η : LyubashevskyParams → ℕ`, `lyubashevskySimulateWord` realizes non-abort special
HVZK for `lyubashevskyFamilyRelation η` with statistical error `m * ((2 * γ + 1) / 2 ^ width)`. -/
theorem efficientNonAbortSpecialHVZK_lyubashevsky (η : LyubashevskyParams → ℕ) :
    EfficientNonAbortSpecialHVZK lyubashevskyFamily
      (lyubashevskyFamilyRelation η)
      lyubashevskyEncoding
      (fun p => lyubashevskySimulate p.n p.m p.k p.q p.γ p.β)
      (fun p => (p.m : ℝ≥0∞) * ((2 * p.γ + 1 : ℝ≥0∞) / 2 ^ p.width)) where
  nonAbortSpecialHVZK := lyubashevskyFamily_nonAbortSpecialHVZK η
  realized := ⟨lyubashevskySimulateWord,
    isPPTOn_lyubashevskySimulateWord,
    nonAbortSimulatorRealizedBy_lyubashevskySimulateWord⟩

end Cslib.Crypto.Protocols.SigmaProtocol
