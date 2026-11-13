/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.UniformNat
public import CslibFrontier.Languages.Probabilistic.Repeat
public import CslibFrontier.Probability.IID
public import CslibFrontier.Probability.RejectionSampling
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Foundations.Data.List.OfFnGetD
import Mathlib.Data.List.GetD

/-!
# Fair-bit samplers for integer intervals and boxes

Sampling the integer box `[-B, B]^m`, of odd cardinality `(2 * B + 1)^m`, from a fixed number of
fair bits is approximate. `sampleIntBox B width` reduces `width` fair bits modulo `2 * B + 1`
(`ProbComp.sampleModNat`) and shifts the residue by `-B` (`boxShift`). Every sample lies in
`[-B, B]`, and the law factors through the residue sampler, so its distance from the exact uniform
law `uniformBox1D B` is the residue sampler's. `sampleIntBoxList` and `sampleIntBoxVec` draw `m`
independent coordinates; their exact counterpart is the uniform law on
`Cslib.Probability.intBox (Fin m) B`. The dyadic centered range
`[-2 ^ (width - 1), 2 ^ width - 1 - 2 ^ (width - 1)]` has power-of-two size and is sampled
exactly by `sampleDyadicIntBox width`.

Each sampler comes with a deterministic coin map, such as `sampleIntBoxCoins`, whose pushforward
of uniform fair bits is the sampler's law. The statistical-distance bounds are in
`CslibFrontier.Crypto.Game.CloseTo.IntBox` and the strict-PPT certificates in
`CslibFrontier.Computability.Probabilistic.IntBox`.

## Main definitions

* `Cslib.Probability.boxShift`, `Cslib.Probability.sampleIntBoxCoins`,
  `Cslib.Probability.sampleIntBox`: the 1D shift, coin map and sampler for `[-B, B]`.
* `Cslib.Probability.sampleIntBoxListCoins`, `Cslib.Probability.sampleIntBoxVecCoins`,
  `Cslib.Probability.sampleIntBoxList`, `Cslib.Probability.sampleIntBoxVec`: `m`-coordinate
  coin maps and samplers for `[-B, B]^m`.
* `Cslib.Probability.sampleDyadicIntBoxCoins`, `Cslib.Probability.sampleDyadicIntBox`: the exact
  dyadic centered sampler.
* `Cslib.Probability.uniformBox1D`, `Cslib.Probability.uniformDyadicIntBox`: the exact uniform
  laws on `[-B, B]` and on the dyadic centered range.
* `Cslib.Probability.vecOfList`: read a list of integers as a vector, padding with `0`.

## Main results

* `Cslib.Probability.eval_sampleIntBox_eq_coins`,
  `Cslib.Probability.eval_sampleIntBoxList_eq_coins`,
  `Cslib.Probability.eval_sampleIntBoxVec_eq_coins`: each law is the pushforward of uniform fair
  bits by its coin map.
* `Cslib.Probability.abs_le_of_mem_support_sampleIntBox`,
  `Cslib.Probability.mem_intBox_of_mem_support_sampleIntBoxVec`: every sample lies in the box.
* `Cslib.Probability.eval_sampleIntBoxVec_eq_iid`,
  `Cslib.Probability.eval_sampleIntBoxList_eq_map_ofFn`: the vector sampler has the independent
  product law, and the list sampler is its list form.
* `Cslib.Probability.eval_sampleIntBox_eq_map_zmod`, `Cslib.Probability.iid_uniformBox1D`: the
  factorization through `ZMod (2 * B + 1)` and the product form of the uniform box law.
* `Cslib.Probability.eval_sampleDyadicIntBox`: the dyadic sampler is exact.

## References

* [L. Ducas et al., *CRYSTALS-Dilithium: A Lattice-Based Digital Signature
  Scheme*][DucasEtAl2018]
-/

@[expose] public section

namespace Cslib.Probability

open Probability.PMF
open scoped ENNReal

/-! ### One-dimensional integer-box sampler -/

/-- Shift a nonnegative residue `u < 2 * B + 1` into the symmetric interval `[-B, B]`. -/
def boxShift (B u : ℕ) : ℤ := (u : ℤ) - B

/-- Deterministic coin-to-residue map underlying `ProbComp.sampleModNat`. -/
def sampleModNatCoins (modulus : ℕ) (coins : List Bool) : ℕ :=
  BitString.binaryValue coins % modulus

/-- Deterministic coin-to-box map for the symmetric integer interval `[-B, B]`. -/
def sampleIntBoxCoins (B : ℕ) (coins : List Bool) : ℤ :=
  boxShift B (sampleModNatCoins (2 * B + 1) coins)

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

/-- The list sampler is the vector sampler read as a list: `sampleIntBoxList B m width` has the
law of `List.ofFn` applied to `sampleIntBoxVec B m width`. -/
theorem eval_sampleIntBoxList_eq_map_ofFn (B m width : ℕ) :
    ProbComp.eval (sampleIntBoxList B m width) =
      (ProbComp.eval (sampleIntBoxVec B m width)).map List.ofFn := by
  rw [eval_sampleIntBoxVec_eq_iid, sampleIntBoxList, ProbComp.eval_replicate_iid]

/-- Every vector in the support of `sampleIntBoxVec B m width` lies in `intBox (Fin m) B`. -/
theorem mem_intBox_of_mem_support_sampleIntBoxVec {B m width : ℕ} {z : Fin m → ℤ}
    (hz : z ∈ (ProbComp.eval (sampleIntBoxVec B m width)).support) :
    z ∈ intBox (Fin m) B := by
  rw [eval_sampleIntBoxVec_eq_coins, PMF.mem_support_map_iff] at hz
  obtain ⟨coins, -, rfl⟩ := hz
  exact sampleIntBoxVecCoins_mem_intBox B m width coins

/-! ### Exact dyadic centered integer-box sampler -/

/-- Deterministic coin-to-integer map for the dyadic half-range
`[-2 ^ (width - 1), 2 ^ width - 1 - 2 ^ (width - 1)]`. -/
def sampleDyadicIntBoxCoins (width : ℕ) (coins : List Bool) : ℤ :=
  (BitString.binaryValue coins : ℤ) - (2 : ℤ) ^ (width - 1)

/-- Sample an integer uniformly from the dyadic range `[0, 2 ^ width - 1] - 2 ^ (width - 1)`. -/
noncomputable def sampleDyadicIntBox (width : ℕ) : ProbComp ℤ :=
  (fun u : ℕ => (u : ℤ) - (2 : ℤ) ^ (width - 1)) <$> ProbComp.sampleBinaryNat width

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

end Cslib.Probability
