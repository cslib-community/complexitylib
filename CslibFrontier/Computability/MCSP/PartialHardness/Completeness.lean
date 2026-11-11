/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.MCSP.PartialHardness.Construction
import Cslib.Foundations.Data.Nat.Asymptotics
import CslibFrontier.Computability.Circuit.Boolean.Lookup
import CslibFrontier.Computability.Circuit.Boolean.MassProduction.ConstantCopies
import CslibFrontier.Foundations.Data.BitString.Binary
import CslibFrontier.Foundations.Data.List.GetD
import CslibFrontier.Foundations.Data.Nat.AlignedPacking
import CslibFrontier.Foundations.Data.Nat.Log
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Yes completeness of the CMMSA table

If a CMMSA instance `I` has a satisfying assignment `S` of weight at most `θ`, then for every choice
of the functions `f` the partial truth table `FromCMMSA.toInstance I Δ k λ P f` is in partial MCSP,
once `λ ≥ λ₀ (m + 1) ²` for a constant `λ₀` depending only on `Δ`, `k` and `P`
(`FromCMMSA.exists_toInstance_mem_PartialMCSP`). This is the completeness half of the library's
reduction from `GapCMMSA Δ g 1` to partial MCSP (issue #4362, route B); the reduction and its
analysis are the library's own, and [Hirahara2022] fixes only the shape of the problem.

**The Yes circuit.** Pack the blocks of the functions `f v`, `v ∈ S`, into one table `F` on
`L = ⌈log₂ (2 θ λ)⌉` inputs. This works because `∑_{v ∈ S} 2 ^ ℓ v ≤ 2 λ w(S) ≤ 2 θ λ ≤ 2 ^ L`, and
because the blocks can be placed at aligned starting points (`Nat.exists_aligned_packing`). On an
input with formula index `j`:

1. choose a term `t` of `φ_j` whose variables all lie in `S`;
2. for each occupied slot `(t, q)` and each seed `i`, read `F` at the address whose bits above
   `ℓ v` are the start of the block of `v` and whose bits below are those of the seed: this is
   `f v` at the seed;
3. output the mask bits of term `t` plus the `Δ k` table values.

At a defined entry this is term `t`'s parity, which is the entry. The `Δ k` readings of `F` cost
`(1 + 1 / P) 2 ^ L / L` gates by Uhlig's theorem
(`MassProduction.eventually_mul_complexity_table_le`). Each address bit and the output read only
`⌈log₂ m⌉ + O(Δ² + Δ k)` input bits, so they cost `O((m + 1) (L + 1) ²)` gates
(`complexity_le_mul_of_forall_dependsOn`). That is at most `2 ^ L / (P L)` once
`(m + 1) ² ≤ 2 ^ L`, which `λ ≥ λ₀ (m + 1) ²` ensures.

**The threshold is existential.** `λ₀ = 2 ^ L₀` comes from Uhlig's and Lupanov's eventual bounds
and is not computed. A reduction fixes it and takes `λ = λ₀ (|I| + 1) ²`, which is polynomial in the
input length whatever the constant is, since `m ≤ |I|` for the encoding of `I`.

## Main results

* `Cslib.PartialMCSP.FromCMMSA.exists_toInstance_mem_PartialMCSP`: Yes instances map to Yes
  instances of partial MCSP for every `f`, once `λ ≥ λ₀ (m + 1) ²`.
* `Cslib.PartialMCSP.FromCMMSA.exists_satTerm`: a satisfying assignment satisfies a term of every
  formula.
* `Cslib.PartialMCSP.FromCMMSA.sum_two_pow_varLength_le_two_mul_weight`: the blocks of an
  assignment `S` have total size at most `2 w(S) λ`.

The last two are also used by the `MINKT*` generator (`Cslib.Kolmogorov.MINKTStar.GenWitness`).

## References

* [S. Hirahara, *NP-Hardness of Learning Programs and Partial MCSP*][Hirahara2022]
* [D. Uhlig, *Networks computing Boolean functions for multiple input values*][Uhlig1992]
-/

public section

namespace Cslib.PartialMCSP.FromCMMSA

open Cslib.Complexity Cslib.Logic.PL Cslib.Circuits Cslib.Circuits.Boolean
  Cslib.Circuits.Boolean.MassProduction Finset Filter

variable {I : CMMSAInstance} {Δ k lam : ℕ}

/-! ### Bits of numbers -/

/-- The low `L` bits of `t`. -/
private def natBits (L t : ℕ) : BitString L := fun r => t.testBit r

private theorem val_equivFin_natBits {L t : ℕ} (ht : t < 2 ^ L) :
    (BitString.equivFin L (natBits L t) : ℕ) = t := by
  have : natBits L t = (BitString.equivFin L).symm ⟨t, ht⟩ := by
    funext r
    simp [natBits]
  rw [this, Equiv.apply_symm_apply]

/-! ### The hard-wired table -/

open Classical in
/-- The table `F` on `L` inputs: block `[o v, o v + 2 ^ ℓ v)` of `v ∈ S` holds the truth table of
`f v`, and every other entry is `false`. -/
private noncomputable def hardTable (f : VarFunctions I lam) (S : Finset ℕ) (o : ℕ → ℕ) (L : ℕ) :
    BooleanFunction L := fun y =>
  decide (∃ v ∈ S, o v ≤ BitString.equivFin L y ∧
    (BitString.equivFin L y : ℕ) < o v + 2 ^ varLength I lam v ∧
    evalVar f v (natBits (varLength I lam v) (BitString.equivFin L y - o v)) = true)

/-- Within block `v`, the table reads `f v`. -/
private theorem hardTable_apply {f : VarFunctions I lam} {S : Finset ℕ} {o : ℕ → ℕ} {L : ℕ}
    (hdisj : ∀ u ∈ S, ∀ v ∈ S, ∀ t, o u ≤ t → t < o u + 2 ^ varLength I lam u → o v ≤ t →
      t < o v + 2 ^ varLength I lam v → u = v)
    {v : ℕ} (hv : v ∈ S) {s : ℕ} (hs : s < 2 ^ varLength I lam v) (y : BitString L)
    (hy : (BitString.equivFin L y : ℕ) = o v + s) :
    hardTable f S o L y = evalVar f v (natBits (varLength I lam v) s) := by
  unfold hardTable
  rw [Bool.eq_iff_iff, decide_eq_true_iff, hy]
  constructor
  · rintro ⟨u, hu, hu₁, hu₂, hu₃⟩
    obtain rfl := hdisj u hu v hv (o v + s) hu₁ hu₂ (Nat.le_add_right _ _) (by omega)
    simpa using hu₃
  · intro h
    exact ⟨v, hv, Nat.le_add_right _ _, by omega, by simpa using h⟩

/-! ### Addresses and the output -/

/-- Bit `r` of the address read by copy `(q, i)` for formula index `j`: for the variable `v` of
slot `(τ j, q)`, a seed bit if `r < ℓ v`, and a bit of the start `o v` of its block otherwise. -/
private def addrBit (lam : ℕ) (τ o : ℕ → ℕ) (x : BitString (inputLength I Δ k lam)) (j : ℕ)
    (q : Fin Δ) (i : Fin k) (r : ℕ) : Bool :=
  if h : τ j < Δ ∧ r < varLength I lam (var I j (τ j) q) ∧ r < seedWidth I lam then
    seed x ⟨_, h.1⟩ q i ⟨r, h.2.2⟩
  else (o (var I j (τ j) q)).testBit r

/-- The `Δ k` addresses read by the Yes circuit, `L` bits each. -/
private def addr (L : ℕ) (τ o : ℕ → ℕ) (x : BitString (inputLength I Δ k lam)) :
    Fin (Δ * k * L) → Bool := fun p =>
  addrBit lam τ o x (formulaIndex x) (finProdFinEquiv.symm (finProdFinEquiv.symm p).1).1
    (finProdFinEquiv.symm (finProdFinEquiv.symm p).1).2 (finProdFinEquiv.symm p).2

variable (I) in
/-- The output for formula index `j`, mask bits `mask` and table values `val`: the masks plus the
values of the occupied slots of term `τ j`. -/
private def combineCore (τ : ℕ → ℕ) (j : ℕ) (mask : Fin Δ → Fin Δ → Bool)
    (val : Fin (Δ * k) → Bool) : Bool :=
  if h : τ j < Δ then
    ∑ q : Fin Δ, if (q : ℕ) < (term I j (τ j)).length then
      mask ⟨_, h⟩ q + ∑ i : Fin k, val (finProdFinEquiv (q, i)) else 0
  else false

variable (I lam) in
/-- The output map of the Yes circuit, on the input and the `Δ k` table values. -/
private def combine (τ : ℕ → ℕ) :
    BitString (inputLength I Δ k lam + Δ * k) → Fin 1 → Bool := fun y _ =>
  combineCore I τ
    (formulaIndex (I := I) (Δ := Δ) (k := k) (lam := lam) fun i => y (Fin.castAdd _ i))
    (fun t q => y (Fin.castAdd _ (maskPos I Δ k lam t q))) fun p => y (Fin.natAdd _ p)

/-! ### Correctness -/

/-- Every formula of a Yes instance has a term whose variables lie in the satisfying assignment. -/
theorem exists_satTerm {S : Finset ℕ}
    (hmono : ∀ φ ∈ I.formulas, ∀ t ∈ φ, ∀ l ∈ t, l.2 = true)
    (hsat : ∀ φ ∈ I.formulas, φ.eval (fun i => decide (i ∈ S)) = true) :
    ∃ τ : ℕ → ℕ, ∀ j < I.formulas.length, τ j < (I.formulas.getD j []).length ∧
      ∀ q < (term I j (τ j)).length, var I j (τ j) q ∈ S := by
  have h (j : ℕ) : ∃ t, j < I.formulas.length → t < (I.formulas.getD j []).length ∧
      ∀ q < (term I j t).length, var I j t q ∈ S := by
    by_cases hj : j < I.formulas.length
    · have hφ := hsat _ (List.getElem_mem hj)
      obtain ⟨c, hc, hct⟩ := List.any_eq_true.1 hφ
      obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 hc
      have hjD : I.formulas.getD j [] = I.formulas[j] := by
        simp [List.getD_eq_getElem?_getD, hj]
      refine ⟨t, fun _ => ⟨hjD ▸ ht, fun q hq => ?_⟩⟩
      have htD : term I j t = I.formulas[j][t] := term_eq_getElem hj ht
      rw [htD] at hq
      have hq' := (Term.eval_eq_true_iff _ _).1 hct _ (List.getElem_mem hq)
      rw [hmono _ (List.getElem_mem hj) _ (List.getElem_mem ht) _ (List.getElem_mem hq)] at hq'
      have hvar : var I j t q = I.formulas[j][t][q].1 := by
        simp [var, htD, List.getD_eq_getElem?_getD, hq]
      rw [hvar]
      simpa using hq'
    · exact ⟨0, fun h => absurd h hj⟩
  choose τ hτ using h
  exact ⟨τ, fun j hj => hτ j hj⟩

/-- The blocks of the variables of an assignment `S` have total size at most `2 w(S) λ`. -/
theorem sum_two_pow_varLength_le_two_mul_weight {S : Finset ℕ}
    (hS : S ⊆ Finset.range I.weights.length) (hwf : I.WellFormed Δ) (hlam : 1 ≤ lam) :
    ∑ v ∈ S, 2 ^ varLength I lam v ≤ 2 * I.weight S * lam := by
  calc ∑ v ∈ S, 2 ^ varLength I lam v ≤ ∑ v ∈ S, 2 * (I.weights.getD v 0 * lam) := by
        refine sum_le_sum fun v hv => Nat.pow_clog_le_mul Nat.one_lt_two ?_
        have hvn := Finset.mem_range.1 (hS hv)
        have hpos := hwf.weight_pos _ (List.getD_mem 0 hvn)
        positivity
    _ = 2 * I.weight S * lam := by
        rw [← Finset.mul_sum, ← Finset.sum_mul, CMMSAInstance.weight, mul_assoc]

/-- The blocks of the satisfying assignment fit in the table. -/
private theorem sum_two_pow_varLength_le {S : Finset ℕ} (hS : S ⊆ Finset.range I.weights.length)
    (hwf : I.WellFormed Δ) (hw : I.weight S ≤ I.threshold) (hlam : 1 ≤ lam) :
    ∑ v ∈ S, 2 ^ varLength I lam v ≤ 2 ^ tableLength I lam :=
  calc ∑ v ∈ S, 2 ^ varLength I lam v ≤ 2 * I.weight S * lam :=
        sum_two_pow_varLength_le_two_mul_weight hS hwf hlam
    _ ≤ 2 * I.threshold * lam := by gcongr
    _ ≤ 2 ^ tableLength I lam := Nat.le_pow_clog Nat.one_lt_two _

/-- The address bits of an occupied slot are those of the start of its block plus the seed. -/
private theorem addrBit_eq {τ o : ℕ → ℕ} {x : BitString (inputLength I Δ k lam)} {j : ℕ}
    {t q : Fin Δ} (ht : τ j = t) {v : ℕ} (hv : var I j t q = v)
    (hvW : varLength I lam v ≤ seedWidth I lam) (hdvd : 2 ^ varLength I lam v ∣ o v) (i : Fin k)
    (r : ℕ) :
    addrBit lam τ o x j q i r = (o v + BitString.equivFin _
      (BitString.zeroExtend (d' := varLength I lam v) (seed x t q i))).testBit r := by
  obtain ⟨c, hc⟩ := hdvd
  have hlt := (BitString.equivFin _
    (BitString.zeroExtend (d' := varLength I lam v) (seed x t q i))).isLt
  rw [hc, Nat.testBit_two_pow_mul_add _ hlt]
  unfold addrBit
  by_cases h : τ j < Δ ∧ r < varLength I lam (var I j (τ j) q) ∧ r < seedWidth I lam
  · rw [dite_eq_left h]
    have htt : (⟨_, h.1⟩ : Fin Δ) = t := Fin.ext ht
    rw [htt]
    rw [ht, hv] at h
    rw [ite_eq_left h.2.1]
    have hbit := BitString.testBit_equivFin
      (BitString.zeroExtend (d' := varLength I lam v) (seed x t q i)) ⟨r, h.2.1⟩
    simp only at hbit
    rw [hbit]
    simp [BitString.zeroExtend, h.2.2]
  · rw [dite_eq_right h]
    rw [ht, hv] at h ⊢
    by_cases hr : r < varLength I lam v
    · exact absurd ⟨t.isLt, hr, by omega⟩ h
    · rw [ite_eq_right hr, hc, Nat.testBit_two_pow_mul]
      simp [show varLength I lam v ≤ r by omega]

/-- **The Yes circuit agrees with the table.** -/
private theorem combine_append_eq {S : Finset ℕ} {f : VarFunctions I lam} {τ : ℕ → ℕ}
    {o : ℕ → ℕ} {L : ℕ} (hS : S ⊆ Finset.range I.weights.length) (hΔ : I.WellFormed Δ)
    (hτ : ∀ j < I.formulas.length, τ j < (I.formulas.getD j []).length ∧
      ∀ q < (term I j (τ j)).length, var I j (τ j) q ∈ S)
    (hfit : ∀ v ∈ S, 2 ^ varLength I lam v ∣ o v ∧ o v + 2 ^ varLength I lam v ≤ 2 ^ L)
    (hdisj : ∀ u ∈ S, ∀ v ∈ S, ∀ t, o u ≤ t → t < o u + 2 ^ varLength I lam u → o v ≤ t →
      t < o v + 2 ^ varLength I lam v → u = v)
    {x : BitString (inputLength I Δ k lam)} {b : Bool} (hx : entry f x = some b) :
    combine I lam τ (Fin.append x (directProduct (hardTable f S o L) (Δ * k) (addr L τ o x)))
      0 = b := by
  have hj := formulaIndex_lt_of_entry_eq_some hx
  obtain ⟨htj, hvars⟩ := hτ _ hj
  have hφΔ : (I.formulas.getD (formulaIndex x) []).length ≤ Δ :=
    hΔ.length_le (List.getD_mem [] hj)
  have htΔ : τ (formulaIndex x) < Δ := lt_of_lt_of_le htj hφΔ
  rw [← termParity_eq_of_entry_eq_some hx ⟨_, htΔ⟩ htj]
  simp only [combine, combineCore, Fin.append_left, Fin.append_right, termParity, slotBit,
    htΔ, ↓reduceDIte]
  refine Finset.sum_congr rfl fun q _ => ?_
  split_ifs with hq
  · congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have hvS := hvars q hq
    set v := var I (formulaIndex x) (τ (formulaIndex x)) q with hv_def
    have hvn := Finset.mem_range.1 (hS hvS)
    have hvW : varLength I lam v ≤ seedWidth I lam := varLength_le_seedWidth hvn
    set s := (BitString.equivFin _ (BitString.zeroExtend (d' := varLength I lam v)
      (seed x ⟨_, htΔ⟩ q i)) : ℕ) with hs_def
    have hs : s < 2 ^ varLength I lam v := (BitString.equivFin _ _).isLt
    have hin : BitString.block (addr L τ o x) (finProdFinEquiv (q, i)) =
        natBits L (o v + s) := by
      funext r
      simp only [BitString.block, addr, Equiv.symm_apply_apply, natBits]
      exact addrBit_eq (t := ⟨_, htΔ⟩) rfl rfl hvW (hfit v hvS).1 i r
    have hlt : o v + s < 2 ^ L := by have := (hfit v hvS).2; omega
    simp only [directProduct, hin]
    rw [hardTable_apply hdisj hvS hs _ (val_equivFin_natBits hlt)]
    have hbits : natBits (varLength I lam v) s =
        BitString.zeroExtend (d' := varLength I lam v) (seed x ⟨_, htΔ⟩ q i) := by
      funext r
      simp only [natBits, hs_def]
      exact BitString.testBit_equivFin _ r
    rw [hbits]
    unfold evalVar
    rw [dite_eq_left hvn, dite_eq_left hvn]
    exact congrArg _ (BitString.zeroExtend_self _)
  · rfl

/-! ### Size -/

/-- Each address bit reads the formula index and one seed bit per term. -/
private theorem complexity_addr_le (L : ℕ) (τ o : ℕ → ℕ) :
    complexity interpretation (addr (I := I) (Δ := Δ) (k := k) (lam := lam) L τ o) ≤
      Δ * k * L * (2 ^ (indexWidth I + Δ) * (2 * (indexWidth I + Δ) + 3) + 1) := by
  refine complexity_le_mul_of_forall_dependsOn _ fun p => ?_
  obtain ⟨⟨qi, r⟩, rfl⟩ := finProdFinEquiv.surjective p
  obtain ⟨⟨q, i⟩, rfl⟩ := finProdFinEquiv.surjective qi
  refine ⟨univ.image (indexPos I Δ k lam) ∪
    (if hr : (r : ℕ) < seedWidth I lam then univ.image fun t => seedPos I Δ k lam t q i ⟨r, hr⟩
      else ∅), ?_, ?_⟩
  · refine (card_union_le _ _).trans (add_le_add (card_image_le.trans (by simp)) ?_)
    split_ifs
    · exact card_image_le.trans (by simp)
    · simp
  · intro x y hxy
    have hj : formulaIndex x = formulaIndex y := by
      have : (fun i => x (indexPos I Δ k lam i)) = fun i => y (indexPos I Δ k lam i) :=
        funext fun i => hxy _ (mem_union_left _ (mem_image_of_mem _ (mem_univ i)))
      simp only [formulaIndex, this]
    simp only [addr, Equiv.symm_apply_apply]
    rw [hj]
    unfold addrBit
    split_ifs with h
    · exact hxy _ (mem_union_right _ (by
        rw [dite_eq_left h.2.2]
        exact mem_image_of_mem _ (mem_univ _)))
    · rfl

/-- The output reads the formula index, the masks and the table values. -/
private theorem complexity_combine_le (τ : ℕ → ℕ) :
    complexity interpretation (combine I lam (Δ := Δ) (k := k) τ) ≤
      1 * (2 ^ (indexWidth I + (Δ * Δ + Δ * k)) *
        (2 * (indexWidth I + (Δ * Δ + Δ * k)) + 3) + 1) := by
  refine complexity_le_mul_of_forall_dependsOn _ fun _ => ?_
  refine ⟨(univ.image fun i => Fin.castAdd (Δ * k) (indexPos I Δ k lam i)) ∪
    (univ.image fun tq : Fin Δ × Fin Δ => Fin.castAdd (Δ * k) (maskPos I Δ k lam tq.1 tq.2)) ∪
    univ.image (Fin.natAdd (inputLength I Δ k lam)), ?_, ?_⟩
  · refine ((card_union_le _ _).trans (add_le_add ((card_union_le _ _).trans
      (add_le_add card_image_le card_image_le)) card_image_le)).trans ?_
    simp only [card_univ, Fintype.card_fin, Fintype.card_prod]
    omega
  · intro x y hxy
    have hj : formulaIndex (I := I) (Δ := Δ) (k := k) (lam := lam)
        (fun i => x (Fin.castAdd _ i)) = formulaIndex fun i => y (Fin.castAdd _ i) := by
      have : (fun i => x (Fin.castAdd (Δ * k) (indexPos I Δ k lam i))) =
          fun i => y (Fin.castAdd (Δ * k) (indexPos I Δ k lam i)) :=
        funext fun i => hxy _ (mem_union_left _ (mem_union_left _
          (mem_image_of_mem _ (mem_univ i))))
      simp only [formulaIndex, this]
    have hm : (fun t q => x (Fin.castAdd (Δ * k) (maskPos I Δ k lam t q))) =
        fun t q => y (Fin.castAdd (Δ * k) (maskPos I Δ k lam t q)) :=
      funext fun t => funext fun q => hxy _ (mem_union_left _ (mem_union_right _
        (Finset.mem_image.2 ⟨(t, q), mem_univ _, rfl⟩)))
    have hv : (fun p => x (Fin.natAdd (inputLength I Δ k lam) p)) =
        fun p => y (Fin.natAdd (inputLength I Δ k lam) p) :=
      funext fun p => hxy _ (mem_union_right _ (mem_image_of_mem _ (mem_univ p)))
    simp only [combine]
    rw [hj, hm, hv]

/-- A junta on `a + e` inputs, with `2 ^ a ≤ 2 (m + 1)` and `a ≤ L`, costs `O((m + 1) (L + 1))`. -/
private theorem junta_le {a L m : ℕ} (e : ℕ) (ha : 2 ^ a ≤ 2 * (m + 1)) (haL : a ≤ L) :
    2 ^ (a + e) * (2 * (a + e) + 3) + 1 ≤ (m + 1) * (L + 1) * (2 ^ (e + 1) * (2 * e + 4)) := by
  have hlin : 2 * (a + e) + 3 + 1 ≤ (L + 1) * (2 * e + 4) := by nlinarith
  have hpos : 1 ≤ 2 ^ (a + e) := Nat.one_le_two_pow
  calc 2 ^ (a + e) * (2 * (a + e) + 3) + 1 ≤ 2 ^ (a + e) * (2 * (a + e) + 3 + 1) := by nlinarith
    _ ≤ 2 ^ a * 2 ^ e * ((L + 1) * (2 * e + 4)) := by rw [pow_add]; gcongr
    _ ≤ 2 * (m + 1) * 2 ^ e * ((L + 1) * (2 * e + 4)) := by gcongr
    _ = (m + 1) * (L + 1) * (2 ^ (e + 1) * (2 * e + 4)) := by ring

/-! ### Yes completeness -/

/-- **Yes completeness of the CMMSA table.** For every `Δ`, `k` and precision `P > 0` there is a
constant `λ₀` such that every Yes instance `I` of `GapCMMSA Δ g σ` maps into partial MCSP for every
choice of the functions `f`, once `λ ≥ λ₀ (m + 1) ²`, where `m` is the number of formulas.

`λ₀` is existential and not computed: it comes from the eventual bounds of Uhlig's theorem
(`MassProduction.eventually_mul_complexity_table_le`) and of `16 (P K) ² L ⁶ ≤ 2 ^ L`. A reduction
fixes it and takes `λ = λ₀ (|I| + 1) ²` for the input length `|I|`, which is at least `m`. The gap
`g` and the proportion `σ` play no part on the Yes side. -/
theorem exists_toInstance_mem_PartialMCSP (Δ k P : ℕ) (hP : 0 < P) :
    ∃ lam₀ : ℕ, ∀ (g σ : ℝ) (I : CMMSAInstance), I ∈ (GapCMMSA Δ g σ).yes →
      ∀ lam, lam₀ * (I.formulas.length + 1) ^ 2 ≤ lam →
        ∀ f : VarFunctions I lam, toInstance I Δ k lam P f ∈ PartialMCSP := by
  obtain ⟨K, hK⟩ : ∃ K, K = 2 ^ (Δ + 1) * (2 * Δ + 4) * (Δ * k) +
      2 ^ (Δ * Δ + Δ * k + 1) * (2 * (Δ * Δ + Δ * k) + 4) := ⟨_, rfl⟩
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.1 ((eventually_mul_complexity_table_le P (Δ * k)).and
    ((Nat.eventually_mul_pow_le_pow (16 * (P * K) ^ 2) 6 Nat.one_lt_two).and
      (eventually_ge_atTop 1)))
  refine ⟨2 ^ L₀, fun g σ I hI lam hlam f => ?_⟩
  obtain ⟨hwf, S, hS, hw, hsat⟩ := mem_yes_GapCMMSA.1 hI
  have hlam1 : 1 ≤ lam := le_trans (Nat.one_le_iff_ne_zero.2 (by positivity)) hlam
  set m := I.formulas.length with hm
  set L := tableLength I lam with hL
  set a := indexWidth I with ha_def
  have h2L : 2 ^ L₀ * (m + 1) ^ 2 ≤ 2 ^ L :=
    calc 2 ^ L₀ * (m + 1) ^ 2 ≤ lam := hlam
      _ ≤ 2 * I.threshold * lam :=
          Nat.le_mul_of_pos_left lam (by have := hwf.threshold_pos; omega)
      _ ≤ 2 ^ L := Nat.le_pow_clog Nat.one_lt_two _
  have hm2 : (m + 1) ^ 2 ≤ 2 ^ L := le_trans (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)) h2L
  have hLL₀ : L₀ ≤ L :=
    (Nat.pow_le_pow_iff_right Nat.one_lt_two).1
      (le_trans (Nat.le_mul_of_pos_right _ (by positivity)) h2L)
  obtain ⟨hUhlig, hpoly, hL1⟩ := hL₀ L hLL₀
  have haL : a ≤ L := Nat.clog_le_of_le_pow (le_trans (by nlinarith) hm2)
  have ha : 2 ^ a ≤ 2 * (m + 1) := Nat.two_pow_clog_two_le m
  obtain ⟨o, hfit, hdisj⟩ := Nat.exists_aligned_packing 2 (varLength I lam) S
  have hsum := sum_two_pow_varLength_le hS hwf hw hlam1
  have hfit' : ∀ v ∈ S, 2 ^ varLength I lam v ∣ o v ∧ o v + 2 ^ varLength I lam v ≤ 2 ^ L :=
    fun v hv => ⟨(hfit v hv).1, (hfit v hv).2.trans hsum⟩
  obtain ⟨τ, hτ⟩ := exists_satTerm hwf.monotone hsat
  let F := hardTable f S o L
  let C : BooleanFunction (inputLength I Δ k lam) := fun x =>
    combine I lam τ (Fin.append x (directProduct F (Δ * k) (addr L τ o x))) 0
  refine mem_iff_exists_total_extension.2 ⟨C, fun y b hy => ?_, ?_⟩
  · have hy' : entry f y = some b := by
      have h : entry f ((BitString.equivFin _).symm (BitString.equivFin _ y)) = some b := hy
      convert h using 2
      exact congrArg (entry f)
        ((BitString.equivFin (inputLength I Δ k lam)).symm_apply_apply y).symm
    exact combine_append_eq hS hwf hτ hfit' hdisj hy'
  · have hC : single C =
        fun x => combine I lam τ (Fin.append x (directProduct F (Δ * k) (addr L τ o x))) := rfl
    have hU := hUhlig F (addr (I := I) (Δ := Δ) (k := k) (lam := lam) L τ o) (combine I lam τ)
    have h1 := (complexity_addr_le (I := I) (Δ := Δ) (k := k) (lam := lam) L τ o).trans
      (Nat.mul_le_mul_left _ (junta_le Δ ha haL))
    have h2 := (complexity_combine_le (I := I) (Δ := Δ) (k := k) (lam := lam) τ).trans
      (by simpa using junta_le (Δ * Δ + Δ * k) ha haL)
    have hover : complexity interpretation (addr (I := I) (Δ := Δ) (k := k) (lam := lam) L τ o) +
        complexity interpretation (combine I lam (Δ := Δ) (k := k) τ) ≤
          (m + 1) * (L + 1) ^ 2 * K :=
      calc _ ≤ _ := Nat.add_le_add h1 h2
        _ ≤ Δ * k * (L + 1) * ((m + 1) * (L + 1) * (2 ^ (Δ + 1) * (2 * Δ + 4))) +
            (m + 1) * (L + 1) * (2 ^ (Δ * Δ + Δ * k + 1) * (2 * (Δ * Δ + Δ * k) + 4)) * (L + 1) :=
          Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.le_succ L)))
            (Nat.le_mul_of_pos_right _ (Nat.succ_pos L))
        _ = (m + 1) * (L + 1) ^ 2 * K := by rw [hK]; ring
    obtain ⟨X, hX⟩ : ∃ X, X = P * K * L * (L + 1) ^ 2 := ⟨_, rfl⟩
    have hX2 : X ^ 2 ≤ 2 ^ L := by
      have h : (L + 1) ^ 2 ≤ 4 * L ^ 2 := by nlinarith
      calc X ^ 2 = (P * K) ^ 2 * L ^ 2 * ((L + 1) ^ 2) ^ 2 := by rw [hX]; ring
        _ ≤ (P * K) ^ 2 * L ^ 2 * (4 * L ^ 2) ^ 2 := by gcongr
        _ = 16 * (P * K) ^ 2 * L ^ 6 := by ring
        _ ≤ 2 ^ L := hpoly
    have hmX : (m + 1) * X ≤ 2 ^ L := by
      have : ((m + 1) * X) ^ 2 ≤ (2 ^ L) ^ 2 := by
        rw [mul_pow, sq (2 ^ L)]
        exact Nat.mul_le_mul hm2 hX2
      exact (Nat.pow_le_pow_iff_left two_ne_zero).1 this
    have hfinal : complexity interpretation (single C) * (P * L) ≤ (P + 2) * 2 ^ L := by
      rw [hC, Nat.mul_comm]
      calc _ ≤ (P + 1) * 2 ^ L + P * L *
            (complexity interpretation (addr (I := I) (Δ := Δ) (k := k) (lam := lam) L τ o) +
              complexity interpretation (combine I lam (Δ := Δ) (k := k) τ)) := hU
        _ ≤ (P + 1) * 2 ^ L + P * L * ((m + 1) * (L + 1) ^ 2 * K) := by gcongr
        _ = (P + 1) * 2 ^ L + (m + 1) * X := by rw [hX]; ring
        _ ≤ (P + 1) * 2 ^ L + 2 ^ L := by gcongr
        _ = (P + 2) * 2 ^ L := by ring
    exact (Nat.le_div_iff_mul_le (Nat.mul_pos hP hL1)).2 hfinal

end Cslib.PartialMCSP.FromCMMSA
