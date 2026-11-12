/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Agreement
public import CslibFrontier.Computability.Circuit.Boolean.Spira
import CslibFrontier.Computability.Circuit.Formula.RestrictionCount
public import CslibFrontier.Computability.Circuit.Boolean.Formula.Restriction
import CslibFrontier.Foundations.Combinatorics.HalvingCover
import Mathlib.Tactic

/-!
# Agreement on two instances

[ChukhinKulikovMihajlinSmal2026], Theorem 1.5 (printed pp. 2, 8–9; PDF pp. 3, 9–10): for a
partial function `f` on `n` bits with `|f⁻¹(0)|, |f⁻¹(1)| ≥ 2`,
`D(f) ≤ D(Agr₂(f)) + ⌈log₂ n⌉ + 1` and `L(f) ≤ 2 n L(Agr₂(f))`. These are
`partialFormulaDepth_le_agreement_two` and `partialFormulaSize_le_agreement_two`. Both follow
from one construction: `exists_computesPartial_of_agreement_two` turns a formula `H` for
`Agr₂(f)` with depth `d` and `ℓ` leaves into a formula for `f` with depth at most
`d + ⌈log₂ n⌉ + 1` and at most `2 n ℓ` leaves.

The proof follows the source, which adapts [BeimelBenDanielKushilevitzWeinreb2010], Theorem 4.
If `H` reads only one of its two input blocks, fixing the other block computes `f`. Otherwise
consider the matrix of `H` on `f⁻¹(0) × f⁻¹(1)`. If `H` has `a` leaves in the first block, it has
at most `2 ^ a` distinct rows (`Formula.card_image_eval_piecewise_le`), and similarly for columns.
The halving cover (`Finset.exists_cover_zero_or_one`), applied to one representative of each
distinct row and column, gives one of two things:
* `t ≤ min {n, ℓ}` inputs `v_j ∈ f⁻¹(1)` such that every `x ∈ f⁻¹(0)` has `H(x, v_j) = 0` for
  some `j`; then `⋀_j (H(x, v_j) ∨ EQ_{v_j}(x))` computes `f`;
* or the dual, with `u_j ∈ f⁻¹(0)` and `⋁_j (H(u_j, x) ∧ ¬EQ_{u_j}(x))`.

Each term has depth `max {d, ⌈log₂ n⌉} + 1`. The balanced tree over the terms adds
`⌈log₂ t⌉ ≤ min {d, ⌈log₂ n⌉}`, because `t ≤ ℓ ≤ 2 ^ d`.

`partialFormulaSize` is the source's `L(f)` for partial functions; on total functions it is
`formulaSize` (`partialFormulaSize_some`).

## Main definitions

* `Cslib.Circuits.Boolean.partialFormulaSize`: the least leaf size of a formula computing a
  partial function.

## Main results

* `Cslib.Circuits.Boolean.exists_computesPartial_of_agreement_two`: the construction.
* `Cslib.Circuits.Boolean.partialFormulaDepth_le_agreement_two`: Theorem 1.5, depth.
* `Cslib.Circuits.Boolean.partialFormulaSize_le_agreement_two`: Theorem 1.5, size.

## References

* [N. Chukhin, A. S. Kulikov, I. Mihajlin and A. V. Smal, *Solving One of Many Instances is
  Almost as Hard as Solving One*][ChukhinKulikovMihajlinSmal2026]
* [A. Beimel, S. Ben Daniel, E. Kushilevitz and E. Weinreb, *Choosing, Agreeing, and Eliminating
  in Communication Complexity*][BeimelBenDanielKushilevitzWeinreb2010]
-/

public section

namespace Cslib.Circuits

namespace Boolean

open Cslib.BitString Formula

variable {n : ℕ} {f : BitString n → Option Bool}

/-- The input of a formula on two blocks of `n` bits with `x` in block `i` and `w` in the other. -/
private def place (i : Fin 2) (x w : BitString n) : BitString (2 * n) :=
  blocksEquiv.symm fun j => if j = i then x else w

private theorem block_place (i : Fin 2) (x w : BitString n) (j : Fin 2) :
    block (place i x w) j = if j = i then x else w := by
  simp [place]

private theorem place_swap (x y : BitString n) : place 1 y x = place 0 x y := by
  unfold place
  congr 1
  funext j
  fin_cases j <;> rfl

/-- A formula for `Agr₂(f)` is `b` on two distinct inputs where `f` is `b`. -/
private theorem eval_place {H : Formula signature (2 * n)}
    (hH : H.ComputesPartial (agreement 2 f)) (i : Fin 2) {x w : BitString n} {b : Bool}
    (hxw : x ≠ w) (hx : f x = some b) (hw : f w = some b) :
    H.eval interpretation (place i x w) = b := by
  refine hH _ _ (agreement_eq_some_iff.2 ⟨fun j j' h => ?_, fun j => ?_⟩)
  · simp only [block_place] at h
    by_cases hj : j = i <;> by_cases hj' : j' = i <;> simp only [hj, hj', ite_true, ite_false] at h
    · exact hj.trans hj'.symm
    · exact absurd h hxw
    · exact absurd h.symm hxw
    · fin_cases i <;> fin_cases j <;> fin_cases j' <;> simp_all
  · rw [block_place]
    split_ifs <;> assumption

/-- `H` reading block `i` from its input, with the other block fixed to `w`. -/
private def restrict (H : Formula signature (2 * n)) (i : Fin 2) (w : BitString n) :
    Formula signature n :=
  H.bind fun p => if (finProdFinEquiv.symm p).1 = i then .input (finProdFinEquiv.symm p).2
    else .const (w (finProdFinEquiv.symm p).2)

private theorem eval_restrict (H : Formula signature (2 * n)) (i : Fin 2) (w x : BitString n) :
    (restrict H i w).eval interpretation x = H.eval interpretation (place i x w) := by
  rw [restrict, eval_bind]
  congr 1
  funext p
  simp only [place, blocksEquiv_symm_apply]
  split_ifs <;> simp

private theorem depthWith_restrict_le (H : Formula signature (2 * n)) (i : Fin 2)
    (w : BitString n) : (restrict H i w).depthWith binaryCost ≤ H.depthWith binaryCost := by
  rw [restrict]
  simpa using depthWith_bind_le (c := 0) (fun p => by split_ifs <;> simp) H

private theorem leafSize_restrict_le (H : Formula signature (2 * n)) (i : Fin 2)
    (w : BitString n) : (restrict H i w).leafSize ≤ H.leafSize :=
  leafSize_bind_le (fun p => by split_ifs <;> simp) H

/-- The formula testing equality with `w`: a balanced conjunction of `n` literals. -/
private def eqFormula (w : BitString n) : Formula signature n :=
  andList ((List.finRange n).map (literal w))

private theorem eval_eqFormula (w x : BitString n) :
    (eqFormula w).eval interpretation x = decide (x = w) := by
  rw [Bool.eq_iff_iff]
  simp [eqFormula, Function.comp_def, List.all_eq_true, funext_iff]

private theorem depthWith_eqFormula_le (w : BitString n) :
    (eqFormula w).depthWith binaryCost ≤ Nat.clog 2 n := by
  simpa [eqFormula] using depthWith_binaryCost_andList_le (d := 0)
    (l := (List.finRange n).map (literal w)) (by simp)

private theorem leafSize_eqFormula_le (w : BitString n) : (eqFormula w).leafSize ≤ n := by
  refine (leafSize_andList_le _).trans ?_
  simp [List.map_map, Function.comp_def]

/-- `F`, negated when `c` is `true`. -/
private def negIf (c : Bool) (F : Formula signature n) : Formula signature n :=
  if c then F.not else F

private theorem eval_negIf (c : Bool) (F : Formula signature n) (x : BitString n) :
    (negIf c F).eval interpretation x = (c ^^ F.eval interpretation x) := by
  cases c <;> simp [negIf]

private theorem depthWith_negIf (c : Bool) (F : Formula signature n) :
    (negIf c F).depthWith binaryCost = F.depthWith binaryCost := by
  cases c <;> simp [negIf]

private theorem leafSize_negIf (c : Bool) (F : Formula signature n) :
    (negIf c F).leafSize = F.leafSize := by
  cases c <;> simp [negIf]

/-- The formula of the covering argument for inputs `ws` where `f` is `b`, reading block `i`.
For `b = true` it is `⋀_w (H(x, w) ∨ EQ_w(x))`; for `b = false` it is the dual
`⋁_w (H(w, x) ∧ ¬EQ_w(x))`, written with negations. -/
private def coverFormula (H : Formula signature (2 * n)) (i : Fin 2) (b : Bool)
    (ws : List (BitString n)) : Formula signature n :=
  negIf (!b) (andList (ws.map fun w => (negIf (!b) (restrict H i w)).or (eqFormula w)))

/-- **The covering formula computes `f`** ([ChukhinKulikovMihajlinSmal2026], proof of
Theorem 1.5): if `f` is `b` on every `w ∈ ws`, and every input where `f` is `!b` has some
`w ∈ ws` where `H` is `!b`, then on inputs where `f` is `b` every term holds by agreement or
equality, and on inputs where `f` is `!b` the covering term fails. -/
private theorem computesPartial_coverFormula {H : Formula signature (2 * n)}
    (hH : H.ComputesPartial (agreement 2 f)) (i : Fin 2) {b : Bool} {ws : List (BitString n)}
    (hws : ∀ w ∈ ws, f w = some b)
    (hcov : ∀ x, f x = some (!b) → ∃ w ∈ ws, H.eval interpretation (place i x w) = !b) :
    (coverFormula H i b ws).ComputesPartial f := by
  intro x c hx
  simp only [coverFormula, eval_negIf, eval_andList, List.all_map, Function.comp_def, eval_or,
    eval_restrict, eval_eqFormula]
  by_cases hc : c = b
  · subst hc
    have hall : (ws.all fun w => ((!c ^^ H.eval interpretation (place i x w)) ||
        decide (x = w))) = true := by
      refine List.all_eq_true.2 fun w hw => ?_
      by_cases hxw : x = w
      · simp [hxw]
      · rw [eval_place hH i hxw hx (hws w hw)]
        cases c <;> simp
    rw [hall]
    cases c <;> rfl
  · have hc' : c = !b := by cases b <;> cases c <;> simp_all
    subst hc'
    obtain ⟨w, hw, hHw⟩ := hcov x hx
    have hxw : x ≠ w := fun h => by
      have := hws w hw
      rw [← h, hx] at this
      cases b <;> simp at this
    have hall : (ws.all fun w => ((!b ^^ H.eval interpretation (place i x w)) ||
        decide (x = w))) = false := by
      refine List.all_eq_false.2 ⟨w, hw, ?_⟩
      rw [hHw]
      cases b <;> simp [hxw]
    rw [hall]
    cases b <;> rfl

private theorem depthWith_coverFormula_le (H : Formula signature (2 * n)) (i : Fin 2) (b : Bool)
    (ws : List (BitString n)) :
    (coverFormula H i b ws).depthWith binaryCost ≤
      max (H.depthWith binaryCost) (Nat.clog 2 n) + 1 + Nat.clog 2 ws.length := by
  rw [coverFormula, depthWith_negIf]
  simpa using depthWith_binaryCost_andList_le (d := max (H.depthWith binaryCost) (Nat.clog 2 n) + 1)
    (l := ws.map fun w => (negIf (!b) (restrict H i w)).or (eqFormula w)) (by
      simp only [List.mem_map]
      rintro _ ⟨w, -, rfl⟩
      simp only [depthWith_or, depthWith_negIf, binaryCost_or]
      have := depthWith_restrict_le H i w
      have := depthWith_eqFormula_le w
      omega)

private theorem leafSize_coverFormula_le (H : Formula signature (2 * n)) (i : Fin 2) (b : Bool)
    (ws : List (BitString n)) :
    (coverFormula H i b ws).leafSize ≤ ws.length * (H.leafSize + n) := by
  rw [coverFormula, leafSize_negIf]
  refine (leafSize_andList_le _).trans ?_
  refine (List.sum_le_length_nsmul _ (H.leafSize + n) fun L hL => ?_).trans (by simp)
  simp only [List.map_map, List.mem_map, Function.comp_apply] at hL
  obtain ⟨w, -, rfl⟩ := hL
  simp only [leafSize_or, leafSize_negIf]
  have := leafSize_restrict_le H i w
  have := leafSize_eqFormula_le w
  omega

/-- If `H` reads no bit of block `j ≠ i`, then `H` with block `j` fixed computes `f` on block
`i`: for each input some distinct input with the same value of `f` exists, and `H` cannot see the
difference. -/
private theorem computesPartial_restrict_of_leafSizeIn_eq_zero {H : Formula signature (2 * n)}
    (hH : H.ComputesPartial (agreement 2 f))
    (hcard : ∀ b, 2 ≤ Fintype.card {x // f x = some b}) {i j : Fin 2} (hij : j ≠ i)
    (h0 : H.leafSizeIn (blockBits n j) = 0) (w₀ : BitString n) :
    (restrict H i w₀).ComputesPartial f := by
  intro x b hx
  obtain ⟨⟨w, hw⟩, hne⟩ := Fintype.exists_ne_of_one_lt_card (hcard b) ⟨x, hx⟩
  have hxw : x ≠ w := fun h => hne (Subtype.ext h.symm)
  rw [eval_restrict, ← eval_place hH i hxw hx hw]
  refine dependsOn_eval_of_leafSizeIn_eq_zero h0 interpretation fun p hp => ?_
  have hpj : (finProdFinEquiv.symm p).1 ≠ j := by simpa [mem_blockBits] using hp
  have hpi : (finProdFinEquiv.symm p).1 = i := by
    fin_cases i <;> fin_cases j <;> simp_all <;> omega
  have hpi' : p.divNat = i := by simpa using hpi
  simp [place, blocksEquiv_symm_apply, hpi']

/-- The row of `x` in block `i`: the values of `H` with `x` in block `i`, as a function of the
other block. -/
private def key (H : Formula signature (2 * n)) (i : Fin 2) (x : BitString n) :
    BitString n → Bool :=
  fun w => H.eval interpretation (place i x w)

open Classical in
/-- `H` has at most `2 ^ a` distinct rows in block `i`, for `a` its leaves in that block. -/
private theorem card_image_key_le (H : Formula signature (2 * n)) (i : Fin 2)
    (S : Finset (BitString n)) : (S.image (key H i)).card ≤ 2 ^ H.leafSizeIn (blockBits n i) := by
  set U := blockBits n i
  have hsplit (x w : BitString n) :
      place i x w = U.piecewise (place i x fun _ => false) (place i (fun _ => false) w) := by
    apply blocksEquiv.injective
    funext j
    simp only [blocksEquiv_apply, block_piecewise, block_place, U]
    split_ifs <;> rfl
  refine le_trans (Finset.card_le_card (t := (Finset.univ.image fun z : BitString (2 * n) =>
      fun z' => H.eval interpretation (U.piecewise z z')).image
        fun g w => g (place i (fun _ => false) w)) fun g hg => ?_)
    (Finset.card_image_le.trans (card_image_eval_piecewise_le interpretation U H))
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hg
  refine Finset.mem_image.2 ⟨_, Finset.mem_image.2 ⟨place i x fun _ => false,
    Finset.mem_univ _, rfl⟩, ?_⟩
  funext w
  simp only [key, hsplit x w]

open Classical in
/-- One representative in `S` of each distinct value of `k` on `S`. -/
private noncomputable def reps (S : Finset (BitString n)) (k : BitString n → BitString n → Bool) :
    Finset (BitString n) :=
  (S.image k).image (Function.invFunOn k S)

private theorem reps_subset (S : Finset (BitString n)) (k : BitString n → BitString n → Bool) :
    reps S k ⊆ S := by
  classical
  intro r hr
  obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hr
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hg
  exact (Function.invFunOn_pos ⟨x, hx, rfl⟩).1

private theorem exists_mem_reps (S : Finset (BitString n)) (k : BitString n → BitString n → Bool)
    {x : BitString n} (hx : x ∈ S) : ∃ r ∈ reps S k, k r = k x := by
  classical
  exact ⟨_, Finset.mem_image.2 ⟨k x, Finset.mem_image_of_mem k hx, rfl⟩,
    (Function.invFunOn_pos ⟨x, hx, rfl⟩).2⟩

open Classical in
private theorem card_reps_le (S : Finset (BitString n)) (k : BitString n → BitString n → Bool) :
    (reps S k).card ≤ (S.image k).card :=
  Finset.card_image_le

/-- The final accounting: `t ≤ min {n, ℓ}` covering terms over a formula of depth `d` with
`ℓ ≤ 2 ^ d` leaves give depth `d + ⌈log₂ n⌉ + 1` and at most `2 n ℓ` leaves. -/
private theorem bounds_of_le {d ℓ t : ℕ} (hℓ : ℓ ≤ 2 ^ d) (htn : t ≤ n) (htℓ : t ≤ ℓ) :
    max d (Nat.clog 2 n) + 1 + Nat.clog 2 t ≤ d + Nat.clog 2 n + 1 ∧
      t * (ℓ + n) ≤ 2 * n * ℓ := by
  have h1 : Nat.clog 2 t ≤ Nat.clog 2 n := Nat.clog_mono_right 2 htn
  have h2 : Nat.clog 2 t ≤ d := Nat.clog_le_of_le_pow (htℓ.trans hℓ)
  refine ⟨by omega, ?_⟩
  nlinarith [Nat.mul_le_mul htn (le_refl ℓ), Nat.mul_le_mul htℓ (le_refl n)]

/-- `f⁻¹(b)` as a finset. -/
private theorem card_filter_eq (b : Bool) :
    (Finset.univ.filter fun x => f x = some b).card = Fintype.card {x // f x = some b} :=
  (Fintype.card_subtype _).symm

open Classical in
/-- **[ChukhinKulikovMihajlinSmal2026], Theorem 1.5, for one formula.** Let `f` be a partial
function on `n` bits with `|f⁻¹(0)|, |f⁻¹(1)| ≥ 2`, and let `H` compute `Agr₂(f)`, with
`binaryCost` depth `d` and `ℓ` leaves. Then some formula computing `f` has depth at most
`d + ⌈log₂ n⌉ + 1` and at most `2 n ℓ` leaves. -/
theorem exists_computesPartial_of_agreement_two
    (hT : 2 ≤ Fintype.card {x // f x = some true}) (hF : 2 ≤ Fintype.card {x // f x = some false})
    {H : Formula signature (2 * n)} (hH : H.ComputesPartial (agreement 2 f)) :
    ∃ G : Formula signature n, G.ComputesPartial f ∧
      G.depthWith binaryCost ≤ H.depthWith binaryCost + Nat.clog 2 n + 1 ∧
      G.leafSize ≤ 2 * n * H.leafSize := by
  have hcard (b : Bool) : 2 ≤ Fintype.card {x // f x = some b} := by cases b <;> assumption
  set d := H.depthWith binaryCost
  set ℓ := H.leafSize
  set a := H.leafSizeIn (blockBits n 0)
  set a' := H.leafSizeIn (blockBits n 1)
  have hsum : a + a' ≤ ℓ := by
    have := H.sum_leafSizeIn_le_leafSize (s := Finset.univ) (pairwiseDisjoint_blockBits n)
    simpa [Fin.sum_univ_two] using this
  have hℓ : ℓ ≤ 2 ^ d := leafSize_le_two_pow_depthWith_binaryCost H
  have hpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · have := (Fintype.card_subtype_le (fun x : BitString 0 => f x = some true)).trans_lt'
        (hcard true)
      simp at this
    · exact h
  -- If `H` reads only one block, fixing the other block computes `f`.
  have hdeg (i j : Fin 2) (hij : j ≠ i) (h0 : H.leafSizeIn (blockBits n j) = 0) :
      ∃ G : Formula signature n, G.ComputesPartial f ∧ G.depthWith binaryCost ≤ d +
        Nat.clog 2 n + 1 ∧ G.leafSize ≤ 2 * n * ℓ :=
    ⟨restrict H i fun _ => false,
      computesPartial_restrict_of_leafSizeIn_eq_zero hH hcard hij h0 _,
      (depthWith_restrict_le H i _).trans (by omega),
      (leafSize_restrict_le H i _).trans (by nlinarith)⟩
  rcases Nat.eq_zero_or_pos a with ha | ha
  · exact hdeg 1 0 (by decide) ha
  rcases Nat.eq_zero_or_pos a' with ha' | ha'
  · exact hdeg 0 1 (by decide) ha'
  -- The rows and columns of `H` on `f⁻¹(0) × f⁻¹(1)`, one representative for each distinct one.
  set F0 := Finset.univ.filter fun x => f x = some false
  set F1 := Finset.univ.filter fun x => f x = some true
  have hdisj : Disjoint F0 F1 := Finset.disjoint_filter.2 fun x _ h0 h1 => by
    rw [h0] at h1
    cases h1
  have hunion : F0.card + F1.card ≤ 2 ^ n := by
    rw [← Finset.card_union_of_disjoint hdisj]
    simpa using Finset.card_le_univ (F0 ∪ F1)
  have hF0 : F0.card = Fintype.card {x // f x = some false} := card_filter_eq false
  have hF1 : F1.card = Fintype.card {x // f x = some true} := card_filter_eq true
  set R := reps F0 (key H 0)
  set C := reps F1 (key H 1)
  have hR : R.card ≤ 2 ^ a ∧ R.card + 1 ≤ 2 ^ n := by
    have h1 : R.card ≤ (F0.image (key H 0)).card := card_reps_le _ _
    have h2 : (F0.image (key H 0)).card ≤ 2 ^ a := card_image_key_le H 0 F0
    have h3 : R.card ≤ F0.card := Finset.card_le_card (reps_subset _ _)
    exact ⟨h1.trans h2, by have := hcard true; omega⟩
  have hC : C.card ≤ 2 ^ a' ∧ C.card + 1 ≤ 2 ^ n := by
    have h1 : C.card ≤ (F1.image (key H 1)).card := card_reps_le _ _
    have h2 : (F1.image (key H 1)).card ≤ 2 ^ a' := card_image_key_le H 1 F1
    have h3 : C.card ≤ F1.card := Finset.card_le_card (reps_subset _ _)
    exact ⟨h1.trans h2, by have := hcard false; omega⟩
  -- `⌈log₂ (r + 1)⌉ ≤ min {n, ℓ}` when there are at most `2 ^ e` rows and `e < ℓ`.
  have hclog {r e : ℕ} (hr : r ≤ 2 ^ e ∧ r + 1 ≤ 2 ^ n) (he : e + 1 ≤ ℓ) :
      Nat.clog 2 (r + 1) ≤ n ∧ Nat.clog 2 (r + 1) ≤ ℓ := by
    refine ⟨Nat.clog_le_of_le_pow hr.2, (Nat.clog_le_of_le_pow ?_).trans he⟩
    rw [pow_succ]
    have := Nat.one_le_two_pow (n := e)
    omega
  rcases Finset.exists_cover_zero_or_one (fun x y => H.eval interpretation (place 0 x y)) R C with
    ⟨cs, hcs, hlen, hcov⟩ | ⟨rs, hrs, hlen, hcov⟩
  · -- Some columns `v₁, …, v_t ∈ f⁻¹(1)` cover `f⁻¹(0)` with zeros.
    have hb := hclog hR (by omega)
    obtain ⟨hd, hl⟩ := bounds_of_le hℓ (hlen.trans hb.1) (hlen.trans hb.2)
    refine ⟨coverFormula H 0 true cs, computesPartial_coverFormula hH 0
      (fun w hw => (Finset.mem_filter.1 (reps_subset _ _ (hcs w hw))).2) fun x hx => ?_,
      (depthWith_coverFormula_le H 0 true cs).trans hd,
      (leafSize_coverFormula_le H 0 true cs).trans hl⟩
    obtain ⟨r, hr, hkey⟩ := exists_mem_reps F0 (key H 0) (Finset.mem_filter.2 ⟨Finset.mem_univ _,
      hx⟩)
    obtain ⟨c, hc, hrc⟩ := hcov r hr
    exact ⟨c, hc, by simpa [key, hrc] using (congrFun hkey c).symm⟩
  · -- Some rows `u₁, …, u_t ∈ f⁻¹(0)` cover `f⁻¹(1)` with ones.
    have hb := hclog hC (by omega)
    obtain ⟨hd, hl⟩ := bounds_of_le hℓ (hlen.trans hb.1) (hlen.trans hb.2)
    refine ⟨coverFormula H 1 false rs, computesPartial_coverFormula hH 1
      (fun w hw => (Finset.mem_filter.1 (reps_subset _ _ (hrs w hw))).2) fun y hy => ?_,
      (depthWith_coverFormula_le H 1 false rs).trans hd,
      (leafSize_coverFormula_le H 1 false rs).trans hl⟩
    obtain ⟨c, hc, hkey⟩ := exists_mem_reps F1 (key H 1) (Finset.mem_filter.2 ⟨Finset.mem_univ _,
      hy⟩)
    obtain ⟨r, hr, hrc⟩ := hcov c hc
    refine ⟨r, hr, ?_⟩
    have := congrFun hkey r
    simp only [key, place_swap] at this
    rw [place_swap, ← this]
    exact hrc

/-- **[ChukhinKulikovMihajlinSmal2026], Theorem 1.5, depth.** If `|f⁻¹(0)|, |f⁻¹(1)| ≥ 2`,
then `D(f) ≤ D(Agr₂(f)) + ⌈log₂ n⌉ + 1`. -/
theorem partialFormulaDepth_le_agreement_two
    (hT : 2 ≤ Fintype.card {x // f x = some true}) (hF : 2 ≤ Fintype.card {x // f x = some false}) :
    partialFormulaDepth f ≤ partialFormulaDepth (agreement 2 f) + Nat.clog 2 n + 1 := by
  obtain ⟨H, hH, hd⟩ := exists_computesPartial_depthWith_eq (agreement 2 f)
  obtain ⟨G, hG, hGd, -⟩ := exists_computesPartial_of_agreement_two hT hF hH
  exact (partialFormulaDepth_le hG).trans (hd ▸ hGd)

/-- The least leaf size of a De Morgan formula computing the partial function `f`, the source's
`L(f)`. -/
noncomputable def partialFormulaSize (f : BitString n → Option Bool) : ℕ :=
  sInf {L | ∃ F : Formula signature n, F.ComputesPartial f ∧ F.leafSize = L}

/-- The partial formula size is at most the leaf size of every formula computing the function. -/
theorem partialFormulaSize_le {F : Formula signature n} (hF : F.ComputesPartial f) :
    partialFormulaSize f ≤ F.leafSize :=
  Nat.sInf_le ⟨F, hF, rfl⟩

/-- Some formula attains the partial formula size. -/
theorem exists_computesPartial_leafSize_eq (f : BitString n → Option Bool) :
    ∃ F : Formula signature n, F.ComputesPartial f ∧ F.leafSize = partialFormulaSize f :=
  Nat.sInf_mem (s := {L | ∃ F : Formula signature n, F.ComputesPartial f ∧ F.leafSize = L}) <|
    let ⟨F, hF⟩ := exists_computesPartial f
    ⟨_, F, hF, rfl⟩

/-- On a total function, the partial formula size is the formula size. -/
theorem partialFormulaSize_some (g : BooleanFunction n) :
    partialFormulaSize (fun x => some (g x)) = formulaSize g := by
  refine le_antisymm ?_ ?_
  · obtain ⟨F, hF, hL⟩ := exists_computes_leafSize_eq g
    exact (partialFormulaSize_le hF.computesPartial).trans hL.le
  · obtain ⟨F, hF, hL⟩ := exists_computesPartial_leafSize_eq fun x => some (g x)
    exact (formulaSize_le fun x => hF x _ rfl).trans hL.le

/-- **[ChukhinKulikovMihajlinSmal2026], Theorem 1.5, size.** If `|f⁻¹(0)|, |f⁻¹(1)| ≥ 2`,
then `L(f) ≤ 2 n L(Agr₂(f))`. -/
theorem partialFormulaSize_le_agreement_two
    (hT : 2 ≤ Fintype.card {x // f x = some true}) (hF : 2 ≤ Fintype.card {x // f x = some false}) :
    partialFormulaSize f ≤ 2 * n * partialFormulaSize (agreement 2 f) := by
  obtain ⟨H, hH, hL⟩ := exists_computesPartial_leafSize_eq (agreement 2 f)
  obtain ⟨G, hG, -, hGL⟩ := exists_computesPartial_of_agreement_two hT hF hH
  exact (partialFormulaSize_le hG).trans (hL ▸ hGL)

end Boolean

end Cslib.Circuits
