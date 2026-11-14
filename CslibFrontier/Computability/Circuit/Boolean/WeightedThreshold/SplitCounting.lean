/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.WeightedThreshold.SharedBottom

/-!
# Counting subcube restrictions of depth-two threshold circuits by splitting gates

Restrict a weighted threshold circuit of depth at most two to a subcube: fix all inputs outside
the image of an injective `emb : κ → Fin n` to `w`. A bottom gate **splits** the subcube if it is
not constant on it (`circuitSplitGates`; there are `circuitUnforcedConstCount` of them).

The constant bottom gates are absorbed into the top threshold, so the restricted circuit is an
upper level set of a real function on `κ → Bool` (`circuitLiveForm`) that depends only on the
splitting gates and their restricted functions (`isUpperLevelSet_eval_embedUpdate`). The top weights
are fixed; only the threshold depends on `w`. Each splitting gate is one of at most `2 ^ |κ| - 1`
nonconstant threshold shifts of its fixed live weights, and the level set is one of at most
`2 ^ |κ| + 1`. Hence restrictions with `D` splitting gates realize at most
`C(G, D) (2 ^ |κ| - 1) ^ D (2 ^ |κ| + 1)` functions, where `G` is the number of bottom gates
(`card_image_eval_embedUpdate_le`).

This is the counting step of Lemma 14 of Reitwiessner, *Depth-Two Threshold Circuits for Andreev's
Function* (2026). Unlike `isDepthTwoOverWeights_eval_embedUpdate`, which allows an arbitrary top
gate, it uses that the top weights are fixed.

## Main definitions

* `Cslib.Circuits.Boolean.WeightedThreshold.circuitSplitGates`: the bottom gates that are not
  constant on a subcube.
* `Cslib.Circuits.Boolean.WeightedThreshold.circuitLiveForm`: the top gate's linear form on the
  live coordinates, with selected bottom gates.

## Main results

* `Cslib.Circuits.Boolean.WeightedThreshold.isUpperLevelSet_eval_embedUpdate`: a restricted
  circuit is an upper level set of its live form.
* `Cslib.Circuits.Boolean.WeightedThreshold.card_image_eval_embedUpdate_le`: the count of
  restricted functions with `D` splitting gates.
* `Cslib.Circuits.Boolean.WeightedThreshold.circuitLiveForm_mixed_eq`: on two live coordinates,
  gates with zero mixed difference give a live form with zero mixed difference.
-/

public section

namespace Cslib.Circuits.Boolean.WeightedThreshold

open Finset

/-- A restriction to the image of an injective `emb` is an embedded update. -/
theorem restrictUpdate_image_eq_embedUpdate {κ ι : Type*} [Fintype κ] [DecidableEq ι]
    {emb : κ → ι} (hinj : Function.Injective emb) (w u : ι → Bool) :
    restrictUpdate (univ.image emb) w u = embedUpdate emb w fun j => u (emb j) := by
  funext i
  by_cases hi : i ∈ univ.image emb
  · obtain ⟨j, -, rfl⟩ := mem_image.mp hi
    rw [restrictUpdate_of_mem _ _ hi, embedUpdate_emb hinj]
  · rw [restrictUpdate_of_notMem _ _ hi, embedUpdate_of_notMem _ _ hi]

/-- A function is forced to a constant outside the image of an injective `emb` exactly when it is
constant along the embedded updates. -/
theorem forcedToConst_image_iff {κ ι : Type*} [Fintype κ] [DecidableEq ι] {emb : κ → ι}
    (hinj : Function.Injective emb) (f : (ι → Bool) → Bool) (w : ι → Bool) :
    ForcedToConst f (univ.image emb) w ↔ ∀ u v : κ → Bool,
      f (embedUpdate emb w u) = f (embedUpdate emb w v) := by
  constructor
  · rintro ⟨b, hb⟩ u v
    exact (hb (liftAssign emb u)).trans (hb (liftAssign emb v)).symm
  · intro h
    exact ⟨f (embedUpdate emb w fun _ => false), fun u => by
      rw [restrictUpdate_image_eq_embedUpdate hinj, h]⟩

variable {κ : Type*} [Fintype κ] {n : ℕ}

/-- The bottom gates of output `o` that are not forced to a constant outside `B` by `w`, i.e. the
bottom gates that **split** the subcube. -/
noncomputable def circuitSplitGates (c : Circuit signature n 1) (o : Fin 1) (B : Finset (Fin n))
    (w : Fin n → Bool) : Finset (Fin c.size) :=
  match c.outputs o with | .input _ => ∅ | .gate top => unforcedConstGates c.program top B w

@[simp] theorem card_circuitSplitGates (c : Circuit signature n 1) (o : Fin 1)
    (B : Finset (Fin n)) (w : Fin n → Bool) :
    #(circuitSplitGates c o B w) = circuitUnforcedConstCount c o B w := by
  unfold circuitSplitGates circuitUnforcedConstCount
  cases c.outputs o <;> rfl

theorem circuitSplitGates_subset (c : Circuit signature n 1) (o : Fin 1) (B : Finset (Fin n))
    (w : Fin n → Bool) : circuitSplitGates c o B w ⊆ outputBottomGates c o := by
  unfold circuitSplitGates
  cases h : c.outputs o
  · exact empty_subset _
  · rw [outputBottomGates_of_gate h]; exact filter_subset _ _

/-- A splitting gate is not forced to a constant. -/
theorem not_forcedToConst_of_mem_circuitSplitGates {c : Circuit signature n 1} {o : Fin 1}
    {B : Finset (Fin n)} {w : Fin n → Bool} {k : Fin c.size} (hk : k ∈ circuitSplitGates c o B w) :
    ¬ ForcedToConst (ltfEval (inputWeight c.program k) (c.program.lines k).op.threshold) B w := by
  unfold circuitSplitGates at hk
  split at hk
  exacts [absurd hk (notMem_empty k), (mem_filter.mp hk).2]

/-- The output gate's linear form on the live coordinates `emb`, keeping only the bottom gates in
`U`, whose values on `u` are `g k u`. For an output reading an input wire this is that wire's
indicator. -/
noncomputable def circuitLiveForm (c : Circuit signature n 1) (o : Fin 1) (emb : κ → Fin n)
    (U : Finset (Fin c.size)) (g : Fin c.size → (κ → Bool) → Bool) (u : κ → Bool) : ℝ :=
  match c.outputs o with
  | .input i => ∑ j, (if emb j = i then 1 else 0) * (u j).toNat
  | .gate top => (∑ k ∈ U, gateWeight c.program top k * (g k u).toNat) +
      ∑ j, inputWeight c.program top (emb j) * (u j).toNat

/-- The live form uses `g` only on `U`. -/
theorem circuitLiveForm_congr (c : Circuit signature n 1) (o : Fin 1) (emb : κ → Fin n)
    (U : Finset (Fin c.size)) {g g' : Fin c.size → (κ → Bool) → Bool}
    (h : ∀ k ∈ U, g k = g' k) : circuitLiveForm c o emb U g = circuitLiveForm c o emb U g' := by
  funext u
  unfold circuitLiveForm
  cases c.outputs o
  · rfl
  · dsimp only; rw [sum_congr rfl fun k hk => by rw [h k hk]]

/-- **Separable live forms on a square**: if every selected gate has zero mixed difference on
`Fin 2 → Bool`, so does the live form. Restricted to two live coordinates, a circuit whose
splitting gates are all constant or literals is thus an upper level set of a separable form. -/
theorem circuitLiveForm_mixed_eq (c : Circuit signature n 1) (o : Fin 1) (emb : Fin 2 → Fin n)
    (U : Finset (Fin c.size)) (g : Fin c.size → (Fin 2 → Bool) → Bool)
    (hg : ∀ k ∈ U, (g k ![false, false]).toNat + (g k ![true, true]).toNat =
      (g k ![true, false]).toNat + (g k ![false, true]).toNat) :
    circuitLiveForm c o emb U g ![false, false] + circuitLiveForm c o emb U g ![true, true] =
      circuitLiveForm c o emb U g ![true, false] + circuitLiveForm c o emb U g ![false, true] := by
  unfold circuitLiveForm
  cases c.outputs o with
  | input i =>
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Bool.toNat_false,
      Bool.toNat_true, Nat.cast_zero, Nat.cast_one]
    ring
  | gate top =>
    dsimp only
    have h : ∑ k ∈ U, (gateWeight c.program top k * (g k ![false, false]).toNat +
          gateWeight c.program top k * (g k ![true, true]).toNat) =
        ∑ k ∈ U, (gateWeight c.program top k * (g k ![true, false]).toNat +
          gateWeight c.program top k * (g k ![false, true]).toNat) :=
      sum_congr rfl fun k hk => by
        rw [← mul_add, ← mul_add]
        congr 1
        exact_mod_cast hg k hk
    rw [sum_add_distrib, sum_add_distrib] at h
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Bool.toNat_false,
      Bool.toNat_true, Nat.cast_zero, Nat.cast_one]
    linarith

/-- **Restriction to an upper level set**: restricting a weighted threshold circuit of depth at most
two outside the image of an injective `emb` to `w` gives an upper level set of its live form with
the splitting gates. The form depends on `w` only through the splitting gates and their restricted
functions; constant bottom gates are absorbed into the threshold. -/
theorem isUpperLevelSet_eval_embedUpdate (c : Circuit signature n 1) (hd : c.depth ≤ 2)
    (o : Fin 1) {emb : κ → Fin n} (hinj : Function.Injective emb) (w : Fin n → Bool) :
    IsUpperLevelSet
      (circuitLiveForm c o emb (circuitSplitGates c o (univ.image emb) w) fun k u =>
        ltfEval (inputWeight c.program k) (c.program.lines k).op.threshold (embedUpdate emb w u))
      fun u => c.eval interpretation (embedUpdate emb w u) o := by
  classical
  have hout_le : c.outputDepths o ≤ 2 := (c.outputDepths_le_depth o).trans hd
  unfold circuitLiveForm circuitSplitGates
  cases hout : c.outputs o with
  | input i₀ =>
    have hval (x : Fin n → Bool) :
        c.eval interpretation x o = ltfEval (fun i : Fin n => if i = i₀ then 1 else 0) 1 x := by
      simp only [Circuit.eval, Function.comp_apply, hout, Program.trace, Wire.elim_input, ltfEval,
        ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ↓reduceIte]
      cases x i₀ <;> simp
    refine ⟨1 - ∑ i ∈ (univ.image emb)ᶜ, (if i = i₀ then (1 : ℝ) else 0) * (w i).toNat,
      fun u => ?_⟩
    dsimp only
    rw [hval, ltfEval_embedUpdate hinj]
    rfl
  | gate top =>
    dsimp only
    have htop : c.program.depths top ≤ 2 := by simpa [Circuit.outputDepths, hout] using hout_le
    set S := gateSupport c.program top
    set U := unforcedConstGates c.program top (univ.image emb) w
    let R : Fin c.size → (κ → Bool) → Bool := fun k u =>
      ltfEval (inputWeight c.program k) (c.program.lines k).op.threshold (embedUpdate emb w u)
    have hR (k : Fin c.size) (hk : k ∈ S) (u : κ → Bool) :
        c.program.eval interpretation (embedUpdate emb w u) k = R k u :=
      eval_eq_ltfEval_inputWeight_of_depths_le_one _ _
        (by have := depths_lt_of_mem_gateSupport c.program hk; omega)
    have hconst (k : Fin c.size) : ∃ b : Bool, k ∈ S → k ∉ U → ∀ u, R k u = b := by
      by_cases hk : k ∈ S ∧ k ∉ U
      · have hf : ForcedToConst
            (ltfEval (inputWeight c.program k) (c.program.lines k).op.threshold)
            (univ.image emb) w := by
          by_contra hnf; exact hk.2 (mem_filter.mpr ⟨hk.1, hnf⟩)
        obtain ⟨b, hb⟩ := hf
        exact ⟨b, fun _ _ u => hb (liftAssign emb u)⟩
      · exact ⟨false, fun h₁ h₂ => absurd ⟨h₁, h₂⟩ hk⟩
    choose b hb using hconst
    have hUS : U ⊆ S := filter_subset _ _
    refine ⟨(c.program.lines top).op.threshold -
      (∑ i ∈ (univ.image emb)ᶜ, inputWeight c.program top i * (w i).toNat) -
      ∑ k ∈ S \ U, gateWeight c.program top k * (b k).toNat, fun u => ?_⟩
    dsimp only
    rw [Circuit.eval_of_output_eq_gate hout, eval_gate_eq, sum_mul_embedUpdate hinj]
    have hgate : (∑ k, gateWeight c.program top k *
        (c.program.eval interpretation (embedUpdate emb w u) k).toNat) =
        (∑ k ∈ U, gateWeight c.program top k * (ltfEval (inputWeight c.program k)
          (c.program.lines k).op.threshold (embedUpdate emb w u)).toNat) +
          ∑ k ∈ S \ U, gateWeight c.program top k * (b k).toNat := by
      rw [← sum_subset (subset_univ S) fun k _ hk => by
        rw [mem_gateSupport, not_not] at hk; simp [hk], ← sum_sdiff hUS, add_comm]
      congr 1
      · exact sum_congr rfl fun k hk => by rw [hR k (hUS hk)]
      · exact sum_congr rfl fun k hk => by
          rw [mem_sdiff] at hk; rw [hR k hk.1, hb k hk.1 hk.2 u]
    rw [hgate]
    exact decide_eq_decide.mpr ⟨fun h => by linarith, fun h => by linarith⟩

/-- **Counting restrictions by splitting gates**: over any set `s` of restrictions `w` with exactly
`D` splitting gates, a weighted threshold circuit of depth at most two with `G` bottom gates
realizes at most `C(G, D) (2 ^ |κ| - 1) ^ D (2 ^ |κ| + 1)` restricted functions. -/
theorem card_image_eval_embedUpdate_le [DecidableEq κ] (c : Circuit signature n 1)
    (hd : c.depth ≤ 2) (o : Fin 1) {emb : κ → Fin n} (hinj : Function.Injective emb)
    (s : Finset (Fin n → Bool)) (D : ℕ)
    (hs : ∀ w ∈ s, circuitUnforcedConstCount c o (univ.image emb) w = D) :
    #(s.image fun w u => c.eval interpretation (embedUpdate emb w u) o) ≤
      (#(outputBottomGates c o)).choose D * (2 ^ Fintype.card κ - 1) ^ D *
        (2 ^ Fintype.card κ + 1) := by
  classical
  set B := outputBottomGates c o
  let f : (Fin n → Bool) → (κ → Bool) → Bool := fun w u =>
    c.eval interpretation (embedUpdate emb w u) o
  let R : (Fin n → Bool) → Fin c.size → (κ → Bool) → Bool := fun w k u =>
    ltfEval (inputWeight c.program k) (c.program.lines k).op.threshold (embedUpdate emb w u)
  let S : (Fin n → Bool) → Finset (Fin c.size) := fun w => circuitSplitGates c o (univ.image emb) w
  let gs : (Fin n → Bool) → Fin c.size → (κ → Bool) → Bool := fun w k =>
    if k ∈ S w then R w k else fun _ => false
  let E : (Fin n → Bool) → (Finset (Fin c.size) × (Fin c.size → (κ → Bool) → Bool)) × ℕ :=
    fun w => ((S w, gs w), #{u : κ → Bool | f w u = true})
  have hlevel (w : Fin n → Bool) :
      IsUpperLevelSet (circuitLiveForm c o emb (S w) (gs w)) (f w) := by
    rw [circuitLiveForm_congr c o emb (S w) (g' := R w) fun k hk => by simp [gs, hk]]
    exact isUpperLevelSet_eval_embedUpdate c hd o hinj w
  have hfac (w w' : Fin n → Bool) (h : E w = E w') : f w = f w' := by
    simp only [E, Prod.mk.injEq] at h
    obtain ⟨⟨hS, hg⟩, hcard⟩ := h
    refine eq_of_isUpperLevelSet_of_card_eq (hlevel w) ?_ hcard
    rw [hS, hg]; exact hlevel w'
  -- `f` factors through `E` on `s`.
  have hle₁ : #(s.image f) ≤ #(s.image E) := by
    refine card_le_card_of_surjOn (fun e => f (Function.invFunOn E ↑s e)) fun y hy => ?_
    obtain ⟨w, hw, rfl⟩ := mem_image.mp (mem_coe.mp hy)
    have hinv := Function.invFunOn_pos (f := E) (s := ↑s) ⟨w, mem_coe.mpr hw, rfl⟩
    exact ⟨E w, mem_coe.mpr (mem_image_of_mem E hw), hfac _ _ hinv.2⟩
  -- The possible descriptions.
  let NC : Fin c.size → Finset ((κ → Bool) → Bool) := fun k => univ.filter fun g =>
    IsThresholdShift (fun j => inputWeight c.program k (emb j)) g ∧ ∃ u v, g u ≠ g v
  let P : Finset (Finset (Fin c.size) × (Fin c.size → (κ → Bool) → Bool)) :=
    (powersetCard D B).biUnion fun I =>
      (Fintype.piFinset fun k => if k ∈ I then NC k else {fun _ => false}).image fun g => (I, g)
  have hmem (w : Fin n → Bool) (hw : w ∈ s) : E w ∈ P ×ˢ range (2 ^ Fintype.card κ + 1) := by
    refine mem_product.mpr ⟨mem_biUnion.mpr ⟨S w, mem_powersetCard.mpr
      ⟨circuitSplitGates_subset c o _ w, by rw [card_circuitSplitGates, hs w hw]⟩, ?_⟩, ?_⟩
    · refine mem_image.mpr ⟨gs w, Fintype.mem_piFinset.mpr fun k => ?_, rfl⟩
      by_cases hk : k ∈ S w
      · simp only [gs, hk, ↓reduceIte, NC, mem_filter, mem_univ, true_and]
        refine ⟨⟨_, ltfEval_embedUpdate hinj _ _ w⟩, ?_⟩
        by_contra hconst
        push Not at hconst
        exact not_forcedToConst_of_mem_circuitSplitGates hk
          ((forcedToConst_image_iff hinj _ w).mpr hconst)
      · simp [gs, hk]
    · refine mem_range.mpr (Nat.lt_succ_of_le ((card_filter_le _ _).trans_eq ?_))
      simp
  have hle₂ : #(s.image E) ≤ #(P ×ˢ range (2 ^ Fintype.card κ + 1)) :=
    card_le_card fun e he => by
      obtain ⟨w, hw, rfl⟩ := mem_image.mp he
      exact hmem w hw
  have hP : #P ≤ B.card.choose D * (2 ^ Fintype.card κ - 1) ^ D := by
    refine card_biUnion_le.trans ?_
    rw [← card_powersetCard, ← smul_eq_mul, ← sum_const]
    refine sum_le_sum fun I hI => card_image_le.trans ?_
    rw [Fintype.card_piFinset]
    have hI' := (mem_powersetCard.mp hI).2
    calc ∏ k, #(if k ∈ I then NC k else {fun _ => false})
        = ∏ k, (if k ∈ I then #(NC k) else 1) := prod_congr rfl fun k _ => by split_ifs <;> simp
      _ = ∏ k ∈ I, #(NC k) := by rw [prod_ite_mem, univ_inter]
      _ ≤ (2 ^ Fintype.card κ - 1) ^ #I :=
          prod_le_pow_card _ _ _ fun k _ => card_isThresholdShift_nonconst_le _
      _ = (2 ^ Fintype.card κ - 1) ^ D := by rw [hI']
  calc #(s.image f) ≤ #(s.image E) := hle₁
    _ ≤ #(P ×ˢ range (2 ^ Fintype.card κ + 1)) := hle₂
    _ = #P * (2 ^ Fintype.card κ + 1) := by rw [card_product, card_range]
    _ ≤ B.card.choose D * (2 ^ Fintype.card κ - 1) ^ D * (2 ^ Fintype.card κ + 1) :=
        Nat.mul_le_mul_right _ hP

end Cslib.Circuits.Boolean.WeightedThreshold
