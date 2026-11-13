/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperserCore.State

/-!
# States of `3.5n` gate elimination

Specialization of the pair-type-generic gate-elimination state
(`Cslib.Circuits.Boolean.AffineDisperserCore.State`) for the `3.5n - o(n)` lower bound of
[Mishra and Santhanam][MishraSanthanam2026]:

* pairs are `ℕ × ℕ` with `locus := True`;
* unpaired parameters have `0/6/7` degree weights (`weight`);
* the potential is `W = 2 s + 3 q + ∑_{x ∈ unpaired} weight (deg x)`, with coefficient `ca = 14`
  for `ΔW ≤ 14 Δa`;
* `Φ` is affine along every affine family on which each pair is tame (`PairTame`), yielding
  Proposition 2.2 (`State.Valid.exists_affine_embedding`) and Lemma 2.3
  (`State.Valid.false_of_fix`, `State.Valid.out_not_affine`).

## Main definitions

* `Cslib.Circuits.Boolean.AffineDisperser.weight`: `0/6/7` degree weights.
* `Cslib.Circuits.Boolean.AffineDisperser.PairTame`: pair-tameness of a family of assignments.
* `Cslib.Circuits.Boolean.AffineDisperser.config`,
  `Cslib.Circuits.Boolean.AffineDisperser.State`: the `3.5n` configuration and state abbreviation.

## Main results

* `Cslib.Circuits.Boolean.AffineDisperser.State.Valid.exists_affine_embedding`: Proposition 2.2.
* `Cslib.Circuits.Boolean.AffineDisperser.State.Valid.exists_out_ne_of_le`,
  `Cslib.Circuits.Boolean.AffineDisperser.State.Valid.false_of_fix`,
  `Cslib.Circuits.Boolean.AffineDisperser.State.Valid.out_not_affine`: Lemma 2.3.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
-/

public section

namespace Cslib.Circuits.Boolean.AffineDisperser

open Finset Cslib.BitString SemiCircuit AffineDisperserCore

/-! ### Weights and pair tameness -/

/-- The weight of an unpaired parameter of degree `k`: `0` if unused, `6` if isolated (`k = 1`)
and `7` if of degree at least two. -/
@[expose] def weight (k : ℕ) : ℕ :=
  if k = 0 then 0 else if k = 1 then 6 else 7

/-- The degree weight function `weight` is monotone. -/
theorem weight_mono {k l : ℕ} (h : k ≤ l) : weight k ≤ weight l := by
  unfold weight; split_ifs <;> omega

/-- Every degree weight `weight k` is at most `7`. -/
theorem weight_le_seven (k : ℕ) : weight k ≤ 7 := by
  unfold weight; split_ifs <;> omega

/-- An unused parameter (`k = 0`) has weight `0`. -/
@[simp] theorem weight_zero : weight 0 = 0 := rfl

/-- An isolated parameter (`k = 1`) has weight `6`. -/
@[simp] theorem weight_one : weight 1 = 6 := rfl

/-- A parameter of degree `k ≥ 2` has weight `7`. -/
theorem weight_of_two_le {k : ℕ} (hk : 2 ≤ k) : weight k = 7 := by
  unfold weight; split_ifs <;> omega

/-- A parameter of positive degree (`k ≥ 1`) has weight at least `6`. -/
theorem six_le_weight {k : ℕ} (hk : 1 ≤ k) : 6 ≤ weight k := by
  unfold weight; split_ifs <;> omega

/-- Along the family `σ` of assignments, the pair `pr` contributes an affine term to a quadratic
map: one of its members, or their sum, is constant. -/
@[expose] def PairTame {α : Type*} (σ : α → ℕ → Bool) (pr : ℕ × ℕ) : Prop :=
  (∀ x y, σ x pr.1 = σ y pr.1) ∨ (∀ x y, σ x pr.2 = σ y pr.2) ∨
    ∀ x y, σ x pr.1 + σ x pr.2 = σ y pr.1 + σ y pr.2

/-! ### `3.5n` configuration and state -/

/-- Configuration for `3.5n` gate elimination: index pairs `ℕ × ℕ`, `0/6/7` weights, potential
`2 s + 3 q + ∑ wt`, potential slope `14`, trivial locus, and pair-tame affinity of `Φ`. -/
@[expose, reducible] def config : AffineDisperserCore.Config where
  Pair := ℕ × ℕ
  fst := Prod.fst
  snd := Prod.snd
  cs := 2
  cq := 3
  ca := 14
  weight := weight
  weight_mono := weight_mono
  weight_zero := weight_zero
  weightBound := 7
  weight_le := weight_le_seven
  locus _ _ := True
  locus_congr _ _ := trivial
  phiOK P phi := ∀ (k : ℕ) (σ : BitString k → ℕ → Bool), IsAffine σ →
    (∀ pr ∈ P, PairTame σ pr) → IsAffine (phi ∘ σ)

/-- The size coefficient in the `3.5n` potential `W` is `2`. -/
theorem config_cs : config.cs = 2 := rfl
/-- The pair coefficient in the `3.5n` potential `W` is `3`. -/
theorem config_cq : config.cq = 3 := rfl
/-- The potential slope in the `3.5n` gate elimination step is `14`. -/
theorem config_ca : config.ca = 14 := rfl
/-- The `3.5n` degree weight function is `weight`. -/
theorem config_weight : config.weight = weight := rfl
/-- The `3.5n` degree weight upper bound is `7`. -/
theorem config_weightBound : config.weightBound = 7 := rfl
/-- The first projection of `3.5n` pairs is `Prod.fst`. -/
theorem config_fst : config.fst = Prod.fst := rfl
/-- The second projection of `3.5n` pairs is `Prod.snd`. -/
theorem config_snd : config.snd = Prod.snd := rfl

/-- A state of gate elimination for a Boolean function on `n` bits. -/
abbrev State (n : ℕ) : Type := AffineDisperserCore.State config n

namespace State

open AffineDisperserCore.State

variable {n : ℕ} {S : State n}

/-! ### Proposition 2.2 and Lemma 2.3 -/

/-- Along an injective affine family of parameter assignments on which every pair is tame, the
parameter map is an injective affine map, so the output of a valid state for an affine
disperser for dimension `d` is not constant when the family has dimension at least `d`. -/
theorem Valid.exists_out_ne {f : BooleanFunction n} {d : ℕ} (hS : S.Valid f)
    (hf : IsAffineDisperser f d) {k : ℕ} (σ : BitString k → ℕ → Bool) (hσ : IsAffine σ)
    (htame : ∀ pr ∈ S.pairs, PairTame σ pr)
    (hinj : ∀ u v, (∀ j ∈ S.params, σ u j = σ v j) → u = v) (hk : d ≤ k) :
    ∃ u v val val', S.Consistent val ∧ S.Consistent val' ∧ (∀ j ∈ S.params, val j = σ u j) ∧
      (∀ j ∈ S.params, val' j = σ v j) ∧ S.out.eval val ≠ S.out.eval val' := by
  obtain ⟨u, v, huv⟩ := hf.mono hk (S.phi ∘ σ) (hS.phi_affine k σ hσ htame)
    (fun u v h => hinj u v (hS.phi_injective _ _ h))
  obtain ⟨val, hval, hcons⟩ := hS.wf.exists_consistent (σ u)
  obtain ⟨val', hval', hcons'⟩ := hS.wf.exists_consistent (σ v)
  refine ⟨u, v, val, val', hcons, hcons', hval, hval', ?_⟩
  rw [hS.computes val hcons trivial, hS.computes val' hcons' trivial,
    hS.phi_congr val (σ u) hval, hS.phi_congr val' (σ v) hval']
  exact huv

/-- **Proposition 2.2** of [Mishra and Santhanam][MishraSanthanam2026]: the image of the
parameter map of a valid state contains the image of an injective affine map from
`BitString a`. -/
theorem Valid.exists_affine_embedding {f : BooleanFunction n} (hS : S.Valid f) :
    ∃ g : BitString S.a → BitString n, IsAffine g ∧ Function.Injective g ∧
      ∀ u, ∃ val, S.Consistent val ∧ g u = S.phi val := by
  set F := S.params \ S.pairs.image Prod.fst
  have hF : F.card = S.a := hS.card_sdiff_image Prod.fst fun _ _ => Or.inl rfl
  have hFp : F ⊆ S.params := Finset.sdiff_subset
  refine ⟨S.phi ∘ spread F hF, hS.phi_affine _ _ (isAffine_spread F hF) ?_, ?_, fun u => ?_⟩
  · intro pr hpr
    refine Or.inl fun u v => ?_
    have : pr.1 ∉ F := fun h => (Finset.mem_sdiff.1 h).2 (Finset.mem_image_of_mem _ hpr)
    rw [spread_of_notMem hF u this, spread_of_notMem hF v this]
  · intro u v h
    exact eq_of_spread hF fun i hi => hS.phi_injective _ _ h i (hFp hi)
  · obtain ⟨val, hval, hcons⟩ := hS.wf.exists_consistent (spread F hF u)
    exact ⟨val, hcons, (hS.phi_congr val _ hval).symm⟩

/-- The output of a valid state for an affine disperser for dimension `d ≤ a` is not
constant. -/
theorem Valid.exists_out_ne_of_le {f : BooleanFunction n} {d : ℕ} (hS : S.Valid f)
    (hf : IsAffineDisperser f d) (ha : d ≤ S.a) :
    ∃ val val', S.Consistent val ∧ S.Consistent val' ∧ S.out.eval val ≠ S.out.eval val' := by
  set F := S.params \ S.pairs.image Prod.fst
  have hF : F.card = S.a := hS.card_sdiff_image Prod.fst fun _ _ => Or.inl rfl
  have hFp : F ⊆ S.params := Finset.sdiff_subset
  obtain ⟨-, -, val, val', h, h', -, -, hne⟩ := Valid.exists_out_ne hS hf (spread F hF)
    (isAffine_spread F hF) (fun pr hpr => Or.inl fun u v => by
      have : pr.1 ∉ F := fun h => (Finset.mem_sdiff.1 h).2 (Finset.mem_image_of_mem _ hpr)
      rw [spread_of_notMem hF u this, spread_of_notMem hF v this])
    (fun u v h => eq_of_spread hF fun i hi => h i (hFp hi)) ha
  exact ⟨val, val', h, h', hne⟩

/-- If `d < a`, the output of a valid state for an affine disperser for dimension `d` is not
constant on the consistent assignments satisfying one more affine equation
`x = c + ∑ j ∈ R, u j` between the parameters: imposing it keeps an affine subspace of dimension
`a - 1 ≥ d` in the image of the parameter map. -/
theorem Valid.false_of_fix {f : BooleanFunction n} {d : ℕ} (hS : S.Valid f)
    (hf : IsAffineDisperser f d) (ha : d < S.a) {x : ℕ} (hx : x ∈ S.params) (c : Bool)
    (R : Finset ℕ) (hR : R ⊆ S.params) (hxR : x ∉ R) (b : Bool)
    (hout : ∀ val, S.Consistent val → val x = c + ∑ j ∈ R, val j → S.out.eval val = b) :
    False := by
  classical
  let rep : ℕ × ℕ → ℕ := fun pr => if pr.1 = x then pr.2 else pr.1
  have hrep : ∀ pr ∈ S.pairs, config.Contains pr (rep pr) := fun pr _ => by
    by_cases h : pr.1 = x <;> simp [rep, h, Config.Contains]
  have hrepx : ∀ pr ∈ S.pairs, rep pr ≠ x := fun pr hpr => by
    by_cases h : pr.1 = x
    · simp only [rep, h, ite_true]
      exact fun h' => (hS.pair_mem pr hpr).2.2 (h.trans h'.symm)
    · simp only [rep, h, ite_false]
      exact h
  set F := S.params \ S.pairs.image rep
  have hF : F.card = S.a := hS.card_sdiff_image rep hrep
  have hxF : x ∈ F := Finset.mem_sdiff.2 ⟨hx, fun h => by
    obtain ⟨pr, hpr, he⟩ := Finset.mem_image.1 h
    exact hrepx pr hpr he⟩
  set F' := F.erase x
  have hF' : F'.card = S.a - 1 := by rw [Finset.card_erase_of_mem hxF, hF]
  have hF'p : F' ⊆ S.params := (Finset.erase_subset _ _).trans Finset.sdiff_subset
  let σ : BitString (S.a - 1) → ℕ → Bool := fun u =>
    Function.update (spread F' hF' u) x (c + ∑ j ∈ R, spread F' hF' u j)
  have hσx : ∀ u, σ u x = c + ∑ j ∈ R, σ u j := fun u => by
    simp only [σ, Function.update_self]
    congr 1
    exact Finset.sum_congr rfl fun j hj =>
      (Function.update_of_ne (by rintro rfl; exact hxR hj) _ _).symm
  have hσ : IsAffine σ :=
    isAffine_update (isAffine_spread F' hF') x (isAffine_const_add_sum (isAffine_spread F' hF') c R)
  obtain ⟨u, v, val, val', hcons, hcons', hval, hval', hne⟩ := Valid.exists_out_ne hS hf σ hσ
    (fun pr hpr => by
      have hnot : rep pr ∉ F' := fun h =>
        (Finset.mem_sdiff.1 (Finset.mem_of_mem_erase h)).2 (Finset.mem_image_of_mem _ hpr)
      have hconst : ∀ u, σ u (rep pr) = false := fun u => by
        simp only [σ, Function.update_of_ne (hrepx pr hpr), spread_of_notMem hF' u hnot]
      rcases hrep pr hpr with h | h
      · exact Or.inl fun u v => by
          have hw : rep pr = pr.1 := h.symm
          rw [← hw, hconst, hconst]
      · exact Or.inr (Or.inl fun u v => by
          have hw : rep pr = pr.2 := h.symm
          rw [← hw, hconst, hconst]))
    (fun u v h => eq_of_spread hF' fun i hi => by
      have := h i (hF'p hi)
      simpa only [σ, Function.update_of_ne (Finset.ne_of_mem_erase hi)] using this)
    (by omega)
  have hfix : ∀ w : ℕ → Bool, ∀ u', (∀ j ∈ S.params, w j = σ u' j) →
      w x = c + ∑ j ∈ R, w j := fun w u' hw => by
    rw [hw x hx, hσx, Finset.sum_congr rfl fun j hj => hw j (hR hj)]
  exact hne ((hout val hcons (hfix val u hval)).trans (hout val' hcons' (hfix val' v hval')).symm)

/-- Part of **Lemma 2.3** of [Mishra and Santhanam][MishraSanthanam2026]: if `d < a`, the output
of a valid state for an affine disperser for dimension `d` is not an affine function of the
parameters. -/
theorem Valid.out_not_affine {f : BooleanFunction n} {d : ℕ} (hS : S.Valid f)
    (hf : IsAffineDisperser f d) (ha : d < S.a) (c : Bool) {T : Finset ℕ} (hT : T ⊆ S.params) :
    ¬ ∀ val, S.Consistent val → S.out.eval val = c + ∑ j ∈ T, val j := fun hout =>
  Valid.out_not_affine_of
    (fun hx c' R hR hxR b hout' => Valid.false_of_fix hS hf ha hx c' R hR hxR b
      fun val hcons hfix => hout' val hcons trivial hfix)
    (Finset.nonempty_iff_ne_empty.2 fun h => by simp [a, m, h] at ha)
    c hT fun val hcons _ => hout val hcons

end State

end Cslib.Circuits.Boolean.AffineDisperser
