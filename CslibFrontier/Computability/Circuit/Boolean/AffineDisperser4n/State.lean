/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperserCore.State

/-!
# States of `4n - 10d` gate elimination with zero-locus pair semantics

Specialization of the pair-type-generic gate-elimination state
(`Cslib.Circuits.Boolean.AffineDisperserCore.State`) for the `4n - 10d` lower bound of
[Mishra and Santhanam][MishraSanthanam2027]:

* pairs are zero-locus pairs `ZeroPair` constraining parameter assignments to `Z(P)`
  (`ZeroPair.Holds`);
* unpaired parameters have `0/6` degree weights (`weight`);
* the potential is `W = s + 4 q + 6 · #{used unpaired parameters}`, with coefficient `ca = 10` for
  `ΔW ≤ 10 Δa`;
* `Φ` is globally affine (`IsAffine`), giving Lemma 2.2 (`State.Valid.exists_affine_embedding`)
  and the hyperplane / non-affinity lemmas (`State.Valid.false_of_fix`,
  `State.Valid.out_not_affine`).

## Main definitions

* `Cslib.Circuits.Boolean.AffineDisperser4n.ZeroPair`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.ZeroPair.Holds`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.ZeroPair.Contains`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.ZeroPair.bias`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.ZeroPair.partner`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.ZeroPair.partnerBias`: zero-locus pairs and accessors.
* `Cslib.Circuits.Boolean.AffineDisperser4n.weight`: the `0/6` degree weight.
* `Cslib.Circuits.Boolean.AffineDisperser4n.config`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.State`: the `4n` configuration and state abbreviation.

## Main results

* `Cslib.Circuits.Boolean.AffineDisperser4n.State.Valid.exists_affine_embedding`: Lemma 2.2,
  `a`-dimensional affine subspace in `Φ(Z(P))`.
* `Cslib.Circuits.Boolean.AffineDisperser4n.State.Valid.exists_affine_subspace_const_of_fix`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.State.Valid.false_of_fix`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.State.Valid.out_not_affine`: hyperplane and affinity
  lower-bound lemmas.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 4n - O(log n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2027] (submission PDF inaccessible with HTTP 1042; cited
  labels and operation names follow issue `#4322` and are unverified against the manuscript)
-/

public section

namespace Cslib.Circuits.Boolean.AffineDisperser4n

open Finset Cslib.BitString SemiCircuit AffineDisperserCore

/-! ### Weights -/

/-- The `0/6` weight of an unpaired parameter of degree `k`: `0` if unused (`k = 0`) and `6` if
used (`k ≥ 1`). -/
@[expose] def weight (k : ℕ) : ℕ :=
  if k = 0 then 0 else 6

/-- An unused parameter (`k = 0`) has weight `0`. -/
@[simp] theorem weight_zero : weight 0 = 0 := rfl

/-- A used parameter (`1 ≤ k`) has weight `6`. -/
theorem weight_of_one_le {k : ℕ} (hk : 1 ≤ k) : weight k = 6 := by
  unfold weight
  split_ifs <;> omega

/-- The degree weight function `weight` is monotone. -/
theorem weight_mono {k l : ℕ} (h : k ≤ l) : weight k ≤ weight l := by
  unfold weight
  split_ifs <;> omega

/-- Every degree weight `weight k` is at most `6`. -/
theorem weight_le_six (k : ℕ) : weight k ≤ 6 := by
  unfold weight
  split_ifs <;> omega

/-! ### Zero-locus pairs -/

/-- A pair of parameters together with biases: on the zero locus `Z(P)`, at least one member equals
its bias (`val fst = fstBias ∨ val snd = sndBias`), i.e.,
`(val fst ^^ fstBias) && (val snd ^^ sndBias) = false`. -/
structure ZeroPair where
  /-- The first parameter of the pair. -/
  fst : ℕ
  /-- The bias of the first parameter. -/
  fstBias : Bool
  /-- The second parameter of the pair. -/
  snd : ℕ
  /-- The bias of the second parameter. -/
  sndBias : Bool
  deriving DecidableEq

namespace ZeroPair

/-- The zero-locus constraint of a pair: at least one member takes its bias. -/
@[expose] def Holds (pr : ZeroPair) (val : ℕ → Bool) : Prop :=
  val pr.fst = pr.fstBias ∨ val pr.snd = pr.sndBias

/-- Decidability of `ZeroPair.Holds`. -/
instance (pr : ZeroPair) (val : ℕ → Bool) : Decidable (pr.Holds val) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Equivalence between `pr.Holds val` and vanishing of the biased product. -/
theorem holds_iff_and_eq_false (pr : ZeroPair) (val : ℕ → Bool) :
    pr.Holds val ↔ ((val pr.fst ^^ pr.fstBias) && (val pr.snd ^^ pr.sndBias)) = false := by
  unfold Holds
  cases val pr.fst <;> cases pr.fstBias <;> cases val pr.snd <;> cases pr.sndBias <;> decide

/-- `pr.Holds` depends only on the values assigned to `pr.fst` and `pr.snd`. -/
theorem holds_congr {pr : ZeroPair} {val val' : ℕ → Bool} (h₁ : val pr.fst = val' pr.fst)
    (h₂ : val pr.snd = val' pr.snd) : pr.Holds val ↔ pr.Holds val' := by
  unfold Holds
  rw [h₁, h₂]

/-- Whether `x` is one of the two parameters in `pr`. -/
@[expose] def Contains (pr : ZeroPair) (x : ℕ) : Prop :=
  pr.fst = x ∨ pr.snd = x

/-- Decidability of `ZeroPair.Contains`. -/
instance (pr : ZeroPair) : DecidablePred pr.Contains :=
  fun _ => inferInstanceAs (Decidable (_ ∨ _))

/-- The bias of `x` in `pr` (assuming `pr.Contains x`). -/
@[expose] def bias (pr : ZeroPair) (x : ℕ) : Bool :=
  if pr.fst = x then pr.fstBias else pr.sndBias

/-- The partner of `x` in `pr` (assuming `pr.Contains x`). -/
@[expose] def partner (pr : ZeroPair) (x : ℕ) : ℕ :=
  if pr.fst = x then pr.snd else pr.fst

/-- The bias of the partner of `x` in `pr` (assuming `pr.Contains x`). -/
@[expose] def partnerBias (pr : ZeroPair) (x : ℕ) : Bool :=
  if pr.fst = x then pr.sndBias else pr.fstBias

/-- The partner of a member of `pr` is also contained in `pr`. -/
theorem contains_partner {pr : ZeroPair} {x : ℕ} (hx : pr.Contains x) :
    pr.Contains (pr.partner x) := by
  rcases hx with h | h <;> unfold Contains partner <;> split_ifs <;> tauto

/-- In a pair with distinct endpoints, the partner of `x` differs from `x`. -/
theorem partner_ne {pr : ZeroPair} {x : ℕ} (hne : pr.fst ≠ pr.snd) (hx : pr.Contains x) :
    pr.partner x ≠ x := by
  rcases hx with h | h <;> unfold partner <;> split_ifs <;> intro he <;> simp_all

/-- Taking the partner twice returns `x`. -/
theorem partner_partner {pr : ZeroPair} {x : ℕ} (hne : pr.fst ≠ pr.snd) (hx : pr.Contains x) :
    pr.partner (pr.partner x) = x := by
  unfold partner
  rcases hx with h | h <;> split_ifs <;> simp_all

/-- The bias of `pr.partner x` in `pr` is `pr.partnerBias x`. -/
theorem bias_partner {pr : ZeroPair} {x : ℕ} (hne : pr.fst ≠ pr.snd) (hx : pr.Contains x) :
    pr.bias (pr.partner x) = pr.partnerBias x := by
  unfold bias partner partnerBias
  rcases hx with h | h <;> split_ifs <;> simp_all

/-- Rewriting `pr.Holds val` in terms of `x` and `pr.partner x`. -/
theorem holds_iff_contains {pr : ZeroPair} {x : ℕ} (hx : pr.Contains x) (val : ℕ → Bool) :
    pr.Holds val ↔ val x = pr.bias x ∨ val (pr.partner x) = pr.partnerBias x := by
  unfold Holds bias partner partnerBias
  rcases hx with rfl | rfl
  · simp
  · by_cases h : pr.fst = pr.snd
    · simp [h]
    · simp [h, or_comm]

/-- Fixing `x` to its bias satisfies `pr.Holds`. -/
theorem holds_of_eq_bias {pr : ZeroPair} {x : ℕ} (hx : pr.Contains x) {val : ℕ → Bool}
    (h : val x = pr.bias x) : pr.Holds val :=
  (holds_iff_contains hx val).2 (Or.inl h)

/-- Fixing `pr.partner x` to `pr.partnerBias x` satisfies `pr.Holds`. -/
theorem holds_of_eq_partnerBias {pr : ZeroPair} {x : ℕ} (hx : pr.Contains x) {val : ℕ → Bool}
    (h : val (pr.partner x) = pr.partnerBias x) : pr.Holds val :=
  (holds_iff_contains hx val).2 (Or.inr h)

/-- Choosing `x = partner ^^ !(bias x ^^ partnerBias x)` forces at least one endpoint to take its
bias, satisfying `pr.Holds`. -/
theorem holds_of_eq_xor {pr : ZeroPair} {x : ℕ} (hx : pr.Contains x) {val : ℕ → Bool}
    (h : val x = (val (pr.partner x) ^^ !(pr.bias x ^^ pr.partnerBias x))) : pr.Holds val := by
  rw [holds_iff_contains hx, h]
  generalize val (pr.partner x) = v
  generalize pr.bias x = a
  generalize pr.partnerBias x = b
  revert v a b
  decide

end ZeroPair

/-! ### `4n` configuration and state -/

/-- Configuration for `4n - 10d` gate elimination: zero-locus pairs, `0/6` weights, potential
`s + 4 q + ∑ wt`, potential slope `10`, and global affinity of `Φ`. -/
@[expose, reducible] def config : AffineDisperserCore.Config where
  Pair := ZeroPair
  fst := ZeroPair.fst
  snd := ZeroPair.snd
  cs := 1
  cq := 4
  ca := 10
  weight := weight
  weight_mono := weight_mono
  weight_zero := weight_zero
  weightBound := 6
  weight_le := weight_le_six
  locus P val := ∀ pr ∈ P, pr.Holds val
  locus_congr hagree hlocus pr hpr :=
    (ZeroPair.holds_congr (hagree pr hpr).1 (hagree pr hpr).2).1 (hlocus pr hpr)
  phiOK _ phi := IsAffine phi

/-- The size coefficient in the `4n` potential `W` is `1`. -/
theorem config_cs : config.cs = 1 := rfl
/-- The pair coefficient in the `4n` potential `W` is `4`. -/
theorem config_cq : config.cq = 4 := rfl
/-- The potential slope in the `4n` gate elimination step is `10`. -/
theorem config_ca : config.ca = 10 := rfl
/-- The `4n` degree weight function is `weight`. -/
theorem config_weight : config.weight = weight := rfl
/-- The `4n` degree weight upper bound is `6`. -/
theorem config_weightBound : config.weightBound = 6 := rfl
/-- The first projection of `4n` pairs is `ZeroPair.fst`. -/
theorem config_fst : config.fst = ZeroPair.fst := rfl
/-- The second projection of `4n` pairs is `ZeroPair.snd`. -/
theorem config_snd : config.snd = ZeroPair.snd := rfl

/-- A state of `4n - 10d` gate elimination for a Boolean function on `n` bits. -/
abbrev State (n : ℕ) : Type := AffineDisperserCore.State config n

namespace State

open AffineDisperserCore.State

variable {n : ℕ} (S : State n)

/-! ### Lemma 2.2 and hyperplane lemmas -/

/-- Fixing every chosen pair representative `rep pr` to its bias in `pr` gives a base assignment
`base` such that `spread F hF u ^^ base` lies in `Z(P)`. -/
private def locusAssign (rep : ZeroPair → ℕ) (F : Finset ℕ) {k : ℕ} (hF : F.card = k)
    (u : BitString k) (i : ℕ) : Bool :=
  spread F hF u i ^^ ∑ pr ∈ S.pairs, if rep pr = i then pr.bias (rep pr) else false

private theorem isAffine_locusAssign (rep : ZeroPair → ℕ) (F : Finset ℕ) {k : ℕ}
    (hF : F.card = k) : IsAffine (S.locusAssign rep F hF) :=
  isAffine_xor_const (isAffine_spread F hF) _

private theorem locusAssign_of_mem {rep : ZeroPair → ℕ} {F : Finset ℕ} {k : ℕ} (hF : F.card = k)
    (hFdisj : ∀ pr ∈ S.pairs, rep pr ∉ F) (u : BitString k) {i : ℕ} (hi : i ∈ F) :
    S.locusAssign rep F hF u i = spread F hF u i := by
  unfold locusAssign
  have hzero : ∑ pr ∈ S.pairs, (if rep pr = i then pr.bias (rep pr) else false) = false := by
    refine Finset.sum_eq_zero fun pr hpr => ?_
    have hne : rep pr ≠ i := fun h => hFdisj pr hpr (h ▸ hi)
    rw [ite_eq_right hne]
    rfl
  rw [hzero, Bool.xor_false]

variable {S}

private theorem locusAssign_rep {f : BooleanFunction n} (hS : S.Valid f)
    {rep : ZeroPair → ℕ} (hrep : ∀ pr ∈ S.pairs, pr.Contains (rep pr))
    {F : Finset ℕ} {k : ℕ} (hF : F.card = k)
    (hFdisj : ∀ pr ∈ S.pairs, rep pr ∉ F) (u : BitString k)
    {pr : ZeroPair} (hpr : pr ∈ S.pairs) :
    S.locusAssign rep F hF u (rep pr) = pr.bias (rep pr) := by
  unfold locusAssign
  rw [spread_of_notMem hF u (hFdisj pr hpr), Bool.false_xor]
  rw [Finset.sum_eq_single_of_mem pr hpr]
  · simp
  · intro pr' hpr' hne
    have hdisj := hS.pairs_disjoint pr' hpr' pr hpr hne
    have hneq : rep pr' ≠ rep pr := by
      rcases hrep pr hpr with h1 | h1 <;> rcases hrep pr' hpr' with h2 | h2 <;>
        rw [← h1, ← h2] <;> tauto
    rw [ite_eq_right hneq]
    rfl

/-- Lemma 2.2 (label per issue `#4322`, unverified against [MishraSanthanam2027]): the image
`Φ(Z(P))` of the zero locus under the parameter map of a valid state contains the image of an
injective affine map from `BitString a`. -/
theorem Valid.exists_affine_embedding {f : BooleanFunction n} (hS : S.Valid f) :
    ∃ g : BitString S.a → BitString n, IsAffine g ∧ Function.Injective g ∧
      ∀ u, ∃ val, S.Consistent val ∧ S.Locus val ∧ g u = S.phi val := by
  set rep : ZeroPair → ℕ := ZeroPair.fst
  have hrep : ∀ pr ∈ S.pairs, pr.Contains (rep pr) := fun _ _ => Or.inl rfl
  set F := S.params \ S.pairs.image rep
  have hF : F.card = S.a := hS.card_sdiff_image rep hrep
  have hFp : F ⊆ S.params := Finset.sdiff_subset
  have hFdisj : ∀ pr ∈ S.pairs, rep pr ∉ F := fun pr hpr h =>
    (Finset.mem_sdiff.1 h).2 (Finset.mem_image_of_mem _ hpr)
  let σ := S.locusAssign rep F hF
  refine ⟨S.phi ∘ σ, hS.phi_affine.comp (S.isAffine_locusAssign rep F hF), ?_, fun u => ?_⟩
  · intro u v huv
    refine eq_of_spread hF fun i hi => ?_
    have hi' := hS.phi_injective _ _ huv i (hFp hi)
    dsimp only [σ] at hi'
    rwa [S.locusAssign_of_mem hF hFdisj u hi, S.locusAssign_of_mem hF hFdisj v hi] at hi'
  · obtain ⟨val, hval, hcons⟩ := hS.wf.exists_consistent (σ u)
    refine ⟨val, hcons, fun pr hpr => ?_, (hS.phi_congr val _ hval).symm⟩
    exact ZeroPair.holds_of_eq_bias (hrep pr hpr)
      (by rw [hval _ (by rcases hrep pr hpr with h | h <;> rw [← h] <;>
            [exact (hS.pair_mem pr hpr).1; exact (hS.pair_mem pr hpr).2.1])]
          exact locusAssign_rep hS hrep hF hFdisj u hpr)

private theorem Valid.exists_affine_subspace_const_of_family {f : BooleanFunction n} {d k : ℕ}
    (hS : S.Valid f) (σ : BitString k → ℕ → Bool) (hσ : IsAffine σ) (hlocus : ∀ u, S.Locus (σ u))
    (hinj : ∀ u v, (∀ j ∈ S.params, σ u j = σ v j) → u = v) (hk : d ≤ k)
    {b : Bool} (hout : ∀ u val, S.Consistent val → (∀ j ∈ S.params, val j = σ u j) →
      S.out.eval val = b) :
    ∃ g : BitString d → BitString n, IsAffine g ∧ Function.Injective g ∧
      ∀ u, ∃ val, S.Consistent val ∧ S.Locus val ∧ S.out.eval val = b ∧
        g u = S.phi val := by
  let τ : BitString d → ℕ → Bool := σ ∘ zeroExtend
  have hτ : IsAffine τ := hσ.comp isAffine_zeroExtend
  refine ⟨S.phi ∘ τ, hS.phi_affine.comp hτ, fun u v h => ?_, fun u => ?_⟩
  · exact zeroExtend_injective hk (hinj _ _ (hS.phi_injective _ _ h))
  · obtain ⟨val, hval, hcons⟩ := hS.wf.exists_consistent (τ u)
    refine ⟨val, hcons, fun pr hpr => ?_, hout _ val hcons hval, (hS.phi_congr val _ hval).symm⟩
    have h1 := (hS.pair_mem pr hpr).1
    have h2 := (hS.pair_mem pr hpr).2.1
    exact (ZeroPair.holds_congr (hval _ h1) (hval _ h2)).2 (hlocus _ pr hpr)

/-- The output of a valid state for an affine disperser for dimension `d ≤ a` is not constant on
`Z(P)`. -/
theorem Valid.exists_out_ne_of_le {f : BooleanFunction n} {d : ℕ} (hS : S.Valid f)
    (hf : IsAffineDisperser f d) (ha : d ≤ S.a) :
    ∃ val val', S.Consistent val ∧ S.Locus val ∧ S.Consistent val' ∧ S.Locus val' ∧
      S.out.eval val ≠ S.out.eval val' := by
  obtain ⟨g, hg, hinj, hval⟩ := Valid.exists_affine_embedding hS
  obtain ⟨u, v, huv⟩ := hf.mono ha g hg hinj
  obtain ⟨val, hc, hl, hg1⟩ := hval u
  obtain ⟨val', hc', hl', hg2⟩ := hval v
  refine ⟨val, val', hc, hl, hc', hl', ?_⟩
  rw [hS.computes val hc hl, hS.computes val' hc' hl', ← hg1, ← hg2]
  exact huv

private theorem Valid.exists_affine_subspace_const_of_erased {n d : ℕ} {S : State n}
    {f : BooleanFunction n} (hS : S.Valid f) (ha : d < S.a) (c : Bool) {x : ℕ}
    (hx : x ∈ S.params) {R : Finset ℕ} (hR : R ⊆ S.params) (b : Bool)
    (hout : ∀ val, S.Consistent val → S.Locus val → val x = c + ∑ j ∈ R, val j →
      S.out.eval val = b)
    (rep : ZeroPair → ℕ) (hrep : ∀ pr ∈ S.pairs, pr.Contains (rep pr))
    {z : ℕ} (hzp : z ∈ S.params) (hrepz : ∀ pr ∈ S.pairs, rep pr ≠ z)
    (rhs : (ℕ → Bool) → Bool)
    (hrhs_aff : ∀ {g : BitString (S.a - 1) → ℕ → Bool}, IsAffine g →
      IsAffine fun u => rhs (g u))
    (hrhs_eq : ∀ g : ℕ → Bool, (∀ pr ∈ S.pairs, g (rep pr) = pr.bias (rep pr)) →
      Function.update g z (rhs g) x = c + ∑ j ∈ R, Function.update g z (rhs g) j) :
    ∃ g : BitString d → BitString n, IsAffine g ∧ Function.Injective g ∧
      ∀ u, ∃ val, S.Consistent val ∧ S.Locus val ∧ S.out.eval val = b ∧
        g u = S.phi val := by
  classical
  set F := S.params \ S.pairs.image rep
  have hF : F.card = S.a := hS.card_sdiff_image rep hrep
  have hzF : z ∈ F := Finset.mem_sdiff.2 ⟨hzp, fun h => by
    obtain ⟨pr, hpr, he⟩ := Finset.mem_image.1 h
    exact hrepz pr hpr he⟩
  set F' := F.erase z
  have hF' : F'.card = S.a - 1 := by rw [Finset.card_erase_of_mem hzF, hF]
  have hF'p : F' ⊆ S.params := (Finset.erase_subset _ _).trans Finset.sdiff_subset
  have hF'disj : ∀ pr ∈ S.pairs, rep pr ∉ F' := fun pr hpr h =>
    (Finset.mem_sdiff.1 (Finset.mem_of_mem_erase h)).2 (Finset.mem_image_of_mem _ hpr)
  let base := S.locusAssign rep F' hF'
  have hbase_rep : ∀ u pr, pr ∈ S.pairs → base u (rep pr) = pr.bias (rep pr) := fun u pr hpr =>
    locusAssign_rep hS hrep hF' hF'disj u hpr
  let σ : BitString (S.a - 1) → ℕ → Bool := fun u => Function.update (base u) z (rhs (base u))
  have hσaff : IsAffine σ :=
    isAffine_update (S.isAffine_locusAssign rep F' hF') z
      (hrhs_aff (S.isAffine_locusAssign rep F' hF'))
  have hlocus : ∀ u pr, pr ∈ S.pairs → pr.Holds (σ u) := fun u pr hpr =>
    ZeroPair.holds_of_eq_bias (hrep pr hpr) (by
      dsimp only [σ]
      rw [Function.update_of_ne (hrepz pr hpr)]
      exact hbase_rep u pr hpr)
  refine Valid.exists_affine_subspace_const_of_family hS σ hσaff hlocus
    (fun u v h => eq_of_spread hF' fun i hi => ?_) (by omega)
    fun u val hcons hval => ?_
  · have hi' := h i (hF'p hi)
    have hiz : i ≠ z := Finset.ne_of_mem_erase hi
    dsimp only [σ, base] at hi'
    rw [Function.update_of_ne hiz, Function.update_of_ne hiz,
      S.locusAssign_of_mem hF' hF'disj u hi,
      S.locusAssign_of_mem hF' hF'disj v hi] at hi'
    exact hi'
  · refine hout val hcons (fun pr hpr => ?_) ?_
    · exact (ZeroPair.holds_congr (hval _ (hS.pair_mem pr hpr).1)
        (hval _ (hS.pair_mem pr hpr).2.1)).2 (hlocus u pr hpr)
    · rw [hval x hx, Finset.sum_congr rfl fun j hj => hval j (hR hj)]
      exact hrhs_eq (base u) (hbase_rep u)

/-- If `d < a` and the output of a valid state is constant `b` on consistent assignments in `Z(P)`
satisfying one affine equation `x = c + ∑ j ∈ R, val j`, then there is an injective affine map
`BitString d → BitString n` into `Φ(Z(P))` whose consistent lifts all evaluate to `b`. -/
theorem Valid.exists_affine_subspace_const_of_fix {f : BooleanFunction n} {d : ℕ} (hS : S.Valid f)
    (ha : d < S.a) {x : ℕ} (hx : x ∈ S.params) (c : Bool) (R : Finset ℕ) (hR : R ⊆ S.params)
    (hxR : x ∉ R) (b : Bool)
    (hout : ∀ val, S.Consistent val → S.Locus val → val x = c + ∑ j ∈ R, val j →
      S.out.eval val = b) :
    ∃ g : BitString d → BitString n, IsAffine g ∧ Function.Injective g ∧
      ∀ u, ∃ val, S.Consistent val ∧ S.Locus val ∧ S.out.eval val = b ∧
        g u = S.phi val := by
  classical
  by_cases hcase : ∃ pr₀ ∈ S.pairs, pr₀.Contains x ∧ pr₀.partner x ∈ R
  · obtain ⟨pr₀, hpr₀, hx0, hyR⟩ := hcase
    set y := pr₀.partner x
    have hpr0_ne : pr₀.fst ≠ pr₀.snd := (hS.pair_mem pr₀ hpr₀).2.2
    have hy0 : pr₀.Contains y := pr₀.contains_partner hx0
    have hyx : y ≠ x := pr₀.partner_ne hpr0_ne hx0
    have hyp : y ∈ S.params := by
      rcases hy0 with h | h <;> rw [← h]
      · exact (hS.pair_mem pr₀ hpr₀).1
      · exact (hS.pair_mem pr₀ hpr₀).2.1
    let rep : ZeroPair → ℕ := fun pr => if pr.Contains x then x else pr.fst
    have hrep : ∀ pr ∈ S.pairs, pr.Contains (rep pr) := fun pr _ => by
      by_cases h : pr.Contains x
      · simp [rep, h]
      · simp only [rep, h, ite_false]; exact Or.inl rfl
    have hrepy : ∀ pr ∈ S.pairs, rep pr ≠ y := fun pr hpr => by
      by_cases h : pr.Contains x
      · simp only [rep, h, ite_true]
        exact hyx.symm
      · simp only [rep, h, ite_false]
        intro heq
        have hne : pr ≠ pr₀ := fun h' => h (h' ▸ hx0)
        have hdisj := hS.pairs_disjoint pr hpr pr₀ hpr₀ hne
        rcases hy0 with h1 | h1 <;> rw [← h1] at heq <;> tauto
    refine Valid.exists_affine_subspace_const_of_erased hS ha c hx hR b hout rep hrep hyp hrepy
      (fun g => (c ^^ pr₀.bias x) + ∑ j ∈ R.erase y, g j)
      (fun hg => isAffine_const_add_sum hg _ _) fun g hgrep => ?_
    have hrepx : rep pr₀ = x := by simp [rep, hx0]
    have hgx : Function.update g y ((c ^^ pr₀.bias x) + ∑ j ∈ R.erase y, g j) x = pr₀.bias x := by
      rw [Function.update_of_ne hyx.symm, ← hrepx]
      exact hgrep pr₀ hpr₀
    have hsum : ∑ j ∈ R.erase y, Function.update g y
        ((c ^^ pr₀.bias x) + ∑ j ∈ R.erase y, g j) j = ∑ j ∈ R.erase y, g j :=
      Finset.sum_congr rfl fun j hj => Function.update_of_ne (Finset.ne_of_mem_erase hj) _ _
    rw [← Finset.add_sum_erase R _ hyR, Function.update_self, hgx, hsum]
    cases c <;> cases pr₀.bias x <;> cases ∑ j ∈ R.erase y, g j <;> rfl
  · push Not at hcase
    let rep : ZeroPair → ℕ := fun pr => if pr.Contains x then pr.partner x else pr.fst
    have hrep : ∀ pr ∈ S.pairs, pr.Contains (rep pr) := fun pr _ => by
      by_cases h : pr.Contains x
      · simp only [rep, h, ite_true]
        exact pr.contains_partner h
      · simp only [rep, h, ite_false]
        exact Or.inl rfl
    have hrepx : ∀ pr ∈ S.pairs, rep pr ≠ x := fun pr hpr => by
      by_cases h : pr.Contains x
      · simp only [rep, h, ite_true]
        exact pr.partner_ne (hS.pair_mem pr hpr).2.2 h
      · simp only [rep, h, ite_false]
        intro heq
        exact h (Or.inl heq)
    refine Valid.exists_affine_subspace_const_of_erased hS ha c hx hR b hout rep hrep hx hrepx
      (fun g => c + ∑ j ∈ R, g j)
      (fun hg => isAffine_const_add_sum hg c R) fun g _ => by
        rw [Function.update_self]
        congr 1
        exact Finset.sum_congr rfl fun j hj =>
          (Function.update_of_ne (by rintro rfl; exact hxR hj) _ _).symm

/-- If `d < a`, the output of a valid state for an affine disperser for dimension `d` is not
constant on the consistent assignments in `Z(P)` satisfying one more affine equation
`x = c + ∑ j ∈ R, u j`. -/
theorem Valid.false_of_fix {f : BooleanFunction n} {d : ℕ} (hS : S.Valid f)
    (hf : IsAffineDisperser f d) (ha : d < S.a) {x : ℕ} (hx : x ∈ S.params) (c : Bool)
    (R : Finset ℕ) (hR : R ⊆ S.params) (hxR : x ∉ R) (b : Bool)
    (hout : ∀ val, S.Consistent val → S.Locus val → val x = c + ∑ j ∈ R, val j →
      S.out.eval val = b) : False := by
  obtain ⟨g, hg, hinj, hval⟩ := Valid.exists_affine_subspace_const_of_fix hS ha hx c R hR hxR b hout
  obtain ⟨u, v, huv⟩ := hf g hg hinj
  obtain ⟨val₁, hc₁, hl₁, ho₁, hg₁⟩ := hval u
  obtain ⟨val₂, hc₂, hl₂, ho₂, hg₂⟩ := hval v
  apply huv
  rw [hg₁, hg₂, ← hS.computes val₁ hc₁ hl₁, ← hS.computes val₂ hc₂ hl₂, ho₁, ho₂]

/-- If `d < a`, the output of a valid state for an affine disperser for dimension `d` is not an
affine function of the parameters on `Z(P)`. -/
theorem Valid.out_not_affine {f : BooleanFunction n} {d : ℕ} (hS : S.Valid f)
    (hf : IsAffineDisperser f d) (ha : d < S.a) (c : Bool) {T : Finset ℕ} (hT : T ⊆ S.params) :
    ¬ ∀ val, S.Consistent val → S.Locus val → S.out.eval val = c + ∑ j ∈ T, val j :=
  Valid.out_not_affine_of (fun hx c R hR hxR b hout =>
      Valid.false_of_fix hS hf ha hx c R hR hxR b hout)
    (Finset.nonempty_iff_ne_empty.2 fun h => by simp [a, m, h] at ha) c hT

end State

end Cslib.Circuits.Boolean.AffineDisperser4n
