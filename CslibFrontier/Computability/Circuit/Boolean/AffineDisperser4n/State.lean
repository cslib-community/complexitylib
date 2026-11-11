/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser.State
public import CslibFrontier.Computability.Circuit.Boolean.SemiCircuit
public import CslibFrontier.Foundations.Combinatorics.AffineDisperser.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Sort

/-!
# States of `4n - 10d` gate elimination with zero-locus pair semantics

A *state* of the `4n - 10d` gate elimination of [Mishra and Santhanam][MishraSanthanam2027] for a
Boolean function `f` on `n` bits consists of a fair semi-circuit reading parameters, a set of
disjoint *zero-locus pairs* `ZeroPair` of distinct parameters with biases, and an affine injective
parameter map `Φ` from parameter values to inputs of `f` such that the semi-circuit computes
`f ∘ Φ` on the zero locus `Z(P)` (`State.Valid`, `State.InZeroLocus`).

Each pair `pr = (p, α, r, β)` imposes the quadratic zero-locus constraint
`(u p ^^ α) && (u r ^^ β) = false`, equivalently `u p = α ∨ u r = β` (`ZeroPair.Holds`).
A state has `m` parameters, `q` pairs, effective affine dimension `a = m - q`, and size `s`
(gates plus equations). The *weight* of an unpaired parameter of degree `k` is `0` if `k = 0` and
`6` if `k ≥ 1` (`weight`), and the *potential* is

  `W = s + 4 q + 6 · #{used unpaired parameters}` (`State.W`).

By Lemma 2.2 (`State.Valid.exists_affine_embedding`), fixing one biased member of each pair yields
an injective affine map from `BitString a` into `Φ(Z(P))`. When `d < a`, the output is not
constant on any affine hyperplane of parameters within `Z(P)` (`State.Valid.false_of_fix`) and
therefore is not an affine function of the parameters (`State.Valid.out_not_affine`). Each step
of gate elimination (`State.Step`) preserves validity, decreases `m + s`, and satisfies
`ΔW ≤ 10 Δa`.

## Main definitions

* `Cslib.Circuits.Boolean.AffineDisperser4n.ZeroPair`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.ZeroPair.Holds`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.ZeroPair.Contains`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.ZeroPair.bias`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.ZeroPair.partner`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.ZeroPair.partnerBias`: zero-locus pairs and accessors.
* `Cslib.Circuits.Boolean.AffineDisperser4n.weight`: the `0/6` degree weight.
* `Cslib.Circuits.Boolean.AffineDisperser4n.State`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.State.Valid`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.State.InZeroLocus`: states, validity on `Z(P)`, and
  the zero locus.
* `Cslib.Circuits.Boolean.AffineDisperser4n.State.Paired`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.State.unpaired`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.State.wt`: paired and unpaired parameters and weights.
* `Cslib.Circuits.Boolean.AffineDisperser4n.State.m`, `State.q`, `State.a`, `State.s`, `State.W`:
  counted quantities and potential.
* `Cslib.Circuits.Boolean.AffineDisperser4n.State.Step`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.State.Preparation`: steps and preparatory operations.
* `Cslib.Circuits.Boolean.AffineDisperser4n.State.IsPartner`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.State.pairsAvoid`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.State.pairsMeeting`: partners and pair filters.

## Main results

* `Cslib.Circuits.Boolean.AffineDisperser4n.State.Valid.exists_affine_embedding`: Lemma 2.2,
  `a`-dimensional affine subspace in `Φ(Z(P))`.
* `Cslib.Circuits.Boolean.AffineDisperser4n.State.Valid.exists_affine_subspace_const_of_fix`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.State.Valid.false_of_fix`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.State.Valid.out_not_affine`: hyperplane and affinity
  lower-bound lemmas.
* `Cslib.Circuits.Boolean.AffineDisperser4n.State.W_add_le`: comparing potentials name by name.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 4n - O(log n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2027] (submission PDF inaccessible with HTTP 1042; cited
  labels and operation names follow issue `#4322` and are unverified against the manuscript)
-/

public section

namespace Cslib.Circuits.Boolean.AffineDisperser4n

open Finset Cslib.BitString SemiCircuit

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

theorem contains_partner {pr : ZeroPair} {x : ℕ} (hx : pr.Contains x) :
    pr.Contains (pr.partner x) := by
  rcases hx with h | h <;> unfold Contains partner <;> split_ifs <;> tauto

theorem partner_ne {pr : ZeroPair} {x : ℕ} (hne : pr.fst ≠ pr.snd) (hx : pr.Contains x) :
    pr.partner x ≠ x := by
  rcases hx with h | h <;> unfold partner <;> split_ifs <;> intro he <;> simp_all

theorem partner_partner {pr : ZeroPair} {x : ℕ} (hne : pr.fst ≠ pr.snd) (hx : pr.Contains x) :
    pr.partner (pr.partner x) = x := by
  unfold partner
  rcases hx with h | h <;> split_ifs <;> simp_all

theorem bias_partner {pr : ZeroPair} {x : ℕ} (hne : pr.fst ≠ pr.snd) (hx : pr.Contains x) :
    pr.bias (pr.partner x) = pr.partnerBias x := by
  unfold bias partner partnerBias
  rcases hx with h | h <;> split_ifs <;> simp_all

theorem holds_iff_contains {pr : ZeroPair} {x : ℕ} (hx : pr.Contains x) (val : ℕ → Bool) :
    pr.Holds val ↔ val x = pr.bias x ∨ val (pr.partner x) = pr.partnerBias x := by
  unfold Holds bias partner partnerBias
  rcases hx with rfl | rfl
  · simp
  · by_cases h : pr.fst = pr.snd
    · simp [h]
    · simp [h, or_comm]

theorem holds_of_eq_bias {pr : ZeroPair} {x : ℕ} (hx : pr.Contains x) {val : ℕ → Bool}
    (h : val x = pr.bias x) : pr.Holds val :=
  (holds_iff_contains hx val).2 (Or.inl h)

theorem holds_of_eq_partnerBias {pr : ZeroPair} {x : ℕ} (hx : pr.Contains x) {val : ℕ → Bool}
    (h : val (pr.partner x) = pr.partnerBias x) : pr.Holds val :=
  (holds_iff_contains hx val).2 (Or.inr h)

theorem holds_of_eq_xor {pr : ZeroPair} {x : ℕ} (hx : pr.Contains x) {val : ℕ → Bool}
    (h : val x = (val (pr.partner x) ^^ !(pr.bias x ^^ pr.partnerBias x))) : pr.Holds val := by
  rw [holds_iff_contains hx, h]
  generalize val (pr.partner x) = v
  generalize pr.bias x = a
  generalize pr.partnerBias x = b
  revert v a b
  decide

end ZeroPair

/-! ### States and validity -/

/-- A state of `4n - 10d` gate elimination for a Boolean function on `n` bits: a semi-circuit,
disjoint zero-locus pairs of parameters, and an affine parameter map `Φ`. -/
structure State (n : ℕ) extends SemiCircuit where
  /-- The zero-locus pairs constraining parameter assignments to `Z(P)`. -/
  pairs : Finset ZeroPair
  /-- The affine parameter map, as a function of all internal values. -/
  phi : (ℕ → Bool) → BitString n

namespace State

variable {n : ℕ} (S : State n)

/-- An assignment lies in the zero locus `Z(P)` when every pair in `S.pairs` holds. -/
@[expose] def InZeroLocus (val : ℕ → Bool) : Prop :=
  ∀ pr ∈ S.pairs, pr.Holds val

/-- Decidability of `State.InZeroLocus`. -/
instance (val : ℕ → Bool) : Decidable (S.InZeroLocus val) :=
  inferInstanceAs (Decidable (∀ pr ∈ S.pairs, _))

/-- `x` belongs to one of the pairs. -/
@[expose] def Paired (x : ℕ) : Prop :=
  ∃ pr ∈ S.pairs, pr.Contains x

/-- Decidability of `State.Paired`. -/
instance : DecidablePred S.Paired :=
  fun _ => inferInstanceAs (Decidable (∃ pr ∈ S.pairs, _))

/-- The unpaired parameters. -/
@[expose] def unpaired : Finset ℕ :=
  S.params.filter fun x => ¬ S.Paired x

/-- The number of parameters. -/
@[expose] def m : ℕ :=
  S.params.card

/-- The number of pairs. -/
@[expose] def q : ℕ :=
  S.pairs.card

/-- The effective affine dimension `a = m - q`. -/
@[expose] def a : ℕ :=
  S.m - S.q

/-- The size of the semi-circuit: gates plus equations. -/
@[expose] def s : ℕ :=
  S.size

/-- The potential `W = s + 4 q + ∑ wt(x)` over the unpaired parameters `x`, where
`wt(x) = 6` if `deg x ≥ 1` and `0` if `deg x = 0`. -/
@[expose] def W : ℕ :=
  S.s + 4 * S.q + ∑ x ∈ S.unpaired, weight (S.deg x)

/-- A valid state for `f`: a well-formed fair semi-circuit, disjoint pairs of distinct
parameters, and an affine parameter map depending only on and injective on the parameters, such
that the output of every consistent assignment in `Z(P)` equals `f` at its image. -/
structure Valid (f : BooleanFunction n) : Prop where
  /-- The semi-circuit is well formed. -/
  wf : S.WellFormed
  /-- Pairs consist of two distinct parameters. -/
  pair_mem : ∀ pr ∈ S.pairs, pr.fst ∈ S.params ∧ pr.snd ∈ S.params ∧ pr.fst ≠ pr.snd
  /-- Distinct pairs are disjoint. -/
  pairs_disjoint : ∀ pr ∈ S.pairs, ∀ pr' ∈ S.pairs, pr ≠ pr' →
    pr.fst ≠ pr'.fst ∧ pr.fst ≠ pr'.snd ∧ pr.snd ≠ pr'.fst ∧ pr.snd ≠ pr'.snd
  /-- The parameter map depends only on the parameters. -/
  phi_congr : ∀ val val', (∀ j ∈ S.params, val j = val' j) → S.phi val = S.phi val'
  /-- The parameter map is globally affine. -/
  phi_affine : IsAffine S.phi
  /-- The parameter map is injective on the parameters. -/
  phi_injective : ∀ val val', S.phi val = S.phi val' → ∀ j ∈ S.params, val j = val' j
  /-- Every consistent assignment in `Z(P)` outputs `f` at its image. -/
  computes : ∀ val, S.Consistent val → S.InZeroLocus val → S.out.eval val = f (S.phi val)

/-! ### Affine embedding helpers -/

/-- Adding a fixed offset assignment preserves affinity of a family. -/
private theorem isAffine_xor_const {k : ℕ} {σ : BitString k → ℕ → Bool} (hσ : IsAffine σ)
    (base : ℕ → Bool) : IsAffine fun u i => σ u i ^^ base i := by
  intro u v w
  funext i
  have h := congrFun (hσ u v w) i
  simp only [Pi.add_apply] at h ⊢
  rw [h]
  generalize σ u i = a
  generalize σ v i = b
  generalize σ w i = c
  generalize base i = d
  revert a b c d
  decide

variable {S}

/-! ### Lemma 2.2 and hyperplane lemmas -/

/-- Choosing one representative member `rep pr` of every pair leaves exactly `a` other
parameters. -/
theorem Valid.card_sdiff_image {f : BooleanFunction n} (hS : S.Valid f) (rep : ZeroPair → ℕ)
    (hrep : ∀ pr ∈ S.pairs, pr.Contains (rep pr)) :
    (S.params \ S.pairs.image rep).card = S.a := by
  have hsub : S.pairs.image rep ⊆ S.params := by
    intro i hi
    obtain ⟨pr, hpr, rfl⟩ := Finset.mem_image.1 hi
    rcases hrep pr hpr with h | h <;> rw [← h]
    · exact (hS.pair_mem pr hpr).1
    · exact (hS.pair_mem pr hpr).2.1
  have hinj : Set.InjOn rep S.pairs := by
    intro pr hpr pr' hpr' heq
    by_contra hne
    have := hS.pairs_disjoint pr hpr pr' hpr' hne
    rcases hrep pr hpr with h | h <;> rcases hrep pr' hpr' with h' | h' <;>
      rw [← h, ← h'] at heq <;> tauto
  rw [Finset.card_sdiff_of_subset hsub, Finset.card_image_of_injOn hinj]
  rfl

/-- Fixing every chosen pair representative `rep pr` to its bias in `pr` gives a base
assignment `base` such that `spread F hF u ^^ base` lies in `Z(P)`. -/
private def locusAssign (S : State n) (rep : ZeroPair → ℕ)
    (F : Finset ℕ) {k : ℕ} (hF : F.card = k) (u : BitString k) (i : ℕ) : Bool :=
  AffineDisperser.State.spread F hF u i ^^
    ∑ pr ∈ S.pairs, if rep pr = i then pr.bias (rep pr) else false

private theorem isAffine_locusAssign (S : State n) (rep : ZeroPair → ℕ)
    (F : Finset ℕ) {k : ℕ} (hF : F.card = k) :
    IsAffine (locusAssign S rep F hF) :=
  isAffine_xor_const (AffineDisperser.State.isAffine_spread F hF) _

private theorem locusAssign_of_mem {rep : ZeroPair → ℕ} {F : Finset ℕ} {k : ℕ} (hF : F.card = k)
    (hFdisj : ∀ pr ∈ S.pairs, rep pr ∉ F) (u : BitString k) {i : ℕ} (hi : i ∈ F) :
    locusAssign S rep F hF u i = AffineDisperser.State.spread F hF u i := by
  unfold locusAssign
  have hzero : ∑ pr ∈ S.pairs, (if rep pr = i then pr.bias (rep pr) else false) = false := by
    refine Finset.sum_eq_zero fun pr hpr => ?_
    have hne : rep pr ≠ i := fun h => hFdisj pr hpr (h ▸ hi)
    rw [ite_eq_right hne]
    rfl
  rw [hzero, Bool.xor_false]

private theorem locusAssign_rep {f : BooleanFunction n} (hS : S.Valid f)
    {rep : ZeroPair → ℕ} (hrep : ∀ pr ∈ S.pairs, pr.Contains (rep pr))
    {F : Finset ℕ} {k : ℕ} (hF : F.card = k)
    (hFdisj : ∀ pr ∈ S.pairs, rep pr ∉ F) (u : BitString k)
    {pr : ZeroPair} (hpr : pr ∈ S.pairs) :
    locusAssign S rep F hF u (rep pr) = pr.bias (rep pr) := by
  unfold locusAssign
  rw [AffineDisperser.State.spread_of_notMem hF u (hFdisj pr hpr), Bool.false_xor]
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
      ∀ u, ∃ val, S.Consistent val ∧ S.InZeroLocus val ∧ g u = S.phi val := by
  set rep : ZeroPair → ℕ := ZeroPair.fst
  have hrep : ∀ pr ∈ S.pairs, pr.Contains (rep pr) := fun _ _ => Or.inl rfl
  set F := S.params \ S.pairs.image rep
  have hF : F.card = S.a := hS.card_sdiff_image rep hrep
  have hFp : F ⊆ S.params := Finset.sdiff_subset
  have hFdisj : ∀ pr ∈ S.pairs, rep pr ∉ F := fun pr hpr h =>
    (Finset.mem_sdiff.1 h).2 (Finset.mem_image_of_mem _ hpr)
  let σ := locusAssign S rep F hF
  refine ⟨S.phi ∘ σ, hS.phi_affine.comp (isAffine_locusAssign S rep F hF), ?_, fun u => ?_⟩
  · intro u v huv
    refine AffineDisperser.State.eq_of_spread hF fun i hi => ?_
    have hi' := hS.phi_injective _ _ huv i (hFp hi)
    dsimp only [σ] at hi'
    rwa [locusAssign_of_mem hF hFdisj u hi, locusAssign_of_mem hF hFdisj v hi] at hi'
  · obtain ⟨val, hval, hcons⟩ := hS.wf.exists_consistent (σ u)
    refine ⟨val, hcons, fun pr hpr => ?_, (hS.phi_congr val _ hval).symm⟩
    exact ZeroPair.holds_of_eq_bias (hrep pr hpr)
      (by rw [hval _ (by rcases hrep pr hpr with h | h <;> rw [← h] <;>
            [exact (hS.pair_mem pr hpr).1; exact (hS.pair_mem pr hpr).2.1])]
          exact locusAssign_rep hS hrep hF hFdisj u hpr)

/-- Along an injective affine family of parameter assignments lying in `Z(P)`, if the output is
constant `b` on consistent assignments in the family and `d ≤ k`, then there is an injective
affine map `BitString d → BitString n` into `Φ(Z(P))` whose consistent lifts all evaluate to `b`. -/
private theorem Valid.exists_affine_subspace_const_of_family {f : BooleanFunction n} {d k : ℕ}
    (hS : S.Valid f) (σ : BitString k → ℕ → Bool) (hσ : IsAffine σ)
    (hlocus : ∀ u, S.InZeroLocus (σ u))
    (hinj : ∀ u v, (∀ j ∈ S.params, σ u j = σ v j) → u = v) (hk : d ≤ k)
    {b : Bool} (hout : ∀ u val, S.Consistent val → (∀ j ∈ S.params, val j = σ u j) →
      S.out.eval val = b) :
    ∃ g : BitString d → BitString n, IsAffine g ∧ Function.Injective g ∧
      ∀ u, ∃ val, S.Consistent val ∧ S.InZeroLocus val ∧ S.out.eval val = b ∧
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
    ∃ val val', S.Consistent val ∧ S.InZeroLocus val ∧ S.Consistent val' ∧ S.InZeroLocus val' ∧
      S.out.eval val ≠ S.out.eval val' := by
  obtain ⟨g, hg, hinj, hval⟩ := hS.exists_affine_embedding
  obtain ⟨u, v, huv⟩ := hf.mono ha g hg hinj
  obtain ⟨val, hc, hl, hg1⟩ := hval u
  obtain ⟨val', hc', hl', hg2⟩ := hval v
  refine ⟨val, val', hc, hl, hc', hl', ?_⟩
  rw [hS.computes val hc hl, hS.computes val' hc' hl', ← hg1, ← hg2]
  exact huv

private theorem Valid.exists_affine_subspace_const_of_erased {n d : ℕ} {S : State n}
    {f : BooleanFunction n} (hS : S.Valid f) (ha : d < S.a) (c : Bool) {x : ℕ}
    (hx : x ∈ S.params) {R : Finset ℕ} (hR : R ⊆ S.params) (b : Bool)
    (hout : ∀ val, S.Consistent val → S.InZeroLocus val → val x = c + ∑ j ∈ R, val j →
      S.out.eval val = b)
    (rep : ZeroPair → ℕ) (hrep : ∀ pr ∈ S.pairs, pr.Contains (rep pr))
    {z : ℕ} (hzp : z ∈ S.params) (hrepz : ∀ pr ∈ S.pairs, rep pr ≠ z)
    (rhs : (ℕ → Bool) → Bool)
    (hrhs_aff : ∀ {g : BitString (S.a - 1) → ℕ → Bool}, IsAffine g →
      IsAffine fun u => rhs (g u))
    (hrhs_eq : ∀ g : ℕ → Bool, (∀ pr ∈ S.pairs, g (rep pr) = pr.bias (rep pr)) →
      Function.update g z (rhs g) x = c + ∑ j ∈ R, Function.update g z (rhs g) j) :
    ∃ g : BitString d → BitString n, IsAffine g ∧ Function.Injective g ∧
      ∀ u, ∃ val, S.Consistent val ∧ S.InZeroLocus val ∧ S.out.eval val = b ∧
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
  let base := locusAssign S rep F' hF'
  have hbase_rep : ∀ u pr, pr ∈ S.pairs → base u (rep pr) = pr.bias (rep pr) := fun u pr hpr =>
    locusAssign_rep hS hrep hF' hF'disj u hpr
  let σ : BitString (S.a - 1) → ℕ → Bool := fun u => Function.update (base u) z (rhs (base u))
  have hσaff : IsAffine σ :=
    AffineDisperser.State.isAffine_update (isAffine_locusAssign S rep F' hF') z
      (hrhs_aff (isAffine_locusAssign S rep F' hF'))
  have hlocus : ∀ u pr, pr ∈ S.pairs → pr.Holds (σ u) := fun u pr hpr =>
    ZeroPair.holds_of_eq_bias (hrep pr hpr) (by
      dsimp only [σ]
      rw [Function.update_of_ne (hrepz pr hpr)]
      exact hbase_rep u pr hpr)
  refine hS.exists_affine_subspace_const_of_family σ hσaff hlocus
    (fun u v h => AffineDisperser.State.eq_of_spread hF' fun i hi => ?_) (by omega)
    fun u val hcons hval => ?_
  · have hi' := h i (hF'p hi)
    have hiz : i ≠ z := Finset.ne_of_mem_erase hi
    dsimp only [σ, base] at hi'
    rw [Function.update_of_ne hiz, Function.update_of_ne hiz,
      locusAssign_of_mem hF' hF'disj u hi,
      locusAssign_of_mem hF' hF'disj v hi] at hi'
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
    (hout : ∀ val, S.Consistent val → S.InZeroLocus val → val x = c + ∑ j ∈ R, val j →
      S.out.eval val = b) :
    ∃ g : BitString d → BitString n, IsAffine g ∧ Function.Injective g ∧
      ∀ u, ∃ val, S.Consistent val ∧ S.InZeroLocus val ∧ S.out.eval val = b ∧
        g u = S.phi val := by
  classical
  -- If `x` is paired with partner `y` and `y ∈ R`, fix `x` to its bias and solve for `y` instead.
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
    refine hS.exists_affine_subspace_const_of_erased ha c hx hR b hout rep hrep hyp hrepy
      (fun g => (c ^^ pr₀.bias x) + ∑ j ∈ R.erase y, g j)
      (fun hg => AffineDisperser.State.isAffine_const_add_sum hg _ _) fun g hgrep => ?_
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
    refine hS.exists_affine_subspace_const_of_erased ha c hx hR b hout rep hrep hx hrepx
      (fun g => c + ∑ j ∈ R, g j)
      (fun hg => AffineDisperser.State.isAffine_const_add_sum hg c R) fun g _ => by
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
    (hout : ∀ val, S.Consistent val → S.InZeroLocus val → val x = c + ∑ j ∈ R, val j →
      S.out.eval val = b) : False := by
  obtain ⟨g, hg, hinj, hval⟩ := hS.exists_affine_subspace_const_of_fix ha hx c R hR hxR b hout
  obtain ⟨u, v, huv⟩ := hf g hg hinj
  obtain ⟨val₁, hc₁, hl₁, ho₁, hg₁⟩ := hval u
  obtain ⟨val₂, hc₂, hl₂, ho₂, hg₂⟩ := hval v
  apply huv
  rw [hg₁, hg₂, ← hS.computes val₁ hc₁ hl₁, ← hS.computes val₂ hc₂ hl₂, ho₁, ho₂]

/-- If `d < a`, the output of a valid state for an affine disperser for dimension `d` is not an
affine function of the parameters on `Z(P)`. -/
theorem Valid.out_not_affine {f : BooleanFunction n} {d : ℕ} (hS : S.Valid f)
    (hf : IsAffineDisperser f d) (ha : d < S.a) (c : Bool) {T : Finset ℕ} (hT : T ⊆ S.params) :
    ¬ ∀ val, S.Consistent val → S.InZeroLocus val → S.out.eval val = c + ∑ j ∈ T, val j := by
  intro hout
  rcases T.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · obtain ⟨x, hx⟩ : S.params.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      rintro h
      simp [a, m, h] at ha
    exact hS.false_of_fix hf ha hx false ∅ (Finset.empty_subset _) (Finset.notMem_empty _) c
      fun val hval hlocus _ => by simpa using hout val hval hlocus
  · refine hS.false_of_fix hf ha (hT hx) c (T.erase x) ((Finset.erase_subset _ _).trans hT)
      (Finset.notMem_erase _ _) false fun val hval hlocus hfix => ?_
    rw [hout val hval hlocus, ← Finset.add_sum_erase T _ hx, hfix]
    generalize ∑ j ∈ T.erase x, val j = e
    cases c <;> cases e <;> rfl

/-! ### Bookkeeping for the potential -/

variable {f : BooleanFunction n}

/-- The weight contributed by the name `x`: `6` if it is a used unpaired parameter, and `0`
otherwise. -/
@[expose] def wt (S : State n) (x : ℕ) : ℕ :=
  if x ∈ S.unpaired then weight (S.deg x) else 0

/-- The weight `S.wt x` of any name `x` is at most `6`. -/
theorem wt_le_six (S : State n) (x : ℕ) : S.wt x ≤ 6 := by
  unfold wt
  split_ifs
  · exact weight_le_six _
  · omega

/-- A name `x` belongs to `S.unpaired` iff it is an unpaired parameter of `S`. -/
theorem mem_unpaired {S : State n} {x : ℕ} : x ∈ S.unpaired ↔ x ∈ S.params ∧ ¬ S.Paired x := by
  simp [unpaired]

/-- For an unpaired parameter `x`, `S.wt x` is `weight (S.deg x)`. -/
theorem wt_of_mem {S : State n} {x : ℕ} (hx : x ∈ S.unpaired) : S.wt x = weight (S.deg x) := by
  simp [wt, hx]

/-- For a name `x` outside `S.unpaired`, `S.wt x = 0`. -/
theorem wt_of_notMem {S : State n} {x : ℕ} (hx : x ∉ S.unpaired) : S.wt x = 0 := by
  simp [wt, hx]

/-- A paired parameter contributes weight `0`. -/
theorem wt_of_paired {S : State n} {x : ℕ} (hx : S.Paired x) : S.wt x = 0 :=
  wt_of_notMem fun h => (mem_unpaired.1 h).2 hx

/-- A name outside `S.params` contributes weight `0`. -/
theorem wt_of_notMem_params {S : State n} {x : ℕ} (hx : x ∉ S.params) : S.wt x = 0 :=
  wt_of_notMem fun h => hx (mem_unpaired.1 h).1

/-- Summing `S.wt` over any superset `N` of `S.params` equals the sum of `weight (S.deg x)` over
`S.unpaired`. -/
theorem sum_wt (S : State n) {N : Finset ℕ} (hN : S.params ⊆ N) :
    ∑ x ∈ N, S.wt x = ∑ x ∈ S.unpaired, weight (S.deg x) := by
  have hU : S.unpaired ⊆ N := (Finset.filter_subset _ _).trans hN
  unfold wt
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 hU]

/-- Expressing the potential `S.W` with the weight sum taken over any superset `N` of
`S.params`. -/
theorem W_eq_sum (S : State n) {N : Finset ℕ} (hN : S.params ⊆ N) :
    S.W = S.s + 4 * S.q + ∑ x ∈ N, S.wt x := by
  rw [sum_wt S hN]
  rfl

/-- Potentials compare name by name: if every name of a common set loses `loss x` and gains at
most `gain x` in weight, the sums of losses and gains bound the change of potential. -/
theorem W_add_le {S S' : State n} {N : Finset ℕ} (hN : S.params ⊆ N) (hN' : S'.params ⊆ N)
    (loss gain : ℕ → ℕ) (h : ∀ x ∈ N, S'.wt x + loss x ≤ S.wt x + gain x) :
    S'.W + S.s + 4 * S.q + ∑ x ∈ N, loss x ≤
      S.W + S'.s + 4 * S'.q + ∑ x ∈ N, gain x := by
  rw [W_eq_sum S hN, W_eq_sum S' hN']
  have := Finset.sum_le_sum h
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at this
  omega

/-- A step of gate elimination from `S` to `S'`: `S'` is valid, `m + s` decreases,
`Δa ∈ {0, -1, -2}`, and `ΔW ≤ 10 Δa`, written without subtraction. -/
structure Step (f : BooleanFunction n) (S S' : State n) : Prop where
  /-- The new state is valid. -/
  valid : S'.Valid f
  /-- `m + s` decreases. -/
  lt : S'.m + S'.s < S.m + S.s
  /-- `a` does not increase. -/
  a_le : S'.a ≤ S.a
  /-- `a` decreases by at most two. -/
  le_a : S.a ≤ S'.a + 2
  /-- `ΔW ≤ 10 Δa`. -/
  potential : S'.W + 10 * S.a ≤ S.W + 10 * S'.a

/-- A preparatory operation of gate elimination from `S` to `S'`: `S'` is valid, with the same
`m`, `s` and `q` as `S` and no larger potential. -/
structure Preparation (f : BooleanFunction n) (S S' : State n) : Prop where
  /-- The new state is valid. -/
  valid : S'.Valid f
  /-- The number of parameters is kept. -/
  m_eq : S'.m = S.m
  /-- The size is kept. -/
  s_eq : S'.s = S.s
  /-- The number of pairs is kept. -/
  q_eq : S'.q = S.q
  /-- The potential does not increase. -/
  W_le : S'.W ≤ S.W

/-- A preparatory operation preserves `a = m - q`. -/
theorem Preparation.a_eq {S S' : State n} (h : Preparation f S S') : S'.a = S.a := by
  simp only [a, h.m_eq, h.q_eq]

/-- A preparatory operation followed by a step is a step. -/
theorem Step.of_preparation {S S₁ S' : State n} (hp : Preparation f S S₁) (h : Step f S₁ S') :
    Step f S S' := by
  obtain ⟨hS', hlt, ha₁, ha₂, hW'⟩ := h
  have := hp.a_eq
  have := hp.m_eq
  have := hp.s_eq
  have := hp.W_le
  exact ⟨hS', by omega, by omega, by omega, by omega⟩

/-! ### Pairs and partners -/

/-- `r` is the partner of `w`: they form a pair. -/
@[expose] def IsPartner (S : State n) (w r : ℕ) : Prop :=
  ∃ pr ∈ S.pairs, (pr.fst = w ∧ pr.snd = r) ∨ (pr.snd = w ∧ pr.fst = r)

/-- Decidability of `State.IsPartner`. -/
instance (S : State n) (w : ℕ) : DecidablePred (S.IsPartner w) :=
  fun _ => inferInstanceAs (Decidable (∃ pr ∈ S.pairs, _))

/-- The pairs avoiding `w`. -/
@[expose] def pairsAvoid (S : State n) (w : ℕ) : Finset ZeroPair :=
  S.pairs.filter fun pr => ¬ pr.Contains w

/-- The pairs with a member in `F`. -/
@[expose] def pairsMeeting (S : State n) (F : Finset ℕ) : Finset ZeroPair :=
  S.pairs.filter fun pr => pr.fst ∈ F ∨ pr.snd ∈ F

/-- Two states with the same pairs have the same paired names. -/
theorem paired_congr {S S' : State n} (h : S'.pairs = S.pairs) {x : ℕ} :
    S'.Paired x ↔ S.Paired x := by
  unfold Paired
  rw [h]

/-- Two states with the same parameters and pairs have the same unpaired parameters. -/
theorem unpaired_congr {S S' : State n} (hp : S'.params = S.params) (h : S'.pairs = S.pairs) :
    S'.unpaired = S.unpaired := by
  ext x
  rw [mem_unpaired, mem_unpaired, hp, paired_congr h]

/-- Every paired name of a valid state is a parameter. -/
theorem Valid.mem_params_of_paired {S : State n} (hS : S.Valid f) {p : ℕ} (hp : S.Paired p) :
    p ∈ S.params := by
  obtain ⟨pr, hpr, h | h⟩ := hp
  · rw [← h]; exact (hS.pair_mem pr hpr).1
  · rw [← h]; exact (hS.pair_mem pr hpr).2.1

/-- A pair containing `w` is unique. -/
theorem Valid.pair_unique {S : State n} (hS : S.Valid f) {w : ℕ} {pr pr' : ZeroPair}
    (hpr : pr ∈ S.pairs) (hpr' : pr' ∈ S.pairs) (h : pr.Contains w) (h' : pr'.Contains w) :
    pr = pr' := by
  by_contra hne
  have := hS.pairs_disjoint pr hpr pr' hpr' hne
  rcases h with rfl | rfl <;> rcases h' with h' | h' <;> tauto

/-- Every paired parameter has a partner. -/
theorem exists_partner {S : State n} {p : ℕ} (hp : S.Paired p) : ∃ r, S.IsPartner p r := by
  obtain ⟨pr, hpr, h | h⟩ := hp
  · exact ⟨pr.snd, pr, hpr, Or.inl ⟨h, rfl⟩⟩
  · exact ⟨pr.fst, pr, hpr, Or.inr ⟨h, rfl⟩⟩

/-- Every paired parameter belongs to a pair `pr ∈ S.pairs` with `pr.Contains p` and
`pr.partner p` as its partner. -/
theorem Valid.exists_pair_of_paired {S : State n} (hS : S.Valid f) {p : ℕ} (hp : S.Paired p) :
    ∃ pr ∈ S.pairs, pr.Contains p ∧ S.IsPartner p (pr.partner p) := by
  obtain ⟨pr, hpr, h⟩ := hp
  refine ⟨pr, hpr, h, pr, hpr, ?_⟩
  rcases h with rfl | rfl
  · exact Or.inl ⟨rfl, by simp [ZeroPair.partner]⟩
  · by_cases h' : pr.fst = pr.snd
    · exact absurd h' (hS.pair_mem pr hpr).2.2
    · exact Or.inr ⟨rfl, by simp [ZeroPair.partner, h']⟩

/-- The partner relation `State.IsPartner` is symmetric. -/
theorem IsPartner.symm {S : State n} {p r : ℕ} (h : S.IsPartner p r) : S.IsPartner r p := by
  obtain ⟨pr, hpr, h⟩ := h
  exact ⟨pr, hpr, by tauto⟩

/-- A parameter that has a partner is paired. -/
theorem IsPartner.paired {S : State n} {w r : ℕ} (h : S.IsPartner w r) : S.Paired w := by
  obtain ⟨pr, hpr, ⟨h1, -⟩ | ⟨h1, -⟩⟩ := h
  · exact ⟨pr, hpr, Or.inl h1⟩
  · exact ⟨pr, hpr, Or.inr h1⟩

/-- In a valid state, a parameter is distinct from its partner. -/
theorem Valid.partner_ne {S : State n} (hS : S.Valid f) {p r : ℕ} (h : S.IsPartner p r) :
    r ≠ p := by
  obtain ⟨pr, hpr, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := h
  · rw [← h1, ← h2]; exact (hS.pair_mem pr hpr).2.2.symm
  · rw [← h1, ← h2]; exact (hS.pair_mem pr hpr).2.2

/-- In a valid state, the partner of a parameter is a parameter. -/
theorem Valid.partner_mem {S : State n} (hS : S.Valid f) {p r : ℕ} (h : S.IsPartner p r) :
    r ∈ S.params :=
  hS.mem_params_of_paired h.symm.paired

/-- A partner is unique. -/
theorem Valid.isPartner_unique {S : State n} (hS : S.Valid f) {w r r' : ℕ}
    (h : S.IsPartner w r) (h' : S.IsPartner w r') : r = r' := by
  obtain ⟨pr, hpr, hr⟩ := h
  obtain ⟨pr', hpr', hr'⟩ := h'
  have := hS.pair_unique (w := w) hpr hpr'
    (by rcases hr with h | h; exacts [Or.inl h.1, Or.inr h.1])
    (by rcases hr' with h | h; exacts [Or.inl h.1, Or.inr h.1])
  subst this
  have h12 := (hS.pair_mem pr hpr).2.2
  rcases hr with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hr' with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
  · exact h2.symm.trans h2'
  · exact absurd (h1.trans h1'.symm) h12
  · exact absurd (h1'.trans h1.symm) h12
  · exact h2.symm.trans h2'

/-- The partners of `w` contribute at most one summand. -/
theorem Valid.sum_partner_le {S : State n} (hS : S.Valid f) (w : ℕ) (N : Finset ℕ) (c : ℕ) :
    ∑ x ∈ N, (if S.IsPartner w x then c else 0) ≤ c := by
  classical
  by_cases h : ∃ r ∈ N, S.IsPartner w r
  · obtain ⟨r, hr, hpr⟩ := h
    rw [Finset.sum_eq_single_of_mem r hr fun x _ hxr => ite_eq_right fun hx =>
      hxr (hS.isPartner_unique hx hpr), ite_eq_left hpr]
  · push Not at h
    rw [Finset.sum_eq_zero fun x hx => ite_eq_right (h x hx)]
    omega

/-- A paired parameter outside `F` is in a pair meeting `F` exactly when its partner is in
`F`. -/
theorem Valid.paired_filter_iff {S : State n} (hS : S.Valid f) {F : Finset ℕ} {u : ℕ}
    (huF : u ∉ F) : (∃ pr ∈ S.pairs.filter (fun pr => ¬ (pr.fst ∈ F ∨ pr.snd ∈ F)),
      pr.Contains u) ↔ S.Paired u ∧ ∀ x ∈ F, ¬ S.IsPartner u x := by
  constructor
  · rintro ⟨pr, hpr, hu⟩
    obtain ⟨hpr, hF⟩ := Finset.mem_filter.1 hpr
    refine ⟨⟨pr, hpr, hu⟩, fun x hx ⟨pr', hpr', hux⟩ => hF ?_⟩
    have := hS.pair_unique hpr hpr' hu (by rcases hux with h | h; exacts [Or.inl h.1, Or.inr h.1])
    subst this
    rcases hux with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inr (h ▸ hx)
    · exact Or.inl (h ▸ hx)
  · rintro ⟨⟨pr, hpr, hu⟩, hpart⟩
    refine ⟨pr, Finset.mem_filter.2 ⟨hpr, ?_⟩, hu⟩
    rintro (h | h) <;> rcases hu with hu | hu
    · exact huF (hu ▸ h)
    · exact hpart _ h ⟨pr, hpr, Or.inr ⟨hu, rfl⟩⟩
    · exact hpart _ h ⟨pr, hpr, Or.inl ⟨hu, rfl⟩⟩
    · exact huF (hu ▸ h)

/-- The parameters of a valid state are at least as many as its pairs. -/
theorem Valid.q_le_m {S : State n} (hS : S.Valid f) : S.q ≤ S.m := by
  have hsub : S.pairs.image ZeroPair.fst ⊆ S.params := fun i hi => by
    obtain ⟨pr, hpr, rfl⟩ := Finset.mem_image.1 hi
    exact (hS.pair_mem pr hpr).1
  have hinj : Set.InjOn ZeroPair.fst (S.pairs : Set ZeroPair) := fun pr hpr pr' hpr' h =>
    hS.pair_unique hpr hpr' (Or.inl rfl) (Or.inl h.symm)
  have := Finset.card_le_card hsub
  rwa [Finset.card_image_of_injOn hinj] at this

/-- At most `|F|` pairs meet a set `F` of parameters. -/
theorem Valid.card_pairsMeeting_le {S : State n} (hS : S.Valid f) (F : Finset ℕ) :
    (S.pairsMeeting F).card ≤ F.card := by
  classical
  refine Finset.card_le_card_of_injOn (fun pr => if pr.fst ∈ F then pr.fst else pr.snd)
    (fun pr hpr => ?_) (fun pr hpr pr' hpr' h => ?_)
  · obtain ⟨-, h⟩ := Finset.mem_filter.1 hpr
    by_cases h1 : pr.fst ∈ F
    · simp only [ite_eq_left h1]; exact h1
    · simp only [ite_eq_right h1]; exact h.resolve_left h1
  · obtain ⟨hpr, -⟩ := Finset.mem_filter.1 hpr
    obtain ⟨hpr', -⟩ := Finset.mem_filter.1 hpr'
    simp only at h
    refine hS.pair_unique hpr hpr' (w := if pr.fst ∈ F then pr.fst else pr.snd)
      (by split_ifs <;> simp [ZeroPair.Contains]) ?_
    rw [h]; split_ifs <;> simp [ZeroPair.Contains]

/-- The number of pairs meeting `{w}` is `1` if `w` is paired and `0` otherwise. -/
theorem Valid.card_pairsMeeting_singleton {S : State n} (hS : S.Valid f) (w : ℕ) :
    (S.pairsMeeting {w}).card = if S.Paired w then 1 else 0 := by
  split_ifs with hw
  · obtain ⟨pr, hpr, hprw⟩ := hw
    rw [Finset.card_eq_one]
    refine ⟨pr, Finset.eq_singleton_iff_unique_mem.2 ⟨Finset.mem_filter.2 ⟨hpr, by simpa⟩,
      fun pr' hpr' => ?_⟩⟩
    obtain ⟨hpr', h⟩ := Finset.mem_filter.1 hpr'
    exact hS.pair_unique hpr' hpr (by simpa [ZeroPair.Contains] using h) hprw
  · refine Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun pr hpr h => hw ?_)
    exact ⟨pr, hpr, by simpa [ZeroPair.Contains, eq_comm] using h⟩

/-- Adding to `F` a parameter that is not the partner of a member of `F` adds its pair, if
any. -/
theorem Valid.card_pairsMeeting_insert {S : State n} (hS : S.Valid f) {F : Finset ℕ} {x : ℕ}
    (hx : x ∉ F) (hpart : ∀ y ∈ F, ¬ S.IsPartner x y) :
    (S.pairsMeeting (insert x F)).card =
      (S.pairsMeeting F).card + if S.Paired x then 1 else 0 := by
  rw [← hS.card_pairsMeeting_singleton x, ← Finset.card_union_of_disjoint]
  · congr 1
    ext pr
    simp only [pairsMeeting, Finset.mem_union, Finset.mem_filter, Finset.mem_insert,
      Finset.mem_singleton]
    tauto
  · rw [Finset.disjoint_left]
    intro pr h₁ h₂
    obtain ⟨hpr, h₁⟩ := Finset.mem_filter.1 h₁
    obtain ⟨-, h₂⟩ := Finset.mem_filter.1 h₂
    simp only [Finset.mem_singleton] at h₂
    rcases h₂ with h₂ | h₂ <;> rcases h₁ with h₁ | h₁
    · exact hx (h₂ ▸ h₁)
    · exact hpart _ h₁ ⟨pr, hpr, Or.inl ⟨h₂, rfl⟩⟩
    · exact hpart _ h₁ ⟨pr, hpr, Or.inr ⟨h₂, rfl⟩⟩
    · exact hx (h₂ ▸ h₁)

end State

end Cslib.Circuits.Boolean.AffineDisperser4n
