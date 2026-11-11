/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.SemiCircuit
public import CslibFrontier.Foundations.Combinatorics.AffineDisperser.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Sort

/-!
# Pair-type-generic states and potential bookkeeping for gate elimination

Shared state representation, pair/partner accounting, spread and affine helpers, and potential
bookkeeping shared by the `3.5n` (`AffineDisperser`) and `4n` (`AffineDisperser4n`) gate
elimination developments.

A configuration `Config` supplies:

* the carrier type `Pair` with endpoints `fst` and `snd` (`ℕ × ℕ` for `3.5n`, `ZeroPair` for `4n`);
* the degree weight `weight : ℕ → ℕ` bounded by `weightBound` and the potential coefficients
  `(cs, cq, ca)`;
* the pointwise locus predicate `locus` (`True` for `3.5n`, `Z(P)` for `4n`) and the parameter-map
  affinity invariant `phiOK` (`PairTame` preservation for `3.5n`, global affinity for `4n`).

## Main definitions

* `Cslib.Circuits.Boolean.AffineDisperserCore.Config`: configuration of pair representation,
  weights, potential coefficients, and state invariants.
* `Cslib.Circuits.Boolean.AffineDisperserCore.State`: generic gate-elimination state extending
  `SemiCircuit`.
* `Cslib.Circuits.Boolean.AffineDisperserCore.State.Valid`, `Step`, `Preparation`: validity, steps,
  and preparatory operations.
* `Cslib.Circuits.Boolean.AffineDisperserCore.State.Paired`, `unpaired`, `m`, `q`, `a`, `s`, `W`,
  `wt`, `IsPartner`, `pairsAvoid`, `pairsMeeting`: pair and potential accounting.

## Main results

* `Cslib.Circuits.Boolean.AffineDisperserCore.State.W_add_le`: comparing potentials name by name.
* `Cslib.Circuits.Boolean.AffineDisperserCore.State.Valid.card_pairsMeeting_le`,
  `card_pairsMeeting_singleton`, `card_pairsMeeting_insert`, `card_sdiff_image`: pair counting.
-/

public section

namespace Cslib.Circuits.Boolean.AffineDisperserCore

open Finset Cslib.BitString SemiCircuit

/-- Configuration of pair representation, degree weights, potential coefficients, and invariants
shared by gate-elimination developments (`3.5n` and `4n`). -/
structure Config where
  /-- Carrier type of parameter pairs. -/
  Pair : Type
  /-- First parameter of a pair. -/
  fst : Pair → ℕ
  /-- Second parameter of a pair. -/
  snd : Pair → ℕ
  /-- Decidable equality on pairs. -/
  [decEq : DecidableEq Pair]
  /-- Coefficient of circuit size `s` in `W`. -/
  cs : ℕ
  /-- Coefficient of pair count `q` in `W`. -/
  cq : ℕ
  /-- Coefficient of `a` in the potential invariant `ΔW ≤ ca * Δa`. -/
  ca : ℕ
  /-- Degree weight of an unpaired parameter. -/
  weight : ℕ → ℕ
  /-- Monotonicity of `weight`. -/
  weight_mono : ∀ {k l : ℕ}, k ≤ l → weight k ≤ weight l
  /-- Unused parameters have weight `0`. -/
  weight_zero : weight 0 = 0
  /-- Upper bound on `weight k`. -/
  weightBound : ℕ
  /-- Every degree weight is at most `weightBound`. -/
  weight_le : ∀ k : ℕ, weight k ≤ weightBound
  /-- Admissibility predicate on assignments relative to `pairs`. -/
  locus : Finset Pair → (ℕ → Bool) → Prop
  /-- Admissibility depends only on coordinates occurring in `pairs`. -/
  locus_congr : ∀ {P : Finset Pair} {val val' : ℕ → Bool},
    (∀ pr ∈ P, val (fst pr) = val' (fst pr) ∧ val (snd pr) = val' (snd pr)) →
    locus P val → locus P val'
  /-- Parameter-map affinity invariant parameterized by `n`, pairs, and `phi`. -/
  phiOK : ∀ {n : ℕ}, Finset Pair → ((ℕ → Bool) → BitString n) → Prop

/-- Synthesize `DecidableEq` on `cfg.Pair` from `cfg.decEq`. -/
instance instDecidableEqConfigPair (cfg : Config) : DecidableEq cfg.Pair :=
  cfg.decEq

namespace Config

/-- Whether `x` is one of the two parameters of the pair `pr`. -/
@[expose, reducible] def Contains (cfg : Config) (pr : cfg.Pair) (x : ℕ) : Prop :=
  cfg.fst pr = x ∨ cfg.snd pr = x

/-- Decidability of `Config.Contains`. -/
instance (cfg : Config) (pr : cfg.Pair) : DecidablePred (cfg.Contains pr) :=
  fun _ => inferInstanceAs (Decidable (_ ∨ _))

end Config

/-- A generic state of gate elimination for a Boolean function on `n` bits. -/
structure State (cfg : Config) (n : ℕ) extends SemiCircuit where
  /-- The pairs of parameters of the state. -/
  pairs : Finset cfg.Pair
  /-- The parameter map, as a function of all internal values. -/
  phi : (ℕ → Bool) → BitString n

namespace State

variable {cfg : Config} {n : ℕ} (S : State cfg n)

/-- Admissibility of an assignment under `cfg.locus` and `S.pairs`. -/
@[expose] def Locus (val : ℕ → Bool) : Prop :=
  cfg.locus S.pairs val

/-- `x` belongs to one of the pairs of `S`. -/
@[expose] def Paired (x : ℕ) : Prop :=
  ∃ pr ∈ S.pairs, cfg.Contains pr x

/-- Decidability of `State.Paired`. -/
instance : DecidablePred S.Paired :=
  fun _ => inferInstanceAs (Decidable (∃ pr ∈ S.pairs, _))

/-- The unpaired parameters of `S`. -/
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

/-- The potential `W = cs * s + cq * q + ∑_{x ∈ unpaired} weight (deg x)`. -/
@[expose] def W : ℕ :=
  cfg.cs * S.s + cfg.cq * S.q + ∑ x ∈ S.unpaired, cfg.weight (S.deg x)

/-- Validity of a gate-elimination state `S` for a Boolean function `f`. -/
structure Valid (f : BooleanFunction n) : Prop where
  /-- The semi-circuit is well formed. -/
  wf : S.WellFormed
  /-- Pairs consist of two distinct parameters. -/
  pair_mem : ∀ pr ∈ S.pairs, cfg.fst pr ∈ S.params ∧ cfg.snd pr ∈ S.params ∧
    cfg.fst pr ≠ cfg.snd pr
  /-- Distinct pairs are disjoint. -/
  pairs_disjoint : ∀ pr ∈ S.pairs, ∀ pr' ∈ S.pairs, pr ≠ pr' →
    cfg.fst pr ≠ cfg.fst pr' ∧ cfg.fst pr ≠ cfg.snd pr' ∧
    cfg.snd pr ≠ cfg.fst pr' ∧ cfg.snd pr ≠ cfg.snd pr'
  /-- The parameter map depends only on the parameters. -/
  phi_congr : ∀ val val', (∀ j ∈ S.params, val j = val' j) → S.phi val = S.phi val'
  /-- The parameter map satisfies `cfg.phiOK`. -/
  phi_affine : cfg.phiOK S.pairs S.phi
  /-- The parameter map is injective on the parameters. -/
  phi_injective : ∀ val val', S.phi val = S.phi val' → ∀ j ∈ S.params, val j = val' j
  /-- Every consistent admissible assignment outputs `f` at its image. -/
  computes : ∀ val, S.Consistent val → S.Locus val → S.out.eval val = f (S.phi val)

/-! ### Spreading bits over a finite set of names and affinity helpers -/

/-- The assignment reading the bits of `u` on the elements of `F`, in increasing order, and
`false` elsewhere. -/
@[expose] def spread (F : Finset ℕ) {k : ℕ} (h : F.card = k) (u : BitString k) : ℕ → Bool :=
  fun i => if hi : i ∈ F then u ((F.orderIsoOfFin h).symm ⟨i, hi⟩) else false

/-- Spreading a `k`-bit string over `F` defines an affine family of assignments. -/
theorem isAffine_spread (F : Finset ℕ) {k : ℕ} (h : F.card = k) : IsAffine (spread F h) := by
  intro u v w
  funext i
  simp only [spread, Pi.add_apply]
  split_ifs <;> rfl

/-- `spread F h u` assigns `false` to every index outside `F`. -/
theorem spread_of_notMem {F : Finset ℕ} {k : ℕ} (h : F.card = k) (u : BitString k) {i : ℕ}
    (hi : i ∉ F) : spread F h u i = false := by
  simp [spread, hi]

/-- At the `i`-th element of `F` in increasing order, `spread F h u` equals `u i`. -/
theorem spread_orderIsoOfFin {F : Finset ℕ} {k : ℕ} (h : F.card = k) (u : BitString k)
    (i : Fin k) : spread F h u (F.orderIsoOfFin h i) = u i := by
  simp only [spread, Finset.coe_mem, ↓reduceDIte, Subtype.coe_eta, OrderIso.symm_apply_apply]

/-- Two `k`-bit strings whose `spread` assignments agree on `F` are equal. -/
theorem eq_of_spread {F : Finset ℕ} {k : ℕ} (h : F.card = k) {u v : BitString k}
    (huv : ∀ i ∈ F, spread F h u i = spread F h v i) : u = v := by
  funext i
  rw [← spread_orderIsoOfFin h u i, ← spread_orderIsoOfFin h v i]
  exact huv _ (F.orderIsoOfFin h i).2

/-- The identity map on an additive group is affine. -/
theorem isAffine_id {α : Type*} [Add α] : IsAffine (fun x : α => x) :=
  fun _ _ _ => rfl

/-- Updating an affine family at one name by an affine function keeps it affine. -/
theorem isAffine_update {α : Type*} [Add α] {σ : α → ℕ → Bool} (hσ : IsAffine σ) (x : ℕ)
    {ψ : α → Bool} (hψ : IsAffine ψ) :
    IsAffine fun u => Function.update (σ u) x (ψ u) := by
  intro u v w
  funext i
  by_cases hi : i = x
  · subst hi
    simp only [Function.update_self, Pi.add_apply, hψ u v w]
  · simp only [Function.update_of_ne hi, Pi.add_apply, congrFun (hσ u v w) i]

/-- A constant plus a sum of coordinates of an affine family is affine. -/
theorem isAffine_const_add_sum {α : Type*} [Add α] {σ : α → ℕ → Bool} (hσ : IsAffine σ)
    (c : Bool) (R : Finset ℕ) : IsAffine fun u => c + ∑ j ∈ R, σ u j := by
  intro u v w
  simp only [fun j => congrFun (hσ u v w) j, Pi.add_apply, Finset.sum_add_distrib]
  generalize ∑ j ∈ R, σ u j = a
  generalize ∑ j ∈ R, σ v j = b
  generalize ∑ j ∈ R, σ w j = e
  revert a b e c
  decide

/-- Adding a fixed offset assignment preserves affinity of a family. -/
theorem isAffine_xor_const {α : Type*} [Add α] {σ : α → ℕ → Bool} (hσ : IsAffine σ)
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

/-- Admissibility of an assignment is preserved when two assignments agree on `S.params`. -/
theorem Valid.locus_congr {f : BooleanFunction n} (hS : S.Valid f) {val val' : ℕ → Bool}
    (hagree : ∀ j ∈ S.params, val j = val' j) (hlocus : S.Locus val) : S.Locus val' :=
  cfg.locus_congr
    (fun pr hpr => ⟨hagree _ (hS.pair_mem pr hpr).1, hagree _ (hS.pair_mem pr hpr).2.1⟩)
    hlocus

/-- Choosing one representative `rep pr` from every pair leaves `a` other parameters. -/
theorem Valid.card_sdiff_image {f : BooleanFunction n} (hS : S.Valid f) (rep : cfg.Pair → ℕ)
    (hrep : ∀ pr ∈ S.pairs, cfg.Contains pr (rep pr)) :
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

/-- Helper deriving `out_not_affine` from `false_of_fix`. -/
theorem Valid.out_not_affine_of {S : State cfg n}
    (hfix : ∀ {x : ℕ}, x ∈ S.params → ∀ (c : Bool) (R : Finset ℕ), R ⊆ S.params → x ∉ R →
      ∀ b : Bool,
        (∀ val, S.Consistent val → S.Locus val → val x = c + ∑ j ∈ R, val j → S.out.eval val = b) →
        False)
    (ha0 : S.params.Nonempty) (c : Bool) {T : Finset ℕ} (hT : T ⊆ S.params) :
    ¬ ∀ val, S.Consistent val → S.Locus val → S.out.eval val = c + ∑ j ∈ T, val j := by
  intro hout
  rcases T.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · obtain ⟨x, hx⟩ := ha0
    exact hfix hx false ∅ (Finset.empty_subset _) (Finset.notMem_empty _) c
      fun val hval hlocus _ => by simpa using hout val hval hlocus
  · refine hfix (hT hx) c (T.erase x) ((Finset.erase_subset _ _).trans hT)
      (Finset.notMem_erase _ _) false fun val hval hlocus hfeq => ?_
    rw [hout val hval hlocus, ← Finset.add_sum_erase T _ hx, hfeq]
    generalize ∑ j ∈ T.erase x, val j = e
    cases c <;> cases e <;> rfl

/-- Helper deriving `¬ S.out.Reads x` from `out_not_affine`. -/
theorem not_out_reads_param_of {S : State cfg n} {x : ℕ}
    (hout : ¬ ∀ val, S.Consistent val → S.Locus val →
      S.out.eval val = S.out.neg + ∑ j ∈ ({x} : Finset ℕ), val j) :
    ¬ S.out.Reads x := by
  intro hr
  refine hout fun val _ _ => ?_
  have hr' : S.out.arg = .node x := hr
  simp only [Lit.eval, hr', Arg.eval_node, Finset.sum_singleton]
  cases S.out.neg <;> cases val x <;> rfl

/-! ### Bookkeeping for the potential -/

variable {f : BooleanFunction n}

/-- The weight contributed by the name `x`: `cfg.weight (S.deg x)` if it is an unpaired
parameter, and `0` otherwise. -/
@[expose] def wt (S : State cfg n) (x : ℕ) : ℕ :=
  if x ∈ S.unpaired then cfg.weight (S.deg x) else 0

/-- The weight `S.wt x` of any name `x` is at most `cfg.weightBound`. -/
theorem wt_le_bound (S : State cfg n) (x : ℕ) : S.wt x ≤ cfg.weightBound := by
  unfold wt
  split_ifs
  · exact cfg.weight_le _
  · omega

/-- A name `x` belongs to `S.unpaired` iff it is an unpaired parameter of `S`. -/
theorem mem_unpaired {S : State cfg n} {x : ℕ} : x ∈ S.unpaired ↔ x ∈ S.params ∧ ¬ S.Paired x := by
  simp [unpaired]

/-- For an unpaired parameter `x`, `S.wt x` is `cfg.weight (S.deg x)`. -/
theorem wt_of_mem {S : State cfg n} {x : ℕ} (hx : x ∈ S.unpaired) :
    S.wt x = cfg.weight (S.deg x) := by
  simp [wt, hx]

/-- For a name `x` outside `S.unpaired`, `S.wt x = 0`. -/
theorem wt_of_notMem {S : State cfg n} {x : ℕ} (hx : x ∉ S.unpaired) : S.wt x = 0 := by
  simp [wt, hx]

/-- A paired parameter contributes weight `0`. -/
theorem wt_of_paired {S : State cfg n} {x : ℕ} (hx : S.Paired x) : S.wt x = 0 :=
  wt_of_notMem fun h => (mem_unpaired.1 h).2 hx

/-- A name outside `S.params` contributes weight `0`. -/
theorem wt_of_notMem_params {S : State cfg n} {x : ℕ} (hx : x ∉ S.params) : S.wt x = 0 :=
  wt_of_notMem fun h => hx (mem_unpaired.1 h).1

/-- Summing `S.wt` over any superset `N` of `S.params` equals the sum of `cfg.weight (S.deg x)`
over `S.unpaired`. -/
theorem sum_wt (S : State cfg n) {N : Finset ℕ} (hN : S.params ⊆ N) :
    ∑ x ∈ N, S.wt x = ∑ x ∈ S.unpaired, cfg.weight (S.deg x) := by
  have hU : S.unpaired ⊆ N := (Finset.filter_subset _ _).trans hN
  unfold wt
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 hU]

/-- Expressing the potential `S.W` with the weight sum taken over any superset `N` of
`S.params`. -/
theorem W_eq_sum (S : State cfg n) {N : Finset ℕ} (hN : S.params ⊆ N) :
    S.W = cfg.cs * S.s + cfg.cq * S.q + ∑ x ∈ N, S.wt x := by
  rw [sum_wt S hN]
  rfl

/-- Potentials compare name by name: if every name of a common set loses `loss x` and gains at
most `gain x` in weight, the sums of losses and gains bound the change of potential. -/
theorem W_add_le {S S' : State cfg n} {N : Finset ℕ} (hN : S.params ⊆ N) (hN' : S'.params ⊆ N)
    (loss gain : ℕ → ℕ) (h : ∀ x ∈ N, S'.wt x + loss x ≤ S.wt x + gain x) :
    S'.W + cfg.cs * S.s + cfg.cq * S.q + ∑ x ∈ N, loss x ≤
      S.W + cfg.cs * S'.s + cfg.cq * S'.q + ∑ x ∈ N, gain x := by
  rw [W_eq_sum S hN, W_eq_sum S' hN']
  have := Finset.sum_le_sum h
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at this
  omega

/-- Unpaired parameters of a state with the same pairs and fewer parameters were unpaired. -/
theorem mem_unpaired_of {S S' : State cfg n} {x : ℕ} (hx : x ∈ S'.unpaired) (hp : x ∈ S.params)
    (hpairs : S.pairs ⊆ S'.pairs) : x ∈ S.unpaired :=
  mem_unpaired.2 ⟨hp, fun ⟨pr, hpr, h⟩ => (mem_unpaired.1 hx).2 ⟨pr, hpairs hpr, h⟩⟩

/-- A step of gate elimination from `S` to `S'`: `S'` is valid, `m + s` decreases,
`Δa ∈ {0, -1, -2}`, and `ΔW ≤ cfg.ca * Δa`, written without subtraction. -/
structure Step (f : BooleanFunction n) (S S' : State cfg n) : Prop where
  /-- The new state is valid. -/
  valid : S'.Valid f
  /-- `m + s` decreases. -/
  lt : S'.m + S'.s < S.m + S.s
  /-- `a` does not increase. -/
  a_le : S'.a ≤ S.a
  /-- `a` decreases by at most two. -/
  le_a : S.a ≤ S'.a + 2
  /-- `ΔW ≤ cfg.ca * Δa`. -/
  potential : S'.W + cfg.ca * S.a ≤ S.W + cfg.ca * S'.a

/-- A preparatory operation of gate elimination from `S` to `S'`: `S'` is valid, with the same
`m`, `s` and `q` as `S` and no larger potential. -/
structure Preparation (f : BooleanFunction n) (S S' : State cfg n) : Prop where
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
theorem Preparation.a_eq {S S' : State cfg n} (h : Preparation f S S') : S'.a = S.a := by
  simp only [a, h.m_eq, h.q_eq]

/-- A preparatory operation followed by a step is a step. -/
theorem Step.of_preparation {S S₁ S' : State cfg n} (hp : Preparation f S S₁)
    (h : Step f S₁ S') : Step f S S' := by
  obtain ⟨hS', hlt, ha₁, ha₂, hW'⟩ := h
  have := hp.a_eq
  have := congrArg (cfg.ca * ·) hp.a_eq
  have := hp.m_eq
  have := hp.s_eq
  have := hp.W_le
  exact ⟨hS', by omega, by omega, by omega, by omega⟩

/-! ### Pairs and partners -/

/-- `r` is the partner of `w`: they form a pair. -/
@[expose] def IsPartner (S : State cfg n) (w r : ℕ) : Prop :=
  ∃ pr ∈ S.pairs, (cfg.fst pr = w ∧ cfg.snd pr = r) ∨ (cfg.snd pr = w ∧ cfg.fst pr = r)

/-- Decidability of `State.IsPartner`. -/
instance (S : State cfg n) (w : ℕ) : DecidablePred (S.IsPartner w) :=
  fun _ => inferInstanceAs (Decidable (∃ pr ∈ S.pairs, _))

/-- The pairs avoiding `w`. -/
@[expose] def pairsAvoid (S : State cfg n) (w : ℕ) : Finset cfg.Pair :=
  S.pairs.filter fun pr => ¬ cfg.Contains pr w

/-- The pairs with a member in `F`. -/
@[expose] def pairsMeeting (S : State cfg n) (F : Finset ℕ) : Finset cfg.Pair :=
  S.pairs.filter fun pr => cfg.fst pr ∈ F ∨ cfg.snd pr ∈ F

/-- Two states with the same pairs have the same paired names. -/
theorem paired_congr {S S' : State cfg n} (h : S'.pairs = S.pairs) {x : ℕ} :
    S'.Paired x ↔ S.Paired x := by
  unfold Paired
  rw [h]

/-- Two states with the same parameters and pairs have the same unpaired parameters. -/
theorem unpaired_congr {S S' : State cfg n} (hp : S'.params = S.params) (h : S'.pairs = S.pairs) :
    S'.unpaired = S.unpaired := by
  ext x
  rw [mem_unpaired, mem_unpaired, hp, paired_congr h]

/-- If `pr ∈ S.pairs` contains `p` and `r` with `p ≠ r`, then `r` is the partner of `p`. -/
theorem isPartner_of_contains {S : State cfg n} {pr : cfg.Pair} (hpr : pr ∈ S.pairs)
    {p r : ℕ} (hp : cfg.Contains pr p) (hr : cfg.Contains pr r) (hne : p ≠ r) :
    S.IsPartner p r := by
  rcases hp with h1 | h1 <;> rcases hr with h2 | h2
  · exact absurd (h1.symm.trans h2) hne
  · exact ⟨pr, hpr, Or.inl ⟨h1, h2⟩⟩
  · exact ⟨pr, hpr, Or.inr ⟨h1, h2⟩⟩
  · exact absurd (h1.symm.trans h2) hne

/-- Any name contained in a pair of a valid state is a parameter. -/
theorem Valid.mem_params_of_contains {S : State cfg n} (hS : S.Valid f) {pr : cfg.Pair}
    (hpr : pr ∈ S.pairs) {p : ℕ} (hp : cfg.Contains pr p) : p ∈ S.params := by
  rcases hp with h | h <;> rw [← h]
  exacts [(hS.pair_mem pr hpr).1, (hS.pair_mem pr hpr).2.1]

/-- Every paired name of a valid state is a parameter. -/
theorem Valid.mem_params_of_paired {S : State cfg n} (hS : S.Valid f) {p : ℕ} (hp : S.Paired p) :
    p ∈ S.params := by
  obtain ⟨pr, hpr, h⟩ := hp
  exact hS.mem_params_of_contains hpr h

/-- A pair containing `w` is unique. -/
theorem Valid.pair_unique {S : State cfg n} (hS : S.Valid f) {w : ℕ} {pr pr' : cfg.Pair}
    (hpr : pr ∈ S.pairs) (hpr' : pr' ∈ S.pairs) (h : cfg.Contains pr w)
    (h' : cfg.Contains pr' w) : pr = pr' := by
  by_contra hne
  have := hS.pairs_disjoint pr hpr pr' hpr' hne
  rcases h with rfl | rfl <;> rcases h' with h' | h' <;> tauto

/-- Every paired parameter has a partner. -/
theorem exists_partner {S : State cfg n} {p : ℕ} (hp : S.Paired p) : ∃ r, S.IsPartner p r := by
  obtain ⟨pr, hpr, h | h⟩ := hp
  · exact ⟨cfg.snd pr, pr, hpr, Or.inl ⟨h, rfl⟩⟩
  · exact ⟨cfg.fst pr, pr, hpr, Or.inr ⟨h, rfl⟩⟩

/-- The partner relation `State.IsPartner` is symmetric. -/
theorem IsPartner.symm {S : State cfg n} {p r : ℕ} (h : S.IsPartner p r) : S.IsPartner r p := by
  obtain ⟨pr, hpr, h⟩ := h
  exact ⟨pr, hpr, by tauto⟩

/-- A parameter that has a partner is paired. -/
theorem IsPartner.paired {S : State cfg n} {w r : ℕ} (h : S.IsPartner w r) : S.Paired w := by
  obtain ⟨pr, hpr, ⟨h1, -⟩ | ⟨h1, -⟩⟩ := h
  · exact ⟨pr, hpr, Or.inl h1⟩
  · exact ⟨pr, hpr, Or.inr h1⟩

/-- In a valid state, a parameter is distinct from its partner. -/
theorem Valid.partner_ne {S : State cfg n} (hS : S.Valid f) {p r : ℕ} (h : S.IsPartner p r) :
    r ≠ p := by
  obtain ⟨pr, hpr, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := h
  · rw [← h1, ← h2]; exact (hS.pair_mem pr hpr).2.2.symm
  · rw [← h1, ← h2]; exact (hS.pair_mem pr hpr).2.2

/-- In a valid state, the partner of a parameter is a parameter. -/
theorem Valid.partner_mem {S : State cfg n} (hS : S.Valid f) {p r : ℕ} (h : S.IsPartner p r) :
    r ∈ S.params :=
  hS.mem_params_of_paired h.symm.paired

/-- A partner is unique. -/
theorem Valid.isPartner_unique {S : State cfg n} (hS : S.Valid f) {w r r' : ℕ}
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

/-- Two parameters sharing the same partner are equal. -/
theorem Valid.isPartner_unique_right {S : State cfg n} (hS : S.Valid f) {u p r : ℕ}
    (hup : S.IsPartner u r) (hpr : S.IsPartner p r) : u = p :=
  hS.isPartner_unique hup.symm hpr.symm

/-- The partners of `w` contribute at most one summand. -/
theorem Valid.sum_partner_le {S : State cfg n} (hS : S.Valid f) (w : ℕ) (N : Finset ℕ) (c : ℕ) :
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
theorem Valid.paired_filter_iff {S : State cfg n} (hS : S.Valid f) {F : Finset ℕ} {u : ℕ}
    (huF : u ∉ F) :
    (∃ pr ∈ S.pairs.filter (fun pr => ¬ (cfg.fst pr ∈ F ∨ cfg.snd pr ∈ F)), cfg.Contains pr u) ↔
      S.Paired u ∧ ∀ x ∈ F, ¬ S.IsPartner u x := by
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
theorem Valid.q_le_m {S : State cfg n} (hS : S.Valid f) : S.q ≤ S.m := by
  have hsub : S.pairs.image cfg.fst ⊆ S.params := fun i hi => by
    obtain ⟨pr, hpr, rfl⟩ := Finset.mem_image.1 hi
    exact (hS.pair_mem pr hpr).1
  have hinj : Set.InjOn cfg.fst (S.pairs : Set cfg.Pair) := fun pr hpr pr' hpr' h =>
    hS.pair_unique hpr hpr' (Or.inl rfl) (Or.inl h.symm)
  have := Finset.card_le_card hsub
  rwa [Finset.card_image_of_injOn hinj] at this

/-- At most `|F|` pairs meet a set `F` of parameters. -/
theorem Valid.card_pairsMeeting_le {S : State cfg n} (hS : S.Valid f) (F : Finset ℕ) :
    (S.pairsMeeting F).card ≤ F.card := by
  classical
  refine Finset.card_le_card_of_injOn (fun pr => if cfg.fst pr ∈ F then cfg.fst pr else cfg.snd pr)
    (fun pr hpr => ?_) (fun pr hpr pr' hpr' h => ?_)
  · obtain ⟨-, h⟩ := Finset.mem_filter.1 hpr
    by_cases h1 : cfg.fst pr ∈ F
    · simp only [ite_eq_left h1]; exact h1
    · simp only [ite_eq_right h1]; exact h.resolve_left h1
  · obtain ⟨hpr, -⟩ := Finset.mem_filter.1 hpr
    obtain ⟨hpr', -⟩ := Finset.mem_filter.1 hpr'
    simp only at h
    refine hS.pair_unique hpr hpr' (w := if cfg.fst pr ∈ F then cfg.fst pr else cfg.snd pr)
      (by split_ifs <;> simp [Config.Contains]) ?_
    rw [h]
    split_ifs <;> simp [Config.Contains]

/-- The number of pairs meeting `{w}` is `1` if `w` is paired and `0` otherwise. -/
theorem Valid.card_pairsMeeting_singleton {S : State cfg n} (hS : S.Valid f) (w : ℕ) :
    (S.pairsMeeting {w}).card = if S.Paired w then 1 else 0 := by
  split_ifs with hw
  · obtain ⟨pr, hpr, hprw⟩ := hw
    rw [Finset.card_eq_one]
    refine ⟨pr, Finset.eq_singleton_iff_unique_mem.2 ⟨Finset.mem_filter.2 ⟨hpr, by simpa⟩,
      fun pr' hpr' => ?_⟩⟩
    obtain ⟨hpr', h⟩ := Finset.mem_filter.1 hpr'
    exact hS.pair_unique hpr' hpr (by simpa [Config.Contains] using h) hprw
  · refine Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun pr hpr h => hw ?_)
    exact ⟨pr, hpr, by simpa [Config.Contains, eq_comm] using h⟩

/-- Adding to `F` a parameter that is not the partner of a member of `F` adds its pair, if
any. -/
theorem Valid.card_pairsMeeting_insert {S : State cfg n} (hS : S.Valid f) {F : Finset ℕ} {x : ℕ}
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

/-- A parameter of degree at most `1` containing `H` among its children has `{H}` as its set of
children. -/
theorem children_eq_singleton {S : State cfg n} {x : ℕ} {H : ℕ ⊕ ℕ}
    (hle : S.deg x ≤ 1) (hH : H ∈ S.children x) : S.children x = {H} := by
  have hpos : 0 < (S.children x).card := Finset.card_pos.2 ⟨H, hH⟩
  have hcard : (S.children x).card = 1 := by unfold SemiCircuit.deg at hle; omega
  obtain ⟨M, hM⟩ := Finset.card_eq_one.1 hcard
  have h1 := Finset.mem_singleton.1 (hM ▸ hH)
  rwa [← h1] at hM

end State

end Cslib.Circuits.Boolean.AffineDisperserCore
