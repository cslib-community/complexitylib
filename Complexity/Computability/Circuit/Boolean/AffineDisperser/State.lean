/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.SemiCircuit
public import Complexity.Foundations.Combinatorics.AffineDisperser.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# States of gate elimination and their potential

A *state* of the gate elimination of [Mishra and Santhanam, Section 2.4][MishraSanthanam2026]
for a Boolean function `f` on `n` bits consists of a fair semi-circuit reading parameters, a set
of disjoint pairs of parameters and an injective map `Φ` from parameter values to inputs of `f`
such that the semi-circuit computes `f ∘ Φ` (`State.Valid`). The source keeps `Φ` in the form

  `Φ(u) = b + L u + ∑_{{p, r} ∈ P} c_{pr} p r`  (form (1) of the source),

an affine map plus quadratic terms over the pairs. We record only the property of this form
that the proof uses: along every affine family of parameter assignments on which each pair has a
constant member, or a constant sum, `Φ` is affine (`State.Valid.phi_affine`). The map `Φ` is
stored as a function of all internal values that depends only on the parameters.

A state has `m` parameters, `q` pairs, `a = m - q` and size `s`, the number of gates plus the
number of equations. The *weight* of an unpaired parameter of degree `k` is `0`, `6` or `7` for
`k = 0`, `k = 1` and `k ≥ 2`, and the *potential* is

  `W = 2 s + 3 q + ∑_{x unpaired} wt(x)`  (equation (5) of the source).

Proposition 2.2 of the source: the image of `Φ` contains the image of an injective affine map
from `BitString a`, informally an affine subspace of dimension `a`
(`State.Valid.exists_affine_embedding`), so the output of a valid state for an affine disperser
for dimension `d ≤ a` is not constant (`State.Valid.exists_out_ne_of_le`). Restricting one more
parameter to an affine function of the others keeps dimension `a - 1`, so when `d < a` the output
is not constant there either (`State.Valid.false_of_fix`); in particular it is not an affine
function of the parameters (`State.Valid.out_not_affine`, part of Lemma 2.3 of the source).

Writing `State.wt S x` for the weight of `x` if it is an unpaired parameter of `S` and `0`
otherwise, the potentials of two states compare name by name (`State.W_add_le`). A *step* of gate
elimination (`State.Step`) is a move to a valid state with smaller `m + s`, `Δa ∈ {0, -1, -2}` and
`ΔW ≤ 14 Δa`, as in Lemma 4.2 of the source; a *preparatory operation* (`State.Preparation`) keeps
`m`, `s` and `q` and does not increase `W`.

## Main definitions

* `Cslib.Circuits.Boolean.AffineDisperser.State`,
  `Cslib.Circuits.Boolean.AffineDisperser.State.Valid`,
  `Cslib.Circuits.Boolean.AffineDisperser.PairTame`: states and tame pairs.
* `Cslib.Circuits.Boolean.AffineDisperser.State.Paired`,
  `Cslib.Circuits.Boolean.AffineDisperser.State.unpaired`,
  `Cslib.Circuits.Boolean.AffineDisperser.State.wt`: paired and unpaired parameters and their
  weights.
* `Cslib.Circuits.Boolean.AffineDisperser.State.m`, `q`, `a`, `s`, `W`: the counted quantities
  and the potential, with `Cslib.Circuits.Boolean.AffineDisperser.weight`.
* `Cslib.Circuits.Boolean.AffineDisperser.State.spread`: spreading bits over a finite set of
  names.
* `Cslib.Circuits.Boolean.AffineDisperser.State.Step`,
  `Cslib.Circuits.Boolean.AffineDisperser.State.Preparation`: steps and preparatory operations.
* `Cslib.Circuits.Boolean.AffineDisperser.State.IsPartner`,
  `Cslib.Circuits.Boolean.AffineDisperser.State.pairsAvoid`,
  `Cslib.Circuits.Boolean.AffineDisperser.State.pairsMeeting`: partners and the pairs avoiding a
  parameter or meeting a set of parameters.

## Main results

* `Cslib.Circuits.Boolean.AffineDisperser.State.Valid.exists_affine_embedding`: Proposition 2.2.
* `Cslib.Circuits.Boolean.AffineDisperser.State.Valid.false_of_fix`,
  `Cslib.Circuits.Boolean.AffineDisperser.State.Valid.out_not_affine`: Lemma 2.3.
* `Cslib.Circuits.Boolean.AffineDisperser.State.W_add_le`: comparing potentials name by name.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.AffineDisperser

open Finset Cslib.BitString SemiCircuit

/-- The weight of an unpaired parameter of degree `k`: `0` if it is unused, `6` if it is
isolated and `7` otherwise (equation (4) of [Mishra and Santhanam][MishraSanthanam2026]). -/
def weight (k : ℕ) : ℕ :=
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
def PairTame {α : Type*} (σ : α → ℕ → Bool) (pr : ℕ × ℕ) : Prop :=
  (∀ x y, σ x pr.1 = σ y pr.1) ∨ (∀ x y, σ x pr.2 = σ y pr.2) ∨
    ∀ x y, σ x pr.1 + σ x pr.2 = σ y pr.1 + σ y pr.2

/-- A state of gate elimination for a function of `n` bits: a semi-circuit, disjoint pairs of
parameters and the parameter map `Φ`. -/
structure State (n : ℕ) extends SemiCircuit where
  /-- The pairs of parameters that may occur together in a quadratic term of `Φ`. -/
  pairs : Finset (ℕ × ℕ)
  /-- The parameter map, as a function of the values of all internal values. -/
  phi : (ℕ → Bool) → BitString n

namespace State

variable {n : ℕ} (S : State n)

/-- `x` belongs to one of the pairs. -/
def Paired (x : ℕ) : Prop :=
  ∃ pr ∈ S.pairs, pr.1 = x ∨ pr.2 = x

/-- Decidability of `State.Paired`. -/
instance : DecidablePred S.Paired :=
  fun _ => inferInstanceAs (Decidable (∃ pr ∈ S.pairs, _))

/-- The unpaired parameters. -/
def unpaired : Finset ℕ :=
  S.params.filter fun x => ¬ S.Paired x

/-- The number of parameters. -/
def m : ℕ :=
  S.params.card

/-- The number of pairs. -/
def q : ℕ :=
  S.pairs.card

/-- The number of parameters minus the number of pairs. -/
def a : ℕ :=
  S.m - S.q

/-- The size of the semi-circuit: gates plus equations. -/
def s : ℕ :=
  S.size

/-- The potential `W = 2 s + 3 q + ∑ wt(x)` over the unpaired parameters `x`. -/
def W : ℕ :=
  2 * S.s + 3 * S.q + ∑ x ∈ S.unpaired, weight (S.deg x)

/-- A valid state for `f`: a well-formed fair semi-circuit, disjoint pairs of distinct
parameters, and an injective parameter map that depends only on the parameters and is affine
along every affine family of assignments on which each pair has a constant member or a constant
sum, such that the output of every consistent assignment is the value of `f` at its image. -/
structure Valid (f : BooleanFunction n) : Prop where
  /-- The semi-circuit is well formed. -/
  wf : S.WellFormed
  /-- Pairs consist of two distinct parameters. -/
  pair_mem : ∀ pr ∈ S.pairs, pr.1 ∈ S.params ∧ pr.2 ∈ S.params ∧ pr.1 ≠ pr.2
  /-- Distinct pairs are disjoint. -/
  pairs_disjoint : ∀ pr ∈ S.pairs, ∀ pr' ∈ S.pairs, pr ≠ pr' →
    pr.1 ≠ pr'.1 ∧ pr.1 ≠ pr'.2 ∧ pr.2 ≠ pr'.1 ∧ pr.2 ≠ pr'.2
  /-- The parameter map depends only on the parameters. -/
  phi_congr : ∀ val val', (∀ j ∈ S.params, val j = val' j) → S.phi val = S.phi val'
  /-- The parameter map is affine along affine families on which every pair is tame. -/
  phi_affine : ∀ (k : ℕ) (σ : BitString k → ℕ → Bool), IsAffine σ →
    (∀ pr ∈ S.pairs, PairTame σ pr) → IsAffine (S.phi ∘ σ)
  /-- The parameter map is injective on the parameters. -/
  phi_injective : ∀ val val', S.phi val = S.phi val' → ∀ j ∈ S.params, val j = val' j
  /-- Every consistent assignment outputs `f` at its image. -/
  computes : ∀ val, S.Consistent val → S.out.eval val = f (S.phi val)

/-! ### Spreading bits over a finite set of names -/

/-- The assignment reading the bits of `u` on the elements of `F`, in increasing order, and
`false` elsewhere. -/
def spread (F : Finset ℕ) {k : ℕ} (h : F.card = k) (u : BitString k) : ℕ → Bool :=
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

/-- Updating an affine family at one name by an affine function keeps it affine. -/
theorem isAffine_update {k : ℕ} {σ : BitString k → ℕ → Bool} (hσ : IsAffine σ) (x : ℕ)
    {ψ : BitString k → Bool} (hψ : IsAffine ψ) :
    IsAffine fun u => Function.update (σ u) x (ψ u) := by
  intro u v w
  funext i
  by_cases hi : i = x
  · subst hi
    simp only [Function.update_self, Pi.add_apply, hψ u v w]
  · simp only [Function.update_of_ne hi, Pi.add_apply, congrFun (hσ u v w) i]

/-- A constant plus a sum of coordinates of an affine family is affine. -/
theorem isAffine_const_add_sum {k : ℕ} {σ : BitString k → ℕ → Bool} (hσ : IsAffine σ)
    (c : Bool) (R : Finset ℕ) : IsAffine fun u => c + ∑ j ∈ R, σ u j := by
  intro u v w
  simp only [fun j => congrFun (hσ u v w) j, Pi.add_apply, Finset.sum_add_distrib]
  generalize ∑ j ∈ R, σ u j = a
  generalize ∑ j ∈ R, σ v j = b
  generalize ∑ j ∈ R, σ w j = e
  revert a b e c; decide

variable {S}

/-! ### Proposition 2.2 -/

/-- Choosing one member `rep pr` of every pair leaves exactly `a` other parameters. -/
theorem Valid.card_sdiff_image {f : BooleanFunction n} (hS : S.Valid f) (rep : ℕ × ℕ → ℕ)
    (hrep : ∀ pr, rep pr = pr.1 ∨ rep pr = pr.2) :
    (S.params \ S.pairs.image rep).card = S.a := by
  have hsub : S.pairs.image rep ⊆ S.params := by
    intro i hi
    obtain ⟨pr, hpr, rfl⟩ := Finset.mem_image.1 hi
    rcases hrep pr with h | h <;> rw [h]
    · exact (hS.pair_mem pr hpr).1
    · exact (hS.pair_mem pr hpr).2.1
  have hinj : Set.InjOn rep S.pairs := by
    intro pr hpr pr' hpr' heq
    by_contra hne
    have := hS.pairs_disjoint pr hpr pr' hpr' hne
    rcases hrep pr with h | h <;> rcases hrep pr' with h' | h' <;> rw [h, h'] at heq <;> tauto
  rw [Finset.card_sdiff_of_subset hsub, Finset.card_image_of_injOn hinj]
  rfl

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
  rw [hS.computes val hcons, hS.computes val' hcons', hS.phi_congr val (σ u) hval,
    hS.phi_congr val' (σ v) hval']
  exact huv

/-- **Proposition 2.2** of [Mishra and Santhanam][MishraSanthanam2026]: the image of the
parameter map of a valid state contains the image of an injective affine map from
`BitString a`. -/
theorem Valid.exists_affine_embedding {f : BooleanFunction n} (hS : S.Valid f) :
    ∃ g : BitString S.a → BitString n, IsAffine g ∧ Function.Injective g ∧
      ∀ u, ∃ val, S.Consistent val ∧ g u = S.phi val := by
  set F := S.params \ S.pairs.image Prod.fst
  have hF : F.card = S.a := hS.card_sdiff_image Prod.fst fun _ => Or.inl rfl
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
  have hF : F.card = S.a := hS.card_sdiff_image Prod.fst fun _ => Or.inl rfl
  have hFp : F ⊆ S.params := Finset.sdiff_subset
  obtain ⟨-, -, val, val', h, h', -, -, hne⟩ := hS.exists_out_ne hf (spread F hF)
    (isAffine_spread F hF) (fun pr hpr => Or.inl fun u v => by
      have : pr.1 ∉ F := fun h => (Finset.mem_sdiff.1 h).2 (Finset.mem_image_of_mem _ hpr)
      rw [spread_of_notMem hF u this, spread_of_notMem hF v this])
    (fun u v h => eq_of_spread hF fun i hi => h i (hFp hi)) ha
  exact ⟨val, val', h, h', hne⟩

/-! ### Lemma 2.3 -/

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
  have hrep : ∀ pr, rep pr = pr.1 ∨ rep pr = pr.2 := fun pr => by
    by_cases h : pr.1 = x <;> simp [rep, h]
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
  obtain ⟨u, v, val, val', hcons, hcons', hval, hval', hne⟩ := hS.exists_out_ne hf σ hσ
    (fun pr hpr => by
      have hnot : rep pr ∉ F' := fun h =>
        (Finset.mem_sdiff.1 (Finset.mem_of_mem_erase h)).2 (Finset.mem_image_of_mem _ hpr)
      have hconst : ∀ u, σ u (rep pr) = false := fun u => by
        simp only [σ, Function.update_of_ne (hrepx pr hpr), spread_of_notMem hF' u hnot]
      rcases hrep pr with h | h
      · exact Or.inl fun u v => by rw [← h, hconst, hconst]
      · exact Or.inr (Or.inl fun u v => by rw [← h, hconst, hconst]))
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
    ¬ ∀ val, S.Consistent val → S.out.eval val = c + ∑ j ∈ T, val j := by
  intro hout
  rcases T.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · obtain ⟨x, hx⟩ : S.params.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      rintro h
      simp [a, m, h] at ha
    exact hS.false_of_fix hf ha hx false ∅ (Finset.empty_subset _) (Finset.notMem_empty _) c
      fun val hval _ => by simpa using hout val hval
  · refine hS.false_of_fix hf ha (hT hx) c (T.erase x) ((Finset.erase_subset _ _).trans hT)
      (Finset.notMem_erase _ _) false fun val hval hfix => ?_
    rw [hout val hval, ← Finset.add_sum_erase T _ hx, hfix]
    generalize ∑ j ∈ T.erase x, val j = e
    cases c <;> cases e <;> rfl

/-! ### Bookkeeping for the potential -/

variable {f : BooleanFunction n}

/-- The weight contributed by the name `x`: its weight if it is an unpaired parameter, and `0`
otherwise. -/
def wt (S : State n) (x : ℕ) : ℕ :=
  if x ∈ S.unpaired then weight (S.deg x) else 0

/-- The weight `S.wt x` of any name `x` is at most `7`. -/
theorem wt_le_seven (S : State n) (x : ℕ) : S.wt x ≤ 7 := by
  unfold wt; split_ifs
  · exact weight_le_seven _
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
    S.W = 2 * S.s + 3 * S.q + ∑ x ∈ N, S.wt x := by
  rw [sum_wt S hN]; rfl

/-- Potentials compare name by name: if every name of a common set loses `loss x` and gains at
most `gain x` in weight, the sums of losses and gains bound the change of potential. -/
theorem W_add_le {S S' : State n} {N : Finset ℕ} (hN : S.params ⊆ N) (hN' : S'.params ⊆ N)
    (loss gain : ℕ → ℕ) (h : ∀ x ∈ N, S'.wt x + loss x ≤ S.wt x + gain x) :
    S'.W + 2 * S.s + 3 * S.q + ∑ x ∈ N, loss x ≤
      S.W + 2 * S'.s + 3 * S'.q + ∑ x ∈ N, gain x := by
  rw [W_eq_sum S hN, W_eq_sum S' hN']
  have := Finset.sum_le_sum h
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at this
  omega

/-- Unpaired parameters of a state with the same pairs and fewer parameters were unpaired. -/
theorem mem_unpaired_of {S S' : State n} {x : ℕ} (hx : x ∈ S'.unpaired) (hp : x ∈ S.params)
    (hpairs : S.pairs ⊆ S'.pairs) : x ∈ S.unpaired :=
  mem_unpaired.2 ⟨hp, fun ⟨pr, hpr, h⟩ => (mem_unpaired.1 hx).2 ⟨pr, hpairs hpr, h⟩⟩

/-- A step of gate elimination from `S` to `S'`, as in Lemma 4.2 of
[Mishra and Santhanam][MishraSanthanam2026]: `S'` is valid, `m + s` decreases,
`Δa ∈ {0, -1, -2}` and `ΔW ≤ 14 Δa`, written without subtraction. -/
structure Step (f : BooleanFunction n) (S S' : State n) : Prop where
  /-- The new state is valid. -/
  valid : S'.Valid f
  /-- `m + s` decreases. -/
  lt : S'.m + S'.s < S.m + S.s
  /-- `a` does not increase. -/
  a_le : S'.a ≤ S.a
  /-- `a` decreases by at most two. -/
  le_a : S.a ≤ S'.a + 2
  /-- `ΔW ≤ 14 Δa`. -/
  potential : S'.W + 14 * S.a ≤ S.W + 14 * S'.a

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
def IsPartner (S : State n) (w r : ℕ) : Prop :=
  ∃ pr ∈ S.pairs, (pr.1 = w ∧ pr.2 = r) ∨ (pr.2 = w ∧ pr.1 = r)

/-- Decidability of `State.IsPartner`. -/
instance (S : State n) (w : ℕ) : DecidablePred (S.IsPartner w) :=
  fun _ => inferInstanceAs (Decidable (∃ pr ∈ S.pairs, _))

/-- The pairs avoiding `w`. -/
def pairsAvoid (S : State n) (w : ℕ) : Finset (ℕ × ℕ) :=
  S.pairs.filter fun pr => pr.1 ≠ w ∧ pr.2 ≠ w

/-- The pairs with a member in `F`. -/
def pairsMeeting (S : State n) (F : Finset ℕ) : Finset (ℕ × ℕ) :=
  S.pairs.filter fun pr => pr.1 ∈ F ∨ pr.2 ∈ F

/-- Two states with the same pairs have the same paired names. -/
theorem paired_congr {S S' : State n} (h : S'.pairs = S.pairs) {x : ℕ} :
    S'.Paired x ↔ S.Paired x := by
  unfold Paired; rw [h]

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
theorem Valid.pair_unique {S : State n} (hS : S.Valid f) {w : ℕ} {pr pr' : ℕ × ℕ}
    (hpr : pr ∈ S.pairs) (hpr' : pr' ∈ S.pairs) (h : pr.1 = w ∨ pr.2 = w)
    (h' : pr'.1 = w ∨ pr'.2 = w) : pr = pr' := by
  by_contra hne
  have := hS.pairs_disjoint pr hpr pr' hpr' hne
  rcases h with rfl | rfl <;> rcases h' with h' | h' <;> tauto

/-- Every paired parameter has a partner. -/
theorem exists_partner {S : State n} {p : ℕ} (hp : S.Paired p) : ∃ r, S.IsPartner p r := by
  obtain ⟨pr, hpr, h | h⟩ := hp
  · exact ⟨pr.2, pr, hpr, Or.inl ⟨h, rfl⟩⟩
  · exact ⟨pr.1, pr, hpr, Or.inr ⟨h, rfl⟩⟩

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
    (huF : u ∉ F) : (∃ pr ∈ S.pairs.filter (fun pr => ¬ (pr.1 ∈ F ∨ pr.2 ∈ F)),
      pr.1 = u ∨ pr.2 = u) ↔ S.Paired u ∧ ∀ x ∈ F, ¬ S.IsPartner u x := by
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
  have hsub : S.pairs.image Prod.fst ⊆ S.params := fun i hi => by
    obtain ⟨pr, hpr, rfl⟩ := Finset.mem_image.1 hi
    exact (hS.pair_mem pr hpr).1
  have hinj : Set.InjOn Prod.fst (S.pairs : Set (ℕ × ℕ)) := fun pr hpr pr' hpr' h =>
    hS.pair_unique hpr hpr' (Or.inl rfl) (Or.inl h.symm)
  have := Finset.card_le_card hsub
  rwa [Finset.card_image_of_injOn hinj] at this

/-- At most `|F|` pairs meet a set `F` of parameters. -/
theorem Valid.card_pairsMeeting_le {S : State n} (hS : S.Valid f) (F : Finset ℕ) :
    (S.pairsMeeting F).card ≤ F.card := by
  classical
  refine Finset.card_le_card_of_injOn (fun pr => if pr.1 ∈ F then pr.1 else pr.2)
    (fun pr hpr => ?_) (fun pr hpr pr' hpr' h => ?_)
  · obtain ⟨-, h⟩ := Finset.mem_filter.1 hpr
    by_cases h1 : pr.1 ∈ F
    · simp only [ite_eq_left h1]; exact h1
    · simp only [ite_eq_right h1]; exact h.resolve_left h1
  · obtain ⟨hpr, -⟩ := Finset.mem_filter.1 hpr
    obtain ⟨hpr', -⟩ := Finset.mem_filter.1 hpr'
    simp only at h
    refine hS.pair_unique hpr hpr' (w := if pr.1 ∈ F then pr.1 else pr.2)
      (by split_ifs <;> simp) ?_
    rw [h]; split_ifs <;> simp

/-- The number of pairs meeting `{w}` is `1` if `w` is paired and `0` otherwise. -/
theorem Valid.card_pairsMeeting_singleton {S : State n} (hS : S.Valid f) (w : ℕ) :
    (S.pairsMeeting {w}).card = if S.Paired w then 1 else 0 := by
  split_ifs with hw
  · obtain ⟨pr, hpr, hprw⟩ := hw
    rw [Finset.card_eq_one]
    refine ⟨pr, Finset.eq_singleton_iff_unique_mem.2 ⟨Finset.mem_filter.2 ⟨hpr, by simpa⟩,
      fun pr' hpr' => ?_⟩⟩
    obtain ⟨hpr', h⟩ := Finset.mem_filter.1 hpr'
    exact hS.pair_unique hpr' hpr (by simpa using h) hprw
  · refine Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun pr hpr h => hw ?_)
    exact ⟨pr, hpr, by simpa [eq_comm] using h⟩

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

end Cslib.Circuits.Boolean.AffineDisperser
