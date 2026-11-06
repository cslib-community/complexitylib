/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Topology
import Mathlib.Tactic

/-!
# Real lifted-plane nonseparation

The colored affine-dependence extraction underlying [XuGaoHu2027], Theorem 5.7,
PDF p. 14. Plane coefficients and observations are arbitrary real numbers.
The homogeneous saddle lift is `(xy,x,y,1)`. General position means that every
family of at most four such lifts is linearly independent; for at least four
observations this is exactly the paper's no-four-coplanar hypothesis.
-/

noncomputable section

public section

namespace Cslib.LeastSquares.Geometry

open Matrix Set
open scoped BigOperators

variable {ι : Type*} [Finite ι]

/-- Homogeneous coordinates of the saddle lift, including the affine constant. -/
@[expose] def lift (p : ι → ℝ × ℝ) (i : ι) : Fin 4 → ℝ :=
  ![(p i).1 * (p i).2, (p i).1, (p i).2, 1]

/-- Lifted general position, also specifying the smaller independent families. -/
@[expose] def LiftedGeneralPosition (p : ι → ℝ × ℝ) : Prop :=
  ∀ s : Finset ι, s.card ≤ 4 → LinearIndependent ℝ (fun i : s => lift p i)

/-- A strict affine separator between kept and omitted saddle lifts. -/
@[expose] def IsRange (p : ι → ℝ × ℝ) (S : Finset ι) : Prop :=
  ∃ c : Fin 4 → ℝ, (∀ i ∈ S, lift p i ⬝ᵥ c < 0) ∧
    ∀ i ∉ S, 0 < lift p i ⬝ᵥ c

omit [Finite ι] in
/-- For at least four observations it suffices to check four-point families;
independence of all smaller families follows by extension. -/
theorem liftedGeneralPosition_iff_four [Fintype ι] (p : ι → ℝ × ℝ) (hn : 4 ≤ Fintype.card ι) :
    LiftedGeneralPosition p ↔
      ∀ s : Finset ι, s.card = 4 → LinearIndependent ℝ (fun i : s => lift p i) := by
  classical
  constructor
  · intro h s hs
    exact h s hs.le
  · intro h s hs
    obtain ⟨t, hst, _, ht⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ s) hs
      (show 4 ≤ Finset.univ.card by simpa using hn)
    exact (h t ht).comp (fun i : s => (⟨i.val, hst i.property⟩ : t))
      (fun i j he => Subtype.ext (congrArg (fun x : t => x.val) he))

omit [Finite ι] in
/-- On a finite data set, allowing omitted points on the cutting plane is
 equivalent to strict separation of both sides. -/
theorem isRange_iff_sublevel (p : ι → ℝ × ℝ) (S : Finset ι) :
    IsRange p S ↔ ∃ c : Fin 4 → ℝ, ∀ i, i ∈ S ↔ lift p i ⬝ᵥ c < 0 := by
  classical
  constructor
  · rintro ⟨c, hc, hd⟩
    refine ⟨c, fun i => ⟨hc i, ?_⟩⟩
    intro hi
    by_contra hn
    have := hd i hn
    linarith
  · rintro ⟨c, hc⟩
    by_cases hS : S.Nonempty
    · obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image S (fun i => lift p i ⬝ᵥ c) hS
      have hjneg := (hc j).mp hj
      let ε := -(lift p j ⬝ᵥ c) / 2
      have hε : 0 < ε := by dsimp only [ε]; linarith
      have he (i : ι) : lift p i ⬝ᵥ (c + Pi.single 3 ε) = lift p i ⬝ᵥ c + ε := by
        rw [dotProduct_add, dotProduct_single]
        change _ + 1 * ε = _
        ring
      refine ⟨c + Pi.single 3 ε, ?_, ?_⟩
      · intro i hi
        rw [he]
        have := hmax i hi
        dsimp only [ε]
        linarith
      · intro i hi
        rw [he]
        have hn : ¬ lift p i ⬝ᵥ c < 0 := fun h => hi ((hc i).mpr h)
        linarith
    · have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      refine ⟨Pi.single 3 1, ?_, ?_⟩
      · simp [hEmpty]
      · intro i _
        rw [dotProduct_single]
        change (0 : ℝ) < 1 * 1
        norm_num

open Classical in
/-- Give the kept lifts positive sign and the omitted lifts negative sign. -/
@[expose] def signedLift (p : ι → ℝ × ℝ) (S : Finset ι) (i : ι) : Fin 4 → ℝ :=
  if i ∈ S then lift p i else -lift p i

private theorem linear_dot (f : (Fin 4 → ℝ) →ₗ[ℝ] ℝ) (v : Fin 4 → ℝ) :
    f v = v ⬝ᵥ (fun k => f (Pi.single k 1)) := by
  classical
  have hv : v = ∑ k, v k • Pi.single k (1 : ℝ) := by
    ext k
    simp [Pi.single_apply]
  conv_lhs => rw [hv]
  simp [dotProduct]

/-- Failure of separation produces a convex dependence of signed lifts. -/
theorem zero_mem_convexHull_signed (p : ι → ℝ × ℝ) (S : Finset ι)
    (hn : ¬ IsRange p S) :
    (0 : Fin 4 → ℝ) ∈ convexHull ℝ (Set.range (signedLift p S)) := by
  classical
  by_contra hz
  have hclosed := (Set.finite_range (signedLift p S)).isClosed_convexHull (𝕜 := ℝ)
  obtain ⟨f, a, h0, hpos⟩ := geometric_hahn_banach_point_closed
    (convex_convexHull ℝ _) hclosed hz
  have ha : 0 < a := by simpa using h0
  apply hn
  refine ⟨fun k => -f (Pi.single k 1), ?_, ?_⟩
  · intro i hi
    have h := hpos (signedLift p S i) (subset_convexHull ℝ _ ⟨i, rfl⟩)
    simp only [signedLift, hi, ite_true] at h
    have hf := linear_dot f.toLinearMap (lift p i)
    change f (lift p i) = _ at hf
    rw [hf] at h
    change a < lift p i ⬝ᵥ (fun k => f (Pi.single k 1)) at h
    change lift p i ⬝ᵥ -(fun k => f (Pi.single k 1)) < 0
    rw [dotProduct_neg]
    linarith
  · intro i hi
    have h := hpos (signedLift p S i) (subset_convexHull ℝ _ ⟨i, rfl⟩)
    simp only [signedLift, hi, ite_false, map_neg] at h
    have hf := linear_dot f.toLinearMap (lift p i)
    change f (lift p i) = _ at hf
    rw [hf] at h
    change a < -(lift p i ⬝ᵥ (fun k => f (Pi.single k 1))) at h
    change 0 < lift p i ⬝ᵥ -(fun k => f (Pi.single k 1))
    rw [dotProduct_neg]
    linarith

/-- A five-index colored affine dependence with strictly positive coefficients.
No rational-plane restriction, nonseparation oracle or preselected witness is
assumed. The indices are distinct, so this is a five-element sub-instance. -/
theorem exists_five_dependence (p : ι → ℝ × ℝ) (hgp : LiftedGeneralPosition p)
    (S : Finset ι) (hn : ¬ IsRange p S) :
    ∃ (f : Fin 5 → ι) (w : Fin 5 → ℝ), Function.Injective f ∧
      (∀ k, 0 < w k) ∧ (∑ k, w k) = 1 ∧
      (∑ k, w k • signedLift p S (f k)) = 0 := by
  classical
  obtain ⟨κ, hκ, z, w, hz, hind, hw, hsum, hzero⟩ :=
    eq_pos_convex_span_of_mem_convexHull (zero_mem_convexHull_signed p S hn)
  let idx (k : κ) : ι := (hz (Set.mem_range_self k)).choose
  have hidx (k : κ) : signedLift p S (idx k) = z k :=
    (hz (Set.mem_range_self k)).choose_spec
  have hinj : Function.Injective idx := by
    intro i j he
    apply hind.injective
    rw [← hidx, ← hidx, he]
  have hle : Fintype.card κ ≤ 5 := by
    have h := hind.card_le_finrank_succ
    have hd := Submodule.finrank_le (vectorSpan ℝ (Set.range z))
    have hf : Module.finrank ℝ (Fin 4 → ℝ) = 4 := by simp
    omega
  have hgt : 4 < Fintype.card κ := by
    by_contra h
    let s : Finset ι := Finset.univ.image idx
    have hs : s.card = Fintype.card κ := Finset.card_image_of_injective _ hinj
    have hlin := hgp s (by omega)
    let e : κ → s := fun k => ⟨idx k, Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩⟩
    have he : Function.Injective e := fun i j h => hinj (congrArg Subtype.val h)
    have hl : LinearIndependent ℝ (fun k => lift p (idx k)) := hlin.comp e he
    have hsigned : LinearIndependent ℝ (fun k => signedLift p S (idx k)) := by
      convert hl.units_smul (fun k => if idx k ∈ S then (1 : ℝˣ) else -1) using 1
      funext k
      dsimp only [signedLift, Pi.smul_apply]
      split_ifs <;> simp_all
    have hwzero : ∀ k, w k = 0 :=
      (Fintype.linearIndependent_iff.mp hsigned) w (by simpa only [hidx] using hzero)
    have : (0 : ℝ) = 1 := by simpa only [hwzero, Finset.sum_const_zero] using hsum
    norm_num at this
  have hc : Fintype.card κ = 5 := by omega
  let e := Fintype.equivFinOfCardEq hc
  refine ⟨idx ∘ e.symm, w ∘ e.symm, hinj.comp e.symm.injective,
    fun k => hw _, ?_, ?_⟩
  · exact (e.symm.sum_comp w).trans hsum
  · have he := e.symm.sum_comp (fun k => w k • signedLift p S (idx k))
    change (∑ k, w (e.symm k) • signedLift p S (idx (e.symm k))) = 0
    rw [he]
    simpa only [hidx] using hzero

/-- Centered cross-scatter of an actual retained subset. -/
@[expose] noncomputable def scatter (p : ι → ℝ × ℝ) (S : Finset ι) : ℝ :=
  (∑ i ∈ S, (p i).1 * (p i).2) -
    (∑ i ∈ S, (p i).1) * (∑ i ∈ S, (p i).2) / S.card

/-- Unique minimization among all subsets of the same cardinality. -/
@[expose] def UniqueMinimum (p : ι → ℝ × ℝ) (S : Finset ι) : Prop :=
  ∀ T : Finset ι, T.card = S.card → T ≠ S → scatter p S < scatter p T

omit [Finite ι] in
open Classical in
/-- Exact change from replacing one retained observation by one omitted observation. -/
theorem scatter_swap [DecidableEq ι] (p : ι → ℝ × ℝ) (S : Finset ι) (a b : ι)
    (ha : a ∈ S) (hb : b ∉ S) :
    scatter p (insert b (S.erase a)) - scatter p S =
      (p b).1 * (p b).2 - (p a).1 * (p a).2 -
      (((∑ i ∈ S, (p i).1) * ((p b).2 - (p a).2) +
        (∑ i ∈ S, (p i).2) * ((p b).1 - (p a).1) +
        ((p b).1 - (p a).1) * ((p b).2 - (p a).2)) / S.card) := by
  classical
  have hba : b ∉ S.erase a := fun h => hb (Finset.mem_of_mem_erase h)
  have hc : (insert b (S.erase a)).card = S.card := by
    rw [Finset.card_insert_of_notMem hba, Finset.card_erase_of_mem ha]
    have : 0 < S.card := Finset.card_pos.mpr ⟨a, ha⟩
    omega
  unfold scatter
  rw [hc]
  simp only [Finset.sum_insert hba, Finset.sum_erase_eq_sub ha]
  ring

omit [Finite ι] in
open Classical in
/-- Unique optimality gives strict positivity of every single swap. -/
theorem UniqueMinimum.swap_pos [DecidableEq ι] (p : ι → ℝ × ℝ) (S : Finset ι)
    (hmin : UniqueMinimum p S) (a b : ι) (ha : a ∈ S) (hb : b ∉ S) :
    0 < scatter p (insert b (S.erase a)) - scatter p S := by
  classical
  apply sub_pos.mpr
  apply hmin
  · rw [Finset.card_insert_of_notMem (fun h => hb (Finset.mem_of_mem_erase h)),
      Finset.card_erase_of_mem ha]
    have := Finset.card_pos.mpr ⟨a, ha⟩
    omega
  · intro he
    have : b ∈ S := he ▸ Finset.mem_insert_self _ _
    exact hb this

omit [Finite ι] in
private theorem weighted_swap_identity [Fintype ι] (x y α γ : ι → ℝ) (m sx sy : ℝ) :
    (∑ a, ∑ b, α a * γ b *
      (m * (x b * y b - x a * y a) - sx * (y b - y a) - sy * (x b - x a) -
        (x b - x a) * (y b - y a))) =
      m * ((∑ a, α a) * (∑ b, γ b * (x b * y b)) -
        (∑ a, α a * (x a * y a)) * (∑ b, γ b)) -
      sx * ((∑ a, α a) * (∑ b, γ b * y b) - (∑ a, α a * y a) * (∑ b, γ b)) -
      sy * ((∑ a, α a) * (∑ b, γ b * x b) - (∑ a, α a * x a) * (∑ b, γ b)) -
      ((∑ a, α a) * (∑ b, γ b * (x b * y b)) -
        (∑ a, α a * x a) * (∑ b, γ b * y b) -
        (∑ a, α a * y a) * (∑ b, γ b * x b) +
        (∑ a, α a * (x a * y a)) * (∑ b, γ b)) := by
  classical
  simp only [Finset.sum_mul_sum]
  simp only [mul_sub, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

omit [Finite ι] in
/-- Lemma 5.6: matching convex combinations of kept and omitted saddle lifts
have strictly negative cross-scatter at a unique fixed-cardinality optimum.
The weights may vanish, but must be supported on the indicated sides. -/
theorem UniqueMinimum.witness_exclusion (p : ι → ℝ × ℝ) (S : Finset ι)
    (hmin : UniqueMinimum p S) {κ : Type*} [Fintype κ] (f : κ → ι) (α γ : κ → ℝ)
    (hα : ∀ i, 0 ≤ α i) (hγ : ∀ i, 0 ≤ γ i)
    (hαS : ∀ i, 0 < α i → f i ∈ S) (hγS : ∀ i, 0 < γ i → f i ∉ S)
    (hα1 : (∑ i, α i) = 1) (hγ1 : (∑ i, γ i) = 1)
    (hx : (∑ i, α i * (p (f i)).1) = ∑ i, γ i * (p (f i)).1)
    (hy : (∑ i, α i * (p (f i)).2) = ∑ i, γ i * (p (f i)).2)
    (hz : (∑ i, α i * ((p (f i)).1 * (p (f i)).2)) =
      ∑ i, γ i * ((p (f i)).1 * (p (f i)).2)) :
    (∑ i, α i * ((p (f i)).1 * (p (f i)).2)) -
      (∑ i, α i * (p (f i)).1) * (∑ i, α i * (p (f i)).2) < 0 := by
  classical
  have hapos : ∃ i, 0 < α i := by
    by_contra hn
    have hle := Finset.sum_nonpos (s := Finset.univ) (f := α)
      (fun i _ => not_lt.mp (not_exists.mp hn i))
    linarith
  have hgpos : ∃ i, 0 < γ i := by
    by_contra hn
    have hle := Finset.sum_nonpos (s := Finset.univ) (f := γ)
      (fun i _ => not_lt.mp (not_exists.mp hn i))
    linarith
  obtain ⟨a, ha⟩ := hapos
  obtain ⟨b, hb⟩ := hgpos
  have hm : (0 : ℝ) < S.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨f a, hαS a ha⟩
  let D (a b : κ) := (S.card : ℝ) * ((p (f b)).1 * (p (f b)).2 - (p (f a)).1 * (p (f a)).2) -
    (∑ i ∈ S, (p i).1) * ((p (f b)).2 - (p (f a)).2) -
    (∑ i ∈ S, (p i).2) * ((p (f b)).1 - (p (f a)).1) -
    ((p (f b)).1 - (p (f a)).1) * ((p (f b)).2 - (p (f a)).2)
  have hD : ∀ i j, 0 < α i → 0 < γ j → 0 < D i j := by
    intro i j hi hj
    have hswap := hmin.swap_pos p S (f i) (f j) (hαS i hi) (hγS j hj)
    rw [scatter_swap p S (f i) (f j) (hαS i hi) (hγS j hj)] at hswap
    have he : D i j = (S.card : ℝ) *
        (scatter p (insert (f j) (S.erase (f i))) - scatter p S) := by
      rw [scatter_swap p S (f i) (f j) (hαS i hi) (hγS j hj)]
      dsimp only [D]
      field_simp
      ring
    rw [he]
    exact mul_pos hm (hmin.swap_pos p S (f i) (f j) (hαS i hi) (hγS j hj))
  have hterm : ∀ i j, 0 ≤ α i * γ j * D i j := by
    intro i j
    by_cases hi : α i = 0
    · simp [hi]
    by_cases hj : γ j = 0
    · simp [hj]
    exact (mul_pos (mul_pos (lt_of_le_of_ne (hα i) (Ne.symm hi))
      (lt_of_le_of_ne (hγ j) (Ne.symm hj)))
      (hD i j (lt_of_le_of_ne (hα i) (Ne.symm hi))
        (lt_of_le_of_ne (hγ j) (Ne.symm hj)))).le
  have hE : 0 < ∑ i, ∑ j, α i * γ j * D i j := by
    apply Finset.sum_pos' (fun i _ => Finset.sum_nonneg fun j _ => hterm i j)
    refine ⟨a, Finset.mem_univ _, ?_⟩
    apply Finset.sum_pos' (fun j _ => hterm a j)
    exact ⟨b, Finset.mem_univ _, mul_pos (mul_pos ha hb) (hD a b ha hb)⟩
  have he := weighted_swap_identity (fun i => (p (f i)).1) (fun i => (p (f i)).2) α γ
    S.card (∑ i ∈ S, (p i).1) (∑ i ∈ S, (p i).2)
  change (∑ i, ∑ j, α i * γ j * D i j) = _ at he
  rw [hα1, hγ1, ← hx, ← hy, ← hz] at he
  nlinarith

omit [Finite ι] in
private theorem normalize_dependence (p : ι → ℝ × ℝ) (S : Finset ι)
    (f : Fin 5 → ι) (w : Fin 5 → ℝ) (hw : ∀ k, 0 < w k)
    (hsum : (∑ k, w k) = 1) (hzero : (∑ k, w k • signedLift p S (f k)) = 0) :
    ∃ α γ : Fin 5 → ℝ,
      (∀ k, 0 ≤ α k ∧ 0 ≤ γ k) ∧
      (∀ k, (0 < α k ↔ f k ∈ S) ∧ (0 < γ k ↔ f k ∉ S)) ∧
      (∑ k, α k) = 1 ∧ (∑ k, γ k) = 1 ∧
      (∑ k, α k • lift p (f k)) = ∑ k, γ k • lift p (f k) := by
  classical
  let α (k : Fin 5) := if f k ∈ S then 2 * w k else 0
  let γ (k : Fin 5) := if f k ∈ S then 0 else 2 * w k
  have hc (j : Fin 4) :
      (∑ k, α k * lift p (f k) j) = ∑ k, γ k * lift p (f k) j := by
    have hz := congrFun hzero j
    have he : (∑ k, α k * lift p (f k) j) - (∑ k, γ k * lift p (f k) j) =
        2 * (∑ k, (w k • signedLift p S (f k)) j) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      dsimp only [α, γ, signedLift]
      split_ifs <;> simp <;> ring
    simp only [Finset.sum_apply, Pi.zero_apply] at hz
    rw [← Finset.sum_apply, hzero, Pi.zero_apply, mul_zero] at he
    linarith
  have hc3 := hc 3
  norm_num [lift] at hc3
  have hab : (∑ k, α k) + (∑ k, γ k) = 2 := by
    rw [← Finset.sum_add_distrib]
    have he (k : Fin 5) : α k + γ k = 2 * w k := by dsimp only [α, γ]; split_ifs <;> ring
    simp only [he, ← Finset.mul_sum, hsum, mul_one]
  refine ⟨α, γ, ?_, ?_, by linarith, by linarith, ?_⟩
  · intro k
    have hwk := hw k
    dsimp only [α, γ]
    split_ifs <;> constructor <;> positivity
  · intro k
    dsimp only [α, γ]
    by_cases hk : f k ∈ S <;> simp [hk, hw k]
  · ext j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hc j

private theorem covariance_support (q : Fin 5 → ℝ × ℝ) (a : Fin 5 → ℝ)
    (ha : ∀ i, 0 ≤ a i) (h1 : (∑ i, a i) = 1)
    (hneg : (∑ i, a i * ((q i).1 * (q i).2)) -
      (∑ i, a i * (q i).1) * (∑ i, a i * (q i).2) < 0) :
    2 ≤ (Finset.univ.filter fun i => 0 < a i).card ∧
      ((Finset.univ.filter fun i => 0 < a i).card = 2 →
        ∃ i j, i ≠ j ∧ 0 < a i ∧ 0 < a j ∧
          ((q i).1 - (q j).1) * ((q i).2 - (q j).2) < 0) := by
  classical
  let A := Finset.univ.filter fun i => 0 < a i
  have hsum (z : Fin 5 → ℝ) : (∑ i, a i * z i) = ∑ i ∈ A, a i * z i := by
    apply (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro i _ hi
    have hz : a i = 0 := by
      have hn : ¬ 0 < a i := by
        simpa only [A, Finset.mem_filter, Finset.mem_univ, true_and] using hi
      exact le_antisymm (not_lt.mp hn) (ha i)
    simp [hz]
  have hmass : (∑ i ∈ A, a i) = 1 := by
    simpa only [mul_one] using (hsum (fun _ => 1)).symm.trans (by simpa using h1)
  have hA : A.Nonempty := by
    by_contra hn
    have hz : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [hz] at hmass
  change 2 ≤ A.card ∧ (A.card = 2 → _)
  constructor
  · by_contra hn
    have hc : A.card = 1 := by have := Finset.card_pos.mpr hA; omega
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
    rw [hsum (fun i => (q i).1 * (q i).2), hsum (fun i => (q i).1),
      hsum (fun i => (q i).2), hi] at hneg
    rw [hi] at hmass
    simp only [Finset.sum_singleton] at hmass hneg
    rw [hmass] at hneg
    nlinarith
  · intro hc
    obtain ⟨i, j, hij, he⟩ := Finset.card_eq_two.mp hc
    have hi : 0 < a i := (Finset.mem_filter.mp (show i ∈ A by rw [he]; simp)).2
    have hj : 0 < a j := (Finset.mem_filter.mp (show j ∈ A by rw [he]; simp)).2
    rw [hsum (fun i => (q i).1 * (q i).2), hsum (fun i => (q i).1),
      hsum (fun i => (q i).2), he] at hneg
    rw [he] at hmass
    simp only [Finset.sum_pair hij] at hmass hneg
    refine ⟨i, j, hij, hi, hj, ?_⟩
    have heq : a i * ((q i).1 * (q i).2) + a j * ((q j).1 * (q j).2) -
        (a i * (q i).1 + a j * (q j).1) * (a i * (q i).2 + a j * (q j).2) =
        a i * a j * (((q i).1 - (q j).1) * ((q i).2 - (q j).2)) := by
      have hai : a i = 1 - a j := by linarith
      rw [hai]
      ring
    rw [heq] at hneg
    by_contra hn
    have hprod := mul_nonneg (mul_pos hi hj).le (not_lt.mp hn)
    linarith

/-- A five-point Radon partition, with both normalized strictly supported sides
and the anti-monotone conclusion on either side of size two. -/
structure FiveWitness [DecidableEq ι] (p : ι → ℝ × ℝ) (S : Finset ι) where
  /-- Distinct original observation indices. -/
  index : Fin 5 → ι
  /-- No observation is counted twice. -/
  injective : Function.Injective index
  /-- Convex weights on the retained side. -/
  keptWeight : Fin 5 → ℝ
  /-- Convex weights on the omitted side. -/
  omittedWeight : Fin 5 → ℝ
  /-- Both sides have nonnegative weights. -/
  nonneg : ∀ k, 0 ≤ keptWeight k ∧ 0 ≤ omittedWeight k
  /-- Every point on each side has strictly positive weight. -/
  positive_iff : ∀ k, (0 < keptWeight k ↔ index k ∈ S) ∧
    (0 < omittedWeight k ↔ index k ∉ S)
  /-- The retained weights are normalized. -/
  kept_sum : (∑ k, keptWeight k) = 1
  /-- The omitted weights are normalized. -/
  omitted_sum : (∑ k, omittedWeight k) = 1
  /-- The two convex combinations coincide in homogeneous saddle coordinates. -/
  lift_eq : (∑ k, keptWeight k • lift p (index k)) = ∑ k, omittedWeight k • lift p (index k)
  /-- Exactly two or three witness observations are omitted. -/
  omitted_card : (Finset.univ.filter fun k => index k ∉ S).card = 2 ∨
    (Finset.univ.filter fun k => index k ∉ S).card = 3
  /-- Whichever side has two elements is an anti-monotone pair. -/
  pair : ∀ side : Bool,
    (Finset.univ.filter fun k => decide (index k ∈ S) = side).card = 2 →
      ∃ i j, i ≠ j ∧ decide (index i ∈ S) = side ∧ decide (index j ∈ S) = side ∧
        ((p (index i)).1 - (p (index j)).1) * ((p (index i)).2 - (p (index j)).2) < 0

/-- Theorem 5.7's five-point Radon and anti-monotone witness, extracted from
unique minimization among actual subsets, lifted general position and failure of
separation by any real affine plane. No witness is supplied as a hypothesis. -/
theorem UniqueMinimum.five_witness [DecidableEq ι] (p : ι → ℝ × ℝ) (S : Finset ι)
    (hmin : UniqueMinimum p S) (hgp : LiftedGeneralPosition p) (hn : ¬ IsRange p S) :
    Nonempty (FiveWitness p S) := by
  classical
  obtain ⟨f, w, hf, hw, hsum, hzero⟩ := exists_five_dependence p hgp S hn
  obtain ⟨α, γ, hnonneg, hpos, hα1, hγ1, heq⟩ := normalize_dependence p S f w hw hsum hzero
  have hcoord (j : Fin 4) : (∑ k, α k * lift p (f k) j) = ∑ k, γ k * lift p (f k) j := by
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun heq j
  have hx : (∑ k, α k * (p (f k)).1) = ∑ k, γ k * (p (f k)).1 := by
    simpa [lift] using hcoord 1
  have hy : (∑ k, α k * (p (f k)).2) = ∑ k, γ k * (p (f k)).2 := by
    simpa [lift] using hcoord 2
  have hz : (∑ k, α k * ((p (f k)).1 * (p (f k)).2)) =
      ∑ k, γ k * ((p (f k)).1 * (p (f k)).2) := by simpa [lift] using hcoord 0
  have hneg := hmin.witness_exclusion p S f α γ (fun k => (hnonneg k).1)
    (fun k => (hnonneg k).2) (fun k h => (hpos k).1.mp h) (fun k h => (hpos k).2.mp h)
    hα1 hγ1 hx hy hz
  have hnegγ : (∑ k, γ k * ((p (f k)).1 * (p (f k)).2)) -
      (∑ k, γ k * (p (f k)).1) * (∑ k, γ k * (p (f k)).2) < 0 := by
    rwa [← hx, ← hy, ← hz]
  obtain ⟨hαcard, hαpair⟩ := covariance_support (p ∘ f) α (fun k => (hnonneg k).1) hα1 hneg
  obtain ⟨hγcard, hγpair⟩ := covariance_support (p ∘ f) γ (fun k => (hnonneg k).2) hγ1 hnegγ
  have hA : (Finset.univ.filter fun k => 0 < α k) = Finset.univ.filter fun k => f k ∈ S := by
    ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and, (hpos k).1]
  have hB : (Finset.univ.filter fun k => 0 < γ k) = Finset.univ.filter fun k => f k ∉ S := by
    ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and, (hpos k).2]
  have hcount : (Finset.univ.filter fun k => f k ∈ S).card +
      (Finset.univ.filter fun k => f k ∉ S).card = 5 := by
    rw [Finset.card_filter_add_card_filter_not]
    decide
  refine ⟨⟨f, hf, α, γ, hnonneg, hpos, hα1, hγ1, heq, ?_, ?_⟩⟩
  · rw [hA] at hαcard
    rw [hB] at hγcard
    omega
  · intro side hc
    cases side with
    | false =>
      have hcard : (Finset.univ.filter fun k => 0 < γ k).card = 2 := by
        rw [hB]; simpa using hc
      obtain ⟨i, j, hij, hi, hj, hpair⟩ := hγpair hcard
      exact ⟨i, j, hij, by simpa using (hpos i).2.mp hi,
        by simpa using (hpos j).2.mp hj, hpair⟩
    | true =>
      have hcard : (Finset.univ.filter fun k => 0 < α k).card = 2 := by
        rw [hA]; simpa using hc
      obtain ⟨i, j, hij, hi, hj, hpair⟩ := hαpair hcard
      exact ⟨i, j, hij, by simpa using (hpos i).1.mp hi,
        by simpa using (hpos j).1.mp hj, hpair⟩

/-- Strict real affine separation on a specified sub-instance. -/
@[expose] def IsRangeOn (p : ι → ℝ × ℝ) (U S : Finset ι) : Prop :=
  ∃ c : Fin 4 → ℝ, ∀ i ∈ U, (i ∈ S → lift p i ⬝ᵥ c < 0) ∧
    (i ∉ S → 0 < lift p i ⬝ᵥ c)

omit [Finite ι] in
/-- The Radon witness prevents separation in every sub-instance containing it. -/
theorem FiveWitness.not_rangeOn [DecidableEq ι] (p : ι → ℝ × ℝ) (S : Finset ι) (W : FiveWitness p S)
    (U : Finset ι) (hU : ∀ k, W.index k ∈ U) : ¬ IsRangeOn p U S := by
  classical
  rintro ⟨c, hc⟩
  have he := congrArg (fun v => v ⬝ᵥ c) W.lift_eq
  simp only [sum_dotProduct, smul_dotProduct, smul_eq_mul] at he
  have hk : ∃ k, 0 < W.keptWeight k := by
    by_contra hn
    have hle := Finset.sum_nonpos (s := Finset.univ) (f := W.keptWeight)
      (fun k _ => not_lt.mp (not_exists.mp hn k))
    linarith [W.kept_sum]
  obtain ⟨k, hk⟩ := hk
  have hleft : (∑ i, W.keptWeight i * (lift p (W.index i) ⬝ᵥ c)) < 0 := by
    have hterm (i : Fin 5) : W.keptWeight i * (lift p (W.index i) ⬝ᵥ c) ≤ 0 := by
      by_cases hi : W.keptWeight i = 0
      · simp [hi]
      have hp := lt_of_le_of_ne (W.nonneg i).1 (Ne.symm hi)
      exact (mul_neg_of_pos_of_neg hp ((hc _ (hU i)).1 ((W.positive_iff i).1.mp hp))).le
    have hh := Finset.sum_lt_sum (s := Finset.univ) (g := fun _ => (0 : ℝ))
      (fun i _ => hterm i) ⟨k, Finset.mem_univ _,
        mul_neg_of_pos_of_neg hk ((hc _ (hU k)).1 ((W.positive_iff k).1.mp hk))⟩
    simpa using hh
  have hright : 0 ≤ ∑ i, W.omittedWeight i * (lift p (W.index i) ⬝ᵥ c) := by
    apply Finset.sum_nonneg
    intro i _
    by_cases hi : W.omittedWeight i = 0
    · simp [hi]
    have hp := lt_of_le_of_ne (W.nonneg i).2 (Ne.symm hi)
    exact (mul_pos hp ((hc _ (hU i)).2 ((W.positive_iff i).2.mp hp))).le
  linarith

open Classical in
/-- Theorem 5.7 including localization: only two or three omitted observations
are needed, unique optimality persists among all same-size subsets of that
sub-instance, and no real affine plane selects the optimum there. The returned
`FiveWitness` includes the Radon weights and the anti-monotone pair conclusion. -/
theorem UniqueMinimum.local_witness [DecidableEq ι] (p : ι → ℝ × ℝ) (S : Finset ι)
    (hmin : UniqueMinimum p S) (hgp : LiftedGeneralPosition p) (hn : ¬ IsRange p S) :
    ∃ W : FiveWitness p S, ∃ D : Finset ι,
      Disjoint S D ∧ (D.card = 2 ∨ D.card = 3) ∧
      (∀ k, W.index k ∈ S ∪ D) ∧
      (∀ T ⊆ S ∪ D, T.card = S.card → T ≠ S → scatter p S < scatter p T) ∧
      ¬ IsRangeOn p (S ∪ D) S := by
  classical
  obtain ⟨W⟩ := hmin.five_witness p S hgp hn
  let D := (Finset.univ.filter fun k => W.index k ∉ S).image W.index
  have hdis : Disjoint S D := by
    apply Finset.disjoint_left.mpr
    intro i hi hd
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hd
    exact (Finset.mem_filter.mp hk).2 hi
  have hc : D.card = (Finset.univ.filter fun k => W.index k ∉ S).card :=
    Finset.card_image_of_injective _ W.injective
  have hU (k : Fin 5) : W.index k ∈ S ∪ D := by
    by_cases hk : W.index k ∈ S
    · exact Finset.mem_union_left _ hk
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k, by simp [hk], rfl⟩)
  exact ⟨W, D, hdis, hc ▸ W.omitted_card, hU,
    fun T _ hcard hne => hmin T hcard hne, W.not_rangeOn p S (S ∪ D) hU⟩

end Cslib.LeastSquares.Geometry
