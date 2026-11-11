/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Algebra/Polynomial/Sturm/Sequence.lean`)

public import CslibFrontier.Init
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Sturm.Sequence
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.List.SignVariations
public import Mathlib.FieldTheory.Separable
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Polynomial.SignRight
import Mathlib.FieldTheory.Perfect
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Tactic.Linarith

/-!
# Sturm's theorem for separable real polynomials

This file proves Sturm's theorem over `ℝ[X]` on top of Mathlib's `Polynomial.sturmSeq`,
`Polynomial.signRight`, and `List.signVariations` (see [BasuPollackRoy2006]).

For any separable (equivalently squarefree) real polynomial `p`, `Polynomial.sturmVariations p x`
counts the sign variations of the canonical Sturm sequence `sturmSeq p (derivative p)` evaluated
at `x`. Across any point `x`, `sturmVariations p` is locally constant away from roots of `p`,
constant on a right neighborhood `(x, x + δ)`, and increases by `1` on a left neighborhood
`(x - δ, x)` precisely when `x` is a root of `p`. Consequently,
`sturmVariations p x + #{r ∈ p.roots.toFinset | r ≤ x}` is locally constant on `ℝ`, hence
constant, yielding the exact root-count identity on half-open intervals `(a, b]`.

## Main definitions

* `Polynomial.sturmVariations`: sign variations of `sturmSeq p (derivative p)` evaluated at `x`.

## Main results

* `Polynomial.sturmSeq_map`: `Polynomial.sturmSeq` commutes with `Polynomial.map` along an
  injective ring homomorphism between fields.
* `Polynomial.sturmVariations_sub_eq_card_roots_Ioc`: Sturm's theorem on `(a, b]` for separable
  `p : ℝ[X]`.
* `Polynomial.sturmVariations_sub_eq_card_roots_Ioc_of_squarefree`: the squarefree form over `ℝ`.
* `Polynomial.sturmVariations_sub_eq_card_roots_Ioo`: open-interval form when the right endpoint is
  not a root.
* `Polynomial.sturmVariations_sub_eq_card_roots_Icc`: closed-interval form when the left endpoint is
  not a root.
* `Polynomial.sturmVariations_antitone`: `sturmVariations p` is antitone for separable `p`.

## References

* [S. Basu, R. Pollack, and M.-F. Roy, *Algorithms in Real Algebraic Geometry*][BasuPollackRoy2006]
  (locator unverified)
-/

public section

open Filter Set SignType
open scoped Topology

namespace Polynomial

private theorem sturmSeq_map_aux {K L : Type*} [Field K] [DecidableEq K] [Field L]
    [DecidableEq L] (f : K →+* L) :
    ∀ (m : ℕ) (p q : K[X]), (if q = 0 then 0 else q.natDegree + 1) ≤ m →
      Polynomial.sturmSeq (p.map f) (q.map f) =
        (Polynomial.sturmSeq p q).map (Polynomial.map f)
  | m, p, q, hm => by
    by_cases hp : p = 0
    · subst hp
      simp only [Polynomial.map_zero, Polynomial.sturmSeq_zero_left, List.map_nil]
    · have hpf : p.map f ≠ 0 := (Polynomial.map_ne_zero_iff f.injective).mpr hp
      by_cases hq : q = 0
      · subst hq
        simp only [Polynomial.map_zero, Polynomial.sturmSeq_zero_right,
          ite_eq_right (fun h => absurd h hp), ite_eq_right (fun h => absurd h hpf),
          List.map_cons, List.map_nil]
      · have hqf : q.map f ≠ 0 := (Polynomial.map_ne_zero_iff f.injective).mpr hq
        obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := by
          have hpos : 0 < m := by
            rw [ite_eq_right (fun h => absurd h hq)] at hm
            omega
          exact Nat.exists_eq_succ_of_ne_zero hpos.ne'
        subst hk
        let r := -p % q
        have hr_meas : (if r = 0 then 0 else r.natDegree + 1) ≤ k := by
          rw [ite_eq_right (fun h => absurd h hq)] at hm
          by_cases hr0 : r = 0
          · simp only [hr0, ↓reduceIte, Nat.zero_le]
          · rw [ite_eq_right (fun h => absurd h hr0)]
            have hlt : r.degree < q.degree := Polynomial.degree_mod_lt (-p) hq
            have hnat : r.natDegree < q.natDegree :=
              (Polynomial.natDegree_lt_iff_degree_lt hr0).mpr
                (by rwa [← Polynomial.degree_eq_natDegree hq])
            omega
        have ih := sturmSeq_map_aux f k q r hr_meas
        rw [Polynomial.sturmSeq_cons hp, Polynomial.sturmSeq_cons hpf, List.map_cons, ← ih,
          ← Polynomial.map_neg, ← Polynomial.map_mod]

/-- `Polynomial.sturmSeq` commutes with `Polynomial.map` along any ring homomorphism between
fields. -/
theorem sturmSeq_map {K L : Type*} [Field K] [DecidableEq K] [Field L] [DecidableEq L]
    (f : K →+* L) (p q : K[X]) :
    Polynomial.sturmSeq (p.map f) (q.map f) = (Polynomial.sturmSeq p q).map (Polynomial.map f) :=
  sturmSeq_map_aux f (if q = 0 then 0 else q.natDegree + 1) p q le_rfl

/-- The number of sign variations of the canonical Sturm sequence `sturmSeq p (derivative p)`
evaluated at `x : ℝ`. -/
@[expose] noncomputable def sturmVariations (p : ℝ[X]) (x : ℝ) : ℕ :=
  open Classical in
  ((sturmSeq p (derivative p)).map (eval x)).signVariations

/-- Any `IsCoprime p q` is preserved under the signed remainder step `(p, q) ↦ (q, -p % q)`. -/
private theorem isCoprime_neg_mod {K : Type*} [Field K] {p q : K[X]} (h : IsCoprime p q) :
    IsCoprime q (-p % q) := by
  rcases h with ⟨a, b, hab⟩
  refine ⟨b - a * (-p / q), -a, ?_⟩
  have hdiv := EuclideanDomain.div_add_mod (-p) q
  linear_combination hab - a * hdiv

/-- Predicate capturing the local Sturm-chain invariants at `x : ℝ` for a list of polynomials:
no element is identically zero, the list is nonempty and its last entry is nonzero at `x`,
no two adjacent entries vanish simultaneously at `x`, and at any interior zero the neighboring
entries have opposite nonzero signs. -/
private inductive IsSturmChainAt (x : ℝ) : List ℝ[X] → Prop
  | singleton {f : ℝ[X]} (hf0 : f ≠ 0) (hfx : f.eval x ≠ 0) : IsSturmChainAt x [f]
  | cons {f g : ℝ[X]} {t : List ℝ[X]} (hf0 : f ≠ 0)
      (hpair : ¬(f.eval x = 0 ∧ g.eval x = 0))
      (htriple : ∀ h t', t = h :: t' → g.eval x = 0 → sign (f.eval x) = -sign (h.eval x))
      (htail : IsSturmChainAt x (g :: t)) :
      IsSturmChainAt x (f :: g :: t)

private theorem isSturmChainAt_ne_nil {x : ℝ} {L : List ℝ[X]} (h : IsSturmChainAt x L) :
    L ≠ [] := by
  cases h <;> simp

private theorem isSturmChainAt_sturmSeq {p q : ℝ[X]} (hp : p ≠ 0) (hcop : IsCoprime p q)
    (x : ℝ) :
    open Classical in IsSturmChainAt x (sturmSeq p q) := by
  classical
  induction p, q using sturmSeq.induct with
  | case1 q => exact absurd rfl hp
  | case2 p q hp0 ih =>
    rw [sturmSeq_cons hp0]
    by_cases hq0 : q = 0
    · subst hq0
      rw [sturmSeq_zero_left]
      have hunit : IsUnit p := isCoprime_zero_right.mp hcop
      obtain ⟨c, hc, hpc⟩ := isUnit_iff.mp hunit
      have hne : p.eval x ≠ 0 := by
        rw [← hpc, eval_C]
        exact hc.ne_zero
      exact IsSturmChainAt.singleton hp0 hne
    · have hcop' : IsCoprime q (-p % q) := isCoprime_neg_mod hcop
      have htail := ih hq0 hcop'
      obtain ⟨t, ht⟩ : ∃ t, sturmSeq q (-p % q) = q :: t := by
        rw [sturmSeq_cons hq0]
        exact ⟨_, rfl⟩
      rw [ht] at htail ⊢
      refine IsSturmChainAt.cons hp0 ?_ ?_ htail
      · rintro ⟨hpx, hqx⟩
        obtain ⟨a, b, hab⟩ := hcop
        have hev := congrArg (eval x) hab
        simp only [eval_add, eval_mul, hpx, hqx, mul_zero, add_zero, eval_one, zero_ne_one] at hev
      · intro h t' ht' hqx
        have hrem : h = -p % q := by
          have := sturmSeq_cons (p := q) (q := -p % q) hq0
          rw [ht] at this
          rcases List.cons.inj this with ⟨_, hsub⟩
          have hr_ne : -p % q ≠ 0 := by
            intro hzero
            rw [hzero, sturmSeq_zero_left] at hsub
            rw [hsub] at ht'
            exact List.cons_ne_nil _ _ ht'.symm
          rw [sturmSeq_cons hr_ne, ht'] at hsub
          exact (List.cons.inj hsub).1
        subst hrem
        have hpx : p.eval x ≠ 0 := by
          intro hpx0
          obtain ⟨a, b, hab⟩ := hcop
          have hev := congrArg (eval x) hab
          simp only [eval_add, eval_mul, hpx0, hqx, mul_zero, add_zero, eval_one,
            zero_ne_one] at hev
        rw [eval_mod_eq_self_of_root hqx, eval_neg, Left.sign_neg, neg_neg]

/-- If `L` is a Sturm chain at `x` whose head does not vanish at `x`, and `y` preserves the sign
of every entry of `L` that does not vanish at `x`, then `L` has the same number of sign variations
at `y` and at `x`. -/
private theorem signVariations_eval_eq_of_isSturmChainAt {x y : ℝ} :
    ∀ {L : List ℝ[X]}, IsSturmChainAt x L →
      (∀ f, L.head? = some f → f.eval x ≠ 0) →
      (∀ f ∈ L, f.eval x ≠ 0 → sign (f.eval y) = sign (f.eval x)) →
      (L.map (eval y)).signVariations = (L.map (eval x)).signVariations
  | [], h, _, _ => absurd rfl (isSturmChainAt_ne_nil h)
  | [_], _, _, _ => by simp only [List.map_cons, List.map_nil, List.signVariations_singleton]
  | f :: g :: t, hchain, hhead, hsign => by
    cases hchain with
    | cons hf0 hpair htriple htail =>
      have hfx : f.eval x ≠ 0 := hhead f rfl
      have hfy_sign : sign (f.eval y) = sign (f.eval x) :=
        hsign f List.mem_cons_self hfx
      have hfy : f.eval y ≠ 0 := by
        rw [← sign_ne_zero, hfy_sign, sign_ne_zero]
        exact hfx
      by_cases hgx : g.eval x = 0
      · have hne_t : t ≠ [] := by
          intro ht0
          subst ht0
          cases htail with
          | singleton _ hgx' => exact hgx' hgx
        obtain ⟨h, t', rfl⟩ := List.exists_cons_of_ne_nil hne_t
        have hsign_fh : sign (f.eval x) = -sign (h.eval x) := htriple h t' rfl hgx
        have hhx : h.eval x ≠ 0 := by
          cases htail with
          | cons _ hpair' _ _ => exact fun hh => hpair' ⟨hgx, hh⟩
        have hhy_sign : sign (h.eval y) = sign (h.eval x) :=
          hsign h (by simp only [List.mem_cons, true_or, or_true]) hhx
        have hhy : h.eval y ≠ 0 := by
          rw [← sign_ne_zero, hhy_sign, sign_ne_zero]
          exact hhx
        have hhtail : IsSturmChainAt x (h :: t') := by
          cases htail with
          | cons _ _ _ htail' => exact htail'
        have ih := signVariations_eval_eq_of_isSturmChainAt hhtail (fun _ h0 => by
          cases h0; exact hhx) (fun q hq => hsign q (by
            simp only [List.mem_cons] at hq ⊢; exact Or.inr (Or.inr hq)))
        simp only [List.map_cons] at ih ⊢
        rw [hgx, List.signVariations_cons_zero_cons]
        have hfx_ne_hhx : sign (f.eval x) ≠ sign (h.eval x) := by
          rw [hsign_fh]
          have hhs : sign (h.eval x) ≠ 0 := sign_ne_zero.mpr hhx
          cases hsh : sign (h.eval x) <;> simp_all
        rw [List.signVariations_cons_cons_of_ne_zero _ hfx hhx, ite_eq_right hfx_ne_hhx]
        by_cases hgy : g.eval y = 0
        · rw [hgy, List.signVariations_cons_zero_cons]
          have hfy_ne_hhy : sign (f.eval y) ≠ sign (h.eval y) := by
            rw [hfy_sign, hhy_sign]; exact hfx_ne_hhx
          rw [List.signVariations_cons_cons_of_ne_zero _ hfy hhy, ite_eq_right hfy_ne_hhy, ih]
        · rw [List.signVariations_cons_cons_of_ne_zero _ hfy hgy,
            List.signVariations_cons_cons_of_ne_zero _ hgy hhy, ih]
          have hopp : sign (f.eval y) = -sign (h.eval y) := by
            rw [hfy_sign, hhy_sign, hsign_fh]
          have hsf : sign (f.eval y) ≠ 0 := sign_ne_zero.mpr hfy
          have hsg : sign (g.eval y) ≠ 0 := sign_ne_zero.mpr hgy
          have hsh : sign (h.eval y) ≠ 0 := sign_ne_zero.mpr hhy
          rcases (sign (f.eval y)).trichotomy with hs1 | hs1 | hs1 <;>
            rcases (sign (g.eval y)).trichotomy with hs2 | hs2 | hs2 <;>
            rcases (sign (h.eval y)).trichotomy with hs3 | hs3 | hs3 <;>
            simp_all
      · have hgy_sign : sign (g.eval y) = sign (g.eval x) :=
          hsign g (by simp only [List.mem_cons, true_or, or_true]) hgx
        have hgy : g.eval y ≠ 0 := by
          rw [← sign_ne_zero, hgy_sign, sign_ne_zero]
          exact hgx
        have ih := signVariations_eval_eq_of_isSturmChainAt htail
          (fun _ h0 => by cases h0; exact hgx)
          (fun q hq => hsign q (List.mem_cons_of_mem f hq))
        simp only [List.map_cons] at ih ⊢
        rw [List.signVariations_cons_cons_of_ne_zero _ hfy hgy,
          List.signVariations_cons_cons_of_ne_zero _ hfx hgx, hfy_sign, hgy_sign, ih]

/-- Near any point `x`, every polynomial in `L` that does not vanish at `x` preserves its sign. -/
private theorem eventually_sign_eq_of_mem {x : ℝ} (L : List ℝ[X]) :
    ∀ᶠ y in 𝓝 x, ∀ f ∈ L, f.eval x ≠ 0 → sign (f.eval y) = sign (f.eval x) := by
  have hall : ∀ᶠ y in 𝓝 x, ∀ f ∈ L.toFinset, f.eval x ≠ 0 → sign (f.eval y) = sign (f.eval x) := by
    refine (Filter.eventually_all_finset L.toFinset).mpr fun f _ => ?_
    by_cases hfx : f.eval x = 0
    · exact Eventually.of_forall fun _ h => absurd hfx h
    · have hcont := (continuousAt_sign_of_ne_zero hfx).tendsto.comp (f.continuous.tendsto x)
      rw [nhds_discrete SignType, tendsto_pure] at hcont
      exact hcont.mono fun y hy _ => hy
  exact hall.mono fun y hy f hf hfx => hy f (List.mem_toFinset.mpr hf) hfx

/-- To the left of a simple root `x` of `p` (`p.eval x = 0` and `(derivative p).eval x ≠ 0`),
`sign (p.eval y)` is opposite to `sign ((derivative p).eval x)`. -/
private theorem eventually_sign_eval_nhdsLT_of_eval_eq_zero {x : ℝ} {p : ℝ[X]}
    (hpx : p.eval x = 0) (hdp : (derivative p).eval x ≠ 0) :
    ∀ᶠ y in 𝓝[<] x, sign (p.eval y) = -sign ((derivative p).eval x) := by
  have hcont : ∀ᶠ c in 𝓝[<] x, sign ((derivative p).eval c) = sign ((derivative p).eval x) := by
    have h := ((continuousAt_sign_of_ne_zero hdp).tendsto.comp
      ((derivative p).continuous.tendsto x)).mono_left (nhdsWithin_le_nhds (s := Set.Iio x))
    rw [nhds_discrete SignType, tendsto_pure] at h
    exact h
  obtain ⟨a, ha, ha_sub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hcont
  refine mem_nhdsLT_iff_exists_Ioo_subset.mpr ⟨a, ha, fun y hy => ?_⟩
  obtain ⟨c, ⟨hc1, hc2⟩, hc3⟩ :=
    exists_deriv_eq_slope (fun z => p.eval z) hy.2 p.continuousOn p.differentiableOn
  rw [Polynomial.deriv, hpx, zero_sub, eq_div_iff (sub_pos.mpr hy.2).ne'] at hc3
  have hpy : p.eval y = (y - x) * (derivative p).eval c := by linarith
  have hc_sign : sign ((derivative p).eval c) = sign ((derivative p).eval x) :=
    ha_sub ⟨lt_trans hy.1 hc1, hc2⟩
  change sign (p.eval y) = -sign ((derivative p).eval x)
  rw [hpy, sign_mul, sign_neg (sub_neg.mpr hy.2), hc_sign, neg_one_mul]

/-- If `p` is separable and does not vanish at `x`, `sturmVariations p` is locally constant
at `x`. -/
private theorem eventually_sturmVariations_of_eval_ne_zero {p : ℝ[X]} (hp : p.Separable)
    {x : ℝ} (hpx : p.eval x ≠ 0) :
    ∀ᶠ y in 𝓝 x, sturmVariations p y = sturmVariations p x := by
  classical
  have hchain := isSturmChainAt_sturmSeq hp.ne_zero hp x
  refine (eventually_sign_eq_of_mem (sturmSeq p (derivative p))).mono fun y hy => ?_
  simp only [sturmVariations]
  exact signVariations_eval_eq_of_isSturmChainAt hchain (fun f hf => by
    rw [head?_sturmSeq hp.ne_zero] at hf
    cases hf
    exact hpx) hy

/-- If `p` is separable and vanishes at `x`, then `sturmVariations p` is constant immediately to
the right of `x` and increases by `1` immediately to the left of `x`. -/
private theorem eventually_sturmVariations_of_eval_eq_zero {p : ℝ[X]} (hp : p.Separable)
    {x : ℝ} (hpx : p.eval x = 0) :
    (∀ᶠ y in 𝓝[>] x, sturmVariations p y = sturmVariations p x) ∧
    (∀ᶠ y in 𝓝[<] x, sturmVariations p y = sturmVariations p x + 1) := by
  classical
  have hdne : (derivative p).eval x ≠ 0 := by
    intro hd0
    obtain ⟨a, b, hab⟩ := hp
    have hev := congrArg (eval x) hab
    simp only [eval_add, eval_mul, hpx, hd0, mul_zero, add_zero, eval_one, zero_ne_one] at hev
  have hdp0 : derivative p ≠ 0 := fun h => hdne (by simp [h])
  have hcop' : IsCoprime (derivative p) (-p % derivative p) :=
    isCoprime_neg_mod hp
  have htail_chain := isSturmChainAt_sturmSeq hdp0 hcop' x
  set tail := sturmSeq (derivative p) (-p % derivative p) with htail_def
  have hseq_eq : sturmSeq p (derivative p) = p :: tail := sturmSeq_cons hp.ne_zero
  have htail_eq : ∀ᶠ y in 𝓝 x,
      (tail.map (eval y)).signVariations = sturmVariations p x := by
    refine (eventually_sign_eq_of_mem tail).mono fun y hy => ?_
    have hvar : (tail.map (eval y)).signVariations = (tail.map (eval x)).signVariations :=
      signVariations_eval_eq_of_isSturmChainAt htail_chain (fun f hf => by
        rw [htail_def, head?_sturmSeq hdp0] at hf
        cases hf
        exact hdne) hy
    rw [hvar, sturmVariations, hseq_eq, List.map_cons, hpx, List.signVariations_zero_cons]
  have hhead_tail : ∃ rest, tail = derivative p :: rest := by
    rw [htail_def, sturmSeq_cons hdp0]
    exact ⟨_, rfl⟩
  obtain ⟨rest, hrest⟩ := hhead_tail
  have hdp_sign : ∀ᶠ y in 𝓝 x, sign ((derivative p).eval y) = sign ((derivative p).eval x) := by
    have h := (continuousAt_sign_of_ne_zero hdne).tendsto.comp ((derivative p).continuous.tendsto x)
    rw [nhds_discrete SignType, tendsto_pure] at h
    exact h
  constructor
  · have hright : ∀ᶠ y in 𝓝[>] x, sign (p.eval y) = sign ((derivative p).eval x) := by
      have h1 := eventually_sign_eq_signRight x p
      rw [signRight_of_eval_eq_zero hpx, signRight_of_eval_ne_zero hdne] at h1
      exact h1
    refine ((htail_eq.filter_mono nhdsWithin_le_nhds).and
      ((hdp_sign.filter_mono nhdsWithin_le_nhds).and hright)).mono ?_
    rintro y ⟨htail_y, hdp_y, hp_y⟩
    have hpy_ne : p.eval y ≠ 0 := by
      rw [← sign_ne_zero, hp_y, sign_ne_zero]
      exact hdne
    have hdy_ne : (derivative p).eval y ≠ 0 := by
      rw [← sign_ne_zero, hdp_y, sign_ne_zero]
      exact hdne
    have htail_y' : ((derivative p).eval y :: rest.map (eval y)).signVariations =
        sturmVariations p x := by
      simpa only [hrest, List.map_cons] using htail_y
    conv_lhs =>
      rw [sturmVariations, hseq_eq, hrest, List.map_cons, List.map_cons,
        List.signVariations_cons_cons_of_ne_zero _ hpy_ne hdy_ne, hp_y, hdp_y, ite_eq_left rfl,
        add_zero, htail_y']
  · have hleft := eventually_sign_eval_nhdsLT_of_eval_eq_zero hpx hdne
    refine ((htail_eq.filter_mono nhdsWithin_le_nhds).and
      ((hdp_sign.filter_mono nhdsWithin_le_nhds).and hleft)).mono ?_
    rintro y ⟨htail_y, hdp_y, hp_y⟩
    have hpy_ne : p.eval y ≠ 0 := fun h => by
      rw [h, sign_zero] at hp_y
      apply sign_ne_zero.mpr hdne
      cases hs : sign ((derivative p).eval x)
      · rfl
      · rw [hs] at hp_y; contradiction
      · rw [hs] at hp_y; contradiction
    have hdy_ne : (derivative p).eval y ≠ 0 := by
      rw [← sign_ne_zero, hdp_y, sign_ne_zero]
      exact hdne
    have hne_sign : sign (p.eval y) ≠ sign ((derivative p).eval y) := by
      rw [hp_y, hdp_y]
      have hs : sign ((derivative p).eval x) ≠ 0 := sign_ne_zero.mpr hdne
      cases h : sign ((derivative p).eval x) <;> simp_all
    have htail_y' : ((derivative p).eval y :: rest.map (eval y)).signVariations =
        sturmVariations p x := by
      simpa only [hrest, List.map_cons] using htail_y
    conv_lhs =>
      rw [sturmVariations, hseq_eq, hrest, List.map_cons, List.map_cons,
        List.signVariations_cons_cons_of_ne_zero _ hpy_ne hdy_ne, ite_eq_right hne_sign, htail_y']

/-- Combining left-neighborhood, value-at-`x`, and right-neighborhood statements on `ℝ` into a
full `𝓝 x` statement. -/
private theorem eventually_nhds_of_lt_of_gt {P : ℝ → Prop} {x : ℝ} (hx : P x)
    (hlt : ∀ᶠ y in 𝓝[<] x, P y) (hgt : ∀ᶠ y in 𝓝[>] x, P y) : ∀ᶠ y in 𝓝 x, P y := by
  obtain ⟨a, ha, ha_sub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hlt
  obtain ⟨b, hb, hb_sub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hgt
  refine Filter.mem_of_superset (Ioo_mem_nhds ha hb) fun y hy => ?_
  rcases lt_trichotomy y x with hlt' | rfl | hgt'
  · exact ha_sub ⟨hy.1, hlt'⟩
  · exact hx
  · exact hb_sub ⟨hgt', hy.2⟩

/-- The augmented function `sturmVariations p x + #{r ∈ p.roots.toFinset | r ≤ x}` is locally
constant on `ℝ` for every separable `p : ℝ[X]`. -/
private theorem isLocallyConstant_sturmVariations_add_card {p : ℝ[X]} (hp : p.Separable) :
    IsLocallyConstant (fun x : ℝ =>
      sturmVariations p x + (p.roots.toFinset.filter (· ≤ x)).card) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  have hno_other : ∀ᶠ y in 𝓝 x,
      ∀ r ∈ p.roots.toFinset, r ≠ x → (r ≤ y ↔ r ≤ x) := by
    refine (Filter.eventually_all_finset p.roots.toFinset).mpr fun r _ => ?_
    by_cases hrx : r = x
    · exact Eventually.of_forall fun _ h => absurd hrx h
    · rcases lt_or_gt_of_ne hrx with hlt | hgt
      · filter_upwards [lt_mem_nhds hlt] with y hy _
        exact iff_of_true hy.le hlt.le
      · filter_upwards [gt_mem_nhds hgt] with y hy _
        exact iff_of_false (not_le_of_gt hy) (not_le_of_gt hgt)
  have hgt_filter : ∀ᶠ y in 𝓝[>] x,
      (p.roots.toFinset.filter (· ≤ y)).card = (p.roots.toFinset.filter (· ≤ x)).card := by
    refine ((hno_other.filter_mono nhdsWithin_le_nhds).and eventually_mem_nhdsWithin).mono ?_
    rintro y ⟨hy, hxy⟩
    congr 1
    ext r
    simp only [Finset.mem_filter, and_congr_right_iff]
    intro hr
    by_cases hrx : r = x
    · subst hrx
      exact iff_of_true (le_of_lt hxy) le_rfl
    · exact hy r hr hrx
  have hlt_filter : ∀ᶠ y in 𝓝[<] x,
      (p.roots.toFinset.filter (· ≤ y)).card + (if p.eval x = 0 then 1 else 0) =
        (p.roots.toFinset.filter (· ≤ x)).card := by
    refine ((hno_other.filter_mono nhdsWithin_le_nhds).and eventually_mem_nhdsWithin).mono ?_
    rintro y ⟨hy, hyx⟩
    by_cases hpx : p.eval x = 0
    · have hxmem : x ∈ p.roots.toFinset :=
        Multiset.mem_toFinset.mpr ((mem_roots hp.ne_zero).mpr hpx)
      have hxnot : x ∉ p.roots.toFinset.filter (· ≤ y) := by
        simp only [Finset.mem_filter, not_and, not_le]
        intro _
        exact hyx
      have heq : p.roots.toFinset.filter (· ≤ x) =
          insert x (p.roots.toFinset.filter (· ≤ y)) := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hr, hle⟩
          rcases eq_or_ne r x with rfl | hrx
          · exact Or.inl rfl
          · exact Or.inr ⟨hr, (hy r hr hrx).mpr hle⟩
        · rintro (rfl | ⟨hr, hle⟩)
          · exact ⟨hxmem, le_rfl⟩
          · by_cases hrx : r = x
            · subst hrx; exact ⟨hxmem, le_rfl⟩
            · exact ⟨hr, (hy r hr hrx).mp hle⟩
      rw [ite_eq_left hpx, heq, Finset.card_insert_of_notMem hxnot, add_comm]
    · rw [ite_eq_right hpx, add_zero]
      congr 1
      ext r
      simp only [Finset.mem_filter, and_congr_right_iff]
      intro hr
      have hrx : r ≠ x := fun h => hpx (h ▸ isRoot_of_mem_roots (Multiset.mem_toFinset.mp hr))
      exact hy r hr hrx
  by_cases hpx : p.eval x = 0
  · obtain ⟨hsv_gt, hsv_lt⟩ := eventually_sturmVariations_of_eval_eq_zero hp hpx
    have hgt : ∀ᶠ y in 𝓝[>] x,
        sturmVariations p y + (p.roots.toFinset.filter (· ≤ y)).card =
          sturmVariations p x + (p.roots.toFinset.filter (· ≤ x)).card := by
      filter_upwards [hsv_gt, hgt_filter] with y hy1 hy2
      rw [hy1, hy2]
    have hlt : ∀ᶠ y in 𝓝[<] x,
        sturmVariations p y + (p.roots.toFinset.filter (· ≤ y)).card =
          sturmVariations p x + (p.roots.toFinset.filter (· ≤ x)).card := by
      filter_upwards [hsv_lt, hlt_filter] with y hy1 hy2
      rw [ite_eq_left hpx] at hy2
      omega
    exact eventually_nhds_of_lt_of_gt rfl hlt hgt
  · have hsv := eventually_sturmVariations_of_eval_ne_zero hp hpx
    have hgt : ∀ᶠ y in 𝓝[>] x,
        sturmVariations p y + (p.roots.toFinset.filter (· ≤ y)).card =
          sturmVariations p x + (p.roots.toFinset.filter (· ≤ x)).card := by
      filter_upwards [hsv.filter_mono nhdsWithin_le_nhds, hgt_filter] with y hy1 hy2
      rw [hy1, hy2]
    have hlt : ∀ᶠ y in 𝓝[<] x,
        sturmVariations p y + (p.roots.toFinset.filter (· ≤ y)).card =
          sturmVariations p x + (p.roots.toFinset.filter (· ≤ x)).card := by
      filter_upwards [hsv.filter_mono nhdsWithin_le_nhds, hlt_filter] with y hy1 hy2
      rw [ite_eq_right hpx, add_zero] at hy2
      rw [hy1, hy2]
    exact eventually_nhds_of_lt_of_gt rfl hlt hgt

/-- **Sturm's theorem** on half-open intervals `(a, b]` for separable `p : ℝ[X]`
([BasuPollackRoy2006], locator unverified): the drop `sturmVariations p a - sturmVariations p b`
equals the number of distinct real roots of `p` in `(a, b]`, with no nonvanishing assumption
on the endpoints. -/
theorem sturmVariations_sub_eq_card_roots_Ioc {p : ℝ[X]} (hp : p.Separable) {a b : ℝ}
    (hab : a ≤ b) :
    sturmVariations p a - sturmVariations p b =
      (p.roots.toFinset.filter (fun r => a < r ∧ r ≤ b)).card := by
  have hconst := (isLocallyConstant_sturmVariations_add_card hp).apply_eq_of_preconnectedSpace a b
  have hsplit : p.roots.toFinset.filter (· ≤ b) =
      p.roots.toFinset.filter (· ≤ a) ∪ p.roots.toFinset.filter (fun r => a < r ∧ r ≤ b) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hr, hrb⟩
      rcases le_or_gt r a with hra | har
      · exact Or.inl ⟨hr, hra⟩
      · exact Or.inr ⟨hr, har, hrb⟩
    · rintro (⟨hr, hra⟩ | ⟨hr, _, hrb⟩)
      · exact ⟨hr, hra.trans hab⟩
      · exact ⟨hr, hrb⟩
  have hdisj : Disjoint (p.roots.toFinset.filter (· ≤ a))
      (p.roots.toFinset.filter (fun r => a < r ∧ r ≤ b)) := by
    rw [Finset.disjoint_left]
    intro r hr1 hr2
    simp only [Finset.mem_filter] at hr1 hr2
    linarith [hr1.2, hr2.2.1]
  rw [hsplit, Finset.card_union_of_disjoint hdisj] at hconst
  omega

/-- `sturmVariations p` is antitone on `ℝ` for separable `p : ℝ[X]`. -/
theorem sturmVariations_antitone {p : ℝ[X]} (hp : p.Separable) :
    Antitone (sturmVariations p) := by
  intro a b hab
  have hconst := (isLocallyConstant_sturmVariations_add_card hp).apply_eq_of_preconnectedSpace a b
  have hsub : p.roots.toFinset.filter (· ≤ a) ⊆ p.roots.toFinset.filter (· ≤ b) := by
    intro r hr
    simp only [Finset.mem_filter] at hr ⊢
    exact ⟨hr.1, hr.2.trans hab⟩
  have hcard := Finset.card_le_card hsub
  omega

/-- Squarefree version of Sturm's theorem on `(a, b]` over `ℝ[X]`. -/
theorem sturmVariations_sub_eq_card_roots_Ioc_of_squarefree {p : ℝ[X]} (hp : Squarefree p)
    {a b : ℝ} (hab : a ≤ b) :
    sturmVariations p a - sturmVariations p b =
      (p.roots.toFinset.filter (fun r => a < r ∧ r ≤ b)).card :=
  sturmVariations_sub_eq_card_roots_Ioc (PerfectField.separable_iff_squarefree.mpr hp) hab

/-- Open-interval form of Sturm's theorem when `b` is not a root. -/
theorem sturmVariations_sub_eq_card_roots_Ioo {p : ℝ[X]} (hp : p.Separable) {a b : ℝ}
    (hab : a ≤ b) (hb : p.eval b ≠ 0) :
    sturmVariations p a - sturmVariations p b =
      (p.roots.toFinset.filter (fun r => a < r ∧ r < b)).card := by
  rw [sturmVariations_sub_eq_card_roots_Ioc hp hab]
  congr 1
  ext r
  simp only [Finset.mem_filter, Multiset.mem_toFinset, mem_roots hp.ne_zero, IsRoot.def]
  constructor
  · rintro ⟨hr, har, hrb⟩
    refine ⟨hr, har, lt_of_le_of_ne hrb ?_⟩
    intro hreq
    subst hreq
    exact hb hr
  · rintro ⟨hr, har, hrb⟩
    exact ⟨hr, har, hrb.le⟩

/-- Closed-interval form of Sturm's theorem when the left endpoint is not a root. -/
theorem sturmVariations_sub_eq_card_roots_Icc {p : ℝ[X]} (hp : p.Separable) {a b : ℝ}
    (hab : a ≤ b) (ha : p.eval a ≠ 0) :
    sturmVariations p a - sturmVariations p b =
      (p.roots.toFinset.filter (fun r => a ≤ r ∧ r ≤ b)).card := by
  rw [sturmVariations_sub_eq_card_roots_Ioc hp hab]
  congr 1
  ext r
  simp only [Finset.mem_filter, Multiset.mem_toFinset, mem_roots hp.ne_zero, IsRoot.def]
  constructor
  · rintro ⟨hr, har, hrb⟩
    exact ⟨hr, har.le, hrb⟩
  · rintro ⟨hr, har, hrb⟩
    refine ⟨hr, lt_of_le_of_ne har ?_, hrb⟩
    intro hreq
    subst hreq
    exact ha hr

end Polynomial
