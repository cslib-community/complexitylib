/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.MarkovChain.Mixing
public import CslibFrontier.Probability.StatisticalDistance.Coupling
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.EventBind

/-!
# Markovian couplings and the coupling bound on mixing

A *Markovian coupling* of a chain `P` on `S` is a chain `Q` on `S × S` whose two coordinates each
move according to `P` ([LevinPeres2017], Section 5.1):
`(Q (x, y)).map Prod.fst = P x` and `(Q (x, y)).map Prod.snd = P y`. Then `(Q ^ t) (x, y)` couples
`(P ^ t) x` with `(P ^ t) y`, so the coupling inequality bounds their statistical distance by the
probability that the two copies differ at time `t`
(`Cslib.Probability.MarkovChain.IsMarkovianCoupling.dist_pow_le`, [LevinPeres2017],
Theorem 5.4). Taking the worst starting pair bounds `d(t)`
(`Cslib.Probability.MarkovChain.distToStationary_le_of_coupling`, Corollary 5.5).

[LevinPeres2017] state these bounds with the tail `P{τ_couple > t}` of the coupling time, for any
coupling of the two chains that satisfies (5.2), Markovian or not. This module bounds by
`P{X_t ≠ Y_t}`, which is at most `P{τ_couple > t}` because `{X_t ≠ Y_t} ⊆ {τ_couple > t}` (this
is the source's intermediate step (5.5)). The results here are restricted to time-homogeneous
Markovian couplings `Q : MarkovChain (S × S)`, but they need no stickiness; [LevinPeres2017],
Remark 5.3, notes that every coupling used in the book is Markovian.
A coupling is *sticky* (`Cslib.Probability.MarkovChain.IsSticky`, [LevinPeres2017], (5.2))
if the diagonal is absorbing. Under stickiness the two events coincide and their probability is
non-increasing in `t` (`Cslib.Probability.MarkovChain.IsSticky.antitone_toOuterMeasure`). No
path-space coupling time is constructed.

## Main definitions

* `Cslib.Probability.MarkovChain.IsMarkovianCoupling`: a Markovian coupling of `P` with itself.
* `Cslib.Probability.MarkovChain.IsSticky`: the diagonal is absorbing.
* `Cslib.Probability.MarkovChain.independentCoupling`: the two copies move independently.

## Main results

* `Cslib.Probability.MarkovChain.IsMarkovianCoupling.coupledWithin_pow`: the `t`-step coupling.
* `Cslib.Probability.MarkovChain.IsMarkovianCoupling.dist_pow_le`: Theorem 5.4.
* `Cslib.Probability.MarkovChain.distToStationary_le_of_coupling`: Corollary 5.5.
* `Cslib.Probability.MarkovChain.IsSticky.antitone_toOuterMeasure`: under a sticky coupling, the
  probability of not having met is non-increasing.

## References

* [LevinPeres2017], Sections 5.1 and 5.2.
-/

public section

open scoped ENNReal Cslib.Probability.PMF

namespace Cslib.Probability.MarkovChain

open Cslib.Probability.PMF

variable {S : Type*}

/-- `Q` is a Markovian coupling of `P` with itself: each coordinate of `Q` moves according to `P`
([LevinPeres2017], Section 5.1). -/
structure IsMarkovianCoupling (P : MarkovChain S) (Q : MarkovChain (S × S)) : Prop where
  /-- The first coordinate moves according to `P`. -/
  map_fst : ∀ z, (Q z).map Prod.fst = P z.1
  /-- The second coordinate moves according to `P`. -/
  map_snd : ∀ z, (Q z).map Prod.snd = P z.2

/-- A coupling is sticky if the two copies stay together once they meet
([LevinPeres2017], (5.2)). -/
@[expose] def IsSticky (Q : MarkovChain (S × S)) : Prop :=
  ∀ x, ∀ w ∈ (Q (x, x)).support, w.1 = w.2

variable {P : MarkovChain S} {Q : MarkovChain (S × S)}

theorem IsMarkovianCoupling.map_fst_pow (h : P.IsMarkovianCoupling Q) (t : ℕ) (z : S × S) :
    ((Q ^ t) z).map Prod.fst = (P ^ t) z.1 := by
  induction t with
  | zero => simp [PMF.pure_map]
  | succ t ih =>
    rw [pow_succ_apply, pow_succ_apply, PMF.map_bind, ← ih, PMF.bind_map]
    exact congrArg _ (funext fun w => h.map_fst w)

theorem IsMarkovianCoupling.map_snd_pow (h : P.IsMarkovianCoupling Q) (t : ℕ) (z : S × S) :
    ((Q ^ t) z).map Prod.snd = (P ^ t) z.2 := by
  induction t with
  | zero => simp [PMF.pure_map]
  | succ t ih =>
    rw [pow_succ_apply, pow_succ_apply, PMF.map_bind, ← ih, PMF.bind_map]
    exact congrArg _ (funext fun w => h.map_snd w)

/-- After `t` steps, a Markovian coupling started at `(x, y)` couples `Pᵗ(x, ·)` with `Pᵗ(y, ·)`
within the probability that the copies differ. -/
theorem IsMarkovianCoupling.coupledWithin_pow (h : P.IsMarkovianCoupling Q) (t : ℕ) (x y : S) :
    CoupledWithin ((P ^ t) x) ((P ^ t) y) (((Q ^ t) (x, y)).toOuterMeasure {w | w.1 ≠ w.2}) :=
  ⟨(Q ^ t) (x, y), h.map_fst_pow t (x, y), h.map_snd_pow t (x, y), le_rfl⟩

/-- **Coupling bound** ([LevinPeres2017], Theorem 5.4, with the event `{X_t ≠ Y_t}`):
`‖Pᵗ(x, ·) - Pᵗ(y, ·)‖_TV ≤ P_{x,y}{X_t ≠ Y_t}`. -/
theorem IsMarkovianCoupling.dist_pow_le [Fintype S] (h : P.IsMarkovianCoupling Q) (t : ℕ)
    (x y : S) :
    dist ((P ^ t) x) ((P ^ t) y) ≤ (((Q ^ t) (x, y)).toOuterMeasure {w | w.1 ≠ w.2}).toReal :=
  (h.coupledWithin_pow t x y).dist_le (toOuterMeasure_ne_top _ _)

/-- **Coupling bound on mixing** ([LevinPeres2017], Corollary 5.5): if for every pair of
starting states there is a Markovian coupling whose copies differ at time `t` with probability at
most `ε`, then `d(t) ≤ ε`. -/
theorem distToStationary_le_of_coupling [Fintype S] {π : PMF S} (hπ : P.IsStationary π)
    (Q : S → S → MarkovChain (S × S)) (hQ : ∀ x y, P.IsMarkovianCoupling (Q x y)) {t : ℕ}
    {ε : ℝ} (hε : ∀ x y, (((Q x y ^ t) (x, y)).toOuterMeasure {w | w.1 ≠ w.2}).toReal ≤ ε) :
    P.distToStationary π t ≤ ε := by
  have h0 : 0 ≤ ε := by
    obtain ⟨x, -⟩ := π.support_nonempty
    exact ENNReal.toReal_nonneg.trans (hε x x)
  exact (hπ.distToStationary_le_distPair t).trans
    (P.distPair_le (fun x y => ((hQ x y).dist_pow_le t x y).trans (hε x y)) h0)

/-- The `t`-step kernel of a sticky coupling is sticky. -/
theorem IsSticky.pow (h : IsSticky Q) (t : ℕ) : IsSticky (Q ^ t) := by
  induction t with
  | zero =>
    intro x w hw
    simp only [pow_zero, one_apply, PMF.support_pure, Set.mem_singleton_iff] at hw
    rw [hw]
  | succ t ih =>
    intro x w hw
    rw [pow_succ_apply, PMF.mem_support_bind_iff] at hw
    obtain ⟨⟨a, b⟩, hv, hw⟩ := hw
    obtain rfl : a = b := ih x _ hv
    exact h a w hw

theorem IsSticky.toOuterMeasure_succ_le (h : IsSticky Q) (t : ℕ) (z : S × S) :
    ((Q ^ (t + 1)) z).toOuterMeasure {w | w.1 ≠ w.2} ≤
      ((Q ^ t) z).toOuterMeasure {w | w.1 ≠ w.2} := by
  rw [pow_succ_apply]
  have := toOuterMeasure_bind_le_mul_ennreal ((Q ^ t) z) Q {w | w.1 ≠ w.2} {w | w.1 ≠ w.2}
    (q₂ := 1) le_rfl (fun a _ _ => toOuterMeasure_le_one _ _) (fun a _ ha => ?_)
  · simpa using this
  · obtain ⟨x, y⟩ := a
    simp only [ne_eq, Set.mem_ofPred_eq, not_not] at ha
    subst ha
    rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
    intro w hw hne
    exact hne (h x w hw)

/-- Under a sticky coupling, the probability that the copies have not met by time `t` is
non-increasing in `t`. -/
theorem IsSticky.antitone_toOuterMeasure (h : IsSticky Q) (z : S × S) :
    Antitone fun t => ((Q ^ t) z).toOuterMeasure {w | w.1 ≠ w.2} :=
  antitone_nat_of_succ_le fun t => h.toOuterMeasure_succ_le t z

/-- The independent coupling: the two copies move independently. -/
noncomputable def independentCoupling (P : MarkovChain S) : MarkovChain (S × S) :=
  ⟨fun z => (P z.1).bind fun a => (P z.2).map (a, ·)⟩

theorem isMarkovianCoupling_independentCoupling (P : MarkovChain S) :
    P.IsMarkovianCoupling P.independentCoupling where
  map_fst _ := map_fst_bind_pair _ _
  map_snd z := by
    change ((P z.1).bind fun a => (P z.2).map (a, ·)).map Prod.snd = P z.2
    rw [PMF.map_bind]
    simp only [PMF.map_comp, Function.comp_def]
    exact (congrArg _ (funext fun _ => PMF.map_id _)).trans (PMF.bind_const _ _)

end Cslib.Probability.MarkovChain
