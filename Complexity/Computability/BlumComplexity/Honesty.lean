/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.BlumComplexity.Basic
import Complexity.Computability.BlumComplexity.Naming
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The honesty theorem

A function is *`g`-honest* [Odifreddi1999, Definition VII.2.13] when some program computes it with
cost at most `g n (f n)` for almost all `n`: its cost is bounded by a fixed function of its own
values. Every complexity class of a computable bound has a `g`-honest name, with one computable `g`
for all bounds. This file derives that from the naming theorem
(`Complexity.Computability.BlumComplexity.Naming`) and the fact that the members of a measured
family are honest for one computable `g` [Odifreddi1999, Exercise VII.2.14a].

## Conventions and scope

`IsHonest g f` is stated for total `f`. The source defines `g`-honesty for partial recursive `φ`
too, with the bound required only where `φ` is defined. `exists_isHonest_of_measured` accordingly
concludes honesty only for the total members `φ_{h i}` of the measured family.

`exists_isHonest_of_measured` takes `g x z = ∑_{e ≤ x} Φ_{h e}(x)`, summed over the `e` with
`φ_{h e}(x) = z` (a term is `0` otherwise). The source's hint takes the maximum of the same terms.
The sum is at least the maximum, so it gives the same conclusion.

## Main definitions

* `Cslib.BlumComplexity.BlumMeasure.IsHonest`: `f` is `g`-honest.

## Main results

* `Cslib.BlumComplexity.BlumMeasure.exists_isHonest_of_measured`: for a measured family
  `φ_{h 0}, φ_{h 1}, …`, one computable `g` makes every total member `g`-honest.
* `Cslib.BlumComplexity.BlumMeasure.honesty_theorem`: **the honesty theorem**. One computable `g`
  gives every `C_t` of a computable `t` a computable `g`-honest name `t'`, with `C_{t'} = C_t`.

## References

* [P. Odifreddi, *Classical Recursion Theory, Volume II*][Odifreddi1999]
* [M. Blum, *A machine-independent theory of the complexity of recursive functions*][Blum1967]
-/

public section

namespace Cslib.BlumComplexity.BlumMeasure

open Encodable Denumerable Filter
open Nat.Partrec (Code)

variable (Φ : BlumMeasure)

/-- A total function `f` is **`g`-honest** [Odifreddi1999, Definition VII.2.13] when some program
computing `f` has cost at most `g n (f n)` for almost all `n`. The source also defines this for
partial functions, and requires `g` to be computable; here `g` is arbitrary and the theorems assume
`Computable₂ g` where needed. -/
def IsHonest (g : ℕ → ℕ → ℕ) (f : ℕ → ℕ) : Prop :=
  ∃ c : Code, (∀ n, f n ∈ c.eval n) ∧ ∀ᶠ n in atTop, ∀ m ∈ Φ.cost c n, m ≤ g n (f n)

variable {Φ} in
theorem isHonest_iff {g : ℕ → ℕ → ℕ} {f : ℕ → ℕ} :
    Φ.IsHonest g f ↔
      ∃ c : Code, (∀ n, f n ∈ c.eval n) ∧ ∀ᶠ n in atTop, ∀ m ∈ Φ.cost c n, m ≤ g n (f n) :=
  Iff.rfl

namespace Honesty

/-- The cost of program `h e` on `x` if its output there is `z`, and `0` otherwise. -/
private noncomputable def term (h : Code → Code) (e x z : ℕ) : ℕ :=
  @dite _ (z ∈ (h (ofNat Code e)).eval x) (Classical.dec _)
    (fun hz => (Φ.cost (h (ofNat Code e)) x).get
      ((Φ.dom_cost_iff _ x).2 (Part.dom_iff_mem.2 ⟨z, hz⟩))) fun _ => 0

private theorem term_mem {h : Code → Code} {e x z : ℕ} (hz : z ∈ (h (ofNat Code e)).eval x) :
    term Φ h e x z ∈ Φ.cost (h (ofNat Code e)) x := by
  simp only [term, hz, ↓reduceDIte]
  exact Part.get_mem _

private theorem computable_term {h : Code → Code} (hh : Computable h)
    (hgr : ComputablePred fun q : Code × ℕ × ℕ => q.2.2 ∈ (h q.1).eval q.2.1) :
    Computable fun q : ℕ × ℕ × ℕ => term Φ h q.1 q.2.1 q.2.2 := by
  have hc : Computable fun q : ℕ × ℕ × ℕ => h (ofNat Code q.1) :=
    hh.comp ((Computable.ofNat Code).comp Computable.fst)
  have hg : ComputablePred fun q : ℕ × ℕ × ℕ => q.2.2 ∈ (h (ofNat Code q.1)).eval q.2.1 :=
    hgr.comp ((Computable.ofNat Code).comp Computable.fst |>.pair Computable.snd)
  obtain ⟨f, hf, hfp⟩ := ComputablePred.computable_iff.1 hg
  have hp : Partrec fun q : ℕ × ℕ × ℕ =>
      cond (f q) (Φ.cost (h (ofNat Code q.1)) q.2.1) (Part.some 0) :=
    Partrec.cond hf (Φ.partrec_cost.comp hc (Computable.fst.comp Computable.snd))
      (Partrec.const' (Part.some 0))
  refine hp.of_eq_tot fun q => ?_
  have hq : q.2.2 ∈ (h (ofNat Code q.1)).eval q.2.1 ↔ f q = true := by
    rw [show (q.2.2 ∈ (h (ofNat Code q.1)).eval q.2.1) =
      (fun q : ℕ × ℕ × ℕ => q.2.2 ∈ (h (ofNat Code q.1)).eval q.2.1) q from rfl, hfp]
  cases hfq : f q with
  | true => exact term_mem Φ (hq.2 hfq)
  | false =>
    have hn : q.2.2 ∉ (h (ofNat Code q.1)).eval q.2.1 := fun hm => by
      have h' := hq.1 hm
      rw [hfq] at h'
      exact Bool.false_ne_true h'
    simp only [term, hn, ↓reduceDIte]
    exact Part.mem_some 0

/-- The bound `g x z = ∑_{e ≤ x} term h e x z`. -/
private noncomputable def bound (h : Code → Code) (x z : ℕ) : ℕ :=
  ∑ e ∈ Finset.range (x + 1), term Φ h e x z

private theorem computable_bound {h : Code → Code} (hh : Computable h)
    (hgr : ComputablePred fun q : Code × ℕ × ℕ => q.2.2 ∈ (h q.1).eval q.2.1) :
    Computable₂ (bound Φ h) := by
  have ht := computable_term Φ hh hgr
  have hr : Computable fun q : ℕ × ℕ => Nat.rec (motive := fun _ => ℕ) 0
      (fun e acc => acc + term Φ h e q.1 q.2) (q.1 + 1) :=
    Computable.nat_rec (Computable.succ.comp Computable.fst) (Computable.const 0)
      (Primrec.nat_add.to_comp.comp (Computable.snd.comp Computable.snd)
        (ht.comp ((Computable.fst.comp Computable.snd).pair
          ((Computable.fst.comp Computable.fst).pair
            (Computable.snd.comp Computable.fst))))).to₂
  refine Computable.to₂ (f := fun q : ℕ × ℕ => bound Φ h q.1 q.2) (hr.of_eq fun q => ?_)
  unfold bound
  induction q.1 + 1 with
  | zero => rfl
  | succ k ih => rw [Finset.sum_range_succ, ← ih]

end Honesty

open Honesty

/-- The total members of a measured family are honest [Odifreddi1999, Exercise VII.2.14a]
(attributed there to [Blum1967]). If `h` is a computable map on programs and the predicate
`φ_{h e} x = z` is decidable, uniformly in `e`, `x` and `z`, then one computable `g` makes every
total `φ_{h e}` `g`-honest. The source states this for every member, partial or not; `IsHonest`
covers total functions only. -/
theorem exists_isHonest_of_measured {h : Code → Code} (hh : Computable h)
    (hgr : ComputablePred fun q : Code × ℕ × ℕ => q.2.2 ∈ (h q.1).eval q.2.1) :
    ∃ g : ℕ → ℕ → ℕ, Computable₂ g ∧
      ∀ (i : Code) (f : ℕ → ℕ), (∀ n, f n ∈ (h i).eval n) → Φ.IsHonest g f := by
  refine ⟨bound Φ h, computable_bound Φ hh hgr, fun i f hf => ⟨h i, hf, ?_⟩⟩
  filter_upwards [eventually_ge_atTop (encode i)] with n hn m hm
  have hmem : f n ∈ (h (ofNat Code (encode i))).eval n := by grind [ofNat_encode]
  have hterm := term_mem Φ hmem
  rw [ofNat_encode] at hterm
  rw [Part.mem_unique hm hterm]
  exact Finset.single_le_sum (f := fun e => term Φ h e n (f n)) (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hn))

/-- **The honesty theorem.** There is one computable `g` such that every complexity class `C_t` of
a computable bound `t` has a `g`-honest name `t'`: `C_{t'} = C_t`. This combines the naming
theorem [Odifreddi1999, Theorem VII.3.6] with [Odifreddi1999, Exercise VII.2.14a]. -/
theorem honesty_theorem :
    ∃ g : ℕ → ℕ → ℕ, Computable₂ g ∧
      ∀ t : ℕ → ℕ, Computable t →
        ∃ t' : ℕ → ℕ, Computable t' ∧ Φ.IsHonest g t' ∧
          Φ.complexityClass t' = Φ.complexityClass t := by
  obtain ⟨h, hh, hgr, hname⟩ := Φ.naming_theorem
  obtain ⟨g, hg, hhon⟩ := Φ.exists_isHonest_of_measured hh hgr
  refine ⟨g, hg, fun t ht => ?_⟩
  obtain ⟨i, hi⟩ := Code.exists_code.1 (Partrec.nat_iff.1 ht)
  have hti : ∀ n, t n ∈ i.eval n := fun n => by rw [hi]; exact Part.mem_some _
  obtain ⟨t', ht', hcls⟩ := hname i t hti
  refine ⟨t', ?_, hhon i t' ht', hcls⟩
  exact Partrec.nat_iff.2 (Code.exists_code.2 ⟨h i, funext fun n => Part.eq_some_iff.2 (ht' n)⟩)

end Cslib.BlumComplexity.BlumMeasure
