/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.Influence
public import Complexity.Foundations.Data.BitString.PartialAssignment
public import Complexity.Probability.Fooling
import Complexity.Probability.PMF

/-!
# Coalition influence and resilient functions

A Boolean function `f` on the cube `ι → Bool` is *undetermined* at `x` by the bits outside a
coalition `Q` (`Cslib.BitString.IsUndetermined`) if two strings that agree with `x` outside `Q`
take different values: after the bits outside `Q` are fixed to those of `x`, the coalition can
still decide the outcome. The *influence* of `Q` under a distribution `D`
(`Cslib.BitString.coalitionInfluence`) is the probability, for `x` drawn from `D`, that `f` is
undetermined at `x` by the bits outside `Q`. Under the uniform distribution this is the influence
`I_Q(f)` of [Chattopadhyay–Zuckerman, Definition 1.6][ChattopadhyayZuckerman2019], which is the
coalitional influence of [O'Donnell, Exercise 9.25][ODonnell2014]; under a distribution `D` it is
the influence `I_{Q,D}(f)` of [Chattopadhyay–Zuckerman, Definition 1.9][ChattopadhyayZuckerman2019].

Chattopadhyay and Zuckerman fix the bits outside `Q` by a distribution on those bits alone. Here
`D` is a distribution on all of the cube and the event ignores the bits in `Q`
(`Cslib.BitString.isUndetermined_congr`), so `coalitionInfluence D Q f` is their `I_{Q,D'}(f)` for
the marginal `D'` of `D` outside `Q`. The marginal of a `k`-wise independent distribution is again
`k`-wise independent, and a `k`-wise independent distribution outside `Q` extends by uniform bits on
`Q`, so the worst case over `k`-wise independent distributions is the same in both readings; this
equivalence is not formalized.

A function is *`(q, ε)`-resilient* (`Cslib.BitString.IsResilient`) if every coalition of `q` bits
has influence at most `ε` under the uniform distribution
[Chattopadhyay–Zuckerman, Definition 1.7][ChattopadhyayZuckerman2019], and *`t`-independent
`(q, ε)`-resilient* (`Cslib.BitString.IsKWiseResilient`) if this holds under every `t`-wise
independent distribution [Chattopadhyay–Zuckerman, Definition 1.10][ChattopadhyayZuckerman2019].
Chattopadhyay and Zuckerman define the largest influence `I_q(f)` and `I_{q,t}(f)` and bound it by
`ε`; the predicates state the bound for every coalition and distribution directly.

Equivalently, `f` is undetermined at `x` by the bits outside `Q` when its restriction fixing the
bits outside `Q` to those of `x` is not constant (`Cslib.BitString.isUndetermined_iff_outside`).

For a monotone function, `f` is undetermined at `x` by the bits outside `Q` exactly when setting
all of `Q` to `true` gives `true` and setting all of `Q` to `false` gives `false`
(`Cslib.BitString.isUndetermined_iff_of_monotone`). The influence of a single bit is the
influence of `Cslib.BitString.influence` (`Cslib.BitString.coalitionInfluence_singleton`)
[O'Donnell, Exercise 9.25(a)][ODonnell2014].

## Main definitions

* `Cslib.BitString.IsUndetermined`: `f` is undetermined at `x` by the bits outside `Q`.
* `Cslib.BitString.coalitionInfluence`: the influence of a coalition under a distribution.
* `Cslib.BitString.IsResilient`: `(q, ε)`-resilient functions.
* `Cslib.BitString.IsKWiseResilient`: `t`-independent `(q, ε)`-resilient functions.

## Main results

* `Cslib.BitString.isUndetermined_iff_outside`: undetermined functions are those with a
  non-constant restriction.
* `Cslib.BitString.isUndetermined_iff_of_monotone`: undetermined monotone functions.
* `Cslib.BitString.coalitionInfluence_uniformOfFintype`: the uniform influence as an average.
* `Cslib.BitString.coalitionInfluence_nonneg`, `Cslib.BitString.coalitionInfluence_le_one`,
  `Cslib.BitString.coalitionInfluence_mono`: influences are probabilities, monotone in the
  coalition.
* `Cslib.BitString.coalitionInfluence_singleton`: the influence of a single bit.
* `Cslib.BitString.isResilient_const`: constant functions are resilient against every coalition.

## References

* [E. Chattopadhyay, D. Zuckerman, *Explicit two-source extractors and resilient
  functions*][ChattopadhyayZuckerman2019]
* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset Function
open scoped BigOperators

variable {ι : Type*}

/-! ### Undetermined functions -/

/-- The function `f` is *undetermined* at `x` by the bits outside the coalition `Q` if two strings
agreeing with `x` outside `Q` take different values under `f`
[Chattopadhyay–Zuckerman, Definitions 1.6 and 1.9][ChattopadhyayZuckerman2019]. -/
@[expose] def IsUndetermined (Q : Finset ι) (f : (ι → Bool) → Bool) (x : ι → Bool) : Prop :=
  ∃ y z : ι → Bool, (∀ i ∉ Q, y i = x i) ∧ (∀ i ∉ Q, z i = x i) ∧ f y ≠ f z

variable {Q Q' : Finset ι} {f : (ι → Bool) → Bool} {x x' : ι → Bool}

/-- Whether `f` is undetermined at `x` by the bits outside `Q` depends only on the bits of `x`
outside `Q`. -/
theorem isUndetermined_congr (h : ∀ i ∉ Q, x i = x' i) :
    IsUndetermined Q f x ↔ IsUndetermined Q f x' := by
  refine ⟨fun ⟨y, z, hy, hz, hf⟩ => ⟨y, z, fun i hi => ?_, fun i hi => ?_, hf⟩,
    fun ⟨y, z, hy, hz, hf⟩ => ⟨y, z, fun i hi => ?_, fun i hi => ?_, hf⟩⟩
  · rw [hy i hi, h i hi]
  · rw [hz i hi, h i hi]
  · rw [hy i hi, h i hi]
  · rw [hz i hi, h i hi]

/-- A larger coalition leaves the function undetermined wherever a smaller one does. -/
theorem IsUndetermined.mono (h : IsUndetermined Q f x) (hQ : Q ⊆ Q') :
    IsUndetermined Q' f x :=
  let ⟨y, z, hy, hz, hf⟩ := h
  ⟨y, z, fun i hi => hy i fun h => hi (hQ h), fun i hi => hz i fun h => hi (hQ h), hf⟩

/-- A constant function is undetermined nowhere. -/
theorem not_isUndetermined_const (b : Bool) : ¬IsUndetermined Q (fun _ => b) x :=
  fun ⟨_, _, _, _, hf⟩ => hf rfl

variable [DecidableEq ι]

/-- A function is undetermined at `x` by the bits outside `Q` exactly when its restriction fixing
the bits outside `Q` to those of `x` (`Cslib.BitString.PartialAssignment.outside`) is not
constant. -/
theorem isUndetermined_iff_outside :
    IsUndetermined Q f x ↔ ∃ y z : ι → Bool,
      f ((PartialAssignment.outside Q x).fill y) ≠ f ((PartialAssignment.outside Q x).fill z) := by
  simp only [PartialAssignment.fill_outside]
  have key (y : ι → Bool) (hy : ∀ i ∉ Q, y i = x i) : Q.piecewise y x = y := funext fun i => by
    by_cases hi : i ∈ Q
    · rw [piecewise_eq_of_mem _ _ _ hi]
    · rw [piecewise_eq_of_notMem _ _ _ hi, hy i hi]
  refine ⟨fun ⟨y, z, hy, hz, h⟩ => ⟨y, z, by rwa [key y hy, key z hz]⟩, fun ⟨y, z, h⟩ =>
    ⟨Q.piecewise y x, Q.piecewise z x, fun i hi => piecewise_eq_of_notMem _ _ _ hi,
      fun i hi => piecewise_eq_of_notMem _ _ _ hi, h⟩⟩

/-- **Undetermined monotone functions.** A monotone function is undetermined at `x` by the bits
outside `Q` exactly when setting all of `Q` to `true` gives `true` and setting all of `Q` to
`false` gives `false`. -/
theorem isUndetermined_iff_of_monotone (hf : Monotone f) :
    IsUndetermined Q f x ↔
      f (Q.piecewise (fun _ => true) x) = true ∧ f (Q.piecewise (fun _ => false) x) = false := by
  constructor
  · rintro ⟨y, z, hy, hz, hyz⟩
    have lo (w : ι → Bool) (hw : ∀ i ∉ Q, w i = x i) : Q.piecewise (fun _ => false) x ≤ w :=
      fun i => by
        by_cases hi : i ∈ Q
        · rw [piecewise_eq_of_mem _ _ _ hi]
          exact Bool.false_le _
        · rw [piecewise_eq_of_notMem _ _ _ hi, hw i hi]
    have up (w : ι → Bool) (hw : ∀ i ∉ Q, w i = x i) : w ≤ Q.piecewise (fun _ => true) x :=
      fun i => by
        by_cases hi : i ∈ Q
        · rw [piecewise_eq_of_mem _ _ _ hi]
          exact Bool.le_true _
        · rw [piecewise_eq_of_notMem _ _ _ hi, hw i hi]
    have key : ∀ a b c e : Bool, a ≤ b → b ≤ e → a ≤ c → c ≤ e → b ≠ c → e = true ∧ a = false := by
      decide
    exact key _ _ _ _ (hf (lo y hy)) (hf (up y hy)) (hf (lo z hz)) (hf (up z hz)) hyz
  · rintro ⟨h1, h0⟩
    refine ⟨Q.piecewise (fun _ => true) x, Q.piecewise (fun _ => false) x,
      fun i hi => piecewise_eq_of_notMem _ _ _ hi, fun i hi => piecewise_eq_of_notMem _ _ _ hi, ?_⟩
    rw [h1, h0]
    decide

/-- A function is undetermined at `x` by the bits other than `i` exactly when flipping bit `i`
of `x` changes its value. -/
theorem isUndetermined_singleton_iff (i : ι) :
    IsUndetermined {i} f x ↔ f (update x i !x i) ≠ f x := by
  have key (y : ι → Bool) (hy : ∀ j ∉ ({i} : Finset ι), y j = x j) :
      f y = f x ∨ f y = f (update x i !x i) := by
    have hyx : y = update x i (y i) := funext fun j => by
      by_cases hj : j = i
      · subst hj
        rw [update_self]
      · rw [update_of_ne hj]
        exact hy j (by rwa [mem_singleton])
    obtain h | h : y i = x i ∨ y i = !x i := by cases y i <;> cases x i <;> simp
    · left
      rw [hyx, h, update_eq_self]
    · right
      rw [hyx, h]
  constructor
  · rintro ⟨y, z, hy, hz, hyz⟩
    rcases key y hy with h1 | h1 <;> rcases key z hz with h2 | h2 <;> rw [h1, h2] at hyz
    · exact absurd rfl hyz
    · exact hyz.symm
    · exact hyz
    · exact absurd rfl hyz
  · intro h
    refine ⟨update x i !x i, x, fun j hj => update_of_ne (by rwa [mem_singleton] at hj) _ _,
      fun _ _ => rfl, h⟩

/-! ### Coalition influence -/

variable [Fintype ι]

instance (Q : Finset ι) (f : (ι → Bool) → Bool) : DecidablePred (IsUndetermined Q f) :=
  fun x => inferInstanceAs
    (Decidable (∃ y z : ι → Bool, (∀ i ∉ Q, y i = x i) ∧ (∀ i ∉ Q, z i = x i) ∧ f y ≠ f z))

/-- The *influence* of the coalition `Q` on `f` under the distribution `D`: the probability, for
`x` drawn from `D`, that `f` is undetermined at `x` by the bits outside `Q`. This is `I_{Q,D}(f)`
[Chattopadhyay–Zuckerman, Definition 1.9][ChattopadhyayZuckerman2019] for the marginal of `D`
outside `Q`; under the uniform distribution it is `I_Q(f)`
[Chattopadhyay–Zuckerman, Definition 1.6][ChattopadhyayZuckerman2019], the coalitional influence
of [O'Donnell, Exercise 9.25][ODonnell2014]. -/
@[expose] noncomputable def coalitionInfluence (D : PMF (ι → Bool)) (Q : Finset ι)
    (f : (ι → Bool) → Bool) : ℝ :=
  ∑ x, (D x).toReal * if IsUndetermined Q f x then 1 else 0

variable {D : PMF (ι → Bool)}

/-- Under the uniform distribution, the influence of a coalition is the fraction of the strings
at which the function is undetermined by the bits outside it. -/
theorem coalitionInfluence_uniformOfFintype (Q : Finset ι) (f : (ι → Bool) → Bool) :
    coalitionInfluence (Probability.PMF.uniformOfFintype (ι → Bool)) Q f =
      𝔼 x, if IsUndetermined Q f x then (1 : ℝ) else 0 :=
  sum_uniformOfFintype_mul _

/-- Influences are nonnegative [O'Donnell, Exercise 9.25(b)][ODonnell2014]. -/
theorem coalitionInfluence_nonneg (D : PMF (ι → Bool)) (Q : Finset ι) (f : (ι → Bool) → Bool) :
    0 ≤ coalitionInfluence D Q f :=
  sum_nonneg fun x _ => mul_nonneg ENNReal.toReal_nonneg (by split_ifs <;> norm_num)

/-- Influences are at most one [O'Donnell, Exercise 9.25(b)][ODonnell2014]. -/
theorem coalitionInfluence_le_one (D : PMF (ι → Bool)) (Q : Finset ι) (f : (ι → Bool) → Bool) :
    coalitionInfluence D Q f ≤ 1 :=
  (sum_le_sum fun x _ => mul_le_of_le_one_right ENNReal.toReal_nonneg
    (by split_ifs <;> norm_num)).trans_eq (Probability.PMF.sum_toReal D)

/-- A larger coalition has at least the influence of a smaller one. -/
theorem coalitionInfluence_mono (D : PMF (ι → Bool)) (hQ : Q ⊆ Q') (f : (ι → Bool) → Bool) :
    coalitionInfluence D Q f ≤ coalitionInfluence D Q' f :=
  sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (by
    by_cases h : IsUndetermined Q f x
    · rw [ite_eq_left h, ite_eq_left (h.mono hQ)]
    · rw [ite_eq_right h]
      split_ifs <;> norm_num) ENNReal.toReal_nonneg

/-- A coalition that leaves the function undetermined everywhere has influence one. -/
theorem coalitionInfluence_eq_one_of_forall (D : PMF (ι → Bool))
    (h : ∀ x, IsUndetermined Q f x) : coalitionInfluence D Q f = 1 := by
  simp only [coalitionInfluence, h, ↓reduceIte, mul_one]
  exact Probability.PMF.sum_toReal D

/-- A coalition that leaves the function determined everywhere has influence zero. -/
theorem coalitionInfluence_eq_zero_of_forall_not (D : PMF (ι → Bool))
    (h : ∀ x, ¬IsUndetermined Q f x) : coalitionInfluence D Q f = 0 := by
  simp only [coalitionInfluence, h, ↓reduceIte, mul_zero, sum_const_zero]

/-- **The influence of a single bit** under the uniform distribution is its influence
`Cslib.BitString.influence` on the function read as signs, the probability that flipping it
changes the value [O'Donnell, Exercise 9.25(a)][ODonnell2014]. -/
theorem coalitionInfluence_singleton (i : ι) (f : (ι → Bool) → Bool) :
    coalitionInfluence (Probability.PMF.uniformOfFintype (ι → Bool)) {i} f =
      influence i fun x => signVal (f x) := by
  rw [coalitionInfluence_uniformOfFintype, influence_signVal]
  refine expect_congr rfl fun x _ => ?_
  simp only [isUndetermined_singleton_iff, ne_eq, ite_not]

/-! ### Resilient functions -/

/-- A function is *`(q, ε)`-resilient* if every coalition of `q` bits has influence at most `ε`
under the uniform distribution
[Chattopadhyay–Zuckerman, Definition 1.7][ChattopadhyayZuckerman2019]. For `q > card ι` there is no
such coalition and the predicate holds vacuously, while their largest influence `I_q(f)` is
undefined. -/
@[expose] def IsResilient (q : ℕ) (ε : ℝ) (f : (ι → Bool) → Bool) : Prop :=
  ∀ Q : Finset ι, #Q = q → coalitionInfluence (Probability.PMF.uniformOfFintype _) Q f ≤ ε

/-- A function is *`t`-independent `(q, ε)`-resilient* if every coalition of `q` bits has
influence at most `ε` under every `t`-wise independent distribution
[Chattopadhyay–Zuckerman, Definition 1.10][ChattopadhyayZuckerman2019], with `D` a distribution on
all bits. This is equivalent to their reading, with a distribution on the bits outside `Q`, by an
argument not formalized here (see the module docstring). For `q > card ι` there is no coalition of
`q` bits and the predicate holds vacuously, while their largest influence `I_{q,t}(f)` is
undefined. -/
@[expose] def IsKWiseResilient (t q : ℕ) (ε : ℝ) (f : (ι → Bool) → Bool) : Prop :=
  ∀ Q : Finset ι, #Q = q → ∀ D : PMF (ι → Bool), IsKWiseIndependent t D →
    coalitionInfluence D Q f ≤ ε

/-- A `t`-independent resilient function is resilient, since the uniform distribution is `t`-wise
independent. -/
theorem IsKWiseResilient.isResilient {t q : ℕ} {ε : ℝ} (h : IsKWiseResilient t q ε f) :
    IsResilient q ε f :=
  fun Q hQ => h Q hQ _ (isKWiseIndependent_uniformOfFintype t)

/-- A constant function is `t`-independent `(q, 0)`-resilient for all `t` and `q`. -/
theorem isKWiseResilient_const (t q : ℕ) (b : Bool) :
    IsKWiseResilient t q 0 fun _ : ι → Bool => b :=
  fun _ _ D _ => (coalitionInfluence_eq_zero_of_forall_not D fun _ =>
    not_isUndetermined_const b).le

/-- A constant function is `(q, 0)`-resilient for every `q`. -/
theorem isResilient_const (q : ℕ) (b : Bool) : IsResilient q 0 fun _ : ι → Bool => b :=
  (isKWiseResilient_const 0 q b).isResilient

end Cslib.BitString
