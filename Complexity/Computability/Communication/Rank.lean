/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Communication.Rectangle
public import Complexity.Foundations.BooleanAnalysis.Fourier
public import Mathlib.Data.Nat.Log
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
import Complexity.Foundations.LinearAlgebra.Matrix.Rank

/-!
# The rank bound and the log-rank conjecture

The *communication matrix* of a Boolean function `f : X → Y → Bool` over a ring `R` has rows
indexed by Alice's inputs, columns indexed by Bob's inputs, and entry `1` where `f` is true and `0`
elsewhere (`communicationMatrix`). A protocol computing `f` writes it as the sum, over the leaves
labelled `true`, of the indicator matrices of their rectangles, each of rank at most one. So over
any commutative ring with the strong rank condition, such as a field, the rank of the communication
matrix is at most the number of leaves labelled `true` (`Protocol.rank_communicationMatrix_le`), and
the ranks of the matrices of `f` and of its negation add up to at most the number of leaves
(`Protocol.rank_add_rank_not_le_leafCount`). This is the *rank bound* `⌈log₂ rank M_f⌉ ≤ D(f)`
(`clog_rank_le_ecomplexity`) [Mehlhorn and Schmidt][MehlhornSchmidt1982],
[Kushilevitz and Nisan, Chapter 1][KushilevitzNisan1997].

More generally, any matrix whose entry at `x` and `y` depends only on `f x y`, through a relabelling
`g` of the outputs, is the sum over the leaves of matrices of rank at most one, so its rank is at
most the number of leaves whose labels `g` does not send to zero (`Protocol.rank_comp_run_le`), and
at most `2 ^ d` for a protocol sending `d` bits (`Protocol.rank_comp_le_two_pow`). This applies in
particular to the *sign matrix* of a Boolean function, with entries `-1` where `f` is true and `1`
elsewhere (`signMatrix`). Its rank exceeds that of the communication matrix by at most one
(`rank_signMatrix_le`); when `2 ≠ 0` in the field the converse holds too, so the two ranks differ
by at most one (`rank_communicationMatrix_le_rank_signMatrix`). In characteristic two the converse
fails: the sign matrix is the all-ones matrix.

When `f` is false somewhere, some leaf is labelled `false`, so the rank of the communication
matrix is less than the number of leaves (`Protocol.rank_communicationMatrix_lt_leafCount`) and less
than `2 ^ d` (`Protocol.rank_communicationMatrix_lt_two_pow`). A protocol that is only correct on a
rectangle `A × B` bounds the rank of the corresponding submatrix
(`Protocol.Solves.rank_communicationMatrix_le`).

The *log-rank conjecture* of Lovász and Saks asserts the converse up to a polynomial: the
communication complexity of every Boolean function is at most polynomial in the logarithm of the
rank of its communication matrix over the reals (`LogRankConjecture`) [LovaszSaks1993, Problem 2.7].
It is open.

## Main definitions

* `Cslib.Communication.communicationMatrix`: the communication matrix of a Boolean function.
* `Cslib.Communication.signMatrix`: the `±1` sign matrix of a Boolean function.
* `Cslib.Communication.LogRankConjecture`: the log-rank conjecture, as a proposition.

## Main results

* `Cslib.Communication.Protocol.rank_communicationMatrix_le`: the rank of the communication matrix
  is at most the number of leaves labelled `true`.
* `Cslib.Communication.Protocol.rank_add_rank_not_le_leafCount`: the ranks of the matrices of `f`
  and of `!f` add up to at most the number of leaves.
* `Cslib.Communication.clog_rank_le_ecomplexity`: the rank bound.
* `Cslib.Communication.Protocol.rank_comp_run_le`,
  `Cslib.Communication.Protocol.rank_comp_le_leafCount`: the rank bound for any relabelling of the
  outputs.
* `Cslib.Communication.Protocol.Solves.rank_communicationMatrix_le`: the rank bound on a rectangle.
* `Cslib.Communication.Protocol.rank_communicationMatrix_lt_leafCount`,
  `Cslib.Communication.Protocol.rank_communicationMatrix_lt_two_pow`: the strict rank bound for
  functions that are false somewhere.
* `Cslib.Communication.rank_signMatrix_le`,
  `Cslib.Communication.rank_communicationMatrix_le_rank_signMatrix`: the sign matrix has rank at
  most one more than the communication matrix, and when `2 ≠ 0` the two ranks differ by at most
  one.
* `Cslib.Communication.Protocol.rank_signMatrix_le_leafCount`: the rank bound for sign matrices.

## References

* [K. Mehlhorn and E. M. Schmidt, *Las Vegas is better than determinism in VLSI and distributed
  computing*][MehlhornSchmidt1982]
* [L. Lovász and M. Saks, *Communication complexity and combinatorial lattice
  theory*][LovaszSaks1993]
* [E. Kushilevitz and N. Nisan, *Communication Complexity*][KushilevitzNisan1997]
-/

@[expose] public section

namespace Cslib.Communication

open Finset

variable {X Y Z : Type*}

/-- The communication matrix of a Boolean function `f` over `R`: rows are indexed by Alice's
inputs, columns by Bob's inputs, and the entry at `x` and `y` is `1` if `f x y` and `0`
otherwise. -/
def communicationMatrix (R : Type*) [Zero R] [One R] (f : X → Y → Bool) : Matrix X Y R :=
  Matrix.of fun x y => if f x y then 1 else 0

@[simp] theorem communicationMatrix_apply (R : Type*) [Zero R] [One R] (f : X → Y → Bool) (x : X)
    (y : Y) : communicationMatrix R f x y = if f x y then 1 else 0 :=
  rfl

namespace Protocol

variable {R : Type*} [CommSemiring R] [StrongRankCondition R]

/-- **The rank bound for relabelled outputs.** For a protocol `p`, maps `a` and `b` into Alice's
and Bob's inputs and a relabelling `g` of the outputs, the matrix with entry `g (p.run (a x) (b y))`
at `x` and `y` has rank at most the size of any set `T` of leaves outside which `g` vanishes on the
labels: it is the sum, over the leaves in `T`, of rank-one matrices supported on their
rectangles. -/
theorem rank_comp_run_le {X' Y' : Type*} [Fintype Y'] (p : Protocol X Y Z) (a : X' → X)
    (b : Y' → Y) (g : Z → R) {T : Finset (Fin p.leafCount)}
    (hT : ∀ i ∉ T, g (p.leafOutput i) = 0) :
    (Matrix.of fun x y => g (p.run (a x) (b y))).rank ≤ #T := by
  classical
  let U : Matrix X' T R := Matrix.of fun x i => if a x ∈ p.leafAlice i then 1 else 0
  let V : Matrix T Y' R :=
    Matrix.of fun i y => if b y ∈ p.leafBob i then g (p.leafOutput i) else 0
  have hUV : (Matrix.of fun x y => g (p.run (a x) (b y))) = U * V := by
    ext x y
    simp only [Matrix.mul_apply, U, V, Matrix.of_apply, ite_mul, one_mul, zero_mul, ← ite_and]
    rw [sum_coe_sort T fun i =>
      if a x ∈ p.leafAlice i ∧ b y ∈ p.leafBob i then g (p.leafOutput i) else 0]
    simp only [← leaf_eq_iff, sum_ite_eq]
    split_ifs with h
    · rw [run_eq_leafOutput_leaf]
    · rw [run_eq_leafOutput_leaf, hT _ h]
  rw [hUV]
  exact (Matrix.rank_mul_le_left U V).trans ((Matrix.rank_le_card_width U).trans_eq
    (Fintype.card_coe T))

/-- **The rank bound on a rectangle.** If a protocol computes `f` on `A × B`, the rank of the
communication matrix of `f` restricted to `A × B` is at most the number of leaves labelled
`true`. -/
theorem Solves.rank_communicationMatrix_le {p : Protocol X Y Bool}
    {f : X → Y → Bool} {A : Set X} {B : Set Y} [Fintype B]
    (hp : p.Solves (fun x y b => f x y = b) A B) :
    (communicationMatrix R fun (x : A) (y : B) => f x y).rank ≤
      #{i | p.leafOutput i = true} := by
  have h : (communicationMatrix R fun (x : A) (y : B) => f x y) =
      Matrix.of fun x y => (fun b => if b then (1 : R) else 0) (p.run x.1 y.1) := by
    ext x y
    simp [(hp x.1 x.2 y.1 y.2 :)]
  rw [h]
  exact rank_comp_run_le p Subtype.val Subtype.val (fun b => if b then (1 : R) else 0)
    fun i hi => by simpa using hi

variable [Fintype Y]

/-- If a protocol computes `f`, then for every set of outputs, given by its indicator `g`, the rank
of the communication matrix of `g ∘ f` is at most the number of leaves labelled in the set. -/
theorem rank_communicationMatrix_comp_le {p : Protocol X Y Z} {f : X → Y → Z} (hp : p.run = f)
    (g : Z → Bool) :
    (communicationMatrix R fun x y => g (f x y)).rank ≤ #{i | g (p.leafOutput i) = true} := by
  subst hp
  exact rank_comp_run_le p id id (fun z => if g z then 1 else 0) fun i hi => by simpa using hi

section Comp

variable {f : X → Y → Z} {p : Protocol X Y Z}

/-- If a protocol computes `f`, then for every relabelling `g` of the outputs, the matrix with
entry `g (f x y)` at `x` and `y` has rank at most the number of leaves. -/
theorem rank_comp_le_leafCount (hp : p.run = f) (g : Z → R) :
    (Matrix.of fun x y => g (f x y)).rank ≤ p.leafCount := by
  subst hp
  exact (rank_comp_run_le p id id g (T := univ) fun i hi => absurd (mem_univ i) hi).trans_eq
    (card_fin _)

/-- If a protocol computes `f` with `d` bits, then for every relabelling `g` of the outputs, the
matrix with entry `g (f x y)` at `x` and `y` has rank at most `2 ^ d`. -/
theorem rank_comp_le_two_pow (hp : p.run = f) (g : Z → R) :
    (Matrix.of fun x y => g (f x y)).rank ≤ 2 ^ p.depth :=
  (rank_comp_le_leafCount hp g).trans p.leafCount_le_two_pow_depth

end Comp

variable {p : Protocol X Y Bool} {f : X → Y → Bool}

/-- **The rank bound.** The rank of the communication matrix of a function computed by a protocol
is at most the number of leaves labelled `true`. -/
theorem rank_communicationMatrix_le (hp : p.run = f) :
    (communicationMatrix R f).rank ≤ #{i | p.leafOutput i = true} :=
  rank_communicationMatrix_comp_le hp id

/-- The ranks of the communication matrices of `f` and of its negation add up to at most the
number of leaves of a protocol computing `f`. -/
theorem rank_add_rank_not_le_leafCount (hp : p.run = f) :
    (communicationMatrix R f).rank + (communicationMatrix R fun x y => !f x y).rank ≤
      p.leafCount := by
  refine (add_le_add (rank_communicationMatrix_le hp)
    (rank_communicationMatrix_comp_le hp not)).trans ?_
  rw [← card_union_of_disjoint (disjoint_filter.mpr fun i _ h => by simp [h])]
  exact (card_le_univ _).trans_eq (card_fin p.leafCount)

/-- A protocol computing `f` sends at least `log₂` of the rank of its communication matrix bits. -/
theorem rank_communicationMatrix_le_two_pow (hp : p.run = f) :
    (communicationMatrix R f).rank ≤ 2 ^ p.depth :=
  (rank_communicationMatrix_le hp).trans ((card_le_univ _).trans
    ((card_fin p.leafCount).trans_le p.leafCount_le_two_pow_depth))

/-- **The strict rank bound.** If a protocol computes a function `f` that is false somewhere, the
rank of the communication matrix of `f` is less than the number of leaves. -/
theorem rank_communicationMatrix_lt_leafCount (hp : p.run = f) (h : ∃ x y, f x y = false) :
    (communicationMatrix R f).rank < p.leafCount := by
  classical
  obtain ⟨x, y, hxy⟩ := h
  refine (rank_communicationMatrix_le hp).trans_lt
    ((card_lt_card (filter_ssubset.mpr ⟨p.leaf x y, mem_univ _, ?_⟩)).trans_eq (card_fin _))
  rw [← run_eq_leafOutput_leaf, hp, hxy]
  decide

/-- If a protocol sending `d` bits computes a function `f` that is false somewhere, the rank of the
communication matrix of `f` is less than `2 ^ d`. -/
theorem rank_communicationMatrix_lt_two_pow (hp : p.run = f) (h : ∃ x y, f x y = false) :
    (communicationMatrix R f).rank < 2 ^ p.depth :=
  (rank_communicationMatrix_lt_leafCount hp h).trans_le p.leafCount_le_two_pow_depth

end Protocol

/-- **The rank bound** [Mehlhorn and Schmidt][MehlhornSchmidt1982]: the communication complexity
of a Boolean function is at least `⌈log₂ r⌉`, for `r` the rank of its communication matrix over any
commutative ring with the strong rank condition, such as `ℝ`. -/
theorem clog_rank_le_ecomplexity [Fintype Y] (R : Type*) [CommSemiring R]
    [StrongRankCondition R] (f : X → Y → Bool) :
    (Nat.clog 2 (communicationMatrix R f).rank : ℕ∞) ≤
      Protocol.ecomplexity (fun x y b => f x y = b) Set.univ Set.univ :=
  Protocol.le_ecomplexity_iff.mpr fun _ hp => by
    exact_mod_cast Nat.clog_le_of_le_pow
      (Protocol.rank_communicationMatrix_le_two_pow (Protocol.solves_univ_iff.mp hp))

/-- **The log-rank conjecture** [LovaszSaks1993, Problem 2.7]: for some constant `c`, every
Boolean function `f` on finite sets has communication complexity at most `c (⌊log₂ r⌋ + 1) ^ c`,
where `r` is the rank of its communication matrix over `ℝ`. The rank bound
`clog_rank_le_ecomplexity` is the converse inequality up to rounding; the conjecture is open. -/
def LogRankConjecture : Prop :=
  ∃ c : ℕ, ∀ (X Y : Type) [Fintype X] [Fintype Y] (f : X → Y → Bool),
    Protocol.ecomplexity (fun x y b => f x y = b) Set.univ Set.univ ≤
      ((c * (Nat.log 2 (communicationMatrix ℝ f).rank + 1) ^ c : ℕ) : ℕ∞)

/-! ### Sign matrices -/

/-- The sign matrix of a Boolean function `f` over `R`: rows are indexed by Alice's inputs,
columns by Bob's inputs, and the entry at `x` and `y` is `-1` if `f x y` and `1` otherwise. -/
def signMatrix (R : Type*) [One R] [Neg R] (f : X → Y → Bool) : Matrix X Y R :=
  Matrix.of fun x y => if f x y then -1 else 1

/-- The entries of the sign matrix. -/
@[simp] theorem signMatrix_apply (R : Type*) [One R] [Neg R] (f : X → Y → Bool) (x : X) (y : Y) :
    signMatrix R f x y = if f x y then -1 else 1 :=
  rfl

/-- Over `ℝ`, the entries of the sign matrix are the signs `BitString.signVal` of the values. -/
theorem signMatrix_apply_eq_signVal (f : X → Y → Bool) (x : X) (y : Y) :
    signMatrix ℝ f x y = BitString.signVal (f x y) :=
  rfl

/-- The sign matrix is `J - 2 M_f`, for the all-ones matrix `J` and the communication matrix
`M_f`. -/
theorem signMatrix_eq_sub (R : Type*) [Ring R] (f : X → Y → Bool) :
    signMatrix R f = Matrix.of (fun _ _ => 1) - (2 : R) • communicationMatrix R f := by
  ext x y
  by_cases h : f x y <;> norm_num [h]

/-- The all-ones matrix has rank at most one. -/
private theorem rank_of_one_le [Fintype Y] (R : Type*) [CommSemiring R] [StrongRankCondition R] :
    (Matrix.of fun (_ : X) (_ : Y) => (1 : R)).rank ≤ 1 := by
  simpa [Matrix.vecMulVec] using Matrix.rank_vecMulVec_le (fun _ : X => (1 : R)) fun _ : Y => 1

section Field

variable [Fintype Y] {R : Type*} [Field R]

/-- The rank of the sign matrix exceeds that of the communication matrix by at most one, over any
field. -/
theorem rank_signMatrix_le (f : X → Y → Bool) :
    (signMatrix R f).rank ≤ (communicationMatrix R f).rank + 1 := by
  rw [signMatrix_eq_sub, add_comm]
  exact (Matrix.rank_sub_le _ _).trans
    (add_le_add (rank_of_one_le R) (Matrix.rank_smul_le _ _))

/-- When `2 ≠ 0`, the rank of the communication matrix exceeds that of the sign matrix by at most
one, since `M_f = (J - S_f) / 2`. In characteristic two this fails: the sign matrix is the all-ones
matrix. -/
theorem rank_communicationMatrix_le_rank_signMatrix [NeZero (2 : R)] (f : X → Y → Bool) :
    (communicationMatrix R f).rank ≤ (signMatrix R f).rank + 1 := by
  have h : communicationMatrix R f = (2 : R)⁻¹ • (Matrix.of (fun _ _ => 1) - signMatrix R f) := by
    rw [signMatrix_eq_sub, sub_sub_cancel, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
  rw [h, add_comm]
  exact (Matrix.rank_smul_le _ _).trans ((Matrix.rank_sub_le _ _).trans
    (add_le_add_left (rank_of_one_le R) _))

end Field

namespace Protocol

variable [Fintype Y] {R : Type*} [CommRing R] [StrongRankCondition R] {f : X → Y → Bool}
  {p : Protocol X Y Bool}

/-- The rank of the sign matrix of a function computed by a protocol is at most the number of
leaves. -/
theorem rank_signMatrix_le_leafCount (hp : p.run = f) : (signMatrix R f).rank ≤ p.leafCount :=
  rank_comp_le_leafCount hp fun b => if b then -1 else 1

/-- The rank of the sign matrix of a function computed by a protocol sending `d` bits is at most
`2 ^ d`. -/
theorem rank_signMatrix_le_two_pow (hp : p.run = f) : (signMatrix R f).rank ≤ 2 ^ p.depth :=
  (rank_signMatrix_le_leafCount hp).trans p.leafCount_le_two_pow_depth

end Protocol

end Cslib.Communication
