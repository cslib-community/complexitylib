/-
Copyright (c) 2026 András Z. Salamon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Z. Salamon
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Order.Setoid.Basic
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# The join matrix of the partition lattice

Partitions of a finite type `α` are equivalence relations `Setoid α`, ordered by refinement, so that
the join `P ⊔ Q` is the finest partition coarser than both and `⊤` is the partition with one block.
The *join matrix* has rows and columns indexed by the partitions, and entry $1$ at $P$ and $Q$ if
$P \sqcup Q = \top$ and $0$ otherwise. It is nonsingular over any field of characteristic zero
(`rank_joinMatrix`). Dowling and Wilson prove this over $\mathbb{Q}$ for every finite lattice
whose Möbius function satisfies $\mu(a, \top) \ne 0$ for all $a$, which holds in geometric lattices
[DowlingWilson1975, Lemma 1 and the proof of Theorem 2]; here it is proved for the partition
lattice, the lattice of flats of the graphic matroid of a complete graph. In the terms of
[LovaszSaks1993, Theorems 3.4 and 3.6] the join matrix is the span indicator of that matroid, and
its rank is the number of partitions $x$ with $\mu(x, \top) \ne 0$, which is all of them.
Lindström's determinant formula for meet semilattices [Lindstrom1969, Theorem], applied to the
dual order with $f_i(x) = [x = \top]$, gives $\det J = \prod_x \mu(x, \top)$ directly.

The proof writes the join matrix as $J = Z \Delta Z^{\mathsf{T}}$, where $Z$ is the zeta matrix of
the refinement order, which is triangular with unit diagonal when the partitions are ordered by
their numbers of blocks, and $\Delta$ is diagonal with entry $c(b)$ at a partition with $b$ blocks.
Here $c(b)$ is the derivative at $0$ of the falling factorial $X (X - 1) \cdots (X - b + 1)$, that
is $(-1)^{b-1} (b-1)!$. Writing $b(z)$ for the number of blocks of $z$, the factorisation rests on
the identity $\sum_{z \ge x} c(b(z)) = [x = \top]$, the values of the Möbius function of the
partition lattice. It follows by differentiating at $0$ the polynomial identity
$$\sum_{z \ge x} X (X - 1) \cdots (X - b(z) + 1) = X^{b(x)},$$
which holds at every natural number $t$ because both sides count the maps from `α` to `Fin t` that
are constant on the blocks of $x$, grouped on the left by their kernels
(`sum_descFactorial_blocks`). This classical counting
argument avoids factorising intervals into products of smaller partition lattices, which Mathlib
does not provide; `mu_top` identifies the values with Mathlib's `IncidenceAlgebra.mu`.

Partitions are `Setoid α` rather than `Finpartition`, since Mathlib's complete lattice on
`Setoid α` provides the join, and the proof works with quotients and kernels (`Setoid.ker`);
`blocks s` is `Nat.card (Quotient s)`. Only a `Finite` instance on `Setoid α` is declared;
statements that sum over the partitions or take ranks assume `[Fintype (Setoid α)]`, which
`Fintype.ofFinite` provides, and counts are stated with `Nat.card`.

## Main definitions

* `Cslib.SetPartition.blocks`: the number of blocks of a partition.
* `Cslib.SetPartition.derivCoeff`: the coefficient $c(b)$, the derivative at $0$ of the falling
  factorial.
* `Cslib.SetPartition.joinMatrix`: the join matrix.
* `Cslib.SetPartition.zetaMatrix`: the zeta matrix of the refinement order.

## Main results

* `Cslib.SetPartition.pow_le_card_setoid`: $j^{N-j} \le B_N$, where $B_N$ is the number of
  partitions of $N$ elements.
* `Cslib.SetPartition.sum_descFactorial_blocks`: counting maps by their kernels.
* `Cslib.SetPartition.derivCoeff_succ`: $c(b + 1) = (-1)^b b!$.
* `Cslib.SetPartition.sum_derivCoeff_blocks`: the Möbius values
  $\sum_{z \ge x} c(b(z)) = [x = \top]$.
* `Cslib.SetPartition.mu_top`: these are the values $\mu(x, \top)$ of Mathlib's Möbius function
  `IncidenceAlgebra.mu`.
* `Cslib.SetPartition.joinMatrix_eq`: the factorisation $J = Z \Delta Z^{\mathsf{T}}$.
* `Cslib.SetPartition.det_zetaMatrix`: the zeta matrix has determinant $1$.
* `Cslib.SetPartition.rank_joinMatrix`: the join matrix has full rank.

## References

* [T. A. Dowling and R. M. Wilson, *Whitney number inequalities for geometric
  lattices*][DowlingWilson1975]
* [B. Lindström, *Determinants on semilattices*][Lindstrom1969]
* [L. Lovász and M. Saks, *Communication complexity and combinatorial lattice
  theory*][LovaszSaks1993]
-/

public section

namespace Cslib.SetPartition

open Finset Polynomial

variable {α : Type*}

/-- There are finitely many partitions of a finite type. Where a `Fintype (Setoid α)` instance is
needed, any will do, for example the noncomputable `Fintype.ofFinite`. -/
instance instFiniteSetoid [Finite α] : Finite (Setoid α) :=
  Finite.of_injective (fun s : Setoid α => (⇑s : α → α → Prop)) fun _ _ h =>
    Setoid.ext fun a b => iff_of_eq (congrFun (congrFun h a) b)

/-- The number of blocks of a partition, that is, of its equivalence classes. -/
noncomputable def blocks (s : Setoid α) : ℕ :=
  Nat.card (Quotient s)

/-! ### Blocks -/

section Blocks

/-- The discrete partition has one block for each element. -/
theorem blocks_bot : blocks (⊥ : Setoid α) = Nat.card α :=
  Nat.card_congr Setoid.quotientBotEquiv

/-- A partition of a finite nonempty type has at least one block. -/
theorem blocks_pos [Finite α] [Nonempty α] (s : Setoid α) : 0 < blocks s :=
  have : Nonempty (Quotient s) := ⟨Quotient.mk s (Classical.arbitrary α)⟩
  Nat.card_pos

/-- A partition of a nonempty type has one block exactly when it is the one-block partition `⊤`. -/
theorem blocks_eq_one_iff [Nonempty α] {s : Setoid α} : blocks s = 1 ↔ s = ⊤ := by
  have : Nonempty (Quotient s) := ⟨Quotient.mk s (Classical.arbitrary α)⟩
  rw [blocks, Nat.card_eq_one_iff_unique, ← Quotient.subsingleton_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, inferInstance⟩⟩

private theorem factor_surjective {r s : Setoid α} (h : r ≤ s) :
    Function.Surjective (Quot.factor r.r s.r fun _ _ hab => h hab) :=
  Quot.ind fun a => ⟨Quot.mk _ a, rfl⟩

/-- A coarser partition has at most as many blocks. -/
theorem blocks_le_of_le [Finite α] {r s : Setoid α} (h : r ≤ s) : blocks s ≤ blocks r :=
  Nat.card_le_card_of_surjective _ (factor_surjective h)

/-- A partition is determined by any coarser partition with as many blocks. -/
theorem eq_of_le_of_blocks_eq [Finite α] {r s : Setoid α} (h : r ≤ s)
    (hb : blocks r = blocks s) : r = s := by
  classical
  have hinj : Function.Injective (Quot.factor r.r s.r fun _ _ hab => h hab) := by
    have : Fintype (Quot r.r) := Fintype.ofFinite _
    have : Fintype (Quot s.r) := Fintype.ofFinite _
    refine ((Fintype.bijective_iff_surjective_and_card _).mpr ⟨factor_surjective h, ?_⟩).1
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hb
  refine le_antisymm h fun a b hab => ?_
  exact Quotient.exact (hinj (Quotient.sound hab : Quotient.mk s a = Quotient.mk s b))

end Blocks

/-! ### A lower bound on the number of partitions -/

section Many

/-- The map that is the identity on the first `j` elements of `Fin N` and `f` on the rest. -/
private def extendMap {N j : ℕ} (f : Fin (N - j) → Fin j) (i : Fin N) : Fin j :=
  if h : (i : ℕ) < j then ⟨i, h⟩ else f ⟨i - j, by omega⟩

private theorem extendMap_injective_ker {N j : ℕ} (hj : j ≤ N) :
    Function.Injective fun f : Fin (N - j) → Fin j => Setoid.ker (extendMap f) := by
  intro f₁ f₂ h
  funext t
  have hp : j + (t : ℕ) < N := by omega
  have key : ∀ f : Fin (N - j) → Fin j, ∀ i : Fin j,
      Setoid.ker (extendMap f) ⟨j + t, hp⟩ ⟨i, by omega⟩ ↔ f t = i := by
    intro f i
    rw [Setoid.ker_def]
    simp only [extendMap, show ¬(j + (t : ℕ) < j) by omega, i.2, ↓reduceDIte]
    simp only [add_tsub_cancel_left, Fin.eta]
  have h1 : Setoid.ker (extendMap f₁) ⟨j + t, hp⟩ ⟨f₁ t, by omega⟩ := (key f₁ (f₁ t)).mpr rfl
  simp only at h
  rw [h] at h1
  exact ((key f₂ (f₁ t)).mp h1).symm

/-- **Many partitions**: $j^{N-j} \le B_N$ for $j \le N$, by placing the first $j$ elements in
distinct blocks and each of the others in one of these blocks. -/
theorem pow_le_card_setoid {N j : ℕ} (hj : j ≤ N) :
    j ^ (N - j) ≤ Nat.card (Setoid (Fin N)) := by
  classical
  have := Fintype.ofFinite (Setoid (Fin N))
  have := Fintype.card_le_of_injective _ (extendMap_injective_ker hj)
  simpa [Fintype.card_fun, Fintype.card_fin, Nat.card_eq_fintype_card] using this

end Many

/-! ### Counting maps by their kernels -/

section Kernels

variable [Finite α] (t : ℕ)

/-- The maps constant on the blocks of `x` are the maps on its blocks. -/
private def constEquiv (x : Setoid α) :
    {f : α → Fin t // x ≤ Setoid.ker f} ≃ (Quotient x → Fin t) where
  toFun f := Quotient.lift f.1 fun _ _ h => f.2 h
  invFun g := ⟨g ∘ Quotient.mk x, fun _ _ h => by
    simp only [Setoid.ker_def, Function.comp_apply, Quotient.sound h]⟩
  left_inv _ := rfl
  right_inv g := funext fun q => Quotient.inductionOn q fun _ => rfl

/-- The maps with kernel `z` are the injective maps on its blocks. -/
private def kerEquiv (z : Setoid α) :
    {f : α → Fin t // Setoid.ker f = z} ≃ (Quotient z ↪ Fin t) where
  toFun f := ⟨Quotient.lift f.1 fun a b h => by
      rw [← f.2] at h
      exact Setoid.ker_def.mp h,
    fun p q => Quotient.inductionOn₂ p q fun a b hab => Quotient.sound (by
      have : Setoid.ker f.1 a b := Setoid.ker_def.mpr hab
      rwa [f.2] at this)⟩
  invFun e := ⟨e ∘ Quotient.mk z, Setoid.ext fun a b => by
    simp only [Setoid.ker_def, Function.comp_apply, e.injective.eq_iff, Quotient.eq]⟩
  left_inv _ := rfl
  right_inv e := by ext q; induction q using Quotient.inductionOn; rfl

private theorem card_const (x : Setoid α) :
    Nat.card {f : α → Fin t // x ≤ Setoid.ker f} = t ^ blocks x := by
  rw [Nat.card_congr (constEquiv t x), Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_fin,
    blocks]

private theorem card_ker (z : Setoid α) :
    Nat.card {f : α → Fin t // Setoid.ker f = z} = t.descFactorial (blocks z) := by
  classical
  have := Fintype.ofFinite (Quotient z)
  rw [Nat.card_congr (kerEquiv t z), Nat.card_eq_fintype_card, Fintype.card_embedding_eq,
    Fintype.card_fin, blocks, Nat.card_eq_fintype_card]

open Classical in
/-- Counting the maps constant on the blocks of `x` by their kernels:
$\sum_{z \ge x} t (t - 1) \cdots (t - b(z) + 1) = t^{b(x)}$, where $b(z)$ is the number of blocks
of $z$. -/
theorem sum_descFactorial_blocks [Fintype (Setoid α)] (x : Setoid α) :
    ∑ z ∈ {z | x ≤ z}, t.descFactorial (blocks z) = t ^ blocks x := by
  classical
  have := Fintype.ofFinite α
  rw [← card_const]
  simp_rw [← card_ker]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [card_eq_sum_card_fiberwise (f := fun f : α → Fin t => Setoid.ker f)
    (t := ({z | x ≤ z} : Finset (Setoid α))) fun f hf => by simpa using hf]
  refine sum_congr rfl fun z hz => ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, filter_filter]
  congr 1
  ext f
  simp only [mem_filter, mem_univ, true_and] at hz ⊢
  exact ⟨fun h => ⟨by rw [h]; exact hz, h⟩, fun h => h.2⟩

end Kernels

/-! ### The Möbius values -/

/-- The derivative at $0$ of the falling factorial $X (X - 1) \cdots (X - b + 1)$, which is
$(-1)^{b-1} (b-1)!$ for $b \ge 1$ (`derivCoeff_succ`). -/
noncomputable def derivCoeff (b : ℕ) : ℤ :=
  (derivative (descPochhammer ℤ b)).eval 0

/-- $c(1) = 1$. -/
theorem derivCoeff_one : derivCoeff 1 = 1 := by
  simp [derivCoeff]

/-- The recurrence $c(b + 2) = -(b + 1) c(b + 1)$, from
$X (X - 1) \cdots (X - b - 1) = X (X - 1) \cdots (X - b) \cdot (X - b - 1)$ and the vanishing of
the first factor at $0$. -/
theorem derivCoeff_succ_succ (b : ℕ) : derivCoeff (b + 2) = -(b + 1) * derivCoeff (b + 1) := by
  rw [derivCoeff, descPochhammer_succ_right, derivative_mul]
  simp only [derivative_sub, derivative_X, derivative_natCast, sub_zero, mul_one, eval_add,
    eval_mul, eval_sub, eval_X, eval_natCast, zero_sub,
    descPochhammer_ne_zero_eval_zero (R := ℤ) (Nat.succ_ne_zero b), add_zero, derivCoeff]
  push_cast
  ring

/-- The closed form $c(b + 1) = (-1)^b b!$. -/
theorem derivCoeff_succ (b : ℕ) : derivCoeff (b + 1) = (-1) ^ b * b.factorial := by
  induction b with
  | zero => simp [derivCoeff_one]
  | succ b ih =>
    rw [derivCoeff_succ_succ, ih, Nat.factorial_succ]
    push_cast
    ring

/-- $c(b) \ne 0$ for $b \ge 1$. -/
theorem derivCoeff_ne_zero {b : ℕ} (hb : 0 < b) : derivCoeff b ≠ 0 := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_lt hb
  rw [zero_add, derivCoeff_succ]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast b.factorial_ne_zero)

section Mobius

variable [Finite α]

open Classical in
/-- The polynomial identity $\sum_{z \ge x} X (X - 1) \cdots (X - b(z) + 1) = X^{b(x)}$, where
$b(z)$ is the number of blocks of $z$. -/
theorem sum_descPochhammer_blocks [Fintype (Setoid α)] (x : Setoid α) :
    ∑ z ∈ {z | x ≤ z}, descPochhammer ℤ (blocks z) = (X : ℤ[X]) ^ blocks x := by
  refine eq_of_infinite_eval_eq _ _ (Set.infinite_of_injective_forall_mem
    (f := fun t : ℕ => (t : ℤ)) Nat.cast_injective fun t => ?_)
  simp only [Set.mem_ofPred_eq, eval_finsetSum, descPochhammer_eval_eq_descFactorial, eval_pow,
    eval_X]
  exact_mod_cast sum_descFactorial_blocks t x

open Classical in
/-- **The Möbius values of the partition lattice**: $\sum_{z \ge x} c(b(z)) = [x = \top]$, where
$b(z)$ is the number of blocks of $z$ and $c(b) = (-1)^{b-1} (b-1)!$ (`derivCoeff`). -/
theorem sum_derivCoeff_blocks [Fintype (Setoid α)] [Nonempty α] (x : Setoid α) :
    ∑ z ∈ {z | x ≤ z}, derivCoeff (blocks z) = if x = ⊤ then 1 else 0 := by
  have h := congrArg (fun p : ℤ[X] => (derivative p).eval 0) (sum_descPochhammer_blocks x)
  simp only [derivative_sum, eval_finsetSum, derivative_X_pow, eval_mul, eval_C, eval_pow,
    eval_X] at h
  simp only [derivCoeff, h, ← blocks_eq_one_iff]
  have := blocks_pos x
  rcases Nat.lt_or_ge (blocks x) 2 with hb | hb
  · obtain h1 : blocks x = 1 := by omega
    simp [h1]
  · simp [show blocks x ≠ 1 by omega, zero_pow (show blocks x - 1 ≠ 0 by omega)]

/-- **The Möbius function of the partition lattice** at the top: $\mu(x, \top) = c(b)$, which is
$(-1)^{b-1} (b-1)!$, for a partition $x$ with $b$ blocks. The locally finite order on the partitions
may be any instance, such as `Fintype.toLocallyFiniteOrder`. -/
theorem mu_top [Nonempty α] [LocallyFiniteOrder (Setoid α)] [DecidableEq (Setoid α)]
    (x : Setoid α) : IncidenceAlgebra.mu ℤ x ⊤ = derivCoeff (blocks x) := by
  classical
  have := Fintype.ofFinite (Setoid α)
  induction x using WellFoundedGT.induction with
  | _ x ih =>
  by_cases hx : x = ⊤
  · subst hx
    rw [IncidenceAlgebra.mu_self, (blocks_eq_one_iff (α := α)).mpr rfl, derivCoeff_one]
  have hsum := sum_derivCoeff_blocks x
  have hset : ({z | x ≤ z} : Finset (Setoid α)) = (Ioc x ⊤).cons x left_notMem_Ioc := by
    rw [← Icc_eq_cons_Ioc le_top]
    ext z
    simp
  rw [hset, sum_cons] at hsum
  simp only [hx, ↓reduceIte] at hsum
  rw [IncidenceAlgebra.mu_eq_neg_sum_Ioc_of_ne hx,
    sum_congr rfl fun z hz => ih z (mem_Ioc.mp hz).1]
  linarith

end Mobius

/-! ### The join matrix -/

open Classical in
/-- The join matrix over `R`: entry $1$ at $P$ and $Q$ if $P \sqcup Q = \top$, and $0$
otherwise. -/
@[expose] noncomputable def joinMatrix (R α : Type*) [Zero R] [One R] :
    Matrix (Setoid α) (Setoid α) R :=
  Matrix.of fun P Q => if P ⊔ Q = ⊤ then 1 else 0

open Classical in
/-- The entries of the join matrix. -/
@[simp] theorem joinMatrix_apply {R : Type*} [Zero R] [One R] (P Q : Setoid α) :
    joinMatrix R α P Q = if P ⊔ Q = ⊤ then 1 else 0 :=
  rfl

open Classical in
/-- The zeta matrix of the refinement order over `R`, entry $1$ at $P$ and $z$ if $P \le z$: the
matrix of Mathlib's `IncidenceAlgebra.zeta`. -/
@[expose] noncomputable def zetaMatrix (R α : Type*) [Zero R] [One R] :
    Matrix (Setoid α) (Setoid α) R :=
  Matrix.of fun P z => if P ≤ z then 1 else 0

section Matrices

variable [Finite α] [Fintype (Setoid α)] {R : Type*}

open Classical in
/-- **The factorisation $J = Z \Delta Z^{\mathsf{T}}$** of the join matrix, with $\Delta$ the
diagonal of the Möbius values $\mu(z, \top) = c(b(z))$, where $b(z)$ is the number of blocks of
$z$. -/
theorem joinMatrix_eq [CommRing R] [Nonempty α] :
    joinMatrix R α = zetaMatrix R α * Matrix.diagonal (fun z => (derivCoeff (blocks z) : R)) *
      (zetaMatrix R α).transpose := by
  ext P Q
  rw [Matrix.mul_apply]
  simp only [joinMatrix, zetaMatrix, Matrix.mul_diagonal, Matrix.of_apply,
    Matrix.transpose_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  have h := congrArg (fun k : ℤ => (k : R)) (sum_derivCoeff_blocks (P ⊔ Q))
  simp only [Int.cast_sum, apply_ite (fun k : ℤ => (k : R)), Int.cast_one, Int.cast_zero] at h
  rw [← h, sum_filter]
  refine sum_congr rfl fun z _ => ?_
  by_cases hP : P ≤ z <;> by_cases hQ : Q ≤ z <;> simp [hP, hQ, sup_le_iff]

open Classical in
/-- The zeta matrix is unitriangular when the partitions are ordered by their numbers of blocks, so
its determinant is $1$. -/
theorem det_zetaMatrix [CommRing R] : (zetaMatrix R α).det = 1 := by
  have hT : (zetaMatrix R α).BlockTriangular fun P => OrderDual.toDual (blocks P) := by
    intro P z hlt
    have : ¬P ≤ z := fun h => absurd (blocks_le_of_le h) (not_le.mpr hlt)
    simp [zetaMatrix, this]
  rw [hT.det]
  refine prod_eq_one fun b _ => ?_
  have : (zetaMatrix R α).toSquareBlock (fun P => OrderDual.toDual (blocks P)) b = 1 := by
    ext ⟨P, hP⟩ ⟨z, hz⟩
    simp only [Matrix.toSquareBlock_def, Matrix.of_apply, zetaMatrix, Matrix.one_apply,
      Subtype.mk.injEq]
    by_cases h : P ≤ z
    · have := eq_of_le_of_blocks_eq h (by simpa using hP.trans hz.symm)
      simp [this]
    · have hne : P ≠ z := by rintro rfl; exact h le_rfl
      simp [h, hne]
  rw [this, Matrix.det_one]

/-- **Dowling–Wilson for the partition lattice**: over a field of characteristic zero, the join
matrix has full rank, the number of partitions [DowlingWilson1975, Lemma 1 and the proof of
Theorem 2]. -/
theorem rank_joinMatrix [Field R] [CharZero R] : (joinMatrix R α).rank = Nat.card (Setoid α) := by
  classical
  rw [Nat.card_eq_fintype_card]
  rcases isEmpty_or_nonempty α with hα | hα
  · have : Subsingleton (Setoid α) := ⟨fun _ _ => Setoid.ext fun a => isEmptyElim a⟩
    have h1 : joinMatrix R α = 1 := by
      ext P Q
      obtain rfl : P = Q := Subsingleton.elim _ _
      have : P = ⊤ := Subsingleton.elim _ _
      simp [this]
    rw [h1, Matrix.rank_one]
  refine Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr ?_))
  rw [joinMatrix_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_zetaMatrix,
    Matrix.det_diagonal, one_mul, mul_one]
  exact prod_ne_zero_iff.mpr fun z _ => Int.cast_ne_zero.mpr (derivCoeff_ne_zero (blocks_pos z))

end Matrices

end Cslib.SetPartition
