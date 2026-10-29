/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Arithmetic.RelativeRankUpper
public import Complexity.Computability.Circuit.Arithmetic.WordPolynomial
import Complexity.Foundations.LinearAlgebra.Matrix.ListProd

/-!
# Lower bound for set-multilinear formulas computing iterated matrix multiplication

LST Lemma 15 (Limaye, Srinivasan and Tavenas [LimayeSrinivasanTavenas2021], ECCC TR21-081
revision 1, §5, statement p. 11, proof p. 12), for formulas, in explicit form: if `10 d ≤ k`,
`2 ^ k ≤ n` and `1 ≤ Δ`, a syntactically set-multilinear formula of product-depth at most `Δ`
computing `IMM_{n,d}` (with its variables renamed) has at least
`2 ^ (k (d ^ (1 / (2 ^ Δ - 1)) / 20 - 1 / 2))` nodes
(`SPFormula.IsSetMultilinear.two_rpow_le_nodeCount_of_imm`). The source assumes
`n ≥ 2 ^ (10 d + 1)` and takes `k = ⌊log₂ n⌋`; these satisfy `10 d ≤ k` and `2 ^ k ≤ n`, so the
hypotheses here are weaker. The bound exceeds `1` only when `d ^ (1 / (2 ^ Δ - 1)) > 10`.

**The model.** LST's set-multilinear circuits are gate-wise semantic: each internal gate computes
a set-multilinear polynomial in a subset of the blocks [LimayeSrinivasanTavenas2021, §1, p. 2].
The hypothesis here is the stricter syntactic predicate `SPFormula.IsSetMultilinear`, for the
blocks of `IMM_{n,d}` (block `i` holds the entries of the `i`-th matrix): the children of a sum
gate are set-multilinear on the same set of blocks, and the children of a product gate on sets
partitioning it. The headline is LST Lemma 15 restricted to such formulas; turning a semantically
set-multilinear formula into a syntactically set-multilinear one of no larger size and
product-depth is a normalization step not done here. The hypotheses are met for every `n` and
`d` by the sum over paths of product-depth one (`immFormula`).

The proof follows the source. Let `w` be the greedy word of the proof of LST Lemma 13 over the
alphabet `{⌊k / √2⌋, -k}` (`sqrtTwoWord`): it is `k`-unbiased (`isUnbiased_sqrtTwoWord`). By LST
Lemma 8 in its fixed-sink form (`projection_wordSubst_imm`), substituting into `IMM_{n,d}` a
variable of block `i` of `X(w)` or `0` for each variable of block `i` gives the word polynomial
`wordPoly K w 0`. Doing the same substitution in the formula (`SPFormula.subst`) keeps it
set-multilinear (`SPFormula.IsSetMultilinear.subst`), and keeps its size and product-depth
(`SPFormula.nodeCount_subst`, `SPFormula.productDepth_subst`). The word polynomial has relative
rank `2 ^ (-|∑ w| / 2) ≥ 2 ^ (-k / 2)` (`relRank_wordPoly`), and LST Claim 16
(`SPFormula.IsSetMultilinear.relRank_polynomial_le_univ`) bounds it by
`nodeCount · 2 ^ (-k d ^ (1 / (2 ^ Δ - 1)) / 20)`.

**Original.** The explicit non-asymptotic statement, and the substitution of formulas, which
replaces a variable set to `0` by the formula `SPFormula.zero` (a sum gate without arguments,
set-multilinear on every set of blocks), so that the substitution keeps syntactic
set-multilinearity without changing the size or the product-depth. LST state Lemma 15 for
circuits, which they first expand into formulas; this file works with formulas directly. The
relative rank is invariant under renaming the variables along their blocks (`relRank_rename`),
which moves the word polynomial onto the variables `Fin m` of a formula.

## Main definitions

* `Cslib.Circuits.Arithmetic.sqrtTwoWord`: the word of LST Lemma 15.
* `Cslib.Circuits.Arithmetic.SPFormula.subst`: substitute variables or `0` for the variables of a
  formula.
* `Cslib.Circuits.Arithmetic.immFormula`: the sum over paths computing `IMM_{n,d}`, on the
  variables numbered by `immVarEquiv`.

## Main results

* `Cslib.Circuits.Arithmetic.isUnbiased_sqrtTwoWord`: the word is `k`-unbiased.
* `Cslib.Circuits.Arithmetic.SPFormula.polynomial_subst`,
  `Cslib.Circuits.Arithmetic.SPFormula.IsSetMultilinear.subst`: substitution of formulas.
* `Cslib.Circuits.Arithmetic.SPFormula.IsSetMultilinear.two_rpow_le_nodeCount_of_imm`: LST
  Lemma 15 for syntactically set-multilinear formulas.
* `Cslib.Circuits.Arithmetic.isSetMultilinear_immFormula`,
  `Cslib.Circuits.Arithmetic.productDepth_immFormula_le`,
  `Cslib.Circuits.Arithmetic.rename_polynomial_immFormula`: the hypotheses of the lower bound are
  met by a formula, for every `n` and `d`.

## References

* [N. Limaye, S. Srinivasan, S. Tavenas, *Superpolynomial lower bounds against low-depth algebraic
  circuits*][LimayeSrinivasanTavenas2021], ECCC TR21-081 revision 1: the definition of
  set-multilinear circuits (§1, p. 2), Lemma 8 (§2.2, p. 7), proof of Lemma 13 (§4, p. 10),
  Lemma 15 and its proof (§5, pp. 11–12)
-/

@[expose] public section

namespace Cslib.Circuits.Arithmetic

open MvPolynomial

variable {K : Type*} {d : ℕ}

/-! ### The word of Lemma 15 -/

section Word

/-- `0 ≤ ⌊k / √2⌋ ≤ k`, so the greedy word over `{⌊k / √2⌋, -k}` is `k`-unbiased. -/
theorem floor_div_sqrt_two_mem_Icc (k : ℕ) : 0 ≤ ⌊(k : ℝ) / √2⌋ ∧ ⌊(k : ℝ) / √2⌋ ≤ k := by
  have hs : 1 ≤ √2 := Real.one_le_sqrt.mpr one_le_two
  refine ⟨Int.floor_nonneg.mpr (by positivity), Int.floor_le_iff.mpr ?_⟩
  push_cast
  calc (k : ℝ) / √2 ≤ k := div_le_self (Nat.cast_nonneg k) hs
    _ < k + 1 := lt_add_one _

/-- **The word of LST Lemma 15** (proof of Lemma 15, p. 12, following the proof of Lemma 13,
p. 10): the greedy word of length `d` over the alphabet `{⌊k / √2⌋, -k}`, whose `i`-th letter
is `⌊k / √2⌋` if the sum of the earlier letters is at most `0`, and `-k` otherwise. -/
noncomputable def sqrtTwoWord (k d : ℕ) : Fin d → ℤ :=
  greedyWord ⌊(k : ℝ) / √2⌋ k d

/-- Every letter of the word of Lemma 15 is `⌊k / √2⌋` or `-k`. -/
theorem sqrtTwoWord_eq_or (k : ℕ) (i : Fin d) :
    sqrtTwoWord k d i = ⌊(k : ℝ) / √2⌋ ∨ sqrtTwoWord k d i = -k :=
  greedyWord_eq_or _ _ i

/-- **The word of Lemma 15 is `k`-unbiased** (LST, proof of Lemma 13): every prefix sum has
absolute value at most `k`. -/
theorem isUnbiased_sqrtTwoWord (k d : ℕ) : IsUnbiased (sqrtTwoWord k d) k :=
  isUnbiased_greedyWord (floor_div_sqrt_two_mem_Icc k).1 (floor_div_sqrt_two_mem_Icc k).2

/-- The sum of all the letters of the word of Lemma 15 has absolute value at most `k`. -/
theorem natAbs_sum_sqrtTwoWord_le (k d : ℕ) : (∑ i, sqrtTwoWord k d i).natAbs ≤ k := by
  simpa using isUnbiased_sqrtTwoWord k d d le_rfl

end Word

/-! ### Substitution in formulas -/

namespace SPFormula

variable {n m : ℕ}

/-- **Substitution of variables or `0`**: replace each input `i` by the input `j` when
`ρ i = some j`, and by the formula `0` (a sum gate without arguments) when `ρ i = none`. It is
the substitution `Cslib.Circuits.Formula.bind` of these formulas. -/
def subst (ρ : Fin n → Option (Fin m)) (F : SPFormula K n) : SPFormula K m :=
  F.bind fun i => (ρ i).elim zero .input

/-- Substitution replaces an input by an input or by `0`. -/
@[simp]
theorem subst_input (ρ : Fin n → Option (Fin m)) (i : Fin n) :
    subst ρ (Formula.input i : SPFormula K n) = (ρ i).elim zero .input :=
  rfl

/-- Substitution in an operation node substitutes in each argument. -/
@[simp]
theorem subst_gate (ρ : Fin n → Option (Fin m)) (op : SigmaPiOp K)
    (args : Fin ((sigmaPiSignature K).Arity op) → SPFormula K n) :
    subst ρ (Formula.gate op args : SPFormula K n) = .gate op fun j => subst ρ (args j) :=
  rfl

/-- Substitution keeps the number of nodes. -/
@[simp]
theorem nodeCount_subst (ρ : Fin n → Option (Fin m)) (F : SPFormula K n) :
    (subst ρ F).nodeCount = F.nodeCount := by
  induction F with
  | input i => cases h : ρ i <;> simp [h]
  | gate op args ih => simp only [subst_gate, Formula.nodeCount_gate, ih]

/-- Substitution keeps the product-depth. -/
@[simp]
theorem productDepth_subst (ρ : Fin n → Option (Fin m)) (F : SPFormula K n) :
    (subst ρ F).productDepth = F.productDepth := by
  induction F with
  | input i => cases h : ρ i <;> simp [h]
  | gate op args ih =>
    simp only [productDepth, subst_gate, Formula.depthWith] at ih ⊢
    simp only [ih]

/-- **The substituted formula computes the substituted polynomial.** -/
theorem polynomial_subst [CommSemiring K] (ρ : Fin n → Option (Fin m)) (F : SPFormula K n) :
    (subst ρ F).polynomial = aeval (fun i => (ρ i).elim 0 X) F.polynomial := by
  rw [aeval_polynomial, algebraMap_eq, polynomial, subst, Formula.eval_bind]
  congr 1
  funext i
  rcases ρ i with _ | j
  · exact polynomial_zero
  · rfl

/-- **Substitution keeps set-multilinearity**: if every variable is replaced by a variable of
the same block or by `0`, a formula set-multilinear on `S` stays set-multilinear on `S`. -/
theorem IsSetMultilinear.subst {blk : Fin n → Fin d} {blk' : Fin m → Fin d}
    {ρ : Fin n → Option (Fin m)} (hρ : ∀ i j, ρ i = some j → blk' j = blk i)
    {F : SPFormula K n} {S : Finset (Fin d)} (hF : F.IsSetMultilinear blk S) :
    (subst ρ F).IsSetMultilinear blk' S := by
  induction hF with
  | input i =>
    rcases h : ρ i with _ | j
    · rw [subst_input, h]
      exact isSetMultilinear_zero _
    · rw [subst_input, h, ← hρ i j h]
      exact .input j
  | const a =>
    have h : SPFormula.subst ρ (SPFormula.const a : SPFormula K n) = SPFormula.const a := by
      rw [subst_gate]
      congr 1
      funext j
      exact j.elim0
    rw [h]
    exact .const a
  | add c F S _ ih => exact .add c _ S ih
  | mul F T hT _ ih => exact .mul _ T hT ih

end SPFormula

/-! ### The lower bound -/

namespace SPFormula

variable {n N : ℕ}

variable (K) in
/-- The substitution of Lemma 8 (`wordSubst`, sink `0`) for a formula computing `IMM_{n,d}` with
its variables renamed by `e`, with the variables of `X(w)` numbered by `f`: `none` stands for
the constant `0`. -/
private noncomputable def immSubst [Zero K] (w : Fin d → ℤ) (e : Fin N → Fin d × Fin n × Fin n)
    (f : WordVar w ≃ Fin (Fintype.card (WordVar w))) (v : Fin N) :
    Option (Fin (Fintype.card (WordVar w))) :=
  (wordSubst w 0 n K (e v)).elim (fun x => some (f x)) fun _ => none

variable [Field K] [NeZero n]

/-- **LST Lemma 15 for syntactically set-multilinear formulas** (ECCC TR21-081 rev. 1, §5,
statement p. 11, proof p. 12, explicit form): let `10 d ≤ k`, `2 ^ k ≤ n` and `1 ≤ Δ`. If `F`
is a formula that is syntactically set-multilinear (`SPFormula.IsSetMultilinear`) on all `d`
blocks of `IMM_{n,d}`, block `i` being the entries of the `i`-th matrix, of product-depth at
most `Δ`, and computes `IMM_{n,d}` with its variables renamed by `e`, then `F` has at least
`2 ^ (k (d ^ (1 / (2 ^ Δ - 1)) / 20 - 1 / 2))` nodes. The bound is nontrivial only when
`d ^ (1 / (2 ^ Δ - 1)) > 10`. The hypotheses are met by `immFormula` for every `n` and `d`.

The source assumes `n ≥ 2 ^ (10 d + 1)` and takes `k = ⌊log₂ n⌋`, which gives `10 d ≤ k` and
`2 ^ k ≤ n`; the hypotheses here are weaker. It states the bound `n ^ Ω(d ^ (1 / (2 ^ Δ - 1)) / Δ)`
for set-multilinear circuits in the gate-wise semantic sense, each internal gate computing a
set-multilinear polynomial in a subset of the blocks (§1, p. 2); this is the formula bound in its
proof, before the expansion of circuits into formulas, under the stricter syntactic predicate:
the children of a sum gate share their set of blocks, and the children of a product gate
partition it. Reaching it from a semantically set-multilinear formula is a normalization step
not proved here. The non-asymptotic statement is original. -/
theorem IsSetMultilinear.two_rpow_le_nodeCount_of_imm (e : Fin N → Fin d × Fin n × Fin n)
    {k Δ : ℕ} (hk : 10 * d ≤ k) (hn : 2 ^ k ≤ n) (hΔ : 1 ≤ Δ) {F : SPFormula K N}
    (hF : F.IsSetMultilinear (fun v => (e v).1) Finset.univ) (hFΔ : F.productDepth ≤ Δ)
    (hFP : rename e F.polynomial = imm K n d) :
    (2 : ℝ) ^ ((k : ℝ) * ((d : ℝ) ^ (1 / (2 ^ Δ - 1 : ℝ)) / 20 - 1 / 2)) ≤ F.nodeCount := by
  classical
  set w := sqrtTwoWord k d
  set f := Fintype.equivFin (WordVar w)
  set ρ := immSubst K w e f
  set blk' : Fin (Fintype.card (WordVar w)) → Fin d := fun j => (f.symm j).1
  set G := SPFormula.subst ρ F
  -- The substitution respects the blocks.
  have hρ : ∀ v j, ρ v = some j → blk' j = (e v).1 := by
    intro v j hv
    simp only [ρ, immSubst] at hv
    rcases h : wordSubst w 0 n K (e v) with x | a
    · rw [h] at hv
      obtain rfl := (Option.some.inj hv).symm
      simp only [blk', Equiv.symm_apply_apply]
      exact wordSubst_eq_inl h
    · rw [h] at hv
      exact absurd hv (by simp)
  have hG : G.IsSetMultilinear blk' Finset.univ := hF.subst hρ
  -- The substituted formula computes the word polynomial, renamed.
  have hGP : G.polynomial = rename f (wordPoly K w 0) := by
    have hτ : 0 < 2 ^ (∑ i, w i).natAbs := Nat.two_pow_pos _
    rw [← projection_wordSubst_imm (isUnbiased_sqrtTwoWord k d) hn hτ, ← hFP, polynomial_subst]
    change _ = ((rename f).comp ((projection (wordSubst w 0 n K)).comp
      (rename e))) F.polynomial
    congr 1
    refine algHom_ext fun v => ?_
    simp only [aeval_X, AlgHom.comp_apply, rename_X, projection_X, ρ,
      immSubst]
    rcases h : wordSubst w 0 n K (e v) with x | a
    · simp
    · obtain rfl := wordSubst_eq_inr h
      simp
  -- Block `i` of the renamed variables has `2 ^ |w i|` variables.
  have hblk : ∀ i, Fintype.card {x // blk' x = i} = 2 ^ (w i).natAbs := by
    intro i
    rw [Fintype.card_congr ((f.symm.subtypeEquiv fun _ => Iff.rfl).trans (Equiv.sigmaSubtype i)),
      Fintype.card_fin]
  have hup := hG.relRank_polynomial_le_univ hblk hk (sqrtTwoWord_eq_or k) hΔ
    (by simpa [G] using hFΔ)
  rw [hGP, relRank_rename (blk := Sigma.fst) f (fun _ => by simp [blk']),
    relRank_wordPoly (Nat.two_pow_pos _), nodeCount_subst] at hup
  -- Combine the two bounds.
  have hsum : (2 : ℝ) ^ (-(k : ℝ) / 2) ≤ 2 ^ (-((∑ i, w i).natAbs : ℝ) / 2) := by
    refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
    have : ((∑ i, w i).natAbs : ℝ) ≤ k := by exact_mod_cast natAbs_sum_sqrtTwoWord_le k d
    linarith
  set D := (d : ℝ) ^ (1 / (2 ^ Δ - 1 : ℝ))
  have hsplit : (2 : ℝ) ^ ((k : ℝ) * (D / 20 - 1 / 2)) * 2 ^ (-(k * D / 20)) =
      2 ^ (-(k : ℝ) / 2) := by
    rw [← Real.rpow_add two_pos]
    congr 1
    ring
  have hx : (0 : ℝ) < 2 ^ (-(k * D / 20)) := Real.rpow_pos_of_pos two_pos _
  exact le_of_mul_le_mul_right (hsplit.trans_le (hsum.trans hup)) hx

end SPFormula

/-! ### The sum over paths computes `IMM_{n,d}` -/

section IMMFormula

open SPFormula

/-- The numbering of the `d n²` variables of `IMM_{n,d}`: the variable `(i, a, c)`, the entry
`(a, c)` of the `i`-th matrix, is numbered `i n² + a n + c`. -/
def immVarEquiv (n d : ℕ) : Fin (d * (n * n)) ≃ Fin d × Fin n × Fin n :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv.symm)

variable (K) in
/-- **The sum over paths for `IMM_{n,d}`**, a formula of product-depth one: a sum gate over all
sequences `p : Fin (d + 1) → Fin n` of the products `∏ i, x_{(i, p i, p (i + 1))}`, with edge
constant `1` on the paths from `0` to `0` and `0` on the others. -/
def immFormula [Zero K] [One K] (n d : ℕ) [NeZero n] : SPFormula K (d * (n * n)) :=
  add (fun j => if finFunctionFinEquiv.symm j 0 = 0 ∧
      finFunctionFinEquiv.symm j (Fin.last d) = 0 then 1 else 0)
    fun j : Fin (n ^ (d + 1)) => mul fun i : Fin d => .input
      ((immVarEquiv n d).symm (i, finFunctionFinEquiv.symm j i.castSucc,
        finFunctionFinEquiv.symm j i.succ))

variable (n : ℕ) [NeZero n]

/-- The sum over paths has product-depth at most one. -/
theorem productDepth_immFormula_le [Zero K] [One K] :
    (immFormula K n d).productDepth ≤ 1 := by
  rw [immFormula, productDepth_add]
  exact Finset.sup_le fun j _ => by simp

/-- The sum over paths is set-multilinear on all blocks of `IMM_{n,d}`. -/
theorem isSetMultilinear_immFormula [Zero K] [One K] :
    (immFormula K n d).IsSetMultilinear (fun v => (immVarEquiv n d v).1) Finset.univ := by
  refine .add _ _ _ fun j => isSetMultilinear_mul_iff.2
    ⟨fun i => {i}, fun i i' h => Finset.disjoint_singleton.2 h, fun i => ?_, by simp⟩
  exact isSetMultilinear_input_iff.2 (by simp)

/-- The sum over paths computes `IMM_{n,d}` on the numbered variables. -/
theorem rename_polynomial_immFormula [CommSemiring K] :
    rename (immVarEquiv n d) (immFormula K n d).polynomial = imm K n d := by
  rw [imm, Matrix.list_prod_ofFn_apply, immFormula, polynomial_add, map_sum]
  refine Fintype.sum_equiv finFunctionFinEquiv.symm _ _ fun j => ?_
  split_ifs <;> simp [immMatrix]

end IMMFormula

end Cslib.Circuits.Arithmetic
