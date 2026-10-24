/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Formula.Subbotovskaya
public import Complexity.Foundations.Data.BitString.Basic
import Cslib.Computability.Circuit.Boolean.Shannon
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Andreev's formula lower bound

Andreev's function `Boolean.andreev b m` on `2 ^ b + b * m` bits treats its first `2 ^ b` bits as
the truth table of a `b`-bit Boolean function `h`, divides its remaining `b * m` bits into `b`
blocks of `m` bits, computes the parity of each block, and evaluates `h` on the resulting `b`-bit
string [Andreev1987], [Jukna, Section 6.5][Jukna2012],
[Arora and Barak, Section 14.3][AroraBarak09].

Fixing the first `2 ^ b` bits to the truth table of any function `h : BooleanFunction b` leaves the
`b * m` block variables free. If a further restriction `ρ` leaves at least one free variable in each
of the `b` blocks, substituting a literal `± x_j` for one surviving variable in block `j` and `0`
for all other free variables turns any formula for `(andreev b m)↾ρ` into a formula for `h` without
increasing its leaf size (`Boolean.formulaSize_le_of_andreevBlock_nonempty`).

Choosing a uniformly random extension leaving `k = b * r` variables free (with `2 * b ≤ 2 ^ r`, for
instance `r = ⌊log₂ b⌋ + 2`), the fraction of extensions that fix an entire `m`-bit block is at
most `C(b m - m, b r) / C(b m, b r) ≤ (1 - 1 / b) ^ (b r) ≤ 2 ^ (-r) ≤ 1 / (2 b)`. By a union
bound, at least half of all extensions leave every block nonempty, so Subbotovskaya's average
shrinkage (`Boolean.exists_mem_formulaSize_sub_sq_le`) yields a single restriction that both
preserves a free variable in every block and shrinks the formula size by `(r / m) ^ (3 / 2)`:
`(L(h) - 2 b r) ^ 2 * m ^ 3 ≤ 4 * L(andreev b m) ^ 2 * r ^ 3`
(`Boolean.formulaSize_sub_sq_mul_pow_three_le_andreev`).

Combining this universal reduction with Shannon's counting theorem on `b` bits
(`Boolean.exists_hard_function_formulaSize`) gives Andreev's `n ^ (5 / 2 - o(1))` lower bound for an
explicit function (`Boolean.pow_two_mul_pow_three_le_formulaSize_andreev_sq`,
`Boolean.two_pow_five_mul_le_formulaSize_andreev_sq`).

## Main definitions

* `Cslib.Circuits.Boolean.andreevTableIndex`: the `2 ^ b` truth-table input coordinates of
  Andreev's function.
* `Cslib.Circuits.Boolean.andreevBlockVar`, `Cslib.Circuits.Boolean.andreevBlock`: the `b` blocks
  of `m` parity variables in Andreev's function.
* `Cslib.Circuits.Boolean.andreev`: Andreev's function on `2 ^ b + b * m` bits.
* `Cslib.Circuits.Boolean.andreevFixTable`: the partial assignment fixing the `2 ^ b` truth-table
  coordinates of `andreev b m` to the truth table of `h : BooleanFunction b`.

## Main results

* `Cslib.Circuits.Boolean.formulaSize_le_of_andreevBlock_nonempty`: if `ρ` extends
  `andreevFixTable b m h` and leaves at least one variable of each block free, then
  `L(h) ≤ L((andreev b m)↾ρ)`.
* `Cslib.Circuits.Boolean.formulaSize_sub_sq_mul_pow_three_le_andreev`: for every
  `h : BooleanFunction b`, `1 ≤ b`, `1 ≤ r ≤ m`, and `2 * b ≤ 2 ^ r`,
  `(L(h) - 2 b r) ^ 2 * m ^ 3 ≤ 4 * L(andreev b m) ^ 2 * r ^ 3`.
* `Cslib.Circuits.Boolean.exists_hard_function_formulaSize`: for all sufficiently large `b`, some
  `h : BooleanFunction b` satisfies `2 ^ b < 3 * b * L(h)`.
* `Cslib.Circuits.Boolean.pow_two_mul_pow_three_le_formulaSize_andreev_sq`,
  `Cslib.Circuits.Boolean.two_pow_five_mul_le_formulaSize_andreev_sq`: Andreev's explicit
  `n ^ (5 / 2 - o(1))` De Morgan formula size lower bound.

## References

* [A. E. Andreev, *On a Method for Obtaining More Than Quadratic Effective Lower Bounds for the
  Complexity of π-Schemes*][Andreev1987]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
* [S. Arora and B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open BitString Finset Function Formula

variable {n b m : ℕ}

/-! ### Andreev's function and truth-table restrictions -/

/-- The `idx`-th truth-table coordinate among the `2 ^ b + b * m` inputs of Andreev's function. -/
def andreevTableIndex (b m : ℕ) (idx : Fin (2 ^ b)) : Fin (2 ^ b + b * m) :=
  Fin.castAdd (b * m) idx

/-- The `t`-th variable of the `j`-th parity block among the `2 ^ b + b * m` inputs of Andreev's
function. -/
def andreevBlockVar (b m : ℕ) (j : Fin b) (t : Fin m) : Fin (2 ^ b + b * m) :=
  Fin.natAdd (2 ^ b) (finProdFinEquiv (j, t))

/-- The `m` input coordinates forming the `j`-th parity block of Andreev's function. -/
def andreevBlock (b m : ℕ) (j : Fin b) : Finset (Fin (2 ^ b + b * m)) :=
  univ.image (andreevBlockVar b m j)

/-- **Andreev's function** on `2 ^ b + b * m` bits: the first `2 ^ b` bits encode the truth table
of a `b`-bit function (indexed via `BitString.equivFin b`), and the remaining `b * m` bits form `b`
blocks of `m` bits whose parities are fed as the `b`-bit input to that truth table. -/
def andreev (b m : ℕ) : BooleanFunction (2 ^ b + b * m) :=
  fun w => w (andreevTableIndex b m
    (BitString.equivFin b fun j => parity m fun t => w (andreevBlockVar b m j t)))

/-- Within each block `j`, the block variable map `andreevBlockVar b m j` is injective. -/
theorem andreevBlockVar_injective (b m : ℕ) (j : Fin b) :
    Function.Injective (andreevBlockVar b m j) := by
  intro t₁ t₂ h
  have h1 := Fin.natAdd_injective (b * m) (2 ^ b) h
  have h2 := finProdFinEquiv.injective h1
  exact (Prod.ext_iff.1 h2).2

/-- Each parity block `andreevBlock b m j` has cardinality `m`. -/
@[simp] theorem card_andreevBlock (b m : ℕ) (j : Fin b) :
    #(andreevBlock b m j) = m := by
  rw [andreevBlock, card_image_of_injective _ (andreevBlockVar_injective b m j), card_univ,
    Fintype.card_fin]

/-- The partial assignment fixing the first `2 ^ b` inputs of `andreev b m` to the truth table of
`h : BooleanFunction b` and leaving all `b * m` block inputs free. -/
def andreevFixTable (b m : ℕ) (h : BooleanFunction b) :
    PartialAssignment (Fin (2 ^ b + b * m)) :=
  Fin.addCases (fun idx => some (h ((BitString.equivFin b).symm idx))) (fun _ => none)

/-- `andreevFixTable b m h` fixes the `idx`-th truth-table coordinate to the value of `h` at
`idx`. -/
@[simp] theorem andreevFixTable_tableIndex (b m : ℕ) (h : BooleanFunction b)
    (idx : Fin (2 ^ b)) :
    andreevFixTable b m h (andreevTableIndex b m idx) =
      some (h ((BitString.equivFin b).symm idx)) := by
  simp [andreevFixTable, andreevTableIndex]

/-- `andreevFixTable b m h` leaves every coordinate past the first `2 ^ b` truth-table bits
free. -/
@[simp] theorem andreevFixTable_natAdd (b m : ℕ) (h : BooleanFunction b) (u : Fin (b * m)) :
    andreevFixTable b m h (Fin.natAdd (2 ^ b) u) = none := by
  simp [andreevFixTable]

/-- `andreevFixTable b m h` leaves every block variable `andreevBlockVar b m j t` free. -/
@[simp] theorem andreevFixTable_blockVar (b m : ℕ) (h : BooleanFunction b)
    (j : Fin b) (t : Fin m) :
    andreevFixTable b m h (andreevBlockVar b m j t) = none := by
  simp [andreevBlockVar]

private theorem free_andreevFixTable (b m : ℕ) (h : BooleanFunction b) :
    (andreevFixTable b m h).free = univ.image (Fin.natAdd (2 ^ b)) := by
  ext i
  simp only [PartialAssignment.mem_free, mem_image, mem_univ, true_and]
  refine ⟨?_, ?_⟩
  · refine Fin.addCases (fun idx hbad => ?_) (fun u _ => ⟨u, rfl⟩) i
    simp [andreevFixTable] at hbad
  · rintro ⟨u, rfl⟩
    exact andreevFixTable_natAdd b m h u

/-- `andreevFixTable b m h` has `b * m` free variables. -/
@[simp] theorem card_free_andreevFixTable (b m : ℕ) (h : BooleanFunction b) :
    #(andreevFixTable b m h).free = b * m := by
  rw [free_andreevFixTable, card_image_of_injective _ (Fin.natAdd_injective (b * m) (2 ^ b)),
    card_univ, Fintype.card_fin]

/-- Every parity block `andreevBlock b m j` is contained in the free variables of
`andreevFixTable b m h`. -/
theorem andreevBlock_subset_free_andreevFixTable (b m : ℕ) (h : BooleanFunction b) (j : Fin b) :
    andreevBlock b m j ⊆ (andreevFixTable b m h).free := by
  intro i hi
  rcases mem_image.1 hi with ⟨t, -, rfl⟩
  simp [PartialAssignment.mem_free]

/-- Under any extension `ρ` of `andreevFixTable b m h`, Andreev's function evaluates `h` on the
block parities of `ρ.fill w`. -/
private theorem andreev_fill_of_extends {h : BooleanFunction b}
    {ρ : PartialAssignment (Fin (2 ^ b + b * m))} (hext : ρ.Extends (andreevFixTable b m h))
    (w : BitString (2 ^ b + b * m)) :
    andreev b m (ρ.fill w) =
      h (fun j => parity m fun t => ρ.fill w (andreevBlockVar b m j t)) := by
  unfold andreev
  set idx := BitString.equivFin b (fun j => parity m fun t => ρ.fill w (andreevBlockVar b m j t))
  have hfixed : ρ (andreevTableIndex b m idx) = some (h ((BitString.equivFin b).symm idx)) :=
    hext _ _ (andreevFixTable_tableIndex b m h idx)
  rw [PartialAssignment.fill_of_eq_some hfixed, Equiv.symm_apply_apply]

/-! ### Projection from non-eliminated parity blocks -/

/-- Updating a single false bit in an `m`-bit string changes its parity by exclusive-or with the
new value. -/
private theorem parity_update_of_eq_false {y : BitString m} {t₀ : Fin m} (hy : y t₀ = false)
    (v : Bool) :
    parity m (update y t₀ v) = (v ^^ parity m y) := by
  rw [parity, parityOn_eq_xor_erase (mem_univ t₀) (update y t₀ v), update_self,
    parityOn_update_of_notMem (notMem_erase t₀ univ),
    parityOn_eq_xor_erase (mem_univ t₀) y, hy, Bool.false_xor]

/-- **Andreev's projection lemma**: if `ρ` extends `andreevFixTable b m h` and leaves at least one
variable in each of the `b` parity blocks free, then `h` is obtained from `(andreev b m)↾ρ` by
substituting a single literal for one free variable in each block and `false` for all other inputs.
Consequently, `L(h) ≤ L((andreev b m)↾ρ)`. -/
theorem formulaSize_le_of_andreevBlock_nonempty {h : BooleanFunction b}
    {ρ : PartialAssignment (Fin (2 ^ b + b * m))} (hext : ρ.Extends (andreevFixTable b m h))
    (hblocks : ∀ j : Fin b, (ρ.free ∩ andreevBlock b m j).Nonempty) :
    formulaSize h ≤ formulaSize (andreev b m ∘ ρ.fill) := by
  have hpivot (j : Fin b) : ∃ t : Fin m, andreevBlockVar b m j t ∈ ρ.free := by
    obtain ⟨i, hi⟩ := hblocks j
    obtain ⟨hi_free, hi_block⟩ := mem_inter.1 hi
    obtain ⟨t, -, rfl⟩ := mem_image.1 hi_block
    exact ⟨t, hi_free⟩
  choose t_fn ht_fn using hpivot
  set y₀ : Fin b → BitString m :=
    fun j t => ρ.fill (fun _ => false) (andreevBlockVar b m j t)
  set r : Fin b → Bool := fun j => parity m (y₀ j)
  set σ : Fin (2 ^ b + b * m) → Formula signature b :=
    Fin.addCases (fun _ => const false) fun u =>
      let p := finProdFinEquiv.symm u
      if p.2 = t_fn p.1 then
        if r p.1 then (input p.1).not else input p.1
      else
        const false
  obtain ⟨F, hF, hFL⟩ := exists_computes_leafSize_eq (andreev b m ∘ ρ.fill)
  have hσ_leaf (i : Fin (2 ^ b + b * m)) : (σ i).leafSize ≤ 1 := by
    refine Fin.addCases (fun _ => ?_) (fun u => ?_) i
    · simp [σ]
    · simp only [σ, Fin.addCases_right]
      split_ifs <;> simp
  have hbind_computes : (F.bind σ).Computes interpretation h := by
    intro z
    rw [eval_bind, hF, comp_apply, andreev_fill_of_extends hext]
    congr 1
    funext j
    have hblock_eq :
        (fun t => ρ.fill (fun i => (σ i).eval interpretation z) (andreevBlockVar b m j t)) =
          update (y₀ j) (t_fn j) (z j ^^ r j) := by
      funext t
      have hσ_val :
          (σ (andreevBlockVar b m j t)).eval interpretation z =
            if t = t_fn j then (z j ^^ r j) else false := by
        simp only [σ, andreevBlockVar, Fin.addCases_right, Equiv.symm_apply_apply]
        split_ifs with ht hr
        · cases hzj : z j <;> simp [hr, hzj]
        · cases hzj : z j <;> simp [hr, hzj]
        · rfl
      by_cases ht : t = t_fn j
      · subst ht
        have hnone : ρ (andreevBlockVar b m j (t_fn j)) = none :=
          PartialAssignment.mem_free.1 (ht_fn j)
        have hσ_eq : (σ (andreevBlockVar b m j (t_fn j))).eval interpretation z = (z j ^^ r j) := by
          simp [hσ_val]
        rw [PartialAssignment.fill_of_eq_none hnone, hσ_eq, update_self]
      · rw [update_of_ne ht]
        have hσ_false : (σ (andreevBlockVar b m j t)).eval interpretation z = false := by
          simp [hσ_val, ht]
        cases hρ : ρ (andreevBlockVar b m j t) with
        | none =>
          simp [y₀, PartialAssignment.fill, hρ, hσ_false]
        | some c =>
          simp [y₀, PartialAssignment.fill, hρ]
    have hy₀_false : y₀ j (t_fn j) = false :=
      PartialAssignment.fill_of_eq_none (PartialAssignment.mem_free.1 (ht_fn j)) (fun _ => false)
    rw [hblock_eq, parity_update_of_eq_false hy₀_false]
    change ((z j ^^ r j) ^^ r j) = z j
    cases z j <;> cases r j <;> rfl
  have hleaf_le : (F.bind σ).leafSize ≤ formulaSize (andreev b m ∘ ρ.fill) := by
    have := F.leafSize_bind_le hσ_leaf
    omega
  exact (formulaSize_le hbind_computes).trans hleaf_le

/-! ### Andreev's reduction and explicit formula lower bound -/

/-- **Andreev's reduction theorem**: for every `b`-bit Boolean function `h`, `1 ≤ b`, `1 ≤ r ≤ m`,
and `2 * b ≤ 2 ^ r`, the formula size of `andreev b m` satisfies
`(L(h) - 2 * b * r) ^ 2 * m ^ 3 ≤ 4 * L(andreev b m) ^ 2 * r ^ 3`
[Andreev1987], [Jukna, Theorem 6.14][Jukna2012]. -/
theorem formulaSize_sub_sq_mul_pow_three_le_andreev (h : BooleanFunction b) (hb : 1 ≤ b)
    {m r : ℕ} (hr1 : 1 ≤ r) (hrm : r ≤ m) (hbr : 2 * b ≤ 2 ^ r) :
    (formulaSize h - 2 * b * r) ^ 2 * m ^ 3 ≤
      4 * formulaSize (andreev b m) ^ 2 * r ^ 3 := by
  set ρ₀ := andreevFixTable b m h
  set k := b * r
  have hk1 : 1 ≤ k := Nat.mul_pos hb hr1
  have hfree₀ : #ρ₀.free = b * m := card_free_andreevFixTable b m h
  have hk : k ≤ #ρ₀.free := by
    rw [hfree₀]
    exact Nat.mul_le_mul_left b hrm
  set A := {ρ ∈ ρ₀.extensions k | ∀ j : Fin b, (ρ.free ∩ andreevBlock b m j).Nonempty}
  have hAcard : #(ρ₀.extensions k) ≤ 2 * #A :=
    PartialAssignment.card_extensions_le_two_mul_card_filter_forall_nonempty ρ₀ hb hfree₀
      (andreevBlock_subset_free_andreevFixTable b m h) (card_andreevBlock b m) hbr
  obtain ⟨ρ, hρA, hshrink⟩ := exists_mem_formulaSize_sub_sq_le (andreev b m) ρ₀ hk1 hk
    (filter_subset _ _) hAcard
  obtain ⟨hρ_ext, hblocks⟩ := mem_filter.1 hρA
  have hproj : formulaSize h ≤ formulaSize (andreev b m ∘ ρ.fill) :=
    formulaSize_le_of_andreevBlock_nonempty (PartialAssignment.mem_extensions.1 hρ_ext).1 hblocks
  have hle₀ : formulaSize (andreev b m ∘ ρ₀.fill) ≤ formulaSize (andreev b m) :=
    formulaSize_comp_fill_le (andreev b m) ρ₀
  have hsub_le :
      (formulaSize h - 2 * b * r) ^ 2 ≤ (formulaSize (andreev b m ∘ ρ.fill) - 2 * k) ^ 2 := by
    have : 2 * b * r = 2 * k := by ring
    rw [this]
    exact Nat.pow_le_pow_left (Nat.sub_le_sub_right hproj (2 * k)) 2
  have hb3 : 0 < b ^ 3 := by positivity
  refine Nat.le_of_mul_le_mul_right ?_ hb3
  calc (formulaSize h - 2 * b * r) ^ 2 * m ^ 3 * b ^ 3
      = (formulaSize h - 2 * b * r) ^ 2 * (#ρ₀.free) ^ 3 := by
          rw [hfree₀]
          ring
    _ ≤ (formulaSize (andreev b m ∘ ρ.fill) - 2 * k) ^ 2 * (#ρ₀.free) ^ 3 :=
          Nat.mul_le_mul_right _ hsub_le
    _ ≤ 4 * formulaSize (andreev b m ∘ ρ₀.fill) ^ 2 * k ^ 3 := hshrink
    _ ≤ 4 * formulaSize (andreev b m) ^ 2 * k ^ 3 :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hle₀ 2))
    _ = 4 * formulaSize (andreev b m) ^ 2 * r ^ 3 * b ^ 3 := by
          dsimp only [k]
          ring

/-- Specialization of Andreev's reduction to `r = Nat.log 2 b + 2`, for which `2 * b ≤ 2 ^ r`
always holds. -/
private theorem formulaSize_sub_sq_mul_pow_three_le_andreev_log (h : BooleanFunction b) (hb : 1 ≤ b)
    {m : ℕ} (hm : Nat.log 2 b + 2 ≤ m) :
    (formulaSize h - 2 * b * (Nat.log 2 b + 2)) ^ 2 * m ^ 3 ≤
      4 * formulaSize (andreev b m) ^ 2 * (Nat.log 2 b + 2) ^ 3 := by
  have hlt : b < 2 ^ (Nat.log 2 b + 1) := Nat.lt_pow_succ_log_self one_lt_two b
  have hbr : 2 * b ≤ 2 ^ (Nat.log 2 b + 2) := by
    rw [pow_succ']
    omega
  exact formulaSize_sub_sq_mul_pow_three_le_andreev h hb (by omega) hm hbr

/-- **Shannon's counting bound for formula leaf size**: for all sufficiently large `b`, some
Boolean function `h` on `b` bits satisfies `2 ^ b < 3 * b * L(h)`. -/
theorem exists_hard_function_formulaSize :
    ∃ B : ℕ, ∀ b ≥ B, ∃ h : BooleanFunction b, 2 ^ b < 3 * b * formulaSize h := by
  obtain ⟨N, hN⟩ := Shannon.exists_hard_function
  refine ⟨max N 1, fun b hb => ?_⟩
  have hbN : N ≤ b := (le_max_left N 1).trans hb
  have hb1 : 1 ≤ b := (le_max_right N 1).trans hb
  obtain ⟨h, hh⟩ := hN b hbN
  obtain ⟨F, hF, _, hsize⟩ := exists_computes_size_le h
  have hcirc := hh F.toCircuit hF.toCircuit
  rw [Formula.size_toCircuit] at hcirc
  have hb_pos : (0 : ℝ) < (b : ℝ) := by positivity
  have hmul_real : (2 ^ b : ℝ) < (F.size : ℝ) * (b : ℝ) := (div_lt_iff₀ hb_pos).1 hcirc
  have hmul_nat : 2 ^ b < F.size * b := by exact_mod_cast hmul_real
  have hpow : b < 2 ^ b := b.lt_two_pow_self
  have hmax : F.size ≤ 3 * formulaSize h := by
    rcases hsize with ⟨c, rfl⟩ | hle
    · rw [size_const] at hmul_nat
      omega
    · omega
  refine ⟨h, ?_⟩
  nlinarith

/-- For `16 ≤ b`, `12 * b ^ 2 * (b + 2) ≤ 2 ^ b`. -/
private theorem twelve_mul_sq_mul_add_two_le_two_pow {b : ℕ} (hb : 16 ≤ b) :
    12 * b ^ 2 * (b + 2) ≤ 2 ^ b := by
  obtain ⟨d, rfl⟩ : ∃ d, b = d + 16 := ⟨b - 16, by omega⟩
  clear hb
  induction d with
  | zero => decide
  | succ d ih =>
    have hstep :
        12 * (d + 16 + 1) ^ 2 * (d + 16 + 1 + 2) ≤
          2 * (12 * (d + 16) ^ 2 * (d + 16 + 2)) := by
      nlinarith
    calc 12 * (d + 1 + 16) ^ 2 * (d + 1 + 16 + 2)
        = 12 * (d + 16 + 1) ^ 2 * (d + 16 + 1 + 2) := by ring
      _ ≤ 2 * (12 * (d + 16) ^ 2 * (d + 16 + 2)) := hstep
      _ ≤ 2 * 2 ^ (d + 16) := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (d + 1 + 16) := by ring

/-- **Andreev's explicit formula lower bound**: for all sufficiently large `b` and all block sizes
`m ≥ ⌊log₂ b⌋ + 2`, the formula size of `andreev b m` satisfies
`2 ^ (2 * b) * m ^ 3 ≤ 144 * b ^ 2 * (⌊log₂ b⌋ + 2) ^ 3 * L(andreev b m) ^ 2`
[Andreev1987], [Jukna, Theorem 6.14][Jukna2012]. -/
theorem pow_two_mul_pow_three_le_formulaSize_andreev_sq :
    ∃ B : ℕ, ∀ b ≥ B, ∀ m ≥ Nat.log 2 b + 2,
      2 ^ (2 * b) * m ^ 3 ≤
        144 * b ^ 2 * (Nat.log 2 b + 2) ^ 3 * formulaSize (andreev b m) ^ 2 := by
  obtain ⟨B₀, hB₀⟩ := exists_hard_function_formulaSize
  refine ⟨max B₀ 16, fun b hb m hm => ?_⟩
  have hb₀ : B₀ ≤ b := (le_max_left B₀ 16).trans hb
  have hb16 : 16 ≤ b := (le_max_right B₀ 16).trans hb
  obtain ⟨h, hh⟩ := hB₀ b hb₀
  set r := Nat.log 2 b + 2
  have handreev := formulaSize_sub_sq_mul_pow_three_le_andreev_log h (by omega) hm
  have hlog : Nat.log 2 b ≤ b := Nat.log_le_self 2 b
  have hexp : 12 * b ^ 2 * r ≤ 2 ^ b := by
    calc 12 * b ^ 2 * r
        ≤ 12 * b ^ 2 * (b + 2) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ 2 ^ b := twelve_mul_sq_mul_add_two_le_two_pow hb16
  have hhalf : 2 ^ b ≤ 6 * b * (formulaSize h - 2 * b * r) := by
    rw [Nat.mul_sub_left_distrib]
    have h1 : 6 * b * formulaSize h = 2 * (3 * b * formulaSize h) := by ring
    have h2 : 6 * b * (2 * b * r) = 12 * b ^ 2 * r := by ring
    rw [h1, h2]
    omega
  have hsq : (2 ^ b) ^ 2 ≤ (6 * b * (formulaSize h - 2 * b * r)) ^ 2 :=
    Nat.pow_le_pow_left hhalf 2
  calc 2 ^ (2 * b) * m ^ 3
      = (2 ^ b) ^ 2 * m ^ 3 := by rw [← pow_mul, mul_comm 2 b]
    _ ≤ (6 * b * (formulaSize h - 2 * b * r)) ^ 2 * m ^ 3 := Nat.mul_le_mul_right _ hsq
    _ = 36 * b ^ 2 * ((formulaSize h - 2 * b * r) ^ 2 * m ^ 3) := by ring
    _ ≤ 36 * b ^ 2 * (4 * formulaSize (andreev b m) ^ 2 * r ^ 3) :=
        Nat.mul_le_mul_left _ handreev
    _ = 144 * b ^ 2 * r ^ 3 * formulaSize (andreev b m) ^ 2 := by ring

/-- **Andreev's `n ^ (5 / 2 - o(1))` lower bound** at block size `m = 2 ^ b` (input length
`n = (b + 1) * 2 ^ b`): for all sufficiently large `b`,
`2 ^ (5 * b) ≤ 144 * b ^ 2 * (⌊log₂ b⌋ + 2) ^ 3 * L(andreev b (2 ^ b)) ^ 2`. -/
theorem two_pow_five_mul_le_formulaSize_andreev_sq :
    ∃ B : ℕ, ∀ b ≥ B,
      2 ^ (5 * b) ≤
        144 * b ^ 2 * (Nat.log 2 b + 2) ^ 3 * formulaSize (andreev b (2 ^ b)) ^ 2 := by
  obtain ⟨B, hB⟩ := pow_two_mul_pow_three_le_formulaSize_andreev_sq
  refine ⟨max B 16, fun b hb => ?_⟩
  have hbB : B ≤ b := (le_max_left B 16).trans hb
  have hb16 : 16 ≤ b := (le_max_right B 16).trans hb
  have hlog : Nat.log 2 b ≤ b := Nat.log_le_self 2 b
  have hexp := twelve_mul_sq_mul_add_two_le_two_pow hb16
  have hm : Nat.log 2 b + 2 ≤ 2 ^ b := by nlinarith
  have h := hB b hbB (2 ^ b) hm
  have hpow : 2 ^ (5 * b) = 2 ^ (2 * b) * (2 ^ b) ^ 3 := by
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  rw [hpow]
  exact h

end Cslib.Circuits.Boolean
