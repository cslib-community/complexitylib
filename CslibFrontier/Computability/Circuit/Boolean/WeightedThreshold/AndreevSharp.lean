/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.WeightedThreshold.AndreevSharpScore
public import CslibFrontier.Computability.Circuit.Boolean.WeightedThreshold.DepthTwoInputs
public import CslibFrontier.Computability.Circuit.Boolean.WeightedThreshold.Andreev
import Mathlib.Tactic.LinearCombination

/-!
# Depth-two threshold circuits for Andreev's function with `(5/16 + o(1)) n ^ 2` gates

For all `b, m`, `andreevSharpCircuit b m` is an explicit depth-two weighted threshold circuit
computing Andreev's function `andreev b m` on all `n = 2 ^ b + b m` inputs, in the model of
`depthTwoInputs`: a top gate reading the bottom gates and the inputs. With `N = 2 ^ b` and
`α = ⌊(m - 1) / 2⌋` it has exactly
`N (N - 1) / 2 + b N (m + α) / 2 + 2 (N - 1) + 2 α b + 3 b m + ⌈b m / 2⌉`
bottom gates and one top gate, improving the `(3/4) n ^ 2` circuit of `WeightedThreshold.Andreev`.
The mathematics is original, AI-assisted work under
[#4640](https://github.com/cslib-community/cslib-frontier/issues/4640). Statement numbers and
labels ("preprint, Theorem 5", proof in Appendix A) refer to the author's unpublished draft
(C. Reitwiessner, *Depth-Two Threshold Circuits for Andreev's Function*), which is not publicly
accessible; the correspondence with it is not verifiable by third parties.

The top gate tests the sign of the score `P` of `AndreevSharpScore`. Its non-affine terms are
realized by six families of bottom gates (`AndreevSharpIndex`):
* the ridge `r_S(2 W_S + t_S)`, by the odd thresholds `[2 W_S + t_S ≥ 2 j + 1]` only, for every
  nonempty `S` (`sum_ridge_steps`);
* `(N / 2) w²` and `(N / 2) ∑ s_i²`, by unit staircases;
* `x_{e_i} s_i`, by the gates `[s_i + B x_{e_i} ≥ B + ℓ]` with `B = n + 2`;
* `x_0 [p = 0] = x_0 - x_0 σ + (4 / N) ∑_S x_0 ⌊t_S / 2⌋` (`four_mul_sum_half`), by the gates
  `[t_S + B x_0 ≥ B + 2 j]` and the odd-level gates `[σ + B x_0 ≥ B + 2 j + 1]`; the even levels
  of `x_0 σ` are the gates of `S = univ`, as in the preprint.

Every bottom gate has integer weights and thresholds and gives each address bit weight `0` or
`1`, constant on each block, so it is sign-coherent (`isSignCoherent_andreevSharpBottomOp`). The
top weights and threshold are integers. With `n = 2 ^ b + b m`, the bottom weights and thresholds
have absolute value at most `2 n`, the top weights on bottom gates at most `2 (n + 1) (n + 4)`,
and the top weights on inputs at most `(2 n ^ 3 + 54 n (n + 1)) / 27`; only the weights
`2 N (α ^ 2 - 1)` on the weight-one table addresses are of cubic order, and they are at most
`O(n ^ 3 / b ^ 2)`.

## Correspondence with the unpublished draft (not publicly verifiable)

* Theorem 5, gate count `eq:bestcount`: `card_andreevSharpIndex`, `size_andreevSharpCircuit`.
* Theorem 5, exact computation: `computes_andreevSharpCircuit`.
* Theorem 5, size at exact balance: `size_andreevSharpCircuit_of_balanced`, the exact identity
  `16 · size = 5 n² - 4 n log₂(n/2) + 48 n - 32 log₂(n/2) - 16`.
* Theorem 5, `m = ⌊N / b⌋`: `size_andreevSharpCircuit_floor_le`,
  `16 · size ≤ 5 (n + b)² + 52 (n + b) + 24` with `b ≤ log₂ n` (`le_log_two_andreev_length`).
* Theorem 5, integer weights and sign coherence (Section 5): `andreevSharpCircuit_int_weights`,
  `weight_andreevSharpBottomOp_blockVar`, `isSignCoherent_andreevSharpBottomOp`, and for the
  circuit's program gates `isSignCoherent_inputWeight_andreevSharpCircuit`.
* Theorem 5, weights polynomial in `n`, and the end of the proof in Appendix A (bottom
  coefficients and thresholds `O(n)`, top coefficients `O(n ^ 3)`), with `n = 2 ^ b + b m`:
  `abs_weight_andreevSharpBottomOp_le` and `abs_threshold_andreevSharpBottomOp_le` (`≤ 2 n`, also
  as `abs_inputWeight_andreevSharpCircuit_le`); `abs_andreevSharpTopWeight_le`
  (`≤ 2 (n + 1) (n + 4)` on bottom gates); `abs_andreevSharpTopInput_le`
  (`27 |v| ≤ 2 n ^ 3 + 54 n (n + 1)` on inputs) and its sharper form
  `sq_mul_abs_andreevSharpTopInput_le` (`27 b ^ 2 |v| ≤ 2 n ^ 3 + 54 b ^ 2 n (n + 1)`); and for
  every weight and threshold of every gate of the circuit `abs_weight_andreevSharpCircuit_le` and
  `abs_threshold_andreevSharpCircuit_le` (`27 |w| ≤ 2 n ^ 3 + 54 (n + 1) (n + 4)`). The constants
  are derived here; the preprint gives only the orders.

## References

* [cslib-frontier#4640](https://github.com/cslib-community/cslib-frontier/issues/4640):
  original AI-assisted work, following C. Reitwiessner, *Depth-Two Threshold Circuits for
  Andreev's Function* (unpublished draft, not publicly accessible), Theorem 5 and Appendix A.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.WeightedThreshold

open BitString Finset

variable {b m : ℕ}

/-! ### Linear forms on Andreev inputs that read blocks through their sums -/

/-- The block counts `s_j = |a_j|` of an Andreev input. -/
def andreevBlockCount (b m : ℕ) (w : BitString (2 ^ b + b * m)) (j : Fin b) : ℕ :=
  ∑ t : Fin m, (w (andreevBlockVar b m j t)).toNat

/-- The block parities of an Andreev input are the parities of its block counts. -/
theorem andreevParities_eq_blockParities (w : BitString (2 ^ b + b * m)) :
    andreevParities b m w = blockParities b (andreevBlockCount b m w) := by
  funext j
  have h : #{t ∈ univ | w (andreevBlockVar b m j t) = true} = andreevBlockCount b m w j := by
    rw [card_filter, andreevBlockCount]
    exact sum_congr rfl fun t _ => by cases w (andreevBlockVar b m j t) <;> rfl
  simp only [andreevParities, parity, parityOn, blockParities, h]

/-- Andreev's function reads the table at the parities of the block counts. -/
theorem andreev_eq_andreevTable (w : BitString (2 ^ b + b * m)) :
    andreev b m w = andreevTable b m w (blockParities b (andreevBlockCount b m w)) := by
  rw [andreev_eq_table_parities, andreevParities_eq_blockParities]

/-- Every block count is at most `m`. -/
theorem andreevBlockCount_le (w : BitString (2 ^ b + b * m)) (j : Fin b) :
    andreevBlockCount b m w j ≤ m :=
  (sum_le_sum (g := fun _ => 1) fun t _ => Bool.toNat_le _).trans (by simp)

/-- The integer weight vector on Andreev inputs with coefficient `a c` on table bit `c` and
coefficient `β j` on every bit of block `j`. -/
def andreevFormWeight (b m : ℕ) (a : BitString b → ℤ) (β : Fin b → ℤ) :
    Fin (2 ^ b + b * m) → ℤ :=
  Fin.addCases (fun idx => a ((BitString.equivFin b).symm idx))
    (fun u => β (finProdFinEquiv.symm u).1)

/-- The weight `andreevFormWeight` on a block bit is the block coefficient. -/
@[simp]
theorem andreevFormWeight_blockVar (a : BitString b → ℤ) (β : Fin b → ℤ) (j : Fin b)
    (t : Fin m) : andreevFormWeight b m a β (andreevBlockVar b m j t) = β j := by
  simp only [andreevFormWeight, andreevBlockVar, Fin.addCases_right, Equiv.symm_apply_apply]

/-- **The form of `andreevFormWeight`**: `∑_c a c x_c + ∑_j β j s_j`. -/
theorem sum_andreevFormWeight_mul (a : BitString b → ℤ) (β : Fin b → ℤ)
    (w : BitString (2 ^ b + b * m)) :
    ∑ i, andreevFormWeight b m a β i * (w i).toNat =
      ∑ c, a c * (andreevTable b m w c).toNat + ∑ j, β j * andreevBlockCount b m w j := by
  rw [Fin.sum_univ_add]
  congr 1
  · simp only [andreevFormWeight, Fin.addCases_left]
    rw [← (BitString.equivFin b).sum_comp]
    simp [andreevTable, andreevTableIndex]
  · simp only [andreevFormWeight, Fin.addCases_right]
    rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
    simp only [Equiv.symm_apply_apply, andreevBlockCount, Nat.cast_sum, mul_sum]
    rfl

/-- `andreevFormWeight` is sign-coherent for Andreev's blocks when every block coefficient is
`0` or `1`. -/
theorem isSignCoherent_andreevFormWeight (a : BitString b → ℤ) (β : Fin b → ℤ)
    (hβ : ∀ j, β j = 0 ∨ β j = 1) :
    IsSignCoherent (andreevBlockVar b m) fun i => (andreevFormWeight b m a β i : ℝ) :=
  IsSignCoherent.of_mem_zero_one fun j t => by
    rcases hβ j with h | h <;> simp [h]

/-- **Gates on integer forms**: the gate with weights `andreevFormWeight b m a β` and threshold
`θ`, reading the inputs in order, compares `θ` with `∑_c a c x_c + ∑_j β j s_j`. -/
theorem interpretation_andreevFormWeight (a : BitString b → ℤ) (β : Fin b → ℤ) (θ : ℤ)
    (w : BitString (2 ^ b + b * m)) :
    interpretation (⟨2 ^ b + b * m, fun i => (andreevFormWeight b m a β i : ℝ), (θ : ℝ)⟩ : Op)
        (fun i => w (id i)) =
      decide (θ ≤ ∑ c, a c * (andreevTable b m w c).toNat +
        ∑ j, β j * andreevBlockCount b m w j) := by
  unfold interpretation
  dsimp only [id]
  rw [← sum_andreevFormWeight_mul]
  exact decide_eq_decide.mpr (by rw [← @Int.cast_le ℝ]; push_cast; rfl)

/-! ### Staircases -/

/-- Unit staircase: `∑_{j < L} [j + 1 ≤ q] = q` for `q ≤ L`. -/
theorem sum_decide_succ_le {q L : ℕ} (h : q ≤ L) :
    ∑ j : Fin L, ((decide ((j : ℤ) + 1 ≤ q)).toNat : ℤ) = q := by
  have := sum_sub_mul_decide_le (fun v : ℤ => v) (ℓ := 0) (u := q) (L := L) (by positivity)
    (by simpa using h)
  simpa using this

/-- Unit staircase with natural-number guards. -/
theorem sum_decide_succ_le_nat {q L : ℕ} (h : q ≤ L) :
    ∑ j : Fin L, (decide (j.1 + 1 ≤ q)).toNat = q := by
  have h' := sum_decide_succ_le h
  have hc : ∑ j : Fin L, ((decide ((j : ℤ) + 1 ≤ q)).toNat : ℤ) =
      ((∑ j : Fin L, (decide (j.1 + 1 ≤ q)).toNat : ℕ) : ℤ) := by
    push_cast
    exact sum_congr rfl fun j _ => by
      rw [decide_eq_decide.mpr (show (j : ℤ) + 1 ≤ q ↔ j.1 + 1 ≤ q by omega)]
  exact_mod_cast hc ▸ h'

/-- Square staircase: `∑_{j < L} (2 j + 1) [j + 1 ≤ u] = u ^ 2` for `u ≤ L`. -/
theorem sum_square_steps {u L : ℕ} (h : u ≤ L) :
    ∑ j : Fin L, (2 * (j : ℤ) + 1) * (decide ((j : ℤ) + 1 ≤ u)).toNat = (u : ℤ) ^ 2 := by
  have := sum_sub_mul_decide_le (fun v : ℤ => v ^ 2) (ℓ := 0) (u := u) (L := L) (by positivity)
    (by simpa using h)
  simp only [zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at this
  rw [← this]
  exact sum_congr rfl fun j _ => by ring_nf

/-- **Odd-threshold ridge staircase** (preprint, Appendix A): if `⌈u / 2⌉ ≤ L`, then
`r_κ(u) = ∑_{j < L} (κ - 8 (2 j + 1)) [2 j + 1 ≤ u]`; the ridge only changes at odd
thresholds. -/
theorem sum_ridge_steps (κ : ℤ) {u L : ℕ} (h : (u + 1) / 2 ≤ L) :
    ∑ j : Fin L, (κ - 8 * (2 * (j : ℤ) + 1)) *
      (decide (2 * (j : ℤ) + 1 ≤ u)).toNat = andreevRidge κ u := by
  have hq : (0 : ℤ) ≤ ((u : ℤ) + 1) / 2 := by omega
  have hq' : ((u : ℤ) + 1) / 2 ≤ 0 + (L : ℤ) := by omega
  have := sum_sub_mul_decide_le (fun v : ℤ => -8 * v ^ 2 + κ * v) hq hq'
  rw [andreevRidge, ← this]
  simp only [zero_add, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero]
  refine sum_congr rfl fun j _ => ?_
  have hd : decide ((j : ℤ) + 1 ≤ ((u : ℤ) + 1) / 2) = decide (2 * (j : ℤ) + 1 ≤ u) :=
    decide_eq_decide.mpr (by omega)
  rw [hd]
  ring

/-- **Gated staircase count.** Let `t < B` and `q ≤ L`, and let the levels `lev j ≥ 1` satisfy
`lev j ≤ t ↔ j + 1 ≤ q`. Then the gates `[B + lev j ≤ t + B x]`, `j < L`, count `x · q`: they are
all off when `x = false`, and when `x = true` exactly the first `q` of them are on. -/
theorem sum_decide_big_le_add_mul {B t : ℤ} (x : Bool) {q L : ℕ} (lev : ℕ → ℤ)
    (hlev : ∀ j, 1 ≤ lev j) (htB : t < B) (hq : q ≤ L) (hiff : ∀ j, lev j ≤ t ↔ j + 1 ≤ q) :
    ∑ j : Fin L, ((decide (B + lev j ≤ t + B * x.toNat)).toNat : ℝ) = x.toNat * q := by
  have hstep (j : Fin L) :
      decide (B + lev j ≤ t + B * x.toNat) = (x && decide (j.1 + 1 ≤ q)) := by
    have h1 := hiff j
    have h2 := hlev j
    cases x
    · simp only [Bool.toNat_false, Nat.cast_zero, mul_zero, add_zero, Bool.false_and,
        decide_eq_false_iff_not, not_le]
      omega
    · simp only [Bool.toNat_true, Nat.cast_one, mul_one, Bool.true_and]
      exact decide_eq_decide.mpr (by omega)
  simp only [hstep]
  cases x
  · simp
  · have h : ∑ j : Fin L, ((decide (j.1 + 1 ≤ q)).toNat : ℝ) = q := by
      exact_mod_cast sum_decide_succ_le_nat hq
    simpa using h

/-! ### The bottom gates -/

section Gates

variable (b m : ℕ)

/-- The number of odd thresholds of the ridge staircase of a nonempty `S`:
`⌈(N + 2 α |S| + |S| m) / 2⌉`, and `0` for `S = ∅`. -/
def andreevSharpRidgeLen (S : Finset (Fin b)) : ℕ :=
  if S = ∅ then 0 else (2 ^ b + (2 * andreevSharpAmp m + m) * #S + 1) / 2

/-- Index type of the bottom gates of the sharper circuit, in six families:
the odd-threshold ridge gates `[2 W_S + t_S ≥ 2 j + 1]`; the load gates `[w ≥ θ]`; the block
square gates `[s_i ≥ ℓ]`; the product gates `[s_i + B x_{e_i} ≥ B + ℓ]`; the odd zero-address
gates `[σ + B x_0 ≥ B + 2 j + 1]`; and the half gates `[t_S + B x_0 ≥ B + 2 j]`, whose instances
for `S = univ` are also the even zero-address gates. -/
abbrev AndreevSharpIndex : Type :=
  (Σ S : Finset (Fin b), Fin (andreevSharpRidgeLen b m S)) ⊕
    (Fin (andreevSharpRange b m) ⊕ ((Fin b × Fin m) ⊕ ((Fin b × Fin m) ⊕
      (Fin ((b * m + 1) / 2) ⊕ (Σ S : Finset (Fin b), Fin (#S * m / 2))))))

/-- The large weight `B = n + 2` switching gates on the table bits `x_0` and `x_{e_i}`. -/
def andreevSharpBig : ℤ :=
  2 ^ b + b * m + 2

/-- Table coefficients of the bottom gates. -/
def andreevSharpTable : AndreevSharpIndex b m → BitString b → ℤ
  | .inl ⟨S, _⟩ => fun c => 2 * andreevSharpMult b m c * (parityOn S c).toNat
  | .inr (.inl _) => fun c => 2 * andreevSharpMult b m c
  | .inr (.inr (.inl _)) => 0
  | .inr (.inr (.inr (.inl (i, _)))) => fun c =>
    if c = Pi.single i true then andreevSharpBig b m else 0
  | .inr (.inr (.inr (.inr _))) => fun c => if c = 0 then andreevSharpBig b m else 0

/-- Block coefficients of the bottom gates; all lie in `{0, 1}`. -/
def andreevSharpBlock : AndreevSharpIndex b m → Fin b → ℤ
  | .inl ⟨S, _⟩ => fun j => if j ∈ S then 1 else 0
  | .inr (.inl _) => 1
  | .inr (.inr (.inl (i, _))) => fun j => if j = i then 1 else 0
  | .inr (.inr (.inr (.inl (i, _)))) => fun j => if j = i then 1 else 0
  | .inr (.inr (.inr (.inr (.inl _)))) => 1
  | .inr (.inr (.inr (.inr (.inr ⟨S, _⟩)))) => fun j => if j ∈ S then 1 else 0

/-- Thresholds of the bottom gates. -/
def andreevSharpThreshold : AndreevSharpIndex b m → ℤ
  | .inl ⟨_, j⟩ => 2 * j + 1
  | .inr (.inl θ) => θ + 1
  | .inr (.inr (.inl (_, ℓ))) => ℓ + 1
  | .inr (.inr (.inr (.inl (_, ℓ)))) => andreevSharpBig b m + ℓ + 1
  | .inr (.inr (.inr (.inr (.inl j)))) => andreevSharpBig b m + 2 * j + 1
  | .inr (.inr (.inr (.inr (.inr ⟨_, j⟩)))) => andreevSharpBig b m + 2 * (j + 1)

/-- Top weights on the bottom gates: minus the coefficients of the gates in the score. -/
def andreevSharpTopWeight : AndreevSharpIndex b m → ℤ
  | .inl ⟨S, j⟩ => 8 * (2 * j + 1) - andreevSharpKappa b m S
  | .inr (.inl θ) => -(2 ^ (b - 1) * (2 * θ + 1))
  | .inr (.inr (.inl (_, ℓ))) => -(2 ^ (b - 1) * (2 * ℓ + 1))
  | .inr (.inr (.inr (.inl _))) => -(2 * 2 ^ b * (1 + andreevSharpAmp m))
  | .inr (.inr (.inr (.inr (.inl _)))) => -((andreevSharpRange b m + 4) * 2 ^ b)
  | .inr (.inr (.inr (.inr (.inr ⟨S, _⟩)))) =>
    4 * (andreevSharpRange b m + 4) - if S = univ then (andreevSharpRange b m + 4) * 2 ^ b else 0

/-- Top table coefficients: minus the affine table part `4 N z - 2 N (α² + 1) E - N (R + 4) x_0`
of the score. -/
def andreevSharpTopTable (c : BitString b) : ℤ :=
  (if c = 0 then ((andreevSharpRange b m : ℤ) + 4) * 2 ^ b else -(4 * 2 ^ b)) +
    if IsSingle c then 2 * 2 ^ b * ((andreevSharpAmp m : ℤ) ^ 2 + 1) else 0

/-- Top block coefficient: minus the affine block part `-2 α N σ` of the score. -/
def andreevSharpTopBlock : ℤ :=
  2 * (andreevSharpAmp m : ℤ) * 2 ^ b

variable {b m}

/-- The integer form read by a bottom gate. -/
def andreevSharpForm (idx : AndreevSharpIndex b m) (x : BitString b → Bool) (s : Fin b → ℕ) :
    ℤ :=
  ∑ c, andreevSharpTable b m idx c * (x c).toNat + ∑ j, andreevSharpBlock b m idx j * s j

/-- The value of a bottom gate. -/
def andreevSharpGate (idx : AndreevSharpIndex b m) (x : BitString b → Bool) (s : Fin b → ℕ) :
    Bool :=
  decide (andreevSharpThreshold b m idx ≤ andreevSharpForm idx x s)

variable (b m) in
/-- The weighted sum read by the top gate. -/
noncomputable def andreevSharpTopSum (x : BitString b → Bool) (s : Fin b → ℕ) : ℝ :=
  ∑ idx, (andreevSharpTopWeight b m idx : ℝ) * (andreevSharpGate idx x s).toNat +
    ((∑ c, andreevSharpTopTable b m c * (x c).toNat +
      ∑ j, andreevSharpTopBlock b m * s j : ℤ) : ℝ)

end Gates

/-! ### Values of the bottom forms -/

section Forms

variable {b m : ℕ} (x : BitString b → Bool) (s : Fin b → ℕ)

private theorem sum_ite_mem_mul (S : Finset (Fin b)) :
    ∑ j, (if j ∈ S then (1 : ℤ) else 0) * s j = ∑ j ∈ S, (s j : ℤ) := by
  simp [sum_ite_mem]

theorem andreevSharpForm_ridge (S : Finset (Fin b)) (j : Fin (andreevSharpRidgeLen b m S)) :
    andreevSharpForm (.inl ⟨S, j⟩) x s =
      ((2 * andreevSharpW b m x S + ∑ i ∈ S, s i : ℕ) : ℤ) := by
  simp only [andreevSharpForm, andreevSharpTable, andreevSharpBlock, sum_ite_mem_mul,
    andreevSharpW]
  push_cast
  rw [mul_sum]
  congr 1
  exact sum_congr rfl fun c _ => by ring

theorem andreevSharpForm_load (θ : Fin (andreevSharpRange b m)) :
    andreevSharpForm (m := m) (.inr (.inl θ)) x s = andreevSharpLoad b m x s := by
  simp only [andreevSharpForm, andreevSharpTable, andreevSharpBlock, andreevSharpLoad,
    Pi.one_apply, one_mul]
  push_cast
  rw [mul_sum]
  congr 1
  exact sum_congr rfl fun c _ => by ring

theorem andreevSharpForm_square (i : Fin b) (ℓ : Fin m) :
    andreevSharpForm (.inr (.inr (.inl (i, ℓ)))) x s = s i := by
  simp [andreevSharpForm, andreevSharpTable, andreevSharpBlock]

theorem andreevSharpForm_product (i : Fin b) (ℓ : Fin m) :
    andreevSharpForm (.inr (.inr (.inr (.inl (i, ℓ))))) x s =
      s i + andreevSharpBig b m * (x (Pi.single i true)).toNat := by
  simp only [andreevSharpForm, andreevSharpTable, andreevSharpBlock, ite_mul,
    zero_mul, one_mul, sum_ite_eq', mem_univ, ite_true]
  ring

theorem andreevSharpForm_zero (j : Fin ((b * m + 1) / 2)) :
    andreevSharpForm (.inr (.inr (.inr (.inr (.inl j))))) x s =
      ∑ i, (s i : ℤ) + andreevSharpBig b m * (x 0).toNat := by
  simp only [andreevSharpForm, andreevSharpTable, andreevSharpBlock, Pi.one_apply, one_mul,
    ite_mul, zero_mul, sum_ite_eq', mem_univ, ite_true]
  ring

theorem andreevSharpForm_half (S : Finset (Fin b)) (j : Fin (#S * m / 2)) :
    andreevSharpForm (.inr (.inr (.inr (.inr (.inr ⟨S, j⟩))))) x s =
      ∑ i ∈ S, (s i : ℤ) + andreevSharpBig b m * (x 0).toNat := by
  simp only [andreevSharpForm, andreevSharpTable, andreevSharpBlock, ite_mul,
    zero_mul, one_mul, sum_ite_eq', mem_univ, ite_true, sum_ite_mem, univ_inter]
  ring

end Forms

/-! ### The top sum equals `2 N - P` -/

section TopSum

variable {b m : ℕ}

/-- For nonempty `S`, `2 W_S ≤ N + 2 α |S|`: half of the nonzero addresses have `S · c` odd. -/
theorem two_mul_andreevSharpW_le (x : BitString b → Bool) {S : Finset (Fin b)} (hS : S ≠ ∅) :
    2 * andreevSharpW b m x S ≤ 2 ^ b + 2 * andreevSharpAmp m * #S := by
  have hpar : 2 * ∑ c : BitString b, ((parityOn S c).toNat : ℝ) = 2 ^ b := by
    rw [mul_sum]
    simp_rw [two_mul_toNat_parityOn]
    rw [sum_sub_distrib, sum_chi]
    simp only [hS, ite_false]
    simp
  have h1 : (andreevSharpW b m x S : ℝ) ≤
      ∑ c, (andreevSharpMult b m c : ℝ) * (parityOn S c).toNat := by
    unfold andreevSharpW
    push_cast
    refine sum_le_sum fun c _ => ?_
    cases x c
    · simp only [Bool.toNat_false, Nat.cast_zero, mul_zero, zero_mul]
      positivity
    · simp
  have h2 : ∑ c, (andreevSharpMult b m c : ℝ) * (parityOn S c).toNat =
      ∑ c : BitString b, ((parityOn S c).toNat : ℝ) + andreevSharpAmp m * #S := by
    simp only [cast_andreevSharpMult, add_mul, sum_add_distrib, ite_mul, zero_mul, one_mul,
      mul_assoc, ← mul_sum]
    have h0 : ∑ c : BitString b, (if c = 0 then 0 else ((parityOn S c).toNat : ℝ)) =
        ∑ c : BitString b, ((parityOn S c).toNat : ℝ) := by
      refine sum_congr rfl fun c _ => ?_
      split_ifs with hc
      · subst hc
        simp [parityOn]
      · rfl
    have hε := oddForm_onSingles (1 : Fin b → ℝ) S
    simp only [oddForm, Pi.one_apply, sum_const, nsmul_eq_mul, mul_one] at hε
    rw [h0, hε]
  have : (2 * andreevSharpW b m x S : ℝ) ≤ 2 ^ b + 2 * andreevSharpAmp m * #S := by
    linarith
  exact_mod_cast this

/-- The ridge family sums to `-∑_S r_S(2 W_S + t_S)`. -/
theorem sum_topWeight_ridge (x : BitString b → Bool) (s : Fin b → ℕ) (hs : ∀ i, s i ≤ m) :
    ∑ S, ∑ j : Fin (andreevSharpRidgeLen b m S),
      (andreevSharpTopWeight b m (.inl ⟨S, j⟩) : ℝ) * (andreevSharpGate (.inl ⟨S, j⟩) x s).toNat =
      -∑ S, (andreevRidge (andreevSharpKappa b m S)
        (2 * andreevSharpW b m x S + ∑ i ∈ S, s i) : ℝ) := by
  rw [← sum_neg_distrib]
  refine sum_congr rfl fun S _ => ?_
  set u := 2 * andreevSharpW b m x S + ∑ i ∈ S, s i with hu
  have hlen : (u + 1) / 2 ≤ andreevSharpRidgeLen b m S := by
    rw [andreevSharpRidgeLen]
    split_ifs with hS
    · subst hS
      simp [hu, andreevSharpW, parityOn]
    · have hW := two_mul_andreevSharpW_le (m := m) x hS
      have ht : ∑ i ∈ S, s i ≤ #S * m := (sum_le_sum fun i _ => hs i).trans (by simp)
      have : u ≤ 2 ^ b + (2 * andreevSharpAmp m + m) * #S := by
        rw [hu]; nlinarith
      omega
  have h := sum_ridge_steps (andreevSharpKappa b m S) hlen
  have hcast : ((2 * andreevSharpW b m x S : ℤ) + ((∑ i ∈ S, s i : ℕ) : ℤ)) = (u : ℤ) := by
    rw [hu]; push_cast; ring
  rw [hcast, ← h]
  push_cast
  rw [← sum_neg_distrib]
  refine sum_congr rfl fun j _ => ?_
  simp only [andreevSharpTopWeight, andreevSharpGate, andreevSharpThreshold,
    andreevSharpForm_ridge, ← hu]
  push_cast
  ring

/-- The load family sums to `-2 ^ (b - 1) w ^ 2`. -/
theorem sum_topWeight_load (x : BitString b → Bool) (s : Fin b → ℕ) (hs : ∀ i, s i ≤ m) :
    ∑ θ : Fin (andreevSharpRange b m),
      (andreevSharpTopWeight b m (.inr (.inl θ)) : ℝ) *
        (andreevSharpGate (.inr (.inl θ)) x s).toNat =
      -(2 ^ (b - 1) * (andreevSharpLoad b m x s : ℝ) ^ 2) := by
  have h := sum_square_steps (andreevSharpLoad_le x s hs)
  have h' := congrArg (fun z : ℤ => -(2 ^ (b - 1) * (z : ℝ))) h
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_add, Int.cast_ofNat, Int.cast_natCast,
    Int.cast_one, Int.cast_pow, mul_sum, ← sum_neg_distrib] at h'
  rw [← h']
  refine sum_congr rfl fun θ _ => ?_
  simp only [andreevSharpTopWeight, andreevSharpGate, andreevSharpThreshold,
    andreevSharpForm_load]
  push_cast
  ring

/-- The square family sums to `-2 ^ (b - 1) ∑_i s_i ^ 2`. -/
theorem sum_topWeight_square (x : BitString b → Bool) (s : Fin b → ℕ) (hs : ∀ i, s i ≤ m) :
    ∑ p : Fin b × Fin m,
      (andreevSharpTopWeight b m (.inr (.inr (.inl p))) : ℝ) *
        (andreevSharpGate (.inr (.inr (.inl p))) x s).toNat =
      -(2 ^ (b - 1) * ∑ i, (s i : ℝ) ^ 2) := by
  rw [Fintype.sum_prod_type, mul_sum, ← sum_neg_distrib]
  refine sum_congr rfl fun i _ => ?_
  have h := sum_square_steps (hs i)
  have h' := congrArg (fun z : ℤ => -(2 ^ (b - 1) * (z : ℝ))) h
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_add, Int.cast_ofNat, Int.cast_natCast,
    Int.cast_one, Int.cast_pow, mul_sum, ← sum_neg_distrib] at h'
  rw [← h']
  refine sum_congr rfl fun ℓ _ => ?_
  simp only [andreevSharpTopWeight, andreevSharpGate, andreevSharpThreshold,
    andreevSharpForm_square]
  push_cast
  ring

private theorem big_gt (s : Fin b → ℕ) (hs : ∀ i, s i ≤ m) (S : Finset (Fin b)) :
    ∑ i ∈ S, (s i : ℤ) < andreevSharpBig b m := by
  have h1 : ∑ i ∈ S, s i ≤ ∑ i, s i := sum_le_sum_of_subset (subset_univ S)
  have h2 : ∑ i, s i ≤ b * m := (sum_le_sum fun i _ => hs i).trans (by simp)
  have : ((∑ i ∈ S, s i : ℕ) : ℤ) < 2 ^ b + b * m + 2 := by
    have : (0 : ℤ) < 2 ^ b := by positivity
    push_cast at h1 h2 ⊢
    linarith
  simpa [andreevSharpBig] using this

/-- The product family sums to `-2 N (1 + α) ∑_i x_{e_i} s_i`. -/
theorem sum_topWeight_product (x : BitString b → Bool) (s : Fin b → ℕ) (hs : ∀ i, s i ≤ m) :
    ∑ p : Fin b × Fin m,
      (andreevSharpTopWeight b m (.inr (.inr (.inr (.inl p)))) : ℝ) *
        (andreevSharpGate (.inr (.inr (.inr (.inl p)))) x s).toNat =
      -(2 * 2 ^ b * (1 + andreevSharpAmp m) *
        ∑ i, ((x (Pi.single i true)).toNat : ℝ) * s i) := by
  rw [Fintype.sum_prod_type, mul_sum, ← sum_neg_distrib]
  refine sum_congr rfl fun i _ => ?_
  have hg (ℓ : Fin m) : (andreevSharpGate (.inr (.inr (.inr (.inl (i, ℓ))))) x s).toNat =
      (decide (andreevSharpBig b m + ((ℓ.1 : ℤ) + 1) ≤
        (s i : ℤ) + andreevSharpBig b m * (x (Pi.single i true)).toNat)).toNat := by
    simp only [andreevSharpGate, andreevSharpThreshold, andreevSharpForm_product, add_assoc]
  have hc : ∑ ℓ : Fin m, ((decide (andreevSharpBig b m + ((ℓ.1 : ℤ) + 1) ≤
      (s i : ℤ) + andreevSharpBig b m * (x (Pi.single i true)).toNat)).toNat : ℝ) =
      (x (Pi.single i true)).toNat * s i :=
    sum_decide_big_le_add_mul _ (fun j => (j : ℤ) + 1) (fun _ => by omega)
      (by simpa using big_gt s hs {i}) (hs i) fun _ => by omega
  simp only [hg, andreevSharpTopWeight]
  rw [← mul_sum, hc]
  push_cast
  ring

/-- The odd zero-address family sums to `-(R + 4) N x_0 ⌈σ / 2⌉`. -/
theorem sum_topWeight_zero (x : BitString b → Bool) (s : Fin b → ℕ) (hs : ∀ i, s i ≤ m) :
    ∑ j : Fin ((b * m + 1) / 2),
      (andreevSharpTopWeight b m (.inr (.inr (.inr (.inr (.inl j))))) : ℝ) *
        (andreevSharpGate (.inr (.inr (.inr (.inr (.inl j))))) x s).toNat =
      -((andreevSharpRange b m + 4) * 2 ^ b * ((x 0).toNat : ℝ) *
        (((∑ i, s i) + 1) / 2 : ℕ)) := by
  have hσ : ∑ i, s i ≤ b * m := (sum_le_sum fun i _ => hs i).trans (by simp)
  have hg (j : Fin ((b * m + 1) / 2)) :
      (andreevSharpGate (.inr (.inr (.inr (.inr (.inl j))))) x s).toNat =
        (decide (andreevSharpBig b m + (2 * (j.1 : ℤ) + 1) ≤
          ((∑ i, s i : ℕ) : ℤ) + andreevSharpBig b m * (x 0).toNat)).toNat := by
    simp only [andreevSharpGate, andreevSharpThreshold, andreevSharpForm_zero, add_assoc,
      Nat.cast_sum]
  have hc : ∑ j : Fin ((b * m + 1) / 2), ((decide (andreevSharpBig b m + (2 * (j.1 : ℤ) + 1) ≤
      ((∑ i, s i : ℕ) : ℤ) + andreevSharpBig b m * (x 0).toNat)).toNat : ℝ) =
      (x 0).toNat * (((∑ i, s i) + 1) / 2 : ℕ) :=
    sum_decide_big_le_add_mul _ (fun j => 2 * (j : ℤ) + 1) (fun _ => by omega)
      (by simpa using big_gt s hs univ) (by omega) fun _ => by omega
  simp only [hg, andreevSharpTopWeight]
  rw [← mul_sum, hc]
  push_cast
  ring

/-- The half family sums to `∑_S (4 (R + 4) - [S = univ] (R + 4) N) x_0 ⌊t_S / 2⌋`. -/
theorem sum_topWeight_half (x : BitString b → Bool) (s : Fin b → ℕ) (hs : ∀ i, s i ≤ m) :
    ∑ S, ∑ j : Fin (#S * m / 2),
      (andreevSharpTopWeight b m (.inr (.inr (.inr (.inr (.inr ⟨S, j⟩))))) : ℝ) *
        (andreevSharpGate (.inr (.inr (.inr (.inr (.inr ⟨S, j⟩))))) x s).toNat =
      ∑ S, (4 * ((andreevSharpRange b m : ℝ) + 4) -
        if S = univ then ((andreevSharpRange b m : ℝ) + 4) * 2 ^ b else 0) *
          ((x 0).toNat : ℝ) * ((∑ i ∈ S, s i) / 2 : ℕ) := by
  refine sum_congr rfl fun S _ => ?_
  have ht : ∑ i ∈ S, s i ≤ #S * m := (sum_le_sum fun i _ => hs i).trans (by simp)
  have hg (j : Fin (#S * m / 2)) :
      (andreevSharpGate (.inr (.inr (.inr (.inr (.inr ⟨S, j⟩))))) x s).toNat =
        (decide (andreevSharpBig b m + 2 * ((j.1 : ℤ) + 1) ≤
          ((∑ i ∈ S, s i : ℕ) : ℤ) + andreevSharpBig b m * (x 0).toNat)).toNat := by
    simp only [andreevSharpGate, andreevSharpThreshold, andreevSharpForm_half, Nat.cast_sum]
  have hc : ∑ j : Fin (#S * m / 2), ((decide (andreevSharpBig b m + 2 * ((j.1 : ℤ) + 1) ≤
      ((∑ i ∈ S, s i : ℕ) : ℤ) + andreevSharpBig b m * (x 0).toNat)).toNat : ℝ) =
      (x 0).toNat * ((∑ i ∈ S, s i) / 2 : ℕ) :=
    sum_decide_big_le_add_mul _ (fun j => 2 * ((j : ℤ) + 1)) (fun _ => by omega)
      (by simpa using big_gt s hs S) (by omega) fun _ => by omega
  simp only [hg, andreevSharpTopWeight]
  rw [← mul_sum, hc]
  push_cast
  ring

/-- **Half counts**: `4 ∑_S ⌊t_S / 2⌋ = N σ - N [p ≠ 0]`, the identity behind
`x_0 [p = 0] = x_0 - x_0 σ + (4 / N) ∑_S x_0 ⌊t_S / 2⌋` (preprint, Appendix A). -/
theorem four_mul_sum_half (s : Fin b → ℕ) :
    4 * ∑ S : Finset (Fin b), (((∑ i ∈ S, s i) / 2 : ℕ) : ℝ) =
      2 ^ b * ∑ i, (s i : ℝ) - 2 ^ b * (1 - if blockParities b s = 0 then 1 else 0) := by
  have hdiv (S : Finset (Fin b)) : 2 * (((∑ i ∈ S, s i) / 2 : ℕ) : ℝ) =
      oddForm (onSingles fun i => (s i : ℝ)) S -
        oddForm (fun c => if c = blockParities b s then 1 else 0) S := by
    rw [oddForm_onSingles]
    have hpar : oddForm (fun c => if c = blockParities b s then (1 : ℝ) else 0) S =
        (parityOn S (blockParities b s)).toNat := by
      simp [oddForm]
    rw [hpar, ← sum_mod_two_eq_toNat_parityOn]
    have : 2 * ((∑ i ∈ S, s i) / 2) = ∑ i ∈ S, s i - (∑ i ∈ S, s i) % 2 := by omega
    have hle : (∑ i ∈ S, s i) % 2 ≤ ∑ i ∈ S, s i := Nat.mod_le _ _
    rw [← Nat.cast_sum]
    exact_mod_cast (show ((2 * ((∑ i ∈ S, s i) / 2) : ℕ) : ℤ) =
      ((∑ i ∈ S, s i : ℕ) : ℤ) - ((∑ i ∈ S, s i) % 2 : ℕ) by push_cast; omega)
  have h4 : 4 * ∑ S : Finset (Fin b), (((∑ i ∈ S, s i) / 2 : ℕ) : ℝ) =
      2 * ∑ S, oddForm (onSingles fun i => (s i : ℝ)) S -
        2 * ∑ S, oddForm (fun c => if c = blockParities b s then 1 else 0) S := by
    rw [← mul_sub, ← sum_sub_distrib, show (4 : ℝ) = 2 * 2 by norm_num, mul_assoc, mul_sum]
    simp_rw [hdiv]
  rw [h4, two_mul_sum_oddForm, two_mul_sum_oddForm, Fintype.card_fin, onSingles_zero]
  have hs1 : ∑ c, onSingles (fun i => (s i : ℝ)) c = ∑ i, (s i : ℝ) := by
    simpa using sum_onSingles_mul (fun i => (s i : ℝ)) fun _ => 1
  rw [hs1]
  simp [eq_comm (a := (0 : BitString b))]

/-- The affine part of the top sum. -/
theorem cast_andreevSharpTopAffine (x : BitString b → Bool) (s : Fin b → ℕ) :
    ((∑ c, andreevSharpTopTable b m c * (x c).toNat +
      ∑ j, andreevSharpTopBlock b m * s j : ℤ) : ℝ) =
      (andreevSharpRange b m + 4) * 2 ^ b * tableVal x 0 -
        4 * 2 ^ b * (∑ c, if c = 0 then 0 else tableVal x c) +
        2 * 2 ^ b * ((andreevSharpAmp m : ℝ) ^ 2 + 1) * (∑ i, tableVal x (Pi.single i true)) +
        2 * andreevSharpAmp m * 2 ^ b * ∑ i, (s i : ℝ) := by
  push_cast
  simp only [andreevSharpTopTable, andreevSharpTopBlock]
  push_cast
  have hE : ∑ c, (if IsSingle c then (1 : ℝ) else 0) * tableVal x c =
      ∑ i, tableVal x (Pi.single i true) := by
    simp_rw [ite_isSingle_eq_onSingles]
    rw [sum_onSingles_mul]
    simp
  have hsplit (c : BitString b) :
      ((if c = 0 then ((andreevSharpRange b m : ℝ) + 4) * 2 ^ b else -(4 * 2 ^ b)) +
        if IsSingle c then 2 * 2 ^ b * ((andreevSharpAmp m : ℝ) ^ 2 + 1) else 0) *
          ((x c).toNat : ℝ) =
      (if c = 0 then ((andreevSharpRange b m : ℝ) + 4) * 2 ^ b * tableVal x c else 0) -
        4 * 2 ^ b * (if c = 0 then 0 else tableVal x c) +
        2 * 2 ^ b * ((andreevSharpAmp m : ℝ) ^ 2 + 1) *
          ((if IsSingle c then (1 : ℝ) else 0) * tableVal x c) := by
    by_cases h0 : c = 0
    · subst h0
      have hu : ¬IsSingle (0 : BitString b) := not_isSingle_zero
      simp [hu, tableVal]
    · by_cases hu : IsSingle c <;> simp [h0, hu, tableVal]
      ring
  simp only [hsplit, sum_add_distrib, sum_sub_distrib, ← mul_sum, hE, sum_ite_eq', mem_univ,
    ite_true]

/-- **The top sum is `2 N - P`**: on block counts at most `m`, the weighted sum read by the top
gate equals `2 · 2 ^ b` minus the sharper score. -/
theorem andreevSharpTopSum_eq (x : BitString b → Bool) (s : Fin b → ℕ) (hs : ∀ i, s i ≤ m) :
    andreevSharpTopSum b m x s = 2 * 2 ^ b - andreevSharpScore b m x s := by
  rw [andreevSharpTopSum, Fintype.sum_sum_type, Fintype.sum_sigma, Fintype.sum_sum_type,
    Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sigma,
    sum_topWeight_ridge x s hs, sum_topWeight_load x s hs, sum_topWeight_square x s hs,
    sum_topWeight_product x s hs, sum_topWeight_zero x s hs, sum_topWeight_half x s hs,
    cast_andreevSharpTopAffine]
  have hhalf := four_mul_sum_half s
  have hsplit : ∑ S : Finset (Fin b), (4 * ((andreevSharpRange b m : ℝ) + 4) -
      if S = univ then ((andreevSharpRange b m : ℝ) + 4) * 2 ^ b else 0) *
        ((x 0).toNat : ℝ) * (((∑ i ∈ S, s i) / 2 : ℕ) : ℝ) =
      ((andreevSharpRange b m : ℝ) + 4) * ((x 0).toNat : ℝ) *
          (4 * ∑ S : Finset (Fin b), (((∑ i ∈ S, s i) / 2 : ℕ) : ℝ)) -
        ((andreevSharpRange b m : ℝ) + 4) * 2 ^ b * ((x 0).toNat : ℝ) *
          (((∑ i, s i) / 2 : ℕ) : ℝ) := by
    simp only [sub_mul, sum_sub_distrib, ite_mul, zero_mul, sum_ite_eq', mem_univ, ite_true,
      mul_sum]
    congr 1
    exact sum_congr rfl fun S _ => by ring
  have hσ2 : ((((∑ i, s i) + 1) / 2 : ℕ) : ℝ) + (((∑ i, s i) / 2 : ℕ) : ℝ) = ∑ i, (s i : ℝ) := by
    have h : ((∑ i, s i) + 1) / 2 + (∑ i, s i) / 2 = ∑ i, s i := by omega
    exact_mod_cast h
  have hpow : (2 : ℝ) ^ (b - 1) * (andreevSharpLoad b m x s : ℝ) ^ 2 =
        2 ^ b / 2 * (andreevSharpLoad b m x s : ℝ) ^ 2 ∧
      (2 : ℝ) ^ (b - 1) * ∑ i, (s i : ℝ) ^ 2 = 2 ^ b / 2 * ∑ i, (s i : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · have hw := andreevSharpLoad_le x s hs
      have : andreevSharpLoad 0 m x s = 0 := by simpa [andreevSharpRange] using hw
      simp [this]
    · have h2 : (2 : ℝ) ^ (b - 1) = 2 ^ b / 2 := by
        rw [eq_div_iff two_ne_zero, ← pow_succ, Nat.sub_add_cancel hb]
      exact ⟨by rw [h2], by rw [h2]⟩
  rw [hsplit, hpow.1, hpow.2, hhalf, andreevSharpScore]
  simp only [tableVal]
  linear_combination -((andreevSharpRange b m : ℝ) + 4) * 2 ^ b * ((x 0).toNat : ℝ) * hσ2

end TopSum

/-! ### The explicit circuit -/

section Circuit

variable (b m : ℕ)

/-- The bottom gate with index `idx`: integer weights `andreevFormWeight` on all inputs and an
integer threshold. -/
noncomputable abbrev andreevSharpBottomOp (idx : AndreevSharpIndex b m) : Op :=
  ⟨2 ^ b + b * m,
    fun i => (andreevFormWeight b m (andreevSharpTable b m idx) (andreevSharpBlock b m idx) i : ℝ),
    (andreevSharpThreshold b m idx : ℝ)⟩

/-- The integer input weights of the top gate. -/
def andreevSharpTopInput : Fin (2 ^ b + b * m) → ℤ :=
  andreevFormWeight b m (andreevSharpTopTable b m) fun _ => andreevSharpTopBlock b m

/-- **The sharper depth-two circuit for Andreev's function** (preprint, Theorem 5): bottom gates
indexed by `AndreevSharpIndex b m`, and a top gate reading the bottom gates and the inputs with
threshold `2 N`. -/
noncomputable def andreevSharpCircuit : Circuit signature (2 ^ b + b * m) 1 :=
  depthTwoInputs (fun j => andreevSharpBottomOp b m ((Fintype.equivFin _).symm j)) (fun _ => id)
    (fun j => (andreevSharpTopWeight b m ((Fintype.equivFin _).symm j) : ℝ))
    (fun i => (andreevSharpTopInput b m i : ℝ)) (2 * 2 ^ b)

variable {b m}

/-- A bottom gate of the circuit evaluates as `andreevSharpGate` on the table bits and block
counts. -/
theorem interpretation_andreevSharpBottomOp (idx : AndreevSharpIndex b m)
    (w : BitString (2 ^ b + b * m)) :
    interpretation (andreevSharpBottomOp b m idx) (fun a => w (id a)) =
      andreevSharpGate idx (andreevTable b m w) (andreevBlockCount b m w) :=
  interpretation_andreevFormWeight _ _ _ w

/-- The circuit compares `2 N` with the top sum on the table bits and block counts. -/
theorem eval_andreevSharpCircuit (w : BitString (2 ^ b + b * m)) (o : Fin 1) :
    (andreevSharpCircuit b m).eval interpretation w o =
      decide (2 * 2 ^ b ≤
        andreevSharpTopSum b m (andreevTable b m w) (andreevBlockCount b m w)) := by
  rw [andreevSharpCircuit, eval_depthTwoInputs]
  simp only [interpretation_andreevSharpBottomOp]
  congr 2
  rw [andreevSharpTopSum, ← (Fintype.equivFin (AndreevSharpIndex b m)).symm.sum_comp]
  congr 1
  have h := sum_andreevFormWeight_mul (andreevSharpTopTable b m)
    (fun _ => andreevSharpTopBlock b m) w
  have h' := congrArg (fun z : ℤ => (z : ℝ)) h
  push_cast at h' ⊢
  rw [← h']
  rfl

/-- **`andreevSharpCircuit b m` computes Andreev's function** on every input (preprint,
Theorem 5). -/
theorem computes_andreevSharpCircuit (b m : ℕ) :
    (andreevSharpCircuit b m).Computes interpretation (single (andreev b m)) := by
  intro w
  funext o
  rw [eval_andreevSharpCircuit, single_apply, andreevSharpTopSum_eq _ _ (andreevBlockCount_le w),
    andreev_eq_andreevTable]
  have hm := andreevSharpScore_margin (andreevTable b m w) (andreevBlockCount b m w)
    (andreevBlockCount_le w)
  have hN : (0 : ℝ) < 2 ^ b := by positivity
  cases hx : andreevTable b m w (blockParities b (andreevBlockCount b m w))
  · have := hm.1 hx
    simp only [decide_eq_false_iff_not, not_le]
    linarith
  · have := hm.2 hx
    simp only [decide_eq_true_eq]
    linarith

/-- The circuit has depth at most `2`. -/
theorem depth_andreevSharpCircuit_le (b m : ℕ) : (andreevSharpCircuit b m).depth ≤ 2 :=
  depth_depthTwoInputs_le ..

/-- The circuit has `|AndreevSharpIndex b m|` bottom gates and one top gate. -/
theorem size_andreevSharpCircuit_eq_card (b m : ℕ) :
    (andreevSharpCircuit b m).size = Fintype.card (AndreevSharpIndex b m) + 1 :=
  size_depthTwoInputs ..

end Circuit

/-! ### The exact gate count -/

section Count

private theorem two_mul_ridgeLen_add_half (b m : ℕ) (S : Finset (Fin b)) :
    2 * (andreevSharpRidgeLen b m S + #S * m / 2) =
      (if S = ∅ then 0 else 2 ^ b) + 2 * (andreevSharpAmp m + m) * #S := by
  rw [andreevSharpRidgeLen]
  split_ifs with hS
  · subst hS
    simp
  · obtain ⟨i, -⟩ := nonempty_iff_ne_empty.mpr hS
    have hb : 2 ^ b = 2 * 2 ^ (b - 1) := by
      rw [← pow_succ']
      congr 1
      have := i.pos
      omega
    have h1 : (2 * andreevSharpAmp m + m) * #S = 2 * (andreevSharpAmp m * #S) + m * #S := by ring
    have h2 : 2 * (andreevSharpAmp m + m) * #S = 2 * (andreevSharpAmp m * #S) + 2 * (m * #S) := by
      ring
    rw [hb, h1, h2, mul_comm #S m]
    omega

/-- The two halved terms of the gate count are even. -/
private theorem andreevSharp_count_even (b m : ℕ) :
    2 ^ b * (2 ^ b - 1) % 2 = 0 ∧ b * 2 ^ b * (m + andreevSharpAmp m) % 2 = 0 := by
  refine ⟨Nat.even_iff.mp (Nat.even_mul_pred_self _), ?_⟩
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  · exact Nat.even_iff.mp (((Nat.even_pow.mpr ⟨even_two, hb.ne'⟩).mul_left b).mul_right _)

/-- **Exact gate count** (preprint, Theorem 5, equation `eq:bestcount`): with `N = 2 ^ b` and
`α = ⌊(m - 1) / 2⌋`, the circuit has
`N (N - 1) / 2 + b N (m + α) / 2 + 2 (N - 1) + 2 α b + 3 b m + ⌈b m / 2⌉` bottom gates. -/
theorem card_andreevSharpIndex (b m : ℕ) :
    Fintype.card (AndreevSharpIndex b m) =
      2 ^ b * (2 ^ b - 1) / 2 + b * 2 ^ b * (m + andreevSharpAmp m) / 2 + 2 * (2 ^ b - 1) +
        2 * andreevSharpAmp m * b + 3 * (b * m) + (b * m + 1) / 2 := by
  simp only [Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin, Fintype.card_prod]
  have hsum : 2 * ∑ S : Finset (Fin b), (andreevSharpRidgeLen b m S + #S * m / 2) =
      2 ^ b * (2 ^ b - 1) + b * 2 ^ b * (m + andreevSharpAmp m) := by
    rw [mul_sum]
    simp_rw [two_mul_ridgeLen_add_half]
    rw [sum_add_distrib, ← mul_sum]
    have hcard : ∑ S : Finset (Fin b), (if S = ∅ then 0 else 2 ^ b) = 2 ^ b * (2 ^ b - 1) := by
      rw [sum_ite, sum_const_zero, zero_add, sum_const, smul_eq_mul, filter_ne', card_erase_of_mem
        (mem_univ _), card_univ, Fintype.card_finset, Fintype.card_fin, mul_comm]
    have hS := two_mul_sum_card_finset b
    rw [hcard]
    nlinarith [hS]
  have hpos : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  obtain ⟨heven1, heven2⟩ := andreevSharp_count_even b m
  rw [sum_add_distrib] at hsum
  rw [andreevSharpRange]
  omega

/-- **Size of the sharper circuit**: the bottom gates of `card_andreevSharpIndex` and one top
gate. -/
theorem size_andreevSharpCircuit (b m : ℕ) :
    (andreevSharpCircuit b m).size =
      2 ^ b * (2 ^ b - 1) / 2 + b * 2 ^ b * (m + andreevSharpAmp m) / 2 + 2 * (2 ^ b - 1) +
        2 * andreevSharpAmp m * b + 3 * (b * m) + (b * m + 1) / 2 + 1 := by
  rw [size_andreevSharpCircuit_eq_card, card_andreevSharpIndex]

end Count

/-! ### Weights -/

section Weights

variable {b m : ℕ}

/-- Every block coefficient of a bottom gate is `0` or `1`. -/
theorem andreevSharpBlock_eq_zero_or_one (idx : AndreevSharpIndex b m) (j : Fin b) :
    andreevSharpBlock b m idx j = 0 ∨ andreevSharpBlock b m idx j = 1 := by
  rcases idx with ⟨S, _⟩ | _ | ⟨i, _⟩ | ⟨i, _⟩ | _ | ⟨S, _⟩ <;>
    simp only [andreevSharpBlock, Pi.one_apply] <;> (try split_ifs) <;> simp

/-- **Bottom address weights lie in `{0, 1}`** (preprint, Theorem 5 and Section 5): every bottom
gate gives each address bit weight `0` or `1`, constant on each block. -/
theorem weight_andreevSharpBottomOp_blockVar (idx : AndreevSharpIndex b m) (j : Fin b)
    (t : Fin m) :
    (andreevSharpBottomOp b m idx).weight (andreevBlockVar b m j t) = 0 ∨
      (andreevSharpBottomOp b m idx).weight (andreevBlockVar b m j t) = 1 := by
  simp only [andreevFormWeight_blockVar]
  rcases andreevSharpBlock_eq_zero_or_one idx j with h | h <;> simp [h]

/-- **Every bottom gate is sign-coherent** for Andreev's blocks. -/
theorem isSignCoherent_andreevSharpBottomOp (idx : AndreevSharpIndex b m) :
    IsSignCoherent (andreevBlockVar b m) (argWeight (andreevSharpBottomOp b m idx) id) := by
  rw [argWeight_id]
  exact isSignCoherent_andreevFormWeight _ _ (andreevSharpBlock_eq_zero_or_one idx)

/-- **The bottom gates of the circuit are sign-coherent**, in the form consumed by lower bounds
over the gates read by the output gate: every such gate of `andreevSharpCircuit b m` has
sign-coherent input weights `inputWeight` for Andreev's blocks. -/
theorem isSignCoherent_inputWeight_andreevSharpCircuit {top : Fin (andreevSharpCircuit b m).size}
    (htop : (andreevSharpCircuit b m).outputs 0 = .gate top)
    {k : Fin (andreevSharpCircuit b m).size}
    (hk : k ∈ gateSupport (andreevSharpCircuit b m).program top) :
    IsSignCoherent (andreevBlockVar b m) (inputWeight (andreevSharpCircuit b m).program k) :=
  isSignCoherent_inputWeight_depthTwoInputs _ _ _ _ _
    (fun _ => isSignCoherent_andreevSharpBottomOp _) htop hk

/-- **Integer weights**: the bottom weights and thresholds, the top weights on gates and inputs, and
the top threshold of `andreevSharpCircuit b m` are integers. -/
theorem andreevSharpCircuit_int_weights :
    (∀ idx i, ∃ z : ℤ, (andreevSharpBottomOp b m idx).weight i = z) ∧
      (∀ idx, ∃ z : ℤ, (andreevSharpBottomOp b m idx).threshold = z) ∧
      (∀ idx : AndreevSharpIndex b m, ∃ z : ℤ, (andreevSharpTopWeight b m idx : ℝ) = z) ∧
      (∀ i, ∃ z : ℤ, (andreevSharpTopInput b m i : ℝ) = z) ∧
      ∃ z : ℤ, (2 * 2 ^ b : ℝ) = z :=
  ⟨fun _ _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩,
    ⟨2 * 2 ^ b, by push_cast; rfl⟩⟩

end Weights

/-! ### Weight magnitudes -/

section Magnitudes

variable {b m : ℕ}

/-- `2 α ≤ m` for the amplification `α = ⌊(m - 1) / 2⌋`. -/
theorem two_mul_andreevSharpAmp_le (m : ℕ) : 2 * andreevSharpAmp m ≤ m := by
  rw [andreevSharpAmp]; omega

/-- The load range is at most `2 n - 2`: `R + 2 ≤ 2 n` with `n = 2 ^ b + b m`. -/
theorem andreevSharpRange_add_two_le (b m : ℕ) :
    andreevSharpRange b m + 2 ≤ 2 * (2 ^ b + b * m) := by
  have h1 : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  have h2 : 2 * andreevSharpAmp m * b ≤ b * m := by
    nlinarith [two_mul_andreevSharpAmp_le m]
  rw [andreevSharpRange]; omega

/-- A nonzero address exists only for `b ≥ 1`. -/
private theorem one_le_of_ne_zero {c : BitString b} (h : c ≠ 0) : 1 ≤ b := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · exact absurd (Subsingleton.elim c 0) h
  · exact hb

/-- Twice a table multiplier is at most `n`: `2 μ_c ≤ 2 ^ b + b m`. -/
theorem two_mul_andreevSharpMult_le (c : BitString b) :
    2 * andreevSharpMult b m c ≤ 2 ^ b + b * m := by
  unfold andreevSharpMult
  split_ifs with h0 hs
  · simp
  · have hb := one_le_of_ne_zero h0
    have h2 := Nat.one_lt_two_pow (n := b) (by omega)
    have := two_mul_andreevSharpAmp_le m
    nlinarith
  · have : 1 ≤ 2 ^ b := Nat.one_le_two_pow
    have h2 := Nat.one_lt_two_pow (n := b) (by have := one_le_of_ne_zero h0; omega)
    omega

/-- Every table coefficient of a bottom gate has absolute value at most `2 n`, with
`n = 2 ^ b + b m`. -/
theorem abs_andreevSharpTable_le (idx : AndreevSharpIndex b m) (c : BitString b) :
    |andreevSharpTable b m idx c| ≤ 2 * (2 ^ b + b * m : ℤ) := by
  have hn : (0 : ℤ) ≤ 2 ^ b + b * m := by positivity
  have hμ : 2 * (andreevSharpMult b m c : ℤ) ≤ 2 ^ b + b * m := by
    exact_mod_cast two_mul_andreevSharpMult_le c
  -- `B = n + 2 ≤ 2 n` once `b ≥ 1`
  have hB (hb : 1 ≤ b) : |andreevSharpBig b m| ≤ 2 * (2 ^ b + b * m : ℤ) := by
    have h2 : (2 : ℤ) ≤ 2 ^ b := by exact_mod_cast Nat.one_lt_two_pow (n := b) (by omega)
    have : (0 : ℤ) ≤ b * m := by positivity
    rw [andreevSharpBig, abs_of_nonneg (by positivity)]
    linarith
  rcases idx with ⟨S, j⟩ | θ | ⟨i, ℓ⟩ | ⟨i, ℓ⟩ | j | ⟨S, j⟩
  · simp only [andreevSharpTable]
    rw [abs_of_nonneg (by positivity)]
    have : ((parityOn S c).toNat : ℤ) ≤ 1 := by exact_mod_cast Bool.toNat_le _
    nlinarith
  · simp only [andreevSharpTable]
    rw [abs_of_nonneg (by positivity)]
    linarith
  · simp only [andreevSharpTable, Pi.zero_apply, abs_zero]; positivity
  · simp only [andreevSharpTable]
    split_ifs
    · exact hB (Nat.one_le_iff_ne_zero.mpr (Fin.pos i).ne')
    · rw [abs_zero]; positivity
  · simp only [andreevSharpTable]
    split_ifs
    · refine hB (Nat.one_le_iff_ne_zero.mpr fun hb => ?_)
      have := j.isLt
      simp [hb] at this
    · rw [abs_zero]; positivity
  · simp only [andreevSharpTable]
    split_ifs
    · refine hB (Nat.one_le_iff_ne_zero.mpr fun hb => ?_)
      subst hb
      have := j.isLt
      simp [Finset.eq_empty_of_isEmpty S] at this
    · rw [abs_zero]; positivity

/-- Every bottom threshold has absolute value at most `2 n`, with `n = 2 ^ b + b m`. -/
theorem abs_andreevSharpThreshold_le (idx : AndreevSharpIndex b m) :
    |andreevSharpThreshold b m idx| ≤ 2 * (2 ^ b + b * m : ℤ) := by
  have hN : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  have hα := two_mul_andreevSharpAmp_le m
  have hR := andreevSharpRange_add_two_le b m
  -- once `b ≥ 1`: `m ≤ b m` and `2 ≤ N`, so `B + m ≤ 2 n`
  have hpos (hb : 1 ≤ b) : m ≤ b * m ∧ 2 ≤ 2 ^ b :=
    ⟨Nat.le_mul_of_pos_left m hb, Nat.one_lt_two_pow (n := b) (by omega)⟩
  suffices h : 0 ≤ andreevSharpThreshold b m idx ∧
      andreevSharpThreshold b m idx ≤ ((2 * (2 ^ b + b * m) : ℕ) : ℤ) by
    rw [abs_of_nonneg h.1]; exact_mod_cast h.2
  rcases idx with ⟨S, j⟩ | θ | ⟨i, ℓ⟩ | ⟨i, ℓ⟩ | j | ⟨S, j⟩ <;>
    simp only [andreevSharpThreshold, andreevSharpBig] <;> refine ⟨by positivity, ?_⟩ <;> norm_cast
  · have hj : j.1 < andreevSharpRidgeLen b m S := j.isLt
    have hS : #S ≤ b := (card_le_univ S).trans_eq (Fintype.card_fin b)
    have hle : (2 * andreevSharpAmp m + m) * #S ≤ 2 * (b * m) := by nlinarith
    unfold andreevSharpRidgeLen at hj
    split_ifs at hj <;> omega
  · have := θ.isLt
    omega
  · have := hpos (Nat.one_le_iff_ne_zero.mpr (Fin.pos i).ne')
    have := ℓ.isLt
    omega
  · have := hpos (Nat.one_le_iff_ne_zero.mpr (Fin.pos i).ne')
    have := ℓ.isLt
    omega
  · have := j.isLt
    have := hpos (Nat.one_le_iff_ne_zero.mpr fun hb => by simp [hb] at this)
    omega
  · have := j.isLt
    have hSm : #S * m ≤ b * m :=
      Nat.mul_le_mul_right m ((card_le_univ S).trans_eq (Fintype.card_fin b))
    have := hpos (Nat.one_le_iff_ne_zero.mpr fun hb => by
      subst hb; simp [Finset.eq_empty_of_isEmpty S] at this)
    omega

/-- A bound on the table and block coefficients bounds every weight of `andreevFormWeight`. -/
theorem abs_andreevFormWeight_le {a : BitString b → ℤ} {β : Fin b → ℤ} {W : ℤ}
    (ha : ∀ c, |a c| ≤ W) (hβ : ∀ j, |β j| ≤ W) (i : Fin (2 ^ b + b * m)) :
    |andreevFormWeight b m a β i| ≤ W := by
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i <;>
    simp only [andreevFormWeight, Fin.addCases_left, Fin.addCases_right]
  exacts [ha _, hβ _]

/-- **Bottom weights are `O(n)`** (preprint, end of Appendix A): every input weight of every bottom
gate of `andreevSharpCircuit b m` has absolute value at most `2 n`, with `n = 2 ^ b + b m`. -/
theorem abs_weight_andreevSharpBottomOp_le (idx : AndreevSharpIndex b m)
    (i : Fin (2 ^ b + b * m)) :
    |(andreevSharpBottomOp b m idx).weight i| ≤ 2 * (2 ^ b + b * m : ℝ) := by
  have h : |andreevFormWeight b m (andreevSharpTable b m idx) (andreevSharpBlock b m idx) i| ≤
      2 * (2 ^ b + b * m : ℤ) := by
    refine abs_andreevFormWeight_le (abs_andreevSharpTable_le idx) (fun j => ?_) i
    have : (1 : ℤ) ≤ 2 * (2 ^ b + b * m) := by
      have : (1 : ℤ) ≤ 2 ^ b := one_le_pow₀ (by norm_num)
      have : (0 : ℤ) ≤ b * m := by positivity
      linarith
    rcases andreevSharpBlock_eq_zero_or_one idx j with h | h <;> rw [h] <;> simp <;> linarith
  unfold andreevSharpBottomOp; dsimp only
  exact_mod_cast h

/-- **Bottom thresholds are `O(n)`** (preprint, end of Appendix A): every bottom threshold of
`andreevSharpCircuit b m` has absolute value at most `2 n`, with `n = 2 ^ b + b m`. -/
theorem abs_threshold_andreevSharpBottomOp_le (idx : AndreevSharpIndex b m) :
    |(andreevSharpBottomOp b m idx).threshold| ≤ 2 * (2 ^ b + b * m : ℝ) := by
  unfold andreevSharpBottomOp; dsimp only
  exact_mod_cast abs_andreevSharpThreshold_le idx

/-- **Top weights on the bottom gates are `O(n ^ 2)`**: each has absolute value at most
`2 (n + 1) (n + 4)`, with `n = 2 ^ b + b m`. The largest, such as `(R + 4) N` on the zero-address
gates, are `Θ(N n)`; the ridge weights are at most `16 n`. -/
theorem abs_andreevSharpTopWeight_le (idx : AndreevSharpIndex b m) :
    |andreevSharpTopWeight b m idx| ≤
      2 * ((2 ^ b + b * m : ℤ) + 1) * ((2 ^ b + b * m : ℤ) + 4) := by
  set n : ℤ := 2 ^ b + b * m with hn
  have hN1 : (1 : ℤ) ≤ 2 ^ b := one_le_pow₀ (by norm_num)
  have hbm : (0 : ℤ) ≤ b * m := by positivity
  have hbN : (b : ℤ) ≤ 2 ^ b := by exact_mod_cast Nat.lt_two_pow_self.le
  have hα : 2 * (andreevSharpAmp m : ℤ) ≤ m := by exact_mod_cast two_mul_andreevSharpAmp_le m
  have hα0 : (0 : ℤ) ≤ andreevSharpAmp m := by positivity
  have hR : (andreevSharpRange b m : ℤ) + 2 ≤ 2 * n := by
    rw [hn]; exact_mod_cast andreevSharpRange_add_two_le b m
  have hR0 : (0 : ℤ) ≤ andreevSharpRange b m := by positivity
  have hQ : 16 * n ≤ 2 * (n + 1) * (n + 4) := by nlinarith [sq_nonneg (2 * n - 3)]
  -- for `b ≥ 1`, `2 ^ (b - 1)` is half of `2 ^ b`
  have hhalf (hb : 1 ≤ b) : (2 : ℤ) * 2 ^ (b - 1) = 2 ^ b ∧ (0 : ℤ) ≤ 2 ^ (b - 1) :=
    ⟨by rw [← pow_succ']; congr 1; omega, by positivity⟩
  have hmb (hb : 1 ≤ b) : (m : ℤ) ≤ b * m := by
    have : (1 : ℤ) ≤ b := by exact_mod_cast hb
    nlinarith
  rcases idx with ⟨S, j⟩ | θ | ⟨i, ℓ⟩ | ⟨i, ℓ⟩ | j | ⟨S, j⟩ <;>
    simp only [andreevSharpTopWeight, andreevSharpKappa]
  · have hj : j.1 < andreevSharpRidgeLen b m S := j.isLt
    have hS : #S ≤ b := (card_le_univ S).trans_eq (Fintype.card_fin b)
    unfold andreevSharpRidgeLen at hj
    split_ifs at hj
    · omega
    have hJ : 2 * j.1 + 1 ≤ 2 ^ b + (2 * andreevSharpAmp m + m) * #S := by omega
    have hJ' : 2 * (j : ℤ) + 1 ≤ 2 ^ b + (2 * andreevSharpAmp m + m) * #S := by exact_mod_cast hJ
    have hS' : (#S : ℤ) ≤ b := by exact_mod_cast hS
    have hS0 : (0 : ℤ) ≤ #S := by positivity
    have h1 : (m : ℤ) * #S ≤ b * m := by nlinarith
    have h2 : (andreevSharpAmp m : ℤ) * #S ≤ andreevSharpAmp m * b := by nlinarith
    have h3 : 2 * (andreevSharpAmp m : ℤ) * b ≤ b * m := by nlinarith
    have hj0 : (0 : ℤ) ≤ j := by positivity
    refine abs_le.mpr ⟨?_, ?_⟩ <;> nlinarith
  · have hθ := θ.isLt
    have hb : 1 ≤ b := by
      by_contra h
      obtain rfl : b = 0 := by omega
      simp [andreevSharpRange] at hθ
    have hθ' : (θ : ℤ) + 1 ≤ andreevSharpRange b m := by exact_mod_cast hθ
    have := hhalf hb
    rw [abs_neg, abs_of_nonneg (by positivity)]
    nlinarith
  · have hb : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr (Fin.pos i).ne'
    have hℓ : (ℓ : ℤ) + 1 ≤ m := by exact_mod_cast ℓ.isLt
    have hmb := hmb hb
    have := hhalf hb
    rw [abs_neg, abs_of_nonneg (by positivity)]
    nlinarith
  · have hb : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr (Fin.pos i).ne'
    have hmb := hmb hb
    have h2 : (2 : ℤ) ≤ 2 ^ b := by exact_mod_cast Nat.one_lt_two_pow (n := b) (by omega)
    rw [abs_neg, abs_of_nonneg (by positivity)]
    nlinarith
  · rw [abs_neg, abs_of_nonneg (by positivity)]
    nlinarith
  · have hle : |(4 : ℤ) - if S = univ then 2 ^ b else 0| ≤ n + 4 := by
      split_ifs
      · rw [abs_le]; constructor <;> linarith
      · simp; linarith
    have hfac : (4 * ((andreevSharpRange b m : ℤ) + 4) -
        if S = univ then ((andreevSharpRange b m : ℤ) + 4) * 2 ^ b else 0) =
        ((andreevSharpRange b m : ℤ) + 4) * (4 - if S = univ then 2 ^ b else 0) := by
      split_ifs <;> ring
    push_cast
    rw [hfac, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ andreevSharpRange b m + 4)]
    have := abs_nonneg ((4 : ℤ) - if S = univ then 2 ^ b else 0)
    nlinarith

/-- `27 N x ^ 2 ≤ 4 (N + x) ^ 3`, from `4 (N + x) ^ 3 - 27 N x ^ 2 = (x - 2 N) ^ 2 (N + 4 x)`. -/
private theorem twentyseven_mul_sq_le {N x : ℤ} (hN : 0 ≤ N) (hx : 0 ≤ x) :
    27 * N * x ^ 2 ≤ 4 * (N + x) ^ 3 := by
  nlinarith [mul_nonneg (sq_nonneg (x - 2 * N)) (by positivity : 0 ≤ N + 4 * x)]

/-- A top input weight is either at most `2 n (n + 1)`, or it sits on a weight-one address
(so `b ≥ 1`) and is at most `2 N α ^ 2 + 2 N`. -/
private theorem abs_andreevSharpTopInput_cases (i : Fin (2 ^ b + b * m)) :
    |andreevSharpTopInput b m i| ≤ 2 * (2 ^ b + b * m : ℤ) * ((2 ^ b + b * m : ℤ) + 1) ∨
      1 ≤ b ∧ |andreevSharpTopInput b m i| ≤
        2 * 2 ^ b * (andreevSharpAmp m : ℤ) ^ 2 + 2 * 2 ^ b := by
  set n : ℤ := 2 ^ b + b * m with hn
  have hN1 : (1 : ℤ) ≤ 2 ^ b := one_le_pow₀ (by norm_num)
  have hbm : (0 : ℤ) ≤ b * m := by positivity
  have hR : (andreevSharpRange b m : ℤ) + 2 ≤ 2 * n := by
    rw [hn]; exact_mod_cast andreevSharpRange_add_two_le b m
  have hR0 : (0 : ℤ) ≤ andreevSharpRange b m := by positivity
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i <;>
    simp only [andreevSharpTopInput, andreevFormWeight, Fin.addCases_left, Fin.addCases_right]
  · set c := (BitString.equivFin b).symm k
    simp only [andreevSharpTopTable]
    by_cases h0 : c = 0
    · left
      have hu : ¬IsSingle (0 : BitString b) := not_isSingle_zero
      simp only [h0, ↓reduceIte, hu, add_zero]
      rw [abs_of_nonneg (by positivity)]
      nlinarith
    by_cases hu : IsSingle c
    · right
      refine ⟨one_le_of_ne_zero h0, ?_⟩
      simp only [h0, hu, ↓reduceIte]
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (andreevSharpAmp m : ℤ)]
    · left
      simp only [h0, hu, ↓reduceIte, add_zero, abs_neg]
      rw [abs_of_nonneg (by positivity)]
      nlinarith
  · left
    have hb : 1 ≤ b := by
      by_contra h
      obtain rfl : b = 0 := by omega
      rw [Nat.zero_mul] at k
      exact k.elim0
    have hα : 2 * (andreevSharpAmp m : ℤ) ≤ m := by exact_mod_cast two_mul_andreevSharpAmp_le m
    have hmb : (m : ℤ) ≤ b * m := by
      have : (1 : ℤ) ≤ b := by exact_mod_cast hb
      nlinarith
    simp only [andreevSharpTopBlock]
    rw [abs_of_nonneg (by positivity)]
    nlinarith

/-- The weight-one top input weights: `27 b ^ 2 (2 N α ^ 2) ≤ 2 n ^ 3`, since `4 α ^ 2 ≤ m ^ 2`
and `27 N (b m) ^ 2 ≤ 4 (N + b m) ^ 3`. -/
private theorem sq_mul_amp_sq_le (b m : ℕ) :
    27 * b ^ 2 * (2 * 2 ^ b * (andreevSharpAmp m : ℤ) ^ 2) ≤ 2 * (2 ^ b + b * m : ℤ) ^ 3 := by
  have hα : 2 * (andreevSharpAmp m : ℤ) ≤ m := by exact_mod_cast two_mul_andreevSharpAmp_le m
  have hα0 : (0 : ℤ) ≤ andreevSharpAmp m := by positivity
  have hcube := twentyseven_mul_sq_le (N := 2 ^ b) (x := b * m) (by positivity) (by positivity)
  have hsq : 4 * (andreevSharpAmp m : ℤ) ^ 2 ≤ m ^ 2 := by nlinarith
  have : (0 : ℤ) ≤ 27 * b ^ 2 * 2 ^ b := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hsq this]

/-- `N ≤ n (n + 1)`. -/
private theorem two_pow_le_mul_succ (b m : ℕ) :
    (2 : ℤ) ^ b ≤ (2 ^ b + b * m) * ((2 ^ b + b * m) + 1) := by
  have : (0 : ℤ) ≤ b * m := by positivity
  have : (1 : ℤ) ≤ 2 ^ b := one_le_pow₀ (by norm_num)
  nlinarith

/-- **Top input weights, sharp form**: `27 b ^ 2 |v_i| ≤ 2 n ^ 3 + 54 b ^ 2 n (n + 1)`, with
`n = 2 ^ b + b m`. Only the weights `2 N (α ^ 2 - 1)` on the weight-one table addresses exceed
`2 n (n + 1)`, and they are `O(N m ^ 2) = O(n ^ 3 / b ^ 2)`. -/
theorem sq_mul_abs_andreevSharpTopInput_le (i : Fin (2 ^ b + b * m)) :
    27 * b ^ 2 * |andreevSharpTopInput b m i| ≤
      2 * (2 ^ b + b * m : ℤ) ^ 3 +
        54 * b ^ 2 * ((2 ^ b + b * m : ℤ) * ((2 ^ b + b * m : ℤ) + 1)) := by
  have hb2 : (0 : ℤ) ≤ 27 * b ^ 2 := by positivity
  have hcube : (0 : ℤ) ≤ (2 ^ b + b * m) ^ 3 := by positivity
  rcases abs_andreevSharpTopInput_cases i with h | ⟨-, h⟩
  · nlinarith [mul_le_mul_of_nonneg_left h hb2]
  · have hN := two_pow_le_mul_succ b m
    nlinarith [mul_le_mul_of_nonneg_left h hb2, sq_mul_amp_sq_le b m,
      mul_le_mul_of_nonneg_left hN hb2]

/-- **Top input weights are `O(n ^ 3)`** (preprint, end of Appendix A):
`27 |v_i| ≤ 2 n ^ 3 + 54 n (n + 1)`, with `n = 2 ^ b + b m`. -/
theorem abs_andreevSharpTopInput_le (i : Fin (2 ^ b + b * m)) :
    27 * |andreevSharpTopInput b m i| ≤
      2 * (2 ^ b + b * m : ℤ) ^ 3 + 54 * ((2 ^ b + b * m : ℤ) * ((2 ^ b + b * m : ℤ) + 1)) := by
  have hcube : (0 : ℤ) ≤ (2 ^ b + b * m) ^ 3 := by positivity
  rcases abs_andreevSharpTopInput_cases i with h | ⟨hb, h⟩
  · linarith
  · have hb' : (1 : ℤ) ≤ b ^ 2 := by exact_mod_cast Nat.one_le_pow _ _ hb
    have hkey := sq_mul_amp_sq_le b m
    have h0 : (0 : ℤ) ≤ 2 * 2 ^ b * (andreevSharpAmp m : ℤ) ^ 2 := by positivity
    have hN := two_pow_le_mul_succ b m
    nlinarith

/-- The circuit-wide polynomial: `(2 n ^ 3 + 54 (n + 1) (n + 4)) / 27`. -/
private theorem andreevSharp_bounds_le (b m : ℕ) :
    2 * (2 ^ b + b * m : ℝ) ≤ (2 * (2 ^ b + b * m : ℝ) ^ 3 +
      54 * (((2 ^ b + b * m : ℝ) + 1) * ((2 ^ b + b * m : ℝ) + 4))) / 27 ∧
    2 * ((2 ^ b + b * m : ℝ) + 1) * ((2 ^ b + b * m : ℝ) + 4) ≤ (2 * (2 ^ b + b * m : ℝ) ^ 3 +
      54 * (((2 ^ b + b * m : ℝ) + 1) * ((2 ^ b + b * m : ℝ) + 4))) / 27 ∧
    (2 * (2 ^ b + b * m : ℝ) ^ 3 + 54 * ((2 ^ b + b * m : ℝ) * ((2 ^ b + b * m : ℝ) + 1))) / 27 ≤
      (2 * (2 ^ b + b * m : ℝ) ^ 3 +
        54 * (((2 ^ b + b * m : ℝ) + 1) * ((2 ^ b + b * m : ℝ) + 4))) / 27 := by
  have h0 : (0 : ℝ) ≤ 2 ^ b + b * m := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [le_div_iff₀ (by norm_num)]; nlinarith [pow_nonneg h0 3]
  · rw [le_div_iff₀ (by norm_num)]; nlinarith [pow_nonneg h0 3]
  · rw [div_le_div_iff_of_pos_right (by norm_num)]; nlinarith

/-- **All weights of the circuit are polynomial in `n`** (preprint, Theorem 5): every weight of
every gate of `andreevSharpCircuit b m` satisfies `27 |w| ≤ 2 n ^ 3 + 54 (n + 1) (n + 4)`, with
`n = 2 ^ b + b m`. -/
theorem abs_weight_andreevSharpCircuit_le (k : Fin (andreevSharpCircuit b m).size)
    (a : Fin ((andreevSharpCircuit b m).program.lines k).op.arity) :
    27 * |((andreevSharpCircuit b m).program.lines k).op.weight a| ≤
      2 * (2 ^ b + b * m : ℝ) ^ 3 +
        54 * (((2 ^ b + b * m : ℝ) + 1) * ((2 ^ b + b * m : ℝ) + 4)) := by
  obtain ⟨h1, h2, h3⟩ := andreevSharp_bounds_le b m
  rw [mul_comm, ← le_div_iff₀ (by norm_num)]
  refine abs_weight_lines_depthTwoInputs_le _ _ _ _ _ (fun j i => ?_) (fun j => ?_)
    (fun i => ?_) k a
  · exact (abs_weight_andreevSharpBottomOp_le _ i).trans h1
  · refine le_trans ?_ h2
    exact_mod_cast abs_andreevSharpTopWeight_le _
  · refine le_trans ?_ h3
    rw [le_div_iff₀ (by norm_num), mul_comm]
    exact_mod_cast abs_andreevSharpTopInput_le i

/-- **All thresholds of the circuit are polynomial in `n`**: every threshold of
`andreevSharpCircuit b m` satisfies `27 |θ| ≤ 2 n ^ 3 + 54 (n + 1) (n + 4)`, with
`n = 2 ^ b + b m`. -/
theorem abs_threshold_andreevSharpCircuit_le (k : Fin (andreevSharpCircuit b m).size) :
    27 * |((andreevSharpCircuit b m).program.lines k).op.threshold| ≤
      2 * (2 ^ b + b * m : ℝ) ^ 3 +
        54 * (((2 ^ b + b * m : ℝ) + 1) * ((2 ^ b + b * m : ℝ) + 4)) := by
  obtain ⟨h1, -, -⟩ := andreevSharp_bounds_le b m
  rw [mul_comm, ← le_div_iff₀ (by norm_num)]
  refine abs_threshold_lines_depthTwoInputs_le _ _ _ _ _ (fun j => ?_) ?_ k
  · exact (abs_threshold_andreevSharpBottomOp_le _).trans h1
  · refine le_trans ?_ h1
    have : (0 : ℝ) ≤ b * m := by positivity
    rw [abs_of_nonneg (by positivity)]
    linarith

/-- **Bottom gates of the circuit have `O(n)` input weights**, in the program's `inputWeight`
form: every gate other than the output gate has input weights of absolute value at most `2 n`. -/
theorem abs_inputWeight_andreevSharpCircuit_le {k : Fin (andreevSharpCircuit b m).size}
    (hk : (andreevSharpCircuit b m).outputs 0 ≠ .gate k) (i : Fin (2 ^ b + b * m)) :
    |inputWeight (andreevSharpCircuit b m).program k i| ≤ 2 * (2 ^ b + b * m : ℝ) := by
  obtain ⟨j, hj⟩ := inputWeight_depthTwoInputs_of_ne _ _ _ _ _ hk
  have h := congrFun hj i
  rw [argWeight_id] at h
  rw [show inputWeight (andreevSharpCircuit b m).program k i = _ from h]
  exact abs_weight_andreevSharpBottomOp_le _ i

end Magnitudes

/-! ### Size corollaries -/

section Corollaries

/-- Twice the gate count, without divisions. -/
theorem two_mul_size_andreevSharpCircuit (b m : ℕ) :
    2 * (andreevSharpCircuit b m).size =
      2 ^ b * (2 ^ b - 1) + b * 2 ^ b * (m + andreevSharpAmp m) + 4 * (2 ^ b - 1) +
        4 * andreevSharpAmp m * b + 6 * (b * m) + 2 * ((b * m + 1) / 2) + 2 := by
  obtain ⟨heven1, heven2⟩ := andreevSharp_count_even b m
  rw [size_andreevSharpCircuit, show 2 * andreevSharpAmp m * b = 2 * (andreevSharpAmp m * b) by
    ring, show 4 * andreevSharpAmp m * b = 4 * (andreevSharpAmp m * b) by ring]
  omega

/-- **Exact size at balance** (preprint, Theorem 5): if `2 ^ b = b m` and `n = 2 ^ b + b m`, then
`16 · size = 5 n² - 4 n b + 48 n - 32 b - 16`, that is,
`size = (5/16) n² - (n/4) log₂(n/2) + 3 n - 2 log₂(n/2) - 1`. -/
theorem size_andreevSharpCircuit_of_balanced {b m : ℕ} (h : 2 ^ b = b * m) :
    16 * ((andreevSharpCircuit b m).size : ℤ) =
      5 * ((2 ^ b + b * m : ℕ) : ℤ) ^ 2 - 4 * ((2 ^ b + b * m : ℕ) : ℤ) * b +
        48 * ((2 ^ b + b * m : ℕ) : ℤ) - 32 * b - 16 := by
  -- `b` divides `2 ^ b`, so it is a power of two `2 ^ j` with `j < 2 ^ j`, and `m` is even
  have hb : b ∣ 2 ^ b := ⟨m, h⟩
  obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hb
  have hjlt : j < 2 ^ j := Nat.lt_two_pow_self
  have hm : m = 2 ^ (2 ^ j - j) := by
    have hpos : 0 < 2 ^ j := by positivity
    have : 2 ^ (2 ^ j) = 2 ^ j * 2 ^ (2 ^ j - j) := by
      rw [← pow_add]; congr 1; omega
    exact (Nat.eq_of_mul_eq_mul_left hpos (h.symm.trans this))
  obtain ⟨k, hk⟩ : ∃ k, 2 ^ (2 ^ j - j) = 2 * k :=
    ⟨2 ^ (2 ^ j - j - 1), by rw [← pow_succ']; congr 1; omega⟩
  set B := 2 ^ j with hB
  have hkpos : 1 ≤ k := by
    have : 0 < 2 ^ (B - j) := by positivity
    omega
  rw [hk] at hm
  subst hm
  have hN : 2 ^ B = 2 * (B * k) := by rw [h]; ring
  have hamp : andreevSharpAmp (2 * k) = k - 1 := by
    rw [andreevSharpAmp]; omega
  have h2 := two_mul_size_andreevSharpCircuit B (2 * k)
  generalize (andreevSharpCircuit B (2 * k)).size = S at h2 ⊢
  rw [hamp, hN] at h2
  have hBpos : 1 ≤ B := Nat.one_le_two_pow
  have hBk : 1 ≤ B * k := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hdiv : (B * (2 * k) + 1) / 2 = B * k := by omega
  rw [hdiv] at h2
  have h2' : (2 * (S : ℤ)) =
      ((2 * (B * k) * (2 * (B * k) - 1) + B * (2 * (B * k)) * (2 * k + (k - 1)) +
        4 * (2 * (B * k) - 1) + 4 * (k - 1) * B + 6 * (B * (2 * k)) + 2 * (B * k) + 2 : ℕ) :
          ℤ) := by
    exact_mod_cast h2
  push_cast [Nat.cast_sub hBk, Nat.cast_sub (by omega : 1 ≤ 2 * (B * k)),
    Nat.cast_sub hkpos] at h2'
  rw [hN]
  push_cast
  linear_combination 8 * h2'

/-- **Size for `m = ⌊2 ^ b / b⌋`** (preprint, Theorem 5): with `n = 2 ^ b + b m`,
`16 · size ≤ 5 (n + b)² + 52 (n + b) + 24`, so `size ≤ (5/16) n² + O(n log n)` since
`b ≤ log₂ n` (`le_log_two_andreev_length`). More generally this holds whenever
`2 ^ b < b (m + 1)` and `b m ≤ 2 ^ b`. -/
theorem size_andreevSharpCircuit_le_of_le {b m : ℕ} (hle : b * m ≤ 2 ^ b)
    (hlt : 2 ^ b < b * (m + 1)) :
    16 * (andreevSharpCircuit b m).size ≤
      5 * (2 ^ b + b * m + b) ^ 2 + 52 * (2 ^ b + b * m + b) + 24 := by
  have h2 := two_mul_size_andreevSharpCircuit b m
  have hα := two_mul_andreevSharpAmp_le m
  set N := 2 ^ b with hN
  have hN1 : 1 ≤ N := Nat.one_le_two_pow
  have hn : 2 * N ≤ N + b * m + b := by nlinarith
  have hαb : 2 * (andreevSharpAmp m * b) ≤ N := by nlinarith
  have hdiv : 2 * ((b * m + 1) / 2) ≤ b * m + 1 := Nat.mul_div_le _ _
  have hsub1 : N * (N - 1) ≤ N * N := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have hsub2 : N - 1 ≤ N := Nat.sub_le _ _
  have hmid : b * N * (m + andreevSharpAmp m) * 2 ≤ 3 * (N * N) := by
    have : b * (m + andreevSharpAmp m) * 2 ≤ 3 * N := by nlinarith
    nlinarith
  nlinarith

/-- The block count `b` is at most `log₂ n` for `n = 2 ^ b + b m`. -/
theorem le_log_two_andreev_length (b m : ℕ) : b ≤ Nat.log 2 (2 ^ b + b * m) :=
  Nat.le_log_of_pow_le one_lt_two (Nat.le_add_right _ _)

/-- **The floor-balanced specialization** `m = ⌊2 ^ b / b⌋` (for `b ≥ 1`):
`16 · size ≤ 5 (n + b)² + 52 (n + b) + 24` with `n = 2 ^ b + b m`. -/
theorem size_andreevSharpCircuit_floor_le {b : ℕ} (hb : 1 ≤ b) :
    16 * (andreevSharpCircuit b (2 ^ b / b)).size ≤
      5 * (2 ^ b + b * (2 ^ b / b) + b) ^ 2 + 52 * (2 ^ b + b * (2 ^ b / b) + b) + 24 :=
  size_andreevSharpCircuit_le_of_le (Nat.mul_div_le _ _) (by
    have := Nat.lt_mul_div_succ (2 ^ b) (show 0 < b by omega)
    linarith)

end Corollaries

end Cslib.Circuits.Boolean.WeightedThreshold
