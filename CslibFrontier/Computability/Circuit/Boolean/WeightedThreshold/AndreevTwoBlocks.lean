/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.WeightedThreshold.AndreevSharp

/-!
# A depth-two threshold circuit for Andreev's function with two address blocks

For two address blocks, `andreevTwoBlocksCircuit m` is an explicit depth-two weighted threshold
circuit computing `andreev 2 m` on all `4 + 2 m` inputs (`computes_andreevTwoBlocksCircuit`), in
the model of `depthTwoInputs`, with exactly `4 ⌈m / 2⌉ + m` bottom gates
(`card_andreevTwoBlocksIndex`, `size_andreevTwoBlocksCircuit`). Every bottom gate sees each
address block only through its count `s_i = |a_i|`: its weights on a block are all `0` or all `1`
(`weight_andreevTwoBlocksBottomOp_blockVar`), so it is also sign-coherent
(`isSignCoherent_andreevTwoBlocksBottomOp`). All weights and thresholds are integers.
Together with `sub_one_le_of_depthTwoInputs_andreev_two`, sign-coherent circuits for two blocks
need between `m - 1` and `4 ⌈m / 2⌉ + m` bottom gates.

## The construction

Write `x_c` for the table bits, `e₀, e₁` for the unit addresses and `𝟙` for the all-ones address.
The bottom gates (`AndreevTwoBlocksIndex`) are, for `j < ⌈m / 2⌉` and each block `i`,
`[s_i + x_0 ≥ 2 (j + 1)]` and `[s_i + x_{e_{1 - i}} ≥ 2 (j + 1)]` (`andreevTwoBlocksAddr`), with
top weights `-8` and `-4`, and for `j < m` the gates `[s₀ + s₁ + x_0 ≥ 2 (j + 1)]`, with top weight
`-8`. The top gate outputs `[Ψ ≥ 13]` with
`Ψ = ∑ v_g g + 10 s₀ + 10 s₁ + 16 x_0 + 4 x_{e₀} + 3 x_{e₁} + 2 x_𝟙`.
Each staircase counts `⌊(t + y) / 2⌋` for `t ≤ T`, `y ∈ {0, 1}` and `⌈T / 2⌉` steps
(`sum_decide_two_mul_succ_le`), so `t - 2 ⌊(t + y) / 2⌋ = ± (t mod 2)` and `Ψ` depends on the
counts only through their parities (`andreevTwoBlocksTopSum_eq`); the remaining finite check is
`thirteen_le_andreevTwoBlocksTopSum_iff`.

## Correspondence with the unpublished draft (not publicly verifiable)

This is part (b) of the remark "Two address blocks" (`prop:k2`) of C. Reitwiessner,
*Depth-Two Threshold Circuits for Andreev's Function* (unpublished draft, not publicly
accessible), with all weights doubled to make them integers (the draft's top weights are
`-4, -2, -4, -2, -4`, its input coefficients `5, 5, 8, 2, 3/2, 1` and its threshold `13 / 2`).
The draft checks the finite case analysis numerically for `m ≤ 40`; here it is proved for all
`m`.

## References

* [cslib-frontier#4640](https://github.com/cslib-community/cslib-frontier/issues/4640):
  original AI-assisted work, milestone M4.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.WeightedThreshold

open BitString Finset

/-! ### Staircases with even thresholds -/

/-- **Even staircase**: `∑_{j < L} [2 (j + 1) ≤ t] = ⌊t / 2⌋` for `0 ≤ t` and `⌊t / 2⌋ ≤ L`. -/
theorem sum_decide_two_mul_succ_le {t : ℤ} {L : ℕ} (h0 : 0 ≤ t) (h : t / 2 ≤ L) :
    ∑ j : Fin L, ((decide (2 * ((j : ℤ) + 1) ≤ t)).toNat : ℤ) = t / 2 := by
  obtain ⟨t, rfl⟩ := Int.eq_ofNat_of_zero_le h0
  have hq : t / 2 ≤ L := by omega
  rw [show (t : ℤ) / 2 = ((t / 2 : ℕ) : ℤ) by omega, ← sum_decide_succ_le hq]
  exact sum_congr rfl fun j _ => by
    rw [decide_eq_decide.mpr (show 2 * ((j : ℤ) + 1) ≤ (t : ℤ) ↔ (j : ℤ) + 1 ≤ ((t / 2 : ℕ) : ℤ) by
      omega)]

/-! ### The bottom gates -/

section Gates

variable (m : ℕ)

/-- Index type of the bottom gates: `(i, r, j)` for the block staircases
`[s_i + x_{andreevTwoBlocksAddr i r} ≥ 2 (j + 1)]`, `j < ⌈m / 2⌉`, and `j < m` for the sum
staircase `[s₀ + s₁ + x_0 ≥ 2 (j + 1)]`. -/
abbrev AndreevTwoBlocksIndex : Type :=
  (Fin 2 × Bool × Fin ((m + 1) / 2)) ⊕ Fin m

/-- The table address read by the block staircase `(i, r)`: the zero address for `r = false`, the
unit address of the other block for `r = true`. -/
def andreevTwoBlocksAddr (i : Fin 2) (r : Bool) : BitString 2 :=
  if r then Pi.single i.rev true else 0

variable {m}

/-- Table coefficients of the bottom gates. -/
def andreevTwoBlocksTable : AndreevTwoBlocksIndex m → BitString 2 → ℤ
  | .inl (i, r, _) => fun c => if c = andreevTwoBlocksAddr i r then 1 else 0
  | .inr _ => fun c => if c = 0 then 1 else 0

/-- Block coefficients of the bottom gates; all lie in `{0, 1}`. -/
def andreevTwoBlocksBlock : AndreevTwoBlocksIndex m → Fin 2 → ℤ
  | .inl (i, _, _) => fun l => if l = i then 1 else 0
  | .inr _ => 1

/-- Thresholds of the bottom gates. -/
def andreevTwoBlocksThreshold : AndreevTwoBlocksIndex m → ℤ
  | .inl (_, _, j) => 2 * ((j : ℤ) + 1)
  | .inr j => 2 * ((j : ℤ) + 1)

/-- Top weights on the bottom gates. -/
def andreevTwoBlocksTopWeight : AndreevTwoBlocksIndex m → ℤ
  | .inl (_, r, _) => if r then -4 else -8
  | .inr _ => -8

/-- Top table coefficients: `16 x_0 + 4 x_{e₀} + 3 x_{e₁} + 2 x_𝟙`. -/
def andreevTwoBlocksTopTable (c : BitString 2) : ℤ :=
  (if c = 0 then 16 else 0) + (if c = Pi.single 0 true then 4 else 0) +
    (if c = Pi.single 1 true then 3 else 0) + if c = (fun _ => true) then 2 else 0

variable (m) in
/-- The weighted sum read by the top gate, for table bits `x` and block counts `s`. -/
def andreevTwoBlocksTopSum (x : BitString 2 → Bool) (s : Fin 2 → ℕ) : ℤ :=
  ∑ idx : AndreevTwoBlocksIndex m, andreevTwoBlocksTopWeight idx *
      (decide (andreevTwoBlocksThreshold idx ≤ ∑ c, andreevTwoBlocksTable idx c * (x c).toNat +
        ∑ l, andreevTwoBlocksBlock idx l * s l)).toNat +
    (∑ c, andreevTwoBlocksTopTable c * (x c).toNat + ∑ l, 10 * (s l : ℤ))

end Gates

/-! ### The top sum depends on the counts only through their parities -/

section TopSum

variable {m : ℕ}

/-- **Closed form of the top sum**: on counts at most `m`, every staircase contributes
`⌊(s + y) / 2⌋`. -/
theorem andreevTwoBlocksTopSum_eq (x : BitString 2 → Bool) (s : Fin 2 → ℕ)
    (hs : ∀ i, s i ≤ m) :
    andreevTwoBlocksTopSum m x s =
      -8 * ((((x 0).toNat : ℤ) + s 0) / 2) - 4 * ((((x (Pi.single 1 true)).toNat : ℤ) + s 0) / 2)
        - 8 * ((((x 0).toNat : ℤ) + s 1) / 2) -
        4 * ((((x (Pi.single 0 true)).toNat : ℤ) + s 1) / 2) -
        8 * ((((x 0).toNat : ℤ) + (s 0 + s 1)) / 2) + 16 * (x 0).toNat +
        4 * (x (Pi.single 0 true)).toNat + 3 * (x (Pi.single 1 true)).toNat +
        2 * (x fun _ => true).toNat + 10 * s 0 + 10 * s 1 := by
  have hblock (c : BitString 2) (i : Fin 2) :
      ∑ j : Fin ((m + 1) / 2), ((decide (2 * ((j : ℤ) + 1) ≤ ((x c).toNat : ℤ) + s i)).toNat : ℤ) =
        (((x c).toNat : ℤ) + s i) / 2 :=
    sum_decide_two_mul_succ_le (by positivity)
      (by have := hs i; have := Bool.toNat_le (x c); omega)
  have hsum : ∑ j : Fin m,
      ((decide (2 * ((j : ℤ) + 1) ≤ ((x 0).toNat : ℤ) + (s 0 + s 1))).toNat : ℤ) =
        (((x 0).toNat : ℤ) + (s 0 + s 1)) / 2 :=
    sum_decide_two_mul_succ_le (by positivity)
      (by have := hs 0; have := hs 1; have := Bool.toNat_le (x 0); omega)
  simp only [andreevTwoBlocksTopSum, Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two,
    Fintype.sum_bool, andreevTwoBlocksTopWeight, andreevTwoBlocksThreshold, andreevTwoBlocksTable,
    andreevTwoBlocksBlock, andreevTwoBlocksTopTable, andreevTwoBlocksAddr, ite_mul, one_mul,
    zero_mul, sum_ite_eq', mem_univ, ite_true, Fin.isValue,
    ← mul_sum, add_mul, sum_add_distrib, Pi.one_apply]
  have hr0 : (Fin.rev 0 : Fin 2) = 1 := rfl
  have hr1 : (Fin.rev 1 : Fin 2) = 0 := rfl
  simp only [hr0, hr1, Bool.false_eq_true, ite_false, one_ne_zero, zero_ne_one, add_zero,
    zero_add, ← mul_sum, hblock, hsum]
  ring

/-- **The finite check**: on counts at most `m`, the top sum is at least `13` exactly when the table
bit at the parities of the counts is `1`. -/
theorem thirteen_le_andreevTwoBlocksTopSum_iff (x : BitString 2 → Bool) (s : Fin 2 → ℕ)
    (hs : ∀ i, s i ≤ m) :
    13 ≤ andreevTwoBlocksTopSum m x s ↔ x (blockParities 2 s) = true := by
  rw [andreevTwoBlocksTopSum_eq x s hs]
  have h0 := Bool.toNat_le (x 0)
  have h1 := Bool.toNat_le (x (Pi.single 0 true))
  have h2 := Bool.toNat_le (x (Pi.single 1 true))
  have h3 := Bool.toNat_le (x fun _ => true)
  rcases Nat.mod_two_eq_zero_or_one (s 0) with p0 | p0 <;>
    rcases Nat.mod_two_eq_zero_or_one (s 1) with p1 | p1
  · have : blockParities 2 s = 0 := by
      funext l; fin_cases l <;> simp [blockParities, p0, p1, Bool.zero_eq_false]
    rw [this]
    cases x 0 <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> simp <;> omega
  · have : blockParities 2 s = Pi.single 1 true := by
      funext l; fin_cases l <;> simp [blockParities, p0, p1, Bool.zero_eq_false]
    rw [this]
    cases x (Pi.single 1 true) <;> simp only [Bool.toNat_false, Bool.toNat_true] <;>
      simp <;> omega
  · have : blockParities 2 s = Pi.single 0 true := by
      funext l; fin_cases l <;> simp [blockParities, p0, p1, Bool.zero_eq_false]
    rw [this]
    cases x (Pi.single 0 true) <;> simp only [Bool.toNat_false, Bool.toNat_true] <;>
      simp <;> omega
  · have : blockParities 2 s = fun _ => true := by
      funext l; fin_cases l <;> simp [blockParities, p0, p1]
    rw [this]
    cases x (fun _ => true) <;> simp only [Bool.toNat_false, Bool.toNat_true] <;>
      simp <;> omega

end TopSum

/-! ### The explicit circuit -/

section Circuit

variable (m : ℕ)

/-- The bottom gate with index `idx`: integer weights `andreevFormWeight` on all inputs and an
integer threshold. -/
noncomputable abbrev andreevTwoBlocksBottomOp (idx : AndreevTwoBlocksIndex m) : Op :=
  ⟨2 ^ 2 + 2 * m,
    fun i => (andreevFormWeight 2 m (andreevTwoBlocksTable idx) (andreevTwoBlocksBlock idx) i : ℝ),
    (andreevTwoBlocksThreshold idx : ℝ)⟩

/-- **The depth-two circuit for two address blocks** (draft remark "Two address blocks", part
(b)): the bottom gates `AndreevTwoBlocksIndex m` and a top gate reading them and the inputs, with
threshold `13`. -/
noncomputable def andreevTwoBlocksCircuit : Circuit signature (2 ^ 2 + 2 * m) 1 :=
  depthTwoInputs (fun j => andreevTwoBlocksBottomOp m ((Fintype.equivFin _).symm j)) (fun _ => id)
    (fun j => (andreevTwoBlocksTopWeight ((Fintype.equivFin _).symm j) : ℝ))
    (fun i => (andreevFormWeight 2 m andreevTwoBlocksTopTable (fun _ => 10) i : ℝ)) 13

variable {m}

/-- The circuit compares `13` with the top sum on the table bits and block counts. -/
theorem eval_andreevTwoBlocksCircuit (w : BitString (2 ^ 2 + 2 * m)) (o : Fin 1) :
    (andreevTwoBlocksCircuit m).eval interpretation w o =
      decide (13 ≤ andreevTwoBlocksTopSum m (andreevTable 2 m w) (andreevBlockCount 2 m w)) := by
  rw [andreevTwoBlocksCircuit, eval_depthTwoInputs]
  simp only [interpretation_andreevFormWeight]
  have h := sum_andreevFormWeight_mul andreevTwoBlocksTopTable (fun _ => 10) w
  have h' := congrArg (fun z : ℤ => (z : ℝ)) h
  refine decide_eq_decide.mpr ?_
  rw [← @Int.cast_le ℝ, andreevTwoBlocksTopSum,
    ← (Fintype.equivFin (AndreevTwoBlocksIndex m)).symm.sum_comp]
  push_cast at h' ⊢
  rw [← h']

/-- **`andreevTwoBlocksCircuit m` computes Andreev's function** with two address blocks on every
input. -/
theorem computes_andreevTwoBlocksCircuit (m : ℕ) :
    (andreevTwoBlocksCircuit m).Computes interpretation (single (andreev 2 m)) := by
  intro w
  funext o
  rw [eval_andreevTwoBlocksCircuit, single_apply, andreev_eq_andreevTable]
  exact Bool.eq_iff_iff.mpr (by
    rw [decide_eq_true_iff]
    exact thirteen_le_andreevTwoBlocksTopSum_iff _ _ (andreevBlockCount_le w))

/-- The circuit has depth at most `2`. -/
theorem depth_andreevTwoBlocksCircuit_le (m : ℕ) : (andreevTwoBlocksCircuit m).depth ≤ 2 :=
  depth_depthTwoInputs_le ..

/-- **Exact gate count**: `4 ⌈m / 2⌉ + m` bottom gates. -/
theorem card_andreevTwoBlocksIndex (m : ℕ) :
    Fintype.card (AndreevTwoBlocksIndex m) = 4 * ((m + 1) / 2) + m := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  ring

/-- **Size of the circuit**: `4 ⌈m / 2⌉ + m` bottom gates and one top gate. -/
theorem size_andreevTwoBlocksCircuit (m : ℕ) :
    (andreevTwoBlocksCircuit m).size = 4 * ((m + 1) / 2) + m + 1 := by
  rw [andreevTwoBlocksCircuit, size_depthTwoInputs, card_andreevTwoBlocksIndex]

end Circuit

/-! ### Weights -/

section Weights

variable {m : ℕ}

/-- Every block coefficient of a bottom gate is `0` or `1`. -/
theorem andreevTwoBlocksBlock_eq_zero_or_one (idx : AndreevTwoBlocksIndex m) (l : Fin 2) :
    andreevTwoBlocksBlock idx l = 0 ∨ andreevTwoBlocksBlock idx l = 1 := by
  rcases idx with ⟨i, _, _⟩ | _ <;> simp only [andreevTwoBlocksBlock] <;> (try split_ifs) <;> simp

/-- **Block-symmetric bottom gates**: a bottom gate gives every bit of block `l` the same weight
`andreevTwoBlocksBlock idx l ∈ {0, 1}`, so it sees the block only through its count. -/
theorem weight_andreevTwoBlocksBottomOp_blockVar (idx : AndreevTwoBlocksIndex m) (l : Fin 2)
    (t : Fin m) :
    (andreevTwoBlocksBottomOp m idx).weight (andreevBlockVar 2 m l t) =
      andreevTwoBlocksBlock idx l := by
  simp only [andreevFormWeight_blockVar]

/-- **Every bottom gate is sign-coherent** for Andreev's blocks. -/
theorem isSignCoherent_andreevTwoBlocksBottomOp (idx : AndreevTwoBlocksIndex m) :
    IsSignCoherent (andreevBlockVar 2 m) (argWeight (andreevTwoBlocksBottomOp m idx) id) := by
  rw [argWeight_id]
  exact isSignCoherent_andreevFormWeight _ _ (andreevTwoBlocksBlock_eq_zero_or_one idx)

end Weights

end Cslib.Circuits.Boolean.WeightedThreshold
