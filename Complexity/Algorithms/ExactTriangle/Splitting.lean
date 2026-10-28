/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.ExactTriangle.Hashing
public import Complexity.Algorithms.ExactTriangle.Lopsided
public import Complexity.Foundations.Data.Matrix.PairChunks
public import Complexity.Foundations.Data.Nat.SqrtRatio
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp

/-!
# Modular splitting of Exact Triangle into finite lopsided queries

Pieces of the third part and chunks of A–B residue classes define lopsided graphs with a
middle vertex `(c, label)`. The three input matrices retain their original orientations.
All bounds below use `16 ≤ D ≤ n` and `1 ≤ g`; the sharper degree bound also uses `g ≤ sqrt D`.
No native program, fast solver or charged instruction bound is asserted.

## Main definitions

* `piece`, `residueClass`, `chunkOf`: vertex blocks and residue query chunks.
* `lopInstance`, `instanceIndices`, `totalChunks`: lopsided graphs and their finite indices.

## Main results

* `existsUnique_mem_piece`, `card_piece_le`: unique piece coverage and size.
* `totalChunks_le`, `card_instanceIndices_le`: chunk and instance bounds.
* `card_middle_lopInstance`, `hasCommonNeighbor_lopInstance_iff`: size and modular correctness.
* `ncard_nbr_lopInstance_le`: degree bound.

## References

The reduction is part of [AlmanWilliams2026, Section 3]. Direct adaptation of
[Instances.lean](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Sec3/Theorem17/Instances.lean), with only required definitions from
`PaperStatements.lean`, [Chunks.lean](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Sec3/Chunks.lean) and [Parameters.lean](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Sec3/Parameters.lean), at
`anthropics/formal-math@16a5ce41304fcdaea4e0be7c132e1c361dc26da5`.
Quoted docstring fragments reproduce comments in the pinned formal source; other prose describes
the local Lean API.
-/

@[expose] public section

namespace Cslib.Algorithms.ExactTriangle

open Cslib.Matrix

/-- The largest number of query pairs that is "at most n²/√D" (Corollary 15 and Theorem 17;
Theorem 5 has "at most N²/√D"): `⌊n²/√D⌋`. -/
def queryCap (n D : ℕ) : ℕ := Nat.sqrt ((n ^ 2) ^ 2 / D)

/-- The integer capacity is exactly the real-valued floor used in the reduction. -/
theorem queryCap_eq_floor (n D : ℕ) : queryCap n D = ⌊(n : ℝ) ^ 2 / Real.sqrt D⌋₊ := by
  rw [queryCap, Nat.sqrt_div_eq_floor_div_sqrt]
  norm_cast

/-- Proof of Theorem 17: "let s := ⌊√D⌋". -/
def sOf (D : ℕ) : ℕ := Nat.sqrt D

/-- Proof of Theorem 17: the bound "⌈s/g⌉" on the number of vertices of a piece. -/
def pieceSize (D g : ℕ) : ℕ := sOf D ⌈/⌉ g

/-- The integer block size equals the real ceiling, also at the zero-divisor convention. -/
theorem pieceSize_eq_ceil (D g : ℕ) : pieceSize D g = ⌈(sOf D : ℝ) / (g : ℝ)⌉₊ := by
  by_cases hg : g = 0
  · simp [pieceSize, hg]
  exact (Nat.ceil_div_eq_ceilDiv _ (Nat.pos_of_ne_zero hg)).symm

/-- Proof of Theorem 17: "split C into pieces C₁, …, C_h of at most ⌈s/g⌉ vertices each".  The paper
does not say how; we take blocks of `⌈s/g⌉` consecutive vertices.  `piece n D g k` is the paper's
`C_{k+1}`. -/
def piece (n D g k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun c : Fin n => c.val / pieceSize D g = k

/-- Proof of Theorem 17: the number `h` of pieces, `⌈n / ⌈s/g⌉⌉` for the blocks of `piece`
(meaningful when `⌈s/g⌉ ≥ 1`). -/
def numPieces (n D g : ℕ) : ℕ := n ⌈/⌉ pieceSize D g

/-- The number of blocks is the ceiling of the real quotient by the block size. -/
theorem numPieces_eq_ceil (n D g : ℕ) :
    numPieces n D g = ⌈(n : ℝ) / (pieceSize D g : ℝ)⌉₊ := by
  by_cases h : pieceSize D g = 0
  · simp [numPieces, h]
  exact (Nat.ceil_div_eq_ceilDiv _ (Nat.pos_of_ne_zero h)).symm

/-- The index of an instance built by the reduction of Theorem 17: a residue `ϱ ∈ ℤ_p`, the number
`j` of a chunk of `W_ϱ`, and the number `k` of a piece of `C`. -/
abbrev InstanceIndex (p : ℕ) : Type := Fin p × ℕ × ℕ


/-- Proof of Theorem 17: "For ϱ ∈ ℤ_p let W_ϱ be the set of edges (a,b) ∈ A × B with w(a,b) ≡ ϱ (mod
p)". -/
def residueClass {n : ℕ} (wAB : Fin n → Fin n → ℤ) (p : ℕ) (ϱ : Fin p) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun q : Fin n × Fin n => wAB q.1 q.2 ≡ ((ϱ : ℕ) : ℤ) [ZMOD (p : ℤ)]

/-- Proof of Theorem 17: "and cut it into chunks of at most n²/√D query pairs".  The `j`-th chunk of
`W_ϱ`. -/
def chunkOf {n : ℕ} (wAB : Fin n → Fin n → ℤ) (D p : ℕ) (ϱ : Fin p) (j : ℕ) :
    Finset (Fin n × Fin n) :=
  chunk (residueClass wAB p ϱ) (queryCap n D) j

/-- Proof of Theorem 17: "For each chunk 𝒬 ⊆ W_ϱ and each piece C_k form the instance of
Lop-AE-SparseTri(n, D) with query pairs W := 𝒬 and middle part C_k × ℤ_p [...], whose middle
vertices are pairs (vertex, label) [...], with a ∼ (c, σ) ⟺ σ ≡ w(a,c) + ϱ,   (c, σ) ∼ b ⟺ σ ≡
−w(b,c)   (mod p)." -/
def lopInstance {n : ℕ} (wAB wBC wAC : Fin n → Fin n → ℤ) (D g p : ℕ) :
    InstanceIndex p → LopsidedGraph n
  | (ϱ, j, k) =>
    { M := {c : Fin n // c ∈ piece n D g k} × Fin p
      adjA := fun a (c, σ) => ((σ : ℕ) : ℤ) ≡ wAC a c + ((ϱ : ℕ) : ℤ) [ZMOD (p : ℤ)]
      adjB := fun (c, σ) b => ((σ : ℕ) : ℤ) ≡ -wBC b c [ZMOD (p : ℤ)]
      W := chunkOf wAB D p ϱ j }

/-- Proof of Theorem 17: "For each chunk 𝒬 ⊆ W_ϱ and each piece C_k" there is an instance; these
are the indices of all the instances. This set depends only on the Exact Triangle instance and on
`D`, `g`, `p`, not on any answer of the oracle. -/
def instanceIndices {n : ℕ} (wAB : Fin n → Fin n → ℤ) (D g p : ℕ) :
    Finset (InstanceIndex p) :=
  Finset.univ.biUnion fun ϱ : Fin p =>
    ((Finset.range (numChunks (residueClass wAB p ϱ) (queryCap n D))) ×ˢ
      (Finset.range (numPieces n D g))).image fun jk => (ϱ, jk)

/-- Total number of query chunks, summed over residues. -/
def totalChunks {n : ℕ} (wAB : Fin n → Fin n → ℤ) (D p : ℕ) : ℕ :=
  ∑ ϱ : Fin p, numChunks (residueClass wAB p ϱ) (queryCap n D)

variable {n : ℕ}

/-- The bound `⌊n²/√D⌋` on the size of a chunk is at least 1, because `√D ≤ n ≤ n²`. -/
theorem one_le_queryCap {D : ℕ} (hD : 1 ≤ D) (hDn : D ≤ n) : 1 ≤ queryCap n D := by
  rw [queryCap_eq_floor]
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast hD.trans hDn
  refine Nat.le_floor ?_
  rw [Nat.cast_one, le_div_iff₀ (Real.sqrt_pos.mpr (by exact_mod_cast hD)), one_mul]
  have hsqrt : Real.sqrt (D : ℝ) ≤ D :=
    Real.sqrt_le_self_iff.mpr (Or.inr (by exact_mod_cast hD))
  exact (hsqrt.trans (by exact_mod_cast hDn)).trans (le_self_pow₀ hn two_ne_zero)

variable {n D g p : ℕ}

/-! ### The pieces -/

/-- `s = ⌊√D⌋ ≤ √D`. -/
theorem sOf_le_sqrt (D : ℕ) : (sOf D : ℝ) ≤ Real.sqrt D :=
  Real.nat_sqrt_le_real_sqrt

/-- `√D < s + 1`. -/
theorem sqrt_lt_sOf_add_one (D : ℕ) : Real.sqrt D < (sOf D : ℝ) + 1 :=
  Real.real_sqrt_lt_nat_sqrt_succ

/-- `s > 0` because `D ≥ 16`. -/
private theorem sOf_pos (hD : 16 ≤ D) : (0 : ℝ) < sOf D := by
  linarith [Real.four_le_sqrt_natCast hD, sqrt_lt_sOf_add_one D]

/-- The bound `⌈s/g⌉` on the size of a piece is at least 1. -/
theorem pieceSize_pos (hD : 16 ≤ D) (hg1 : 1 ≤ g) : 0 < pieceSize D g := by
  rw [pieceSize_eq_ceil]
  exact Nat.ceil_pos.mpr (div_pos (sOf_pos hD) (by exact_mod_cast hg1))

/-- `⌈s/g⌉ ≤ s` because `g ≥ 1`. -/
theorem pieceSize_le_sOf (hg1 : 1 ≤ g) : pieceSize D g ≤ sOf D := by
  rw [pieceSize_eq_ceil]
  exact Nat.ceil_le.mpr (div_le_self (Nat.cast_nonneg _) (by exact_mod_cast hg1))

/-- A vertex lies in the piece number `k` exactly if its number divided by `⌈s/g⌉` is `k`. -/
theorem mem_piece {k : ℕ} (c : Fin n) : c ∈ piece n D g k ↔ c.val / pieceSize D g = k := by
  simp [piece]

/-- Proof of Theorem 17: "split C into pieces C₁, …, C_h of at most ⌈s/g⌉ vertices each": every
vertex of `C` lies in exactly one of the `h` pieces. -/
theorem existsUnique_mem_piece (hD : 16 ≤ D) (hg1 : 1 ≤ g) (c : Fin n) :
    ∃! k, k < numPieces n D g ∧ c ∈ piece n D g k := by
  refine ⟨c.val / pieceSize D g, ⟨?_, (mem_piece c).mpr rfl⟩,
    fun k hk => ((mem_piece c).mp hk.2).symm⟩
  rw [numPieces_eq_ceil]
  refine Nat.lt_ceil.mpr (lt_of_le_of_lt Nat.cast_div_le ?_)
  exact div_lt_div_of_pos_right (by exact_mod_cast c.isLt)
    (by exact_mod_cast pieceSize_pos hD hg1)

/-- Proof of Theorem 17, "pieces [...] of at most ⌈s/g⌉ vertices each": `|C_k| ≤ ⌈s/g⌉`, because the
numbers of the vertices of the piece number `k` lie in `[k ⌈s/g⌉, (k + 1) ⌈s/g⌉)`. -/
theorem card_piece_le (hD : 16 ≤ D) (hg1 : 1 ≤ g) (n k : ℕ) :
    (piece n D g k).card ≤ pieceSize D g :=
  Finset.univ.card_filter_div_eq_le (fun _ _ _ _ h => Fin.ext h) (pieceSize_pos hD hg1) k

/-- Proof of Theorem 17: "so that h ≤ ⌈ng/s⌉". -/
theorem numPieces_le (hD : 16 ≤ D) (hg1 : 1 ≤ g) :
    numPieces n D g ≤ ⌈(n : ℝ) * (g : ℝ) / (sOf D : ℝ)⌉₊ := by
  have hsize : (0 : ℝ) < pieceSize D g := by exact_mod_cast pieceSize_pos hD hg1
  have hg : (0 : ℝ) < g := by exact_mod_cast hg1
  -- `s ≤ ⌈s/g⌉ g`
  have hs' : (sOf D : ℝ) / (g : ℝ) ≤ pieceSize D g := by
    rw [pieceSize_eq_ceil]
    exact Nat.le_ceil _
  have hs := (div_le_iff₀ hg).mp hs'
  rw [numPieces_eq_ceil]
  refine Nat.ceil_mono ?_
  rw [div_le_div_iff₀ hsize (sOf_pos hD)]
  calc (n : ℝ) * (sOf D : ℝ) ≤ (n : ℝ) * ((pieceSize D g : ℝ) * (g : ℝ)) := by gcongr
    _ = (n : ℝ) * (g : ℝ) * (pieceSize D g : ℝ) := by ring

/-! ### Residues -/

/-- The residue of the integer `x` modulo `p`, as an element of `Fin p`. -/
def resFin (hp : p ≠ 0) (x : ℤ) : Fin p :=
  ⟨x.natMod p, Int.natMod_lt hp⟩

/-- The residue of `x` is congruent to `x`. -/
theorem resFin_modEq (hp : p ≠ 0) (x : ℤ) : ((resFin hp x : ℕ) : ℤ) ≡ x [ZMOD (p : ℤ)] := by
  change ((x % (p : ℤ)).toNat : ℤ) ≡ x [ZMOD (p : ℤ)]
  rw [Int.natCast_toNat_emod (Nat.pos_of_ne_zero hp)]
  exact Int.mod_modEq x p

/-- An element of `Fin p` is congruent to `x` modulo `p` exactly if it is the residue of `x`. -/
private theorem modEq_iff_eq_resFin (hp : p ≠ 0) (σ : Fin p) (x : ℤ) :
    ((σ : ℕ) : ℤ) ≡ x [ZMOD (p : ℤ)] ↔ σ = resFin hp x := by
  refine ⟨fun h => ?_, fun h => h ▸ resFin_modEq hp x⟩
  -- Two congruent numbers in `{0, …, p − 1}` are equal.
  have hmod : (σ : ℕ) ≡ (resFin hp x : ℕ) [MOD p] :=
    (Int.natCast_modEq_iff).mp (h.trans (resFin_modEq hp x).symm)
  exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt hmod σ.isLt (resFin hp x).isLt)

/-! ### The arithmetic behind the two counts -/

/-- The number `⌈|S|/cap⌉` of chunks of `S` satisfies `⌈|S|/cap⌉ cap ≤ |S| + cap − 1`. -/
private theorem numChunks_mul_le (S : Finset (Fin n × Fin n)) (cap : ℕ) (hcap : 1 ≤ cap) :
    numChunks S cap * cap + 1 ≤ S.card + cap := by
  rw [numChunks]
  exact Nat.ceilDiv_mul_lt hcap

/-- `s + 1` exceeds `√D` by at least `1/(2√D + 1)`: since `(s + 1)²` and `D` are integers,
`1 ≤ (s + 1)² − D = (s + 1 − √D)(s + 1 + √D)`. -/
private theorem one_le_gap_mul (D : ℕ) :
    1 ≤ ((sOf D : ℝ) + 1 - Real.sqrt D) * (2 * Real.sqrt D + 1) := by
  have hsq : Real.sqrt D ^ 2 = D := Real.sq_sqrt (Nat.cast_nonneg D)
  have hle := sOf_le_sqrt D
  have hlt := sqrt_lt_sOf_add_one D
  have hinteger : (D : ℝ) + 1 ≤ ((sOf D : ℝ) + 1) ^ 2 := by
    have hreal : (D : ℝ) < ((sOf D : ℝ) + 1) ^ 2 :=
      hsq ▸ pow_lt_pow_left₀ hlt (Real.sqrt_nonneg _) two_ne_zero
    have hnat : D < (sOf D + 1) ^ 2 := by exact_mod_cast hreal
    exact_mod_cast hnat
  calc (1 : ℝ) ≤ ((sOf D : ℝ) + 1) ^ 2 - Real.sqrt D ^ 2 := by linarith [hinteger, hsq]
    _ = ((sOf D : ℝ) + 1 - Real.sqrt D) * ((sOf D : ℝ) + 1 + Real.sqrt D) := by ring
    _ ≤ ((sOf D : ℝ) + 1 - Real.sqrt D) * (2 * Real.sqrt D + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)

/-- The inequality behind "at most p + √D [...] chunks": `n² < (s + 1) ⌊n²/√D⌋ + p`.

Write `r = √D`, `x = n²/r` and `δ = s + 1 − r`.  Then
`(s + 1)⌊x⌋ > (s + 1)(x − 1) = n² + xδ − (s + 1)`, so it is enough that `xδ ≥ r/2 + 1 ≥ s + 1 − p`.
This holds because `x ≥ r³` (as `D ≤ n`), `δ ≥ 1/(2r + 1)` (as `D` is an integer) and `r ≥ 4`. -/
private theorem sq_lt_mul_queryCap_add (hD : 16 ≤ D) (hDn : D ≤ n)
    (hp : Real.sqrt D / 2 ≤ (p : ℝ)) : n ^ 2 < (sOf D + 1) * queryCap n D + p := by
  have hgap := one_le_gap_mul D
  have hs := sOf_le_sqrt D
  set r := Real.sqrt D with hr
  set δ := (sOf D : ℝ) + 1 - r with hδ
  set x := (n : ℝ) ^ 2 / r with hx
  have hr4 : 4 ≤ r := Real.four_le_sqrt_natCast hD
  have hxr : x * r = (n : ℝ) ^ 2 := div_mul_cancel₀ _ (by linarith)
  have hx3 : r ^ 3 ≤ x := by
    rw [hx, le_div_iff₀ (by linarith)]
    calc r ^ 3 * r = (r ^ 2) ^ 2 := by ring
      _ = (D : ℝ) ^ 2 := by rw [hr, Real.sq_sqrt (Nat.cast_nonneg D)]
      _ ≤ (n : ℝ) ^ 2 := by gcongr
  have hxδ : r / 2 + 1 ≤ x * δ := by
    refine le_of_mul_le_mul_right ?_ (show 0 < 2 * r + 1 by linarith)
    calc (r / 2 + 1) * (2 * r + 1) ≤ r ^ 3 := by
          -- `r³ ≥ 4r²` and `r² ≥ 4r`
          linarith [mul_le_mul_of_nonneg_right hr4 (sq_nonneg r),
            mul_le_mul_of_nonneg_right hr4 (show 0 ≤ r by linarith)]
      _ ≤ x * 1 := by rw [mul_one]; exact hx3
      _ ≤ x * (δ * (2 * r + 1)) :=
          mul_le_mul_of_nonneg_left hgap (le_trans (by positivity) hx3)
      _ = x * δ * (2 * r + 1) := by ring
  have hfloor : x < (queryCap n D : ℝ) + 1 := by
    rw [queryCap_eq_floor]
    exact Nat.lt_floor_add_one _
  have hmain : (n : ℝ) ^ 2 < ((sOf D : ℝ) + 1) * (queryCap n D : ℝ) + p :=
    calc (n : ℝ) ^ 2 = x * r := hxr.symm
      _ ≤ x * r + x * δ - ((sOf D : ℝ) + 1) + r / 2 := by
          -- `s + 1 ≤ r + 1 ≤ xδ + r/2`
          linarith [hxδ, hs]
      _ = ((sOf D : ℝ) + 1) * (x - 1) + r / 2 := by rw [hδ]; ring
      _ < ((sOf D : ℝ) + 1) * (queryCap n D : ℝ) + p :=
          add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left (by linarith [hfloor]) (by positivity)) hp
  exact_mod_cast hmain

/-- Proof of Theorem 17: the two facts used for the count of the instances, "s ≥ √D − 1 ≥ 3√D/4
because D ≥ 16, and √D ≤ √n ≤ 2n/3 because D ≤ n and we may assume n ≥ 3". -/
theorem le_sOf_and_sqrt_le (hD : 16 ≤ D) (hDn : D ≤ n) :
    3 * Real.sqrt D / 4 ≤ (sOf D : ℝ) ∧ Real.sqrt D ≤ 2 * (n : ℝ) / 3 := by
  have hsqrtD := Real.four_le_sqrt_natCast hD
  have hsqrtn := Real.four_le_sqrt_natCast (hD.trans hDn)
  constructor
  · calc 3 * Real.sqrt D / 4 ≤ Real.sqrt D - 1 := by linarith
      _ ≤ (sOf D : ℝ) := by linarith [sqrt_lt_sOf_add_one D]
  · calc Real.sqrt D ≤ Real.sqrt n := Real.sqrt_le_sqrt (by exact_mod_cast hDn)
      _ ≤ 2 * (n : ℝ) / 3 := by
          -- `n = √n √n ≥ 4√n`
          linarith [mul_le_mul_of_nonneg_right hsqrtn (Real.sqrt_nonneg n),
            Real.mul_self_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

section Matrices

variable (wAB wBC wAC : Fin n → Fin n → ℤ)

/-! ### The sets `W_ϱ` -/

/-- A pair lies in `W_ϱ` exactly if `ϱ` is the residue of its weight. -/
theorem mem_residueClass (hp : p ≠ 0) (ϱ : Fin p) (q : Fin n × Fin n) :
    q ∈ residueClass wAB p ϱ ↔ ϱ = resFin hp (wAB q.1 q.2) := by
  rw [← modEq_iff_eq_resFin]
  simp only [residueClass, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨Int.ModEq.symm, Int.ModEq.symm⟩

/-- Proof of Theorem 17, the sets `W_ϱ` for `ϱ ∈ ℤ_p`: every pair `(a,b) ∈ A × B` lies in exactly
one of them. -/
theorem existsUnique_mem_residueClass (hp : p ≠ 0) (q : Fin n × Fin n) :
    ∃! ϱ : Fin p, q ∈ residueClass wAB p ϱ :=
  ⟨resFin hp (wAB q.1 q.2), (mem_residueClass wAB hp _ q).mpr rfl,
    fun ϱ hϱ => (mem_residueClass wAB hp ϱ q).mp hϱ⟩

/-- The sets `W_ϱ` have `n²` pairs in all. -/
private theorem sum_card_residueClass (hp : p ≠ 0) :
    ∑ ϱ : Fin p, (residueClass wAB p ϱ).card = n ^ 2 := by
  calc ∑ ϱ : Fin p, (residueClass wAB p ϱ).card
      = ∑ ϱ : Fin p, ((Finset.univ : Finset (Fin n × Fin n)).filter
          fun q => resFin hp (wAB q.1 q.2) = ϱ).card := by
        refine Finset.sum_congr rfl fun ϱ _ => congrArg Finset.card ?_
        ext q
        rw [mem_residueClass wAB hp]
        simp [eq_comm]
    _ = (Finset.univ : Finset (Fin n × Fin n)).card :=
        (Finset.card_eq_sum_card_fiberwise fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)).symm
    _ = n ^ 2 := by simp [sq]

/-! ### The chunks -/

/-- Proof of Theorem 17: "cut it into chunks of at most n²/√D query pairs".  (The chunks of `W_ϱ`
cover it: `biUnion_chunk`.) -/
theorem card_chunkOf_le (hD : 1 ≤ D) (hDn : D ≤ n) (ϱ : Fin p) (j : ℕ) :
    ((chunkOf wAB D p ϱ j).card : ℝ) ≤ (n : ℝ) ^ 2 / Real.sqrt D :=
  calc ((chunkOf wAB D p ϱ j).card : ℝ) ≤ (queryCap n D : ℝ) := by
        exact_mod_cast card_chunk_le _ (one_le_queryCap hD hDn) j
    _ ≤ (n : ℝ) ^ 2 / Real.sqrt D := by
        rw [queryCap_eq_floor]
        exact Nat.floor_le (by positivity)

/-- There are at most `p + s` chunks in all.  Each `W_ϱ` has at most `(|W_ϱ| + cap − 1)/cap` chunks,
where `cap = ⌊n²/√D⌋`, so `p + s + 1` chunks or more would need `n² ≥ (s + 1) cap + p` pairs. -/
private theorem totalChunks_le_add_sOf (hD : 16 ≤ D) (hDn : D ≤ n) (hp0 : p ≠ 0)
    (hp : Real.sqrt D / 2 ≤ (p : ℝ)) : totalChunks wAB D p ≤ p + sOf D := by
  have hsum : totalChunks wAB D p * queryCap n D + p ≤ n ^ 2 + p * queryCap n D := by
    have h := Finset.sum_le_sum fun ϱ (_ : ϱ ∈ (Finset.univ : Finset (Fin p))) =>
      numChunks_mul_le (residueClass wAB p ϱ) (queryCap n D) (one_le_queryCap (by omega) hDn)
    simp only [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_one] at h
    rwa [sum_card_residueClass wAB hp0] at h
  have hpairs := sq_lt_mul_queryCap_add hD hDn hp
  by_contra hmany
  have hmul : (p + sOf D + 1) * queryCap n D ≤ totalChunks wAB D p * queryCap n D :=
    Nat.mul_le_mul_right _ (by omega)
  rw [show (p + sOf D + 1) * queryCap n D = p * queryCap n D + (sOf D + 1) * queryCap n D by
    ring] at hmul
  -- `hsum` and `hmul` give `(s + 1) cap + p ≤ n²`, against `hpairs`.
  omega

/-- Proof of Theorem 17: "There are at most p + √D ≤ 2√D chunks in all."

NOTE.  A chunk holds a whole number of pairs, at most `⌊n²/√D⌋`, so the count is at most
`p + (n² − p)/⌊n²/√D⌋`, and the second term can exceed `√D` slightly.  The printed bound is still
true, because the count is an integer, `D` is an integer and `D ≤ n` (`sq_lt_mul_queryCap_add`). -/
theorem totalChunks_le (hD : 16 ≤ D) (hDn : D ≤ n) (hp : p ∈ Nat.sqrtPrimeWindow D) :
    (totalChunks wAB D p : ℝ) ≤ (p : ℝ) + Real.sqrt D ∧
    (p : ℝ) + Real.sqrt D ≤ 2 * Real.sqrt D := by
  obtain ⟨hprime, hge, hlt⟩ := Nat.mem_sqrtPrimeWindow.mp hp
  have hnat : (totalChunks wAB D p : ℝ) ≤ (p : ℝ) + (sOf D : ℝ) := by
    exact_mod_cast totalChunks_le_add_sOf wAB hD hDn hprime.ne_zero hge
  exact ⟨by linarith [sOf_le_sqrt D], by linarith⟩

/-! ### The instances -/

/-- Proof of Theorem 17: "middle part C_k × ℤ_p, of size at most sp ≤ D".  So each instance is an
instance of Lop-AE-SparseTri(n, D). -/
theorem card_middle_lopInstance (hD : 16 ≤ D) (hg1 : 1 ≤ g) (hp : p ∈ Nat.sqrtPrimeWindow D)
    (ι : InstanceIndex p) : Fintype.card (lopInstance wAB wBC wAC D g p ι).M ≤ D := by
  obtain ⟨-, -, hlt⟩ := Nat.mem_sqrtPrimeWindow.mp hp
  have hsp : (sOf D : ℝ) * (p : ℝ) ≤ D :=
    calc (sOf D : ℝ) * (p : ℝ) ≤ Real.sqrt D * Real.sqrt D :=
          mul_le_mul (sOf_le_sqrt D) hlt.le (Nat.cast_nonneg p) (Real.sqrt_nonneg _)
      _ = D := Real.mul_self_sqrt (Nat.cast_nonneg D)
  calc Fintype.card ({c : Fin n // c ∈ piece n D g ι.2.2} × Fin p)
      = (piece n D g ι.2.2).card * p := by
        rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin]
    _ ≤ sOf D * p := Nat.mul_le_mul_right p
        ((card_piece_le hD hg1 n ι.2.2).trans (pieceSize_le_sOf hg1))
    _ ≤ D := by exact_mod_cast hsp

/-- A query pair of the instance with index `(ϱ, j, k)` lies in `W_ϱ`, and `j` is the number of its
chunk. -/
theorem mem_lopInstance_W {wAB wBC wAC : Fin n → Fin n → ℤ}
    {ι : InstanceIndex p} {q : Fin n × Fin n}
    (hq : q ∈ (lopInstance wAB wBC wAC D g p ι).W) :
    q ∈ residueClass wAB p ι.1 ∧ rankIn (residueClass wAB p ι.1) q / queryCap n D = ι.2.1 :=
  Finset.mem_filter.mp hq

/-- Proof of Theorem 17: "Within the chunk, the condition S(a,b,c) ≡ 0 (mod p) has become the
equality w(a,c) + ϱ ≡ −w(b,c) of a label of (a,c) and a label of (b,c)". -/
theorem weightSum_modEq_zero_iff {p ϱ : ℤ} {a b : Fin n} (hϱ : wAB a b ≡ ϱ [ZMOD p]) (c : Fin n) :
    weightSum wAB wBC wAC a b c ≡ 0 [ZMOD p] ↔ wAC a c + ϱ ≡ -wBC b c [ZMOD p] := by
  rw [Int.modEq_iff_dvd, Int.modEq_iff_dvd,
    show 0 - weightSum wAB wBC wAC a b c = -wBC b c - (wAC a c + ϱ) + (ϱ - wAB a b) by
      simp only [weightSum]; ring]
  exact dvd_add_left (Int.modEq_iff_dvd.mp hϱ)

/-- Proof of Theorem 17: "a query pair (a,b) ∈ 𝒬 has a common neighbor if and only if some c ∈ C_k
has S(a,b,c) ≡ 0 (mod p)". -/
theorem hasCommonNeighbor_lopInstance_iff (hp : p ≠ 0)
    {ι : InstanceIndex p} {q : Fin n × Fin n}
    (hq : q ∈ (lopInstance wAB wBC wAC D g p ι).W) :
    (lopInstance wAB wBC wAC D g p ι).HasCommonNeighbor q.1 q.2 ↔
      ∃ c ∈ piece n D g ι.2.2, weightSum wAB wBC wAC q.1 q.2 c ≡ 0 [ZMOD (p : ℤ)] := by
  have hϱ : wAB q.1 q.2 ≡ ((ι.1 : ℕ) : ℤ) [ZMOD (p : ℤ)] :=
    (Finset.mem_filter.mp (mem_lopInstance_W hq).1).2
  constructor
  · -- A common neighbor `(c, σ)` carries the label `σ` of `(a,c)` and of `(b,c)`.
    rintro ⟨⟨c, σ⟩, hA, hB⟩
    exact ⟨c, c.2, (weightSum_modEq_zero_iff wAB wBC wAC hϱ c).mpr (hA.symm.trans hB)⟩
  · -- If the two labels agree, the vertex `c` with that label is a common neighbor.
    rintro ⟨c, hc, hS⟩
    have hB := resFin_modEq hp (-wBC q.2 c)
    exact ⟨(⟨c, hc⟩, resFin hp (-wBC q.2 c)),
      hB.trans ((weightSum_modEq_zero_iff wAB wBC wAC hϱ c).mp hS).symm, hB⟩

/-- Proof of Theorem 17, "For each chunk 𝒬 ⊆ W_ϱ and each piece C_k": `(ϱ, j, k)` is the index of an
instance exactly if `j` is the number of a chunk of `W_ϱ` and `k` the number of a piece. -/
theorem mem_instanceIndices (ι : InstanceIndex p) :
    ι ∈ instanceIndices wAB D g p ↔
      ι.2.1 < numChunks (residueClass wAB p ι.1) (queryCap n D) ∧ ι.2.2 < numPieces n D g := by
  obtain ⟨ϱ, j, k⟩ := ι
  simp only [instanceIndices, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_image, Finset.mem_product, Finset.mem_range, Prod.mk.injEq, Prod.exists]
  exact ⟨fun ⟨_, _, _, h, h1, h2, h3⟩ => by subst h1 h2 h3; exact h,
    fun h => ⟨ϱ, j, k, h, rfl, rfl, rfl⟩⟩

/-- There are as many instances as chunks times pieces. -/
theorem card_instanceIndices (D g p : ℕ) :
    (instanceIndices wAB D g p).card = totalChunks wAB D p * numPieces n D g := by
  unfold instanceIndices totalChunks
  rw [Finset.card_biUnion, Finset.sum_mul]
  · refine Finset.sum_congr rfl fun ϱ _ => ?_
    rw [Finset.card_image_of_injective _ (Prod.mk_right_injective ϱ), Finset.card_product,
      Finset.card_range, Finset.card_range]
  · intro ϱ _ ϱ' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨_, _, h⟩ := Finset.mem_image.mp hx'
    exact hne (congrArg Prod.fst h).symm

/-- Proof of Theorem 17: "There are at most 2√D h ≤ 2√D(ng/s + 1) ≤ 4ng instances". -/
theorem card_instanceIndices_le (hD : 16 ≤ D) (hDn : D ≤ n) (hg1 : 1 ≤ g)
    (hp : p ∈ Nat.sqrtPrimeWindow D) :
    ((instanceIndices wAB D g p).card : ℝ) ≤ 4 * (n : ℝ) * (g : ℝ) := by
  obtain ⟨hs, hsqrt⟩ := le_sOf_and_sqrt_le hD hDn
  obtain ⟨hchunks, hchunks'⟩ := totalChunks_le wAB hD hDn hp
  have hs0 := sOf_pos hD
  have hpieces : (numPieces n D g : ℝ) ≤ (n : ℝ) * (g : ℝ) / (sOf D : ℝ) + 1 :=
    calc (numPieces n D g : ℝ) ≤ (⌈(n : ℝ) * (g : ℝ) / (sOf D : ℝ)⌉₊ : ℝ) := by
          exact_mod_cast numPieces_le hD hg1
      _ ≤ (n : ℝ) * (g : ℝ) / (sOf D : ℝ) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  -- `2√D · ng/s ≤ 8ng/3` because `s ≥ 3√D/4`, and `2√D ≤ 4n/3 ≤ 4ng/3`.
  have hmain :
      Real.sqrt D * ((n : ℝ) * (g : ℝ) / (sOf D : ℝ)) ≤ 4 / 3 * ((n : ℝ) * (g : ℝ)) := by
    rw [← mul_div_assoc, div_le_iff₀ hs0]
    calc Real.sqrt D * ((n : ℝ) * (g : ℝ))
        = 4 / 3 * ((n : ℝ) * (g : ℝ)) * (3 * Real.sqrt D / 4) := by ring
      _ ≤ 4 / 3 * ((n : ℝ) * (g : ℝ)) * (sOf D : ℝ) := by gcongr
  have hng : (n : ℝ) ≤ (n : ℝ) * (g : ℝ) :=
    le_mul_of_one_le_right (Nat.cast_nonneg n) (by exact_mod_cast hg1)
  calc ((instanceIndices wAB D g p).card : ℝ)
      = (totalChunks wAB D p : ℝ) * (numPieces n D g : ℝ) := by
        rw [card_instanceIndices, Nat.cast_mul]
    _ ≤ 2 * Real.sqrt D * (numPieces n D g : ℝ) := by gcongr; exact hchunks.trans hchunks'
    _ ≤ 2 * Real.sqrt D * ((n : ℝ) * (g : ℝ) / (sOf D : ℝ) + 1) := by gcongr
    _ ≤ 4 * (n : ℝ) * (g : ℝ) := by linarith [hmain, hng, hsqrt]

end Matrices

/-! ### The neighborhoods in an instance -/

/-- The graph of a function into `Fin p` has as many points as the domain. -/
private theorem ncard_graph {α : Type} [Fintype α] (f : α → Fin p) :
    {v : α × Fin p | v.2 = f v.1}.ncard = Fintype.card α := by
  have h : {v : α × Fin p | v.2 = f v.1} = Set.univ.graphOn f := by
    ext v
    simp [Set.mem_graphOn, eq_comm]
  rw [h, Set.ncard_graphOn, Set.ncard_univ, Nat.card_eq_fintype_card]

/-- Section 3.1, "The reductions below [...] produce at most n²/√D query pairs and sets of at most
√D elements", and Remark 20, "every vertex of A has O(√D/g) neighbors in the middle part": in an
instance of the reduction, a vertex of `A` or of `B` has exactly one neighbor `(c, σ)` for every
`c ∈ C_k`, hence at most `⌈s/g⌉` neighbors.  (And `⌈s/g⌉ ≤ s ≤ √D`; for `g ≤ √D` also
`⌈s/g⌉ ≤ 2√D/g`, `pieceSize_le_two_mul_sqrt_div`.) -/
theorem ncard_nbr_lopInstance_le (wAB wBC wAC : Fin n → Fin n → ℤ) (hD : 16 ≤ D)
    (hg1 : 1 ≤ g) (hp : p ≠ 0) (ι : InstanceIndex p) :
    (∀ a, {v | (lopInstance wAB wBC wAC D g p ι).adjA a v}.ncard ≤ pieceSize D g) ∧
    (∀ b, {v | (lopInstance wAB wBC wAC D g p ι).adjB v b}.ncard ≤ pieceSize D g) := by
  -- The neighbors of a vertex are the graph of the function that sends `c` to its label.
  have hgraph : ∀ (f : {c : Fin n // c ∈ piece n D g ι.2.2} → ℤ),
      {v : {c : Fin n // c ∈ piece n D g ι.2.2} × Fin p |
        ((v.2 : ℕ) : ℤ) ≡ f v.1 [ZMOD (p : ℤ)]}.ncard ≤ pieceSize D g := by
    intro f
    refine le_trans (le_of_eq ?_) (card_piece_le hD hg1 n ι.2.2)
    rw [← Fintype.card_coe, ← ncard_graph fun c => resFin hp (f c)]
    congr 1
    ext v
    exact modEq_iff_eq_resFin hp v.2 _
  exact ⟨fun a => hgraph fun c => wAC a c + ((ι.1 : ℕ) : ℤ), fun b => hgraph fun c => -wBC b c⟩

end Cslib.Algorithms.ExactTriangle
