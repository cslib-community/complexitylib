/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Encoding
public import CslibFrontier.Computability.Circuit.Boolean.Encoding
public import CslibFrontier.Computability.Complexity.Classes.NP
public import CslibFrontier.Computability.Complexity.Reduction
public import CslibFrontier.Computability.Complexity.Problems.Clique
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.Copositive
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MotzkinStraus
public import CslibFrontier.Foundations.Data.Rat.Basic
public import Mathlib.Tactic.Matrix.ListMatrix
import CslibFrontier.Computability.Circuit.Encoding.Check
import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Computability.PolyTime.Int.DotProduct
import CslibFrontier.Computability.PolyTime.Int.ExactDiv
import CslibFrontier.Foundations.Data.List.DotProduct
import CslibFrontier.Foundations.Data.List.OfFn
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# CoNP-Completeness of Matrix Copositivity

Testing whether an encoded symmetric rational matrix `M` is *copositive*—meaning `x ⬝ᵥ M *ᵥ x ≥ 0`
for all entrywise nonnegative vectors `x`—is `coNP`-complete, and testing non-copositivity is
`NP`-complete. The completeness statements are credited to [MurtyKabadi1987] (secondary search
summaries indicate that [MurtyKabadi1987] proves hardness by reducing from subset sum rather than
`Clique`; the published text was not inspected). This library's `Clique`/Motzkin–Straus
reduction (`polyTimeReducible_Clique_NonCopositive`), the row-list representation `SymRatMatrix`,
binary encoding `encSymRatMatrix`, denominator-cleared verifier `NonCopositive.check`, and the
KKT/Cramer bounded integer witness derivation are original to this formalization.

By `Matrix.exists_nat_dotProduct_lt_zero_of_rat`, a symmetric rational matrix fails to be
copositive if and only if it admits a polynomially bit-bounded nonnegative integer vector `p` with
`p ⬝ᵥ M *ᵥ p < 0`. A polynomial-time verifier clears denominators by multiplying by the product
`D` of entry denominators and evaluates `p ⬝ᵥ M_int *ᵥ p < 0`, placing `NonCopositive` in `NP`
and `Copositive` in `coNP`. In the reverse direction, the Motzkin–Straus copositivity
characterization (`SimpleGraph.exists_nonneg_dotProduct_copositiveCliqueMatrix_lt_zero_iff`) gives
a polynomial-time many-one reduction from `Clique` to `NonCopositive`.

We also provide an optional input encoding `encRatArithCircuitInput` for rational arithmetic
circuits over `encRat`.

## Main definitions

- `Cslib.Complexity.encRat`: binary encoding of `ℚ` via `(q.num, q.den)`.
- `Cslib.Complexity.SymRatMatrix`, `Cslib.Complexity.encSymRatMatrix`: symmetric rational square
  matrices represented by row lists and their binary encoding.
- `Cslib.Complexity.Copositive`, `Cslib.Complexity.NonCopositive`: the copositivity and
  non-copositivity decision problems.
- `Cslib.Complexity.NonCopositive.check`: polynomial-time verifier relation for `NonCopositive`.
- `Cslib.Complexity.cliqueToSymRatMatrix`: polynomial-time reduction from `Clique` to
  `NonCopositive`.
- `Cslib.Complexity.encRatArithCircuit`, `Cslib.Complexity.encRatArithCircuitInput`: binary
  encodings for rational arithmetic circuits and circuit-input pairs.

## Main results

- `Cslib.Complexity.NonCopositive.mem_NP`, `Cslib.Complexity.Copositive.mem_coNP`: `NP` / `coNP`
  membership using the bounded nonnegative integer witness theorem.
- `Cslib.Complexity.polyTimeReducible_Clique_NonCopositive`: polynomial-time many-one reduction
  `Clique ≤ₚ NonCopositive`.
- `Cslib.Complexity.NonCopositive_npHard`, `Cslib.Complexity.NonCopositive_npComplete`:
  `NP`-completeness of `NonCopositive`.
- `Cslib.Complexity.Copositive_coNPHard`, `Cslib.Complexity.Copositive_coNPComplete`:
  `coNP`-completeness of `Copositive`.

## References

- [MotzkinStraus1965] T. S. Motzkin and E. G. Straus, *Maxima for graphs and a new proof of a
  theorem of Turán*, Canadian Journal of Mathematics 17, 1965, 533–540 (bibliographic metadata
  only; the published text is uninspected, and no internal theorem numbers are claimed).
- [MurtyKabadi1987] K. G. Murty and S. N. Kabadi, *Some NP-complete problems in quadratic and
  nonlinear programming*, Mathematical Programming 39(2), 1987, 117–129 (bibliographic metadata
  only; the published text is uninspected, and no internal theorem numbers are claimed).
-/

public section

namespace Cslib.Complexity

open Matrix Turing.MultiTapeTM

/-! ### Rational and symmetric matrix encodings -/

/-- Binary encoding of rational numerator-denominator pairs `(q.num, q.den)`. -/
abbrev encRatData : ℤ × ℕ ↪ List Bool :=
  encPair encIntBin encNat

/-- Binary encoding of rational numbers `ℚ` as `(q.num, q.den)`. -/
@[expose] def encRat : ℚ ↪ List Bool where
  toFun q := encRatData (q.num, q.den)
  inj' _ _ h :=
    Rat.ext (congrArg Prod.fst (encRatData.injective h))
      (congrArg Prod.snd (encRatData.injective h))

/-- Binary encoding of a rational matrix row list. -/
abbrev encRatMatrixRows : List (List ℚ) ↪ List Bool :=
  encList (encList encRat)

/-- Binary encoding of `Clique` instances `(G, k)`. -/
abbrev encClique : Graph × ℕ ↪ List Bool :=
  encPair encGraph encNat

/-- A square symmetric rational matrix represented by its list of rows. -/
structure SymRatMatrix where
  /-- The rows of the matrix. -/
  rows : List (List ℚ)
  /-- Every row has length equal to the number of rows. -/
  square : ∀ r ∈ rows, r.length = rows.length
  /-- Symmetry of entries under index transposition. -/
  symm : ∀ i j, (rows.getD i []).getD j 0 = (rows.getD j []).getD i 0

@[ext]
theorem SymRatMatrix.ext {M₁ M₂ : SymRatMatrix} (h : M₁.rows = M₂.rows) : M₁ = M₂ := by
  cases M₁
  cases M₂
  simp only [SymRatMatrix.mk.injEq]
  exact h

/-- Binary encoding of symmetric rational matrices via their row lists. -/
@[expose] def encSymRatMatrix : SymRatMatrix ↪ List Bool where
  toFun M := encRatMatrixRows M.rows
  inj' _ _ h := SymRatMatrix.ext (encRatMatrixRows.injective h)

/-- Binary encoding of `(M, p)` pairs for `NonCopositive` verification. -/
abbrev encSymRatMatrixWitness : SymRatMatrix × List ℕ ↪ List Bool :=
  encPair encSymRatMatrix (encList encNat)

/-- Interpret a `SymRatMatrix` as an `n × n` `Matrix` over `ℚ`, where `n = M.rows.length`. -/
@[expose] def SymRatMatrix.toMatrix (M : SymRatMatrix) :
    Matrix (Fin M.rows.length) (Fin M.rows.length) ℚ :=
  Matrix.of fun i j => (M.rows.getD i []).getD j 0

theorem SymRatMatrix.isSymm_toMatrix (M : SymRatMatrix) : M.toMatrix.IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, SymRatMatrix.toMatrix, Matrix.of_apply]
  exact M.symm j i

/-- The language of symmetric rational matrices that are copositive. -/
@[expose] def Copositive : Set SymRatMatrix :=
  {M | M.toMatrix.IsCopositive}

/-- The language of symmetric rational matrices that are not copositive. -/
@[expose] def NonCopositive : Set SymRatMatrix :=
  {M | ¬ M.toMatrix.IsCopositive}

theorem mem_Copositive_iff {M : SymRatMatrix} : M ∈ Copositive ↔ M.toMatrix.IsCopositive :=
  Iff.rfl

theorem mem_NonCopositive_iff {M : SymRatMatrix} : M ∈ NonCopositive ↔ ¬ M.toMatrix.IsCopositive :=
  Iff.rfl

theorem NonCopositive_eq_compl : NonCopositive = Copositiveᶜ := rfl

theorem Copositive_eq_compl : Copositive = NonCopositiveᶜ := by
  ext M
  simp only [Set.mem_compl_iff, mem_Copositive_iff, mem_NonCopositive_iff, not_not]

/-- Copositivity of a `SymRatMatrix` over `ℚ` coincides with copositivity over `ℝ`. -/
theorem mem_Copositive_iff_real {M : SymRatMatrix} :
    M ∈ Copositive ↔ (M.toMatrix.map (Rat.cast : ℚ → ℝ)).IsCopositive :=
  Matrix.isCopositive_rat_iff_map_real M.isSymm_toMatrix

/-! ### NP verifier for non-copositivity -/

/-- Common denominator for all entries of a rational matrix `M`: the product of its denominators. -/
@[expose] def SymRatMatrix.commonDenom (M : SymRatMatrix) : ℤ :=
  (M.rows.flatten.map fun q : ℚ => (q.den : ℤ)).prod

/-- Integerized matrix obtained by multiplying each entry of `M` by `M.commonDenom`. -/
@[expose] def SymRatMatrix.intRows (M : SymRatMatrix) : List (List ℤ) :=
  let D := M.commonDenom
  M.rows.map fun r => r.map fun q => q.num * (D / (q.den : ℤ))

/-- Polynomial-time verifier relation for `NonCopositive`: `p` has length `M.rows.length` and
`p ⬝ᵥ M.intRows *ᵥ p < 0`. -/
@[expose] def NonCopositive.check (M : SymRatMatrix) (p : List ℕ) : Bool :=
  let M_int := M.intRows
  let p_int : List ℤ := p.map Nat.cast
  let quad : ℤ :=
    Mathlib.Tactic.Matrix.ListMatrix.dotProduct M.rows.length p_int
      (M_int.map fun row =>
        Mathlib.Tactic.Matrix.ListMatrix.dotProduct M.rows.length row p_int)
  decide (p.length = M.rows.length) && decide (quad < 0)

private def SymRatMatrix.commonDenomNat (M : SymRatMatrix) : ℕ :=
  (M.rows.flatten.map fun q : ℚ => q.den).prod

private theorem SymRatMatrix.commonDenomNat_pos (M : SymRatMatrix) : 0 < M.commonDenomNat :=
  List.prod_pos fun _ hx => by
    obtain ⟨q, _, rfl⟩ := List.mem_map.1 hx
    exact q.pos

private theorem SymRatMatrix.commonDenom_eq_nat (M : SymRatMatrix) :
    M.commonDenom = (M.commonDenomNat : ℤ) := by
  dsimp only [SymRatMatrix.commonDenom, SymRatMatrix.commonDenomNat]
  rw [Nat.cast_list_prod (R := ℤ), List.map_map]
  rfl

private theorem SymRatMatrix.toMatrix_eq_getElem (M : SymRatMatrix) (i j : Fin M.rows.length) :
    M.toMatrix i j =
      M.rows[i.1][j.1]'(by rw [M.square _ (List.getElem_mem i.2)]; exact j.2) := by
  have hj_lt : j.1 < M.rows[i.1].length := by
    rw [M.square _ (List.getElem_mem i.2)]
    exact j.2
  dsimp only [SymRatMatrix.toMatrix, Matrix.of_apply]
  rw [List.getD_eq_getElem _ _ i.2, List.getD_eq_getElem _ _ hj_lt]

private theorem SymRatMatrix.den_dvd_commonDenomNat (M : SymRatMatrix)
    {i j : Fin M.rows.length} :
    (M.toMatrix i j).den ∣ M.commonDenomNat := by
  have hi : M.rows[i.1] ∈ M.rows := List.getElem_mem i.2
  have hj_lt : j.1 < M.rows[i.1].length := by
    rw [M.square _ hi]
    exact j.2
  have hmem_row : M.rows[i.1][j.1] ∈ M.rows[i.1] := List.getElem_mem hj_lt
  have hmem_flat : M.rows[i.1][j.1] ∈ M.rows.flatten :=
    List.mem_flatten.2 ⟨M.rows[i.1], hi, hmem_row⟩
  rw [M.toMatrix_eq_getElem i j]
  exact List.dvd_prod (List.mem_map.2 ⟨M.rows[i.1][j.1], hmem_flat, rfl⟩)

private noncomputable def SymRatMatrix.intMatrix (M : SymRatMatrix) :
    Matrix (Fin M.rows.length) (Fin M.rows.length) ℤ :=
  Matrix.of fun i j => (M.intRows.getD i []).getD j 0

private theorem SymRatMatrix.intMatrix_eq (M : SymRatMatrix) (i j : Fin M.rows.length) :
    M.intMatrix i j =
      (M.toMatrix i j).num * ((M.commonDenomNat / (M.toMatrix i j).den : ℕ) : ℤ) := by
  have hi : i.1 < M.rows.length := i.2
  have hi_int : i.1 < M.intRows.length := by
    simp only [SymRatMatrix.intRows, List.length_map]
    exact hi
  have hj : j.1 < M.rows[i.1].length := by
    rw [M.square _ (List.getElem_mem hi)]
    exact j.2
  have hj_int : j.1 < M.intRows[i.1].length := by
    simp only [SymRatMatrix.intRows, List.getElem_map, List.length_map]
    exact hj
  dsimp only [SymRatMatrix.intMatrix, Matrix.of_apply]
  rw [List.getD_eq_getElem _ _ hi_int, List.getD_eq_getElem _ _ hj_int]
  simp only [SymRatMatrix.intRows, List.getElem_map]
  rw [← M.toMatrix_eq_getElem i j, M.commonDenom_eq_nat, Int.natCast_ediv]

private theorem SymRatMatrix.intMatrix_mul_eq (M : SymRatMatrix)
    (i j : Fin M.rows.length) :
    (M.commonDenomNat : ℚ) * M.toMatrix i j = (M.intMatrix i j : ℚ) := by
  rw [M.intMatrix_eq i j]
  exact Matrix.rat_clearDenom_entry M.den_dvd_commonDenomNat

private theorem SymRatMatrix.dotProduct_check_eq (M : SymRatMatrix) {p : List ℕ}
    (hlen : p.length = M.rows.length) :
    let pFin : Fin M.rows.length → ℕ := fun i => p.getD i.1 0
    Mathlib.Tactic.Matrix.ListMatrix.dotProduct M.rows.length (p.map Nat.cast)
        (M.intRows.map fun row =>
          Mathlib.Tactic.Matrix.ListMatrix.dotProduct M.rows.length row (p.map Nat.cast)) =
      (fun i => (pFin i : ℤ)) ⬝ᵥ (M.intMatrix *ᵥ fun i => (pFin i : ℤ)) := by
  intro pFin
  have hp_ofFn :
      (p.map Nat.cast : List ℤ) = List.ofFn fun i : Fin M.rows.length => (pFin i : ℤ) := by
    refine List.ext_getElem (by simp only [List.length_map, List.length_ofFn, hlen]) ?_
    intro k hk1 hk2
    have hk_lt : k < p.length := by simpa only [List.length_map] using hk1
    simp only [List.getElem_map, List.getElem_ofFn, pFin, List.getD_eq_getElem _ _ hk_lt]
  have hrows_ofFn :
      (M.intRows.map fun row =>
          Mathlib.Tactic.Matrix.ListMatrix.dotProduct M.rows.length row (p.map Nat.cast)) =
        List.ofFn fun i : Fin M.rows.length => (M.intMatrix *ᵥ fun j => (pFin j : ℤ)) i := by
    refine List.ext_getElem ?_ ?_
    · simp only [List.length_map, SymRatMatrix.intRows, List.length_ofFn]
    intro k hk1 hk2
    have hk_lt : k < M.rows.length := by
      simpa only [List.length_map, SymRatMatrix.intRows] using hk1
    have hrow_len : M.rows[k].length = M.rows.length := M.square _ (List.getElem_mem hk_lt)
    have hrow_ofFn :
        (M.intRows[k]'(by
          simp only [SymRatMatrix.intRows, List.length_map]; exact hk_lt) : List ℤ) =
          List.ofFn fun j : Fin M.rows.length => M.intMatrix ⟨k, hk_lt⟩ j := by
      refine List.ext_getElem ?_ ?_
      · simp only [SymRatMatrix.intRows, List.getElem_map, List.length_map, List.length_ofFn,
          hrow_len]
      intro j hj1 hj2
      have hj_lt : j < M.rows.length := by simpa only [List.length_ofFn] using hj2
      have hk_int : k < M.intRows.length := by
        simp only [SymRatMatrix.intRows, List.length_map]; exact hk_lt
      have hj_int : j < M.intRows[k].length := by
        simp only [SymRatMatrix.intRows, List.getElem_map, List.length_map]
        rw [hrow_len]; exact hj_lt
      simp only [List.getElem_ofFn, SymRatMatrix.intMatrix, Matrix.of_apply,
        List.getD_eq_getElem _ _ hk_int, List.getD_eq_getElem _ _ hj_int]
    simp only [List.getElem_map, List.getElem_ofFn, Matrix.mulVec]
    rw [hrow_ofFn, hp_ofFn]
    exact Mathlib.Tactic.Matrix.ListMatrix.dotProduct_ofFn
      (fun j => M.intMatrix ⟨k, hk_lt⟩ j) (fun j => (pFin j : ℤ))
  rw [hrows_ofFn, hp_ofFn]
  exact Mathlib.Tactic.Matrix.ListMatrix.dotProduct_ofFn
    (fun i => (pFin i : ℤ)) (M.intMatrix *ᵥ fun j => (pFin j : ℤ))

private theorem SymRatMatrix.dotProduct_scale (M : SymRatMatrix) (pFin : Fin M.rows.length → ℕ) :
    (M.commonDenomNat : ℚ) *
        ((fun i => (pFin i : ℚ)) ⬝ᵥ (M.toMatrix *ᵥ fun i => (pFin i : ℚ))) =
      (((fun i => (pFin i : ℤ)) ⬝ᵥ (M.intMatrix *ᵥ fun i => (pFin i : ℤ)) : ℤ) : ℚ) := by
  rw [Matrix.dotProduct_scale_of_eq (M₂ := M.intMatrix.map (Int.cast : ℤ → ℚ))
    (fun i j => by simpa only [Matrix.map_apply] using M.intMatrix_mul_eq i j),
    Matrix.intCast_dotProduct_mulVec_nat]

private theorem NonCopositive.sound_of_check {M : SymRatMatrix} {p : List ℕ}
    (hc : NonCopositive.check M p = true) : M ∈ NonCopositive := by
  simp only [NonCopositive.check, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hlen, hquad⟩ := hc
  rw [SymRatMatrix.dotProduct_check_eq M hlen] at hquad
  set pFin : Fin M.rows.length → ℕ := fun i => p.getD i.1 0
  have hnegQ :
      (M.commonDenomNat : ℚ) *
          ((fun i => (pFin i : ℚ)) ⬝ᵥ (M.toMatrix *ᵥ fun i => (pFin i : ℚ))) < 0 := by
    rw [M.dotProduct_scale pFin]
    exact Int.cast_lt_zero.2 hquad
  have hneg : (fun i => (pFin i : ℚ)) ⬝ᵥ (M.toMatrix *ᵥ fun i => (pFin i : ℚ)) < 0 :=
    lt_of_not_ge fun hge =>
      not_lt_of_ge (mul_nonneg (Nat.cast_nonneg _) hge) hnegQ
  intro hcop
  exact (not_lt_of_ge (hcop (fun i => (pFin i : ℚ)) fun i => Nat.cast_nonneg _)) hneg

private theorem length_encRat_num_le (q : ℚ) : (encIntBin q.num).length ≤ (encRat q).length := by
  change (encIntBin q.num).length ≤ (encPair encIntBin encNat (q.num, q.den)).length
  rw [encPair_apply, List.length_append, length_frame]
  dsimp only
  omega

private theorem length_encRat_den_le (q : ℚ) : (encNat q.den).length ≤ (encRat q).length := by
  change (encNat q.den).length ≤ (encPair encIntBin encNat (q.num, q.den)).length
  rw [encPair_apply, List.length_append, length_frame]
  dsimp only
  omega

private theorem natAbs_le_two_pow_encIntBin (z : ℤ) : z.natAbs ≤ 2 ^ (encIntBin z).length := by
  have h := Nat.lt_size_self z.natAbs
  have hlen : z.natAbs.size ≤ (encIntBin z).length := by
    rw [length_encIntBin]
    exact Nat.le_succ _
  exact (h.le).trans (Nat.pow_le_pow_right (by omega : 1 ≤ 2) hlen)

private theorem nat_le_two_pow_encNat (n : ℕ) : n ≤ 2 ^ (encNat n).length := by
  have h := Nat.lt_size_self n
  have hlen : n.size = (encNat n).length := by simp only [encNat_apply, Nat.size_eq_bits_len]
  rw [← hlen]
  exact h.le

private theorem list_prod_le_two_pow_sum {α : Type*} (l : List α) (f w : α → ℕ)
    (hf : ∀ a ∈ l, f a ≤ 2 ^ w a) : (l.map f).prod ≤ 2 ^ (l.map w).sum := by
  induction l with
  | nil => simp only [List.map_nil, List.prod_nil, List.sum_nil, pow_zero, le_rfl]
  | cons a l ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons, pow_add]
      exact Nat.mul_le_mul (hf a List.mem_cons_self)
        (ih fun x hx => hf x (List.mem_cons_of_mem a hx))

private theorem sum_encRat_flatten_le_rows (rows : List (List ℚ)) :
    (rows.flatten.map fun q => (encRat q).length).sum ≤ (encList (encList encRat) rows).length := by
  have hflat : (rows.flatten.map fun q => (encRat q).length).sum =
      (rows.map fun r => (r.map fun q => (encRat q).length).sum).sum := by
    induction rows with
    | nil => rfl
    | cons r rs ih =>
        simp only [List.flatten_cons, List.map_append, List.sum_append, List.map_cons,
          List.sum_cons, ih]
  rw [hflat]
  have hrows : ∀ r ∈ rows, (r.map fun q => (encRat q).length).sum ≤ (encList encRat r).length :=
    fun r _ => sum_length_le_length_encList encRat r
  have hsum :
      (rows.map fun r => (r.map fun q => (encRat q).length).sum).sum ≤
        (rows.map fun r => (encList encRat r).length).sum := by
    clear hflat
    induction rows with
    | nil => rfl
    | cons r rs ih =>
        simp only [List.map_cons, List.sum_cons]
        exact Nat.add_le_add (hrows r List.mem_cons_self)
          (ih fun s hs => hrows s (List.mem_cons_of_mem r hs))
  exact hsum.trans (sum_length_le_length_encList (encList encRat) rows)

private theorem NonCopositive.complete_of_mem {M : SymRatMatrix} (hM : M ∈ NonCopositive) :
    ∃ p : List ℕ,
      NonCopositive.check M p = true ∧
        (encList encNat p).length ≤
          ((Polynomial.X * (16 * (Polynomial.X + 1) ^ 2 + 3)).eval (encSymRatMatrix M).length) := by
  set L := (encSymRatMatrix M).length
  set n := M.rows.length
  have hn_le_L : n ≤ L := by
    change M.rows.length ≤ (encList (encList encRat) M.rows).length
    exact SizedListEncoding.length_le (encA := encList encRat) M.rows
  have hden_le : M.commonDenomNat ≤ 2 ^ L := by
    refine (list_prod_le_two_pow_sum M.rows.flatten (fun q => q.den) (fun q => (encRat q).length)
      fun q _ => (nat_le_two_pow_encNat q.den).trans
        (Nat.pow_le_pow_right (by omega) (length_encRat_den_le q))).trans ?_
    exact Nat.pow_le_pow_right (by omega) (sum_encRat_flatten_le_rows M.rows)
  have hB : ∀ i j : Fin n, |M.intMatrix i j| ≤ ((2 ^ (2 * L) : ℕ) : ℤ) := by
    intro i j
    have hi : M.rows[i.1] ∈ M.rows := List.getElem_mem i.2
    have hj_lt : j.1 < M.rows[i.1].length := by
      rw [M.square _ hi]
      exact j.2
    have hq_enc_le : (encRat (M.toMatrix i j)).length ≤ L := by
      have hr : (encList encRat (M.rows[i.1])).length ≤ L := by
        change (encList encRat (M.rows[i.1])).length ≤ (encList (encList encRat) M.rows).length
        exact SizedListEncoding.length_elem_le (encA := encList encRat) M.rows _ hi
      have hq' : (encRat (M.rows[i.1][j.1])).length ≤ (encList encRat (M.rows[i.1])).length :=
        SizedListEncoding.length_elem_le (encA := encRat) (M.rows[i.1]) _ (List.getElem_mem hj_lt)
      rw [M.toMatrix_eq_getElem i j]
      exact hq'.trans hr
    have hnum_le : (M.toMatrix i j).num.natAbs ≤ 2 ^ L :=
      (natAbs_le_two_pow_encIntBin _).trans
        (Nat.pow_le_pow_right (by omega) ((length_encRat_num_le _).trans hq_enc_le))
    have hquot_le : M.commonDenomNat / (M.toMatrix i j).den ≤ 2 ^ L :=
      (Nat.div_le_self _ _).trans hden_le
    rw [M.intMatrix_eq i j, abs_mul, abs_of_nonneg (Int.natCast_nonneg _), ← Int.natCast_natAbs,
      ← Int.natCast_mul]
    exact Int.ofNat_le.2 (by
      calc
        (M.toMatrix i j).num.natAbs * (M.commonDenomNat / (M.toMatrix i j).den) ≤
            2 ^ L * 2 ^ L := Nat.mul_le_mul hnum_le hquot_le
        _ = 2 ^ (2 * L) := by rw [← pow_add, two_mul])
  obtain ⟨pFin, hpFin_le, hpFin_neg⟩ :=
    Matrix.exists_nat_dotProduct_lt_zero_of_rat M.commonDenomNat_pos M.isSymm_toMatrix
      M.intMatrix_mul_eq hB hM
  simp only [Fintype.card_fin] at hpFin_le
  let p : List ℕ := List.ofFn pFin
  have hp_len : p.length = n := List.length_ofFn
  have hquad_neg :
      (fun i => (pFin i : ℤ)) ⬝ᵥ (M.intMatrix *ᵥ fun i => (pFin i : ℤ)) < 0 := by
    refine Int.cast_lt_zero (R := ℚ).1 ?_
    rw [← M.dotProduct_scale pFin]
    exact mul_neg_of_pos_of_neg (Nat.cast_pos.2 M.commonDenomNat_pos) hpFin_neg
  have hcheck : NonCopositive.check M p = true := by
    simp only [NonCopositive.check, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨hp_len, ?_⟩
    rw [SymRatMatrix.dotProduct_check_eq M hp_len]
    have hp_getD : (fun i : Fin M.rows.length => p.getD i.1 0) = pFin := by
      ext i
      simp only [p, List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.2, ↓reduceDIte,
        Option.getD_some, Fin.eta]
    rw [hp_getD]
    exact hquad_neg
  refine ⟨p, hcheck, ?_⟩
  have hpow_elem : ∀ a ∈ p, (encNat a).length ≤ 8 * (L + 1) ^ 2 + 1 := by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
    have hmax : max (2 ^ (2 * L)) 1 = 2 ^ (2 * L) := max_eq_left Nat.one_le_two_pow
    have hle1 : Nat.factorial n ≤ 2 ^ (L ^ 2) := by
      have hn2 : n ≤ 2 ^ L := hn_le_L.trans Nat.lt_two_pow_self.le
      calc
        Nat.factorial n ≤ n ^ n := Nat.factorial_le_pow n
        _ ≤ (2 ^ L) ^ n := Nat.pow_le_pow_left hn2 n
        _ = 2 ^ (L * n) := (pow_mul 2 L n).symm
        _ ≤ 2 ^ (L * L) := Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left L hn_le_L)
        _ = 2 ^ (L ^ 2) := by rw [sq]
    have hle2 : (n * (max (2 ^ (2 * L)) 1) ^ 2 + 1) ^ n ≤ 2 ^ (6 * L ^ 2 + L) := by
      rw [hmax]
      have hbase : n * (2 ^ (2 * L)) ^ 2 + 1 ≤ 2 ^ (5 * L + 1) := by
        have hn2 : n ≤ 2 ^ L := hn_le_L.trans Nat.lt_two_pow_self.le
        have hmul : n * (2 ^ (2 * L)) ^ 2 ≤ 2 ^ L * 2 ^ (4 * L) := by
          rw [← pow_mul, show 2 * L * 2 = 4 * L by ring]
          exact Nat.mul_le_mul_right _ hn2
        calc
          n * (2 ^ (2 * L)) ^ 2 + 1 ≤ 2 ^ L * 2 ^ (4 * L) + 2 ^ (5 * L) :=
            Nat.add_le_add hmul Nat.one_le_two_pow
          _ = 2 ^ (5 * L) + 2 ^ (5 * L) := by rw [← pow_add, show L + 4 * L = 5 * L by ring]
          _ = 2 ^ (5 * L + 1) := by rw [pow_succ]; ring
      calc
        (n * (2 ^ (2 * L)) ^ 2 + 1) ^ n ≤ (2 ^ (5 * L + 1)) ^ n :=
          Nat.pow_le_pow_left hbase n
        _ = 2 ^ ((5 * L + 1) * n) := (pow_mul 2 _ n).symm
        _ ≤ 2 ^ ((5 * L + 1) * L) :=
          Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ hn_le_L)
        _ ≤ 2 ^ (6 * L ^ 2 + L) :=
          Nat.pow_le_pow_right (by omega) (by nlinarith)
    have hlt_pow : pFin i < 2 ^ (8 * (L + 1) ^ 2 + 1) := by
      have h1 : pFin i ≤ 2 ^ (L ^ 2) * 2 ^ (6 * L ^ 2 + L) :=
        (hpFin_le i).trans (Nat.mul_le_mul hle1 hle2)
      have h2 : 2 ^ (L ^ 2) * 2 ^ (6 * L ^ 2 + L) < 2 ^ (8 * (L + 1) ^ 2 + 1) := by
        rw [← pow_add]
        exact Nat.pow_lt_pow_right (by omega) (by nlinarith)
      exact lt_of_le_of_lt h1 h2
    simp only [encNat_apply, Nat.size_eq_bits_len]
    exact Nat.size_le.2 hlt_pow
  have hlist_le := length_encList_le encNat p hpow_elem
  have hbound : p.length * (2 * (8 * (L + 1) ^ 2 + 1) + 1) ≤
      (Polynomial.X * (16 * (Polynomial.X + 1) ^ 2 + 3)).eval L := by
    simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_add,
      Polynomial.eval_ofNat, Polynomial.eval_pow, Polynomial.eval_one, hp_len]
    calc
      n * (2 * (8 * (L + 1) ^ 2 + 1) + 1) = n * (16 * (L + 1) ^ 2 + 3) := by ring
      _ ≤ L * (16 * (L + 1) ^ 2 + 3) := Nat.mul_le_mul_right _ hn_le_L
  exact hlist_le.trans hbound

theorem NonCopositive.exists_check_eq_true_iff (M : SymRatMatrix) :
    (∃ p : List ℕ, NonCopositive.check M p = true) ↔ M ∈ NonCopositive := by
  constructor
  · rintro ⟨p, hp⟩
    exact NonCopositive.sound_of_check hp
  · intro hM
    obtain ⟨p, hp, _⟩ := NonCopositive.complete_of_mem hM
    exact ⟨p, hp⟩

private theorem computableInPolyTime_intCastRat :
    ComputableInPolyTime (fun z : ℤ => (z : ℚ)) encIntBin encRat := by
  have h : ComputableInPolyTime (fun z : ℤ => (z, (1 : ℕ))) encIntBin encRatData := by
    fun_prop
  exact h.of_enc_eq fun z => by
    change encPair encIntBin encNat ((z : ℚ).num, (z : ℚ).den) =
      encPair encIntBin encNat (z, 1)
    rw [Rat.num_intCast, Rat.den_intCast]

private theorem computableInPolyTime_rows :
    ComputableInPolyTime SymRatMatrix.rows encSymRatMatrix encRatMatrixRows :=
  (ComputableTidilyInPolyTime.of_eq (f := SymRatMatrix.rows)
    (encIn := encSymRatMatrix) (encMid := encRatMatrixRows) fun _ => rfl).computableInPolyTime

private theorem computableInPolyTime_ratPair :
    ComputableInPolyTime (fun q : ℚ => (q.num, q.den)) encRat encRatData :=
  (ComputableTidilyInPolyTime.of_eq (f := fun q : ℚ => (q.num, q.den))
    (encIn := encRat) (encMid := encRatData) fun _ => rfl).computableInPolyTime

private theorem computableInPolyTime_ratNum :
    ComputableInPolyTime Rat.num encRat encIntBin :=
  computableInPolyTime_ratPair.fst'

private theorem computableInPolyTime_ratDen :
    ComputableInPolyTime Rat.den encRat encNat :=
  computableInPolyTime_ratPair.snd'

private theorem computableInPolyTime_commonDenom :
    ComputableInPolyTime SymRatMatrix.commonDenom encSymRatMatrix encIntBin := by
  have hrows : ComputableInPolyTime SymRatMatrix.rows encSymRatMatrix encRatMatrixRows :=
    computableInPolyTime_rows
  have hflat : ComputableInPolyTime (fun M : SymRatMatrix => M.rows.flatten)
      encSymRatMatrix (encList encRat) := by
    have htidy :
        ComputableTidilyInPolyTime (List.flatten (α := ℚ)) encRatMatrixRows (encList encRat) :=
      ComputableTidilyInPolyTime.flatten encRat
    exact htidy.computableInPolyTime.comp hrows
  have hdens :
      ComputableInPolyTime (fun M : SymRatMatrix => M.rows.flatten.map fun q : ℚ => (q.den : ℤ))
        encSymRatMatrix (encList encIntBin) := by
    have hq : ComputableInPolyTime (fun q : ℚ => (q.den : ℤ)) encRat encIntBin :=
      ComputableInPolyTime.intBin_natCast.comp computableInPolyTime_ratDen
    exact (ComputableInPolyTime.map hq).comp hflat
  exact ComputableInPolyTime.intBin_prod.comp hdens

private theorem computableInPolyTime_intRows :
    ComputableInPolyTime SymRatMatrix.intRows encSymRatMatrix (encList (encList encIntBin)) := by
  have hrows : ComputableTidilyInPolyTime SymRatMatrix.rows encSymRatMatrix encRatMatrixRows :=
    ComputableTidilyInPolyTime.of_eq (f := SymRatMatrix.rows)
      (encIn := encSymRatMatrix) (encMid := encRatMatrixRows) fun _ => rfl
  have hnum : ComputableInPolyTime (fun p : SymRatMatrix × ℚ => p.2.num)
      (encPair encSymRatMatrix encRat) encIntBin :=
    computableInPolyTime_ratNum.comp (ComputableInPolyTime.snd encSymRatMatrix encRat)
  have hdenZ : ComputableInPolyTime (fun p : SymRatMatrix × ℚ => (p.2.den : ℤ))
      (encPair encSymRatMatrix encRat) encIntBin :=
    ComputableInPolyTime.intBin_natCast.comp
      (computableInPolyTime_ratDen.comp (ComputableInPolyTime.snd encSymRatMatrix encRat))
  have hD : ComputableInPolyTime (fun p : SymRatMatrix × ℚ => p.1.commonDenom)
      (encPair encSymRatMatrix encRat) encIntBin :=
    computableInPolyTime_commonDenom.comp (ComputableInPolyTime.fst encSymRatMatrix encRat)
  have hentry :
      ComputableInPolyTime
        (fun p : SymRatMatrix × ℚ => p.2.num * (p.1.commonDenom / (p.2.den : ℤ)))
        (encPair encSymRatMatrix encRat) encIntBin :=
    ComputableInPolyTime.intBin_mul' hnum (ComputableInPolyTime.intBin_div' hD hdenZ)
  have hentry' :
      ComputableTidilyInPolyTime
        (fun x : (SymRatMatrix × List ℚ) × ℚ =>
          x.2.num * (x.1.1.commonDenom / (x.2.den : ℤ)))
        (encPair (encPair encSymRatMatrix (encList encRat)) encRat) encIntBin :=
    (hentry.comp (ComputableInPolyTime.prod
      ((ComputableInPolyTime.fst encSymRatMatrix (encList encRat)).comp
        (ComputableInPolyTime.fst _ _))
      (ComputableInPolyTime.snd _ _))).tidy
  have hrow_map :
      ComputableTidilyInPolyTime
        (fun p : SymRatMatrix × List ℚ =>
          p.2.map fun q => q.num * (p.1.commonDenom / (q.den : ℤ)))
        (encPair encSymRatMatrix (encList encRat)) (encList encIntBin) :=
    ComputableTidilyInPolyTime.mapWithInput
      (ComputableTidilyInPolyTime.snd encSymRatMatrix (encList encRat)) hentry'
  exact (ComputableTidilyInPolyTime.mapWithInput hrows hrow_map).computableInPolyTime

theorem NonCopositive.computableInPolyTime_check :
    ComputableInPolyTime (fun x : SymRatMatrix × List ℕ => NonCopositive.check x.1 x.2)
      encSymRatMatrixWitness encBool := by
  have hrows :
      ComputableInPolyTime (fun x : SymRatMatrix × List ℕ => x.1.rows)
        encSymRatMatrixWitness encRatMatrixRows :=
    computableInPolyTime_rows.comp (ComputableInPolyTime.fst encSymRatMatrix (encList encNat))
  have hn_unary :
      ComputableInPolyTime (fun x : SymRatMatrix × List ℕ => x.1.rows.length)
        encSymRatMatrixWitness encUnary :=
    (ComputableTidilyInPolyTime.length_list (encList encRat)).computableInPolyTime.comp hrows
  have hp_len_unary :
      ComputableInPolyTime (fun x : SymRatMatrix × List ℕ => x.2.length)
        encSymRatMatrixWitness encUnary :=
    (ComputableTidilyInPolyTime.length_list encNat).computableInPolyTime.comp
      (ComputableInPolyTime.snd encSymRatMatrix (encList encNat))
  have hlen_eq :
      ComputableInPolyTime (fun x : SymRatMatrix × List ℕ => decide (x.2.length = x.1.rows.length))
        encSymRatMatrixWitness encBool :=
    (ComputableTidilyInPolyTime.decide_eq encUnary).computableInPolyTime.comp
      (ComputableInPolyTime.prod hp_len_unary hn_unary)
  have hp_int :
      ComputableInPolyTime (fun x : SymRatMatrix × List ℕ => x.2.map (Nat.cast : ℕ → ℤ))
        encSymRatMatrixWitness (encList encIntBin) :=
    (ComputableInPolyTime.map ComputableInPolyTime.intBin_natCast).comp
      (ComputableInPolyTime.snd encSymRatMatrix (encList encNat))
  have hM_int :
      ComputableTidilyInPolyTime (fun x : SymRatMatrix × List ℕ => x.1.intRows)
        encSymRatMatrixWitness (encList (encList encIntBin)) :=
    (computableInPolyTime_intRows.comp
      (ComputableInPolyTime.fst encSymRatMatrix (encList encNat))).tidy
  have hrow_dot :
      ComputableTidilyInPolyTime
        (fun y : (SymRatMatrix × List ℕ) × List ℤ =>
          Mathlib.Tactic.Matrix.ListMatrix.dotProduct y.1.1.rows.length y.2
            (y.1.2.map (Nat.cast : ℕ → ℤ)))
        (encPair encSymRatMatrixWitness (encList encIntBin)) encIntBin :=
    (ComputableInPolyTime.listDotProduct.comp
      (ComputableInPolyTime.prod (hn_unary.comp (ComputableInPolyTime.fst _ _))
        (ComputableInPolyTime.prod (ComputableInPolyTime.snd _ _)
          (hp_int.comp (ComputableInPolyTime.fst _ _))))).tidy
  have hmatVec :
      ComputableInPolyTime
        (fun x : SymRatMatrix × List ℕ =>
          x.1.intRows.map fun row =>
            Mathlib.Tactic.Matrix.ListMatrix.dotProduct x.1.rows.length row
              (x.2.map (Nat.cast : ℕ → ℤ)))
        encSymRatMatrixWitness (encList encIntBin) :=
    (ComputableTidilyInPolyTime.mapWithInput hM_int hrow_dot).computableInPolyTime
  have hquad :
      ComputableInPolyTime
        (fun x : SymRatMatrix × List ℕ =>
          Mathlib.Tactic.Matrix.ListMatrix.dotProduct x.1.rows.length
            (x.2.map (Nat.cast : ℕ → ℤ))
            (x.1.intRows.map fun row =>
              Mathlib.Tactic.Matrix.ListMatrix.dotProduct x.1.rows.length row
                (x.2.map (Nat.cast : ℕ → ℤ))))
        encSymRatMatrixWitness encIntBin :=
    ComputableInPolyTime.listDotProduct.comp
      (ComputableInPolyTime.prod hn_unary (ComputableInPolyTime.prod hp_int hmatVec))
  have hneg :
      ComputableInPolyTime
        (fun x : SymRatMatrix × List ℕ =>
          decide
            (Mathlib.Tactic.Matrix.ListMatrix.dotProduct x.1.rows.length
                (x.2.map (Nat.cast : ℕ → ℤ))
                (x.1.intRows.map fun row =>
                  Mathlib.Tactic.Matrix.ListMatrix.dotProduct x.1.rows.length row
                    (x.2.map (Nat.cast : ℕ → ℤ))) < 0))
        encSymRatMatrixWitness encBool :=
    ComputableInPolyTime.intBin_lt' hquad (ComputableInPolyTime.const 0)
  exact (ComputableInPolyTime.bool_and.comp (ComputableInPolyTime.prod hlen_eq hneg)).of_enc_eq
    fun _ => rfl

theorem NonCopositive.mem_NP : NonCopositive ∈ NP encSymRatMatrix := by
  have hmem : {M : SymRatMatrix | ∃ p : List ℕ, NonCopositive.check M p = true} ∈
      NP encSymRatMatrix :=
    mem_NP_of_witness (Decoder.list Decoder.nat) NonCopositive.computableInPolyTime_check
      (fun _ _ => Iff.rfl)
      (fun M _ h => by
        obtain ⟨p', hp', hlen⟩ :=
          NonCopositive.complete_of_mem (NonCopositive.sound_of_check h)
        exact ⟨p', hp', hlen⟩)
  have hset : {M : SymRatMatrix | ∃ p : List ℕ, NonCopositive.check M p = true} = NonCopositive :=
    Set.ext NonCopositive.exists_check_eq_true_iff
  rwa [← hset]

theorem Copositive.mem_coNP : Copositive ∈ coNP encSymRatMatrix := by
  change Copositiveᶜ ∈ NP encSymRatMatrix
  rw [← NonCopositive_eq_compl]
  exact NonCopositive.mem_NP

/-! ### Reduction from `Clique` to `NonCopositive` -/

/-- Entry `(u, v)` of the reduction matrix for `(G, k)`. -/
@[expose] def cliqueEntry (G : Graph) (k u v : ℕ) : ℚ :=
  if u = v then (((k : ℤ) - 2 : ℤ) : ℚ)
  else if G.adjBool u v then (-1 : ℚ)
  else (((k : ℤ) - 2 : ℤ) : ℚ)

/-- Row list produced by the reduction from a `Clique` instance `(G, k)` to a symmetric rational
matrix. For `k ≥ 2` on a graph with nonempty vertex list, this is the Motzkin–Straus matrix
`(k - 2) J - (k - 1) A_G`. -/
@[expose] def cliqueToRows (gk : Graph × ℕ) : List (List ℚ) :=
  let (G, k) := gk
  if k = 0 then [[(-1 : ℚ)]]
  else if G.distinctVertices.isEmpty then [[(1 : ℚ)]]
  else if k = 1 then [[(-1 : ℚ)]]
  else
    G.distinctVertices.map fun u =>
      G.distinctVertices.map fun v => cliqueEntry G k u v

private theorem graph_adjBool_comm (G : Graph) (u v : ℕ) :
    G.adjBool u v = G.adjBool v u := by
  rw [Bool.eq_iff_iff, G.adjBool_eq_true_iff u v, G.adjBool_eq_true_iff v u,
    G.toSimpleGraph.adj_comm]

private theorem cliqueToRows_square (gk : Graph × ℕ) :
    ∀ r ∈ cliqueToRows gk, r.length = (cliqueToRows gk).length := by
  rcases gk with ⟨G, k⟩
  dsimp only [cliqueToRows]
  split_ifs
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    rfl
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    rfl
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    rfl
  · intro r hr
    obtain ⟨u, _, rfl⟩ := List.mem_map.1 hr
    simp only [List.length_map]

private theorem cliqueToRows_symm (gk : Graph × ℕ) :
    ∀ i j, ((cliqueToRows gk).getD i []).getD j 0 =
      ((cliqueToRows gk).getD j []).getD i 0 := by
  rcases gk with ⟨G, k⟩
  intro i j
  dsimp only [cliqueToRows]
  split_ifs
  · rcases i with _ | i <;> rcases j with _ | j <;>
      simp only [List.getD_cons_zero, List.getD_cons_succ, List.getD_nil]
  · rcases i with _ | i <;> rcases j with _ | j <;>
      simp only [List.getD_cons_zero, List.getD_cons_succ, List.getD_nil]
  · rcases i with _ | i <;> rcases j with _ | j <;>
      simp only [List.getD_cons_zero, List.getD_cons_succ, List.getD_nil]
  · by_cases hi : i < G.distinctVertices.length
    · by_cases hj : j < G.distinctVertices.length
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, Option.map_some,
          Option.getD_some, cliqueEntry]
        by_cases huv : G.distinctVertices[i] = G.distinctVertices[j]
        · simp only [huv, ↓reduceIte]
        · have hvu : G.distinctVertices[j] ≠ G.distinctVertices[i] := fun h => huv h.symm
          simp only [huv, hvu, ↓reduceIte]
          rw [graph_adjBool_comm G]
      · have hj' : ¬ j < G.distinctVertices.length := hj
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_eq_getElem hi, List.getElem?_eq_none (Nat.le_of_not_lt hj'),
          Option.map_some, Option.map_none, Option.getD_some, Option.getD_none,
          List.getElem?_nil]
    · have hi' : ¬ i < G.distinctVertices.length := hi
      by_cases hj : j < G.distinctVertices.length
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_eq_getElem hj, List.getElem?_eq_none (Nat.le_of_not_lt hi'),
          Option.map_some, Option.map_none, Option.getD_some, Option.getD_none,
          List.getElem?_nil]
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_eq_none (Nat.le_of_not_lt hi'),
          List.getElem?_eq_none (Nat.le_of_not_lt hj), Option.map_none, Option.getD_none,
          List.getElem?_nil]

/-- Polynomial-time many-one reduction mapping a `Clique` instance `(G, k)` to a symmetric
rational matrix `M` such that `(G, k) ∈ Clique ↔ M ∈ NonCopositive`. -/
def cliqueToSymRatMatrix (gk : Graph × ℕ) : SymRatMatrix where
  rows := cliqueToRows gk
  square := cliqueToRows_square gk
  symm := cliqueToRows_symm gk

@[simp]
theorem cliqueToSymRatMatrix_rows (gk : Graph × ℕ) :
    (cliqueToSymRatMatrix gk).rows = cliqueToRows gk := by
  dsimp only [cliqueToSymRatMatrix]

private def singletonSymRatMatrix (c : ℚ) : SymRatMatrix where
  rows := [[c]]
  square r hr := by
    simp only [List.mem_singleton] at hr
    subst hr
    rfl
  symm i j := by
    rcases i with _ | i <;> rcases j with _ | j <;>
      simp only [List.getD_cons_zero, List.getD_cons_succ, List.getD_nil]

private theorem singleton_neg_nonCopositive :
    singletonSymRatMatrix (-1) ∈ NonCopositive := by
  intro hcop
  have hlen : (singletonSymRatMatrix (-1)).rows.length = 1 := rfl
  let i0 : Fin (singletonSymRatMatrix (-1)).rows.length := ⟨0, by omega⟩
  have h := hcop (fun _ => (1 : ℚ)) fun _ => by norm_num
  dsimp only [SymRatMatrix.toMatrix, dotProduct, Matrix.mulVec, Matrix.of_apply] at h
  rw [Finset.sum_eq_single i0
    (fun b _ hb => absurd (Fin.ext (by omega : b.1 = i0.1)) hb)
    (fun hm => absurd (Finset.mem_univ _) hm)] at h
  rw [Finset.sum_eq_single i0
    (fun b _ hb => absurd (Fin.ext (by omega : b.1 = i0.1)) hb)
    (fun hm => absurd (Finset.mem_univ _) hm)] at h
  dsimp only [singletonSymRatMatrix, i0] at h
  simp only [List.getD_cons_zero] at h
  norm_num at h

private theorem singleton_pos_copositive :
    singletonSymRatMatrix 1 ∈ Copositive := by
  intro x hx
  have hlen : (singletonSymRatMatrix 1).rows.length = 1 := rfl
  let i0 : Fin (singletonSymRatMatrix 1).rows.length := ⟨0, by omega⟩
  dsimp only [SymRatMatrix.toMatrix, dotProduct, Matrix.mulVec, Matrix.of_apply]
  rw [Finset.sum_eq_single i0
    (fun b _ hb => absurd (Fin.ext (by omega : b.1 = i0.1)) hb)
    (fun hm => absurd (Finset.mem_univ _) hm)]
  rw [Finset.sum_eq_single i0
    (fun b _ hb => absurd (Fin.ext (by omega : b.1 = i0.1)) hb)
    (fun hm => absurd (Finset.mem_univ _) hm)]
  dsimp only [singletonSymRatMatrix, i0]
  simp only [List.getD_cons_zero, one_mul]
  exact mul_nonneg (hx i0) (hx i0)

theorem cliqueToSymRatMatrix_mem_iff (gk : Graph × ℕ) :
    gk ∈ Clique ↔ cliqueToSymRatMatrix gk ∈ NonCopositive := by
  rcases gk with ⟨G, k⟩
  by_cases hk0 : k = 0
  · subst hk0
    have hin : (G, 0) ∈ Clique := by
      rw [mem_Clique_iff]
      exact ⟨∅, fun _ h => absurd h (Finset.notMem_empty _),
        by simp only [SimpleGraph.isNClique_iff, Finset.coe_empty, SimpleGraph.isClique_empty,
          Finset.card_empty, and_self]⟩
    have hM : cliqueToSymRatMatrix (G, 0) ∈ NonCopositive := by
      have hrows : (cliqueToSymRatMatrix (G, 0)).rows = (singletonSymRatMatrix (-1)).rows := by
        simp only [cliqueToSymRatMatrix_rows, cliqueToRows, ↓reduceIte, singletonSymRatMatrix]
      rw [SymRatMatrix.ext hrows]
      exact singleton_neg_nonCopositive
    exact iff_of_true hin hM
  · by_cases hemp : G.distinctVertices.isEmpty = true
    · have hnot : (G, k) ∉ Clique := by
        intro hmem
        rw [mem_Clique_iff] at hmem
        obtain ⟨S, hSG, hS⟩ := hmem
        have hpos : 0 < S.card := by rw [hS.card_eq]; omega
        obtain ⟨v, hvS⟩ := Finset.card_pos.1 hpos
        have hv : v ∈ G.distinctVertices := Graph.mem_distinctVertices.2 (hSG v hvS)
        have hnil : G.distinctVertices = [] := List.isEmpty_iff.1 hemp
        rw [hnil] at hv
        cases hv
      have hM : cliqueToSymRatMatrix (G, k) ∉ NonCopositive := by
        have hrows : (cliqueToSymRatMatrix (G, k)).rows = (singletonSymRatMatrix 1).rows := by
          simp only [cliqueToSymRatMatrix_rows, cliqueToRows, hk0, ↓reduceIte, hemp,
            singletonSymRatMatrix]
        rw [SymRatMatrix.ext hrows]
        exact fun h => h singleton_pos_copositive
      exact iff_of_false hnot hM
    · by_cases hk1 : k = 1
      · subst hk1
        have hne : G.distinctVertices ≠ [] := by
          intro hnil
          apply hemp
          simp only [hnil, List.isEmpty_nil]
        obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil G.distinctVertices hne
        have hvG : v ∈ G.1 := Graph.mem_distinctVertices.1 hv
        have hin : (G, 1) ∈ Clique := by
          rw [mem_Clique_iff]
          refine ⟨{v}, fun _ hw => by simp only [Finset.mem_singleton] at hw; rwa [hw], ?_⟩
          simp only [SimpleGraph.isNClique_iff, Finset.coe_singleton,
            SimpleGraph.isClique_singleton, Finset.card_singleton, and_self]
        have hM : cliqueToSymRatMatrix (G, 1) ∈ NonCopositive := by
          have hrows : (cliqueToSymRatMatrix (G, 1)).rows = (singletonSymRatMatrix (-1)).rows := by
            simp only [cliqueToSymRatMatrix_rows, cliqueToRows, hk0, hemp, Bool.false_eq_true,
              ↓reduceIte, singletonSymRatMatrix]
          rw [SymRatMatrix.ext hrows]
          exact singleton_neg_nonCopositive
        exact iff_of_true hin hM
      · have hk2 : 2 ≤ k := by omega
        have hne : G.distinctVertices ≠ [] := by
          intro hnil
          apply hemp
          simp only [hnil, List.isEmpty_nil]
        have hn_pos : 0 < G.distinctVertices.length := List.length_pos_of_ne_nil hne
        let _ : Nonempty (Fin G.distinctVertices.length) := ⟨⟨0, hn_pos⟩⟩
        let ι : Fin G.distinctVertices.length ↪ ℕ :=
          ⟨fun i => G.distinctVertices[i.1],
            fun i j hij => Fin.ext (G.nodup_distinctVertices.getElem_inj_iff.1 hij)⟩
        let H : SimpleGraph (Fin G.distinctVertices.length) := G.toSimpleGraph.comap ι
        let _ : DecidableRel H.Adj := fun i j =>
          decidable_of_iff (G.adjBool (ι i) (ι j) = true)
            (by
              simp only [H, SimpleGraph.comap_adj]
              exact G.adjBool_eq_true_iff (ι i) (ι j))
        have hrows_eq :
            (cliqueToSymRatMatrix (G, k)).rows =
              G.distinctVertices.map fun u =>
                G.distinctVertices.map fun v => cliqueEntry G k u v := by
          simp only [cliqueToSymRatMatrix_rows, cliqueToRows, hk0, hemp, Bool.false_eq_true, hk1,
            ↓reduceIte]
        have hlen_rows : (cliqueToSymRatMatrix (G, k)).rows.length = G.distinctVertices.length := by
          rw [hrows_eq, List.length_map]
        let eFin : Fin (cliqueToSymRatMatrix (G, k)).rows.length ≃ Fin G.distinctVertices.length :=
          ⟨Fin.cast hlen_rows, Fin.cast hlen_rows.symm, fun _ => rfl, fun _ => rfl⟩
        have hmat_eq :
            ∀ i j : Fin (cliqueToSymRatMatrix (G, k)).rows.length,
              (cliqueToSymRatMatrix (G, k)).toMatrix i j =
                ((H.copositiveCliqueMatrix k).map (Int.cast : ℤ → ℚ)) (eFin i) (eFin j) := by
          intro i j
          have hi : i.1 < G.distinctVertices.length := hlen_rows ▸ i.2
          have hj : j.1 < G.distinctVertices.length := hlen_rows ▸ j.2
          have hget1 : (cliqueToSymRatMatrix (G, k)).rows.getD i.1 [] =
              G.distinctVertices.map fun v => cliqueEntry G k G.distinctVertices[i.1] v := by
            have hrows_get := congrArg (fun l => List.getD l i.1 []) hrows_eq
            rw [hrows_get, List.getD_eq_getElem?_getD, List.getElem?_map,
              List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some]
          have hget2 :
              (G.distinctVertices.map fun v =>
                  cliqueEntry G k G.distinctVertices[i.1] v).getD j.1 0 =
                cliqueEntry G k G.distinctVertices[i.1] G.distinctVertices[j.1] := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj,
              Option.map_some, Option.getD_some]
          dsimp only [SymRatMatrix.toMatrix, Matrix.of_apply]
          rw [hget1, hget2, Matrix.map_apply, SimpleGraph.copositiveCliqueMatrix_apply]
          have hnodup := G.nodup_distinctVertices
          by_cases hij : eFin i = eFin j
          · have hval : i.1 = j.1 := congrArg Fin.val (eFin.injective hij)
            have hnotadj : ¬ H.Adj (eFin i) (eFin j) := by
              rw [hij]
              exact H.loopless.irrefl _
            simp only [cliqueEntry, hval, ↓reduceIte, hnotadj, Int.cast_sub, Int.cast_natCast,
              Int.cast_ofNat]
          · have hij_val : G.distinctVertices[i.1] ≠ G.distinctVertices[j.1] := by
              intro hval
              have hinj := hnodup.getElem_inj_iff.1 hval
              exact hij (Fin.ext hinj)
            have hadj_iff :
                H.Adj (eFin i) (eFin j) ↔
                  G.adjBool G.distinctVertices[i.1] G.distinctVertices[j.1] = true := by
              dsimp only [H, SimpleGraph.comap_adj, ι, eFin]
              exact (G.adjBool_eq_true_iff G.distinctVertices[i.1] G.distinctVertices[j.1]).symm
            by_cases hadj : G.adjBool G.distinctVertices[i.1] G.distinctVertices[j.1] = true
            · have hH : H.Adj (eFin i) (eFin j) := hadj_iff.2 hadj
              simp only [cliqueEntry, hij_val, ↓reduceIte, hadj, hH, Int.cast_neg, Int.cast_one]
            · have hH : ¬ H.Adj (eFin i) (eFin j) := fun h => hadj (hadj_iff.1 h)
              simp only [cliqueEntry, hij_val, ↓reduceIte, hadj, Bool.false_eq_true, hH,
                Int.cast_sub, Int.cast_natCast, Int.cast_ofNat]
        have hnc_iff :
            cliqueToSymRatMatrix (G, k) ∈ NonCopositive ↔
              ∃ x : Fin G.distinctVertices.length → ℚ, (∀ v, 0 ≤ x v) ∧
                x ⬝ᵥ ((H.copositiveCliqueMatrix k).map (Int.cast : ℤ → ℚ) *ᵥ x) < 0 := by
          have hsub : (cliqueToSymRatMatrix (G, k)).toMatrix =
              ((H.copositiveCliqueMatrix k).map (Int.cast : ℤ → ℚ)).submatrix eFin eFin :=
            Matrix.ext fun i j => hmat_eq i j
          rw [mem_NonCopositive_iff, hsub, Matrix.IsCopositive.submatrix_equiv_iff,
            Matrix.IsCopositive]
          push Not
          rfl
        have hclique_iff : (G, k) ∈ Clique ↔ k ≤ H.cliqueNum := by
          rw [mem_Clique_iff]
          constructor
          · rintro ⟨S, hSG, hS⟩
            let S' : Finset (Fin G.distinctVertices.length) :=
              Finset.univ.filter fun i => ι i ∈ S
            have hS'_img : S'.image ι = S := by
              ext v
              simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, S']
              constructor
              · rintro ⟨i, hi, rfl⟩
                exact hi
              · intro hvS
                obtain ⟨idx, hidx, rfl⟩ :=
                  List.mem_iff_getElem.1 (Graph.mem_distinctVertices.2 (hSG v hvS))
                exact ⟨⟨idx, hidx⟩, hvS, rfl⟩
            have hS'clique : H.IsClique (S' : Set (Fin G.distinctVertices.length)) := by
              intro i hi j hj hij
              simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, S'] at hi hj
              exact hS.isClique hi hj (ι.injective.ne hij)
            have hcard : S'.card = k := by
              have hcard_eq : S'.card = (S'.image ι).card :=
                (Finset.card_image_of_injective S' ι.injective).symm
              rw [hcard_eq, hS'_img, hS.card_eq]
            rw [← hcard]
            exact hS'clique.card_le_cliqueNum
          · intro hle
            obtain ⟨S_max, hS_max⟩ := H.exists_isNClique_cliqueNum
            obtain ⟨S', hS'_sub, hS'_card⟩ :=
              Finset.exists_subset_card_eq (n := k) (by rw [hS_max.card_eq]; exact hle)
            refine ⟨S'.map ι, ?_, ?_⟩
            · intro v hv
              obtain ⟨i, _, rfl⟩ := Finset.mem_map.1 hv
              exact Graph.mem_distinctVertices.1 (List.getElem_mem i.2)
            · rw [SimpleGraph.isNClique_iff]
              refine ⟨?_, ?_⟩
              · intro u hu v hv hij
                rw [Finset.coe_map, Set.mem_image] at hu hv
                rcases hu with ⟨i, hi, rfl⟩
                rcases hv with ⟨j, hj, rfl⟩
                exact hS_max.isClique (hS'_sub hi) (hS'_sub hj) fun h => hij (congrArg ι h)
              · rw [Finset.card_map, hS'_card]
        rw [hclique_iff, hnc_iff]
        exact (SimpleGraph.exists_nonneg_dotProduct_copositiveCliqueMatrix_lt_zero_iff H hk2).symm

private theorem computableInPolyTime_distinctVertices_gk :
    ComputableInPolyTime (fun gk : Graph × ℕ => gk.1.distinctVertices) encClique (encList encNat) :=
  Graph.computableInPolyTime_distinctVertices.comp (ComputableInPolyTime.fst encGraph encNat)

private theorem computableInPolyTime_toRows :
    ComputableInPolyTime cliqueToRows encClique encRatMatrixRows := by
  have hk0 :
      ComputableInPolyTime (fun gk : Graph × ℕ => decide (gk.2 = 0)) encClique encBool :=
    (ComputableTidilyInPolyTime.decide_eq encNat).computableInPolyTime.comp
      (ComputableInPolyTime.prod (ComputableInPolyTime.snd encGraph encNat)
        (ComputableInPolyTime.const 0))
  have hk1 :
      ComputableInPolyTime (fun gk : Graph × ℕ => decide (gk.2 = 1)) encClique encBool :=
    (ComputableTidilyInPolyTime.decide_eq encNat).computableInPolyTime.comp
      (ComputableInPolyTime.prod (ComputableInPolyTime.snd encGraph encNat)
        (ComputableInPolyTime.const 1))
  have hemp :
      ComputableInPolyTime (fun gk : Graph × ℕ => gk.1.distinctVertices.isEmpty)
        encClique encBool := by
    have hlen : ComputableInPolyTime (fun gk : Graph × ℕ => gk.1.distinctVertices.length)
        encClique encUnary :=
      (ComputableTidilyInPolyTime.length_list encNat).computableInPolyTime.comp
        computableInPolyTime_distinctVertices_gk
    have hdec :
        ComputableInPolyTime (fun gk : Graph × ℕ => decide (gk.1.distinctVertices.length = 0))
          encClique encBool :=
      (ComputableTidilyInPolyTime.decide_eq encUnary).computableInPolyTime.comp
        (ComputableInPolyTime.prod hlen (ComputableInPolyTime.const 0))
    exact hdec.of_enc_eq fun gk => by
      simp only [encBool_apply]
      cases gk.1.distinctVertices <;> rfl
  have hk2Rat :
      ComputableInPolyTime (fun gk : Graph × ℕ => (((gk.2 : ℤ) - 2 : ℤ) : ℚ)) encClique encRat :=
    computableInPolyTime_intCastRat.comp
      (by fun_prop :
        ComputableInPolyTime (fun gk : Graph × ℕ => (gk.2 : ℤ) - 2) encClique encIntBin)
  have hentry :
      ComputableTidilyInPolyTime
        (fun x : ((Graph × ℕ) × ℕ) × ℕ => cliqueEntry x.1.1.1 x.1.1.2 x.1.2 x.2)
        (encPair (encPair encClique encNat) encNat) encRat := by
    have heq_uv :
        ComputableInPolyTime (fun x : ((Graph × ℕ) × ℕ) × ℕ => decide (x.1.2 = x.2))
          (encPair (encPair encClique encNat) encNat) encBool :=
      (ComputableTidilyInPolyTime.decide_eq encNat).computableInPolyTime.comp
        (ComputableInPolyTime.prod
          ((ComputableInPolyTime.snd encClique encNat).comp (ComputableInPolyTime.fst _ _))
          (ComputableInPolyTime.snd _ _))
    have hadj :
        ComputableInPolyTime
          (fun x : ((Graph × ℕ) × ℕ) × ℕ => x.1.1.1.adjBool x.1.2 x.2)
          (encPair (encPair encClique encNat) encNat) encBool :=
      Graph.computableInPolyTime_adjBool_comp
        ((ComputableInPolyTime.fst encGraph encNat).comp
          ((ComputableInPolyTime.fst encClique encNat).comp (ComputableInPolyTime.fst _ _)))
        ((ComputableInPolyTime.snd encClique encNat).comp (ComputableInPolyTime.fst _ _))
        (ComputableInPolyTime.snd _ _)
    have hk2' :
        ComputableInPolyTime (fun x : ((Graph × ℕ) × ℕ) × ℕ => (((x.1.1.2 : ℤ) - 2 : ℤ) : ℚ))
          (encPair (encPair encClique encNat) encNat) encRat :=
      hk2Rat.comp ((ComputableInPolyTime.fst encClique encNat).comp (ComputableInPolyTime.fst _ _))
    have hinner :
        ComputableInPolyTime
          (fun x : ((Graph × ℕ) × ℕ) × ℕ =>
            if x.1.1.1.adjBool x.1.2 x.2 then (-1 : ℚ)
            else (((x.1.1.2 : ℤ) - 2 : ℤ) : ℚ))
          (encPair (encPair encClique encNat) encNat) encRat :=
      ComputableInPolyTime.ite' hadj (ComputableInPolyTime.const (-1)) hk2'
    have hfull :
        ComputableInPolyTime
          (fun x : ((Graph × ℕ) × ℕ) × ℕ =>
            if decide (x.1.2 = x.2) then (((x.1.1.2 : ℤ) - 2 : ℤ) : ℚ)
            else if x.1.1.1.adjBool x.1.2 x.2 then (-1 : ℚ)
            else (((x.1.1.2 : ℤ) - 2 : ℤ) : ℚ))
          (encPair (encPair encClique encNat) encNat) encRat :=
      ComputableInPolyTime.ite' heq_uv hk2' hinner
    exact (hfull.of_enc_eq fun x => by
      simp only [cliqueEntry, decide_eq_true_eq]).tidy
  have hrow :
      ComputableTidilyInPolyTime
        (fun p : (Graph × ℕ) × ℕ =>
          p.1.1.distinctVertices.map fun v => cliqueEntry p.1.1 p.1.2 p.2 v)
        (encPair encClique encNat) (encList encRat) :=
    ComputableTidilyInPolyTime.mapWithInput
      (computableInPolyTime_distinctVertices_gk.comp
        (ComputableInPolyTime.fst encClique encNat)).tidy
      hentry
  have hmat :
      ComputableInPolyTime
        (fun gk : Graph × ℕ =>
          gk.1.distinctVertices.map fun u =>
            gk.1.distinctVertices.map fun v => cliqueEntry gk.1 gk.2 u v)
        encClique encRatMatrixRows :=
    (ComputableTidilyInPolyTime.mapWithInput
      computableInPolyTime_distinctVertices_gk.tidy hrow).computableInPolyTime
  have hb1 :
      ComputableInPolyTime
        (fun gk : Graph × ℕ =>
          if decide (gk.2 = 1) then [[(-1 : ℚ)]]
          else
            gk.1.distinctVertices.map fun u =>
              gk.1.distinctVertices.map fun v => cliqueEntry gk.1 gk.2 u v)
        encClique encRatMatrixRows :=
    ComputableInPolyTime.ite' hk1 (ComputableInPolyTime.const [[(-1 : ℚ)]]) hmat
  have hb2 :
      ComputableInPolyTime
        (fun gk : Graph × ℕ =>
          if gk.1.distinctVertices.isEmpty then [[(1 : ℚ)]]
          else if decide (gk.2 = 1) then [[(-1 : ℚ)]]
          else
            gk.1.distinctVertices.map fun u =>
              gk.1.distinctVertices.map fun v => cliqueEntry gk.1 gk.2 u v)
        encClique encRatMatrixRows :=
    ComputableInPolyTime.ite' hemp (ComputableInPolyTime.const [[(1 : ℚ)]]) hb1
  exact (ComputableInPolyTime.ite' hk0 (ComputableInPolyTime.const [[(-1 : ℚ)]]) hb2).of_enc_eq
    fun gk => by
      rcases gk with ⟨G, k⟩
      simp only [cliqueToRows, decide_eq_true_eq]

theorem computableInPolyTime_cliqueToSymRatMatrix :
    ComputableInPolyTime cliqueToSymRatMatrix encClique encSymRatMatrix :=
  computableInPolyTime_toRows.of_enc_eq fun _ => rfl

/-- Polynomial-time many-one reduction from `Clique` to `NonCopositive`. -/
theorem polyTimeReducible_Clique_NonCopositive :
    PolyTimeReducible encClique encSymRatMatrix Clique NonCopositive :=
  ⟨cliqueToSymRatMatrix, computableInPolyTime_cliqueToSymRatMatrix, cliqueToSymRatMatrix_mem_iff⟩

/-- `NonCopositive` is `NP`-hard (proved here via `Clique` and Motzkin–Straus; [MurtyKabadi1987]
establishes completeness in the literature, reported via subset sum). -/
theorem NonCopositive_npHard : NPHard encSymRatMatrix NonCopositive :=
  HardUnder.trans (fun _ _ h₁ h₂ => h₁.trans h₂) Clique_npHard
    polyTimeReducible_Clique_NonCopositive

/-- `NonCopositive` is `NP`-complete (completeness statement credited to [MurtyKabadi1987];
library proof combines bounded integer witness verification with `Clique`/Motzkin–Straus). -/
theorem NonCopositive_npComplete : NPComplete encSymRatMatrix NonCopositive :=
  ⟨NonCopositive.mem_NP, NonCopositive_npHard⟩

/-- `Copositive` is `coNP`-hard (proved here via `Clique` and Motzkin–Straus). -/
theorem Copositive_coNPHard : coNPHard encSymRatMatrix Copositive := by
  rw [coNPHard, Copositive_eq_compl]
  exact HardUnder.compl (fun _ _ h => h.compl) (fun _ _ h => h) NonCopositive_npHard

/-- `Copositive` is `coNP`-complete (completeness statement credited to [MurtyKabadi1987];
library proof uses `NonCopositive` membership and the `Clique`/Motzkin–Straus reduction). -/
theorem Copositive_coNPComplete : coNPComplete encSymRatMatrix Copositive :=
  ⟨Copositive.mem_coNP, Copositive_coNPHard⟩

/-! ### Optional rational arithmetic circuit input encoding -/

/-- Binary encoding of rational arithmetic circuits with `m` outputs over `encRat`. -/
abbrev encRatArithCircuit (m : ℕ) :
    (Σ n, Cslib.Circuits.Circuit (Cslib.Circuits.arithSignature ℚ) n m) ↪ List Bool :=
  Cslib.Circuits.Circuit.encCircuit (Cslib.Circuits.ArithOp.encoding encRat) m

/-- Binary encoding of `(C, x)` pairs for rational arithmetic circuits with `m` outputs and
rational input vectors `x : List ℚ`. -/
abbrev encRatArithCircuitInput (m : ℕ) :
    (Σ n, Cslib.Circuits.Circuit (Cslib.Circuits.arithSignature ℚ) n m) × List ℚ ↪ List Bool :=
  encPair (encRatArithCircuit m) (encList encRat)

end Cslib.Complexity
