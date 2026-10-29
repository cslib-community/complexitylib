/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Rational.Runtime.Determinant
public import Complexity.Computability.PolyTime.Int.ExactDiv
public import Complexity.Foundations.Data.Polynomial.HermiteInterpolation
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Factorial
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Executable confluent Hermite Cramer recovery

Executable list-of-rows builders and plain `Turing.MultiTapeTM.ComputableInPolyTime` certificates
for recovering the integer constant term `H(0) = (H_zero : ℚ)` of a rational polynomial
`H ∈ ℚ[X]` with `H.natDegree < N` (`N = nodes.length * J`) from a `nodes.length × J` table `jets`
(`jets.length = nodes.length`, each row of length `J`) of integer-scaled order-`J` Taylor jets
`Ω · [z ^ j] H(t_i + z)` with nonzero scale `Ω ≠ 0` at distinct integer nodes
`nodes = [t_0, …, t_{Q-1}]` (`nodes.Nodup`).

Following Appendix B.3, equation (B.1), of [OpenAI2026ETH], `hermiteRows nodes J` tabulates the
`N × N` integer confluent Vandermonde matrix `V` (`Polynomial.hermiteMatrix`), `cramerColZeroRows`
replaces column `0` with the flattened scaled jet vector `b = Ω y` to form `V_{(0)}`, and
`hermiteRecoverZero` evaluates `N_H = detRows V_{(0)}` and `D_H = detRows V` via the division-free
staged determinant of `Complexity/Computability/Circuit/Rational/Runtime/Determinant.lean`
before performing the single total integer
division `N_H / (Ω · D_H)` (`Int.ediv`, exact when `nodes.Nodup` and `Ω ≠ 0`, and returning `0`
when `Ω = 0` or `D_H = 0`). `hermiteRecoverModPowTwo` composes this recovery with `Int.modPowTwo`
to extract bounded counts modulo `2 ^ ℓ`.

## Main definitions

* `Cslib.Circuits.Rational.hermiteRows`: executable `(nodes.length * J) × (nodes.length * J)`
  integer confluent Vandermonde matrix as `List (List ℤ)`.
* `Cslib.Circuits.Rational.cramerColZeroRows`: replace column `0` of each row `k` with `rhs[k]`.
* `Cslib.Circuits.Rational.hermiteRecoverZero`: recover integer `H(0) = det V_{(0)} / (Ω · det V)`
  for nonzero `Ω ≠ 0` and distinct `nodes` via `detRows` and total `Int.ediv` (returning `0` when
  `Ω = 0` or `det V = 0`).
* `Cslib.Circuits.Rational.hermiteRecoverModPowTwo`: recover the least nonnegative residue of
  integer `H(0)` modulo `2 ^ ℓ` under the same `Ω ≠ 0`, `nodes.Nodup`, degree, and jet-shape
  hypotheses.

## Main results

* `Cslib.Circuits.Rational.length_hermiteRows`,
  `Cslib.Circuits.Rational.length_of_mem_hermiteRows`,
  `Cslib.Circuits.Rational.length_cramerColZeroRows`,
  `Cslib.Circuits.Rational.length_of_mem_cramerColZeroRows`: shape well-formedness.
* `Cslib.Circuits.Rational.ofRows_hermiteRows`,
  `Cslib.Circuits.Rational.detRows_hermiteRows`,
  `Cslib.Circuits.Rational.detRows_hermiteRows_ne_zero`: `ofRows` and `detRows` agreement with
  `Polynomial.hermiteMatrix` and nonsingularity for `nodes.Nodup`.
* `Cslib.Circuits.Rational.detRows_cramerColZeroRows_eq_mul_eval_zero`,
  `Cslib.Circuits.Rational.hermiteRecoverZero_eq_of_rowEntry`,
  `Cslib.Circuits.Rational.hermiteRecoverZero_eq`,
  `Cslib.Circuits.Rational.hermiteRecoverModPowTwo_eq`,
  `Cslib.Circuits.Rational.modPowTwo_sum_hermiteRecoverZero_eq`: exact Cramer numerator identity
  and integer / modular recovery of `H(0)` and coordinate sums.
* `Cslib.Circuits.Rational.intBits_tdiv_le`, `Cslib.Circuits.Rational.intBits_ediv_le`,
  `Cslib.Circuits.Rational.intBits_emod_le_of_ne_zero`,
  `Cslib.Circuits.Rational.intBits_emod_le_add_one_of_ne_zero`,
  `Cslib.Circuits.Rational.intBits_emod_le_max`,
  `Cslib.Circuits.Rational.intBits_modPowTwo_le`,
  `Cslib.Circuits.Rational.intBits_le_of_mem_hermiteRows`,
  `Cslib.Circuits.Rational.intBits_le_of_mem_cramerColZeroRows`: sign-magnitude bit-length bounds
  for division, modular reduction, and Hermite/Cramer table entries.
* `Cslib.Circuits.Rational.computableInPolyTime_hermiteRows`,
  `Cslib.Circuits.Rational.hermiteRows_polytime`,
  `Cslib.Circuits.Rational.computableInPolyTime_cramerColZeroRows`,
  `Cslib.Circuits.Rational.cramerColZeroRows_polytime`,
  `Cslib.Circuits.Rational.computableInPolyTime_hermiteRecoverZero`,
  `Cslib.Circuits.Rational.hermiteRecoverZero_polytime`,
  `Cslib.Circuits.Rational.computableInPolyTime_hermiteRecoverModPowTwo`,
  `Cslib.Circuits.Rational.hermiteRecoverModPowTwo_polytime`,
  `Cslib.Circuits.Rational.computableInPolyTime_modPowTwo_sum_hermiteRecoverZero`: plain
  polynomial-time certificates.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH]
-/

@[expose] public section

namespace Cslib.Circuits.Rational

/-! ### Executable list-of-rows builders -/

/-- The `(nodes.length * J) × (nodes.length * J)` integer confluent Vandermonde (Hermite) matrix
at `nodes` of uniform order `J`, stored in row-major `(node, jet-order)` order: row `i * J + j`
and column `m` holds `(m.choose j : ℤ) * nodes[i] ^ (m - j)`, which vanishes for `m < j`. -/
def hermiteRows (nodes : List ℤ) (J : ℕ) : List (List ℤ) :=
  nodes.flatMap fun t =>
    (List.range J).map fun j =>
      (List.range (nodes.length * J)).map fun m => (m.choose j : ℤ) * t ^ (m - j)

/-- Replace column `0` of each row `k` of `mat` with `rhs.getD k 0`, keeping the tail of each row
unchanged. -/
def cramerColZeroRows (mat : List (List ℤ)) (rhs : List ℤ) : List (List ℤ) :=
  mat.zipIdx.map fun p => rhs.getD p.2 0 :: p.1.tail

/-- Recover the integer value `H(0) = (H_zero : ℚ)` of `H ∈ ℚ[X]` with
`H.natDegree < nodes.length * J` from a `nodes.length × J` table `jets`
(`jets.length = nodes.length`, each row of length `J`) of its `Ω`-scaled order-`J` Taylor jets
with nonzero scale `Ω ≠ 0` at distinct integer `nodes` (`nodes.Nodup`), via Cramer's rule,
`detRows`, and total `Int.ediv` (returning `0` when `Ω = 0` or
`detRows (hermiteRows nodes J) = 0`; see `hermiteRecoverZero_eq`). -/
def hermiteRecoverZero (nodes : List ℤ) (J : ℕ) (Ω : ℤ) (jets : List (List ℤ)) : ℤ :=
  (detRows (cramerColZeroRows (hermiteRows nodes J) jets.flatten)).ediv
    (Ω * detRows (hermiteRows nodes J))

/-- Recover the least nonnegative residue of integer `H(0)` modulo `2 ^ ℓ` from `Ω`-scaled
order-`J` Taylor jets `jets` under the hypotheses of `hermiteRecoverZero_eq` (`nodes.Nodup`,
`Ω ≠ 0`, `H.natDegree < nodes.length * J`, integer `H(0)`, and `nodes.length × J` jet shape; see
`hermiteRecoverModPowTwo_eq`). -/
def hermiteRecoverModPowTwo (nodes : List ℤ) (J ℓ : ℕ) (Ω : ℤ) (jets : List (List ℤ)) : ℤ :=
  (hermiteRecoverZero nodes J Ω jets).modPowTwo ℓ

/-! ### Shape and well-formedness -/

/-- `hermiteRows nodes J` has `nodes.length * J` rows. -/
@[simp]
theorem length_hermiteRows (nodes : List ℤ) (J : ℕ) :
    (hermiteRows nodes J).length = nodes.length * J := by
  simp [hermiteRows, List.length_flatMap]

/-- Every row of `hermiteRows nodes J` has length `nodes.length * J`. -/
theorem length_of_mem_hermiteRows {nodes : List ℤ} {J : ℕ} {row : List ℤ}
    (hrow : row ∈ hermiteRows nodes J) : row.length = nodes.length * J := by
  rw [hermiteRows, List.mem_flatMap] at hrow
  obtain ⟨_, -, hmem⟩ := hrow
  obtain ⟨_, -, rfl⟩ := List.mem_map.mp hmem
  simp

/-- `cramerColZeroRows mat rhs` preserves the number of rows of `mat`. -/
@[simp]
theorem length_cramerColZeroRows (mat : List (List ℤ)) (rhs : List ℤ) :
    (cramerColZeroRows mat rhs).length = mat.length := by
  simp [cramerColZeroRows]

/-- If every row of `mat` has length `mat.length`, then every row of `cramerColZeroRows mat rhs`
has length `mat.length`. -/
theorem length_of_mem_cramerColZeroRows {mat : List (List ℤ)} {rhs : List ℤ}
    (hmat : ∀ r ∈ mat, r.length = mat.length) {row : List ℤ}
    (hrow : row ∈ cramerColZeroRows mat rhs) : row.length = mat.length := by
  rw [cramerColZeroRows, List.mem_map] at hrow
  obtain ⟨⟨r, k⟩, hmem, rfl⟩ := hrow
  have hr_mem : r ∈ mat := (List.mem_zipIdx hmem).2.2 ▸ List.getElem_mem _
  have hr_len : r.length = mat.length := hmat r hr_mem
  have hpos : 0 < mat.length := by
    rcases mat with _ | ⟨_, _⟩
    · simp at hr_mem
    · simp
  simp only [List.length_cons, List.length_tail, hr_len]
  omega

/-- Every row of `cramerColZeroRows (hermiteRows nodes J) rhs` has length `nodes.length * J`. -/
theorem length_of_mem_cramerColZeroRows_hermiteRows {nodes : List ℤ} {J : ℕ} {rhs : List ℤ}
    {row : List ℤ} (hrow : row ∈ cramerColZeroRows (hermiteRows nodes J) rhs) :
    row.length = nodes.length * J := by
  simpa only [length_hermiteRows] using length_of_mem_cramerColZeroRows
    (fun _ hr => by rw [length_of_mem_hermiteRows hr, length_hermiteRows]) hrow

/-! ### Agreement with `Polynomial.hermiteMatrix` and `Matrix.updateCol` -/

private lemma getD_flatMap_uniform {α β : Type*} (l : List α) (J : ℕ) (f : α → List β)
    (hf : ∀ a ∈ l, (f a).length = J) (d : β) (i : Fin l.length) (j : Fin J) :
    (l.flatMap f).getD (j.val + J * i.val) d = (f l[i]).getD j.val d := by
  induction l with
  | nil => exact i.elim0
  | cons a tl ih =>
    have ha : (f a).length = J := hf a List.mem_cons_self
    refine Fin.cases ?_ (fun i' => ?_) i
    · exact List.getD_append (f a) (tl.flatMap f) d j.val (ha ▸ j.isLt)
    · have hidx : j.val + J * (Fin.succ i').val = (j.val + J * i'.val) + (f a).length := by
        simp only [Fin.val_succ, ha]
        ring
      change (f a ++ tl.flatMap f).getD (j.val + J * (Fin.succ i').val) d = (f tl[i']).getD j.val d
      rw [hidx, List.getD_append_right (f a) (tl.flatMap f) d _ (Nat.le_add_left _ _),
        Nat.add_sub_cancel]
      exact ih (fun b hb => hf b (List.mem_cons_of_mem _ hb)) i'

/-- Entry `(finProdFinEquiv r, finProdFinEquiv c)` of `hermiteRows nodes J` equals entry `(r, c)`
of `Polynomial.hermiteMatrix`. -/
theorem rowEntry_hermiteRows (nodes : List ℤ) (J : ℕ)
    (r c : Fin nodes.length × Fin J) :
    rowEntry (hermiteRows nodes J) (finProdFinEquiv r) (finProdFinEquiv c) =
      Polynomial.hermiteMatrix (fun i : Fin nodes.length => nodes[i]) J r c := by
  obtain ⟨i, j⟩ := r
  have hr_eq : (finProdFinEquiv (i, j) : ℕ) = j.val + J * i.val := rfl
  have hc_lt : (finProdFinEquiv c : ℕ) < nodes.length * J := (finProdFinEquiv c).isLt
  rw [rowEntry, hermiteRows, hr_eq,
    getD_flatMap_uniform nodes J _ (fun _ _ => by simp) [] i j]
  simp only [List.getD_eq_getElem?_getD, j.isLt, hc_lt, List.getElem?_map,
    List.getElem?_range, Option.map_some, Option.getD_some, Polynomial.hermiteMatrix_apply]

/-- `ofRows (hermiteRows nodes J)` is `Polynomial.hermiteMatrix` reindexed along
`finProdFinEquiv`. -/
theorem ofRows_hermiteRows (nodes : List ℤ) (J : ℕ) :
    ofRows (hermiteRows nodes J) =
      Matrix.reindex (finProdFinEquiv.trans (finCongr (length_hermiteRows nodes J).symm))
        (finProdFinEquiv.trans (finCongr (length_hermiteRows nodes J).symm))
        (Polynomial.hermiteMatrix (fun i : Fin nodes.length => nodes[i]) J) := by
  set e := finProdFinEquiv.trans (finCongr (length_hermiteRows nodes J).symm)
  ext k m
  obtain ⟨r, rfl⟩ := e.surjective k
  obtain ⟨c, rfl⟩ := e.surjective m
  have her : (e r : ℕ) = (finProdFinEquiv r : ℕ) := rfl
  have hec : (e c : ℕ) = (finProdFinEquiv c : ℕ) := rfl
  simp only [ofRows, Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, her, hec, rowEntry_hermiteRows]

/-- `detRows (hermiteRows nodes J)` equals the determinant of `Polynomial.hermiteMatrix`. -/
theorem detRows_hermiteRows (nodes : List ℤ) (J : ℕ) :
    detRows (hermiteRows nodes J) =
      (Polynomial.hermiteMatrix (fun i : Fin nodes.length => nodes[i]) J).det := by
  rw [detRows_eq_det_ofRows, ofRows_hermiteRows, Matrix.det_reindex_self]

/-- At distinct integer nodes (`nodes.Nodup`), `detRows (hermiteRows nodes J)` is nonzero. -/
theorem detRows_hermiteRows_ne_zero {nodes : List ℤ} (hnodup : nodes.Nodup) (J : ℕ) :
    detRows (hermiteRows nodes J) ≠ 0 := by
  rw [detRows_hermiteRows]
  refine Polynomial.det_hermiteMatrix_ne_zero fun i j hij => Fin.ext ?_
  exact (hnodup.getElem_inj_iff (hi := i.isLt) (hj := j.isLt)).mp hij

/-- Looking up entry `(i, j)` of `cramerColZeroRows mat rhs` for `i < mat.length` returns
`rhs.getD i 0` in column `0` and `rowEntry mat i j` in columns `j > 0`. -/
theorem rowEntry_cramerColZeroRows (mat : List (List ℤ)) (rhs : List ℤ)
    {i : ℕ} (hi : i < mat.length) (j : ℕ) :
    rowEntry (cramerColZeroRows mat rhs) i j =
      if j = 0 then rhs.getD i 0 else rowEntry mat i j := by
  have hi' : i < (cramerColZeroRows mat rhs).length := by simpa using hi
  rw [rowEntry, List.getD_eq_getElem _ _ hi']
  simp only [cramerColZeroRows, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
  cases j with
  | zero => simp
  | succ k =>
    simp only [Nat.succ_ne_zero, ↓reduceIte, rowEntry, List.getD_eq_getElem _ _ hi,
      List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_tail]

/-- For nonempty `mat`, `ofRows (cramerColZeroRows mat rhs)` is `(ofRows mat).updateCol 0`
reindexed along `length_cramerColZeroRows`. -/
theorem ofRows_cramerColZeroRows (mat : List (List ℤ)) (rhs : List ℤ) (h0 : 0 < mat.length) :
    ofRows (cramerColZeroRows mat rhs) =
      Matrix.reindex (finCongr (length_cramerColZeroRows mat rhs).symm)
        (finCongr (length_cramerColZeroRows mat rhs).symm)
        ((ofRows mat).updateCol ⟨0, h0⟩ fun i => rhs.getD i 0) := by
  ext i j
  have hi : i.val < mat.length := by simpa only [length_cramerColZeroRows] using i.isLt
  simp only [ofRows, Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    finCongr_symm, finCongr_apply, Fin.val_cast, Matrix.updateCol_apply, Fin.ext_iff,
    rowEntry_cramerColZeroRows mat rhs hi]

/-- `detRows (cramerColZeroRows mat rhs)` is the determinant of `ofRows mat` with column `0`
replaced by `rhs`. -/
theorem detRows_cramerColZeroRows (mat : List (List ℤ)) (rhs : List ℤ) (h0 : 0 < mat.length) :
    detRows (cramerColZeroRows mat rhs) =
      ((ofRows mat).updateCol ⟨0, h0⟩ fun i => rhs.getD i 0).det := by
  rw [detRows_eq_det_ofRows, ofRows_cramerColZeroRows mat rhs h0, Matrix.det_reindex_self]

private lemma getD_flatten_eq_rowEntry {jets : List (List ℤ)} {J : ℕ}
    (hjets_row : ∀ row ∈ jets, row.length = J) (i : Fin jets.length) (j : Fin J) :
    jets.flatten.getD (j.val + J * i.val) 0 = rowEntry jets i j := by
  rw [List.flatten_eq_flatMap, getD_flatMap_uniform jets J id hjets_row 0 i j, id_eq,
    rowEntry, List.getD_eq_getElem _ _ i.isLt]
  rfl

/-- `detRows` of `cramerColZeroRows (hermiteRows nodes J) jets.flatten` equals the determinant of
`Polynomial.hermiteMatrix` with column `(0, 0)` replaced by `(i, j) ↦ rowEntry jets i j`. -/
theorem detRows_cramerColZeroRows_hermiteRows (nodes : List ℤ) (J : ℕ) (jets : List (List ℤ))
    (hQ : 0 < nodes.length) (hJ : 0 < J)
    (hjets_len : jets.length = nodes.length) (hjets_row : ∀ row ∈ jets, row.length = J) :
    detRows (cramerColZeroRows (hermiteRows nodes J) jets.flatten) =
      ((Polynomial.hermiteMatrix (fun i : Fin nodes.length => nodes[i]) J).updateCol
        (⟨0, hQ⟩, ⟨0, hJ⟩) fun r => rowEntry jets r.1 r.2).det := by
  have hpos : 0 < (hermiteRows nodes J).length := by
    rw [length_hermiteRows]
    exact Nat.mul_pos hQ hJ
  set e : Fin nodes.length × Fin J ≃ Fin (hermiteRows nodes J).length :=
    finProdFinEquiv.trans (finCongr (length_hermiteRows nodes J).symm)
  have he0 : e.symm ⟨0, hpos⟩ = (⟨0, hQ⟩, ⟨0, hJ⟩) := by
    apply e.injective
    rw [Equiv.apply_symm_apply]
    ext
    simp [e]
  have hrhs : (fun r : Fin nodes.length × Fin J => jets.flatten.getD (e r) 0) =
      fun r => rowEntry jets r.1 r.2 := by
    funext ⟨i, j⟩
    have her : (e (i, j) : ℕ) = j.val + J * i.val := rfl
    rw [her]
    have hi' : i.val < jets.length := by omega
    exact getD_flatten_eq_rowEntry hjets_row ⟨i.val, hi'⟩ j
  rw [detRows_cramerColZeroRows _ _ hpos, ofRows_hermiteRows, Matrix.updateCol_reindex,
    he0, hrhs, Matrix.det_reindex_self]

/-! ### Exact Cramer recovery of `H(0)` -/

/-- Exact integer Cramer identity for scaled Taylor jets: without any distinctness or nonzero-scale
assumption, `detRows (cramerColZeroRows (hermiteRows nodes J) jets.flatten)` equals
`(Ω * detRows (hermiteRows nodes J)) * H_zero`. -/
theorem detRows_cramerColZeroRows_eq_mul_eval_zero {nodes : List ℤ} {J : ℕ} {Ω H_zero : ℤ}
    {jets : List (List ℤ)} {H : Polynomial ℚ}
    (hdeg : H.natDegree < nodes.length * J)
    (hH0 : H.eval 0 = (H_zero : ℚ))
    (hjets_len : jets.length = nodes.length)
    (hjets_row : ∀ row ∈ jets, row.length = J)
    (hjets : ∀ (i : Fin nodes.length) (j : Fin J),
      (rowEntry jets i j : ℚ) = (Ω : ℚ) * (Polynomial.taylor (nodes[i] : ℚ) H).coeff j) :
    detRows (cramerColZeroRows (hermiteRows nodes J) jets.flatten) =
      (Ω * detRows (hermiteRows nodes J)) * H_zero := by
  have hN : 0 < nodes.length * J := Nat.zero_lt_of_lt hdeg
  have hQ : 0 < nodes.length := Nat.pos_of_mul_pos_right hN
  have hJ : 0 < J := Nat.pos_of_mul_pos_left hN
  let t : Fin nodes.length → ℤ := fun i => nodes[i]
  let c0 : Fin nodes.length × Fin J := (⟨0, hQ⟩, ⟨0, hJ⟩)
  set p : Polynomial ℚ := (Ω : ℚ) • H
  have hp_deg : p.degree < ↑(nodes.length * J) := by
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intro m hm
    simp only [p, Polynomial.coeff_smul, smul_eq_mul,
      Polynomial.coeff_eq_zero_of_natDegree_lt (hdeg.trans_le hm), mul_zero]
  have hp_c0 : p.coeff (finProdFinEquiv c0) = (Ω : ℚ) * (H_zero : ℚ) := by
    have hc0_val : (finProdFinEquiv c0 : ℕ) = 0 := by simp [c0]
    rw [hc0_val, Polynomial.coeff_smul, smul_eq_mul, Polynomial.coeff_zero_eq_eval_zero, hH0]
  have hjet_eq : Polynomial.taylorJet (fun i => (t i : ℚ)) J p =
      fun r => (rowEntry jets r.1 r.2 : ℚ) := by
    funext ⟨i, j⟩
    simp only [p, map_smul, Polynomial.taylorJet_apply, t]
    exact (hjets i j).symm
  have hcramer := Polynomial.det_hermiteMatrix_mul_coeff t hp_deg c0
  rw [hp_c0, hjet_eq] at hcramer
  have hmap_update :
      ((Polynomial.hermiteMatrix t J).map (Int.cast : ℤ → ℚ)).updateCol c0
        (fun r => (rowEntry jets r.1 r.2 : ℚ)) =
      (((Polynomial.hermiteMatrix t J).updateCol c0
        fun r => rowEntry jets r.1 r.2).map (Int.cast : ℤ → ℚ)) := by
    ext r c
    simp only [Matrix.map_apply, Matrix.updateCol_apply]
    split_ifs <;> rfl
  rw [hmap_update, ← Int.cast_det] at hcramer
  rw [detRows_cramerColZeroRows_hermiteRows nodes J jets hQ hJ hjets_len hjets_row,
    detRows_hermiteRows]
  apply Int.cast_injective (α := ℚ)
  rw [← hcramer]
  push_cast
  ring

/-- **Exact confluent Hermite Cramer recovery (`rowEntry` form).** When `nodes` are distinct,
`Ω ≠ 0`, `H ∈ ℚ[X]` has `natDegree < nodes.length * J` and integer value `H(0) = H_zero`, and
`jets` holds the `Ω`-scaled order-`J` Taylor jets at `nodes`, `hermiteRecoverZero` returns
`H_zero`. -/
theorem hermiteRecoverZero_eq_of_rowEntry {nodes : List ℤ} {J : ℕ} {Ω H_zero : ℤ}
    {jets : List (List ℤ)} {H : Polynomial ℚ}
    (hnodup : nodes.Nodup) (hΩ : Ω ≠ 0)
    (hdeg : H.natDegree < nodes.length * J)
    (hH0 : H.eval 0 = (H_zero : ℚ))
    (hjets_len : jets.length = nodes.length)
    (hjets_row : ∀ row ∈ jets, row.length = J)
    (hjets : ∀ (i : Fin nodes.length) (j : Fin J),
      (rowEntry jets i j : ℚ) = (Ω : ℚ) * (Polynomial.taylor (nodes[i] : ℚ) H).coeff j) :
    hermiteRecoverZero nodes J Ω jets = H_zero := by
  rw [hermiteRecoverZero,
    detRows_cramerColZeroRows_eq_mul_eval_zero hdeg hH0 hjets_len hjets_row hjets]
  exact Int.ediv_mul_left_exact H_zero (mul_ne_zero hΩ (detRows_hermiteRows_ne_zero hnodup J))

/-- **Exact confluent Hermite Cramer recovery (`getElem` form, [OpenAI2026ETH] eq. (B.1)).** -/
theorem hermiteRecoverZero_eq {nodes : List ℤ} {J : ℕ} {Ω H_zero : ℤ}
    {jets : List (List ℤ)} {H : Polynomial ℚ}
    (hnodup : nodes.Nodup) (hΩ : Ω ≠ 0)
    (hdeg : H.natDegree < nodes.length * J)
    (hH0 : H.eval 0 = (H_zero : ℚ))
    (hjets_len : jets.length = nodes.length)
    (hjets_row : ∀ row ∈ jets, row.length = J)
    (hjets : ∀ (i : Fin nodes.length) (j : Fin J),
      have hi : i.val < jets.length := by omega
      have hj : j.val < (jets[i.val]'hi).length := by
        rw [hjets_row _ (List.getElem_mem hi)]; exact j.isLt
      ((jets[i.val]'hi)[j.val]'hj : ℚ) =
        (Ω : ℚ) * (Polynomial.taylor (nodes[i] : ℚ) H).coeff j) :
    hermiteRecoverZero nodes J Ω jets = H_zero := by
  refine hermiteRecoverZero_eq_of_rowEntry hnodup hΩ hdeg hH0 hjets_len hjets_row fun i j => ?_
  have hi : i.val < jets.length := by omega
  have hj : j.val < (jets[i.val]'hi).length := by
    rw [hjets_row _ (List.getElem_mem hi)]; exact j.isLt
  rw [rowEntry, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
  exact hjets i j

/-- Modular recovery of a count `count ∈ [0, 2 ^ ℓ)` congruent to `H(0)` modulo `2 ^ ℓ`. -/
theorem hermiteRecoverModPowTwo_eq {nodes : List ℤ} {J ℓ : ℕ} {Ω H_zero count : ℤ}
    {jets : List (List ℤ)} {H : Polynomial ℚ}
    (hnodup : nodes.Nodup) (hΩ : Ω ≠ 0)
    (hdeg : H.natDegree < nodes.length * J)
    (hH0 : H.eval 0 = (H_zero : ℚ))
    (hjets_len : jets.length = nodes.length)
    (hjets_row : ∀ row ∈ jets, row.length = J)
    (hjets : ∀ (i : Fin nodes.length) (j : Fin J),
      (rowEntry jets i j : ℚ) = (Ω : ℚ) * (Polynomial.taylor (nodes[i] : ℚ) H).coeff j)
    (hcount₀ : 0 ≤ count) (hcount₁ : count < (2 : ℤ) ^ ℓ)
    (hdvd : (2 : ℤ) ^ ℓ ∣ H_zero - count) :
    hermiteRecoverModPowTwo nodes J ℓ Ω jets = count := by
  rw [hermiteRecoverModPowTwo,
    hermiteRecoverZero_eq_of_rowEntry hnodup hΩ hdeg hH0 hjets_len hjets_row hjets]
  exact Int.modPowTwo_eq_of_dvd_sub hcount₀ hcount₁ hdvd

/-- Multi-coordinate count recovery modulo `2 ^ ℓ` ([OpenAI2026ETH], Appendix B.3): summing the
recovered integer constant terms `H_s(0)` across coordinates and reducing modulo `2 ^ ℓ` yields
`count` whenever `0 ≤ count < 2 ^ ℓ` and `2 ^ ℓ ∣ ∑_s H_s(0) - count`. -/
theorem modPowTwo_sum_hermiteRecoverZero_eq {nodes : List ℤ} {J ℓ : ℕ} {Ω count : ℤ}
    {coordJets : List (List (List ℤ))} {Hs : List (Polynomial ℚ)} {H_zeros : List ℤ}
    (hnodup : nodes.Nodup) (hΩ : Ω ≠ 0)
    (hlen_H : Hs.length = coordJets.length)
    (hlen_Z : H_zeros.length = coordJets.length)
    (hcoord : ∀ s : Fin coordJets.length,
      have hsH : s.val < Hs.length := by omega
      have hsZ : s.val < H_zeros.length := by omega
      (Hs[s.val]'hsH).natDegree < nodes.length * J ∧
      (Hs[s.val]'hsH).eval 0 = ((H_zeros[s.val]'hsZ : ℤ) : ℚ) ∧
      coordJets[s].length = nodes.length ∧
      (∀ row ∈ coordJets[s], row.length = J) ∧
      (∀ (i : Fin nodes.length) (j : Fin J),
        (rowEntry coordJets[s] i j : ℚ) =
          (Ω : ℚ) * (Polynomial.taylor (nodes[i] : ℚ) (Hs[s.val]'hsH)).coeff j))
    (hcount₀ : 0 ≤ count) (hcount₁ : count < (2 : ℤ) ^ ℓ)
    (hdvd : (2 : ℤ) ^ ℓ ∣ H_zeros.sum - count) :
    ((coordJets.map (hermiteRecoverZero nodes J Ω)).sum).modPowTwo ℓ = count := by
  have hmap : coordJets.map (hermiteRecoverZero nodes J Ω) = H_zeros := by
    apply List.ext_getElem (by simp [hlen_Z])
    intro s hs hs'
    simp only [List.length_map] at hs
    obtain ⟨hdeg, hH0, hjlen, hjrow, hj⟩ := hcoord ⟨s, hs⟩
    simp only [List.getElem_map]
    exact hermiteRecoverZero_eq_of_rowEntry hnodup hΩ hdeg hH0 hjlen hjrow hj
  rw [hmap]
  exact Int.modPowTwo_eq_of_dvd_sub hcount₀ hcount₁ hdvd

/-! ### Entry magnitude and bit-length bounds -/

/-- Truncated integer division never increases the sign-magnitude bit length of the dividend. -/
theorem intBits_tdiv_le (a b : ℤ) : intBits (a.tdiv b) ≤ intBits a :=
  Nat.add_le_add_right (Int.size_natAbs_tdiv_le a b) 1

/-- Euclidean integer division never increases the sign-magnitude bit length of the dividend. -/
theorem intBits_ediv_le (a b : ℤ) : intBits (a.ediv b) ≤ intBits a :=
  Nat.add_le_add_right (Int.size_natAbs_ediv_le a b) 1

/-- For a nonzero divisor `b`, the Euclidean remainder `a.emod b` has sign-magnitude bit length at
most `intBits b`. -/
theorem intBits_emod_le_of_ne_zero (a : ℤ) {b : ℤ} (hb : b ≠ 0) :
    intBits (a.emod b) ≤ intBits b :=
  Nat.add_le_add_right (Int.size_natAbs_emod_le_of_ne_zero a hb) 1

/-- For a nonzero divisor `b`, `intBits (a.emod b) ≤ intBits b + 1`. -/
theorem intBits_emod_le_add_one_of_ne_zero (a : ℤ) {b : ℤ} (hb : b ≠ 0) :
    intBits (a.emod b) ≤ intBits b + 1 :=
  (intBits_emod_le_of_ne_zero a hb).trans (Nat.le_succ _)

/-- Unconditionally on `b` (including `b = 0`),
`intBits (a.emod b) ≤ max (intBits a) (intBits b)`. -/
theorem intBits_emod_le_max (a b : ℤ) : intBits (a.emod b) ≤ max (intBits a) (intBits b) := by
  by_cases hb : b = 0
  · subst hb
    change intBits (a % 0) ≤ _
    rw [Int.emod_zero]
    exact le_max_left _ _
  · exact (intBits_emod_le_of_ne_zero a hb).trans (le_max_right _ _)

/-- Reducing modulo `2 ^ ℓ` produces an integer of sign-magnitude bit length at most `ℓ + 1`. -/
theorem intBits_modPowTwo_le (x : ℤ) (ℓ : ℕ) : intBits (x.modPowTwo ℓ) ≤ ℓ + 1 :=
  (intBits_le_iff _ _).mpr (Int.natAbs_modPowTwo_lt x ℓ)

/-- If every node in `nodes` has magnitude below `2 ^ b`, then every entry of
`hermiteRows nodes J` has magnitude strictly below `2 ^ ((nodes.length * J) * (b + 1))`. -/
theorem natAbs_lt_of_mem_hermiteRows {nodes : List ℤ} {J b : ℕ}
    (hnodes : ∀ t ∈ nodes, t.natAbs < 2 ^ b) {row : List ℤ} (hrow : row ∈ hermiteRows nodes J)
    {z : ℤ} (hz : z ∈ row) :
    z.natAbs < 2 ^ ((nodes.length * J) * (b + 1)) := by
  rw [hermiteRows, List.mem_flatMap] at hrow
  obtain ⟨t, ht, hrow_map⟩ := hrow
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hrow_map
  obtain ⟨m, hm_mem, rfl⟩ := List.mem_map.mp hz
  have hm : m < nodes.length * J := List.mem_range.mp hm_mem
  have hchoose : m.choose j < 2 ^ (nodes.length * J) :=
    (Nat.choose_le_two_pow m j).trans_lt (Nat.pow_lt_pow_right (by norm_num) hm)
  have ht_le : t.natAbs ≤ 2 ^ b := (hnodes t ht).le
  have hpow : (t ^ (m - j)).natAbs ≤ 2 ^ (b * (nodes.length * J)) := by
    rw [Int.natAbs_pow]
    calc t.natAbs ^ (m - j)
        ≤ (2 ^ b) ^ (m - j) := Nat.pow_le_pow_left ht_le (m - j)
      _ = 2 ^ (b * (m - j)) := (pow_mul 2 b (m - j)).symm
      _ ≤ 2 ^ (b * (nodes.length * J)) :=
          Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left b (by omega))
  rw [Int.natAbs_mul, Int.natAbs_natCast]
  calc m.choose j * (t ^ (m - j)).natAbs
      < 2 ^ (nodes.length * J) * 2 ^ (b * (nodes.length * J)) := by
        exact (Nat.mul_le_mul_left (m.choose j) hpow).trans_lt
          (Nat.mul_lt_mul_of_pos_right hchoose (by positivity))
    _ = 2 ^ ((nodes.length * J) * (b + 1)) := by
        rw [← pow_add]
        congr 1
        ring

/-- Entry bit-length bound for `hermiteRows`: if every node has `intBits t ≤ b + 1`, then every
entry `z` of `hermiteRows nodes J` satisfies `intBits z ≤ (nodes.length * J) * (b + 1) + 1`. -/
theorem intBits_le_of_mem_hermiteRows {nodes : List ℤ} {J b : ℕ}
    (hnodes : ∀ t ∈ nodes, intBits t ≤ b + 1) {row : List ℤ} (hrow : row ∈ hermiteRows nodes J)
    {z : ℤ} (hz : z ∈ row) :
    intBits z ≤ (nodes.length * J) * (b + 1) + 1 :=
  (intBits_le_iff _ _).mpr <| natAbs_lt_of_mem_hermiteRows
    (fun t ht => (intBits_le_iff _ _).mp (hnodes t ht)) hrow hz

/-- Entry bit-length bound for `cramerColZeroRows`: replacing column `0` with `rhs` preserves any
common bit-length bound on `mat` and `rhs`. -/
theorem intBits_le_of_mem_cramerColZeroRows {mat : List (List ℤ)} {rhs : List ℤ} {B : ℕ}
    (hmat : ∀ row ∈ mat, ∀ z ∈ row, intBits z ≤ B + 1)
    (hrhs : ∀ w ∈ rhs, intBits w ≤ B + 1)
    {row : List ℤ} (hrow : row ∈ cramerColZeroRows mat rhs) {z : ℤ} (hz : z ∈ row) :
    intBits z ≤ B + 1 := by
  rw [cramerColZeroRows, List.mem_map] at hrow
  obtain ⟨⟨r, k⟩, hmem, rfl⟩ := hrow
  have hr_mem : r ∈ mat := (List.mem_zipIdx hmem).2.2 ▸ List.getElem_mem _
  rcases List.mem_cons.mp hz with rfl | htail
  · rcases Nat.lt_or_ge k rhs.length with hk | hk
    · rw [List.getD_eq_getElem _ _ hk]
      exact hrhs _ (List.getElem_mem hk)
    · rw [List.getD_eq_default _ _ hk, intBits_le_iff]
      exact Nat.two_pow_pos B
  · exact hmat r hr_mem z (List.mem_of_mem_tail htail)

/-! ### Plain polynomial-time certificates -/

open Turing MultiTapeTM

private theorem nat_choose_eq_ite (m j : ℕ) :
    m.choose j = if j ≤ m then m.factorial / (j.factorial * (m - j).factorial) else 0 := by
  by_cases h : j ≤ m
  · rw [ite_eq_left h]
    exact Nat.choose_eq_factorial_div_factorial h
  · rw [ite_eq_right h]
    exact Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge h)

private theorem unary_choose_intBin :
    ComputableInPolyTime (fun p : ℕ × ℕ => (p.1.choose p.2 : ℤ))
      (encPair encUnary encUnary) encIntBin := by
  have hle : ComputableInPolyTime (fun p : ℕ × ℕ => decide (p.2 ≤ p.1))
      (encPair encUnary encUnary) encBool := by fun_prop
  have hdiv : ComputableInPolyTime
      (fun p : ℕ × ℕ => ((p.1.factorial / (p.2.factorial * (p.1 - p.2).factorial) : ℕ) : ℤ))
      (encPair encUnary encUnary) encIntBin := by fun_prop
  have h := hle.ite_decide hdiv (.const 0)
  refine h.of_enc_eq fun ⟨m, j⟩ => congrArg encIntBin ?_
  simp only [nat_choose_eq_ite]
  split_ifs <;> rfl

variable {α : Type} {encIn : α ↪ List Bool}

/-- Constructing `hermiteRows (nodes x) (J x)` from binary integer nodes and a unary order `J` is
computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_hermiteRows {nodes : α → List ℤ} {J : α → ℕ}
    (hnodes : ComputableInPolyTime nodes encIn (encList encIntBin))
    (hJ : ComputableInPolyTime J encIn encUnary) :
    ComputableInPolyTime (fun x => hermiteRows (nodes x) (J x))
      encIn (encList (encList encIntBin)) := by
  have hdim : ComputableInPolyTime (fun x => (nodes x).length * J x) encIn encUnary := by
    fun_prop
  have hentry : ComputableInPolyTime
      (fun q : ((α × ℤ) × ℕ) × ℕ => (q.2.choose q.1.2 : ℤ) * q.1.1.2 ^ (q.2 - q.1.2))
      (encPair (encPair (encPair encIn encIntBin) encUnary) encUnary) encIntBin := by
    have hchoose : ComputableInPolyTime
        (fun q : ((α × ℤ) × ℕ) × ℕ => (q.2.choose q.1.2 : ℤ))
        (encPair (encPair (encPair encIn encIntBin) encUnary) encUnary) encIntBin :=
      unary_choose_intBin.comp ((ComputableInPolyTime.snd _ _).prod
        ((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.fst _ _)))
    have hpow : ComputableInPolyTime
        (fun q : ((α × ℤ) × ℕ) × ℕ => q.1.1.2 ^ (q.2 - q.1.2))
        (encPair (encPair (encPair encIn encIntBin) encUnary) encUnary) encIntBin := by fun_prop
    exact ComputableInPolyTime.intBin_mul' hchoose hpow
  have hrow : ComputableInPolyTime
      (fun p : (α × ℤ) × ℕ =>
        (List.range ((nodes p.1.1).length * J p.1.1)).map fun m =>
          (m.choose p.2 : ℤ) * p.1.2 ^ (m - p.2))
      (encPair (encPair encIn encIntBin) encUnary) (encList encIntBin) :=
    ComputableInPolyTime.mapWithInput
      (ComputableInPolyTime.range.comp
        (hdim.comp ((ComputableInPolyTime.fst _ _).comp
          (ComputableInPolyTime.fst _ _))))
      hentry
  have hblock : ComputableInPolyTime
      (fun p : α × ℤ =>
        (List.range (J p.1)).map fun j =>
          (List.range ((nodes p.1).length * J p.1)).map fun m =>
            (m.choose j : ℤ) * p.2 ^ (m - j))
      (encPair encIn encIntBin) (encList (encList encIntBin)) :=
    ComputableInPolyTime.mapWithInput
      (ComputableInPolyTime.range.comp
        (hJ.comp (ComputableInPolyTime.fst _ _)))
      hrow
  exact ComputableInPolyTime.flatMapWithInput hnodes hblock

/-- `hermiteRows` is computable in polynomial time on `encPair (encList encIntBin) encUnary`. -/
theorem hermiteRows_polytime :
    ComputableInPolyTime (fun p : List ℤ × ℕ => hermiteRows p.1 p.2)
      (encPair (encList encIntBin) encUnary) (encList (encList encIntBin)) :=
  computableInPolyTime_hermiteRows (by fun_prop) (by fun_prop)

/-- Replacing column `0` via `cramerColZeroRows` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_cramerColZeroRows
    {mat : α → List (List ℤ)} {rhs : α → List ℤ}
    (hmat : ComputableInPolyTime mat encIn (encList (encList encIntBin)))
    (hrhs : ComputableInPolyTime rhs encIn (encList encIntBin)) :
    ComputableInPolyTime (fun x => cramerColZeroRows (mat x) (rhs x))
      encIn (encList (encList encIntBin)) := by
  unfold cramerColZeroRows
  fun_prop

/-- `cramerColZeroRows` is computable in polynomial time on pairs of integer matrix and RHS. -/
theorem cramerColZeroRows_polytime :
    ComputableInPolyTime (fun p : List (List ℤ) × List ℤ => cramerColZeroRows p.1 p.2)
      (encPair (encList (encList encIntBin)) (encList encIntBin))
      (encList (encList encIntBin)) :=
  computableInPolyTime_cramerColZeroRows (by fun_prop) (by fun_prop)

/-- Confluent Hermite Cramer recovery `hermiteRecoverZero` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_hermiteRecoverZero
    {nodes : α → List ℤ} {J : α → ℕ} {Ω : α → ℤ} {jets : α → List (List ℤ)}
    (hnodes : ComputableInPolyTime nodes encIn (encList encIntBin))
    (hJ : ComputableInPolyTime J encIn encUnary)
    (hΩ : ComputableInPolyTime Ω encIn encIntBin)
    (hjets : ComputableInPolyTime jets encIn (encList (encList encIntBin))) :
    ComputableInPolyTime
      (fun x => hermiteRecoverZero (nodes x) (J x) (Ω x) (jets x))
      encIn encIntBin := by
  have hflat : ComputableInPolyTime (fun x => (jets x).flatten) encIn (encList encIntBin) := by
    simp only [List.flatten_eq_flatMap]
    fun_prop
  unfold hermiteRecoverZero
  fun_prop

/-- Direct tuple certificate for `hermiteRecoverZero` over binary integers and unary order `J`. -/
theorem hermiteRecoverZero_polytime :
    ComputableInPolyTime
      (fun q : ((List ℤ × ℕ) × ℤ) × List (List ℤ) =>
        hermiteRecoverZero q.1.1.1 q.1.1.2 q.1.2 q.2)
      (encPair (encPair (encPair (encList encIntBin) encUnary) encIntBin)
        (encList (encList encIntBin)))
      encIntBin := by
  fun_prop

/-- Modular confluent Hermite Cramer recovery `hermiteRecoverModPowTwo` is computable in
polynomial time when `J` and `ℓ` are given in unary. -/
@[fun_prop]
theorem computableInPolyTime_hermiteRecoverModPowTwo
    {nodes : α → List ℤ} {J ℓ : α → ℕ} {Ω : α → ℤ} {jets : α → List (List ℤ)}
    (hnodes : ComputableInPolyTime nodes encIn (encList encIntBin))
    (hJ : ComputableInPolyTime J encIn encUnary)
    (hℓ : ComputableInPolyTime ℓ encIn encUnary)
    (hΩ : ComputableInPolyTime Ω encIn encIntBin)
    (hjets : ComputableInPolyTime jets encIn (encList (encList encIntBin))) :
    ComputableInPolyTime
      (fun x => hermiteRecoverModPowTwo (nodes x) (J x) (ℓ x) (Ω x) (jets x))
      encIn encIntBin := by
  unfold hermiteRecoverModPowTwo
  fun_prop

/-- Direct tuple certificate for `hermiteRecoverModPowTwo`. -/
theorem hermiteRecoverModPowTwo_polytime :
    ComputableInPolyTime
      (fun q : (((List ℤ × ℕ) × ℕ) × ℤ) × List (List ℤ) =>
        hermiteRecoverModPowTwo q.1.1.1.1 q.1.1.1.2 q.1.1.2 q.1.2 q.2)
      (encPair (encPair (encPair (encPair (encList encIntBin) encUnary) encUnary) encIntBin)
        (encList (encList encIntBin)))
      encIntBin := by
  fun_prop

/-- Recovering a coordinate sum `∑_s H_s(0) mod 2 ^ ℓ` across a list of scaled jet tables sharing
`nodes`, `J`, and `Ω` ([OpenAI2026ETH], Appendix B.3) is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_modPowTwo_sum_hermiteRecoverZero
    {nodes : α → List ℤ} {J ℓ : α → ℕ} {Ω : α → ℤ}
    {coordJets : α → List (List (List ℤ))}
    (hnodes : ComputableInPolyTime nodes encIn (encList encIntBin))
    (hJ : ComputableInPolyTime J encIn encUnary)
    (hℓ : ComputableInPolyTime ℓ encIn encUnary)
    (hΩ : ComputableInPolyTime Ω encIn encIntBin)
    (hcoordJets : ComputableInPolyTime coordJets encIn
      (encList (encList (encList encIntBin)))) :
    ComputableInPolyTime
      (fun x => ((coordJets x).map (hermiteRecoverZero (nodes x) (J x) (Ω x))).sum.modPowTwo (ℓ x))
      encIn encIntBin := by
  have hitem : ComputableInPolyTime
      (fun p : α × List (List ℤ) => hermiteRecoverZero (nodes p.1) (J p.1) (Ω p.1) p.2)
      (encPair encIn (encList (encList encIntBin))) encIntBin := by fun_prop
  have hmap : ComputableInPolyTime
      (fun x => (coordJets x).map (hermiteRecoverZero (nodes x) (J x) (Ω x)))
      encIn (encList encIntBin) :=
    ComputableInPolyTime.mapWithInput hcoordJets hitem
  have hsum : ComputableInPolyTime
      (fun x => ((coordJets x).map (hermiteRecoverZero (nodes x) (J x) (Ω x))).sum)
      encIn encIntBin := by fun_prop
  exact ComputableInPolyTime.intBin_modPowTwo' hsum hℓ

end Cslib.Circuits.Rational
