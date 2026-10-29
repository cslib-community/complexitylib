/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Rational.Runtime.Encode
public import Complexity.Computability.Circuit.Rational.Runtime.Lift
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

/-!
# Pointwise normalization and encoding in polynomial time

At each point `(t, p, r)` of the three-dimensional integer grid, the executable hitting-list
generator materializes the `n + 1` integer lift matrices `[U₀, U₁, …, Uₙ]`, tests whether
`det U₀ = 0`, and when `det U₀ ≠ 0` computes every entry of each normalized matrix `U₀⁻¹ * Uₐ` as
the reduced rational ratio of two integer determinants via Cramer's rule, before serializing the
resulting tuple with `encodeTuple`.

This module expresses that per-point pipeline directly on the list-of-rows tables produced by
`liftRows` and certifies that it runs in polynomial time on a multi-tape Turing machine:

* `cramerRows A B colA colB` replaces column `colA` of `A` by column `colB` of `B`;
* `matrixEntryWord A B den i j` encodes `Rat.divInt (detRows (cramerRows A B i j)) den`;
* `matrixWord A B den` and `tupleWord tables den` serialize one normalized matrix and the full
  tuple of `n` normalized matrices;
* `pointWordOfTables`, `pointWordsOfTables`, `pointWord`, and `pointWords` perform the singularity
  test on `U₀` and emit the encoded tuple (or `[]` when singular).

## Main definitions

* `Cslib.Circuits.Rational.cramerRows`: column replacement on lists of integer rows.
* `Cslib.Circuits.Rational.matrixEntryWord`, `Cslib.Circuits.Rational.matrixWord`,
  `Cslib.Circuits.Rational.tupleWord`: encoded entry, matrix, and tuple from integer row tables
  and a common denominator.
* `Cslib.Circuits.Rational.pointWordOfTables`, `Cslib.Circuits.Rational.pointWordsOfTables`,
  `Cslib.Circuits.Rational.pointWord`, `Cslib.Circuits.Rational.pointWords`: the singularity-tested
  encoded tuple at a grid point, as a bit word and as a singleton-or-empty list of bit words.

## Main results

* `Cslib.Circuits.Rational.cramerRows_eq`: `cramerRows` agrees with `Matrix.updateCol` on `rowsOf`.
* `Cslib.Circuits.Rational.matrixEntryWord_eq`, `Cslib.Circuits.Rational.matrixWord_eq`,
  `Cslib.Circuits.Rational.tupleWord_eq`: agreement with `ExecutableGenerator.normalizedEntry`,
  `ExecutableGenerator.normalized`, and `encodeTuple`.
* `Cslib.Circuits.Rational.pointWord_eq`, `Cslib.Circuits.Rational.pointWords_eq`: `pointWord` and
  `pointWords` agree with `ExecutableGenerator.atPoint` composed with `encodeTuple`.
* `Cslib.Circuits.Rational.computableInPolyTime_cramerRows`,
  `Cslib.Circuits.Rational.computableInPolyTime_matrixEntryWord`,
  `Cslib.Circuits.Rational.computableInPolyTime_matrixWord`,
  `Cslib.Circuits.Rational.computableInPolyTime_tupleWord`,
  `Cslib.Circuits.Rational.pointWordOfTables_polytime`,
  `Cslib.Circuits.Rational.pointWordsOfTables_polytime`,
  `Cslib.Circuits.Rational.computableInPolyTime_pointWord`,
  `Cslib.Circuits.Rational.computableInPolyTime_pointWords`,
  `Cslib.Circuits.Rational.pointWord_polytime`: polynomial-time certificates for the per-point
  pipeline.

## References

* Adapted from OpenAI's formalization [OpenAI2026RationalHitting] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Computability/RationalHitting/PointComputation.lean), via the complexitylib port
  [Schlesinger2026RationalHitting] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.Circuits.Rational

open Matrix

/-! ### List-level Cramer normalization and tuple encoding -/

/-- Replace column `colA` of `A` with column `colB` of `B`, producing an `A.length × A.length`
list of rows. -/
def cramerRows (A B : List (List ℤ)) (colA colB : ℕ) : List (List ℤ) :=
  tabulateTable A.length A.length fun r c =>
    if c = colA then rowEntry B r colB else rowEntry A r c

/-- Encoded reduced-rational `(i, j)`-entry of `A⁻¹ * B` given the common denominator `den`,
computed by Cramer's rule and `detRows`. -/
def matrixEntryWord (A B : List (List ℤ)) (den : ℤ) (i j : ℕ) : List Bool :=
  encodeRat (Rat.divInt (detRows (cramerRows A B i j)) den)

/-- Encoded `d × d` rational matrix `A⁻¹ * B` in row-major order given the common denominator
`den`, where `d = A.length`. -/
def matrixWord (A B : List (List ℤ)) (den : ℤ) : List Bool :=
  (List.range A.length).flatMap fun i =>
    (List.range A.length).flatMap fun j =>
      matrixEntryWord A B den i j

/-- Encoded tuple of `n` normalized rational matrices from a list `tables` of `n + 1` integer
tables `[U₀, U₁, …, Uₙ]` and the common denominator `den`. -/
def tupleWord (tables : List (List (List ℤ))) (den : ℤ) : List Bool :=
  tables.tail.flatMap fun B => matrixWord (tables.headD []) B den

/-- Emit the encoded normalized tuple for a list of integer tables `[U₀, U₁, …, Uₙ]`, or `[]`
when `detRows U₀ = 0`. -/
def pointWordOfTables (tables : List (List (List ℤ))) : List Bool :=
  let den := detRows (tables.headD [])
  if den = 0 then [] else tupleWord tables den

/-- Singleton list `[tupleWord tables den]` when `detRows (tables.headD []) ≠ 0`, and `[]` when
singular; used to enumerate grid points by `List.flatMap`. -/
def pointWordsOfTables (tables : List (List (List ℤ))) : List (List Bool) :=
  let den := detRows (tables.headD [])
  if den = 0 then [] else [tupleWord tables den]

/-- Encoded normalized tuple at the grid coordinates `(t, p, r)`, or `[]` if singular. -/
def pointWord (n N M Dg t p r : ℕ) : List Bool :=
  pointWordOfTables (liftRows n N M Dg t p r)

/-- Singleton list containing the encoded normalized tuple at `(t, p, r)` when nonsingular, or
`[]` when singular. -/
def pointWords (n N M Dg t p r : ℕ) : List (List Bool) :=
  pointWordsOfTables (liftRows n N M Dg t p r)

/-! ### Agreement with the executable generator -/

/-- `cramerRows` on `rowsOf` computes the rows of `Matrix.updateCol`. -/
theorem cramerRows_eq {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℤ) (i j : Fin d) :
    cramerRows (rowsOf A) (rowsOf B) i.val j.val =
      rowsOf (A.updateCol i (fun r => B r j)) := by
  rw [cramerRows, length_rowsOf]
  refine tabulateTable_eq_rowsOf _ _ fun r c => ?_
  simp only [Matrix.updateCol_apply, rowEntry_rowsOf, Fin.ext_iff]

/-- `matrixEntryWord` agrees with ` encodeRat (ExecutableGenerator.normalizedEntry A B den i j)`. -/
theorem matrixEntryWord_eq {d : ℕ} (A B : DeterminantAlgorithm.Table d) (den : ℤ) (i j : Fin d) :
    matrixEntryWord (rowsOf (DeterminantAlgorithm.denote A))
        (rowsOf (DeterminantAlgorithm.denote B)) den i.val j.val =
      encodeRat (ExecutableGenerator.normalizedEntry A B den i j) := by
  simp only [matrixEntryWord, ExecutableGenerator.normalizedEntry, cramerRows_eq,
    detRows_eq, DeterminantAlgorithm.determinant_eq, DeterminantAlgorithm.denote_tabulate]

/-- `matrixWord` serializes all `d × d` entries of `ExecutableGenerator.normalizedEntry A B den`. -/
theorem matrixWord_eq {d : ℕ} (A B : DeterminantAlgorithm.Table d) (den : ℤ) :
    matrixWord (rowsOf (DeterminantAlgorithm.denote A))
        (rowsOf (DeterminantAlgorithm.denote B)) den =
      (List.finRange d).flatMap fun i =>
        (List.finRange d).flatMap fun j =>
          encodeRat (ExecutableGenerator.normalizedEntry A B den i j) := by
  simp only [matrixWord, length_rowsOf, ← List.map_coe_finRange_eq_range,
    List.flatMap_map, matrixEntryWord_eq]

private lemma vector_toList_eq_map_finRange {α : Type*} {m : ℕ} (v : Vector α m) :
    v.toList = (List.finRange m).map v.get := by
  rw [← List.ofFn_eq_map, ← Vector.toList_ofFn]
  congr 1
  ext i hi
  simp [Vector.get]

/-- `tupleWord` on the row lists of `A` equals `encodeTuple` on the normalized tuple. -/
theorem tupleWord_eq {n d : ℕ} (A : Vector (DeterminantAlgorithm.Table d) (n + 1)) (den : ℤ) :
    tupleWord (A.toList.map fun T => rowsOf (DeterminantAlgorithm.denote T)) den =
      encodeTuple (ExecutableGenerator.tuple (ExecutableGenerator.normalized A den)) := by
  simp only [tupleWord, vector_toList_eq_map_finRange, List.finRange_succ,
    List.map_cons, List.map_map, List.headD_cons, List.tail_cons, List.flatMap_map,
    Function.comp_def, matrixWord_eq, encodeTuple, ExecutableGenerator.tuple_normalized]

/-- `pointWordOfTables` on the row lists of `A` tests `determinant (A.get 0) = 0` and encodes the
normalized tuple when nonsingular. -/
private theorem pointWordOfTables_eq {n d : ℕ} (A : Vector (DeterminantAlgorithm.Table d) (n + 1)) :
    pointWordOfTables (A.toList.map fun T => rowsOf (DeterminantAlgorithm.denote T)) =
      let den := DeterminantAlgorithm.determinant (A.get 0)
      if den = 0 then []
      else encodeTuple (ExecutableGenerator.tuple (ExecutableGenerator.normalized A den)) := by
  have hhead :
      (A.toList.map fun T => rowsOf (DeterminantAlgorithm.denote T)).headD [] =
        rowsOf (DeterminantAlgorithm.denote (A.get 0)) := by
    simp [vector_toList_eq_map_finRange, List.finRange_succ]
  simp only [pointWordOfTables, hhead, detRows_rowsOf_denote, tupleWord_eq]

/-- `pointWordsOfTables` on the row lists of `A` produces `[]` when singular and the singleton
encoded tuple when nonsingular. -/
private theorem pointWordsOfTables_eq {n d : ℕ}
    (A : Vector (DeterminantAlgorithm.Table d) (n + 1)) :
    pointWordsOfTables (A.toList.map fun T => rowsOf (DeterminantAlgorithm.denote T)) =
      let den := DeterminantAlgorithm.determinant (A.get 0)
      if den = 0 then []
      else [encodeTuple (ExecutableGenerator.tuple (ExecutableGenerator.normalized A den))] := by
  have hhead :
      (A.toList.map fun T => rowsOf (DeterminantAlgorithm.denote T)).headD [] =
        rowsOf (DeterminantAlgorithm.denote (A.get 0)) := by
    simp [vector_toList_eq_map_finRange, List.finRange_succ]
  simp only [pointWordsOfTables, hhead, detRows_rowsOf_denote, tupleWord_eq]

/-- `pointWord` at `(x 0, x 1, x 2)` agrees with `ExecutableGenerator.atPoint n N e x` followed by
`encodeTuple`. -/
theorem pointWord_eq (n N e : ℕ) (x : Fin 3 → ℕ) :
    pointWord n N (CyclotomicRing.dimension e) (CyclotomicRing.degree e) (x 0) (x 1) (x 2) =
      (ExecutableGenerator.atPoint n N e x).elim [] encodeTuple := by
  rw [pointWord, liftRows_eq_inputTables, pointWordOfTables_eq, ExecutableGenerator.atPoint]
  dsimp only
  split_ifs <;> rfl

/-- `pointWords` at `(x 0, x 1, x 2)` agrees with `((ExecutableGenerator.atPoint n N e x).map
encodeTuple).toList`. -/
theorem pointWords_eq (n N e : ℕ) (x : Fin 3 → ℕ) :
    pointWords n N (CyclotomicRing.dimension e) (CyclotomicRing.degree e) (x 0) (x 1) (x 2) =
      ((ExecutableGenerator.atPoint n N e x).map encodeTuple).toList := by
  rw [pointWords, liftRows_eq_inputTables, pointWordsOfTables_eq, ExecutableGenerator.atPoint]
  dsimp only
  split_ifs <;> rfl

/-! ### Polynomial-time certificates -/

open Turing MultiTapeTM MultiTapeTM.ComputableInPolyTime

variable {α : Type} {encIn : α ↪ List Bool}

@[local fun_prop]
private theorem bitsFlatMapWithInput {β : Type} {encB : β ↪ List Bool}
    {list : α → List β} {f : α → β → List Bool}
    (hlist : ComputableInPolyTime list encIn (encList encB))
    (hf : ComputableInPolyTime (fun p : α × β => f p.1 p.2)
      (encPair encIn encB) encBits) :
    ComputableInPolyTime (fun x => (list x).flatMap (f x)) encIn encBits := by
  simpa only [List.flatten_eq_flatMap, List.flatMap_map, id_eq] using
    bitsFlatten (mapWithInput hlist hf)

@[local fun_prop]
private theorem intBin_isZero' {z : α → ℤ}
    (hz : ComputableInPolyTime z encIn encIntBin) :
    ComputableInPolyTime (fun x => decide (z x = 0)) encIn encBool :=
  hz.decide_eq' (const 0)

@[local fun_prop]
private theorem computableInPolyTime_detRows {A : α → List (List ℤ)}
    (hA : ComputableInPolyTime A encIn (encList (encList encIntBin))) :
    ComputableInPolyTime (fun x => detRows (A x)) encIn encIntBin :=
  detRows_polytime.comp hA

@[local fun_prop]
private theorem listTail' {β : Type} {encB : β ↪ List Bool} {l : α → List β}
    (hl : ComputableInPolyTime l encIn (encList encB)) :
    ComputableInPolyTime (fun x => (l x).tail) encIn (encList encB) := by
  simpa only [Function.comp_def, List.drop_one] using
    (dropUnary (encA := encB)).comp (hl.prod (const 1))

/-- Column replacement `cramerRows` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_cramerRows {A B : α → List (List ℤ)} {colA colB : α → ℕ}
    (hA : ComputableInPolyTime A encIn (encList (encList encIntBin)))
    (hB : ComputableInPolyTime B encIn (encList (encList encIntBin)))
    (hcolA : ComputableInPolyTime colA encIn encUnary)
    (hcolB : ComputableInPolyTime colB encIn encUnary) :
    ComputableInPolyTime
      (fun x => cramerRows (A x) (B x) (colA x) (colB x))
      encIn (encList (encList encIntBin)) := by
  have hlen : ComputableInPolyTime (fun x => (A x).length) encIn encUnary :=
    (length_list _).comp hA
  exact computableInPolyTime_tabulateTable hlen hlen (by fun_prop)

/-- Encoding one normalized rational entry via Cramer's rule and `detRows` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_matrixEntryWord {A B : α → List (List ℤ)} {den : α → ℤ}
    {i j : α → ℕ}
    (hA : ComputableInPolyTime A encIn (encList (encList encIntBin)))
    (hB : ComputableInPolyTime B encIn (encList (encList encIntBin)))
    (hden : ComputableInPolyTime den encIn encIntBin)
    (hi : ComputableInPolyTime i encIn encUnary)
    (hj : ComputableInPolyTime j encIn encUnary) :
    ComputableInPolyTime
      (fun x => matrixEntryWord (A x) (B x) (den x) (i x) (j x))
      encIn encBits := by
  unfold matrixEntryWord
  fun_prop

/-- Encoding a full normalized rational matrix is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_matrixWord {A B : α → List (List ℤ)} {den : α → ℤ}
    (hA : ComputableInPolyTime A encIn (encList (encList encIntBin)))
    (hB : ComputableInPolyTime B encIn (encList (encList encIntBin)))
    (hden : ComputableInPolyTime den encIn encIntBin) :
    ComputableInPolyTime
      (fun x => matrixWord (A x) (B x) (den x))
      encIn encBits := by
  unfold matrixWord
  fun_prop

/-- Encoding a tuple of normalized rational matrices from `tables` and `den` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_tupleWord {tables : α → List (List (List ℤ))} {den : α → ℤ}
    (htables : ComputableInPolyTime tables encIn (encList (encList (encList encIntBin))))
    (hden : ComputableInPolyTime den encIn encIntBin) :
    ComputableInPolyTime
      (fun x => tupleWord (tables x) (den x))
      encIn encBits := by
  unfold tupleWord
  fun_prop

/-- Singularity-tested tuple encoding on a list of integer tables is polynomial-time. -/
@[fun_prop]
theorem pointWordOfTables_polytime :
    ComputableInPolyTime pointWordOfTables
      (encList (encList (encList encIntBin))) encBits := by
  unfold pointWordOfTables
  fun_prop

/-- Compositional polynomial-time certificate for `pointWordOfTables`. -/
@[fun_prop]
theorem computableInPolyTime_pointWordOfTables {tables : α → List (List (List ℤ))}
    (htables : ComputableInPolyTime tables encIn (encList (encList (encList encIntBin)))) :
    ComputableInPolyTime (fun x => pointWordOfTables (tables x)) encIn encBits :=
  pointWordOfTables_polytime.comp htables

/-- Singularity-tested singleton-or-empty tuple encoding on a list of integer tables is
polynomial-time. -/
@[fun_prop]
theorem pointWordsOfTables_polytime :
    ComputableInPolyTime pointWordsOfTables
      (encList (encList (encList encIntBin))) (encList encBits) := by
  unfold pointWordsOfTables
  fun_prop

/-- Compositional polynomial-time certificate for `pointWordsOfTables`. -/
@[fun_prop]
theorem computableInPolyTime_pointWordsOfTables {tables : α → List (List (List ℤ))}
    (htables : ComputableInPolyTime tables encIn (encList (encList (encList encIntBin)))) :
    ComputableInPolyTime (fun x => pointWordsOfTables (tables x)) encIn (encList encBits) :=
  pointWordsOfTables_polytime.comp htables

/-- Computing the encoded normalized tuple at a grid point is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_pointWord {n N M Dg t p r : α → ℕ}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hN : ComputableInPolyTime N encIn encUnary)
    (hM : ComputableInPolyTime M encIn encUnary)
    (hDg : ComputableInPolyTime Dg encIn encUnary)
    (ht : ComputableInPolyTime t encIn encUnary)
    (hp : ComputableInPolyTime p encIn encUnary)
    (hr : ComputableInPolyTime r encIn encUnary) :
    ComputableInPolyTime
      (fun x => pointWord (n x) (N x) (M x) (Dg x) (t x) (p x) (r x))
      encIn encBits := by
  unfold pointWord
  fun_prop

/-- Computing the singleton-or-empty list of encoded tuples at a grid point is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_pointWords {n N M Dg t p r : α → ℕ}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hN : ComputableInPolyTime N encIn encUnary)
    (hM : ComputableInPolyTime M encIn encUnary)
    (hDg : ComputableInPolyTime Dg encIn encUnary)
    (ht : ComputableInPolyTime t encIn encUnary)
    (hp : ComputableInPolyTime p encIn encUnary)
    (hr : ComputableInPolyTime r encIn encUnary) :
    ComputableInPolyTime
      (fun x => pointWords (n x) (N x) (M x) (Dg x) (t x) (p x) (r x))
      encIn (encList encBits) := by
  unfold pointWords
  fun_prop

/-- Standalone polynomial-time certificate for `pointWord` on a 7-tuple of unary naturals. -/
@[fun_prop]
theorem pointWord_polytime :
    ComputableInPolyTime
      (fun q : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ =>
        pointWord q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2.1 q.2.2.2.2.2.2)
      (encPair encUnary (encPair encUnary (encPair encUnary (encPair encUnary
        (encPair encUnary (encPair encUnary encUnary))))))
      encBits := by
  fun_prop

end Cslib.Circuits.Rational
