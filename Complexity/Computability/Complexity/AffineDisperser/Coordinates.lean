/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Combinatorics.AffineDisperser.Bits
public import Complexity.Foundations.Data.BitString.List
public import Complexity.Foundations.Data.BitString.List.Operations
public import Complexity.Foundations.Data.List.OfFn
public import Mathlib.RingTheory.Trace.Defs
import Complexity.Foundations.Data.List.Lookup
import Mathlib.Data.List.GetD

/-!
# Ben-Sasson and Kopparty's function in coordinates

Let `B` be a basis of a field `F` over `𝔽₂` indexed by `Fin n`. A bit list `a` stands for the
element `∑_{u < n} a u • B u` (`Cslib.AffineDisperser.fieldOfBits`), and a multiplication table
lists the coordinates of the products `B u * B w` (`Cslib.AffineDisperser.IsMulTable`). With such a
table, field arithmetic is a computation on bit lists: a product is the sum of the table entries
`B u * B w` with `a u = b w = 1` (`Cslib.AffineDisperser.fieldMul`), the power `y ^ (2 ^ k - 1)`
follows from `k - 1` steps `z ↦ z ^ 2 * y`, the elementary symmetric polynomial `e_t` from the
recursion `e_{j + 1}(z, ys) = e_{j + 1}(ys) + z e_j(ys)`, and the trace from the traces
`Tr (B u) = ∑_v [B u * B v]_v` of the basis vectors, the diagonal of the multiplication matrices.

So `traceSym 1 r t` on blocks of `n` bits is computed from the multiplication table alone
(`Cslib.AffineDisperser.traceSymCoords_eq`): its value depends on the basis only through the
table.

## Main definitions

* `Cslib.AffineDisperser.fieldOfBits`: the field element with given coordinates.
* `Cslib.AffineDisperser.IsMulTable`: a multiplication table of a basis.
* `Cslib.AffineDisperser.fieldMul`: multiplication in coordinates.
* `Cslib.AffineDisperser.traceSymCoords`: `traceSym 1 r t` in coordinates.

## Main results

* `Cslib.AffineDisperser.fieldOfBits_fieldMul`: `fieldMul` multiplies.
* `Cslib.AffineDisperser.fieldOfBits_foldl_ite`, `Cslib.AffineDisperser.fieldOfBits_foldl_fieldMul`:
  folds of products multiply.
* `Cslib.AffineDisperser.fieldOfBits_esymmCoords`: the dynamic program for `e_t`.
* `Cslib.AffineDisperser.traceBit_traceVector`: the trace as a bit.
* `Cslib.AffineDisperser.traceSymCoords_eq`: `traceSymCoords` computes `traceSymBits 1 r t`.

## References

* [E. Ben-Sasson, S. Kopparty, *Affine dispersers from subspace polynomials*][BenSassonKopparty2012]
-/

@[expose] public section

namespace Cslib.AffineDisperser

open Module Cslib.BitString

/-! ### Coordinates -/

section Coordinates

variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {n : ℕ}

/-- The field element whose coordinates in the basis `B` are the first `n` bits of `a`; missing
bits are zero. -/
noncomputable def fieldOfBits (B : Basis (Fin n) (ZMod 2) F) (a : List Bool) : F :=
  ofBits B fun u => a.getD u false

theorem repr_fieldOfBits (B : Basis (Fin n) (ZMod 2) F) (a : List Bool) (u : Fin n) :
    B.repr (fieldOfBits B a) u = bitEquiv.symm (a.getD u false) := by
  rw [fieldOfBits, ofBits, Basis.repr_sum_self]

@[simp]
theorem fieldOfBits_nil (B : Basis (Fin n) (ZMod 2) F) : fieldOfBits B [] = 0 := by
  simp [fieldOfBits, ofBits]

/-- The coordinates of a sum: `listXor` adds coordinate words. -/
theorem fieldOfBits_listXor (B : Basis (Fin n) (ZMod 2) F) (words : List (List Bool)) :
    fieldOfBits B (listXor n words) = (words.map (fieldOfBits B)).sum := by
  have hget (u : Fin n) : (listXor n words).getD u false =
      (words.map fun w => w.getD u false).foldl xor false := by
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp [listXor, List.getD_eq_getElem?_getD]
  simp only [fieldOfBits, ofBits, hget, bitEquiv_symm_foldl_xor, List.map_map]
  clear hget
  induction words with
  | nil => simp
  | cons w words ih =>
    simp only [List.map_cons, List.sum_cons, add_smul, Finset.sum_add_distrib, ← ih,
      Function.comp_apply]
    rfl


private theorem sum_map_flatMap {α β M : Type*} [AddCommMonoid M] (l : List α)
    (g : α → List β) (f : β → M) :
    ((l.flatMap g).map f).sum = (l.map fun a => ((g a).map f).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

/-- The coordinates of the product `B u * B w` in the multiplication table `tab`. -/
def tableEntry (tab : List (List (List Bool))) (u w : ℕ) : List Bool :=
  (tab.getD u []).getD w []

/-- **Multiplication in coordinates**: the coordinates of the product of the elements with
coordinates `a` and `b`, the sum of the products `B u * B w` read from the multiplication table
`tab` of the basis, for the bits `a u = b w = 1`. -/
def fieldMul (tab : List (List (List Bool))) (a b : List Bool) : List Bool :=
  listXor tab.length ((List.range tab.length).flatMap fun u => (List.range tab.length).map fun w =>
    if a.getD u false && b.getD w false then tableEntry tab u w else [])

/-- A multiplication table of the basis `B`: `tab` lists, for `u, w < n`, the coordinates of the
product `B u * B w`. -/
def IsMulTable (B : Basis (Fin n) (ZMod 2) F) (tab : List (List (List Bool))) : Prop :=
  tab.length = n ∧ ∀ u w : Fin n, B u * B w = fieldOfBits B (tableEntry tab u w)

/-- With a multiplication table of the basis `B`, `fieldMul` multiplies: the element with
coordinates `fieldMul tab a b` is the product of those with coordinates `a` and `b`. -/
theorem fieldOfBits_fieldMul {B : Basis (Fin n) (ZMod 2) F} {tab : List (List (List Bool))}
    (htab : IsMulTable B tab) (a b : List Bool) :
    fieldOfBits B (fieldMul tab a b) = fieldOfBits B a * fieldOfBits B b := by
  rw [fieldMul, htab.1, fieldOfBits_listXor, sum_map_flatMap, List.sum_map_range]
  simp_rw [List.map_map, Function.comp_def, List.sum_map_range]
  rw [fieldOfBits, fieldOfBits, ofBits, ofBits, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => ?_
  rw [smul_mul_smul_comm, htab.2 u w]
  cases a.getD u false <;> cases b.getD w false <;>
    simp

/-- A fold of products in coordinates, skipping the elements with `c x`, multiplies the selected
factors. -/
theorem fieldOfBits_foldl_ite {B : Basis (Fin n) (ZMod 2) F} {tab : List (List (List Bool))}
    (htab : IsMulTable B tab) {X : Type*} (c : X → Prop) [DecidablePred c]
    (f : X → List Bool) (l : List X) (init : List Bool) :
    fieldOfBits B (l.foldl (fun acc x => if c x then acc else fieldMul tab acc (f x)) init) =
      fieldOfBits B init *
        ((l.filter fun x => !decide (c x)).map fun x => fieldOfBits B (f x)).prod := by
  induction l generalizing init with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, ih, List.filter_cons]
    by_cases hx : c x
    · simp [hx]
    · simp only [hx, ↓reduceIte, decide_false, Bool.not_false, List.map_cons, List.prod_cons,
        fieldOfBits_fieldMul htab]
      ring

/-- A fold of products in coordinates multiplies all the factors. -/
theorem fieldOfBits_foldl_fieldMul {B : Basis (Fin n) (ZMod 2) F}
    {tab : List (List (List Bool))} (htab : IsMulTable B tab) {X : Type*} (f : X → List Bool)
    (l : List X) (init : List Bool) :
    fieldOfBits B (l.foldl (fun acc x => fieldMul tab acc (f x)) init) =
      fieldOfBits B init * (l.map fun x => fieldOfBits B (f x)).prod := by
  simpa using fieldOfBits_foldl_ite htab (fun _ : X => False) f l init

/-- The power `y ^ (2 ^ (k + 1) - 1)` in coordinates, by `k` steps `z ↦ z ^ 2 * y` from `y`. -/
def powerPred (tab : List (List (List Bool))) (y : List Bool) (k : ℕ) : List Bool :=
  (fun z => fieldMul tab (fieldMul tab z z) y)^[k] y

theorem fieldOfBits_powerPred {B : Basis (Fin n) (ZMod 2) F} {tab : List (List (List Bool))}
    (htab : IsMulTable B tab) (y : List Bool) (k : ℕ) :
    fieldOfBits B (powerPred tab y k) = fieldOfBits B y ^ (2 ^ (k + 1) - 1) := by
  induction k with
  | zero => simp [powerPred]
  | succ k ih =>
    rw [powerPred, Function.iterate_succ_apply', ← powerPred, fieldOfBits_fieldMul htab,
      fieldOfBits_fieldMul htab, ih, ← pow_add, ← pow_succ]
    congr 1
    have := Nat.one_le_two_pow (n := k + 1)
    rw [pow_succ 2 (k + 1)]
    omega

/-- One step of the elementary symmetric polynomials `e₁, …, e_t` in coordinates: adding an
element `z` replaces `e_{j + 1}` by `e_{j + 1} + z e_j`, with `e₀ = 1`. -/
def esymmStep (tab : List (List (List Bool))) (E : List (List Bool)) (z : List Bool) :
    List (List Bool) :=
  (List.range E.length).map fun j =>
    listXor tab.length [E.getD j [], if j = 0 then z else fieldMul tab z (E.getD (j - 1) [])]

/-- The coordinates of the `t`-th elementary symmetric polynomial `e_t` of the elements with
coordinates `zs`, for `t ≥ 1`, by dynamic programming over `e₁, …, e_t`. -/
def esymmCoords (tab : List (List (List Bool))) (t : ℕ) (zs : List (List Bool)) : List Bool :=
  (zs.foldl (esymmStep tab) (List.replicate t [])).getD (t - 1) []

private theorem esymm_cons_succ {R : Type*} [CommSemiring R] (a : R) (s : Multiset R) (j : ℕ) :
    (a ::ₘ s).esymm (j + 1) = s.esymm (j + 1) + a * s.esymm j := by
  simp only [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map, Function.comp_def, Multiset.prod_cons, Multiset.sum_map_mul_left]

private theorem fieldOfBits_foldl_esymmStep {B : Basis (Fin n) (ZMod 2) F}
    {tab : List (List (List Bool))} (htab : IsMulTable B tab) (zs : List (List Bool))
    (E : List (List Bool)) (s : Multiset F)
    (hE : ∀ j < E.length, fieldOfBits B (E.getD j []) = s.esymm (j + 1)) :
    (zs.foldl (esymmStep tab) E).length = E.length ∧
      ∀ j < E.length, fieldOfBits B ((zs.foldl (esymmStep tab) E).getD j []) =
        (↑(zs.map (fieldOfBits B)) + s).esymm (j + 1) := by
  induction zs generalizing E s with
  | nil => simpa using hE
  | cons z zs ih =>
    have hlen : (esymmStep tab E z).length = E.length := by simp [esymmStep]
    have hstep : ∀ j < (esymmStep tab E z).length,
        fieldOfBits B ((esymmStep tab E z).getD j []) = (fieldOfBits B z ::ₘ s).esymm (j + 1) := by
      intro j hj
      rw [hlen] at hj
      rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hj)]
      simp only [esymmStep, List.getElem_map, List.getElem_range]
      rw [htab.1, fieldOfBits_listXor, esymm_cons_succ]
      split_ifs with hj0
      · subst hj0
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hE 0 hj,
          Multiset.esymm_zero, mul_one]
      · obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        rw [List.map_cons, List.map_cons, List.map_nil, List.sum_cons, List.sum_cons,
          List.sum_nil, add_zero, hE (j + 1) hj, fieldOfBits_fieldMul htab, Nat.add_sub_cancel,
          hE j (by omega)]
    obtain ⟨h1, h2⟩ := ih (esymmStep tab E z) (fieldOfBits B z ::ₘ s) hstep
    refine ⟨h1.trans hlen, fun j hj => ?_⟩
    rw [List.foldl_cons, h2 j (by rw [hlen]; exact hj), List.map_cons, ← Multiset.cons_coe,
      Multiset.cons_add, Multiset.add_cons]

/-- **The dynamic program for `e_t`**: with a multiplication table of the basis `B` and `0 < t`,
`esymmCoords tab t zs` has the coordinates of the `t`-th elementary symmetric polynomial of the
elements with coordinates `zs`. -/
theorem fieldOfBits_esymmCoords {B : Basis (Fin n) (ZMod 2) F} {tab : List (List (List Bool))}
    (htab : IsMulTable B tab) {t : ℕ} (ht : 0 < t) (zs : List (List Bool)) :
    fieldOfBits B (esymmCoords tab t zs) = (↑(zs.map (fieldOfBits B)) : Multiset F).esymm t := by
  have h := (fieldOfBits_foldl_esymmStep htab zs (List.replicate t []) 0 (fun j hj => by
    rw [List.getD_eq_getElem _ _ hj, List.getElem_replicate, fieldOfBits_nil,
      Multiset.esymm, Multiset.powersetCard_zero_right]; simp)).2 (t - 1) (by simpa using ht)
  rw [esymmCoords, h, add_zero, Nat.sub_add_cancel ht]


/-- The trace is the trace of the multiplication matrix: the sum of the diagonal coordinates
`[x * b i]_i`. -/
theorem trace_eq_sum_repr_mul {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {ι : Type*} [Fintype ι] (b : Basis ι R S) (x : S) :
    Algebra.trace R S x = ∑ i, b.repr (x * b i) i := by
  classical
  rw [Algebra.trace_eq_matrix_trace b, Matrix.trace]
  simp [Algebra.leftMulMatrix_eq_repr_mul]

/-- The traces of the basis elements, as bits: the trace of `B u` is the sum over `v` of the
coordinate `v` of `B u * B v`. -/
def traceVector (tab : List (List (List Bool))) : List Bool :=
  (List.range tab.length).map fun u =>
    ((List.range tab.length).map fun v => (tableEntry tab u v).getD v false).foldl xor false

/-- The trace, as a bit, of the element with coordinates `a`, from the traces `τ` of the basis
elements. -/
def traceBit (τ a : List Bool) : Bool :=
  ((List.range τ.length).map fun u => a.getD u false && τ.getD u false).foldl xor false

/-- **The trace as a bit**: with a multiplication table of the basis `B`,
`traceBit (traceVector tab) a` is the trace over `ZMod 2` of the element with coordinates `a`. -/
theorem traceBit_traceVector {B : Basis (Fin n) (ZMod 2) F} {tab : List (List (List Bool))}
    (htab : IsMulTable B tab) (a : List Bool) :
    traceBit (traceVector tab) a = bitEquiv (Algebra.trace (ZMod 2) F (fieldOfBits B a)) := by
  have hτ (u : Fin n) : bitEquiv.symm ((traceVector tab).getD u false) =
      Algebra.trace (ZMod 2) F (B u) := by
    rw [trace_eq_sum_repr_mul B, List.getD_eq_getElem _ _ (by simp [traceVector, htab.1])]
    simp only [traceVector, List.getElem_map, List.getElem_range, htab.1,
      bitEquiv_symm_foldl_xor, List.map_map, Function.comp_def, List.sum_map_range]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [htab.2 u v, repr_fieldOfBits]
  have hlen : (traceVector tab).length = n := by simp [traceVector, htab.1]
  apply bitEquiv.symm.injective
  rw [traceBit, hlen, bitEquiv_symm_foldl_xor, RingEquiv.symm_apply_apply, List.map_map,
    Function.comp_def, List.sum_map_range, fieldOfBits, ofBits, map_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [map_smul, smul_eq_mul, ← hτ u]
  cases a.getD u false <;> cases (traceVector tab).getD u false <;> decide


/-- Blocks of `n` bits: bit `u` of block `i < r` is input bit `n i + u`, among the first `r n`
input bits. -/
def blockPos {r n N : ℕ} (h : r * n ≤ N) (q : Fin r × Fin n) : Fin N :=
  Fin.castLE h (finProdFinEquiv q)

private theorem readField_blockPos (B : Basis (Fin n) (ZMod 2) F) {r N : ℕ} (h : r * n ≤ N)
    (x : List Bool) (i : Fin r) :
    readField B (blockPos h) (ofList N x) i = fieldOfBits B ((x.drop (n * i)).take n) := by
  rw [readField, fieldOfBits]
  congr 1
  funext u
  rw [List.getD_take_drop x (n * i) u.2]
  simp [blockPos, ofList, finProdFinEquiv_apply_val, add_comm]

/-- **Ben-Sasson and Kopparty's function in coordinates**: `traceSym 1 r t` at the elements with
coordinates the blocks of `n = tab.length` bits of `x`, computed from the multiplication table
`tab`: the powers by repeated squaring, the elementary symmetric polynomial by dynamic programming,
and the trace from the traces of the basis elements. -/
def traceSymCoords (tab : List (List (List Bool))) (r t : ℕ) (x : List Bool) : Bool :=
  traceBit (traceVector tab) (esymmCoords tab t ((List.range r).map fun i =>
    powerPred tab ((x.drop (tab.length * i)).take tab.length) (r - i)))

/-- **Correctness of the coordinate computation**: with a multiplication table of the basis `B`,
`traceSymCoords` computes `traceSymBits 1 r t B` on blocks of `n` bits. -/
theorem traceSymCoords_eq {B : Basis (Fin n) (ZMod 2) F} {tab : List (List (List Bool))}
    (htab : IsMulTable B tab) {r t N : ℕ} (ht : 0 < t) (h : r * n ≤ N) (x : List Bool) :
    traceSymCoords tab r t x = traceSymBits (1 : F) r t B (blockPos h) (ofList N x) := by
  rw [traceSymBits, traceSym_eq_esymm, one_mul, traceSymCoords, traceBit_traceVector htab,
    fieldOfBits_esymmCoords htab ht, Fin.univ_val_map, htab.1]
  congr 3
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.length_map, List.length_range] at h1
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn, fieldOfBits_powerPred htab,
    readField_blockPos B h x ⟨i, h1⟩]
  rw [show r - i + 1 = r + 1 - i by omega]

end Coordinates

end Cslib.AffineDisperser
