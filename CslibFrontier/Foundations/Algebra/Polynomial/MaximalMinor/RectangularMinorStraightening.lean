/-
Copyright (c) 2026 Yuqing Kong, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuqing Kong, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Algebra.Polynomial.MaximalMinor.DuplicatedFinsetOrder

/-!
# Straightening two minors of a rectangular generic matrix

This file transports the square Laplace straightening theorem through the
tagged row and column orders.  The first layer below packages a minor by its
two finite index sets; this is the paper-facing representation used by the
straightening statement.

Ported by Christian Reitwiessner from Yuqing Kong's Apache-2.0 formalization,
`RectangularMinorStraightening.lean` at commit
`4e27ef9d167be69902385307d40123ec665dc532` of
https://github.com/yuqkong-1844/finite-sample-information-monotones .
The mathematical source is [Kong2027]. This general algebra is intended for
Mathlib; its placement exception is recorded in `UPSTREAM.md`.
-/

public section

namespace Cslib

noncomputable section

namespace GenericMaximalMinor

/-- The canonical minor index associated to equally large row and column
sets.  Both sets are enumerated in increasing order. -/
@[expose] def minorIndexOfFinsets {n m : ℕ} (A : Finset (Fin n)) (B : Finset (Fin m))
    (hcard : A.card = B.card) : MinorIndex n m where
  size := ⟨A.card, by
    have hAn : A.card ≤ n := by
      simpa using Finset.card_le_univ A
    have hBm : B.card ≤ m := by
      simpa using Finset.card_le_univ B
    omega⟩
  rows := A.orderEmbOfFin rfl
  cols := B.orderEmbOfFin hcard.symm

@[simp] lemma rowSet_minorIndexOfFinsets {n m : ℕ}
    (A : Finset (Fin n)) (B : Finset (Fin m)) (hcard : A.card = B.card) :
    (minorIndexOfFinsets A B hcard).rowSet = A := by
  exact Finset.map_orderEmbOfFin_univ A rfl

@[simp] lemma colSet_minorIndexOfFinsets {n m : ℕ}
    (A : Finset (Fin n)) (B : Finset (Fin m)) (hcard : A.card = B.card) :
    (minorIndexOfFinsets A B hcard).colSet = B := by
  exact Finset.map_orderEmbOfFin_univ B hcard.symm

/-- The canonical generic minor selected by two finite subsets.  As with
`finsetMinor`, unequal cardinalities give zero. -/
@[expose] def finsetMinorPoly {D : Type*} [CommRing D] {n m : ℕ}
    (A : Finset (Fin n)) (B : Finset (Fin m)) : GenericPoly D n m :=
  if h : A.card = B.card then minorPoly (minorIndexOfFinsets A B h) else 0

@[simp] lemma finsetMinorPoly_of_card_ne {D : Type*} [CommRing D] {n m : ℕ}
    (A : Finset (Fin n)) (B : Finset (Fin m)) (hcard : A.card ≠ B.card) :
    finsetMinorPoly (D := D) A B = 0 := by
  simp [finsetMinorPoly, hcard]

lemma finsetMinorPoly_of_card_eq {D : Type*} [CommRing D] {n m : ℕ}
    (A : Finset (Fin n)) (B : Finset (Fin m)) (hcard : A.card = B.card) :
    finsetMinorPoly (D := D) A B = minorPoly (minorIndexOfFinsets A B hcard) := by
  rw [finsetMinorPoly, dite_eq_left hcard]

/-! ## Transporting subsets across equal finite cardinalities -/

/-- Transport a subset of `Fin a` across an equality `a = b`. -/
def castFinset {a b : ℕ} (h : a = b) (P : Finset (Fin a)) : Finset (Fin b) :=
  P.map (Fin.castOrderIso h).toEmbedding

@[simp] lemma card_castFinset {a b : ℕ} (h : a = b) (P : Finset (Fin a)) :
    (castFinset h P).card = P.card := by
  simp [castFinset]

@[simp] lemma mem_castFinset_iff {a b : ℕ} (h : a = b)
    (P : Finset (Fin a)) (i : Fin b) :
    i ∈ castFinset h P ↔ (Fin.castOrderIso h).symm i ∈ P := by
  simp [castFinset]

@[simp] lemma castFinset_univ {a b : ℕ} (h : a = b) :
    castFinset h (Finset.univ : Finset (Fin a)) = Finset.univ := by
  ext i
  simp

@[simp] lemma castFinset_compl {a b : ℕ} (h : a = b)
    (P : Finset (Fin a)) :
    castFinset h Pᶜ = (castFinset h P)ᶜ := by
  ext i
  simp

lemma prefixLE_castFinset_iff {a b : ℕ} (h : a = b)
    (P Q : Finset (Fin a)) :
    castFinset h P ≼ₚ castFinset h Q ↔ P ≼ₚ Q := by
  subst b
  simp [castFinset]

lemma prefixLT_castFinset_iff {a b : ℕ} (h : a = b)
    (P Q : Finset (Fin a)) :
    castFinset h P ≺ₚ castFinset h Q ↔ P ≺ₚ Q := by
  subst b
  simp [castFinset]

lemma goodSubset_castFinset_iff {a b : ℕ} (h : a = b)
    (P : Finset (Fin a)) :
    GoodSubset (castFinset h P) ↔ GoodSubset P := by
  unfold GoodSubset
  rw [← castFinset_compl, prefixLE_castFinset_iff]

@[simp] lemma castFinset_symm_castFinset {a b : ℕ} (h : a = b)
    (P : Finset (Fin a)) :
    castFinset h.symm (castFinset h P) = P := by
  subst b
  simp [castFinset]

/-- Transport the domain of a function between equal finite types. -/
def castFinFunction {a b : ℕ} (h : a = b) {γ : Type*}
    (f : Fin a → γ) : Fin b → γ :=
  fun i ↦ f ((Fin.castOrderIso h).symm i)

/-- Pull a subset back along the same finite cast equivalence. -/
def castFinsetBack {a b : ℕ} (h : a = b)
    (P : Finset (Fin b)) : Finset (Fin a) :=
  P.map (Fin.castOrderIso h).symm.toEmbedding

@[simp] lemma castFinset_castFinsetBack {a b : ℕ} (h : a = b)
    (P : Finset (Fin b)) :
    castFinset h (castFinsetBack h P) = P := by
  ext i
  simp [castFinset, castFinsetBack]

@[simp] lemma castFinsetBack_castFinset {a b : ℕ} (h : a = b)
    (P : Finset (Fin a)) :
    castFinsetBack h (castFinset h P) = P := by
  ext i
  simp [castFinset, castFinsetBack]

lemma injOn_castFinFunction_iff {a b : ℕ} (h : a = b) {γ : Type*}
    (f : Fin a → γ) (P : Finset (Fin b)) :
    Set.InjOn (castFinFunction h f) P ↔
      Set.InjOn f (castFinsetBack h P) := by
  let e : Fin a ≃o Fin b := Fin.castOrderIso h
  constructor
  · intro hinj x hx y hy hxy
    have hex : e x ∈ P := by
      simpa [castFinsetBack, e] using hx
    have hey : e y ∈ P := by
      simpa [castFinsetBack, e] using hy
    apply e.injective
    apply hinj hex hey
    simpa [castFinFunction, e] using hxy
  · intro hinj x hx y hy hxy
    apply e.symm.injective
    apply hinj
    · exact Finset.mem_map.mpr ⟨x, hx, by simp [e]⟩
    · exact Finset.mem_map.mpr ⟨y, hy, by simp [e]⟩
    · simpa [castFinFunction, e] using hxy

@[simp] lemma image_castFinFunction {a b : ℕ} (h : a = b) {γ : Type*}
    [DecidableEq γ] (f : Fin a → γ) (P : Finset (Fin b)) :
    P.image (castFinFunction h f) = (castFinsetBack h P).image f := by
  rw [castFinsetBack, Finset.map_eq_image, Finset.image_image]
  rfl

lemma castFinFunction_mono {a b : ℕ} (h : a = b)
    {γ : Type*} [Preorder γ] (f : Fin a → γ) (hf : Monotone f) :
    Monotone (castFinFunction h f) := by
  intro i j hij
  exact hf ((Fin.castOrderIso h).symm.monotone hij)

/-! ## The duplicated square matrix attached to two rectangular minors -/

/-- Column positions transported to the cardinality of the duplicated row
order. -/
def rectangularColLeftSet {n m : ℕ}
    (S₁ S₂ : Finset (Fin n)) (T₁ T₂ : Finset (Fin m))
    (hsize : T₁.card + T₂.card = S₁.card + S₂.card) :
    Finset (Fin (S₁.card + S₂.card)) :=
  castFinset hsize (duplicatedLeftSet T₁ T₂)

/-- Forget a transported column tag. -/
def rectangularColForget {n m : ℕ}
    (S₁ S₂ : Finset (Fin n)) (T₁ T₂ : Finset (Fin m))
    (hsize : T₁.card + T₂.card = S₁.card + S₂.card) :
    Fin (S₁.card + S₂.card) → Fin m :=
  castFinFunction hsize (duplicatedForget T₁ T₂)

/-- The square generic matrix obtained by duplicating the row and column
content of two rectangular minors. -/
def rectangularDuplicatedMatrix {D : Type*} [CommRing D] {n m : ℕ}
    (S₁ S₂ : Finset (Fin n)) (T₁ T₂ : Finset (Fin m))
    (hsize : T₁.card + T₂.card = S₁.card + S₂.card) :
    Matrix (Fin (S₁.card + S₂.card)) (Fin (S₁.card + S₂.card))
      (GenericPoly D n m) :=
  fun i j ↦ MvPolynomial.X
    (duplicatedForget S₁ S₂ i,
      rectangularColForget S₁ S₂ T₁ T₂ hsize j)

@[simp] lemma rectangularColLeftSet_compl {n m : ℕ}
    (S₁ S₂ : Finset (Fin n)) (T₁ T₂ : Finset (Fin m))
    (hsize : T₁.card + T₂.card = S₁.card + S₂.card) :
    (rectangularColLeftSet S₁ S₂ T₁ T₂ hsize)ᶜ =
      castFinset hsize (duplicatedRightSet T₁ T₂) := by
  rw [rectangularColLeftSet, ← castFinset_compl, duplicatedLeftSet_compl]

lemma rectangularColImage_prefixLT {n m : ℕ}
    (S₁ S₂ : Finset (Fin n)) (T₁ T₂ : Finset (Fin m))
    (hsize : T₁.card + T₂.card = S₁.card + S₂.card)
    (P : Finset (Fin (S₁.card + S₂.card)))
    (hinj : Set.InjOn (rectangularColForget S₁ S₂ T₁ T₂ hsize) P)
    (hP : P ≺ₚ rectangularColLeftSet S₁ S₂ T₁ T₂ hsize) :
    P.image (rectangularColForget S₁ S₂ T₁ T₂ hsize) ≺ₚ T₁ := by
  have hinj' : Set.InjOn (duplicatedForget T₁ T₂)
      (castFinsetBack hsize P) :=
    (injOn_castFinFunction_iff hsize (duplicatedForget T₁ T₂) P).mp hinj
  have hP' : castFinsetBack hsize P ≺ₚ duplicatedLeftSet T₁ T₂ := by
    have hcast := (prefixLT_castFinset_iff hsize
      (castFinsetBack hsize P) (duplicatedLeftSet T₁ T₂)).mp
    exact hcast (by
      simpa [rectangularColLeftSet] using hP)
  have hstrict := duplicatedImage_prefixLT T₁ T₂
    (castFinsetBack hsize P) hinj' hP'
  simpa [duplicatedImage, rectangularColForget] using hstrict

lemma rectangularColImage_prefixLE_of_prefixLE {n m : ℕ}
    (S₁ S₂ : Finset (Fin n)) (T₁ T₂ : Finset (Fin m))
    (hsize : T₁.card + T₂.card = S₁.card + S₂.card)
    (P Q : Finset (Fin (S₁.card + S₂.card)))
    (hinjP : Set.InjOn (rectangularColForget S₁ S₂ T₁ T₂ hsize) P)
    (hinjQ : Set.InjOn (rectangularColForget S₁ S₂ T₁ T₂ hsize) Q)
    (hPQ : P ≼ₚ Q) :
    P.image (rectangularColForget S₁ S₂ T₁ T₂ hsize) ≼ₚ
      Q.image (rectangularColForget S₁ S₂ T₁ T₂ hsize) := by
  have hinjP' : Set.InjOn (duplicatedForget T₁ T₂)
      (castFinsetBack hsize P) :=
    (injOn_castFinFunction_iff hsize (duplicatedForget T₁ T₂) P).mp hinjP
  have hinjQ' : Set.InjOn (duplicatedForget T₁ T₂)
      (castFinsetBack hsize Q) :=
    (injOn_castFinFunction_iff hsize (duplicatedForget T₁ T₂) Q).mp hinjQ
  have hPQ' : castFinsetBack hsize P ≼ₚ castFinsetBack hsize Q := by
    apply (prefixLE_castFinset_iff hsize _ _).mp
    simpa using hPQ
  have hle := duplicatedImage_prefixLE_of_prefixLE T₁ T₂
    (castFinsetBack hsize P) (castFinsetBack hsize Q) hinjP' hinjQ' hPQ'
  simpa [duplicatedImage, rectangularColForget] using hle

/-! ## Identifying surviving duplicated minors -/

/-- Pulling the generic matrix back along two monotone maps does not change a
minor when both maps are injective on the selected positions.  The increasing
enumerations on both sides agree, so no sign is introduced here. -/
lemma finsetMinor_pulledGenericMatrix {D : Type*} [CommRing D]
    {N n m : ℕ} (f : Fin N → Fin n) (g : Fin N → Fin m)
    (hf : Monotone f) (hg : Monotone g)
    (P Q : Finset (Fin N))
    (hinjP : Set.InjOn f P) (hinjQ : Set.InjOn g Q) :
    finsetMinor (Matrix.of (fun i j ↦ (MvPolynomial.X (f i, g j) : GenericPoly D n m))) P Q =
      finsetMinorPoly (D := D) (P.image f) (Q.image g) := by
  classical
  by_cases hPQ : P.card = Q.card
  · have hA : (P.image f).card = P.card :=
      Finset.card_image_iff.mpr hinjP
    have hB : (Q.image g).card = Q.card :=
      Finset.card_image_iff.mpr hinjQ
    have hAB : (P.image f).card = (Q.image g).card :=
      hA.trans (hPQ.trans hB.symm)
    let : Fintype P := Subtype.fintype (fun i : Fin N ↦ i ∈ P)
    rw [finsetMinor, dite_eq_left hPQ, finsetMinorPoly, dite_eq_left hAB]
    let eP : Fin (P.image f).card ≃o P :=
      (Fin.castOrderIso hA).trans (P.orderIsoOfFin rfl)
    let ePQ : P ≃o Q :=
      (P.orderIsoOfFin rfl).symm.trans (Q.orderIsoOfFin hPQ.symm)
    have hePQ : ePQ.toEquiv = orderedFinsetEquiv P Q hPQ := by
      rfl
    have hrowStrict : StrictMono (fun i ↦ f (eP i)) := by
      intro i j hij
      have hij' : eP i < eP j := eP.strictMono hij
      have hle : f (eP i) ≤ f (eP j) := hf hij'.le
      exact lt_of_le_of_ne hle (by
        intro heq
        apply hij'.ne
        apply Subtype.ext
        exact hinjP (eP i).property (eP j).property heq)
    have hcolStrict : StrictMono (fun i ↦ g (ePQ (eP i))) := by
      intro i j hij
      have hij' : ePQ (eP i) < ePQ (eP j) :=
        ePQ.strictMono (eP.strictMono hij)
      have hle : g (ePQ (eP i)) ≤ g (ePQ (eP j)) := hg hij'.le
      exact lt_of_le_of_ne hle (by
        intro heq
        apply hij'.ne
        apply Subtype.ext
        exact hinjQ (ePQ (eP i)).property (ePQ (eP j)).property heq)
    have hrowEnum :
        (fun i ↦ f (eP i)) = (P.image f).orderEmbOfFin rfl := by
      apply Finset.orderEmbOfFin_unique rfl
      · intro i
        exact Finset.mem_image.mpr ⟨eP i, (eP i).property, rfl⟩
      · exact hrowStrict
    have hcolEnum :
        (fun i ↦ g (ePQ (eP i))) =
          (Q.image g).orderEmbOfFin hAB.symm := by
      apply Finset.orderEmbOfFin_unique hAB.symm
      · intro i
        exact Finset.mem_image.mpr
          ⟨ePQ (eP i), (ePQ (eP i)).property, rfl⟩
      · exact hcolStrict
    let M : Matrix P P (GenericPoly D n m) :=
      fun i j ↦ MvPolynomial.X
        (f i, g (orderedFinsetEquiv P Q hPQ j))
    unfold minorAlongEquiv
    change Matrix.det M = minorPoly (minorIndexOfFinsets
      (P.image f) (Q.image g) hAB)
    unfold minorPoly minorMatrix
    calc
      Matrix.det M = Matrix.det (M.reindex eP.symm.toEquiv eP.symm.toEquiv) :=
        (Matrix.det_reindex_self eP.symm.toEquiv M).symm
      _ = Matrix.det (fun i j ↦
          MvPolynomial.X
            ((minorIndexOfFinsets (P.image f) (Q.image g) hAB).rows i,
              (minorIndexOfFinsets (P.image f) (Q.image g) hAB).cols j)) := by
        apply congrArg Matrix.det
        funext i j
        change MvPolynomial.X
            (f (eP i), g (orderedFinsetEquiv P Q hPQ (eP j))) =
          MvPolynomial.X
            ((minorIndexOfFinsets (P.image f) (Q.image g) hAB).rows i,
              (minorIndexOfFinsets (P.image f) (Q.image g) hAB).cols j)
        rw [← hePQ]
        change MvPolynomial.X (f (eP i), g (ePQ (eP j))) =
          MvPolynomial.X
            ((P.image f).orderEmbOfFin rfl i,
              (Q.image g).orderEmbOfFin hAB.symm j)
        rw [← congrFun hrowEnum i, ← congrFun hcolEnum j]
  · rw [finsetMinor_of_card_ne _ _ _ hPQ]
    apply (finsetMinorPoly_of_card_ne (D := D) (P.image f) (Q.image g) ?_).symm
    intro himage
    apply hPQ
    have hA : (P.image f).card = P.card :=
      Finset.card_image_iff.mpr hinjP
    have hB : (Q.image g).card = Q.card :=
      Finset.card_image_iff.mpr hinjQ
    omega

lemma finsetMinor_pulled_eq_zero_of_not_injOn_left
    {R : Type*} [CommRing R] {N n m : ℕ}
    (H : Fin n → Fin m → R) (f : Fin N → Fin n) (g : Fin N → Fin m)
    (P Q : Finset (Fin N)) (hnot : ¬Set.InjOn f P) :
    finsetMinor (Matrix.of (fun i j ↦ H (f i) (g j))) P Q = 0 := by
  classical
  by_cases hcard : P.card = Q.card
  · let : Fintype P := Subtype.fintype (fun i : Fin N ↦ i ∈ P)
    unfold Set.InjOn at hnot
    push Not at hnot
    rcases hnot with ⟨x, hx, y, hy, hxy, hne⟩
    rw [finsetMinor, dite_eq_left hcard]
    unfold minorAlongEquiv
    apply Matrix.det_zero_of_row_eq
      (show (⟨x, hx⟩ : P) ≠ ⟨y, hy⟩ by
        intro heq
        exact hne (congrArg Subtype.val heq))
    funext j
    change H (f x) _ = H (f y) _
    rw [hxy]
  · exact finsetMinor_of_card_ne _ _ _ hcard

lemma finsetMinor_pulled_eq_zero_of_not_injOn_right
    {R : Type*} [CommRing R] {N n m : ℕ}
    (H : Fin n → Fin m → R) (f : Fin N → Fin n) (g : Fin N → Fin m)
    (P Q : Finset (Fin N)) (hnot : ¬Set.InjOn g Q) :
    finsetMinor (Matrix.of (fun i j ↦ H (f i) (g j))) P Q = 0 := by
  classical
  by_cases hcard : P.card = Q.card
  · let : Fintype P := Subtype.fintype (fun i : Fin N ↦ i ∈ P)
    unfold Set.InjOn at hnot
    push Not at hnot
    rcases hnot with ⟨x, hx, y, hy, hxy, hne⟩
    let e : P ≃ Q := orderedFinsetEquiv P Q hcard
    let i : P := e.symm ⟨x, hx⟩
    let j : P := e.symm ⟨y, hy⟩
    have hij : i ≠ j := by
      intro hij
      apply hne
      have := congrArg (fun q : P ↦ (e q : Fin N)) hij
      simpa [i, j, e] using this
    rw [finsetMinor, dite_eq_left hcard]
    unfold minorAlongEquiv
    apply Matrix.det_zero_of_column_eq hij
    intro k
    change H _ (g (e i)) = H _ (g (e j))
    rw [show e i = (⟨x, hx⟩ : Q) by simp [i],
      show e j = (⟨y, hy⟩ : Q) by simp [j], hxy]
  · exact finsetMinor_of_card_ne _ _ _ hcard

lemma finsetMinor_rectangularDuplicatedMatrix {D : Type*} [CommRing D]
    {n m : ℕ} (S₁ S₂ : Finset (Fin n)) (T₁ T₂ : Finset (Fin m))
    (hsize : T₁.card + T₂.card = S₁.card + S₂.card)
    (P Q : Finset (Fin (S₁.card + S₂.card)))
    (hinjP : Set.InjOn (duplicatedForget S₁ S₂) P)
    (hinjQ : Set.InjOn
      (rectangularColForget S₁ S₂ T₁ T₂ hsize) Q) :
    finsetMinor (rectangularDuplicatedMatrix (D := D)
        S₁ S₂ T₁ T₂ hsize) P Q =
      finsetMinorPoly (D := D)
        (P.image (duplicatedForget S₁ S₂))
        (Q.image (rectangularColForget S₁ S₂ T₁ T₂ hsize)) := by
  exact finsetMinor_pulledGenericMatrix
    (duplicatedForget S₁ S₂)
    (rectangularColForget S₁ S₂ T₁ T₂ hsize)
    (duplicatedForget_mono S₁ S₂)
    (castFinFunction_mono hsize (duplicatedForget T₁ T₂)
      (duplicatedForget_mono T₁ T₂))
    P Q hinjP hinjQ

lemma rectangularColForget_injOn_leftSet {n m : ℕ}
    (S₁ S₂ : Finset (Fin n)) (T₁ T₂ : Finset (Fin m))
    (hsize : T₁.card + T₂.card = S₁.card + S₂.card) :
    Set.InjOn (rectangularColForget S₁ S₂ T₁ T₂ hsize)
      (rectangularColLeftSet S₁ S₂ T₁ T₂ hsize) := by
  unfold rectangularColForget rectangularColLeftSet
  rw [injOn_castFinFunction_iff]
  simpa using
    (duplicatedForget_injOn_leftSet T₁ T₂)

lemma rectangularColForget_injOn_rightSet {n m : ℕ}
    (S₁ S₂ : Finset (Fin n)) (T₁ T₂ : Finset (Fin m))
    (hsize : T₁.card + T₂.card = S₁.card + S₂.card) :
    Set.InjOn (rectangularColForget S₁ S₂ T₁ T₂ hsize)
      (castFinset hsize (duplicatedRightSet T₁ T₂)) := by
  unfold rectangularColForget
  rw [injOn_castFinFunction_iff]
  simpa using (duplicatedForget_injOn_rightSet T₁ T₂)

@[simp] lemma rectangularColImage_leftSet {n m : ℕ}
    (S₁ S₂ : Finset (Fin n)) (T₁ T₂ : Finset (Fin m))
    (hsize : T₁.card + T₂.card = S₁.card + S₂.card) :
    (rectangularColLeftSet S₁ S₂ T₁ T₂ hsize).image
        (rectangularColForget S₁ S₂ T₁ T₂ hsize) = T₁ := by
  unfold rectangularColForget rectangularColLeftSet
  rw [image_castFinFunction]
  simpa [duplicatedImage] using
    (duplicatedImage_leftSet T₁ T₂)

@[simp] lemma rectangularColImage_rightSet {n m : ℕ}
    (S₁ S₂ : Finset (Fin n)) (T₁ T₂ : Finset (Fin m))
    (hsize : T₁.card + T₂.card = S₁.card + S₂.card) :
    (castFinset hsize (duplicatedRightSet T₁ T₂)).image
        (rectangularColForget S₁ S₂ T₁ T₂ hsize) = T₂ := by
  unfold rectangularColForget
  rw [image_castFinFunction]
  simpa [duplicatedImage] using (duplicatedImage_rightSet T₁ T₂)

lemma finsetMinor_rectangularDuplicatedMatrix_left {D : Type*} [CommRing D]
    {n m : ℕ} (S₁ S₂ : Finset (Fin n)) (T₁ T₂ : Finset (Fin m))
    (hsize : T₁.card + T₂.card = S₁.card + S₂.card) :
    finsetMinor (rectangularDuplicatedMatrix (D := D) S₁ S₂ T₁ T₂ hsize)
        (duplicatedLeftSet S₁ S₂)
        (rectangularColLeftSet S₁ S₂ T₁ T₂ hsize) =
      finsetMinorPoly (D := D) S₁ T₁ := by
  rw [finsetMinor_rectangularDuplicatedMatrix
    S₁ S₂ T₁ T₂ hsize
    (duplicatedLeftSet S₁ S₂)
    (rectangularColLeftSet S₁ S₂ T₁ T₂ hsize)
    (duplicatedForget_injOn_leftSet S₁ S₂)
    (rectangularColForget_injOn_leftSet S₁ S₂ T₁ T₂ hsize)]
  rw [← duplicatedImage]
  rw [duplicatedImage_leftSet, rectangularColImage_leftSet]

lemma finsetMinor_rectangularDuplicatedMatrix_right {D : Type*} [CommRing D]
    {n m : ℕ} (S₁ S₂ : Finset (Fin n)) (T₁ T₂ : Finset (Fin m))
    (hsize : T₁.card + T₂.card = S₁.card + S₂.card) :
    finsetMinor (rectangularDuplicatedMatrix (D := D) S₁ S₂ T₁ T₂ hsize)
        (duplicatedRightSet S₁ S₂)
        (castFinset hsize (duplicatedRightSet T₁ T₂)) =
      finsetMinorPoly (D := D) S₂ T₂ := by
  rw [finsetMinor_rectangularDuplicatedMatrix
    S₁ S₂ T₁ T₂ hsize
    (duplicatedRightSet S₁ S₂)
    (castFinset hsize (duplicatedRightSet T₁ T₂))
    (duplicatedForget_injOn_rightSet S₁ S₂)
    (rectangularColForget_injOn_rightSet S₁ S₂ T₁ T₂ hsize)]
  rw [← duplicatedImage]
  rw [duplicatedImage_rightSet, rectangularColImage_rightSet]

/-! ## Signed Laplace products -/

lemma intUnit_cast_mul_mem_iff {R : Type*} [CommRing R]
    (H : AddSubgroup R) (u : ℤˣ) (x : R) :
    (u : R) * x ∈ H ↔ x ∈ H := by
  have hu : u = 1 ∨ u = -1 := by
    have hmem : u ∈ (Finset.univ : Finset ℤˣ) := Finset.mem_univ u
    rw [UnitsInt.univ] at hmem
    simpa using hmem
  rcases hu with rfl | rfl
  · simp
  · simp

/-- A signed Laplace permutation sum is the product of its two complementary
canonical minors.  The single coefficient is an integer unit, hence only a
harmless sign over every coefficient ring. -/
lemma exists_intUnit_mul_laplacePermSum_eq_mul_finsetMinor
    {R : Type*} [CommRing R] {N : ℕ}
    (Y : Matrix (Fin N) (Fin N) R) (A B : Finset (Fin N))
    (hcard : A.card = B.card) :
    ∃ u : ℤˣ, (u : R) * laplacePermSum Y A B =
      finsetMinor Y A B * finsetMinor Y Aᶜ Bᶜ := by
  classical
  let e : A ≃ B := orderedFinsetEquiv A B hcard
  have hcomp : Aᶜ.card = Bᶜ.card := by
    simpa [Finset.card_compl] using congrArg (fun k ↦ N - k) hcard
  let : Fintype {i : Fin N // i ∈ Aᶜ} :=
    Subtype.fintype (fun i : Fin N ↦ i ∈ Aᶜ)
  let : Fintype {i : Fin N // ¬i ∈ A} :=
    Subtype.fintype (fun i : Fin N ↦ ¬i ∈ A)
  let cA : {i : Fin N // i ∈ Aᶜ} ≃ {i : Fin N // ¬i ∈ A} :=
    Equiv.subtypeEquivRight (fun i ↦ by simp)
  let cB : {i : Fin N // i ∈ Bᶜ} ≃ {i : Fin N // ¬i ∈ B} :=
    Equiv.subtypeEquivRight (fun i ↦ by simp)
  let ec : {i : Fin N // i ∈ Aᶜ} ≃ {i : Fin N // i ∈ Bᶜ} :=
    cA.trans (e.toCompl.trans cB.symm)
  let s₁ : ℤˣ := Equiv.Perm.sign e.extendSubtype
  let s₂ : ℤˣ := Equiv.Perm.sign
    (ec.trans (orderedFinsetEquiv Aᶜ Bᶜ hcomp).symm)
  have hleft : minorAlongEquiv Y e = finsetMinor Y A B := by
    rw [finsetMinor, dite_eq_left hcard]
  have hcompMinor : minorAlongEquiv Y e.toCompl = minorAlongEquiv Y ec := by
    let M : Matrix {i : Fin N // ¬i ∈ A} {i : Fin N // ¬i ∈ A} R :=
      fun i j ↦ Y i (e.toCompl j)
    let Mc : Matrix {i : Fin N // i ∈ Aᶜ} {i : Fin N // i ∈ Aᶜ} R :=
      fun i j ↦ Y i (ec j)
    unfold minorAlongEquiv
    change Matrix.det M = Matrix.det Mc
    calc
      Matrix.det M = Matrix.det (M.reindex cA.symm cA.symm) :=
        (Matrix.det_reindex_self cA.symm M).symm
      _ = Matrix.det Mc := by
        apply congrArg Matrix.det
        funext i j
        rfl
  have hright : minorAlongEquiv Y e.toCompl =
      (s₂ : R) * finsetMinor Y Aᶜ Bᶜ := by
    rw [hcompMinor]
    simpa [s₂] using
      (minorAlongEquiv_eq_sign_mul_finsetMinor Y Aᶜ Bᶜ hcomp ec)
  have hblock := sign_mul_det_maskedMatrix_eq_mul_minors Y A B e
  rw [← laplacePermSum_eq_det_maskedMatrix, hleft, hright] at hblock
  refine ⟨s₂ * s₁, ?_⟩
  simp only [Units.val_mul, Int.cast_mul]
  calc
    (s₂ : R) * (s₁ : R) * laplacePermSum Y A B =
        (s₂ : R) * ((s₁ : R) * laplacePermSum Y A B) := by ring
    _ = (s₂ : R) * ((s₂ : R) *
        (finsetMinor Y A B * finsetMinor Y Aᶜ Bᶜ)) := by
      rw [hblock]
      ring
    _ = finsetMinor Y A B * finsetMinor Y Aᶜ Bᶜ := by
      rw [← mul_assoc, ← Int.cast_mul, Int.units_coe_mul_self]
      simp

/-! ## The rectangular straightening span -/

lemma row_left_prefixLE_right_of_good {n : ℕ}
    (S₁ S₂ : Finset (Fin n)) (hgood : GoodSubset (duplicatedLeftSet S₁ S₂)) :
    S₁ ≼ₚ S₂ := by
  have hpos : duplicatedLeftSet S₁ S₂ ≼ₚ duplicatedRightSet S₁ S₂ := by
    rw [← duplicatedLeftSet_compl]
    exact hgood
  have himage := duplicatedImage_prefixLE_of_prefixLE S₁ S₂
    (duplicatedLeftSet S₁ S₂) (duplicatedRightSet S₁ S₂)
    (duplicatedForget_injOn_leftSet S₁ S₂)
    (duplicatedForget_injOn_rightSet S₁ S₂) hpos
  simpa only [duplicatedImage_leftSet, duplicatedImage_rightSet] using himage

lemma col_left_prefixLE_right_of_good {n m : ℕ}
    (S₁ S₂ : Finset (Fin n)) (T₁ T₂ : Finset (Fin m))
    (hsize : T₁.card + T₂.card = S₁.card + S₂.card)
    (hgood : GoodSubset (rectangularColLeftSet S₁ S₂ T₁ T₂ hsize)) :
    T₁ ≼ₚ T₂ := by
  have hpos : rectangularColLeftSet S₁ S₂ T₁ T₂ hsize ≼ₚ
      castFinset hsize (duplicatedRightSet T₁ T₂) := by
    rw [← rectangularColLeftSet_compl]
    exact hgood
  have himage := rectangularColImage_prefixLE_of_prefixLE
    S₁ S₂ T₁ T₂ hsize
    (rectangularColLeftSet S₁ S₂ T₁ T₂ hsize)
    (castFinset hsize (duplicatedRightSet T₁ T₂))
    (rectangularColForget_injOn_leftSet S₁ S₂ T₁ T₂ hsize)
    (rectangularColForget_injOn_rightSet S₁ S₂ T₁ T₂ hsize) hpos
  simpa only [rectangularColImage_leftSet, rectangularColImage_rightSet] using himage

lemma left_bad_row_or_col_of_not_minorLE {n m : ℕ}
    (S₁ S₂ : Finset (Fin n)) (T₁ T₂ : Finset (Fin m))
    (hsize : T₁.card + T₂.card = S₁.card + S₂.card)
    (hnot : ¬(S₁ ≼ₚ S₂ ∧ T₁ ≼ₚ T₂)) :
    ¬GoodSubset (duplicatedLeftSet S₁ S₂) ∨
      ¬GoodSubset (rectangularColLeftSet S₁ S₂ T₁ T₂ hsize) := by
  by_contra h
  push Not at h
  exact hnot ⟨row_left_prefixLE_right_of_good S₁ S₂ h.1,
    col_left_prefixLE_right_of_good S₁ S₂ T₁ T₂ hsize h.2⟩

/-- Products allowed on the right-hand side of rectangular two-minor
straightening. -/
@[expose] def twoMinorStraighteningGenerators {D : Type*} [CommRing D] {n m : ℕ}
    (S₁ S₂ : Finset (Fin n)) (T₁ _T₂ : Finset (Fin m)) :
    Set (GenericPoly D n m) :=
  {x | ∃ A C : Finset (Fin n), ∃ B E : Finset (Fin m),
    A.card = B.card ∧ C.card = E.card ∧
    A ≼ₚ S₁ ∧ B ≼ₚ T₁ ∧ A ≼ₚ C ∧ B ≼ₚ E ∧
    (A ≺ₚ S₁ ∨ B ≺ₚ T₁) ∧
    A.card + C.card = S₁.card + S₂.card ∧
    x = finsetMinorPoly (D := D) A B * finsetMinorPoly (D := D) C E}

/-- Integral span of the output products in two-minor straightening. -/
@[expose] def twoMinorStraighteningSpan {D : Type*} [CommRing D] {n m : ℕ}
    (S₁ S₂ : Finset (Fin n)) (T₁ T₂ : Finset (Fin m)) :
    AddSubgroup (GenericPoly D n m) :=
  AddSubgroup.closure (twoMinorStraighteningGenerators (D := D) S₁ S₂ T₁ T₂)

lemma laplacePermSum_mem_twoMinorStraighteningSpan
    {D : Type*} [CommRing D] {n m : ℕ}
    (S₁ S₂ : Finset (Fin n)) (T₁ T₂ : Finset (Fin m))
    (hsize : T₁.card + T₂.card = S₁.card + S₂.card)
    (hnot : ¬(S₁ ≼ₚ S₂ ∧ T₁ ≼ₚ T₂))
    (P Q : Finset (Fin (S₁.card + S₂.card)))
    (hcard : P.card = Q.card)
    (hPle : P ≼ₚ duplicatedLeftSet S₁ S₂)
    (hQle : Q ≼ₚ rectangularColLeftSet S₁ S₂ T₁ T₂ hsize)
    (hPgood : GoodSubset P) (hQgood : GoodSubset Q) :
    laplacePermSum
        (rectangularDuplicatedMatrix (D := D) S₁ S₂ T₁ T₂ hsize) P Q ∈
      twoMinorStraighteningSpan (D := D) S₁ S₂ T₁ T₂ := by
  classical
  let f := duplicatedForget S₁ S₂
  let g := rectangularColForget S₁ S₂ T₁ T₂ hsize
  let Y := rectangularDuplicatedMatrix (D := D) S₁ S₂ T₁ T₂ hsize
  let H := twoMinorStraighteningSpan (D := D) S₁ S₂ T₁ T₂
  obtain ⟨u, hu⟩ :=
    exists_intUnit_mul_laplacePermSum_eq_mul_finsetMinor Y P Q hcard
  apply (intUnit_cast_mul_mem_iff H u (laplacePermSum Y P Q)).mp
  rw [hu]
  by_cases hinjP : Set.InjOn f P
  · by_cases hinjQ : Set.InjOn g Q
    · by_cases hinjPc : Set.InjOn f (Pᶜ : Finset (Fin (S₁.card + S₂.card)))
      · by_cases hinjQc : Set.InjOn g (Qᶜ : Finset (Fin (S₁.card + S₂.card)))
        · let A : Finset (Fin n) := P.image f
          let B : Finset (Fin m) := Q.image g
          let C : Finset (Fin n) := Pᶜ.image f
          let E : Finset (Fin m) := Qᶜ.image g
          have hAB : A.card = B.card := by
            dsimp [A, B]
            rw [Finset.card_image_iff.mpr hinjP,
              Finset.card_image_iff.mpr hinjQ, hcard]
          have hCE : C.card = E.card := by
            calc
              C.card = Pᶜ.card := Finset.card_image_iff.mpr hinjPc
              _ = Qᶜ.card := by
                simpa [Finset.card_compl] using
                  congrArg (fun k ↦ S₁.card + S₂.card - k) hcard
              _ = E.card := (Finset.card_image_iff.mpr hinjQc).symm
          have hAle : A ≼ₚ S₁ := by
            have h := duplicatedImage_prefixLE_of_prefixLE S₁ S₂
              P (duplicatedLeftSet S₁ S₂) hinjP
              (duplicatedForget_injOn_leftSet S₁ S₂) hPle
            rw [duplicatedImage_leftSet] at h
            change duplicatedImage S₁ S₂ P ≼ₚ S₁
            exact h
          have hBle : B ≼ₚ T₁ := by
            have h' := rectangularColImage_prefixLE_of_prefixLE
              S₁ S₂ T₁ T₂ hsize
              Q (rectangularColLeftSet S₁ S₂ T₁ T₂ hsize)
              hinjQ
              (rectangularColForget_injOn_leftSet S₁ S₂ T₁ T₂ hsize) hQle
            simpa [B, g] using h'
          have hAC : A ≼ₚ C := by
            have h := duplicatedImage_prefixLE_of_prefixLE S₁ S₂
              P Pᶜ hinjP hinjPc hPgood
            change duplicatedImage S₁ S₂ P ≼ₚ duplicatedImage S₁ S₂ Pᶜ
            exact h
          have hBE : B ≼ₚ E := by
            have h' := rectangularColImage_prefixLE_of_prefixLE
              S₁ S₂ T₁ T₂ hsize Q Qᶜ hinjQ hinjQc hQgood
            simpa [B, E, g] using h'
          have hstrict : A ≺ₚ S₁ ∨ B ≺ₚ T₁ := by
            rcases left_bad_row_or_col_of_not_minorLE
              S₁ S₂ T₁ T₂ hsize hnot with hrow | hcol
            · left
              have hne : P ≠ duplicatedLeftSet S₁ S₂ := by
                intro heq
                apply hrow
                simpa [heq] using hPgood
              have hs := duplicatedImage_prefixLT S₁ S₂ P hinjP ⟨hPle, hne⟩
              change duplicatedImage S₁ S₂ P ≺ₚ S₁
              exact hs
            · right
              have hne : Q ≠ rectangularColLeftSet S₁ S₂ T₁ T₂ hsize := by
                intro heq
                apply hcol
                simpa [heq] using hQgood
              have hs := rectangularColImage_prefixLT
                S₁ S₂ T₁ T₂ hsize Q hinjQ ⟨hQle, hne⟩
              simpa [B, g] using hs
          have htotal : A.card + C.card = S₁.card + S₂.card := by
            calc
              A.card + C.card = P.card + Pᶜ.card := by
                rw [Finset.card_image_iff.mpr hinjP,
                  Finset.card_image_iff.mpr hinjPc]
              _ = Fintype.card (Fin (S₁.card + S₂.card)) :=
                Finset.card_add_card_compl P
              _ = S₁.card + S₂.card := Fintype.card_fin _
          have hminor₁ : finsetMinor Y P Q =
              finsetMinorPoly (D := D) A B := by
            simpa [Y, A, B, f, g] using
              (finsetMinor_rectangularDuplicatedMatrix
                (D := D) S₁ S₂ T₁ T₂ hsize P Q hinjP hinjQ)
          have hminor₂ : finsetMinor Y Pᶜ Qᶜ =
              finsetMinorPoly (D := D) C E := by
            simpa [Y, C, E, f, g] using
              (finsetMinor_rectangularDuplicatedMatrix
                (D := D) S₁ S₂ T₁ T₂ hsize Pᶜ Qᶜ hinjPc hinjQc)
          apply AddSubgroup.subset_closure
          exact ⟨A, C, B, E, hAB, hCE, hAle, hBle, hAC, hBE,
            hstrict, htotal, congrArg₂ (· * ·) hminor₁ hminor₂⟩
        · have hz : finsetMinor Y Pᶜ Qᶜ = 0 := by
            change finsetMinor (Matrix.of (fun i j ↦
              (MvPolynomial.X (f i, g j) : GenericPoly D n m))) Pᶜ Qᶜ = 0
            exact finsetMinor_pulled_eq_zero_of_not_injOn_right
              (fun i j ↦ (MvPolynomial.X (i, j) : GenericPoly D n m))
              f g Pᶜ Qᶜ hinjQc
          rw [hz, mul_zero]
          exact H.zero_mem
      · have hz : finsetMinor Y Pᶜ Qᶜ = 0 := by
          change finsetMinor (Matrix.of (fun i j ↦
            (MvPolynomial.X (f i, g j) : GenericPoly D n m))) Pᶜ Qᶜ = 0
          exact finsetMinor_pulled_eq_zero_of_not_injOn_left
            (fun i j ↦ (MvPolynomial.X (i, j) : GenericPoly D n m))
            f g Pᶜ Qᶜ hinjPc
        rw [hz, mul_zero]
        exact H.zero_mem
    · have hz : finsetMinor Y P Q = 0 := by
        change finsetMinor (Matrix.of (fun i j ↦
          (MvPolynomial.X (f i, g j) : GenericPoly D n m))) P Q = 0
        exact finsetMinor_pulled_eq_zero_of_not_injOn_right
          (fun i j ↦ (MvPolynomial.X (i, j) : GenericPoly D n m))
          f g P Q hinjQ
      rw [hz, zero_mul]
      exact H.zero_mem
  · have hz : finsetMinor Y P Q = 0 := by
      change finsetMinor (Matrix.of (fun i j ↦
        (MvPolynomial.X (f i, g j) : GenericPoly D n m))) P Q = 0
      exact finsetMinor_pulled_eq_zero_of_not_injOn_left
        (fun i j ↦ (MvPolynomial.X (i, j) : GenericPoly D n m))
        f g P Q hinjP
    rw [hz, zero_mul]
    exact H.zero_mem

/-- Two-minor straightening for a rectangular generic matrix.  Membership in
the additive closure is precisely a finite integral linear combination of the
products described by `twoMinorStraighteningGenerators`. -/
theorem two_minor_straightening {D : Type*} [CommRing D] {n m : ℕ}
    (S₁ S₂ : Finset (Fin n)) (T₁ T₂ : Finset (Fin m))
    (hcard₁ : S₁.card = T₁.card) (hcard₂ : S₂.card = T₂.card)
    (hnot : ¬(S₁ ≼ₚ S₂ ∧ T₁ ≼ₚ T₂)) :
    finsetMinorPoly (D := D) S₁ T₁ * finsetMinorPoly (D := D) S₂ T₂ ∈
      twoMinorStraighteningSpan (D := D) S₁ S₂ T₁ T₂ := by
  classical
  have hsize : T₁.card + T₂.card = S₁.card + S₂.card := by omega
  let Y := rectangularDuplicatedMatrix (D := D) S₁ S₂ T₁ T₂ hsize
  let A := duplicatedLeftSet S₁ S₂
  let B := rectangularColLeftSet S₁ S₂ T₁ T₂ hsize
  let H := twoMinorStraighteningSpan (D := D) S₁ S₂ T₁ T₂
  have hAB : A.card = B.card := by
    dsimp [A, B, rectangularColLeftSet]
    rw [card_castFinset, card_duplicatedLeftSet, card_duplicatedLeftSet, hcard₁]
  have hlapSquare : laplacePermSum Y A B ∈ laplaceStraighteningSpan Y A B :=
    laplacePermSum_mem_straighteningSpan Y A B
  have hsquare_le : laplaceStraighteningSpan Y A B ≤ H := by
    apply (AddSubgroup.closure_le _).mpr
    intro x hx
    rcases hx with ⟨P, Q, hPA, hQB, hPgood, hQgood, rfl⟩
    by_cases hPQ : P.card = Q.card
    · exact laplacePermSum_mem_twoMinorStraighteningSpan
        S₁ S₂ T₁ T₂ hsize hnot P Q hPQ hPA hQB hPgood hQgood
    · rw [laplacePermSum_eq_zero_of_card_ne Y P Q hPQ]
      exact H.zero_mem
  have hlap : laplacePermSum Y A B ∈ H := hsquare_le hlapSquare
  obtain ⟨u, hu⟩ :=
    exists_intUnit_mul_laplacePermSum_eq_mul_finsetMinor Y A B hAB
  have hleft : finsetMinor Y A B = finsetMinorPoly (D := D) S₁ T₁ := by
    simpa [Y, A, B] using
      (finsetMinor_rectangularDuplicatedMatrix_left
        (D := D) S₁ S₂ T₁ T₂ hsize)
  have hright : finsetMinor Y Aᶜ Bᶜ = finsetMinorPoly (D := D) S₂ T₂ := by
    rw [show Aᶜ = duplicatedRightSet S₁ S₂ by
        simpa [A] using duplicatedLeftSet_compl S₁ S₂,
      show Bᶜ = castFinset hsize (duplicatedRightSet T₁ T₂) by
        simp [B]]
    simpa [Y] using
      (finsetMinor_rectangularDuplicatedMatrix_right
        (D := D) S₁ S₂ T₁ T₂ hsize)
  have hulap : (u : GenericPoly D n m) * laplacePermSum Y A B ∈ H :=
    (intUnit_cast_mul_mem_iff H u (laplacePermSum Y A B)).mpr hlap
  rw [hu, hleft, hright] at hulap
  exact hulap

end GenericMaximalMinor

end

end Cslib
