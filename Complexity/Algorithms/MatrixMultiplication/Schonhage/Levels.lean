/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.MatrixMultiplication.Schonhage.Full
public import Complexity.Foundations.Data.Finset.OrderGlue

/-!
# Matrix entries indexed by tensor strings

## Main definitions

* `arrayL`, `arrayR`: batch arrays with exactly `m` inner levels.
* `leftStrOf`, `rightStrOf`, `outStrOf`: entry strings.

## Main results

* `existsUnique_leftStr`, `existsUnique_rightStr`, `existsUnique_outStr`: unique entry strings.

## References

Adapted selectively from [AlmanWilliams2026, Section 2] and
[Anthropic's pinned formal source](https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Sec2).
Source pin: `16a5ce41304fcdaea4e0be7c132e1c361dc26da5`. These are finite mathematical
counts and identities; they give no native program or instruction-cost certificate.
-/

@[expose] public section

open Finset

namespace Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Recognize the constructors `.p i j` as inner left variables. -/
def LeftVar.IsInner : LeftVar → Prop
  | .x _ => False
  | .p _ _ => True
/-- Recognize the constructors `.q i j` as inner right variables. -/
def RightVar.IsInner : RightVar → Prop
  | .y _ => False
  | .q _ _ => True
instance LeftVar.instDecidablePredIsInner : DecidablePred LeftVar.IsInner
  | .x _ => isFalse fun h => h
  | .p _ _ => isTrue trivial
instance RightVar.instDecidablePredIsInner : DecidablePred RightVar.IsInner
  | .y _ => isFalse fun h => h
  | .q _ _ => isTrue trivial
/-- Positions of the inner left variables in `u`. -/
def innerSetL {L : ℕ} (u : LeftStr L) : Finset (Fin L) := univ.filter fun ℓ => (u ℓ).IsInner
/-- Positions of the inner right variables in `v`. -/
def innerSetR {L : ℕ} (v : RightStr L) : Finset (Fin L) := univ.filter fun ℓ => (v ℓ).IsInner
/-- Positions at which the output string is `.z0`. -/
def innerSetO {L : ℕ} (w : OutStr L) : Finset (Fin L) := univ.filter fun ℓ => (w ℓ).IsInner

/-- The outer dimension `3 ^ (L - m)`, with natural-number subtraction. In particular, this
definition gives `1` if `m > L`. -/
def N0 (L m : ℕ) : ℕ := 3 ^ (L - m)
/-- The thin dimension `4 ^ m`. -/
def D (m : ℕ) : ℕ := 4 ^ m
/-- The binomial coefficient `L.choose m`, counting size-`m` subsets of `Fin L`. -/
def K (L m : ℕ) : ℕ := L.choose m

/-- Extract `i` from `.x i`; return `0` on inner left variables. -/
def LeftVar.outerIndex : LeftVar → Fin 3
  | .x i => i
  | .p _ _ => 0
/-- Extract `(i, j)` from `.p i j`; return `(0, 0)` on outer left variables. -/
def LeftVar.innerIndex : LeftVar → Fin 2 × Fin 2
  | .x _ => (0, 0)
  | .p i j => (i, j)
/-- Extract `j` from `.y j`; return `0` on inner right variables. -/
def RightVar.outerIndex : RightVar → Fin 3
  | .y j => j
  | .q _ _ => 0
/-- Extract `(i, j)` from `.q i j`; return `(0, 0)` on outer right variables. -/
def RightVar.innerIndex : RightVar → Fin 2 × Fin 2
  | .y _ => (0, 0)
  | .q i j => (i, j)
/-- Extract the first index from `.z i j`; return `0` on `.z0`. -/
def OutVar.rowIndex : OutVar → Fin 3
  | .z i _ => i
  | .z0 => 0
/-- Extract the second index from `.z i j`; return `0` on `.z0`. -/
def OutVar.colIndex : OutVar → Fin 3
  | .z _ j => j
  | .z0 => 0

/-- Functions from `Fin (L - m)` to `Fin 3`, used as outer row and column indices. Each value
specifies the index of an outer left or right variable. -/
abbrev OuterStr (L m : ℕ) : Type := Fin (L - m) → Fin 3

/-- Functions from `Fin m` to pairs of `Fin 2` indices, used for the common inner dimension of
the two matrices. Left and right inner variables with the same pair of indices share one
element of this type, so contraction over `InnerStr m` is ordinary matrix multiplication. -/
abbrev InnerStr (m : ℕ) : Type := Fin m → Fin 2 × Fin 2

/-- Extract the outer left indices in increasing order of their positions, assuming `u` has
exactly `m` inner positions. -/
def outerPartL {L m : ℕ} (u : LeftStr L) (h : (innerSetL u).card = m) : OuterStr L m :=
  fun k => (u (((innerSetL u)ᶜ.orderEmbOfFin (card_compl_of_card_eq (innerSetL u) h)) k)).outerIndex
/-- Extract the inner left index pairs in increasing order of their positions, assuming `u`
has exactly `m` inner positions. -/
def innerPartL {L m : ℕ} (u : LeftStr L) (h : (innerSetL u).card = m) : InnerStr m :=
  fun k => (u (Finset.orderEmbOfFin (innerSetL u) h k)).innerIndex
/-- The outer part of a right string whose inner set has `m` elements. -/
def outerPartR {L m : ℕ} (v : RightStr L) (h : (innerSetR v).card = m) : OuterStr L m :=
  fun k => (v (((innerSetR v)ᶜ.orderEmbOfFin (card_compl_of_card_eq (innerSetR v) h)) k)).outerIndex
/-- The inner part of a right string whose inner set has `m` elements. -/
def innerPartR {L m : ℕ} (v : RightStr L) (h : (innerSetR v).card = m) : InnerStr m :=
  fun k => (v (Finset.orderEmbOfFin (innerSetR v) h k)).innerIndex

/-- Read the first indices of the outer output variables in increasing position order,
assuming `w` has exactly `m` inner positions. -/
def rowO {L m : ℕ} (w : OutStr L) (h : (innerSetO w).card = m) : OuterStr L m :=
  fun k => (w (((innerSetO w)ᶜ.orderEmbOfFin (card_compl_of_card_eq (innerSetO w) h)) k)).rowIndex
/-- Read the second indices of the outer output variables in increasing position order,
assuming `w` has exactly `m` inner positions. -/
def colO {L m : ℕ} (w : OutStr L) (h : (innerSetO w).card = m) : OuterStr L m :=
  fun k => (w (((innerSetO w)ᶜ.orderEmbOfFin (card_compl_of_card_eq (innerSetO w) h)) k)).colIndex

/-- Integer matrices with outer row indices and inner column indices. -/
abbrev LeftMat (L m : ℕ) : Type := Matrix (OuterStr L m) (InnerStr m) ℤ
/-- Integer matrices with inner row indices and outer column indices. -/
abbrev RightMat (L m : ℕ) : Type := Matrix (InnerStr m) (OuterStr L m) ℤ

/-- Encode a family of integer matrices as a left array. A string with exactly `m` inner
positions selects `X` at that set of positions, with row `outerPartL` and column
`innerPartL`; every other string has value zero. -/
def arrayL {L : ℕ} (m : ℕ) (X : Finset (Fin L) → LeftMat L m) : LeftStr L → ℤ :=
  fun u =>
    if h : (innerSetL u).card = m then X (innerSetL u) (outerPartL u h) (innerPartL u h) else 0

/-- Encode a family of integer matrices as a right array. A string with exactly `m` inner
positions selects `Y` at that set of positions, with row `innerPartR` and column
`outerPartR`; every other string has value zero. -/
def arrayR {L : ℕ} (m : ℕ) (Y : Finset (Fin L) → RightMat L m) : RightStr L → ℤ :=
  fun v =>
    if h : (innerSetR v).card = m then Y (innerSetR v) (innerPartR v h) (outerPartR v h) else 0

/-! ### The block-count parameter `M` -/

/-- The quantity `K L m * N0 L m ^ 2` used in the leaf and tile bounds. -/
def M (L m : ℕ) : ℕ := K L m * N0 L m ^ 2


variable {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m)

/-! ### Left, right and output strings with a given inner set, outer part and inner part -/

/-- The left string with inner set `Q`, outer part `r` and inner part `π`. -/
def leftStrOf (r : OuterStr L m) (π : InnerStr m) : LeftStr L :=
  glue Q hQ (fun k => .p (π k).1 (π k).2) (fun k => .x (r k))

/-- The right string with inner set `Q`, inner part `π` and outer part `c`. -/
def rightStrOf (π : InnerStr m) (c : OuterStr L m) : RightStr L :=
  glue Q hQ (fun k => .q (π k).1 (π k).2) (fun k => .y (c k))

/-- Construct an output string with `.z0` at `Q` and `.z (r k) (c k)` at the `k`-th position
of its complement. Both sets of positions use increasing order. -/
def outStrOf (r c : OuterStr L m) : OutStr L :=
  glue Q hQ (fun _ => .z0) (fun k => .z (r k) (c k))

/-- The inner set of `leftStrOf Q hQ r π` is `Q`. -/
@[simp]
theorem innerSetL_leftStrOf (r : OuterStr L m) (π : InnerStr m) :
    innerSetL (leftStrOf Q hQ r π) = Q :=
  filter_glue Q hQ LeftVar.IsInner (fun _ => trivial) fun _ => id

/-- The inner set of `rightStrOf Q hQ π c` is `Q`. -/
@[simp]
theorem innerSetR_rightStrOf (π : InnerStr m) (c : OuterStr L m) :
    innerSetR (rightStrOf Q hQ π c) = Q :=
  filter_glue Q hQ RightVar.IsInner (fun _ => trivial) fun _ => id

/-- The inner set of `outStrOf Q hQ r c` is `Q`. -/
@[simp]
theorem innerSetO_outStrOf (r c : OuterStr L m) : innerSetO (outStrOf Q hQ r c) = Q :=
  filter_glue Q hQ OutVar.IsInner (fun _ => trivial) fun _ => id

/-- The outer part of `leftStrOf Q hQ r π` is `r`. -/
@[simp]
theorem outerPartL_leftStrOf (r : OuterStr L m) (π : InnerStr m)
    (h : (innerSetL (leftStrOf Q hQ r π)).card = m) : outerPartL (leftStrOf Q hQ r π) h = r :=
  funext fun k => congrArg LeftVar.outerIndex
    (glue_orderEmbOfFin_compl_of_eq Q hQ _ _ (innerSetL_leftStrOf Q hQ r π) h k)

/-- The inner part of `leftStrOf Q hQ r π` is `π`. -/
@[simp]
theorem innerPartL_leftStrOf (r : OuterStr L m) (π : InnerStr m)
    (h : (innerSetL (leftStrOf Q hQ r π)).card = m) : innerPartL (leftStrOf Q hQ r π) h = π :=
  funext fun k => congrArg LeftVar.innerIndex
    (glue_orderEmbOfFin_of_eq Q hQ _ _ (innerSetL_leftStrOf Q hQ r π) h k)

/-- The inner part of `rightStrOf Q hQ π c` is `π`. -/
@[simp]
theorem innerPartR_rightStrOf (π : InnerStr m) (c : OuterStr L m)
    (h : (innerSetR (rightStrOf Q hQ π c)).card = m) : innerPartR (rightStrOf Q hQ π c) h = π :=
  funext fun k => congrArg RightVar.innerIndex
    (glue_orderEmbOfFin_of_eq Q hQ _ _ (innerSetR_rightStrOf Q hQ π c) h k)

/-- The outer part of `rightStrOf Q hQ π c` is `c`. -/
@[simp]
theorem outerPartR_rightStrOf (π : InnerStr m) (c : OuterStr L m)
    (h : (innerSetR (rightStrOf Q hQ π c)).card = m) : outerPartR (rightStrOf Q hQ π c) h = c :=
  funext fun k => congrArg RightVar.outerIndex
    (glue_orderEmbOfFin_compl_of_eq Q hQ _ _ (innerSetR_rightStrOf Q hQ π c) h k)

/-- The variable of `outStrOf Q hQ r c` at the `k`-th lowest level outside its inner set. -/
private theorem outStrOf_outerLevel (r c : OuterStr L m)
    (h : (innerSetO (outStrOf Q hQ r c)).card = m) (k : Fin (L - m)) :
    outStrOf Q hQ r c (((innerSetO (outStrOf Q hQ r c))ᶜ.orderEmbOfFin (card_compl_of_card_eq
      (innerSetO (outStrOf Q hQ r c)) h)) k) = .z (r k) (c k) := by
  simp only [innerSetO_outStrOf] at h ⊢
  exact glue_orderEmbOfFin_compl Q hQ _ _ k

/-- The row of `outStrOf Q hQ r c` is `r`. -/
@[simp]
theorem rowO_outStrOf (r c : OuterStr L m) (h : (innerSetO (outStrOf Q hQ r c)).card = m) :
    rowO (outStrOf Q hQ r c) h = r :=
  funext fun k => congrArg OutVar.rowIndex (outStrOf_outerLevel Q hQ r c h k)

/-- The column of `outStrOf Q hQ r c` is `c`. -/
@[simp]
theorem colO_outStrOf (r c : OuterStr L m) (h : (innerSetO (outStrOf Q hQ r c)).card = m) :
    colO (outStrOf Q hQ r c) h = c :=
  funext fun k => congrArg OutVar.colIndex (outStrOf_outerLevel Q hQ r c h k)

variable {Q}

/-- A left string with inner set `Q` is the string `leftStrOf` of its outer part and its inner
part. -/
theorem leftStr_eq_leftStrOf {u : LeftStr L} (hu : innerSetL u = Q) (h : (innerSetL u).card = m) :
    u = leftStrOf Q hQ (outerPartL u h) (innerPartL u h) := by
  subst hu
  refine eq_glue_of_reconstruct _ h LeftVar.IsInner
    (fromSubset := fun π : Fin 2 × Fin 2 => .p π.1 π.2) ?_ ?_ rfl
  · rintro (i | ⟨i, j⟩) hs
    exacts [hs.elim, rfl]
  · rintro (i | ⟨i, j⟩) hs
    exacts [rfl, (hs trivial).elim]

/-- A right string with inner set `Q` is the string `rightStrOf` of its inner part and its outer
part. -/
theorem rightStr_eq_rightStrOf {v : RightStr L} (hv : innerSetR v = Q)
    (h : (innerSetR v).card = m) : v = rightStrOf Q hQ (innerPartR v h) (outerPartR v h) := by
  subst hv
  refine eq_glue_of_reconstruct _ h RightVar.IsInner
    (fromSubset := fun π : Fin 2 × Fin 2 => .q π.1 π.2) ?_ ?_ rfl
  · rintro (j | ⟨i, j⟩) ht
    exacts [ht.elim, rfl]
  · rintro (j | ⟨i, j⟩) ht
    exacts [rfl, (ht trivial).elim]

/-- An output string with inner set `Q` is the string `outStrOf` of its row and its column. -/
theorem outStr_eq_outStrOf {w : OutStr L} (hw : innerSetO w = Q) (h : (innerSetO w).card = m) :
    w = outStrOf Q hQ (rowO w h) (colO w h) := by
  subst hw
  refine eq_glue_of_reconstruct _ h OutVar.IsInner (fromSubset := fun _ : Unit => .z0)
    (fromCompl := fun rc : Fin 3 × Fin 3 => .z rc.1 rc.2) (toSubset := fun _ => ())
    (toCompl := fun z => (z.rowIndex, z.colIndex)) ?_ ?_ rfl
  · rintro (⟨i, j⟩ | _) hz
    exacts [hz.elim, rfl]
  · rintro (⟨i, j⟩ | _) hz
    exacts [rfl, (hz trivial).elim]

variable {hQ}

/-- Left strings with the same inner set and different outer or inner parts are different. -/
theorem leftStrOf_inj {r r' : OuterStr L m} {π π' : InnerStr m} :
    leftStrOf Q hQ r π = leftStrOf Q hQ r' π' ↔ r = r' ∧ π = π' := by
  refine ⟨fun h => ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  obtain ⟨hp, hx⟩ := (glue_inj Q hQ).mp h
  exact ⟨funext fun k => LeftVar.x.inj (congrFun hx k),
    funext fun k => Prod.ext (LeftVar.p.inj (congrFun hp k)).1 (LeftVar.p.inj (congrFun hp k)).2⟩

/-- Output strings with different inner sets, rows or columns are different. -/
theorem outStrOf_inj {Q' : Finset (Fin L)} {hQ' : Q'.card = m} {r c r' c' : OuterStr L m} :
    outStrOf Q hQ r c = outStrOf Q' hQ' r' c' ↔ Q = Q' ∧ r = r' ∧ c = c' := by
  refine ⟨fun h => ?_, by rintro ⟨rfl, rfl, rfl⟩; rfl⟩
  obtain rfl : Q = Q' := by rw [← innerSetO_outStrOf Q hQ r c, h, innerSetO_outStrOf]
  have hz := fun k => OutVar.z.inj (congrFun ((glue_inj Q hQ).mp h).2 k)
  exact ⟨rfl, funext fun k => (hz k).1, funext fun k => (hz k).2⟩

variable (Q) (hQ)
include hQ

/-- For a set `Q` of cardinality `m`, an outer index `r` and an inner index `π` determine a
unique left string with those extracted parts and inner set `Q`. -/
theorem existsUnique_leftStr (r : OuterStr L m) (π : InnerStr m) :
    ∃! u : LeftStr L, innerSetL u = Q
      ∧ ∃ h : (innerSetL u).card = m, outerPartL u h = r ∧ innerPartL u h = π := by
  have hset := innerSetL_leftStrOf Q hQ r π
  refine ⟨leftStrOf Q hQ r π, ⟨hset, hset.symm ▸ hQ, outerPartL_leftStrOf Q hQ r π _,
    innerPartL_leftStrOf Q hQ r π _⟩, ?_⟩
  rintro u ⟨hu, h, rfl, rfl⟩
  exact leftStr_eq_leftStrOf hQ hu h

/-- For a set `Q` of cardinality `m`, an inner index `π` and an outer index `c` determine a
unique right string with those extracted parts and inner set `Q`. -/
theorem existsUnique_rightStr (π : InnerStr m) (c : OuterStr L m) :
    ∃! v : RightStr L, innerSetR v = Q
      ∧ ∃ h : (innerSetR v).card = m, innerPartR v h = π ∧ outerPartR v h = c := by
  have hset := innerSetR_rightStrOf Q hQ π c
  refine ⟨rightStrOf Q hQ π c, ⟨hset, hset.symm ▸ hQ,
    innerPartR_rightStrOf Q hQ π c _, outerPartR_rightStrOf Q hQ π c _⟩, ?_⟩
  rintro v ⟨hv, h, rfl, rfl⟩
  exact rightStr_eq_rightStrOf hQ hv h

/-- For a set `Q` of cardinality `m`, a row `r` and a column `c` determine a unique output
string with those extracted indices and inner set `Q`. -/
theorem existsUnique_outStr (r c : OuterStr L m) :
    ∃! w : OutStr L, innerSetO w = Q
      ∧ ∃ h : (innerSetO w).card = m, rowO w h = r ∧ colO w h = c := by
  have hset := innerSetO_outStrOf Q hQ r c
  refine ⟨outStrOf Q hQ r c, ⟨hset, hset.symm ▸ hQ, rowO_outStrOf Q hQ r c _,
    colO_outStrOf Q hQ r c _⟩, ?_⟩
  rintro w ⟨hw, h, rfl, rfl⟩
  exact outStr_eq_outStrOf hQ hw h

end Cslib.Algorithms.MatrixMultiplication.Schonhage
