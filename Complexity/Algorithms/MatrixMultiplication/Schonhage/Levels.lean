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

* `existsUnique_leftStr`, `existsUnique_rightStr`, `existsUnique_outStr`: nonvacuous entry layouts.

## References

Adapted selectively from [AlmanWilliams2026, Section 2] and
[Anthropic's pinned formal source](https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Sec2).
Source pin: `16a5ce41304fcdaea4e0be7c132e1c361dc26da5`. These are finite mathematical
counts and identities; they give no native program or instruction-cost certificate.
Source-derived descriptions below are paraphrases.
-/

@[expose] public section

open Finset

namespace Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Section 2.2: We call the variables of the inner product, p, q, and z₀, inner. -/
def LeftVar.IsInner : LeftVar → Prop
  | .x _ => False
  | .p _ _ => True
/-- Section 2.2: the right variables `q` are inner, the `y` are outer. -/
def RightVar.IsInner : RightVar → Prop
  | .y _ => False
  | .q _ _ => True
instance LeftVar.instDecidablePredIsInner : DecidablePred LeftVar.IsInner
  | .x _ => isFalse fun h => h
  | .p _ _ => isTrue trivial
instance RightVar.instDecidablePredIsInner : DecidablePred RightVar.IsInner
  | .y _ => isFalse fun h => h
  | .q _ _ => isTrue trivial
/-- Section 2.3.3: The inner set of a left string is the set of levels at which it has a p (as
opposed to an x). -/
def innerSetL {L : ℕ} (u : LeftStr L) : Finset (Fin L) := univ.filter fun ℓ => (u ℓ).IsInner
/-- Section 2.3.3: the inner set of a right string is the set of levels at which it has a q (as
opposed to a y). -/
def innerSetR {L : ℕ} (v : RightStr L) : Finset (Fin L) := univ.filter fun ℓ => (v ℓ).IsInner
/-- Section 2.3.3: the inner set of an output string is the set of levels at which it has z₀ (as
opposed to a z_ij). -/
def innerSetO {L : ℕ} (w : OutStr L) : Finset (Fin L) := univ.filter fun ℓ => (w ℓ).IsInner

/-- Section 2.3.3: N₀ := 3^{L-m}.  Meant for `m ≤ L`; for `m > L` the subtraction of natural
numbers is cut off at 0 and the value is 1. -/
def N0 (L m : ℕ) : ℕ := 3 ^ (L - m)
/-- Section 2.3.3: D := 4^m. -/
def D (m : ℕ) : ℕ := 4 ^ m
/-- Section 2.3.3: K := binom(L, m), the number of subsets of `{1, …, L}` of size `m`. -/
def K (L m : ℕ) : ℕ := L.choose m

/-- The index `i` of an outer left variable `x_i` (the value at a `p` is never used). -/
def LeftVar.outerIndex : LeftVar → Fin 3
  | .x i => i
  | .p _ _ => 0
/-- The index pair `(i, j)` of an inner left variable `p_ij` (the value at an `x` is never used). -/
def LeftVar.innerIndex : LeftVar → Fin 2 × Fin 2
  | .x _ => (0, 0)
  | .p i j => (i, j)
/-- The index `j` of an outer right variable `y_j` (the value at a `q` is never used). -/
def RightVar.outerIndex : RightVar → Fin 3
  | .y j => j
  | .q _ _ => 0
/-- The index pair `(i, j)` of an inner right variable `q_ij` (the value at a `y` is never used). -/
def RightVar.innerIndex : RightVar → Fin 2 × Fin 2
  | .y _ => (0, 0)
  | .q i j => (i, j)
/-- The first index `i` of an outer output variable `z_ij` (the value at `z₀` is never used). -/
def OutVar.rowIndex : OutVar → Fin 3
  | .z i _ => i
  | .z0 => 0
/-- The second index `j` of an outer output variable `z_ij` (the value at `z₀` is never used). -/
def OutVar.colIndex : OutVar → Fin 3
  | .z _ j => j
  | .z0 => 0

/-- A string of `L - m` outer left variables `x_{i₁} ⋯ x_{i_{L-m}}`, written as the string of its
indices `i₁ ⋯ i_{L-m}`.  The same type is used for strings `y_{j₁} ⋯ y_{j_{L-m}}` of outer right
variables.  Section 2.3.3: these strings index the `N₀` rows of an `N₀ × D` matrix and the `N₀`
columns of a `D × N₀` matrix. -/
abbrev OuterStr (L m : ℕ) : Type := Fin (L - m) → Fin 3

/-- A string of `m` inner left variables `π = p_{i₁j₁} ⋯ p_{i_m j_m}`, written as the string of its
index pairs.  The same type is used for strings `π' = q_{i₁j₁} ⋯ q_{i_m j_m}` of inner right
variables, so that the paper's `π'`, with the same indices as `π`, is the same element of this
type as `π`. Section 2.3.3: these strings index the `D` columns of an `N₀ × D` matrix and the `D`
rows of a `D × N₀` matrix. With this convention the paper's (AB)[r, c] := ∑_π A[r, π] B[π', c] is
the usual matrix product. -/
abbrev InnerStr (m : ℕ) : Type := Fin m → Fin 2 × Fin 2

/-- Section 2.3.3: its outer part is the string of its variables at the other levels, for a left
string whose inner set has `m` elements. -/
def outerPartL {L m : ℕ} (u : LeftStr L) (h : (innerSetL u).card = m) : OuterStr L m :=
  fun k => (u (((innerSetL u)ᶜ.orderEmbOfFin (card_compl_of_card_eq (innerSetL u) h)) k)).outerIndex
/-- Section 2.3.3: The inner part of a string is the string of its variables at the levels of its
inner set, in the order of the levels, for a left string whose inner set has `m` elements. -/
def innerPartL {L m : ℕ} (u : LeftStr L) (h : (innerSetL u).card = m) : InnerStr m :=
  fun k => (u (Finset.orderEmbOfFin (innerSetL u) h k)).innerIndex
/-- The outer part of a right string whose inner set has `m` elements. -/
def outerPartR {L m : ℕ} (v : RightStr L) (h : (innerSetR v).card = m) : OuterStr L m :=
  fun k => (v (((innerSetR v)ᶜ.orderEmbOfFin (card_compl_of_card_eq (innerSetR v) h)) k)).outerIndex
/-- The inner part of a right string whose inner set has `m` elements. -/
def innerPartR {L m : ℕ} (v : RightStr L) (h : (innerSetR v).card = m) : InnerStr m :=
  fun k => (v (Finset.orderEmbOfFin (innerSetR v) h k)).innerIndex

/-- Section 2.3.3: if the variables of w at the levels outside Q are z_{i₁j₁}, …, z_{i_{L-m}
j_{L-m}}, in the order of the levels, then the row of w is the string x_{i₁} ⋯ x_{i_{L-m}}. -/
def rowO {L m : ℕ} (w : OutStr L) (h : (innerSetO w).card = m) : OuterStr L m :=
  fun k => (w (((innerSetO w)ᶜ.orderEmbOfFin (card_compl_of_card_eq (innerSetO w) h)) k)).rowIndex
/-- Section 2.3.3: and its column is the string y_{j₁} ⋯ y_{j_{L-m}}. -/
def colO {L m : ℕ} (w : OutStr L) (h : (innerSetO w).card = m) : OuterStr L m :=
  fun k => (w (((innerSetO w)ᶜ.orderEmbOfFin (card_compl_of_card_eq (innerSetO w) h)) k)).colIndex

/-- An `N₀ × D` matrix, its rows and columns indexed by strings as in Section 2.3.3. -/
abbrev LeftMat (L m : ℕ) : Type := Matrix (OuterStr L m) (InnerStr m) ℤ
/-- A `D × N₀` matrix, its rows and columns indexed by strings as in Section 2.3.3. -/
abbrev RightMat (L m : ℕ) : Type := Matrix (InnerStr m) (OuterStr L m) ℤ

/-- Section 2.3.3: a[u] := X_Q[u] […] for all the left strings u […] whose inner set Q has exactly
m elements, and a[u] := 0 […] at every other string, where X_Q[u] is the entry of `X_Q` at the
row and the column of u: the row is the outer part of `u` and the column is its inner part. The
family `X` gives a matrix `X Q` for every set `Q` of levels; only those with `|Q| = m` are used. -/
def arrayL {L : ℕ} (m : ℕ) (X : Finset (Fin L) → LeftMat L m) : LeftStr L → ℤ :=
  fun u =>
    if h : (innerSetL u).card = m then X (innerSetL u) (outerPartL u h) (innerPartL u h) else 0

/-- Section 2.3.3: b[v] := Y_Q[v] for the right strings `v` whose inner set `Q` has exactly `m`
elements, the row given by the inner part of v and the column by the outer part, and `b[v] := 0`
at every other string. -/
def arrayR {L : ℕ} (m : ℕ) (Y : Finset (Fin L) → RightMat L m) : RightStr L → ℤ :=
  fun v =>
    if h : (innerSetR v).card = m then Y (innerSetR v) (innerPartR v h) (outerPartR v h) else 0

/-! ### 2.3.4 Tiling the N × D × N product by products of shape N₀ × D × N₀: the number `M` -/

/-- Section 2.3.4: M := K N₀². -/
def M (L m : ℕ) : ℕ := K L m * N0 L m ^ 2


variable {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m)

/-! ### Left, right and output strings with a given inner set, outer part and inner part -/

/-- The left string with inner set `Q`, outer part `r` and inner part `π`. -/
def leftStrOf (r : OuterStr L m) (π : InnerStr m) : LeftStr L :=
  glue Q hQ (fun k => .p (π k).1 (π k).2) (fun k => .x (r k))

/-- The right string with inner set `Q`, inner part `π` and outer part `c`. -/
def rightStrOf (π : InnerStr m) (c : OuterStr L m) : RightStr L :=
  glue Q hQ (fun k => .q (π k).1 (π k).2) (fun k => .y (c k))

/-- The output string with inner set `Q`, row `r` and column `c` (Section 2.3.3: the output strings
with inner set Q index the entries of the product X_Q Y_Q): it has `z₀` at the levels of `Q`, and
at the `k`-th lowest level outside `Q` it has `z_{r_k c_k}`. -/
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
    (glue_outerLevel_of_eq Q hQ _ _ (innerSetL_leftStrOf Q hQ r π) h k)

/-- The inner part of `leftStrOf Q hQ r π` is `π`. -/
@[simp]
theorem innerPartL_leftStrOf (r : OuterStr L m) (π : InnerStr m)
    (h : (innerSetL (leftStrOf Q hQ r π)).card = m) : innerPartL (leftStrOf Q hQ r π) h = π :=
  funext fun k => congrArg LeftVar.innerIndex
    (glue_innerLevel_of_eq Q hQ _ _ (innerSetL_leftStrOf Q hQ r π) h k)

/-- The inner part of `rightStrOf Q hQ π c` is `π`. -/
@[simp]
theorem innerPartR_rightStrOf (π : InnerStr m) (c : OuterStr L m)
    (h : (innerSetR (rightStrOf Q hQ π c)).card = m) : innerPartR (rightStrOf Q hQ π c) h = π :=
  funext fun k => congrArg RightVar.innerIndex
    (glue_innerLevel_of_eq Q hQ _ _ (innerSetR_rightStrOf Q hQ π c) h k)

/-- The outer part of `rightStrOf Q hQ π c` is `c`. -/
@[simp]
theorem outerPartR_rightStrOf (π : InnerStr m) (c : OuterStr L m)
    (h : (innerSetR (rightStrOf Q hQ π c)).card = m) : outerPartR (rightStrOf Q hQ π c) h = c :=
  funext fun k => congrArg RightVar.outerIndex
    (glue_outerLevel_of_eq Q hQ _ _ (innerSetR_rightStrOf Q hQ π c) h k)

/-- The variable of `outStrOf Q hQ r c` at the `k`-th lowest level outside its inner set. -/
private theorem outStrOf_outerLevel (r c : OuterStr L m)
    (h : (innerSetO (outStrOf Q hQ r c)).card = m) (k : Fin (L - m)) :
    outStrOf Q hQ r c (((innerSetO (outStrOf Q hQ r c))ᶜ.orderEmbOfFin (card_compl_of_card_eq
      (innerSetO (outStrOf Q hQ r c)) h)) k) = .z (r k) (c k) := by
  rw [outerLevel_congr Q hQ (innerSetO_outStrOf Q hQ r c) h, outStrOf, glue_outerLevel]

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
  refine glue_index _ h LeftVar.IsInner (inner := fun π : Fin 2 × Fin 2 => .p π.1 π.2) ?_ ?_ rfl
  · rintro (i | ⟨i, j⟩) hs
    exacts [hs.elim, rfl]
  · rintro (i | ⟨i, j⟩) hs
    exacts [rfl, (hs trivial).elim]

/-- A right string with inner set `Q` is the string `rightStrOf` of its inner part and its outer
part. -/
theorem rightStr_eq_rightStrOf {v : RightStr L} (hv : innerSetR v = Q)
    (h : (innerSetR v).card = m) : v = rightStrOf Q hQ (innerPartR v h) (outerPartR v h) := by
  subst hv
  refine glue_index _ h RightVar.IsInner (inner := fun π : Fin 2 × Fin 2 => .q π.1 π.2) ?_ ?_ rfl
  · rintro (j | ⟨i, j⟩) ht
    exacts [ht.elim, rfl]
  · rintro (j | ⟨i, j⟩) ht
    exacts [rfl, (ht trivial).elim]

/-- An output string with inner set `Q` is the string `outStrOf` of its row and its column. -/
theorem outStr_eq_outStrOf {w : OutStr L} (hw : innerSetO w = Q) (h : (innerSetO w).card = m) :
    w = outStrOf Q hQ (rowO w h) (colO w h) := by
  subst hw
  refine glue_index _ h OutVar.IsInner (inner := fun _ : Unit => .z0)
    (outer := fun rc : Fin 3 × Fin 3 => .z rc.1 rc.2) (innerIndex := fun _ => ())
    (outerIndex := fun z => (z.rowIndex, z.colIndex)) ?_ ?_ rfl
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

/-- Section 2.3.3: A string is determined by its inner set, its outer part, and its inner part,
and the left strings with inner set Q index the entries of such a matrix: for each set `Q` of `m`
levels, each row `r` and each column `π` there is exactly one left string with inner set `Q`, outer
part `r` and inner part `π`. -/
theorem existsUnique_leftStr (r : OuterStr L m) (π : InnerStr m) :
    ∃! u : LeftStr L, innerSetL u = Q
      ∧ ∃ h : (innerSetL u).card = m, outerPartL u h = r ∧ innerPartL u h = π := by
  have hset := innerSetL_leftStrOf Q hQ r π
  refine ⟨leftStrOf Q hQ r π, ⟨hset, hset.symm ▸ hQ, outerPartL_leftStrOf Q hQ r π _,
    innerPartL_leftStrOf Q hQ r π _⟩, ?_⟩
  rintro u ⟨hu, h, rfl, rfl⟩
  exact leftStr_eq_leftStrOf hQ hu h

/-- Section 2.3.3: Similarly, the right strings v with inner set Q index the entries of a D × N₀
matrix. -/
theorem existsUnique_rightStr (π : InnerStr m) (c : OuterStr L m) :
    ∃! v : RightStr L, innerSetR v = Q
      ∧ ∃ h : (innerSetR v).card = m, innerPartR v h = π ∧ outerPartR v h = c := by
  have hset := innerSetR_rightStrOf Q hQ π c
  refine ⟨rightStrOf Q hQ π c, ⟨hset, hset.symm ▸ hQ,
    innerPartR_rightStrOf Q hQ π c _, outerPartR_rightStrOf Q hQ π c _⟩, ?_⟩
  rintro v ⟨hv, h, rfl, rfl⟩
  exact rightStr_eq_rightStrOf hQ hv h

/-- Section 2.3.3: Finally, the output strings with inner set Q index the entries of the product
X_Q Y_Q. -/
theorem existsUnique_outStr (r c : OuterStr L m) :
    ∃! w : OutStr L, innerSetO w = Q
      ∧ ∃ h : (innerSetO w).card = m, rowO w h = r ∧ colO w h = c := by
  have hset := innerSetO_outStrOf Q hQ r c
  refine ⟨outStrOf Q hQ r c, ⟨hset, hset.symm ▸ hQ, rowO_outStrOf Q hQ r c _,
    colO_outStrOf Q hQ r c _⟩, ?_⟩
  rintro w ⟨hw, h, rfl, rfl⟩
  exact outStr_eq_outStrOf hQ hw h

end Cslib.Algorithms.MatrixMultiplication.Schonhage
