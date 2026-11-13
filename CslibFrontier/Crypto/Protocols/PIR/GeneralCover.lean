/-
Copyright (c) 2026 Samuel Schlesinger, Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.PIR.CoveringCode
public import CslibFrontier.Crypto.Protocols.PIR.Indexed
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Ring

/-!
# Exact unbalanced covering-code schemes (Theorem 1) and general radius-`r` covers

`PIR.CoveringCode` formalizes [Chor, Goldreich, Kushilevitz and Sudan, Section
3.3][ChorGoldreichKushilevitzSudan1998] in the uniform `PIR.Scheme` model, where every server sends
answers of the same fixed bit length. Because non-perfect covering codes assign unequal numbers of
non-codewords to different servers, `PIR.CoveringCode` proves Theorem 1's exact bit count
`k + (2 ^ d + (d - 1) · k) · ℓ` only for *balanced* covers (`k · (m + 1) = 2 ^ d`, which forces `k`
to divide `2 ^ d`, excluding for example Figure 1's optimal `d = 5, k = 7` and `d = 6, k = 12`
codes) and covers only radius `1`.

This module completes both directions of Section 3.3 (pp. 8–10):

* **Multi-coordinate subcube emulation (`PIR.diffCoords`, `PIR.emulateCubeQuery`,
  `PIR.query_cube_eq_emulateCubeQuery`).** Generalizing `PIR.query_update_cube` from Hamming
  distance `1` to arbitrary distance: for any two words `σ, w : D → Bool`, the subcube query of `w`
  in `PIR.cube D ι` agrees with `q σ` outside `diffCoords σ w = {l | σ l ≠ w l}` and adds `e_{i l}`
  at each `l ∈ diffCoords σ w`. Thus knowing `q σ` and the `|diffCoords σ w|` coordinates `(i l)`
  determines `q w`.
* **Full CGKS Theorem 1 via per-server answer widths (`PIR.ExactRadiusOneCover`,
  `PIR.hasIndexedScheme_of_hammingDist`).** Following Footnote 1 of Section 3.3 (p. 9), an
  `ExactRadiusOneCover S D` partitions `D → Bool` across `k = |S|` distinct codewords `code s` so
  every word `w` is assigned to a server within Hamming distance `1` and each codeword is assigned
  to itself (`ExactRadiusOneCover.ofHammingDist` builds one canonically from any injective
  radius-`1` covering code). Server `s` replies with `1` bit for `code s` and `ℓ` bits for each of
  its `m_s = |AssignedNeighbour K s|` assigned non-codewords (`PIR.IndexedScheme`). Because
  `k + ∑ s, m_s = 2 ^ d` (`card_add_sum_card_assignedNeighbour`), total communication is
  `k + (2 ^ d + (d - 1) · k) · ℓ` for *every* injective `k`-word radius-`1` covering code on `d ≥ 1`
  coordinates (`hasIndexedScheme_of_hammingDist`). Instantiated on the explicit `7`-word radius-`1`
  covering code of `Fin 5 → Bool` (`sevenWordCode`, `K(5, 1) = 7` in Figure 1, p. 10), this yields a
  `7`-server scheme communicating `60 · ℓ + 7` bits for `n ≤ ℓ ^ 5`
  (`hasIndexedScheme_seven_of_le_pow_five`), whereas `7 ∤ 32` rules out any balanced uniform cover.
* **General radius-`r` and radius-`2` covering-code schemes (`PIR.radiusCoverScheme`,
  `PIR.hasScheme_of_hammingDist_le`, `PIR.hasScheme_of_hammingDist_two`,
  `PIR.hasScheme_of_hammingDist_two_sq`).** For any radius-`r` covering code of `D → Bool`, each
  server tabulates emulated subcube parities over `RadiusBallQuery D r ι` (`∑ j ≤ r, C(d, j) · ℓ^j`
  bits), giving a uniform `PIR.Scheme` communicating
  `k · (d · ℓ + ∑ j ≤ r, C(d, j) · ℓ ^ j)` bits. At `r = 2` this gives
  `k · (2 d ℓ + C(d, 2) ℓ² + 1) = k · d · ℓ + k · C(d, 2) · ℓ² + k · (d · ℓ + 1)` bits
  (`hasScheme_of_hammingDist_two`, matching Section 3.3's displayed leading expression
  `k · d · ℓ + k · C(d, 2) · ℓ²` on p. 10 plus the `k · (d · ℓ + 1)` lower-order radius-`0` and
  radius-`1` answer bits), and for `d ≥ 2`, `ℓ ≥ 1` the coarser polynomial upper bound
  `k · d · ℓ + k · d² · ℓ²` (`hasScheme_of_hammingDist_two_sq`). Instantiated on `{00000, 11111}`
  (`repetitionFive`), this gives a `2`-server radius-`2` scheme on `n ≤ ℓ ^ 5` with
  `20 ℓ² + 20 ℓ + 2` bits (`hasScheme_two_radius_two_of_le_pow_five`).

## Main definitions

* `Cslib.Crypto.Protocols.PIR.diffCoords`, `Cslib.Crypto.Protocols.PIR.emulateCubeQuery`:
  disagreement coordinates and multi-coordinate query emulation on `PIR.cube`.
* `Cslib.Crypto.Protocols.PIR.ExactRadiusOneCover`: exact partitions of `D → Bool` into subsets of
  radius-`1` balls around `k` distinct codewords (CGKS Section 3.3, Footnote 1).
* `Cslib.Crypto.Protocols.PIR.ExactRadiusOneCover.indexedScheme`: per-server covering-code scheme.
* `Cslib.Crypto.Protocols.PIR.sevenWordCode`: explicit `7`-word radius-`1` covering code of
  `Fin 5 → Bool` (CGKS Figure 1).
* `Cslib.Crypto.Protocols.PIR.RadiusBallQuery`, `Cslib.Crypto.Protocols.PIR.radiusCoverScheme`:
  general radius-`r` covering-code PIR scheme.
* `Cslib.Crypto.Protocols.PIR.repetitionFive`: the `2`-word radius-`2` covering code
  `{00000, 11111}` of `Fin 5 → Bool`.

## Main results

* `Cslib.Crypto.Protocols.PIR.query_cube_eq_emulateCubeQuery`: multi-coordinate emulation identity.
* `Cslib.Crypto.Protocols.PIR.ExactRadiusOneCover.indexedCommunication_indexedScheme_eq`,
  `Cslib.Crypto.Protocols.PIR.hasIndexedScheme_of_hammingDist`: full CGKS Theorem 1 for arbitrary
  injective radius-`1` covering codes.
* `Cslib.Crypto.Protocols.PIR.hasIndexedScheme_seven_of_le_pow_five`: `7`-server `60 ℓ + 7`-bit PIR
  for `n ≤ ℓ ^ 5` (CGKS Figure 1, `d = 5`).
* `Cslib.Crypto.Protocols.PIR.hasScheme_of_hammingDist_le`,
  `Cslib.Crypto.Protocols.PIR.hasScheme_of_hammingDist_two`,
  `Cslib.Crypto.Protocols.PIR.hasScheme_of_hammingDist_two_sq`: radius-`r` and radius-`2`
  covering-code PIR bounds.
* `Cslib.Crypto.Protocols.PIR.hasScheme_two_radius_two_of_le_pow_five`: `2`-server radius-`2` PIR
  on `Fin 5 → Bool`.

## References

* [B. Chor, O. Goldreich, E. Kushilevitz, M. Sudan, *Private information
  retrieval*][ChorGoldreichKushilevitzSudan1998], Section 3.3 (Theorem 1, Footnote 1, Figure 1, and
  pp. 8–10); numbering of the authors' journal version of April 21, 1998
-/

public section

namespace Cslib.Crypto.Protocols.PIR

open Probability

/-! ### Multi-coordinate subcube emulation -/

section EmulateCube

variable {D ι : Type} [Fintype D] [Fintype ι] [DecidableEq ι]

/-- Coordinates at which `σ` and `w` disagree; its cardinality is definitionally `hammingDist σ w`.
-/
@[expose] def diffCoords (σ w : D → Bool) : Finset D :=
  Finset.univ.filter fun l => σ l ≠ w l

@[simp] theorem card_diffCoords (σ w : D → Bool) :
    (diffCoords σ w).card = hammingDist σ w :=
  rfl

@[simp] theorem mem_diffCoords {σ w : D → Bool} {l : D} :
    l ∈ diffCoords σ w ↔ σ l ≠ w l :=
  Finset.mem_filter_univ l

/-- Emulate a subcube query at disagreement set `T : Finset D` by flipping coordinate `δ ⟨l, hl⟩` in
`a l` for every `l ∈ T` and leaving `a l` unchanged outside `T`. -/
@[expose] def emulateCubeQuery [DecidableEq D] (a : D → ι → Bool) (T : Finset D) (δ : T → ι)
    (l : D) : ι → Bool :=
  if h : l ∈ T then a l + Pi.single (δ ⟨l, h⟩) true else a l

omit [Fintype D] [Fintype ι] in
@[simp] theorem emulateCubeQuery_of_mem [DecidableEq D] (a : D → ι → Bool) (T : Finset D)
    (δ : T → ι) {l : D} (hl : l ∈ T) :
    emulateCubeQuery a T δ l = a l + Pi.single (δ ⟨l, hl⟩) true :=
  dite_eq_left hl

omit [Fintype D] [Fintype ι] in
@[simp] theorem emulateCubeQuery_of_notMem [DecidableEq D] (a : D → ι → Bool) (T : Finset D)
    (δ : T → ι) {l : D} (hl : l ∉ T) :
    emulateCubeQuery a T δ l = a l :=
  dite_eq_right hl

/-- Multi-coordinate generalization of `PIR.query_update_cube`: for any draw `(r, q)` of
`PIR.cube D ι` on target `i` and any two words `σ, w : D → Bool`, the query `q w` is obtained from
`q σ` by flipping `(i l)` on `diffCoords σ w`. -/
theorem query_cube_eq_emulateCubeQuery [DecidableEq D] {i : D → ι} {r : Unit}
    {q : (D → Bool) → D → ι → Bool}
    (hrq : (r, q) ∈ (ProbComp.eval ((cube D ι).query i)).support) (σ w : D → Bool) :
    q w = emulateCubeQuery (q σ) (diffCoords σ w) (fun l => i l.1) := by
  suffices ∀ (T : Finset D) (σ : D → Bool), diffCoords σ w = T →
      q w = emulateCubeQuery (q σ) T (fun l => i l.1) from
    this (diffCoords σ w) σ rfl
  intro T
  induction T using Finset.induction with
  | empty =>
    intro σ hT
    have hσw : σ = w := by
      funext l
      by_contra hne
      have hmem : l ∈ diffCoords σ w := mem_diffCoords.mpr hne
      rw [hT] at hmem
      exact Finset.notMem_empty l hmem
    subst hσw
    funext l
    simp [emulateCubeQuery]
  | @insert l₀ T' hl₀ ih =>
    intro σ hT
    have hl₀_mem : l₀ ∈ diffCoords σ w := hT ▸ Finset.mem_insert_self l₀ T'
    have hne₀ : σ l₀ ≠ w l₀ := mem_diffCoords.mp hl₀_mem
    let σ' : D → Bool := Function.update σ l₀ (!σ l₀)
    have hσ' : diffCoords σ' w = T' := by
      ext l
      rw [mem_diffCoords]
      by_cases hll₀ : l = l₀
      · subst hll₀
        simp [σ', Bool.eq_not_of_ne hne₀.symm, hl₀]
      · have hiff : l ∈ diffCoords σ w ↔ l ∈ insert l₀ T' := by rw [hT]
        rw [mem_diffCoords, Finset.mem_insert] at hiff
        simp [σ', hll₀, hiff]
    rw [ih σ' hσ', show σ' = Function.update σ l₀ (!σ l₀) from rfl, query_update_cube hrq σ l₀]
    funext l
    by_cases hll₀ : l = l₀
    · subst hll₀
      simp [emulateCubeQuery, hl₀]
    · simp [emulateCubeQuery, hll₀]

end EmulateCube

/-- Embed `Fin n` into the `|D|`-dimensional cube `D → Fin ℓ` whenever `n ≤ ℓ ^ |D|`. -/
private noncomputable def cubeIndexEmb (D : Type) [Fintype D] {n ℓ : ℕ}
    (h : n ≤ ℓ ^ Fintype.card D) : Fin n ↪ (D → Fin ℓ) :=
  letI := Classical.decEq D
  have hcard : Fintype.card (D → Fin ℓ) = ℓ ^ Fintype.card D := by
    rw [Fintype.card_fun, Fintype.card_fin]
  (Fin.castLEEmb (h.trans_eq hcard.symm)).trans (Fintype.equivFin (D → Fin ℓ)).symm.toEmbedding

/-! ### Exact partitions of radius-`1` covers and full CGKS Theorem 1 -/

/-- An exact partition of the cube `D → Bool` into subsets of radius-`1` balls around `|S|` distinct
codewords [CGKS, Section 3.3, Footnote 1, p. 9][ChorGoldreichKushilevitzSudan1998]: each word `w` is
assigned to a server `assign w` within Hamming distance `1`, and each codeword `code s` is assigned
to `s` itself (which forces `code` to be injective). -/
structure ExactRadiusOneCover (S D : Type) [Fintype D] where
  /-- The distinct codeword held by each server. -/
  code : S → D → Bool
  /-- Assignment of every cube word to the server whose ball covers it. -/
  assign : (D → Bool) → S
  /-- Each codeword is covered by its own server (`c_s ∈ S(c_s)`). -/
  assign_code : ∀ s, assign (code s) = s
  /-- Every word lies within Hamming distance `1` of its assigned server's codeword. -/
  hammingDist_assign_le_one : ∀ w, hammingDist (code (assign w)) w ≤ 1

namespace ExactRadiusOneCover

variable {S D : Type} [Fintype D]

/-- Different servers in an `ExactRadiusOneCover` hold distinct codewords. -/
theorem code_injective (K : ExactRadiusOneCover S D) : Function.Injective K.code :=
  Function.LeftInverse.injective K.assign_code

open scoped Classical in
private noncomputable def chooseAssign (code : S → D → Bool)
    (hc : ∀ w, ∃ s, hammingDist (code s) w ≤ 1) (w : D → Bool) : S :=
  if h : ∃ s, code s = w then Classical.choose h else Classical.choose (hc w)

/-- Build an `ExactRadiusOneCover` canonically from any injective radius-`1` covering code
`code : S → D → Bool`: each codeword `code s` is assigned to `s`, and each non-codeword is assigned
to a covering codeword within Hamming distance `1`. -/
noncomputable def ofHammingDist (code : S → D → Bool) (hinj : Function.Injective code)
    (hc : ∀ w, ∃ s, hammingDist (code s) w ≤ 1) : ExactRadiusOneCover S D where
  code := code
  assign := chooseAssign code hc
  assign_code s := by
    have hex : ∃ s', code s' = code s := ⟨s, rfl⟩
    rw [chooseAssign, dite_eq_left hex]
    exact hinj (Classical.choose_spec hex)
  hammingDist_assign_le_one w := by
    by_cases hex : ∃ s, code s = w
    · rw [chooseAssign, dite_eq_left hex, Classical.choose_spec hex, hammingDist_self]
      exact Nat.zero_le 1
    · rw [chooseAssign, dite_eq_right hex]
      exact Classical.choose_spec (hc w)

@[simp] theorem code_ofHammingDist (code : S → D → Bool) (hinj : Function.Injective code)
    (hc : ∀ w, ∃ s, hammingDist (code s) w ≤ 1) :
    (ofHammingDist code hinj hc).code = code := by
  rfl

section Partition

variable (K : ExactRadiusOneCover S D)

/-- Non-codeword cube vertices assigned to server `s` in the exact cover `K`. -/
abbrev AssignedNeighbour (s : S) : Type :=
  {w : D → Bool // K.assign w = s ∧ w ≠ K.code s}

/-- The `|S|` codewords together with all `AssignedNeighbour K s` partition `D → Bool`. -/
noncomputable def partitionEquiv : S ⊕ (Σ s, K.AssignedNeighbour s) ≃ (D → Bool) where
  toFun
    | Sum.inl s => K.code s
    | Sum.inr ⟨_, w⟩ => w.1
  invFun w :=
    if h : w = K.code (K.assign w) then Sum.inl (K.assign w)
    else Sum.inr ⟨K.assign w, ⟨w, rfl, h⟩⟩
  left_inv
    | Sum.inl s => by
      dsimp only
      split_ifs with h
      · exact congrArg Sum.inl (K.assign_code s)
      · exact False.elim (h (congrArg K.code (K.assign_code s)).symm)
    | Sum.inr ⟨s, ⟨w, hassign, hne⟩⟩ => by
      subst hassign
      dsimp only
      split_ifs with h
      · exact False.elim (hne h)
      · rfl
  right_inv w := by
    dsimp only
    split_ifs with h
    · exact h.symm
    · rfl

theorem card_add_sum_card_assignedNeighbour (K : ExactRadiusOneCover S D) [DecidableEq D]
    [Fintype S] [DecidableEq S] :
    Fintype.card S + ∑ s : S, Fintype.card (K.AssignedNeighbour s) = 2 ^ Fintype.card D := by
  classical
  have h := Fintype.card_congr K.partitionEquiv
  rw [Fintype.card_sum, Fintype.card_sigma, Fintype.card_fun, Fintype.card_bool] at h
  convert h using 2

theorem card_le_two_pow (K : ExactRadiusOneCover S D) [Fintype S] :
    Fintype.card S ≤ 2 ^ Fintype.card D := by
  classical
  have h := K.card_add_sum_card_assignedNeighbour
  omega

theorem sum_card_assignedNeighbour (K : ExactRadiusOneCover S D) [DecidableEq D] [Fintype S]
    [DecidableEq S] :
    ∑ s : S, Fintype.card (K.AssignedNeighbour s) = 2 ^ Fintype.card D - Fintype.card S := by
  have h := K.card_add_sum_card_assignedNeighbour
  omega

end Partition

section Scheme

variable (K : ExactRadiusOneCover S D) [DecidableEq D]
  (ι : Type) [Fintype ι] [DecidableEq ι]

/-- **Per-server covering-code PIR scheme**
[CGKS, Section 3.3, Theorem 1 and Footnote 1][ChorGoldreichKushilevitzSudan1998]: server `s`
receives the subcube query for `K.code s`, replies with `1` bit for `K.code s` itself and `|ι|` bits
for each assigned non-codeword `w : K.AssignedNeighbour s`, and the user sums the `2 ^ |D|`
recovered subcube parities. -/
noncomputable def indexedScheme :
    IndexedScheme (D → ι) S Unit (fun _ => D → ι → Bool)
      (fun s => Bool × (K.AssignedNeighbour s → ι → Bool)) where
  query i := (fun rq => (rq.1, fun s => rq.2 (K.code s))) <$> (cube D ι).query i
  answer s x a :=
    ((cube D ι).answer (K.code s) x a, fun w k =>
      (cube D ι).answer (K.code s) x (emulateCubeQuery a (diffCoords (K.code s) w.1) fun _ => k))
  reconstruct i _ a :=
    ∑ w : D → Bool,
      let s := K.assign w
      if h : w = K.code s then (a s).1
      else (a s).2 ⟨w, rfl, h⟩ (i (Classical.choose (Function.ne_iff.mp (Ne.symm h))))

variable {K ι}

theorem eval_serverQuery_indexedScheme (s : S) (i : D → ι) :
    ProbComp.eval ((K.indexedScheme ι).serverQuery s i) =
      ProbComp.eval ((cube D ι).serverQuery (K.code s) i) := by
  rw [IndexedScheme.eval_serverQuery, Scheme.eval_serverQuery, indexedScheme, ProbComp.eval_map,
    PMF.map_comp]
  rfl

/-- `K.indexedScheme ι` is perfectly private, inheriting uniform subcube queries from `PIR.cube`. -/
theorem isPrivate_indexedScheme : (K.indexedScheme ι).IsPrivate :=
  (K.indexedScheme ι).isPrivate_iff.mpr fun s i i' => by
    rw [eval_serverQuery_indexedScheme, eval_serverQuery_indexedScheme,
      isPrivate_cube.eval_serverQuery_eq (K.code s) i i']

/-- `K.indexedScheme ι` is perfectly correct: every word `w : D → Bool` is either `K.code s` or
differs from `K.code s` at a single coordinate `l₀`, so `(a s)` supplies its exact `PIR.cube`
answer. -/
theorem isCorrect_indexedScheme : (K.indexedScheme ι).IsCorrect := by
  rw [IndexedScheme.isCorrect_iff]
  intro x i r q hrq
  simp only [indexedScheme, ProbComp.eval_map, PMF.mem_support_map_iff, Prod.mk.injEq] at hrq
  obtain ⟨⟨r₀, q₀⟩, h₀, -, rfl⟩ := hrq
  refine Eq.trans ?_ (isCorrect_cube.reconstruct_eq x i h₀)
  rw [reconstruct_cube]
  refine Finset.sum_congr rfl fun w _ => ?_
  dsimp only [indexedScheme]
  split_ifs with hw
  · rw [← hw]
  · set s := K.assign w
    set l₀ := Classical.choose (Function.ne_iff.mp (Ne.symm hw))
    have hl₀ : K.code s l₀ ≠ w l₀ := Classical.choose_spec (Function.ne_iff.mp (Ne.symm hw))
    have hfun : (fun _ : diffCoords (K.code s) w => i l₀) =
        fun l : diffCoords (K.code s) w => i l.1 := by
      funext l
      have hcard : (diffCoords (K.code s) w).card ≤ 1 := K.hammingDist_assign_le_one w
      have heq : l₀ = l.1 := Finset.card_le_one.mp hcard l₀ (mem_diffCoords.mpr hl₀) l.1 l.2
      exact congrArg i heq
    rw [hfun, ← query_cube_eq_emulateCubeQuery h₀ (K.code s) w, answer_cube, answer_cube]

/-- Raw exact communication count of `K.indexedScheme ι` (valid even when `D` is empty): `|S|`
queries of `|D| · |ι|` bits, `|S|` codeword bits, and `(2 ^ |D| - |S|) · |ι|` non-codeword bits. -/
theorem indexedCommunication_indexedScheme (K : ExactRadiusOneCover S D) (ι : Type) [Fintype ι]
    [DecidableEq ι] [Fintype S] [DecidableEq S] :
    indexedCommunication S (fun _ => D → ι → Bool)
      (fun s => Bool × (K.AssignedNeighbour s → ι → Bool)) =
      Fintype.card S * Fintype.card D * Fintype.card ι + Fintype.card S +
        (2 ^ Fintype.card D - Fintype.card S) * Fintype.card ι := by
  have hQ : Fintype.card (D → ι → Bool) = 2 ^ (Fintype.card D * Fintype.card ι) := by
    simp only [Fintype.card_fun, Fintype.card_bool, ← pow_mul, Nat.mul_comm (Fintype.card ι)]
  rw [indexedCommunication_of_card_answer S (fun _ => D → ι → Bool)
      (fun s => Bool × (K.AssignedNeighbour s → ι → Bool))
      (aBits := fun s => 1 + Fintype.card (K.AssignedNeighbour s) * Fintype.card ι) (fun s => by
        simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fun, ← pow_mul, pow_add,
          pow_one, Nat.mul_comm (Fintype.card ι)])]
  simp only [hQ, Nat.clog_pow 2 _ (by norm_num)]
  calc ∑ s : S, (Fintype.card D * Fintype.card ι +
        (1 + Fintype.card (K.AssignedNeighbour s) * Fintype.card ι))
      = ∑ _s : S, (Fintype.card D * Fintype.card ι + 1) +
          (∑ s : S, Fintype.card (K.AssignedNeighbour s)) * Fintype.card ι := by
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun s _ => by ring
    _ = Fintype.card S * (Fintype.card D * Fintype.card ι + 1) +
          (2 ^ Fintype.card D - Fintype.card S) * Fintype.card ι := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, K.sum_card_assignedNeighbour]
    _ = Fintype.card S * Fintype.card D * Fintype.card ι + Fintype.card S +
          (2 ^ Fintype.card D - Fintype.card S) * Fintype.card ι := by ring

/-- **Theorem 1's exact communication count for arbitrary radius-`1` covers**
[CGKS, Section 3.3, Theorem 1, p. 9][ChorGoldreichKushilevitzSudan1998]: on any nonempty coordinate
set (`0 < |D|`), `K.indexedScheme ι` communicates `k + (2 ^ d + (d - 1) · k) · ℓ` bits, with no
balancedness assumption on `K`. -/
theorem indexedCommunication_indexedScheme_eq (K : ExactRadiusOneCover S D) (ι : Type) [Fintype ι]
    [DecidableEq ι] [Fintype S] [DecidableEq S] (hD : 0 < Fintype.card D) :
    indexedCommunication S (fun _ => D → ι → Bool)
      (fun s => Bool × (K.AssignedNeighbour s → ι → Bool)) =
      Fintype.card S +
        (2 ^ Fintype.card D + (Fintype.card D - 1) * Fintype.card S) * Fintype.card ι := by
  rw [K.indexedCommunication_indexedScheme ι]
  have hle : Fintype.card S ≤ 2 ^ Fintype.card D := K.card_le_two_pow
  set d := Fintype.card D - 1
  have hd : Fintype.card D = d + 1 := (Nat.sub_add_cancel hD).symm
  have hsub : 2 ^ Fintype.card D = Fintype.card S + (2 ^ Fintype.card D - Fintype.card S) :=
    (Nat.add_sub_of_le hle).symm
  calc Fintype.card S * Fintype.card D * Fintype.card ι + Fintype.card S +
        (2 ^ Fintype.card D - Fintype.card S) * Fintype.card ι
      = Fintype.card S * (d + 1) * Fintype.card ι + Fintype.card S +
          (2 ^ Fintype.card D - Fintype.card S) * Fintype.card ι := by rw [hd]
    _ = Fintype.card S + (Fintype.card S + (2 ^ Fintype.card D - Fintype.card S) +
          d * Fintype.card S) * Fintype.card ι := by ring
    _ = Fintype.card S + (2 ^ Fintype.card D + d * Fintype.card S) * Fintype.card ι := by
        rw [← hsub]

omit [DecidableEq D] in
/-- Any `ExactRadiusOneCover` on `d ≥ 1` coordinates yields a `k`-server `IndexedScheme` for
`n ≤ ℓ ^ d` communicating `k + (2 ^ d + (d - 1) · k) · ℓ` bits. -/
theorem hasIndexedScheme (K : ExactRadiusOneCover S D) [Fintype S] (hD : 0 < Fintype.card D)
    {n ℓ : ℕ} (h : n ≤ ℓ ^ Fintype.card D) :
    HasIndexedScheme (Fin n) (Fintype.card S)
      (Fintype.card S + (2 ^ Fintype.card D + (Fintype.card D - 1) * Fintype.card S) * ℓ) := by
  classical
  have hP := (K.isCorrect_indexedScheme (ι := Fin ℓ)).comap (cubeIndexEmb D h) false
    |>.hasIndexedScheme ((K.isPrivate_indexedScheme (ι := Fin ℓ)).comap (cubeIndexEmb D h) false)
  rwa [K.indexedCommunication_indexedScheme_eq (Fin ℓ) hD, Fintype.card_fin] at hP

end Scheme

end ExactRadiusOneCover

/-- **CGKS Section 3.3, Theorem 1 (general unbalanced form)**
[CGKS, p. 9][ChorGoldreichKushilevitzSudan1998]: if `D → Bool` (`0 < |D|`) admits an injective
`k`-word radius-`1` covering code `c : S → D → Bool`, then every `n ≤ ℓ ^ |D|` has a perfectly
correct and perfectly private `k`-server `IndexedScheme` communicating
`k + (2 ^ d + (d - 1) · k) · ℓ` bits. -/
theorem hasIndexedScheme_of_hammingDist {S D : Type} [Fintype S] [Fintype D]
    (hD : 0 < Fintype.card D) {c : S → D → Bool} (hinj : Function.Injective c)
    (hc : ∀ w, ∃ s, hammingDist (c s) w ≤ 1) {n ℓ : ℕ} (h : n ≤ ℓ ^ Fintype.card D) :
    HasIndexedScheme (Fin n) (Fintype.card S)
      (Fintype.card S + (2 ^ Fintype.card D + (Fintype.card D - 1) * Fintype.card S) * ℓ) :=
  (ExactRadiusOneCover.ofHammingDist c hinj hc).hasIndexedScheme hD h

/-! ### Explicit `7`-word unbalanced radius-`1` covering code of `Fin 5 → Bool` (CGKS Figure 1) -/

/-- Explicit `7`-word radius-`1` covering code of `{0, 1}^5` attaining optimal size `K(5, 1) = 7`
listed in [CGKS, Figure 1, p. 10][ChorGoldreichKushilevitzSudan1998]. Because `7 ∤ 2 ^ 5`, no
balanced `PIR.RadiusOneCover` exists for `(d, k) = (5, 7)`. -/
@[expose] def sevenWordCode : Fin 7 → Fin 5 → Bool
  | 0 => ![false, false, false, false, false]
  | 1 => ![false, false, false, false, true]
  | 2 => ![false, false, false, true, false]
  | 3 => ![false, true, true, true, true]
  | 4 => ![true, false, true, true, true]
  | 5 => ![true, true, false, true, true]
  | 6 => ![true, true, true, false, false]

theorem sevenWordCode_injective : Function.Injective sevenWordCode := by
  decide

theorem sevenWordCode_covers :
    ∀ w : Fin 5 → Bool, ∃ s : Fin 7, hammingDist (sevenWordCode s) w ≤ 1 := by
  decide

/-- **Seven servers with `60 · ℓ + 7` bits (`d = 5` row of CGKS Figure 1, p. 10)**
[CGKS, Section 3.3][ChorGoldreichKushilevitzSudan1998]: every `n ≤ ℓ ^ 5` has a perfectly correct
and perfectly private `7`-server `IndexedScheme` communicating `60 · ℓ + 7` bits (saving `10 · ℓ`
bits over the uniform `70 · ℓ + 7` bound of `PIR.RadiusOneCover.hasScheme_of_hammingDist`). -/
theorem hasIndexedScheme_seven_of_le_pow_five {n ℓ : ℕ} (h : n ≤ ℓ ^ 5) :
    HasIndexedScheme (Fin n) 7 (60 * ℓ + 7) := by
  have hP := hasIndexedScheme_of_hammingDist (S := Fin 7) (D := Fin 5)
    (by simp) sevenWordCode_injective sevenWordCode_covers (n := n) (ℓ := ℓ)
    (by simpa using h)
  simp only [Fintype.card_fin] at hP
  exact hP.mono (by omega)

/-! ### General radius-`r` and radius-`2` covering-code schemes -/

section RadiusCover

variable {S D : Type} [Fintype D] [DecidableEq D]

/-- Index of emulated subcube answers within a Hamming ball of radius `r`: a disagreement subset
`coords ⊆ D` of size at most `r` together with candidate coordinates `offsets : coords → ι`. -/
structure RadiusBallQuery (D : Type) (r : ℕ) (ι : Type) where
  /-- Subset of coordinates where the emulated cube vertex disagrees with the server's codeword. -/
  coords : Finset D
  /-- The disagreement set has size at most `r`. -/
  card_coords_le : coords.card ≤ r
  /-- Candidate target coordinate along each flipped dimension. -/
  offsets : coords → ι

/-- Equivalence between `RadiusBallQuery D r ι` and the corresponding dependent pair. -/
@[expose] def RadiusBallQuery.sigmaEquiv (D : Type) (r : ℕ) (ι : Type) :
    RadiusBallQuery D r ι ≃ Σ T : {T : Finset D // T.card ≤ r}, (T.1 → ι) where
  toFun u := ⟨⟨u.coords, u.card_coords_le⟩, u.offsets⟩
  invFun := fun ⟨⟨T, hT⟩, δ⟩ => ⟨T, hT, δ⟩
  left_inv := fun ⟨_, _, _⟩ => rfl
  right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl

instance instDecidableEqRadiusBallQuery (D : Type) [DecidableEq D] (r : ℕ) (ι : Type)
    [DecidableEq ι] : DecidableEq (RadiusBallQuery D r ι) :=
  (RadiusBallQuery.sigmaEquiv D r ι).decidableEq

instance instFintypeRadiusBallQuery (D : Type) [Fintype D] [DecidableEq D] (r : ℕ)
    (ι : Type) [Fintype ι] : Fintype (RadiusBallQuery D r ι) :=
  Fintype.ofEquiv _ (RadiusBallQuery.sigmaEquiv D r ι).symm

/-- A server emulating a Hamming ball of radius `r` tabulates `∑ j ≤ r, C(|D|, j) · |ι| ^ j`
single-bit subcube answers. -/
theorem card_radiusBallQuery (D : Type) [Fintype D] [DecidableEq D] (r : ℕ) (ι : Type)
    [Fintype ι] :
    Fintype.card (RadiusBallQuery D r ι) =
      ∑ j ∈ Finset.range (r + 1), (Fintype.card D).choose j * Fintype.card ι ^ j := by
  rw [Fintype.card_congr (RadiusBallQuery.sigmaEquiv D r ι), Fintype.card_sigma]
  simp only [Fintype.card_fun, Fintype.card_coe]
  let B : Finset (Finset D) := Finset.univ.filter fun T : Finset D => T.card ≤ r
  have hsum : (∑ T : {T : Finset D // T.card ≤ r}, Fintype.card ι ^ T.1.card) =
      ∑ T ∈ B, Fintype.card ι ^ T.card :=
    (Finset.sum_subtype B (fun _ => by simp [B]) (fun T : Finset D => Fintype.card ι ^ T.card)).symm
  rw [hsum, ← Finset.sum_fiberwise_of_maps_to
    (g := Finset.card) (t := Finset.range (r + 1))
    (fun T hT => Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hT).2))]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjle : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hpowerset : B.filter (fun T => T.card = j) = (Finset.univ : Finset D).powersetCard j := by
    ext T
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard,
      Finset.subset_univ]
    exact ⟨fun h => h.2, fun h => ⟨h.le.trans hjle, h⟩⟩
  rw [hpowerset, Finset.sum_congr rfl (fun T hT => by rw [(Finset.mem_powersetCard.mp hT).2]),
    Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, smul_eq_mul]

/-- **General radius-`r` covering-code PIR scheme**
[CGKS, Section 3.3, pp. 9–10][ChorGoldreichKushilevitzSudan1998]: given a radius-`r` covering code
`c : S → D → Bool`, server `s` receives the subcube query for `c s` and returns the emulated
subcube answer bit for every `u : RadiusBallQuery D r ι`. -/
noncomputable def radiusCoverScheme (r : ℕ) (c : S → D → Bool)
    (hc : ∀ w, ∃ s, hammingDist (c s) w ≤ r) (ι : Type) [Fintype ι] [DecidableEq ι] :
    Scheme (D → ι) S Unit (D → ι → Bool) (RadiusBallQuery D r ι → Bool) where
  query i := (fun rq => (rq.1, fun s => rq.2 (c s))) <$> (cube D ι).query i
  answer s x a u := (cube D ι).answer (c s) x (emulateCubeQuery a u.coords u.offsets)
  reconstruct i _ a :=
    ∑ w : D → Bool,
      let s := Classical.choose (hc w)
      a s ⟨diffCoords (c s) w, Classical.choose_spec (hc w), fun l => i l.1⟩

theorem eval_serverQuery_radiusCoverScheme (r : ℕ) (c : S → D → Bool)
    (hc : ∀ w, ∃ s, hammingDist (c s) w ≤ r) (ι : Type) [Fintype ι] [DecidableEq ι]
    (s : S) (i : D → ι) :
    ProbComp.eval ((radiusCoverScheme r c hc ι).serverQuery s i) =
      ProbComp.eval ((cube D ι).serverQuery (c s) i) := by
  rw [Scheme.eval_serverQuery, Scheme.eval_serverQuery, radiusCoverScheme, ProbComp.eval_map,
    PMF.map_comp]
  rfl

theorem isPrivate_radiusCoverScheme (r : ℕ) (c : S → D → Bool)
    (hc : ∀ w, ∃ s, hammingDist (c s) w ≤ r) (ι : Type) [Fintype ι] [DecidableEq ι] :
    (radiusCoverScheme r c hc ι).IsPrivate :=
  (radiusCoverScheme r c hc ι).isPrivate_iff.mpr fun s i i' => by
    rw [eval_serverQuery_radiusCoverScheme, eval_serverQuery_radiusCoverScheme,
      isPrivate_cube.eval_serverQuery_eq (c s) i i']

theorem isCorrect_radiusCoverScheme (r : ℕ) (c : S → D → Bool)
    (hc : ∀ w, ∃ s, hammingDist (c s) w ≤ r) (ι : Type) [Fintype ι] [DecidableEq ι] :
    (radiusCoverScheme r c hc ι).IsCorrect := by
  rw [Scheme.isCorrect_iff]
  intro x i r_u q hrq
  simp only [radiusCoverScheme, ProbComp.eval_map, PMF.mem_support_map_iff, Prod.mk.injEq] at hrq
  obtain ⟨⟨r₀, q₀⟩, h₀, -, rfl⟩ := hrq
  refine Eq.trans ?_ (isCorrect_cube.reconstruct_eq x i h₀)
  rw [reconstruct_cube]
  refine Finset.sum_congr rfl fun w _ => ?_
  dsimp only [radiusCoverScheme]
  set s := Classical.choose (hc w)
  rw [← query_cube_eq_emulateCubeQuery h₀ (c s) w, answer_cube, answer_cube]

theorem communication_radiusCoverScheme [Fintype S] (r : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] :
    communication S (D → ι → Bool) (RadiusBallQuery D r ι → Bool) =
      Fintype.card S * (Fintype.card D * Fintype.card ι +
        ∑ j ∈ Finset.range (r + 1), (Fintype.card D).choose j * Fintype.card ι ^ j) := by
  rw [communication_of_card_answer S (D → ι → Bool) (RadiusBallQuery D r ι → Bool)
    (ℓ := ∑ j ∈ Finset.range (r + 1), (Fintype.card D).choose j * Fintype.card ι ^ j)
    (by rw [Fintype.card_fun, Fintype.card_bool, card_radiusBallQuery])]
  simp only [Fintype.card_fun, Fintype.card_bool, ← pow_mul, Nat.clog_pow 2 _ (by norm_num),
    Nat.mul_comm (Fintype.card ι)]

omit [DecidableEq D] in
/-- **Schemes from radius-`r` covering codes**
[CGKS, Section 3.3, pp. 9–10][ChorGoldreichKushilevitzSudan1998]: if every word of `D → Bool` is
within Hamming distance `r` of one of `k = |S|` codewords, every `n ≤ ℓ ^ d` has a perfectly correct
and perfectly private `k`-server scheme communicating
`k · (d · ℓ + ∑ j ≤ r, C(d, j) · ℓ ^ j)` bits. -/
theorem hasScheme_of_hammingDist_le [Fintype S] {r : ℕ} {c : S → D → Bool}
    (hc : ∀ w, ∃ s, hammingDist (c s) w ≤ r) {n ℓ : ℕ} (h : n ≤ ℓ ^ Fintype.card D) :
    HasScheme (Fin n) (Fintype.card S)
      (Fintype.card S * (Fintype.card D * ℓ +
        ∑ j ∈ Finset.range (r + 1), (Fintype.card D).choose j * ℓ ^ j)) := by
  classical
  have hP := (isCorrect_radiusCoverScheme r c hc (Fin ℓ)).comap (cubeIndexEmb D h) false
    |>.hasScheme ((isPrivate_radiusCoverScheme r c hc (Fin ℓ)).comap (cubeIndexEmb D h) false)
  rwa [communication_radiusCoverScheme, Fintype.card_fin] at hP

omit [DecidableEq D] in
/-- **Radius-`2` covering-code PIR scheme (full-ball count)**
[CGKS, Section 3.3, pp. 9–10][ChorGoldreichKushilevitzSudan1998]: a `k`-word radius-`2` covering
code of `D → Bool` yields a `k`-server PIR scheme for `n ≤ ℓ ^ d` communicating
`k · (2 d ℓ + C(d, 2) · ℓ² + 1) = k · d · ℓ + k · C(d, 2) · ℓ² + k · (d · ℓ + 1)` bits (the
`k · d · ℓ + k · C(d, 2) · ℓ²` query and distance-`2` answer terms displayed on p. 10 of CGKS,
together with the `k · (d · ℓ + 1)` distance-`0` and distance-`1` answer bits). -/
theorem hasScheme_of_hammingDist_two [Fintype S] {c : S → D → Bool}
    (hc : ∀ w, ∃ s, hammingDist (c s) w ≤ 2) {n ℓ : ℕ} (h : n ≤ ℓ ^ Fintype.card D) :
    HasScheme (Fin n) (Fintype.card S)
      (Fintype.card S * (2 * Fintype.card D * ℓ + (Fintype.card D).choose 2 * ℓ ^ 2 + 1)) := by
  refine (hasScheme_of_hammingDist_le hc h).mono (le_of_eq ?_)
  simp only [Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, Nat.choose_zero_right,
    Nat.choose_one_right, pow_zero, pow_one, mul_one]
  ring

omit [DecidableEq D] in
/-- **Coarser polynomial radius-`2` bound (`k · d · ℓ + k · d² · ℓ²`)**: when `2 ≤ |D|` and `1 ≤ ℓ`,
replacing `C(d, 2)` by `d²` absorbs the lower-order `k · (d · ℓ + 1)` distance-`0` and distance-`1`
answer bits in `hasScheme_of_hammingDist_two`, giving a `k`-server scheme for `n ≤ ℓ ^ d` within
`k · d · ℓ + k · d² · ℓ²` bits. -/
theorem hasScheme_of_hammingDist_two_sq [Fintype S] {c : S → D → Bool}
    (hc : ∀ w, ∃ s, hammingDist (c s) w ≤ 2) (hD : 2 ≤ Fintype.card D) {n ℓ : ℕ}
    (hℓ : 1 ≤ ℓ) (h : n ≤ ℓ ^ Fintype.card D) :
    HasScheme (Fin n) (Fintype.card S)
      (Fintype.card S * Fintype.card D * ℓ +
        Fintype.card S * Fintype.card D ^ 2 * ℓ ^ 2) := by
  refine (hasScheme_of_hammingDist_two hc h).mono ?_
  have hchoose : 2 * (Fintype.card D).choose 2 ≤ Fintype.card D * (Fintype.card D - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.mul_div_le _ 2
  obtain ⟨d', hd'⟩ := Nat.exists_eq_add_of_le hD
  obtain ⟨ℓ', hℓ'⟩ := Nat.exists_eq_add_of_le hℓ
  have hinner : Fintype.card D * ℓ + (Fintype.card D).choose 2 * ℓ ^ 2 + 1 ≤
      Fintype.card D ^ 2 * ℓ ^ 2 := by
    have hmul : 2 * (Fintype.card D * ℓ + (Fintype.card D).choose 2 * ℓ ^ 2 + 1) ≤
        2 * (Fintype.card D ^ 2 * ℓ ^ 2) := by
      calc 2 * (Fintype.card D * ℓ + (Fintype.card D).choose 2 * ℓ ^ 2 + 1)
          = 2 * Fintype.card D * ℓ + (2 * (Fintype.card D).choose 2) * ℓ ^ 2 + 2 := by ring
        _ ≤ 2 * Fintype.card D * ℓ + Fintype.card D * (Fintype.card D - 1) * ℓ ^ 2 + 2 := by
            gcongr
        _ ≤ 2 * (Fintype.card D ^ 2 * ℓ ^ 2) := by
            have hsub1 : 2 + d' - 1 = d' + 1 := by omega
            rw [hd', hℓ', hsub1]
            have hpoly : 2 * ((2 + d') ^ 2 * (1 + ℓ') ^ 2) =
                (2 * (2 + d') * (1 + ℓ') + (2 + d') * (d' + 1) * (1 + ℓ') ^ 2 + 2) +
                  (d' ^ 2 * (1 + ℓ') ^ 2 + d' * (5 * ℓ' ^ 2 + 8 * ℓ' + 3) +
                    6 * ℓ' ^ 2 + 8 * ℓ') := by ring
            omega
    omega
  calc Fintype.card S * (2 * Fintype.card D * ℓ + (Fintype.card D).choose 2 * ℓ ^ 2 + 1)
      = Fintype.card S * Fintype.card D * ℓ +
          Fintype.card S * (Fintype.card D * ℓ + (Fintype.card D).choose 2 * ℓ ^ 2 + 1) := by ring
    _ ≤ Fintype.card S * Fintype.card D * ℓ +
          Fintype.card S * (Fintype.card D ^ 2 * ℓ ^ 2) := by gcongr
    _ = Fintype.card S * Fintype.card D * ℓ +
          Fintype.card S * Fintype.card D ^ 2 * ℓ ^ 2 := by ring

end RadiusCover

/-- The `2`-word repetition code `{00000, 11111}` on `Fin 5 → Bool` has covering radius `2` (every
`5`-bit word has at most `2` zeros or at most `2` ones), but not covering radius `1`. -/
@[expose] def repetitionFive : Bool → Fin 5 → Bool :=
  fun b _ => b

theorem repetitionFive_covers_two :
    ∀ w : Fin 5 → Bool, ∃ b : Bool, hammingDist (repetitionFive b) w ≤ 2 := by
  decide

theorem not_repetitionFive_covers_one :
    ¬ ∀ w : Fin 5 → Bool, ∃ b : Bool, hammingDist (repetitionFive b) w ≤ 1 := by
  decide

/-- Two servers using the radius-`2` cover `{00000, 11111}` of `Fin 5 → Bool` achieve
`20 ℓ² + 20 ℓ + 2` bits for every `n ≤ ℓ ^ 5`. -/
theorem hasScheme_two_radius_two_of_le_pow_five {n ℓ : ℕ} (h : n ≤ ℓ ^ 5) :
    HasScheme (Fin n) 2 (20 * ℓ ^ 2 + 20 * ℓ + 2) := by
  have hP := hasScheme_of_hammingDist_two repetitionFive_covers_two (n := n) (ℓ := ℓ)
    (by simpa using h)
  simp only [Fintype.card_bool, Fintype.card_fin] at hP
  exact hP.mono (by
    have hc : (5 : ℕ).choose 2 = 10 := by decide
    rw [hc]
    omega)

end Cslib.Crypto.Protocols.PIR
