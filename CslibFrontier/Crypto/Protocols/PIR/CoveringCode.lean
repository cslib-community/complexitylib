/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.PIR.Cube
public import Mathlib.InformationTheory.Hamming
import CslibFrontier.Foundations.Data.Hamming

/-!
# Covering-code schemes for private information retrieval

The subcube scheme `PIR.cube` uses `2 ^ d` servers, one for each `σ : D → Bool`. The covering-code
method of [Chor, Goldreich, Kushilevitz and Sudan, Section 3.3][ChorGoldreichKushilevitzSudan1998]
keeps only the servers of a radius-`1` covering code of `D → Bool` and lets each of them *emulate*
its neighbours.

The server `σ` knows its query `(T l ⊕ σ l e_{i l})_l`. The query of the neighbour that differs from
it at `l` differs from it only in the `l`-th set, by flipping one unknown position `i l`. So `σ` can
send the answers for all `ℓ` choices of that position, and the user picks the right one. The kept
servers receive the queries of `PIR.cube`, so privacy is inherited
(`PIR.RadiusOneCover.isPrivate_scheme`). The user recovers the `2 ^ d` answers of `PIR.cube`, so
correctness is too (`PIR.RadiusOneCover.isCorrect_scheme`).

A `PIR.RadiusOneCover S D M` fixes this data, following the footnote to Section 3.3 (an exact
cover of the cube by subsets of the radius-`1` balls):
* the codewords `code s` of the servers `s : S`;
* for each server, the directions `dir s r` (for `r : M`) of the neighbours it emulates;
* a map `cover` assigning to each word `w : D → Bool` a server, and possibly one of its directions,
  that produce `w`.

The volume bound `2 ^ d ≤ |S| (|M| + 1)` follows (`PIR.RadiusOneCover.two_pow_card_le`).

**Communication.** The library measures communication with fixed-length queries and answers
(`PIR.communication`), so every server answers with `1 + |M| ℓ` bits, as if it emulated `|M|`
neighbours. The scheme communicates `k ((d + m) ℓ + 1)` bits, where `k = |S|` and `m = |M|`
(`PIR.RadiusOneCover.communication_scheme`). The source counts `k + (2 ^ d - k) ℓ` answer bits
instead, emulating each non-codeword once with possibly different answer lengths. The two counts
agree when the cover is *balanced*, `k (m + 1) = 2 ^ d`
(`PIR.RadiusOneCover.communication_scheme_of_balanced`): `cover` is then a bijection, so every
server emulates `m` distinct neighbours and no word is produced twice. The count is then the bound
`k + (2 ^ d + (d - 1) k) ℓ` of Theorem 1. Balance is a property of the cover; the source's
"balancing" (end of Section 3.2, Section 3.4) refers instead to the split of communication between
the user and the servers. Variable-length answers are not formalized, so Theorem 1 is covered for
balanced covers only. Every radius-`1` covering code gives a cover with `M = D`, emulating all
neighbours (`PIR.RadiusOneCover.ofHammingDist`), with `k (2 d ℓ + 1)` bits; this is the bound of
Theorem 1 exactly when the code is perfect.

A new cover of a concrete cube `Fin d → Bool` can be supplied by discharging `coveredWord_cover`
with `decide`, as for `PIR.RadiusOneCover.cubeThree` and `PIR.RadiusOneCover.cubeFour`.

Both cases of Corollary 2 use balanced covers:
* two servers, the repetition code `{000, 111}` (`PIR.RadiusOneCover.cubeThree`), with `12 ℓ + 2`
  bits for `n ≤ ℓ ^ 3` (`PIR.hasScheme_two_of_le_pow_three`);
* four servers, the code `{0000, 1111, 1000, 0111}` (`PIR.RadiusOneCover.cubeFour`), with
  `28 ℓ + 4` bits for `n ≤ ℓ ^ 4` (`PIR.hasScheme_four_of_le_pow_four`).

## Main definitions

* `Cslib.Crypto.Protocols.PIR.RadiusOneCover`: radius-`1` covers of `D → Bool` with emulation
  directions.
* `Cslib.Crypto.Protocols.PIR.RadiusOneCover.scheme`: the covering-code scheme.
* `Cslib.Crypto.Protocols.PIR.RadiusOneCover.ofHammingDist`: the cover of a radius-`1` covering
  code.
* `Cslib.Crypto.Protocols.PIR.RadiusOneCover.cubeThree`,
  `Cslib.Crypto.Protocols.PIR.RadiusOneCover.cubeFour`: the covers of Corollary 2.

## Main results

* `Cslib.Crypto.Protocols.PIR.RadiusOneCover.isCorrect_scheme`,
  `Cslib.Crypto.Protocols.PIR.RadiusOneCover.isPrivate_scheme`,
  `Cslib.Crypto.Protocols.PIR.RadiusOneCover.communication_scheme`: the covering-code scheme.
* `Cslib.Crypto.Protocols.PIR.RadiusOneCover.communication_scheme_of_balanced`: Theorem 1's count
  for balanced covers.
* `Cslib.Crypto.Protocols.PIR.RadiusOneCover.hasScheme`,
  `Cslib.Crypto.Protocols.PIR.RadiusOneCover.hasScheme_of_hammingDist`: schemes for `n`-bit
  databases.
* `Cslib.Crypto.Protocols.PIR.hasScheme_two_of_le_pow_three`,
  `Cslib.Crypto.Protocols.PIR.hasScheme_four_of_le_pow_four`: Corollary 2.

## References

* [B. Chor, O. Goldreich, E. Kushilevitz, M. Sudan, *Private information
  retrieval*][ChorGoldreichKushilevitzSudan1998], Section 3.3 (Theorem 1, Corollary 2); numbering of
  the authors' journal version of April 21, 1998
-/

public section

namespace Cslib.Crypto.Protocols.PIR

open Probability

/-- The word produced by the server `s` and an optional direction `r`: the codeword `code s`, or
the codeword with the coordinate `dir s r` flipped. Exposed so that downstream modules can check
the obligation `coveredWord_cover` of a concrete cover by `decide`. -/
@[expose] def RadiusOneCover.coveredWord {S D M : Type} [DecidableEq D] (code : S → D → Bool)
    (dir : S → M → D) : S × Option M → D → Bool
  | (s, none) => code s
  | (s, some r) => Function.update (code s) (dir s r) (!code s (dir s r))

/-- A radius-`1` cover of the cube `D → Bool` by the servers `S`
[CGKS, Section 3.3][ChorGoldreichKushilevitzSudan1998]. The server `s` has the codeword `code s`
and emulates the neighbours of `code s` in the directions `dir s r`, for `r : M`. Every word is
produced by the server and the optional direction that `cover` assigns to it. -/
structure RadiusOneCover (S D M : Type) [DecidableEq D] where
  /-- The codeword of each server. -/
  code : S → D → Bool
  /-- The directions of the neighbours that each server emulates. -/
  dir : S → M → D
  /-- The server, and possibly the direction, that produce each word. -/
  cover : (D → Bool) → S × Option M
  /-- Each word is produced by its assigned server and direction. -/
  coveredWord_cover : ∀ w, RadiusOneCover.coveredWord code dir (cover w) = w

namespace RadiusOneCover

@[simp]
theorem coveredWord_none {S D M : Type} [DecidableEq D] (code : S → D → Bool) (dir : S → M → D)
    (s : S) : coveredWord code dir (s, none) = code s :=
  rfl

@[simp]
theorem coveredWord_some {S D M : Type} [DecidableEq D] (code : S → D → Bool) (dir : S → M → D)
    (s : S) (r : M) :
    coveredWord code dir (s, some r) = Function.update (code s) (dir s r) (!code s (dir s r)) :=
  rfl

variable {S D M : Type} [DecidableEq D] (K : RadiusOneCover S D M)

theorem cover_injective : Function.Injective K.cover :=
  Function.LeftInverse.injective K.coveredWord_cover

include K in
/-- **The volume bound** [CGKS, Section 3.3][ChorGoldreichKushilevitzSudan1998]: a server and its
`|M|` emulated neighbours produce at most `|M| + 1` words, so `2 ^ d ≤ |S| (|M| + 1)`. -/
theorem two_pow_card_le [Fintype S] [Fintype D] [Fintype M] :
    2 ^ Fintype.card D ≤ Fintype.card S * (Fintype.card M + 1) := by
  have h := Fintype.card_le_of_injective _ K.cover_injective
  rwa [Fintype.card_fun, Fintype.card_bool, Fintype.card_prod, Fintype.card_option] at h

/-! ### The scheme -/

section Scheme

variable [Fintype D] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The answer of the `2 ^ d`-server scheme that the user reads for the word produced by the
server `s` and the optional direction `r`: the answer bit of `s` itself, or the emulated answer
for the position `j` of the flipped coordinate. -/
private def readAnswer (j : D → ι) : S × Option M → (S → Bool × (M → ι → Bool)) → Bool
  | (s, none), a => (a s).1
  | (s, some r), a => (a s).2 r (j (K.dir s r))

variable (ι)

/-- **The covering-code scheme** [CGKS, Section 3.3][ChorGoldreichKushilevitzSudan1998]. The
server `s` receives the query of `PIR.cube` for the server `code s`. It answers with the answer
bit of `PIR.cube` and, for each direction `l = dir s r` and each position `k : ι`, with the answer
of `PIR.cube` to the query with `e_k` added to its `l`-th set. The user reads the answer of every
server of `PIR.cube` from the emulating server and adds them. -/
noncomputable def scheme : Scheme (D → ι) S Unit (D → ι → Bool) (Bool × (M → ι → Bool)) where
  query i := (fun rq => (rq.1, fun s => rq.2 (K.code s))) <$> (cube D ι).query i
  answer s x a :=
    ((cube D ι).answer (K.code s) x a, fun r k =>
      (cube D ι).answer (K.code s) x
        (Function.update a (K.dir s r) (a (K.dir s r) + Pi.single k true)))
  reconstruct i _ a := ∑ w : D → Bool, K.readAnswer i (K.cover w) a

variable {ι}

theorem query_scheme (i : D → ι) :
    (K.scheme ι).query i = (fun rq => (rq.1, fun s => rq.2 (K.code s))) <$> (cube D ι).query i := by
  rfl

/-- The server `s` of the covering-code scheme receives the query of the server `code s` of
`PIR.cube`. -/
theorem eval_serverQuery_scheme (s : S) (i : D → ι) :
    ProbComp.eval ((K.scheme ι).serverQuery s i) =
      ProbComp.eval ((cube D ι).serverQuery (K.code s) i) := by
  rw [Scheme.eval_serverQuery, Scheme.eval_serverQuery, query_scheme, ProbComp.eval_map,
    PMF.map_comp]
  rfl

/-- **The covering-code scheme is private** [CGKS, Section 3.3][ChorGoldreichKushilevitzSudan1998]:
its queries are those of `PIR.cube`. -/
theorem isPrivate_scheme : (K.scheme ι).IsPrivate :=
  (K.scheme ι).isPrivate_iff.mpr fun s i i' => by
    rw [eval_serverQuery_scheme, eval_serverQuery_scheme,
      isPrivate_cube.eval_serverQuery_eq (K.code s) i i']

/-- **The covering-code scheme is correct** [CGKS, Section 3.3][ChorGoldreichKushilevitzSudan1998]:
the user reads the answer of every server of `PIR.cube`. -/
theorem isCorrect_scheme : (K.scheme ι).IsCorrect := by
  rw [Scheme.isCorrect_iff]
  intro x i r q hrq
  rw [query_scheme, ProbComp.eval_map] at hrq
  obtain ⟨⟨r₀, q₀⟩, h₀, hrq⟩ := (PMF.mem_support_map_iff _ _ _).1 hrq
  simp only [Prod.mk.injEq] at hrq
  obtain ⟨-, rfl⟩ := hrq
  refine Eq.trans ?_ (isCorrect_cube.reconstruct_eq x i h₀)
  rw [reconstruct_cube]
  refine Finset.sum_congr rfl fun w _ => ?_
  -- Read the answer of the server `w` from the server that produces it.
  conv_rhs => rw [← K.coveredWord_cover w]
  rcases K.cover w with ⟨s, _ | r⟩
  · rfl
  · change (cube D ι).answer (K.code s) x
        (Function.update (q₀ (K.code s)) (K.dir s r)
          (q₀ (K.code s) (K.dir s r) + Pi.single (i (K.dir s r)) true)) =
      (cube D ι).answer _ x
        (q₀ (Function.update (K.code s) (K.dir s r) (!K.code s (K.dir s r))))
    rw [query_update_cube h₀, answer_cube, answer_cube]

/-- **The covering-code scheme sends `d` sets of `ℓ` bits to each of the `k` servers and receives
`1 + m ℓ` bits from each**, in the fixed-length measure: `k ((d + m) ℓ + 1)` bits. -/
theorem communication_scheme [Fintype S] [Fintype M] [DecidableEq M] :
    communication S (D → ι → Bool) (Bool × (M → ι → Bool)) =
      Fintype.card S * ((Fintype.card D + Fintype.card M) * Fintype.card ι + 1) := by
  rw [communication_eq]
  simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_bool]
  rw [← pow_mul, ← pow_mul, ← pow_succ', Nat.clog_pow 2 _ (by norm_num),
    Nat.clog_pow 2 _ (by norm_num)]
  ring

/-- **Theorem 1's count for balanced covers** [CGKS, Theorem 1][ChorGoldreichKushilevitzSudan1998]:
when the `k` servers and their `m` emulated neighbours each produce exactly the `2 ^ d` words,
`k (m + 1) = 2 ^ d`, the scheme communicates `k + (2 ^ d + (d - 1) k) ℓ` bits. (*Balanced* is a
property of the cover, not the source's balancing of user and server communication.) -/
theorem communication_scheme_of_balanced [Fintype S] [Fintype M] [DecidableEq M]
    (hD : 0 < Fintype.card D)
    (hbal : Fintype.card S * (Fintype.card M + 1) = 2 ^ Fintype.card D) :
    communication S (D → ι → Bool) (Bool × (M → ι → Bool)) =
      Fintype.card S + (2 ^ Fintype.card D + (Fintype.card D - 1) * Fintype.card S) *
        Fintype.card ι := by
  rw [communication_scheme, ← hbal]
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hD
  rw [hd, Nat.add_sub_cancel]
  ring

include K in
/-- **Schemes from radius-`1` covers** [CGKS, Section 3.3][ChorGoldreichKushilevitzSudan1998]:
with a cover of `D → Bool` by `k` servers each emulating `m` neighbours, every `n ≤ ℓ ^ d` has a
perfectly correct and perfectly private `k`-server scheme for `n`-bit databases communicating
`k ((d + m) ℓ + 1)` bits. -/
theorem hasScheme [Fintype S] [Fintype M] {n ℓ : ℕ} (h : n ≤ ℓ ^ Fintype.card D) :
    HasScheme (Fin n) (Fintype.card S)
      (Fintype.card S * ((Fintype.card D + Fintype.card M) * ℓ + 1)) := by
  classical
  have hcard : Fintype.card (D → Fin ℓ) = ℓ ^ Fintype.card D := by
    rw [Fintype.card_fun, Fintype.card_fin]
  let e : Fin n ↪ (D → Fin ℓ) :=
    (Fin.castLEEmb (h.trans_eq hcard.symm)).trans (Fintype.equivFin (D → Fin ℓ)).symm.toEmbedding
  have hP := (K.isCorrect_scheme (ι := Fin ℓ)).comap e |>.hasScheme
    ((K.isPrivate_scheme (ι := Fin ℓ)).comap e)
  rwa [communication_scheme, Fintype.card_fin] at hP

end Scheme

/-! ### Covers from covering codes -/

section HammingDist

variable [Fintype D]

/-- The cover of a radius-`1` covering code `c : S → D → Bool` in which every server emulates all
its neighbours: each word is assigned a codeword within distance `1` and the coordinate where
they differ, if any. -/
noncomputable def ofHammingDist (c : S → D → Bool) (hc : ∀ w, ∃ s, hammingDist (c s) w ≤ 1) :
    RadiusOneCover S D D where
  code := c
  dir _ l := l
  cover w :=
    let s := Classical.choose (hc w)
    if h : w = c s then (s, none)
    else (s, some (Classical.choose (Function.ne_iff.mp (Ne.symm h))))
  coveredWord_cover w := by
    dsimp only
    split_ifs with h
    · exact h.symm
    · exact update_not_eq_of_hammingDist_le_one (Classical.choose_spec (hc w))
        (Classical.choose_spec (Function.ne_iff.mp (Ne.symm h)))

omit [DecidableEq D] in
/-- **Schemes from radius-`1` covering codes**
[CGKS, Section 3.3][ChorGoldreichKushilevitzSudan1998]: if every word of `D → Bool` is within
Hamming distance `1` of one of `k` codewords, every `n ≤ ℓ ^ d` has a perfectly correct and
perfectly private `k`-server scheme for `n`-bit databases communicating `k (2 d ℓ + 1)` bits. Each
server emulates all `d` neighbours of its codeword. This matches Theorem 1's
`k + (2 ^ d + (d - 1) k) ℓ` when the code is perfect, `k (d + 1) = 2 ^ d`, and exceeds it by
`(k (d + 1) - 2 ^ d) ℓ` in general. -/
theorem hasScheme_of_hammingDist [Fintype S] {c : S → D → Bool}
    (hc : ∀ w, ∃ s, hammingDist (c s) w ≤ 1) {n ℓ : ℕ} (h : n ≤ ℓ ^ Fintype.card D) :
    HasScheme (Fin n) (Fintype.card S) (Fintype.card S * (2 * Fintype.card D * ℓ + 1)) := by
  classical
  exact ((ofHammingDist c hc).hasScheme h).mono (le_of_eq (by ring))

end HammingDist

/-! ### The covers of Corollary 2 -/

/-- The repetition code `{000, 111}` covers the cube `Fin 3 → Bool` with radius `1`
[CGKS, Section 3.3][ChorGoldreichKushilevitzSudan1998]. Each codeword emulates its three
neighbours, so the cover is balanced: `2 (3 + 1) = 2 ^ 3`. -/
def cubeThree : RadiusOneCover Bool (Fin 3) (Fin 3) where
  code b _ := b
  dir _ l := l
  cover w :=
    let b := (w 0 && w 1) || (w 0 && w 2) || (w 1 && w 2)
    if w 0 ≠ b then (b, some 0) else if w 1 ≠ b then (b, some 1)
    else if w 2 ≠ b then (b, some 2) else (b, none)
  coveredWord_cover := by decide

/-- The code `{0000, 1111, 1000, 0111}` covers the cube `Fin 4 → Bool` with radius `1`
[CGKS, Section 3.3][ChorGoldreichKushilevitzSudan1998]. The codeword of `(a, b)` is `a b b b`, and
each codeword emulates its neighbours in the last three coordinates, so the cover is balanced:
`4 (3 + 1) = 2 ^ 4`. -/
def cubeFour : RadiusOneCover (Bool × Bool) (Fin 4) (Fin 3) where
  code ab l := if l = 0 then ab.1 else ab.2
  dir _ r := r.succ
  cover w :=
    let v : Fin 3 → Bool := fun r => w r.succ
    let b := (v 0 && v 1) || (v 0 && v 2) || (v 1 && v 2)
    if v 0 ≠ b then ((w 0, b), some 0) else if v 1 ≠ b then ((w 0, b), some 1)
    else if v 2 ≠ b then ((w 0, b), some 2) else ((w 0, b), none)
  coveredWord_cover := by decide

end RadiusOneCover

/-- **Two servers with `12 ℓ + 2` bits** [CGKS, Corollary 2][ChorGoldreichKushilevitzSudan1998]:
every `n ≤ ℓ ^ 3` has a perfectly correct and perfectly private two-server scheme for `n`-bit
databases communicating `12 ℓ + 2` bits. With `ℓ = ⌈n ^ (1/3)⌉` this is the source's
`12 n ^ (1/3) + 2`. -/
theorem hasScheme_two_of_le_pow_three {n ℓ : ℕ} (h : n ≤ ℓ ^ 3) :
    HasScheme (Fin n) 2 (12 * ℓ + 2) := by
  have hP := RadiusOneCover.cubeThree.hasScheme (n := n) (ℓ := ℓ) (by rwa [Fintype.card_fin])
  simp only [Fintype.card_bool, Fintype.card_fin] at hP
  exact hP.mono (by omega)

/-- **Four servers with `28 ℓ + 4` bits** [CGKS, Corollary 2][ChorGoldreichKushilevitzSudan1998]:
every `n ≤ ℓ ^ 4` has a perfectly correct and perfectly private four-server scheme for `n`-bit
databases communicating `28 ℓ + 4` bits. With `ℓ = ⌈n ^ (1/4)⌉` this is the source's
`28 n ^ (1/4) + 4`. -/
theorem hasScheme_four_of_le_pow_four {n ℓ : ℕ} (h : n ≤ ℓ ^ 4) :
    HasScheme (Fin n) 4 (28 * ℓ + 4) := by
  have hP := RadiusOneCover.cubeFour.hasScheme (n := n) (ℓ := ℓ) (by rwa [Fintype.card_fin])
  simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin] at hP
  exact hP.mono (by omega)

end Cslib.Crypto.Protocols.PIR
