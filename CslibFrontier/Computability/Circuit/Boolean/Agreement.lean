/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.PartialKarchmerWigderson
public import CslibFrontier.Computability.Communication.OneOutEveryArity
public import CslibFrontier.Foundations.Data.BitString.Block
import Mathlib.Tactic

/-!
# Agreement on many inputs and formula depth

The *agreement function* of a partial Boolean function `f` on `n` bits
([ChukhinKulikovMihajlinSmal2026], Definition 3.3, printed p. 7; PDF p. 8) reads `k * n` bits as
`k` blocks of `n` bits (`BitString.block`). It is `b` when the blocks are pairwise distinct and
`f` is `b` on each of them, and undefined otherwise (`agreement_eq_some_iff`): it asks for the
common value of `f` on `k` distinct inputs promised to agree.

Its Karchmer–Wigderson game is the one-out-of-`k` problem of the Karchmer–Wigderson game of `f`,
an answer `(i, j)` naming bit `j` of block `i` (Remark 3.5, `ecomplexity_kwRelation_agreement`).
With the Karchmer–Wigderson theorem for partial functions and the source's Theorem 1.2
(`OneOut.ecomplexity_le_oneOut`), this gives Corollary 1.3: computing the common value of `f` on
`k` distinct inputs is almost as hard, in formula depth, as computing `f`
(`partialFormulaDepth_le_agreement`, `partialFormulaDepth_agreement_le`). Corollary 1.4
(`OneOut.ecomplexity_le_mul_oneOut`) gives a linear bound at every arity
(`partialFormulaDepth_le_mul`).

The source states both corollaries with `O(·)` and `|f⁻¹(0)|, |f⁻¹(1)| ≥ k ≥ 1`; here the
constants are explicit and Corollary 1.3 needs only `k ≥ 1` and `n ≥ 1`. The source's `KW_f` gives
Alice the input in `f⁻¹(0)`; `kwRelation` gives her the one in `f⁻¹(1)`, which exchanges the
players and changes no complexity.

## Main definitions

* `Cslib.Circuits.Boolean.agreement`: the agreement function `Agr_k(f)`.

## Main results

* `Cslib.Circuits.Boolean.agreement_eq_some_iff`: the values of the agreement function.
* `Cslib.Circuits.Boolean.ecomplexity_kwRelation_agreement`: Remark 3.5.
* `Cslib.Circuits.Boolean.partialFormulaDepth_agreement_le`,
  `Cslib.Circuits.Boolean.partialFormulaDepth_le_agreement`: Corollary 1.3.
* `Cslib.Circuits.Boolean.partialFormulaDepth_le_mul`: the formula-depth half of Corollary 1.4.

## References

* [N. Chukhin, A. S. Kulikov, I. Mihajlin and A. V. Smal, *Solving One of Many Instances is
  Almost as Hard as Solving One*][ChukhinKulikovMihajlinSmal2026]
-/

public section

namespace Cslib.Circuits.Boolean

open Cslib.Communication Cslib.BitString

variable {n k : ℕ} {f : BitString n → Option Bool}

open scoped Classical in
/-- **The agreement function** `Agr_k(f)` ([ChukhinKulikovMihajlinSmal2026], Definition 3.3): on
`k` blocks of `n` bits that are pairwise distinct and on which `f` takes one value, that value;
undefined otherwise. -/
noncomputable def agreement (k : ℕ) (f : BitString n → Option Bool) (z : BitString (k * n)) :
    Option Bool :=
  if Function.Injective (block z) then
    if ∀ i, f (block z i) = some true then some true
    else if ∀ i, f (block z i) = some false then some false
    else none
  else none

/-- For `k ≥ 1`, the agreement function is `b` exactly on pairwise distinct blocks on each of which
`f` is `b`. -/
theorem agreement_eq_some_iff [NeZero k] {z : BitString (k * n)} {b : Bool} :
    agreement k f z = some b ↔ Function.Injective (block z) ∧ ∀ i, f (block z i) = some b := by
  by_cases hinj : Function.Injective (block z)
  · by_cases ht : ∀ i, f (block z i) = some true <;> cases b <;> simp [agreement, hinj, ht]
  · simp [agreement, hinj]

/-- The input of `Agr_k(f)` concatenating `k` distinct inputs where `f` is `b`. -/
private noncomputable def encode [NeZero k] {b : Bool} (x : Fin k ↪ {x // f x = some b}) :
    {z // agreement k f z = some b} :=
  ⟨blocksEquiv.symm fun i => (x i).1, agreement_eq_some_iff.2
    ⟨by rw [block_blocksEquiv_symm]; exact fun _ _ h => x.injective (Subtype.ext h),
      fun i => by simpa using (x i).2⟩⟩

/-- The `k` distinct inputs where `f` is `b` that an input of `Agr_k(f)` concatenates. -/
private def decode [NeZero k] {b : Bool} (z : {z // agreement k f z = some b}) :
    Fin k ↪ {x // f x = some b} :=
  ⟨fun i => ⟨block z.1 i, (agreement_eq_some_iff.1 z.2).2 i⟩, fun _ _ h =>
    (agreement_eq_some_iff.1 z.2).1 (congrArg Subtype.val h)⟩

private theorem val_encode [NeZero k] {b : Bool} (x : Fin k ↪ {x // f x = some b}) :
    (encode x).1 = blocksEquiv.symm fun i => (x i).1 :=
  rfl

private theorem val_decode [NeZero k] {b : Bool} (z : {z // agreement k f z = some b}) (i : Fin k) :
    (decode z i).1 = block z.1 i :=
  rfl

/-- **[ChukhinKulikovMihajlinSmal2026], Remark 3.5.** For `k ≥ 1`, the Karchmer–Wigderson game
of `Agr_k(f)` is as hard as the one-out-of-`k` problem of the Karchmer–Wigderson game of `f`:
the players translate between concatenated blocks and `k`-tuples, and between bit
`finProdFinEquiv (i, j)` and bit `j` of block `i`. The source's `|f⁻¹(0)|, |f⁻¹(1)| ≥ k` is
needed only for its definition of `Agr_k(f)`. -/
theorem ecomplexity_kwRelation_agreement [NeZero k] (f : BitString n → Option Bool) :
    Protocol.ecomplexity (kwRelation (agreement k f)) Set.univ Set.univ =
      Protocol.ecomplexity (OneOut.Relation (k := k) (kwRelation f)) Set.univ Set.univ := by
  refine le_antisymm (Protocol.le_ecomplexity_iff.2 fun p hp => ?_)
    (Protocol.le_ecomplexity_iff.2 fun q hq => ?_)
  · refine (Protocol.ecomplexity_le_depth (p := (p.comap decode decode).map
      fun a => finProdFinEquiv (a.index, a.value)) fun z _ w _ => ?_).trans (by simp)
    simpa [kwRelation, OneOut.Relation, val_decode] using hp (decode z) trivial (decode w) trivial
  · refine (Protocol.ecomplexity_le_depth (p := (q.comap encode encode).map
      fun m => ⟨(finProdFinEquiv.symm m).1, (finProdFinEquiv.symm m).2⟩) fun x _ y _ => ?_).trans
      (by simp)
    simpa [kwRelation, OneOut.Relation, val_encode] using hq (encode x) trivial (encode y) trivial

/-- **Remark 3.5 with the Karchmer–Wigderson theorem**: the formula depth of `Agr_k(f)` is the
communication complexity of the one-out-of-`k` problem of the Karchmer–Wigderson game of `f`. -/
theorem natCast_partialFormulaDepth_agreement [NeZero n] [NeZero k]
    (f : BitString n → Option Bool) :
    (partialFormulaDepth (agreement k f) : ℕ∞) =
      Protocol.ecomplexity (OneOut.Relation (k := k) (kwRelation f)) Set.univ Set.univ := by
  rw [natCast_partialFormulaDepth_eq_ecomplexity, ecomplexity_kwRelation_agreement]

/-- **[ChukhinKulikovMihajlinSmal2026], Corollary 1.3, upper bound.** For `k, n ≥ 1`,
`D(Agr_k(f)) ≤ D(f)`. The source applies a formula for `f` to the first block; here the same
step is `OneOut.ecomplexity_le`, which runs a protocol for the game of `f` on the first
coordinate, under Remark 3.5 and the Karchmer–Wigderson theorem. -/
theorem partialFormulaDepth_agreement_le [NeZero n] [NeZero k] (f : BitString n → Option Bool) :
    partialFormulaDepth (agreement k f) ≤ partialFormulaDepth f := by
  have h := OneOut.ecomplexity_le (kwRelation f) (0 : Fin k)
  rw [← natCast_partialFormulaDepth_eq_ecomplexity, ← natCast_partialFormulaDepth_agreement] at h
  exact_mod_cast h

/-- The Karchmer–Wigderson game of a partial function is total. -/
theorem kwRelation_total (x : {x // f x = some true}) (y : {y // f y = some false}) :
    ∃ i, kwRelation f x y i := by
  by_contra h
  push Not at h
  have hxy : x.1 = y.1 := funext fun i => by simpa [kwRelation] using h i
  simpa [hxy, y.2] using x.2

/-- `f⁻¹(b)` has at most `2ⁿ` elements. -/
private theorem card_preimage_le (b : Bool) :
    Fintype.card {x // f x = some b} ≤ 2 ^ n :=
  (Fintype.card_subtype_le _).trans (by simp)

/-- **[ChukhinKulikovMihajlinSmal2026], Corollary 1.3, lower bound.** For `k ≥ 1` and `n ≥ 1`,
`D(f) ≤ max {D(Agr_k(f)), ⌈log₂ n⌉} + 18 ⌈log₂ k⌉ + 3 ⌈log₂ (n + 1)⌉ + 3`: Theorem 1.2 for the
Karchmer–Wigderson game of `f`, with output set `[n]`. The source's `|f⁻¹(0)|, |f⁻¹(1)| ≥ k` is
not needed. -/
theorem partialFormulaDepth_le_max_agreement [NeZero n] [NeZero k]
    (f : BitString n → Option Bool) :
    partialFormulaDepth f ≤ max (partialFormulaDepth (agreement k f)) (Nat.clog 2 n) +
      (18 * Nat.clog 2 k + 3 * Nat.clog 2 (n + 1) + 3) := by
  rcases isEmpty_or_nonempty {x // f x = some true} with hA | hA
  · simp [partialFormulaDepth_eq_zero_of_isEmpty (.inl hA)]
  rcases isEmpty_or_nonempty {y // f y = some false} with hB | hB
  · simp [partialFormulaDepth_eq_zero_of_isEmpty (.inr hB)]
  have h := OneOut.ecomplexity_le_oneOut (k := k) (R := kwRelation f) kwRelation_total
    (card_preimage_le true) (card_preimage_le false)
  rw [← natCast_partialFormulaDepth_eq_ecomplexity, ← natCast_partialFormulaDepth_agreement,
    Fintype.card_fin] at h
  have hmax : ((max (partialFormulaDepth (agreement k f)) (Nat.clog 2 n) : ℕ) : ℕ∞) =
      max (partialFormulaDepth (agreement k f) : ℕ∞) (Nat.clog 2 n : ℕ) :=
    Monotone.map_max fun _ _ h => Nat.cast_le.mpr h
  rw [← hmax] at h
  exact_mod_cast h

/-- **[ChukhinKulikovMihajlinSmal2026], Corollary 1.3, lower bound**, in additive form: for
`k ≥ 1` and `n ≥ 1`, `D(f) ≤ D(Agr_k(f)) + 18 ⌈log₂ k⌉ + 4 ⌈log₂ (n + 1)⌉ + 3`, the source's
`D(f) - O(log k + log n) ≤ D(Agr_k(f))`. -/
theorem partialFormulaDepth_le_agreement [NeZero n] [NeZero k] (f : BitString n → Option Bool) :
    partialFormulaDepth f ≤
      partialFormulaDepth (agreement k f) + 18 * Nat.clog 2 k + 4 * Nat.clog 2 (n + 1) + 3 := by
  have h := partialFormulaDepth_le_max_agreement (k := k) f
  have hn : Nat.clog 2 n ≤ Nat.clog 2 (n + 1) := Nat.clog_mono_right 2 (Nat.le_succ n)
  omega

/-- **[ChukhinKulikovMihajlinSmal2026], Corollary 1.4, formula depth.** For `n ≥ 1` and
`1 ≤ k ≤ min {|f⁻¹(0)|, |f⁻¹(1)|}`, `D(f) ≤ 19 · D(Agr_k(f)) + 4 ⌈log₂ (n + 1)⌉ + 3`: a lower
bound `D(Agr_k(f)) ≥ D(f)/19 - O(log n)` at every arity. -/
theorem partialFormulaDepth_le_mul [NeZero n] [NeZero k] (f : BitString n → Option Bool)
    (hA : k ≤ Fintype.card {x // f x = some true})
    (hB : k ≤ Fintype.card {y // f y = some false}) :
    partialFormulaDepth f ≤
      19 * partialFormulaDepth (agreement k f) + 4 * Nat.clog 2 (n + 1) + 3 := by
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have : Nonempty {x // f x = some true} := Fintype.card_pos_iff.mp (hk.trans_le hA)
  have : Nonempty {y // f y = some false} := Fintype.card_pos_iff.mp (hk.trans_le hB)
  have h := OneOut.ecomplexity_le_mul_oneOut (k := k) (R := kwRelation f) kwRelation_total
    (card_preimage_le true) (card_preimage_le false) hA hB
  rw [← natCast_partialFormulaDepth_eq_ecomplexity, ← natCast_partialFormulaDepth_agreement,
    Fintype.card_fin] at h
  have h' : partialFormulaDepth f ≤ 19 * partialFormulaDepth (agreement k f) +
      (Nat.clog 2 n + 3 * Nat.clog 2 (n + 1) + 3) := by exact_mod_cast h
  have hn : Nat.clog 2 n ≤ Nat.clog 2 (n + 1) := Nat.clog_mono_right 2 (Nat.le_succ n)
  omega

end Cslib.Circuits.Boolean
