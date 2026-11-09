/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Nondeterministic.Basic
public import Mathlib.Data.Nat.Log
import CslibFrontier.Foundations.Data.ENat.IInf

/-!
# Cover numbers

The *`z`-cover number* `Nondeterministic.coverNumber z R A B` of a relation
`R : X → Y → Bool → Prop` on `A × B` is the least number of rectangles in a `z`-cover of `R` on
`A × B` (`Nondeterministic.IsCover`), or `⊤` if there is none. For a function `f : X → Y → Bool`,
`Nondeterministic.coverNumberFun z f A B` is the cover number of the relation `f x y = b`; on all of
`X × Y` this is `C^z(f)` of [Kushilevitz and Nisan, Definition 2.1(4), p. 17][KushilevitzNisan1997],
and for `z = true` it is the *rectangle covering bound* of the Boolean matrix `f`
[FioriniMassarPokuttaTiwaryDeWolf2015, footnote 2].

Nondeterministic communication complexity is the base-`2` logarithm of the cover number, rounded up:
`ecomplexity z R A B ≤ k` exactly when `coverNumber z R A B ≤ 2 ^ k`
(`Nondeterministic.ecomplexity_le_iff_coverNumber_le`), so
`ecomplexity z R A B = ⌈log₂ (coverNumber z R A B)⌉` when the cover number is finite
(`Nondeterministic.ecomplexity_eq_clog_coverNumber`). A fooling set bounds the cover number from
below by its size (`Nondeterministic.card_le_coverNumberFun_of_isFoolingSet`), not only its
complexity by the logarithm of its size.

## Main definitions

* `Cslib.Communication.Nondeterministic.coverNumber`,
  `Cslib.Communication.Nondeterministic.coverNumberFun`: the least number of rectangles in a cover.

## Main results

* `Cslib.Communication.Nondeterministic.IsCover.coverNumber_le`,
  `Cslib.Communication.Nondeterministic.coverNumber_le_iff`,
  `Cslib.Communication.Nondeterministic.le_coverNumber_iff`: bounds through covers.
* `Cslib.Communication.Nondeterministic.hasCover_iff_coverNumber_le`,
  `Cslib.Communication.Nondeterministic.ecomplexity_le_iff_coverNumber_le`,
  `Cslib.Communication.Nondeterministic.ecomplexity_le_clog`,
  `Cslib.Communication.Nondeterministic.ecomplexity_eq_clog_coverNumber`: nondeterministic
  complexity is `⌈log₂⌉` of the cover number.
* `Cslib.Communication.Nondeterministic.card_le_coverNumberFun_of_isFoolingSet`: the fooling-set
  bound on cover numbers.

## References

* [E. Kushilevitz, N. Nisan, *Communication Complexity*][KushilevitzNisan1997]
* [FioriniMassarPokuttaTiwaryDeWolf2015], Section 1
-/

public section

namespace Cslib.Communication

namespace Nondeterministic

variable {X Y : Type*}

/-- The `z`-cover number of `R` on `A × B`: the least number of rectangles in a `z`-cover of `R` on
`A × B`, or `⊤` if there is none. -/
noncomputable def coverNumber (z : Bool) (R : X → Y → Bool → Prop) (A : Set X) (B : Set Y) : ℕ∞ :=
  ⨅ r : {r : ℕ // ∃ C : Fin r → Set X × Set Y, IsCover z R A B C}, (r.1 : ℕ∞)

/-- The `z`-cover number of `f` on `A × B`: `coverNumber` of the relation `f x y = b`. For
`z = true` on all of `X × Y` this is the rectangle covering bound of the Boolean matrix `f`. -/
@[expose] noncomputable def coverNumberFun (z : Bool) (f : X → Y → Bool) (A : Set X) (B : Set Y) :
    ℕ∞ :=
  coverNumber z (fun x y b => f x y = b) A B

variable {R : X → Y → Bool → Prop} {f : X → Y → Bool} {z : Bool} {A : Set X} {B : Set Y}
  {κ κ' : Type*}

/-- A cover can be reindexed along an embedding of index types, using empty rectangles for the new
indices. -/
theorem IsCover.of_embedding {C : κ → Set X × Set Y} (hC : IsCover z R A B C) (e : κ ↪ κ') :
    IsCover z R A B (Function.extend e C fun _ => (∅, ∅)) := by
  obtain ⟨hmem, hcov⟩ := hC
  refine ⟨fun w' x hx hxC y hy hyC => ?_, fun x hx y hy hR => ?_⟩
  · by_cases hw' : ∃ w, e w = w'
    · obtain ⟨w, rfl⟩ := hw'
      rw [e.injective.extend_apply] at hxC hyC
      exact hmem w x hx hxC y hy hyC
    · rw [Function.extend_apply' _ _ _ hw'] at hxC
      exact absurd hxC (Set.notMem_empty x)
  · obtain ⟨w, hw⟩ := hcov x hx y hy hR
    exact ⟨e w, by rwa [e.injective.extend_apply]⟩

/-- A cover by rectangles indexed by a finite type `κ` bounds the cover number by `|κ|`. -/
theorem IsCover.coverNumber_le [Fintype κ] {C : κ → Set X × Set Y} (hC : IsCover z R A B C) :
    coverNumber z R A B ≤ Fintype.card κ := by
  classical
  refine iInf_le (fun r : {r : ℕ // ∃ C : Fin r → Set X × Set Y, IsCover z R A B C} =>
    (r.1 : ℕ∞)) ⟨Fintype.card κ, _, hC.of_embedding (Fintype.equivFin κ).toEmbedding⟩

/-- Lower bounds on the cover number are lower bounds on the size of every cover. -/
theorem le_coverNumber_iff {c : ℕ∞} :
    c ≤ coverNumber z R A B ↔ ∀ r (C : Fin r → Set X × Set Y), IsCover z R A B C → c ≤ r := by
  simp only [coverNumber, le_iInf_iff, Subtype.forall, forall_exists_index]

/-- `R` has `z`-cover number at most `r` exactly when it has a `z`-cover by `r` rectangles. -/
theorem coverNumber_le_iff {r : ℕ} :
    coverNumber z R A B ≤ r ↔ ∃ C : Fin r → Set X × Set Y, IsCover z R A B C := by
  classical
  refine ⟨fun h => ?_, fun ⟨C, hC⟩ => by simpa using hC.coverNumber_le⟩
  obtain ⟨⟨s, C, hC⟩, hsr⟩ := ENat.iInf_natCast_le_natCast_iff.mp h
  exact ⟨_, hC.of_embedding (Fin.castLEEmb hsr)⟩

/-- A cover by `2 ^ k` rectangles indexed by `k`-bit guesses is a cover by at most `2 ^ k`
rectangles. -/
theorem hasCover_iff_coverNumber_le {k : ℕ} :
    HasCover z R A B k ↔ coverNumber z R A B ≤ (2 ^ k : ℕ) := by
  rw [coverNumber_le_iff]
  refine ⟨fun ⟨C, hC⟩ => ⟨C ∘ (BitString.equivFin k).symm, ?_⟩,
    fun ⟨C, hC⟩ => ⟨C ∘ BitString.equivFin k, ?_⟩⟩
  · obtain ⟨hmem, hcov⟩ := hC
    refine ⟨fun w => hmem _, fun x hx y hy hR => ?_⟩
    obtain ⟨w, hw⟩ := hcov x hx y hy hR
    exact ⟨BitString.equivFin k w, by simpa using hw⟩
  · obtain ⟨hmem, hcov⟩ := hC
    refine ⟨fun w => hmem _, fun x hx y hy hR => ?_⟩
    obtain ⟨w, hw⟩ := hcov x hx y hy hR
    exact ⟨(BitString.equivFin k).symm w, by simpa using hw⟩

/-- Nondeterministic complexity is at most `k` exactly when the cover number is at most `2 ^ k`. -/
theorem ecomplexity_le_iff_coverNumber_le {k : ℕ} :
    ecomplexity z R A B ≤ k ↔ coverNumber z R A B ≤ (2 ^ k : ℕ) :=
  ecomplexity_le_iff.trans hasCover_iff_coverNumber_le

/-- A cover by at most `r` rectangles bounds the nondeterministic complexity by `⌈log₂ r⌉`. -/
theorem ecomplexity_le_clog {r : ℕ} (h : coverNumber z R A B ≤ r) :
    ecomplexity z R A B ≤ Nat.clog 2 r :=
  ecomplexity_le_iff_coverNumber_le.2 <| h.trans <| by exact_mod_cast Nat.le_pow_clog one_lt_two r

/-- **Nondeterministic complexity is `⌈log₂⌉` of the cover number**, when the cover number is
finite. -/
theorem ecomplexity_eq_clog_coverNumber {r : ℕ} (h : coverNumber z R A B = r) :
    ecomplexity z R A B = Nat.clog 2 r := by
  refine le_antisymm (ecomplexity_le_clog h.le) (le_ecomplexity_iff.2 fun k hk => ?_)
  rw [hasCover_iff_coverNumber_le, h, Nat.cast_le] at hk
  exact_mod_cast Nat.clog_le_of_le_pow hk

/-- The nondeterministic complexity is infinite exactly when the cover number is. -/
theorem ecomplexity_eq_top_iff_coverNumber_eq_top :
    ecomplexity z R A B = ⊤ ↔ coverNumber z R A B = ⊤ := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_contra hne
    obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.1 hne
    exact ENat.natCast_ne_top _ <| top_le_iff.1 <| h ▸ ecomplexity_le_clog hr.symm.le
  · by_contra hne
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hne
    exact ENat.natCast_ne_top _ <| top_le_iff.1 <|
      h ▸ ecomplexity_le_iff_coverNumber_le.1 hk.symm.le

/-- `IsCover.coverNumber_le` for functions. -/
theorem IsCover.coverNumberFun_le [Fintype κ] {C : κ → Set X × Set Y}
    (hC : IsCover z (fun x y b => f x y = b) A B C) :
    coverNumberFun z f A B ≤ Fintype.card κ :=
  hC.coverNumber_le

/-- `le_coverNumber_iff` for functions. -/
theorem le_coverNumberFun_iff {c : ℕ∞} :
    c ≤ coverNumberFun z f A B ↔
      ∀ r (C : Fin r → Set X × Set Y), IsCover z (fun x y b => f x y = b) A B C → c ≤ r :=
  le_coverNumber_iff

/-- `coverNumber_le_iff` for functions. -/
theorem coverNumberFun_le_iff {r : ℕ} :
    coverNumberFun z f A B ≤ r ↔
      ∃ C : Fin r → Set X × Set Y, IsCover z (fun x y b => f x y = b) A B C :=
  coverNumber_le_iff

/-- **The fooling-set bound on cover numbers.** A fooling set for `f` with value `z` inside `A × B`
has at most as many pairs as a `z`-cover of `f` on `A × B` has rectangles. -/
theorem card_le_coverNumberFun_of_isFoolingSet {S : Finset (X × Y)} (hS : IsFoolingSet f z S)
    (hSAB : ∀ q ∈ S, q.1 ∈ A ∧ q.2 ∈ B) :
    (S.card : ℕ∞) ≤ coverNumberFun z f A B :=
  le_coverNumberFun_iff.2 fun r _ hC => by
    simpa using (Nat.cast_le (α := ℕ∞)).2 (hC.card_le hS hSAB)

end Nondeterministic

end Cslib.Communication
