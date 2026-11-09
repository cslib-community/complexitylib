/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Kolmogorov.ConditionalPartrec
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Data.Set.Card
import CslibFrontier.Computability.Kolmogorov.Incompressibility
import CslibFrontier.Computability.Kolmogorov.Uncomputability
import CslibFrontier.Foundations.Computability.DistinctValues
import CslibFrontier.Foundations.Data.Nat.BinarySize
import CslibFrontier.Foundations.Data.Nat.Bits
import CslibFrontier.Foundations.Data.Set.Card
import Mathlib.Data.Nat.Log

/-!
# Symmetry of information

The **Kolmogorov–Levin theorem** [Shen, Uspensky and Vereshchagin, Section
2.2][ShenUspenskyVereshchagin2017] states that the plain complexity of a pair is the complexity of
its first component plus the conditional complexity of the second given the first, up to a
logarithmic term:

  `C(x, y) = C(x) + C(y | x) + O(log C(x, y))`.

Here `C(x) = universal.complexity x` is the plain complexity of the Partrec universal method,
`C(y | x) = (condUniversal x).complexity y` is the conditional complexity of
`Cslib.Kolmogorov.DescriptionMethod.condUniversal`, a pair is coded by `Nat.pair x y`, and `log` is
the binary length `Nat.size`. The objects are natural numbers rather than binary strings, and the
pairing is `Nat.pair`; another computable pairing changes `C(x, y)` by at most a constant.

The upper bound is the chain rule `exists_complexity_universal_pair_le`. This file proves the lower
bound (`exists_complexity_universal_add_condUniversal_le`), with explicit coefficients:

  `C(x) + C(y | x) ≤ C(x, y) + 2 log C(x, y) + 4 log log C(x, y) + O(1)`.

The proof is the standard counting argument. Let `k = C(x, y)`. The set `S_x` of `v` with
`C(x, v) ≤ k` is computably enumerable from `k` and `x`, contains `y`, and has fewer than
`2 ^ (k + 1)` elements; let `2 ^ l ≤ |S_x| < 2 ^ (l + 1)`. Given `x`, the number `y` is described
by `k` and its index in an enumeration of `S_x`, which is below `2 ^ (l + 1)`. The set of `u` with
`|S_u| ≥ 2 ^ l` is computably enumerable from `k` and `l`, contains `x`, and has fewer than
`2 ^ (k + 1 - l)` elements, since the sets `{u} × S_u` are disjoint subsets of the fewer than
`2 ^ (k + 1)` pairs of complexity at most `k`. So `x` is described by `k` and its index in that
enumeration, written with exactly `k + 1 - l` digits, from which `l` can be recovered. The two
descriptions together cost `k + 2` bits besides two self-delimiting codes of `k`. The enumerations
are `Nat.nthDistinctValue` of primitive recursive sequences of clocked runs of `universal`.

With the chain rule this gives the two-sided form (`exists_abs_complexity_universal_pair_sub_le`),
the comparison of `I(x : y) = C(y) - C(y | x)` with `C(x) + C(y) - C(x, y)`
(`exists_abs_algorithmicInformation_sub_le`), and the symmetry of the algorithmic information
(`exists_abs_algorithmicInformation_sub_algorithmicInformation_le`) [Shen, Uspensky and
Vereshchagin, Section 2.3][ShenUspenskyVereshchagin2017]. The logarithmic term cannot be removed
for plain complexity [Shen, Uspensky and Vereshchagin, Section 2.2][ShenUspenskyVereshchagin2017];
the exact symmetry of prefix complexity is not formalized here.

## Main definitions

* `Cslib.Kolmogorov.algorithmicInformation`: the information `I(x : y) = C(y) - C(y | x)` in `x`
  about `y`.

## Main results

* `Cslib.Kolmogorov.DescriptionMethod.finite_setOf_ecomplexity_pair_le`,
  `Cslib.Kolmogorov.DescriptionMethod.ncard_setOf_ecomplexity_pair_le_lt`: fewer than
  `2 ^ (k + 1)` numbers `v` have `C(x, v) ≤ k`.
* `Cslib.Kolmogorov.DescriptionMethod.finite_setOf_two_pow_le_ncard`,
  `Cslib.Kolmogorov.DescriptionMethod.two_pow_mul_ncard_setOf_two_pow_le_ncard_lt`: fewer than
  `2 ^ (k + 1 - l)` numbers `u` have at least `2 ^ l` partners `v` with `C(u, v) ≤ k`.
* `Cslib.Kolmogorov.DescriptionMethod.exists_complexity_universal_add_condUniversal_le`: the
  **Kolmogorov–Levin theorem**, the hard direction.
* `Cslib.Kolmogorov.DescriptionMethod.exists_abs_complexity_universal_pair_sub_le`: the
  two-sided form `|C(x, y) - C(x) - C(y | x)| ≤ 6 log C(x, y) + O(1)`.
* `Cslib.Kolmogorov.exists_algorithmicInformation_ge`: `I(x : y) ≥ -O(1)`.
* `Cslib.Kolmogorov.exists_abs_algorithmicInformation_sub_le`: `I(x : y)` is
  `C(x) + C(y) - C(x, y)` up to `6 log C(x, y) + O(1)`.
* `Cslib.Kolmogorov.exists_abs_algorithmicInformation_sub_algorithmicInformation_le`:
  **symmetry of information**, `|I(x : y) - I(y : x)| ≤ 12 log C(x, y) + O(1)`.

## References

* [A. Shen, V. A. Uspensky, N. Vereshchagin, *Kolmogorov Complexity and Algorithmic
  Randomness*][ShenUspenskyVereshchagin2017]
* [M. Li, P. Vitányi, *An Introduction to Kolmogorov Complexity and Its
  Applications*][LiVitanyi2019]
-/

public section

namespace Cslib.Kolmogorov

open Encodable Denumerable Nat.Partrec

namespace DescriptionMethod

/-! ### Counting pairs of bounded complexity -/

section Counting

variable (M : DescriptionMethod ℕ)

private theorem finite_ncard_setOf_ecomplexity_le_lt (k : ℕ) :
    {z | M.ecomplexity z ≤ k}.Finite ∧ {z | M.ecomplexity z ≤ k}.ncard < 2 ^ (k + 1) := by
  rw [← Set.encard_lt_coe_iff_finite_ncard_lt]
  refine (Set.encard_le_encard fun z hz => ?_).trans_lt
    (by exact_mod_cast M.encard_setOf_ecomplexity_lt (k + 1))
  exact (show M.ecomplexity z ≤ k from hz).trans_lt (by exact_mod_cast k.lt_succ_self)

private theorem finite_ncard_setOf_ecomplexity_pair_le_lt (k x : ℕ) :
    {v | M.ecomplexity (Nat.pair x v) ≤ k}.Finite ∧
      {v | M.ecomplexity (Nat.pair x v) ≤ k}.ncard < 2 ^ (k + 1) := by
  rw [← Set.encard_lt_coe_iff_finite_ncard_lt]
  have hinj : Function.Injective (Nat.pair x) := fun a b h => (Nat.pair_eq_pair.mp h).2
  rw [← hinj.encard_image]
  refine (Set.encard_le_encard ?_).trans_lt
    (by exact_mod_cast M.encard_setOf_ecomplexity_lt (k + 1))
  rintro _ ⟨v, hv, rfl⟩
  exact (show M.ecomplexity (Nat.pair x v) ≤ k from hv).trans_lt
    (by exact_mod_cast k.lt_succ_self)

/-- Only finitely many `v` have `C(x, v) ≤ k`. -/
theorem finite_setOf_ecomplexity_pair_le (k x : ℕ) :
    {v | M.ecomplexity (Nat.pair x v) ≤ k}.Finite :=
  (M.finite_ncard_setOf_ecomplexity_pair_le_lt k x).1

/-- Fewer than `2 ^ (k + 1)` numbers `v` have `C(x, v) ≤ k`. -/
theorem ncard_setOf_ecomplexity_pair_le_lt (k x : ℕ) :
    {v | M.ecomplexity (Nat.pair x v) ≤ k}.ncard < 2 ^ (k + 1) :=
  (M.finite_ncard_setOf_ecomplexity_pair_le_lt k x).2

private theorem ncard_setOf_ecomplexity_pair_le_eq (k u : ℕ) :
    {v | M.ecomplexity (Nat.pair u v) ≤ k}.ncard =
      {z ∈ {z | M.ecomplexity z ≤ k} | z.unpair.1 = u}.ncard := by
  rw [← Set.ncard_image_of_injective _
    (fun a b h => (Nat.pair_eq_pair.mp h).2 : Function.Injective (Nat.pair u))]
  congr 1
  ext z
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨hv, by simp⟩
  · rintro ⟨hz, rfl⟩
    exact ⟨z.unpair.2, by simpa using hz, by simp⟩

/-- Only finitely many `u` have at least `2 ^ l` partners `v` with `C(u, v) ≤ k`. -/
theorem finite_setOf_two_pow_le_ncard (k l : ℕ) :
    {u | 2 ^ l ≤ {v | M.ecomplexity (Nat.pair u v) ≤ k}.ncard}.Finite := by
  simp only [M.ncard_setOf_ecomplexity_pair_le_eq]
  exact Set.finite_setOf_le_ncard_fiber (M.finite_ncard_setOf_ecomplexity_le_lt k).1 _
    (pow_pos Nat.two_pos l).ne'

/-- **Few numbers have many partners**: fewer than `2 ^ (k + 1 - l)` numbers `u` have at least
`2 ^ l` partners `v` with `C(u, v) ≤ k`, since the pairs `(u, v)` are distinct and there are fewer
than `2 ^ (k + 1)` pairs of complexity at most `k`. -/
theorem two_pow_mul_ncard_setOf_two_pow_le_ncard_lt (k l : ℕ) :
    2 ^ l * {u | 2 ^ l ≤ {v | M.ecomplexity (Nat.pair u v) ≤ k}.ncard}.ncard < 2 ^ (k + 1) := by
  simp only [M.ncard_setOf_ecomplexity_pair_le_eq]
  have hT := M.finite_ncard_setOf_ecomplexity_le_lt k
  exact (Set.mul_ncard_setOf_le_ncard_fiber_le hT.1 _ _).trans_lt hT.2

end Counting

/-! ### Enumerating the pairs of bounded complexity -/

/-- The `n`-th attempt to enumerate `{v | C(x, v) ≤ k}`: read `n` as a program `p` of length at
most `k` and a fuel `t`, and report `v` if `p` outputs `Nat.pair x v` within fuel `t`. -/
private def sectionEvent (kx : ℕ × ℕ) (n : ℕ) : Option ℕ :=
  (decode (α := List Bool) n.unpair.1).bind fun p =>
    if p.length ≤ kx.1 then
      ((universal.run p).runFor n.unpair.2).bind fun z =>
        if z.unpair.1 = kx.2 then some z.unpair.2 else none
    else none

private theorem primrec₂_sectionEvent : Primrec₂ sectionEvent := by
  have hz : Primrec₂ fun (a : (ℕ × ℕ) × ℕ) (z : ℕ) =>
      if z.unpair.1 = a.1.2 then some z.unpair.2 else none :=
    Primrec₂.mk <| Primrec.ite (Primrec.eq.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.option_some.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))
      (Primrec.const none)
  have hp : Primrec₂ fun (a : (ℕ × ℕ) × ℕ) (p : List Bool) =>
      if p.length ≤ a.1.1 then
        ((universal.run p).runFor a.2.unpair.2).bind fun z =>
          if z.unpair.1 = a.1.2 then some z.unpair.2 else none
      else none :=
    Primrec₂.mk <| Primrec.ite (Primrec.nat_le.comp (Primrec.list_length.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.option_bind (primrec₂_universal_runFor.comp Primrec.snd
          (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst))))
        (hz.comp₂ (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right))
      (Primrec.const none)
  exact Primrec₂.mk <| Primrec.option_bind
    (Primrec.decode.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))) hp

private theorem exists_sectionEvent_eq_some_iff {k x v : ℕ} :
    (∃ n, sectionEvent (k, x) n = some v) ↔ universal.ecomplexity (Nat.pair x v) ≤ k := by
  constructor
  · rintro ⟨n, hn⟩
    simp only [sectionEvent, Option.bind_eq_some_iff] at hn
    obtain ⟨p, -, hn⟩ := hn
    split_ifs at hn with hlen
    obtain ⟨z, hz, hv⟩ := Option.bind_eq_some_iff.mp hn
    split_ifs at hv with hx
    obtain rfl := Option.some.inj hv
    have hzx : Nat.pair x z.unpair.2 = z := by rw [← hx, Nat.pair_unpair]
    rw [hzx]
    exact (ecomplexity_le_length (Produces.of_mem_runFor hz)).trans (by exact_mod_cast hlen)
  · intro h
    obtain ⟨p, hp, hlen⟩ :=
      exists_length_eq_ecomplexity (ne_top_of_le_ne_top (ENat.natCast_ne_top k) h)
    obtain ⟨t, ht⟩ := produces_iff_exists_mem_runFor.mp hp
    refine ⟨Nat.pair (encode p) t, ?_⟩
    have hlen' : p.length ≤ k := by
      rw [← hlen] at h
      exact_mod_cast h
    simp [sectionEvent, hlen', Option.mem_def.mp ht]

private theorem setOf_exists_sectionEvent_eq (k x : ℕ) :
    {v | ∃ n, sectionEvent (k, x) n = some v} = {v | universal.ecomplexity (Nat.pair x v) ≤ k} :=
  Set.ext fun _ => exists_sectionEvent_eq_some_iff

/-- The `s`-th attempt to enumerate `{u | 2 ^ l ≤ |{v | C(u, v) ≤ k}|}`: read `s` as a number `u`
and a bound `n`, and report `u` if the first `n` attempts to enumerate `{v | C(u, v) ≤ k}` found at
least `2 ^ l` values. -/
private def heavyEvent (kl : ℕ × ℕ) (s : ℕ) : Option ℕ :=
  if 2 ^ kl.2 ≤ (Nat.distinctValues (sectionEvent (kl.1, s.unpair.1)) s.unpair.2).length then
    some s.unpair.1 else none

private theorem primrec₂_heavyEvent : Primrec₂ heavyEvent := by
  have hdv := Primrec.distinctValues primrec₂_sectionEvent
  have hpow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  exact Primrec₂.mk <| Primrec.ite (Primrec.nat_le.comp
      (hpow.comp (Primrec.const 2) (Primrec.snd.comp Primrec.fst))
      (Primrec.list_length.comp (hdv.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)))
        (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))))
    (Primrec.option_some.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)))
    (Primrec.const none)

private theorem exists_heavyEvent_eq_some_iff {k l u : ℕ} :
    (∃ s, heavyEvent (k, l) s = some u) ↔
      2 ^ l ≤ {v | universal.ecomplexity (Nat.pair u v) ≤ k}.ncard := by
  have hfin : {v | ∃ n, sectionEvent (k, u) n = some v}.Finite :=
    setOf_exists_sectionEvent_eq k u ▸ universal.finite_setOf_ecomplexity_pair_le k u
  constructor
  · rintro ⟨s, hs⟩
    simp only [heavyEvent] at hs
    split_ifs at hs with h
    obtain rfl := Option.some.inj hs
    rw [← setOf_exists_sectionEvent_eq]
    exact h.trans (Nat.length_distinctValues_le_ncard hfin _)
  · intro h
    obtain ⟨N, hN⟩ := Nat.exists_length_distinctValues_eq_ncard hfin
    refine ⟨Nat.pair u N, ?_⟩
    rw [setOf_exists_sectionEvent_eq] at hN
    simp [heavyEvent, hN, h]

/-- Decode, given `x`, a program `selfDelimitingCode k.bits ++ j.bits` as the `j`-th element of
`{v | C(x, v) ≤ k}`. -/
private def sectionDecoder (x : ℕ) (q : List Bool) : Part ℕ :=
  Nat.nthDistinctValue (sectionEvent ((decodeSelfDelimiting q).1.foldr Nat.bit 0, x))
    ((decodeSelfDelimiting q).2.foldr Nat.bit 0)

private theorem partrec₂_sectionDecoder : Partrec₂ sectionDecoder := by
  have hd := primrec_decodeSelfDelimiting
  exact (Partrec.nthDistinctValue primrec₂_sectionEvent).comp
    (Primrec.pair (Primrec.list_foldr_nat_bit.comp (Primrec.fst.comp (hd.comp Primrec.snd)))
      Primrec.fst).to_comp
    (Primrec.list_foldr_nat_bit.comp (Primrec.snd.comp (hd.comp Primrec.snd))).to_comp

/-- Decode a program `selfDelimitingCode k.bits ++ w`, with `w` of length `k + 1 - l`, as the
element of index `w.foldr Nat.bit 0` of `{u | 2 ^ l ≤ |{v | C(u, v) ≤ k}|}`. -/
private def heavyDecoder (q : List Bool) : Part ℕ :=
  Nat.nthDistinctValue (heavyEvent ((decodeSelfDelimiting q).1.foldr Nat.bit 0,
    (decodeSelfDelimiting q).1.foldr Nat.bit 0 + 1 - (decodeSelfDelimiting q).2.length))
    ((decodeSelfDelimiting q).2.foldr Nat.bit 0)

private theorem partrec_heavyDecoder : Partrec heavyDecoder := by
  have hd := primrec_decodeSelfDelimiting
  have hk := Primrec.list_foldr_nat_bit.comp (Primrec.fst.comp hd)
  exact (Partrec.nthDistinctValue primrec₂_heavyEvent).comp
    (Primrec.pair hk (Primrec.nat_sub.comp (Primrec.succ.comp hk)
      (Primrec.list_length.comp (Primrec.snd.comp hd)))).to_comp
    (Primrec.list_foldr_nat_bit.comp (Primrec.snd.comp hd)).to_comp

/-! ### The Kolmogorov–Levin theorem -/

/-- **Kolmogorov–Levin theorem**, the hard direction [Shen, Uspensky and Vereshchagin, Section
2.2][ShenUspenskyVereshchagin2017]: there is a constant `c` with
`C(x) + C(y | x) ≤ C(x, y) + 2 size (C(x, y)) + 4 size (size (C(x, y))) + c` for all `x` and `y`,
for the plain complexity of `universal`, pairs coded by `Nat.pair`. -/
theorem exists_complexity_universal_add_condUniversal_le :
    ∃ c : ℕ, ∀ x y, universal.complexity x + (condUniversal x).complexity y ≤
      universal.complexity (Nat.pair x y) + 2 * (universal.complexity (Nat.pair x y)).size +
        4 * (universal.complexity (Nat.pair x y)).size.size + c := by
  obtain ⟨cY, hcY⟩ := exists_ecomplexity_condUniversal_le_of_partrec₂ partrec₂_sectionDecoder
  obtain ⟨cX, hcX⟩ := exists_ecomplexity_universal_le_of_partrec partrec_heavyDecoder
  refine ⟨cX + cY + 4, fun x y => ?_⟩
  set k := universal.complexity (Nat.pair x y) with hk
  have hxy : universal.ecomplexity (Nat.pair x y) ≤ k := by rw [hk, natCast_complexity_universal]
  -- the partners of `x`, and the logarithm `l` of their number
  set S := {v | universal.ecomplexity (Nat.pair x v) ≤ k} with hS
  have hSfin : S.Finite := universal.finite_setOf_ecomplexity_pair_le k x
  have hSlt : S.ncard < 2 ^ (k + 1) := universal.ncard_setOf_ecomplexity_pair_le_lt k x
  have hm0 : S.ncard ≠ 0 := ((Set.ncard_pos hSfin).mpr ⟨y, hxy⟩).ne'
  set l := Nat.log 2 S.ncard with hl
  have hlm : 2 ^ l ≤ S.ncard := Nat.pow_log_le_self 2 hm0
  have hml : S.ncard < 2 ^ (l + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two _
  have hlk : l ≤ k := by
    have h := (Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp (hlm.trans_lt hSlt)
    omega
  -- describing `y` given `x`, by its index `j` among the partners of `x`
  obtain ⟨n, hn⟩ := exists_sectionEvent_eq_some_iff.mpr hxy
  obtain ⟨j, hj, hjy⟩ :=
    Nat.exists_mem_nthDistinctValue_of_finite (setOf_exists_sectionEvent_eq k x ▸ hSfin) hn
  rw [setOf_exists_sectionEvent_eq] at hj
  have hY : (condUniversal x).ecomplexity y ≤
      ((selfDelimitingCode k.bits ++ j.bits).length : ℕ) + cY := by
    refine hcY x _ y ?_
    simpa [sectionDecoder, decodeSelfDelimiting_selfDelimitingCode_append] using hjy
  -- describing `x`, by its index `i` among the numbers with at least `2 ^ l` partners
  set B := {u | 2 ^ l ≤ {v | universal.ecomplexity (Nat.pair u v) ≤ k}.ncard} with hB
  have hBfin : B.Finite := universal.finite_setOf_two_pow_le_ncard k l
  have hBlt : 2 ^ l * B.ncard < 2 ^ (k + 1) :=
    universal.two_pow_mul_ncard_setOf_two_pow_le_ncard_lt k l
  have hrangeB : {u | ∃ s, heavyEvent (k, l) s = some u} = B :=
    Set.ext fun u => exists_heavyEvent_eq_some_iff
  obtain ⟨s, hs⟩ := exists_heavyEvent_eq_some_iff.mpr hlm
  obtain ⟨i, hi, hix⟩ := Nat.exists_mem_nthDistinctValue_of_finite (hrangeB ▸ hBfin) hs
  rw [hrangeB] at hi
  have hiB : i < 2 ^ (k + 1 - l) := by
    refine Nat.lt_of_mul_lt_mul_left (a := 2 ^ l) ?_
    calc 2 ^ l * i < 2 ^ l * B.ncard := Nat.mul_lt_mul_of_pos_left hi (pow_pos Nat.two_pos l)
      _ < 2 ^ (k + 1) := hBlt
      _ = 2 ^ l * 2 ^ (k + 1 - l) := by rw [← pow_add, Nat.add_sub_cancel' (by omega)]
  have hisize : i.size ≤ k + 1 - l := Nat.size_le.mpr hiB
  have hjsize : j.size ≤ l + 1 := Nat.size_le.mpr (hj.trans hml)
  -- `i` is written with exactly `k + 1 - l` digits, so that `l` can be recovered
  have hrest : (i.bits ++ List.replicate (k + 1 - l - i.size) false).length = k + 1 - l := by
    rw [List.length_append, List.length_replicate, Nat.size_eq_bits_len]
    omega
  have hl' : k + 1 - (k + 1 - l) = l := by omega
  have hX : universal.ecomplexity x ≤
      ((selfDelimitingCode k.bits ++ (i.bits ++ List.replicate (k + 1 - l - i.size) false)).length
        : ℕ) + cX := by
    refine hcX _ x ?_
    simpa [heavyDecoder, decodeSelfDelimiting_selfDelimitingCode_append,
      Nat.foldr_bit_append_replicate_false, hrest, hl'] using hix
  rw [← natCast_complexity_universal] at hX
  rw [← natCast_complexity_condUniversal] at hY
  norm_cast at hX hY
  rw [List.length_append, hrest, length_selfDelimitingCode, Nat.size_eq_bits_len] at hX
  rw [List.length_append, length_selfDelimitingCode, Nat.size_eq_bits_len,
    Nat.size_eq_bits_len] at hY
  omega

/-- **Kolmogorov–Levin theorem**, two-sided form [Shen, Uspensky and Vereshchagin, Section
2.2][ShenUspenskyVereshchagin2017]: there is a constant `c` with
`|C(x, y) - C(x) - C(y | x)| ≤ 6 size (C(x, y)) + c` for all `x` and `y`. -/
theorem exists_abs_complexity_universal_pair_sub_le :
    ∃ c : ℕ, ∀ x y, |(universal.complexity (Nat.pair x y) : ℤ) - universal.complexity x -
      (condUniversal x).complexity y| ≤ 6 * (universal.complexity (Nat.pair x y)).size + c := by
  obtain ⟨c₁, h₁⟩ := exists_complexity_universal_pair_le
  obtain ⟨c₂, h₂⟩ := exists_complexity_universal_add_condUniversal_le
  obtain ⟨c₃, h₃⟩ := exists_complexity_universal_comp_le (Primrec.fst.comp Primrec.unpair).to_comp
  refine ⟨2 * c₃ + c₁ + c₂ + 2, fun x y => ?_⟩
  have e₁ := h₁ x y
  have e₂ := h₂ x y
  have e₃ : universal.complexity x ≤ universal.complexity (Nat.pair x y) + c₃ := by
    simpa using h₃ (Nat.pair x y)
  have e₄ : (universal.complexity x).size ≤
      (universal.complexity (Nat.pair x y)).size + c₃ + 1 :=
    (Nat.size_le_size e₃).trans <| (Nat.size_add_le _ _).trans <| by
      have := Nat.size_le_self c₃
      omega
  have e₅ := Nat.size_le_self (universal.complexity (Nat.pair x y)).size
  rw [abs_le]
  constructor <;> omega

end DescriptionMethod

/-! ### Symmetry of information -/

open DescriptionMethod

/-- The **algorithmic information** `I(x : y) = C(y) - C(y | x)` in `x` about `y`
[Shen, Uspensky and Vereshchagin, Section 2.3][ShenUspenskyVereshchagin2017]: how much shorter `y`
can be described when `x` is known, for the plain complexity of `universal`. -/
@[expose] noncomputable def algorithmicInformation (x y : ℕ) : ℤ :=
  universal.complexity y - (condUniversal x).complexity y

/-- The algorithmic information is nonnegative up to a constant
[Shen, Uspensky and Vereshchagin, Section 2.3][ShenUspenskyVereshchagin2017]. -/
theorem exists_algorithmicInformation_ge :
    ∃ c : ℕ, ∀ x y, -(c : ℤ) ≤ algorithmicInformation x y := by
  obtain ⟨c, hc⟩ := exists_complexity_condUniversal_le
  refine ⟨c, fun x y => ?_⟩
  have h := hc x y
  rw [algorithmicInformation]
  omega

/-- The algorithmic information is `C(x) + C(y) - C(x, y)` up to a logarithmic term: there is a
constant `c` with `|I(x : y) - (C(x) + C(y) - C(x, y))| ≤ 6 size (C(x, y)) + c`
[Shen, Uspensky and Vereshchagin, Section 2.3][ShenUspenskyVereshchagin2017]. -/
theorem exists_abs_algorithmicInformation_sub_le :
    ∃ c : ℕ, ∀ x y, |algorithmicInformation x y - (universal.complexity x +
      universal.complexity y - universal.complexity (Nat.pair x y) : ℤ)| ≤
        6 * (universal.complexity (Nat.pair x y)).size + c := by
  obtain ⟨c, hc⟩ := exists_abs_complexity_universal_pair_sub_le
  refine ⟨c, fun x y => ?_⟩
  have h := abs_le.mp (hc x y)
  rw [abs_le, algorithmicInformation]
  constructor <;> omega

/-- **Symmetry of information** [Shen, Uspensky and Vereshchagin, Section
2.3][ShenUspenskyVereshchagin2017]: there is a constant `c` with
`|I(x : y) - I(y : x)| ≤ 12 size (C(x, y)) + c` for all `x` and `y`. -/
theorem exists_abs_algorithmicInformation_sub_algorithmicInformation_le :
    ∃ c : ℕ, ∀ x y, |algorithmicInformation x y - algorithmicInformation y x| ≤
      12 * (universal.complexity (Nat.pair x y)).size + c := by
  obtain ⟨c, hc⟩ := exists_abs_algorithmicInformation_sub_le
  obtain ⟨d, hd⟩ := exists_complexity_universal_comp_le
    (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.unpair)
      (Primrec.fst.comp Primrec.unpair)).to_comp
  refine ⟨2 * c + 7 * d + 6, fun x y => ?_⟩
  have h₁ := abs_le.mp (hc x y)
  have h₂ := abs_le.mp (hc y x)
  have e₁ : universal.complexity (Nat.pair y x) ≤ universal.complexity (Nat.pair x y) + d := by
    simpa using hd (Nat.pair x y)
  have e₂ : universal.complexity (Nat.pair x y) ≤ universal.complexity (Nat.pair y x) + d := by
    simpa using hd (Nat.pair y x)
  have e₃ : (universal.complexity (Nat.pair y x)).size ≤
      (universal.complexity (Nat.pair x y)).size + d + 1 :=
    (Nat.size_le_size e₁).trans <| (Nat.size_add_le _ _).trans <| by
      have := Nat.size_le_self d
      omega
  rw [abs_le]
  constructor <;> omega

end Cslib.Kolmogorov
