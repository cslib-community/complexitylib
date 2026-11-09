/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Kolmogorov.ChainRule
public import CslibFrontier.Computability.Kolmogorov.Partrec

/-!
# The conditional universal description method

The conditional description method `condUniversal y`, for a condition `y : ℕ`, reads a program as
the header of a code `c` (`codeHeader c`, as for `universal`) followed by a program `p`, and runs
`c` on the pair `Nat.pair y (encode p)`: the described partial recursive function has access to the
condition. The conditional complexity `C(x | y)` is `(condUniversal y).complexity x`.

Every partial recursive function of the condition and the program is at most a constant worse
than `condUniversal`, uniformly in the condition: this is the conditional invariance theorem
[Shen, Uspensky and Vereshchagin, Section 2.2][ShenUspenskyVereshchagin2017], stated here both for
partial recursive decoders (`exists_ecomplexity_condUniversal_le_of_partrec₂`) and for partial
recursive conditional description methods (`IsCondPartrec.exists_ecomplexity_condUniversal_le`).
Its first consequences are `C(y | x) ≤ C(y) + O(1)` and `C(x | x) = O(1)`, and, combined with the
generic `Cslib.Kolmogorov.DescriptionMethod.Composition`, the chain rule
`C(⟨x, y⟩) ≤ C(x) + C(y | x) + 2 log C(x) + O(1)` for the plain complexity of `universal`, with
pairs coded by `Nat.pair` and `log` the binary length `Nat.size`.

## Main definitions

* `Cslib.Kolmogorov.DescriptionMethod.condUniversal`: the conditional universal method.
* `Cslib.Kolmogorov.DescriptionMethod.IsCondPartrec`: partial recursive conditional description
  methods for natural numbers.

## Main results

* `Cslib.Kolmogorov.DescriptionMethod.condUniversal_produces_codeHeader_append`: the program
  `codeHeader c ++ p` describes, given `y`, the output of `c` on `Nat.pair y (encode p)`.
* `Cslib.Kolmogorov.DescriptionMethod.exists_ecomplexity_condUniversal_le_of_partrec₂`,
  `Cslib.Kolmogorov.DescriptionMethod.IsCondPartrec.exists_ecomplexity_condUniversal_le`: the
  **conditional invariance theorem**.
* `Cslib.Kolmogorov.DescriptionMethod.exists_complexity_condUniversal_le`: `C(y | x) ≤ C(y) + O(1)`.
* `Cslib.Kolmogorov.DescriptionMethod.exists_complexity_condUniversal_self_le`: `C(x | x) = O(1)`.
* `Cslib.Kolmogorov.DescriptionMethod.exists_complexity_universal_pair_le`: the **chain rule**
  `C(⟨x, y⟩) ≤ C(x) + C(y | x) + 2 log C(x) + O(1)`.

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

/-- The *conditional universal* description method, given the condition `y : ℕ`: the decoder of
the self-delimiting code splits a program into the binary representation of a number `n` and a
program `p`, and `p` runs under the description method of the code `curry (ofNat Code n) y`, which
runs `ofNat Code n` on `Nat.pair y (encode p)`. -/
def condUniversal (y : ℕ) : DescriptionMethod ℕ where
  run q := (ofCode (Code.curry (ofNat Code ((decodeSelfDelimiting q).1.foldr Nat.bit 0)) y)).run
    (decodeSelfDelimiting q).2

@[simp]
theorem condUniversal_run_codeHeader_append (y : ℕ) (c : Code) (p : List Bool) :
    (condUniversal y).run (codeHeader c ++ p) = (ofCode (Code.curry c y)).run p := by
  simp [condUniversal, codeHeader]

/-- A program describes `x` given `y` exactly when the code it announces outputs `x` on the pair of
`y` and the rest of the program. -/
theorem condUniversal_produces_iff {y : ℕ} {q : List Bool} {x : ℕ} :
    (condUniversal y).Produces q x ↔
      x ∈ (ofNat Code ((decodeSelfDelimiting q).1.foldr Nat.bit 0)).eval
        (Nat.pair y (encode (decodeSelfDelimiting q).2)) := by
  rw [Produces]
  change x ∈ (ofCode _).run _ ↔ _
  rw [← Produces, ofCode_produces_iff, Code.eval_curry]

theorem condUniversal_produces_codeHeader_append {y : ℕ} {c : Code} {p : List Bool} {x : ℕ} :
    (condUniversal y).Produces (codeHeader c ++ p) x ↔ x ∈ c.eval (Nat.pair y (encode p)) := by
  rw [Produces, condUniversal_run_codeHeader_append, ← Produces, ofCode_produces_iff,
    Code.eval_curry]

/-- The outputs of the conditional universal method are partial recursive jointly in the condition
and the program. -/
theorem partrec₂_condUniversal_eval :
    Partrec₂ fun (y : ℕ) (q : List Bool) =>
      (ofNat Code ((decodeSelfDelimiting q).1.foldr Nat.bit 0)).eval
        (Nat.pair y (encode (decodeSelfDelimiting q).2)) := by
  have hd := primrec_decodeSelfDelimiting
  exact Code.eval_part.comp
    ((Computable.ofNat Code).comp
      (Primrec.list_foldr_nat_bit.comp (Primrec.fst.comp (hd.comp Primrec.snd))).to_comp)
    (Primrec₂.natPair.comp Primrec.fst
      (Primrec.encode.comp (Primrec.snd.comp (hd.comp Primrec.snd)))).to_comp

/-- **Conditional invariance for partial recursive decoders.** If a partial recursive function `f`
of the condition and the program outputs `x` on `y` and `q`, then `x` has a description given `y`
at most a constant longer than `q`, the constant depending only on `f`. -/
theorem exists_ecomplexity_condUniversal_le_of_partrec₂ {f : ℕ → List Bool →. ℕ}
    (hf : Partrec₂ f) :
    ∃ c : ℕ, ∀ y q x, x ∈ f y q → (condUniversal y).ecomplexity x ≤ q.length + c := by
  obtain ⟨c, hc⟩ := Code.exists_code.mp hf
  refine ⟨(codeHeader c).length, fun y q x hx => ?_⟩
  have h : (condUniversal y).Produces (codeHeader c ++ q) x := by
    rw [condUniversal_produces_codeHeader_append, hc]
    simpa using hx
  exact (ecomplexity_le_length h).trans (by rw [List.length_append, Nat.cast_add, add_comm])

/-- A conditional description method for natural numbers is *partial recursive* when a partial
recursive function of the condition and the program has exactly its outputs. Nothing is assumed
about its clock. -/
@[expose] def IsCondPartrec (N : ℕ → DescriptionMethod ℕ) : Prop :=
  ∃ f : ℕ → List Bool →. ℕ, Partrec₂ f ∧ ∀ y p x, (N y).Produces p x ↔ x ∈ f y p

theorem isCondPartrec_condUniversal : IsCondPartrec condUniversal :=
  ⟨_, partrec₂_condUniversal_eval, fun _ _ _ => condUniversal_produces_iff⟩

/-- **Conditional invariance theorem** [Shen, Uspensky and Vereshchagin, Section
2.2][ShenUspenskyVereshchagin2017]: `condUniversal` is at most a constant worse than every partial
recursive conditional description method, uniformly in the condition. -/
theorem IsCondPartrec.exists_ecomplexity_condUniversal_le {N : ℕ → DescriptionMethod ℕ}
    (hN : IsCondPartrec N) :
    ∃ c : ℕ, ∀ y x, (condUniversal y).ecomplexity x ≤ (N y).ecomplexity x + c := by
  obtain ⟨f, hf, hN⟩ := hN
  obtain ⟨c, hc⟩ := exists_ecomplexity_condUniversal_le_of_partrec₂ hf
  refine ⟨c, fun y x => ?_⟩
  by_cases h : (N y).ecomplexity x = ⊤
  · simp [h]
  obtain ⟨p, hp, hlen⟩ := exists_length_eq_ecomplexity h
  rw [← hlen]
  exact hc y p x ((hN y p x).mp hp)

/-- Every natural number has a description under the conditional universal method, whatever the
condition. -/
theorem ecomplexity_condUniversal_ne_top (y x : ℕ) : (condUniversal y).ecomplexity x ≠ ⊤ :=
  ecomplexity_ne_top_iff.mpr ⟨codeHeader (Code.const x) ++ [],
    condUniversal_produces_codeHeader_append.mpr (by simp)⟩

@[simp]
theorem natCast_complexity_condUniversal (y x : ℕ) :
    ((condUniversal y).complexity x : ℕ∞) = (condUniversal y).ecomplexity x :=
  natCast_complexity (ecomplexity_condUniversal_ne_top y x)

/-- A condition does not make a description longer by more than a constant:
`C(y | x) ≤ C(y) + O(1)` [Shen, Uspensky and Vereshchagin, Section
2.2][ShenUspenskyVereshchagin2017]. -/
theorem exists_complexity_condUniversal_le :
    ∃ c : ℕ, ∀ x y, (condUniversal x).complexity y ≤ universal.complexity y + c := by
  obtain ⟨F, hF, hU⟩ := isPartrec_universal
  obtain ⟨c, hc⟩ := exists_ecomplexity_condUniversal_le_of_partrec₂ (f := fun _ q => F q)
    (hF.comp Computable.snd)
  refine ⟨c, fun x y => ?_⟩
  obtain ⟨p, hp, hlen⟩ := exists_length_eq_ecomplexity (ecomplexity_universal_ne_top y)
  have h := hc x p y ((hU p y).mp hp)
  rw [hlen, ← natCast_complexity_universal, ← natCast_complexity_condUniversal] at h
  exact_mod_cast h

/-- A number is described by a constant number of bits given itself: `C(x | x) = O(1)`
[Shen, Uspensky and Vereshchagin, Section 2.2][ShenUspenskyVereshchagin2017]. -/
theorem exists_complexity_condUniversal_self_le :
    ∃ c : ℕ, ∀ x, (condUniversal x).complexity x ≤ c := by
  obtain ⟨c, hc⟩ := exists_ecomplexity_condUniversal_le_of_partrec₂
    (Computable₂.partrec₂ (f := fun (y : ℕ) (_ : List Bool) => y) Computable.fst)
  refine ⟨c, fun x => ?_⟩
  have h := hc x [] x (Part.mem_some x)
  rw [← natCast_complexity_condUniversal, List.length_nil, Nat.cast_zero, zero_add] at h
  exact_mod_cast h

/-! ### The chain rule -/

/-- The composition of `universal` and `condUniversal` along `Nat.pair` is partial recursive. -/
theorem isPartrec_compose_universal_condUniversal :
    (universal.compose condUniversal Nat.pair).IsPartrec := by
  obtain ⟨F, hF, hU⟩ := isPartrec_universal
  obtain ⟨G, hG, hC⟩ := isCondPartrec_condUniversal
  refine ⟨fun r => (F (decodeSelfDelimiting r).1).bind fun x =>
    (G x (decodeSelfDelimiting r).2).map (Nat.pair x), ?_, fun r z => ?_⟩
  · have hd := primrec_decodeSelfDelimiting
    refine Partrec.bind (hF.comp (Primrec.fst.comp hd).to_comp) ?_
    refine Partrec.map (hG.comp Computable.snd (Primrec.snd.comp (hd.comp Primrec.fst)).to_comp) ?_
    exact (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to_comp.to₂
  · rw [Part.mem_bind_iff]
    constructor
    · intro h
      obtain ⟨x, hx, hz⟩ := Computation.exists_of_mem_bind h
      obtain ⟨y, hy, rfl⟩ := Computation.exists_of_mem_map hz
      exact ⟨x, (hU _ x).mp hx, Part.mem_map _ ((hC x _ y).mp hy)⟩
    · rintro ⟨x, hx, hz⟩
      obtain ⟨y, hy, rfl⟩ := (Part.mem_map_iff _).mp hz
      exact Computation.mem_bind ((hU _ x).mpr hx) (Computation.mem_map _ ((hC x _ y).mpr hy))

/-- **Chain rule** for the plain complexity of `universal` [Shen, Uspensky and Vereshchagin,
Section 2.2][ShenUspenskyVereshchagin2017]: there is a constant `c` with
`C(⟨x, y⟩) ≤ C(x) + C(y | x) + 2 size (C(x)) + c`. -/
theorem exists_complexity_universal_pair_le :
    ∃ c : ℕ, ∀ x y, universal.complexity (Nat.pair x y) ≤
      universal.complexity x + (condUniversal x).complexity y +
        2 * (universal.complexity x).size + c := by
  obtain ⟨c, hc⟩ := isAdditivelyOptimal_universal.exists_ecomplexity_le _
    isPartrec_compose_universal_condUniversal
  refine ⟨c + 1, fun x y => ?_⟩
  have h := (hc (Nat.pair x y)).trans
    (add_le_add_left ((Composition.compose universal condUniversal Nat.pair).ecomplexity_le x y) c)
  rw [← natCast_complexity_universal, ← natCast_complexity_universal x,
    ← natCast_complexity_condUniversal, ENat.toNat_natCast] at h
  have h' : universal.complexity (Nat.pair x y) ≤ universal.complexity x +
      (condUniversal x).complexity y + (2 * (universal.complexity x).size + 1) + c := by
    exact_mod_cast h
  omega

end DescriptionMethod

end Cslib.Kolmogorov
