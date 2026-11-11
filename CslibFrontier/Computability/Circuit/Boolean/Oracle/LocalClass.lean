/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Computability.Language

/-!
# Local classes of oracle devices

Chen, Hirahara, Oliveira, Pich, Rajgopal and Santhanam measure the oracle gates of an oracle
circuit in three ways: their *quantity* (the number of oracle gates), their *locality* (the largest
fan-in of an oracle gate) and their *adaptivity* (the largest number of oracle gates on a path from
an input to the output). A language is in their class `[q, ℓ, a]–C` when one oracle language `O`
and, for each input length `n`, an oracle circuit from `C` with these measures bounded by `q n`,
`ℓ n` and `a n` compute it [ChenHiraharaOliveiraPichRajgopalSanthanam2020, Section 2.5,
Definition 11, p. 13; repeated as Definition 62, Appendix A.2, p. 51].

The definition is parametric in the class `C` of devices. An `OracleModel` packages a family of
devices with their evaluation under an oracle, a size and the three oracle measures, and
`OracleModel.LocalClass` is Definition 11 for promise problems over it: the class of the source is
`[q, ℓ, a]–C[S]` with `C[S]` the devices of the model of size at most `S`. A language `L` is the
promise problem with no-instances its complement. The models in this library are oracle formulas
(`Cslib.Circuits.Boolean.formulaModel`, with `LocalFormulaClass`) and oracle circuits
(`Cslib.Circuits.Boolean.circuitModel`, with `LocalCircuitClass`).

## Main definitions

* `Cslib.Circuits.Boolean.OracleModel`: devices with an oracle evaluation, a size and the three
  oracle measures.
* `Cslib.Circuits.Boolean.OracleModel.LocalClass`: the local class `[q, ℓ, a]–C[S]` of a promise
  problem.

## Main results

* `Cslib.Circuits.Boolean.OracleModel.LocalClass.mono`, `OracleModel.LocalClass.anti`: the classes
  grow with their parameters and shrink with their promise sets.
* `Cslib.Circuits.Boolean.OracleModel.LocalClass.of_two_pow`: a promise problem whose instances
  have lengths that are powers of two is in a local class once each length `2 ^ n` has a
  separating device, and every other length has some device within the bounds.

## References

* [L. Chen, S. Hirahara, I. C. Oliveira, J. Pich, N. Rajgopal, R. Santhanam, *Beyond Natural
  Proofs: Hardness Magnification and Locality*][ChenHiraharaOliveiraPichRajgopalSanthanam2020]
-/

public section

namespace Cslib.Circuits.Boolean

/-- A model of oracle devices for Definition 11 of
[ChenHiraharaOliveiraPichRajgopalSanthanam2020]: devices on `m` inputs, their output under an
oracle language, their size, and the quantity, locality and adaptivity of their oracle gates.
Locality is a predicate, "every oracle gate has fan-in at most `ℓ`", monotone in `ℓ`. -/
structure OracleModel where
  /-- The devices on `m` inputs. -/
  Device : ℕ → Type
  /-- The output of a device on an input when its oracle gates answer membership in `O`. -/
  eval : {m : ℕ} → Device m → Language Bool → (Fin m → Bool) → Bool
  /-- The size of a device. -/
  size : {m : ℕ} → Device m → ℕ
  /-- The quantity of the oracle gates: their number. -/
  queryCount : {m : ℕ} → Device m → ℕ
  /-- The locality of the oracle gates: every oracle gate has fan-in at most `ℓ`. -/
  QueryArityAtMost : {m : ℕ} → Device m → ℕ → Prop
  /-- The adaptivity of the oracle gates: the largest number of them on a path to the output. -/
  adaptivity : {m : ℕ} → Device m → ℕ
  /-- A locality bound holds for every larger bound. -/
  queryArityAtMost_mono : ∀ {m : ℕ} {E : Device m} {ℓ ℓ' : ℕ},
    QueryArityAtMost E ℓ → ℓ ≤ ℓ' → QueryArityAtMost E ℓ'

namespace OracleModel

variable (M : OracleModel)

/-- **Local classes** [ChenHiraharaOliveiraPichRajgopalSanthanam2020, Section 2.5,
Definition 11, p. 13], for promise problems: the promise problem with yes-instances `Yes` and
no-instances `No` is in `[q, ℓ, a]–C[S]`, for the devices `C` of the model `M`, when there is one
oracle language `O` such that, for every input length `m`, some device on `m` inputs with
- size at most `S m`,
- at most `q m` oracle gates (quantity), each of fan-in at most `ℓ m` (locality),
- at most `a m` oracle gates on any path to the output (adaptivity),
answers `true` on the yes-instances and `false` on the no-instances of length `m` under `O`. -/
@[expose] def LocalClass (q ℓ a S : ℕ → ℕ) (Yes No : Language Bool) : Prop :=
  ∃ O : Language Bool, ∀ m, ∃ E : M.Device m,
    M.size E ≤ S m ∧ M.queryCount E ≤ q m ∧ M.QueryArityAtMost E (ℓ m) ∧ M.adaptivity E ≤ a m ∧
      (∀ x : Fin m → Bool, List.ofFn x ∈ Yes → M.eval E O x = true) ∧
      (∀ x : Fin m → Bool, List.ofFn x ∈ No → M.eval E O x = false)

variable {M}

/-- The local classes grow with their parameters. -/
theorem LocalClass.mono {q ℓ a S q' ℓ' a' S' : ℕ → ℕ} {Yes No : Language Bool}
    (h : M.LocalClass q ℓ a S Yes No) (hq : q ≤ q') (hℓ : ℓ ≤ ℓ') (ha : a ≤ a') (hS : S ≤ S') :
    M.LocalClass q' ℓ' a' S' Yes No := by
  obtain ⟨O, hO⟩ := h
  refine ⟨O, fun m => ?_⟩
  obtain ⟨E, hS', hq', hℓ', ha', hyes, hno⟩ := hO m
  exact ⟨E, hS'.trans (hS m), hq'.trans (hq m), M.queryArityAtMost_mono hℓ' (hℓ m),
    ha'.trans (ha m), hyes, hno⟩

/-- Shrinking the yes- and no-instances keeps a promise problem in a local class. -/
theorem LocalClass.anti {q ℓ a S : ℕ → ℕ} {Yes No Yes' No' : Language Bool}
    (h : M.LocalClass q ℓ a S Yes No) (hY : Yes' ≤ Yes) (hN : No' ≤ No) :
    M.LocalClass q ℓ a S Yes' No' := by
  obtain ⟨O, hO⟩ := h
  refine ⟨O, fun m => ?_⟩
  obtain ⟨E, hS, hq, hℓ, ha, hyes, hno⟩ := hO m
  exact ⟨E, hS, hq, hℓ, ha, fun x hx => hyes x (hY hx), fun x hx => hno x (hN hx)⟩

/-- **Instances of power-of-two length.** If every yes- and no-instance has length a power of two,
such as the truth tables of a property, a promise problem is in a local class once some oracle
`O` and, at each length `2 ^ n`, a device within the bounds at `2 ^ n` separates the instances of
that length, provided every other length has some device within the bounds; there is nothing to
separate at those lengths. -/
theorem LocalClass.of_two_pow {q ℓ a S : ℕ → ℕ} {Yes No : Language Bool} (O : Language Bool)
    (hYes : ∀ w ∈ Yes, ∃ n, w.length = 2 ^ n) (hNo : ∀ w ∈ No, ∃ n, w.length = 2 ^ n)
    (hdef : ∀ m, (¬∃ n, m = 2 ^ n) → ∃ E : M.Device m,
      M.size E ≤ S m ∧ M.queryCount E ≤ q m ∧ M.QueryArityAtMost E (ℓ m) ∧ M.adaptivity E ≤ a m)
    (hpow : ∀ n, ∃ E : M.Device (2 ^ n),
      M.size E ≤ S (2 ^ n) ∧ M.queryCount E ≤ q (2 ^ n) ∧ M.QueryArityAtMost E (ℓ (2 ^ n)) ∧
        M.adaptivity E ≤ a (2 ^ n) ∧
        (∀ x : Fin (2 ^ n) → Bool, List.ofFn x ∈ Yes → M.eval E O x = true) ∧
        (∀ x : Fin (2 ^ n) → Bool, List.ofFn x ∈ No → M.eval E O x = false)) :
    M.LocalClass q ℓ a S Yes No := by
  refine ⟨O, fun m => ?_⟩
  by_cases hm : ∃ n, m = 2 ^ n
  · obtain ⟨n, rfl⟩ := hm
    exact hpow n
  · obtain ⟨E, hS, hq, hℓ, ha⟩ := hdef m hm
    refine ⟨E, hS, hq, hℓ, ha, fun x hx => ?_, fun x hx => ?_⟩
    · obtain ⟨n, hn⟩ := hYes _ hx
      exact absurd ⟨n, by simpa using hn⟩ hm
    · obtain ⟨n, hn⟩ := hNo _ hx
      exact absurd ⟨n, by simpa using hn⟩ hm

end OracleModel

end Cslib.Circuits.Boolean
