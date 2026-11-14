/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SIS.Basic
public import CslibFrontier.Crypto.Computational.CollisionResistant
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary.Decode
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.BinaryDiv
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.Negligible

/-!
# Ajtai's hash function and collision finding

Ajtai's function `ajtaiHash A x = A x mod q` ([Ajtai1996]) on integer vectors is linear, so two
distinct inputs with the same hash differ by a nonzero kernel vector of `A`. When both inputs lie
in `[0, β]^m` the difference is a short integer solution with bound `β`
(`IsAjtaiCollision.isSolution_sub`); when both lie in `[-β, β]^m` it is one with bound `2 * β`
(`isSolution_sub_of_abs_le`). No primality assumption on `q` is needed.

`ajtaiCollisionExperiment q β F` draws a uniform `A ∈ ℤ_q^{n×m}`, and the finder `F` wins when it
returns a collision in `[0, β]^m`. The SIS solver `collisionToSIS F` returns the difference of
`F`'s pair, and `ajtaiAdvantage_le_sisAdvantage` bounds the collision-finding advantage by its SIS
advantage for every modulus, dimension, bound and finder.

For a `SISParams` family `P`, `isPPT_collisionToSIS` proves that `collisionToSIS` preserves
uniform strict PPT on `P.encInput` and encoded integer-vector pairs (`SISParams.AjtaiFinder.IsPPT`),
yielding `ajtaiAdvantage_negligible_of_sis` under `SIS P`. Package `ajtaiSetup P`,
`ajtaiFamilyHash P` and `ajtaiFamilyValid P` (canonical `SIS.encodeVec` words representing vectors
in `[0, P.β κ]^m`) as a setup-parameterized hash family: `SIS.collisionResistantForOn_ajtai`
proves `CollisionResistantForOn` under `SIS P` when `P.m` is polynomial-time computable in unary,
and `computableInPolyTime_ajtaiFamilyValid` / `computableInPolyTime_ajtaiFamilyHash` certify
the domain test and hash evaluation.

## Main definitions

* `Cslib.Crypto.ajtaiHash`: Ajtai's linear hash function.
* `Cslib.Crypto.IsAjtaiCollision`: a collision in `[0, β]^m`.
* `Cslib.Crypto.ajtaiCollisionExperiment`, `Cslib.Crypto.ajtaiAdvantage`: the collision-finding
  experiment and its success probability.
* `Cslib.Crypto.collisionToSIS`: the SIS solver built from a collision finder.
* `Cslib.Crypto.SISParams.AjtaiFinder`, `Cslib.Crypto.SISParams.AjtaiFinder.IsPPT`: family-level
  Ajtai collision finders and their uniform strict-PPT predicate.
* `Cslib.Crypto.ajtaiSetup`, `Cslib.Crypto.ajtaiDecodeVec`, `Cslib.Crypto.ajtaiFamilyHash`,
  `Cslib.Crypto.ajtaiFamilyValid`, `Cslib.Crypto.ajtaiWordCollisionToSIS`: setup-parameterized
  Ajtai hash family over `[0, β]^m` and its word-level SIS reduction.

## Main results

* `Cslib.Crypto.IsAjtaiCollision.isSolution_sub`, `Cslib.Crypto.isSolution_sub_of_abs_le`:
  collisions give short integer solutions.
* `Cslib.Crypto.ajtaiAdvantage_le_sisAdvantage`: collision finding reduces to SIS.
* `Cslib.Crypto.isPPT_collisionToSIS`, `Cslib.Crypto.ajtaiAdvantage_negligible_of_sis`:
  `collisionToSIS` preserves uniform strict PPT and yields negligible collision advantage under
  `SIS P`.
* `Cslib.Crypto.computableInPolyTime_ajtaiFamilyValid`,
  `Cslib.Crypto.computableInPolyTime_ajtaiFamilyHash`: deterministic polynomial-time
  recognizability of valid inputs and hash evaluation.
* `Cslib.Crypto.collisionGameFor_ajtai_le_sisAdvantage`,
  `Cslib.Crypto.isPPT_ajtaiWordCollisionToSIS`,
  `Cslib.Crypto.SIS.collisionResistantForOn_ajtai`: `CollisionResistantForOn` for Ajtai's hash
  family under `SIS P`.

## References

* [M. Ajtai, *Generating Hard Instances of Lattice Problems*][Ajtai1996]
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 8.1.1 (Definition 8.2, pp. 290–291)
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped _root_.Matrix NNReal

variable {n m q : ℕ}

/-- Ajtai's linear hash function `x ↦ A x mod q` on integer vectors ([Ajtai1996]). -/
@[expose] def ajtaiHash (A : Matrix (Fin n) (Fin m) (ZMod q)) (x : Fin m → ℤ) : Fin n → ZMod q :=
  A *ᵥ (Int.cast ∘ x)

/-- Ajtai's hash function is additive. -/
theorem ajtaiHash_sub (A : Matrix (Fin n) (Fin m) (ZMod q)) (x y : Fin m → ℤ) :
    ajtaiHash A (x - y) = ajtaiHash A x - ajtaiHash A y := by
  rw [ajtaiHash, ajtaiHash, ajtaiHash, ← Matrix.mulVec_sub]
  congr 1
  funext i
  exact Int.cast_sub (x i) (y i)

/-- Distinct inputs in `[-β, β]^m` with the same Ajtai hash differ by a short integer solution
with bound `2 * β`. -/
theorem isSolution_sub_of_abs_le {A : Matrix (Fin n) (Fin m) (ZMod q)} {β : ℕ}
    {x y : Fin m → ℤ} (hxy : x ≠ y) (hx : ∀ i, |x i| ≤ β) (hy : ∀ i, |y i| ≤ β)
    (h : ajtaiHash A x = ajtaiHash A y) :
    SIS.IsSolution A (2 * β) (x - y) := by
  refine ⟨sub_ne_zero.mpr hxy, fun i => ?_, ?_⟩
  · have hxi := abs_le.mp (hx i)
    have hyi := abs_le.mp (hy i)
    simp only [Pi.sub_apply, Nat.cast_mul, Nat.cast_ofNat, abs_le]
    omega
  · change ajtaiHash A (x - y) = 0
    rw [ajtaiHash_sub, h, sub_self]

/-- `(x, y)` is a collision of Ajtai's hash function for `A` in `[0, β]^m`: distinct inputs in
`[0, β]^m` with the same hash. -/
@[expose] def IsAjtaiCollision (A : Matrix (Fin n) (Fin m) (ZMod q)) (β : ℕ) (x y : Fin m → ℤ) :
    Prop :=
  x ≠ y ∧ (∀ i, 0 ≤ x i ∧ x i ≤ β) ∧ (∀ i, 0 ≤ y i ∧ y i ≤ β) ∧
    ajtaiHash A x = ajtaiHash A y

instance (A : Matrix (Fin n) (Fin m) (ZMod q)) (β : ℕ) (x y : Fin m → ℤ) :
    Decidable (IsAjtaiCollision A β x y) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- A collision in `[0, β]^m` differs by a short integer solution with bound `β`. -/
theorem IsAjtaiCollision.isSolution_sub {A : Matrix (Fin n) (Fin m) (ZMod q)} {β : ℕ}
    {x y : Fin m → ℤ} (h : IsAjtaiCollision A β x y) : SIS.IsSolution A β (x - y) := by
  obtain ⟨hxy, hx, hy, hxy'⟩ := h
  refine ⟨sub_ne_zero.mpr hxy, fun i => ?_, ?_⟩
  · have hxi := hx i
    have hyi := hy i
    simp only [Pi.sub_apply, abs_le]
    omega
  · change ajtaiHash A (x - y) = 0
    rw [ajtaiHash_sub, hxy', sub_self]

/-- The SIS solver built from a collision finder: run the finder and return the difference of
its pair. -/
@[expose] def collisionToSIS
    (F : Matrix (Fin n) (Fin m) (ZMod q) → ProbComp ((Fin m → ℤ) × (Fin m → ℤ)))
    (A : Matrix (Fin n) (Fin m) (ZMod q)) : ProbComp (Fin m → ℤ) := do
  let (x, y) ← F A
  return x - y

section Experiment

variable (q) [NeZero q]

/-- The Ajtai collision-finding experiment for modulus `q`, dimensions `n × m` and box
`[0, β]^m`: the challenger draws a uniform `A ∈ ℤ_q^{n×m}`; the finder wins when it returns a
collision of `ajtaiHash A` in the box. -/
@[expose] noncomputable def ajtaiCollisionExperiment (β : ℕ)
    (F : Matrix (Fin n) (Fin m) (ZMod q) → ProbComp ((Fin m → ℤ) × (Fin m → ℤ))) :
    ProbComp Bool := do
  let A ← ProbComp.uniform (Matrix (Fin n) (Fin m) (ZMod q))
  let (x, y) ← F A
  return decide (IsAjtaiCollision A β x y)

/-- The collision-finding advantage of `F`: its success probability in
`ajtaiCollisionExperiment`. -/
@[expose] noncomputable def ajtaiAdvantage (β : ℕ)
    (F : Matrix (Fin n) (Fin m) (ZMod q) → ProbComp ((Fin m → ℤ) × (Fin m → ℤ))) : ℝ≥0 :=
  Game.succProbability (ProbComp.eval (ajtaiCollisionExperiment q β F))

/-- **Collision finding reduces to SIS** ([Ajtai1996]): every collision finder's advantage is at
most the SIS advantage of `collisionToSIS`, for every nonzero modulus. -/
theorem ajtaiAdvantage_le_sisAdvantage (β : ℕ)
    (F : Matrix (Fin n) (Fin m) (ZMod q) → ProbComp ((Fin m → ℤ) × (Fin m → ℤ))) :
    ajtaiAdvantage q β F ≤ sisAdvantage q β (collisionToSIS F) := by
  refine ENNReal.toNNReal_mono (PMF.apply_ne_top _ _) ?_
  simp only [ajtaiCollisionExperiment, sisExperiment, collisionToSIS, bind_assoc,
    ProbComp.eval_bind]
  refine PMF.bind_apply_mono_on_support _ _ fun A _ => ?_
  refine PMF.bind_apply_mono_on_support _ _ fun ⟨x, y⟩ _ => ?_
  by_cases h : IsAjtaiCollision A β x y
  · simp [h, h.isSolution_sub]
  · simp [h]

end Experiment

/-! ### Asymptotic efficiency and `CollisionResistantForOn` under `SIS` -/

/-- A collision finder for Ajtai's hash function across the `SISParams` family `P`: given security
parameter `κ` and matrix `A ∈ ℤ_q^{n×m}`, output a pair `(x, y)` of integer vectors in
`(Fin (P.m κ) → ℤ)^2`. -/
abbrev SISParams.AjtaiFinder (P : SISParams) : Type :=
  ∀ κ, Matrix (Fin (P.n κ)) (Fin (P.m κ)) (ZMod (P.q κ)) →
    ProbComp ((Fin (P.m κ) → ℤ) × (Fin (P.m κ) → ℤ))

/-- Uniform strict PPT admissibility for an `AjtaiFinder` on `P.encInput` and the encoded pair of
output integer vectors. -/
@[expose] def SISParams.AjtaiFinder.IsPPT {P : SISParams} (F : P.AjtaiFinder) : Prop :=
  IsPPTOn P.encInput (encPair encBits encBits)
    fun x => (fun p => (SIS.encodeVec p.1, SIS.encodeVec p.2)) <$> F x.secParam x.matrix

private def subDecodedIntLists (w : List Bool × List Bool) : List Bool :=
  let l₁ := (Decoder.list Decoder.intBin).decode w.1
  let l₂ := (Decoder.list Decoder.intBin).decode w.2
  encList encIntBin ((l₁.zip l₂).map fun p => p.1 - p.2)

private theorem subDecodedIntLists_encodeVec {m : ℕ} (u v : Fin m → ℤ) :
    subDecodedIntLists (SIS.encodeVec u, SIS.encodeVec v) = SIS.encodeVec (u - v) := by
  simp only [subDecodedIntLists, SIS.encodeVec, (Decoder.list Decoder.intBin).decode_enc]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi _
    simp only [List.length_map, List.length_zip, List.length_ofFn, min_self] at hi
    simp only [List.getElem_map, List.getElem_zip, List.getElem_ofFn, Pi.sub_apply]

private theorem computableInPolyTime_subDecodedIntLists :
    ComputableInPolyTime subDecodedIntLists (encPair encBits encBits) encBits := by
  let dec := Decoder.list Decoder.intBin
  have hdec₁ : ComputableInPolyTime (fun w : List Bool × List Bool => dec.decode w.1)
      (encPair encBits encBits) (encList encIntBin) :=
    dec.computableInPolyTime.comp (ComputableInPolyTime.fst encBits encBits)
  have hdec₂ : ComputableInPolyTime (fun w : List Bool × List Bool => dec.decode w.2)
      (encPair encBits encBits) (encList encIntBin) :=
    dec.computableInPolyTime.comp (ComputableInPolyTime.snd encBits encBits)
  have hzip := (ComputableInPolyTime.zip encIntBin encIntBin).comp (hdec₁.prod hdec₂)
  have hmap : ComputableInPolyTime
      (List.map (fun p : ℤ × ℤ => p.1 - p.2))
      (encList (encPair encIntBin encIntBin)) (encList encIntBin) :=
    .of_tidy (ComputableTidilyInPolyTime.map ComputableInPolyTime.intBin_sub.tidy)
  exact (ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.encode (encList encIntBin))).comp (hmap.comp hzip)

/-- `collisionToSIS` preserves uniform strict PPT across any `SISParams` family, without extra
hypotheses on `P`. -/
theorem isPPT_collisionToSIS (P : SISParams) {F : P.AjtaiFinder} (hF : F.IsPPT) :
    SISParams.Solver.IsPPT (P := P) (fun κ => collisionToSIS (F κ)) := by
  have hmap := hF.map computableInPolyTime_subDecodedIntLists
  refine hmap.congr fun x => ?_
  simp only [collisionToSIS, bind_pure_comp, Functor.map_map, subDecodedIntLists_encodeVec]

/-- Under `SIS P`, every uniform strict PPT `AjtaiFinder` has negligible collision-finding
advantage. -/
theorem ajtaiAdvantage_negligible_of_sis (P : SISParams) (hSIS : SIS P) {F : P.AjtaiFinder}
    (hF : F.IsPPT) :
    Negligible fun κ => ajtaiAdvantage (P.q κ) (P.β κ) (F κ) :=
  negligible_of_le (hSIS _ (isPPT_collisionToSIS P hF))
    fun κ => ajtaiAdvantage_le_sisAdvantage (P.q κ) (P.β κ) (F κ)

/-- Public setup distribution for Ajtai's hash family at parameter `P`: draw a uniform matrix
`A ∈ ℤ_q^{n×m}` and bundle it with `κ`. -/
@[expose] noncomputable def ajtaiSetup (P : SISParams) (κ : ℕ) : PMF P.Input :=
  (ProbComp.eval (ProbComp.uniform (Matrix (Fin (P.n κ)) (Fin (P.m κ)) (ZMod (P.q κ))))).map
    fun A => ⟨κ, A⟩

/-- Total vector decoder from a `List Bool` to `Fin m → ℤ`, padding short lists with zero. -/
@[expose] def ajtaiDecodeVec (m : ℕ) (w : List Bool) : Fin m → ℤ :=
  let l := (Decoder.list Decoder.intBin).decode w
  fun i => l.getD i.val 0

@[simp] theorem ajtaiDecodeVec_encodeVec {m : ℕ} (x : Fin m → ℤ) :
    ajtaiDecodeVec m (SIS.encodeVec x) = x := by
  ext i
  simp only [ajtaiDecodeVec, SIS.encodeVec, (Decoder.list Decoder.intBin).decode_enc,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some,
    Fin.eta]

/-- Word-level Ajtai hash function indexed by `d : P.Input` (`x ↦ A x mod q` on the decoded
vector `ajtaiDecodeVec (P.m d.secParam) w`). -/
@[expose] def ajtaiFamilyHash (P : SISParams) (d : P.Input) (w : List Bool) :
    Fin (P.n d.secParam) → ZMod (P.q d.secParam) :=
  ajtaiHash d.matrix (ajtaiDecodeVec (P.m d.secParam) w)

@[simp] theorem ajtaiFamilyHash_encodeVec (P : SISParams) (d : P.Input)
    (x : Fin (P.m d.secParam) → ℤ) :
    ajtaiFamilyHash P d (SIS.encodeVec x) = ajtaiHash d.matrix x := by
  simp only [ajtaiFamilyHash, ajtaiDecodeVec_encodeVec]

/-- Valid input words for Ajtai's hash function at security parameter `κ` and `d : P.Input`:
`d.secParam = κ` and `w` is the canonical `SIS.encodeVec` of a vector in `[0, P.β κ]^m`. -/
@[expose] def ajtaiFamilyValid (P : SISParams) (κ : ℕ) (d : P.Input) (w : List Bool) : Bool :=
  let l := (Decoder.list Decoder.intBin).decode w
  decide (d.secParam = κ) &&
  decide (l.length = P.m d.secParam) &&
  decide (w = encList encIntBin l) &&
  l.all fun z => decide (0 ≤ z) && decide (z ≤ P.β d.secParam)

theorem ajtaiFamilyValid_eq_true_iff (P : SISParams) (κ : ℕ) (d : P.Input) (w : List Bool) :
    ajtaiFamilyValid P κ d w = true ↔
      d.secParam = κ ∧
        ∃ x : Fin (P.m d.secParam) → ℤ,
          w = SIS.encodeVec x ∧ ∀ i, 0 ≤ x i ∧ x i ≤ P.β d.secParam := by
  simp only [ajtaiFamilyValid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, and_assoc]
  constructor
  · rintro ⟨rfl, hlen, hw, hbounds⟩
    refine ⟨rfl, fun i => ((Decoder.list Decoder.intBin).decode w)[i.val]'(by omega), ?_, ?_⟩
    · conv_lhs => rw [hw]
      congr 1
      apply List.ext_getElem (by simp [hlen])
      intro j hj _
      simp only [List.getElem_ofFn]
    · intro i
      exact hbounds _ (List.getElem_mem (by omega))
  · rintro ⟨rfl, x, rfl, hx⟩
    refine ⟨rfl, ?_, ?_, ?_⟩
    · simp only [SIS.encodeVec, (Decoder.list Decoder.intBin).decode_enc, List.length_ofFn]
    · simp only [SIS.encodeVec, (Decoder.list Decoder.intBin).decode_enc]
    · intro z hz
      simp only [SIS.encodeVec, (Decoder.list Decoder.intBin).decode_enc, List.mem_ofFn] at hz
      obtain ⟨i, rfl⟩ := hz
      exact hx i

theorem ajtaiFamilyValid_encodeVec {P : SISParams} {κ : ℕ}
    (A : Matrix (Fin (P.n κ)) (Fin (P.m κ)) (ZMod (P.q κ)))
    {x : Fin (P.m κ) → ℤ} (hx : ∀ i, 0 ≤ x i ∧ x i ≤ P.β κ) :
    ajtaiFamilyValid P κ ⟨κ, A⟩ (SIS.encodeVec x) = true :=
  (ajtaiFamilyValid_eq_true_iff P κ ⟨κ, A⟩ (SIS.encodeVec x)).mpr ⟨rfl, x, rfl, hx⟩

theorem isAjtaiCollision_of_isCollisionFor_ajtai {P : SISParams} {κ : ℕ}
    {A : Matrix (Fin (P.n κ)) (Fin (P.m κ)) (ZMod (P.q κ))} {w₁ w₂ : List Bool}
    (hcol : isCollisionFor (ajtaiFamilyHash P) (ajtaiFamilyValid P) κ ⟨κ, A⟩ w₁ w₂ = true) :
    IsAjtaiCollision A (P.β κ)
      (ajtaiDecodeVec (P.m κ) w₁) (ajtaiDecodeVec (P.m κ) w₂) := by
  rw [isCollisionFor_eq_true_iff] at hcol
  obtain ⟨hv₁, hv₂, hne, hH⟩ := hcol
  rw [ajtaiFamilyValid_eq_true_iff] at hv₁ hv₂
  obtain ⟨_, x₁, rfl, hx₁⟩ := hv₁
  obtain ⟨_, x₂, rfl, hx₂⟩ := hv₂
  simp only [ajtaiDecodeVec_encodeVec, ajtaiFamilyHash_encodeVec] at hH ⊢
  exact ⟨fun h => hne (congrArg SIS.encodeVec h), hx₁, hx₂, hH⟩

/-- Valid inputs for `ajtaiFamilyValid P` are recognizable in deterministic polynomial time when
`P.m` and `P.β` are computable in polynomial time. -/
theorem computableInPolyTime_ajtaiFamilyValid (P : SISParams)
    (hm : ComputableInPolyTime P.m encUnary encUnary)
    (hβ : ComputableInPolyTime P.β encUnary encNat) :
    ComputableInPolyTime (fun ((κ, d), w) => ajtaiFamilyValid P κ d w)
      (encPair (encPair encUnary P.encInput) encBits) encBool := by
  let E := encPair (encPair encUnary P.encInput) encBits
  have hκ : ComputableInPolyTime (fun p : (ℕ × P.Input) × List Bool => p.1.1) E encUnary := by
    fun_prop
  have hd : ComputableInPolyTime (fun p : (ℕ × P.Input) × List Bool => p.1.2) E P.encInput := by
    fun_prop
  have hw : ComputableInPolyTime (fun p : (ℕ × P.Input) × List Bool => p.2) E encBits := by
    fun_prop
  have hinputWords : ComputableInPolyTime
      (fun x : P.Input => (x.secParam, SIS.encodeMatrix x.matrix))
      P.encInput (encPair encUnary encBits) :=
    ComputableInPolyTime.of_eq fun _ => rfl
  have hdSec : ComputableInPolyTime (fun p : (ℕ × P.Input) × List Bool => p.1.2.secParam) E
      encUnary :=
    ((ComputableInPolyTime.fst encUnary encBits).comp hinputWords).comp hd
  have hl : ComputableInPolyTime
      (fun p : (ℕ × P.Input) × List Bool => (Decoder.list Decoder.intBin).decode p.2)
      E (encList encIntBin) :=
    (Decoder.list Decoder.intBin).computableInPolyTime.comp hw
  have h1 : ComputableInPolyTime
      (fun p : (ℕ × P.Input) × List Bool => decide (p.1.2.secParam = p.1.1)) E encBool :=
    (ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.decide_eq encUnary)).comp
      (hdSec.prod hκ)
  have h2 : ComputableInPolyTime
      (fun p : (ℕ × P.Input) × List Bool =>
        decide (((Decoder.list Decoder.intBin).decode p.2).length = P.m p.1.2.secParam))
      E encBool :=
    (ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.decide_eq encUnary)).comp
      (((ComputableInPolyTime.length_list encIntBin).comp hl).prod (hm.comp hdSec))
  have hw_reenc : ComputableInPolyTime
      (fun p : (ℕ × P.Input) × List Bool =>
        encList encIntBin ((Decoder.list Decoder.intBin).decode p.2))
      E encBits :=
    (ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.encode (encList encIntBin))).comp hl
  have h3 : ComputableInPolyTime
      (fun p : (ℕ × P.Input) × List Bool =>
        decide (p.2 = encList encIntBin ((Decoder.list Decoder.intBin).decode p.2)))
      E encBool :=
    (ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.decide_eq encBits)).comp
      (hw.prod hw_reenc)
  have hβ_cast : ComputableInPolyTime
      (fun p : (ℕ × P.Input) × List Bool => (P.β p.1.2.secParam : ℤ)) E encIntBin :=
    ComputableInPolyTime.intBin_natCast.comp (hβ.comp hdSec)
  have hElem : ComputableInPolyTime
      (fun p : ((ℕ × P.Input) × List Bool) × ℤ =>
        decide (0 ≤ p.2) && decide (p.2 ≤ (P.β p.1.1.2.secParam : ℤ)))
      (encPair E encIntBin) encBool := by
    have hz : ComputableInPolyTime (fun p : ((ℕ × P.Input) × List Bool) × ℤ => p.2)
        (encPair E encIntBin) encIntBin := by fun_prop
    have hlow : ComputableInPolyTime (fun p : ((ℕ × P.Input) × List Bool) × ℤ => decide (0 ≤ p.2))
        (encPair E encIntBin) encBool :=
      ComputableInPolyTime.intBin_le.comp ((ComputableInPolyTime.const (0 : ℤ)).prod hz)
    have hhi : ComputableInPolyTime
        (fun p : ((ℕ × P.Input) × List Bool) × ℤ => decide (p.2 ≤ (P.β p.1.1.2.secParam : ℤ)))
        (encPair E encIntBin) encBool :=
      ComputableInPolyTime.intBin_le.comp
        (hz.prod (hβ_cast.comp (ComputableInPolyTime.fst E encIntBin)))
    exact ComputableInPolyTime.bool_and.comp (hlow.prod hhi)
  have h4 : ComputableInPolyTime
      (fun p : (ℕ × P.Input) × List Bool =>
        ((Decoder.list Decoder.intBin).decode p.2).all fun z =>
          decide (0 ≤ z) && decide (z ≤ P.β p.1.2.secParam))
      E encBool :=
    .of_tidy (ComputableTidilyInPolyTime.allWithInput hl.tidy hElem.tidy)
  unfold ajtaiFamilyValid
  have h12 := ComputableInPolyTime.bool_and.comp (h1.prod h2)
  have h123 := ComputableInPolyTime.bool_and.comp (h12.prod h3)
  exact ComputableInPolyTime.bool_and.comp (h123.prod h4)

private theorem ajtaiRowDot_eq {m q : ℕ} [NeZero q] (rowVec : Fin m → ZMod q)
    (w : List Bool) :
    ((∑ j : Fin m, rowVec j * ((ajtaiDecodeVec m w j : ℤ) : ZMod q)).val : ℤ) =
      (((List.ofFn fun j : Fin m => (rowVec j).val).zip
        ((Decoder.list Decoder.intBin).decode w)).map
          (fun p : ℕ × ℤ => (p.1 : ℤ) * p.2)).sum % (q : ℤ) := by
  let l := (Decoder.list Decoder.intBin).decode w
  let row := List.ofFn fun j : Fin m => (rowVec j).val
  have hcast : ∑ j : Fin m, rowVec j * ((ajtaiDecodeVec m w j : ℤ) : ZMod q) =
      ((∑ j : Fin m, ((rowVec j).val : ℤ) * ajtaiDecodeVec m w j : ℤ) : ZMod q) := by
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    simp
  rw [hcast, ZMod.val_intCast]
  congr 1
  have hlist :
      ((row.zip l).map fun p : ℕ × ℤ => (p.1 : ℤ) * p.2) =
        List.ofFn fun i : Fin (min m l.length) =>
          ((rowVec ⟨i.val, lt_of_lt_of_le i.isLt (min_le_left _ _)⟩).val : ℤ) *
            l.getD i.val 0 := by
    apply List.ext_getElem
    · simp [row]
    · intro i hi _
      have him : i < m := by simp [row] at hi; omega
      have hil : i < l.length := by simp [row] at hi; omega
      simp only [List.getElem_map, List.getElem_zip, List.getElem_ofFn, row,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hil, Option.getD_some]
  rw [hlist, List.sum_ofFn]
  unfold ajtaiDecodeVec
  let c (j : ℕ) : ℤ := if hj : j < m then ((rowVec ⟨j, hj⟩).val : ℤ) * l.getD j 0 else 0
  have h1 :
      (∑ j : Fin m,
          ((rowVec j).val : ℤ) * ((Decoder.list Decoder.intBin).decode w).getD j.val 0) =
        ∑ j : Fin m, c j.val :=
    Finset.sum_congr rfl fun j _ => by
      simp only [c, j.isLt, ↓reduceDIte, Fin.eta]
      rfl
  have h2 :
      (∑ i : Fin (min m l.length),
          ((rowVec ⟨i.val, lt_of_lt_of_le i.isLt (min_le_left _ _)⟩).val : ℤ) * l.getD i.val 0) =
        ∑ i : Fin (min m l.length), c i.val :=
    Finset.sum_congr rfl fun i _ => by
      simp only [c, lt_of_lt_of_le i.isLt (min_le_left _ _), ↓reduceDIte]
  rw [h1, h2, Finset.sum_fin_eq_sum_range (fun j : Fin m => c j.val),
    Finset.sum_fin_eq_sum_range (fun i : Fin (min m l.length) => c i.val)]
  have hlhs :
      (∑ j ∈ Finset.range m, if hj : j < m then c (⟨j, hj⟩ : Fin m).val else 0) =
        ∑ j ∈ Finset.range m, c j :=
    Finset.sum_congr rfl fun j hj => by
      simp only [Finset.mem_range] at hj
      simp only [hj, ↓reduceDIte]
  have hrhs :
      (∑ i ∈ Finset.range (min m l.length),
          if hi : i < min m l.length then c (⟨i, hi⟩ : Fin (min m l.length)).val else 0) =
        ∑ i ∈ Finset.range (min m l.length), c i :=
    Finset.sum_congr rfl fun i hi => by
      simp only [Finset.mem_range] at hi
      simp only [hi, ↓reduceDIte]
  rw [hlhs, hrhs]
  refine (Finset.sum_subset (Finset.range_mono (min_le_left m l.length)) ?_).symm
  intro j hj hnot
  simp only [Finset.mem_range] at hj hnot
  have hlen : l.length ≤ j := by omega
  simp only [c, hj, ↓reduceDIte, List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen,
    Option.getD_none, mul_zero]

/-- Evaluating `ajtaiFamilyHash` (returning the canonical residue coordinates in `[0, P.q κ)`)
is deterministic polynomial time when `P.q` is computable in polynomial time. -/
theorem computableInPolyTime_ajtaiFamilyHash (P : SISParams)
    (hq : ComputableInPolyTime P.q encUnary encNat) :
    ComputableInPolyTime
      (fun (d, w) => List.ofFn fun i : Fin (P.n d.secParam) => (ajtaiFamilyHash P d w i).val)
      (encPair P.encInput encBits) (encList encNat) := by
  let E := encPair P.encInput encBits
  have hd : ComputableInPolyTime (fun p : P.Input × List Bool => p.1) E P.encInput := by
    fun_prop
  have hw : ComputableInPolyTime (fun p : P.Input × List Bool => p.2) E encBits := by
    fun_prop
  have hinputWords : ComputableInPolyTime
      (fun x : P.Input => (x.secParam, SIS.encodeMatrix x.matrix))
      P.encInput (encPair encUnary encBits) :=
    ComputableInPolyTime.of_eq fun _ => rfl
  have hdSec : ComputableInPolyTime (fun p : P.Input × List Bool => p.1.secParam) E encUnary :=
    ((ComputableInPolyTime.fst encUnary encBits).comp hinputWords).comp hd
  have hmatWord : ComputableInPolyTime
      (fun p : P.Input × List Bool => SIS.encodeMatrix p.1.matrix) E encBits :=
    ((ComputableInPolyTime.snd encUnary encBits).comp hinputWords).comp hd
  have hrows : ComputableInPolyTime
      (fun p : P.Input × List Bool =>
        (Decoder.list (Decoder.list Decoder.nat)).decode (SIS.encodeMatrix p.1.matrix))
      E (encList (encList encNat)) :=
    (Decoder.list (Decoder.list Decoder.nat)).computableInPolyTime.comp hmatWord
  have hqVal : ComputableInPolyTime (fun p : P.Input × List Bool => P.q p.1.secParam) E encNat :=
    hq.comp hdSec
  have hl : ComputableInPolyTime
      (fun p : P.Input × List Bool => (Decoder.list Decoder.intBin).decode p.2)
      E (encList encIntBin) :=
    (Decoder.list Decoder.intBin).computableInPolyTime.comp hw
  have hpar : ComputableInPolyTime
      (fun p : P.Input × List Bool =>
        (P.q p.1.secParam, (Decoder.list Decoder.intBin).decode p.2))
      E (encPair encNat (encList encIntBin)) :=
    hqVal.prod hl
  have hrowEval : ComputableInPolyTime
      (fun p : (ℕ × List ℤ) × List ℕ =>
        ((((p.2.zip p.1.2).map fun q : ℕ × ℤ => (q.1 : ℤ) * q.2).sum) % (p.1.1 : ℤ)).toNat)
      (encPair (encPair encNat (encList encIntBin)) (encList encNat)) encNat := by
    let Erow := encPair (encPair encNat (encList encIntBin)) (encList encNat)
    have hq' : ComputableInPolyTime (fun p : (ℕ × List ℤ) × List ℕ => p.1.1) Erow encNat := by
      fun_prop
    have hl' : ComputableInPolyTime (fun p : (ℕ × List ℤ) × List ℕ => p.1.2)
        Erow (encList encIntBin) := by
      fun_prop
    have hr' : ComputableInPolyTime (fun p : (ℕ × List ℤ) × List ℕ => p.2)
        Erow (encList encNat) := by
      fun_prop
    have hzip := (ComputableInPolyTime.zip encNat encIntBin).comp (hr'.prod hl')
    have hmul : ComputableInPolyTime (fun q : ℕ × ℤ => (q.1 : ℤ) * q.2)
        (encPair encNat encIntBin) encIntBin :=
      ComputableInPolyTime.intBin_mul.comp
        ((ComputableInPolyTime.intBin_natCast.comp (ComputableInPolyTime.fst _ _)).prod
          (ComputableInPolyTime.snd _ _))
    have hmap : ComputableInPolyTime (List.map fun q : ℕ × ℤ => (q.1 : ℤ) * q.2)
        (encList (encPair encNat encIntBin)) (encList encIntBin) :=
      .of_tidy (ComputableTidilyInPolyTime.map hmul.tidy)
    have hsum : ComputableInPolyTime
        (fun p : (ℕ × List ℤ) × List ℕ =>
          ((p.2.zip p.1.2).map fun q : ℕ × ℤ => (q.1 : ℤ) * q.2).sum)
        Erow encIntBin :=
      ComputableInPolyTime.intBin_sum.comp (hmap.comp hzip)
    exact ComputableInPolyTime.intBin_emodNat' hsum hq'
  have hcomp : ComputableInPolyTime
      (fun p : P.Input × List Bool =>
        ((Decoder.list (Decoder.list Decoder.nat)).decode (SIS.encodeMatrix p.1.matrix)).map
          fun row => ((((row.zip ((Decoder.list Decoder.intBin).decode p.2)).map
            fun q : ℕ × ℤ => (q.1 : ℤ) * q.2).sum) % (P.q p.1.secParam : ℤ)).toNat)
      E (encList encNat) :=
    .of_tidy (ComputableTidilyInPolyTime.mapWith hrowEval.tidy hpar.tidy hrows.tidy)
  refine hcomp.of_enc_eq fun ⟨d, w⟩ => congrArg (encList encNat) ?_
  have hdecRows :
      (Decoder.list (Decoder.list Decoder.nat)).decode (SIS.encodeMatrix d.matrix) =
        List.ofFn fun i : Fin (P.n d.secParam) =>
          List.ofFn fun j : Fin (P.m d.secParam) => (d.matrix i j).val := by
    simp only [SIS.encodeMatrix, (Decoder.list (Decoder.list Decoder.nat)).decode_enc]
  dsimp only
  rw [hdecRows, List.map_ofFn]
  congr 1
  funext i
  have hi := ajtaiRowDot_eq (d.matrix i) w
  have heq : (ajtaiFamilyHash P d w i).val =
      ((((List.ofFn fun j : Fin (P.m d.secParam) => (d.matrix i j).val).zip
        ((Decoder.list Decoder.intBin).decode w)).map
          fun q : ℕ × ℤ => (q.1 : ℤ) * q.2).sum % (P.q d.secParam : ℤ)).toNat := by
    have hnonneg :
        0 ≤ (((List.ofFn fun j : Fin (P.m d.secParam) => (d.matrix i j).val).zip
          ((Decoder.list Decoder.intBin).decode w)).map
            fun q : ℕ × ℤ => (q.1 : ℤ) * q.2).sum % (P.q d.secParam : ℤ) :=
      Int.emod_nonneg _ (Nat.cast_ne_zero.mpr (P.hq d.secParam).ne)
    change ((∑ j : Fin (P.m d.secParam),
      d.matrix i j * ((ajtaiDecodeVec (P.m d.secParam) w j : ℤ) : ZMod (P.q d.secParam))).val) = _
    omega
  exact heq

/-- Word-level SIS solver constructed from a setup-parameterized collision finder `F`. -/
def ajtaiWordCollisionToSIS (P : SISParams) (F : CollisionFinderFor P.Input) : P.Solver :=
  fun κ A => do
    let (w₁, w₂) ← F κ ⟨κ, A⟩
    let l₁ := (Decoder.list Decoder.intBin).decode w₁
    let l₂ := (Decoder.list Decoder.intBin).decode w₂
    return fun i =>
      if l₁.length = P.m κ ∧ l₂.length = P.m κ then
        l₁.getD i.val 0 - l₂.getD i.val 0
      else
        0

/-- Any collision found by `F` in `collisionGameFor (ajtaiSetup P) (ajtaiFamilyHash P)
(ajtaiFamilyValid P)` yields a SIS solution for `ajtaiWordCollisionToSIS P F`. -/
theorem collisionGameFor_ajtai_le_sisAdvantage (P : SISParams) (F : CollisionFinderFor P.Input)
    (κ : ℕ) :
    Game.succProbability
      (collisionGameFor (ajtaiSetup P) (ajtaiFamilyHash P) (ajtaiFamilyValid P) F κ) ≤
      sisAdvantage (P.q κ) (P.β κ) (ajtaiWordCollisionToSIS P F κ) := by
  refine ENNReal.toNNReal_mono (PMF.apply_ne_top _ _) ?_
  simp only [collisionGameFor, Game.withSetup, collisionExperiment, ajtaiSetup,
    sisExperiment, ajtaiWordCollisionToSIS, bind_assoc, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.bind_map, Function.comp_def]
  refine PMF.bind_apply_mono_on_support _ _ fun A _ => ?_
  refine PMF.bind_apply_mono_on_support _ _ fun ⟨w₁, w₂⟩ _ => ?_
  by_cases hcol : isCollisionFor (ajtaiFamilyHash P) (ajtaiFamilyValid P) κ ⟨κ, A⟩ w₁ w₂ = true
  · have hAjtai := isAjtaiCollision_of_isCollisionFor_ajtai hcol
    have hsol := hAjtai.isSolution_sub
    have hcol' := hcol
    rw [isCollisionFor_eq_true_iff] at hcol'
    have hlen₁ : ((Decoder.list Decoder.intBin).decode w₁).length = P.m κ := by
      have hv₁ := hcol'.1
      simp only [ajtaiFamilyValid, Bool.and_eq_true, decide_eq_true_eq] at hv₁
      exact hv₁.1.1.2
    have hlen₂ : ((Decoder.list Decoder.intBin).decode w₂).length = P.m κ := by
      have hv₂ := hcol'.2.1
      simp only [ajtaiFamilyValid, Bool.and_eq_true, decide_eq_true_eq] at hv₂
      exact hv₂.1.1.2
    have hvec :
        (fun i : Fin (P.m κ) =>
          if ((Decoder.list Decoder.intBin).decode w₁).length = P.m κ ∧
              ((Decoder.list Decoder.intBin).decode w₂).length = P.m κ then
            ((Decoder.list Decoder.intBin).decode w₁).getD i.val 0 -
              ((Decoder.list Decoder.intBin).decode w₂).getD i.val 0
          else 0) =
          ajtaiDecodeVec (P.m κ) w₁ - ajtaiDecodeVec (P.m κ) w₂ := by
      ext i
      simp [hlen₁, hlen₂, ajtaiDecodeVec]
    simp only [hcol, PMF.pure_bind, hvec, decide_eq_true hsol, PMF.pure_apply, ↓reduceIte,
      le_refl]
  · simp only [Bool.eq_false_iff.mpr hcol, PMF.pure_apply, Bool.true_eq_false, ↓reduceIte, zero_le]

private def wordPairToSISVec (m : ℕ) (w : List Bool × List Bool) : List Bool :=
  let l₁ := (Decoder.list Decoder.intBin).decode w.1
  let l₂ := (Decoder.list Decoder.intBin).decode w.2
  encList encIntBin
    (if l₁.length = m ∧ l₂.length = m then
      (l₁.zip l₂).map fun p => p.1 - p.2
    else
      List.replicate m 0)

private theorem wordPairToSISVec_eq_encodeVec {m : ℕ} (w : List Bool × List Bool) :
    wordPairToSISVec m w =
      SIS.encodeVec fun i : Fin m =>
        if ((Decoder.list Decoder.intBin).decode w.1).length = m ∧
            ((Decoder.list Decoder.intBin).decode w.2).length = m then
          ((Decoder.list Decoder.intBin).decode w.1).getD i.val 0 -
            ((Decoder.list Decoder.intBin).decode w.2).getD i.val 0
        else 0 := by
  simp only [wordPairToSISVec, SIS.encodeVec]
  congr 1
  split_ifs with h
  · apply List.ext_getElem
    · simp [h.1, h.2]
    · intro i hi _
      have hi₁ : i < ((Decoder.list Decoder.intBin).decode w.1).length := by
        simp only [List.length_map, List.length_zip, h.1, h.2, min_self] at hi
        omega
      have hi₂ : i < ((Decoder.list Decoder.intBin).decode w.2).length := by
        simp only [List.length_map, List.length_zip, h.1, h.2, min_self] at hi
        omega
      simp only [List.getElem_map, List.getElem_zip, List.getElem_ofFn,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi₁, List.getElem?_eq_getElem hi₂,
        Option.getD_some]
  · apply List.ext_getElem <;> simp

private theorem computableInPolyTime_wordPairToSISVec :
    ComputableInPolyTime (fun p : ℕ × (List Bool × List Bool) => wordPairToSISVec p.1 p.2)
      (encPair encUnary (encPair encBits encBits)) encBits := by
  let E := encPair encUnary (encPair encBits encBits)
  let dec := Decoder.list Decoder.intBin
  have hm : ComputableInPolyTime (fun p : ℕ × (List Bool × List Bool) => p.1) E encUnary := by
    fun_prop
  have hw₁ : ComputableInPolyTime (fun p : ℕ × (List Bool × List Bool) => p.2.1) E encBits := by
    fun_prop
  have hw₂ : ComputableInPolyTime (fun p : ℕ × (List Bool × List Bool) => p.2.2) E encBits := by
    fun_prop
  have hl₁ : ComputableInPolyTime (fun p : ℕ × (List Bool × List Bool) => dec.decode p.2.1)
      E (encList encIntBin) :=
    dec.computableInPolyTime.comp hw₁
  have hl₂ : ComputableInPolyTime (fun p : ℕ × (List Bool × List Bool) => dec.decode p.2.2)
      E (encList encIntBin) :=
    dec.computableInPolyTime.comp hw₂
  have hc₁ := (ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.decide_eq encUnary)).comp
    (((ComputableInPolyTime.length_list encIntBin).comp hl₁).prod hm)
  have hc₂ := (ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.decide_eq encUnary)).comp
    (((ComputableInPolyTime.length_list encIntBin).comp hl₂).prod hm)
  have hcond := ComputableInPolyTime.bool_and.comp (hc₁.prod hc₂)
  have hsub : ComputableInPolyTime
      (fun p : ℕ × (List Bool × List Bool) =>
        ((dec.decode p.2.1).zip (dec.decode p.2.2)).map fun q : ℤ × ℤ => q.1 - q.2)
      E (encList encIntBin) := by
    have hmap : ComputableInPolyTime (List.map (fun q : ℤ × ℤ => q.1 - q.2))
        (encList (encPair encIntBin encIntBin)) (encList encIntBin) :=
      .of_tidy (ComputableTidilyInPolyTime.map ComputableInPolyTime.intBin_sub.tidy)
    exact hmap.comp ((ComputableInPolyTime.zip encIntBin encIntBin).comp (hl₁.prod hl₂))
  have hrep : ComputableInPolyTime
      (fun p : ℕ × (List Bool × List Bool) => List.replicate p.1 (0 : ℤ))
      E (encList encIntBin) :=
    ComputableInPolyTime.replicate hm (ComputableInPolyTime.const (0 : ℤ))
  refine ((ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.encode (encList encIntBin))).comp
      (ComputableInPolyTime.ite' hcond hsub hrep)).of_enc_eq fun p => ?_
  by_cases h₁ : (dec.decode p.2.1).length = p.1 <;>
    by_cases h₂ : (dec.decode p.2.2).length = p.1 <;>
    simp [wordPairToSISVec, dec, h₁, h₂]

/-- `ajtaiWordCollisionToSIS` is uniform strict PPT whenever `P.m` is polynomial-time
computable in unary and `F` is uniform strict PPT. -/
theorem isPPT_ajtaiWordCollisionToSIS (P : SISParams)
    (hm : ComputableInPolyTime P.m encUnary encUnary)
    {F : CollisionFinderFor P.Input}
    (hF : IsPPTOn (encPair encUnary P.encInput) (encPair encBits encBits) fun p => F p.1 p.2) :
    (ajtaiWordCollisionToSIS P F).IsPPT := by
  have hinputWords : ComputableInPolyTime
      (fun x : P.Input => (x.secParam, SIS.encodeMatrix x.matrix))
      P.encInput (encPair encUnary encBits) :=
    ComputableInPolyTime.of_eq fun _ => rfl
  have hsec : ComputableInPolyTime (fun x : P.Input => x.secParam) P.encInput encUnary :=
    (ComputableInPolyTime.fst encUnary encBits).comp hinputWords
  have hprep : ComputableInPolyTime (fun x : P.Input => (x.secParam, x))
      P.encInput (encPair encUnary P.encInput) :=
    hsec.prod ComputableInPolyTime.id'
  have hrun : IsPPTOn P.encInput (encPair encBits encBits)
      fun x => F x.secParam x :=
    hF.preprocess hprep
  have hmInput : ComputableInPolyTime (fun x : P.Input => P.m x.secParam) P.encInput encUnary :=
    hm.comp hsec
  have hpost : ComputableInPolyTime
      (fun p : P.Input × (List Bool × List Bool) => wordPairToSISVec (P.m p.1.secParam) p.2)
      (encPair P.encInput (encPair encBits encBits)) encBits :=
    computableInPolyTime_wordPairToSISVec.comp
      ((hmInput.comp (ComputableInPolyTime.fst _ _)).prod (ComputableInPolyTime.snd _ _))
  refine (hrun.map_with (f := fun x w => wordPairToSISVec (P.m x.secParam) w) hpost).congr
    fun x => ?_
  simp only [ajtaiWordCollisionToSIS, bind_pure_comp, Functor.map_map,
    wordPairToSISVec_eq_encodeVec]

/-- **Ajtai's hash family is setup-parameterized collision-resistant on `[0, P.β κ]^m` under
`SIS P`** ([Ajtai1996]; [BonehShoup2023], Definition 8.2): when `P.m` is polynomial-time
computable in unary and `SIS P` holds, every uniform strict PPT collision finder wins
`collisionGameFor (ajtaiSetup P) (ajtaiFamilyHash P) (ajtaiFamilyValid P)` with negligible
probability. -/
theorem SIS.collisionResistantForOn_ajtai (P : SISParams)
    (hm : ComputableInPolyTime P.m encUnary encUnary) (hSIS : SIS P) :
    CollisionResistantForOn P.encInput (ajtaiSetup P) (ajtaiFamilyHash P) (ajtaiFamilyValid P) := by
  refine CollisionResistantForOn.of_negligible fun F hF => ?_
  exact negligible_of_le (hSIS _ (isPPT_ajtaiWordCollisionToSIS P hm hF))
    (collisionGameFor_ajtai_le_sisAdvantage P F)

end Cslib.Crypto
