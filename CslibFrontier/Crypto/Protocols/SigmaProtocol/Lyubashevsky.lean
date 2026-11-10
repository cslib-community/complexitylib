/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SIS.Basic
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Abort
public import CslibFrontier.Probability.RejectionSampling
public import Cslib.Foundations.Data.BitString
public import Mathlib.Data.Matrix.ColumnRowPartitioned
import CslibFrontier.Probability.PMF

/-!
# Lyubashevsky's identification protocol

Lyubashevsky's lattice-based identification protocol ([Lyubashevsky2009], [Lyubashevsky2012]),
with the uniform-box rejection sampling of Dilithium ([DucasEtAl2018]), as a Sigma protocol with
aborts. The statement is a pair `(A, T)` of matrices over `ZMod q`, of sizes `n × m` and
`n × k`; a witness is an integer matrix `S` with small entries and `A S = T`. Challenges are bit
strings `c ∈ {0,1}^k`, read as integer vectors `ĉ` (`lyubashevskyChallenge`).

* The prover draws `y` uniformly from the box `[-γ, γ]^m` and commits to `w = A y`.
* On the challenge `c` it computes `z = y + S ĉ`. It answers `z` when `z` lies in the inner box
  `[-(γ - β), γ - β]^m`, and aborts otherwise.
* The verifier accepts `z` when `z` lies in the inner box and `A z = w + T ĉ`.

When every entry of `S` is at most `η` in absolute value and `k η ≤ β ≤ γ`:

* **Completeness** (`lyubashevsky_nonAbortComplete`). Every answer the prover gives is accepted,
  for any `S` with `A S = T`. At every challenge the prover aborts with probability exactly
  `1 - ((2 (γ - β) + 1) / (2 γ + 1)) ^ m`, which is at most `2 m β / (2 γ + 1)`.
* **Special soundness** (`lyubashevsky_specialSoundness`). Two accepting conversations
  `(w, c, z)` and `(w, c', z')` with `c ≠ c'` give `(z - z', ĉ' - ĉ)`, a short integer solution
  for `[A | T]` with bound `max (2 (γ - β)) 1`. As usual for lattice protocols, the extracted
  witness belongs to this relaxed relation, not to the prover's.
* **Zero knowledge up to aborts** (`lyubashevsky_nonAbortSpecialHVZK`). At each challenge, the
  simulator draws `z` uniformly from `[-γ, γ]^m`, aborts unless `z` lies in the inner box, and
  solves for `w = A z - T ĉ`. It has exactly the law of the honest prover's published
  transcripts and aborts. The proof is the box rejection-sampling lemma
  (`Cslib.Probability.PMF.boxReject_eq`).

All statements are exact laws over `PMF`. The protocol's samplers are not claimed to be
efficient, and no hardness assumption is used here.

## Main definitions

* `SigmaProtocol.lyubashevsky`: the protocol.
* `SigmaProtocol.lyubashevskyRelation`: witnesses with small entries.
* `SigmaProtocol.lyubashevskyExtract`, `SigmaProtocol.lyubashevskySimulate`: its extractor and
  simulator.

## Main results

* `SigmaProtocol.lyubashevsky_nonAbortComplete`: answers are always accepted.
* `SigmaProtocol.lyubashevsky_acceptedTranscript_none`,
  `SigmaProtocol.lyubashevsky_acceptedTranscript_none_le`: the exact abort probability and its
  bound.
* `SigmaProtocol.lyubashevsky_specialSoundness`: extraction of a short integer solution.
* `SigmaProtocol.lyubashevsky_nonAbortSpecialHVZK`: exact zero knowledge up to aborts.

## References

* [V. Lyubashevsky, *Fiat-Shamir with Aborts: Applications to Lattice and Factoring-Based
  Signatures*][Lyubashevsky2009]
* [V. Lyubashevsky, *Lattice Signatures without Trapdoors*][Lyubashevsky2012]
* [L. Ducas et al., *CRYSTALS-Dilithium: A Lattice-Based Digital Signature
  Scheme*][DucasEtAl2018]
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.SigmaProtocol

open Probability Probability.PMF
open scoped ENNReal _root_.Matrix

/-- A bit-string challenge as a `0`-`1` integer vector. -/
def lyubashevskyChallenge {k : ℕ} (c : BitString k) : Fin k → ℤ :=
  fun j => if c j then 1 else 0

/-- Lyubashevsky's identification protocol with box rejection sampling, for statements
`(A, T)` and witnesses `S` with `A S = T`. The prover commits to `A y` for `y` uniform in
`[-γ, γ]^m`, and answers the challenge `c` with `y + S ĉ` if it lies in `[-(γ - β), γ - β]^m`,
and aborts otherwise. The verifier checks that the answer `z` lies in that box and that
`A z = w + T ĉ`. -/
noncomputable def lyubashevsky (n m k q γ β : ℕ) :
    SigmaProtocol (Matrix (Fin m) (Fin k) ℤ)
      (Matrix (Fin n) (Fin m) (ZMod q) × Matrix (Fin n) (Fin k) (ZMod q))
      (Fin n → ZMod q) (BitString k) (Option (Fin m → ℤ)) where
  State := Fin m → ℤ
  commit _ y := (uniformOfFinset (intBox (Fin m) γ) (intBox_nonempty γ)).map fun r =>
    (y.1 *ᵥ (Int.cast ∘ r), r)
  respond S _ r c :=
    let z := r + S *ᵥ lyubashevskyChallenge c
    if z ∈ intBox (Fin m) (γ - β) then some z else none
  verify y w c
    | none => false
    | some z => decide (z ∈ intBox (Fin m) (γ - β) ∧
        y.1 *ᵥ (Int.cast ∘ z) = w + y.2 *ᵥ (Int.cast ∘ lyubashevskyChallenge c))

/-- The witness relation: `A S = T` modulo `q`, and every entry of `S` lies in `[-η, η]`. -/
def lyubashevskyRelation {n m k q : ℕ} (η : ℕ) (S : Matrix (Fin m) (Fin k) ℤ)
    (y : Matrix (Fin n) (Fin m) (ZMod q) × Matrix (Fin n) (Fin k) (ZMod q)) : Prop :=
  y.1 * S.map Int.cast = y.2 ∧ ∀ i j, |S i j| ≤ η

instance {n m k q : ℕ} (η : ℕ) (S : Matrix (Fin m) (Fin k) ℤ)
    (y : Matrix (Fin n) (Fin m) (ZMod q) × Matrix (Fin n) (Fin k) (ZMod q)) :
    Decidable (lyubashevskyRelation η S y) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The extractor returns `(z - z', ĉ' - ĉ)`, a kernel vector of `[A | T]`. -/
def lyubashevskyExtract (n m k q : ℕ)
    (_ : Matrix (Fin n) (Fin m) (ZMod q) × Matrix (Fin n) (Fin k) (ZMod q))
    (_ : Fin n → ZMod q) (c : BitString k) (z : Option (Fin m → ℤ)) (c' : BitString k)
    (z' : Option (Fin m → ℤ)) : Fin m ⊕ Fin k → ℤ :=
  Sum.elim (z.getD 0 - z'.getD 0) (lyubashevskyChallenge c' - lyubashevskyChallenge c)

/-- The simulator draws `z` by rejection sampling with no shift, uniformly from `[-γ, γ]^m`
and kept only inside `[-(γ - β), γ - β]^m`, and solves the verification equation for the
commitment. -/
noncomputable def lyubashevskySimulate (n m k q γ β : ℕ)
    (y : Matrix (Fin n) (Fin m) (ZMod q) × Matrix (Fin n) (Fin k) (ZMod q)) (c : BitString k) :
    PMF (Option ((Fin n → ZMod q) × (Fin m → ℤ))) :=
  (boxReject (Fin m) γ β 0).map <| Option.map fun z =>
    (y.1 *ᵥ (Int.cast ∘ z) - y.2 *ᵥ (Int.cast ∘ lyubashevskyChallenge c), z)

variable {n m k q γ β : ℕ}

/-- The verifier rejects aborts. -/
@[simp] theorem lyubashevsky_not_accepts_none
    {y : Matrix (Fin n) (Fin m) (ZMod q) × Matrix (Fin n) (Fin k) (ZMod q)} {w : Fin n → ZMod q}
    {c : BitString k} : ¬(lyubashevsky n m k q γ β).Accepts y w c none := by
  simp [Accepts, lyubashevsky]

/-- The verifier accepts an answer in the inner box that satisfies the linear equation. -/
@[simp] theorem lyubashevsky_accepts_some_iff
    {y : Matrix (Fin n) (Fin m) (ZMod q) × Matrix (Fin n) (Fin k) (ZMod q)} {w : Fin n → ZMod q}
    {c : BitString k} {z : Fin m → ℤ} :
    (lyubashevsky n m k q γ β).Accepts y w c (some z) ↔ z ∈ intBox (Fin m) (γ - β) ∧
      y.1 *ᵥ (Int.cast ∘ z) = w + y.2 *ᵥ (Int.cast ∘ lyubashevskyChallenge c) := by
  simp only [Accepts, lyubashevsky, decide_eq_true_eq]

/-- The accepted view at a challenge is box rejection sampling shifted by `S ĉ`, with the
commitment `A (z - S ĉ)` of the published answer `z`. -/
theorem lyubashevsky_acceptedTranscript (S : Matrix (Fin m) (Fin k) ℤ)
    (y : Matrix (Fin n) (Fin m) (ZMod q) × Matrix (Fin n) (Fin k) (ZMod q)) (c : BitString k) :
    (lyubashevsky n m k q γ β).acceptedTranscript S y c =
      (boxReject (Fin m) γ β (S *ᵥ lyubashevskyChallenge c)).map (Option.map fun z =>
        (y.1 *ᵥ (Int.cast ∘ (z - S *ᵥ lyubashevskyChallenge c)), z)) := by
  simp only [acceptedTranscript, transcript, lyubashevsky, boxReject, shiftReject, PMF.map_comp]
  congr 1
  funext r
  simp only [Function.comp_apply]
  split_ifs <;> simp

/-- Reduction modulo `q` commutes with integer matrix-vector products. -/
private theorem intCast_comp_mulVec (S : Matrix (Fin m) (Fin k) ℤ) (v : Fin k → ℤ) :
    (Int.cast ∘ (S *ᵥ v) : Fin m → ZMod q) = S.map Int.cast *ᵥ (Int.cast ∘ v) :=
  funext (RingHom.map_mulVec (Int.castRingHom (ZMod q)) S v)

/-- Reduction modulo `q` commutes with subtraction of integer vectors. -/
private theorem intCast_comp_sub {ι : Type*} (a b : ι → ℤ) :
    (Int.cast ∘ (a - b) : ι → ZMod q) = Int.cast ∘ a - Int.cast ∘ b :=
  funext fun i => Int.cast_sub (a i) (b i)

/-- The entries of a challenge vector are `0` or `1`. -/
private theorem abs_lyubashevskyChallenge_le (c : BitString k) (j : Fin k) :
    |lyubashevskyChallenge c j| ≤ 1 := by
  unfold lyubashevskyChallenge
  split_ifs <;> simp

/-- `S ĉ` has sup norm at most `k η` when the entries of `S` are at most `η`. -/
theorem mulVec_lyubashevskyChallenge_mem_intBox {η : ℕ} {S : Matrix (Fin m) (Fin k) ℤ}
    (hS : ∀ i j, |S i j| ≤ η) (c : BitString k) :
    S *ᵥ lyubashevskyChallenge c ∈ intBox (Fin m) (k * η) := by
  rw [mem_intBox]
  intro i
  calc |(S *ᵥ lyubashevskyChallenge c) i| = |∑ j, S i j * lyubashevskyChallenge c j| := rfl
    _ ≤ ∑ j, |S i j * lyubashevskyChallenge c j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin k, (η : ℤ) := Finset.sum_le_sum fun j _ => by
      rw [abs_mul]
      exact (mul_le_of_le_one_right (abs_nonneg _) (abs_lyubashevskyChallenge_le c j)).trans
        (hS i j)
    _ = ((k * η : ℕ) : ℤ) := by simp

/-- Erasing the commitment of a published transcript leaves the abort probability unchanged. -/
private theorem map_optionMap_apply_none {α δ : Type} (p : PMF (Option α)) (f : α → δ) :
    p.map (Option.map f) none = p none := by
  rw [PMF.map_apply, tsum_eq_single none]
  · simp
  · intro o ho
    cases o with
    | none => exact absurd rfl ho
    | some a => simp

/-- **Completeness up to aborts.** Every answer of the honest prover is accepted, for any
witness with `A S = T`, however large its entries. -/
theorem lyubashevsky_nonAbortComplete :
    (lyubashevsky n m k q γ β).NonAbortComplete fun S y => y.1 * S.map Int.cast = y.2 := by
  intro S y hSy c t z htz
  rw [lyubashevsky_acceptedTranscript] at htz
  obtain ⟨oz, hoz, hsome⟩ := (PMF.mem_support_map_iff _ _ _).mp htz
  cases oz with
  | none => cases hsome
  | some z' =>
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hsome
    obtain ⟨rfl, rfl⟩ := hsome
    rw [lyubashevsky_accepts_some_iff]
    refine ⟨mem_intBox_of_some_mem_support_boxReject hoz, ?_⟩
    rw [intCast_comp_sub, intCast_comp_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hSy,
      sub_add_cancel]

/-- **Abort probability.** If the entries of `S` are at most `η` and `k η ≤ β ≤ γ`, then at every
challenge the prover aborts with probability exactly
`1 - ((2 (γ - β) + 1) / (2 γ + 1)) ^ m`. -/
theorem lyubashevsky_acceptedTranscript_none {η : ℕ} (hβ : β ≤ γ) (hη : k * η ≤ β)
    {S : Matrix (Fin m) (Fin k) ℤ} (hS : ∀ i j, |S i j| ≤ η)
    (y : Matrix (Fin n) (Fin m) (ZMod q) × Matrix (Fin n) (Fin k) (ZMod q)) (c : BitString k) :
    (lyubashevsky n m k q γ β).acceptedTranscript S y c none =
      1 - ((2 * (γ - β) + 1 : ℕ) / (2 * γ + 1 : ℝ≥0∞)) ^ m := by
  rw [lyubashevsky_acceptedTranscript, map_optionMap_apply_none,
    boxReject_apply_none hβ (intBox_mono hη (mulVec_lyubashevskyChallenge_mem_intBox hS c)),
    Fintype.card_fin]

/-- **Abort bound.** Under the same hypotheses, the prover aborts with probability at most
`2 m β / (2 γ + 1)` at every challenge. -/
theorem lyubashevsky_acceptedTranscript_none_le {η : ℕ} (hβ : β ≤ γ) (hη : k * η ≤ β)
    {S : Matrix (Fin m) (Fin k) ℤ} (hS : ∀ i j, |S i j| ≤ η)
    (y : Matrix (Fin n) (Fin m) (ZMod q) × Matrix (Fin n) (Fin k) (ZMod q)) (c : BitString k) :
    (lyubashevsky n m k q γ β).acceptedTranscript S y c none ≤ 2 * m * β / (2 * γ + 1) := by
  rw [lyubashevsky_acceptedTranscript, map_optionMap_apply_none]
  simpa only [Fintype.card_fin] using
    boxReject_apply_none_le hβ (intBox_mono hη (mulVec_lyubashevskyChallenge_mem_intBox hS c))

/-- **Special soundness.** From two accepting conversations with a common commitment and
distinct challenges, `lyubashevskyExtract` computes a short integer solution for `[A | T]`
with bound `max (2 (γ - β)) 1`. -/
theorem lyubashevsky_specialSoundness :
    (lyubashevsky n m k q γ β).SpecialSoundness
      (fun u y => SIS.IsSolution (Matrix.fromCols y.1 y.2) (max (2 * (γ - β)) 1) u)
      (lyubashevskyExtract n m k q) := by
  intro y w c oz c' oz' hc hz hz'
  cases oz with
  | none => exact absurd hz lyubashevsky_not_accepts_none
  | some z =>
  cases oz' with
  | none => exact absurd hz' lyubashevsky_not_accepts_none
  | some z' =>
  rw [lyubashevsky_accepts_some_iff] at hz hz'
  refine ⟨fun h => hc (funext fun j => ?_), ?_, ?_⟩
  · have hj := congr_fun h (Sum.inr j)
    simp only [lyubashevskyExtract, Sum.elim_inr, Pi.sub_apply, Pi.zero_apply, sub_eq_zero,
      lyubashevskyChallenge] at hj
    cases hcj : c j <;> cases hcj' : c' j <;> simp_all
  · rintro (i | j)
    · have hzi := mem_intBox.mp hz.1 i
      have hzi' := mem_intBox.mp hz'.1 i
      simp only [lyubashevskyExtract, Option.getD_some, Sum.elim_inl, Pi.sub_apply]
      calc |z i - z' i| ≤ |z i| + |z' i| := abs_sub _ _
        _ ≤ ((γ - β : ℕ) : ℤ) + ((γ - β : ℕ) : ℤ) := add_le_add hzi hzi'
        _ ≤ ((max (2 * (γ - β)) 1 : ℕ) : ℤ) := by push_cast; omega
    · simp only [lyubashevskyExtract, Sum.elim_inr, Pi.sub_apply]
      have h' := abs_lyubashevskyChallenge_le c' j
      have h := abs_lyubashevskyChallenge_le c j
      unfold lyubashevskyChallenge at h h' ⊢
      split_ifs <;> simp
  · rw [Matrix.fromCols_mulVec]
    simp only [lyubashevskyExtract, Option.getD_some]
    change y.1 *ᵥ (Int.cast ∘ (z - z')) + y.2 *ᵥ
      (Int.cast ∘ (lyubashevskyChallenge c' - lyubashevskyChallenge c)) = 0
    rw [intCast_comp_sub, intCast_comp_sub, Matrix.mulVec_sub, Matrix.mulVec_sub, hz.2, hz'.2]
    abel

/-- **Zero knowledge up to aborts.** If `k η ≤ β ≤ γ`, then for every witness in
`lyubashevskyRelation η` and every challenge, `lyubashevskySimulate` has exactly the law of the
prover's published transcripts and aborts. -/
theorem lyubashevsky_nonAbortSpecialHVZK {η : ℕ} (hβ : β ≤ γ) (hη : k * η ≤ β) :
    (lyubashevsky n m k q γ β).NonAbortSpecialHVZK (lyubashevskyRelation η)
      (lyubashevskySimulate n m k q γ β) where
  accepts y c t z h := by
    obtain ⟨oz, hoz, hsome⟩ := (PMF.mem_support_map_iff _ _ _).mp h
    cases oz with
    | none => cases hsome
    | some z' =>
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hsome
      obtain ⟨rfl, rfl⟩ := hsome
      rw [lyubashevsky_accepts_some_iff]
      exact ⟨mem_intBox_of_some_mem_support_boxReject hoz, (sub_add_cancel _ _).symm⟩
  acceptedTranscript_eq S y hSy c := by
    rw [lyubashevsky_acceptedTranscript, lyubashevskySimulate,
      boxReject_eq (v' := 0) hβ
        (intBox_mono hη (mulVec_lyubashevskyChallenge_mem_intBox hSy.2 c))
        (zero_mem_intBox β)]
    congr 1
    funext oz
    cases oz with
    | none => rfl
    | some z =>
      simp only [Option.map_some, intCast_comp_sub, intCast_comp_mulVec, Matrix.mulVec_sub,
        Matrix.mulVec_mulVec, hSy.1]

end SigmaProtocol

end Cslib.Crypto.Protocols
