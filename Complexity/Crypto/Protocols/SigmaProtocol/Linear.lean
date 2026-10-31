/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Protocols.SigmaProtocol.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.Span.Basic
import Complexity.Probability.PMF

/-!
# Sigma protocols for linear relations

Fix a prime `q`. Boneh and Shoup's Schnorr, Okamoto, Chaum–Pedersen and generic linear
protocols ([BonehShoup2023], Sections 19.1 and 19.5.1–19.5.4) are one protocol, for the
preimage of a `ZMod q`-linear map. Groups are written additively: a group of prime order `q`
is a `ZMod q`-module, and the book's `g ^ α` is `α • g`. A multiplicative group of exponent `q`
can be used through `Additive` with `AddCommGroup.zmodModule`.

In `linear ψ u ι`, a statement `y` determines a linear map `ψ y : M →ₗ[ZMod q] N` and a target
`u y : N`; a witness is a preimage `x` with `ψ y x = u y`. The prover commits to `ψ y r` for a
uniform `r : M` and answers the challenge `c` with `r + c • x`. Challenges come from any type `C`
with an injection `ι : C ↪ ZMod q`, which covers a subset of `ZMod q` as well as bit strings
read as numbers below `q`.

Completeness and special honest-verifier zero knowledge hold for every modulus. Special
soundness, which divides by a difference of distinct challenges, uses that `q` is prime. The
instances need no hypothesis that the group is cyclic or that the given elements generate it.

## Main definitions

* `SigmaProtocol.linear`: the protocol for preimages of statement-dependent linear maps.
* `SigmaProtocol.linearExtract`, `SigmaProtocol.linearSimulate`: its extractor and simulator.
* `SigmaProtocol.schnorr`: knowledge of `α` with `α • g = u` (Example 19.1).
* `SigmaProtocol.okamoto`: knowledge of `(α, β)` with `α • g + β • h = u` (Section 19.5.1).
* `SigmaProtocol.chaumPedersen`: `(u, v, w)` is a Diffie–Hellman triple (Section 19.5.2).
* `SigmaProtocol.linearSystem`: a solution of `∑ j, α j • g i j = u i` for all `i`
  (Section 19.5.3).

## Main results

* `SigmaProtocol.linear_complete`, `SigmaProtocol.linear_specialSoundness`,
  `SigmaProtocol.linear_specialHVZK`: Theorem 19.12 for groups of prime order `q`.
* The same three properties for each instance, with the instance's own relation
  (Theorems 19.9–19.11 and Examples 19.2–19.3).

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Sections 19.1, 19.4 and 19.5.
* [C.-P. Schnorr, *Efficient Signature Generation by Smart Cards*][Schnorr1991]
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.SigmaProtocol

open Probability

universe u

section Linear

variable {q : ℕ} {M N Y C : Type u} [AddCommGroup M] [Module (ZMod q) M] [Fintype M]
  [AddCommGroup N] [Module (ZMod q) N] [DecidableEq N]

/-- The Sigma protocol for a preimage of the linear map `ψ y` at `u y`
([BonehShoup2023], Figures 19.8 and 19.9). The prover commits to `ψ y r` for a uniform `r` and
answers the challenge `c` with `r + ι c • x`; the verifier checks `ψ y z = t + ι c • u y`. -/
noncomputable def linear (ψ : Y → M →ₗ[ZMod q] N) (u : Y → N) (ι : C ↪ ZMod q) :
    SigmaProtocol M Y N C M where
  State := M
  commit _ y := (PMF.uniformOfFintype M).map fun r => (ψ y r, r)
  respond x _ r c := r + ι c • x
  verify y t c z := decide (ψ y z = t + ι c • u y)

/-- The extractor divides the difference of the responses by the difference of the
challenges. -/
def linearExtract (ι : C ↪ ZMod q) (_ : Y) (_ : N) (c : C) (z : M) (c' : C) (z' : M) : M :=
  (ι c - ι c')⁻¹ • (z - z')

/-- The simulator samples a uniform response and solves the verification equation for the
commitment. -/
noncomputable def linearSimulate (ψ : Y → M →ₗ[ZMod q] N) (u : Y → N) (ι : C ↪ ZMod q)
    (y : Y) (c : C) : PMF (N × M) :=
  (PMF.uniformOfFintype M).map fun z => (ψ y z - ι c • u y, z)

variable (ψ : Y → M →ₗ[ZMod q] N) (u : Y → N) (ι : C ↪ ZMod q)

/-- A conversation is accepting exactly when it satisfies the verification equation
`ψ y z = t + ι c • u y`. -/
@[simp] theorem linear_accepts_iff {y : Y} {t : N} {c : C} {z : M} :
    (linear ψ u ι).Accepts y t c z ↔ ψ y z = t + ι c • u y := by
  simp only [Accepts, linear, decide_eq_true_eq]

/-- An honest transcript is `(ψ y r, r + ι c • x)` for a uniform `r`. -/
theorem linear_transcript (x : M) (y : Y) (c : C) :
    (linear ψ u ι).transcript x y c =
      (PMF.uniformOfFintype M).map fun r => (ψ y r, r + ι c • x) := by
  simp only [transcript, linear, PMF.map_comp]
  rfl

/-- Honest conversations are accepting ([BonehShoup2023], Theorem 19.12). -/
theorem linear_complete : (linear ψ u ι).Complete fun x y => ψ y x = u y := by
  intro x y hxy c tz htz
  rw [linear_transcript] at htz
  obtain ⟨r, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp htz
  simp only [linear_accepts_iff, map_add, map_smul, hxy]

/-- `linearExtract` is a witness extractor when `q` is prime ([BonehShoup2023], Theorem 19.12). -/
theorem linear_specialSoundness [Fact q.Prime] :
    (linear ψ u ι).SpecialSoundness (fun x y => ψ y x = u y) (linearExtract ι) := by
  intro y t c z c' z' hc hz hz'
  rw [linear_accepts_iff] at hz hz'
  have hne : ι c - ι c' ≠ 0 := sub_ne_zero.mpr (ι.injective.ne hc)
  simp only [linearExtract, map_smul, map_sub, hz, hz', add_sub_add_left_eq_sub, ← sub_smul,
    smul_smul, inv_mul_cancel₀ hne, one_smul]

/-- `linearSimulate` is a perfect simulator at every challenge ([BonehShoup2023],
Theorem 19.12). -/
theorem linear_specialHVZK :
    (linear ψ u ι).SpecialHVZK (fun x y => ψ y x = u y) (linearSimulate ψ u ι) where
  accepts y c tz htz := by
    obtain ⟨z, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp htz
    simp only [linear_accepts_iff, sub_add_cancel]
  transcript_eq x y hxy c := by
    rw [linear_transcript, linearSimulate]
    conv_lhs => rw [← PMF.uniformOfFintype_map_equiv (Equiv.addRight (ι c • x))]
    rw [PMF.map_comp]
    congr 1
    funext r
    simp only [Function.comp_apply, Equiv.coe_addRight, map_add, map_smul, hxy,
      add_sub_cancel_right]

end Linear

section Instances

variable {q : ℕ} [NeZero q] {G C : Type} [AddCommGroup G] [Module (ZMod q) G] [DecidableEq G]
  (ι : C ↪ ZMod q)

/-! ### Schnorr -/

/-- Schnorr's Sigma protocol for knowledge of `α` with `α • g = u`
([BonehShoup2023], Example 19.1). -/
noncomputable def schnorr (g : G) : SigmaProtocol (ZMod q) G G C (ZMod q) :=
  linear (fun _ => LinearMap.toSpanSingleton (ZMod q) G g) id ι

variable {ι} {g : G}

/-- Schnorr's verification equation `z • g = t + c • u` ([BonehShoup2023], Example 19.1). -/
@[simp] theorem schnorr_accepts_iff {u t : G} {c : C} {z : ZMod q} :
    (schnorr ι g).Accepts u t c z ↔ z • g = t + ι c • u := by
  simp only [schnorr, linear_accepts_iff, LinearMap.toSpanSingleton_apply, id]

theorem schnorr_complete : (schnorr ι g).Complete fun α u => α • g = u :=
  (linear_complete _ _ ι).mono fun _ _ h => by simpa using h

/-- Example 19.2 of [BonehShoup2023]. -/
theorem schnorr_specialSoundness [Fact q.Prime] :
    (schnorr ι g).SpecialSoundness (fun α u => α • g = u) (linearExtract ι) :=
  (linear_specialSoundness _ _ ι).mono fun _ _ h => by simpa using h

/-- Example 19.3 of [BonehShoup2023]. -/
theorem schnorr_specialHVZK :
    (schnorr ι g).SpecialHVZK (fun α u => α • g = u)
      (linearSimulate (fun _ => LinearMap.toSpanSingleton (ZMod q) G g) id ι) :=
  (linear_specialHVZK _ _ ι).mono fun _ _ h => by simpa using h

/-! ### Okamoto -/

variable (ι) in
/-- Okamoto's Sigma protocol for knowledge of a representation `(α, β)` of `u`, meaning
`α • g + β • h = u` ([BonehShoup2023], Section 19.5.1). -/
noncomputable def okamoto (g h : G) : SigmaProtocol (ZMod q × ZMod q) G G C (ZMod q × ZMod q) :=
  linear (fun _ => (LinearMap.toSpanSingleton (ZMod q) G g).coprod
    (LinearMap.toSpanSingleton (ZMod q) G h)) id ι

variable {h : G}

/-- Okamoto's verification equation `z₁ • g + z₂ • h = t + c • u`
([BonehShoup2023], Section 19.5.1). -/
@[simp] theorem okamoto_accepts_iff {u t : G} {c : C} {z : ZMod q × ZMod q} :
    (okamoto ι g h).Accepts u t c z ↔ z.1 • g + z.2 • h = t + ι c • u := by
  simp only [okamoto, linear_accepts_iff, LinearMap.coprod_apply,
    LinearMap.toSpanSingleton_apply, id]

/-- Theorem 19.9 of [BonehShoup2023]: completeness. -/
theorem okamoto_complete : (okamoto ι g h).Complete fun w u => w.1 • g + w.2 • h = u :=
  (linear_complete _ _ ι).mono fun _ _ hw => by simpa using hw

/-- Theorem 19.9 of [BonehShoup2023]: special soundness. -/
theorem okamoto_specialSoundness [Fact q.Prime] :
    (okamoto ι g h).SpecialSoundness (fun w u => w.1 • g + w.2 • h = u) (linearExtract ι) :=
  (linear_specialSoundness _ _ ι).mono fun _ _ hw => by simpa using hw

/-- Theorem 19.9 of [BonehShoup2023]: special honest-verifier zero knowledge. -/
theorem okamoto_specialHVZK :
    (okamoto ι g h).SpecialHVZK (fun w u => w.1 • g + w.2 • h = u)
      (linearSimulate (fun _ => (LinearMap.toSpanSingleton (ZMod q) G g).coprod
        (LinearMap.toSpanSingleton (ZMod q) G h)) id ι) :=
  (linear_specialHVZK _ _ ι).mono fun _ _ hw => by simpa using hw

/-! ### Chaum–Pedersen -/

variable (ι) in
/-- The Chaum–Pedersen protocol for Diffie–Hellman triples: a witness for `(u, v, w)` is `β`
with `β • g = v` and `β • u = w` ([BonehShoup2023], Section 19.5.2). -/
noncomputable def chaumPedersen (g : G) : SigmaProtocol (ZMod q) (G × G × G) (G × G) C (ZMod q) :=
  linear (fun s => (LinearMap.toSpanSingleton (ZMod q) G g).prod
    (LinearMap.toSpanSingleton (ZMod q) G s.1)) Prod.snd ι

/-- The Chaum–Pedersen verification equations `z • g = t₁ + c • v` and `z • u = t₂ + c • w`
([BonehShoup2023], Section 19.5.2). -/
@[simp] theorem chaumPedersen_accepts_iff {s : G × G × G} {t : G × G} {c : C} {z : ZMod q} :
    (chaumPedersen ι g).Accepts s t c z ↔
      z • g = t.1 + ι c • Prod.fst s.2 ∧ z • s.1 = t.2 + ι c • Prod.snd s.2 := by
  simp [chaumPedersen, Prod.ext_iff]

/-- Theorem 19.10 of [BonehShoup2023]: completeness. -/
theorem chaumPedersen_complete :
    (chaumPedersen ι g).Complete fun β s => β • g = Prod.fst s.2 ∧ β • s.1 = Prod.snd s.2 :=
  (linear_complete _ _ ι).mono fun _ _ h => by simpa [Prod.ext_iff] using h

/-- Theorem 19.10 of [BonehShoup2023]: special soundness. -/
theorem chaumPedersen_specialSoundness [Fact q.Prime] :
    (chaumPedersen ι g).SpecialSoundness
      (fun β s => β • g = Prod.fst s.2 ∧ β • s.1 = Prod.snd s.2)
      (linearExtract ι) :=
  (linear_specialSoundness _ _ ι).mono fun _ _ h => by simpa [Prod.ext_iff] using h

/-- Theorem 19.10 of [BonehShoup2023]: special honest-verifier zero knowledge. -/
theorem chaumPedersen_specialHVZK :
    (chaumPedersen ι g).SpecialHVZK (fun β s => β • g = Prod.fst s.2 ∧ β • s.1 = Prod.snd s.2)
      (linearSimulate (fun s => (LinearMap.toSpanSingleton (ZMod q) G g).prod
        (LinearMap.toSpanSingleton (ZMod q) G s.1)) Prod.snd ι) :=
  (linear_specialHVZK _ _ ι).mono fun _ _ h => by simpa [Prod.ext_iff] using h

/-! ### Systems of linear equations -/

variable (ι) in
/-- The generic linear protocol for `m` equations `∑ j, α j • g i j = u i` in `n` unknowns, with
the statement `(g, u)` ([BonehShoup2023], Section 19.5.3 and Figure 19.8). -/
noncomputable def linearSystem (m n : ℕ) :
    SigmaProtocol (Fin n → ZMod q) ((Fin m → Fin n → G) × (Fin m → G)) (Fin m → G) C
      (Fin n → ZMod q) :=
  linear (fun s => LinearMap.pi fun i => Fintype.linearCombination (ZMod q) (s.1 i)) Prod.snd ι

variable {m n : ℕ}

/-- The generic linear protocol checks each equation `∑ j, z j • g i j = t i + c • u i`
([BonehShoup2023], Figure 19.8). -/
@[simp] theorem linearSystem_accepts_iff {s : (Fin m → Fin n → G) × (Fin m → G)}
    {t : Fin m → G} {c : C} {z : Fin n → ZMod q} :
    (linearSystem ι m n).Accepts s t c z ↔ ∀ i, ∑ j, z j • s.1 i j = t i + ι c • s.2 i := by
  simp only [linearSystem, linear_accepts_iff, funext_iff, LinearMap.pi_apply,
    Fintype.linearCombination_apply, Pi.add_apply, Pi.smul_apply]

/-- Theorem 19.11 of [BonehShoup2023]: completeness. -/
theorem linearSystem_complete :
    (linearSystem (G := G) ι m n).Complete fun α s => ∀ i, ∑ j, α j • s.1 i j = s.2 i :=
  (linear_complete _ _ ι).mono fun _ _ h => by
    simpa [funext_iff, LinearMap.pi_apply, Fintype.linearCombination_apply] using h

/-- Theorem 19.11 of [BonehShoup2023]: special soundness. -/
theorem linearSystem_specialSoundness [Fact q.Prime] :
    (linearSystem (G := G) ι m n).SpecialSoundness (fun α s => ∀ i, ∑ j, α j • s.1 i j = s.2 i)
      (linearExtract ι) :=
  (linear_specialSoundness _ _ ι).mono fun _ _ h => by
    simpa [funext_iff, LinearMap.pi_apply, Fintype.linearCombination_apply] using h

/-- Theorem 19.11 of [BonehShoup2023]: special honest-verifier zero knowledge. -/
theorem linearSystem_specialHVZK :
    (linearSystem (G := G) ι m n).SpecialHVZK (fun α s => ∀ i, ∑ j, α j • s.1 i j = s.2 i)
      (linearSimulate (fun s : (Fin m → Fin n → G) × (Fin m → G) =>
        LinearMap.pi fun i => Fintype.linearCombination (ZMod q) (s.1 i)) Prod.snd ι) :=
  (linear_specialHVZK _ _ ι).mono fun _ _ h => by
    simpa [funext_iff, LinearMap.pi_apply, Fintype.linearCombination_apply] using h

end Instances

end Cslib.Crypto.Protocols.SigmaProtocol
