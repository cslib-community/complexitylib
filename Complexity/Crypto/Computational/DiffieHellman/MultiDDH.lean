/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.DiffieHellman
import Complexity.Probability.PMF.Uniform

/-!
# Fixed-first-coordinate DDH rerandomization and Multi-DDH

Fixed-first-coordinate rerandomization preserves the real DDH law and sends any non-DDH triple
to the ideal pair law. Independent coordinate rerandomization gives the single-shared-secret
case of Multi-DDH (I), with the exact exceptional-point loss `1 / q`.

This is shared distributional support, not an efficient lazy-sampling reduction. The tuple wrapper
samples every coordinate of its finite index type. Extracted from the reviewed Naor–Reingold
source in PR #1103, authored by worker-jetski-cf53d356 (Gemini), with its mathematics unchanged.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.ddhFixedURerandomizeLaw_real`: real fixed-coordinate law.
* `Cslib.Crypto.PrimeOrderGroupFamily.ddhFixedURerandomizeLaw_ideal`: non-DDH fixed-coordinate law.
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_multiDDH_le`: Multi-DDH loss for one shared secret.

## References

* [BonehShoup2023], Section 10.11, Exercises 10.8 and 10.11.
-/

@[expose] public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM
open scoped ENNReal NNReal

variable (F : PrimeOrderGroupFamily)

/-! ### Fixed-$u$ DDH random self-reduction and Multi-DDH (I) (Exercises 10.8 & 10.11) -/

/-- Fixed-$u$ DDH rerandomization ([BonehShoup2023], Section 10.11, Exercise 10.8, p. 425):
given `(u, v, w)` and exponents `σ, τ : ZMod (F.order d)`, output
`(v*, w*) = (σ • g + τ • v, σ • u + τ • w)`. -/
def ddhFixedURerandomize (d : F.Desc) (u v w : F.Carrier d)
    (σ τ : ZMod (F.order d)) : F.Carrier d × F.Carrier d :=
  (σ • F.generator d + τ • v, σ • u + τ • w)

/-- Algebraic action of `ddhFixedURerandomize` on multiples of the generator:
`v* = (σ + τ * β) • g` and `w* = (α * (σ + τ * β) + τ * (γ - α * β)) • g`. -/
theorem ddhFixedURerandomize_smul_generator (d : F.Desc) (α β γ σ τ : ZMod (F.order d)) :
    F.ddhFixedURerandomize d (α • F.generator d) (β • F.generator d) (γ • F.generator d) σ τ =
      ((σ + τ * β) • F.generator d,
        (α * (σ + τ * β) + τ * (γ - α * β)) • F.generator d) := by
  simp only [ddhFixedURerandomize, smul_smul, ← add_smul]
  refine Prod.ext rfl (congrArg (· • F.generator d) (by ring))

/-- Word-level fixed-$u$ DDH rerandomization on encoded group elements. -/
def ddhFixedUWordRerandomize (d : F.Desc) (u v w : List Bool) (σ τ : ℕ) :
    List Bool × List Bool :=
  (F.add (d, F.smul (d, σ, F.encode d (F.generator d)), F.smul (d, τ, v)),
   F.add (d, F.smul (d, σ, u), F.smul (d, τ, w)))

/-- `ddhFixedUWordRerandomize` computes the encoded output of `ddhFixedURerandomize`. -/
theorem ddhFixedUWordRerandomize_encode (d : F.Desc) (u v w : F.Carrier d) (σ τ : ℕ) :
    F.ddhFixedUWordRerandomize d (F.encode d u) (F.encode d v) (F.encode d w) σ τ =
      ((F.encode d (F.ddhFixedURerandomize d u v w σ τ).1,
        F.encode d (F.ddhFixedURerandomize d u v w σ τ).2)) := by
  simp [ddhFixedUWordRerandomize, ddhFixedURerandomize, F.smul_encode, F.add_encode]

/-- `ddhFixedUWordRerandomize` is computable in polynomial time. -/
theorem computableInPolyTime_ddhFixedUWordRerandomize :
    ComputableInPolyTime
      (fun input : F.Desc × List Bool × List Bool × List Bool × ℕ × ℕ =>
        F.ddhFixedUWordRerandomize input.1 input.2.1 input.2.2.1 input.2.2.2.1
          input.2.2.2.2.1 input.2.2.2.2.2)
      (encPair F.encDesc
        (encPair encBits (encPair encBits (encPair encBits (encPair encNat encNat)))))
      (encPair encBits encBits) := by
  have hd : ComputableInPolyTime
      (fun input : F.Desc × List Bool × List Bool × List Bool × ℕ × ℕ => input.1)
      (encPair F.encDesc
        (encPair encBits (encPair encBits (encPair encBits (encPair encNat encNat)))))
      F.encDesc := by fun_prop
  have hu : ComputableInPolyTime
      (fun input : F.Desc × List Bool × List Bool × List Bool × ℕ × ℕ => input.2.1)
      (encPair F.encDesc
        (encPair encBits (encPair encBits (encPair encBits (encPair encNat encNat)))))
      encBits := by fun_prop
  have hv : ComputableInPolyTime
      (fun input : F.Desc × List Bool × List Bool × List Bool × ℕ × ℕ => input.2.2.1)
      (encPair F.encDesc
        (encPair encBits (encPair encBits (encPair encBits (encPair encNat encNat)))))
      encBits := by fun_prop
  have hw : ComputableInPolyTime
      (fun input : F.Desc × List Bool × List Bool × List Bool × ℕ × ℕ => input.2.2.2.1)
      (encPair F.encDesc
        (encPair encBits (encPair encBits (encPair encBits (encPair encNat encNat)))))
      encBits := by fun_prop
  have hσ : ComputableInPolyTime
      (fun input : F.Desc × List Bool × List Bool × List Bool × ℕ × ℕ => input.2.2.2.2.1)
      (encPair F.encDesc
        (encPair encBits (encPair encBits (encPair encBits (encPair encNat encNat)))))
      encNat := by fun_prop
  have hτ : ComputableInPolyTime
      (fun input : F.Desc × List Bool × List Bool × List Bool × ℕ × ℕ => input.2.2.2.2.2)
      (encPair F.encDesc
        (encPair encBits (encPair encBits (encPair encBits (encPair encNat encNat)))))
      encNat := by fun_prop
  have hgen := F.computableInPolyTime_generator.comp hd
  have hσg := F.computableInPolyTime_smul.comp (hd.prod (hσ.prod hgen))
  have hτv := F.computableInPolyTime_smul.comp (hd.prod (hτ.prod hv))
  have hσu := F.computableInPolyTime_smul.comp (hd.prod (hσ.prod hu))
  have hτw := F.computableInPolyTime_smul.comp (hd.prod (hτ.prod hw))
  have hv' := F.computableInPolyTime_add.comp (hd.prod (hσg.prod hτv))
  have hw' := F.computableInPolyTime_add.comp (hd.prod (hσu.prod hτw))
  exact hv'.prod hw'

/-- The distribution of `(v*, w*)` obtained by drawing `σ, τ : ZMod (F.order d)` independently and
uniformly in `ddhFixedURerandomize` ([BonehShoup2023], Exercise 10.8, p. 425). -/
noncomputable def ddhFixedURerandomizeLaw (d : F.Desc) (u v w : F.Carrier d) :
    PMF (F.Carrier d × F.Carrier d) := do
  let σ ← PMF.uniformOfFintype (ZMod (F.order d))
  let τ ← PMF.uniformOfFintype (ZMod (F.order d))
  return F.ddhFixedURerandomize d u v w σ τ

/-- The real DDH pair distribution `(β • g, (α * β) • g)` for a fixed first exponent `α`. -/
noncomputable def ddhFixedURealLaw (d : F.Desc) (α : ZMod (F.order d)) :
    PMF (F.Carrier d × F.Carrier d) := do
  let β ← PMF.uniformOfFintype (ZMod (F.order d))
  return (β • F.generator d, (α * β) • F.generator d)

/-- The ideal pair distribution `(β • g, γ • g)` on `F.Carrier d × F.Carrier d`. -/
noncomputable def ddhFixedUIdealLaw (d : F.Desc) :
    PMF (F.Carrier d × F.Carrier d) := do
  let β ← PMF.uniformOfFintype (ZMod (F.order d))
  let γ ← PMF.uniformOfFintype (ZMod (F.order d))
  return (β • F.generator d, γ • F.generator d)

/-- **Boneh–Shoup Exercise 10.8(a)**: if `(u, v, w) = (α • g, β • g, (α * β) • g)` is a DDH triple,
then `ddhFixedURerandomizeLaw` produces `ddhFixedURealLaw d α` for every `α, β`. -/
theorem ddhFixedURerandomizeLaw_real (d : F.Desc) (α β : ZMod (F.order d)) :
    F.ddhFixedURerandomizeLaw d (α • F.generator d) (β • F.generator d)
      ((α * β) • F.generator d) = F.ddhFixedURealLaw d α := by
  simp only [ddhFixedURerandomizeLaw, ddhFixedURealLaw, ddhFixedURerandomize_smul_generator,
    sub_self, mul_zero, add_zero, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  rw [PMF.bind_comm]
  have hσ (τ : ZMod (F.order d)) :
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun σ =>
        PMF.pure ((σ + τ * β) • F.generator d, (α * (σ + τ * β)) • F.generator d)) =
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun β' =>
        PMF.pure (β' • F.generator d, (α * β') • F.generator d)) :=
    by
      change (PMF.uniformOfFintype (ZMod (F.order d))).bind
        ((fun β' => PMF.pure (β' • F.generator d, (α * β') • F.generator d)) ∘
          Equiv.addRight (τ * β)) = _
      rw [← PMF.bind_map, PMF.uniformOfFintype_map_equiv]
  simp_rw [hσ, PMF.bind_const]

/-- **Boneh–Shoup Exercise 10.8(b)**: if `(u, v, w) = (α • g, β • g, γ • g)` is a non-DDH triple
(`γ ≠ α * β`), then `ddhFixedURerandomizeLaw` produces `ddhFixedUIdealLaw d`. -/
theorem ddhFixedURerandomizeLaw_ideal (d : F.Desc) {α β γ : ZMod (F.order d)} (hγ : γ ≠ α * β) :
    F.ddhFixedURerandomizeLaw d (α • F.generator d) (β • F.generator d) (γ • F.generator d) =
      F.ddhFixedUIdealLaw d := by
  simp only [ddhFixedURerandomizeLaw, ddhFixedUIdealLaw, ddhFixedURerandomize_smul_generator,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  rw [PMF.bind_comm]
  have hσ (τ : ZMod (F.order d)) :
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun σ =>
        PMF.pure ((σ + τ * β) • F.generator d,
          (α * (σ + τ * β) + τ * (γ - α * β)) • F.generator d)) =
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun β' =>
        PMF.pure (β' • F.generator d,
          (α * β' + τ * (γ - α * β)) • F.generator d)) :=
    by
      change (PMF.uniformOfFintype (ZMod (F.order d))).bind
        ((fun β' => PMF.pure (β' • F.generator d,
          (α * β' + τ * (γ - α * β)) • F.generator d)) ∘ Equiv.addRight (τ * β)) = _
      rw [← PMF.bind_map, PMF.uniformOfFintype_map_equiv]
  simp_rw [hσ]
  rw [PMF.bind_comm]
  congr 1; funext β'
  change (PMF.uniformOfFintype (ZMod (F.order d))).bind
    ((fun γ' => PMF.pure (β' • F.generator d, γ' • F.generator d)) ∘
      (Equiv.mulRight₀ (γ - α * β) (sub_ne_zero.mpr hγ)).trans (Equiv.addLeft (α * β'))) = _
  rw [← PMF.bind_map, PMF.uniformOfFintype_map_equiv]

/-- The Multi-DDH (I) real tuple family `i ↦ (B i • g, (α * B i) • g)` for a fixed `α` and an
index type `ι` ([BonehShoup2023], Section 10.11, Exercise 10.11, p. 426). -/
noncomputable def multiDDHRealTupleLaw (d : F.Desc) (ι : Type*) [Fintype ι] [DecidableEq ι]
    (α : ZMod (F.order d)) : PMF (ι → F.Carrier d × F.Carrier d) :=
  (PMF.uniformOfFintype (ι → ZMod (F.order d))).map fun B i =>
    (B i • F.generator d, (α * B i) • F.generator d)

/-- The Multi-DDH (I) ideal tuple family `i ↦ (B₀ i • g, B₁ i • g)` for an index type `ι`
([BonehShoup2023], Section 10.11, Exercise 10.11, p. 426). -/
noncomputable def multiDDHIdealTupleLaw (d : F.Desc) (ι : Type*) [Fintype ι] [DecidableEq ι] :
    PMF (ι → F.Carrier d × F.Carrier d) :=
  (PMF.uniformOfFintype (ι → ZMod (F.order d) × ZMod (F.order d))).map fun B i =>
    ((B i).1 • F.generator d, (B i).2 • F.generator d)

/-- Multi-DDH (I) rerandomization ([BonehShoup2023], Exercise 10.11, p. 426): given a single
candidate DDH triple `(u, v, w)`, draw independent `(σ i, τ i) ← ZMod q × ZMod q` for each `i : ι`
and output `i ↦ ddhFixedURerandomize d u v w (σ i) (τ i)`. -/
noncomputable def multiDDHRerandomizeLaw (d : F.Desc) (ι : Type*) [Fintype ι] [DecidableEq ι]
    (u v w : F.Carrier d) : PMF (ι → F.Carrier d × F.Carrier d) :=
  (PMF.uniformOfFintype (ι → ZMod (F.order d) × ZMod (F.order d))).map fun r i =>
    F.ddhFixedURerandomize d u v w (r i).1 (r i).2

private def ddhRerandomizeRealTupleEquiv {q : ℕ} (ι : Type*) (β : ZMod q) :
    (ι → ZMod q × ZMod q) ≃ ((ι → ZMod q) × (ι → ZMod q)) where
  toFun r := (fun i => (r i).1 + (r i).2 * β, fun i => (r i).2)
  invFun p i := (p.1 i - p.2 i * β, p.2 i)
  left_inv r := by ext i <;> simp
  right_inv p := by ext i <;> simp

private def ddhRerandomizeRealCoordEquiv {q : ℕ} (β : ZMod q) :
    (ZMod q × ZMod q) ≃ (ZMod q × ZMod q) where
  toFun p := (p.1 + p.2 * β, p.2)
  invFun p := (p.1 - p.2 * β, p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp

private def ddhRerandomizeSecondCoordEquiv {q : ℕ} [Fact (Nat.Prime q)]
    {α β γ : ZMod q} (hγ : γ ≠ α * β) :
    (ZMod q × ZMod q) ≃ (ZMod q × ZMod q) where
  toFun p := (p.1, α * p.1 + p.2 * (γ - α * β))
  invFun p := (p.1, (p.2 - α * p.1) * (γ - α * β)⁻¹)
  left_inv p := by
    have hne : γ - α * β ≠ 0 := sub_ne_zero.mpr hγ
    ext
    · rfl
    · dsimp; rw [add_sub_cancel_left, mul_assoc, mul_inv_cancel₀ hne, mul_one]
  right_inv p := by
    have hne : γ - α * β ≠ 0 := sub_ne_zero.mpr hγ
    ext
    · rfl
    · dsimp; rw [mul_assoc, inv_mul_cancel₀ hne, mul_one, add_sub_cancel]

/-- On any real DDH triple `(α • g, β • g, (α * β) • g)`, `multiDDHRerandomizeLaw` produces
`multiDDHRealTupleLaw d ι α` ([BonehShoup2023], Exercise 10.11). -/
theorem multiDDHRerandomizeLaw_real (d : F.Desc) (ι : Type*) [Fintype ι] [DecidableEq ι]
    (α β : ZMod (F.order d)) :
    F.multiDDHRerandomizeLaw d ι (α • F.generator d) (β • F.generator d)
      ((α * β) • F.generator d) = F.multiDDHRealTupleLaw d ι α := by
  let e : (ι → ZMod (F.order d) × ZMod (F.order d)) ≃
      ((ι → ZMod (F.order d)) × (ι → ZMod (F.order d))) :=
    ddhRerandomizeRealTupleEquiv ι β
  rw [multiDDHRealTupleLaw,
    ← PMF.uniformOfFintype_prod_map_fst (α := ι → ZMod (F.order d)) (β := ι → ZMod (F.order d)),
    ← PMF.uniformOfFintype_map_equiv e, PMF.map_comp, PMF.map_comp,
    multiDDHRerandomizeLaw]
  congr 1; funext r; funext i
  simp [e, ddhRerandomizeRealTupleEquiv, ddhFixedURerandomize_smul_generator]

/-- On any non-DDH triple `(α • g, β • g, γ • g)` with `γ ≠ α * β`, `multiDDHRerandomizeLaw`
produces `multiDDHIdealTupleLaw d ι` ([BonehShoup2023], Exercise 10.11). -/
theorem multiDDHRerandomizeLaw_ideal (d : F.Desc) (ι : Type*) [Fintype ι] [DecidableEq ι]
    {α β γ : ZMod (F.order d)} (hγ : γ ≠ α * β) :
    F.multiDDHRerandomizeLaw d ι (α • F.generator d) (β • F.generator d) (γ • F.generator d) =
      F.multiDDHIdealTupleLaw d ι := by
  let e : (ι → ZMod (F.order d) × ZMod (F.order d)) ≃
      (ι → ZMod (F.order d) × ZMod (F.order d)) :=
    Equiv.piCongrRight fun _ =>
      (ddhRerandomizeRealCoordEquiv β).trans (ddhRerandomizeSecondCoordEquiv hγ)
  rw [multiDDHIdealTupleLaw, ← PMF.uniformOfFintype_map_equiv e, PMF.map_comp,
    multiDDHRerandomizeLaw]
  congr 1; funext r; funext i
  simp [e, ddhRerandomizeRealCoordEquiv, ddhRerandomizeSecondCoordEquiv,
    ddhFixedURerandomize_smul_generator]

/-- **Boneh–Shoup Exercise 10.11 ($n = 1$ Multi-DDH (I), p. 426)**: for a single shared secret `α`,
any finite index type `ι` (`|ι|` pairs), and any test
`test : F.Carrier d → (ι → F.Carrier d × F.Carrier d) → PMF Bool`, the advantage between
`(α • g, multiDDHRealTupleLaw d ι α)` and `(α • g, multiDDHIdealTupleLaw d ι)` is at most the DDH
advantage of the rerandomizing wrapper `multiDDHRerandomizeLaw` (which samples `|ι|` pairs) plus
`(F.order d)⁻¹`. -/
theorem advantage_multiDDH_le (d : F.Desc) (ι : Type*) [Fintype ι] [DecidableEq ι]
    (test : F.Carrier d → (ι → F.Carrier d × F.Carrier d) → PMF Bool) :
    Game.advantage
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
        (F.multiDDHRealTupleLaw d ι α).bind (test (α • F.generator d)))
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
        (F.multiDDHIdealTupleLaw d ι).bind (test (α • F.generator d))) ≤
    Game.advantage
      ((F.ddhRealTupleLaw d).bind fun t =>
        (F.multiDDHRerandomizeLaw d ι t.1 t.2.1 t.2.2).bind (test t.1))
      ((F.ddhIdealTupleLaw d).bind fun t =>
        (F.multiDDHRerandomizeLaw d ι t.1 t.2.1 t.2.2).bind (test t.1)) +
      (F.order d : ℝ≥0)⁻¹ := by
  have hreal :
      ((F.ddhRealTupleLaw d).bind fun t =>
        (F.multiDDHRerandomizeLaw d ι t.1 t.2.1 t.2.2).bind (test t.1)) =
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
        (F.multiDDHRealTupleLaw d ι α).bind (test (α • F.generator d))) := by
    simp only [ddhRealTupleLaw, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind,
      PMF.pure_bind, multiDDHRerandomizeLaw_real, PMF.bind_const]
  rw [← hreal]
  refine (Game.advantage_triangle _
    ((F.ddhIdealTupleLaw d).bind fun t =>
      (F.multiDDHRerandomizeLaw d ι t.1 t.2.1 t.2.2).bind (test t.1)) _).trans ?_
  refine add_le_add le_rfl ?_
  simp only [ddhIdealTupleLaw, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind,
    PMF.pure_bind]
  -- Bound the advantage inside the outer `α, β` averages using `Game.advantage_bind_le`.
  have hpoint (α β : ZMod (F.order d)) :
      (Game.advantage
        ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun γ =>
          (F.multiDDHRerandomizeLaw d ι (α • F.generator d) (β • F.generator d)
            (γ • F.generator d)).bind (test (α • F.generator d)))
        ((F.multiDDHIdealTupleLaw d ι).bind (test (α • F.generator d))) : ℝ) ≤
      (((F.order d : ℝ≥0)⁻¹ : ℝ≥0) : ℝ) := by
    refine NNReal.coe_le_coe.mpr ?_
    simpa only [ZMod.card] using
      Game.advantage_bind_uniformOfFintype_of_ne_le (α * β)
        (fun γ => (F.multiDDHRerandomizeLaw d ι (α • F.generator d) (β • F.generator d)
          (γ • F.generator d)).bind (test (α • F.generator d)))
        ((F.multiDDHIdealTupleLaw d ι).bind (test (α • F.generator d)))
        (fun γ hγ => by rw [F.multiDDHRerandomizeLaw_ideal d ι hγ])
  have hβ (α : ZMod (F.order d)) :
      (Game.advantage
        ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun β =>
          (PMF.uniformOfFintype (ZMod (F.order d))).bind fun γ =>
            (F.multiDDHRerandomizeLaw d ι (α • F.generator d) (β • F.generator d)
              (γ • F.generator d)).bind (test (α • F.generator d)))
        ((F.multiDDHIdealTupleLaw d ι).bind (test (α • F.generator d))) : ℝ) ≤
      (((F.order d : ℝ≥0)⁻¹ : ℝ≥0) : ℝ) := by
    rw [← PMF.bind_const (PMF.uniformOfFintype (ZMod (F.order d)))
      ((F.multiDDHIdealTupleLaw d ι).bind (test (α • F.generator d)))]
    exact Game.advantage_bind_le _ _ _ (hpoint α)
  exact NNReal.coe_le_coe.mp (Game.advantage_bind_le _ _ _ hβ)

end Cslib.Crypto.PrimeOrderGroupFamily
