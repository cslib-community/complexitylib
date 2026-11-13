/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.DiffieHellman
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Tactic.GameHop
import CslibFrontier.Tactic.PolyTime

/-!
# Fixed-first-coordinate DDH rerandomization and Multi-DDH

Fixed-first-coordinate rerandomization preserves the real DDH law and sends any non-DDH triple
to the random pair law. Independent coordinate rerandomization gives the single-shared-secret
case of Multi-DDH (I), with the exact exceptional-point loss `1 / q`.

This is shared distributional support, not an efficient lazy-sampling reduction. The tuple wrapper
samples every coordinate of its finite index type. Extracted from the reviewed Naor–Reingold
source in PR #1103, authored by worker-jetski-cf53d356 (Gemini), with its mathematics unchanged.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.ddhFixedURerandomizeLaw_real`: real fixed-coordinate law.
* `Cslib.Crypto.PrimeOrderGroupFamily.ddhFixedURerandomizeLaw_random`: non-DDH fixed-coordinate law.
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

@[local fun_prop]
private theorem computableInPolyTime_add_comp {α : Type} {encIn : α ↪ List Bool}
    {d : α → F.Desc} {x y : α → List Bool}
    (hd : ComputableInPolyTime d encIn F.encDesc)
    (hx : ComputableInPolyTime x encIn encBits)
    (hy : ComputableInPolyTime y encIn encBits) :
    ComputableInPolyTime (fun a => F.add (d a, x a, y a)) encIn encBits :=
  F.computableInPolyTime_add.comp (hd.prod (hx.prod hy))

@[local fun_prop]
private theorem computableInPolyTime_smul_comp {α : Type} {encIn : α ↪ List Bool}
    {d : α → F.Desc} {k : α → ℕ} {x : α → List Bool}
    (hd : ComputableInPolyTime d encIn F.encDesc)
    (hk : ComputableInPolyTime k encIn encNat)
    (hx : ComputableInPolyTime x encIn encBits) :
    ComputableInPolyTime (fun a => F.smul (d a, k a, x a)) encIn encBits :=
  F.computableInPolyTime_smul.comp (hd.prod (hk.prod hx))

/-- `ddhFixedUWordRerandomize` is computable in polynomial time. -/
theorem computableInPolyTime_ddhFixedUWordRerandomize :
    ComputableInPolyTime
      (fun input : F.Desc × List Bool × List Bool × List Bool × ℕ × ℕ =>
        F.ddhFixedUWordRerandomize input.1 input.2.1 input.2.2.1 input.2.2.2.1
          input.2.2.2.2.1 input.2.2.2.2.2)
      (encPair F.encDesc
        (encPair encBits (encPair encBits (encPair encBits (encPair encNat encNat)))))
      (encPair encBits encBits) := by
  unfold ddhFixedUWordRerandomize
  fun_prop

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

/-- The random pair distribution `(β • g, γ • g)` on `F.Carrier d × F.Carrier d`. -/
noncomputable def ddhFixedURandomLaw (d : F.Desc) :
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
(`γ ≠ α * β`), then `ddhFixedURerandomizeLaw` produces `ddhFixedURandomLaw d`. -/
theorem ddhFixedURerandomizeLaw_random (d : F.Desc) {α β γ : ZMod (F.order d)} (hγ : γ ≠ α * β) :
    F.ddhFixedURerandomizeLaw d (α • F.generator d) (β • F.generator d) (γ • F.generator d) =
      F.ddhFixedURandomLaw d := by
  simp only [ddhFixedURerandomizeLaw, ddhFixedURandomLaw, ddhFixedURerandomize_smul_generator,
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
  congr 1 with β' : 1
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

/-- The Multi-DDH (I) random tuple family `i ↦ (B₀ i • g, B₁ i • g)` for an index type `ι`
([BonehShoup2023], Section 10.11, Exercise 10.11, p. 426). -/
noncomputable def multiDDHRandomTupleLaw (d : F.Desc) (ι : Type*) [Fintype ι] [DecidableEq ι] :
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
  congr 1 with r : 1; funext i
  simp [e, ddhRerandomizeRealTupleEquiv, ddhFixedURerandomize_smul_generator]

/-- On any non-DDH triple `(α • g, β • g, γ • g)` with `γ ≠ α * β`, `multiDDHRerandomizeLaw`
produces `multiDDHRandomTupleLaw d ι` ([BonehShoup2023], Exercise 10.11). -/
theorem multiDDHRerandomizeLaw_random (d : F.Desc) (ι : Type*) [Fintype ι] [DecidableEq ι]
    {α β γ : ZMod (F.order d)} (hγ : γ ≠ α * β) :
    F.multiDDHRerandomizeLaw d ι (α • F.generator d) (β • F.generator d) (γ • F.generator d) =
      F.multiDDHRandomTupleLaw d ι := by
  let e : (ι → ZMod (F.order d) × ZMod (F.order d)) ≃
      (ι → ZMod (F.order d) × ZMod (F.order d)) :=
    Equiv.piCongrRight fun _ =>
      (ddhRerandomizeRealCoordEquiv β).trans (ddhRerandomizeSecondCoordEquiv hγ)
  rw [multiDDHRandomTupleLaw, ← PMF.uniformOfFintype_map_equiv e, PMF.map_comp,
    multiDDHRerandomizeLaw]
  congr 1 with r : 1; funext i
  simp [e, ddhRerandomizeRealCoordEquiv, ddhRerandomizeSecondCoordEquiv,
    ddhFixedURerandomize_smul_generator]

/-- **Boneh–Shoup Exercise 10.11 ($n = 1$ Multi-DDH (I), p. 426)**: for a single shared secret `α`,
any finite index type `ι` (`|ι|` pairs), and any test
`test : F.Carrier d → (ι → F.Carrier d × F.Carrier d) → PMF Bool`, the advantage between
`(α • g, multiDDHRealTupleLaw d ι α)` and `(α • g, multiDDHRandomTupleLaw d ι)` is at most the DDH
advantage of the rerandomizing wrapper `multiDDHRerandomizeLaw` (which samples `|ι|` pairs) plus
`(F.order d)⁻¹`. -/
theorem advantage_multiDDH_le (d : F.Desc) (ι : Type*) [Fintype ι] [DecidableEq ι]
    (test : F.Carrier d → (ι → F.Carrier d × F.Carrier d) → PMF Bool) :
    Game.advantage
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
        (F.multiDDHRealTupleLaw d ι α).bind (test (α • F.generator d)))
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
        (F.multiDDHRandomTupleLaw d ι).bind (test (α • F.generator d))) ≤
    Game.advantage
      ((F.ddhRealTupleLaw d).bind fun (u, v, w) =>
        (F.multiDDHRerandomizeLaw d ι u v w).bind (test u))
      ((F.ddhRandomTupleLaw d).bind fun (u, v, w) =>
        (F.multiDDHRerandomizeLaw d ι u v w).bind (test u)) +
      (F.order d : ℝ≥0)⁻¹ := by
  have hreal :
      ((F.ddhRealTupleLaw d).bind fun (u, v, w) =>
        (F.multiDDHRerandomizeLaw d ι u v w).bind (test u)) =
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
        (F.multiDDHRealTupleLaw d ι α).bind (test (α • F.generator d))) := by
    simp only [pmf_norm, ddhRealTupleLaw, multiDDHRerandomizeLaw_real, PMF.bind_const]
  have hideal :
      Game.advantage
        ((F.ddhRandomTupleLaw d).bind fun (u, v, w) =>
          (F.multiDDHRerandomizeLaw d ι u v w).bind (test u))
        ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
          (F.multiDDHRandomTupleLaw d ι).bind (test (α • F.generator d))) ≤
      (F.order d : ℝ≥0)⁻¹ := by
    simp only [pmf_norm, ddhRandomTupleLaw]
    peel_binds α
    rw [← PMF.bind_const (PMF.uniformOfFintype (ZMod (F.order d)))
      ((F.multiDDHRandomTupleLaw d ι).bind (test (α • F.generator d)))]
    peel_binds β
    simpa only [ZMod.card] using
      Game.advantage_bind_uniformOfFintype_of_ne_le (α * β)
        (fun γ => (F.multiDDHRerandomizeLaw d ι (α • F.generator d) (β • F.generator d)
          (γ • F.generator d)).bind (test (α • F.generator d)))
        ((F.multiDDHRandomTupleLaw d ι).bind (test (α • F.generator d)))
        (fun γ hγ => by rw [F.multiDDHRerandomizeLaw_random d ι hγ])
  game_trans
    [(F.ddhRealTupleLaw d).bind fun (u, v, w) =>
       (F.multiDDHRerandomizeLaw d ι u v w).bind (test u),
     (F.ddhRandomTupleLaw d).bind fun (u, v, w) =>
       (F.multiDDHRerandomizeLaw d ι u v w).bind (test u)]
    using [hreal, le_rfl, hideal]

end Cslib.Crypto.PrimeOrderGroupFamily
