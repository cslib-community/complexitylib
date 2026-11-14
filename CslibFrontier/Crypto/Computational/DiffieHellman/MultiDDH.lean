/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.DiffieHellman
public import CslibFrontier.Crypto.Computational.DiffieHellman.Order
public import CslibFrontier.Crypto.Computational.DiffieHellman.SampleExp
import CslibFrontier.Computability.Probabilistic.PPT.Extension
import CslibFrontier.Computability.Probabilistic.PPT.PairCapture
import CslibFrontier.Computability.Probabilistic.Repeat
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.Product
import CslibFrontier.Tactic.GameHop
import CslibFrontier.Tactic.Negligible
import CslibFrontier.Tactic.PolyTime

/-!
# Fixed-first-coordinate DDH rerandomization and Multi-DDH

Fixed-first-coordinate rerandomization preserves the real DDH law and sends any non-DDH triple
to the random pair law ([BonehShoup2023], Section 10.11, Exercise 10.8). Combining Exercise 10.9's
single-exponent shift with Exercise 10.8's fixed-first-coordinate rerandomization yields both the
single-shared-secret ($n = 1$) step and the full two-parameter $(n, m)$ Multi-DDH (I) reduction
([BonehShoup2023], Exercise 10.11, p. 426), with tight algebraic loss `1 / q` independent of the
number of secrets and pairs.

We provide both the exact distributional laws (`ddhFixedURerandomizeLaw`,
`multiDDHRerandomizeLaw`, `ddhShiftAndRerandomizeLaw`, used by Naor–Reingold's prefix-tree hybrid
and the Multi-DDH game hops) and the executable `ProbComp` reductions and uniform strict PPT
witnesses (`ddhFixedUSelfReduceDistinguisher`, `singleSecretMultiDDHToDDHDistinguisher`,
`DDH.singleSecretMultiDDH`, `multiDDHToDDHDistinguisher`, `DDH.multiDDH`) using approximate
exponent sampling via `sampleExp`.
The distributional core was extracted from the reviewed Naor–Reingold source in PR #1103,
authored by worker-jetski-cf53d356 (Gemini).

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.ddhFixedURerandomize`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhFixedUWordRerandomize`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhFixedURerandomizeLaw`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhFixedURerandomizeComp`: algebraic, word-level,
  distributional, and executable fixed-first-coordinate DDH rerandomization (Exercise 10.8).
* `Cslib.Crypto.PrimeOrderGroupFamily.ddhFixedUSelfReduceDistinguisher`: the efficient
  fixed-first-coordinate DDH random self-reduction.
* `Cslib.Crypto.PrimeOrderGroupFamily.multiDDHRealTupleLaw`,
  `Cslib.Crypto.PrimeOrderGroupFamily.multiDDHRandomTupleLaw`,
  `Cslib.Crypto.PrimeOrderGroupFamily.multiDDHRerandomizeLaw`: finite-index Multi-DDH (I) laws.
* `Cslib.Crypto.PrimeOrderGroupFamily.SingleSecretMultiDDHInput`,
  `Cslib.Crypto.PrimeOrderGroupFamily.encSingleSecretMultiDDHInput`,
  `Cslib.Crypto.PrimeOrderGroupFamily.SingleSecretMultiDDHDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.singleSecretMultiDDHRealGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.singleSecretMultiDDHRandomGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.SingleSecretMultiDDH`,
  `Cslib.Crypto.PrimeOrderGroupFamily.singleSecretMultiDDHToDDHDistinguisher`: the single-secret
  ($n = 1$) Multi-DDH (I) games, assumption, and executable reduction to DDH.
* `Cslib.Crypto.PrimeOrderGroupFamily.ddhShift`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhWordShift`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhShiftAndRerandomizeLaw`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhShiftAndRerandomizeComp`: single-exponent shift
  (Exercise 10.9) and per-secret block generation for full two-parameter Multi-DDH (I).
* `Cslib.Crypto.PrimeOrderGroupFamily.MultiDDHInput`,
  `Cslib.Crypto.PrimeOrderGroupFamily.encMultiDDHInput`,
  `Cslib.Crypto.PrimeOrderGroupFamily.MultiDDHDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.multiDDHRealGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.multiDDHRandomGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.MultiDDH`,
  `Cslib.Crypto.PrimeOrderGroupFamily.multiDDHToDDHDistinguisher`: the full two-parameter $(n, m)$
  Multi-DDH (I) games, assumption, and executable reduction to DDH (Exercise 10.11).

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.ddhFixedURerandomizeLaw_real`: real fixed-coordinate law.
* `Cslib.Crypto.PrimeOrderGroupFamily.ddhFixedURerandomizeLaw_random`: non-DDH fixed-coordinate law.
* `Cslib.Crypto.PrimeOrderGroupFamily.isPPT_ddhFixedUSelfReduceDistinguisher`,
  `advantage_ddhFixedURerandomizeLaw_ddhFixedUSelfReduceDistinguisher_le`:
  the fixed-first-coordinate self-reduction is PPT and loses at most `2 / 2 ^ n` against exact
  rerandomization.
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_multiDDH_le`: distributional Multi-DDH loss for
  one shared secret.
* `Cslib.Crypto.PrimeOrderGroupFamily.isPPT_singleSecretMultiDDHToDDHDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.advantage_singleSecretMultiDDHGame_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DDH.singleSecretMultiDDH`: single-secret ($n = 1$)
  Multi-DDH (I) is implied by `DDH` for any polynomial-time pair-count schedule.
* `Cslib.Crypto.PrimeOrderGroupFamily.isPPT_multiDDHToDDHDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.advantage_multiDDHGame_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DDH.multiDDH`: full two-parameter $(n, m)$ Multi-DDH (I) is
  implied by `DDH` for any polynomial-time secret-count and pair-count schedules.

## References

* [BonehShoup2023], Section 10.11, Exercises 10.8, 10.9, and 10.11.
-/

public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM
open scoped ENNReal NNReal

variable (F : PrimeOrderGroupFamily)

/-! ### Fixed-$u$ DDH random self-reduction and Multi-DDH (I) (Exercises 10.8 & 10.11) -/

/-- Fixed-$u$ DDH rerandomization ([BonehShoup2023], Section 10.11, Exercise 10.8, p. 425):
given `(u, v, w)` and exponents `σ, τ : ZMod (F.order d)`, output
`(v*, w*) = (σ • g + τ • v, σ • u + τ • w)`. -/
@[expose] def ddhFixedURerandomize (d : F.Desc) (u v w : F.Carrier d)
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
@[expose] def ddhFixedUWordRerandomize (d : F.Desc) (u v w : List Bool) (σ τ : ℕ) :
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

variable {F} in
/-- Compositional polynomial-time certificate for `ddhFixedUWordRerandomize`. -/
@[fun_prop] theorem computableInPolyTime_ddhFixedUWordRerandomize_comp {α : Type}
    {enc : α ↪ List Bool} {d : α → F.Desc} {u v w : α → List Bool} {σ τ : α → ℕ}
    (hd : ComputableInPolyTime d enc F.encDesc)
    (hu : ComputableInPolyTime u enc encBits)
    (hv : ComputableInPolyTime v enc encBits)
    (hw : ComputableInPolyTime w enc encBits)
    (hσ : ComputableInPolyTime σ enc encNat)
    (hτ : ComputableInPolyTime τ enc encNat) :
    ComputableInPolyTime
      (fun a => F.ddhFixedUWordRerandomize (d a) (u a) (v a) (w a) (σ a) (τ a))
      enc (encPair encBits encBits) :=
  F.computableInPolyTime_ddhFixedUWordRerandomize.comp
    (hd.prod (hu.prod (hv.prod (hw.prod (hσ.prod hτ)))))

variable {F} in
/-- The encoded pair output of `ddhFixedURerandomize` with natural-number exponents is computable
in polynomial time. -/
@[fun_prop] theorem computableInPolyTime_encode_ddhFixedURerandomize {α : Type}
    {enc : α ↪ List Bool} {d : α → F.Desc} {u v w : (a : α) → F.Carrier (d a)} {σ τ : α → ℕ}
    (hd : ComputableInPolyTime d enc F.encDesc)
    (hu : ComputableInPolyTime (fun a => F.encode (d a) (u a)) enc encBits)
    (hv : ComputableInPolyTime (fun a => F.encode (d a) (v a)) enc encBits)
    (hw : ComputableInPolyTime (fun a => F.encode (d a) (w a)) enc encBits)
    (hσ : ComputableInPolyTime σ enc encNat)
    (hτ : ComputableInPolyTime τ enc encNat) :
    ComputableInPolyTime
      (fun a =>
        (F.encode (d a) (F.ddhFixedURerandomize (d a) (u a) (v a) (w a) (σ a) (τ a)).1,
         F.encode (d a) (F.ddhFixedURerandomize (d a) (u a) (v a) (w a) (σ a) (τ a)).2))
      enc (encPair encBits encBits) :=
  .of_enc_eq (computableInPolyTime_ddhFixedUWordRerandomize_comp hd hu hv hw hσ hτ) fun a => by
    simp [F.ddhFixedUWordRerandomize_encode]

/-- The distribution of `(v*, w*)` obtained by drawing `σ, τ : ZMod (F.order d)` independently and
uniformly in `ddhFixedURerandomize` ([BonehShoup2023], Exercise 10.8, p. 425). -/
@[expose] noncomputable def ddhFixedURerandomizeLaw (d : F.Desc) (u v w : F.Carrier d) :
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
@[expose] noncomputable def multiDDHRealTupleLaw (d : F.Desc) (ι : Type*) [Fintype ι]
    [DecidableEq ι] (α : ZMod (F.order d)) : PMF (ι → F.Carrier d × F.Carrier d) :=
  (PMF.uniformOfFintype (ι → ZMod (F.order d))).map fun B i =>
    (B i • F.generator d, (α * B i) • F.generator d)

/-- The Multi-DDH (I) random tuple family `i ↦ (B₀ i • g, B₁ i • g)` for an index type `ι`
([BonehShoup2023], Section 10.11, Exercise 10.11, p. 426). -/
@[expose] noncomputable def multiDDHRandomTupleLaw (d : F.Desc) (ι : Type*) [Fintype ι]
    [DecidableEq ι] : PMF (ι → F.Carrier d × F.Carrier d) :=
  (PMF.uniformOfFintype (ι → ZMod (F.order d) × ZMod (F.order d))).map fun B i =>
    ((B i).1 • F.generator d, (B i).2 • F.generator d)

/-- Multi-DDH (I) rerandomization ([BonehShoup2023], Exercise 10.11, p. 426): given a single
candidate DDH triple `(u, v, w)`, draw independent `(σ i, τ i) ← ZMod q × ZMod q` for each `i : ι`
and output `i ↦ ddhFixedURerandomize d u v w (σ i) (τ i)`. -/
@[expose] noncomputable def multiDDHRerandomizeLaw (d : F.Desc) (ι : Type*) [Fintype ι]
    [DecidableEq ι] (u v w : F.Carrier d) : PMF (ι → F.Carrier d × F.Carrier d) :=
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

/-- On a real DDH triple, `multiDDHRerandomizeLaw` produces `multiDDHRealTupleLaw`. -/
theorem ddhRealTupleLaw_bind_multiDDHRerandomizeLaw (d : F.Desc) (ι : Type*) [Fintype ι]
    [DecidableEq ι] (test : F.Carrier d → (ι → F.Carrier d × F.Carrier d) → PMF Bool) :
    ((F.ddhRealTupleLaw d).bind fun (u, v, w) =>
      (F.multiDDHRerandomizeLaw d ι u v w).bind (test u)) =
    ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
      (F.multiDDHRealTupleLaw d ι α).bind (test (α • F.generator d))) := by
  simp only [pmf_norm, ddhRealTupleLaw, multiDDHRerandomizeLaw_real, PMF.bind_const]

/-- On a random DDH triple, `multiDDHRerandomizeLaw` agrees with `multiDDHRandomTupleLaw` except on
the `1 / q` fraction of triples that happen to be valid DDH triples. -/
theorem advantage_ddhRandomTupleLaw_multiDDHRerandomizeLaw_le (d : F.Desc) (ι : Type*) [Fintype ι]
    [DecidableEq ι] (test : F.Carrier d → (ι → F.Carrier d × F.Carrier d) → PMF Bool) :
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
  game_trans
    [(F.ddhRealTupleLaw d).bind fun (u, v, w) =>
       (F.multiDDHRerandomizeLaw d ι u v w).bind (test u),
     (F.ddhRandomTupleLaw d).bind fun (u, v, w) =>
       (F.multiDDHRerandomizeLaw d ι u v w).bind (test u)]
    using [F.ddhRealTupleLaw_bind_multiDDHRerandomizeLaw d ι test, le_rfl,
      F.advantage_ddhRandomTupleLaw_multiDDHRerandomizeLaw_le d ι test]

/-! ### Executable fixed-$u$ DDH random self-reduction (Exercise 10.8) -/

/-- Executable fixed-$u$ DDH rerandomization ([BonehShoup2023], Exercise 10.8, p. 425): sample two
independent approximate uniform exponents `σ, τ ← F.sampleExp n d` and output
`F.ddhFixedURerandomize d u v w σ τ`. -/
noncomputable def ddhFixedURerandomizeComp (n : ℕ) (d : F.Desc) (u v w : F.Carrier d) :
    ProbComp (F.Carrier d × F.Carrier d) := do
  let σ ← F.sampleExp n d
  let τ ← F.sampleExp n d
  return F.ddhFixedURerandomize d u v w σ τ

/-- The fixed-$u$ DDH random self-reduction ([BonehShoup2023], Exercise 10.8, p. 425): rerandomize
`(v, w)` while keeping `u` fixed via `ddhFixedURerandomizeComp`, then run `distinguisher` on
`(u, v', w')`. -/
noncomputable def ddhFixedUSelfReduceDistinguisher (distinguisher : F.DDHDistinguisher) :
    F.DDHDistinguisher := fun n d u v w => do
  let (v', w') ← F.ddhFixedURerandomizeComp n d u v w
  distinguisher n d u v' w'

variable {F} in
/-- `ddhFixedURerandomizeComp` is uniform strict PPT on encoded group elements. -/
theorem isPPTOn_encode_ddhFixedURerandomizeComp {α : Type} {enc : α ↪ List Bool}
    {n : α → ℕ} {d : α → F.Desc} {u v w : (a : α) → F.Carrier (d a)}
    (hn : ComputableInPolyTime n enc encUnary)
    (hd : ComputableInPolyTime d enc F.encDesc)
    (hu : ComputableInPolyTime (fun a => F.encode (d a) (u a)) enc encBits)
    (hv : ComputableInPolyTime (fun a => F.encode (d a) (v a)) enc encBits)
    (hw : ComputableInPolyTime (fun a => F.encode (d a) (w a)) enc encBits) :
    IsPPTOn enc (encPair encBits encBits) fun a =>
      (fun p => (F.encode (d a) p.1, F.encode (d a) p.2)) <$>
        F.ddhFixedURerandomizeComp (n a) (d a) (u a) (v a) (w a) := by
  let E1 := encPair enc encNat
  let E2 := encPair E1 encNat
  have hp1 : ComputableInPolyTime (fun p : (α × ℕ) × ℕ => p.1) E2 E1 :=
    ComputableInPolyTime.fst E1 encNat
  have ha : ComputableInPolyTime (fun p : (α × ℕ) × ℕ => p.1.1) E2 enc :=
    (ComputableInPolyTime.fst enc encNat).comp hp1
  have hσ : ComputableInPolyTime (fun p : (α × ℕ) × ℕ => p.1.2) E2 encNat :=
    (ComputableInPolyTime.snd enc encNat).comp hp1
  have hτ : ComputableInPolyTime (fun p : (α × ℕ) × ℕ => p.2) E2 encNat :=
    ComputableInPolyTime.snd E1 encNat
  refine ((F.isPPTOn_sampleExp hn hd).bind_pair
    ((F.isPPTOn_sampleExp (hn.comp (ComputableInPolyTime.fst enc encNat))
      (hd.comp (ComputableInPolyTime.fst enc encNat))).map_pair
      (computableInPolyTime_encode_ddhFixedURerandomize
        (hd.comp ha) (hu.comp ha) (hv.comp ha) (hw.comp ha) hσ hτ))).congr fun a => ?_
  simp [ddhFixedURerandomizeComp, map_bind]

private theorem isPPTOn_encode_ddhFixedURerandomizeComp_ddhInput :
    IsPPTOn F.encDDHInput (encPair encBits encBits) fun x =>
      (fun p => (F.encode x.groupParameters p.1, F.encode x.groupParameters p.2)) <$>
        F.ddhFixedURerandomizeComp x.secParam x.groupParameters
          x.leftPublic x.rightPublic x.candidateShared :=
  isPPTOn_encode_ddhFixedURerandomizeComp
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)

/-- `ddhFixedUSelfReduceDistinguisher` is uniform strict PPT whenever `distinguisher` is. -/
theorem isPPT_ddhFixedUSelfReduceDistinguisher {distinguisher : F.DDHDistinguisher}
    (hD : distinguisher.IsPPT) : (F.ddhFixedUSelfReduceDistinguisher distinguisher).IsPPT := by
  obtain ⟨W, hW, hWD⟩ := hD.exists_bool_factor F.encDDHInput_apply
  have hpost : IsPPTOn (encPair F.encDDHInput (encPair encBits encBits)) encBool
      (fun (p : F.DDHInput × List Bool × List Bool) =>
        W (p.1.secParam, p.1.groupParameters,
          F.encode p.1.groupParameters p.1.leftPublic, p.2)) :=
    hW.preprocess (by fun_prop)
  refine (F.isPPTOn_encode_ddhFixedURerandomizeComp_ddhInput.bind_pair hpost).congr fun x => ?_
  have hfun (p : F.Carrier x.groupParameters × F.Carrier x.groupParameters) :
      distinguisher x.secParam x.groupParameters x.leftPublic p.1 p.2 =
        W (x.secParam, x.groupParameters, F.encode x.groupParameters x.leftPublic,
           (F.encode x.groupParameters p.1, F.encode x.groupParameters p.2)) :=
    hWD ⟨⟨x.secParam, x.groupParameters, x.leftPublic, p.1⟩, p.2⟩
  simp [ddhFixedUSelfReduceDistinguisher, bind_map_left, hfun]

/-- Replacing `ddhFixedURerandomizeComp` by the exact uniform rerandomization law
`ddhFixedURerandomizeLaw` changes `Game.advantage` by at most `2 / 2 ^ n`. -/
theorem advantage_bind_ddhFixedURerandomizeComp_le (n : ℕ) (d : F.Desc) (u v w : F.Carrier d)
    (k : F.Carrier d × F.Carrier d → Game) :
    Game.advantage
      ((ProbComp.eval (F.ddhFixedURerandomizeComp n d u v w)).bind k)
      ((F.ddhFixedURerandomizeLaw d u v w).bind k) ≤ 2 / 2 ^ n := by
  simpa only [ddhFixedURerandomizeComp, ddhFixedURerandomizeLaw, ProbComp.eval_bind,
    ProbComp.eval_pure, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind,
    PMF.pure_bind] using
    F.advantage_bind_sampleExp_pair_le n d
      (fun σ τ => k (F.ddhFixedURerandomize d u v w σ τ))

/-- **Sampling loss of the fixed-$u$ DDH self-reduction**: on any fixed triple `(u, v, w)`,
replacing the two exact uniform exponents of `ddhFixedURerandomizeLaw` by the `sampleExp` draws of
`ddhFixedUSelfReduceDistinguisher` changes the acceptance law by at most `2 / 2 ^ n`. -/
theorem advantage_ddhFixedURerandomizeLaw_ddhFixedUSelfReduceDistinguisher_le
    (distinguisher : F.DDHDistinguisher) (n : ℕ) (d : F.Desc) (u v w : F.Carrier d) :
    Game.advantage
      ((F.ddhFixedURerandomizeLaw d u v w).bind fun (v', w') =>
        ProbComp.eval (distinguisher n d u v' w'))
      (ProbComp.eval (F.ddhFixedUSelfReduceDistinguisher distinguisher n d u v w)) ≤
      2 / 2 ^ n := by
  rw [Game.advantage_comm]
  simpa only [ddhFixedUSelfReduceDistinguisher, ProbComp.eval_bind] using
    F.advantage_bind_ddhFixedURerandomizeComp_le n d u v w
      (fun (v', w') => ProbComp.eval (distinguisher n d u v' w'))

/-! ### Executable single-secret ($n = 1$) Multi-DDH (I) reduction (Exercise 10.11) -/

/-- Encoding of a pair of group elements `(v, w) : F.Carrier d × F.Carrier d` via `encPair`. -/
@[expose] def encCarrierPair (d : F.Desc) : F.Carrier d × F.Carrier d ↪ List Bool :=
  (Function.Embedding.prodMap ⟨F.encode d, F.encode_injective d⟩
    ⟨F.encode d, F.encode_injective d⟩).trans (encPair encBits encBits)

@[simp] theorem encCarrierPair_apply (d : F.Desc) (p : F.Carrier d × F.Carrier d) :
    F.encCarrierPair d p = encPair encBits encBits (F.encode d p.1, F.encode d p.2) := rfl

/-- `encList (F.encCarrierPair d)` encodes a list of group-element pairs as `encList` of their
encoded word pairs. -/
theorem encList_encCarrierPair (d : F.Desc) (pairs : List (F.Carrier d × F.Carrier d)) :
    encList (F.encCarrierPair d) pairs =
      encList (encPair encBits encBits)
        (pairs.map fun p => (F.encode d p.1, F.encode d p.2)) := by
  simp [encList, encCarrierPair, List.flatMap_map, Function.comp_def]

/-- The input of a single-secret ($n = 1$) Multi-DDH (I) distinguisher ([BonehShoup2023],
Section 10.11, Exercise 10.11, p. 426): the security parameter, public group parameters `d`, the
shared first element `u = α • g`, and a list of candidate pairs `(v_j, w_j)`. -/
structure SingleSecretMultiDDHInput where
  /-- The security parameter, given to machines in unary. -/
  secParam : ℕ
  /-- Public parameters selecting the group, its prime order and generator within the family. -/
  groupParameters : F.Desc
  /-- The shared first element `u = α • g`. -/
  leftPublic : F.Carrier groupParameters
  /-- The list of candidate pairs `(v_j, w_j)`. -/
  pairs : List (F.Carrier groupParameters × F.Carrier groupParameters)

/-- The encoding of a `SingleSecretMultiDDHInput`: the unary security parameter, the group
parameters, the encoded first element, and the list of encoded pairs, each framed except the last
(`encSingleSecretMultiDDHInput_apply`). -/
enc_structure encSingleSecretMultiDDHInput (F : PrimeOrderGroupFamily) :
    SingleSecretMultiDDHInput F where
  secParam : encUnary, groupParameters : F.encDesc,
  leftPublic : (F.encode groupParameters) using (F.encode_injective groupParameters),
  pairs : (encList (F.encCarrierPair groupParameters)) using
    ((encList (F.encCarrierPair groupParameters)).injective)

/-- A single-secret ($n = 1$) Multi-DDH (I) distinguisher over the family: given the security
parameter, public group parameters `d`, the shared element `u : F.Carrier d`, and a list of
candidate pairs `List (F.Carrier d × F.Carrier d)`, it outputs a bit.
`SingleSecretMultiDDHDistinguisher.IsPPT` states its efficiency on encodings. -/
abbrev SingleSecretMultiDDHDistinguisher : Type :=
  ℕ → (d : F.Desc) → F.Carrier d → List (F.Carrier d × F.Carrier d) → ProbComp Bool

variable {F} in
/-- A `SingleSecretMultiDDHDistinguisher` is PPT when one uniform strict PPT machine reads
`encSingleSecretMultiDDHInput` and writes the distinguisher's output bit. -/
def SingleSecretMultiDDHDistinguisher.IsPPT
    (distinguisher : F.SingleSecretMultiDDHDistinguisher) : Prop :=
  IsPPTOn F.encSingleSecretMultiDDHInput encBool fun x =>
    distinguisher x.secParam x.groupParameters x.leftPublic x.pairs

variable {F} in
/-- Characterization of `SingleSecretMultiDDHDistinguisher.IsPPT` in terms of `IsPPTOn`. -/
@[simp] theorem SingleSecretMultiDDHDistinguisher.isPPT_iff
    (distinguisher : F.SingleSecretMultiDDHDistinguisher) :
    distinguisher.IsPPT ↔
      IsPPTOn F.encSingleSecretMultiDDHInput encBool fun x =>
        distinguisher x.secParam x.groupParameters x.leftPublic x.pairs :=
  Iff.rfl

variable {F} in
/-- A PPT `SingleSecretMultiDDHDistinguisher` run on computed inputs is uniform strict PPT. -/
theorem SingleSecretMultiDDHDistinguisher.IsPPT.comp
    {distinguisher : F.SingleSecretMultiDDHDistinguisher} (hD : distinguisher.IsPPT)
    {α : Type} {enc : α ↪ List Bool} {n : α → ℕ} {d : α → F.Desc}
    {u : (a : α) → F.Carrier (d a)}
    {pairs : (a : α) → List (F.Carrier (d a) × F.Carrier (d a))}
    (hn : ComputableInPolyTime n enc encUnary)
    (hd : ComputableInPolyTime d enc F.encDesc)
    (hu : ComputableInPolyTime (fun a => F.encode (d a) (u a)) enc encBits)
    (hpairs : ComputableInPolyTime
      (fun a => encList (F.encCarrierPair (d a)) (pairs a)) enc encBits) :
    IsPPTOn enc encBool fun a => distinguisher (n a) (d a) (u a) (pairs a) :=
  IsPPTOn.preprocess hD (F.encSingleSecretMultiDDHInput_mk_polyTime hn hd hu hpairs)

/-- The real single-secret ($n = 1$) Multi-DDH (I) game with `count n` pairs ([BonehShoup2023],
Exercise 10.11, p. 426): sample `d ← setup n`, `α ← ZMod (F.order d)`, and `count n` independent
pairs `(β_j • g, (α * β_j) • g)` via `multiDDHRealTupleLaw d (Fin (count n)) α`, then pass the list
`List.ofFn tuple` to `distinguisher`. -/
noncomputable def singleSecretMultiDDHRealGame (setup : ℕ → PMF F.Desc) (count : ℕ → ℕ)
    (distinguisher : F.SingleSecretMultiDDHDistinguisher) (n : ℕ) : Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let tuple ← F.multiDDHRealTupleLaw d (Fin (count n)) α
  ProbComp.eval (distinguisher n d (α • F.generator d) (List.ofFn tuple))

/-- The random single-secret ($n = 1$) Multi-DDH (I) game with `count n` pairs ([BonehShoup2023],
Exercise 10.11, p. 426): sample `d ← setup n`, `α ← ZMod (F.order d)`, and `count n` independent
random pairs `(β_j • g, γ_j • g)` via `multiDDHRandomTupleLaw d (Fin (count n))`, then pass the list
`List.ofFn tuple` to `distinguisher`. -/
noncomputable def singleSecretMultiDDHRandomGame (setup : ℕ → PMF F.Desc) (count : ℕ → ℕ)
    (distinguisher : F.SingleSecretMultiDDHDistinguisher) (n : ℕ) : Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let tuple ← F.multiDDHRandomTupleLaw d (Fin (count n))
  ProbComp.eval (distinguisher n d (α • F.generator d) (List.ofFn tuple))

/-- The single-secret ($n = 1$) Multi-DDH (I) assumption for a setup law and pair-count schedule
`count` ([BonehShoup2023], Exercise 10.11, p. 426): every PPT `SingleSecretMultiDDHDistinguisher`
has negligible advantage between `singleSecretMultiDDHRealGame` and
`singleSecretMultiDDHRandomGame`. -/
def SingleSecretMultiDDH (setup : ℕ → PMF F.Desc) (count : ℕ → ℕ) : Prop :=
  Game.Indistinguishable (F.singleSecretMultiDDHRealGame setup count)
    (F.singleSecretMultiDDHRandomGame setup count) SingleSecretMultiDDHDistinguisher.IsPPT

/-- Executable reduction from single-secret ($n = 1$) Multi-DDH (I) to DDH ([BonehShoup2023],
Exercise 10.11, p. 426): given a single candidate DDH triple `(u, v, w)`, generate `count n`
independent pairs via `OracleComp.replicate (count n) (F.ddhFixedURerandomizeComp n d u v w)` and
pass `(u, pairs)` to `distinguisher`. -/
noncomputable def singleSecretMultiDDHToDDHDistinguisher (count : ℕ → ℕ)
    (distinguisher : F.SingleSecretMultiDDHDistinguisher) : F.DDHDistinguisher :=
  fun n d u v w => do
    let pairs ← OracleComp.replicate (count n) (F.ddhFixedURerandomizeComp n d u v w)
    distinguisher n d u pairs

/-- `singleSecretMultiDDHToDDHDistinguisher` is uniform strict PPT whenever `count` is computable
in polynomial time and `distinguisher` is PPT. -/
theorem isPPT_singleSecretMultiDDHToDDHDistinguisher {count : ℕ → ℕ}
    (hcount : ComputableInPolyTime count encUnary encUnary)
    {distinguisher : F.SingleSecretMultiDDHDistinguisher} (hD : distinguisher.IsPPT) :
    (F.singleSecretMultiDDHToDDHDistinguisher count distinguisher).IsPPT := by
  obtain ⟨W, hW, hWD⟩ := hD.exists_bool_factor F.encSingleSecretMultiDDHInput_apply
  have hrep : IsPPTOn F.encDDHInput (encList (encPair encBits encBits)) fun x =>
      OracleComp.replicate (count x.secParam)
        ((fun p => (F.encode x.groupParameters p.1, F.encode x.groupParameters p.2)) <$>
          F.ddhFixedURerandomizeComp x.secParam x.groupParameters
            x.leftPublic x.rightPublic x.candidateShared) :=
    F.isPPTOn_encode_ddhFixedURerandomizeComp_ddhInput.replicate (hcount.comp (by fun_prop))
  have hpost : IsPPTOn (encPair F.encDDHInput (encList (encPair encBits encBits))) encBool
      (fun (p : F.DDHInput × List (List Bool × List Bool)) =>
        W (p.1.secParam, p.1.groupParameters, F.encode p.1.groupParameters p.1.leftPublic,
           encList (encPair encBits encBits) p.2)) :=
    hW.preprocess (by fun_prop)
  refine (hrep.bind_pair hpost).congr fun x => ?_
  have hfun (pairs : List (F.Carrier x.groupParameters × F.Carrier x.groupParameters)) :
      distinguisher x.secParam x.groupParameters x.leftPublic pairs =
        W (x.secParam, x.groupParameters, F.encode x.groupParameters x.leftPublic,
           encList (encPair encBits encBits)
             (pairs.map fun p => (F.encode x.groupParameters p.1,
               F.encode x.groupParameters p.2))) := by
    rw [← F.encList_encCarrierPair x.groupParameters pairs]
    exact hWD ⟨x.secParam, x.groupParameters, x.leftPublic, pairs⟩
  unfold singleSecretMultiDDHToDDHDistinguisher
  simp [OracleComp.replicate_map, bind_map_left, hfun]

private theorem advantage_replicate_iid_le {α : Type} (count : ℕ)
    (prog : ProbComp α) (μ : PMF α) {c : ℝ≥0}
    (hc : ∀ k : α → Game, Game.advantage ((ProbComp.eval prog).bind k) (μ.bind k) ≤ c)
    (k : List α → Game) :
    Game.advantage
      ((ProbComp.eval (OracleComp.replicate count prog)).bind k)
      ((PMF.iid μ count).bind fun tuple => k (List.ofFn tuple)) ≤
      (count : ℝ≥0) * c := by
  induction count generalizing k with
  | zero =>
      simp [OracleComp.replicate_zero, PMF.iid, List.ofFn_zero]
  | succ m ih =>
      simp only [OracleComp.replicate_succ, PMF.iid, ProbComp.eval_bind, ProbComp.eval_map,
        PMF.monad_bind_eq_bind, PMF.bind_bind, PMF.bind_map, Function.comp_def, List.ofFn_succ]
      refine (Game.advantage_triangle _
        (μ.bind fun x =>
          (ProbComp.eval (OracleComp.replicate m prog)).bind fun xs => k (x :: xs)) _).trans ?_
      have hhead := hc fun x =>
        (ProbComp.eval (OracleComp.replicate m prog)).bind fun xs => k (x :: xs)
      have htail := Game.advantage_bind_le_nnreal μ _ _ fun x => ih (fun xs => k (x :: xs))
      calc
        _ ≤ c + (m : ℝ≥0) * c := add_le_add hhead htail
        _ = ((m + 1 : ℕ) : ℝ≥0) * c := by push_cast; ring

private theorem multiDDHRerandomizeLaw_fin_zero_map_ofFn (d : F.Desc) (u v w : F.Carrier d) :
    (F.multiDDHRerandomizeLaw d (Fin 0) u v w).map List.ofFn = PMF.pure [] := by
  simp [multiDDHRerandomizeLaw, Function.comp_def, List.ofFn_zero, PMF.map, PMF.bind_const]

private theorem multiDDHRerandomizeLaw_fin_succ_map_ofFn (d : F.Desc) (m : ℕ)
    (u v w : F.Carrier d) :
    (F.multiDDHRerandomizeLaw d (Fin (m + 1)) u v w).map List.ofFn =
      (F.ddhFixedURerandomizeLaw d u v w).bind fun x =>
        (F.multiDDHRerandomizeLaw d (Fin m) u v w).map (fun rest => x :: List.ofFn rest) := by
  unfold ddhFixedURerandomizeLaw
  rw [multiDDHRerandomizeLaw, ← Probability.PMF.pi_uniformOfFintype,
    Probability.PMF.pi_fin_succ, Probability.PMF.pi_uniformOfFintype,
    ← PMF.uniformOfFintype_prod]
  simp [multiDDHRerandomizeLaw, PMF.map_bind, PMF.bind_map, PMF.bind_bind, PMF.map_comp,
    Function.comp_def, List.ofFn_succ]

private theorem multiDDHRerandomizeLaw_fin_map_ofFn (d : F.Desc) (count : ℕ)
    (u v w : F.Carrier d) :
    (F.multiDDHRerandomizeLaw d (Fin count) u v w).map List.ofFn =
      (PMF.iid (F.ddhFixedURerandomizeLaw d u v w) count).map List.ofFn := by
  induction count with
  | zero =>
      rw [multiDDHRerandomizeLaw_fin_zero_map_ofFn]
      simp [PMF.iid, List.ofFn_zero]
  | succ m ih =>
      rw [multiDDHRerandomizeLaw_fin_succ_map_ofFn]
      have hmap :
          (fun x => (F.multiDDHRerandomizeLaw d (Fin m) u v w).map
            (fun rest => x :: List.ofFn rest)) =
          fun x => ((F.multiDDHRerandomizeLaw d (Fin m) u v w).map List.ofFn).map (x :: ·) := by
        funext x
        exact (PMF.map_comp _ _ _).symm
      rw [hmap, ih]
      simp [PMF.iid, PMF.map_bind, PMF.map_comp, Function.comp_def, List.ofFn_succ]

/-- Replacing `OracleComp.replicate count (F.ddhFixedURerandomizeComp n d u v w)` by
`F.multiDDHRerandomizeLaw d (Fin count) u v w` changes `Game.advantage` by at most
`(2 * count : ℝ≥0) / 2 ^ n`. -/
theorem advantage_replicate_ddhFixedURerandomizeComp_le (count n : ℕ) (d : F.Desc)
    (u v w : F.Carrier d) (k : List (F.Carrier d × F.Carrier d) → Game) :
    Game.advantage
      ((ProbComp.eval (OracleComp.replicate count (F.ddhFixedURerandomizeComp n d u v w))).bind k)
      ((F.multiDDHRerandomizeLaw d (Fin count) u v w).bind fun tuple => k (List.ofFn tuple)) ≤
      (2 * count : ℝ≥0) / 2 ^ n := by
  have hmap (μ : PMF (Fin count → F.Carrier d × F.Carrier d)) :
      (μ.bind fun tuple => k (List.ofFn tuple)) = (μ.map List.ofFn).bind k :=
    (PMF.bind_map _ _ _).symm
  rw [hmap, multiDDHRerandomizeLaw_fin_map_ofFn, ← hmap]
  refine (advantage_replicate_iid_le count (F.ddhFixedURerandomizeComp n d u v w)
    (F.ddhFixedURerandomizeLaw d u v w)
    (F.advantage_bind_ddhFixedURerandomizeComp_le n d u v w) k).trans_eq ?_
  ring

/-- **Sampling loss of `singleSecretMultiDDHToDDHDistinguisher`**: on any fixed triple `(u, v, w)`,
replacing `multiDDHRerandomizeLaw d (Fin (count n)) u v w` by
`singleSecretMultiDDHToDDHDistinguisher count distinguisher` changes the acceptance law by at most
`(2 * count n : ℝ≥0) / 2 ^ n`. -/
theorem advantage_multiDDHRerandomizeLaw_singleSecretMultiDDHToDDHDistinguisher_le
    (count : ℕ → ℕ) (distinguisher : F.SingleSecretMultiDDHDistinguisher) (n : ℕ) (d : F.Desc)
    (u v w : F.Carrier d) :
    Game.advantage
      ((F.multiDDHRerandomizeLaw d (Fin (count n)) u v w).bind fun tuple =>
        ProbComp.eval (distinguisher n d u (List.ofFn tuple)))
      (ProbComp.eval (F.singleSecretMultiDDHToDDHDistinguisher count distinguisher n d u v w)) ≤
      (2 * count n : ℝ≥0) / 2 ^ n := by
  rw [Game.advantage_comm]
  unfold singleSecretMultiDDHToDDHDistinguisher
  simpa only [ProbComp.eval_bind] using
    F.advantage_replicate_ddhFixedURerandomizeComp_le (count n) n d u v w
      (fun pairs => ProbComp.eval (distinguisher n d u pairs))

private theorem advantage_four_hop {gReal exactReal ddhReal ddhRandom exactRandom gRandom : Game}
    {s ord : ℝ≥0}
    (hreal : gReal = exactReal)
    (hsamp_real : Game.advantage exactReal ddhReal ≤ s)
    (hsamp_random : Game.advantage ddhRandom exactRandom ≤ s)
    (hideal : Game.advantage exactRandom gRandom ≤ ord) :
    Game.advantage gReal gRandom ≤ Game.advantage ddhReal ddhRandom + ord + 2 * s := by
  rw [hreal]
  have h1 := Game.advantage_triangle exactReal ddhReal gRandom
  have h2 := Game.advantage_triangle ddhReal ddhRandom gRandom
  have h3 := Game.advantage_triangle ddhRandom exactRandom gRandom
  have hle := (h1.trans (add_le_add le_rfl (h2.trans (add_le_add le_rfl h3)))).trans
    (add_le_add hsamp_real (add_le_add le_rfl (add_le_add hsamp_random hideal)))
  refine hle.trans_eq ?_
  ring

private theorem ddhRealGame_eq_bind_ddhRealTupleLaw (setup : ℕ → PMF F.Desc)
    (distinguisher : F.DDHDistinguisher) (n : ℕ) :
    F.ddhRealGame setup distinguisher n =
      (setup n).bind fun d =>
        (F.ddhRealTupleLaw d).bind fun (u, v, w) =>
          ProbComp.eval (distinguisher n d u v w) := by
  simp only [ddhRealGame, Game.withSetup, ddhRealExperiment, ddhRealTupleLaw,
    ProbComp.eval_uniform, pmf_norm]

private theorem ddhRandomGame_eq_bind_ddhRandomTupleLaw (setup : ℕ → PMF F.Desc)
    (distinguisher : F.DDHDistinguisher) (n : ℕ) :
    F.ddhRandomGame setup distinguisher n =
      (setup n).bind fun d =>
        (F.ddhRandomTupleLaw d).bind fun (u, v, w) =>
          ProbComp.eval (distinguisher n d u v w) := by
  simp only [ddhRandomGame, Game.withSetup, ddhRandomExperiment, ddhRandomTupleLaw,
    ProbComp.eval_uniform, pmf_norm]

/-- **Quantitative single-secret ($n = 1$) Multi-DDH (I) reduction** ([BonehShoup2023],
Exercise 10.11, p. 426): for any setup distribution `setup`, pair-count schedule `count`, and
distinguisher, the distinguishing advantage between `singleSecretMultiDDHRealGame` and
`singleSecretMultiDDHRandomGame` is bounded by the DDH advantage of
`singleSecretMultiDDHToDDHDistinguisher` plus the expected inverse group order
`(∑' d, setup n d * (F.order d)⁻¹).toNNReal` and the exponent-sampling loss
`(4 * count n : ℝ≥0) / 2 ^ n`. -/
theorem advantage_singleSecretMultiDDHGame_le (setup : ℕ → PMF F.Desc) (count : ℕ → ℕ)
    (distinguisher : F.SingleSecretMultiDDHDistinguisher) (n : ℕ) :
    Game.advantage (F.singleSecretMultiDDHRealGame setup count distinguisher n)
      (F.singleSecretMultiDDHRandomGame setup count distinguisher n) ≤
    Game.advantage
      (F.ddhRealGame setup (F.singleSecretMultiDDHToDDHDistinguisher count distinguisher) n)
      (F.ddhRandomGame setup (F.singleSecretMultiDDHToDDHDistinguisher count distinguisher) n) +
      (∑' d, setup n d * (F.order d : ℝ≥0∞)⁻¹).toNNReal +
      (4 * count n : ℝ≥0) / 2 ^ n := by
  let test (d : F.Desc) (u : F.Carrier d)
      (tuple : Fin (count n) → F.Carrier d × F.Carrier d) : Game :=
    ProbComp.eval (distinguisher n d u (List.ofFn tuple))
  let exactReal : Game :=
    (setup n).bind fun d =>
      (F.ddhRealTupleLaw d).bind fun (u, v, w) =>
        (F.multiDDHRerandomizeLaw d (Fin (count n)) u v w).bind (test d u)
  let exactRandom : Game :=
    (setup n).bind fun d =>
      (F.ddhRandomTupleLaw d).bind fun (u, v, w) =>
        (F.multiDDHRerandomizeLaw d (Fin (count n)) u v w).bind (test d u)
  have hreal_eq : F.singleSecretMultiDDHRealGame setup count distinguisher n = exactReal := by
    unfold singleSecretMultiDDHRealGame exactReal
    simp only [PMF.monad_bind_eq_bind]
    congr 1; funext d
    exact (F.ddhRealTupleLaw_bind_multiDDHRerandomizeLaw d (Fin (count n)) (test d)).symm
  have hsamp_real :
      Game.advantage exactReal
        (F.ddhRealGame setup (F.singleSecretMultiDDHToDDHDistinguisher count distinguisher) n) ≤
      (2 * count n : ℝ≥0) / 2 ^ n := by
    rw [F.ddhRealGame_eq_bind_ddhRealTupleLaw]
    refine Game.advantage_bind_le_nnreal (setup n) _ _ fun d => ?_
    refine Game.advantage_bind_le_nnreal (F.ddhRealTupleLaw d) _ _ fun ⟨u, v, w⟩ => ?_
    exact F.advantage_multiDDHRerandomizeLaw_singleSecretMultiDDHToDDHDistinguisher_le count
      distinguisher n d u v w
  have hsamp_random :
      Game.advantage
        (F.ddhRandomGame setup (F.singleSecretMultiDDHToDDHDistinguisher count distinguisher) n)
        exactRandom ≤
      (2 * count n : ℝ≥0) / 2 ^ n := by
    rw [F.ddhRandomGame_eq_bind_ddhRandomTupleLaw, Game.advantage_comm]
    refine Game.advantage_bind_le_nnreal (setup n) _ _ fun d => ?_
    refine Game.advantage_bind_le_nnreal (F.ddhRandomTupleLaw d) _ _ fun ⟨u, v, w⟩ => ?_
    exact F.advantage_multiDDHRerandomizeLaw_singleSecretMultiDDHToDDHDistinguisher_le count
      distinguisher n d u v w
  have hideal :
      Game.advantage exactRandom (F.singleSecretMultiDDHRandomGame setup count distinguisher n) ≤
        (∑' d, setup n d * (F.order d : ℝ≥0∞)⁻¹).toNNReal := by
    unfold exactRandom singleSecretMultiDDHRandomGame
    simp only [PMF.monad_bind_eq_bind]
    refine F.advantage_bind_le_expected_inv_order (setup n) _ _ fun d => ?_
    exact F.advantage_ddhRandomTupleLaw_multiDDHRerandomizeLaw_le d (Fin (count n)) (test d)
  refine (advantage_four_hop hreal_eq hsamp_real hsamp_random hideal).trans_eq ?_
  ring

/-- **Single-secret ($n = 1$) Multi-DDH (I) from DDH** ([BonehShoup2023], Section 10.11,
Exercise 10.11, p. 426): if `F.DDH setup` holds and `count : ℕ → ℕ` is computable in polynomial
time (in unary), then `F.SingleSecretMultiDDH setup count` holds. -/
theorem DDH.singleSecretMultiDDH {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc}
    {count : ℕ → ℕ} (hDDH : F.DDH setup)
    (hcount : ComputableInPolyTime count encUnary encUnary) :
    F.SingleSecretMultiDDH setup count := by
  intro distinguisher hD
  have hddh := hDDH _ (F.isPPT_singleSecretMultiDDHToDDHDistinguisher hcount hD)
  have hord := hDDH.negligible_expected_inv_order
  obtain ⟨t, _, ht, _, htm⟩ := hcount
  have hpoly : PolynomiallyBounded count := ht.mono_of_le fun n => by
    simpa using htm.length_le n
  have hsamp : Negligible fun n => (4 * count n : ℝ≥0) / 2 ^ n := by
    simpa [Nat.cast_mul] using ((PolynomiallyBounded.const 4).mul hpoly).negligible_div_two_pow
  exact negligible_of_le ((hddh.add hord).add hsamp)
    (F.advantage_singleSecretMultiDDHGame_le setup count distinguisher)

/-! ### Full two-parameter $(n, m)$ Multi-DDH (I) reduction (Exercises 10.9 & 10.11) -/

/-- Single-exponent DDH shift ([BonehShoup2023], Section 10.11, Exercise 10.9, p. 425):
given `(u, v, w)` and exponent `ρ : ZMod (F.order d)`, output
`(u', w') = (ρ • g + u, ρ • v + w)` while keeping `v` fixed. -/
@[expose] def ddhShift (d : F.Desc) (u v w : F.Carrier d)
    (ρ : ZMod (F.order d)) : F.Carrier d × F.Carrier d :=
  (ρ • F.generator d + u, ρ • v + w)

/-- Algebraic action of `ddhShift` on multiples of the generator:
`u' = (α + ρ) • g` and `w' = ((α + ρ) * β + (γ - α * β)) • g`. -/
theorem ddhShift_smul_generator (d : F.Desc) (α β γ ρ : ZMod (F.order d)) :
    F.ddhShift d (α • F.generator d) (β • F.generator d) (γ • F.generator d) ρ =
      ((α + ρ) • F.generator d, ((α + ρ) * β + (γ - α * β)) • F.generator d) := by
  simp only [ddhShift, smul_smul, ← add_smul]
  exact Prod.ext (congrArg (· • F.generator d) (add_comm ρ α))
    (congrArg (· • F.generator d) (by ring))

/-- Word-level single-exponent DDH shift on encoded group elements. -/
@[expose] def ddhWordShift (d : F.Desc) (u v w : List Bool) (ρ : ℕ) :
    List Bool × List Bool :=
  (F.add (d, F.smul (d, ρ, F.encode d (F.generator d)), u),
   F.add (d, F.smul (d, ρ, v), w))

/-- `ddhWordShift` computes the encoded output of `ddhShift`. -/
theorem ddhWordShift_encode (d : F.Desc) (u v w : F.Carrier d) (ρ : ℕ) :
    F.ddhWordShift d (F.encode d u) (F.encode d v) (F.encode d w) ρ =
      (F.encode d (F.ddhShift d u v w ρ).1,
        F.encode d (F.ddhShift d u v w ρ).2) := by
  simp [ddhWordShift, ddhShift, F.smul_encode, F.add_encode]

/-- `ddhWordShift` is computable in polynomial time. -/
theorem computableInPolyTime_ddhWordShift :
    ComputableInPolyTime
      (fun input : F.Desc × List Bool × List Bool × List Bool × ℕ =>
        F.ddhWordShift input.1 input.2.1 input.2.2.1 input.2.2.2.1 input.2.2.2.2)
      (encPair F.encDesc (encPair encBits (encPair encBits (encPair encBits encNat))))
      (encPair encBits encBits) := by
  unfold ddhWordShift
  fun_prop

variable {F} in
/-- Compositional polynomial-time certificate for `ddhWordShift`. -/
@[fun_prop] theorem computableInPolyTime_ddhWordShift_comp {α : Type}
    {enc : α ↪ List Bool} {d : α → F.Desc} {u v w : α → List Bool} {ρ : α → ℕ}
    (hd : ComputableInPolyTime d enc F.encDesc)
    (hu : ComputableInPolyTime u enc encBits)
    (hv : ComputableInPolyTime v enc encBits)
    (hw : ComputableInPolyTime w enc encBits)
    (hρ : ComputableInPolyTime ρ enc encNat) :
    ComputableInPolyTime
      (fun a => F.ddhWordShift (d a) (u a) (v a) (w a) (ρ a))
      enc (encPair encBits encBits) :=
  F.computableInPolyTime_ddhWordShift.comp (hd.prod (hu.prod (hv.prod (hw.prod hρ))))

variable {F} in
/-- The encoded pair output of `ddhShift` with a natural-number exponent is computable in
polynomial time. -/
@[fun_prop] theorem computableInPolyTime_encode_ddhShift {α : Type}
    {enc : α ↪ List Bool} {d : α → F.Desc} {u v w : (a : α) → F.Carrier (d a)} {ρ : α → ℕ}
    (hd : ComputableInPolyTime d enc F.encDesc)
    (hu : ComputableInPolyTime (fun a => F.encode (d a) (u a)) enc encBits)
    (hv : ComputableInPolyTime (fun a => F.encode (d a) (v a)) enc encBits)
    (hw : ComputableInPolyTime (fun a => F.encode (d a) (w a)) enc encBits)
    (hρ : ComputableInPolyTime ρ enc encNat) :
    ComputableInPolyTime
      (fun a =>
        (F.encode (d a) (F.ddhShift (d a) (u a) (v a) (w a) (ρ a)).1,
         F.encode (d a) (F.ddhShift (d a) (u a) (v a) (w a) (ρ a)).2))
      enc (encPair encBits encBits) :=
  .of_enc_eq (computableInPolyTime_ddhWordShift_comp hd hu hv hw hρ) fun a => by
    simp [F.ddhWordShift_encode]

/-- The real law of one secret block `(α • g, List.ofFn tuple)` with `m` pairs in
Multi-DDH (I) ([BonehShoup2023], Exercise 10.11, p. 426). -/
noncomputable def multiDDHRealBlockLaw (d : F.Desc) (m : ℕ) :
    PMF (F.Carrier d × List (F.Carrier d × F.Carrier d)) := do
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let tuple ← F.multiDDHRealTupleLaw d (Fin m) α
  return (α • F.generator d, List.ofFn tuple)

/-- The random law of one secret block `(α • g, List.ofFn tuple)` with `m` pairs in
Multi-DDH (I) ([BonehShoup2023], Exercise 10.11, p. 426). -/
noncomputable def multiDDHRandomBlockLaw (d : F.Desc) (m : ℕ) :
    PMF (F.Carrier d × List (F.Carrier d × F.Carrier d)) := do
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let tuple ← F.multiDDHRandomTupleLaw d (Fin m)
  return (α • F.generator d, List.ofFn tuple)

/-- Exact law of one shifted-and-rerandomized secret block in the Multi-DDH (I) reduction
([BonehShoup2023], Exercise 10.11, p. 426): sample `ρ ← ZMod (F.order d)`, shift `(u, v, w)` to
`(u', v, w')` via `ddhShift` (Exercise 10.9), and draw `m` rerandomized pairs via
`multiDDHRerandomizeLaw d (Fin m) u' v w'` (Exercise 10.8). -/
noncomputable def ddhShiftAndRerandomizeLaw (d : F.Desc) (m : ℕ)
    (u v w : F.Carrier d) :
    PMF (F.Carrier d × List (F.Carrier d × F.Carrier d)) := do
  let ρ ← PMF.uniformOfFintype (ZMod (F.order d))
  let (u', w') := F.ddhShift d u v w ρ
  let tuple ← F.multiDDHRerandomizeLaw d (Fin m) u' v w'
  return (u', List.ofFn tuple)

/-- On any real DDH triple `(α • g, β • g, (α * β) • g)`, `ddhShiftAndRerandomizeLaw d m`
produces `multiDDHRealBlockLaw d m` ([BonehShoup2023], Exercise 10.11). -/
theorem ddhShiftAndRerandomizeLaw_real (d : F.Desc) (m : ℕ) (α β : ZMod (F.order d)) :
    F.ddhShiftAndRerandomizeLaw d m (α • F.generator d) (β • F.generator d)
      ((α * β) • F.generator d) = F.multiDDHRealBlockLaw d m := by
  unfold ddhShiftAndRerandomizeLaw multiDDHRealBlockLaw
  simp only [ddhShift_smul_generator, sub_self, add_zero, multiDDHRerandomizeLaw_real,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  change (PMF.uniformOfFintype (ZMod (F.order d))).bind
    (((fun α' => (F.multiDDHRealTupleLaw d (Fin m) α').bind fun tuple =>
      PMF.pure (α' • F.generator d, List.ofFn tuple))) ∘ Equiv.addLeft α) = _
  rw [← PMF.bind_map, PMF.uniformOfFintype_map_equiv]

/-- On any non-DDH triple `(α • g, β • g, γ • g)` with `γ ≠ α * β`,
`ddhShiftAndRerandomizeLaw d m` produces `multiDDHRandomBlockLaw d m`
([BonehShoup2023], Exercise 10.11). -/
theorem ddhShiftAndRerandomizeLaw_random (d : F.Desc) (m : ℕ) {α β γ : ZMod (F.order d)}
    (hγ : γ ≠ α * β) :
    F.ddhShiftAndRerandomizeLaw d m (α • F.generator d) (β • F.generator d)
      (γ • F.generator d) = F.multiDDHRandomBlockLaw d m := by
  unfold ddhShiftAndRerandomizeLaw multiDDHRandomBlockLaw
  have hne (ρ : ZMod (F.order d)) : (α + ρ) * β + (γ - α * β) ≠ (α + ρ) * β := by
    intro h
    exact hγ (by linear_combination h)
  simp only [ddhShift_smul_generator, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  simp_rw [fun ρ => F.multiDDHRerandomizeLaw_random d (Fin m) (hne ρ)]
  change (PMF.uniformOfFintype (ZMod (F.order d))).bind
    (((fun α' => (F.multiDDHRandomTupleLaw d (Fin m)).bind fun tuple =>
      PMF.pure (α' • F.generator d, List.ofFn tuple))) ∘ Equiv.addLeft α) = _
  rw [← PMF.bind_map, PMF.uniformOfFintype_map_equiv]

/-- On a real DDH triple, `k` independent draws from `ddhShiftAndRerandomizeLaw d m` produce
`PMF.iid (multiDDHRealBlockLaw d m) k`. -/
theorem ddhRealTupleLaw_bind_iid_ddhShiftAndRerandomizeLaw (d : F.Desc) (k m : ℕ)
    (test : (Fin k → F.Carrier d × List (F.Carrier d × F.Carrier d)) → PMF Bool) :
    ((F.ddhRealTupleLaw d).bind fun (u, v, w) =>
      (PMF.iid (F.ddhShiftAndRerandomizeLaw d m u v w) k).bind test) =
    (PMF.iid (F.multiDDHRealBlockLaw d m) k).bind test := by
  simp only [pmf_norm, ddhRealTupleLaw, ddhShiftAndRerandomizeLaw_real, PMF.bind_const]

/-- On a random DDH triple, `k` independent draws from `ddhShiftAndRerandomizeLaw d m` agree with
`PMF.iid (multiDDHRandomBlockLaw d m) k` except on the `1 / q` fraction of triples that happen to be
valid DDH triples. -/
theorem advantage_ddhRandomTupleLaw_iid_ddhShiftAndRerandomizeLaw_le (d : F.Desc) (k m : ℕ)
    (test : (Fin k → F.Carrier d × List (F.Carrier d × F.Carrier d)) → PMF Bool) :
    Game.advantage
      ((F.ddhRandomTupleLaw d).bind fun (u, v, w) =>
        (PMF.iid (F.ddhShiftAndRerandomizeLaw d m u v w) k).bind test)
      ((PMF.iid (F.multiDDHRandomBlockLaw d m) k).bind test) ≤
    (F.order d : ℝ≥0)⁻¹ := by
  simp only [pmf_norm, ddhRandomTupleLaw]
  rw [← PMF.bind_const (PMF.uniformOfFintype (ZMod (F.order d)))
    ((PMF.iid (F.multiDDHRandomBlockLaw d m) k).bind test)]
  peel_binds α
  rw [← PMF.bind_const (PMF.uniformOfFintype (ZMod (F.order d)))
    ((PMF.iid (F.multiDDHRandomBlockLaw d m) k).bind test)]
  peel_binds β
  simpa only [ZMod.card] using
    Game.advantage_bind_uniformOfFintype_of_ne_le (α * β)
      (fun γ => (PMF.iid (F.ddhShiftAndRerandomizeLaw d m
        (α • F.generator d) (β • F.generator d) (γ • F.generator d)) k).bind test)
      ((PMF.iid (F.multiDDHRandomBlockLaw d m) k).bind test)
      (fun γ hγ => by rw [F.ddhShiftAndRerandomizeLaw_random d m hγ])

/-- Executable generation of one secret block in the Multi-DDH (I) reduction ([BonehShoup2023],
Exercise 10.11, p. 426): sample an approximate uniform exponent `ρ ← F.sampleExp n d`, shift
`(u, v, w)` to `(u', v, w')` via `F.ddhShift d u v w ρ` (Exercise 10.9), and generate `pairCount`
independent pairs for `(u', v, w')` via
`OracleComp.replicate pairCount (F.ddhFixedURerandomizeComp n d u' v w')` (Exercise 10.8). -/
noncomputable def ddhShiftAndRerandomizeComp (pairCount n : ℕ) (d : F.Desc)
    (u v w : F.Carrier d) :
    ProbComp (F.Carrier d × List (F.Carrier d × F.Carrier d)) := do
  let ρ ← F.sampleExp n d
  let (u', w') := F.ddhShift d u v w ρ
  let pairs ← OracleComp.replicate pairCount (F.ddhFixedURerandomizeComp n d u' v w')
  return (u', pairs)

private theorem isPPTOn_encode_ddhShiftAndRerandomizeComp_ddhInput {pairCount : ℕ → ℕ}
    (hpair : ComputableInPolyTime pairCount encUnary encUnary) :
    IsPPTOn F.encDDHInput (encPair encBits (encList (encPair encBits encBits))) fun x =>
      (fun (b : F.Carrier x.groupParameters ×
          List (F.Carrier x.groupParameters × F.Carrier x.groupParameters)) =>
        (F.encode x.groupParameters b.1,
          b.2.map fun p => (F.encode x.groupParameters p.1, F.encode x.groupParameters p.2))) <$>
        F.ddhShiftAndRerandomizeComp (pairCount x.secParam) x.secParam x.groupParameters
          x.leftPublic x.rightPublic x.candidateShared := by
  let E1 := encPair F.encDDHInput encNat
  let E2 := encPair E1 (encList (encPair encBits encBits))
  have hx : ComputableInPolyTime (fun q : F.DDHInput × ℕ => q.1) E1 F.encDDHInput :=
    ComputableInPolyTime.fst F.encDDHInput encNat
  have hρ : ComputableInPolyTime (fun q : F.DDHInput × ℕ => q.2) E1 encNat :=
    ComputableInPolyTime.snd F.encDDHInput encNat
  have hn : ComputableInPolyTime (fun q : F.DDHInput × ℕ => q.1.secParam) E1 encUnary :=
    (F.encDDHInput_secParam_polyTime .id').comp hx
  have hd : ComputableInPolyTime (fun q : F.DDHInput × ℕ => q.1.groupParameters) E1 F.encDesc :=
    (F.encDDHInput_groupParameters_polyTime .id').comp hx
  have hu : ComputableInPolyTime
      (fun q : F.DDHInput × ℕ => F.encode q.1.groupParameters q.1.leftPublic) E1 encBits :=
    (F.encDDHInput_leftPublic_polyTime .id').comp hx
  have hv : ComputableInPolyTime
      (fun q : F.DDHInput × ℕ => F.encode q.1.groupParameters q.1.rightPublic) E1 encBits :=
    (F.encDDHInput_rightPublic_polyTime .id').comp hx
  have hw : ComputableInPolyTime
      (fun q : F.DDHInput × ℕ => F.encode q.1.groupParameters q.1.candidateShared) E1 encBits :=
    (F.encDDHInput_candidateShared_polyTime .id').comp hx
  have hshift := computableInPolyTime_encode_ddhShift hd hu hv hw hρ
  have hu' : ComputableInPolyTime
      (fun q : F.DDHInput × ℕ =>
        F.encode q.1.groupParameters
          (F.ddhShift q.1.groupParameters q.1.leftPublic q.1.rightPublic
            q.1.candidateShared q.2).1) E1 encBits :=
    (ComputableInPolyTime.fst encBits encBits).comp hshift
  have hw' : ComputableInPolyTime
      (fun q : F.DDHInput × ℕ =>
        F.encode q.1.groupParameters
          (F.ddhShift q.1.groupParameters q.1.leftPublic q.1.rightPublic
            q.1.candidateShared q.2).2) E1 encBits :=
    (ComputableInPolyTime.snd encBits encBits).comp hshift
  have hinner := isPPTOn_encode_ddhFixedURerandomizeComp hn hd hu' hv hw'
  have hrep := hinner.replicate (hpair.comp hn)
  have hq : ComputableInPolyTime
      (fun r : (F.DDHInput × ℕ) × List (List Bool × List Bool) => r.1) E2 E1 :=
    ComputableInPolyTime.fst E1 (encList (encPair encBits encBits))
  have hpairs : ComputableInPolyTime
      (fun r : (F.DDHInput × ℕ) × List (List Bool × List Bool) => r.2)
      E2 (encList (encPair encBits encBits)) :=
    ComputableInPolyTime.snd E1 (encList (encPair encBits encBits))
  have hpair_out := (hu'.comp hq).prod hpairs
  have hsample := F.isPPTOn_sampleExp
    (F.encDDHInput_secParam_polyTime .id') (F.encDDHInput_groupParameters_polyTime .id')
  refine (hsample.bind_pair (hrep.map_pair hpair_out)).congr fun x => ?_
  unfold ddhShiftAndRerandomizeComp
  simp [OracleComp.replicate_map, map_bind]

/-- Encoding of one secret block `(u, pairs) : F.Carrier d × List (F.Carrier d × F.Carrier d)` in
Multi-DDH (I) via `encPair`. -/
@[expose] def encMultiDDHBlock (d : F.Desc) :
    F.Carrier d × List (F.Carrier d × F.Carrier d) ↪ List Bool :=
  (Function.Embedding.prodMap ⟨F.encode d, F.encode_injective d⟩
    (encList (F.encCarrierPair d))).trans (encPair encBits encBits)

@[simp] theorem encMultiDDHBlock_apply (d : F.Desc)
    (b : F.Carrier d × List (F.Carrier d × F.Carrier d)) :
    F.encMultiDDHBlock d b =
      encPair encBits encBits (F.encode d b.1, encList (F.encCarrierPair d) b.2) := rfl

/-- `encList (F.encMultiDDHBlock d)` encodes a list of secret blocks as `encList` of their encoded
first elements and encoded pair lists. -/
theorem encList_encMultiDDHBlock (d : F.Desc)
    (blocks : List (F.Carrier d × List (F.Carrier d × F.Carrier d))) :
    encList (F.encMultiDDHBlock d) blocks =
      encList (encPair encBits (encList (encPair encBits encBits)))
        (blocks.map fun b =>
          (F.encode d b.1, b.2.map fun p => (F.encode d p.1, F.encode d p.2))) := by
  simp [encList, encMultiDDHBlock, List.flatMap_map, Function.comp_def]

/-- The input of a two-parameter $(n, m)$ Multi-DDH (I) distinguisher ([BonehShoup2023],
Section 10.11, Exercise 10.11, p. 426): the security parameter, public group parameters `d`, and a
list of secret blocks `(u_i, [(v_{i,j}, w_{i,j})])`. -/
structure MultiDDHInput where
  /-- The security parameter, given to machines in unary. -/
  secParam : ℕ
  /-- Public parameters selecting the group, its prime order and generator within the family. -/
  groupParameters : F.Desc
  /-- The list of secret blocks `(u_i, [(v_{i,j}, w_{i,j})])`. -/
  blocks : List (F.Carrier groupParameters ×
    List (F.Carrier groupParameters × F.Carrier groupParameters))

/-- The encoding of a `MultiDDHInput`: the unary security parameter, the group parameters, and the
list of encoded secret blocks, each framed except the last (`encMultiDDHInput_apply`). -/
enc_structure encMultiDDHInput (F : PrimeOrderGroupFamily) : MultiDDHInput F where
  secParam : encUnary, groupParameters : F.encDesc,
  blocks : (encList (F.encMultiDDHBlock groupParameters)) using
    ((encList (F.encMultiDDHBlock groupParameters)).injective)

/-- A two-parameter $(n, m)$ Multi-DDH (I) distinguisher over the family ([BonehShoup2023],
Section 10.11, Exercise 10.11, p. 426): given the security parameter, public group parameters `d`,
and a list of secret blocks `List (F.Carrier d × List (F.Carrier d × F.Carrier d))`, it outputs a
bit. `MultiDDHDistinguisher.IsPPT` states its efficiency on encodings. -/
abbrev MultiDDHDistinguisher : Type :=
  ℕ → (d : F.Desc) → List (F.Carrier d × List (F.Carrier d × F.Carrier d)) → ProbComp Bool

variable {F} in
/-- A `MultiDDHDistinguisher` is PPT when one uniform strict PPT machine reads `encMultiDDHInput`
and writes the distinguisher's output bit. -/
def MultiDDHDistinguisher.IsPPT (distinguisher : F.MultiDDHDistinguisher) : Prop :=
  IsPPTOn F.encMultiDDHInput encBool fun x =>
    distinguisher x.secParam x.groupParameters x.blocks

variable {F} in
/-- Characterization of `MultiDDHDistinguisher.IsPPT` in terms of `IsPPTOn`. -/
@[simp] theorem MultiDDHDistinguisher.isPPT_iff (distinguisher : F.MultiDDHDistinguisher) :
    distinguisher.IsPPT ↔
      IsPPTOn F.encMultiDDHInput encBool fun x =>
        distinguisher x.secParam x.groupParameters x.blocks :=
  Iff.rfl

variable {F} in
/-- A PPT `MultiDDHDistinguisher` run on computed inputs is uniform strict PPT. -/
theorem MultiDDHDistinguisher.IsPPT.comp {distinguisher : F.MultiDDHDistinguisher}
    (hD : distinguisher.IsPPT)
    {α : Type} {enc : α ↪ List Bool} {n : α → ℕ} {d : α → F.Desc}
    {blocks : (a : α) → List (F.Carrier (d a) × List (F.Carrier (d a) × F.Carrier (d a)))}
    (hn : ComputableInPolyTime n enc encUnary)
    (hd : ComputableInPolyTime d enc F.encDesc)
    (hblocks : ComputableInPolyTime
      (fun a => encList (F.encMultiDDHBlock (d a)) (blocks a)) enc encBits) :
    IsPPTOn enc encBool fun a => distinguisher (n a) (d a) (blocks a) :=
  IsPPTOn.preprocess hD (F.encMultiDDHInput_mk_polyTime hn hd hblocks)

/-- The real two-parameter $(n, m)$ Multi-DDH (I) game with `secretCount n` secrets and
`pairCount n` pairs per secret ([BonehShoup2023], Exercise 10.11, p. 426): sample `d ← setup n` and
`secretCount n` independent real secret blocks `(α_i • g, [(β_{i,j} • g, (α_i * β_{i,j}) • g)])`
via `PMF.iid (F.multiDDHRealBlockLaw d (pairCount n)) (secretCount n)`, then pass `List.ofFn blocks`
to `distinguisher`. -/
noncomputable def multiDDHRealGame (setup : ℕ → PMF F.Desc) (secretCount pairCount : ℕ → ℕ)
    (distinguisher : F.MultiDDHDistinguisher) (n : ℕ) : Game := do
  let d ← setup n
  let blocks ← PMF.iid (F.multiDDHRealBlockLaw d (pairCount n)) (secretCount n)
  ProbComp.eval (distinguisher n d (List.ofFn blocks))

/-- The random two-parameter $(n, m)$ Multi-DDH (I) game with `secretCount n` secrets and
`pairCount n` pairs per secret ([BonehShoup2023], Exercise 10.11, p. 426): sample `d ← setup n` and
`secretCount n` independent random secret blocks `(α_i • g, [(β_{i,j} • g, γ_{i,j} • g)])` via
`PMF.iid (F.multiDDHRandomBlockLaw d (pairCount n)) (secretCount n)`, then pass `List.ofFn blocks`
to `distinguisher`. -/
noncomputable def multiDDHRandomGame (setup : ℕ → PMF F.Desc) (secretCount pairCount : ℕ → ℕ)
    (distinguisher : F.MultiDDHDistinguisher) (n : ℕ) : Game := do
  let d ← setup n
  let blocks ← PMF.iid (F.multiDDHRandomBlockLaw d (pairCount n)) (secretCount n)
  ProbComp.eval (distinguisher n d (List.ofFn blocks))

/-- The two-parameter $(n, m)$ Multi-DDH (I) assumption for a setup law, secret-count schedule
`secretCount`, and pair-count schedule `pairCount` ([BonehShoup2023], Exercise 10.11, p. 426):
every PPT `MultiDDHDistinguisher` has negligible advantage between `multiDDHRealGame` and
`multiDDHRandomGame`. -/
def MultiDDH (setup : ℕ → PMF F.Desc) (secretCount pairCount : ℕ → ℕ) : Prop :=
  Game.Indistinguishable (F.multiDDHRealGame setup secretCount pairCount)
    (F.multiDDHRandomGame setup secretCount pairCount) MultiDDHDistinguisher.IsPPT

/-- Executable reduction from two-parameter $(n, m)$ Multi-DDH (I) to DDH ([BonehShoup2023],
Exercise 10.11, p. 426): given a single candidate DDH triple `(u, v, w)`, generate `secretCount n`
independent secret blocks, each with `pairCount n` candidate pairs via `ddhShiftAndRerandomizeComp`,
and pass `blocks` to `distinguisher`. -/
noncomputable def multiDDHToDDHDistinguisher (secretCount pairCount : ℕ → ℕ)
    (distinguisher : F.MultiDDHDistinguisher) : F.DDHDistinguisher :=
  fun n d u v w => do
    let blocks ← OracleComp.replicate (secretCount n)
      (F.ddhShiftAndRerandomizeComp (pairCount n) n d u v w)
    distinguisher n d blocks

/-- `multiDDHToDDHDistinguisher` is uniform strict PPT whenever `secretCount` and `pairCount` are
computable in polynomial time and `distinguisher` is PPT. -/
theorem isPPT_multiDDHToDDHDistinguisher {secretCount pairCount : ℕ → ℕ}
    (hsecret : ComputableInPolyTime secretCount encUnary encUnary)
    (hpair : ComputableInPolyTime pairCount encUnary encUnary)
    {distinguisher : F.MultiDDHDistinguisher} (hD : distinguisher.IsPPT) :
    (F.multiDDHToDDHDistinguisher secretCount pairCount distinguisher).IsPPT := by
  obtain ⟨W, hW, hWD⟩ := hD.exists_bool_factor F.encMultiDDHInput_apply
  have hrep : IsPPTOn F.encDDHInput
      (encList (encPair encBits (encList (encPair encBits encBits)))) fun x =>
      OracleComp.replicate (secretCount x.secParam)
        ((fun (b : F.Carrier x.groupParameters ×
            List (F.Carrier x.groupParameters × F.Carrier x.groupParameters)) =>
          (F.encode x.groupParameters b.1,
            b.2.map fun p => (F.encode x.groupParameters p.1, F.encode x.groupParameters p.2))) <$>
          F.ddhShiftAndRerandomizeComp (pairCount x.secParam) x.secParam x.groupParameters
            x.leftPublic x.rightPublic x.candidateShared) :=
    (F.isPPTOn_encode_ddhShiftAndRerandomizeComp_ddhInput hpair).replicate
      (hsecret.comp (by fun_prop))
  have hpost : IsPPTOn
      (encPair F.encDDHInput (encList (encPair encBits (encList (encPair encBits encBits)))))
      encBool
      (fun (p : F.DDHInput × List (List Bool × List (List Bool × List Bool))) =>
        W (p.1.secParam, p.1.groupParameters,
           encList (encPair encBits (encList (encPair encBits encBits))) p.2)) :=
    hW.preprocess (by fun_prop)
  refine (hrep.bind_pair hpost).congr fun x => ?_
  have hfun (blocks : List (F.Carrier x.groupParameters ×
      List (F.Carrier x.groupParameters × F.Carrier x.groupParameters))) :
      distinguisher x.secParam x.groupParameters blocks =
        W (x.secParam, x.groupParameters,
           encList (encPair encBits (encList (encPair encBits encBits)))
             (blocks.map fun b =>
               (F.encode x.groupParameters b.1,
                 b.2.map fun p =>
                   (F.encode x.groupParameters p.1, F.encode x.groupParameters p.2)))) := by
    rw [← F.encList_encMultiDDHBlock x.groupParameters blocks]
    exact hWD ⟨x.secParam, x.groupParameters, blocks⟩
  unfold multiDDHToDDHDistinguisher
  simp [OracleComp.replicate_map, bind_map_left, hfun]

/-- Replacing `ddhShiftAndRerandomizeComp pairCount n d u v w` by
`ddhShiftAndRerandomizeLaw d pairCount u v w` changes `Game.advantage` by at most
`(1 + 2 * pairCount : ℝ≥0) / 2 ^ n`. -/
theorem advantage_bind_ddhShiftAndRerandomizeComp_le (pairCount n : ℕ) (d : F.Desc)
    (u v w : F.Carrier d)
    (k : F.Carrier d × List (F.Carrier d × F.Carrier d) → Game) :
    Game.advantage
      ((ProbComp.eval (F.ddhShiftAndRerandomizeComp pairCount n d u v w)).bind k)
      ((F.ddhShiftAndRerandomizeLaw d pairCount u v w).bind k) ≤
      (1 + 2 * pairCount : ℝ≥0) / 2 ^ n := by
  unfold ddhShiftAndRerandomizeComp ddhShiftAndRerandomizeLaw
  simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
  refine (Game.advantage_triangle _
    ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun ρ =>
      (ProbComp.eval (OracleComp.replicate pairCount
        (F.ddhFixedURerandomizeComp n d (F.ddhShift d u v w ρ).1 v (F.ddhShift d u v w ρ).2))).bind
        fun pairs => k ((F.ddhShift d u v w ρ).1, pairs)) _).trans ?_
  have h1 := F.advantage_bind_sampleExp_le n d fun ρ =>
    (ProbComp.eval (OracleComp.replicate pairCount
      (F.ddhFixedURerandomizeComp n d (F.ddhShift d u v w ρ).1 v (F.ddhShift d u v w ρ).2))).bind
      fun pairs => k ((F.ddhShift d u v w ρ).1, pairs)
  have h2 := Game.advantage_bind_le_nnreal (PMF.uniformOfFintype (ZMod (F.order d))) _ _ fun ρ =>
    F.advantage_replicate_ddhFixedURerandomizeComp_le pairCount n d
      (F.ddhShift d u v w ρ).1 v (F.ddhShift d u v w ρ).2
      (fun pairs => k ((F.ddhShift d u v w ρ).1, pairs))
  calc
    _ ≤ (1 : ℝ≥0) / 2 ^ n + (2 * pairCount : ℝ≥0) / 2 ^ n := add_le_add h1 h2
    _ = (1 + 2 * pairCount : ℝ≥0) / 2 ^ n := by rw [← add_div]

/-- Replacing `OracleComp.replicate secretCount (F.ddhShiftAndRerandomizeComp pairCount n d u v w)`
by `PMF.iid (F.ddhShiftAndRerandomizeLaw d pairCount u v w) secretCount` changes `Game.advantage`
by at most `(secretCount * (1 + 2 * pairCount) : ℝ≥0) / 2 ^ n`. -/
theorem advantage_replicate_ddhShiftAndRerandomizeComp_le (secretCount pairCount n : ℕ)
    (d : F.Desc) (u v w : F.Carrier d)
    (k : List (F.Carrier d × List (F.Carrier d × F.Carrier d)) → Game) :
    Game.advantage
      ((ProbComp.eval (OracleComp.replicate secretCount
        (F.ddhShiftAndRerandomizeComp pairCount n d u v w))).bind k)
      ((PMF.iid (F.ddhShiftAndRerandomizeLaw d pairCount u v w) secretCount).bind fun blocks =>
        k (List.ofFn blocks)) ≤
      (secretCount * (1 + 2 * pairCount) : ℝ≥0) / 2 ^ n := by
  refine (advantage_replicate_iid_le secretCount
    (F.ddhShiftAndRerandomizeComp pairCount n d u v w)
    (F.ddhShiftAndRerandomizeLaw d pairCount u v w)
    (F.advantage_bind_ddhShiftAndRerandomizeComp_le pairCount n d u v w) k).trans_eq ?_
  ring

/-- **Sampling loss of `multiDDHToDDHDistinguisher`**: on any fixed triple `(u, v, w)`, replacing
`PMF.iid (ddhShiftAndRerandomizeLaw d (pairCount n) u v w) (secretCount n)` by
`multiDDHToDDHDistinguisher secretCount pairCount distinguisher` changes the acceptance law by at
most `(secretCount n * (1 + 2 * pairCount n) : ℝ≥0) / 2 ^ n`. -/
theorem advantage_ddhShiftAndRerandomizeLaw_multiDDHToDDHDistinguisher_le
    (secretCount pairCount : ℕ → ℕ) (distinguisher : F.MultiDDHDistinguisher) (n : ℕ) (d : F.Desc)
    (u v w : F.Carrier d) :
    Game.advantage
      ((PMF.iid (F.ddhShiftAndRerandomizeLaw d (pairCount n) u v w) (secretCount n)).bind
        fun blocks => ProbComp.eval (distinguisher n d (List.ofFn blocks)))
      (ProbComp.eval
        (F.multiDDHToDDHDistinguisher secretCount pairCount distinguisher n d u v w)) ≤
      (secretCount n * (1 + 2 * pairCount n) : ℝ≥0) / 2 ^ n := by
  rw [Game.advantage_comm]
  unfold multiDDHToDDHDistinguisher
  simpa only [ProbComp.eval_bind] using
    F.advantage_replicate_ddhShiftAndRerandomizeComp_le (secretCount n) (pairCount n) n d u v w
      (fun blocks => ProbComp.eval (distinguisher n d blocks))

/-- **Quantitative two-parameter $(n, m)$ Multi-DDH (I) reduction** ([BonehShoup2023],
Exercise 10.11, p. 426): for any setup distribution `setup`, secret-count schedule `secretCount`,
pair-count schedule `pairCount`, and distinguisher, the distinguishing advantage between
`multiDDHRealGame` and `multiDDHRandomGame` is bounded by the DDH advantage of
`multiDDHToDDHDistinguisher` plus the expected inverse group order
`(∑' d, setup n d * (F.order d)⁻¹).toNNReal` and the exponent-sampling loss
`(2 * secretCount n * (1 + 2 * pairCount n) : ℝ≥0) / 2 ^ n`. -/
theorem advantage_multiDDHGame_le (setup : ℕ → PMF F.Desc) (secretCount pairCount : ℕ → ℕ)
    (distinguisher : F.MultiDDHDistinguisher) (n : ℕ) :
    Game.advantage (F.multiDDHRealGame setup secretCount pairCount distinguisher n)
      (F.multiDDHRandomGame setup secretCount pairCount distinguisher n) ≤
    Game.advantage
      (F.ddhRealGame setup
        (F.multiDDHToDDHDistinguisher secretCount pairCount distinguisher) n)
      (F.ddhRandomGame setup
        (F.multiDDHToDDHDistinguisher secretCount pairCount distinguisher) n) +
      (∑' d, setup n d * (F.order d : ℝ≥0∞)⁻¹).toNNReal +
      (2 * secretCount n * (1 + 2 * pairCount n) : ℝ≥0) / 2 ^ n := by
  let test (d : F.Desc)
      (blocks : Fin (secretCount n) → F.Carrier d × List (F.Carrier d × F.Carrier d)) : Game :=
    ProbComp.eval (distinguisher n d (List.ofFn blocks))
  let exactReal : Game :=
    (setup n).bind fun d =>
      (F.ddhRealTupleLaw d).bind fun (u, v, w) =>
        (PMF.iid (F.ddhShiftAndRerandomizeLaw d (pairCount n) u v w) (secretCount n)).bind
          (test d)
  let exactRandom : Game :=
    (setup n).bind fun d =>
      (F.ddhRandomTupleLaw d).bind fun (u, v, w) =>
        (PMF.iid (F.ddhShiftAndRerandomizeLaw d (pairCount n) u v w) (secretCount n)).bind
          (test d)
  have hreal_eq : F.multiDDHRealGame setup secretCount pairCount distinguisher n = exactReal := by
    unfold multiDDHRealGame exactReal
    simp only [PMF.monad_bind_eq_bind]
    congr 1; funext d
    exact (F.ddhRealTupleLaw_bind_iid_ddhShiftAndRerandomizeLaw d
      (secretCount n) (pairCount n) (test d)).symm
  have hsamp_real :
      Game.advantage exactReal
        (F.ddhRealGame setup
          (F.multiDDHToDDHDistinguisher secretCount pairCount distinguisher) n) ≤
      (secretCount n * (1 + 2 * pairCount n) : ℝ≥0) / 2 ^ n := by
    rw [F.ddhRealGame_eq_bind_ddhRealTupleLaw]
    refine Game.advantage_bind_le_nnreal (setup n) _ _ fun d => ?_
    refine Game.advantage_bind_le_nnreal (F.ddhRealTupleLaw d) _ _ fun ⟨u, v, w⟩ => ?_
    exact F.advantage_ddhShiftAndRerandomizeLaw_multiDDHToDDHDistinguisher_le secretCount
      pairCount distinguisher n d u v w
  have hsamp_random :
      Game.advantage
        (F.ddhRandomGame setup
          (F.multiDDHToDDHDistinguisher secretCount pairCount distinguisher) n)
        exactRandom ≤
      (secretCount n * (1 + 2 * pairCount n) : ℝ≥0) / 2 ^ n := by
    rw [F.ddhRandomGame_eq_bind_ddhRandomTupleLaw, Game.advantage_comm]
    refine Game.advantage_bind_le_nnreal (setup n) _ _ fun d => ?_
    refine Game.advantage_bind_le_nnreal (F.ddhRandomTupleLaw d) _ _ fun ⟨u, v, w⟩ => ?_
    exact F.advantage_ddhShiftAndRerandomizeLaw_multiDDHToDDHDistinguisher_le secretCount
      pairCount distinguisher n d u v w
  have hideal :
      Game.advantage exactRandom
        (F.multiDDHRandomGame setup secretCount pairCount distinguisher n) ≤
        (∑' d, setup n d * (F.order d : ℝ≥0∞)⁻¹).toNNReal := by
    unfold exactRandom multiDDHRandomGame
    simp only [PMF.monad_bind_eq_bind]
    refine F.advantage_bind_le_expected_inv_order (setup n) _ _ fun d => ?_
    exact F.advantage_ddhRandomTupleLaw_iid_ddhShiftAndRerandomizeLaw_le d
      (secretCount n) (pairCount n) (test d)
  refine (advantage_four_hop hreal_eq hsamp_real hsamp_random hideal).trans_eq ?_
  ring

/-- **Multi-DDH (I) from DDH** ([BonehShoup2023], Section 10.11, Exercise 10.11, p. 426):
if `F.DDH setup` holds and both `secretCount : ℕ → ℕ` and `pairCount : ℕ → ℕ` are computable in
polynomial time (in unary), then `F.MultiDDH setup secretCount pairCount` holds. -/
theorem DDH.multiDDH {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc}
    {secretCount pairCount : ℕ → ℕ} (hDDH : F.DDH setup)
    (hsecret : ComputableInPolyTime secretCount encUnary encUnary)
    (hpair : ComputableInPolyTime pairCount encUnary encUnary) :
    F.MultiDDH setup secretCount pairCount := by
  intro distinguisher hD
  have hddh := hDDH _ (F.isPPT_multiDDHToDDHDistinguisher hsecret hpair hD)
  have hord := hDDH.negligible_expected_inv_order
  obtain ⟨ts, _, hts, _, htms⟩ := hsecret
  have hpoly_s : PolynomiallyBounded secretCount := hts.mono_of_le fun n => by
    simpa using htms.length_le n
  obtain ⟨tp, _, htp, _, htmp⟩ := hpair
  have hpoly_p : PolynomiallyBounded pairCount := htp.mono_of_le fun n => by
    simpa using htmp.length_le n
  have hpoly : PolynomiallyBounded (fun n => 2 * secretCount n * (1 + 2 * pairCount n)) :=
    ((PolynomiallyBounded.const 2).mul hpoly_s).mul
      ((PolynomiallyBounded.const 1).add ((PolynomiallyBounded.const 2).mul hpoly_p))
  have hsamp : Negligible fun n => (2 * secretCount n * (1 + 2 * pairCount n) : ℝ≥0) / 2 ^ n := by
    simpa [Nat.cast_mul, Nat.cast_add] using hpoly.negligible_div_two_pow
  exact negligible_of_le ((hddh.add hord).add hsamp)
    (F.advantage_multiDDHGame_le setup secretCount pairCount distinguisher)

end Cslib.Crypto.PrimeOrderGroupFamily
