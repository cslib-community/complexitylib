/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Communication.Randomized
public import Complexity.Computability.Communication.Rectangle
public import Complexity.Probability.MutualInformation
public import Mathlib.Basic.Real.ENatENNReal
import Complexity.Probability.PMF.Map

/-!
# Information cost of communication protocols

The information cost of a protocol measures what its transcript `T` reveals about the inputs,
rather than how many bits it sends. Fix a joint law of Alice's input `X`, Bob's input `Y` and `T`.
Its *internal information cost* `I(T; X | Y) + I(T; Y | X)` (`internalInfoCost`) is what each
player learns about the other's input. Its *external information cost* `I(T; X Y)`
(`externalInfoCost`) is what an outside observer learns about both
[Braverman and Rao, Section 1][BravermanRao2011].

For a deterministic protocol `p` on inputs drawn from `μ`, the transcript is the leaf that `p`
reaches (`Protocol.leaf`), which determines and is determined by the bits sent on the way
there (`Protocol.transcriptLaw`). A private-coin protocol draws the players' random bits
uniformly and independently of the inputs (`PrivateCoin.inputLaw`, `PrivateCoin.transcriptLaw`);
its transcript is the leaf of the deterministic protocol run on inputs and random bits. A
public-coin protocol draws a deterministic protocol, and its costs are the averages of the costs
of the protocols it draws (`PublicCoin.internalInfoCost`, `PublicCoin.externalInfoCost`). This is
Braverman and Rao's public-coin convention, where the public randomness is part of the
transcript and reveals nothing about the inputs by itself
[Braverman and Rao, Lemma 3.13][BravermanRao2011].

Information is at most communication:
`internalInfoCost ≤ externalInfoCost ≤ log₂ (number of leaves) ≤ depth`. The first inequality is
proved by induction on the protocol tree. Each bit sent splits both costs by the chain rule; a
bit sent by Alice tells Bob at most what it tells an observer and tells Alice nothing, because,
given her input and the transcript so far, it is independent of Bob's input. This independence
holds because conditioning on a partial transcript keeps the law of the two players' views in the
product form `w (x, y) * α (Alice's view) * β (Bob's view)`. The last two inequalities bound
mutual information by the entropy of the transcript. With independent inputs the internal and
external costs agree (`Protocol.internalInfoCost_eq_externalInfoCost`). This is the information
identity `I(T; X Y) - (I(T; X | Y) + I(T; Y | X)) = I(X; Y) - I(X; Y | T)`
(`externalInfoCost_sub_internalInfoCost`) together with the inequality.

`PublicCoin.infoComplexity` is the least internal information cost of a public-coin protocol
solving a relation with error `ε` on every pair of inputs from `A × B`. It is at most the
public-coin communication complexity (`PublicCoin.infoComplexity_le_ecomplexity`). Braverman and
Rao instead bound the error on inputs drawn from `μ`, which they take to be supported on the input
domain, and also allow private coins. For `μ` supported on `A × B`, worst-case error at most `ε`
gives error at most `ε` on inputs drawn from `μ`, so `infoComplexity` (a stricter error requirement
over a smaller class of protocols) is an upper bound on their information complexity. Without
that hypothesis it is not: inputs outside `A × B` carry no correctness requirement. For
`A = B = ∅`, a protocol that sends nothing and outputs a fixed answer solves every relation, so
the information complexity is `0` under every `μ`.

## Main definitions

* `Cslib.Communication.internalInfoCost`, `Cslib.Communication.externalInfoCost`: the
  information costs of a joint law of inputs and transcript.
* `Cslib.Communication.Protocol.transcriptLaw`, `Cslib.Communication.PrivateCoin.inputLaw`,
  `Cslib.Communication.PrivateCoin.transcriptLaw`: the joint laws of inputs and transcript.
* `Cslib.Communication.PublicCoin.internalInfoCost`,
  `Cslib.Communication.PublicCoin.externalInfoCost`: costs of public-coin protocols.
* `Cslib.Communication.PublicCoin.infoComplexity`: information complexity of a relation.

## Main results

* `Cslib.Communication.Protocol.internalInfoCost_le_externalInfoCost`,
  `Cslib.Communication.PrivateCoin.internalInfoCost_le_externalInfoCost`,
  `Cslib.Communication.PublicCoin.internalInfoCost_le_externalInfoCost`: internal at most external.
* `Cslib.Communication.Protocol.externalInfoCost_le_depth` and its private- and public-coin
  versions, and the corresponding `internalInfoCost_le_depth`: information at most communication.
  The internal bound is [Braverman and Rao, Lemma 3.14][BravermanRao2011], strengthened by going
  through `internalInfoCost ≤ externalInfoCost`; their proof bounds each transmitted bit's two
  terms by `1` using the same per-bit independence.
* `Cslib.Communication.PublicCoin.infoComplexity_le_ecomplexity`: information complexity is at
  most communication complexity; `Cslib.Communication.PublicCoin.le_infoComplexity_iff`: lower
  bounds on information complexity are lower bounds on the cost of every solving protocol.
* `Cslib.Communication.externalInfoCost_sub_internalInfoCost`: the information identity.
* `Cslib.Communication.Protocol.internalInfoCost_eq_externalInfoCost` and its private- and
  public-coin versions: equality for independent inputs
  [Braverman and Rao, Section 1][BravermanRao2011].

## References

* [M. Braverman and A. Rao, *Information equals amortized communication*][BravermanRao2011]
-/

public section

namespace Cslib.Communication

open Cslib.Probability Cslib.Probability.PMF
open scoped ENNReal

variable {X Y Z τ τ' Ω : Type*}

/-- The **internal information cost** `I(T; X | Y) + I(T; Y | X)` of a joint law of Alice's input
`X`, Bob's input `Y` and a transcript `T`: what the players learn about each other's input. -/
noncomputable def internalInfoCost [Finite X] [Finite Y] [Finite τ] (law : PMF (X × Y × τ)) : ℝ :=
  condMutualInfo (law.map fun (x, y, t) => (y, x, t)) + condMutualInfo law

/-- The **external information cost** `I(T; X Y)` of a joint law of Alice's input `X`, Bob's
input `Y` and a transcript `T`: what an observer learns about the inputs. -/
noncomputable def externalInfoCost [Finite X] [Finite Y] [Finite τ] (law : PMF (X × Y × τ)) : ℝ :=
  mutualInfo (law.map fun (x, y, t) => ((x, y), t))

section Law

variable [Finite X] [Finite Y] [Finite τ] [Finite τ']

theorem internalInfoCost_map (ν : PMF Ω) (A : Ω → X) (B : Ω → Y) (T : Ω → τ) :
    internalInfoCost (ν.map fun ω => (A ω, B ω, T ω)) =
      condMutualInfo (ν.map fun ω => (B ω, A ω, T ω)) +
        condMutualInfo (ν.map fun ω => (A ω, B ω, T ω)) := by
  rw [internalInfoCost, PMF.map_comp]
  rfl

theorem externalInfoCost_map (ν : PMF Ω) (A : Ω → X) (B : Ω → Y) (T : Ω → τ) :
    externalInfoCost (ν.map fun ω => (A ω, B ω, T ω)) =
      mutualInfo (ν.map fun ω => ((A ω, B ω), T ω)) := by
  rw [externalInfoCost, PMF.map_comp]
  rfl

theorem internalInfoCost_nonneg (law : PMF (X × Y × τ)) : 0 ≤ internalInfoCost law :=
  add_nonneg (condMutualInfo_nonneg _) (condMutualInfo_nonneg _)

theorem externalInfoCost_nonneg (law : PMF (X × Y × τ)) : 0 ≤ externalInfoCost law :=
  mutualInfo_nonneg _

/-- The external information cost is at most the logarithm of the number of transcripts. -/
theorem externalInfoCost_le_logb_card [Fintype τ] (law : PMF (X × Y × τ)) :
    externalInfoCost law ≤ Real.logb 2 (Fintype.card τ) :=
  (mutualInfo_le_entropy_map_snd _).trans (entropy_le_log_card _)

/-- Re-encoding the transcript injectively on the support does not change the internal
information cost. -/
theorem internalInfoCost_map_congr (ν : PMF Ω) (A : Ω → X) (B : Ω → Y) {T : Ω → τ}
    {T' : Ω → τ'} {e : τ → τ'} (he : Function.Injective e)
    (h : ∀ ω ∈ ν.support, T' ω = e (T ω)) :
    internalInfoCost (ν.map fun ω => (A ω, B ω, T' ω)) =
      internalInfoCost (ν.map fun ω => (A ω, B ω, T ω)) := by
  rw [internalInfoCost_map, internalInfoCost_map, condMutualInfo_map_congr ν B A he h,
    condMutualInfo_map_congr ν A B he h]

/-- Re-encoding the transcript injectively on the support does not change the external
information cost. -/
theorem externalInfoCost_map_congr (ν : PMF Ω) (A : Ω → X) (B : Ω → Y) {T : Ω → τ}
    {T' : Ω → τ'} {e : τ → τ'} (he : Function.Injective e)
    (h : ∀ ω ∈ ν.support, T' ω = e (T ω)) :
    externalInfoCost (ν.map fun ω => (A ω, B ω, T' ω)) =
      externalInfoCost (ν.map fun ω => (A ω, B ω, T ω)) := by
  rw [externalInfoCost_map, externalInfoCost_map,
    mutualInfo_map_congr ν (fun ω => (A ω, B ω)) he h]

/-- **Information identity**: the external information cost exceeds the internal one by
`I(X; Y) - I(X; Y | T)`. -/
theorem externalInfoCost_sub_internalInfoCost (law : PMF (X × Y × τ)) :
    externalInfoCost law - internalInfoCost law =
      mutualInfo (law.map fun (x, y, _) => (x, y)) -
        condMutualInfo (law.map fun (x, y, t) => (t, x, y)) := by
  have hl : law = law.map fun q => (q.1, q.2.1, q.2.2) := (PMF.map_id law).symm
  rw [hl, externalInfoCost_map, internalInfoCost_map, PMF.map_comp, PMF.map_comp,
    condMutualInfo_map, condMutualInfo_map, condMutualInfo_map, mutualInfo_map,
    mutualInfo_map]
  simp only [Function.comp_def]
  have e1 := entropy_map_eq_of_comp law (F := fun q : X × Y × τ => (q.1, q.2.1))
    (G := fun q => (q.2.1, q.1)) (e := Prod.swap) Prod.swap_injective (fun _ _ => rfl)
  have e2 := entropy_map_eq_of_comp law (F := fun q : X × Y × τ => (q.1, q.2.1, q.2.2))
    (G := fun q => (q.2.1, q.1, q.2.2)) (e := fun t => (t.2.1, t.1, t.2.2))
    (fun s t h => by
      obtain ⟨_, _, _⟩ := s
      obtain ⟨_, _, _⟩ := t
      simp only [Prod.mk.injEq] at h
      simp [h]) (fun _ _ => rfl)
  have e3 := entropy_map_eq_of_comp law (F := fun q : X × Y × τ => (q.1, q.2.1, q.2.2))
    (G := fun q => ((q.1, q.2.1), q.2.2)) (e := fun t => ((t.1, t.2.1), t.2.2))
    (fun s t h => by
      obtain ⟨_, _, _⟩ := s
      obtain ⟨_, _, _⟩ := t
      simp only [Prod.mk.injEq] at h
      simp [h]) (fun _ _ => rfl)
  have e4 := entropy_map_eq_of_comp law (F := fun q : X × Y × τ => (q.1, q.2.1, q.2.2))
    (G := fun q => (q.2.2, q.1, q.2.1)) (e := fun t => (t.2.2, t.1, t.2.1))
    (fun s t h => by
      obtain ⟨_, _, _⟩ := s
      obtain ⟨_, _, _⟩ := t
      simp only [Prod.mk.injEq] at h
      simp [h]) (fun _ _ => rfl)
  have e5 := entropy_map_eq_of_comp law (F := fun q : X × Y × τ => (q.1, q.2.2))
    (G := fun q => (q.2.2, q.1)) (e := Prod.swap) Prod.swap_injective (fun _ _ => rfl)
  have e6 := entropy_map_eq_of_comp law (F := fun q : X × Y × τ => (q.2.1, q.2.2))
    (G := fun q => (q.2.2, q.2.1)) (e := Prod.swap) Prod.swap_injective (fun _ _ => rfl)
  linarith

/-- With independent inputs, `internalInfoCost ≤ externalInfoCost` is an equality. -/
theorem internalInfoCost_eq_of_mutualInfo_eq_zero (law : PMF (X × Y × τ))
    (hle : internalInfoCost law ≤ externalInfoCost law)
    (h : mutualInfo (law.map fun (x, y, _) => (x, y)) = 0) :
    internalInfoCost law = externalInfoCost law := by
  have := externalInfoCost_sub_internalInfoCost law
  have := condMutualInfo_nonneg (law.map fun (x, y, t) => (t, x, y))
  linarith

end Law

/-! ### Information is at most external information

Proof plumbing for the induction on the protocol tree. The players' views `u : U` and `v : V`
contain their inputs `fx u` and `fy v` (and, for private coins, their random bits). -/

section Core

variable {U V : Type*}

/-- The law of the views has the product form `w (fx u) (fy v) * α u * β v`. -/
private def ProductForm (fx : U → X) (fy : V → Y) (ν : PMF (U × V)) : Prop :=
  ∃ (w : X → Y → ℝ≥0∞) (α : U → ℝ≥0∞) (β : V → ℝ≥0∞),
    ∀ u v, ν (u, v) = w (fx u) (fy v) * α u * β v

variable {fx : U → X} {fy : V → Y}

/-- Conditioning on a bit of Alice keeps the product form. -/
private theorem productForm_conditionalSnd_alice {ν : PMF (U × V)} (hν : ProductForm fx fy ν)
    (s : U → Bool) {c : Bool} (hc : ν.map (fun ω => s ω.1) c ≠ 0) :
    ProductForm fx fy (conditionalSnd (ν.map fun ω => (s ω.1, ω)) c) := by
  obtain ⟨w, α, β, hν⟩ := hν
  refine ⟨fun x y => w x y / ν.map (fun ω => s ω.1) c, fun u => if s u = c then α u else 0, β,
    fun u v => ?_⟩
  rw [conditionalSnd_map_prodMk_apply ν (fun ω => s ω.1) hc]
  dsimp only
  by_cases h : s u = c
  · rw [ite_eq_left h, ite_eq_left h, hν, div_eq_mul_inv, div_eq_mul_inv]
    ring
  · rw [ite_eq_right h, ite_eq_right h, ENNReal.zero_div, mul_zero, zero_mul]

/-- Conditioning on a bit of Bob keeps the product form. -/
private theorem productForm_conditionalSnd_bob {ν : PMF (U × V)} (hν : ProductForm fx fy ν)
    (s : V → Bool) {c : Bool} (hc : ν.map (fun ω => s ω.2) c ≠ 0) :
    ProductForm fx fy (conditionalSnd (ν.map fun ω => (s ω.2, ω)) c) := by
  obtain ⟨w, α, β, hν⟩ := hν
  refine ⟨fun x y => w x y / ν.map (fun ω => s ω.2) c, α, fun v => if s v = c then β v else 0,
    fun u v => ?_⟩
  rw [conditionalSnd_map_prodMk_apply ν (fun ω => s ω.2) hc]
  dsimp only
  by_cases h : s v = c
  · rw [ite_eq_left h, ite_eq_left h, hν, div_eq_mul_inv, div_eq_mul_inv]
    ring
  · rw [ite_eq_right h, ite_eq_right h, ENNReal.zero_div, mul_zero]

variable [Finite U] [Finite V] [Finite X] [Finite Y]

/-- Given her input, a bit of Alice is independent of Bob's input: `I(Y; s | X) = 0`. -/
private theorem condMutualInfo_eq_zero_alice {ν : PMF (U × V)} (hν : ProductForm fx fy ν)
    (s : U → Bool) :
    condMutualInfo (ν.map fun ω => (fx ω.1, fy ω.2, s ω.1)) = 0 := by
  classical
  let := Fintype.ofFinite U
  let := Fintype.ofFinite V
  obtain ⟨w, α, β, hν⟩ := hν
  refine condMutualInfo_eq_zero_of_apply_eq_mul _
    (fun x y => w x y * ∑ v, if y = fy v then β v else 0)
    (fun x c => ∑ u, if x = fx u ∧ c = s u then α u else 0) fun x y c => ?_
  have key : ∀ u v, (if (x, y, c) = (fx u, fy v, s u) then ν (u, v) else 0) =
      (if x = fx u ∧ c = s u then α u else 0) * (w x y * if y = fy v then β v else 0) := by
    intro u v
    by_cases h1 : x = fx u ∧ c = s u
    · obtain ⟨rfl, rfl⟩ := h1
      by_cases h2 : y = fy v
      · subst h2
        rw [ite_eq_left rfl, ite_eq_left ⟨rfl, rfl⟩, ite_eq_left rfl, hν]
        ring
      · rw [ite_eq_right (fun h => h2 (congrArg (fun t => t.2.1) h)), ite_eq_right h2, mul_zero,
          mul_zero]
    · rw [ite_eq_right (fun h => h1 ⟨congrArg (fun t => t.1) h, congrArg (fun t => t.2.2) h⟩),
        ite_eq_right h1, zero_mul]
  calc _ = ∑ u, ∑ v,
        (if x = fx u ∧ c = s u then α u else 0) * (w x y * if y = fy v then β v else 0) := by
        rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
        exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by convert key u v
    _ = _ := by
        simp only [← Finset.mul_sum, ← Finset.sum_mul]
        ring

/-- Given his input, a bit of Bob is independent of Alice's input: `I(X; s | Y) = 0`. -/
private theorem condMutualInfo_eq_zero_bob {ν : PMF (U × V)} (hν : ProductForm fx fy ν)
    (s : V → Bool) :
    condMutualInfo (ν.map fun ω => (fy ω.2, fx ω.1, s ω.2)) = 0 := by
  classical
  let := Fintype.ofFinite U
  let := Fintype.ofFinite V
  obtain ⟨w, α, β, hν⟩ := hν
  refine condMutualInfo_eq_zero_of_apply_eq_mul _
    (fun y x => w x y * ∑ u, if x = fx u then α u else 0)
    (fun y c => ∑ v, if y = fy v ∧ c = s v then β v else 0) fun y x c => ?_
  have key : ∀ u v, (if (y, x, c) = (fy v, fx u, s v) then ν (u, v) else 0) =
      (if x = fx u then α u else 0) * (w x y * if y = fy v ∧ c = s v then β v else 0) := by
    intro u v
    by_cases h1 : y = fy v ∧ c = s v
    · obtain ⟨rfl, rfl⟩ := h1
      by_cases h2 : x = fx u
      · subst h2
        rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_left ⟨rfl, rfl⟩, hν]
        ring
      · rw [ite_eq_right (fun h => h2 (congrArg (fun t => t.2.1) h)), ite_eq_right h2, zero_mul]
    · rw [ite_eq_right (fun h => h1 ⟨congrArg (fun t => t.1) h, congrArg (fun t => t.2.2) h⟩),
        ite_eq_right h1, mul_zero, mul_zero]
  calc _ = ∑ u, ∑ v,
        (if x = fx u then α u else 0) * (w x y * if y = fy v ∧ c = s v then β v else 0) := by
        rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
        exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by convert key u v
    _ = _ := by
        simp only [← Finset.mul_sum, ← Finset.sum_mul]
        ring

end Core

section Step

variable [Finite X] [Finite Y]

/-- One step of the induction: a bit `Bit = k ∘ T`, independent of one player's input given the
other's. -/
private theorem internalInfoCost_le_of_step {n : ℕ} (ν : PMF Ω) (A : Ω → X) (B : Ω → Y)
    (T : Ω → Fin n) (Bit : Ω → Bool) (k : Fin n → Bool) (hk : ∀ ω, Bit ω = k (T ω))
    (hbit : condMutualInfo (ν.map fun ω => (A ω, B ω, Bit ω)) = 0 ∨
      condMutualInfo (ν.map fun ω => (B ω, A ω, Bit ω)) = 0)
    (hbranch : ∀ c, ((ν.map Bit) c).toReal *
        internalInfoCost ((conditionalSnd (ν.map fun ω => (Bit ω, ω)) c).map
          fun ω => (A ω, B ω, T ω)) ≤
      ((ν.map Bit) c).toReal *
        externalInfoCost ((conditionalSnd (ν.map fun ω => (Bit ω, ω)) c).map
          fun ω => (A ω, B ω, T ω))) :
    internalInfoCost (ν.map fun ω => (A ω, B ω, T ω)) ≤
      externalInfoCost (ν.map fun ω => (A ω, B ω, T ω)) := by
  rw [internalInfoCost_map, externalInfoCost_map,
    condMutualInfo_map_eq_add_sum ν B A T Bit k hk,
    condMutualInfo_map_eq_add_sum ν A B T Bit k hk,
    mutualInfo_map_eq_add_sum ν (fun ω => (A ω, B ω)) T Bit k hk]
  have hb : condMutualInfo (ν.map fun ω => (B ω, A ω, Bit ω)) +
      condMutualInfo (ν.map fun ω => (A ω, B ω, Bit ω)) ≤
        mutualInfo (ν.map fun ω => ((A ω, B ω), Bit ω)) := by
    rcases hbit with h | h
    · rw [h, add_zero, ← mutualInfo_map_swap_left ν A B Bit]
      exact condMutualInfo_map_le_mutualInfo ν B A Bit
    · rw [h, zero_add]
      exact condMutualInfo_map_le_mutualInfo ν A B Bit
  have hs : ∑ c, ((ν.map Bit) c).toReal *
        condMutualInfo ((conditionalSnd (ν.map fun ω => (Bit ω, ω)) c).map
          fun ω => (B ω, A ω, T ω)) +
      ∑ c, ((ν.map Bit) c).toReal *
        condMutualInfo ((conditionalSnd (ν.map fun ω => (Bit ω, ω)) c).map
          fun ω => (A ω, B ω, T ω)) ≤
      ∑ c, ((ν.map Bit) c).toReal *
        mutualInfo ((conditionalSnd (ν.map fun ω => (Bit ω, ω)) c).map
          fun ω => ((A ω, B ω), T ω)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun c _ => ?_
    have := hbranch c
    rw [internalInfoCost_map, externalInfoCost_map] at this
    linarith
  linarith

/-- The branch of the step where the bit equals `c`, from the induction hypothesis on the
subprotocol continuing there. -/
private theorem branch_le {n m : ℕ} (ν : PMF Ω) (A : Ω → X) (B : Ω → Y) (T : Ω → Fin n)
    (Bit : Ω → Bool) (c : Bool) (L : Ω → Fin m) {e : Fin m → Fin n}
    (he : Function.Injective e) (hT : ∀ ω, Bit ω = c → T ω = e (L ω))
    (ih : (ν.map Bit) c ≠ 0 →
      internalInfoCost ((conditionalSnd (ν.map fun ω => (Bit ω, ω)) c).map
          fun ω => (A ω, B ω, L ω)) ≤
        externalInfoCost ((conditionalSnd (ν.map fun ω => (Bit ω, ω)) c).map
          fun ω => (A ω, B ω, L ω))) :
    ((ν.map Bit) c).toReal *
        internalInfoCost ((conditionalSnd (ν.map fun ω => (Bit ω, ω)) c).map
          fun ω => (A ω, B ω, T ω)) ≤
      ((ν.map Bit) c).toReal *
        externalInfoCost ((conditionalSnd (ν.map fun ω => (Bit ω, ω)) c).map
          fun ω => (A ω, B ω, T ω)) := by
  by_cases hc : (ν.map Bit) c = 0
  · simp [hc]
  have hsupp : ∀ ω ∈ (conditionalSnd (ν.map fun ω => (Bit ω, ω)) c).support,
      T ω = e (L ω) := fun ω hω => hT ω (eq_of_mem_support_conditionalSnd_map ν Bit hc hω)
  rw [internalInfoCost_map_congr _ A B he hsupp, externalInfoCost_map_congr _ A B he hsupp]
  exact mul_le_mul_of_nonneg_left (ih hc) ENNReal.toReal_nonneg

end Step

section Main

variable {U V : Type*} [Finite U] [Finite V] [Finite X] [Finite Y]

/-- Internal at most external information, for the leaf of a protocol on views of product
form. -/
private theorem internalInfoCost_le_externalInfoCost_aux (fx : U → X) (fy : V → Y) :
    ∀ (p : Protocol U V Z) (ν : PMF (U × V)), ProductForm fx fy ν →
      internalInfoCost (ν.map fun ω => (fx ω.1, fy ω.2, p.leaf ω.1 ω.2)) ≤
        externalInfoCost (ν.map fun ω => (fx ω.1, fy ω.2, p.leaf ω.1 ω.2))
  | .output z, ν, _ => by
    rw [internalInfoCost_map,
      condMutualInfo_map_eq_zero_of_determined ν (fun ω => fy ω.2) (fun ω => fx ω.1)
        (fun ω => (Protocol.output z : Protocol U V Z).leaf ω.1 ω.2)
        (fun _ => ⟨0, Nat.zero_lt_one⟩) (fun _ _ => rfl),
      condMutualInfo_map_eq_zero_of_determined ν (fun ω => fx ω.1) (fun ω => fy ω.2)
        (fun ω => (Protocol.output z : Protocol U V Z).leaf ω.1 ω.2)
        (fun _ => ⟨0, Nat.zero_lt_one⟩) (fun _ _ => rfl), add_zero]
    exact externalInfoCost_nonneg _
  | .alice s p₀ p₁, ν, hν => by
    refine internalInfoCost_le_of_step ν _ _ _ (fun ω => s ω.1)
      (fun i => decide (p₀.leafCount ≤ i.val)) (fun ω => ?_)
      (Or.inl (condMutualInfo_eq_zero_alice hν s)) fun c => ?_
    · rw [Protocol.leaf_alice]
      cases s ω.1 <;> simp
    · cases c
      · exact branch_le ν _ _ _ _ false (fun ω => p₀.leaf ω.1 ω.2)
          (Fin.castAdd_injective _ _) (fun ω h => by rw [Protocol.leaf_alice]; simp [h])
          fun hc => internalInfoCost_le_externalInfoCost_aux fx fy p₀ _
            (productForm_conditionalSnd_alice hν s hc)
      · exact branch_le ν _ _ _ _ true (fun ω => p₁.leaf ω.1 ω.2)
          (Fin.natAdd_injective _ _) (fun ω h => by rw [Protocol.leaf_alice]; simp [h])
          fun hc => internalInfoCost_le_externalInfoCost_aux fx fy p₁ _
            (productForm_conditionalSnd_alice hν s hc)
  | .bob s p₀ p₁, ν, hν => by
    refine internalInfoCost_le_of_step ν _ _ _ (fun ω => s ω.2)
      (fun i => decide (p₀.leafCount ≤ i.val)) (fun ω => ?_)
      (Or.inr (condMutualInfo_eq_zero_bob hν s)) fun c => ?_
    · rw [Protocol.leaf_bob]
      cases s ω.2 <;> simp
    · cases c
      · exact branch_le ν _ _ _ _ false (fun ω => p₀.leaf ω.1 ω.2)
          (Fin.castAdd_injective _ _) (fun ω h => by rw [Protocol.leaf_bob]; simp [h])
          fun hc => internalInfoCost_le_externalInfoCost_aux fx fy p₀ _
            (productForm_conditionalSnd_bob hν s hc)
      · exact branch_le ν _ _ _ _ true (fun ω => p₁.leaf ω.1 ω.2)
          (Fin.natAdd_injective _ _) (fun ω h => by rw [Protocol.leaf_bob]; simp [h])
          fun hc => internalInfoCost_le_externalInfoCost_aux fx fy p₁ _
            (productForm_conditionalSnd_bob hν s hc)

end Main

/-! ### Deterministic protocols -/

namespace Protocol

/-- `log₂` of the number of leaves is at most the depth. -/
theorem logb_leafCount_le_depth (p : Protocol X Y Z) : Real.logb 2 p.leafCount ≤ p.depth := by
  calc Real.logb 2 p.leafCount ≤ Real.logb 2 ((2 : ℝ) ^ p.depth) :=
        Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast p.leafCount_pos)
          (by exact_mod_cast p.leafCount_le_two_pow_depth)
    _ = p.depth := by rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]

/-- The joint law of Alice's input, Bob's input and the leaf that `p` reaches, on inputs drawn
from `μ`. -/
noncomputable def transcriptLaw (p : Protocol X Y Z) (μ : PMF (X × Y)) :
    PMF (X × Y × Fin p.leafCount) :=
  μ.map fun q => (q.1, q.2, p.leaf q.1 q.2)

theorem transcriptLaw_eq (p : Protocol X Y Z) (μ : PMF (X × Y)) :
    p.transcriptLaw μ = μ.map fun q => (q.1, q.2, p.leaf q.1 q.2) := by
  rw [transcriptLaw]

/-- The inputs of the transcript law are drawn from `μ`. -/
theorem map_transcriptLaw (p : Protocol X Y Z) (μ : PMF (X × Y)) :
    (p.transcriptLaw μ).map (fun (x, y, _) => (x, y)) = μ := by
  rw [transcriptLaw, PMF.map_comp]
  exact PMF.map_id μ

variable [Finite X] [Finite Y]

/-- The internal information cost of a deterministic protocol is at most its external
information cost. -/
theorem internalInfoCost_le_externalInfoCost (p : Protocol X Y Z) (μ : PMF (X × Y)) :
    internalInfoCost (p.transcriptLaw μ) ≤ externalInfoCost (p.transcriptLaw μ) := by
  rw [transcriptLaw_eq]
  exact internalInfoCost_le_externalInfoCost_aux id id p μ
    ⟨fun x y => μ (x, y), fun _ => 1, fun _ => 1, fun u v => by simp⟩

/-- **Information is at most communication** for deterministic protocols. -/
theorem externalInfoCost_le_depth (p : Protocol X Y Z) (μ : PMF (X × Y)) :
    externalInfoCost (p.transcriptLaw μ) ≤ p.depth :=
  (externalInfoCost_le_logb_card _).trans (by simpa using p.logb_leafCount_le_depth)

theorem internalInfoCost_le_depth (p : Protocol X Y Z) (μ : PMF (X × Y)) :
    internalInfoCost (p.transcriptLaw μ) ≤ p.depth :=
  (p.internalInfoCost_le_externalInfoCost μ).trans (p.externalInfoCost_le_depth μ)

/-- With independent inputs, the internal and external information costs agree. -/
theorem internalInfoCost_eq_externalInfoCost (p : Protocol X Y Z) (μ : PMF (X × Y))
    (hμ : mutualInfo μ = 0) :
    internalInfoCost (p.transcriptLaw μ) = externalInfoCost (p.transcriptLaw μ) :=
  internalInfoCost_eq_of_mutualInfo_eq_zero _ (p.internalInfoCost_le_externalInfoCost μ)
    (by rw [map_transcriptLaw]; exact hμ)

end Protocol

/-! ### Private-coin protocols -/

namespace PrivateCoin

variable {a b : ℕ}

/-- Inputs drawn from `μ`, together with independent uniformly random bit strings for Alice and
Bob. -/
noncomputable def inputLaw (a b : ℕ) (μ : PMF (X × Y)) :
    PMF ((X × BitString a) × Y × BitString b) :=
  (μ.bind fun q => (PMF.uniformOfFintype (BitString a × BitString b)).map (q, ·)).map
    (Equiv.prodProdProdComm X Y (BitString a) (BitString b))

theorem inputLaw_apply (μ : PMF (X × Y)) (x : X) (r : BitString a) (y : Y) (r' : BitString b) :
    inputLaw a b μ ((x, r), y, r') =
      μ (x, y) * (Fintype.card (BitString a × BitString b) : ℝ≥0∞)⁻¹ := by
  rw [inputLaw, map_equiv_apply]
  exact (bind_map_prodMk_apply μ _ ((x, y), (r, r'))).trans
    (by rw [PMF.uniformOfFintype_apply])

/-- The joint law of Alice's input, Bob's input and the leaf that the private-coin protocol `P`
reaches, on inputs drawn from `μ` and uniformly random bits. -/
noncomputable def transcriptLaw (P : PrivateCoin a b X Y Z) (μ : PMF (X × Y)) :
    PMF (X × Y × Fin P.leafCount) :=
  (inputLaw a b μ).map fun (u, v) => (u.1, v.1, P.leaf u v)

theorem transcriptLaw_eq (P : PrivateCoin a b X Y Z) (μ : PMF (X × Y)) :
    P.transcriptLaw μ = (inputLaw a b μ).map fun (u, v) => (u.1, v.1, P.leaf u v) := by
  rw [transcriptLaw]

/-- The inputs of the transcript law are drawn from `μ`. -/
theorem map_transcriptLaw (P : PrivateCoin a b X Y Z) (μ : PMF (X × Y)) :
    (P.transcriptLaw μ).map (fun (x, y, _) => (x, y)) = μ := by
  rw [transcriptLaw, PMF.map_comp, inputLaw, PMF.map_comp]
  exact map_fst_bind_pair μ _

variable [Finite X] [Finite Y]

/-- The internal information cost of a private-coin protocol is at most its external
information cost. -/
theorem internalInfoCost_le_externalInfoCost (P : PrivateCoin a b X Y Z) (μ : PMF (X × Y)) :
    internalInfoCost (P.transcriptLaw μ) ≤ externalInfoCost (P.transcriptLaw μ) := by
  rw [transcriptLaw_eq]
  exact internalInfoCost_le_externalInfoCost_aux Prod.fst Prod.fst P (inputLaw a b μ)
    ⟨fun x y => μ (x, y), fun _ => (Fintype.card (BitString a × BitString b) : ℝ≥0∞)⁻¹,
      fun _ => 1, fun u v => by rw [inputLaw_apply, mul_one]⟩

/-- **Information is at most communication** for private-coin protocols. -/
theorem externalInfoCost_le_depth (P : PrivateCoin a b X Y Z) (μ : PMF (X × Y)) :
    externalInfoCost (P.transcriptLaw μ) ≤ P.depth :=
  (externalInfoCost_le_logb_card _).trans (by simpa using P.logb_leafCount_le_depth)

theorem internalInfoCost_le_depth (P : PrivateCoin a b X Y Z) (μ : PMF (X × Y)) :
    internalInfoCost (P.transcriptLaw μ) ≤ P.depth :=
  (P.internalInfoCost_le_externalInfoCost μ).trans (P.externalInfoCost_le_depth μ)

/-- With independent inputs, the internal and external information costs agree. -/
theorem internalInfoCost_eq_externalInfoCost (P : PrivateCoin a b X Y Z) (μ : PMF (X × Y))
    (hμ : mutualInfo μ = 0) :
    internalInfoCost (P.transcriptLaw μ) = externalInfoCost (P.transcriptLaw μ) :=
  internalInfoCost_eq_of_mutualInfo_eq_zero _ (P.internalInfoCost_le_externalInfoCost μ)
    (by rw [map_transcriptLaw]; exact hμ)

end PrivateCoin

/-! ### Public-coin protocols -/

namespace PublicCoin

variable [Finite X] [Finite Y]

/-- The internal information cost of a public-coin protocol: the average over the public coins
of the internal information cost of the deterministic protocol they select. It is valued in
`ℝ≥0∞`, like `PublicCoin.depth` and the public-coin communication complexity, so that the average
over a countable support needs no summability side condition; the deterministic costs are real and
enter through `ENNReal.ofReal`. -/
noncomputable def internalInfoCost (π : PublicCoin X Y Z) (μ : PMF (X × Y)) : ℝ≥0∞ :=
  ∑' p, π p * ENNReal.ofReal (Communication.internalInfoCost (p.transcriptLaw μ))

/-- The external information cost of a public-coin protocol: the average over the public coins
of the external information cost of the deterministic protocol they select, valued in `ℝ≥0∞`
like `PublicCoin.internalInfoCost`. -/
noncomputable def externalInfoCost (π : PublicCoin X Y Z) (μ : PMF (X × Y)) : ℝ≥0∞ :=
  ∑' p, π p * ENNReal.ofReal (Communication.externalInfoCost (p.transcriptLaw μ))

@[simp] theorem internalInfoCost_pure (p : Protocol X Y Z) (μ : PMF (X × Y)) :
    internalInfoCost (PMF.pure p) μ =
      ENNReal.ofReal (Communication.internalInfoCost (p.transcriptLaw μ)) := by
  classical
  simp [internalInfoCost, PMF.pure_apply]

@[simp] theorem externalInfoCost_pure (p : Protocol X Y Z) (μ : PMF (X × Y)) :
    externalInfoCost (PMF.pure p) μ =
      ENNReal.ofReal (Communication.externalInfoCost (p.transcriptLaw μ)) := by
  classical
  simp [externalInfoCost, PMF.pure_apply]

/-- The internal information cost of a public-coin protocol is at most its external
information cost. -/
theorem internalInfoCost_le_externalInfoCost (π : PublicCoin X Y Z) (μ : PMF (X × Y)) :
    π.internalInfoCost μ ≤ π.externalInfoCost μ := by
  refine tsum_le_tsum fun p => ?_
  gcongr
  exact p.internalInfoCost_le_externalInfoCost μ

/-- **Information is at most communication** for public-coin protocols. -/
theorem externalInfoCost_le_depth (π : PublicCoin X Y Z) (μ : PMF (X × Y)) :
    π.externalInfoCost μ ≤ π.depth := by
  calc π.externalInfoCost μ ≤ ∑' p, π p * (π.depth : ℝ≥0∞) := by
        refine tsum_le_tsum fun p => ?_
        by_cases hp : p ∈ π.support
        · gcongr
          calc ENNReal.ofReal (Communication.externalInfoCost (p.transcriptLaw μ))
              ≤ ENNReal.ofReal p.depth :=
                ENNReal.ofReal_le_ofReal (p.externalInfoCost_le_depth μ)
            _ = ((p.depth : ℕ∞) : ℝ≥0∞) := by simp
            _ ≤ π.depth := ENat.toENNReal_le.mpr (depth_le_depth hp)
        · rw [(PMF.apply_eq_zero_iff π p).mpr hp, zero_mul, zero_mul]
    _ = π.depth := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

theorem internalInfoCost_le_depth (π : PublicCoin X Y Z) (μ : PMF (X × Y)) :
    π.internalInfoCost μ ≤ π.depth :=
  (π.internalInfoCost_le_externalInfoCost μ).trans (π.externalInfoCost_le_depth μ)

/-- With independent inputs, the internal and external information costs agree. -/
theorem internalInfoCost_eq_externalInfoCost (π : PublicCoin X Y Z) (μ : PMF (X × Y))
    (hμ : mutualInfo μ = 0) : π.internalInfoCost μ = π.externalInfoCost μ := by
  refine tsum_congr fun p => ?_
  rw [p.internalInfoCost_eq_externalInfoCost μ hμ]

/-- The **information complexity** of `R` on `A × B` with error `ε` on inputs drawn from `μ`: the
least internal information cost of a public-coin protocol solving `R` with error at most `ε` on
every pair of inputs from `A × B`, or `⊤` if there is none. Braverman and Rao bound the error on
inputs drawn from `μ` and also allow private coins, so for `μ` supported on `A × B` this is an
upper bound on their information complexity. Inputs outside `A × B` carry no correctness
requirement, so without that hypothesis it can be smaller. -/
noncomputable def infoComplexity (ε : ℝ) (R : X → Y → Z → Prop) (A : Set X) (B : Set Y)
    (μ : PMF (X × Y)) : ℝ≥0∞ :=
  ⨅ π : {π : PublicCoin X Y Z // π.Solves ε R A B}, π.1.internalInfoCost μ

theorem infoComplexity_le_internalInfoCost {π : PublicCoin X Y Z} {ε : ℝ}
    {R : X → Y → Z → Prop} {A : Set X} {B : Set Y} (h : π.Solves ε R A B) (μ : PMF (X × Y)) :
    infoComplexity ε R A B μ ≤ π.internalInfoCost μ :=
  iInf_le (fun π : {π : PublicCoin X Y Z // π.Solves ε R A B} => π.1.internalInfoCost μ) ⟨π, h⟩

/-- Lower bounds on information complexity are lower bounds on the internal information cost of
every public-coin protocol solving the relation, including when there is none. -/
theorem le_infoComplexity_iff {c : ℝ≥0∞} {ε : ℝ} {R : X → Y → Z → Prop} {A : Set X} {B : Set Y}
    {μ : PMF (X × Y)} :
    c ≤ infoComplexity ε R A B μ ↔
      ∀ π : PublicCoin X Y Z, π.Solves ε R A B → c ≤ π.internalInfoCost μ := by
  simp only [infoComplexity, le_iInf_iff, Subtype.forall]

/-- A deterministic protocol solving `R` bounds the information complexity by its internal
information cost. -/
theorem infoComplexity_le_protocol {p : Protocol X Y Z} {ε : ℝ} {R : X → Y → Z → Prop}
    {A : Set X} {B : Set Y} (hp : p.Solves R A B) (hε : 0 ≤ ε) (μ : PMF (X × Y)) :
    infoComplexity ε R A B μ ≤
      ENNReal.ofReal (Communication.internalInfoCost (p.transcriptLaw μ)) :=
  (infoComplexity_le_internalInfoCost (solves_pure hp hε) μ).trans_eq (internalInfoCost_pure p μ)

/-- **Information complexity is at most communication complexity.** -/
theorem infoComplexity_le_ecomplexity (ε : ℝ) (R : X → Y → Z → Prop) (A : Set X) (B : Set Y)
    (μ : PMF (X × Y)) : infoComplexity ε R A B μ ≤ ecomplexity ε R A B := by
  by_cases h : ecomplexity ε R A B = ⊤
  · rw [h, ENat.toENNReal_top]
    exact le_top
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp h
  obtain ⟨π, hπ, hd⟩ := ecomplexity_le_iff.mp hk.symm.le
  rw [← hk]
  calc infoComplexity ε R A B μ ≤ π.internalInfoCost μ := infoComplexity_le_internalInfoCost hπ μ
    _ ≤ π.depth := π.internalInfoCost_le_depth μ
    _ ≤ ((k : ℕ∞) : ℝ≥0∞) := ENat.toENNReal_le.mpr hd

end PublicCoin

end Cslib.Communication
