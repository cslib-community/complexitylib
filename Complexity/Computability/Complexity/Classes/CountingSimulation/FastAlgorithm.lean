/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.CountingSimulation.Guarded
public import Complexity.Computability.Complexity.Classes.CountingSimulation.Admissible
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.FastContractionMachine
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.FastContractionStep
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.FastContractionPolyTime
import Mathlib.Analysis.SpecificLimits.Normed
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryDivision
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimePrimitives

/-!
# The fast contraction algorithm, assembled

The contraction interface (`CountingSimulation.ContractionAlgorithm`) for admissible explicit
networks, from the native machine of the recursion of Theorem D.1 of [OpenAI2026ETH]
(`FastContraction.fastCertificate`), reduced to its remaining obligations
(`CountingSimulation.contractionAlgorithmOfFast`).

**The guard** (`CountingSimulation.fastGuard`) tests what `ExplicitAdmissible` already implies
(rows first, full tables) and the degree bound `degreeBound m` of the schedule (§D.4.2, (D.6),
p. 58). An admissible network of degree at most `C ⌊log₂ s⌋` fails it only for `s` below a
threshold depending on `C` (`CountingSimulation.exists_le_of_fastGuard_eq_false`), since
`degreeBound m ≥ m ^ (9 / 10)` and `m ≥ s`.

**The clock** is subexponential on admissible inputs: with `m ≤ C s` edges and precision
`P ≤ D s` it is at most `2 ^ (K₀ (C + D) s / √⌊log₂ s⌋)` (`CountingSimulation.fuel_le`).

**The resources.** `CountingSimulation.FastAnalysis` is the resource analysis of the recursion on
admissible guarded inputs: a derivation of the root with polynomial depth, node sizes and leaf
space, leaf time `poly(n) 2 ^ O(s / √⌊log₂ s⌋)`, and, from some size on, a node count within the
clock. From it and polynomial-time components of the scheme, the fast machine meets the
interface's bounds (`CountingSimulation.fastCertificate_le`), through
`Cslib.GenericRAM.StackRecursion.Scheme.certificate_le`. Below the size threshold the run may not
finish, and the machine falls back to direct summation, at a constant factor.

The guard is polynomial-time (`CountingSimulation.fastGuard_polyTime`).

For the native child builder (`FastContraction.nativeMk`), the components of the scheme are
polynomial-time (`FastContraction.scheme_nativeMk_polyTime`), and the step, the passage of
well-formedness to the children and the well-formed roots are proved; there the one remaining
obligation is the resource analysis (`CountingSimulation.contractionAlgorithmOfNative`).

**Remaining obligations** (the hypotheses of `CountingSimulation.contractionAlgorithmOfFast`): the
components of the scheme in polynomial time, the correctness of one active call
(`FastContraction.StepCorrect`), the passage of well-formedness to the children
(`FastContraction.WFChildren`) and to the root, and the resource analysis.

## Main definitions

* `Cslib.Complexity.CountingSimulation.fastGuard`: the guard.
* `Cslib.Complexity.CountingSimulation.FastAnalysis`: the resource analysis.
* `Cslib.Complexity.CountingSimulation.contractionAlgorithmOfFast`: the contraction algorithm from
  the remaining obligations.
* `Cslib.Complexity.CountingSimulation.contractionAlgorithmOfNative`: the same for the native child
  builder, from the resource analysis alone.

## Main results

* `Cslib.Complexity.CountingSimulation.exists_le_of_fastGuard_eq_false`: admissible networks
  failing the guard are small.
* `Cslib.Complexity.CountingSimulation.fastGuard_polyTime`: the guard is polynomial-time.
* `Cslib.Complexity.CountingSimulation.wf_root`: guarded inputs have well-formed roots.
* `Cslib.Complexity.CountingSimulation.fuel_le`: the clock on admissible inputs.
* `Cslib.Complexity.CountingSimulation.fastCertificate_le`: the fast machine within the
  interface's bounds.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Theorem D.1 (p. 53) and
  Appendix D.4.
-/

public section

namespace Cslib.Complexity.CountingSimulation

open Cslib.Circuits.Frontier Cslib.Circuits.Frontier.ContractionSchedule Filter

/-- **The guard of the fast algorithm**: the network is rows-first bipartite at its number of
rows, every table lists the values at all bit strings on its ports, and its maximum degree is at
most `degreeBound m`, for `m` its number of edges. -/
@[expose] def fastGuard (G : ℕ × ExplicitTensorNetwork ℕ) : Bool :=
  decide (G.2.IsRowsFirstBipartite G.1 ∧ (∀ v ∈ G.2.vertices, v.2.length = 2 ^ v.1.length) ∧
    G.2.maxDegree ≤ degreeBound G.2.numEdges)

/-- A power of the logarithm is eventually below a power: `(C L) ^ 10 ≤ 2 ^ (9 L)` from some
`L₀` on. -/
private theorem exists_pow_ten_le (C : ℕ) : ∃ L₀, ∀ L, L₀ ≤ L → (C * L) ^ 10 ≤ 2 ^ (9 * L) := by
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt 10 (r := (2 : ℝ) ^ 9) (by norm_num)
  have hC : (0 : ℝ) < 1 / ((C : ℝ) ^ 10 + 1) := by positivity
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp ((tendsto_order.1 hlim).2 _ hC)
  refine ⟨L₀, fun L hL => ?_⟩
  have h := hL₀ L hL
  have h2 : (0 : ℝ) < ((2 : ℝ) ^ 9) ^ L := by positivity
  have h1 : (0 : ℝ) < (C : ℝ) ^ 10 + 1 := by positivity
  rw [div_lt_div_iff₀ h2 h1, one_mul] at h
  have hL10 : (0 : ℝ) ≤ (L : ℝ) ^ 10 := by positivity
  have hle : ((C * L) ^ 10 : ℕ) ≤ ((2 ^ (9 * L) : ℕ) : ℝ) := by
    push_cast
    rw [mul_pow, pow_mul]
    nlinarith
  exact_mod_cast hle

/-- **Admissible networks failing the guard are small.** For every `C` there is `s₀` such that a
network admissible at size `s` with constant `C` that fails `fastGuard` has `s ≤ s₀`. -/
theorem exists_le_of_fastGuard_eq_false (C : ℕ) :
    ∃ s₀, ∀ s G, ExplicitAdmissible C s G → fastGuard G = false → s ≤ s₀ := by
  obtain ⟨L₀, hL₀⟩ := exists_pow_ten_le C
  refine ⟨2 ^ L₀, fun s G hA hg => ?_⟩
  obtain ⟨hrows, -, hdeg, -, htab, hsm⟩ := hA
  have hbig : degreeBound G.2.numEdges < G.2.maxDegree := by
    simp only [fastGuard, decide_eq_false_iff_not, not_and, not_le] at hg
    exact hg hrows htab
  by_contra hs
  rw [not_le] at hs
  have hL : L₀ ≤ Nat.log 2 s := Nat.le_log_of_pow_le one_lt_two hs.le
  have h1 : s ^ 9 ≤ G.2.numEdges ^ 9 := Nat.pow_le_pow_left hsm 9
  have h2 := pow_nine_le_degreeBound_pow_ten G.2.numEdges
  have h3 : degreeBound G.2.numEdges ^ 10 < (C * Nat.log 2 s) ^ 10 :=
    Nat.pow_lt_pow_left (hbig.trans_le hdeg) (by norm_num)
  have h4 := hL₀ _ hL
  have h5 : 2 ^ (9 * Nat.log 2 s) ≤ s ^ 9 := by
    rw [pow_mul']
    exact Nat.pow_le_pow_left
      (Nat.pow_log_le_self 2 (by have := Nat.one_le_two_pow (n := L₀); omega)) 9
  omega

/-! ### The guard in polynomial time -/

section GuardPolyTime

open Turing.MultiTapeTM

/-- The encoding of an explicit network with its number of rows. -/
local notation "encG" => encPair encNat ExplicitTensorNetwork.encExplicitNetwork

/-- The guard as a conjunction of list tests. -/
private def guardTest (G : ℕ × ExplicitTensorNetwork ℕ) : Bool :=
  G.2.vertices.all (fun v => v.1.all fun i => decide (i < G.2.numEdges)) &&
    (List.range G.2.numEdges).all (fun i =>
      decide (((G.2.vertices.take G.1).flatMap Prod.fst).count i = 1) &&
        decide (((G.2.vertices.drop G.1).flatMap Prod.fst).count i = 1)) &&
    G.2.vertices.all (fun v => decide (v.2.length = 2 ^ v.1.length)) &&
    G.2.vertices.all (fun v => decide (v.1.length ≤ degreeBound G.2.numEdges))

private theorem fastGuard_eq_guardTest (G : ℕ × ExplicitTensorNetwork ℕ) :
    fastGuard G = guardTest G := by
  refine Bool.eq_iff_iff.mpr ?_
  simp only [fastGuard, guardTest, DescribedNetwork.IsRowsFirstBipartite,
    ExplicitTensorNetwork.maxDegree_le_iff, decide_eq_true_eq, Bool.and_eq_true,
    List.all_eq_true, List.mem_range, List.count_flatMap, Function.comp_def]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨⟨fun v hv i hi => h1 v hv i hi, fun i hi => h2 i hi⟩, h3⟩, h4⟩
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    exact ⟨⟨fun v hv i hi => h1 v hv i hi, fun i hi => h2 i hi⟩, h3, h4⟩

/-- **The guard is polynomial-time.** -/
theorem fastGuard_polyTime : ComputableInPolyTime fastGuard encG encBool := by
  have hpair : ComputableInPolyTime (DescribedNetwork.equivProd (T := List ℕ))
      ExplicitTensorNetwork.encExplicitNetwork
      (encPair encUnary (encList (encPair (encList encNat) (encList encNat)))) :=
    ComputableInPolyTime.of_eq fun _ => rfl
  have hd := ComputableInPolyTime.snd encNat ExplicitTensorNetwork.encExplicitNetwork
  have hr := ComputableInPolyTime.fst encNat ExplicitTensorNetwork.encExplicitNetwork
  have hm : ComputableInPolyTime (fun G : ℕ × ExplicitTensorNetwork ℕ => G.2.numEdges) encG
      encUnary := (ComputableInPolyTime.fst _ _).comp (hpair.comp hd)
  have hvs : ComputableInPolyTime (fun G : ℕ × ExplicitTensorNetwork ℕ => G.2.vertices) encG
      (encList (encPair (encList encNat) (encList encNat))) :=
    (ComputableInPolyTime.snd _ _).comp (hpair.comp hd)
  -- Ports in range.
  have h1 : ComputableInPolyTime (fun G : ℕ × ExplicitTensorNetwork ℕ =>
      G.2.vertices.all (fun v => v.1.all fun i => decide (i < G.2.numEdges))) encG encBool := by
    refine ComputableInPolyTime.allWithInput hvs ?_
    refine ComputableInPolyTime.allWithInput
      ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.snd _ _)) ?_
    exact ComputableInPolyTime.binary_lt.comp ((ComputableInPolyTime.snd _ _).prod
      (ComputableInPolyTime.unary_to_binary.comp (hm.comp ((ComputableInPolyTime.fst _ _).comp
        (ComputableInPolyTime.fst _ _)))))
  -- Each edge has one row port and one column port.
  have hlen := (ComputableInPolyTime.length_list _).comp hvs
  have hcap := ComputableInPolyTime.binary_min_unary' hlen hr
  have htake : ComputableInPolyTime (fun G : ℕ × ExplicitTensorNetwork ℕ =>
      G.2.vertices.take (min G.2.vertices.length G.1)) encG
      (encList (encPair (encList encNat) (encList encNat))) :=
    .of_tidy (ComputableTidilyInPolyTime.listTakeWithInput hvs.tidy hcap.tidy)
  have hdrop : ComputableInPolyTime (fun G : ℕ × ExplicitTensorNetwork ℕ =>
      G.2.vertices.drop (min G.2.vertices.length G.1)) encG
      (encList (encPair (encList encNat) (encList encNat))) :=
    .of_tidy (ComputableTidilyInPolyTime.listDropWithInput hvs.tidy hcap.tidy)
  have hflat {l : ℕ × ExplicitTensorNetwork ℕ → List (List ℕ × List ℕ)}
      (hl : ComputableInPolyTime l encG (encList (encPair (encList encNat) (encList encNat)))) :
      ComputableInPolyTime (fun G => (l G).flatMap Prod.fst) encG (encList encNat) :=
    ComputableInPolyTime.flatMapWithInput (f := fun _ v => v.1) hl
      ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.snd _ _))
  have hcount {l : ℕ × ExplicitTensorNetwork ℕ → List ℕ}
      (hl : ComputableInPolyTime l encG (encList encNat)) :
      ComputableInPolyTime (fun p : (ℕ × ExplicitTensorNetwork ℕ) × ℕ =>
        decide ((l p.1).count p.2 = 1)) (encPair encG encUnary) encBool := by
    have hc := ComputableInPolyTime.countPWithInput (test := fun p a => decide (a = p.2))
      (hl.comp (ComputableInPolyTime.fst encG encUnary))
      (ComputableInPolyTime.decide_eq' (ComputableInPolyTime.snd _ _)
        (ComputableInPolyTime.unary_to_binary.comp ((ComputableInPolyTime.snd _ _).comp
          (ComputableInPolyTime.fst _ _))))
    refine (ComputableInPolyTime.decide_eq' hc (ComputableInPolyTime.const 1)).of_enc_eq
      fun p => ?_
    simp only [Function.comp_apply, List.count_eq_countP]
    congr 3
  have h2 : ComputableInPolyTime (fun G : ℕ × ExplicitTensorNetwork ℕ =>
      (List.range G.2.numEdges).all (fun i =>
        decide (((G.2.vertices.take (min G.2.vertices.length G.1)).flatMap Prod.fst).count i = 1) &&
          decide (((G.2.vertices.drop (min G.2.vertices.length G.1)).flatMap Prod.fst).count i =
            1))) encG encBool :=
    ComputableInPolyTime.allWithInput (ComputableInPolyTime.range.comp hm)
      (ComputableInPolyTime.bool_and.comp ((hcount (hflat htake)).prod (hcount (hflat hdrop))))
  -- Full tables.
  have h3 : ComputableInPolyTime (fun G : ℕ × ExplicitTensorNetwork ℕ =>
      G.2.vertices.all (fun v => decide (v.2.length = 2 ^ v.1.length))) encG encBool := by
    refine ComputableInPolyTime.allWithInput hvs ?_
    have hv := ComputableInPolyTime.snd encG (encPair (encList encNat) (encList encNat))
    exact ComputableInPolyTime.decide_eq'
      (ComputableInPolyTime.unary_to_binary.comp ((ComputableInPolyTime.length_list _).comp
        ((ComputableInPolyTime.snd _ _).comp hv)))
      (ComputableInPolyTime.binary_two_pow.comp ((ComputableInPolyTime.length_list _).comp
        ((ComputableInPolyTime.fst _ _).comp hv)))
  -- The degree bound.
  have h4 : ComputableInPolyTime (fun G : ℕ × ExplicitTensorNetwork ℕ =>
      G.2.vertices.all (fun v => decide (v.1.length ≤ degreeBound G.2.numEdges))) encG
      encBool := by
    refine ComputableInPolyTime.allWithInput hvs ?_
    exact ComputableInPolyTime.binary_le'
      (ComputableInPolyTime.unary_to_binary.comp ((ComputableInPolyTime.length_list _).comp
        ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.snd _ _))))
      (degreeBound_polyTime.comp (hm.comp (ComputableInPolyTime.fst _ _)))
  refine (ComputableInPolyTime.bool_and.comp ((ComputableInPolyTime.bool_and.comp
    ((ComputableInPolyTime.bool_and.comp (h1.prod h2)).prod h3)).prod h4)).of_enc_eq fun G => ?_
  have ht : G.2.vertices.take (min G.2.vertices.length G.1) = G.2.vertices.take G.1 := by
    rcases le_total G.2.vertices.length G.1 with hle | hle
    · rw [min_eq_left hle, List.take_length, List.take_of_length_le hle]
    · rw [min_eq_right hle]
  have hdr : G.2.vertices.drop (min G.2.vertices.length G.1) = G.2.vertices.drop G.1 := by
    rcases le_total G.2.vertices.length G.1 with hle | hle
    · rw [min_eq_left hle, List.drop_length, List.drop_of_length_le hle]
    · rw [min_eq_right hle]
  rw [fastGuard_eq_guardTest, guardTest]
  simp only [Function.comp_apply, ht, hdr]

end GuardPolyTime

/-! ### The clock -/

open FastContraction in
/-- **The clock is subexponential on admissible inputs**: with `m ≤ C s` edges and precision
`P ≤ D s`, it is at most `2 ^ (K₀ (C + D) s / √⌊log₂ s⌋)`. -/
theorem fuel_le {C D s P : ℕ} {G : ℕ × ExplicitTensorNetwork ℕ} (hA : ExplicitAdmissible C s G)
    (hs : 2 ≤ s) (hP : P ≤ D * s) :
    fuel (ExplicitTensorNetwork.capPrecision (P, G)) ≤
      2 ^ (fuelConst * (C + D) * s / Nat.sqrt (Nat.log 2 s)) := by
  obtain ⟨-, hm, -, -, -, hsm⟩ := hA
  simp only [fuel, ExplicitTensorNetwork.capPrecision]
  refine Nat.pow_le_pow_right (by norm_num) ?_
  set x := G.2.numEdges + min (ExplicitTensorNetwork.encExplicitNetwork G.2).length P
  have hx : x ≤ (C + D) * s := by
    have := min_le_right (ExplicitTensorNetwork.encExplicitNetwork G.2).length P
    rw [add_mul]; omega
  have hsx : s ≤ x := by omega
  have hq : 1 ≤ Nat.sqrt (Nat.log 2 s) := by
    rw [Nat.le_sqrt, Nat.one_mul]; exact Nat.le_log_of_pow_le one_lt_two (by simpa using hs)
  have hq' : Nat.sqrt (Nat.log 2 s) ≤ Nat.sqrt (Nat.log 2 x) :=
    Nat.sqrt_le_sqrt (Nat.log_mono_right hsx)
  calc fuelConst * x / Nat.sqrt (Nat.log 2 x) ≤ fuelConst * x / Nat.sqrt (Nat.log 2 s) :=
        Nat.div_le_div_left hq' hq
    _ ≤ fuelConst * (C + D) * s / Nat.sqrt (Nat.log 2 s) := by
        refine Nat.div_le_div_right ?_
        rw [Nat.mul_assoc]
        exact Nat.mul_le_mul_left _ hx

/-! ### The resources of the fast machine -/

section Resources

open FastContraction Cslib.GenericRAM Cslib.GenericRAM.StackRecursion Turing.MultiTapeTM

variable (mk : Call (List ℕ) → ChildCursor.State → ℕ × DescribedNetwork (VertexDesc (List ℕ)))

/-- **The resource analysis of the fast machine**, the remaining obligation of the running time.
For all constants `C` and `D` there are `K` and `s₀` such that on every input `(P, r, G)` with
`2 ≤ s`, `1 ≤ P ≤ D s`, `G` admissible at size `s` with constant `C` and passing the guard, the
root of the capped input has a derivation whose nodes, frames and values are at most `F` long,
whose leaves take time at most `TL` and space at most `SL`, with `H` open calls, such that
`H + F + SL ≤ K (n + 1) ^ K` and `TL ≤ K (n + 1) ^ K 2 ^ (K s / √⌊log₂ s⌋)` for the input length
`n`; and from `s₀` on its `N` nodes fit in the clock, `2 N - 1 ≤ fuel`. -/
@[expose] def FastAnalysis : Prop :=
  ∀ C D : ℕ, ∃ K s₀ : ℕ, ∀ (s P : ℕ) (G : ℕ × ExplicitTensorNetwork ℕ), 2 ≤ s → 1 ≤ P →
    P ≤ D * s → ExplicitAdmissible C s G → fastGuard G = true →
    ∃ (I : Invariant (Call (List ℕ)) Frame (ℕ × List ℕ)) (N H F TL SL : ℕ),
      (scheme tableEntry mk).Eval I (root (ExplicitTensorNetwork.capPrecision (P, G)))
        (0, value tableEntry mk (root (ExplicitTensorNetwork.capPrecision (P, G)))) N H ∧
      (s₀ ≤ s → 2 * N - 1 ≤ fuel (ExplicitTensorNetwork.capPrecision (P, G))) ∧
      (∀ x, I.node x → (encCall (encList encNat) x).length ≤ F ∧
        ((scheme tableEntry mk).isLeaf x = true →
          (leafCertificate tableEntryCertificate mk).time x ≤ TL ∧
            (leafCertificate tableEntryCertificate mk).space x ≤ SL)) ∧
      (∀ x a, I.frame x a → (encPair (encCall (encList encNat)) encFrame (x, a)).length ≤ F) ∧
      (∀ v, I.value v → (encValue v).length ≤ F) ∧
      H + F + SL ≤ K * ((FastContraction.encInput (P, G)).length + 1) ^ K ∧
      TL ≤ K * ((FastContraction.encInput (P, G)).length + 1) ^ K *
        2 ^ (K * s / Nat.sqrt (Nat.log 2 s))

/-- `c B ^ d ≤ c B ^ E X` for `1 ≤ B`, `d ≤ E` and `1 ≤ X`. -/
private theorem lift_le {c B d E X : ℕ} (hB : 1 ≤ B) (hd : d ≤ E) (hX : 1 ≤ X) :
    c * B ^ d ≤ c * B ^ E * X :=
  (Nat.mul_le_mul_left c (Nat.pow_le_pow_right hB hd)).trans (Nat.le_mul_of_pos_right _ hX)

private theorem mul_succ_le_sq (H F : ℕ) : (H + 1) * (F + 1) ≤ (H + F + 1) ^ 2 := by nlinarith

private theorem mul_add_one_le {c x : ℕ} (hx : 1 ≤ x) : c * x + 1 ≤ (c + 1) * x := by nlinarith

/-- The arithmetic of the time bound. -/
private theorem time_assemble
    {capT runT cnT crT capL fuel Z TL Wb n R₁ R₂ Q W c₁ k₁ c₃ ka c₂ k₂ : ℕ}
    (hrun : runT ≤ cnT + crT + 2 * capL + (fuel + 1) * (Z + TL + Wb))
    (hq : capT + cnT + crT + capL ≤ Q) (hQ : Q ≤ c₁ * W)
    (hP1 : (fuel + 1) * Z ≤ 2 * k₁ * W) (hP2 : (fuel + 1) * TL ≤ 2 * ka * W)
    (hP3 : (fuel + 1) * Wb ≤ 2 * c₃ * W) (hn : n + 1 ≤ 1 * W) (hR₁ : R₁ ≤ c₂ * W)
    (hR₂ : R₂ ≤ k₂ * W) :
    2 * (capT + runT) + n + (R₁ + R₂) ≤ (6 * c₁ + 1 + 4 * k₁ + 4 * c₃ + 4 * ka + c₂ + k₂) * W := by
  have e : (fuel + 1) * (Z + TL + Wb) = (fuel + 1) * Z + (fuel + 1) * TL + (fuel + 1) * Wb := by
    ring
  rw [e] at hrun
  nlinarith

/-- The arithmetic of the space bound. -/
private theorem space_assemble
    {capS runS cnS crS capL fb Z SL n R₁ R₂ Q W c₁ k₁ c₃ ka c₂ k₂ : ℕ}
    (hrun : runS ≤ cnS + crS + 2 * capL + Z + SL + fb)
    (hq : capS + cnS + crS + capL + fb ≤ Q) (hQ : Q ≤ c₁ * W)
    (hZ : Z ≤ k₁ * W) (hSL : SL ≤ ka * W) (hn : n + 1 ≤ 1 * W) (hR₁ : R₁ ≤ c₂ * W)
    (hR₂ : R₂ ≤ k₂ * W) :
    2 * (capS + runS) + n + (R₁ + R₂) ≤ (6 * c₁ + 1 + 4 * k₁ + 4 * c₃ + 4 * ka + c₂ + k₂) * W := by
  nlinarith

variable {mk}

/-- **The fast machine within the interface's bounds.** Given polynomial-time components of the
scheme and the resource analysis, for all constants `C` and `D` there is `K` such that on every
guarded input admissible at size `s ≥ 2` with constant `C` and with precision `1 ≤ P ≤ D s`, the
fast machine takes time at most `K (n + 1) ^ K 2 ^ (K s / √⌊log₂ s⌋)` and space at most
`K (n + 1) ^ K`. -/
theorem fastCertificate_le
    (hpoly : (scheme tableEntry mk).PolyTime (encCall (encList encNat)) encFrame encValue)
    (hana : FastAnalysis mk) (C D : ℕ) :
    ∃ K : ℕ, ∀ (s P : ℕ) (G : ℕ × ExplicitTensorNetwork ℕ), 2 ≤ s → 1 ≤ P → P ≤ D * s →
      ExplicitAdmissible C s G → fastGuard G = true →
      (fastCertificate hpoly).time (P, G) ≤
          K * ((FastContraction.encInput (P, G)).length + 1) ^ K *
            2 ^ (K * s / Nat.sqrt (Nat.log 2 s)) ∧
        (fastCertificate hpoly).space (P, G) ≤
          K * ((FastContraction.encInput (P, G)).length + 1) ^ K := by
  obtain ⟨Ka, s₀, hKa⟩ := hana C D
  obtain ⟨K₁, hK₁⟩ := Scheme.certificate_le hpoly (leafCertificate tableEntryCertificate mk)
  obtain ⟨K₂, hK₂⟩ := ExplicitTensorNetwork.exists_directContractionBinaryCertificate_le
  have hcapP := NativeCertificate.ofPolyTime_isPolynomial
    ExplicitTensorNetwork.capPrecision_polyTime
  have hcnP := NativeCertificate.ofPolyTime_isPolynomial fuel_polyTime
  have hcrP := NativeCertificate.ofPolyTime_isPolynomial root_polyTime
  have hcapL := ExplicitTensorNetwork.capPrecision_polyTime.polyBounded_length
  have hfuelL := fuel_polyTime.polyBounded_length
  obtain ⟨c₁, d₁, h₁⟩ := (((((((hcapP.1.add hcapP.2).add (hcnP.1.comp hcapL)).add
    (hcnP.2.comp hcapL)).add (hcrP.1.comp hcapL)).add (hcrP.2.comp hcapL)).add hcapL).add
    (hfuelL.comp hcapL)).exists_le
  have htP := NativeCertificate.ofPolyTime_isPolynomial tag_polyTime
  have hdP := NativeCertificate.ofPolyTime_isPolynomial decode_polyTime
  have hfP := NativeCertificate.ofPolyTime_isPolynomial
    (ComputableInPolyTime.fst FastContraction.encInput encValue)
  obtain ⟨c₂, d₂, h₂⟩ := (((((htP.1.add htP.2).add hdP.1).add hdP.2).add hfP.1).add
    hfP.2).exists_le
  -- The constants.
  set E := 2 * d₁ + 2 * Ka * K₁ + (Ka + 1) * d₂ + K₂ + Ka + 1 with hE
  set Kc := 6 * c₁ + 1 + 4 * K₁ * (Ka + 1) ^ (2 * K₁) + 4 * (c₁ + 1) ^ 2 + 4 * Ka +
    c₂ * (Ka + 2) ^ d₂ + K₂ * 2 ^ (C * s₀) with hKc
  refine ⟨Kc + E + FastContraction.fuelConst * (C + D) + Ka, fun s P G hs hP hPD hA hg => ?_⟩
  obtain ⟨I, N, H, F, TL, SL, he, hN, hnode, hframe, hvalue, hHFS, hTL⟩ :=
    hKa s P G hs hP hPD hA hg
  set q : ℕ × ℕ × ExplicitTensorNetwork ℕ := (P, G) with hq
  set n := (FastContraction.encInput q).length with hn
  set B := n + 1 with hB
  have hB1 : 1 ≤ B := by omega
  set S := Nat.sqrt (Nat.log 2 s)
  set Xf := 2 ^ (FastContraction.fuelConst * (C + D) * s / S)
  set Xa := 2 ^ (Ka * s / S)
  set X := 2 ^ ((FastContraction.fuelConst * (C + D) + Ka) * s / S)
  have hXf : 1 ≤ Xf := Nat.one_le_two_pow
  have hXa : 1 ≤ Xa := Nat.one_le_two_pow
  have hXfX : Xf ≤ X := Nat.pow_le_pow_right (by norm_num)
    (Nat.div_le_div_right (Nat.mul_le_mul_right _ (by omega)))
  have hXfXa : Xf * Xa ≤ X := by
    rw [← pow_add]
    refine Nat.pow_le_pow_right (by norm_num) (Nat.div_add_div_le_add_div.trans ?_)
    rw [add_mul]
  have hX1 : 1 ≤ X := Nat.one_le_two_pow
  -- The run.
  obtain ⟨hrT, hrS⟩ := hK₁ (NativeCertificate.ofPolyTime fuel_polyTime)
    (NativeCertificate.ofPolyTime root_polyTime) I F TL SL hnode hframe hvalue
    (ExplicitTensorNetwork.capPrecision q) _ N H he
  have hfuel : FastContraction.fuel (ExplicitTensorNetwork.capPrecision q) ≤ Xf :=
    fuel_le hA hs hPD
  have hq1 := h₁ q
  have hrT' : (runCertificate hpoly).time (ExplicitTensorNetwork.capPrecision q) ≤ _ := hrT
  have hrS' : (runCertificate hpoly).space (ExplicitTensorNetwork.capPrecision q) ≤ _ := hrS
  -- Polynomial pieces.
  set Q₁ := c₁ * B ^ d₁ with hQ₁
  have hBK (k : ℕ) : 1 ≤ B ^ k := Nat.one_le_pow _ _ (by omega)
  have hHF : (H + 1) * (F + 1) ≤ ((Ka + 1) * B ^ Ka) ^ 2 := by
    have h1 : H + F ≤ Ka * B ^ Ka := by have := hHFS; omega
    have h2 := hBK Ka
    calc (H + 1) * (F + 1) ≤ (H + F + 1) ^ 2 := mul_succ_le_sq H F
      _ ≤ (Ka * B ^ Ka + B ^ Ka) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ = ((Ka + 1) * B ^ Ka) ^ 2 := by ring
  have hZ : K₁ * ((H + 1) * (F + 1)) ^ K₁ ≤ K₁ * (Ka + 1) ^ (2 * K₁) * B ^ (2 * Ka * K₁) := by
    calc K₁ * ((H + 1) * (F + 1)) ^ K₁ ≤ K₁ * (((Ka + 1) * B ^ Ka) ^ 2) ^ K₁ :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hHF _)
      _ = K₁ * (Ka + 1) ^ (2 * K₁) * B ^ (2 * Ka * K₁) := by
          rw [mul_pow, ← pow_mul, mul_pow, ← pow_mul, ← pow_mul,
            show Ka * 2 * K₁ = 2 * Ka * K₁ by ring]
          ring
  have hW : ((encNat (FastContraction.fuel (ExplicitTensorNetwork.capPrecision q))).length + 1) ^ 2
      ≤ (c₁ + 1) ^ 2 * B ^ (2 * d₁) := by
    have h1 : (encNat (FastContraction.fuel (ExplicitTensorNetwork.capPrecision q))).length ≤ Q₁ :=
      by omega
    have h2 := hBK d₁
    calc _ ≤ (Q₁ + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ ≤ ((c₁ + 1) * B ^ d₁) ^ 2 := Nat.pow_le_pow_left (mul_add_one_le h2) 2
      _ = (c₁ + 1) ^ 2 * B ^ (2 * d₁) := by ring
  have hTL' : TL ≤ Ka * B ^ Ka * Xa := hTL
  have hF : F ≤ Ka * B ^ Ka := by have := hHFS; omega
  have hSL : SL ≤ Ka * B ^ Ka := by have := hHFS; omega
  -- Decoding and direct summation.
  set R₁ := c₂ * (Ka + 2) ^ d₂ * B ^ ((Ka + 1) * d₂) with hR₁
  set R₂ := K₂ * 2 ^ (C * s₀) * B ^ K₂ with hR₂
  have hdec : ∀ v : ℕ × List ℕ, I.value v →
      (NativeCertificate.ofPolyTime tag_polyTime).time (q, v) +
        (NativeCertificate.ofPolyTime tag_polyTime).space (q, v) +
        (NativeCertificate.ofPolyTime decode_polyTime).time (q, v) +
        (NativeCertificate.ofPolyTime decode_polyTime).space (q, v) +
        (NativeCertificate.ofPolyTime
          (ComputableInPolyTime.fst FastContraction.encInput encValue)).time (q, v) +
        (NativeCertificate.ofPolyTime
          (ComputableInPolyTime.fst FastContraction.encInput encValue)).space (q, v) ≤ R₁ := by
    intro v hv
    have h := h₂ (q, v)
    have hv' := hvalue v hv
    have hk1 : B ≤ B ^ (Ka + 1) := by
      calc B = B ^ 1 := (pow_one B).symm
        _ ≤ B ^ (Ka + 1) := Nat.pow_le_pow_right hB1 (by omega)
    have hk2 : B ^ Ka ≤ B ^ (Ka + 1) := Nat.pow_le_pow_right hB1 (by omega)
    have hlen : (encPair FastContraction.encInput encValue (q, v)).length + 1 ≤
        (Ka + 2) * B ^ (Ka + 1) := by
      have hl := length_encPair (enc₁ := FastContraction.encInput) (enc₂ := encValue) (q, v)
      simp only at hl
      rw [hl]
      have : Ka * B ^ Ka ≤ Ka * B ^ (Ka + 1) := Nat.mul_le_mul_left _ hk2
      have e : (Ka + 2) * B ^ (Ka + 1) = Ka * B ^ (Ka + 1) + 2 * B ^ (Ka + 1) := by ring
      omega
    calc _ ≤ c₂ * ((encPair FastContraction.encInput encValue (q, v)).length + 1) ^ d₂ := h
      _ ≤ c₂ * ((Ka + 2) * B ^ (Ka + 1)) ^ d₂ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlen _)
      _ = R₁ := by rw [hR₁, mul_pow, ← pow_mul, Nat.mul_assoc]
  obtain ⟨hdT, hdS⟩ := hK₂ q
  have hm : q.2.2.numEdges ≤ C * s := hA.2.1
  have hdir (hs₀ : s < s₀) :
      ExplicitTensorNetwork.directContractionBinaryCertificate.time q ≤ R₂ := by
    refine hdT.trans ?_
    have h2 : 2 ^ q.2.2.numEdges ≤ 2 ^ (C * s₀) :=
      Nat.pow_le_pow_right (by norm_num) (hm.trans (Nat.mul_le_mul_left _ hs₀.le))
    calc K₂ * ((encInput q).length + 1) ^ K₂ * 2 ^ q.2.2.numEdges
        ≤ K₂ * B ^ K₂ * 2 ^ (C * s₀) := Nat.mul_le_mul_left _ h2
      _ = R₂ := by rw [hR₂]; ring
  have hdirS : ExplicitTensorNetwork.directContractionBinaryCertificate.space q ≤ R₂ :=
    hdS.trans (by
      rw [hR₂]
      calc K₂ * ((encInput q).length + 1) ^ K₂ ≤
          K₂ * ((encInput q).length + 1) ^ K₂ * 2 ^ (C * s₀) :=
            Nat.le_mul_of_pos_right _ Nat.one_le_two_pow
        _ = K₂ * 2 ^ (C * s₀) * B ^ K₂ := by ring)
  have hbig : s₀ ≤ s → (scheme tableEntry mk).run fuel root (ExplicitTensorNetwork.capPrecision q) =
      some (0, value tableEntry mk (root (ExplicitTensorNetwork.capPrecision q))) :=
    fun h => Scheme.run_eq_some he (hN h)
  clear hKa hK₁ hK₂ h₁ h₂
  -- Everything against `W = B ^ E X`.
  set W := B ^ E * X with hWdef
  have lift {c d : ℕ} (hd : d ≤ E) : c * B ^ d ≤ c * W := by
    rw [hWdef, ← Nat.mul_assoc]; exact lift_le hB1 hd hX1
  have lift' {c d : ℕ} (hd : d ≤ E) : c * B ^ d ≤ c * B ^ E :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hB1 hd)
  have hQW : Q₁ ≤ c₁ * W := lift (by omega)
  have hR₁W : R₁ ≤ c₂ * (Ka + 2) ^ d₂ * W := lift (by omega)
  have hR₂W : R₂ ≤ K₂ * 2 ^ (C * s₀) * W := lift (by omega)
  have hnW : n + 1 ≤ 1 * W := by
    have := lift (c := 1) (d := 1) (by omega); rw [pow_one] at this; omega
  have hfuel1 : FastContraction.fuel (ExplicitTensorNetwork.capPrecision q) + 1 ≤ 2 * Xf := by
    omega
  have hP1 : (FastContraction.fuel (ExplicitTensorNetwork.capPrecision q) + 1) *
      (K₁ * ((H + 1) * (F + 1)) ^ K₁) ≤ 2 * (K₁ * (Ka + 1) ^ (2 * K₁)) * W := by
    calc _ ≤ (2 * Xf) * (K₁ * (Ka + 1) ^ (2 * K₁) * B ^ (2 * Ka * K₁)) :=
          Nat.mul_le_mul hfuel1 hZ
      _ = 2 * (K₁ * (Ka + 1) ^ (2 * K₁)) * (B ^ (2 * Ka * K₁) * Xf) := by ring
      _ ≤ 2 * (K₁ * (Ka + 1) ^ (2 * K₁)) * W := Nat.mul_le_mul_left _
          (Nat.mul_le_mul (Nat.pow_le_pow_right hB1 (by omega)) hXfX)
  have hP2 : (FastContraction.fuel (ExplicitTensorNetwork.capPrecision q) + 1) * TL ≤
      2 * Ka * W := by
    calc _ ≤ (2 * Xf) * (Ka * B ^ Ka * Xa) := Nat.mul_le_mul hfuel1 hTL'
      _ = 2 * Ka * (B ^ Ka * (Xf * Xa)) := by ring
      _ ≤ 2 * Ka * W := Nat.mul_le_mul_left _
          (Nat.mul_le_mul (Nat.pow_le_pow_right hB1 (by omega)) hXfXa)
  have hP3 : (FastContraction.fuel (ExplicitTensorNetwork.capPrecision q) + 1) *
      ((encNat (FastContraction.fuel (ExplicitTensorNetwork.capPrecision q))).length + 1) ^ 2 ≤
      2 * (c₁ + 1) ^ 2 * W := by
    calc _ ≤ (2 * Xf) * ((c₁ + 1) ^ 2 * B ^ (2 * d₁)) := Nat.mul_le_mul hfuel1 hW
      _ = 2 * (c₁ + 1) ^ 2 * (B ^ (2 * d₁) * Xf) := by ring
      _ ≤ 2 * (c₁ + 1) ^ 2 * W := Nat.mul_le_mul_left _
          (Nat.mul_le_mul (Nat.pow_le_pow_right hB1 (by omega)) hXfX)
  have hZE : K₁ * ((H + 1) * (F + 1)) ^ K₁ ≤ K₁ * (Ka + 1) ^ (2 * K₁) * B ^ E :=
    hZ.trans (lift' (by omega))
  have hQE : Q₁ ≤ c₁ * B ^ E := lift' (by omega)
  have hR₁E : R₁ ≤ c₂ * (Ka + 2) ^ d₂ * B ^ E := lift' (by omega)
  have hR₂E : R₂ ≤ K₂ * 2 ^ (C * s₀) * B ^ E := lift' (by omega)
  have hSLE : SL ≤ Ka * B ^ E := hSL.trans (lift' (by omega))
  have hnE : n + 1 ≤ 1 * B ^ E := by
    have := lift' (c := 1) (d := 1) (by omega); rw [pow_one] at this; omega
  have hKK : Kc ≤ Kc + E + FastContraction.fuelConst * (C + D) + Ka := by omega
  have hBE : B ^ E ≤ B ^ (Kc + E + FastContraction.fuelConst * (C + D) + Ka) :=
    Nat.pow_le_pow_right hB1 (by omega)
  have hXK : X ≤ 2 ^ ((Kc + E + FastContraction.fuelConst * (C + D) + Ka) * s / S) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.div_le_div_right (Nat.mul_le_mul_right _ (by omega)))
  refine ⟨?_, ?_⟩
  · rw [fastCertificate_time]
    have hrest : ((scheme tableEntry mk).run fuel root (ExplicitTensorNetwork.capPrecision q)).elim
        (ExplicitTensorNetwork.directContractionBinaryCertificate.time q) (fun v =>
          (NativeCertificate.ofPolyTime tag_polyTime).time (q, v) +
            if decide (v.1 = 0) = true then
              (NativeCertificate.ofPolyTime decode_polyTime).time (q, v)
            else (NativeCertificate.ofPolyTime
                (ComputableInPolyTime.fst FastContraction.encInput encValue)).time (q, v) +
              ExplicitTensorNetwork.directContractionBinaryCertificate.time q) ≤ R₁ + R₂ := by
      rcases hr : (scheme tableEntry mk).run fuel root
        (ExplicitTensorNetwork.capPrecision q) with _ | v
      · by_cases hs₀ : s₀ ≤ s
        · rw [hbig hs₀] at hr; cases hr
        · simp only [Option.elim_none]; have := hdir (by omega); omega
      · have hd := hdec v (Scheme.value_of_run_eq_some he hr)
        simp only [Option.elim_some]
        split_ifs with h0
        · omega
        · by_cases hs₀ : s₀ ≤ s
          · rw [hbig hs₀] at hr; cases hr; simp at h0
          · have := hdir (by omega); omega
    have htot := time_assemble (capT := (NativeCertificate.ofPolyTime
        ExplicitTensorNetwork.capPrecision_polyTime).time q) hrT' (by omega) hQW hP1 hP2
      hP3 hnW hR₁W hR₂W
    have hKc' : Kc = 6 * c₁ + 1 + 4 * (K₁ * (Ka + 1) ^ (2 * K₁)) + 4 * (c₁ + 1) ^ 2 + 4 * Ka +
        c₂ * (Ka + 2) ^ d₂ + K₂ * 2 ^ (C * s₀) := by rw [hKc]; ring
    rw [← hKc'] at htot
    calc _ ≤ _ := Nat.add_le_add_left hrest _
      _ ≤ Kc * W := htot
      _ ≤ _ := by
        rw [hWdef, ← Nat.mul_assoc]
        exact Nat.mul_le_mul (Nat.mul_le_mul hKK hBE) hXK
  · rw [fastCertificate_space]
    have hrest : ((scheme tableEntry mk).run fuel root (ExplicitTensorNetwork.capPrecision q)).elim
        (ExplicitTensorNetwork.directContractionBinaryCertificate.space q) (fun v =>
          (NativeCertificate.ofPolyTime tag_polyTime).space (q, v) +
            if decide (v.1 = 0) = true then
              (NativeCertificate.ofPolyTime decode_polyTime).space (q, v)
            else (NativeCertificate.ofPolyTime
                (ComputableInPolyTime.fst FastContraction.encInput encValue)).space (q, v) +
              ExplicitTensorNetwork.directContractionBinaryCertificate.space q) ≤ R₁ + R₂ := by
      rcases hr : (scheme tableEntry mk).run fuel root
        (ExplicitTensorNetwork.capPrecision q) with _ | v
      · simp only [Option.elim_none]; omega
      · have hd := hdec v (Scheme.value_of_run_eq_some he hr)
        simp only [Option.elim_some]
        split_ifs <;> omega
    have htot := space_assemble (capS := (NativeCertificate.ofPolyTime
        ExplicitTensorNetwork.capPrecision_polyTime).space q) (c₃ := (c₁ + 1) ^ 2) hrS'
      (by omega) hQE hZE hSLE hnE hR₁E hR₂E
    have hKc' : Kc = 6 * c₁ + 1 + 4 * (K₁ * (Ka + 1) ^ (2 * K₁)) + 4 * (c₁ + 1) ^ 2 + 4 * Ka +
        c₂ * (Ka + 2) ^ d₂ + K₂ * 2 ^ (C * s₀) := by rw [hKc]; ring
    rw [← hKc'] at htot
    calc _ ≤ _ := Nat.add_le_add_left hrest _
      _ ≤ Kc * B ^ E := htot
      _ ≤ _ := Nat.mul_le_mul hKK hBE

/-- **The contraction algorithm from the fast machine**, given its remaining obligations:
polynomial-time components of the scheme, the correctness of one active
call and the passage of well-formedness to the children (`FastContraction.StepCorrect`,
`FastContraction.WFChildren`), well-formed roots on guarded inputs, and the resource analysis
(`FastAnalysis`). It branches on the guard (`ContractionAlgorithm.ofGuarded`) to the fast machine
or to direct summation. -/
noncomputable def contractionAlgorithmOfFast
    (hpoly : (scheme tableEntry mk).PolyTime (encCall (encList encNat)) encFrame encValue)
    {WF : Call (List ℕ) → Prop}
    (hstep : StepCorrect tableEntry mk WF) (hwf : WFChildren mk WF)
    (hroot : ∀ P G, fastGuard G = true → WF (root (ExplicitTensorNetwork.capPrecision (P, G))))
    (hana : FastAnalysis mk) :
    ContractionAlgorithm (encPair encNat ExplicitTensorNetwork.encExplicitNetwork)
      (fun G => G.2.contraction) ExplicitAdmissible :=
  ContractionAlgorithm.ofGuarded fastGuard_polyTime (fastCertificate hpoly)
    (fun P G hg => fastValue_eq mk hstep hwf (P, G) (hroot P G hg))
    (fun C D => fastCertificate_le hpoly hana C D) (fun _ _ _ hA => hA.2.1)
    exists_le_of_fastGuard_eq_false

/-- **Guarded inputs have well-formed roots**: the modulus is irreducible modulo `2`, and the
tables as descriptors keep the rows-first ports. -/
theorem wf_root (P : ℕ) {G : ℕ × ExplicitTensorNetwork ℕ} (hg : fastGuard G = true) :
    FastContraction.WF (root (ExplicitTensorNetwork.capPrecision (P, G))) := by
  refine ⟨irreducible_modulus _, ?_⟩
  have hrows : G.2.IsRowsFirstBipartite G.1 := by
    simp only [fastGuard, decide_eq_true_eq] at hg
    exact hg.1
  obtain ⟨h1, h2⟩ := hrows
  refine ⟨fun v hv i hi => ?_, fun i hi => ?_⟩
  · simp only [root, ExplicitTensorNetwork.capPrecision, rootNet, List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact h1 w hw i hi
  · simp only [root, ExplicitTensorNetwork.capPrecision, rootNet, ← List.map_take,
      ← List.map_drop, List.map_map, Function.comp_def] at hi ⊢
    exact h2 i hi

/-- **The contraction algorithm from the native recursion**, given its one remaining obligation,
the resource analysis. The components of the scheme are polynomial-time
(`FastContraction.scheme_nativeMk_polyTime`), and the step, the passage of well-formedness to the
children and the well-formed roots are proved (`FastContraction.stepCorrect_nativeMk`,
`FastContraction.wfChildren_nativeMk`, `CountingSimulation.wf_root`). -/
noncomputable def contractionAlgorithmOfNative (hana : FastAnalysis nativeMk) :
    ContractionAlgorithm (encPair encNat ExplicitTensorNetwork.encExplicitNetwork)
      (fun G => G.2.contraction) ExplicitAdmissible :=
  contractionAlgorithmOfFast (scheme_nativeMk_polyTime tableEntry)
    (stepCorrect_nativeMk tableEntry) wfChildren_nativeMk
    (fun P _ hg => wf_root P hg) hana

end Resources

end Cslib.Complexity.CountingSimulation
