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
import Complexity.Computability.Circuit.Frontier.TensorNetwork.RowsFirstPolyTime
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

The guard is polynomial-time (`CountingSimulation.fastGuard_polyTime`), with the rows-first test
`DescribedNetwork.rowsFirst_polyTime`.

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
* `Cslib.Complexity.CountingSimulation.exists_clockedRun_le`: the budget of a clocked run, the
  arithmetic shared with the machine for entry procedures (`CountingSimulation.exists_fastCore_le`).
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

/-- **The guard is polynomial-time**: the rows-first test (`DescribedNetwork.rowsFirst_polyTime`),
the lengths of the tables and the degrees of the vertices. -/
theorem fastGuard_polyTime : ComputableInPolyTime fastGuard encG encBool := by
  have hd := ComputableInPolyTime.snd encNat ExplicitTensorNetwork.encExplicitNetwork
  have hm : ComputableInPolyTime (fun G : ℕ × ExplicitTensorNetwork ℕ => G.2.numEdges) encG
      encUnary := DescribedNetwork.numEdges_polyTime.comp hd
  have hvs : ComputableInPolyTime (fun G : ℕ × ExplicitTensorNetwork ℕ => G.2.vertices) encG
      (encList (encPair (encList encNat) (encList encNat))) :=
    DescribedNetwork.vertices_polyTime.comp hd
  -- Rows first.
  have hrows : ComputableInPolyTime (fun G : ℕ × ExplicitTensorNetwork ℕ =>
      decide (G.2.IsRowsFirstBipartite G.1)) encG encBool :=
    DescribedNetwork.rowsFirst_polyTime
  -- Full tables.
  have htab : ComputableInPolyTime (fun G : ℕ × ExplicitTensorNetwork ℕ =>
      G.2.vertices.all (fun v => decide (v.2.length = 2 ^ v.1.length))) encG encBool := by
    refine ComputableInPolyTime.allWithInput hvs ?_
    have hv := ComputableInPolyTime.snd encG (encPair (encList encNat) (encList encNat))
    exact ComputableInPolyTime.decide_eq'
      (ComputableInPolyTime.unary_to_binary.comp ((ComputableInPolyTime.length_list _).comp
        ((ComputableInPolyTime.snd _ _).comp hv)))
      (ComputableInPolyTime.binary_two_pow.comp ((ComputableInPolyTime.length_list _).comp
        ((ComputableInPolyTime.fst _ _).comp hv)))
  -- The degree bound.
  have hdeg : ComputableInPolyTime (fun G : ℕ × ExplicitTensorNetwork ℕ =>
      G.2.vertices.all (fun v => decide (v.1.length ≤ degreeBound G.2.numEdges))) encG
      encBool := by
    refine ComputableInPolyTime.allWithInput hvs ?_
    exact ComputableInPolyTime.binary_le'
      (ComputableInPolyTime.unary_to_binary.comp ((ComputableInPolyTime.length_list _).comp
        ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.snd _ _))))
      (degreeBound_polyTime.comp (hm.comp (ComputableInPolyTime.fst _ _)))
  refine (ComputableInPolyTime.bool_and.comp (hrows.prod (ComputableInPolyTime.bool_and.comp
    (htab.prod hdeg)))).of_enc_eq fun G => ?_
  simp only [fastGuard, ExplicitTensorNetwork.maxDegree_le_iff, Function.comp_apply,
    Bool.decide_and, List.all_eq, decide_eq_true_eq]

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

/-- **The budget of a clocked run**, the arithmetic shared by the fast machines
(`CountingSimulation.fastCertificate_le`, `CountingSimulation.exists_fastCore_le`). Take a run
bounded as in `Cslib.GenericRAM.StackRecursion.Scheme.certificate_le` with constant `K₁`, whose
derivation has open calls, node sizes and leaf space at most `Ka B ^ Ka`, leaf time at most
`Ka B ^ Ka 2 ^ (Ka s / S)` and clock at most `2 ^ (kf s / S)`, for `B` above the input length
`n`; let the steps `pre` before it and the fuel and root machines cost at most `c B ^ d`, and the
output step `rest` at most `r₁ B ^ e₁ + r₂ B ^ e₂`. Then the steps, twice the run, the input
and the output step are at most `K B ^ K 2 ^ (K s / S)` in time and `K B ^ K` in space, for one
`K` depending only on the constants. -/
theorem exists_clockedRun_le (K₁ Ka c d r₁ e₁ r₂ e₂ kf : ℕ) :
    ∃ K : ℕ, ∀ {s S n B fuel H F TL SL A AS runT runS pre preS rest restS : ℕ}, n < B →
      runT ≤ A + (fuel + 1) * (K₁ * ((H + 1) * (F + 1)) ^ K₁ + TL +
        ((encNat fuel).length + 1) ^ 2) →
      runS ≤ AS + K₁ * ((H + 1) * (F + 1)) ^ K₁ + SL + (encNat fuel).length →
      pre + preS + A + AS + (encNat fuel).length ≤ c * B ^ d →
      rest + restS ≤ r₁ * B ^ e₁ + r₂ * B ^ e₂ → fuel ≤ 2 ^ (kf * s / S) →
      H + F + SL ≤ Ka * B ^ Ka → TL ≤ Ka * B ^ Ka * 2 ^ (Ka * s / S) →
      pre + (2 * runT + n + rest) ≤ K * B ^ K * 2 ^ (K * s / S) ∧
        preS + (2 * runS + n + restS) ≤ K * B ^ K := by
  set E := 2 * d + 2 * Ka * K₁ + Ka + e₁ + e₂ + 1
  set Z₀ := K₁ * (Ka + 1) ^ (2 * K₁)
  set M := 4 * c + 4 * Z₀ + 4 * (c + 1) ^ 2 + 4 * Ka + r₁ + r₂ + 1 with hM
  refine ⟨M + E + kf + Ka, fun {s S n B fuel H F TL SL A AS runT runS pre preS rest restS}
    hn hrT hrS hpoly hrest hfuel hHFS hTL => ?_⟩
  have hBE {k : ℕ} (hk : k ≤ E) : B ^ k ≤ B ^ E := Nat.pow_le_pow_right (by omega) hk
  have hB1 (k : ℕ) : 1 ≤ B ^ k := Nat.one_le_pow _ _ (by omega)
  -- The pieces against `B ^ E`.
  have hc : c * B ^ d ≤ c * B ^ E := Nat.mul_le_mul_left _ (hBE (by omega))
  have hr : r₁ * B ^ e₁ + r₂ * B ^ e₂ ≤ (r₁ + r₂) * B ^ E := by
    rw [Nat.add_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ (hBE (by omega)))
      (Nat.mul_le_mul_left _ (hBE (by omega)))
  have hB : B ≤ B ^ E := by simpa using hBE (k := 1) (by omega)
  have hZ : K₁ * ((H + 1) * (F + 1)) ^ K₁ ≤ Z₀ * B ^ E := by
    have h1 : H + F + 1 ≤ (Ka + 1) * B ^ Ka := by have := hB1 Ka; rw [add_one_mul]; omega
    have h2 : (H + 1) * (F + 1) ≤ ((Ka + 1) * B ^ Ka) ^ 2 :=
      (Nat.mul_le_mul (by omega : H + 1 ≤ H + F + 1) (by omega : F + 1 ≤ H + F + 1)).trans
        ((sq _).symm.le.trans (Nat.pow_le_pow_left h1 2))
    calc K₁ * ((H + 1) * (F + 1)) ^ K₁ ≤ K₁ * (((Ka + 1) * B ^ Ka) ^ 2) ^ K₁ :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2 _)
      _ = Z₀ * B ^ (2 * Ka * K₁) := by
          rw [mul_pow, ← pow_mul, mul_pow, ← pow_mul, ← pow_mul]; ring
      _ ≤ Z₀ * B ^ E := Nat.mul_le_mul_left _ (hBE (by omega))
  have hL : ((encNat fuel).length + 1) ^ 2 ≤ (c + 1) ^ 2 * B ^ E := by
    calc ((encNat fuel).length + 1) ^ 2 ≤ ((c + 1) * B ^ d) ^ 2 :=
          Nat.pow_le_pow_left (by have := hB1 d; rw [add_one_mul]; omega) 2
      _ = (c + 1) ^ 2 * B ^ (2 * d) := by ring
      _ ≤ (c + 1) ^ 2 * B ^ E := Nat.mul_le_mul_left _ (hBE (by omega))
  have hKa : Ka * B ^ Ka ≤ Ka * B ^ E := Nat.mul_le_mul_left _ (hBE (by omega))
  -- The space.
  have hspace : preS + (2 * runS + n + restS) ≤ M * B ^ E := by
    have e : M * B ^ E = 4 * (c * B ^ E) + 4 * (Z₀ * B ^ E) + 4 * ((c + 1) ^ 2 * B ^ E) +
        4 * (Ka * B ^ E) + (r₁ + r₂) * B ^ E + B ^ E := by rw [hM]; ring
    omega
  -- The time, against `W = B ^ E X` with `X ≥ 2 ^ (kf s / S) 2 ^ (Ka s / S)`.
  set Xf := 2 ^ (kf * s / S)
  set Xa := 2 ^ (Ka * s / S)
  set X := 2 ^ ((kf + Ka) * s / S)
  have hXf : 1 ≤ Xf := Nat.one_le_two_pow
  have hXa : 1 ≤ Xa := Nat.one_le_two_pow
  have hX : Xf * Xa ≤ X := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (Nat.div_add_div_le_add_div.trans (by rw [add_mul]))
  have hXfX : Xf ≤ X := (Nat.le_mul_of_pos_right _ hXa).trans hX
  set W := B ^ E * X
  have hEW (a : ℕ) : a * B ^ E ≤ a * W :=
    Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ (hXf.trans hXfX))
  have hfuel1 : fuel + 1 ≤ 2 * Xf := by omega
  have hP1 : (fuel + 1) * (K₁ * ((H + 1) * (F + 1)) ^ K₁) ≤ 2 * (Z₀ * W) :=
    calc _ ≤ 2 * Xf * (Z₀ * B ^ E) := Nat.mul_le_mul hfuel1 hZ
      _ = 2 * (Z₀ * (B ^ E * Xf)) := by ring
      _ ≤ 2 * (Z₀ * W) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hXfX))
  have hP2 : (fuel + 1) * TL ≤ 2 * (Ka * W) :=
    calc _ ≤ 2 * Xf * (Ka * B ^ E * Xa) :=
          Nat.mul_le_mul hfuel1 (hTL.trans (Nat.mul_le_mul_right _ hKa))
      _ = 2 * (Ka * (B ^ E * (Xf * Xa))) := by ring
      _ ≤ 2 * (Ka * W) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hX))
  have hP3 : (fuel + 1) * ((encNat fuel).length + 1) ^ 2 ≤ 2 * ((c + 1) ^ 2 * W) :=
    calc _ ≤ 2 * Xf * ((c + 1) ^ 2 * B ^ E) := Nat.mul_le_mul hfuel1 hL
      _ = 2 * ((c + 1) ^ 2 * (B ^ E * Xf)) := by ring
      _ ≤ 2 * ((c + 1) ^ 2 * W) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hXfX))
  have htime : pre + (2 * runT + n + rest) ≤ M * W := by
    have e : M * W = 4 * (c * W) + 4 * (Z₀ * W) + 4 * ((c + 1) ^ 2 * W) + 4 * (Ka * W) +
        (r₁ + r₂) * W + 1 * W := by rw [hM]; ring
    rw [Nat.mul_add, Nat.mul_add] at hrT
    have := hEW c; have := hEW (r₁ + r₂); have := hEW 1
    omega
  have hMK : M ≤ M + E + kf + Ka := by omega
  have hEK : B ^ E ≤ B ^ (M + E + kf + Ka) := Nat.pow_le_pow_right (by omega) (by omega)
  refine ⟨htime.trans ?_, hspace.trans (Nat.mul_le_mul hMK hEK)⟩
  rw [← Nat.mul_assoc]
  exact Nat.mul_le_mul (Nat.mul_le_mul hMK hEK)
    (Nat.pow_le_pow_right (by norm_num) (Nat.div_le_div_right (Nat.mul_le_mul_right _ (by omega))))

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
  obtain ⟨K, hK⟩ := exists_clockedRun_le K₁ Ka (4 * c₁) d₁ (2 * (c₂ * (Ka + 2) ^ d₂))
    ((Ka + 1) * d₂) (2 * (K₂ * 2 ^ (C * s₀))) K₂ (FastContraction.fuelConst * (C + D))
  refine ⟨K, fun s P G hs hP hPD hA hg => ?_⟩
  obtain ⟨I, N, H, F, TL, SL, he, hN, hnode, hframe, hvalue, hHFS, hTL⟩ :=
    hKa s P G hs hP hPD hA hg
  set q : ℕ × ℕ × ExplicitTensorNetwork ℕ := (P, G)
  have hq1 := h₁ q
  obtain ⟨hdT, hdS⟩ := hK₂ q
  set B := (FastContraction.encInput q).length + 1 with hB
  obtain ⟨hrT, hrS⟩ := hK₁ (NativeCertificate.ofPolyTime fuel_polyTime)
    (NativeCertificate.ofPolyTime root_polyTime) I F TL SL hnode hframe hvalue
    (ExplicitTensorNetwork.capPrecision q) _ N H he
  have hrT' : (runCertificate hpoly).time (ExplicitTensorNetwork.capPrecision q) ≤ _ := hrT
  have hrS' : (runCertificate hpoly).space (ExplicitTensorNetwork.capPrecision q) ≤ _ := hrS
  -- Decoding a value of the run, and direct summation below `s₀`.
  have hdec (v : ℕ × List ℕ) (hv : I.value v) :
      (NativeCertificate.ofPolyTime tag_polyTime).time (q, v) +
        (NativeCertificate.ofPolyTime tag_polyTime).space (q, v) +
        (NativeCertificate.ofPolyTime decode_polyTime).time (q, v) +
        (NativeCertificate.ofPolyTime decode_polyTime).space (q, v) +
        (NativeCertificate.ofPolyTime
          (ComputableInPolyTime.fst FastContraction.encInput encValue)).time (q, v) +
        (NativeCertificate.ofPolyTime
          (ComputableInPolyTime.fst FastContraction.encInput encValue)).space (q, v) ≤
        c₂ * (Ka + 2) ^ d₂ * B ^ ((Ka + 1) * d₂) := by
    refine (h₂ (q, v)).trans ?_
    rw [Nat.mul_assoc, pow_mul, ← mul_pow]
    refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _)
    have := hvalue v hv
    have hB1 : B ≤ B ^ (Ka + 1) := Nat.le_self_pow (by omega) _
    have hBK := Nat.mul_le_mul_left Ka
      (Nat.pow_le_pow_right (by omega : 1 ≤ B) (by omega : Ka ≤ Ka + 1))
    simp only [length_encPair (enc₁ := FastContraction.encInput) (enc₂ := encValue), add_mul]
    omega
  have h2 : 1 ≤ 2 ^ (C * s₀) := Nat.one_le_two_pow
  have hdir (hs₀ : s < s₀) :
      ExplicitTensorNetwork.directContractionBinaryCertificate.time q ≤
        K₂ * 2 ^ (C * s₀) * B ^ K₂ := by
    refine hdT.trans (le_of_le_of_eq (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num)
      (hA.2.1.trans (Nat.mul_le_mul_left _ hs₀.le)))) (by ring))
  have hdirS : ExplicitTensorNetwork.directContractionBinaryCertificate.space q ≤
      K₂ * 2 ^ (C * s₀) * B ^ K₂ :=
    hdS.trans (le_of_le_of_eq (Nat.le_mul_of_pos_right _ h2) (by ring))
  have hbig : s₀ ≤ s → (scheme tableEntry mk).run fuel root (ExplicitTensorNetwork.capPrecision q) =
      some (0, value tableEntry mk (root (ExplicitTensorNetwork.capPrecision q))) :=
    fun h => Scheme.run_eq_some he (hN h)
  have hrest : ((scheme tableEntry mk).run fuel root (ExplicitTensorNetwork.capPrecision q)).elim
        (ExplicitTensorNetwork.directContractionBinaryCertificate.time q) (fun v =>
          (NativeCertificate.ofPolyTime tag_polyTime).time (q, v) +
            if decide (v.1 = 0) = true then
              (NativeCertificate.ofPolyTime decode_polyTime).time (q, v)
            else (NativeCertificate.ofPolyTime
                (ComputableInPolyTime.fst FastContraction.encInput encValue)).time (q, v) +
              ExplicitTensorNetwork.directContractionBinaryCertificate.time q) +
      ((scheme tableEntry mk).run fuel root (ExplicitTensorNetwork.capPrecision q)).elim
        (ExplicitTensorNetwork.directContractionBinaryCertificate.space q) (fun v =>
          (NativeCertificate.ofPolyTime tag_polyTime).space (q, v) +
            if decide (v.1 = 0) = true then
              (NativeCertificate.ofPolyTime decode_polyTime).space (q, v)
            else (NativeCertificate.ofPolyTime
                (ComputableInPolyTime.fst FastContraction.encInput encValue)).space (q, v) +
              ExplicitTensorNetwork.directContractionBinaryCertificate.space q) ≤
      2 * (c₂ * (Ka + 2) ^ d₂) * B ^ ((Ka + 1) * d₂) + 2 * (K₂ * 2 ^ (C * s₀)) * B ^ K₂ := by
    rw [Nat.mul_assoc 2, Nat.mul_assoc 2]
    rcases hr : (scheme tableEntry mk).run fuel root (ExplicitTensorNetwork.capPrecision q)
      with _ | v
    · have hs₀ : s < s₀ := Nat.lt_of_not_le fun h => by rw [hbig h] at hr; cases hr
      have := hdir hs₀
      simp only [Option.elim_none]; omega
    · have hd := hdec v (Scheme.value_of_run_eq_some he hr)
      simp only [Option.elim_some]
      split_ifs with h0
      · omega
      · have hs₀ : s < s₀ := Nat.lt_of_not_le fun h => by
          rw [hbig h] at hr; cases hr; simp at h0
        have := hdir hs₀; omega
  rw [fastCertificate_time, fastCertificate_space]
  exact (hK (n := (FastContraction.encInput q).length)
    (pre := 2 * (NativeCertificate.ofPolyTime ExplicitTensorNetwork.capPrecision_polyTime).time q)
    (preS := 2 * (NativeCertificate.ofPolyTime ExplicitTensorNetwork.capPrecision_polyTime).space q)
    (by omega) hrT' hrS' (by rw [Nat.mul_assoc]; omega) hrest (fuel_le hA hs hPD) hHFS hTL).imp
    (fun h => by omega) fun h => by omega

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
