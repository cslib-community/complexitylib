/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.CountingSimulation.Admissible
public import Complexity.Computability.Complexity.Classes.CountingSimulation.Containments
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.DirectContraction
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.ExplicitBlockNetwork.TablePolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
import Complexity.Foundations.Data.Nat.Log

/-!
# The block-counting network families

The explicit block-counting networks of #1833 (`Turing.MultiTapePTM.explicitBlockNetwork`) form
a network family (`Cslib.Complexity.CountingSimulation.NetworkFamily`) for the accept count of
every finite-state fair-coin machine, with explicit networks encoded by
`Cslib.Circuits.Frontier.ExplicitTensorNetwork.encExplicitNetwork` and admissibility
`Cslib.Complexity.CountingSimulation.ExplicitAdmissible`. This discharges the network interface
of the counting simulation (milestone H3 of #1833), so the conditional class containments of
`Complexity.Computability.Complexity.Classes.CountingSimulation.Containments` hold assuming only a
contraction algorithm. The joint time-and-space forms keep a single deciding machine within
time `2 ^ (C * T n / √⌊log₂ (T n)⌋)` and workspace `T n ^ d`, for a time-constructible
`T` with `max n 2 ≤ T n`. The contraction algorithm remains an explicit hypothesis; this
module does not prove the unconditional simulation.

**The family.** At the input `x`, the clock `t` and the schedule number `σ`, the network
(`Cslib.Complexity.CountingSimulation.blockNetworkOf`) is the explicit block-counting network
with blocks of `blockLength t = ⌈log₂ (t + 2)⌉` steps, `numBlocks t` intervals and the schedule
of `σ`'s base-3 digits (`Turing.MultiTapePTM.scheduleOfNat`), together with its `numBlocks t (3 k
+ 2)` row vertices. The number of blocked heads is `k + 1` (the input head and the `k` work
heads), and the admissibility constant is `6 (3 k + 1) (s + k + 4)` for `s` states.

* **Construction.** The network is computed on numbers
  (`Turing.MultiTapePTM.explicitBlockNetwork_eq_explicitNetworkNum`), in polynomial time
  (`Turing.MultiTapePTM.computableInPolyTime_explicitNetworkNum`), with `2 ^ b ≤ 2 (t + 2)`.
* **Counting identity.** Summing over the `3 ^ ((k + 1) numBlocks t)` schedule numbers is summing
  over the schedules (`Turing.MultiTapePTM.sum_range_scheduleOfNat`), which gives the accept count
  at the padded time (`Turing.MultiTapePTM.sum_contraction_explicitBlockNetwork`).
* **Admissibility** follows from `Turing.MultiTapePTM.admissible_explicitBlockNetwork`, with the
  vertex count, the table lengths and `t ≤ numBlocks t * blockLength t ≤ numEdges`.

## Main definitions

* `Cslib.Complexity.CountingSimulation.blockNetworkOf`: the network of an input, a clock and a
  schedule number.
* `Cslib.Complexity.CountingSimulation.blockNetworkFamily`: the network family of a machine.

## Main results

* `Cslib.Complexity.CountingSimulation.computableInPolyTime_blockNetworkOf`: the construction is
  polynomial-time.
* `Cslib.Complexity.CountingSimulation.networkFamilies_explicitAdmissible`: network families exist
  for all machines.
* `Cslib.Complexity.CountingSimulation.NTIME_subset_iUnion_DTIME_of_contractionAlgorithm`,
  `BPTIME_subset_iUnion_DTIME_of_contractionAlgorithm`,
  `PPTIME_subset_iUnion_DTIME_of_contractionAlgorithm`: the class containments assuming only a
  contraction algorithm.

* `SharpTIME_subset_iUnion_FTIME_of_contractionAlgorithm`: exact terminal counting with binary
  output, assuming only a contraction algorithm.
* `exists_computableInTimeAndSpace_of_mem_SharpTIME_of_contractionAlgorithm`: its joint
  time and polynomial-workspace bound.
* `exists_decidableInTimeAndSpace_of_mem_NTIME_of_contractionAlgorithm`,
  `exists_decidableInTimeAndSpace_of_mem_BPTIME_of_contractionAlgorithm`,
  `exists_decidableInTimeAndSpace_of_mem_PPTIME_of_contractionAlgorithm`: the joint time and
  polynomial-workspace bounds, assuming only a contraction algorithm.

## References

* [J. Hopcroft, W. Paul, L. Valiant, *On Time Versus Space*][HopcroftPaulValiant1977]
* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Theorem D.1 (contraction).
-/

public section

namespace Cslib.Complexity.CountingSimulation

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.ComputableInPolyTime
  Cslib.Circuits.Frontier ExplicitTensorNetwork

instance (t : ℕ) : NeZero (blockLength t) := ⟨Nat.pos_iff_ne_zero.mp (one_le_blockLength t)⟩

variable {k s : ℕ} {State : Type} (machine : MultiTapePTM k Bool State) (e : State ≃ Fin s)

/-- **The block-counting network** of the input `x`, the clock `t` and the schedule number `σ`:
the explicit block-counting network with blocks of `blockLength t` steps, `numBlocks t`
intervals and the schedule of `σ`, with its `numBlocks t * (3 * k + 2)` row vertices. -/
@[expose] noncomputable def blockNetworkOf (p : List Bool × ℕ × ℕ) :
    ℕ × ExplicitTensorNetwork ℕ :=
  (numBlocks p.2.1 * (3 * k + 2), machine.explicitBlockNetwork p.1 (blockLength p.2.1)
    (MultiTapePTM.scheduleOfNat k (numBlocks p.2.1) p.2.2) e)

/-- An interval of a clock `t` has at most `2 (t + 2)` choice strings. -/
theorem two_pow_blockLength_le (t : ℕ) : 2 ^ blockLength t ≤ 2 * (t + 2) := by
  have h := Nat.pow_pred_clog_lt_self one_lt_two (by omega : 1 < t + 2)
  have hpos := Nat.clog_pos one_lt_two (by omega : 1 < t + 2)
  unfold blockLength
  obtain ⟨c, hc⟩ : ∃ c, Nat.clog 2 (t + 2) = c + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  rw [hc] at h ⊢
  rw [pow_succ]
  simp only [Nat.pred_succ] at h
  omega

/-- **The construction is polynomial-time**, from the input in binary, the clock in unary and the
schedule number in binary. -/
theorem computableInPolyTime_blockNetworkOf [Finite State] :
    ComputableInPolyTime (blockNetworkOf machine e) (encPair encBits (encPair encUnary encNat))
      (encPair encNat encExplicitNetwork) := by
  classical
  have ht : ComputableInPolyTime (fun p : List Bool × ℕ × ℕ => p.2.1)
      (encPair encBits (encPair encUnary encNat)) encUnary := (snd _ _).fst'
  have hb : ComputableInPolyTime (fun p : List Bool × ℕ × ℕ => blockLength p.2.1)
      (encPair encBits (encPair encUnary encNat)) encUnary := by
    unfold blockLength
    exact (unary_clog_const 2).comp (unary_add' ht (const 2))
  have hq : ComputableInPolyTime (fun p : List Bool × ℕ × ℕ => numBlocks p.2.1)
      (encPair encBits (encPair encUnary encNat)) encUnary := by
    have h := unary_div.comp ((unary_sub' (unary_add' ht hb) (const 1)).prod hb)
    simpa only [numBlocks, Nat.ceilDiv_eq_add_pred_div, Function.comp_def] using h
  have hnet := MultiTapePTM.computableInPolyTime_explicitNetworkNum e machine (fst _ _) hb
    (fun p => Nat.pos_of_neZero (blockLength p.2.1)) hq (snd _ _).snd'
    (unary_mul' (const 2) (unary_add' ht (const 2))) fun p => two_pow_blockLength_le p.2.1
  have heq : blockNetworkOf machine e = fun p =>
      (numBlocks p.2.1 * (3 * k + 2), MultiTapePTM.explicitNetworkNum e (blockLength p.2.1)
        machine p.1 (numBlocks p.2.1) p.2.2) := by
    funext p
    rw [blockNetworkOf, MultiTapePTM.explicitBlockNetwork_eq_explicitNetworkNum]
  rw [heq]
  refine (unary_to_binary.comp (unary_mul' hq (const _))).prod ?_
  exact hnet.of_enc_eq fun _ => rfl

theorem numBlocks_pos {t : ℕ} (ht : 2 ≤ t) : 0 < numBlocks t := by
  have := le_paddedTime t
  unfold paddedTime at this
  rcases Nat.eq_zero_or_pos (numBlocks t) with h | h
  · rw [h, Nat.zero_mul] at this
    omega
  · exact h

/-- **The counting identity**: summed over the schedule numbers, the contractions of the networks
are the accept count at the padded time. -/
theorem sum_contraction_blockNetworkOf [Finite State] (x : List Bool) {t : ℕ} (ht : 2 ≤ t) :
    ∑ σ ∈ Finset.range (scheduleCount (k + 1) t),
        (blockNetworkOf machine e (x, t, σ)).2.contraction =
      machine.acceptCount x (paddedTime t) := by
  rw [scheduleCount, paddedTime,
    ← machine.sum_contraction_explicitBlockNetwork x (blockLength t) e (numBlocks_pos ht)]
  exact MultiTapePTM.sum_range_scheduleOfNat
    (fun σ => (machine.explicitBlockNetwork x (blockLength t) σ e).contraction)

/-- **Admissibility**: from the clock `t = 2` on, every network is admissible at size `t` with
the constant `6 (3 k + 1) (s + k + 4)`. -/
theorem explicitAdmissible_blockNetworkOf (x : List Bool) {t : ℕ} (σ : ℕ) (ht : 2 ≤ t) :
    ExplicitAdmissible (6 * (3 * k + 1) * (s + k + 4)) t (blockNetworkOf machine e (x, t, σ)) := by
  have hb : blockLength t ≤ 3 * Nat.log 2 t := Nat.clog_two_add_two_le_three_mul_log_two ht
  have hqb : numBlocks t * blockLength t ≤ 2 * t := by
    have := paddedTime_add_one_le ht
    unfold paddedTime at this
    omega
  obtain ⟨h1, h2, h3⟩ := machine.admissible_explicitBlockNetwork x (blockLength t)
    (MultiTapePTM.scheduleOfNat k (numBlocks t) σ) e hb hqb
  have htq := le_paddedTime t
  unfold paddedTime at htq
  have hb1 := one_le_blockLength t
  refine ⟨h1, h2, h3, ?_, fun v hv => machine.length_table_explicitBlockNetwork x _ _ e hv, ?_⟩
  · change (machine.explicitBlockNetwork x (blockLength t) _ e).vertices.length ≤ _
    rw [MultiTapePTM.length_vertices_explicitBlockNetwork, MultiTapePTM.letterBits]
    dsimp only
    have hq : numBlocks t ≤ 2 * t := le_trans (Nat.le_mul_of_pos_right _ hb1) hqb
    have e1 : numBlocks t * (3 * k + 2) ≤ 2 * t * (3 * k + 2) := Nat.mul_le_mul_right _ hq
    have e2 : numBlocks t * (3 * k + 1) * ((s + k + 4) * blockLength t) =
        (3 * k + 1) * (s + k + 4) * (numBlocks t * blockLength t) := by ring
    have e3 : (3 * k + 1) * (s + k + 4) * (numBlocks t * blockLength t) ≤
        (3 * k + 1) * (s + k + 4) * (2 * t) := Nat.mul_le_mul_left _ hqb
    have e4 : 2 * t * (3 * k + 2) ≤ 2 * ((3 * k + 1) * (s + k + 4) * t) := by
      have : 3 * k + 2 ≤ (3 * k + 1) * (s + k + 4) := by nlinarith
      calc 2 * t * (3 * k + 2) = 2 * (t * (3 * k + 2)) := by ring
        _ ≤ 2 * (t * ((3 * k + 1) * (s + k + 4))) := by gcongr
        _ = 2 * ((3 * k + 1) * (s + k + 4) * t) := by ring
    have e5 : (3 * k + 1) * (s + k + 4) * (2 * t) = 2 * ((3 * k + 1) * (s + k + 4) * t) := by
      ring
    have e6 : 6 * (3 * k + 1) * (s + k + 4) * t = 6 * ((3 * k + 1) * (s + k + 4) * t) := by ring
    omega
  · change t ≤ (machine.explicitBlockNetwork x (blockLength t) _ e).numEdges
    rw [MultiTapePTM.numEdges_explicitBlockNetwork, MultiTapePTM.letterBits]
    dsimp only
    have : numBlocks t * blockLength t * 1 ≤
        numBlocks t * blockLength t * (2 * (3 * k + 1) * (s + k + 4)) :=
      Nat.mul_le_mul_left _ (by nlinarith)
    have e7 : numBlocks t * blockLength t * (2 * (3 * k + 1) * (s + k + 4)) =
        2 * (numBlocks t * (3 * k + 1) * ((s + k + 4) * blockLength t)) := by ring
    omega

/-- **The block-counting network family** of a finite-state fair-coin machine, for its accept
count: `k + 1` blocked heads, admissibility constant `6 (3 k + 1) (s + k + 4)`, and the networks
`blockNetworkOf`. -/
noncomputable def blockNetworkFamily [Finite State] :
    NetworkFamily (encPair encNat encExplicitNetwork) (fun G => G.2.contraction)
      ExplicitAdmissible (fun x τ => machine.acceptCount x τ) where
  heads := k + 1
  constant := 6 * (3 * k + 1) * (s + k + 4)
  net := blockNetworkOf machine e
  polyTime := computableInPolyTime_blockNetworkOf machine e
  sum_value _ _ _ ht := sum_contraction_blockNetworkOf machine e _ ht
  admissible _ _ σ _ ht _ := explicitAdmissible_blockNetworkOf machine e _ σ ht

/-- **Network families for all machines** (milestone H3 of #1833): the explicit block-counting
networks discharge the network interface of the counting simulation. -/
theorem networkFamilies_explicitAdmissible :
    NetworkFamilies (encPair encNat encExplicitNetwork) (fun G => G.2.contraction)
      ExplicitAdmissible :=
  fun _ State _ M => ⟨blockNetworkFamily M (Finite.equivFin State)⟩

/-! ### The class containments assuming a contraction algorithm -/

variable {α : Type} {enc : α ↪ List Bool} {T : ℕ → ℕ}

/-- Exact terminal-path counting with subexponential time and polynomial workspace,
conditional only on a contraction algorithm for admissible explicit networks. -/
theorem exists_computableInTimeAndSpace_of_mem_SharpTIME_of_contractionAlgorithm
    (A : ContractionAlgorithm (encPair encNat encExplicitNetwork) (fun G => G.2.contraction)
      ExplicitAdmissible) (hT : TimeConstructible T) (hTn : ∀ n, max n 2 ≤ T n)
    {f : α → ℕ} (hf : f ∈ SharpTIME enc T) :
    ∃ C d : ℕ, ComputableInTimeAndSpace f enc encNat
      (fun a => 2 ^ (C * T (enc a).length / Nat.sqrt (Nat.log 2 (T (enc a).length))))
      (fun a => T (enc a).length ^ d) :=
  exists_computableInTimeAndSpace_of_mem_SharpTIME networkFamilies_explicitAdmissible A hT hTn hf

/-- The functional counting containment, assuming only the explicit-network contraction
algorithm. Output is the exact natural count in binary. -/
theorem SharpTIME_subset_iUnion_FTIME_of_contractionAlgorithm
    (A : ContractionAlgorithm (encPair encNat encExplicitNetwork) (fun G => G.2.contraction)
      ExplicitAdmissible) (hT : TimeConstructible T) (hTn : ∀ n, max n 2 ≤ T n) :
    SharpTIME enc T ⊆ ⋃ C : ℕ,
      FTIME enc encNat (fun n => 2 ^ (C * T n / Nat.sqrt (Nat.log 2 (T n)))) :=
  SharpTIME_subset_iUnion_FTIME networkFamilies_explicitAdmissible A hT hTn

/-- **Nondeterministic time with polynomial workspace**, conditional only on a
contraction algorithm for admissible explicit networks. For time-constructible `T` with
`max n 2 ≤ T n`, one deterministic machine decides each problem in `NTIME[T]` within time
`2 ^ (C * T n / √⌊log₂ (T n)⌋)` and workspace `T n ^ d`. -/
theorem exists_decidableInTimeAndSpace_of_mem_NTIME_of_contractionAlgorithm
    (A : ContractionAlgorithm (encPair encNat encExplicitNetwork) (fun G => G.2.contraction)
      ExplicitAdmissible) (hT : TimeConstructible T) (hTn : ∀ n, max n 2 ≤ T n)
    {L : Set α} (hL : L ∈ NTIME enc T) :
    ∃ C d : ℕ, DecidableInTimeAndSpace L enc
      (fun a => 2 ^ (C * T (enc a).length / Nat.sqrt (Nat.log 2 (T (enc a).length))))
      (fun a => T (enc a).length ^ d) :=
  exists_decidableInTimeAndSpace_of_mem_NTIME networkFamilies_explicitAdmissible A hT hTn hL

/-- **Bounded-error probabilistic time with polynomial workspace**, conditional only on a
contraction algorithm for admissible explicit networks. For time-constructible `T` with
`max n 2 ≤ T n`, one deterministic machine decides each problem in `BPTIME[T]` within time
`2 ^ (C * T n / √⌊log₂ (T n)⌋)` and workspace `T n ^ d`. -/
theorem exists_decidableInTimeAndSpace_of_mem_BPTIME_of_contractionAlgorithm
    (A : ContractionAlgorithm (encPair encNat encExplicitNetwork) (fun G => G.2.contraction)
      ExplicitAdmissible) (hT : TimeConstructible T) (hTn : ∀ n, max n 2 ≤ T n)
    {L : Set α} (hL : L ∈ BPTIME enc T) :
    ∃ C d : ℕ, DecidableInTimeAndSpace L enc
      (fun a => 2 ^ (C * T (enc a).length / Nat.sqrt (Nat.log 2 (T (enc a).length))))
      (fun a => T (enc a).length ^ d) :=
  exists_decidableInTimeAndSpace_of_mem_BPTIME networkFamilies_explicitAdmissible A hT hTn hL

/-- **Strict-majority probabilistic time with polynomial workspace**, conditional only on a
contraction algorithm for admissible explicit networks. For time-constructible `T` with
`max n 2 ≤ T n`, one deterministic machine decides each problem in `PPTIME[T]` within time
`2 ^ (C * T n / √⌊log₂ (T n)⌋)` and workspace `T n ^ d`. -/
theorem exists_decidableInTimeAndSpace_of_mem_PPTIME_of_contractionAlgorithm
    (A : ContractionAlgorithm (encPair encNat encExplicitNetwork) (fun G => G.2.contraction)
      ExplicitAdmissible) (hT : TimeConstructible T) (hTn : ∀ n, max n 2 ≤ T n)
    {L : Set α} (hL : L ∈ PPTIME enc T) :
    ∃ C d : ℕ, DecidableInTimeAndSpace L enc
      (fun a => 2 ^ (C * T (enc a).length / Nat.sqrt (Nat.log 2 (T (enc a).length))))
      (fun a => T (enc a).length ^ d) :=
  exists_decidableInTimeAndSpace_of_mem_PPTIME networkFamilies_explicitAdmissible A hT hTn hL

/-- **`NTIME[T] ⊆ ⋃ C, DTIME[2 ^ (C * T / √⌊log₂ T⌋)]`**, conditional only on a contraction
algorithm for admissible explicit networks, for a time-constructible `T` with `max n 2 ≤ T n`. -/
theorem NTIME_subset_iUnion_DTIME_of_contractionAlgorithm
    (A : ContractionAlgorithm (encPair encNat encExplicitNetwork) (fun G => G.2.contraction)
      ExplicitAdmissible) (hT : TimeConstructible T) (hTn : ∀ n, max n 2 ≤ T n) :
    NTIME enc T ⊆ ⋃ C, DTIME enc fun n => 2 ^ (C * T n / Nat.sqrt (Nat.log 2 (T n))) :=
  NTIME_subset_iUnion_DTIME networkFamilies_explicitAdmissible A hT hTn

/-- **`BPTIME[T] ⊆ ⋃ C, DTIME[2 ^ (C * T / √⌊log₂ T⌋)]`**, conditional only on a contraction
algorithm for admissible explicit networks, for a time-constructible `T` with `max n 2 ≤ T n`. -/
theorem BPTIME_subset_iUnion_DTIME_of_contractionAlgorithm
    (A : ContractionAlgorithm (encPair encNat encExplicitNetwork) (fun G => G.2.contraction)
      ExplicitAdmissible) (hT : TimeConstructible T) (hTn : ∀ n, max n 2 ≤ T n) :
    BPTIME enc T ⊆ ⋃ C, DTIME enc fun n => 2 ^ (C * T n / Nat.sqrt (Nat.log 2 (T n))) :=
  BPTIME_subset_iUnion_DTIME networkFamilies_explicitAdmissible A hT hTn

/-- **`PPTIME[T] ⊆ ⋃ C, DTIME[2 ^ (C * T / √⌊log₂ T⌋)]`**, conditional only on a contraction
algorithm for admissible explicit networks, for a time-constructible `T` with `max n 2 ≤ T n`. -/
theorem PPTIME_subset_iUnion_DTIME_of_contractionAlgorithm
    (A : ContractionAlgorithm (encPair encNat encExplicitNetwork) (fun G => G.2.contraction)
      ExplicitAdmissible) (hT : TimeConstructible T) (hTn : ∀ n, max n 2 ≤ T n) :
    PPTIME enc T ⊆ ⋃ C, DTIME enc fun n => 2 ^ (C * T n / Nat.sqrt (Nat.log 2 (T n))) :=
  PPTIME_subset_iUnion_DTIME networkFamilies_explicitAdmissible A hT hTn

end Cslib.Complexity.CountingSimulation
