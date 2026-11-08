/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.TimeSpace.Basic
public import Complexity.Computability.Complexity.Classes.Time.SigmaTwoChain
public import Complexity.Computability.Machines.Turing.MultiTape.Universal.LookupRun
public import Complexity.Computability.Machines.Turing.MultiTape.Universal.Bit
public import Complexity.Computability.Machines.Turing.MultiTape.Universal.Space
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Lists
import Complexity.Computability.Machines.Turing.MultiTape.Internal.OCombinators
import Complexity.Computability.Machines.Turing.MultiTape.Internal.BinarySizeFacts
import Complexity.Computability.Machines.Turing.MultiTape.BlockTrace
import Complexity.Computability.Machines.Turing.MultiTape.Run
import Complexity.Computability.Machines.Turing.MultiTape.Universal.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Universal.Input
import Mathlib.Data.Nat.Size
import Complexity.Tactic.EncLen

/-!
# The time–space speedup: `TISP(t, s) ⊆ Σ₂TIME`

A machine running in time `T` and work space `S` is simulated in two-quantifier alternating time by
guessing configurations. The existential player writes `b = ⌊√T⌋ + 1` configurations of the
universal machine (`Turing.MultiTapeTM.Universal`), at distance `b` steps from one another. The
universal player picks one block, and the verifier recomputes that block of `b` steps and compares
the result with the next guessed configuration (`Cslib.Complexity.mem_SigmaTwoTIME_of_chain`).

This is the speedup lemma of [Kannan][Kannan1984], in the form of Arora and Barak ([AroraBarak09],
§5.4) and of
[Fortnow, Lipton, van Melkebeek and Viglas, Lemma 3.1][FortnowLiptonVanMelkebeekViglas2005].

**The bound is weaker than the textbook one.** The textbook bound is `TISP(t, s) ⊆ Σ₂TIME(√(t s))`.
This file proves `TISP(t, s) ⊆ Σ₂TIME(√t · (s + n log² n + log² t))`. The verifier recomputes a
block step by step, and each step copies the whole configuration of `O(s + log n)` bits, so a block
of `√t` steps costs `√t · s` rather than `√t + s`. Reaching `√(t s)` needs a simulation whose
steps cost `O(1)` amortized, and that remains open. The weaker bound still suffices for the
Arora–Barak instance `TISP(n¹², n²) ⊆ Σ₂TIME(n⁸)`. At `t = n¹²` and `s = n²` the general bound
would give `n⁷`.

The simulation reads the input through an oracle `look` (`Turing.MultiTapeTM.Universal.lookStep`),
not from the instance. The input of the simulated machine is then any word `ι a` that `look`
describes from a short parameter `P a`. The lower bound `NTIME(n) ⊄ TISP(n^{1.2}, n^{0.2})` needs
exactly this: it simulates a machine on an input padded to a polynomial length, without writing the
padding.

## Main results

* `Cslib.Complexity.mem_SigmaTwoTIME_of_virtualRun`: the speedup for a machine on an input
  described by an oracle, with an explicit cost bound.
* `Cslib.Complexity.TISP_subset_SigmaTwoTIME`: `TISP(t, s) ⊆ Σ₂TIME(τ)` whenever
  `(√t + 1) · (s + (n + 1) (log n)² + (log t)²) = O(τ)`.
* `Cslib.Complexity.TISP_pow_twelve_subset_SigmaTwoTIME`: `TISP(n¹², n²) ⊆ Σ₂TIME(n⁸)`, the
  Arora–Barak instance.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [L. Fortnow, R. Lipton, D. van Melkebeek, A. Viglas, *Time-Space Lower Bounds for
  Satisfiability*][FortnowLiptonVanMelkebeekViglas2005]
-/

public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.Universal

/-! ### Honest runs of the simulation -/

section Honest

variable {k : ℕ} {State : Type} [Fintype State] (eS : State ↪ ℕ) (M : MultiTapeTM k Bool State)

/-- An input symbol of a word of bits is encoded within two bits. -/
private lemma length_eSym_inputSymbol_le (y : List Bool) (q : ℕ) :
    (eSym (inputSymbol (y.map eBit) q)).length ≤ 2 := by
  unfold inputSymbol
  split_ifs
  · simp
  · rcases h : ((y.map eBit).drop (q - 1)).head? with _ | o
    · simp
    · obtain ⟨b, -, rfl⟩ : ∃ b ∈ y, eBit b = o := by
        have := List.mem_of_mem_head? h
        exact List.mem_map.mp (List.mem_of_mem_drop this)
      cases b <;> simp only [encOption_some, List.length_cons, encUnary_apply,
        List.length_replicate] <;> decide

/-- **Honest configurations.** Along the simulation of the description of a machine within the
space `s`, the configuration is encoded within `O(s + log n)` bits, at most one symbol is
emitted while the machine computes a single bit, and the input head stays on the input. -/
private lemma honest_bounds {y : List Bool} {b : Bool} {T s : ℕ}
    (hM : M.ComputesInTimeAndSpace y [b] T s) (j : ℕ) :
    (eCfg ((stepOut (desc eS eBit M) (y.map eBit))^[j] (init (desc eS eBit M), [])).1).length ≤
        (12 * descLen (desc eS eBit M) + 40) * (s + (encNat y.length).length + 2) ∧
      ((stepOut (desc eS eBit M) (y.map eBit))^[j] (init (desc eS eBit M), [])).2.length ≤ 1 ∧
      ((stepOut (desc eS eBit M) (y.map eBit))^[j] (init (desc eS eBit M), [])).1.inputPos ≤
        y.length + 1 := by
  set d := desc eS eBit M
  have hsim := simulate_desc eS eBit M y j
  have hout : ((stepOut d (y.map eBit))^[j] (init d, [])).2 =
      (M.runFrom (M.initCfg y) j).output.map eBit := congrArg Prod.fst hsim
  refine ⟨?_, ?_, ?_⟩
  · have hc := length_eCfg_le_space d (y.map eBit) j
    have hσ : simSpace d (y.map eBit) j ≤ s :=
      (simSpace_desc eS eBit M y j).trans_le (space_le_of_runsInSpace hM.2.2 j)
    have hE := ComputableTidilyInO.length_encNat_add_le y.length 1
    have hk := tapes_le d
    simp only [List.length_map] at hc
    change (eCfg (run d (y.map eBit) j)).length ≤ _
    nlinarith
  · rw [hout, List.length_map]
    simpa using (hM.output_runFrom_prefix j).length_le
  · simpa using (inv_iterate d (y.map eBit) j).1.inputPos

/-- The time of a step without the input, in the length of the description, of the configuration
and of the position of the input head. -/
private lemma wTime_le (d : Desc) (c : SCfg) (o : Option ℕ) (ho : (eSym o).length ≤ 2)
    (hk : c.workTapes.length ≤ descLen d) :
    wTime ((d, c), o) ≤ (2 * descLen d + 1) * (descLen d + 1) *
      (4 * descLen d + 2 * (eCfg c).length + 12) + ((encNat c.inputPos).length + 1) ^ 2 := by
  have ht := table_le d
  have hl : (eWCtx ((d, c), o)).length + 1 ≤ 4 * descLen d + 2 * (eCfg c).length + 12 := by
    enc_len [eWCtx, descLen]
  unfold wTime
  simp only [WCtx.cfg, WCtx.desc]
  have h₁ : c.workTapes.length + d.table.length + 1 ≤ 2 * descLen d + 1 := by omega
  have h₂ := Nat.mul_le_mul (Nat.mul_le_mul h₁ (le_refl ((eDesc d).length + 1))) hl
  exact Nat.add_le_add_right h₂ _

/-- The constant of the cost of honest steps, for a description of length `D`. -/
private def honestK (D : ℕ) : ℕ :=
  (2 * D + 1) * (D + 1) * (4 * D + 12 + 4 * (12 * D + 40)) + 4 * (12 * D + 40) + 2 * D + 12

/-- **The cost of honest steps.** Along the run with a faithful oracle of the description of a
machine within the space `s`, every step with the oracle costs, and every configuration with its
output is encoded within, `honestK` times the space, the oracle cost `L`, the length of the
parameter and the square of the length of the input length. -/
private lemma honest_cost {π : Type} {encP : π ↪ List Bool} {look : π × ℕ → Option ℕ}
    {TL SL : π × ℕ → ℕ} {p : π} {y : List Bool} {b : Bool} {T s L : ℕ}
    (hM : M.ComputesInTimeAndSpace y [b] T s)
    (hlook : ∀ q ≤ y.length + 1, look (p, q) = inputSymbol (y.map eBit) q)
    (hL : ∀ q ≤ y.length + 1, TL (p, q) + SL (p, q) ≤ L) (j : ℕ) :
    lookStepTime (desc eS eBit M) look TL SL
        (p, (lookStep (desc eS eBit M) look p)^[j] (init (desc eS eBit M), [])) ≤
      honestK (descLen (desc eS eBit M)) *
        (s + (encP p).length + L + ((encNat y.length).length + 1) ^ 2) ∧
    (encPair encP (encPair eCfg (encList encUnary))
        (p, (lookStep (desc eS eBit M) look p)^[j] (init (desc eS eBit M), []))).length ≤
      honestK (descLen (desc eS eBit M)) *
        (s + (encP p).length + L + ((encNat y.length).length + 1) ^ 2) := by
  have hlook' : ∀ q ≤ (y.map eBit).length + 1, look (p, q) = inputSymbol (y.map eBit) q := by
    simpa only [List.length_map] using hlook
  rw [lookStep_iterate_eq_stepOut (desc eS eBit M) look (x := y.map eBit) hlook' j]
  obtain ⟨hc, hout, hpos⟩ := honest_bounds eS M hM j
  have hinv := inv_iterate (desc eS eBit M) (y.map eBit) j
  set d := desc eS eBit M
  set c := (stepOut d (y.map eBit))^[j] (init d, [])
  have htapes : c.1.workTapes.length ≤ descLen d := hinv.1.tapes
  have hsym : (eSym (look (p, c.1.inputPos))).length ≤ 2 := by
    rw [hlook _ hpos]; exact length_eSym_inputSymbol_le y _
  have hw := wTime_le d c.1 _ hsym htapes
  have hposE : (encNat c.1.inputPos).length ≤ (encNat y.length).length + 1 :=
    (length_encNat_mono hpos).trans
      (ComputableTidilyInO.length_encNat_add_le y.length 1)
  have hL' := hL _ hpos
  have hlist : (encList encUnary c.2).length ≤ 2 * descLen d + 1 := by
    have h := length_encList_le encUnary c.2 (b := descLen d) fun o ho => by
      simpa only [encUnary_apply, List.length_replicate] using hinv.2.2 o ho
    have : c.2.length * (2 * descLen d + 1) ≤ 1 * (2 * descLen d + 1) :=
      Nat.mul_le_mul_right _ hout
    omega
  have hsq : ((encNat c.1.inputPos).length + 1) ^ 2 ≤
      4 * ((encNat y.length).length + 1) ^ 2 := by
    have h₁ : ((encNat c.1.inputPos).length + 1) ^ 2 ≤ ((encNat y.length).length + 2) ^ 2 :=
      Nat.pow_le_pow_left (by omega) 2
    nlinarith
  have hE1 : (encNat y.length).length + 1 ≤ ((encNat y.length).length + 1) ^ 2 :=
    Nat.le_self_pow two_ne_zero _
  obtain ⟨W, hW⟩ : ∃ W, W = s + (encP p).length + L + ((encNat y.length).length + 1) ^ 2 :=
    ⟨_, rfl⟩
  rw [← hW]
  have hW1 : 1 ≤ W := by
    have := Nat.one_le_pow 2 ((encNat y.length).length + 1) (Nat.succ_pos _)
    omega
  have hsW : s + (encNat y.length).length + 2 ≤ 2 * W := by omega
  -- the inner factor of the step without the input
  have hinner : 4 * descLen d + 2 * (eCfg c.1).length + 12 ≤
      (4 * descLen d + 12 + 4 * (12 * descLen d + 40)) * W := by
    have h₁ := Nat.mul_le_mul_left (4 * descLen d + 12) hW1
    have h₂ := Nat.mul_le_mul_left (12 * descLen d + 40) hsW
    linarith
  have hA := Nat.mul_le_mul_left ((2 * descLen d + 1) * (descLen d + 1)) hinner
  have hDW := Nat.mul_le_mul_left (2 * descLen d) hW1
  have h₀ : 0 ≤ (4 * (12 * descLen d + 40) + 2 * descLen d) * W := Nat.zero_le _
  have h₁ := Nat.mul_le_mul_left (12 * descLen d + 40) hsW
  unfold honestK
  simp only [lookStepTime, length_encPair]
  constructor
  · linarith
  · linarith

end Honest

/-- The numeric core of the speedup: a block of `b + 1` steps of width `W + 1`, with
`b + 1 ≤ 2 (r + 1)` and `(r + 1) W ≤ C τ + C`, costs at most `4 K C (τ + 1)`. -/
private lemma speedup_arith {K b r W C τ : ℕ} (hb : b + 1 ≤ 2 * (r + 1)) (hW : 1 ≤ W)
    (hτ : (r + 1) * W ≤ C * τ + C) : K * ((b + 1) * (W + 1)) ≤ 4 * K * C * τ + 4 * K * C := by
  have h₁ : (b + 1) * (W + 1) ≤ (2 * (r + 1)) * (2 * W) := Nat.mul_le_mul hb (by omega)
  have h₂ : (2 * (r + 1)) * (2 * W) = 4 * ((r + 1) * W) := by ring
  have h₃ := Nat.mul_le_mul_left K (h₁.trans (h₂ ▸ Nat.mul_le_mul_left 4 hτ))
  calc K * ((b + 1) * (W + 1)) ≤ K * (4 * (C * τ + C)) := h₃
    _ = 4 * K * C * τ + 4 * K * C := by ring

/-- The arithmetic of a checked block: with `X` the cost of a configuration (`X ≤ K W`), the
block of `b` steps with a counter of `z` bits (`(z + 1)² ≤ 4 W`) costs `O((b + 1) (W + 1))`. -/
private lemma block_arith {K W b z p X : ℕ} (hW : 1 ≤ W) (hp : p ≤ W) (hX : X ≤ K * W)
    (hz : (z + 1) ^ 2 ≤ 4 * W) :
    2 * p + 1 + (2 * X + 1 + (2 * z + 1)) + (b + 1) * (2 * (K * W) + (z + 1) ^ 2) +
        (2 * p + 1 + (2 * X + 1 + (2 * z + 1))) ≤
      (8 * K + 24) * ((b + 1) * (W + 1)) := by
  have hz1 : z + 1 ≤ (z + 1) ^ 2 := Nat.le_self_pow two_ne_zero _
  have h₁ : (b + 1) * (2 * (K * W) + (z + 1) ^ 2) ≤ (b + 1) * (2 * (K * W) + 4 * W) :=
    Nat.mul_le_mul_left _ (by omega)
  have h₂ : 1 ≤ (b + 1) * (W + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h₃ : W + 1 ≤ (b + 1) * (W + 1) := Nat.le_mul_of_pos_left _ (Nat.succ_pos b)
  have h₄ : K * W ≤ K * ((b + 1) * (W + 1)) :=
    Nat.mul_le_mul_left _ ((Nat.le_succ W).trans h₃)
  have h₅ : (b + 1) * (2 * (K * W) + 4 * W) ≤ (2 * K + 4) * ((b + 1) * (W + 1)) := by
    have : (b + 1) * (2 * (K * W) + 4 * W) = (2 * K + 4) * ((b + 1) * W) := by ring
    rw [this]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.le_succ W))
  have h₆ := Nat.zero_le (K * ((b + 1) * (W + 1)))
  linarith

/-- The certificate: `b` configurations, each of cost `≤ K W`, and a counter of `z` bits. -/
private lemma cert_arith {K W b z X : ℕ} (hz : (z + 1) ^ 2 ≤ 4 * W)
    (hX : X ≤ b * (2 * (K * W) + 1)) :
    2 * z + 1 + X ≤ (8 * K + 24) * ((b + 1) * (W + 1)) := by
  have hz1 : z + 1 ≤ (z + 1) ^ 2 := Nat.le_self_pow two_ne_zero _
  have h₃ : W + 1 ≤ (b + 1) * (W + 1) := Nat.le_mul_of_pos_left _ (Nat.succ_pos b)
  have h₁ : b * (2 * (K * W) + 1) ≤ (2 * K + 1) * ((b + 1) * (W + 1)) := by
    have : b * (2 * (K * W) + 1) = 2 * K * (b * W) + b := by ring
    rw [this]
    have h₇ : b * W ≤ (b + 1) * (W + 1) := Nat.mul_le_mul (Nat.le_succ b) (Nat.le_succ W)
    have h₈ : b ≤ (b + 1) * (W + 1) :=
      (Nat.le_succ b).trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos W))
    have h₉ := Nat.mul_le_mul_left (2 * K) h₇
    linarith
  have h₆ := Nat.zero_le (K * ((b + 1) * (W + 1)))
  linarith

/-- Blocks of `ofBits bw` steps compose. -/
private lemma iterate_lookRun {π : Type} (d : Desc) (look : π × ℕ → Option ℕ) (p : π)
    (bw : List Bool) (c : SCfg × List ℕ) (i : ℕ) :
    (fun s => lookRun d look (p, (s, bw)))^[i] c = (lookStep d look p)^[ofBits bw * i] c := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, Nat.mul_succ, Nat.add_comm, Function.iterate_add_apply]
    rfl

variable {α : Type} {enc : α ↪ List Bool}

/-- **The speedup by a virtual run.** Let `M` compute the bit `g a` from the input `ι a` within
the time `T a` and the work space `S a`, and let the input be available through an oracle `look`
on a linear parameter `P a`, faithful on the positions the input head reaches and within the
cost `L a`. Then `{a | g a}` is in `Σ₂TIME(τ)` for every `τ` with
`(√T + 1) · (S + |P| + L + (log |ι a|)² + (log T)²) = O(τ)`: the existential player writes `√T`
configurations at distance `√T` steps, and the universal player checks one block of `√T` steps.
The logarithm is of the length `|ι a|` of the simulated input, not of the length `n = |enc a|` of
the instance; for a virtually padded input `|ι a|` is much larger than `n`. -/
theorem mem_SigmaTwoTIME_of_virtualRun {π : Type} [Inhabited π] {eP : π ↪ List Bool} {k : ℕ}
    {State : Type} [Finite State] {M : MultiTapeTM k Bool State} {ι : α → List Bool}
    {g : α → Bool} {T S : α → ℕ} (hM : ∀ a, M.ComputesInTimeAndSpace (ι a) [g a] (T a) (S a))
    {P : α → π} (hP : ComputableInO P enc eP (fun a => (enc a).length) (fun a => (enc a).length))
    {look : π × ℕ → Option ℕ} {TL SL : π × ℕ → ℕ}
    (hlook : ComputableInO look (encPair eP encNat) eSym TL SL)
    (hlookEq : ∀ a q, q ≤ (ι a).length + 1 → look (P a, q) = inputSymbol ((ι a).map eBit) q)
    {L : α → ℕ} (hL : ∀ a q, q ≤ (ι a).length + 1 → TL (P a, q) + SL (P a, q) ≤ L a)
    {τ : ℕ → ℕ}
    (hτ : ∃ C, ∀ a, (Nat.sqrt (T a) + 1) * (S a + (eP (P a)).length + L a +
      ((ι a).length.size + 1) ^ 2 + ((T a).size + 1) ^ 2) ≤ C * τ (enc a).length + C) :
    {a | g a = true} ∈ SigmaTwoTIME enc τ := by
  obtain ⟨C, hC⟩ := hτ
  have : Fintype State := Fintype.ofFinite State
  let eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
  let d := desc eS eBit M
  let K := honestK (descLen d)
  -- the bounds of a block from a configuration
  let R : π × (SCfg × List ℕ) × List Bool → ℕ := fun q =>
    (Finset.range (ofBits q.2.2 + 1)).sup fun k =>
      lookStepTime d look TL SL (q.1, (lookStep d look q.1)^[k] q.2.1)
  let B : π × (SCfg × List ℕ) × List Bool → ℕ := fun q =>
    (Finset.range (ofBits q.2.2 + 1)).sup fun k =>
      (encPair eP (encPair eCfg (encList encUnary)) (q.1, (lookStep d look q.1)^[k] q.2.1)).length
  have hrun := lookRun_inO d look (R := R) (B := B) hlook
    (fun q k hk => Finset.le_sup (f := fun k =>
      lookStepTime d look TL SL (q.1, (lookStep d look q.1)^[k] q.2.1))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)))
    (fun q k hk => Finset.le_sup (f := fun k =>
      (encPair eP (encPair eCfg (encList encUnary)) (q.1, (lookStep d look q.1)^[k] q.2.1)).length)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)))
  have hnext := hrun.prod (ComputableInO.const (encMid := encBool) true)
  -- the test: the output is the bit `1`
  have hgoal : ComputableInO (fun x : π × (SCfg × List ℕ) => decide ([1] = x.2.2))
      (encPair eP (encPair eCfg (encList encUnary))) encBool
      (fun x => (encPair eP (encPair eCfg (encList encUnary)) x).length)
      (fun x => (encPair eP (encPair eCfg (encList encUnary)) x).length) := by
    have h := (ComputableInO.const (encIn := encPair eP (encPair eCfg (encList encUnary)))
      (encMid := encList encUnary) [1]).eq'
      (ComputableInO.snd eP (encPair eCfg (encList encUnary))).snd'
    have h1 : (encList encUnary [1]).length ≤ 4 := by decide
    refine h.mono 64 (fun x => ?_) (fun x => ?_)
    · have h2 : (encList encUnary x.2.2).length ≤
          (encPair eP (encPair eCfg (encList encUnary)) x).length := by
        enc_len
      nlinarith
    · have h2 : (encList encUnary x.2.2).length ≤
          (encPair eP (encPair eCfg (encList encUnary)) x).length := by
        enc_len
      enc_len at h2 ⊢
  refine mem_SigmaTwoTIME_of_chain (eS := encPair eCfg (encList encUnary)) (t := τ)
    (s₀ := (init d, [])) (next := lookRun d look) hP hnext hgoal ?_ ?_
  · intro a bw m h
    rw [iterate_lookRun] at h
    have hfaith : ∀ q ≤ ((ι a).map eBit).length + 1,
        look (P a, q) = inputSymbol ((ι a).map eBit) q := by
      simpa only [List.length_map] using hlookEq a
    rw [lookStep_iterate_eq_stepOut d look hfaith] at h
    have hsim := congrArg Prod.fst (simulate_desc eS eBit M (ι a) (ofBits bw * m))
    simp only [simulate] at hsim
    rw [hsim] at h
    have h' : [1] = (M.runFrom (M.initCfg (ι a)) (ofBits bw * m)).output.map eBit :=
      of_decide_eq_true h
    obtain ⟨b, hb, h1⟩ := List.map_eq_singleton_iff.mp h'.symm
    have hpre := (hM a).output_runFrom_prefix (ofBits bw * m)
    rw [hb] at hpre
    have hbg : b = g a := by
      have := hpre.eq_of_length (by simp)
      simpa using this
    change g a = true
    rw [← hbg]
    cases b
    · exact absurd h1 (by decide)
    · rfl
  · refine ⟨4 * (8 * K + 24) * C + 1, fun a ha => ?_⟩
    have ha : g a = true := ha
    have hfaith : ∀ q ≤ ((ι a).map eBit).length + 1,
        look (P a, q) = inputSymbol ((ι a).map eBit) q := by
      simpa only [List.length_map] using hlookEq a
    obtain ⟨W, hW⟩ : ∃ W, W = S a + (eP (P a)).length + L a +
        ((encNat (ι a).length).length + 1) ^ 2 + ((T a).size + 1) ^ 2 := ⟨_, rfl⟩
    have hCW : (Nat.sqrt (T a) + 1) * W ≤ C * τ (enc a).length + C := by
      rw [hW, length_encNat_eq_size]; exact hC a
    have hW1 : 1 ≤ W := by
      have := Nat.one_le_pow 2 ((T a).size + 1) (Nat.succ_pos _); omega
    have hcost : ∀ j, lookStepTime d look TL SL
          (P a, (lookStep d look (P a))^[j] (init d, [])) ≤ K * W ∧
        (encPair eP (encPair eCfg (encList encUnary))
          (P a, (lookStep d look (P a))^[j] (init d, []))).length ≤ K * W := by
      intro j
      obtain ⟨h₁, h₂⟩ := honest_cost eS M (encP := eP) (hM a) (hlookEq a) (hL a) j
      have h₃ : K * (S a + (eP (P a)).length + L a + ((encNat (ι a).length).length + 1) ^ 2) ≤
          K * W := Nat.mul_le_mul_left _ (by omega)
      exact ⟨h₁.trans h₃, h₂.trans h₃⟩
    have hcfg : ∀ j, (encPair eCfg (encList encUnary)
        ((lookStep d look (P a))^[j] (init d, []))).length ≤ K * W := fun j => by
      have := (hcost j).2
      rw [length_encPair] at this
      dsimp only at this
      omega
    set b := Nat.sqrt (T a) + 1 with hb
    have hob : ofBits b.bits = b := Nat.foldr_bit_bits b
    have hiter : ∀ i, (fun s => lookRun d look (P a, (s, b.bits)))^[i] (init d, []) =
        (lookStep d look (P a))^[b * i] (init d, []) := fun i => by
      rw [iterate_lookRun, hob]
    -- the final arithmetic
    have hfin : ∀ X, X ≤ (8 * K + 24) * ((b + 1) * (W + 1)) →
        X ≤ (4 * (8 * K + 24) * C + 1) * τ (enc a).length + (4 * (8 * K + 24) * C + 1) := by
      intro X hX
      have := speedup_arith (K := 8 * K + 24) (b := b) (r := Nat.sqrt (T a)) (by omega) hW1 hCW
      nlinarith
    have hKW : K * W ≤ (8 * K + 24) * ((b + 1) * (W + 1)) := by
      have h₁ : W ≤ (b + 1) * (W + 1) :=
        (Nat.le_succ W).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos b))
      exact Nat.mul_le_mul (by omega) h₁
    -- the length of the counter
    have hz : (b.bits.length + 1) ^ 2 ≤ 4 * W := by
      have hbT : b ≤ T a + 1 := by have := Nat.sqrt_le_self (T a); omega
      have h₂ : (encNat b).length ≤ (encNat (T a)).length + 1 :=
        (length_encNat_mono hbT).trans
          (ComputableTidilyInO.length_encNat_add_le (T a) 1)
      rw [length_encNat_eq_size (T a)] at h₂
      have h₅ : b.bits.length = (encNat b).length := rfl
      have h₃ : (b.bits.length + 1) ^ 2 ≤ ((T a).size + 2) ^ 2 :=
        Nat.pow_le_pow_left (by omega) 2
      have h₄ : ((T a).size + 2) ^ 2 ≤ 4 * ((T a).size + 1) ^ 2 := by nlinarith
      omega
    refine ⟨b.bits, b, ?_, fun i hi => ?_, ?_, ?_⟩
    · -- the run accepts
      have hJ : T a ≤ b * b := (Nat.lt_succ_sqrt (T a)).le
      change decide ([1] = _) = true
      rw [hiter, lookStep_iterate_eq_stepOut d look hfaith]
      have hsim := congrArg Prod.fst (simulate_desc eS eBit M (ι a) (b * b))
      simp only [simulate] at hsim
      rw [hsim, ((hM a).runFrom_of_le hJ).2, ha]
      rfl
    · -- a checked block
      apply hfin
      rw [hiter]
      dsimp only
      rw [hob]
      set c := (lookStep d look (P a))^[b * i] (init d, [])
      have hR : R (P a, (c, b.bits)) ≤ K * W := Finset.sup_le fun k _ => by
        change lookStepTime d look TL SL (P a, (lookStep d look (P a))^[k] c) ≤ K * W
        rw [← Function.iterate_add_apply]; exact (hcost _).1
      have hB : B (P a, (c, b.bits)) ≤ K * W := Finset.sup_le fun k _ => by
        change (encPair eP (encPair eCfg (encList encUnary))
          (P a, (lookStep d look (P a))^[k] c)).length ≤ K * W
        rw [← Function.iterate_add_apply]; exact (hcost _).2
      have hX : (encPair eCfg (encList encUnary) c).length ≤ K * W := hcfg (b * i)
      have hblk := block_arith (K := K) (b := b) (p := (eP (P a)).length) hW1 (by omega) hX hz
      have hmul : (b + 1) * (R (P a, (c, b.bits)) + B (P a, (c, b.bits)) +
          (b.bits.length + 1) ^ 2) ≤ (b + 1) * (2 * (K * W) + (b.bits.length + 1) ^ 2) :=
        Nat.mul_le_mul_left _ (by omega)
      enc_len at hblk ⊢
    · -- the final test
      apply hfin
      refine le_trans ?_ hKW
      change (encPair eP (encPair eCfg (encList encUnary)) (P a, _)).length ≤ K * W
      rw [hiter]
      exact (hcost _).2
    · -- the certificate
      apply hfin
      rw [length_encPair, encBits_apply]
      have hl := length_encList_le (encPair eCfg (encList encUnary))
        ((List.range b).map fun i => (fun s => lookRun d look (P a, (s, b.bits)))^[i + 1]
          (init d, [])) (b := K * W) fun x hx => by
        obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
        rw [hiter]
        exact hcfg _
      rw [List.length_map, List.length_range] at hl
      exact cert_arith hz hl

/-- The square root of a linear bound, up to a constant. -/
private lemma sqrt_mul_add_le (c₁ c₂ t : ℕ) :
    Nat.sqrt (c₁ * t + c₂) + 1 ≤ (c₁ + c₂ + 1) * (Nat.sqrt t + 1) := by
  have ht := Nat.lt_succ_sqrt' t
  rw [Nat.succ_eq_add_one] at ht
  have h : Nat.sqrt (c₁ * t + c₂) < (c₁ + c₂ + 1) * (Nat.sqrt t + 1) := by
    rw [Nat.sqrt_lt']
    have h₁ : 1 ≤ (Nat.sqrt t + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos _)
    have h₂ : c₁ * t ≤ c₁ * (Nat.sqrt t + 1) ^ 2 := Nat.mul_le_mul_left _ ht.le
    have h₃ : c₂ * 1 ≤ c₂ * (Nat.sqrt t + 1) ^ 2 := Nat.mul_le_mul_left _ h₁
    have h₄ : (c₁ + c₂ + 1) * (Nat.sqrt t + 1) ^ 2 ≤
        (c₁ + c₂ + 1) * (c₁ + c₂ + 1) * (Nat.sqrt t + 1) ^ 2 :=
      Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
    have h₅ : ((c₁ + c₂ + 1) * (Nat.sqrt t + 1)) ^ 2 =
        (c₁ + c₂ + 1) * (c₁ + c₂ + 1) * (Nat.sqrt t + 1) ^ 2 := by ring
    rw [h₅]
    nlinarith
  omega

/-- The length of a linear bound, up to an additive constant. -/
private lemma size_mul_add_le (c₁ c₂ t : ℕ) : (c₁ * t + c₂).size ≤ t.size + c₁ + c₂ := by
  rw [Nat.size_le]
  have ht := Nat.lt_size_self t
  have h₁ : c₁ < 2 ^ c₁ := Nat.lt_two_pow_self
  have h₂ : c₂ < 2 ^ c₂ := Nat.lt_two_pow_self
  have h₃ : 1 ≤ 2 ^ t.size := Nat.one_le_two_pow
  have h₄ : c₁ * t ≤ 2 ^ c₁ * 2 ^ t.size := Nat.mul_le_mul h₁.le ht.le
  have h₅ : 2 ^ (t.size + c₁ + c₂) = 2 ^ c₁ * 2 ^ t.size * 2 ^ c₂ := by
    rw [pow_add, pow_add]; ring
  rw [h₅]
  have h₆ : 1 ≤ 2 ^ c₁ * 2 ^ t.size := Nat.one_le_iff_ne_zero.mpr (by positivity)
  nlinarith

/-- **The time–space speedup: `TISP(t, s) ⊆ Σ₂TIME(√t · (s + n log² n + log² t))`.** A problem
decidable within time `O(t)` and work space `O(s)` simultaneously is in `Σ₂TIME(τ)` for every
`τ` with `(√t + 1) · (s + (n + 1) (log n)² + (log t)²) = O(τ)`. The textbook bound is
`Σ₂TIME(√(t s))`; the factor `s` here, rather than `√s`, comes from copying a configuration of
`O(s)` bits at each of the `√t` steps of the checked block. -/
theorem TISP_subset_SigmaTwoTIME {t s τ : ℕ → ℕ}
    (hτ : ∃ C, ∀ n, (Nat.sqrt (t n) + 1) * (s n + (n + 1) * (n.size + 1) ^ 2 +
      ((t n).size + 1) ^ 2) ≤ C * τ n + C) :
    TISP enc t s ⊆ SigmaTwoTIME enc τ := by
  obtain ⟨C, hC⟩ := hτ
  intro A hA
  obtain ⟨c, ⟨k, State, hfin, M, hM⟩, -⟩ := mem_TISP_iff_computableInO.mp hA
  have hset : A = {a | indicator A a = true} := Set.ext (indicator_eq_iff.mp rfl)
  rw [hset]
  have hP : ComputableInO (fun a => (enc a).map eBit) enc (encList encUnary)
      (fun a => (enc a).length) (fun a => (enc a).length) :=
    computableInO_map_eBit.comp_linear (ComputableInO.of_eq (encMid := encBits) fun _ => rfl)
  have hPlen : ∀ a, (encList encUnary ((enc a).map eBit)).length ≤ 3 * (enc a).length :=
    fun a => by
      have := length_encList_le encUnary ((enc a).map eBit) (b := 1) fun x hx => by
        obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
        simp only [encUnary_apply, List.length_replicate]
        cases y <;> decide
      rw [List.length_map] at this
      omega
  refine mem_SigmaTwoTIME_of_virtualRun (ι := enc) (g := indicator A) (M := M)
    (T := fun a => c * (t (enc a).length + 1)) (S := fun a => c * (s (enc a).length + 1))
    (fun a => hM a) hP inputSymbol_stream_inO (fun a q _ => rfl)
    (L := fun a => 12 * ((enc a).length + 2) * ((enc a).length.size + 2) ^ 2)
    (fun a q hq => ?_) ?_
  · -- the cost of the input oracle
    have he := hPlen a
    have hm : (encNat q).length ≤ (enc a).length.size + 1 := by
      have := (length_encNat_mono hq).trans
        (ComputableTidilyInO.length_encNat_add_le (enc a).length 1)
      rwa [length_encNat_eq_size (enc a).length] at this
    simp only [length_encPair]
    generalize (encList encUnary ((enc a).map eBit)).length = e at he ⊢
    generalize (encNat q).length = m at hm ⊢
    generalize (enc a).length = n at he hm ⊢
    have hY : (m + 1) ^ 2 ≤ (n.size + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hY1 : m + 1 ≤ (m + 1) ^ 2 := Nat.le_self_pow two_ne_zero _
    have h1 : (e + 1) * (m + 1) ^ 2 ≤ (3 * n + 1) * (n.size + 2) ^ 2 :=
      Nat.mul_le_mul (by omega) hY
    have hY0 : 1 ≤ (n.size + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h2 : n * 1 ≤ n * (n.size + 2) ^ 2 := Nat.mul_le_mul_left _ hY0
    linarith
  · -- the bound
    refine ⟨(c + c + 1) * (c + c + 100 + (c + c + 1) ^ 2) * C, fun a => ?_⟩
    obtain ⟨p, hp, hpn⟩ : ∃ p, (encList encUnary ((enc a).map eBit)).length = p ∧
        p ≤ 3 * (enc a).length := ⟨_, rfl, hPlen a⟩
    simp only [hp]
    generalize (enc a).length = n at hpn ⊢
    have hsq := sqrt_mul_add_le c c (t n)
    have hsz := size_mul_add_le c c (t n)
    have hct : c * (t n + 1) = c * t n + c := by ring
    rw [hct]
    have hs1 : 1 ≤ (n.size + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have ht1 : 1 ≤ ((t n).size + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hQ1 : 1 ≤ s n + (n + 1) * (n.size + 1) ^ 2 + ((t n).size + 1) ^ 2 := by omega
    have hn : n + 1 ≤ (n + 1) * (n.size + 1) ^ 2 := Nat.le_mul_of_pos_right _ hs1
    have hsn : (n.size + 1) ^ 2 ≤ (n + 1) * (n.size + 1) ^ 2 :=
      Nat.le_mul_of_pos_left _ (Nat.succ_pos n)
    have h3 : 12 * (n + 2) * (n.size + 2) ^ 2 ≤ 96 * ((n + 1) * (n.size + 1) ^ 2) := by
      have h₁ : (n.size + 2) ^ 2 ≤ 4 * (n.size + 1) ^ 2 := by nlinarith
      have h₂ := Nat.mul_le_mul (show 12 * (n + 2) ≤ 24 * (n + 1) by omega) h₁
      linarith
    have h5 : ((c * t n + c).size + 1) ^ 2 ≤ (c + c + 1) ^ 2 * ((t n).size + 1) ^ 2 := by
      rw [← mul_pow]
      refine Nat.pow_le_pow_left ?_ 2
      have := Nat.mul_le_mul_left (c + c) (Nat.succ_pos (t n).size)
      nlinarith
    have hcQ := Nat.mul_le_mul_left c hQ1
    have h5' := Nat.mul_le_mul_left ((c + c + 1) ^ 2)
      (show ((t n).size + 1) ^ 2 ≤ s n + (n + 1) * (n.size + 1) ^ 2 + ((t n).size + 1) ^ 2 by
        omega)
    have hcs := Nat.mul_le_mul_left c
      (show s n ≤ s n + (n + 1) * (n.size + 1) ^ 2 + ((t n).size + 1) ^ 2 by omega)
    have hsum : c * (s n + 1) + p + 12 * (n + 2) * (n.size + 2) ^ 2 + (n.size + 1) ^ 2 +
        ((c * t n + c).size + 1) ^ 2 ≤ (c + c + 100 + (c + c + 1) ^ 2) *
          (s n + (n + 1) * (n.size + 1) ^ 2 + ((t n).size + 1) ^ 2) := by
      nlinarith
    calc (Nat.sqrt (c * t n + c) + 1) * (c * (s n + 1) + p + 12 * (n + 2) * (n.size + 2) ^ 2 +
          (n.size + 1) ^ 2 + ((c * t n + c).size + 1) ^ 2)
        ≤ ((c + c + 1) * (Nat.sqrt (t n) + 1)) * ((c + c + 100 + (c + c + 1) ^ 2) *
          (s n + (n + 1) * (n.size + 1) ^ 2 + ((t n).size + 1) ^ 2)) := Nat.mul_le_mul hsq hsum
      _ = (c + c + 1) * (c + c + 100 + (c + c + 1) ^ 2) * ((Nat.sqrt (t n) + 1) *
          (s n + (n + 1) * (n.size + 1) ^ 2 + ((t n).size + 1) ^ 2)) := by ring
      _ ≤ (c + c + 1) * (c + c + 100 + (c + c + 1) ^ 2) * (C * τ n + C) :=
        Nat.mul_le_mul_left _ (hC n)
      _ = _ := by ring

/-- The square of the length of a number is linear in the number. -/
private lemma size_succ_sq_le (n : ℕ) : (n.size + 1) ^ 2 ≤ 8 * (n + 1) := by
  have h₁ : ∀ k : ℕ, (k + 1) ^ 2 ≤ 4 * 2 ^ k := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      have := Nat.lt_two_pow_self (n := k)
      have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      rw [h2]
      nlinarith
  have h₂ : 2 ^ n.size ≤ 2 * (n + 1) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · obtain ⟨k, hk⟩ : ∃ k, n.size = k + 1 :=
        Nat.exists_eq_add_one.mpr (Nat.size_pos.mpr hn)
      have : 2 ^ k ≤ n := Nat.lt_size.mp (by omega)
      rw [hk, pow_succ]
      omega
  have := h₁ n.size
  omega

/-- The length of the twelfth power. -/
private lemma size_pow_twelve_le (n : ℕ) : ((n + 1) ^ 12).size + 1 ≤ 13 * (n.size + 1) := by
  have h₁ : (n + 1).size ≤ n.size + 1 := by
    rw [Nat.size_le, pow_succ]
    have := Nat.lt_size_self n
    omega
  have h₂ : ((n + 1) ^ 12).size ≤ 12 * (n + 1).size := by
    rw [Nat.size_le, pow_mul']
    exact Nat.pow_lt_pow_left (Nat.lt_size_self _) (by decide)
  omega

/-- **Arora–Barak's instance of the speedup: `TISP(n¹², n²) ⊆ Σ₂TIME(n⁸)`**, the inclusion used in
the proof of `NTIME(n) ⊄ TISP(n^{1.2}, n^{0.2})` ([AroraBarak09], §5.4). -/
theorem TISP_pow_twelve_subset_SigmaTwoTIME :
    TISP enc (fun n => (n + 1) ^ 12) (fun n => (n + 1) ^ 2) ⊆
      SigmaTwoTIME enc (fun n => (n + 1) ^ 8) := by
  refine TISP_subset_SigmaTwoTIME ⟨2722, fun n => ?_⟩
  have hsqrt : Nat.sqrt ((n + 1) ^ 12) = (n + 1) ^ 6 := by
    rw [show (n + 1) ^ 12 = ((n + 1) ^ 6) ^ 2 by ring]
    exact Nat.sqrt_eq' _
  rw [hsqrt]
  have h₁ := size_succ_sq_le n
  have h₂ : (((n + 1) ^ 12).size + 1) ^ 2 ≤ 169 * (n.size + 1) ^ 2 := by
    have := Nat.pow_le_pow_left (size_pow_twelve_le n) 2
    have h : (13 * (n.size + 1)) ^ 2 = 169 * (n.size + 1) ^ 2 := by ring
    exact this.trans_eq h
  have h₃ : (n + 1) * (n.size + 1) ^ 2 ≤ (n + 1) * (8 * (n + 1)) := Nat.mul_le_mul_left _ h₁
  have h₃' : (n + 1) * (8 * (n + 1)) = 8 * (n + 1) ^ 2 := by ring
  have h₄ : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow two_ne_zero _
  have h₅ : (n + 1) ^ 2 + (n + 1) * (n.size + 1) ^ 2 + (((n + 1) ^ 12).size + 1) ^ 2 ≤
      1361 * (n + 1) ^ 2 := by linarith
  have h₆ : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (Nat.succ_pos n)
  have h₇ : (n + 1) ^ 6 + 1 ≤ 2 * (n + 1) ^ 6 := by linarith
  have h₈ := Nat.mul_le_mul h₇ h₅
  have h₉ : 2 * (n + 1) ^ 6 * (1361 * (n + 1) ^ 2) = 2722 * (n + 1) ^ 8 := by ring
  rw [h₉] at h₈
  exact h₈.trans (Nat.le_add_right _ _)

end Cslib.Complexity
