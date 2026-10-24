/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.MassProduction.Schedule
public import Complexity.Computability.Circuit.Boolean.MassProduction.FineStatement
public import Complexity.Computability.Circuit.Replication
public import Cslib.Computability.Circuit.Boolean.Complexity
import Complexity.Computability.Circuit.Boolean.MassProduction.Pipeline
import Complexity.Computability.Circuit.Boolean.MassProduction.Scheduler
import Complexity.Computability.Circuit.Boolean.MassProduction.FineParameters
import Complexity.Computability.Circuit.Boolean.MassProduction.Uhlig
import Complexity.Foundations.Combinatorics.LineCode.HighRate
import Complexity.Foundations.Combinatorics.LineCode.HighRate.Packing
import Complexity.Foundations.Combinatorics.LineCode.Menu
import Complexity.Foundations.Data.BitString.Basic
import Complexity.Foundations.FieldTheory.Finite.Subfield
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Fine mass production

The construction for `2 ^ D` copies of a function on `p + w` inputs:

1. Store, for every suffix, the `2 ^ p` values of the prefixes in `copies` codewords of a
   high-rate line-parity code on `K ^ ℓ`, with `K` a field of `2 ^ b` elements
   (`LineCode.HighRate.exists_lineCode`). Every bit of every code coordinate is a resource
   function of the suffix; there are `copies * card K ^ ℓ * b` of them.
2. A scheduler circuit gives every request a punctured line through its information point, with
   the lines of distinct requests disjoint (`IsScheduler`). It exists, with near-linear size,
   whenever universal menus exist (`SchedulerSizeBound`), and they do under the direction budget
   (`LineCode.exists_isUniversalMenu`).
3. A pipeline looks up the information points, routes every suffix to the resources on its
   line, evaluates each resource once and sums the returned bits (`PipelineSizeBound`).

With the parameters of `MassProduction.Fine`, the resource bank costs
`(1 + o(1)) / (1 - γ) · 2 ^ n / n` and every other circuit is exponentially smaller.

`SchedulerSizeBound` and `PipelineSizeBound` are the two circuit-size contracts; this module
derives the core fine theorem from them (`fineMassProducesThrough_of_bounds`) and discharges
both (`schedulerSizeBound`, `pipelineSizeBound`). Sizes count every gate. These
are bounds on circuit size, not on the running time of any circuit constructor.

## Main definitions

* `Cslib.Circuits.Boolean.MassProduction.SchedulerSizeBound`: near-linear schedulers exist.
* `Cslib.Circuits.Boolean.MassProduction.PipelineSizeBound`: the finite composition bound.

## Main results

* `Cslib.Circuits.Boolean.MassProduction.exists_complexity_le_of_bounds`: the finite bound at
  one input length.
* `Cslib.Circuits.Boolean.MassProduction.fineMassProducesThrough_of_bounds`: the core fine
  theorem from the two contracts.
* `Cslib.Circuits.Boolean.MassProduction.schedulerSizeBound`,
  `Cslib.Circuits.Boolean.MassProduction.pipelineSizeBound`: both contracts hold.
* `Cslib.Circuits.Boolean.MassProduction.fineMassProducesThrough`,
  `Cslib.Circuits.Boolean.MassProduction.fineMassProducesAt`: the fine coefficient
  `1 / (1 - γ) + o(1)` at every rational exponent below one.
* `Cslib.Circuits.Boolean.MassProduction.exponentialMassProduction`: the exponential copy range.
* `Cslib.Circuits.Boolean.MassProduction.realFineMassProduction`: real rates.

## References

* Simplifies MassProduction/Nonuniform/{FiniteBound,LupanovRuntime,EventualParameters,
  OverheadPolynomial,LeadingCost,CodeQuantitative,SharpTheorem}.lean in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.MassProduction

open Filter BitString LineCode

/-- Schedulers of size at most `A * 2 ^ D * (s + 1) * (D + ℓ * b + 2) ^ E` exist for `2 ^ D`
requests whenever universal menus exist for every number of pending requests. -/
def SchedulerSizeBound (A E : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (ℓ b s D : ℕ) (bits : K ≃+ BitString b)
    (scalar : Fin s ≃ {c : K // c ≠ 0}),
    (∀ k, 0 < k → k ≤ 2 ^ D → ∃ r, k * r ≤ 2 ^ D * (2 + 3 * (ℓ * b)) + 2 * k ∧
      ∃ menu : Fin r → Fin k → Fin ℓ → K, IsUniversalMenu (2 ^ D) menu) →
    ∃ c : Circuit Boolean.signature (2 ^ D * (ℓ * b)) (2 ^ D * (s * (ℓ * b))),
      IsScheduler bits scalar c ∧ c.size ≤ A * 2 ^ D * (s + 1) * (D + ℓ * b + 2) ^ E

/-- The finite composition bound: `t` copies of a function on `p + w` inputs cost a scheduler,
the resource bank and an overhead of at most
`A * (2 ^ p + t * (s + 1) + copies * (s + 1) ^ ℓ) * (p + w + ℓ * b + log₂ (t + copies) + 2) ^ E`
gates. -/
def PipelineSizeBound (A E : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (ℓ b s t p w copies L : ℕ)
    (bits : K ≃+ BitString b) (scalar : Fin s ≃ {c : K // c ≠ 0}) (C : LineCode K ℓ)
    (_ : BitString p ↪ Fin copies × C.info × Fin b)
    (sched : Circuit Boolean.signature (t * (ℓ * b)) (t * (s * (ℓ * b)))),
    IsScheduler bits scalar sched →
    (∀ g : BooleanFunction w, complexity Boolean.interpretation (single g) ≤ L) →
    ∀ f : BooleanFunction (p + w),
      complexity Boolean.interpretation (directProduct f t) ≤
        sched.size + copies * Fintype.card K ^ ℓ * b * L +
          A * (2 ^ p + t * (s + 1) + copies * (s + 1) ^ ℓ) *
            (p + w + ℓ * b + Nat.log 2 (t + copies) + 2) ^ E

private theorem pow_le_pow_add {B E E' : ℕ} {x : ℕ} (hx : x ≤ B) (hB : 1 ≤ B) :
    x ^ E ≤ B ^ (E + E') :=
  (Nat.pow_le_pow_left hx E).trans (Nat.pow_le_pow_right hB (Nat.le_add_right E E'))

/-- **The finite fine bound** at one input length. With a field of `2 ^ (h * m)` elements,
`ℓ ≤ 2 ^ h`, enough blocks for the rate precision `X`, the direction budget, a negligible last
code copy and single copies of size at most `L` on `w` inputs, the `2 ^ D` copies of every
function on `p + w` inputs cost a resource bank `R * L` with `X R ≤ (X + 2) 2 ^ p`, plus an
overhead `O` exponentially smaller than `2 ^ (p + w)`. -/
theorem exists_complexity_le_of_bounds {A₁ E₁ A₂ E₂ : ℕ} (hS : SchedulerSizeBound A₁ E₁)
    (hP : PipelineSizeBound A₂ E₂) {X p w ℓ h m D L : ℕ} (hX : 0 < X) (hh : 0 < h) (hm : 0 < m)
    (hℓh : ℓ ≤ 2 ^ h) (hrate : X * (2 ^ (h * ℓ) - 1) ≤ m)
    (hbudget : 9 + D ≤ (ℓ - 2) * (h * m))
    (hloss : X * (h * m) * 2 ^ (ℓ * (h * m)) ≤ 2 ^ p)
    (hL : ∀ g : BooleanFunction w, complexity Boolean.interpretation (single g) ≤ L)
    (f : BooleanFunction (p + w)) :
    ∃ R O : ℕ, complexity Boolean.interpretation (directProduct f (2 ^ D)) ≤ R * L + O ∧
      X * R ≤ (X + 2) * 2 ^ p ∧
      O ≤ (A₁ + 4 * A₂) * (2 ^ p + 2 ^ (D + h * m)) *
        (2 * (p + w) + ℓ * (h * m) + D + 4) ^ (E₁ + E₂) := by
  set b := h * m with hbdef
  have hb : b ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  have hℓ2 : 2 ≤ ℓ := by
    by_contra hlt
    rw [show ℓ - 2 = 0 by omega, Nat.zero_mul] at hbudget
    omega
  obtain ⟨K, _, _, _, hcard⟩ := exists_field_card_eq_two_pow hb
  classical
  obtain ⟨bits⟩ := nonempty_addEquiv_bitString hcard
  have hs : Fintype.card {c : K // c ≠ 0} = 2 ^ b - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, hcard]
  let scalar : Fin (2 ^ b - 1) ≃ {c : K // c ≠ 0} := (Fintype.equivFinOfCardEq hs).symm
  have hs1 : 2 ^ b - 1 + 1 = 2 ^ b := Nat.sub_add_cancel Nat.one_le_two_pow
  -- The code and its rate.
  obtain ⟨C, hC⟩ := HighRate.exists_lineCode (K := K) h m hℓh hcard
  obtain ⟨N, hNdef⟩ : ∃ N, N = Fintype.card K ^ ℓ := ⟨_, rfl⟩
  have hN : N = (2 ^ (h * ℓ)) ^ m := by
    rw [hNdef, hcard, ← pow_mul, ← pow_mul, hbdef]; ring_nf
  have hNb : N = 2 ^ (ℓ * b) := by rw [hNdef, hcard, ← pow_mul, mul_comm]
  have hrate' : X * N ≤ (X + 1) * C.info.card := by
    rw [hC, hN]
    exact HighRate.retainedDimension_rate _ m X hm hrate
  have hNpos : 0 < N := by rw [hNb]; positivity
  have hKpos : 0 < C.info.card := by
    by_contra h0
    have : C.info.card = 0 := by omega
    rw [this, Nat.mul_zero] at hrate'
    exact absurd hrate' (by have := Nat.mul_pos hX hNpos; omega)
  set copies := HighRate.packingCopies (2 ^ p) C.info.card b with hcopies
  obtain ⟨emb⟩ := HighRate.nonempty_embedding_packingCopies (I := C.info) (2 ^ p) b
    (by rwa [Fintype.card_coe]) (by omega)
  rw [Fintype.card_coe] at emb
  let place : BitString p ↪ Fin copies × C.info × Fin b :=
    (BitString.equivFin p).toEmbedding.trans emb
  -- Menus and the scheduler.
  have hbudget' : 512 * 2 ^ D * Fintype.card K ≤ Fintype.card K ^ (ℓ - 1) := by
    rw [hcard, ← pow_mul, show 512 = 2 ^ 9 by rfl, ← pow_add, ← pow_add]
    apply Nat.pow_le_pow_right (by norm_num)
    have : b * (ℓ - 1) = (ℓ - 2) * b + b := by
      rw [show ℓ - 1 = ℓ - 2 + 1 by omega]; ring
    omega
  have hmenu : ∀ k, 0 < k → k ≤ 2 ^ D → ∃ r, k * r ≤ 2 ^ D * (2 + 3 * (ℓ * b)) + 2 * k ∧
      ∃ menu : Fin r → Fin k → Fin ℓ → K, IsUniversalMenu (2 ^ D) menu := by
    intro k hk hkt
    refine ⟨menuLength (2 ^ D) k (ℓ * b), ?_, exists_isUniversalMenu hcard hbudget' hk hkt⟩
    have := mul_menuLength_le (2 ^ D) k (ℓ * b)
    nlinarith
  obtain ⟨sched, hsched, hsize⟩ := hS K ℓ b (2 ^ b - 1) D bits scalar hmenu
  have hpipe := hP K ℓ b (2 ^ b - 1) (2 ^ D) p w copies L bits scalar C place sched hsched hL f
  rw [← hNdef, hs1] at hpipe
  have hpow : (2 ^ b) ^ ℓ = N := by rw [hNdef, hcard]
  rw [hpow] at hpipe
  have hlossN : X * (N * b) ≤ 2 ^ p := by
    rw [hNb]
    calc X * (2 ^ (ℓ * b) * b) = X * b * 2 ^ (ℓ * b) := by ring
      _ ≤ 2 ^ p := hloss
  refine ⟨copies * N * b, sched.size + A₂ * (2 ^ p + 2 ^ D * 2 ^ b + copies * N) *
      (p + w + ℓ * b + Nat.log 2 (2 ^ D + copies) + 2) ^ E₂,
    hpipe.trans (le_of_eq (by ring)), ?_, ?_⟩
  -- The resource bank.
  · have hstore := HighRate.mul_packingCopies_mul_le (2 ^ p) C.info.card N b X hrate'
    linarith
  -- The overhead.
  · have hcN : copies * N ≤ 3 * 2 ^ p := by
      have hN2 : N ≤ 2 * C.info.card := by nlinarith
      have hNp : N ≤ 2 ^ p := by
        have : N ≤ X * (N * b) := by
          calc N = 1 * (N * 1) := by ring
            _ ≤ X * (N * b) := by gcongr <;> omega
        omega
      have hq := Nat.div_mul_le_self (2 ^ p) (C.info.card * b)
      rw [hcopies, HighRate.packingCopies]
      have hmul : 2 ^ p / (C.info.card * b) * (2 * C.info.card) ≤
          2 * (2 ^ p / (C.info.card * b) * (C.info.card * b)) := by
        have : C.info.card ≤ C.info.card * b := Nat.le_mul_of_pos_right _ (by omega)
        calc 2 ^ p / (C.info.card * b) * (2 * C.info.card)
            = 2 * (2 ^ p / (C.info.card * b) * C.info.card) := by ring
          _ ≤ 2 * (2 ^ p / (C.info.card * b) * (C.info.card * b)) := by gcongr
      calc (2 ^ p / (C.info.card * b) + 1) * N
          = 2 ^ p / (C.info.card * b) * N + N := by ring
        _ ≤ 2 ^ p / (C.info.card * b) * (2 * C.info.card) + N := by gcongr
        _ ≤ 3 * 2 ^ p := by omega
    have hcopies_le : copies ≤ 2 ^ p + 1 := by
      rw [hcopies, HighRate.packingCopies]
      have := Nat.div_le_self (2 ^ p) (C.info.card * b)
      omega
    set B := 2 * (p + w) + ℓ * b + D + 4 with hB
    have hB1 : 1 ≤ B := by omega
    have hlog : Nat.log 2 (2 ^ D + copies) ≤ D + p + 1 := by
      have : 2 ^ D + copies < 2 ^ (D + p + 2) := by
        have h1 : 2 ^ D ≤ 2 ^ (D + p) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h2 : 2 ^ p ≤ 2 ^ (D + p) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h3 : 2 ^ (D + p + 2) = 4 * 2 ^ (D + p) := by rw [pow_add]; ring
        have h4 : 1 ≤ 2 ^ (D + p) := Nat.one_le_two_pow
        omega
      have := Nat.log_lt_of_lt_pow (by positivity) this
      omega
    have hDb : 2 ^ D * 2 ^ b = 2 ^ (D + b) := (pow_add 2 D b).symm
    have hsched_le : sched.size ≤ A₁ * (2 ^ p + 2 ^ (D + b)) * B ^ (E₁ + E₂) := by
      calc sched.size ≤ A₁ * 2 ^ D * (2 ^ b - 1 + 1) * (D + ℓ * b + 2) ^ E₁ := hsize
        _ = A₁ * 2 ^ (D + b) * (D + ℓ * b + 2) ^ E₁ := by rw [hs1, ← hDb]; ring
        _ ≤ A₁ * (2 ^ p + 2 ^ (D + b)) * B ^ (E₁ + E₂) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.le_add_left _ _))
            (pow_le_pow_add (by omega) hB1)
    have hpipe_le : A₂ * (2 ^ p + 2 ^ D * 2 ^ b + copies * N) *
        (p + w + ℓ * b + Nat.log 2 (2 ^ D + copies) + 2) ^ E₂ ≤
        4 * A₂ * (2 ^ p + 2 ^ (D + b)) * B ^ (E₁ + E₂) := by
      have hmid : 2 ^ p + 2 ^ D * 2 ^ b + copies * N ≤ 4 * (2 ^ p + 2 ^ (D + b)) := by
        rw [hDb]; omega
      calc A₂ * (2 ^ p + 2 ^ D * 2 ^ b + copies * N) *
            (p + w + ℓ * b + Nat.log 2 (2 ^ D + copies) + 2) ^ E₂
          ≤ A₂ * (4 * (2 ^ p + 2 ^ (D + b))) * B ^ (E₁ + E₂) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ hmid)
              ((pow_le_pow_add (E' := E₁) (by omega) hB1).trans_eq (by rw [add_comm]))
        _ = 4 * A₂ * (2 ^ p + 2 ^ (D + b)) * B ^ (E₁ + E₂) := by ring
    calc sched.size + A₂ * (2 ^ p + 2 ^ D * 2 ^ b + copies * N) *
          (p + w + ℓ * b + Nat.log 2 (2 ^ D + copies) + 2) ^ E₂
        ≤ A₁ * (2 ^ p + 2 ^ (D + b)) * B ^ (E₁ + E₂) +
          4 * A₂ * (2 ^ p + 2 ^ (D + b)) * B ^ (E₁ + E₂) := Nat.add_le_add hsched_le hpipe_le
      _ = (A₁ + 4 * A₂) * (2 ^ p + 2 ^ (D + b)) * B ^ (E₁ + E₂) := by ring

/-- The pipeline of `MassProduction.Pipeline` satisfies the composition contract. -/
theorem pipelineSizeBound : PipelineSizeBound 1444 4 := by
  intro K _ _ _ ℓ b s t p w copies L bits scalar C place sched hsched hL f
  rw [Pipeline.succ_eq_card scalar]
  exact complexity_directProduct_le_explicit_of_isScheduler bits scalar C place sched hsched hL f

/-- **Fine mass production from the circuit contracts.** If schedulers and the pipeline obey
polynomial size bounds, then at every rational exponent `num / den < 1` and positive precision `P`,
eventually every function on `n` inputs has `k ≤ 2 ^ (⌊num n / den⌋ + 1)` copies of cost at most
`(1 + 1 / P) den / (den - num) · 2 ^ n / n`. -/
theorem fineMassProducesThrough_of_bounds {A₁ E₁ A₂ E₂ : ℕ} (hS : SchedulerSizeBound A₁ E₁)
    (hP : PipelineSizeBound A₂ E₂) {num den : ℕ} (hnd : num < den) :
    FineMassProducesThrough num den := by
  intro P
  set X := 16 * (P + 1) with hXdef
  have hX : 0 < X := by omega
  have hden : 0 < den := by omega
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp (eventually_mul_complexity_single_le X)
  set ℓ := Fine.dimension num den X with hℓ
  set h := Fine.blockWidth num den X with hh
  filter_upwards [Fine.eventually_add_depth_le (X := X) hnd 9,
    Fine.eventually_le_blocks (num := num) (X := X) hden (X * (2 ^ (h * ℓ) - 1) + 1),
    Fine.eventually_le_suffixWidth (X := X) hnd hX (m₀ + 1),
    Fine.eventually_mul_two_pow_dimension_le (X := X) hnd.le X,
    Fine.eventually_overhead_le (X := X) hnd hX P ((A₁ + 4 * A₂) * 5 ^ (E₁ + E₂)) (E₁ + E₂)]
    with n hbud hblocks hsuf hloss hover
  intro f k hk
  set p := Fine.prefixWidth num den X n with hp
  set w := Fine.suffixWidth num den X n with hw
  set m := Fine.blocks num den X n with hm
  set D := Fine.depth num den n with hD
  have hsplit : n = p + w := (Fine.prefixWidth_add_suffixWidth hnd.le n).symm
  -- Single copies on the suffix.
  set L := (X + 1) * 2 ^ w / (X * w) with hLdef
  have hXw : 0 < X * w := Nat.mul_pos hX (by omega)
  have hL : ∀ g : BooleanFunction w, complexity Boolean.interpretation (single g) ≤ L := fun g =>
    (Nat.le_div_iff_mul_le hXw).mpr (by
      have := hm₀ w (by omega) g
      calc complexity Boolean.interpretation (single g) * (X * w) =
            X * w * complexity Boolean.interpretation (single g) := by ring
        _ ≤ (X + 1) * 2 ^ w := this)
  have hLspec : X * w * L ≤ (X + 1) * 2 ^ w := by
    rw [mul_comm]; exact Nat.div_mul_le_self _ _
  -- Transport `f` to the split input.
  let f' : BooleanFunction (p + w) := fun y => f (y ∘ Fin.cast hsplit)
  have hff' : (fun x : Fin n → Bool => f' (x ∘ Fin.cast hsplit.symm)) = f := by
    funext x
    simp only [f']
    congr 1
  obtain ⟨R, O, hcomp, hR, hO⟩ := exists_complexity_le_of_bounds (D := D) (h := h) (ℓ := ℓ)
    (m := m) (p := p) (w := w) hS hP hX Fine.blockWidth_pos (by omega)
    Fine.dimension_le_two_pow_blockWidth (by omega) hbud hloss hL f'
  have hcost : massComplexity f k ≤ (R * L + O : ℕ) := by
    calc massComplexity f k = massComplexity (fun x : Fin n → Bool =>
          f' (x ∘ Fin.cast hsplit.symm)) k := by rw [hff']
      _ ≤ massComplexity f' k := massComplexity_comp_wiring_le _ k
      _ ≤ complexity Boolean.interpretation (directProduct f' k) := massComplexity_le_complexity
      _ ≤ complexity Boolean.interpretation (directProduct f' (2 ^ D)) := by
          exact_mod_cast complexity_directProduct_mono hk
      _ ≤ (R * L + O : ℕ) := by exact_mod_cast hcomp
  -- The overhead is negligible.
  have hbase : 2 * (p + w) + ℓ * (h * m) + D + 4 ≤ 5 * (n + 1) := by
    have h1 := Fine.dimension_mul_fieldWidth_le (num := num) (den := den) (X := X) n
    have h2 := Fine.prefixWidth_le (X := X) hnd.le n
    have h3 : D ≤ n + 1 := by
      rw [hD, Fine.depth]
      have : num * n / den ≤ n := Nat.div_le_of_le_mul (by nlinarith)
      omega
    have h4 : ℓ * (h * m) ≤ n := by
      rcases h1 with h1 | h1
      · rw [← hℓ, ← hp] at h1; unfold Fine.fieldWidth at h1; rw [← hh, ← hm] at h1; omega
      · unfold Fine.fieldWidth at h1; rw [← hh, ← hm] at h1; rw [h1, Nat.mul_zero]; omega
    omega
  have hO' : 2 * P * (den - num) * n * O ≤ den * 2 ^ n := by
    refine le_trans ?_ hover
    apply Nat.mul_le_mul_left
    calc O ≤ (A₁ + 4 * A₂) * (2 ^ p + 2 ^ (D + h * m)) *
          (2 * (p + w) + ℓ * (h * m) + D + 4) ^ (E₁ + E₂) := hO
      _ ≤ (A₁ + 4 * A₂) * (2 ^ p + 2 ^ (D + h * m)) * (5 * (n + 1)) ^ (E₁ + E₂) := by
          gcongr
      _ = (A₁ + 4 * A₂) * 5 ^ (E₁ + E₂) * (2 ^ p + 2 ^ (D + h * m)) * (n + 1) ^ (E₁ + E₂) := by
          rw [mul_pow]; ring
  -- The leading coefficient.
  have hfinal := Fine.mul_add_le_of_slack (P := P)
    (Fine.mul_le_suffixWidth (X := X) hnd.le n) hsplit hR hLspec hO'
  calc ((P * (den - num) * n : ℕ) : ℕ∞) * massComplexity f k
      ≤ ((P * (den - num) * n : ℕ) : ℕ∞) * (R * L + O : ℕ) := by gcongr
    _ = ((P * (den - num) * n * (R * L + O) : ℕ) : ℕ∞) := by push_cast; ring
    _ ≤ ((P + 1) * den * 2 ^ n : ℕ) := by exact_mod_cast hfinal

/-- The halving scheduler of `MassProduction.Scheduler` satisfies the scheduler contract. -/
theorem schedulerSizeBound : SchedulerSizeBound 524288 5 :=
  fun _ _ _ _ _ _ _ _ bits scalar hmenu => exists_isScheduler bits scalar hmenu

/-- **Fine mass production** at every rational exponent `num / den < 1`: for every precision
`P`, eventually every function on `n` inputs has `k ≤ 2 ^ (⌊num n / den⌋ + 1)` copies of cost
`c` with `P (den - num) n c ≤ (P + 1) den 2 ^ n`, that is, at most
`(1 + 1 / P) / (1 - num / den) · 2 ^ n / n` when `P > 0`. -/
theorem fineMassProducesThrough {num den : ℕ} (hnd : num < den) :
    FineMassProducesThrough num den :=
  fineMassProducesThrough_of_bounds schedulerSizeBound pipelineSizeBound hnd

/-- The source's statement at every rational exponent below one. -/
theorem fineMassProducesAt {num den : ℕ} (hnd : num < den) : FineMassProducesAt num den :=
  (fineMassProducesThrough hnd).fineMassProducesAt

/-- **Exponential-range mass production**: every fixed rational exponent below one has a
constant coefficient at every positive input length. -/
theorem exponentialMassProduction : ExponentialMassProduction :=
  exponentialMassProduction_of_fine fun _ _ hnd => fineMassProducesThrough hnd

/-- **Fine mass production for real rates**: for every real `0 ≤ γ < 1` and every `ε > 0`,
eventually every positive number of copies at most `2 ^ (γ n)` costs at most
`(1 / (1 - γ) + ε) 2 ^ n / n`. -/
theorem realFineMassProduction : RealFineMassProduction :=
  realFineMassProduction_of_fine fun _ _ hnd => fineMassProducesThrough hnd

end Cslib.Circuits.Boolean.MassProduction
