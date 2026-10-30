/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.CountingSimulation.Accumulate
public import Complexity.Computability.Complexity.Classes.CountingSimulation.Interfaces
public import Complexity.Computability.Complexity.Classes.Constructible
public import Complexity.Foundations.Data.Nat.SqrtLog
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LinearSpaceArith

/-!
# The deterministic counting simulation, assembled from its interfaces

This module assembles the deterministic simulation of #1833 from the two interfaces of
`Cslib.Complexity.CountingSimulation.NetworkFamily` and
`Cslib.Complexity.CountingSimulation.ContractionAlgorithm`. **It is conditional**: every result
here assumes a network family and a contraction algorithm, which are proved separately.

On an input `x` with clock `t`, the simulation (`Cslib.Complexity.CountingSimulation.simulate`)
visits the `scheduleCount heads t` movement schedules one at a time, contracts the network of each
modulo `2 ^ (paddedTime t + 1)`, and adds the residues modulo the same power of two
(`Cslib.Complexity.CountingSimulation.modSum`). Since the count is at most `2 ^ (paddedTime t)`,
the residue of the sum is the count itself (`Cslib.Complexity.CountingSimulation.simulate_eq`).

Its cost is the number of schedules times the cost of one network, and its workspace that of one
network and an accumulator (`Cslib.Complexity.CountingSimulation.exists_computableInO_simulate`).
With the clock `t = c * T n` of a time-constructible `T n ≥ max n 2`, the schedules number
`3 ^ O(T / log T)`, so the total time is `2 ^ O(T / √(log T))` in the natural-number scale of
`Nat.exists_three_pow_mul_le_two_pow_div_sqrt_log_two`, and the space is polynomial in `T`
(`Cslib.Complexity.CountingSimulation.exists_computableInO_count`). The result may be any
polynomial-time function of the padded time, in unary, and the count, such as a comparison
deciding acceptance.

## Main definitions

* `Cslib.Complexity.CountingSimulation.scheduleResidue`: the contraction of the network of one
  schedule, modulo `2 ^ (paddedTime t + 1)`.
* `Cslib.Complexity.CountingSimulation.simulate`: the streamed sum of these residues.

## Main results

* `Cslib.Complexity.CountingSimulation.simulate_eq`: the simulation computes the count.
* `Cslib.Complexity.CountingSimulation.exists_computableInO_simulate`: its time and space bounds in
  terms of the clock.
* `Cslib.Complexity.CountingSimulation.exists_computableInO_count`: from a time-constructible bound,
  the count at the padded clock, or any polynomial-time function of it and the padded time, within
  time `2 ^ (C * T n / √⌊log₂ (T n)⌋)` and space `T n ^ d`.
-/

public section

namespace Cslib.Complexity.CountingSimulation

open Turing.MultiTapeTM Cslib.GenericRAM

variable {N : Type} {encN : N ↪ List Bool} {value : N → ℕ} {Admissible : ℕ → ℕ → N → Prop}
  {count : List Bool → ℕ → ℕ}

/-! ### The algorithm and its correctness -/

/-- The value of the network of the schedule `p.2` for the input `p.1.1` and the clock `p.1.2`,
modulo `2 ^ (paddedTime p.1.2 + 1)`. -/
def scheduleResidue (F : NetworkFamily encN value Admissible count) (p : (List Bool × ℕ) × ℕ) :
    ℕ :=
  value (F.net (p.1.1, p.1.2, p.2)) % 2 ^ (paddedTime p.1.2 + 1)

/-- **The simulation** on the input `p.1` with the clock `p.2`: when `|p.1| ≤ p.2` and `2 ≤ p.2`,
the residues of the networks of all schedules, summed one at a time modulo
`2 ^ (paddedTime p.2 + 1)`; otherwise `0`. -/
def simulate (F : NetworkFamily encN value Admissible count) (p : List Bool × ℕ) : ℕ :=
  if p.1.length ≤ p.2 ∧ 2 ≤ p.2 then
    modSum (scheduleResidue F) (fun p => 2 ^ (paddedTime p.2 + 1))
      (fun p => scheduleCount F.heads p.2) p
  else 0

/-- **The simulation computes the count**: when `|x| ≤ t` and `2 ≤ t`, and the count at the padded
time is at most `2 ^ paddedTime t`, the residue of the sum of the network values modulo
`2 ^ (paddedTime t + 1)` is the count itself. -/
theorem simulate_eq (F : NetworkFamily encN value Admissible count) {x : List Bool} {t : ℕ}
    (hx : x.length ≤ t) (ht : 2 ≤ t) (hcount : count x (paddedTime t) ≤ 2 ^ paddedTime t) :
    simulate F (x, t) = count x (paddedTime t) := by
  rw [simulate, ite_eq_left_of_eq_true _ _ (eq_true (⟨hx, ht⟩ : x.length ≤ t ∧ 2 ≤ t)),
    modSum_eq_sum_mod]
  simp only [scheduleResidue]
  rw [← Finset.sum_nat_mod, F.sum_value x t hx ht]
  exact Nat.mod_eq_of_lt (hcount.trans_lt (Nat.pow_lt_pow_right one_lt_two (Nat.lt_succ_self _)))

/-! ### Polynomial-time parameters -/

private theorem paddedTime_eq (t : ℕ) :
    paddedTime t = (t + Nat.clog 2 (t + 2) - 1) / Nat.clog 2 (t + 2) * Nat.clog 2 (t + 2) := by
  rw [paddedTime, numBlocks, blockLength, Nat.ceilDiv_eq_add_pred_div]

private theorem computableInPolyTime_paddedTime_succ :
    ComputableInPolyTime (fun t => paddedTime t + 1) encUnary encNat := by
  simp only [paddedTime_eq]
  fun_prop

private theorem computableInPolyTime_paddedTime :
    ComputableInPolyTime paddedTime encUnary encUnary := by
  rw [show paddedTime = _ from funext paddedTime_eq]
  fun_prop

private theorem computableInPolyTime_two_pow_paddedTime :
    ComputableInPolyTime (fun t => 2 ^ (paddedTime t + 1)) encUnary encNat := by
  simp only [paddedTime_eq]
  fun_prop

private theorem computableInPolyTime_scheduleCount (heads : ℕ) :
    ComputableInPolyTime (scheduleCount heads) encUnary encNat := by
  have h : ComputableInPolyTime
      (fun t => 3 ^ (heads * ((t + Nat.clog 2 (t + 2) - 1) / Nat.clog 2 (t + 2)))) encUnary
      encNat :=
    ComputableInPolyTime.binary_pow' (ComputableInPolyTime.const (encOut := encNat) 3) (by fun_prop)
  convert h using 2 with t
  rw [scheduleCount, numBlocks, blockLength, Nat.ceilDiv_eq_add_pred_div]

/-! ### Resource bounds -/

/-- **Time and space of the simulation** (conditional on the interfaces). For a constant `k`, the
simulation on an input `x` with clock `t` runs within time
`k * (|x| + t + 1) ^ k * scheduleCount heads t * 2 ^ (k * t / √⌊log₂ t⌋)` and space
`k * (|x| + t + 1) ^ k`: it contracts one network per schedule, keeping one network, its
contraction workspace and an accumulator. -/
theorem exists_computableInO_simulate (F : NetworkFamily encN value Admissible count)
    (A : ContractionAlgorithm encN value Admissible) :
    ∃ k : ℕ, ComputableInO (simulate F) (encPair encBits encUnary) encNat
      (fun p => k * (p.1.length + p.2 + 1) ^ k * scheduleCount F.heads p.2 *
        2 ^ (k * p.2 / Nat.sqrt (Nat.log 2 p.2)))
      (fun p => k * (p.1.length + p.2 + 1) ^ k) := by
  classical
  -- The polynomial-time pieces.
  have hP : ComputableInPolyTime (fun p : (List Bool × ℕ) × ℕ => paddedTime p.1.2 + 1)
      (encPair (encPair encBits encUnary) encNat) encNat :=
    computableInPolyTime_paddedTime_succ.comp (by fun_prop)
  have hPc : ComputableInPolyTime (fun p : List Bool × ℕ => paddedTime p.2 + 1)
      (encPair encBits encUnary) encNat :=
    computableInPolyTime_paddedTime_succ.comp (by fun_prop)
  have hnet : ComputableInPolyTime (fun p : (List Bool × ℕ) × ℕ => F.net (p.1.1, p.1.2, p.2))
      (encPair (encPair encBits encUnary) encNat) encN :=
    F.polyTime.comp (by fun_prop)
  have hmod : ComputableInPolyTime (fun p : List Bool × ℕ => 2 ^ (paddedTime p.2 + 1))
      (encPair encBits encUnary) encNat :=
    computableInPolyTime_two_pow_paddedTime.comp (by fun_prop)
  have hcnt : ComputableInPolyTime (fun p : List Bool × ℕ => scheduleCount F.heads p.2)
      (encPair encBits encUnary) encNat :=
    (computableInPolyTime_scheduleCount F.heads).comp (by fun_prop)
  have hguard : ComputableInPolyTime
      (fun p : List Bool × ℕ => decide (p.1.length ≤ p.2 ∧ 2 ≤ p.2))
      (encPair encBits encUnary) encBool := by fun_prop
  -- The residue of one schedule: the contraction of its network at the precision.
  let cr : NativeCertificate (scheduleResidue F) (encPair (encPair encBits encUnary) encNat)
      encNat :=
    A.certificate.comp ((NativeCertificate.ofPolyTime hP).prod (NativeCertificate.ofPolyTime hnet))
  let R : List Bool × ℕ → ℕ := fun c =>
    (Finset.range (scheduleCount F.heads c.2)).sup fun i => cr.time (c, i)
  let Q : List Bool × ℕ → ℕ := fun c =>
    (Finset.range (scheduleCount F.heads c.2)).sup fun i => cr.space (c, i)
  obtain ⟨a, d, hms⟩ := exists_computableInO_modSum hmod hcnt cr (fun _ => by positivity)
    (fun c i _ => Nat.mod_lt _ (by positivity)) R Q
    (fun c i hi => Finset.le_sup (f := fun i => cr.time (c, i)) (Finset.mem_range.mpr hi))
    (fun c i hi => Finset.le_sup (f := fun i => cr.space (c, i)) (Finset.mem_range.mpr hi))
  let cms : NativeCertificate (modSum (scheduleResidue F) (fun p => 2 ^ (paddedTime p.2 + 1))
      (fun p => scheduleCount F.heads p.2)) (encPair encBits encUnary) encNat := ⟨_, _, hms⟩
  let csim : NativeCertificate (simulate F) (encPair encBits encUnary) encNat :=
    (NativeCertificate.branch (NativeCertificate.ofPolyTime hguard) cms
      (NativeCertificate.const 0)).congr fun p => by simp only [simulate, decide_eq_true_eq]
  -- Bounds on the pieces.
  obtain ⟨K, hK⟩ := A.bound F.constant 2
  obtain ⟨pP, hpP, mP, bP⟩ := exists_mono_poly_cert hP
  obtain ⟨pN, hpN, mN, bN⟩ := exists_mono_poly_cert hnet
  obtain ⟨pG, hpG, -, bG⟩ := exists_mono_poly_cert hguard
  obtain ⟨an, dn, hnl⟩ := hnet.polyBounded_length.exists_le
  set sz : List Bool × ℕ → ℕ := fun c => (encPair encBits encUnary c).length with hsz
  let Z : List Bool × ℕ → ℕ := fun c => 2 * sz c + 1 + (encNat (scheduleCount F.heads c.2)).length
  let Y : List Bool × ℕ → ℕ := fun c =>
    2 * (encNat (paddedTime c.2 + 1)).length + 1 + an * (Z c + 1) ^ dn
  let U : List Bool × ℕ → ℕ := fun c => pP (Z c) + pN (Z c) + K * (Y c + 1) ^ K
  let E : List Bool × ℕ → ℕ := fun c => 2 ^ (K * c.2 / Nat.sqrt (Nat.log 2 c.2))
  have hE (c : List Bool × ℕ) : 1 ≤ E c := Nat.one_le_two_pow
  have hcnt1 (c : List Bool × ℕ) : 1 ≤ scheduleCount F.heads c.2 := Nat.one_le_pow _ _ (by norm_num)
  -- One schedule at a good context.
  have hone (c : List Bool × ℕ) (hc : c.1.length ≤ c.2 ∧ 2 ≤ c.2) (i : ℕ)
      (hi : i < scheduleCount F.heads c.2) :
      cr.time (c, i) ≤ U c * E c ∧ cr.space (c, i) ≤ U c := by
    have hZ : (encPair (encPair encBits encUnary) encNat (c, i)).length ≤ Z c := by
      have := (length_encNat_mono hi.le)
      simp only [length_encPair, Z, sz] at this ⊢
      omega
    have hG : (encN (F.net (c.1, c.2, i))).length ≤
        an * ((encPair (encPair encBits encUnary) encNat (c, i)).length + 1) ^ dn := hnl (c, i)
    have hY : (encPair encNat encN (paddedTime c.2 + 1, F.net (c.1, c.2, i))).length ≤ Y c := by
      have hG' := hG.trans
        (Nat.mul_le_mul_left an (Nat.pow_le_pow_left (Nat.add_le_add_right hZ 1) dn))
      rw [length_encPair]
      simp only [Y]
      omega
    have hA := hK c.2 (paddedTime c.2 + 1) (F.net (c.1, c.2, i)) hc.2 (by omega)
      (paddedTime_add_one_le hc.2) (F.admissible c.1 c.2 i hc.1 hc.2 hi)
    have hKY := Nat.mul_le_mul_left K (Nat.pow_le_pow_left (Nat.add_le_add_right hY 1) K)
    have h1 := (bP (c, i)).1.trans (mP hZ)
    have h2 := (bN (c, i)).1.trans (mN hZ)
    have h3 := (bP (c, i)).2.trans (mP hZ)
    have h4 := (bN (c, i)).2.trans (mN hZ)
    have hEc := hE c
    simp only [cr, NativeCertificate.comp_time, NativeCertificate.comp_space,
      NativeCertificate.prod_time, NativeCertificate.prod_space]
    constructor
    · have hmul : K * ((encPair encNat encN (paddedTime c.2 + 1, F.net (c.1, c.2, i))).length +
          1) ^ K * E c ≤ K * (Y c + 1) ^ K * E c := Nat.mul_le_mul_right _ hKY
      have hpe : pP (Z c) + pN (Z c) ≤ (pP (Z c) + pN (Z c)) * E c := Nat.le_mul_of_pos_right _ hEc
      simp only [U, E] at hA hmul hpe ⊢
      nlinarith [hA.1]
    · simp only [U] at hA ⊢
      omega
  -- Collect the polynomial overhead.
  let V : List Bool × ℕ → ℕ := fun c => pG (sz c) + sz c + 2 * (a * (sz c + 1) ^ d + U c)
  have hszp : PolyBounded sz sz := PolyBounded.self
  have hcntp : PolyBounded sz fun c => (encNat (scheduleCount F.heads c.2)).length :=
    hcnt.polyBounded_length
  have hPcp : PolyBounded sz fun c => (encNat (paddedTime c.2 + 1)).length := hPc.polyBounded_length
  have hZp : PolyBounded sz Z :=
    (((PolyBounded.const 2).mul hszp).add (PolyBounded.const 1)).add hcntp
  have hYp : PolyBounded sz Y :=
    ((((PolyBounded.const 2).mul hPcp).add (PolyBounded.const 1))).add
      ((PolyBounded.const an).mul ((hZp.add (PolyBounded.const 1)).pow dn))
  have hUp : PolyBounded sz U :=
    (((PolyBounded.of_polynomiallyBounded id hpP).comp hZp).add
      ((PolyBounded.of_polynomiallyBounded id hpN).comp hZp)).add
      ((PolyBounded.const K).mul ((hYp.add (PolyBounded.const 1)).pow K))
  have hVp : PolyBounded sz V :=
    (((PolyBounded.of_polynomiallyBounded id hpG).comp hszp).add hszp).add
      ((PolyBounded.const 2).mul (((PolyBounded.const a).mul
        ((hszp.add (PolyBounded.const 1)).pow d)).add hUp))
  obtain ⟨k₀, d₀, hV⟩ := hVp.exists_le
  -- The simulation's time and space.
  have htime (c : List Bool × ℕ) :
      csim.time c ≤ V c * scheduleCount F.heads c.2 * E c := by
    have hG := (bG c).1
    have hVc : pG (sz c) + sz c + 2 * (a * (sz c + 1) ^ d + U c) = V c := rfl
    have hcE : 1 ≤ scheduleCount F.heads c.2 * E c := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by have := hcnt1 c; omega) (by have := hE c; omega))
    simp only [csim, cms, NativeCertificate.congr, NativeCertificate.branch_time,
      NativeCertificate.const_time]
    split_ifs with hc
    · have hc' : c.1.length ≤ c.2 ∧ 2 ≤ c.2 := of_decide_eq_true hc
      have hR : R c ≤ U c * E c :=
        Finset.sup_le fun i hi => (hone c hc' i (Finset.mem_range.mp hi)).1
      have h1 : (scheduleCount F.heads c.2 + 1) * (a * (sz c + 1) ^ d + R c) ≤
          2 * (a * (sz c + 1) ^ d + U c) * (scheduleCount F.heads c.2 * E c) := by
        have hAE : a * (sz c + 1) ^ d ≤ a * (sz c + 1) ^ d * E c := Nat.le_mul_of_pos_right _ (hE c)
        calc _ ≤ (scheduleCount F.heads c.2 + 1) * (a * (sz c + 1) ^ d + U c * E c) :=
              Nat.mul_le_mul_left _ (by omega)
          _ ≤ (2 * scheduleCount F.heads c.2) * ((a * (sz c + 1) ^ d + U c) * E c) :=
              Nat.mul_le_mul (by have := hcnt1 c; omega)
                ((Nat.add_le_add_right hAE (U c * E c)).trans_eq (Nat.add_mul _ _ _).symm)
          _ = _ := by ring
      have h2 : pG (sz c) ≤ pG (sz c) * (scheduleCount F.heads c.2 * E c) :=
        Nat.le_mul_of_pos_right _ hcE
      calc _ ≤ pG (sz c) * (scheduleCount F.heads c.2 * E c) +
            2 * (a * (sz c + 1) ^ d + U c) * (scheduleCount F.heads c.2 * E c) := by
              simp only [sz] at hG h1 h2 ⊢
              omega
        _ ≤ V c * (scheduleCount F.heads c.2 * E c) := by
              rw [← hVc, ← Nat.add_mul]
              exact Nat.mul_le_mul_right _ (by omega)
        _ = _ := by ring
    · have h2 : pG (sz c) + sz c ≤ (pG (sz c) + sz c) * (scheduleCount F.heads c.2 * E c) :=
        Nat.le_mul_of_pos_right _ hcE
      calc _ ≤ (pG (sz c) + sz c) * (scheduleCount F.heads c.2 * E c) := by
              simp only [sz] at hG h2 ⊢
              omega
        _ ≤ V c * (scheduleCount F.heads c.2 * E c) := Nat.mul_le_mul_right _ (by omega)
        _ = _ := by ring
  have hspace (c : List Bool × ℕ) : csim.space c ≤ V c := by
    have hG := (bG c).2
    simp only [csim, cms, NativeCertificate.congr, NativeCertificate.branch_space,
      NativeCertificate.const_space]
    split_ifs with hc
    · have hc' : c.1.length ≤ c.2 ∧ 2 ≤ c.2 := of_decide_eq_true hc
      have hQ : Q c ≤ U c := Finset.sup_le fun i hi => (hone c hc' i (Finset.mem_range.mp hi)).2
      simp only [V, sz] at hG hQ ⊢
      omega
    · simp only [V, sz] at hG ⊢
      omega
  -- Absorb the constants.
  set k := k₀ * 2 ^ d₀ + d₀ + K with hk
  have hVk (c : List Bool × ℕ) : V c ≤ k * (c.1.length + c.2 + 1) ^ k := by
    have hszc : sz c + 1 ≤ 2 * (c.1.length + c.2 + 1) := by
      simp only [sz, length_encPair, encBits_apply, encUnary_apply, List.length_replicate]
      omega
    calc V c ≤ k₀ * (sz c + 1) ^ d₀ := hV c
      _ ≤ k₀ * (2 * (c.1.length + c.2 + 1)) ^ d₀ :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hszc _)
      _ = k₀ * 2 ^ d₀ * (c.1.length + c.2 + 1) ^ d₀ := by rw [mul_pow, mul_assoc]
      _ ≤ k * (c.1.length + c.2 + 1) ^ k :=
          Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
  refine ⟨k, csim.computes.mono_le (fun c => ?_) fun c => (hspace c).trans (hVk c)⟩
  have hEk : E c ≤ 2 ^ (k * c.2 / Nat.sqrt (Nat.log 2 c.2)) :=
    Nat.pow_le_pow_right (by norm_num)
      (Nat.div_le_div_right (Nat.mul_le_mul_right _ (by omega)))
  exact (htime c).trans (Nat.mul_le_mul (Nat.mul_le_mul_right _ (hVk c)) hEk)

/-- **The count within time `2 ^ O(T / √(log T))` and polynomial space** (conditional on the
interfaces). Let `T` be time-constructible with `max n 2 ≤ T n`, let `c ≥ 1`, and let `rule` be a
polynomial-time function of a padded time, in unary, and a count, in binary. Given a network family
for `count`, with `count x τ ≤ 2 ^ τ`, and a contraction algorithm, the function sending `x` to
`rule` of the padded clock `τ = paddedTime (c * T |x|)` and of `count x τ` is computable within
time `2 ^ (C * T n / √⌊log₂ (T n)⌋)` and space `T n ^ d` on inputs of length `n`, for constants `C`
and `d`. -/
theorem exists_computableInO_count (F : NetworkFamily encN value Admissible count)
    (A : ContractionAlgorithm encN value Admissible) (hcount : ∀ x τ, count x τ ≤ 2 ^ τ)
    {T : ℕ → ℕ} (hT : TimeConstructible T) (hTn : ∀ n, max n 2 ≤ T n) {c : ℕ} (hc : 1 ≤ c)
    {β : Type} {encβ : β ↪ List Bool} {rule : ℕ × ℕ → β}
    (hrule : ComputableInPolyTime rule (encPair encUnary encNat) encβ) :
    ∃ C d : ℕ, ComputableInO
      (fun x : List Bool =>
        rule (paddedTime (c * T x.length), count x (paddedTime (c * T x.length))))
      encBits encβ
      (fun x => 2 ^ (C * T x.length / Nat.sqrt (Nat.log 2 (T x.length))))
      (fun x => T x.length ^ d) := by
  obtain ⟨k, hsim⟩ := exists_computableInO_simulate F A
  -- Preparing the context `(x, c * T |x|)`, with the clock in unary.
  have hmul : ComputableInPolyTime (fun n : ℕ => c * n) encUnary encUnary := by fun_prop
  have htau : ComputableInPolyTime (fun p : List Bool × ℕ => paddedTime p.2)
      (encPair encBits encUnary) encUnary := computableInPolyTime_paddedTime.comp (by fun_prop)
  let cT : NativeCertificate (fun x : List Bool => T x.length) encBits encNat :=
    ⟨_, _, hT.computableInO⟩
  let cU : NativeCertificate (fun n : ℕ => n) encNat encUnary := ⟨_, _, ComputableInO.natToUnary⟩
  let cX : NativeCertificate (fun x : List Bool => x) encBits encBits :=
    NativeCertificate.linear (ComputableInO.of_eq fun _ => rfl)
  let cpre : NativeCertificate (fun x : List Bool => (x, c * T x.length)) encBits
      (encPair encBits encUnary) :=
    cX.prod ((NativeCertificate.ofPolyTime hmul).comp (cU.comp cT))
  let csim : NativeCertificate (simulate F) (encPair encBits encUnary) encNat := ⟨_, _, hsim⟩
  let ctotal := (NativeCertificate.ofPolyTime hrule).comp
    (((NativeCertificate.ofPolyTime htau).prod csim).comp cpre)
  -- Monotone polynomial bounds of the polynomial-time pieces.
  obtain ⟨pm, hpm, mm, bm⟩ := exists_mono_poly_cert hmul
  obtain ⟨pt, hpt, mt, bt⟩ := exists_mono_poly_cert htau
  obtain ⟨pr, hpr, mr, br⟩ := exists_mono_poly_cert hrule
  let W : ℕ → ℕ := fun n => 2 * n + (n + 1) ^ 2 + pm n + pt (3 * n + 1) + pr (6 * n + 3) +
    k * (2 * n + 1) ^ k + (n + n + pm n)
  have hW : Cslib.PolynomiallyBounded W := by fun_prop
  obtain ⟨a, e, hWa⟩ := Cslib.polynomiallyBounded_iff_le.mp hW
  -- The cost at an input, in terms of the clock `t = c * T |x|`.
  have hcost (x : List Bool) :
      ctotal.time x ≤ W (c * T x.length) * scheduleCount F.heads (c * T x.length) *
          2 ^ (k * (c * T x.length) / Nat.sqrt (Nat.log 2 (c * T x.length))) ∧
        ctotal.space x ≤ W (c * T x.length) := by
    simp only [ctotal, cpre, csim, cX, cT, cU, NativeCertificate.comp_time,
      NativeCertificate.comp_space, NativeCertificate.prod_time, NativeCertificate.prod_space,
      NativeCertificate.linear_time, NativeCertificate.linear_space, encBits_apply,
      Function.comp_apply]
    set n := x.length
    set t := c * T n with ht
    have hnT : n ≤ T n := (le_max_left _ _).trans (hTn n)
    have h2T : 2 ≤ T n := (le_max_right _ _).trans (hTn n)
    have hTt : T n ≤ t := Nat.le_mul_of_pos_left _ hc
    have hnt : n ≤ t := hnT.trans hTt
    have h2t : 2 ≤ t := h2T.trans hTt
    have hτ := paddedTime_add_one_le h2t
    have hcnt1 : 1 ≤ scheduleCount F.heads t := Nat.one_le_pow _ _ (by norm_num)
    have hE : 1 ≤ 2 ^ (k * t / Nat.sqrt (Nat.log 2 t)) := Nat.one_le_two_pow
    have hctx : (encPair encBits encUnary (x, t)).length ≤ 3 * t + 1 := by
      simp only [length_encPair, encBits_apply, encUnary_apply, List.length_replicate]
      omega
    have hsimx : simulate F (x, t) = count x (paddedTime t) :=
      simulate_eq F hnt h2t (hcount x _)
    have hout : (encPair encUnary encNat (paddedTime t, simulate F (x, t))).length ≤ 6 * t + 3 := by
      have h1 : (encUnary (paddedTime t)).length = paddedTime t := by
        simp only [encUnary_apply, List.length_replicate]
      have h2 : (encNat (simulate F (x, t))).length ≤ paddedTime t + 1 := by
        rw [hsimx]
        calc _ ≤ (encNat (2 ^ paddedTime t)).length := length_encNat_mono (hcount x _)
          _ = paddedTime t + 1 := by rw [length_encNat_eq_size, Nat.size_pow]
      simp only [length_encPair]
      omega
    have hTu : (encUnary (T n)).length ≤ t := by
      simp only [encUnary_apply, List.length_replicate]
      exact hTt
    have hmT := (bm (T n)).1.trans (mm hTu)
    have hmS := (bm (T n)).2.trans (mm hTu)
    have htT := (bt (x, t)).1.trans (mt hctx)
    have htS := (bt (x, t)).2.trans (mt hctx)
    have hrT := (br (paddedTime t, simulate F (x, t))).1.trans (mr hout)
    have hrS := (br (paddedTime t, simulate F (x, t))).2.trans (mr hout)
    have hpow : k * (n + t + 1) ^ k ≤ k * (2 * t + 1) ^ k :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    have hsq : (T n + 1) ^ 2 ≤ (t + 1) ^ 2 := Nat.pow_le_pow_left (by omega) _
    constructor
    · have hsimT : k * (n + t + 1) ^ k * scheduleCount F.heads t *
          2 ^ (k * t / Nat.sqrt (Nat.log 2 t)) ≤
          k * (2 * t + 1) ^ k *
            (scheduleCount F.heads t * 2 ^ (k * t / Nat.sqrt (Nat.log 2 t))) := by
        rw [Nat.mul_assoc]
        exact Nat.mul_le_mul_right _ hpow
      have hrest : 2 * t + (t + 1) ^ 2 + pm t + pt (3 * t + 1) + pr (6 * t + 3) ≤
          (2 * t + (t + 1) ^ 2 + pm t + pt (3 * t + 1) + pr (6 * t + 3)) *
            (scheduleCount F.heads t * 2 ^ (k * t / Nat.sqrt (Nat.log 2 t))) :=
        Nat.le_mul_of_pos_right _ (Nat.mul_pos hcnt1 hE)
      have hWt : W t * scheduleCount F.heads t * 2 ^ (k * t / Nat.sqrt (Nat.log 2 t)) =
          W t * (scheduleCount F.heads t * 2 ^ (k * t / Nat.sqrt (Nat.log 2 t))) := by ring
      rw [hWt]
      have hWle : (2 * t + (t + 1) ^ 2 + pm t + pt (3 * t + 1) + pr (6 * t + 3)) *
            (scheduleCount F.heads t * 2 ^ (k * t / Nat.sqrt (Nat.log 2 t))) +
          k * (2 * t + 1) ^ k * (scheduleCount F.heads t * 2 ^ (k * t / Nat.sqrt (Nat.log 2 t))) ≤
          W t * (scheduleCount F.heads t * 2 ^ (k * t / Nat.sqrt (Nat.log 2 t))) := by
        rw [← Nat.add_mul]
        exact Nat.mul_le_mul_right _ (by simp only [W]; omega)
      omega
    · simp only [W]
      omega
  -- Absorb the cost into `2 ^ O(T / √(log T))` and `T ^ O(1)`.
  obtain ⟨C, hC⟩ := Nat.exists_three_pow_mul_le_two_pow_div_sqrt_log_two F.heads c e k
  refine ⟨(a + 0 + 1) * (C + 1), a * c ^ e + 0 + 2 * e,
    (ctotal.computes.of_enc_eq fun x => congrArg encβ ?_).mono_le (fun x => ?_) fun x => ?_⟩
  · have hnt : x.length ≤ c * T x.length :=
      ((le_max_left _ _).trans (hTn _)).trans (Nat.le_mul_of_pos_left _ hc)
    have h2t : 2 ≤ c * T x.length :=
      ((le_max_right _ _).trans (hTn _)).trans (Nat.le_mul_of_pos_left _ hc)
    simp only [Function.comp_apply]
    rw [simulate_eq F hnt h2t (hcount x _)]
  · set n := x.length
    have h2T : 2 ≤ T n := (le_max_right _ _).trans (hTn n)
    have hcostT := (hcost x).1
    have hWt := hWa (c * T n)
    have hmain : 3 ^ (F.heads * (c * T n ⌈/⌉ Nat.clog 2 (c * T n + 2))) * (c * T n + 1) ^ e *
        2 ^ (k * (c * T n) / Nat.sqrt (Nat.log 2 (c * T n))) ≤
        2 ^ (C * T n / Nat.sqrt (Nat.log 2 (T n))) := hC (T n) h2T
    have habs := Nat.mul_two_pow_div_sqrt_log_two_add_le (a := a) (b := 0) (C := C) h2T
    calc ctotal.time x ≤ W (c * T n) * scheduleCount F.heads (c * T n) *
          2 ^ (k * (c * T n) / Nat.sqrt (Nat.log 2 (c * T n))) := hcostT
      _ ≤ a * (c * T n + 1) ^ e * scheduleCount F.heads (c * T n) *
          2 ^ (k * (c * T n) / Nat.sqrt (Nat.log 2 (c * T n))) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hWt)
      _ = a * (3 ^ (F.heads * (c * T n ⌈/⌉ Nat.clog 2 (c * T n + 2))) * (c * T n + 1) ^ e *
          2 ^ (k * (c * T n) / Nat.sqrt (Nat.log 2 (c * T n)))) := by
          simp only [scheduleCount, numBlocks, blockLength]
          ring
      _ ≤ a * 2 ^ (C * T n / Nat.sqrt (Nat.log 2 (T n))) + 0 := by
          rw [Nat.add_zero]
          exact Nat.mul_le_mul_left _ hmain
      _ ≤ _ := habs
  · set n := x.length
    have h2T : 2 ≤ T n := (le_max_right _ _).trans (hTn n)
    have hspace := (hcost x).2
    have hWt := hWa (c * T n)
    have hct : c * T n + 1 ≤ c * (T n + 1) := by nlinarith
    calc ctotal.space x ≤ a * (c * T n + 1) ^ e := hspace.trans hWt
      _ ≤ a * (c * (T n + 1)) ^ e := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hct _)
      _ = a * c ^ e * (T n + 1) ^ e + 0 := by rw [mul_pow, Nat.mul_assoc, add_zero]
      _ ≤ T n ^ (a * c ^ e + 0 + 2 * e) := Nat.mul_add_one_pow_add_le_pow h2T

end Cslib.Complexity.CountingSimulation
