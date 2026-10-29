/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Kolmogorov.MINKT
import Complexity.Computability.Kolmogorov.TimeBounded

/-!
Regression clients for time-bounded Kolmogorov complexity (`K^t`), Levin's `Kt`, the universal
multi-tape description method `universalTM`, `MINKT`, `MINKTAt ∈ NP`, and `GapMINKT`.
-/

namespace ComplexityTests.KolmogorovTimeBounded

open Cslib Cslib.Kolmogorov Cslib.Kolmogorov.DescriptionMethod Cslib.Complexity
open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.Universal

/-! ### Concrete bounds and properties of `K^t` and `Kt` -/

-- Antitonicity instantiated at concrete step bounds and time functions.
example : timeBoundedAt 10 [true, false, true] ≤ timeBoundedAt 4 [true, false, true] :=
  timeBoundedAt_antitone [true, false, true] (by omega)

example :
    timeBounded (fun n => 2 * n + 2) [true, false, true] ≤
      timeBounded (fun n => n + 1) [true, false, true] :=
  timeBounded_antitone [true, false, true] (fun n => by change n + 1 ≤ 2 * n + 2; omega)

-- Concrete upper bounds `K(x) ≤ K^{n+1}(x) ≤ |x| + copyOverhead` (LP20 Fact 2.1).
example :
    plain [true, false, true] ≤ (3 + copyOverhead : ℕ) ∧
      timeBounded (fun n => n + 1) [true, false, true] ≤ (3 + copyOverhead : ℕ) :=
  ⟨(plain_le_timeBounded (fun n => n + 1) [true, false, true]).trans
    (timeBounded_le (fun _ => le_rfl) [true, false, true]),
    timeBounded_le (fun _ => le_rfl) [true, false, true]⟩

-- Concrete `Partrec.universal` complexity bound via `universalTM` at `t(n) = n + 1`.
example : ∃ c : ℕ, ∀ n : ℕ,
    universal.ecomplexity n ≤ (n.bits.length + copyOverhead : ℕ) + c := by
  obtain ⟨c, hc⟩ := exists_ecomplexity_universal_le_timeBounded_bits
  refine ⟨c, fun n => (hc (fun m => m + 1) n).trans ?_⟩
  exact add_le_add_left (timeBounded_le (fun _ => le_rfl) n.bits) (c : ℕ∞)

-- Bridge between `ℕ∞` and the `ℕ` infimum when a witness exists.
example (x : List Bool) :
    timeBoundedNat (fun n => n + 1) x =
      sInf {k : ℕ | ∃ p : List Bool, p.length = k ∧
        x ∈ (universalTM.run p).runFor (x.length + 1)} :=
  timeBoundedNat_eq_sInf (timeBounded_ne_top (t := fun n => n + 1) le_rfl)

-- Concrete counting bound: at least 13 of the 16 4-bit strings have `K^{n^2}(x) ≥ 2`.
example :
    13 ≤
      {x : List Bool |
        x.length = 4 ∧ ((4 - 2 : ℕ) : ℕ∞) ≤ timeBounded (fun n => n ^ 2) x}.ncard := by
  have h := two_pow_lt_ncard_setOf_length_eq_le_timeBounded_add (fun n => n ^ 2) 4 2
  omega

-- Levin's `Kt` on a concrete 4-bit string (`|[1, 0, 1, 0]| = 4`, `⌈log₂ 5⌉ = 3`).
example (x : List Bool) (k : ℕ) :
    levinKt [true, false, true, false] ≤ (4 + copyOverhead + 3 : ℕ) ∧
    levinKtNat [true, false, true, false] ≤ 4 + copyOverhead + 3 ∧
    (levinKtNat x ≤ k ↔
      ∃ (p : List Bool) (s : ℕ),
        x ∈ (universalTM.run p).runFor s ∧ p.length + Nat.clog 2 s ≤ k) :=
  ⟨levinKt_le_length_add [true, false, true, false],
   levinKtNat_le_iff.mpr (levinKt_le_length_add [true, false, true, false]),
   levinKtNat_le_iff.trans levinKt_le_natCast_iff⟩

/-! ### Non-vacuous `MINKT`, `MINKTAt`, and `GapMINKT` instances -/

-- Concrete `MINKT` and `MINKTAt` yes-instances.
example (x : List Bool) :
    (⟨x, x.length + 1, x.length + copyOverhead⟩ : MINKT.Instance) ∈ MINKT ∧
    (⟨[true, false, true], 4, 3 + copyOverhead⟩ : MINKT.Instance) ∈ MINKT ∧
    x ∈ MINKTAt (fun n => n + 1) (fun n => n + copyOverhead) :=
  ⟨MINKT.mk_mem_iff.mpr (timeBoundedAt_le_length_add le_rfl),
   MINKT.mk_mem_iff.mpr (timeBoundedAt_le_length_add le_rfl),
   timeBounded_le (fun _ => le_rfl) x⟩

-- Concrete `MINKT` no-instance from an incompressible string of length `s + 1`.
example (t s : ℕ) :
    ∃ x : List Bool, x.length = s + 1 ∧ (⟨x, t, s⟩ : MINKT.Instance) ∉ MINKT := by
  obtain ⟨x, hx, hall⟩ := exists_length_eq_forall_le_timeBounded (s + 1)
  refine ⟨x, hx, ?_⟩
  rw [MINKT.mk_mem_iff, not_le]
  have hle : ((s + 1 : ℕ) : ℕ∞) ≤ timeBoundedAt t x := hall (fun _ => t)
  exact (ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self s)).trans_le hle

-- Non-trivial `GapMINKT` with strict gap `σ(n, s) = 2 * s + 1` and `τ(n, t) = 2 * t + 2`:
-- exhibits both a concrete yes-instance and a no-instance of length `2 * s + 2`.
example :
    let P := GapMINKT (fun _ s => 2 * s + 1) (fun _ t => 2 * t + 2)
      (fun _ s => by omega) (fun _ t => by omega)
    (⟨[true, false], 3, 2 + copyOverhead⟩ : MINKT.Instance) ∈ P.yes ∧
      ∀ t s : ℕ, ∃ x : List Bool, x.length = 2 * s + 2 ∧
        (⟨x, t, s⟩ : MINKT.Instance) ∈ P.no := by
  intro P
  refine ⟨MINKT.mk_mem_iff.mpr (timeBoundedAt_le_length_add le_rfl), fun t s => ?_⟩
  obtain ⟨x, hx, hall⟩ := exists_length_eq_forall_le_timeBounded (2 * s + 2)
  refine ⟨x, hx, ?_⟩
  rw [GapMINKT.no_eq, GapMINKT.mem_noSet_iff]
  dsimp only
  have hle : ((2 * s + 2 : ℕ) : ℕ∞) ≤ timeBoundedAt (2 * t + 2) x :=
    hall (fun _ => 2 * t + 2)
  exact (ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self (2 * s + 1))).trans_le hle

-- Derive `NP` membership for the linear-threshold language
-- `MINKTAt (n ↦ n + 1) (n ↦ n + copyOverhead)` from `MINKTAt.mem_NP_polynomial₂` by rewriting
-- both bounds as polynomial evaluations.
example : MINKTAt (fun n => n + 1) (fun n => n + copyOverhead) ∈ NP encBits := by
  have ht : (fun n : ℕ => n + 1) = (Polynomial.X + 1).eval := by
    funext n
    simp
  have hs : (fun n : ℕ => n + copyOverhead) = (Polynomial.X + Polynomial.C copyOverhead).eval := by
    funext n
    simp
  rw [ht, hs]
  exact MINKTAt.mem_NP_polynomial₂ (Polynomial.X + 1) (Polynomial.X + Polynomial.C copyOverhead)

end ComplexityTests.KolmogorovTimeBounded
