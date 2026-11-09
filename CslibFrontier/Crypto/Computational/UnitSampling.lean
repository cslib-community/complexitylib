/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Words
public import CslibFrontier.Crypto.Game
public import CslibFrontier.Languages.Probabilistic.UniformNat
public import Mathlib.Data.Nat.Totient
import CslibFrontier.Crypto.Computational.Homomorphic.Leveled.ExactSecurity
import CslibFrontier.Crypto.Game.Statistical
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.PMF.UniformSubset
import CslibFrontier.Probability.StatisticalDistance
import Mathlib.Data.Nat.Size

/-!
# Sampling units modulo a product of two primes

Paillier and Goldwasser–Micali encryption over a modulus `N = p * q` draw their randomness with
`ProbComp.sampleModNat (n + |N|) N` and use it as a unit modulo `N`, while the security proofs
reason about a uniform unit. The draw is within `N / 2 ^ (n + |N|) ≤ 1 / 2 ^ n` of a uniform
residue modulo `N`, and a uniform residue is within the fraction `(N - φ(N)) / N` of non-units of a
uniform unit. When `p` and `q` have at least `n` bits, this fraction is at most `4 / 2 ^ n`.

## Main results

* `Cslib.Crypto.Game.advantage_bind_units_le`: restricting a uniform residue modulo `N` to the
  units changes the advantage of any continuation by at most `(N - φ(N)) / N`.
* `Cslib.Crypto.Game.advantage_sampleModNat_units_le`: for `N = p * q` with `n`-bit primes,
  replacing `ProbComp.sampleModNat (n + |N|) N` by a uniform unit changes the advantage of any
  continuation by at most `5 / 2 ^ n`.
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped ENNReal NNReal Cslib.Probability.PMF

/-- A uniform draw from `Fin M` is a uniform draw from `ZMod M`. -/
private theorem uniformOfFintype_fin_bind (M : ℕ) [NeZero M] (k : ℕ → Game) :
    ((PMF.uniformOfFintype (Fin M)).bind fun i => k i.val) =
      (PMF.uniformOfFintype (ZMod M)).bind fun r => k r.val := by
  rcases Nat.exists_eq_succ_of_ne_zero (NeZero.ne M) with ⟨m, rfl⟩
  rfl

/-- Restricting a uniform residue modulo `N` to the units changes the advantage of any
continuation by at most the fraction `(N - φ(N)) / N` of non-units. -/
theorem Game.advantage_bind_units_le (N : ℕ) [NeZero N] (k : ZMod N → Game) :
    Game.advantage ((PMF.uniformOfFintype (ZMod N)).bind k)
      ((PMF.uniformOfFintype (ZMod N)ˣ).bind fun u => k u) ≤
      ((N - N.totient : ℕ) : ℝ≥0) / N := by
  classical
  let E : Set (ZMod N) := {x | x.val.Coprime N}
  let S : Finset (ZMod N) := Finset.univ.filter (· ∈ E)
  let e : (ZMod N)ˣ ≃ S := ZMod.unitsEquivCoprime.trans
    (Equiv.subtypeEquivRight fun x => by simp [S, E])
  have hS : S.Nonempty := ⟨_, (e 1).2⟩
  have : Nonempty S := ⟨e 1⟩
  have hev : ∃ a ∈ E, a ∈ (PMF.uniformOfFintype (ZMod N)).support :=
    ⟨((1 : (ZMod N)ˣ) : ZMod N), ZMod.val_coe_unit_coprime 1,
      Probability.PMF.mem_support_uniformOfFintype _⟩
  have hmap : (PMF.uniformOfFintype (ZMod N)ˣ).map (fun u : (ZMod N)ˣ => (u : ZMod N)) =
      PMF.uniformOfFinset S hS := by
    have hcomp : (fun u : (ZMod N)ˣ => (u : ZMod N)) = Subtype.val ∘ e := rfl
    rw [hcomp, ← PMF.map_comp, Probability.PMF.uniformOfFintype_map_equiv e,
      Probability.PMF.uniformOfFintype_finset_map_val]
  have hfilter : (PMF.uniformOfFintype (ZMod N)).filter E hev = PMF.uniformOfFinset S hS := by
    refine Probability.PMF.pmf_eq_uniformOfFinset_of_ite_const hS
      (c := (Fintype.card (ZMod N) : ℝ≥0∞)⁻¹ *
        (∑' a, E.indicator (PMF.uniformOfFintype (ZMod N)) a)⁻¹) fun θ => ?_
    by_cases hθ : θ ∈ E
    · simp only [PMF.filter_apply, Set.indicator_of_mem hθ, PMF.uniformOfFintype_apply, S,
        Finset.mem_filter, Finset.mem_univ, true_and, hθ, ↓reduceIte]
    · simp only [PMF.filter_apply, Set.indicator_apply, hθ, ↓reduceIte, zero_mul, S,
        Finset.mem_filter, Finset.mem_univ, true_and]
  have hcardS : (Finset.univ.filter (· ∈ E)).card = N.totient := by
    rw [← ZMod.card_units_eq_totient N]
    exact ((Fintype.card_congr e).trans (Fintype.card_coe S)).symm
  have hcount : (Finset.univ.filter (· ∈ Eᶜ)).card = N - N.totient := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (ZMod N))) (fun x => x ∈ E)
    rw [Finset.card_univ, ZMod.card] at h
    have h2 : Finset.univ.filter (· ∈ Eᶜ) = Finset.univ.filter (fun x => ¬ x ∈ E) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_compl_iff]
    rw [h2]
    omega
  have hbind : (PMF.uniformOfFintype (ZMod N)ˣ).bind (fun u => k u) =
      ((PMF.uniformOfFintype (ZMod N)ˣ).map (fun u : (ZMod N)ˣ => (u : ZMod N))).bind k := by
    rw [PMF.bind_map]
    rfl
  rw [← NNReal.coe_le_coe, Game.advantage_eq_nndist, coe_nndist, hbind, hmap, ← hfilter]
  refine (PMF.dist_bind_le _ _ k).trans (le_of_eq ?_)
  rw [Probability.PMF.dist_filter, Probability.PMF.toOuterMeasure_uniformOfFintype_toReal, hcount,
    ZMod.card, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_natCast]

/-- For distinct primes `p` and `q` of at least `n` bits, the non-units modulo `p * q` are at most
a `4 / 2 ^ n` fraction of the residues. -/
private theorem sub_totient_div_le {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpn : n ≤ p.size) (hqn : n ≤ q.size) :
    ((p * q - (p * q).totient : ℕ) : ℝ≥0) / (p * q : ℕ) ≤ 4 / 2 ^ n := by
  have hpow {x m : ℕ} (hx : x.Prime) (hm : m ≤ x.size) : 2 ^ m ≤ 2 * x := by
    cases m with
    | zero => rw [pow_zero]; have := hx.two_le; omega
    | succ m => rw [pow_succ']; exact Nat.mul_le_mul_left 2 (Nat.lt_size.mp hm)
  have h2p := hpow hp hpn
  have h2q := hpow hq hqn
  have hle : (p - 1) * (q - 1) ≤ p * q := Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
  have hnat : (p * q - (p - 1) * (q - 1)) * 2 ^ n ≤ 4 * (p * q) := by
    zify [hle, hp.one_le, hq.one_le] at h2p h2q ⊢
    nlinarith [mul_le_mul_of_nonneg_right h2p (Int.natCast_nonneg q),
      mul_le_mul_of_nonneg_right h2q (Int.natCast_nonneg p), pow_pos (two_pos : (0 : ℤ) < 2) n]
  rw [Nat.totient_mul ((Nat.coprime_primes hp hq).mpr hpq), Nat.totient_prime hp,
    Nat.totient_prime hq, div_le_div_iff₀ (Nat.cast_pos.mpr (Nat.mul_pos hp.pos hq.pos))
      (by positivity)]
  exact_mod_cast hnat

/-- For `N = p * q` with distinct primes `p` and `q` of at least `n` bits, drawing
`r ← ProbComp.sampleModNat (n + |N|) N` instead of a uniform unit `u` modulo `N` changes the
advantage of any continuation `k` by at most `5 / 2 ^ n`: at most `1 / 2 ^ n` from the residue
sampler and at most `4 / 2 ^ n` from the non-units. -/
theorem Game.advantage_sampleModNat_units_le {p q n : ℕ} [NeZero (p * q)] (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (hpn : n ≤ p.size) (hqn : n ≤ q.size) (k : ℕ → Game) :
    Game.advantage
      ((ProbComp.eval (ProbComp.sampleModNat (n + (encNat (p * q)).length) (p * q))).bind k)
      ((PMF.uniformOfFintype (ZMod (p * q))ˣ).bind fun u => k u.val.val) ≤ 5 / 2 ^ n := by
  have h1 := Homomorphic.Scheme.advantage_bind_sampleModNat_fin_le
    (n + (encNat (p * q)).length) (p * q) k
  rw [uniformOfFintype_fin_bind] at h1
  have hw : ((p * q : ℕ) : ℝ≥0) / 2 ^ (n + (encNat (p * q)).length) ≤ 1 / 2 ^ n := by
    rw [encNat_apply, Nat.size_eq_bits_len, div_le_div_iff₀ (by positivity) (by positivity),
      one_mul, pow_add, mul_comm ((2 : ℝ≥0) ^ n)]
    gcongr
    exact_mod_cast (Nat.lt_size_self (p * q)).le
  calc _ ≤ _ := Game.advantage_triangle _ ((PMF.uniformOfFintype (ZMod (p * q))).bind
        fun x => k x.val) _
    _ ≤ (1 : ℝ≥0) / 2 ^ n + 4 / 2 ^ n := add_le_add (h1.trans hw)
      ((Game.advantage_bind_units_le (p * q) fun x => k x.val).trans
        (sub_totient_div_le hp hq hpq hpn hqn))
    _ = 5 / 2 ^ n := by ring

end Cslib.Crypto
